import ZlibF.Zlib.«deflate_base.c»
import ZlibF.Zlib.«deflate_strategies.c»

/-!
# deflate.c, part 3: the public functions

Faithful translation of `deflate.c` (default x86_64 Linux build). Parts 1 and 2 are `deflate_base.c.lean`
(`slide_hash`, `read_buf`, `fill_window`, `flush_pending`, the macros) and `deflate_strategies.c.lean`
(`longest_match`, `deflate_stored`, ..., `deflate_huff`).

**Order.** Lean needs a definition before its use, so the order differs from the C where a function is only declared
(in `zlib.h`) when it is used: `deflateEnd`, `deflateResetKeep`, `lm_init`, `deflateReset` come before
`deflateInit2_`, and `deflateParams` and `deflateCopy` come after `deflate`. No function changes.

**Output parameters.** C passes `unsigned *pending`, `int *bits`, `uInt *dictLength`. The runtime has no pointer to
a scalar cell. The value-returning interfaces take a nullability flag and return the final
value for each output. The exported C ABI entries at the end of this module use addresses
and perform the scalar loads and stores in source order.

**`deflate` of the gzip header** (`name`, `comment`): the two loops are textually identical except for the field
`name` / `comment` (and the `gzindex = 0` after the name); one function `gz_string_loop` with a selector serves both.
-/

namespace Zlib.Deflate
open C
open Zlib.Trees («_tr_init» «_tr_flush_bits» «_tr_flush_block» «_tr_stored_block» «_tr_align»)
open Zlib.Crc32 (crc32 crc32_z)

def deflate_copyright : CGlobalConstStr String :=
  " deflate 1.4.0.1 Copyright 1995-2026 Jean-loup Gailly and Mark Adler "

/-- The three function addresses stored in the C compression configuration table. -/
def CompressFunc.call (f : CompressFunc) (s : DeflateStatePtr) (flush : Int32) : M block_state :=
  match f with
  | .stored => deflate_stored s flush
  | .fast => deflate_fast s flush
  | .slow => deflate_slow s flush

/-- The z_stream pointer value `Z_NULL`. -/
abbrev Z_NULL_strm : ZStreamPtr := none

/-- `local int deflateStateCheck(z_streamp strm)` -/
def deflateStateCheck (strm : ZStreamPtr) : M (COrder 6 (CStatic Int32)) := do
  -- if (strm == Z_NULL || strm->zalloc == (alloc_func)0 || strm->zfree == (free_func)0) return 1;
  if strm == none then return 1
  let z ← ldZStream strm
  if z.zalloc == FnPtr.null || z.zfree == FnPtr.null then return 1
  -- s = strm->state;
  let s ← castDeflateState z.state
  -- if (s == Z_NULL || s->strm != strm || (s->status != INIT_STATE && ... )) return 1;
  if s == none then return 1
  let d ← ldDeflateState s
  if d.strm != strm || (d.status != INIT_STATE && d.status != GZIP_STATE && d.status != EXTRA_STATE &&
      d.status != NAME_STATE && d.status != COMMENT_STATE && d.status != HCRC_STATE &&
      d.status != BUSY_STATE && d.status != FINISH_STATE) then return 1
  return 0

/-- `ERR_RETURN(strm, err)`: `return (strm->msg = ERR_MSG(err), (err))` -/
def ERR_RETURN (strm : ZStreamPtr) (err : Int32) : M Int32 := do
  let m ← ERR_MSG err
  zwr strm (fun z => { z with msg := m })
  return err

/-- `ZFREE(strm, state)` through the configured stream deallocator. -/
def ZFREE_state (strm : ZStreamPtr) (p : DeflateStatePtr) : M Unit := do
  zfree_default strm
  freeDeflateState p

/-- `int ZEXPORT deflateEnd(z_streamp strm)` -/
def deflateEnd (strm : ZStreamPtr) : M (COrder 23 (CExport Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let sp ← castDeflateState (← zrd strm (·.state))
  -- status = strm->state->status;
  let status ← rd sp (·.status)
  -- TRY_FREE(strm, strm->state->pending_buf); head; prev; window
  let pb ← rd sp (·.pending_buf)
  if pb != .null then ZFREE_bytes strm pb
  let hd ← rd (← castDeflateState (← ldZStream strm).state) (·.head)
  if hd != .null then ZFREE_words strm hd
  let pv ← rd (← castDeflateState (← ldZStream strm).state) (·.prev)
  if pv != .null then ZFREE_words strm pv
  let wd ← rd (← castDeflateState (← ldZStream strm).state) (·.window)
  if wd != .null then ZFREE_bytes strm wd
  -- ZFREE(strm, strm->state);
  ZFREE_state strm (← castDeflateState (← ldZStream strm).state)
  -- strm->state = Z_NULL;
  zwr strm (fun z => { z with state := none })
  -- return status == BUSY_STATE ? Z_DATA_ERROR : Z_OK;
  return if status == BUSY_STATE then Z_DATA_ERROR else Z_OK

/-- `int ZEXPORT deflateResetKeep(z_streamp strm)` -/
def deflateResetKeep (strm : ZStreamPtr) : M (COrder 9 (CExport Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  -- strm->total_in = strm->total_out = 0; strm->msg = Z_NULL; strm->data_type = Z_UNKNOWN;
  zwr strm (fun z => { z with total_in := 0, total_out := 0, msg := .null, data_type := Z_UNKNOWN })
  -- s = (deflate_state *)strm->state; s->pending = 0; s->pending_out = s->pending_buf;
  let s ← castDeflateState (← zrd strm (·.state))
  wr s (fun d =>
    let d := { d with pending := 0 }
    { d with pending_out := d.pending_buf })
  -- if (s->wrap < 0) s->wrap = -s->wrap;
  let d ← ldDeflateState s
  if d.wrap < 0 then
    let w ← ineg d.wrap
    wr s (fun d => { d with wrap := w })
  -- s->status = s->wrap == 2 ? GZIP_STATE : INIT_STATE;
  wr s (fun d => { d with status := if d.wrap == 2 then GZIP_STATE else INIT_STATE })
  -- strm->adler = s->wrap == 2 ? crc32(0L, Z_NULL, 0) : adler32(0L, Z_NULL, 0);
  let adler ← if (← rd s (·.wrap)) == 2 then crc32 0 (Ptr.null : BPtr) 0 else Zlib.Adler32.adler32 0 (Ptr.null : BPtr) 0
  zwr strm (fun z => { z with adler })
  -- s->last_flush = -2; s->gzhead = Z_NULL;
  wr s (fun d =>
    let d := { d with last_flush := -2 }
    { d with gzhead := none })
  -- { uInt matches = s->level == 0 ? s->matches : 0; _tr_init(s); s->matches = matches; }
  let d ← ldDeflateState s
  let «matches» : UInt32 := if d.level == 0 then d.«matches» else 0
  _tr_init s
  wr s (fun d => { d with «matches» := «matches» })
  -- s->block_start = (long)s->strstart; s->lookahead = 0;
  -- s->match_length = s->prev_length = MIN_MATCH-1; s->match_available = 0;
  wr s (fun d =>
    let d := { d with block_start := d.strstart.toUInt64.toInt64 }
    let d := { d with lookahead := 0 }
    let d := { d with prev_length := MIN_MATCH_u - 1 }
    let d := { d with match_length := MIN_MATCH_u - 1 }
    { d with match_available := 0 })
  return Z_OK

/-- `local void lm_init(deflate_state *s)` -/
def lm_init (s : DeflateStatePtr) : M (COrder 10 (CStatic Unit)) := do
  -- s->window_size = (ulg)2L*s->w_size;
  wr s (fun d => { d with window_size := 2 * d.w_size.toUInt64 })
  CLEAR_HASH s
  -- s->matches = 0;
  wr s (fun d => { d with «matches» := 0 })
  -- s->max_lazy_match = configuration_table[s->level].max_lazy; good_match; nice_match; max_chain_length
  let c ← config_at (← rd s (·.level))
  wr s (fun d =>
    let d := { d with max_lazy_match := c.max_lazy.toUInt32 }
    let d := { d with good_match := c.good_length.toUInt32 }
    let d := { d with nice_match := c.nice_length.toUInt32.toInt32 }
    { d with max_chain_length := c.max_chain.toUInt32 })
  -- s->strstart = 0; s->block_start = 0L; s->lookahead = 0; s->insert = 0;
  -- s->match_length = s->prev_length = MIN_MATCH-1; s->match_available = 0; s->ins_h = 0;
  wr s (fun d =>
    let d := { d with strstart := 0 }
    let d := { d with block_start := 0 }
    let d := { d with lookahead := 0 }
    let d := { d with insert := 0 }
    let d := { d with prev_length := MIN_MATCH_u - 1 }
    let d := { d with match_length := MIN_MATCH_u - 1 }
    let d := { d with match_available := 0 }
    { d with ins_h := 0 })

/-- `int ZEXPORT deflateReset(z_streamp strm)` -/
def deflateReset (strm : ZStreamPtr) : M (COrder 11 (CExport Int32)) := do
  let ret ← deflateResetKeep strm
  if ret == Z_OK then lm_init (← castDeflateState (← zrd strm (·.state)))
  return ret

/-- Initialize the allocated record and its four buffers in the order of the patched C stores.
The allocator may observe the published stream and state between buffer requests. -/
def initAllocated (strm : ZStreamPtr) (s : DeflateStatePtr) (level method windowBits memLevel strategy wrap : Int32) : M Int32 := do
  -- zmemzero(s, sizeof(deflate_state));
  stDeflateState s DeflateState.zeroed
  -- strm->state = (struct internal_state FAR *)s; s->strm = strm; s->status = INIT_STATE;
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  wr s (fun d => { d with strm := strm, status := INIT_STATE, wrap, w_bits := windowBits.toUInt32 })
  let w_size ← cinline (ishl 1 (← rd s (·.w_bits)).toNat)
  wr s (fun d => { d with w_size := w_size.toUInt32 })
  wr s (fun d => { d with w_mask := d.w_size - 1 })
  wr s (fun d => { d with hash_bits := memLevel.toUInt32 + 7 })
  let hash_size ← cinline (ishl 1 (← rd s (·.hash_bits)).toNat)
  wr s (fun d => { d with hash_size := hash_size.toUInt32 })
  wr s (fun d => { d with hash_mask := d.hash_size - 1 })
  wr s (fun d => { d with hash_shift := (d.hash_bits + (MIN_MATCH_u - 1)) / MIN_MATCH_u })
  let window ← ZALLOC_bytes strm (← cinline (rd s (·.w_size))) 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm (← cinline (rd s (·.w_size)))
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm (← cinline (rd s (·.hash_size)))
  wr s (fun d => { d with head })
  wr s (fun d => { d with high_water := 0 })
  let lit_bufsize ← cinline (ishl 1 (← iadd memLevel 6).toInt.toNat)
  wr s (fun d => { d with lit_bufsize := lit_bufsize.toUInt32 })
  let pending_buf ← ZALLOC_bytes strm (← cinline (rd s (·.lit_bufsize))) 4
  wr s (fun d => { d with pending_buf })
  wr s (fun d => { d with pending_buf_size := d.lit_bufsize.toUInt64 * 4 })
  let d ← ldDeflateState s
  if d.window == .null || d.prev == .null || d.head == .null || d.pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd d.pending_buf d.lit_bufsize.toNat
  wr s (fun d => { d with sym_buf })
  wr s (fun d => { d with sym_end := (d.lit_bufsize - 1) * 3 })
  wr s (fun d =>
    let d := { d with level, strategy }
    { d with «method» := method.toUInt32.toUInt8 })
  -- return deflateReset(strm);
  deflateReset strm

/-- `int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel, int strategy,
const char *version, int stream_size)` -/
def deflateInit2_ (strm : ZStreamPtr) (level method windowBits memLevel strategy : Int32) (version : ConstCStr)
    (stream_size : Int32) : M (COrder 5 (CExport Int32)) := do
  let mut level := level
  let mut wrap : Int32 := 1
  -- static const char my_version[] = ZLIB_VERSION;  (first character '1')
  -- if (version == Z_NULL || version[0] != my_version[0] || stream_size != sizeof(z_stream)) return Z_VERSION_ERROR;
  if version == .null then return Z_VERSION_ERROR
  if (← load8 version) != 49 || stream_size != sizeof_z_stream then return Z_VERSION_ERROR
  -- if (strm == Z_NULL) return Z_STREAM_ERROR;
  if strm == none then return Z_STREAM_ERROR
  -- strm->msg = Z_NULL;
  zwr strm (fun z => { z with msg := .null })
  -- if (strm->zalloc == (alloc_func)0) { strm->zalloc = zcalloc; strm->opaque = (voidpf)0; }
  if (← zrd strm (·.zalloc)) == FnPtr.null then
    zwr strm (fun z => { z with zalloc := FnPtr.fn "zcalloc", «opaque» := .null })
  -- if (strm->zfree == (free_func)0) strm->zfree = zcfree;
  if (← zrd strm (·.zfree)) == FnPtr.null then
    zwr strm (fun z => { z with zfree := FnPtr.fn "zcfree" })
  -- if (level == Z_DEFAULT_COMPRESSION) level = 6;
  if level == Z_DEFAULT_COMPRESSION then level := 6
  let mut bits ← cdecl windowBits
  if bits < 0 then
    -- suppress zlib wrapper
    wrap := 0
    if bits < -15 then return Z_STREAM_ERROR
    bits ← ineg bits
  else if bits > 15 then
    wrap := 2                                    -- write gzip wrapper instead
    bits ← isub bits 16
  -- if (memLevel < 1 || ... ) return Z_STREAM_ERROR;
  if memLevel < 1 || memLevel > MAX_MEM_LEVEL || method != Z_DEFLATED ||
      bits < 8 || bits > 15 || level < 0 || level > 9 ||
      strategy < 0 || strategy > Z_FIXED || (bits == 8 && wrap != 1) then
    return Z_STREAM_ERROR
  -- if (bits == 8) bits = 9;
  if bits == 8 then bits := 9
  -- s = (deflate_state *) ZALLOC(strm, 1, sizeof(deflate_state)); if (s == Z_NULL) return Z_MEM_ERROR;
  zalloc_default strm
  let s ← allocDeflateState
  if s == none then return Z_MEM_ERROR
  initAllocated strm s level method bits memLevel strategy wrap

/-- `int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size)` -/
def deflateInit_ (strm : ZStreamPtr) (level : Int32) (version : ConstCStr) (stream_size : Int32) : M (COrder 4 (CExport Int32)) :=
  deflateInit2_ strm level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY version stream_size

/-- `int ZEXPORT deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)` -/
def deflateSetDictionary (strm : ZStreamPtr) (dictionary : ConstBPtr) (dictLength : UInt32) : M (COrder 7 (CExport Int32)) := do
  let mut dictionary := dictionary
  let mut dictLength := dictLength
  -- if (deflateStateCheck(strm) || dictionary == Z_NULL) return Z_STREAM_ERROR;
  if (← deflateStateCheck strm) != 0 || dictionary == .null then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  let wrap := d.wrap
  -- if (wrap == 2 || (wrap == 1 && s->status != INIT_STATE) || s->lookahead || (wrap == 0 && (long)s->strstart != s->block_start))
  if wrap == 2 || (wrap == 1 && d.status != INIT_STATE) || d.lookahead != 0 ||
      (wrap == 0 && d.strstart.toUInt64.toInt64 != d.block_start) then
    return Z_STREAM_ERROR
  -- if (wrap == 1) strm->adler = adler32(strm->adler, dictionary, dictLength);
  if wrap == 1 then
    let a ← zrd strm (·.adler)
    let r ← Zlib.Adler32.adler32 a dictionary dictLength
    zwr strm (fun z => { z with adler := r })
  -- s->wrap = 0;
  wr s (fun d => { d with wrap := 0 })
  -- if (dictLength >= s->w_size) { ... }
  if dictLength ≥ d.w_size then
    if wrap == 0 then
      CLEAR_HASH s
      wr s (fun d =>
        let d := { d with strstart := 0 }
        let d := { d with block_start := 0 }
        { d with insert := 0 })
    -- dictionary += dictLength - s->w_size; dictLength = s->w_size;
    dictionary ← padd dictionary (dictLength - d.w_size).toNat
    dictLength := d.w_size
  -- avail = strm->avail_in; next = strm->next_in;
  let z ← ldZStream strm
  let avail := z.avail_in
  let next := z.next_in
  -- strm->avail_in = dictLength; strm->next_in = (z_const Bytef *)dictionary;
  zwr strm (fun z =>
    let z := { z with avail_in := dictLength }
    { z with next_in := dictionary })
  fill_window s
  -- while (s->lookahead >= MIN_MATCH) { ... }
  let _ ← cwhile
    (fun (u : Unit) => do pure ((← rd s (·.lookahead)) ≥ MIN_MATCH_u, u))
    (fun (u : Unit) => do
      let d ← ldDeflateState s
      let str : UInt32 := d.strstart                            -- str = s->strstart;
      let n : UInt32 := d.lookahead - (MIN_MATCH_u - 1)         -- n = s->lookahead - (MIN_MATCH-1);
      -- do { UPDATE_HASH(...); s->prev[str & s->w_mask] = s->head[s->ins_h]; s->head[s->ins_h] = (Pos)str; str++; } while (--n);
      let (str, _) ← cdoWhile
        (fun (str, n) => do
          let d ← ldDeflateState s
          UPDATE_HASH s (← cinline (index8 d.window (str + (MIN_MATCH_u - 1)).toNat))
          let d ← ldDeflateState s
          let v ← Ptr.index d.head d.ins_h.toNat
          Ptr.store (← padd d.prev (str &&& d.w_mask).toNat) v
          Ptr.store (← padd d.head d.ins_h.toNat) str.toUInt16
          pure (str + 1, n))
        (fun (str, n) => let n := n - 1; pure (n != 0, (str, n)))
        (str, n)
      -- s->strstart = str; s->lookahead = MIN_MATCH-1; fill_window(s);
      wr s (fun d => { d with strstart := str, lookahead := MIN_MATCH_u - 1 })
      fill_window s
      pure u)
    ()
  -- s->strstart += s->lookahead; s->block_start = (long)s->strstart; s->insert = s->lookahead; s->lookahead = 0;
  wr s (fun d => { d with strstart := d.strstart + d.lookahead })
  wr s (fun d =>
    let d := { d with block_start := d.strstart.toUInt64.toInt64 }
    let d := { d with insert := d.lookahead }
    { d with lookahead := 0 })
  -- s->match_length = s->prev_length = MIN_MATCH-1; s->match_available = 0;
  wr s (fun d =>
    let d := { d with prev_length := MIN_MATCH_u - 1 }
    let d := { d with match_length := MIN_MATCH_u - 1 }
    { d with match_available := 0 })
  -- strm->next_in = next; strm->avail_in = avail; s->wrap = wrap;
  zwr strm (fun z => { z with next_in := next, avail_in := avail })
  wr s (fun d => { d with wrap })
  return Z_OK

/-- `int ZEXPORT deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`; the second component
is `*dictLength` when `hasDictLength` (the pointer is not NULL) and `none` otherwise. -/
def deflateGetDictionary (strm : ZStreamPtr) (dictionary : BPtr) (hasDictLength : Bool) :
    M (Int32 × Option UInt32) := do
  if (← deflateStateCheck strm) != 0 then return (Z_STREAM_ERROR, none)
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  -- len = s->strstart + s->lookahead; if (len > s->w_size) len = s->w_size;
  let mut len : UInt32 := d.strstart + d.lookahead
  if len > d.w_size then len := d.w_size
  -- if (dictionary != Z_NULL && len) zmemcpy(dictionary, s->window + s->strstart + s->lookahead - len, len);
  if dictionary != .null && len != 0 then
    let from_ ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
    memcpyB dictionary (← psub from_ len.toNat) len.toNat
  -- if (dictLength != Z_NULL) *dictLength = len;
  return (Z_OK, if hasDictLength then some len else none)

/-- `int ZEXPORT deflateSetHeader(z_streamp strm, gz_headerp head)` -/
def deflateSetHeader (strm : ZStreamPtr) (head : GzHeaderPtr) : M (COrder 12 (CExport Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  if (← rd s (·.wrap)) != 2 then return Z_STREAM_ERROR
  wr s (fun d => { d with gzhead := head })
  return Z_OK

/-- `int ZEXPORT deflatePending(z_streamp strm, unsigned *pending, int *bits)`; the results are the values stored
through `pending` and `bits` (when the pointer is not NULL). -/
def deflatePending (strm : ZStreamPtr) (hasPending hasBits : Bool) :
    M (Int32 × Option UInt32 × Option Int32) := do
  if (← deflateStateCheck strm) != 0 then return (Z_STREAM_ERROR, none, none)
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  -- if (bits != Z_NULL) *bits = strm->state->bi_valid;
  let bits := if hasBits then some d.bi_valid else none
  if hasPending then
    -- *pending = (unsigned)strm->state->pending;
    let p : UInt32 := d.pending.toUInt32
    -- if (*pending != strm->state->pending) { *pending = (unsigned)-1; return Z_BUF_ERROR; }
    if p.toUInt64 != d.pending then return (Z_BUF_ERROR, some 0xffffffff, bits)
    return (Z_OK, some p, bits)
  return (Z_OK, none, bits)

/-- `int ZEXPORT deflateUsed(z_streamp strm, int *bits)` -/
def deflateUsed (strm : ZStreamPtr) (hasBits : Bool) : M (Int32 × Option Int32) := do
  if (← deflateStateCheck strm) != 0 then return (Z_STREAM_ERROR, none)
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  return (Z_OK, if hasBits then some d.bi_used else none)

/-- `int ZEXPORT deflatePrime(z_streamp strm, int bits, int value)` -/
def deflatePrime (strm : ZStreamPtr) (bits value : Int32) : M (COrder 15 (CExport Int32)) := do
  let mut bits := bits
  let mut value := value
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  -- if (bits < 0 || bits > 16) return Z_BUF_ERROR;
  if bits < 0 || bits > 16 then return Z_BUF_ERROR
  -- if (s->pending_out != s->pending_buf) { ... move partially flushed pending output to buffer start }
  let d ← ldDeflateState s
  if d.pending_out != d.pending_buf then
    -- Bytef *to = s->pending_buf, *from = s->pending_out; ulg n = s->pending; while (n--) *to++ = *from++;
    let _ ← cwhile
      (fun (n, from_, to) => pure (n != 0, (n - 1, from_, to)))
      (fun (n, from_, to) => do
        store8 to (← load8 from_)
        let dst ← padd to 1
        let src ← padd from_ 1
        pure (n, src, dst))
      (d.pending, d.pending_out, d.pending_buf)
    wr s (fun d => { d with pending_out := d.pending_buf })
  -- need = (s->bi_valid + bits) >> 3;
  let d ← ldDeflateState s
  let need : Int32 := (← iadd d.bi_valid bits) >>> 3
  -- if (s->pending_buf_size - s->pending < (ulg)need) return Z_BUF_ERROR;
  if d.pending_buf_size - d.pending < need.toInt64.toUInt64 then return Z_BUF_ERROR
  -- do { ... } while (bits);
  let (_, _) ← cdoWhile
    (fun (bits, value) => do
      let d ← ldDeflateState s
      -- put = Buf_size - s->bi_valid; if (put > bits) put = bits;
      let mut put ← isub Buf_size d.bi_valid
      if put > bits then put := bits
      -- s->bi_buf |= (ush)((value & ((1 << put) - 1)) << s->bi_valid);
      let mask ← isub (← ishl 1 put.toInt) 1
      let sh ← ishl (value &&& mask) d.bi_valid.toInt
      wr s (fun d => { d with bi_buf := d.bi_buf ||| sh.toInt16.toUInt16 })
      -- s->bi_valid += put;
      let bv ← iadd d.bi_valid put
      wr s (fun d => { d with bi_valid := bv })
      -- _tr_flush_bits(s);
      _tr_flush_bits s
      -- value >>= put; bits -= put;
      pure (← isub bits put, value >>> put))
    (fun (bits, value) => pure (bits != 0, (bits, value)))
    (bits, value)
  return Z_OK

/-- `HCRC_UPDATE(beg)`: `if (s->gzhead->hcrc && s->pending > (beg)) strm->adler = crc32_z(strm->adler,
s->pending_buf + (beg), s->pending - (beg));` -/
def HCRC_UPDATE (strm : ZStreamPtr) (s : DeflateStatePtr) (beg : UInt64) : M Unit := do
  let d ← ldDeflateState s
  let gh ← ldGzHeader d.gzhead
  if gh.hcrc != 0 && d.pending > beg then
    let a ← zrd strm (·.adler)
    let r ← crc32_z a (← padd d.pending_buf beg.toNat) (d.pending - beg)
    zwr strm (fun z => { z with adler := r })

/-- State of the loop that copies the gzip `extra` field. -/
structure ExtraS where
  beg : UInt64
  left : UInt64
  ret : Bool

/-- State of the `do { ... } while (val != 0)` loops that copy the gzip name and comment. -/
structure StrS where
  beg : UInt64
  val : Int32
  ret : Bool

/-- The `NAME_STATE` and `COMMENT_STATE` loops of `deflate`: `ulg beg = s->pending; int val; do { if (s->pending ==
s->pending_buf_size) { HCRC_UPDATE(beg); flush_pending(strm); if (s->pending != 0) { s->last_flush = -1; return Z_OK; }
beg = 0; } val = s->gzhead->name[s->gzindex++]; put_byte(s, val); } while (val != 0); HCRC_UPDATE(beg);`
(`sel` selects `name` or `comment`). Returns `true` if the C returns `Z_OK` from inside the loop. -/
def gz_string_loop (strm : ZStreamPtr) (s : DeflateStatePtr) (sel : GzHeader → BPtr) : M Bool := do
  let beg ← rd s (·.pending)
  let st ← cdoWhileBrk
    (fun (st : StrS) => do
      let mut beg := st.beg
      let d ← ldDeflateState s
      if d.pending == d.pending_buf_size then
        HCRC_UPDATE strm s beg
        flush_pending strm
        if (← rd s (·.pending)) != 0 then
          wr s (fun d => { d with last_flush := -1 })
          return .brk { st with ret := true }
        beg := 0
      let d ← ldDeflateState s
      let gh ← ldGzHeader d.gzhead
      -- val = s->gzhead->name[s->gzindex++];
      let base ← cdecl (sel gh)
      let i ← cdecl d.gzindex
      wr s (fun d => { d with gzindex := d.gzindex + 1 })
      let b ← index8 base i.toNat
      put_byte s b
      pure (.next { st with beg, val := b.toUInt32.toInt32 }))
    (fun st => pure (st.val != 0, st))
    { beg, val := 0, ret := false }
  if st.ret then return true
  HCRC_UPDATE strm s st.beg
  return false

/-- `RANK(f)`: `(((f) * 2) - ((f) > 4 ? 9 : 0))` -/
def RANK (f : Int32) : M Int32 := do
  isub (← chk32 (f.toInt * 2)) (if f > 4 then 9 else 0)

namespace Phases

/-- Phase 1 of `deflate`: refusals and the flush of pending output on entry. -/
def entryPhase (strm : ZStreamPtr) (flush : Int32) (k : DeflateStatePtr → M Int32) : M Int32 := do
  -- if (deflateStateCheck(strm) || flush > Z_BLOCK || flush < 0) return Z_STREAM_ERROR;
  if (← deflateStateCheck strm) != 0 || flush > Z_BLOCK || flush < 0 then return Z_STREAM_ERROR
  -- s = strm->state;
  let s ← castDeflateState (← zrd strm (·.state))
  let z ← ldZStream strm
  let d ← ldDeflateState s
  -- if (strm->next_out == Z_NULL || (strm->avail_in != 0 && strm->next_in == Z_NULL) || (s->status == FINISH_STATE && flush != Z_FINISH))
  if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH) then
    return ← ERR_RETURN strm Z_STREAM_ERROR
  -- if (strm->avail_out == 0) ERR_RETURN(strm, Z_BUF_ERROR);
  if z.avail_out == 0 then return ← ERR_RETURN strm Z_BUF_ERROR
  -- old_flush = s->last_flush; s->last_flush = flush;
  let old_flush := d.last_flush
  wr s (fun d => { d with last_flush := flush })
  -- Flush as much pending output as possible
  if d.pending != 0 then
    flush_pending strm
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  else if z.avail_in == 0 then
    if (← cinline (RANK flush)) ≤ (← cinline (RANK old_flush)) && flush != Z_FINISH then
      return ← ERR_RETURN strm Z_BUF_ERROR
  -- if (s->status == FINISH_STATE && strm->avail_in != 0) ERR_RETURN(strm, Z_BUF_ERROR);
  let d ← ldDeflateState s
  let z ← ldZStream strm
  if d.status == FINISH_STATE && z.avail_in != 0 then
    return ← ERR_RETURN strm Z_BUF_ERROR
  k s

/-- Phase 2 of `deflate`: the header states up to the flush on entering `BUSY_STATE`. -/
def headerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (_flush : Int32) (k : M Int32) : M Int32 := do
  -- Write the header
  let d ← ldDeflateState s
  if d.status == INIT_STATE && d.wrap == 0 then
    wr s (fun d => { d with status := BUSY_STATE })
  if (← rd s (·.status)) == INIT_STATE then
    -- zlib header: uInt header = (Z_DEFLATED + ((s->w_bits - 8) << 4)) << 8;
    let d ← ldDeflateState s
    let mut header : UInt32 := ((8 : UInt32) + ((d.w_bits - 8) <<< 4)) <<< 8
    -- level_flags
    let level_flags : UInt32 :=
      if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 0
      else if d.level < 6 then 1
      else if d.level == 6 then 2
      else 3
    header := header ||| (level_flags <<< 6)                  -- header |= (level_flags << 6);
    if d.strstart != 0 then header := header ||| 0x20          -- header |= PRESET_DICT;
    header := header + (31 - (header % 31))                    -- header += 31 - (header % 31);
    putShortMSB s header
    -- Save the adler32 of the preset dictionary:
    if (← rd s (·.strstart)) != 0 then
      let a ← zrd strm (·.adler)
      putShortMSB s (a >>> 16).toUInt32
      let a ← zrd strm (·.adler)
      putShortMSB s (a &&& 0xffff).toUInt32
    -- strm->adler = adler32(0L, Z_NULL, 0); s->status = BUSY_STATE;
    let r ← Zlib.Adler32.adler32 0 (Ptr.null : BPtr) 0
    zwr strm (fun z => { z with adler := r })
    wr s (fun d => { d with status := BUSY_STATE })
    -- Compression must start with an empty pending buffer
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  -- #ifdef GZIP
  if (← rd s (·.status)) == GZIP_STATE then
    -- gzip header: strm->adler = crc32(0L, Z_NULL, 0);
    let r ← crc32 0 (Ptr.null : BPtr) 0
    zwr strm (fun z => { z with adler := r })
    put_byte s 31
    put_byte s 139
    put_byte s 8
    let d ← ldDeflateState s
    -- the XFL byte: s->level == 9 ? 2 : (s->strategy >= Z_HUFFMAN_ONLY || s->level < 2 ? 4 : 0)
    if d.gzhead == none then
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s 0
      put_byte s 0
      let d ← ldDeflateState s
      let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
      put_byte s xfl
      put_byte s OS_CODE.toUInt32.toUInt8
      wr s (fun d => { d with status := BUSY_STATE })
      -- Compression must start with an empty pending buffer
      flush_pending strm
      if (← rd s (·.pending)) != 0 then
        wr s (fun d => { d with last_flush := -1 })
        return Z_OK
    else
      let gh ← ldGzHeader d.gzhead
      -- put_byte(s, (text ? 1 : 0) + (hcrc ? 2 : 0) + (extra == NULL ? 0 : 4) + (name == NULL ? 0 : 8) + (comment == NULL ? 0 : 16));
      -- (each term is a constant, so the sum is at most 31 and cannot overflow)
      put_byte s (((if gh.text != 0 then 1 else 0) + (if gh.hcrc != 0 then 2 else 0) +
        (if gh.extra == .null then 0 else 4) + (if gh.name == .null then 0 else 8) +
        (if gh.comment == .null then 0 else 16) : Nat).toUInt8)
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s (gh.time &&& 0xff).toUInt8
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s ((gh.time >>> 8) &&& 0xff).toUInt8
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s ((gh.time >>> 16) &&& 0xff).toUInt8
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s ((gh.time >>> 24) &&& 0xff).toUInt8
      let d ← ldDeflateState s
      let xfl : UInt8 := if d.level == 9 then 2 else if d.strategy ≥ Z_HUFFMAN_ONLY || d.level < 2 then 4 else 0
      put_byte s xfl
      let gh ← ldGzHeader (← rd s (·.gzhead))
      put_byte s (gh.os &&& 0xff).toUInt32.toUInt8
      let gh ← ldGzHeader (← rd s (·.gzhead))
      if gh.extra != .null then
        let gh ← ldGzHeader (← rd s (·.gzhead))
        put_byte s (gh.extra_len &&& 0xff).toUInt8
        let gh ← ldGzHeader (← rd s (·.gzhead))
        put_byte s ((gh.extra_len >>> 8) &&& 0xff).toUInt8
      let gh ← ldGzHeader (← rd s (·.gzhead))
      if gh.hcrc != 0 then
        -- strm->adler = crc32_z(strm->adler, s->pending_buf, s->pending);
        let d ← ldDeflateState s
        let a ← zrd strm (·.adler)
        let r ← crc32_z a d.pending_buf d.pending
        zwr strm (fun z => { z with adler := r })
      -- s->gzindex = 0; s->status = EXTRA_STATE;
      wr s (fun d => { d with gzindex := 0 })
      wr s (fun d => { d with status := EXTRA_STATE })
  if (← rd s (·.status)) == EXTRA_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.extra != .null then
      -- ulg beg = s->pending; ulg left = (s->gzhead->extra_len & 0xffff) - s->gzindex;
      let st ← cwhileBrk
        (fun (st : ExtraS) => do
          let d ← ldDeflateState s
          pure (d.pending + st.left > d.pending_buf_size, st))
        (fun (st : ExtraS) => do
          let d ← ldDeflateState s
          let gh ← ldGzHeader d.gzhead
          -- ulg copy = s->pending_buf_size - s->pending;
          let copy := d.pending_buf_size - d.pending
          -- zmemcpy(s->pending_buf + s->pending, s->gzhead->extra + s->gzindex, copy);
          memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) copy.toNat
          -- s->pending = s->pending_buf_size; HCRC_UPDATE(beg); s->gzindex += copy;
          wr s (fun d => { d with pending := d.pending_buf_size })
          HCRC_UPDATE strm s st.beg
          wr s (fun d => { d with gzindex := d.gzindex + copy })
          flush_pending strm
          if (← rd s (·.pending)) != 0 then
            wr s (fun d => { d with last_flush := -1 })
            return .brk { st with ret := true }
          -- beg = 0; left -= copy;
          pure (.next { st with beg := 0, left := st.left - copy }))
        { beg := d.pending, left := (gh.extra_len &&& 0xffff).toUInt64 - d.gzindex, ret := false }
      if st.ret then return Z_OK
      -- zmemcpy(s->pending_buf + s->pending, s->gzhead->extra + s->gzindex, left);
      let d ← ldDeflateState s
      let gh ← ldGzHeader d.gzhead
      memcpyB (← padd d.pending_buf d.pending.toNat) (← padd gh.extra d.gzindex.toNat) st.left.toNat
      -- s->pending += left; HCRC_UPDATE(beg); s->gzindex = 0;
      wr s (fun d => { d with pending := d.pending + st.left })
      HCRC_UPDATE strm s st.beg
      wr s (fun d => { d with gzindex := 0 })
    wr s (fun d => { d with status := NAME_STATE })
  if (← rd s (·.status)) == NAME_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.name != .null then
      if (← gz_string_loop strm s (·.name)) then return Z_OK
      wr s (fun d => { d with gzindex := 0 })
    wr s (fun d => { d with status := COMMENT_STATE })
  if (← rd s (·.status)) == COMMENT_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.comment != .null then
      if (← gz_string_loop strm s (·.comment)) then return Z_OK
    wr s (fun d => { d with status := HCRC_STATE })
  if (← rd s (·.status)) == HCRC_STATE then
    let d ← ldDeflateState s
    let gh ← ldGzHeader d.gzhead
    if gh.hcrc != 0 then
      -- if (s->pending + 2 > s->pending_buf_size) { flush_pending(strm); if (s->pending != 0) {...return Z_OK;} }
      if d.pending + 2 > d.pending_buf_size then
        flush_pending strm
        if (← rd s (·.pending)) != 0 then
          wr s (fun d => { d with last_flush := -1 })
          return Z_OK
      let a ← zrd strm (·.adler)
      put_byte s (a &&& 0xff).toUInt8
      let a ← zrd strm (·.adler)
      put_byte s ((a >>> 8) &&& 0xff).toUInt8
      let r ← crc32 0 (Ptr.null : BPtr) 0
      zwr strm (fun z => { z with adler := r })
    wr s (fun d => { d with status := BUSY_STATE })
    -- Compression must start with an empty pending buffer
    flush_pending strm
    if (← rd s (·.pending)) != 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  k

/-- Phase 3 of `deflate`: the strategy and the flush markers after it. -/
def strategyPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) (k : M Int32) : M Int32 := do
  -- Start a new block or continue the current one.
  let d ← ldDeflateState s
  if (← zrd strm (·.avail_in)) != 0 || d.lookahead != 0 || (flush != Z_NO_FLUSH && d.status != FINISH_STATE) then
    -- bstate = s->level == 0 ? deflate_stored(s, flush) : s->strategy == Z_HUFFMAN_ONLY ? deflate_huff(s, flush) :
    --          s->strategy == Z_RLE ? deflate_rle(s, flush) : (*(configuration_table[s->level].func))(s, flush);
    let bstate : block_state ←
      if d.level == 0 then deflate_stored s flush
      else if d.strategy == Z_HUFFMAN_ONLY then deflate_huff s flush
      else if d.strategy == Z_RLE then deflate_rle s flush
      else do
        match (← config_at d.level).func with
        | .stored => deflate_stored s flush
        | .fast => deflate_fast s flush
        | .slow => deflate_slow s flush
    -- if (bstate == finish_started || bstate == finish_done) s->status = FINISH_STATE;
    if bstate == finish_started || bstate == finish_done then
      wr s (fun d => { d with status := FINISH_STATE })
    -- if (bstate == need_more || bstate == finish_started) { if (strm->avail_out == 0) s->last_flush = -1; return Z_OK; }
    if bstate == need_more || bstate == finish_started then
      if (← zrd strm (·.avail_out)) == 0 then
        wr s (fun d => { d with last_flush := -1 })
      return Z_OK
    if bstate == block_done then
      if flush == Z_PARTIAL_FLUSH then
        _tr_align s
      else if flush != Z_BLOCK then
        -- FULL_FLUSH or SYNC_FLUSH
        _tr_stored_block s (Ptr.null : BPtr) 0 0
        if flush == Z_FULL_FLUSH then
          CLEAR_HASH s                                        -- forget history
          if (← rd s (·.lookahead)) == 0 then
            wr s (fun d => { d with strstart := 0 })
            wr s (fun d => { d with block_start := 0 })
            wr s (fun d => { d with insert := 0 })
      flush_pending strm
      if (← zrd strm (·.avail_out)) == 0 then
        wr s (fun d => { d with last_flush := -1 })
        return Z_OK
  k

/-- Phase 4 of `deflate`: the trailer. -/
def trailerPhase (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) : M Int32 := do
  -- if (flush != Z_FINISH) return Z_OK; if (s->wrap <= 0) return Z_STREAM_END;
  if flush != Z_FINISH then return Z_OK
  if (← rd s (·.wrap)) ≤ 0 then return Z_STREAM_END
  -- Write the trailer
  if (← rd s (·.wrap)) == 2 then
    let a ← zrd strm (·.adler)
    put_byte s (a &&& 0xff).toUInt8
    let a ← zrd strm (·.adler)
    put_byte s ((a >>> 8) &&& 0xff).toUInt8
    let a ← zrd strm (·.adler)
    put_byte s ((a >>> 16) &&& 0xff).toUInt8
    let a ← zrd strm (·.adler)
    put_byte s ((a >>> 24) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s (t &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s ((t >>> 8) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s ((t >>> 16) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s ((t >>> 24) &&& 0xff).toUInt8
  else
    let a ← zrd strm (·.adler)
    putShortMSB s (a >>> 16).toUInt32
    let a ← zrd strm (·.adler)
    putShortMSB s (a &&& 0xffff).toUInt32
  flush_pending strm
  -- if (s->wrap > 0) s->wrap = -s->wrap; /* write the trailer only once! */
  let w ← rd s (·.wrap)
  if w > 0 then
    let nw ← ineg w
    wr s (fun d => { d with wrap := nw })
  -- return s->pending != 0 ? Z_OK : Z_STREAM_END;
  return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END

end Phases

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` -/
def deflate (strm : ZStreamPtr) (flush : Int32) : M (COrder 22 (CExport Int32)) :=
  Phases.entryPhase strm flush fun s =>
    Phases.headerPhase strm s flush (Phases.strategyPhase strm s flush (Phases.trailerPhase strm s flush))

/-- `int ZEXPORT deflateParams(z_streamp strm, int level, int strategy)` -/
def deflateParams (strm : ZStreamPtr) (level strategy : Int32) : M (COrder 16 (CExport Int32)) := do
  let mut level := level
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  -- if (level == Z_DEFAULT_COMPRESSION) level = 6;
  if level == Z_DEFAULT_COMPRESSION then level := 6
  -- if (level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED) return Z_STREAM_ERROR;
  if level < 0 || level > 9 || strategy < 0 || strategy > Z_FIXED then return Z_STREAM_ERROR
  -- func = configuration_table[s->level].func;
  let d ← ldDeflateState s
  let func := (← config_at d.level).func
  -- if ((strategy != s->strategy || func != configuration_table[level].func) && s->last_flush != -2) { ... }
  let differs ← if strategy != d.strategy then pure true else do
    pure (func != (← config_at level).func)
  if differs && d.last_flush != -2 then
    -- Flush the last buffer:
    let err ← deflate strm Z_BLOCK
    if err == Z_STREAM_ERROR then return err
    -- if (strm->avail_in || (s->strstart - s->block_start) + s->lookahead) return Z_BUF_ERROR;
    if (← zrd strm (·.avail_in)) != 0 then return Z_BUF_ERROR
    let d ← ldDeflateState s
    let diff ← lsub d.strstart.toUInt64.toInt64 d.block_start
    let tot ← ladd diff d.lookahead.toUInt64.toInt64
    if tot != 0 then return Z_BUF_ERROR
  -- if (s->level != level) { ... }
  let d ← ldDeflateState s
  if d.level != level then
    if d.level == 0 && d.«matches» != 0 then
      if d.«matches» == 1 then slide_hash s else CLEAR_HASH s
      wr s (fun d => { d with «matches» := 0 })
    -- s->level = level; s->max_lazy_match = ...; good_match; nice_match; max_chain_length
    wr s (fun d => { d with level := level })
    let c ← config_at level
    wr s (fun d =>
      let d := { d with max_lazy_match := c.max_lazy.toUInt32 }
      let d := { d with good_match := c.good_length.toUInt32 }
      let d := { d with nice_match := c.nice_length.toUInt32.toInt32 }
      { d with max_chain_length := c.max_chain.toUInt32 })
  -- s->strategy = strategy;
  wr s (fun d => { d with strategy })
  return Z_OK

/-- `int ZEXPORT deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain)` -/
def deflateTune (strm : ZStreamPtr) (good_length max_lazy nice_length max_chain : Int32) : M (COrder 17 (CExport Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  wr s (fun d =>
    let d := { d with good_match := good_length.toUInt32 }
    let d := { d with max_lazy_match := max_lazy.toUInt32 }
    let d := { d with nice_match := nice_length }
    { d with max_chain_length := max_chain.toUInt32 })
  return Z_OK

/-- `z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen)` -/
def deflateBound_z (strm : ZStreamPtr) (sourceLen : UInt64) : M (COrder 18 (CExport UInt64)) := do
  -- fixedlen = sourceLen + (sourceLen >> 3) + (sourceLen >> 8) + (sourceLen >> 9) + 4;
  let mut fixedlen : UInt64 := sourceLen + (sourceLen >>> 3) + (sourceLen >>> 8) + (sourceLen >>> 9) + 4
  if fixedlen < sourceLen then fixedlen := 0xffffffffffffffff
  -- storelen = sourceLen + (sourceLen >> 5) + (sourceLen >> 7) + (sourceLen >> 11) + 7;
  let mut storelen : UInt64 := sourceLen + (sourceLen >>> 5) + (sourceLen >>> 7) + (sourceLen >>> 11) + 7
  if storelen < sourceLen then storelen := 0xffffffffffffffff
  -- if (deflateStateCheck(strm)) { bound = max(fixedlen, storelen); return bound + 18 < bound ? -1 : bound + 18; }
  if (← deflateStateCheck strm) != 0 then
    let bound := if fixedlen > storelen then fixedlen else storelen
    return if bound + 18 < bound then 0xffffffffffffffff else bound + 18
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  -- switch (s->wrap < 0 ? -s->wrap : s->wrap)
  let w ← if d.wrap < 0 then ineg d.wrap else pure d.wrap
  let mut wraplen : UInt64 := 18
  if w == 0 then
    wraplen := 0                                                 -- raw deflate
  else if w == 1 then
    wraplen := 6 + (if d.strstart != 0 then 4 else 0)           -- zlib wrapper
  else if w == 2 then
    wraplen := 18                                                -- gzip wrapper
    if d.gzhead != none then
      let gh ← ldGzHeader d.gzhead
      -- /* gzip writes only the low 16 bits of the extra length */
      -- if (s->gzhead->extra != Z_NULL) wraplen += 2 + (z_size_t)(s->gzhead->extra_len & 0xffff);   (patch 0007)
      if gh.extra != .null then wraplen := wraplen + ((2 : UInt64) + (gh.extra_len &&& 0xffff).toUInt64)
      -- str = s->gzhead->name; if (str != Z_NULL) do { wraplen++; } while (*str++);
      if gh.name != .null then
        let (wl, _) ← cdoWhile
          (fun (wl, str) => pure (wl + 1, str))
          (fun (wl, str) => do
            let b ← load8 str
            pure (b != 0, (wl, ← padd str 1)))
          (wraplen, gh.name)
        wraplen := wl
      if gh.comment != .null then
        let (wl, _) ← cdoWhile
          (fun (wl, str) => pure (wl + 1, str))
          (fun (wl, str) => do
            let b ← load8 str
            pure (b != 0, (wl, ← padd str 1)))
          (wraplen, gh.comment)
        wraplen := wl
      -- if (s->gzhead->hcrc) wraplen += 2;
      if gh.hcrc != 0 then wraplen := wraplen + 2
  else
    wraplen := 18                                                -- for compiler happiness
  -- if (s->w_bits != 15 || s->hash_bits != 8 + 7 || s->strategy == Z_FIXED) { ... }   (patch 0006)
  if d.w_bits != 15 || d.hash_bits != 15 || d.strategy == Z_FIXED then
    let bound := if d.w_bits ≤ d.hash_bits && d.level != 0 then fixedlen else storelen
    return if bound + wraplen < bound then 0xffffffffffffffff else bound + wraplen
  -- bound = sourceLen + (sourceLen >> 12) + (sourceLen >> 14) + (sourceLen >> 25) + 13 - 6 + wraplen;
  let bound : UInt64 := sourceLen + (sourceLen >>> 12) + (sourceLen >>> 14) + (sourceLen >>> 25) + 13 - 6 + wraplen
  return if bound < sourceLen then 0xffffffffffffffff else bound

/-- `uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen)` -/
def deflateBound (strm : ZStreamPtr) (sourceLen : UInt64) : M (COrder 19 (CExport UInt64)) := do
  let bound ← deflateBound_z strm sourceLen
  -- return (uLong)bound != bound ? (uLong)-1 : (uLong)bound;   (uLong and z_size_t are both 64 bits)
  return bound

/-- `int ZEXPORT deflateCopy(z_streamp dest, z_streamp source)` (the `MAXSEG_64K` branch is not compiled; `LIT_MEM`
is undefined). -/
def deflateCopy (dest source : ZStreamPtr) : M (COrder 24 (CExport Int32)) := do
  -- if (dest == Z_NULL) return Z_STREAM_ERROR;
  if dest == none then return Z_STREAM_ERROR
  -- if (deflateStateCheck(source)) { dest->state = Z_NULL; return Z_STREAM_ERROR; }
  if (← deflateStateCheck source) != 0 then
    zwr dest (fun z => { z with state := none })
    return Z_STREAM_ERROR
  -- ss = source->state;
  let ss ← castDeflateState (← zrd source (·.state))
  -- ds = (deflate_state *) ZALLOC(source, 1, sizeof(deflate_state));
  zalloc_default source
  let ds ← allocDeflateState
  if ds == none then
    zwr dest (fun z => { z with state := none })
    return Z_MEM_ERROR
  -- zmemcpy(ds, ss, sizeof(deflate_state));
  copyDeflateState ds ss
  -- ds->window = ZALLOC(source, ds->w_size, 2*sizeof(Byte)); ds->prev = ...; ds->head = ...; ds->pending_buf = ...
  let dd ← ldDeflateState ds
  let window ← ZALLOC_bytes source dd.w_size 2
  wr ds (fun d => { d with window })
  let prev ← ZALLOC_words source (← cinline (rd ds (·.w_size)))
  wr ds (fun d => { d with prev })
  let head ← ZALLOC_words source (← cinline (rd ds (·.hash_size)))
  wr ds (fun d => { d with head })
  let pending_buf ← ZALLOC_bytes source (← cinline (rd ds (·.lit_bufsize))) 4
  wr ds (fun d => { d with pending_buf })
  let buffers ← ldDeflateState ds
  if buffers.window == .null || buffers.prev == .null || buffers.head == .null || buffers.pending_buf == .null then
    if buffers.pending_buf != .null then ZFREE_bytes source buffers.pending_buf
    let head ← rd ds (·.head)
    if head != .null then ZFREE_words source head
    let prev ← rd ds (·.prev)
    if prev != .null then ZFREE_words source prev
    let window ← rd ds (·.window)
    if window != .null then ZFREE_bytes source window
    zfree_default source
    freeDeflateState ds
    zwr dest (fun z => { z with state := none })
    return Z_MEM_ERROR
  -- zmemcpy(dest, source, sizeof(z_stream)); dest->state = (struct internal_state FAR *) ds; ds->strm = dest;
  -- (memcpy of overlapping objects is undefined when dest == source)
  copyZStream dest source
  zwr dest (fun z => { z with state := StateRef.ofDeflateState ds })
  wr ds (fun d => { d with strm := dest })
  -- zmemcpy(ds->window, ss->window, ss->high_water);
  let sd ← ldDeflateState ss
  let buffers ← ldDeflateState ds
  memcpyB buffers.window sd.window sd.high_water.toNat
  -- prev is an array of 16-bit Pos values; Ptr.memcpy counts elements.
  let dstPrev ← rd ds (·.prev)
  let srcPrev ← rd ss (·.prev)
  Ptr.memcpy dstPrev srcPrev (if sd.slid != 0 || sd.strstart - sd.insert > buffers.w_size
    then buffers.w_size else sd.strstart - sd.insert).toNat
  Ptr.memcpy (← rd ds (·.head)) sd.head buffers.hash_size.toNat
  -- Relocate pointers inside the destination pending buffer, then copy their live bytes.
  let off ← Ptr.diff sd.pending_out sd.pending_buf
  let pending_out ← Ptr.add buffers.pending_buf off.toInt
  wr ds (fun d => { d with pending_out })
  memcpyB (← rd ds (·.pending_out)) sd.pending_out sd.pending.toNat
  let sym_buf ← padd (← rd ds (·.pending_buf)) buffers.lit_bufsize.toNat
  wr ds (fun d => { d with sym_buf })
  memcpyB (← rd ds (·.sym_buf)) sd.sym_buf sd.sym_next.toNat
  -- ds->l_desc.dyn_tree = ds->dyn_ltree; ds->d_desc.dyn_tree = ds->dyn_dtree; ds->bl_desc.dyn_tree = ds->bl_tree;
  match ds with
  | none => ub "null deflate_state"
  | some (.tab id) =>
    wr ds (fun d => { d with
      l_desc := { d.l_desc with dyn_tree := .ref (.dstate_dyn_ltree id) 0 },
      d_desc := { d.d_desc with dyn_tree := .ref (.dstate_dyn_dtree id) 0 },
      bl_desc := { d.bl_desc with dyn_tree := .ref (.dstate_bl_tree id) 0 } })
  return Z_OK

def deflateGetDictionary_c (strm : ZStreamPtr) (dictionary : BPtr) (dictLength : PtrU32) :
    M (COrder 8 (CExportAs "deflateGetDictionary" Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  let d ← ldDeflateState s
  -- len = s->strstart + s->lookahead; if (len > s->w_size) len = s->w_size;
  let mut len : UInt32 := d.strstart + d.lookahead
  if len > d.w_size then len := d.w_size
  -- if (dictionary != Z_NULL && len) zmemcpy(dictionary, s->window + s->strstart + s->lookahead - len, len);
  if dictionary != .null && len != 0 then
    let from_ ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
    memcpyB dictionary (← psub from_ len.toNat) len.toNat
  if dictLength != .null then storeU32 dictLength len
  return Z_OK

def deflatePending_c (strm : ZStreamPtr) (pending : PtrU32) (bits : OutInt32) :
    M (COrder 13 (CExportAs "deflatePending" Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  if bits != .null then
    let s ← castDeflateState (← zrd strm (·.state))
    storeI32 bits (← rd s (·.bi_valid))
  if pending != .null then
    let s ← castDeflateState (← zrd strm (·.state))
    storeU32 pending (← rd s (·.pending)).toUInt32
    let reported ← loadU32 pending
    let s ← castDeflateState (← zrd strm (·.state))
    if reported.toUInt64 != (← rd s (·.pending)) then
      storeU32 pending 0xffffffff
      return Z_BUF_ERROR
  return Z_OK

def deflateUsed_c (strm : ZStreamPtr) (bits : OutInt32) : M (COrder 14 (CExportAs "deflateUsed" Int32)) := do
  if (← deflateStateCheck strm) != 0 then return Z_STREAM_ERROR
  if bits != .null then
    let s ← castDeflateState (← zrd strm (·.state))
    storeI32 bits (← rd s (·.bi_used))
  return Z_OK

end Zlib.Deflate
