import ZlibF.Zlib.«inflate.c»

/-!
# infback.c — faithful translation

Source: `infback.c` of the verified source, default x86_64 Linux build (same configuration as `inflate.c.lean`; read its
header first: the registers, the monad `X`, `goto inf_leave` as `throw Ex.leave`, the loops).

## The call-backs

`inflateBack` takes the caller's functions as parameters (they are caller code, not library code):

* `inflateBack` is the value-in/value-out interface used by the existing callback safety protocol.
* `inflateBack_c` passes the address of its local `next` to the input callback. The address
  stays live through all input and output callbacks of this activation. The decoder publishes
  its current `next` before each callback and reads it back afterwards. Nested activations
  share the caller's live pointer variables and introduce their own distinct local.
* Both interfaces run the same mode dispatch on the shared zlib heap.

## Other decisions

* `inflateBackInit_` does **not** zero the state: the record is `allocInflateState`, arbitrary integers and null
  pointers, and only the fields the C writes are written.
* `ret` is not initialised in the C before `for (;;)`; it is set before every `goto inf_leave`. It starts as `0` here.
-/

namespace Zlib.Infback
open C
open Zlib.Crc32 (crc32)
open Zlib.Inffast (inflate_fast)
open Zlib.Inftrees (inflate_table inflate_fixed)
open Zlib.Inflate (X Ex IL Stop xwhile xwhileBrk xdoWhile xloopBrk shl32 shr32 shl64 u2i i2u chkI32 BITS DROPBITS BYTEBITS
  INITBITS LOAD RESTORE rdS wrS rdZ wrZ lensP workP codesP orderAt setMsg setMode ZALLOCS ZFREES)

/-- `in_func`: `unsigned (*)(void FAR *, z_const unsigned char FAR * FAR *)`; see the file comment. -/
abbrev InCb := BPtr → BPtr → M (UInt32 × BPtr)
/-- `out_func`: `int (*)(void FAR *, unsigned char FAR *, unsigned)` -/
abbrev OutCb := BPtr → BPtr → UInt32 → M Int32

/-- What `inflateBack()` and its macros share. -/
structure BCtx where
  strm : ZStreamPtr
  st : InflateStatePtr
  inCb : InCb
  inDesc : BPtr
  outCb : OutCb
  outDesc : BPtr

/-- Operations used by the shared decoder at the two calls into caller code. -/
structure DecoderCtx where
  strm : ZStreamPtr
  st : InflateStatePtr
  input : BPtr → X (UInt32 × BPtr)
  output : BPtr → UInt32 → X Int32

instance : Coe BCtx DecoderCtx where
  coe c := { strm := c.strm, st := c.st, input := fun next => liftM (c.inCb c.inDesc next),
             output := fun buf len => liftM (c.outCb c.outDesc buf len) }

/-- The C input callback receives `&next`. The output callback can access any
    live pointer variable retained by caller code as well as the ordinary heap. -/
abbrev CInCb := VoidPtr → BPtrCell → PointerLocalM UInt32
abbrev COutCb := VoidPtr → BPtr → UInt32 → PointerLocalM Int32

/-- Give a value-style input callback the C ABI, writing its returned pointer
    through the supplied address. -/
def adaptInput (input : InCb) : CInCb := fun desc cell => do
  let (n, p) ← input desc (← cell.read)
  cell.write p
  return n

/-- A value-style output callback operates on the ordinary C heap. -/
def adaptOutput (output : OutCb) : COutCb := fun desc buf len =>
  liftM (output desc buf len)

/-- Publish the current register to its addressed variable for the duration of
    a call, then import the value that caller code left in that variable. -/
def callWithNext (cell : BPtrCell) (next : BPtr) (callback : PointerLocalM α) :
    PointerLocalM (α × BPtr) := do
  cell.write next
  let result ← callback
  return (result, ← cell.read)

/-- Run a pointer-local action with the current decoder registers. -/
def inDecoder (action : PointerLocalM α) : X α := do
  let l ← get
  let (value, cells) ← action.run l.pointerLocals
  set { l with pointerLocals := cells }
  return value

/-- Callback operations for the C entry with an addressable input cursor. -/
def addressedCtx (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (input : CInCb) (inDesc : BPtr) (output : COutCb) (outDesc : BPtr) : DecoderCtx where
  strm := strm
  st := st
  input next := inDecoder (callWithNext cell next (input inDesc cell))
  output buf len := do
    let (rc, next) ← inDecoder (callWithNext cell (← get).next (output outDesc buf len))
    modify fun l => { l with next }
    return rc

/-- `int ZEXPORT inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window, const char *version,
int stream_size)` -/
def inflateBackInit_ (strm : ZStreamPtr) (windowBits : Int32) (window : BPtr) (version : ConstCStr) (stream_size : Int32) :
    M (CExport Int32) := do
  -- if (version == Z_NULL || version[0] != ZLIB_VERSION[0] || stream_size != (int)(sizeof(z_stream))) return Z_VERSION_ERROR;
  if version == .null then return Z_VERSION_ERROR
  if (← index8 version 0) != literalFirstByte ZLIB_VERSION then return Z_VERSION_ERROR
  if stream_size != 112 then return Z_VERSION_ERROR
  -- if (strm == Z_NULL || window == Z_NULL || windowBits < 8 || windowBits > 15) return Z_STREAM_ERROR;
  if strm == none || window == .null || windowBits < 8 || windowBits > 15 then return Z_STREAM_ERROR
  -- strm->msg = Z_NULL;
  wrZ strm fun z => { z with msg := .null }
  -- if (strm->zalloc == (alloc_func)0) { strm->zalloc = zcalloc; strm->opaque = (voidpf)0; }
  if (← rdZ strm (·.zalloc)) == .null then
    wrZ strm fun z => { z with zalloc := .fn "zcalloc", «opaque» := .null }
  -- if (strm->zfree == (free_func)0) strm->zfree = zcfree;
  if (← rdZ strm (·.zfree)) == .null then
    wrZ strm fun z => { z with zfree := .fn "zcfree" }
  -- state = (struct inflate_state FAR *)ZALLOC(strm, 1, sizeof(struct inflate_state));   (not zeroed)
  let state ← ZALLOCS strm
  -- if (state == Z_NULL) return Z_MEM_ERROR;
  if state == none then return Z_MEM_ERROR
  -- strm->state = (struct internal_state FAR *)state;
  wrZ strm fun z => { z with state := StateRef.ofInflateState state }
  -- state->dmax = 32768U; state->wbits = (uInt)windowBits; state->wsize = 1U << windowBits;
  wrS state fun s => { s with dmax := 32768 }
  wrS state fun s => { s with wbits := i2u windowBits }
  let ws ← shl32 1 (i2u windowBits)
  wrS state fun s => { s with wsize := ws }
  -- state->window = window; state->wnext = 0; state->whave = 0; state->sane = 1;
  wrS state fun s => { s with window }
  wrS state fun s => { s with wnext := 0 }
  wrS state fun s => { s with whave := 0 }
  wrS state fun s => { s with sane := 1 }
  return Z_OK

/-! ## The macros of `infback.c` that differ from `inflate.c` -/

/-- `PULL()`: calls the caller's `in` when `have == 0`; `goto inf_leave` with `next = NULL`, `ret = Z_BUF_ERROR` if it
returns 0. -/
def PULL (c : DecoderCtx) : X Unit := do
  let l ← get
  if l.have_ == 0 then
    -- have = in(in_desc, &next);
    let (h, nx) ← c.input l.next
    let l ← get
    set { l with have_ := h, next := nx }
    if h == 0 then
      -- next = Z_NULL; ret = Z_BUF_ERROR; goto inf_leave;
      set { l with have_ := h, next := .null, ret := Z_BUF_ERROR }
      throw Ex.leave

/-- `PULLBYTE()` -/
def PULLBYTE (c : DecoderCtx) : X Unit := do
  PULL c
  Zlib.Inflate.absorbInputByte

/-- `NEEDBITS(n)` -/
def NEEDBITS (c : DecoderCtx) (n : UInt32) : X Unit :=
  xwhile (do return (← get).bits < n) (PULLBYTE c)

/-- `NEEDBITS(state->extra)` evaluates the field each time the C macro tests its loop condition. -/
def needExtra (c : DecoderCtx) : X Unit :=
  xwhile (do return (← get).bits < (← rdS c.st (·.extra))) (PULLBYTE c)

/-- `ROOM()`: when the window is full, hand it to `out`. -/
def ROOM (c : DecoderCtx) : X Unit := do
  let l ← get
  if l.left == 0 then
    -- put = state->window; left = state->wsize; state->whave = left;
    let s ← ldInflateState c.st
    set { l with put := s.window, left := s.wsize }
    wrS c.st fun s => { s with whave := s.wsize }
    -- if (out(out_desc, put, left)) { ret = Z_BUF_ERROR; goto inf_leave; }
    if (← c.output s.window s.wsize) != 0 then
      modify fun l => { l with ret := Z_BUF_ERROR }
      throw Ex.leave

/-- `strm->msg = "..."; state->mode = BAD;` -/
def badMode (c : DecoderCtx) (msg : String) : M Unit := do
  setMsg c.strm msg
  setMode c.st BAD

/-- `for (;;) { here = TABLE[BITS(bitsOfTable)]; if ((unsigned)(here.bits) <= bits) break; PULLBYTE(); }` -/
def lookup1 (c : DecoderCtx) (dist : Bool) : X Unit :=
  Zlib.Inflate.lookupRoot c.st dist (PULLBYTE c)

/-- `for (;;) { here = TABLE[last.val + (BITS(last.bits + last.op) >> last.bits)]; if ((unsigned)(last.bits + here.bits) <= bits) break; PULLBYTE(); }` -/
def lookup2 (c : DecoderCtx) (dist : Bool) : X Unit :=
  Zlib.Inflate.lookupLink c.st dist (PULLBYTE c)

/-! ## The modes -/

/-- This case is entered both by dispatch and by falling through from TABLE.
    In Lean both paths execute the same action. -/
@[inline] def sharedCase (action : X Unit) : X Unit := action

/-- Output the literal after ROOM has returned, using the current length. -/
@[reducible, inline] def emitLiteral (st : InflateStatePtr) : X Unit := do
  let l ← get
  store8 l.put (← ldInflateState st).length.toUInt8
  let p ← l.put.add 1
  set { l with put := p, left := l.left - 1 }

/-- Add the extra bits to the decoded length or distance. The callback can run inside needExtra. -/
def extendExtra (c : DecoderCtx) (dist : Bool) : X Unit := do
  let ex ← rdS c.st (·.extra)
  if ex != 0 then
    needExtra c
    let b ← BITS (← rdS c.st (·.extra))
    if dist then wrS c.st fun s => { s with offset := s.offset + b }
    else wrS c.st fun s => { s with length := s.length + b }
    DROPBITS (← rdS c.st (·.extra))

/-- Copy the match through the current output window, including ROOM at each new segment. -/
def backMatch (c : DecoderCtx) : X Unit := do
  xdoWhile
    (do
      ROOM c
      let s ← ldInflateState c.st
      let l ← get
      -- copy = state->wsize - state->offset;
      let copy := s.wsize - s.offset
      -- if (copy < left) { from = put + copy; copy = left - copy; } else { from = put - state->offset; copy = left; }
      let (from_, copy) ← if copy < l.left then do
          pure (← l.put.add (copy.toNat : Int), l.left - copy)
        else do
          pure (← l.put.add (-(s.offset.toNat : Int)), l.left)
      -- if (copy > state->length) copy = state->length;
      let copy := if copy > s.length then s.length else copy
      -- state->length -= copy; left -= copy;
      wrS c.st fun s => { s with length := s.length - copy }
      set { l with copy := copy, from_ := from_, left := l.left - copy }
      Zlib.Inflate.copyMatchBytes)
    (do return (← rdS c.st (·.length)) != 0)

/-- `case LEN:` -/
def back_LEN (c : DecoderCtx) : X Unit := do
  let l ← get
  -- if (have >= 6 && left >= 258) { RESTORE(); inflate_fast(strm, state->wsize); LOAD(); break; }
  if l.have_ >= 6 && l.left >= 258 then
    RESTORE c.strm c.st
    inflate_fast c.strm (← rdS c.st (·.wsize))
    LOAD c.strm c.st
    return
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    DROPBITS (← get).last.bits.toUInt32
  -- DROPBITS(here.bits); state->length = (unsigned)here.val;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  wrS c.st fun s => { s with length := here.val.toUInt32 }
  -- if (here.op == 0) { ROOM(); *put++ = (unsigned char)(state->length); left--; state->mode = LEN; break; }
  if here.op == 0 then
    ROOM c
    emitLiteral c.st
    setMode c.st LEN
    return
  -- if (here.op & 32) { state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    setMode c.st TYPE
    return
  -- if (here.op & 64) { "invalid literal/length code"; BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; if (state->extra != 0) { NEEDBITS; length += BITS(extra); DROPBITS(extra); }
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15 }
  extendExtra c false
  -- get distance code
  lookup1 c true
  let here := (← get).here
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    DROPBITS (← get).last.bits.toUInt32
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  -- if (here.op & 64) { "invalid distance code"; BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15;
  wrS c.st fun s => { s with offset := here.val.toUInt32 }
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15 }
  extendExtra c true
  -- if (state->offset > state->wsize - (state->whave < state->wsize ? left : 0)) { "invalid distance too far back"; BAD; break; }
  let s ← ldInflateState c.st
  let l ← get
  if s.offset > s.wsize - (if s.whave < s.wsize then l.left else 0) then
    badMode c "invalid distance too far back"
    return
  -- do { ROOM(); copy = state->wsize - state->offset; ...; do { *put++ = *from++; } while (--copy); } while (state->length != 0);
  backMatch c

/-- The callback decoder uses the same length permutation as the ordinary decoder. -/
abbrev storeOrderedLength := Zlib.Inflate.storeOrderedLength

abbrev appendCurrentCode := Zlib.Inflate.appendCurrentCode
abbrev setPreviousLength := Zlib.Inflate.setPreviousLength
abbrev setRepeatCount := Zlib.Inflate.setRepeatCount

/-- `case TABLE:` (falls through into `LEN`) -/
def back_TABLE (c : DecoderCtx) : X Unit := do
  NEEDBITS c 14
  let b ← BITS 5
  wrS c.st fun s => { s with nlen := b + 257 }
  DROPBITS 5
  let b ← BITS 5
  wrS c.st fun s => { s with ndist := b + 1 }
  DROPBITS 5
  let b ← BITS 4
  wrS c.st fun s => { s with ncode := b + 4 }
  DROPBITS 4
  -- if (state->nlen > 286 || state->ndist > 30) { "too many length or distance symbols"; BAD; break; }
  let s ← ldInflateState c.st
  if s.nlen > 286 || s.ndist > 30 then
    badMode c "too many length or distance symbols"
    return
  -- state->have = 0; while (state->have < state->ncode) { NEEDBITS(3); lens[order[have++]] = BITS(3); DROPBITS(3); }
  wrS c.st fun s => { s with «have» := 0 }
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < s.ncode)
    (do
      NEEDBITS c 3
      storeOrderedLength c.st (do return (← BITS 3).toUInt16)
      DROPBITS 3)
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < 19)
    (storeOrderedLength c.st (pure 0))
  -- state->next = state->codes; state->lencode = (code const FAR *)(state->next); state->lenbits = 7;
  wrS c.st fun s =>
    let s := { s with next := codesP c.st }
    let s := { s with lencode := s.next }
    { s with lenbits := 7 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid code lengths set"
    return
  -- state->have = 0; while (state->have < state->nlen + state->ndist) { ... }
  wrS c.st fun s => { s with «have» := 0 }
  Zlib.Inflate.readCodeLengths c.st (lookup1 c false) (NEEDBITS c) (badMode c "invalid bit length repeat")
  -- if (state->mode == BAD) break;
  if (← rdS c.st (·.mode)) == BAD then return
  -- if (state->lens[256] == 0) { "invalid code -- missing end-of-block"; BAD; break; }
  if (← Ptr.index (lensP c.st) 256) == (0 : UInt16) then
    badMode c "invalid code -- missing end-of-block"
    return
  wrS c.st fun s =>
    let s := { s with next := codesP c.st }
    let s := { s with lencode := s.next }
    { s with lenbits := 10 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table LENS (lensP c.st) s.nlen s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid literal/lengths set"
    return
  wrS c.st fun s => { s with distcode := s.next, distbits := 8 }
  let s ← ldInflateState c.st
  let (r, nx, db) ← inflate_table DISTS (← (lensP c.st).add (s.nlen.toNat : Int)) s.ndist s.next s.distbits (workP c.st)
  wrS c.st fun s => { s with next := nx, distbits := db }
  modify fun l => { l with ret := r }
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN; /* fallthrough */
  setMode c.st LEN
  sharedCase (back_LEN c)

/-- Move the available input of a stored block to the output window, then
    advance the two cursors and the remaining lengths. -/
@[reducible, inline] def copyStoredInput (st : InflateStatePtr) : X Unit := do
  let l ← get
  let mut copy := l.copy
  if copy > l.have_ then copy := l.have_
  if copy > l.left then copy := l.left
  memcpyB l.put l.next copy.toNat
  let nx ← l.next.add (copy.toNat : Int)
  let pt ← l.put.add (copy.toNat : Int)
  set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
  wrS st fun s => { s with length := s.length - copy }

/-- `case STORED:` -/
def back_STORED (c : DecoderCtx) : X Unit := do
  BYTEBITS
  NEEDBITS c 32
  let l ← get
  if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
    badMode c "invalid stored block lengths"
    return
  wrS c.st fun s => { s with length := l.hold.toUInt32 &&& 0xffff }
  INITBITS
  -- while (state->length != 0) { copy = state->length; PULL(); ROOM(); ... }
  xwhile
    (do return (← rdS c.st (·.length)) != 0)
    (do
      let s ← ldInflateState c.st
      modify fun l => { l with copy := s.length }
      PULL c
      ROOM c
      copyStoredInput c.st)
  setMode c.st TYPE

/-- `case TYPE:` -/
def back_TYPE (c : DecoderCtx) : X Unit := do
  -- if (state->last) { BYTEBITS(); state->mode = DONE; break; }
  if (← rdS c.st (·.last)) != 0 then
    BYTEBITS
    setMode c.st DONE
    return
  NEEDBITS c 3
  let b ← BITS 1
  wrS c.st fun s => { s with last := u2i b }
  DROPBITS 1
  match (← BITS 2) with
  | 0 => setMode c.st STORED
  | 1 =>
    inflate_fixed c.st
    setMode c.st LEN
  | 2 => setMode c.st TABLE
  | _ => badMode c "invalid block type"
  DROPBITS 2

/-- The `switch (state->mode)` of `inflateBack()`. -/
def back_dispatch (c : DecoderCtx) : X Unit := do
  let m ← rdS c.st (·.mode)
  if m == TYPE then back_TYPE c
  else if m == STORED then back_STORED c
  else if m == TABLE then back_TABLE c
  else if m == LEN then sharedCase (back_LEN c)
  else if m == DONE then
    -- ret = Z_STREAM_END; goto inf_leave;
    modify fun l => { l with ret := Z_STREAM_END }
    throw Ex.leave
  else if m == BAD then
    modify fun l => { l with ret := Z_DATA_ERROR }
    throw Ex.leave
  else
    -- default: ret = Z_STREAM_ERROR; goto inf_leave;
    modify fun l => { l with ret := Z_STREAM_ERROR }
    throw Ex.leave

/-- Validate the stream and initialize the locals before entering its dispatch loop. -/
@[inline] def withBackStream {m : Type → Type} [Monad m] [MonadLiftT M m]
    (strm : ZStreamPtr) (invalid : α)
    (body : InflateStatePtr → BPtr → UInt32 → BPtr → UInt32 → m α) : m α := do
  -- if (strm == Z_NULL || strm->state == Z_NULL) return invalid;
  if strm == none then return invalid
  let z ← ldZStream strm
  if z.state == none then return invalid
  -- state = (struct inflate_state FAR *)strm->state;
  let st ← castInflateState z.state
  -- strm->msg = Z_NULL; state->mode = TYPE; state->last = 0; state->whave = 0;
  wrZ strm fun z => { z with msg := .null }
  wrS st fun s => { s with mode := TYPE, last := 0, whave := 0 }
  -- next = strm->next_in; have = next != Z_NULL ? strm->avail_in : 0; hold = 0; bits = 0;
  let z ← ldZStream strm
  let s ← ldInflateState st
  let next := z.next_in
  let have_ := if next != .null then z.avail_in else 0
  -- put = state->window; left = state->wsize;
  body st next have_ s.window s.wsize

private def backRegisters (next : BPtr) (have_ : UInt32) (put : BPtr) (left : UInt32) : IL :=
  { IL.init with next, have_, put, left }

/-- Run the case dispatch with C locals, retaining any updates to active caller
    variables across the loop and the jump to `inf_leave`. -/
def runBackModesFrom (registers : IL) (body : X Unit) : PointerLocalM IL := do
  let initial := { registers with pointerLocals := ← get }
  let (_, last) ← (xwhile (pure true) body).run.run initial
  set last.pointerLocals
  return last

@[inline] def runBackModes (next : BPtr) (have_ : UInt32) (put : BPtr) (left : UInt32)
    (body : X Unit) : PointerLocalM IL :=
  runBackModesFrom (backRegisters next have_ put left) body

/-- Value-callback entry covered by the existing safety contract. -/
def inflateBack (strm : ZStreamPtr) (inCb : InCb) (in_desc : BPtr) (outCb : OutCb) (out_desc : BPtr) : M Int32 :=
  withBackStream strm Z_STREAM_ERROR fun st next have_ put left => do
    let l0 := backRegisters next have_ put left
    let c : BCtx := { strm, st, inCb, inDesc := in_desc, outCb, outDesc := out_desc }
    -- for (;;) switch (state->mode) { ... }
    let (_, l) ← StateT.run (ExceptT.run (xwhile (pure true) (back_dispatch c))) l0
    -- inf_leave: if (left < state->wsize) { if (out(out_desc, state->window, state->wsize - left) && ret == Z_STREAM_END) ret = Z_BUF_ERROR; }
    let s ← ldInflateState st
    let mut ret := l.ret
    if l.left < s.wsize then
      if (← outCb out_desc s.window (s.wsize - l.left)) != 0 && ret == Z_STREAM_END then ret := Z_BUF_ERROR
    -- strm->next_in = next; strm->avail_in = have; return ret;
    wrZ strm fun z => { z with next_in := l.next, avail_in := l.have_ }
    return ret

/-- The C ABI exit delivers any remaining window bytes, then writes the final
    input pointer and byte count back to the caller's stream. -/
@[inline] def finishBack (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (output : COutCb) (outDesc : VoidPtr) (l : IL) : PointerLocalM Int32 := do
  let s ← ldInflateState st
  let mut ret := l.ret
  let mut next := l.next
  if l.left < s.wsize then
    let (rc, updated) ← callWithNext cell next (output outDesc s.window (s.wsize - l.left))
    next := updated
    if rc != 0 && ret == Z_STREAM_END then ret := Z_BUF_ERROR
  wrZ strm fun z => { z with next_in := next, avail_in := l.have_ }
  return ret

/-- `inflateBack(strm, in, in_desc, out, out_desc)` with the lifetime and
    address of the actual C local `next`. -/
def inflateBack_c (strm : ZStreamPtr) (input : CInCb) (inDesc : VoidPtr)
    (output : COutCb) (outDesc : VoidPtr) : PointerLocalM (CExportAs "inflateBack" Int32) :=
  withBackStream strm Z_STREAM_ERROR fun st next have_ put left =>
    withBPtrCell next fun cell => do
      let c := addressedCtx strm st cell input inDesc output outDesc
      let l ← runBackModesFrom (backRegisters next have_ put left) (back_dispatch c)
      finishBack strm st cell output outDesc l

/-- `int ZEXPORT inflateBackEnd(z_streamp strm)` -/
def inflateBackEnd (strm : ZStreamPtr) : M (CExport Int32) := do
  -- if (strm == Z_NULL || strm->state == Z_NULL || strm->zfree == (free_func)0) return Z_STREAM_ERROR;
  if strm == none then return Z_STREAM_ERROR
  let z ← ldZStream strm
  if z.state == none || z.zfree == .null then return Z_STREAM_ERROR
  -- ZFREE(strm, strm->state); strm->state = Z_NULL;
  let st ← castInflateState z.state
  ZFREES strm st
  wrZ strm fun z => { z with state := none }
  return Z_OK

end Zlib.Infback
