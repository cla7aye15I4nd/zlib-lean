import ZlibF.Proof.«deflate.c.engine.slow-loop»
import ZlibF.Proof.«deflate.c.engine.entry-correspondence»
import ZlibF.Proof.«deflate.c.engine.pending-output»

/-! # Source cut points for the public compressor entry

The equality retains every refusal, header, dispatch and trailer branch.
It changes no translated source statement.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees («_tr_stored_block» «_tr_align»)
open Zlib.Crc32 (crc32 crc32_z)
set_option autoImplicit false

/-- From the first gzip status test to the return of the exported function. -/
def publicDataTail (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) : M Int32 := do
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
  Phases.strategyPhase strm s flush (Phases.trailerPhase strm s flush)

/-- The raw-stream shortcut and zlib header, with the early return on a full output buffer. -/
def publicZlibHeader (strm : ZStreamPtr) (s : DeflateStatePtr) (next : M Int32) : M Int32 := do
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
  next

/-- Whole-computation equality for the public entry, including the short-circuit rank test. -/
theorem public_deflate_source (strm : ZStreamPtr) (flush : Int32) :
    deflate strm flush = Phases.entryPhase strm flush (fun s =>
      publicZlibHeader strm s (publicDataTail strm s flush)) := rfl

end Zlib.Deflate.Engine.Proofs
