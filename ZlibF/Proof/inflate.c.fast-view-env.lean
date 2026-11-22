import ZlibF.Proof.«inflate.c.fast-default-invariant»
import ZlibF.Proof.«inflate.c.fast-buffers»
import ZlibF.Proof.«inflate.c.default-state»
import ZlibF.Proof.«inffast.c.progress-origin»
import ZlibF.Proof.«inflate.c.fast-writeback-frame»
import ZlibF.Proof.«inflate.c.slow-output-exact-frame»
import ZlibF.Spec.Common.Streams

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- Assemble a general caller `Zlib.Inffast.Proofs.Env` from the decoder's
initialized default state and dispatch buffer packet. Supports both distinct
blocks and disjoint slices within a single caller byte object. -/
noncomputable def fast_view_env
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : s.mode = LEN)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 && slow.bits < 8) = true) :
    Zlib.Inffast.Proofs.Env :=
  let good := invariant.good
  let fit := invariant.platform
  let margins : (6 ≤ slow.have_ ∧ 258 ≤ slow.left) ∧ slow.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  let inputRoom : 6 ≤ z.avail_in.toNat := by
    rw [inputCount]
    exact UInt32.le_iff_toNat_le.mp margins.1.1
  let outputRoom : 258 ≤ z.avail_out.toNat := by
    rw [outputCount]
    exact UInt32.le_iff_toNat_le.mp margins.1.2
  let smallBits : s.bits.toNat < 8 := by
    rw [stateBits]
    exact UInt32.lt_iff_toNat_lt.mp margins.2
  let views := buffers.fast_views good fit fast
  let ir := views.choose
  let rest1 := views.choose_spec
  let or_ := rest1.choose
  let rest2 := rest1.choose_spec
  let ia := rest2.choose
  let rest3 := rest2.choose_spec
  let oa := rest3.choose
  let rest4 := rest3.choose_spec
  let io := rest4.choose
  let rest5 := rest4.choose_spec
  let oo := rest5.choose
  let facts := rest5.choose_spec
  let tables := invariant.tables (by rw [mode]; unfold DataTableMode; decide)
  let lenT := tables.lengthTable
  let distT := tables.distanceTable
  let lr := lenT.choose
  let lo := lenT.choose_spec.choose
  let la := lenT.choose_spec.choose_spec.choose
  let lfacts := lenT.choose_spec.choose_spec.choose_spec
  let dr := distT.choose
  let doff := distT.choose_spec.choose
  let da := distT.choose_spec.choose_spec.choose
  let dfacts := distT.choose_spec.choose_spec.choose_spec
  let privateWindow : ∀ w, s.window = .ref (.blk w) 0 → or_ ≠ BRef.blk w := by
    have pw := callerRange_private_window good buffers.output.range facts.2.2.2.2.2.1
    intro w win eq
    exact pw w win eq
  let winInfo : Σ' wb : Nat, Σ' wa : Array UInt8,
      s.window ≠ .null →
        s.window = .ref (BRef.blk wb) 0 ∧ BRef.blk wb ≠ or_ ∧
          h.bytes wb = some wa ∧ s.wsize.toNat ≤ wa.size :=
    if null : s.window = .null then
      ⟨0, #[], fun hnon => False.elim (hnon null)⟩
    else
      let blockEx : ∃ wb wa, s.window = .ref (BRef.blk wb) 0 ∧ h.bytes wb = some wa ∧
          Space.ro h (BRef.blk wb) = false ∧ wa.size = (2 ^ s.wbits.toNat) :=
        good.inv.win.block.resolve_left null
      let wb := blockEx.choose
      let wa := blockEx.choose_spec.choose
      let hblk := blockEx.choose_spec.choose_spec
      ⟨wb, wa, fun _ => ⟨hblk.1, fun eq => privateWindow wb hblk.1 eq.symm, hblk.2.1, by
        have ws := good.inv.win.ws
        rw [hblk.2.2.2]
        rcases ws with h0 | hpow <;> omega⟩⟩
  let wb := winInfo.1
  let wa := winInfo.2.1
  let winLive := winInfo.2.2
  let winWhave : s.whave ≠ 0 →
      s.window = .ref (BRef.blk wb) 0 ∧ WinRel false wb or_ s.wnext (0 + s.wsize.toNat ≤ oo + z.avail_out.toNat) ∧
        h.bytes wb = some wa ∧ 0 + s.wsize.toNat ≤ wa.size := by
    intro nonzero
    have nonnull : s.window ≠ .null := by
      intro null
      have zero := good.inv.win.nullws null
      have whave : s.whave.toNat ≤ s.wsize.toNat := good.inv.win.hv
      have hzero : s.wsize.toNat = 0 := by rw [zero]; rfl
      have hwhave0 : s.whave.toNat = 0 := by omega
      exact nonzero (UInt32.toNat_inj.mp hwhave0)
    have live := winLive nonnull
    exact ⟨live.1, fun eq => live.2.1 eq, live.2.2.1, by simpa using live.2.2.2⟩
  let wsize : s.wsize.toNat ≤ 32768 := by
    have pow := Nat.pow_le_pow_right (by decide : 0 < 2) good.inv.win.wbits
    have := good.inv.win.ws
    omega
  { h0 := h
    strm := some r
    start := slow.out_
    r := r
    sm0 := z
    stid := zs
    s0 := s
    hstrm := rfl
    hsm := good.live.hz
    hrw := by cases r <;> rfl
    hstate := good.live.zst
    hs0 := good.live.hs
    ib := ir
    i0 := io
    IN := ia
    hnin := inputCursor.trans facts.1
    hIN := facts.2.1
    hai := inputRoom
    hINsz := by rw [inputCount]; exact facts.2.2.1
    hINbig := facts.2.2.2.1
    ob := or_
    o0 := oo
    A0 := oa
    hnout := outputCursor.trans facts.2.2.2.2.2.1
    hA0 := facts.2.2.2.2.2.2.1
    hro := facts.2.2.2.2.2.2.2.1
    hao := outputRoom
    hAsz := by rw [outputCount]; exact facts.2.2.2.2.2.2.2.2.1
    hAbig := facts.2.2.2.2.2.2.2.2.2.1
    hstart := by rw [outputCount]; exact buffers.output.count
    hbeg := by rw [outputCount]; exact buffers.output.produced or_ oo facts.2.2.2.2.2.1
    hsep := by
      rcases facts.2.2.2.2.2.2.2.2.2.2 with hne | hdisj
      · exact Or.inl hne
      · by_cases heq : ir = or_
        · exact Or.inr ⟨heq, by rwa [inputCount, outputCount]⟩
        · exact Or.inl heq
    hbits := smallBits
    hhold := by rw [stateHold, stateBits]; exact buffers.bits.hold_lt
    hsane := by
      have sane := invariant.pending.sane
      intro zero
      rw [zero] at sane
      cases sane
    hmode := mode
    halias_win := fun eq => by cases eq
    hws := wsize
    hwh := good.inv.win.hv
    hwn := by
      have wn := good.inv.win.wn
      omega
    wb := wb
    woff := 0
    W := wa
    hwin := winWhave
    hwinLive := fun hnon => by
      have hl := winLive hnon
      exact ⟨hl.1, hl.2.1, hl.2.2.1, by simpa using hl.2.2.2⟩
    rl := lr
    ol := lo
    LCA := la
    hlc := lfacts.1
    hLCA := lfacts.2.1
    hlt := lfacts.2.2
    rd := dr
    od := doff
    DCA := da
    hdc := dfacts.1
    hDCA := dfacts.2.1
    hdt := dfacts.2.2 }

/-- Execute the proved general-view `inflate_fast` theorem and discharge every
public state, accounting, bit-invariant, progress and output-frame obligation
without requiring `ib ≠ ob`. -/
theorem fast_view_exec
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {slow : IL} {bs : List UInt8}
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (mode : s.mode = LEN)
    (inputCursor : z.next_in = slow.next)
    (inputCount : z.avail_in = slow.have_)
    (outputCursor : z.next_out = slow.put)
    (outputCount : z.avail_out = slow.left)
    (stateHold : s.hold = slow.hold)
    (stateBits : s.bits = slow.bits)
    (fast : (slow.have_ >= 6 && slow.left >= 258 && slow.bits < 8) = true) :
    ∃ finished zNext sNext used made regs, used ≤ bs.length ∧
      C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h = .ok ((), finished) ∧
      DefaultStateJ finished r zs zNext sNext ∧
      StreamAccounting z zNext used made ∧
      DispatchBuffers finished r regs (bs.drop used) ∧
      ByteViewSizes h finished ∧
      regs.next = inputAdvance slow.next used ∧ regs.have_.toNat + used = slow.have_.toNat ∧
      regs.put = inputAdvance slow.put made ∧ regs.left.toNat + made = slow.left.toNat ∧
      regs.bits.toNat < 8 ∧ regs.bits.toNat ≤ slow.bits.toNat + 8 * used ∧
      sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
      regs = { slow with
        put := zNext.next_out, left := zNext.avail_out,
        next := zNext.next_in, have_ := zNext.avail_in, hold := sNext.hold, bits := sNext.bits } ∧
      (sNext.mode = BAD ∨ sNext.mode = TYPE ∨ 0 < made) ∧
      BufferFrame h finished (fun b => StreamRoot r b ∨ b = zs) [⟨slow.put, slow.left.toNat⟩] := by
  let e := fast_view_env invariant buffers mode inputCursor inputCount
    outputCursor outputCount stateHold stateBits fast
  have he_h0 : e.h0 = h := rfl
  have he_r : e.r = r := rfl
  have he_stid : e.stid = zs := rfl
  have he_sm0 : e.sm0 = z := rfl
  have he_s0 : e.s0 = s := rfl
  obtain ⟨finished, call, post, progress, origin⟩ := inflate_fast_safe_progress_origin e
  have actualPost := post
  have runEq : C.run (Zlib.Inffast.inflate_fast (some r) slow.out_) h = .ok ((), finished) := call
  obtain ⟨used, made, buffered, bytes, msg, nextMode, nextBits, nextHold,
    usedBuf, _, madeBound, bytesSize, bitsLt, holdLt,
    heapEq, outsideUnchanged, classification, _⟩ := post
  let zNext : ZStream := { z with
    next_in := .ref e.ib (e.i0 + used)
    next_out := .ref e.ob (e.o0 + made)
    avail_in := UInt32.ofNat (z.avail_in.toNat - used)
    avail_out := UInt32.ofNat (z.avail_out.toNat - made)
    msg := msg }
  let sNext : InflateState := { s with mode := nextMode, bits := nextBits, hold := nextHold }
  have privateWindow : ∀ w, e.s0.window = .ref (.blk w) 0 → e.ob ≠ BRef.blk w := by
    intro w win
    have hl := e.hwinLive (by rw [win]; simp)
    have hwb : e.s0.window = .ref (.blk e.wb) e.woff := hl.1
    rw [win] at hwb
    have hw : e.wb = w := BRef.blk.inj (Ptr.ref.inj hwb).1.symm
    rw [← hw]
    exact hl.2.1.symm
  have tables0 := invariant.tables (by rw [mode]; unfold DataTableMode; decide)
  obtain ⟨zRet, sRet, goodRet, tablesRet, pendingRet, heldRet, bitsRet, winRet⟩ :=
    fastPost_retained e invariant.good invariant.pending tables0.lengthLeaves privateWindow actualPost
  have stateGet : finished.istates zs = some sNext := by
    rw [heapEq]
    change (e.r.put (Space.put (setI e.h0 e.stid { e.s0 with mode := nextMode, bits := nextBits, hold := nextHold }) e.ob bytes) zNext).istates zs = some sNext
    rw [he_r, he_h0, he_stid, he_s0, ZStreamRef.put_istates, byte_view_put_istates]
    exact upd_same _ _ _
  have zGet : r.get finished = some zNext := by
    rw [heapEq]
    change r.get (e.r.put (Space.put (setI e.h0 e.stid { e.s0 with mode := nextMode, bits := nextBits, hold := nextHold }) e.ob bytes) { e.sm0 with next_in := .ref e.ib (e.i0 + used), next_out := .ref e.ob (e.o0 + made), avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - made), msg }) = some zNext
    rw [he_r, he_h0, he_stid, he_s0, he_sm0]
    have live1 : r.get (Space.put (setI h zs sNext) e.ob bytes) = some z := by
      rw [byte_view_put_stream, ZStreamRef.get_setI]
      exact invariant.good.live.hz
    rw [ZStreamRef.get_put, live1]
    rfl
  have sEq : sRet = sNext := Option.some.inj (goodRet.live.hs.symm.trans stateGet)
  have zEq : zRet = zNext := Option.some.inj (goodRet.live.hz.symm.trans zGet)
  subst sRet zRet
  have sizes : ByteViewSizes h finished := by
    rw [heapEq, he_r, he_h0, he_stid, he_s0, he_sm0, byte_view_put_setI]
    exact ((byte_view_sizes_setI h zs sNext).trans
      (byte_view_sizes_put e.hA0 e.hro bytes bytesSize)).trans
      (byte_view_sizes_stream_put _ r zNext)
  have modesExit : DataExitMode nextMode := by
    rcases classification with same | type | bad
    · rw [same.1, he_s0]
      exact Or.inl (by change DataTableMode s.mode; rw [mode]; unfold DataTableMode; decide)
    · exact Or.inr (Or.inl type.1)
    · exact Or.inr (Or.inr bad)
  have staticEq : finished.static = h.static := by
    rw [heapEq, he_r, he_h0, he_stid, he_s0, he_sm0, ZStreamRef.put_static, Zlib.Inffast.Proofs.space_put_static]
    rfl
  have decodeJ : DefaultDecodeJ finished r zs zNext sNext :=
    invariant.toDefaultDecodeJ.data_writeback goodRet tablesRet pendingRet modesExit heldRet
      rfl rfl rfl staticEq (sizes.platform invariant.platform) winRet rfl
  have formatDone : HeaderDone sNext :=
    (invariant.data_format (by rw [mode]; unfold DataTableMode; decide)).same rfl rfl
  have finalJ : DefaultStateJ finished r zs zNext sNext :=
    ⟨decodeJ, invariant.requestedBits, invariant.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl formatDone))))⟩
  have usedLe : used ≤ z.avail_in.toNat := by
    rw [he_sm0] at usedBuf
    omega
  have madeBoundZ : made ≤ z.avail_out.toNat := by
    rw [he_sm0] at madeBound
    exact madeBound
  have usedBytes : used ≤ bs.length := by
    rw [← buffers.bits.have_eq, ← inputCount]
    exact usedLe
  have availInSub : zNext.avail_in.toNat + used = z.avail_in.toNat := by
    change (UInt32.ofNat (z.avail_in.toNat - used)).toNat + used = z.avail_in.toNat
    have hlt := z.avail_in.toNat_lt
    rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
    omega
  have availOutSub : zNext.avail_out.toNat + made = z.avail_out.toNat := by
    change (UInt32.ofNat (z.avail_out.toNat - made)).toNat + made = z.avail_out.toNat
    have hlt := z.avail_out.toNat_lt
    rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)]
    omega
  have nextInAdv : zNext.next_in = advance z.next_in used := by
    have hnin : z.next_in = .ref e.ib e.i0 := e.hnin
    rw [hnin]
    rfl
  have nextOutAdv : zNext.next_out = advance z.next_out made := by
    have hnout : z.next_out = .ref e.ob e.o0 := e.hnout
    rw [hnout]
    rfl
  have accounting : StreamAccounting z zNext used made :=
    ⟨usedLe, madeBoundZ, availInSub, availOutSub, nextInAdv, nextOutAdv, rfl, rfl, rfl, rfl, rfl⟩
  let regs : IL := { slow with
    put := zNext.next_out
    left := zNext.avail_out
    next := zNext.next_in
    have_ := zNext.avail_in
    hold := sNext.hold
    bits := sNext.bits }
  have regsNext : regs.next = inputAdvance slow.next used := by
    have hnin : slow.next = .ref e.ib e.i0 := inputCursor.symm.trans e.hnin
    rw [hnin]
    rfl
  have regsHave : regs.have_.toNat + used = slow.have_.toNat := by
    rw [← inputCount]
    exact availInSub
  have regsPut : regs.put = inputAdvance slow.put made := by
    have hnout : slow.put = .ref e.ob e.o0 := outputCursor.symm.trans e.hnout
    rw [hnout]
    rfl
  have regsLeft : regs.left.toNat + made = slow.left.toNat := by
    rw [← outputCount]
    exact availOutSub
  have readonly : ∀ ref : BRef, Space.ro finished ref = Space.ro h ref := by
    intro ref
    rw [heapEq, he_r, he_h0, he_stid, he_s0, he_sm0, byte_view_ro_stream_put, Zlib.Inffast.Proofs.space_ro_put, byte_view_ro_setI]
  have inputContents : bs = (e.IN.toList.drop e.i0).take bs.length := by
    rcases buffers.bits.next with empty | ⟨ref, array, off, ptr, get, _, contents⟩
    · have : bs.length = 0 := by rw [empty]; rfl
      simp [empty]
    · have ptr' : Ptr.ref e.ib e.i0 = Ptr.ref ref off := (inputCursor.symm.trans e.hnin).symm.trans ptr
      cases ptr'
      have same : array = e.IN := Option.some.inj (get.symm.trans e.hIN)
      simpa only [same] using contents
  have bitInvNext : BitInv finished regs (bs.drop used) := by
    have dropLen : (bs.drop used).length = regs.have_.toNat := by
      rw [List.length_drop, ← buffers.bits.have_eq]
      omega
    refine ⟨dropLen.symm, Or.inr ?_, heldRet⟩
    have availInEq : regs.have_.toNat = slow.have_.toNat - used := by omega
    by_cases hsame : e.ib = e.ob
    · have getBytes : Space.get finished e.ib = some bytes := by
        rw [heapEq, he_r, he_h0, he_stid, he_s0, he_sm0, hsame, byte_view_get_stream_put]
        exact byte_view_get_put (by rw [byte_view_get_setI]; exact e.hA0)
          (by rw [byte_view_ro_setI]; exact e.hro) bytes
      have sizeIN : e.A0.size = e.IN.size := by
        have h1 : Space.get h e.ib = some e.IN := e.hIN
        have h2 : Space.get h e.ib = some e.A0 := by rw [hsame]; exact e.hA0
        have eqArr : e.IN = e.A0 := Option.some.inj (h1.symm.trans h2)
        rw [eqArr]
      have dropBound : e.i0 + used + (bs.drop used).length ≤ bytes.size := by
        rw [bytesSize, sizeIN, dropLen, availInEq, ← inputCount]
        have hsz := e.hINsz
        rw [he_sm0] at hsz
        omega
      have sepDisjoint : e.i0 + z.avail_in.toNat ≤ e.o0 ∨ e.o0 + z.avail_out.toNat ≤ e.i0 := by
        have hsep := e.hsep
        rw [he_sm0] at hsep
        rcases hsep with hne | ⟨_, hdisj⟩
        · exact False.elim (hne hsame)
        · exact hdisj
      have sliceEq : bs.drop used = (bytes.toList.drop (e.i0 + used)).take (bs.drop used).length := by
        apply List.ext_getElem?
        intro k
        by_cases hk : k < (bs.drop used).length
        · have hkBs : used + k < bs.length := by
            rw [List.length_drop] at hk
            omega
          have hkAvail : used + k < z.avail_in.toNat := by
            rw [inputCount, buffers.bits.have_eq]
            exact hkBs
          have kDrop : (bs.drop used)[k]? = bs[used + k]? := by
            rw [List.getElem?_drop]
          have kIn : bs[used + k]? = e.IN[e.i0 + (used + k)]? := by
            conv => lhs; rw [inputContents]
            rw [List.getElem?_take_of_lt hkBs, List.getElem?_drop, Array.getElem?_toList]
          have kOut : (e.i0 + (used + k)) < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ e.i0 + (used + k) := by
            rw [he_sm0]
            rcases sepDisjoint with hlo | hhi <;> omega
          have bytesSame : bytes[e.i0 + (used + k)]? = e.A0[e.i0 + (used + k)]? :=
            outsideUnchanged (e.i0 + (used + k)) (by simpa only [Bool.false_eq_true, ↓reduceIte] using kOut)
          have arrEq : e.A0 = e.IN := by
            have h1 : Space.get h e.ib = some e.IN := e.hIN
            have h2 : Space.get h e.ib = some e.A0 := by rw [hsame]; exact e.hA0
            exact (Option.some.inj (h1.symm.trans h2)).symm
          rw [arrEq] at bytesSame
          have kRhs : ((bytes.toList.drop (e.i0 + used)).take (bs.drop used).length)[k]? = bytes[e.i0 + (used + k)]? := by
            rw [List.getElem?_take_of_lt hk, List.getElem?_drop, Array.getElem?_toList, Nat.add_assoc]
          rw [kDrop, kIn, ← bytesSame, kRhs]
        · have hge : (bs.drop used).length ≤ k := Nat.le_of_not_lt hk
          rw [List.getElem?_eq_none hge]
          rw [List.getElem?_eq_none (by rw [List.length_take]; exact Nat.le_trans (Nat.min_le_left _ _) hge)]
      exact ⟨e.ib, bytes, e.i0 + used, rfl, getBytes, dropBound, sliceEq⟩
    · have getIN : Space.get finished e.ib = some e.IN := by
        rw [heapEq, he_r, he_h0, he_stid, he_s0, he_sm0, byte_view_get_stream_put, byte_view_get_put_ne _ hsame bytes, byte_view_get_setI]
        exact e.hIN
      have dropBound : e.i0 + used + (bs.drop used).length ≤ e.IN.size := by
        rw [dropLen, availInEq, ← inputCount]
        have hsz := e.hINsz
        rw [he_sm0] at hsz
        omega
      have sliceEq : bs.drop used = (e.IN.toList.drop (e.i0 + used)).take (bs.drop used).length := by
        rw [List.length_drop]
        conv => lhs; rw [inputContents, List.drop_take, List.drop_drop]
      exact ⟨e.ib, e.IN, e.i0 + used, rfl, getIN, dropBound, sliceEq⟩
  have nextBuffers : DispatchBuffers finished r regs (bs.drop used) :=
    buffers.advance_both invariant.good goodRet winRet sizes readonly regsNext regsHave regsPut regsLeft rfl bitInvNext
  have bitBudget : regs.bits.toNat ≤ slow.bits.toNat + 8 * used := by
    have bb := origin.bit_budget (he_stid ▸ stateGet) (he_r ▸ zGet)
    rw [he_s0, he_sm0] at bb
    have availDiff : z.avail_in.toNat - zNext.avail_in.toNat = used := by omega
    rw [stateBits, availDiff] at bb
    exact bb
  have modesDisj : sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD := by
    rcases classification with same | type | bad
    · exact Or.inl (same.1.trans (congrArg InflateState.mode he_s0))
    · exact Or.inr (Or.inl type.1)
    · exact Or.inr (Or.inr bad)
  have madeProgress : sNext.mode = BAD ∨ sNext.mode = TYPE ∨ 0 < made := by
    obtain ⟨smProg, stProg, hsmP, hstP, prog⟩ := progress
    have smPEq : smProg = zNext := Option.some.inj (hsmP.symm.trans (he_r ▸ zGet))
    have stPEq : stProg = sNext := Option.some.inj (hstP.symm.trans (he_stid ▸ stateGet))
    subst smProg stProg
    by_cases hbad : sNext.mode = BAD
    · exact Or.inl hbad
    · by_cases htype : sNext.mode = TYPE
      · exact Or.inr (Or.inl htype)
      · have hlt := prog htype hbad
        rw [he_sm0] at hlt
        exact Or.inr (Or.inr (by omega))
  have frame : BufferFrame h finished (fun b => StreamRoot r b ∨ b = zs) [⟨slow.put, slow.left.toNat⟩] := by
    have putPtr : slow.put = .ref e.ob e.o0 := outputCursor.symm.trans e.hnout
    have leftNat : slow.left.toNat = z.avail_out.toNat := congrArg UInt32.toNat outputCount.symm
    rw [putPtr, leftNat]
    have hf' : ∀ j, j < e.o0 ∨ e.o0 + z.avail_out.toNat ≤ j → bytes[j]? = e.A0[j]? := by
      intro j hj
      rw [← he_sm0] at hj
      simpa only [Bool.false_eq_true, ↓reduceIte] using outsideUnchanged j hj
    have frame1 : BufferFrame h (Space.put h e.ob bytes) (fun b => StreamRoot r b ∨ b = zs)
        [⟨.ref e.ob e.o0, z.avail_out.toNat⟩] :=
      bufferFrame_weaken (fun _ imp => False.elim imp)
        (byte_view_segment_buffer_frame e.hA0 e.hro bytesSize hf')
    have hz1 : r.get (Space.put h e.ob bytes) = some z := by
      rw [byte_view_put_stream]
      exact invariant.good.live.hz
    have hs1 : (Space.put h e.ob bytes).istates zs = some s := by
      rw [byte_view_put_istates]
      exact invariant.good.live.hs
    have frame2 := (fastWriteback_heap_frame hz1 hs1 zNext sNext [⟨.ref e.ob e.o0, z.avail_out.toNat⟩]).1
    have composed := BufferFrame.singleton_trans frame1 frame2
      (byte_view_put_shape e.hA0 e.hro bytes) e.hA0
      (by rw [byte_view_ro_put]; exact e.hro)
      (by rw [byte_view_ro_setI, byte_view_ro_stream_put, byte_view_ro_put]; exact e.hro)
    have heapEq2 : setI (r.put (Space.put h e.ob bytes) zNext) zs sNext = finished := by
      rw [heapEq, he_r, he_h0, he_stid, he_s0, he_sm0, byte_view_put_setI, ZStreamRef.put_setI]
    rwa [← heapEq2]
  exact ⟨finished, zNext, sNext, used, made, regs, usedBytes, runEq, finalJ, accounting,
    nextBuffers, sizes, regsNext, regsHave, regsPut, regsLeft, bitsLt, bitBudget,
    winRet, modesDisj, rfl, madeProgress, frame⟩

#print axioms fast_view_env
#print axioms fast_view_exec

end Zlib.Inflate.Proofs
