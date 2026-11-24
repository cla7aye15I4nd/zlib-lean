import ZlibF.Proof.«infback.c.addressed-extra»
import ZlibF.Proof.«infback.c.addressed-literal»

/-! Match copying through the addressed inflateBack decoder's caller window. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored
set_option autoImplicit false

section
variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)
include cb

private theorem copy_tail (c : DecoderCtx) (ownerEq : c.st = some (.tab owner))
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    {f : Nat} {from_ : BPtr} (ptr : from_ = .ref (.blk w) f) (count : UInt32)
    (inRange : f + count.toNat ≤ off + cap) (positive : 0 < count.toNat) (space : count.toNat ≤ l.left.toNat)
    (length : 0 < s.length.toNat) :
    ∃ regs H t, runX (lcTail c s l from_ count) l h = .ok ((.ok (), regs), H) ∧
      H.istates owner = some t ∧ Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧
      t = {s with length := t.length} ∧ t.length.toNat < s.length.toNat ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧ regs.have_ = l.have_ := by
  obtain ⟨a, get, fits⟩ := buf.window.storage
  let n := if count > s.length then s.length else count
  have clipped : n.toNat = min count.toNat s.length.toNat := by
    dsimp only [n]; split
    · next g => have := UInt32.lt_iff_toNat_lt.mp g; omega
    · next g =>
      have le : count.toNat ≤ s.length.toNat := Nat.le_of_not_gt fun x => g (UInt32.lt_iff_toNat_lt.mpr x)
      exact (Nat.min_eq_left le).symm
  let t := {s with length := s.length - n}
  let p := off + (cap - l.left.toNat)
  let start := {l with copy := n, from_ := from_, left := l.left - n}
  let ready := setI h owner t
  have bound := buf.left
  have save : wrS c.st (fun s => {s with length := s.length - n}) h = .ok ((), ready) :=
    ownerEq ▸ wrS_tab state _
  obtain ⟨a', copy, size, frame⟩ := mc_run (h := ready) (w := w) get buf.window.writable
    (l := start) (p := p) (f := f) (k := n.toNat) (by omega) ptr buf.put rfl
    (by omega) (by dsimp only [p]; omega)
  let H := winHeap ready w a'
  let regs := mcRegs start w p f n.toNat 0
  have sub : (l.left - n).toNat = l.left.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have remain : t.length.toNat = s.length.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have valid : Buffers cell w off cap t regs H := by
    refine ⟨buf.live, ⟨⟨a', upd_same .., by omega⟩, buf.window.writable⟩, buf.address, buf.size, buf.positive,
      by change (l.left - n).toNat ≤ cap; omega, ?_, ?_⟩
    · change Ptr.ref (BRef.blk w) (p + n.toNat) = .ref _ (off + (cap - (l.left - n).toNat))
      congr 1; dsimp only [p]; omega
    · intro has
      obtain ⟨b, ix, src, eq, gb, room, separate⟩ := buf.input has
      by_cases same : b = w
      · subst b; cases Option.some.inj (get.symm.trans gb)
        exact ⟨w, ix, a', eq, upd_same .., by change ix + l.have_.toNat ≤ a'.size; omega, separate⟩
      · exact ⟨b, ix, src, eq, (upd_ne h.bytes w _ b same).trans gb, room, separate⟩
  refine ⟨regs, H, t, ?_, upd_same .., valid, ?_, rfl, by omega, rfl, rfl, rfl⟩
  · unfold lcTail
    rw [← show n = (if count > s.length then s.length else count) from rfl]
    simp only [runX_bind, runX_lift_ok save, runX_set]
    exact copy
  · exact cb.copy _ _ a a' s t.length allowed state get size (fun j away => frame j (by dsimp only [p]; omega))

/-- ROOM may replace the live input cursor before either half of the circular
window is read. A successful trip strictly reduces the outstanding length. -/
private theorem copy_trip {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (dist : s.offset.toNat ≤ cap) (length : 0 < s.length.toNat) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H t, runX (lcBody c) l h = .ok ((status, regs), H) ∧ H.istates owner = some t ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧
      t = {s with whave := t.whave, length := t.length} ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧ regs.have_ = l.have_ ∧
      (status = .ok () → t.length.toNat < s.length.toNat) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  obtain ⟨status, r, H, t, room, valid, ok, st, len, _, have_, ⟨bits, hold, shape⟩, space, err⟩ :=
    room_safe (strm := strm) cb state buf allowed
  change runX (ROOM c) l h = _ at room
  have record : t = {s with whave := t.whave} := by rcases shape with rfl | rfl <;> rfl
  cases status with
  | error e =>
    refine ⟨.error e, r, H, t, ?_, st, valid, ok, ?_, bits, hold, have_, nofun, err⟩
    · change runX (lcBody c) l h = _; unfold lcBody; rw [runX_bind, room]
    · conv => lhs; rw [record]
      rw [len]
  | ok u =>
    cases u
    have size := valid.size
    have offset := congrArg InflateState.offset record
    change t.offset = s.offset at offset
    have fit : t.offset.toNat ≤ t.wsize.toNat := by rw [offset, size]; exact dist
    have left := valid.left
    have pos : 0 < r.left.toNat := Nat.pos_of_ne_zero (fun eq => space rfl (UInt32.toNat_inj.mp eq))
    obtain ⟨a, get, window⟩ := valid.window.storage
    have getP : Space.get H (.blk w : BRef) = some a := get
    have gap : (t.wsize - t.offset).toNat = cap - t.offset.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr fit), size]
    have ld : ldInflateState c.st H = .ok (t, H) := ldInflateState_tab st
    have post {r' : IL} {H' : Heap} {t' : InflateState}
        (live : H'.istates owner = some t') (buffer : Buffers cell w off cap t' r' H') (allow : admitted r'.pointerLocals H')
        (fields : t' = {t with length := t'.length}) (less : t'.length.toNat < t.length.toNat)
        (bit' : r'.bits = r.bits) (hold' : r'.hold = r.hold) (have' : r'.have_ = r.have_) :
        H'.istates owner = some t' ∧ Buffers cell w off cap t' r' H' ∧ admitted r'.pointerLocals H' ∧
        t' = {s with whave := t'.whave, length := t'.length} ∧ r'.bits = l.bits ∧ r'.hold = l.hold ∧
        r'.have_ = l.have_ ∧ (Except.ok () = (Except.ok () : Except Ex Unit) → t'.length.toNat < s.length.toNat) ∧
        (∀ e, Except.ok () = Except.error e → e = Ex.leave ∧ r'.ret = Z_BUF_ERROR) := by
      refine ⟨live, buffer, allow, ?_, bit'.trans bits, hold'.trans hold, have'.trans have_, (fun _ => len ▸ less), fun _ eq => nomatch eq⟩
      have hv := congrArg InflateState.whave fields
      change t'.whave = t.whave at hv
      conv => lhs; rw [fields, record]
      rw [hv]
    by_cases ahead : t.wsize - t.offset < r.left
    · have near := UInt32.lt_iff_toNat_lt.mp ahead
      let at_ := off + (cap - r.left.toNat) + (t.wsize - t.offset).toNat
      have add : OkOn H (r.put.add ((t.wsize - t.offset).toNat : Int)) (.ref (.blk w) at_) := by
        rw [valid.put]; exact Ptr.add_nat_ok getP (by omega)
      have amount : (r.left - (t.wsize - t.offset)).toNat = r.left.toNat - (cap - t.offset.toNat) := by
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega)), gap]
      obtain ⟨r', H', t', run, result⟩ := copy_tail cb c rfl st valid ok (f := at_) rfl
        (r.left - (t.wsize - t.offset)) (by dsimp only [at_]; omega) (by omega) (by omega) (len ▸ length)
      obtain ⟨st', valid', ok', fields, less, bit', hold', have'⟩ := result
      refine ⟨.ok (), r', H', t', ?_, post st' valid' ok' fields less bit' hold' have'⟩
      change runX (lcBody c) l h = _
      unfold lcBody; rw [runX_bind, room]
      simp only [runX_bind, runX_lift_ok ld, runX_get, ahead, ↓reduceIte, runX_lift_ok add, runX_pure]
      exact run
    · have far : r.left.toNat ≤ (t.wsize - t.offset).toNat :=
        Nat.le_of_not_gt fun x => ahead (UInt32.lt_iff_toNat_lt.mpr x)
      let at_ := off + (cap - r.left.toNat) - t.offset.toNat
      have add : OkOn H (r.put.add (-(t.offset.toNat : Int))) (.ref (.blk w) at_) := by
        have index : ((((off + (cap - r.left.toNat) : Nat) : Int) + -(t.offset.toNat : Int)).toNat) = at_ := by
          dsimp only [at_]; omega
        rw [valid.put, ← index]; exact Ptr.add_ok getP (by omega) (by omega)
      obtain ⟨r', H', t', run, result⟩ := copy_tail cb c rfl st valid ok (f := at_) rfl r.left
        (by dsimp only [at_]; omega) pos (Nat.le_refl _) (len ▸ length)
      obtain ⟨st', valid', ok', fields, less, bit', hold', have'⟩ := result
      refine ⟨.ok (), r', H', t', ?_, post st' valid' ok' fields less bit' hold' have'⟩
      change runX (lcBody c) l h = _
      unfold lcBody; rw [runX_bind, room]
      simp only [runX_bind, runX_lift_ok ld, runX_get, ahead, ↓reduceIte, runX_lift_ok add, runX_pure]
      exact run

private structure Copying (owner w off cap : Nat) (cell : BPtrCell) (admitted : PointerLocals → Heap → Prop)
    (base : InflateState) (before : IL) (t : InflateState) (regs : IL) (H : Heap) : Prop where
  state : H.istates owner = some t
  buffers : Buffers cell w off cap t regs H
  allowed : admitted regs.pointerLocals H
  record : t = {base with length := t.length, whave := t.whave}
  bits : regs.bits = before.bits
  hold : regs.hold = before.hold
  count : regs.have_ = before.have_

private theorem match_loop {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (dist : s.offset.toNat ≤ cap)
    (length : 0 < s.length.toNat) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H t, runX (xdoWhile (lcBody c) (lcCond c)) l h = .ok ((status, regs), H) ∧
      Copying owner w off cap cell admitted s l t regs H ∧ (status = .ok () → t.length = 0) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let inv := fun (regs : IL) H => ∃ t, Copying owner w off cap cell admitted s l t regs H
  let post := fun (v : Except Ex Unit) (regs : IL) H => ∃ t, Copying owner w off cap cell admitted s l t regs H ∧
    (v = .ok () → t.length = 0) ∧ (∀ e, v = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR)
  have trip {r : IL} {g : Heap} {t : InflateState} (I : Copying owner w off cap cell admitted s l t r g)
      (positive : 0 < t.length.toNat) :
      ∃ v next G u, runX (lcBody c) r g = .ok ((v, next), G) ∧ Copying owner w off cap cell admitted s l u next G ∧
        (v = .ok () → u.length.toNat < t.length.toNat) ∧ (∀ e, v = .error e → e = Ex.leave ∧ next.ret = Z_BUF_ERROR) := by
    have offset := congrArg InflateState.offset I.record
    change t.offset = s.offset at offset
    obtain ⟨v, next, G, u, run, st, valid, ok, fields, bits, hold, count, less, err⟩ :=
      copy_trip (strm := strm) cb I.state I.buffers I.allowed (by rw [offset]; exact dist) positive
    refine ⟨v, next, G, u, run, ⟨st, valid, ok, ?_, bits.trans I.bits, hold.trans I.hold, count.trans I.count⟩, less, err⟩
    conv => lhs; rw [fields, I.record]
  obtain ⟨v, first, H1, t1, run, I1, _, err1⟩ := trip ⟨state, buf, allowed, rfl, rfl, rfl, rfl⟩ length
  change runX (lcBody c) l h = _ at run
  cases v with
  | error e => exact ⟨.error e, first, H1, t1, by change runX (xdoWhile (lcBody c) (lcCond c)) l h = _;
                                                       unfold xdoWhile; rw [runX_bind, run], I1, nofun, err1⟩
  | ok u =>
    cases u
    obtain ⟨v, r, H, tail, t, result⟩ := xwhileBrk_wf (cond := lcCond c) (body := do lcBody c; pure false)
      inv post (fun _ H => stLen owner H) (fun r g ⟨t, I⟩ => by
        have read : rdS c.st (·.length) g = .ok (t.length, g) := by
          rw [show c.st = some (.tab owner) from rfl, rdI_eq]; simp [I.state]
        refine ⟨r, g, t.length != 0, by unfold lcCond; rw [runX_bind, runX_lift_ok read]; rfl, ?_, ?_⟩
        · intro guard
          have pos : 0 < t.length.toNat := Nat.pos_of_ne_zero fun eq => (bne_iff_ne.mp guard) (UInt32.toNat_inj.mp eq)
          obtain ⟨status, next, G, u, step, nextI, less, err⟩ := trip I pos
          cases status with
          | error e => exact ⟨.error e, next, G, by rw [runX_bind, step], u, nextI, nofun, err⟩
          | ok unit_ =>
            refine ⟨.ok false, next, G, by rw [runX_bind, step]; rfl, ⟨u, nextI⟩, ?_⟩
            rw [stLen_of nextI.state, stLen_of I.state]; exact less rfl
        · intro done
          exact ⟨t, I, fun _ => by simpa using done, fun _ eq => nomatch eq⟩)
      (show inv first H1 from ⟨t1, I1⟩) (by rw [stLen_of I1.state]; have := UInt32.toNat_lt t1.length; unfold fuel; omega)
    refine ⟨v, r, H, t, ?_, result⟩
    change runX (xdoWhile (lcBody c) (lcCond c)) l h = _
    unfold xdoWhile
    rw [runX_bind, run]
    exact tail

/-- C checks the initialized window history before the first write. Every
valid match finishes the whole circular copy or leaves on callback failure. -/
theorem match_copy {r : ZStreamRef} {z : ZStream} {s : InflateState} {l : IL} {h : Heap}
    (stream : r.get h = some z) (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h)
    (allowed : admitted l.pointerLocals h) (length : 0 < s.length.toNat) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    if s.offset > s.wsize - (if s.whave < s.wsize then l.left else 0) then
      ∃ j, strTable[j]? = some "invalid distance too far back" ∧
        runX (lenCopy c) l h = .ok ((.ok (), l), setI (r.put h {z with msg := .ref (.str j) 0}) owner {s with mode := BAD})
    else ∃ status regs H t, runX (lenCopy c) l h = .ok ((status, regs), H) ∧ H.istates owner = some t ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧ (t = {s with whave := t.whave, length := t.length} ∧
      (t.whave = s.whave ∨ t.whave = s.wsize)) ∧
      regs.bits = l.bits ∧ regs.hold = l.hold ∧ regs.have_ = l.have_ ∧ (status = .ok () → t.length = 0) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have ld : ldInflateState c.st h = .ok (s,h) := ldInflateState_tab state
  by_cases far : s.offset > s.wsize - (if s.whave < s.wsize then l.left else 0)
  · obtain ⟨j, msg, bad⟩ := badMode_ctx_literal c rfl rfl stream state _ lit_too_far
    simp only [far, ↓reduceIte]
    refine ⟨j, msg, ?_⟩
    change runX (lenCopy c) l h = _
    rw [lenCopy_eq]; simp only [runX_bind, runX_lift_ok ld, runX_get, far, ↓reduceIte, runX_lift_ok bad]; rfl
  · have limit := buf.left
    have size := buf.size
    have dist : s.offset.toNat ≤ cap := by
      have le : s.offset.toNat ≤ (s.wsize - (if s.whave < s.wsize then l.left else 0)).toNat :=
        Nat.le_of_not_gt fun x => far (UInt32.lt_iff_toNat_lt.mpr x)
      split at le
      · rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))] at le; omega
      · simp only [UInt32.sub_zero] at le; omega
    let history := fun (t : InflateState) => t.wsize = s.wsize ∧ (t.whave = s.whave ∨ t.whave = s.wsize)
    have guard := cb.withDecoder history (fun _ _ old => old) (fun _ old => ⟨old.1, Or.inr old.1⟩)
    obtain ⟨status, regs, H, t, run, I, done, err⟩ := match_loop (strm := some r) guard state buf
      (.intro allowed state ⟨rfl, Or.inl rfl⟩) dist length
    simp only [far, ↓reduceIte]
    refine ⟨status, regs, H, t, ?_, I.state, I.buffers, I.allowed.1, ⟨I.record, (I.allowed.2 t I.state).2⟩, I.bits, I.hold, I.count, done, err⟩
    change runX (lenCopy c) l h = _
    rw [lenCopy_eq]; simp only [runX_bind, runX_lift_ok ld, runX_get, far, ↓reduceIte]; exact run

end
#print axioms match_copy
end Zlib.Infback.AddressedTable
