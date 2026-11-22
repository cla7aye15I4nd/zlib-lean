import ZlibF.Proof.«inflate.c.window»

/-!
# inflate.c: `updatewindow`

Safety of `updatewindow` on the real translation. The window is a ring buffer; the copy is done in at most two
pieces (`uwPost`). The proofs cover `copy >= wsize`, a copy that fits, a copy that wraps,
and a copy that ends at the end of the window.
-/

namespace Zlib.Inflate.Spec
open C

/-- The window block and the state record after `updatewindow` copied `copy` bytes that end at offset `eo` of the
buffer `ebytes` into the ring buffer `a` of the state `st` (whose `wsize` is already set): the ring buffer is
filled in at most two pieces, as in `inflate.c`. -/
def uwPost (st : InflateState) (a ebytes : Array UInt8) (eo : Nat) (copy : UInt32) : Array UInt8 × InflateState :=
  if st.wsize ≤ copy then
    (copyRange a ebytes 0 (eo - st.wsize.toNat) st.wsize.toNat, { st with wnext := 0, whave := st.wsize })
  else if st.wsize - st.wnext > copy then
    (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) copy.toNat,
      { st with
        wnext := if st.wnext + copy == st.wsize then 0 else st.wnext + copy,
        whave := if st.whave < st.wsize then st.whave + copy else st.whave })
  else if copy - (st.wsize - st.wnext) ≠ 0 then
    (copyRange (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat)
        ebytes 0 (eo - (copy - (st.wsize - st.wnext)).toNat) (copy - (st.wsize - st.wnext)).toNat,
      { st with wnext := copy - (st.wsize - st.wnext), whave := st.wsize })
  else
    (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize - st.wnext).toNat,
      { st with wnext := 0, whave := if st.whave < st.wsize then st.whave + (st.wsize - st.wnext) else st.whave })

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem shl_toNat_aux {b : UInt32} (hb : b.toNat ≤ 15) : ((1 : UInt32) <<< b).toNat = 2 ^ b.toNat := W.shl_toNat b hb

/-- The state after the first two lines of `updatewindow` when `wsize` was 0. -/
def initWinS (st : InflateState) : InflateState :=
  if st.wsize == 0 then { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } else st

theorem shl32_one {b : UInt32} (hb : b.toNat ≤ 15) : shl32 1 b = pure ((1 : UInt32) <<< b) := by
  have : b < 32 := by rw [UInt32.lt_iff_toNat_lt]; have : (32 : UInt32).toNat = 32 := rfl; omega
  simp [shl32, this]

/-- Initialising `wsize` first does not change what `updatewindow` does. -/
theorem uw_init {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w : Nat}
    (hL : Live H r zs z st) (hw : st.window = .ref (.blk w) 0) (hb : st.wbits.toNat ≤ 15) (e : BPtr) (copy : UInt32) :
    updatewindow (some r) e copy H = updatewindow (some r) e copy (setI H zs (initWinS st)) := by
  have hz := hL.hz
  have hs := hL.hs
  have hwnl : (st.window == Ptr.null) = false := by rw [hw]; simp
  have hsh := shl32_one hb
  by_cases h0 : st.wsize = 0
  · have hws0 : (st.wsize == 0) = true := by simp [h0]
    have hI : initWinS st = { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } := by
      simp [initWinS, hws0]
    have hpos : ((1 : UInt32) <<< st.wbits) ≠ 0 := by
      intro e; have := shl_toNat_aux hb; rw [e] at this; have h2 := Nat.two_pow_pos st.wbits.toNat
      have h3 : (0 : UInt32).toNat = 0 := rfl
      omega
    rw [hI]
    unfold updatewindow
    simp only [bind_app, pure_app, ldI_eq, ldZ_eq, wrI_eq, hz, hL.zst, castI, hs, hwnl, hws0, hsh,
      Bool.false_eq_true, ite_false, ite_true, setI_istates_same, ZStreamRef.get_setI]
    simp only [hpos, beq_iff_eq]
    simp only [ite_false, ite_false, bind_app, ldI_eq, setI_istates_same]
    done
  · have hws0 : (st.wsize == 0) = false := by simpa using h0
    have hI : initWinS st = st := by simp [initWinS, hws0]
    rw [hI]
    have : setI H zs st = H := by
      simp only [setI]; rw [upd_self _ _ _ hs]
    rw [this]

theorem zallocb_run {H : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get H = some z) (hza : z.zalloc = .fn "zcalloc") (items size : UInt32) :
    ZALLOCB (some r) items size H = Zlib.Zutil.zcalloc z.«opaque» items size H := by
  simp [ZALLOCB, ldZ_eq, hz, hza]

/-- The window is `NULL` and the allocation fails: `updatewindow` returns 1 and only the allocation counter moves. -/
theorem uw_alloc_fail {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live H r zs z st) (hza : z.zalloc = .fn "zcalloc") (hb : st.wbits.toNat ≤ 15) (hw : st.window = .null)
    (hok : ¬ H.allocOk H.nalloc = true) (e : BPtr) (copy : UInt32) :
    updatewindow (some r) e copy H = .ok (1, setI { H with nalloc := H.nalloc + 1 } zs st) := by
  have hz := hL.hz
  have hs := hL.hs
  have hsh := shl32_one hb
  unfold updatewindow
  have hf := Zlib.Zutil.Proofs.zcalloc_fail_run H z.«opaque» (1 <<< st.wbits) 1 hok
  have hf' : Zlib.Zutil.zcalloc z.«opaque» (1 <<< st.wbits) 1 H = .ok (.null, { H with nalloc := H.nalloc + 1 }) := by
    simpa [Zlib.Zutil.Proofs.failHeap] using hf
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hw, beq_self_eq_true, ite_true, hsh,
    zallocb_run hz hza, hf', wrI_eq]
  have e : ({ st with window := Ptr.null } : InflateState) = st := by rw [← hw]
  simp only [e, setI]

theorem ZStreamRef.get_allocHeap (h : Heap) (n : Nat) (r : ZStreamRef) : r.get (Zlib.Zutil.Proofs.allocHeap h n) = r.get h := by
  cases r <;> rfl

/-- The window is `NULL` and the allocation succeeds: the call continues as on the state with the new window block. -/
theorem uw_alloc_ok {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live H r zs z st) (hza : z.zalloc = .fn "zcalloc") (hb : st.wbits.toNat ≤ 15) (hw : st.window = .null)
    (hok : H.allocOk H.nalloc = true) (hF : Fresh H) (e : BPtr) (copy : UInt32) :
    updatewindow (some r) e copy H = updatewindow (some r) e copy
      (setI (Zlib.Zutil.Proofs.allocHeap H ((1 <<< st.wbits : UInt32) * 1).toNat) zs
        { st with window := .ref (.blk H.nextBlk) 0 }) := by
  have hz := hL.hz
  have hs := hL.hs
  have hsh := shl32_one hb
  have hc := Zlib.Zutil.Proofs.zcalloc_ok_run H z.«opaque» (1 <<< st.wbits) 1 hok hF
  have hne : (Ptr.ref (BRef.blk H.nextBlk) 0 == (Ptr.null : BPtr)) = false := by simp
  have hnn : (Ptr.ref (BRef.blk H.nextBlk) 0 : BPtr) ≠ Ptr.null := by simp
  have hI : (Zlib.Zutil.Proofs.allocHeap H ((1 <<< st.wbits : UInt32) * 1).toNat).istates zs = some st := by
    simpa [Zlib.Zutil.Proofs.allocHeap] using hs
  unfold updatewindow
  simp only [bind_app, pure_app, ldI_eq, ldZ_eq, hz, hL.zst, castI, hs, hw, beq_self_eq_true, ite_true, hsh,
    zallocb_run hz hza, hc, wrI_eq, hne, Bool.false_eq_true, ite_false, ZStreamRef.get_setI, setI_istates_same, hI]
  simp only [bind_app, ldI_eq, setI_istates_same, ZStreamRef.get_allocHeap, ite_false, Bool.false_eq_true, beq_iff_eq, hz, hL.zst, castI, hne, hsh]
  done

/-- The ring-buffer indices after `updatewindow` (`uwPost`) keep the window invariant, and the other fields are kept. -/
theorem uwPost_arith {st : InflateState} {a ebytes : Array UInt8} {eo : Nat} {copy : UInt32}
    (_hpos : st.wsize.toNat ≠ 0)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat)
    (hcl : copy.toNat < 2 ^ 32) (hw32 : st.wsize.toNat ≤ 2 ^ 16) :
    (uwPost st a ebytes eo copy).2.wsize = st.wsize ∧ (uwPost st a ebytes eo copy).2.wbits = st.wbits ∧
    (uwPost st a ebytes eo copy).2.window = st.window ∧ (uwPost st a ebytes eo copy).2.reqbits = st.reqbits ∧
    (uwPost st a ebytes eo copy).2.bits = st.bits ∧ (uwPost st a ebytes eo copy).2.next = st.next ∧
    (uwPost st a ebytes eo copy).2.lencode = st.lencode ∧ (uwPost st a ebytes eo copy).2.distcode = st.distcode ∧
    (uwPost st a ebytes eo copy).2.lens = st.lens ∧ (uwPost st a ebytes eo copy).2.work = st.work ∧
    (uwPost st a ebytes eo copy).2.codes = st.codes ∧ (uwPost st a ebytes eo copy).2.strm = st.strm ∧
    (uwPost st a ebytes eo copy).2.mode = st.mode ∧
    (uwPost st a ebytes eo copy).2.whave.toNat ≤ (uwPost st a ebytes eo copy).2.wsize.toNat ∧
    (uwPost st a ebytes eo copy).2.wnext.toNat < (uwPost st a ebytes eo copy).2.wsize.toNat ∧
    ((uwPost st a ebytes eo copy).2.whave.toNat < (uwPost st a ebytes eo copy).2.wsize.toNat →
      (uwPost st a ebytes eo copy).2.wnext.toNat = (uwPost st a ebytes eo copy).2.whave.toNat) := by
  have e1 := st.wsize.toNat_lt
  have e2 := st.wnext.toNat_lt
  have e3 := st.whave.toNat_lt
  unfold uwPost
  repeat' split
  all_goals
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_add, UInt32.toNat_sub, gt_iff_lt, beq_iff_eq,
      ne_eq, ← UInt32.toNat_inj, UInt32.toNat_zero, Nat.not_lt, Nat.not_le] at *
    omega

theorem initWinS_facts {st : InflateState} (hwb : st.wbits.toNat ≤ 15)
    (hws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0))
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat) :
    (initWinS st).wsize.toNat = 2 ^ st.wbits.toNat ∧ (initWinS st).wbits = st.wbits ∧ (initWinS st).window = st.window ∧
    (initWinS st).whave.toNat ≤ (initWinS st).wsize.toNat ∧ (initWinS st).wnext.toNat < (initWinS st).wsize.toNat ∧
    ((initWinS st).whave.toNat < (initWinS st).wsize.toNat → (initWinS st).wnext.toNat = (initWinS st).whave.toNat) ∧
    (initWinS st).reqbits = st.reqbits ∧ (initWinS st).bits = st.bits ∧ (initWinS st).next = st.next ∧
    (initWinS st).lencode = st.lencode ∧ (initWinS st).distcode = st.distcode ∧ (initWinS st).lens = st.lens ∧
    (initWinS st).work = st.work ∧ (initWinS st).codes = st.codes ∧ (initWinS st).strm = st.strm ∧
    (initWinS st).mode = st.mode := by
  have hpow := shl_toNat_aux hwb
  have h2pos := Nat.two_pow_pos st.wbits.toNat
  by_cases h0 : st.wsize = 0
  · have e : initWinS st = { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } := by simp [initWinS, h0]
    rw [e]
    refine ⟨hpow, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show (0 : UInt32).toNat ≤ _; simp
    · show (0 : UInt32).toNat < ((1 : UInt32) <<< st.wbits).toNat; rw [hpow]; simp; omega
    · intro hh; show (0 : UInt32).toNat = (0 : UInt32).toNat; rfl
  · have e : initWinS st = st := by simp [initWinS, h0]
    have : st.wsize.toNat ≠ 0 := fun hh => h0 (UInt32.toNat_inj.mp (by simpa using hh))
    rw [e]
    refine ⟨by omega, rfl, rfl, hv, by omega, heq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem uwPost_size (st : InflateState) (a ebytes : Array UInt8) (eo : Nat) (copy : UInt32) :
    (uwPost st a ebytes eo copy).1.size = a.size := by
  unfold uwPost
  split
  · exact size_copyRange ..
  · split
    · exact size_copyRange ..
    · split
      · rw [size_copyRange, size_copyRange]
      · exact size_copyRange ..

theorem uniq_allocHeap {h : Heap} (hU : Uniq h) (hF : Fresh h) (n : Nat) : Uniq (Zlib.Zutil.Proofs.allocHeap h n) := by
  intro b
  by_cases hb : b = h.nextBlk
  · subst hb
    have := Heap.not_live.mp (hF _ (Nat.le_refl _))
    obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := this
    simp [Zlib.Zutil.Proofs.allocHeap, e1, e2, e3, e4, e5, e6]
  · have := hU b
    simpa only [Zlib.Zutil.Proofs.allocHeap, upd_ne _ _ _ _ hb] using this

/-- The state of a stream whose window `NULL` was just replaced by the new block. -/
def withWin (st : InflateState) (nb : Nat) : InflateState := { st with window := .ref (.blk nb) 0 }

end Zlib.Inflate.Proofs
