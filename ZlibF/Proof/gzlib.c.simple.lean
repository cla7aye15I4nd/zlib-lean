import ZlibF.Proof.«gzlib.c.error»

/-!
# gzlib.c: `gz_intmax`, `GT_OFF`, `gzbuffer`, `gzeof`, `gztell64`, `gztell`, `gzerror`, `gzclearerr`

The functions that read or write a few fields. Each theorem says exactly what is returned and what the heap becomes;
the null-handle case is separate (`*_null`).

`PosInv s` is the numeric part of the position bookkeeping (`docs/en/proof/gzip.md`, "Positions, seeking and error ownership"):
`skip` is not negative and `x.pos + skip` is a `z_off64_t`. `gz_reset` establishes it (`resetRec_posInv`), `gzseek64`
keeps it (`gzlib.c.seek`); the read and write functions have to keep it, and `gztell64` needs it to avoid signed overflow.
-/

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- The distance `gztell64` adds to `x.pos`: `skip`, unless a read has come up short. -/
def tellSkip (s : GzState) : Int64 := if s.past != 0 then 0 else s.skip

/-- `gztell64`'s result as a number. -/
def tellPos (s : GzState) : Int := s.x.pos.toInt + (tellSkip s).toInt

/-- The numeric invariant of the position fields. -/
structure PosInv (s : GzState) : Prop where
  skip_nonneg : 0 ≤ s.skip.toInt
  lo : -9223372036854775808 ≤ tellPos s
  hi : tellPos s < 9223372036854775808

/-- `z_off_t` is `long`: the same 64 bits as `z_off64_t`. -/
def IsLit (r : BPtr) (t : String) : Prop := ∃ i, r = .ref (.str i) 0 ∧ strTable[i]? = some t

/-- The record `gzclearerr` has before it calls `gz_error`: a reader clears `eof` and `past`. -/
def clearRec (s : GzState) : GzState := if s.mode == GZ_READ then { s with eof := 0, past := 0 } else s

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

/-! ## gz_intmax, GT_OFF -/

/-- `GT_OFF(x)` is false for every `x`: `sizeof(int) == sizeof(z_off64_t)` is false, and `gz_intmax` is not called. -/
theorem GT_OFF_run (x : UInt32) (h : Heap) : GT_OFF x h = .ok (false, h) := by
  simp [GT_OFF]

/-! ## gzbuffer -/

/-! ## gzeof -/

/-! ## gztell64, gztell -/

theorem gztell64_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s) :
    gztell64 (hnd gs) h = .ok (Int64.ofInt (tellPos s), h) := by
  have hs := hG.hs
  have e := i64add_run s.x.pos (tellSkip s) (by have := hP.lo; unfold tellPos at this; omega)
    (by have := hP.hi; unfold tellPos at this; omega) h
  unfold gztell64
  rcases hG.mode with hm | hm
  · by_cases hp : s.past = 0
    · gsimp [hs, hm, hp]
      simpa [tellSkip, tellPos, hp] using e
    · gsimp [hs, hm, hp]
      simpa [tellSkip, tellPos, hp] using e
  · by_cases hp : s.past = 0
    · gsimp [hs, hm, hp, GZ_READ, GZ_WRITE]
      simpa [tellSkip, tellPos, hp] using e
    · gsimp [hs, hm, hp, GZ_READ, GZ_WRITE]
      simpa [tellSkip, tellPos, hp] using e

/-- **gztell64.** The result is `x.pos + (past ? 0 : skip)` as a number; the heap is unchanged. -/
theorem gztell64_spec {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s) :
    ∃ r, C.run (gztell64 (hnd gs)) h = .ok (r, h) ∧ r.toInt = tellPos s := by
  refine ⟨_, gztell64_run hG hP, i64_toInt_ofInt hP.lo hP.hi⟩

/-- `gztell` on a handle with `GzGood` and `PosInv`: returns `x.pos + (past ? 0 : skip)` as a number; no fault (`PosInv` rules out signed overflow); the heap is unchanged. -/
theorem gztell_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (hP : PosInv s) :
    gztell (hnd gs) h = .ok (Int64.ofInt (tellPos s), h) := by
  unfold gztell
  simp [bind_app, gztell64_run hG hP]

/-! ## gzerror -/

/-- `gzerror(NULL, errnum)` returns NULL and does not change the heap, whatever `errnum` is. -/
theorem gzerror_null_file (errnum : BPtr) (h : Heap) : gzerror none errnum h = .ok (.null, h) := rfl

/-! ## gzclearerr -/

/-- `gzclearerr(NULL)` does nothing: no fault, the heap is unchanged. -/
theorem gzclearerr_null (h : Heap) : gzclearerr none h = .ok ((), h) := rfl

theorem GzGood.clearRec {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) : GzGood (setS h gs (clearRec s)) gs (clearRec s) := by
  refine GzGood.withRec hG (Or.inl (by unfold Spec.clearRec; split <;> rfl)) (by unfold Spec.clearRec; split <;> rfl)
    (by unfold Spec.clearRec; split <;> rfl) (by unfold Spec.clearRec; split <;> rfl) (by unfold Spec.clearRec; split <;> rfl)
    (by intro hh; have := hG.memerr (by unfold Spec.clearRec at hh; split at hh <;> exact hh); unfold Spec.clearRec; split <;> exact this)

end Zlib.Gzlib.Proofs
