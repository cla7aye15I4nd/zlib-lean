import ZlibF.Proof.«inflate.c.main.check0»
import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«adler32.c»

/-!
# inflate.c: the trailer modes `LENGTH` and `CHECK`

`case LENGTH:` and `case CHECK:` of `inflate()`, and the fall-through `DONE`. Every exit and every error message.
`CHECK` calls `crc32` or `adler32` on the output written by this call; the callee theorems `crc32_z_correct` and
`adler32_z_correct` give the value.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- `case LENGTH:` with no length to check (`wrap = 0` or `flags = 0`): `state->mode = DONE; ret = Z_STREAM_END;
goto inf_leave`. -/
theorem inflate_LENGTH_skip {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hno : s.wrap = 0 ∨ s.flags = 0) :
    runX (inflate_LENGTH c) l h =
      .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), setI h zs { s with mode := DONE }) := by
  have hb : ¬ (¬ s.wrap = 0 ∧ ¬ s.flags = 0) := by
    rcases hno with e | e <;> simp [e]
  unfold inflate_LENGTH
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hb, setMode, wrI_eq, inflate_DONE, runX_modify, runX_throw]

/-- `case LENGTH:` with a length to check (`wrap ≠ 0`, `flags ≠ 0`): `NEEDBITS(32)`; if the input ran out, `goto inf_leave` with
the registers of that moment; else, when `(wrap & 4)` is set and `hold` differs from the low 32 bits of `total`, the error
"incorrect length check" (`BAD`, `break`); else `INITBITS`, `mode = DONE`, `ret = Z_STREAM_END`, `goto inf_leave`.
`bs` are the input bytes not yet pulled; the bit stream is preserved. -/
theorem inflate_LENGTH_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (hw : s.wrap ≠ 0) (hf : s.flags ≠ 0) (B : BitInv h l bs) :
    ∃ rr l' j, runX (NEEDBITS 32) l h = .ok ((rr, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧
      (rr = .error Ex.leave → l'.have_ = 0 ∧ j = bs.length ∧ l'.bits.toNat < 32 ∧
        runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, l'), h)) ∧
      (rr = .ok () → 32 ≤ l'.bits.toNat ∧
        ((s.wrap &&& 4) ≠ 0 → l'.hold ≠ (s.total &&& 0xffffffff) →
          ∃ i, strTable[i]? = some "incorrect length check" ∧
            runX (inflate_LENGTH c) l h = .ok ((.ok (), l'), tcBadHeap h r zs z s i)) ∧
        (¬ ((s.wrap &&& 4) ≠ 0 ∧ l'.hold ≠ (s.total &&& 0xffffffff)) →
          runX (inflate_LENGTH c) l h = .ok ((.error Ex.leave, { l' with hold := 0, bits := 0, ret := Z_STREAM_END }),
            setI h zs { s with mode := DONE }))) := by
  obtain ⟨rr, l', j, hrun, hj, B', hS, hbits, hshape, hmax, hid, hok, hleave⟩ := NEEDBITS_run B 32 (by decide)
  have hw' : ¬ s.wrap = 0 := hw
  have hf' : ¬ s.flags = 0 := hf
  refine ⟨rr, l', j, hrun, hj, B', hS, ?_, ?_⟩
  · intro e
    obtain ⟨h1, h2, h3⟩ := hleave e
    refine ⟨h2, h1, h3, ?_⟩
    unfold inflate_LENGTH
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, hw', hf', hrun, e]
  · intro e
    refine ⟨hok e, ?_, ?_⟩
    · intro h4 hne
      obtain ⟨i, hi, hbad⟩ := tcBadMode_run (c := c) "incorrect length check" lit_length_check hr hc hz hs
      refine ⟨i, hi, ?_⟩
      unfold inflate_LENGTH
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, hs, hw', hf', hrun, e, runX_get, h4, hne, hbad, runX_pure]
    · intro hn
      unfold inflate_LENGTH
      rw [hc]
      have hn' : ¬ (¬ s.wrap &&& 4 = 0 ∧ ¬ l'.hold = s.total &&& 4294967295) := hn
      simp [runX_bind, runX_lift, ldI_eq, hs, hw', hf', hrun, e, runX_get, hn', runX_INITBITS, setMode, wrI_eq,
        inflate_DONE, runX_modify, runX_throw]

/-! ### `case CHECK:` -/

/-- The condition of `if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(...)`. -/
def chkCond (s : InflateState) (out : UInt32) : Bool := (s.wrap &&& 4) != 0 && out != 0

/-- The stream record after the accounting of `CHECK`: `total_out += out` and, when the check is updated, `adler = v`. -/
def chkZ (z : ZStream) (s : InflateState) (out : UInt32) (v : UInt64) : ZStream :=
  { z with total_out := z.total_out + out.toUInt64, adler := if chkCond s out then v else z.adler }

/-- The state record after the accounting of `CHECK`: `total += out` and, when the check is updated, `check = v`. -/
def chkS (s : InflateState) (out : UInt32) (v : UInt64) : InflateState :=
  { s with total := s.total + out.toUInt64, check := if chkCond s out then v else s.check }

/-- The heap after the accounting of `CHECK`. -/
def chkH (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (out : UInt32) (v : UInt64) : Heap :=
  setI (r.put h (chkZ z s out v)) zs (chkS s out v)

/-- `case CHECK:` with `wrap = 0`: no check; `state->mode = LENGTH` and the fall-through into `LENGTH`. -/
theorem inflate_CHECK_nowrap {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (hw : s.wrap = 0) :
    runX (inflate_CHECK c) l h = runX (inflate_LENGTH c) l (setI h zs { s with mode := LENGTH }) := by
  unfold inflate_CHECK
  rw [hc]
  simp [runX_bind, runX_lift, ldI_eq, hs, hw, setMode, wrI_eq]

/-- `put` addresses the byte `off` of the block `blk` (bytes `a`), and the `out` bytes before it are inside the block. -/
def PutAt (h : Heap) (put : BPtr) (out : UInt32) (blk off : Nat) (a : Array UInt8) : Prop :=
  put = .ref (.blk blk) off ∧ h.bytes blk = some a ∧ out.toNat ≤ off ∧ off ≤ a.size

end Zlib.Inflate.Proofs
