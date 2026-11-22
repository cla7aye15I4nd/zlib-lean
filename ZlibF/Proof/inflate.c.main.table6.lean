import ZlibF.Proof.«inflate.c.main.table5»

/-!
# inflate.c: `case LENLENS:` as a whole
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The state record after both loops of `LENLENS` ran to the end (`M = ncode - have`). -/
def llDone (s : InflateState) (S : List Bool) : InflateState :=
  lzSt (llSt s S (s.ncode.toNat - s.«have».toNat)) (19 - (llSt s S (s.ncode.toNat - s.«have».toNat)).«have».toNat)

theorem llDone_lens (s : InflateState) (S : List Bool) (hnc : s.ncode.toNat ≤ 19) (hhn : s.«have».toNat ≤ s.ncode.toNat) :
    (llDone s S).lens = lensZero (lensRead s.lens s.«have».toNat S (s.ncode.toNat - s.«have».toNat)) s.ncode.toNat
      (19 - s.ncode.toNat) := by
  have h1 := llSt_have s S (s.ncode.toNat - s.«have».toNat) (by omega)
  unfold llDone lzSt llSt
  simp only [llSt] at h1 ⊢
  rw [h1]
  have e : s.«have».toNat + (s.ncode.toNat - s.«have».toNat) = s.ncode.toNat := by omega
  rw [e]

end Zlib.Inflate.Proofs
