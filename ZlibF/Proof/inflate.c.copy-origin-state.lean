import ZlibF.Proof.«inflate.c.default-origin-state»
import ZlibF.Proof.«inflate.c.copy-window-heap»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual copy's pointer relocation keeps the dynamic-base or paired
fixed-table origin, now relative to the new decoder record. -/
theorem CopyTableOrigin.relocated {old : Nat} {s : InflateState}
    (origin : CopyTableOrigin old s) (dest : ZStreamRef) (fresh nextOff distOff : Nat)
    (window : BPtr) : CopyTableOrigin fresh (copiedGeneric dest old fresh nextOff distOff window s) := by
  rcases origin with dynamic | fixed
  · exact Or.inl (by simp only [copiedGeneric, dynamic, ↓reduceIte])
  · have different : s.lencode ≠ .ref (.istate_codes old) 0 := by
      rw [fixed.1]
      intro impossible
      cases impossible
    exact Or.inr (by simpa only [copiedGeneric, different, ↓reduceIte] using fixed)

end Zlib.Inflate.Proofs
