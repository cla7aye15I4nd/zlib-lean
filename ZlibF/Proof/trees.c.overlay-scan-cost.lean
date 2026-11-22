import ZlibF.Proof.«trees.c.universal-overlay-costs»
import ZlibF.Math.DeflateOverlayTiny

/-!
# trees.c: reference bit-length symbol weights under `κ0`

Defines `refWeight`, the bit cost of each bit-length symbol `0..18` under the 7-bit reference code
`κ0` (`DeflateOverlayTiny.refLen`) plus `blExtraBits`. Region-charged scan bounds live in
`trees.c.overlay-scan-region`.
-/

namespace Zlib.Trees.Proofs.Out
open ZlibF.Math.DeflateOverlayTiny (refLen)
set_option autoImplicit false

/-- The cost of bit-length symbol `k` under `κ0`, extra bits included. -/
def refWeight (k : Nat) : Nat := refLen k + blExtraBits k

theorem blExtraBits_zero {x : Nat} (small : x ≤ 15) : blExtraBits x = 0 := by
  simp [blExtraBits, show x ≠ 16 by omega, show x ≠ 17 by omega, show x ≠ 18 by omega]

end Zlib.Trees.Proofs.Out
