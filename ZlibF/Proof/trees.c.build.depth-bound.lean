import ZlibF.Proof.«trees.c.build.weight-values»
import ZlibF.Math.DeflateHuffmanDepth

/-! # Fibonacci levels rule out wrap in the actual depth bytes -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- Both the mathematical levels and the source depth bytes are bounded.
The last field rules out wrap in every actual parent-depth update. -/
structure BTDepthBound (tk : TK) (N K : Nat) (d : DeflateState) : Prop where
  level : ∀ q, 574 - 2 * K ≤ q → q < 573 →
    GB.clK (Hn d) (574 - 2 * K) N 1000 (2 * (K - 1)) (Hn d q) ≤ 22
  height : ∀ q, 574 - 2 * K ≤ q → q < 573 → d.depth[Hn d q]!.toNat ≤ 22
  nowrap : ∀ a, a < K - 1 →
    max d.depth[Hn d (572 - 2 * a)]!.toNat d.depth[Hn d (571 - 2 * a)]!.toNat + 1 < 256

end Zlib.Trees.Proofs
