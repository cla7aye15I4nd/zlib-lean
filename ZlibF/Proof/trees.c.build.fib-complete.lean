import ZlibF.Proof.«trees.c.build.fib-codes»
import ZlibF.Proof.«trees.c.build.weight-values»

/-! # The complete actual source constructor establishes FibPush -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- FibPush refers to actual final stored lengths. The natural weights
are retained before gen_codes reuses their union fields. Their total is
bounded by the original leaf mass plus the at-most-two dummy writes. -/
def BTFibResult (tk : TK) (N : Nat) (original result : DeflateState) : Prop :=
  ∃ (prepared built : DeflateState) (mc : Int32) (K : Nat),
    BTBuilt tk N K mc prepared built ∧
    frn (tk.arr built) (Hn built (574 - 2 * K)) ≤ mass (fun v => (btFreq tk original v).toNat) N + 2 ∧
    HuffmanAbstract.FibPushR (LeafRank.count (Hn built) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (frn (tk.arr built) (Hn built (574 - 2 * K)))
      (LeafRank.value (Hn built) (frn (tk.arr built)) (574 - 2 * K) (K - 1) mc.toInt.toNat)
      (LeafRank.value (Hn built) (curL (tk.arr result)) (574 - 2 * K) (K - 1) mc.toInt.toNat)

end Zlib.Trees.Proofs
