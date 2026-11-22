import ZlibF.Runtime.Ptr

/-!
# Natural-offset pointer arithmetic for implementation proofs

These helpers use the runtime's checked pointer addition. The rules retain the
same live-array, bounds and subtraction premises as the runtime lemmas.
-/

namespace ZlibF.Proof.PointerArithmetic
open C

/-- `p + n` for a pointer into an array. -/
def addNat {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (n : Int)
/-- `p - n` for a pointer into an array. -/
def subNat {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : M (Ptr R) := Ptr.add p (-(n : Int))

end ZlibF.Proof.PointerArithmetic
