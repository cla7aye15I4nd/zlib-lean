import ZlibF.Spec.Common.Inflate.InflateRootTable

/-!
# Bounds of a root link and its second-level entries

These facts are outputs of actual table construction. The slow decoder uses
bits+op to index the subtable and bits+leaf.bits for its fit test.
-/
namespace Zlib.Inftrees.Spec.Subtable
open C Zlib.Inftrees Zlib.Inftrees.Proofs

def IsLink (type : UInt32) (entry : Code) : Bool :=
  if type = LENS then entry.op != 0 && (entry.op &&& 0xf0) == 0
  else (entry.op &&& 0xf0) == 0

def Safe (ca : Array Code) (offset : Nat) (link : Code) : Prop :=
  1 ≤ link.bits.toNat ∧ 1 ≤ link.op.toNat ∧
    link.bits.toNat + link.op.toNat ≤ 15 ∧
    offset + link.val.toNat + 2 ^ link.op.toNat ≤ ca.size ∧
    ∀ j, j < 2 ^ link.op.toNat →
      ∃ entry, ca[offset + link.val.toNat + j]? = some entry ∧
        1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ link.op.toNat

end Zlib.Inftrees.Spec.Subtable
