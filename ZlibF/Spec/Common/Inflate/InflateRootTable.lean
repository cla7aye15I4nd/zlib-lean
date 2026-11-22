import ZlibF.Spec.Common.Inflate.InflateTableContent

/-!
# Positive code lengths in a constructed root table

Array bounds alone do not ensure that a lookup consumes a positive number
of bits. This local predicate is established by the actual constructor,
including empty and singleton-invalid entries.
-/
namespace Zlib.Inftrees.Spec.RootTable
open C Zlib.Inftrees Zlib.Inftrees.Proofs

def Safe (ca : Array Code) (offset root : Nat) : Prop :=
  1 ≤ root ∧ root ≤ 15 ∧ offset + 2 ^ root ≤ ca.size ∧
    ∀ i, i < 2 ^ root →
      ∃ entry, ca[offset + i]? = some entry ∧
        1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ root

end Zlib.Inftrees.Spec.RootTable
