import ZlibF.Spec.Common.Inflate.InflateTableContent
import ZlibF.Spec.Common.Inflate.FastTable

/-!
# Table predicates established by the actual constructor

This obligation connects construction to the predicates used by the decoder. Every root
entry must be covered, including invalid entries in empty or single-symbol codes. A result
about the leaves and links that were written is insufficient by itself.
-/

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- The code-length table has no second level. Every lookup reads a nonzero number of bits
and yields a code-length alphabet symbol or an invalid marker. -/
def CodeLengthTableSafe (ca : Array Code) (offset root : Nat) : Prop :=
  1 ≤ root ∧ root ≤ 7 ∧ offset + 2 ^ root ≤ ca.size ∧
    ∀ i, i < 2 ^ root →
      let entry := ca.getD (offset + i) default
      1 ≤ entry.bits.toNat ∧ entry.bits.toNat ≤ root ∧
        ((entry.op = 0 ∧ entry.val.toNat < 19) ∨ entry.op = 64)

end Zlib.Inftrees.Spec
