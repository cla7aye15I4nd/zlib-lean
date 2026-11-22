import ZlibF.Spec.Common.Inflate.InflateTableSafety

/-!
# The returned extent of a decoding table

The constructor returns a pointer just past the storage it used. A later table may be
built in the same array at that pointer. Decoder safety must therefore depend only on
cells before the returned pointer, rather than on the size of the backing array.
-/

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- All root cells and every second-level cell that the decoder may read lie before the
returned end. This is a property of a successful constructor result, not an input
assumption. -/
def TableReadExtent (type : UInt32) (ca : Array Code) (offset root used : Nat) : Prop :=
  1 ≤ root ∧ root ≤ 15 ∧ offset + 2 ^ root ≤ offset + used ∧
    ∀ i, i < 2 ^ root →
      let entry := ca.getD (offset + i) default
      ((type = LENS ∧ Zlib.Inffast.Spec.LenLink entry) ∨
       (type = DISTS ∧ Zlib.Inffast.Spec.DistLink entry)) →
      offset + entry.val.toNat + 2 ^ entry.op.toNat ≤ offset + used

end Zlib.Inftrees.Spec
