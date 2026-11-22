import ZlibF.Spec.Common.Inflate.InflateSubtable
import ZlibF.Spec.Common.Inflate.InflateTableExtent

/-!
# Goals of the table constructor

What the actual `inflate_table` establishes, stated over the table definitions in
`ZlibF/Spec/Common/Inflate/`.
-/

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- On every existing `CallPre`, the real translated function returns and retains both the
safety result and its constructed table contents. Rejected and oversized tables are allowed.
This is an internal table-builder obligation; it does not by itself establish decoder safety. -/
def Goal.inflate_table_content : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      RetInfo type pre.f codes.toNat r ∧ TableContent type pre.f codes.toNat rc oc r after

end Zlib.Inftrees.Spec

namespace Zlib.Inftrees.Spec.RootTable
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- Every successful actual table construction gives the root-entry bounds
needed by lookup1. No validity of the compressed input is assumed. -/
def Goal.constructor_root_bits : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (_pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∃ ca : Array Code,
        Space.get after rc = some ca ∧ Safe ca oc r.2.2.toNat)

end Zlib.Inftrees.Spec.RootTable

namespace Zlib.Inftrees.Spec.Subtable
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- Each actual root link has a bounded subtable of positive-length leaves.
Empty and singleton tables are included and must not invent links. -/
def Goal.constructor_subtable_bits : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (_pre : CallPre h type rl ol codes rc oc bits rw ow),
    (type = LENS ∨ type = DISTS) →
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      (r.1 = 0 → ∃ ca : Array Code,
        Space.get after rc = some ca ∧ RootTable.Safe ca oc r.2.2.toNat ∧
        ∀ i entry, i < 2 ^ r.2.2.toNat → ca[oc + i]? = some entry →
          IsLink type entry = true → entry.bits.toNat = r.2.2.toNat ∧ Safe ca oc entry)

end Zlib.Inftrees.Spec.Subtable

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- Successful construction establishes every table predicate that the slow and fast
decoders use. The real call and existing safety frame remain explicit. The input lengths
may be empty, incomplete, oversubscribed or too large for the capacity; error returns are
allowed. No table property or callee contract is an input hypothesis. -/
def Goal.inflate_table_decoder_safe : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        1 ≤ r.2.2.toNat ∧ r.2.2.toNat ≤ 15 ∧
        (type = CODES → CodeLengthTableSafe ca oc r.2.2.toNat) ∧
        (type = LENS → Zlib.Inffast.Spec.LenTableSafe ca oc r.2.2.toNat) ∧
        (type = DISTS → Zlib.Inffast.Spec.DistTableSafe ca oc r.2.2.toNat))

end Zlib.Inftrees.Spec

namespace Zlib.Inftrees.Spec
open C Zlib.Inftrees Zlib.Inftrees.Proofs

/-- The actual builder bounds its returned extent and establishes both the decoder
predicate and the extent needed when a following table reuses the same array. Accepted
empty and single-symbol codes are included. -/
def Goal.inflate_table_read_extent : Prop :=
  ∀ (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (codes : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (pre : CallPre h type rl ol codes rc oc bits rw ow),
    ∃ r after,
      C.run (inflate_table type (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (r, after) ∧
      Result h rw rc ow oc (capOf type) codes.toNat pre.wa pre.ca (.ref rc oc) bits r after ∧
      (r.1 = 0 → ∃ (ca : Array Code) (used : Nat),
        Space.get after rc = some ca ∧
        r.2.1 = .ref rc (oc + used) ∧ used ≤ capOf type ∧
        TableReadExtent type ca oc r.2.2.toNat used ∧
        (type = CODES → CodeLengthTableSafe ca oc r.2.2.toNat) ∧
        (type = LENS → Zlib.Inffast.Spec.LenTableSafe ca oc r.2.2.toNat) ∧
        (type = DISTS → Zlib.Inffast.Spec.DistTableSafe ca oc r.2.2.toNat))

end Zlib.Inftrees.Spec
