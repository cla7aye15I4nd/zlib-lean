import ZlibF.Spec.Common.ByteAddress

/-!
# Goals of the CRC low-address-bit model

The address goals stated over `ZlibF/Spec/Common/ByteAddress.lean`.
-/

namespace C.ByteAddress.Spec

def Goal.address_read_is_pure : Prop :=
  ∀ (h : Heap) (p : BPtr),
    C.run (Zlib.Crc32.addrOf p) h = .ok (value h p, h)

def Goal.raw_block_unchanged : Prop :=
  ∀ (h : Heap) (block offset : Nat),
    C.run (Zlib.Crc32.addrOf (.ref (.blk block) offset)) h =
      .ok (UInt64.ofNat offset, h)

/-- Every concrete non-block origin residue is representable. No static
or embedded field is forced to be aligned. -/
def Goal.every_layout_is_representable : Prop :=
  ∀ physicalBase : BRef → Nat,
    (∀ block, physicalBase (.blk block) % 8 = 0) →
    ∃ h : Heap, ModelsLowBits h physicalBase

/-- Every existing heap admits any concrete non-block layout, while all
pre-existing storage and allocation choices stay exactly the same. -/
def Goal.every_existing_heap_accepts_layout : Prop :=
  ∀ (h : Heap) (physicalBase : BRef → Nat),
    (∀ block, physicalBase (.blk block) % 8 = 0) →
    ModelsLowBits (withLayout h physicalBase) physicalBase ∧
      SameStorage h (withLayout h physicalBase)

/-- The source cast followed by its mask agrees with the actual base plus
offset, including unsigned wrap before masking. -/
def Goal.mask_refines_base_plus_offset : Prop :=
  ∀ (h : Heap) (physicalBase : BRef → Nat), ModelsLowBits h physicalBase →
    ∀ (ref : BRef) (offset : Nat),
      low (value h (.ref ref offset)) = (physicalBase ref + offset) % 8

def Goal.pointer_advance_preserves_low_bits : Prop :=
  ∀ (h : Heap) (ref : BRef) (offset count : Nat),
    low (value h (.ref ref (offset + count))) =
      (low (value h (.ref ref offset)) + count) % 8

/-- The first aligned position lies at most seven bytes ahead. A source
loop may exhaust its input earlier; this is a position-arithmetic claim. -/
def Goal.first_aligned_offset : Prop :=
  ∀ (h : Heap) (ref : BRef) (offset : Nat),
    let count := (8 - low (value h (.ref ref offset))) % 8
    count ≤ 7 ∧ low (value h (.ref ref (offset + count))) = 0 ∧
      ∀ before, before < count → low (value h (.ref ref (offset + before))) ≠ 0

def Goal.byte_stores_preserve_bases : Prop :=
  ∀ (h : Heap) (ref : BRef) (bytes : Array UInt8),
    (Space.put h ref bytes).byteBase = h.byteBase

def Goal.byte_modifies_preserve_bases : Prop :=
  ∀ (h : Heap) (ref : BRef) (modify : Array UInt8 → Array UInt8),
    (Space.modify h ref modify).byteBase = h.byteBase

end C.ByteAddress.Spec
