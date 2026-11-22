import ZlibF.Runtime.Address
import ZlibF.Runtime.Ptr
import ZlibF.Zlib.«crc32.c»

/-!
# Obligations for the CRC low-address-bit model

These definitions state the metadata interpretation independently of checksum
arithmetic. Non-block origins range over all residues. Raw blocks retain
the existing aligned-origin convention; general ABI layout is not claimed.
-/

namespace C.ByteAddress.Spec

/-- The exact integer observation made by the CRC alignment condition. -/
def low (value : UInt64) : Nat := (value &&& 7).toNat

/-- A concrete base-address assignment agrees with the model where the
program observes it. This is a representation relation, not a caller
contract required by the general checksum theorem. -/
def ModelsLowBits (h : Heap) (physicalBase : BRef → Nat) : Prop :=
  ∀ ref, physicalBase ref % 8 = base h ref

/-- Assign concrete low address bits without rebuilding the existing heap. -/
def withLayout (h : Heap) (physicalBase : BRef → Nat) : Heap :=
  { h with byteBase := fun ref =>
      ⟨physicalBase ref.toBRef % 8, Nat.mod_lt _ (by decide)⟩ }

/-- All heap components that predate the address metadata are unchanged. -/
def SameStorage (before after : Heap) : Prop :=
  after.bytes = before.bytes ∧ after.words = before.words ∧
  after.ro = before.ro ∧ after.streams = before.streams ∧
  after.gzheaders = before.gzheaders ∧ after.dstates = before.dstates ∧
  after.istates = before.istates ∧ after.gzstates = before.gzstates ∧
  after.static = before.static ∧ after.nextBlk = before.nextBlk ∧
  after.nalloc = before.nalloc ∧ after.allocOk = before.allocOk ∧
  after.garbage = before.garbage

end C.ByteAddress.Spec
