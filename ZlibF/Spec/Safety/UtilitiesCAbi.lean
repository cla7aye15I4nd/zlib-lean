import ZlibF.Spec.Common.Utilities
import ZlibF.Zlib.«compress.c»

/-!
# C-ABI pointer-cell compressor safety goals

Safety goals for the pointer-cell `destLen : PtrU64` compressor entrypoints
(`compress2_z_c`, `compress2_c`, `compress_z_c`, `compress_c`) lowered to C by
`Lean2C.Simple` (`ZlibF/Zlib/compress.c.lean`).
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec
set_option autoImplicit false

/-- **Safety of a pointer-cell compressor entry**: runs without undefined behavior (`C.run … = .ok`),
returns `Z_STREAM_ERROR` without mutating objects on rejected arguments, writes at most `capacity`
bytes at `dest` and the resulting length to `destLen`, releases all temporary allocations, and
blames `Z_MEM_ERROR` only on an allocator failure. -/
def CompressorCSafety
    (program : BPtr → BPtr → BPtr → UInt64 → M Int32)
    (nullableLength : Bool) : Prop :=
  ∀ h dest destLen source capacity n xs,
    Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (nullableLength = false → destLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat xs) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    Separate source n.toNat dest capacity.toNat →
    Separate destLen 8 dest capacity.toNat →
    Separate destLen 8 source n.toNat →
    ∃ rc after,
      C.run (program dest destLen source n) h = .ok (rc, after) ∧
      (compressRejected dest (if destLen = .null then none else some capacity) source n →
        rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape h after) ∧
      (destLen ≠ .null → (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out got h₁ expected,
          Store h dest out h₁ ∧
          Store h₁ destLen (lengthBytes got) expected ∧
          SameObjectsUpToTableShape expected after ∧
          out.length ≤ capacity.toNat ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

/-- Safety of C-ABI `compress2_z_c` (`CompressorCSafety`). -/
def Goal.compress2_z_c_safety : Prop :=
  ∀ level, CompressorCSafety (fun d dl s n => Zlib.Compress.compress2_z_c d dl s n level) true

/-- Safety of C-ABI `compress2_c` (`CompressorCSafety`). -/
def Goal.compress2_c_safety : Prop :=
  ∀ level, CompressorCSafety (fun d dl s n => Zlib.Compress.compress2_c d dl s n level) false

/-- Safety of C-ABI `compress_z_c` (`CompressorCSafety`). -/
def Goal.compress_z_c_safety : Prop :=
  CompressorCSafety Zlib.Compress.compress_z_c true

/-- Safety of C-ABI `compress_c` (`CompressorCSafety`). -/
def Goal.compress_c_safety : Prop :=
  CompressorCSafety Zlib.Compress.compress_c false

end ZlibF.Spec.Public