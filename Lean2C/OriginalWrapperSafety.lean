import Lean2C.OriginalCompress
import Lean2C.OriginalUncompressReturn
import ZlibF.Proof.«public-compress-safe-c»
import ZlibF.Proof.«public-uncompress-safe»

/-! Apply the library safety proofs directly to the imported original (`false`) or generated
(`true`) wrapper. Both statements use the common LP64 raw-length-cell domain. -/

namespace Lean2C.OriginalWrapperSafety
open C ZlibF.Spec ZlibF.Spec.Public

/-- On accepted compressor arguments the imported call returns, the output fits,
and its final heap contains precisely the output and the little-endian length write
up to the registered allowance for table shapes. -/
theorem compress {h : Heap} {dest src : BPtr} {block offset : Nat} {capacity n : UInt64}
    {bytes : List UInt8} (generated : Bool) (level : Int32) (aligned : UInt64.ofNat offset % 8 = 0)
    (nonnull : dest ≠ .null) (validSrc : src = .null → n = 0)
    (fresh : Fresh h) (uniq : Zlib.Deflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (cell : LengthCell h (.ref (.blk block) offset) capacity)
    (input : src ≠ .null → Bytes h src n.toNat bytes) (output : Writable h dest capacity.toNat)
    (apart : Separate src n.toNat dest capacity.toNat)
    (outCell : Separate (.ref (.blk block) offset) 8 dest capacity.toNat)
    (inCell : Separate (.ref (.blk block) offset) 8 src n.toNat) :
    let dl := Ptr.ref (BRef.blk block) offset
    ∃ rc after out got mid expected, C.run (OriginalCompress.source generated dest dl src n level) h = .ok (rc, after) ∧
      Store h dest out mid ∧ Store mid dl (lengthBytes got) expected ∧ SameObjectsUpToTableShape expected after ∧
      out.length ≤ capacity.toNat ∧ (rc = Z_MEM_ERROR → AllocationFailed h after) := by
  dsimp only
  rw [OriginalCompress.source_abi generated dest src block offset n level aligned nonnull]
  obtain ⟨rc, after, run, _, accepted⟩ := Proofs.Compress.compress2_z_c_safety_pub level h dest
    (.ref (.blk block) offset) src capacity n bytes fresh uniq globals fit (fun _ => cell)
    (fun _ => by simp) input (fun _ => output) apart outCell inCell
  obtain ⟨out, got, mid, expected, result⟩ := accepted (by simp) validSrc (fun eq => (nonnull eq).elim)
  exact ⟨rc, after, out, got, mid, expected, run, result⟩

/-- On accepted decompressor arguments the imported computation returns, writes within
the output capacity, records both counts in C order and satisfies the original heap frame.
The registered public safety theorem requires separate length cells. -/
theorem uncompress {h : Heap} {dest src : BPtr} {sb so db destOff : Nat} {capacity n : UInt64}
    {bytes : List UInt8} (generated : Bool)
    (srcAligned : UInt64.ofNat so % 8 = 0) (dstAligned : UInt64.ofNat destOff % 8 = 0)
    (validSrc : src = .null → n = 0) (validDst : dest = .null → capacity = 0)
    (fresh : Fresh h) (uniq : Zlib.Inflate.Spec.Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (outCell : LengthCell h (.ref (.blk db) destOff) capacity) (inCell : LengthCell h (.ref (.blk sb) so) n)
    (input : src ≠ .null → Bytes h src n.toNat bytes) (output : dest ≠ .null → Writable h dest capacity.toNat)
    (apart : UtilitySeparation dest capacity.toNat src n.toNat (.ref (.blk db) destOff) (.ref (.blk sb) so)) :
    let dl := Ptr.ref (BRef.blk db) destOff
    let sl := Ptr.ref (BRef.blk sb) so
    ∃ rc after out got consumed h₁ h₂ expected,
      C.run (OriginalUncompress.source generated dest dl src sl) h = .ok (rc, after) ∧
      StorePrefix h dest out capacity.toNat h₁ ∧ Store h₁ sl (lengthBytes consumed) h₂ ∧
      Store h₂ dl (lengthBytes got) expected ∧ SameObjectsUpToTableShape expected after ∧
      out.length ≤ capacity.toNat ∧ consumed.toNat ≤ n.toNat ∧
      (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR) ∧
      (got.toNat = out.length ∨ (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity ∧ consumed = n)) ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) := by
  dsimp only
  rw [OriginalUncompress.source_abi generated dest src sb so db destOff srcAligned dstAligned]
  obtain ⟨rc, after, run, _, accepted⟩ := Proofs.Uncompress.uncompress2_z_safe h dest
    (.ref (.blk db) destOff) src (.ref (.blk sb) so) capacity n bytes fresh uniq globals fit
    (fun _ => outCell) (fun _ => inCell) (fun _ => ⟨by simp, by simp⟩) input output apart
  obtain ⟨out, got, consumed, h₁, h₂, expected, result⟩ := accepted (by simp) (by simp) validSrc validDst
  exact ⟨rc, after, out, got, consumed, h₁, h₂, expected, run, result⟩

#print axioms compress
#print axioms uncompress
end Lean2C.OriginalWrapperSafety
