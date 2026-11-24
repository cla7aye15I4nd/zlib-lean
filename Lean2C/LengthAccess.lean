import Lean2C.Soundness
import ZlibF.Proof.«public-uncompress-memory»

namespace Lean2C.LengthAccess
open C CSource Semantics ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.Uncompress (load64_cell store64_writable)

/-- For an existing length cell, eight-byte alignment is exactly the extra
condition for its typed C read to return the value promised by the byte model. -/
theorem read_cell_iff {h : Heap} {p : BPtr} {n : UInt64} (cell : LengthCell h p n) :
    readHeap .u64 p h = .ok (.u64 n) ↔ ByteAddress.value h p % 8 = 0 := by
  by_cases aligned : ByteAddress.value h p % 8 = 0
  · simp [readHeap, aligned, load64_cell cell, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [readHeap, aligned, Bind.bind, Except.bind]

/-- On a writable eight-byte region, a typed C write succeeds exactly when
aligned. The resulting heap agrees with the modeled little-endian store. -/
theorem write_cell_iff {h : Heap} {p : BPtr} (n : UInt64) (region : Writable h p 8) :
    (∃ after, writeHeap .u64 p (.u64 n) h = .ok after ∧ Store h p (lengthBytes n) after) ↔
      ByteAddress.value h p % 8 = 0 := by
  by_cases aligned : ByteAddress.value h p % 8 = 0
  · obtain ⟨after, run, stored⟩ := store64_writable n region
    refine ⟨fun _ => aligned, fun _ => ⟨after, ?_, stored⟩⟩
    have cast : evalCast .u64 (.u64 n) = .ok (.u64 n) := by simp
    simp [writeHeap, aligned, cast, run, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [writeHeap, aligned, Bind.bind, Except.bind]

end Lean2C.LengthAccess
