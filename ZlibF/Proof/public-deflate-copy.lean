import ZlibF.Proof.«deflate.c.copy-failure»
import ZlibF.Proof.«deflate.c.copy-success»
import ZlibF.Proof.«public-deflate-goals»
import ZlibF.Proof.«public-stream-refusal»
import ZlibF.Spec.Common.Copy
import ZlibF.Spec.Functional.Copy
import ZlibF.Spec.Safety.Copy

/-!
# `Goal.deflateCopy` and `Goal.deflateCopy_safety`

Null arguments are refused. From a reachable source, the invariant `DInv` holds
(`reachable_inv_of`), and the run splits on the allocations:
- when one of the five allocations fails, `copy_failure` applies;
- when all of them succeed, `copy_success` applies.
`Goal.deflateCopy_safety` drops the copied-content clauses.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false

/-- `deflateCopy` with a null destination refuses. -/
theorem deflateCopy_null_dest (h : Heap) (source : ZStreamPtr) :
    C.run (deflateCopy none source) h = .ok (Z_STREAM_ERROR, h) := by
  simp [C.run, deflateCopy]

/-- `deflateCopy` with a null source refuses and clears the destination state. -/
theorem deflateCopy_null_source {h : Heap} {dest : ZStreamRef} {z : ZStream} (get : dest.get h = some z) :
    C.run (deflateCopy (some dest) none) h = .ok (Z_STREAM_ERROR, dest.put h { z with state := none }) := by
  simp [C.run, deflateCopy, deflateStateCheck, zwr_eq, get]

/-- The facts of the deflate sequence proof, with no hypothesis. -/
theorem sequence_facts : SequenceFacts :=
  Call.sequence_facts_of (Block.tinyOverlay_of_two Zlib.Deflate.Engine.Proofs.tinyOverlayAt_128
    Zlib.Deflate.Engine.Proofs.tinyOverlayAt_256)

/-- **`int deflateCopy(z_streamp dest, z_streamp source)`.** Null arguments are refused. From every
reachable source into a distinct destination record the copy returns. It writes only the destination
record and new blocks, and either fails on a genuine allocation failure, releasing everything it
allocated, or succeeds with the relocated state, the copied prefixes and exactly its five new blocks
in the ledger. -/
theorem deflate_copy_public : Goal.deflateCopy := by
  refine ⟨fun h source => deflateCopy_null_dest h source,
    fun h dest z get => deflateCopy_null_source get, ?_⟩
  intro h source i z s dest oldDest reach good _ distinct destGet
  obtain ⟨ds, z1, d, inv, -, -⟩ := reachable_inv_of sequence_facts reach
  obtain ⟨e1, e2, e3⟩ := inv.unique good
  subst e1 e2 e3
  by_cases ok : h.allocOk h.nalloc = true ∧ bytePtr (copyH0 h s) ≠ .null ∧
      wordPtr (copyW (copyH0 h s) s) ≠ .null ∧ wordPtr (copyP (copyH0 h s) s) ≠ .null ∧
      bytePtr (copyQ (copyH0 h s) s) ≠ .null
  · obtain ⟨after, run, sg, st, fr, copied, rest⟩ := copy_success inv distinct destGet ok
    exact ⟨Z_OK, after, run, sg, st, fr, Or.inr ⟨rfl, copied, rest⟩⟩
  · obtain ⟨after, run, sg, st, fr, failed, dg, lc⟩ := copy_failure inv distinct destGet ok
    exact ⟨Z_MEM_ERROR, after, run, sg, st, fr, Or.inl ⟨rfl, failed, dg, lc⟩⟩

/-- **Safety of `deflateCopy`**: the safety content of `Goal.deflateCopy`; the refusal of an inconsistent
source is the copy clause of `Goal.deflate_refusal`. -/
theorem deflate_copy_safety : Goal.deflateCopy_safety := by
  obtain ⟨c1, c2, c3⟩ := deflate_copy_public
  refine ⟨c1, c2, ?_, fun h source dest oldDest dget hr =>
    ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal.2.2.2.2 h dest oldDest (some source) dget hr⟩
  intro h source i z s dest oldDest reach good alloc distinct destGet
  obtain ⟨rc, after, run, sg, st, fr, res⟩ := c3 h source i z s dest oldDest reach good alloc distinct destGet
  refine ⟨rc, after, run, sg, st, fr, ?_⟩
  rcases res with failure | ⟨ok, copied, dg, -, -, -, -, -, -, own, lc⟩
  · exact Or.inl failure
  · exact Or.inr ⟨ok, ⟨_, _, _, dg, alloc⟩, copied, dg.live.hs, own, lc⟩

end Zlib.Deflate.Universal

#print axioms Zlib.Deflate.Universal.deflate_copy_public
#print axioms Zlib.Deflate.Universal.deflate_copy_safety
