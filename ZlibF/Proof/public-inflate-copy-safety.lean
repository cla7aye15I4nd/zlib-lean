import ZlibF.Proof.«public-inflate-copy»
import ZlibF.Proof.«public-stream-refusal»
import ZlibF.Spec.Safety.Copy

/-!
# Safety of `inflateCopy`

`Goal.inflateCopy_safety` from the full contract `Goal.inflateCopy`
(`Zlib.Inflate.Proofs.inflate_copy_public`): the copied contents are dropped, and the success
branch gives the reachable destination by `StreamReachable.inflateCopy`.
-/

namespace ZlibF.Spec.Public.InflateCopySafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

/-- `Goal.inflateCopy_safety`: `inflateCopy` refuses null arguments and is safe from every reachable source into a distinct destination record; on `Z_OK` the copy is reachable, on `Z_MEM_ERROR` nothing leaks; from `Zlib.Inflate.Proofs.inflate_copy_public`. An inconsistent source is refused by the copy clause of `Goal.inflate_refusal`. -/
theorem inflateCopy_safety : Goal.inflateCopy_safety := by
  obtain ⟨hnull, hnone, hmain⟩ := Zlib.Inflate.Proofs.inflate_copy_public
  refine ⟨hnull, hnone, ?_, fun h source dest oldDest dget hr =>
    ZlibF.Spec.Public.RefusalProof.inflate_refusal.2.2.2.2.2.2 h dest oldDest (some source) dget hr⟩
  intro h source i z s dest oldDest reach good alloc diff destGet
  obtain ⟨rc, after, hrun, hsrc, hst, hfr, hbr⟩ :=
    hmain h source i z s dest oldDest reach good alloc diff destGet
  refine ⟨rc, after, hrun, hsrc, hst, hfr, ?_⟩
  rcases hbr with hmem | ⟨hrc, copied, hgood, -, -, -, hfresh, hl⟩
  · exact Or.inl hmem
  · subst hrc
    exact Or.inr ⟨rfl, StreamReachable.inflateCopy reach diff destGet hrun,
      copied, hgood.live.hs, hfresh, hl⟩

end ZlibF.Spec.Public.InflateCopySafetyProof
