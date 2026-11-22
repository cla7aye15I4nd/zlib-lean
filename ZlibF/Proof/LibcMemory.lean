import ZlibF.Proof.HeapWP
import ZlibF.Proof.LibcArray

namespace C
open Std.WP
open scoped HeapWP

/-- A successful byte-block copy writes the specified destination slice and preserves any
predicate on a different block. Source and destination may occupy disjoint slices of one block. -/
theorem memcpyB_frame (dst src watched doff soff n : Nat) (da sa : Array UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ dst)
    (separate : dst ≠ src ∨ doff + n ≤ soff ∨ soff + n ≤ doff)
    (dstBound : doff + n ≤ da.size) (srcBound : soff + n ≤ sa.size) :
    ⦃ fun h => h.bytes dst = some da ∧ h.bytes src = some sa ∧
        h.ro dst = false ∧ F (h.bytes watched) ⦄
      memcpyB (.ref (.blk dst) doff) (.ref (.blk src) soff) n
    ⦃ fun _ h => h.bytes dst = some (copyRange da sa doff soff n) ∧ F (h.bytes watched) ⦄ := by
  refine ⟨fun h ⟨hd, hs, writable, frame⟩ => ?_⟩
  have run := Ptr.memcpy_ok (rd := BRef.blk dst) (rs := BRef.blk src) hd hs writable
    dstBound srcBound (by simpa using separate)
  rw [wp_run, show memcpyB _ _ n h = _ from run]
  change upd h.bytes dst _ dst = _ ∧ F (upd h.bytes dst _ watched)
  simpa [outside] using frame

/-- Frame both a separate block and every destination index outside the written slice. -/
theorem memcpyB_range_frame (dst src watched doff soff n : Nat) (da sa : Array UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ dst)
    (separate : dst ≠ src ∨ doff + n ≤ soff ∨ soff + n ≤ doff)
    (dstBound : doff + n ≤ da.size) (srcBound : soff + n ≤ sa.size) :
    ⦃ fun h => h.bytes dst = some da ∧ h.bytes src = some sa ∧
        h.ro dst = false ∧ F (h.bytes watched) ⦄
      memcpyB (.ref (.blk dst) doff) (.ref (.blk src) soff) n
    ⦃ fun _ h => h.bytes dst = some (copyRange da sa doff soff n) ∧ F (h.bytes watched) ∧
        ∀ i, i < doff ∨ doff + n ≤ i → (h.bytes dst).bind (·[i]?) = da[i]? ⦄ := by
  have spec := memcpyB_frame dst src watched doff soff n da sa F outside separate dstBound srcBound
  refine ⟨spec.entails_wp_of_post ?_⟩
  intro _ h ⟨write, kept⟩
  refine ⟨write, kept, fun i hi => ?_⟩
  simp [write, copyRange.getElem? da sa doff soff n i dstBound, show ¬ (doff ≤ i ∧ i < doff + n) by omega]

end C
