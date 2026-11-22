import ZlibF.Proof.HeapWP
import ZlibF.Proof.LibcArray
import ZlibF.Runtime.LibcAllocation

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

/-- A byte-block `memmove` writes the destination slice (allowing source/destination overlap) and
preserves any predicate on a different block. -/
theorem memmoveB_frame (dst src watched doff soff n : Nat) (da sa : Array UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ dst)
    (dstBound : doff + n ≤ da.size) (srcBound : soff + n ≤ sa.size) :
    ⦃ fun h => h.bytes dst = some da ∧ h.bytes src = some sa ∧
        h.ro dst = false ∧ F (h.bytes watched) ⦄
      memmoveB (.ref (.blk dst) doff) (.ref (.blk src) soff) n
    ⦃ fun _ h => h.bytes dst = some (copyRange da sa doff soff n) ∧ F (h.bytes watched) ⦄ := by
  refine ⟨fun h ⟨hd, hs, writable, frame⟩ => ?_⟩
  have run := Ptr.memmove_ok (rd := BRef.blk dst) (rs := BRef.blk src) hd hs writable
    dstBound srcBound
  rw [wp_run, show memmoveB _ _ n h = _ from run]
  change upd h.bytes dst _ dst = _ ∧ F (upd h.bytes dst _ watched)
  simpa [outside] using frame

/-- Frame both a separate block and every destination index outside the `memmoveB` slice. -/
theorem memmoveB_range_frame (dst src watched doff soff n : Nat) (da sa : Array UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ dst)
    (dstBound : doff + n ≤ da.size) (srcBound : soff + n ≤ sa.size) :
    ⦃ fun h => h.bytes dst = some da ∧ h.bytes src = some sa ∧
        h.ro dst = false ∧ F (h.bytes watched) ⦄
      memmoveB (.ref (.blk dst) doff) (.ref (.blk src) soff) n
    ⦃ fun _ h => h.bytes dst = some (copyRange da sa doff soff n) ∧ F (h.bytes watched) ∧
        ∀ i, i < doff ∨ doff + n ≤ i → (h.bytes dst).bind (·[i]?) = da[i]? ⦄ := by
  have spec := memmoveB_frame dst src watched doff soff n da sa F outside dstBound srcBound
  refine ⟨spec.entails_wp_of_post ?_⟩
  intro _ h ⟨write, kept⟩
  refine ⟨write, kept, fun i hi => ?_⟩
  simp [write, copyRange.getElem? da sa doff soff n i dstBound, show ¬ (doff ≤ i ∧ i < doff + n) by omega]

/-- A byte-block `memset` fills the destination slice with `val` and preserves any predicate on a
different block. -/
theorem memsetB_frame (dst watched off n : Nat) (da : Array UInt8) (val : UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ dst)
    (dstBound : off + n ≤ da.size) :
    ⦃ fun h => h.bytes dst = some da ∧ h.ro dst = false ∧ F (h.bytes watched) ⦄
      memsetB (.ref (.blk dst) off) val n
    ⦃ fun _ h => h.bytes dst = some (fillRange da off n val) ∧ F (h.bytes watched) ⦄ := by
  refine ⟨fun h ⟨hd, writable, frame⟩ => ?_⟩
  have run := Ptr.fill_ok (r := BRef.blk dst) hd writable dstBound (v := val)
  rw [wp_run, show memsetB _ _ n h = _ from run]
  change upd h.bytes dst _ dst = _ ∧ F (upd h.bytes dst _ watched)
  simpa [outside] using frame

/-- Frame both a separate block and every destination index across `memsetB` (exact pointwise view). -/
theorem memsetB_range_frame (dst watched off n : Nat) (da : Array UInt8) (val : UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ dst)
    (dstBound : off + n ≤ da.size) :
    ⦃ fun h => h.bytes dst = some da ∧ h.ro dst = false ∧ F (h.bytes watched) ⦄
      memsetB (.ref (.blk dst) off) val n
    ⦃ fun _ h => h.bytes dst = some (fillRange da off n val) ∧ F (h.bytes watched) ∧
        ∀ i, (h.bytes dst).bind (·[i]?) = if off ≤ i ∧ i < off + n then some val else da[i]? ⦄ := by
  have spec := memsetB_frame dst watched off n da val F outside dstBound
  refine ⟨spec.entails_wp_of_post ?_⟩
  intro _ h ⟨write, kept⟩
  refine ⟨write, kept, fun i => ?_⟩
  simp [write, fillRange.getElem? da off n val i dstBound]

/-- General `freeB` Hoare rule over the updated heap. -/
theorem freeB_spec (target : Nat) (a : Array UInt8) (P : Heap → Prop) :
    ⦃ fun h => h.bytes target = some a ∧ h.ro target = false ∧
        P { h with bytes := upd h.bytes target none } ⦄
      freeB (.ref (.blk target) 0)
    ⦃ fun _ h => P h ⦄ := by
  refine ⟨fun h ⟨hb, hro, hp⟩ => ?_⟩
  rw [wp_run, freeB_ok hb hro]
  exact hp

/-- Freeing a writable byte block clears `target` and preserves any predicate on a different block. -/
theorem freeB_frame (target watched : Nat) (a : Array UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ target) :
    ⦃ fun h => h.bytes target = some a ∧ h.ro target = false ∧ F (h.bytes watched) ⦄
      freeB (.ref (.blk target) 0)
    ⦃ fun _ h => h.bytes target = none ∧ F (h.bytes watched) ⦄ := by
  refine ⟨fun h ⟨hb, hro, frame⟩ => ?_⟩
  rw [wp_run, freeB_ok hb hro]
  exact ⟨by simp, by simpa [upd_ne _ _ _ _ outside] using frame⟩

/-- Freeing a writable byte block preserves `F (h.bytes watched)` and all non-`bytes` heap tables. -/
theorem freeB_tables_frame (target watched : Nat) (a : Array UInt8)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ target) (h₀ : Heap) :
    ⦃ fun h => h = h₀ ∧ h.bytes target = some a ∧ h.ro target = false ∧ F (h.bytes watched) ⦄
      freeB (.ref (.blk target) 0)
    ⦃ fun _ h => h.bytes target = none ∧ F (h.bytes watched) ∧
        h.words = h₀.words ∧ h.streams = h₀.streams ∧ h.gzheaders = h₀.gzheaders ∧
        h.dstates = h₀.dstates ∧ h.istates = h₀.istates ∧ h.gzstates = h₀.gzstates ∧
        h.ro = h₀.ro ∧ h.static = h₀.static ∧ h.allocOk = h₀.allocOk ∧
        h.garbage = h₀.garbage ∧ h.nextBlk = h₀.nextBlk ∧ h.nalloc = h₀.nalloc ⦄ := by
  refine ⟨fun h ⟨rfl, hb, hro, frame⟩ => ?_⟩
  rw [wp_run, freeB_ok hb hro]
  refine ⟨by simp, by simpa [upd_ne _ _ _ _ outside] using frame,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end C
