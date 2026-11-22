import ZlibF.Proof.«inflate.c.output-frame-live-compose»
import ZlibF.Proof.«inflate.c.default-view-loop»
import ZlibF.Proof.«inflate.c.call-dispatch-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Persistent exact frame and allocation metadata for the actual loop. The
frame names the cumulative output prefix and the header record's regions at
loop entry; the attached record is the entry one. -/
def DefaultViewFrameLoopInv (c : Ctx) (r : ZStreamRef) (zs : Nat) (initialHeap : Heap) (head : GzHeaderPtr)
    (initial : IL) (input : List UInt8) (regs : IL) (heap : Heap) : Prop :=
  ∃ stream state used made, used ≤ input.length ∧ DefaultStateJ heap r zs stream state ∧
    (∃ rest, rest.length = input.length - used ∧ DispatchBuffers heap r regs rest) ∧
    HeaderLocal c heap r state regs ∧ regs.bits.toNat ≤ 39 ∧
    ByteViewSizes initialHeap heap ∧ regs.next = inputAdvance initial.next used ∧
    regs.have_.toNat + used = initial.have_.toNat ∧ regs.put = inputAdvance initial.put made ∧
    regs.left.toNat + made = initial.left.toNat ∧
    FastMemoryMetaFrame r initialHeap heap ∧ state.head = head ∧
    RegionsWithin (HeaderRegions heap head) (HeaderRegions initialHeap head) ∧
    BufferFrame initialHeap heap (CallChanged c r zs head)
      (⟨initial.put, initial.left.toNat⟩ :: HeaderRegions initialHeap head)

/-- One dispatch extends the cumulative call frame. -/
theorem call_frame_step {c : Ctx} {h0 heap next : Heap} {r : ZStreamRef} {zs : Nat}
    {stream nextStream : ZStream} {state nextState : InflateState} {head : GzHeaderPtr}
    {l0 regs : IL} {made : Nat}
    (views : RegionViews (CallChanged c r zs head) (⟨l0.put, 0⟩ :: HeaderRegions h0 head))
    (live : heap.live = h0.live) (liveNext : next.live = heap.live)
    (currentGood : Good heap r zs stream state) (nextGood : Good next r zs nextStream nextState)
    (headEq : state.head = head) (nextHead : nextState.head = state.head)
    (within : RegionsWithin (HeaderRegions heap head) (HeaderRegions h0 head))
    (put : regs.put = inputAdvance l0.put made)
    (left : regs.left.toNat + made = l0.left.toNat)
    (frame : BufferFrame h0 heap (CallChanged c r zs head) (⟨l0.put, l0.left.toNat⟩ :: HeaderRegions h0 head))
    (step : DispatchCallFrame c r zs state regs heap next) :
    RegionsWithin (HeaderRegions next head) (HeaderRegions h0 head) ∧
      BufferFrame h0 next (CallChanged c r zs head) (⟨l0.put, l0.left.toNat⟩ :: HeaderRegions h0 head) := by
  have liveForward : ∀ x, h0.live x → heap.live x := by
    intro x alive
    rw [live]
    exact alive
  rcases step with output | ⟨_, _, foot, kept⟩
  · have regionsEq := output_frame_header_regions output currentGood nextGood liveNext head
    refine ⟨by rw [regionsEq]; exact within, ?_⟩
    have right := BufferFrame.mono_changed output (wider := CallChanged c r zs head)
      fun _ view => CallChanged.of_view view
    rw [put] at right
    have withinStep := output_step_within l0.put made regs.left.toNat (HeaderRegions h0 head)
    have totalEq : made + regs.left.toNat = l0.left.toNat := by omega
    rw [totalEq] at withinStep
    exact BufferFrame.trans_within frame right withinStep
      views.head_length liveForward
  · rw [headEq] at foot kept
    obtain ⟨nextHeadEq, nextWithin⟩ := kept nextState nextGood.live.hs
    rw [nextHead, headEq] at nextWithin
    refine ⟨nextWithin.trans within, ?_⟩
    exact BufferFrame.trans_within frame foot (within.trans (RegionsWithin.tail _ _))
      views.head_length liveForward

/-- The actual complete default mode loop changes only its output buffer
range, the private stream/state records, the local `hbuf`, the attached header
record and that record's caller buffers. Its proof retains the same initialized
state, caller packet and strict rank. -/
theorem inflate_default_view_frame_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (local_ : HeaderLocal c h r s l) (incoming : l.bits.toNat ≤ 39)
    (views : RegionViews (CallChanged c r zs s.head) (⟨l.put, 0⟩ :: HeaderRegions h s.head)) :
    ∃ exit regs after stream state used made, used ≤ bs.length ∧
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error exit, regs), after) ∧
      DefaultStateJ after r zs stream state ∧
      (∃ rest, rest.length = bs.length - used ∧ DispatchBuffers after r regs rest) ∧
      HeaderLocal c after r state regs ∧ regs.bits.toNat ≤ 39 ∧ ByteViewSizes h after ∧
      regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧
      FastMemoryMetaFrame r h after ∧ state.head = s.head ∧
      BufferFrame h after (CallChanged c r zs s.head) (⟨l.put, l.left.toNat⟩ :: HeaderRegions h s.head) := by
  let P := DefaultViewFrameLoopInv c r zs h s.head l bs
  let Q := fun (outcome : Except Ex Unit) (regs : IL) (after : Heap) => outcome ≠ .ok () ∧ P regs after
  have initial : P l h := ⟨z, s, 0, 0, by omega, invariant,
    ⟨bs, by simp, buffers⟩, local_, incoming, ByteViewSizes.refl h,
    (inputAdvance_zero l.next).symm, by rfl, (inputAdvance_zero l.put).symm, by rfl, FastMemoryMetaFrame.refl r h,
    rfl, RegionsWithin.refl _,
    BufferFrame.mono_changed (bufferFrame_live_refl E.hz E.hs _) fun _ view => CallChanged.of_view view⟩
  have step : ∀ regs heap, P regs heap → ∃ test regs1 heap1,
      runX (pure true : X Bool) regs heap = .ok ((test, regs1), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs1 heap1
       | .ok false => Q (.ok ()) regs1 heap1
       | .ok true => ∃ result regs2 heap2,
           runX (do inflate_dispatch c; pure false) regs1 heap1 = .ok ((result, regs2), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) regs2 heap2
            | .ok true => Q (.ok ()) regs2 heap2
            | .ok false => P regs2 heap2 ∧ defaultViewHeapRank zs regs2 heap2 < defaultViewHeapRank zs regs heap)) := by
    intro regs heap current
    obtain ⟨stream, state, used, made, bound, currentJ, ⟨rest, restLength, packet⟩, currentLocal, bits,
      sizes, next, count, put, left, metadata, headEq, within, frame⟩ := current
    have currentEnv : Env c heap r zs stream state := ⟨E.strm, E.st, currentJ.good.live.hz, currentJ.good.live.hs⟩
    obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, used2, made2, bound2,
      run, finalJ, ⟨rest2, rest2Length, finalPacket⟩, finalSizes, next2, count2, put2, left2, finalBits,
      finalLocal, progress⟩ :=
      inflate_dispatch_default_view_state_rank currentEnv currentJ packet currentLocal bits
    have callFrame := inflate_dispatch_call_frame currentEnv currentJ packet currentLocal bits run
    have metadata2 := fastMemoryMetaFrameX_inflate_dispatch r c E.strm regs heap outcome finalRegs finalHeap run
    have totalMetadata := metadata.trans metadata2
    have liveEq : heap.live = h.live := congrArg (fun x => x.2.2.2.2.2.2) metadata
    have liveNext : finalHeap.live = heap.live := congrArg (fun x => x.2.2.2.2.2.2) metadata2
    have nextHead := dispatch_head_kept E.strm run currentJ.good.live.hs finalJ.good.live.hs
    obtain ⟨nextWithin, totalFrame⟩ := call_frame_step views liveEq liveNext currentJ.good finalJ.good
      headEq nextHead within put left frame callFrame
    have totalBound : used + used2 ≤ bs.length := by omega
    have final : P finalRegs finalHeap := by
      refine ⟨finalStream, finalState, used + used2, made + made2, totalBound, finalJ,
        ⟨rest2, by omega, finalPacket⟩, finalLocal, finalBits, sizes.trans finalSizes, ?_, ?_, ?_, ?_,
        totalMetadata, nextHead.trans headEq, nextWithin, totalFrame⟩
      · rw [next2, next, inputAdvance_add]
      · omega
      · rw [put2, put, inputAdvance_add]
      · omega
    refine ⟨.ok true, regs, heap, rfl, ?_⟩
    cases outcome with
    | error fault =>
      refine ⟨.error fault, finalRegs, finalHeap, ?_, ?_⟩
      · rw [runX_bind, run]
      · exact ⟨(by intro impossible; cases impossible), final⟩
    | ok unitVal =>
      cases unitVal
      refine ⟨.ok false, finalRegs, finalHeap, ?_, final, ?_⟩
      · rw [runX_bind, run]
        rfl
      · rw [defaultViewHeapRank_eq finalJ.good, defaultViewHeapRank_eq currentJ.good]
        exact progress rfl
  have budget : defaultViewHeapRank zs l h + 2 < fuel := by
    rw [defaultViewHeapRank_eq invariant.good]
    exact dispatchRank_fuel l s.mode incoming
  obtain ⟨outcome, regs, after, run, stopped, final⟩ :=
    xwhileBrk_rank P (defaultViewHeapRank zs) Q step initial budget
  cases outcome with
  | ok unitVal => exact False.elim (stopped (by cases unitVal; rfl))
  | error exit =>
    obtain ⟨stream, state, used, made, bound, finalJ, packet, finalLocal, bits,
      sizes, next, count, put, left, metadata, headEq, _, frame⟩ := final
    exact ⟨exit, regs, after, stream, state, used, made, bound, run, finalJ, packet,
      finalLocal, bits, sizes, next, count, put, left, metadata, headEq, frame⟩

#print axioms inflate_default_view_frame_loop
end Zlib.Inflate.Proofs
