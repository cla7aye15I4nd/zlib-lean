import ZlibF.Proof.«deflate.c.engine.call-size-finishing»
import ZlibF.Proof.«deflate.c.engine.public-first-counters»

/-! # The size of the first call

The first `deflate` call with room writes the 2-byte zlib header. With one byte of room it delivers
the first header byte and holds the second; otherwise both header bytes are delivered and the data
part follows from the header's `BUSY_STATE` boundary. Either way the outcome is the ledger outcome
of a `BUSY_STATE` call that held the 2 header bytes at its start.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of the first call.** -/
theorem first_call_size {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {flush rc : Int32}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (bits : config.windowBits = 15)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (companion : SizeCompanion d [])
    (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    ∃ used produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      StreamAccounting z z' used produced ∧
      (flush = Z_FINISH → rc = Z_OK → z'.avail_out = 0) ∧
      BusySizeOutcome after r ds z' result flush rc (origin + fillEnd d + used) base 2 produced := by
  obtain ⟨outputBytes, outGet, outRw, outBound, outside⟩ := caller_raw_output initial.good buffers pointer
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have room : 2 ≤ buf.size := by have size := trees.base.size; have lo := trees.base.lit_lo; omega
  have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have held0 : heldBytes d = 0 := by
    unfold heldBytes
    rw [initial.pending, initial.bits]
    rfl
  by_cases one : z.avail_out.toNat = 1
  · have oneWord : z.avail_out = 1 := UInt32.toNat_inj.mp one
    obtain ⟨other, z', result, finishRun, stateA, _buffersA, accountA, emptyA, pendingA, statusA, _lastA⟩ :=
      first_finish_one_buffered initial level boundary buffers pointer oneWord valid
    have finishSource := first_finish_one_source initial level trees.base.pbuf trees.base.bytes room trees.base.rw
      pointer outGet outRw separate outBound oneWord valid
    have actual : deflate (some r) flush h = .ok (Z_OK, other) := by
      rcases clean with noFlush | finish
      · subst noFlush
        have noFlushRun := first_no_flush_one_source initial level trees.base.pbuf trees.base.bytes room
          trees.base.rw pointer outGet outRw separate outBound oneWord valid
        exact noFlushRun.trans (finishSource.symm.trans finishRun)
      · subst finish
        exact finishRun
    obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
    subst heaps
    have canonical : other = headerOneHeap h r ds pb ob oo z d buf outputBytes :=
      (Prod.mk.inj (Except.ok.inj (finishRun.symm.trans finishSource))).2
    have states : result = headerOneState d pb := by
      have live := stateA.good.live.hs
      rw [canonical] at live
      simp only [headerOneHeap, setD_dstates_same] at live
      exact Option.some.inj live.symm
    have companionA : SizeCompanion result [] := by rw [states]; exact companion
    have fillA : fillEnd result = fillEnd d := by rw [states]; rfl
    have heldA : heldBytes result = 1 := by
      have bitsA : result.bi_valid = d.bi_valid := by rw [states]; rfl
      unfold heldBytes
      rw [pendingA, bitsA, initial.bits]
      rfl
    refine ⟨0, 1, z', result, stateA.good.live.hz, stateA.good.live.hs, accountA, fun _ _ => emptyA,
      Or.inl ⟨statusA, input, origin, base, [], stateA.toContentBoundary, ?_, companionA, ?_⟩⟩
    · rw [fillA]; rfl
    · rw [heldA]
      omega
  · have outputRoom : 2 ≤ z.avail_out.toNat := by omega
    have accountH := header_complete_accounting pointer outputRoom
    have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
    have publish : PublishReady d := ⟨initial.pending, initial.pendingOut, by rw [initial.bits]; decide⟩
    rcases clean with noFlush | finish
    · subst noFlush
      have first := public_default_header_complete initial level trees.base.pbuf trees.base.bytes room trees.base.rw
        pointer outGet outRw separate outBound outputRoom valid
      have contentH := header_complete_content (oo := oo) boundary.toContentBoundary trees.base.pbuf trees.base.bytes
        outGet outside
      have stateH : BufferedBoundary (headerCompleteHeap h r ds pb ob oo z d buf outputBytes) r ds
          (headerCompleteStream z ob oo) (headerCompleteState d) input origin base [] config :=
        ⟨contentH, boundary.configuration, ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩,
          boundary.bits, boundary.strict,
          header_complete_chains boundary.good trees.base.pbuf boundary.end_frontier outside,
          fun _ => initial.pendingOut⟩
      have buffersH := header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom
      have readyH : PublishReady (headerCompleteState d) := ⟨initial.pending, initial.pendingOut, boundary.bits⟩
      obtain ⟨used, produced, z', result, getA, stateA, accountA, roomA, outcome⟩ :=
        busy_data_tail_size (d := headerCompleteState d) stateH buffersH rfl level initial.strategy pointerH memory
          wrapConfig bits readyH valid companion (Or.inl rfl) (first.symm.trans run)
      have heldH : heldBytes (headerCompleteState d) = 0 := held0
      rw [heldH] at outcome
      refine ⟨0 + used, 2 + produced, z', result, getA, stateA, stream_accounting_trans accountH accountA, roomA, ?_⟩
      rw [Nat.zero_add]
      exact outcome.prepend rfl
    · subst finish
      have first := public_default_finish_header_complete initial level trees.base.pbuf trees.base.bytes room
        trees.base.rw pointer outGet outRw separate outBound outputRoom valid
      obtain ⟨stateS, endS, publishS⟩ := header_finish_strategy_boundary (boundary.strategy publish)
        boundary.end_frontier publish trees.base.pbuf trees.base.bytes outGet outside
      have buffersH := last_flush_buffers
        (header_complete_good (oo := oo) initial.good trees.base.bytes outGet separate)
        (header_complete_buffers initial.good buffers trees.base.bytes outGet separate pointer outputRoom) Z_FINISH
      have stateH := stateS.buffered endS (fun _ => publishS.2.1)
      obtain ⟨used, produced, z', result, getA, stateA, accountA, roomA, outcome⟩ :=
        busy_data_tail_size (d := headerFinishState d) stateH buffersH rfl level initial.strategy pointerH memory
          wrapConfig bits publishS valid companion (Or.inr rfl) (first.symm.trans run)
      have heldH : heldBytes (headerFinishState d) = 0 := held0
      rw [heldH] at outcome
      refine ⟨0 + used, 2 + produced, z', result, getA, stateA, stream_accounting_trans accountH accountA, roomA, ?_⟩
      rw [Nat.zero_add]
      exact outcome.prepend rfl

end Zlib.Deflate.Engine.Proofs
