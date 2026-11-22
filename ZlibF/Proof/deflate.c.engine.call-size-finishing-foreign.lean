import ZlibF.Proof.«deflate.c.engine.call-size-finishing»
import ZlibF.Proof.«deflate.c.engine.call-size-busy-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-resume»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-zlib-trailer»

/-! # The size of a FINISH_STATE call into a foreign output pointer

The twins of `deflate.c.engine.call-size-finishing.lean` for a caller output pointer into another deflate state's `depth`
array.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- After the final block, only the one-time trailer is queued. -/
theorem foreign_public_finishing_tail_size_execution {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (empty : z.avail_in = 0) (pending : d.pending = 0) :
    ∃ produced rc after z' result,
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧ (rc = Z_OK → z'.avail_out = 0) ∧ result.status = FINISH_STATE ∧
      produced + heldBytes result + owedTrailer result = heldBytes d + owedTrailer d := by
  rcases phase.wrapper with wrap | wrap
  · obtain ⟨other, pb, buf, trees⟩ := good.trees
    have eq : other = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst other
    obtain ⟨_produced, after, _z', _result, _written, _remaining, run, _rest⟩ :=
      foreign_zlib_trailer_publish_encoding good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    obtain ⟨produced, z', result, _get, _state, goodA, account, size, wrapA, statusA, _rcA, roomA⟩ :=
      foreign_trailer_run_size good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits run
    have header := public_finishing_header_source good phase empty
    refine ⟨produced, _, after, z', result, header.trans run, goodA, account, roomA, statusA.trans phase.status, ?_⟩
    have held : heldBytes d = 0 := by
      unfold heldBytes
      rw [pending, phase.bits]
      rfl
    unfold owedTrailer
    rw [wrapA, wrap, held]
    simp
    omega
  · exact ⟨0, Z_STREAM_END, h, z, d,
      public_finished_headers good phase.status empty phase.lookahead wrap,
      good, stream_accounting_zero z, fun ok => absurd ok (by decide), phase.status, by omega⟩

/-- **The size of a `Z_FINISH` call in `FINISH_STATE`** with no new input. -/
theorem foreign_public_finishing_size_execution {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (empty : z.avail_in = 0)
    (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ (rc = Z_OK → z'.avail_out = 0) ∧ result.status = FINISH_STATE ∧
      produced + heldBytes result + owedTrailer result = heldBytes d + owedTrailer d := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have phase0 : FinishingPhase { d with last_flush := Z_FINISH } config :=
    phase.control rfl (fun w p => phase.cursor w p)
  by_cases queued : d.pending = 0
  · obtain ⟨produced, rc, after, z', result, tailRun, goodA, account, roomA, statusA, size⟩ :=
      foreign_public_finishing_tail_size_execution good0 buffers0 phase0 pointer empty queued
    have entry := public_finish_entry good phase.status empty phase.lookahead queued nonnull positive lower upper
    have source := public_finishing_header_source good0 phase0 empty
    exact ⟨produced, rc, after, z', result, entry.trans (source.symm.trans tailRun), goodA, account, roomA, statusA, size⟩
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM, _frameF⟩ :=
      flush_pending_resume_foreign_bits good0 buffers0 pointer low pending0
    obtain ⟨heldM0, wrapM, statusM⟩ := pending_flush_held pendingCount fields
    have heldM : produced + heldBytes dm = heldBytes d := heldM0
    have moved : 0 < produced := by
      rw [amount]
      apply Nat.lt_min.mpr
      refine ⟨?_, output⟩
      have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
      change 0 < d.pending.toNat
      omega
    have phaseM : FinishingPhase dm config := by
      apply phase0.control (by rw [fields])
      intro _ emptyM
      exact reset moved (by rw [emptyM]; rfl)
    have owedM : owedTrailer dm = owedTrailer d := by unfold owedTrailer; rw [wrapM]
    have emptyM : zm.avail_in = 0 := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      rw [empty] at count
      exact count
    by_cases exhausted : zm.avail_out = 0
    · have run := public_pending_finish_exhausted good goodM nonnull positive (by simp [empty]) queued flushRun exhausted
      refine ⟨produced, Z_OK, _, zm, _, run, last_flush_good goodM (-1), accountM, fun _ => exhausted, ?_, ?_⟩
      · change dm.status = FINISH_STATE
        rw [statusM]; exact phase.status
      · change produced + heldBytes dm + owedTrailer dm = heldBytes d + owedTrailer d
        omega
    · have left : 0 < zm.avail_out.toNat := by
        have nonzero : zm.avail_out.toNat ≠ 0 := fun zero => exhausted (UInt32.toNat_inj.mp zero)
        omega
      have noPending : dm.pending = 0 := by
        apply UInt64.toNat_inj.mp
        change dm.pending.toNat = 0
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        change dm.pending.toNat + produced = d.pending.toNat at pendingCount
        omega
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨laterProduced, rc, after, z', result, tailRun, goodA, accountA, roomA, statusA, sizeA⟩ :=
        foreign_public_finishing_tail_size_execution goodM buffersM phaseM pointerM emptyM noPending
      have entry := public_pending_finish_continue good goodM nonnull positive (by simp [empty]) queued flushRun exhausted (fun _ => emptyM)
      refine ⟨produced + laterProduced, rc, after, z', result, entry.trans tailRun, goodA,
        by simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA, roomA, statusA, ?_⟩
      omega

/-- **The size of a `Z_FINISH` call in `FINISH_STATE`** offered new input: pending bytes move,
then the call refuses. -/
theorem foreign_public_finishing_new_input_size_execution {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (nonempty : z.avail_in ≠ 0) (output : 0 < z.avail_out.toNat)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ (rc = Z_OK → z'.avail_out = 0) ∧ result.status = FINISH_STATE ∧
      produced + heldBytes result + owedTrailer result = heldBytes d + owedTrailer d := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  by_cases queued : d.pending = 0
  · have source := public_finished_new_input_source good phase.status queued nonnull positive (valid nonempty) nonempty lower upper
    obtain ⟨message, refused⟩ := err_return_run good0.live.hz Z_BUF_ERROR
    let z' := { z with msg := message }
    have goodA := stream_control_good (z' := z') good0 rfl good.live.zalloc good.live.zfree
    refine ⟨0, Z_BUF_ERROR, _, z', _, source.trans refused, goodA, stream_accounting_zero z, fun ok => absurd ok (by decide), phase.status, ?_⟩
    change 0 + heldBytes d + owedTrailer d = heldBytes d + owedTrailer d
    omega
  · obtain ⟨before, pending⟩ := good_pending_bits good
    have pending0 := last_flush_pending_bits good pending Z_FINISH
    have low : d.bi_valid.toInt < 8 := by rw [phase.bits]; decide
    obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, goodM, buffersM,
        accountM, _sizesM, _storageM, amount, pendingCount, _lowM, fields, reset, _bytesM, _pendingM, _bitsM, _frameF⟩ :=
      flush_pending_resume_foreign_bits good0 buffers0 pointer low pending0
    obtain ⟨heldM0, wrapM, statusM⟩ := pending_flush_held pendingCount fields
    have heldM : produced + heldBytes dm = heldBytes d := heldM0
    have owedM : owedTrailer dm = owedTrailer d := by unfold owedTrailer; rw [wrapM]
    have statusD : dm.status = FINISH_STATE := statusM.trans phase.status
    have moved : 0 < produced := by
      rw [amount]
      apply Nat.lt_min.mpr
      refine ⟨?_, output⟩
      have nonzero : d.pending.toNat ≠ 0 := fun zero => queued (UInt64.toNat_inj.mp zero)
      change 0 < d.pending.toNat
      omega
    have inputM : zm.avail_in = z.avail_in := by
      apply UInt32.toNat_inj.mp
      have count := accountM.2.2.1
      omega
    by_cases exhausted : zm.avail_out = 0
    · have run := public_pending_finish_exhausted good goodM nonnull positive valid queued flushRun exhausted
      refine ⟨produced, Z_OK, _, zm, _, run, last_flush_good goodM (-1), accountM, fun _ => exhausted, statusD, ?_⟩
      change produced + heldBytes dm + owedTrailer dm = heldBytes d + owedTrailer d
      omega
    · have newInput : zm.avail_in ≠ 0 := by rw [inputM]; exact nonempty
      have source := public_pending_finish_new_input_source good goodM nonnull positive valid queued flushRun exhausted statusD newInput
      obtain ⟨message, refused⟩ := err_return_run goodM.live.hz Z_BUF_ERROR
      let z' := { zm with msg := message }
      have goodA := stream_control_good (z' := z') goodM rfl goodM.live.zalloc goodM.live.zfree
      have account : StreamAccounting zm z' 0 0 := stream_accounting_zero zm
      refine ⟨produced, Z_BUF_ERROR, _, z', dm, source.trans refused, goodA,
        by simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountM account,
        fun ok => absurd ok (by decide), statusD, by omega⟩

end Zlib.Deflate.Engine.Proofs
