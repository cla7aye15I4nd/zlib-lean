import ZlibF.Proof.«public-roundtrip-inflate»
import ZlibF.Proof.«deflate.c.engine.finish-progress-foreign»

/-! # Every finishing schedule of the default encoder ends

`Goal.deflate_finish_ends`: after any default history, every continuation by `Z_FINISH` calls with
positive room that offers the rest of a fixed input makes boundedly many unfinished calls, and
once it ends it has accepted the whole input and its output decodes to its input.

The bound is a natural measure of the private state and the unread rest of the input `rest`:

* in `INIT_STATE`: `(2^32 + rest) * 131078`;
* otherwise: `(lookahead + rest) * 131078`, plus `65541 + pending` in `BUSY_STATE` and
  `pending + trailer` after it (the rank of `DefaultFinishBoundary.finish_progress`).

A call from `INIT_STATE` leaves it (`public_default_first_finish_phase`); the lookahead is a 32-bit
count and the pending bytes fit the pending buffer, so the measure falls. Every later `Z_FINISH`
call that returns `Z_OK` lowers the rank (`finish_progress`, `foreign_finish_progress`). Caller
edits change neither the state nor the unread rest. The stream ends with `Z_STREAM_END`, which
accepts all offered input.
-/

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The measure of a finishing continuation: the private state and the unread rest. -/
def finishMeasure (d : DeflateState) (rest : Nat) : Nat :=
  if d.status = INIT_STATE then (4294967296 + rest) * 131078
  else (d.lookahead.toNat + rest) * 131078 +
    (if d.status = BUSY_STATE then 65541 + d.pending.toNat
     else d.pending.toNat + (if d.wrap = 1 then 4 else 0))

/-- The first `Z_FINISH` call from `INIT_STATE` leaves it, with at most a pending buffer of
queued bytes. -/
theorem first_finish_leaves_init {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d result : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (status : d.status = INIT_STATE) (nonnull : z.next_out ≠ .null) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate (some r) Z_FINISH h = .ok (rc, after))
    (goodA : DGood after r ds z' result) :
    result.status ≠ INIT_STATE ∧ result.pending.toNat ≤ 65536 := by
  rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
  · have level : d.level = 6 :=
      (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
    rcases caller_output_storage_cases boundary.good buffers with null | ⟨ob, oo, pointer⟩ | ⟨owner, oo, pointer⟩
    · exact absurd null nonnull
    · obtain ⟨_u, _p, rcP, afterP, zP, resultP, runP, goodP, _b, _a, _al, _bits, phaseP, _last, _ended⟩ :=
        public_default_first_finish_phase start level state buffers pointer output boundary.configuration.memory valid
      obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
      subst afterP
      have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans goodA.live.hs)
      subst resultP
      exact ⟨public_finish_phase_started phaseP,
        default_memory_pending_count goodP phaseP boundary.configuration.memory⟩
    · obtain ⟨_u, _p, rcP, afterP, zP, resultP, runP, goodP, _b, _a, _al, _bits, phaseP, _last, _ended⟩ :=
        default_foreign_public_first_finish_phase start level state buffers pointer output
          boundary.configuration.memory valid
      obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
      subst afterP
      have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans goodA.live.hs)
      subst resultP
      exact ⟨public_finish_phase_started phaseP,
        default_memory_pending_count goodP phaseP boundary.configuration.memory⟩
  · obtain ⟨_input, _origin, _base, _xs, _state, busy⟩ := working
    rw [busy] at status
    exact absurd status (by decide)
  · rw [finishing.status] at status
    exact absurd status (by decide)

/-- **One `Z_FINISH` call of a continuation.** From a protocol boundary, with positive room and
the unread rest offered, the call returns `Z_OK` with a smaller measure, or `Z_STREAM_END` having
accepted everything offered. -/
theorem finish_call_measure {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {rc : Int32} {input output : List UInt8} {used : Nat}
    (boundary : DefaultFinishBoundary h r ds z d config) (get : r.get h = some z)
    (nonnull : z.next_out ≠ .null) (room : 0 < z.avail_out.toNat)
    (protocol : ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = [])
    (step : DataStep .deflate h after r Z_FINISH rc input output used) :
    ∃ z' result, DefaultFinishBoundary after r ds z' result config ∧ r.get after = some z' ∧
      used ≤ input.length ∧
      ((rc = Z_OK ∧ finishMeasure result (input.length - used) < finishMeasure d input.length) ∨
       (rc = Z_STREAM_END ∧ used = input.length)) := by
  have original := step
  obtain ⟨z0, z1, get0, get1, buffers, _header, snapshot, usedEq, _bytes, run⟩ := original
  have same0 : z0 = z := Option.some.inj (get0.symm.trans get)
  subst same0
  have run' : deflate (some r) Z_FINISH h = .ok (rc, after) := run
  have length := caller_bytes_length snapshot
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
  have accepted : d.status = FINISH_STATE → z0.avail_in = 0 := by
    intro finished
    have empty := protocol ds d boundary.good.live.zst boundary.good.live.hs finished
    rw [empty] at length
    exact UInt32.toNat_inj.mp length.symm
  -- the call through the protocol boundary
  have called : ∃ usedP producedP rcP afterP zP resultP,
      deflate (some r) Z_FINISH h = .ok (rcP, afterP) ∧ DefaultFinishBoundary afterP r ds zP resultP config ∧
      StreamAccounting z0 zP usedP producedP ∧ (rcP = Z_OK ∨ rcP = Z_STREAM_END) := by
    rcases caller_output_storage_cases boundary.good buffers with null | ⟨ob, oo, pointer⟩ | ⟨owner, oo, pointer⟩
    · exact absurd null nonnull
    · obtain ⟨u, p, rcP, a, zP, resP, runP, stateP, _b, accP, allowedP, _e⟩ :=
        boundary.finish buffers pointer room valid accepted
      exact ⟨u, p, rcP, a, zP, resP, runP, stateP, accP, allowedP⟩
    · obtain ⟨u, p, rcP, a, zP, resP, runP, stateP, _b, accP, allowedP, _e⟩ :=
        boundary.foreign_finish buffers pointer room valid accepted
      exact ⟨u, p, rcP, a, zP, resP, runP, stateP, accP, allowedP⟩
  obtain ⟨usedP, producedP, rcP, afterP, zP, result, runP, stateA, accountP, allowed⟩ := called
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run'))
  subst rcP afterP
  have streams : zP = z1 := Option.some.inj (stateA.good.live.hz.symm.trans get1)
  subst z1
  have usedSame : usedP = used := by
    have count := accountP.2.2.1
    omega
  clear usedEq
  subst used
  have usedLe : usedP ≤ input.length := by have count := accountP.2.2.1; omega
  have restA : zP.avail_in.toNat = input.length - usedP := by have count := accountP.2.2.1; omega
  refine ⟨zP, result, stateA, stateA.good.live.hz, usedLe, ?_⟩
  rcases allowed with ok | ended
  · subst ok
    left
    refine ⟨rfl, ?_⟩
    have pendingA : result.pending.toNat ≤ 65536 := by
      rcases stateA.phase with ⟨_i, _o, _b, startA, _s⟩ | phaseA
      · -- no call returns to `INIT_STATE`
        by_cases initial : d.status = INIT_STATE
        · exact absurd startA.status (first_finish_leaves_init boundary buffers initial nonnull room valid run'
            stateA.good).1
        · rcases caller_output_storage_cases boundary.good buffers with null | ⟨ob, oo, pointer⟩ |
              ⟨owner, oo, pointer⟩
          · exact absurd null nonnull
          · obtain ⟨_u, _p, rcF, afterF, zF, resF, runF, stateF, _b, _a, _al, _less, _empty, startedF⟩ :=
              boundary.finish_progress buffers pointer room valid accepted initial
            obtain ⟨_, heapsF⟩ := Prod.mk.inj (Except.ok.inj (runF.symm.trans run'))
            subst afterF
            have statesF : resF = result := Option.some.inj (stateF.good.live.hs.symm.trans stateA.good.live.hs)
            subst resF
            exact absurd startA.status startedF
          · obtain ⟨_u, _p, rcF, afterF, zF, resF, runF, stateF, _b, _a, _al, _less, _empty, startedF⟩ :=
              boundary.foreign_finish_progress buffers pointer room valid accepted initial
            obtain ⟨_, heapsF⟩ := Prod.mk.inj (Except.ok.inj (runF.symm.trans run'))
            subst afterF
            have statesF : resF = result := Option.some.inj (stateF.good.live.hs.symm.trans stateA.good.live.hs)
            subst resF
            exact absurd startA.status startedF
      · exact default_memory_pending_count stateA.good phaseA boundary.configuration.memory
    by_cases initial : d.status = INIT_STATE
    · obtain ⟨startedA, _⟩ := first_finish_leaves_init boundary buffers initial nonnull room valid run' stateA.good
      have look := result.lookahead.toNat_lt
      have restLe : input.length - usedP ≤ input.length := Nat.sub_le _ _
      unfold finishMeasure
      rw [ite_eq_left initial, ite_eq_right startedA]
      have sumLe : result.lookahead.toNat + (input.length - usedP) ≤ 4294967295 + input.length := by omega
      have scaled := Nat.mul_le_mul_right 131078 sumLe
      have wrapLe : (if result.wrap = 1 then 4 else 0) ≤ 4 := by split <;> omega
      split
      · rw [Nat.add_mul] at scaled ⊢
        rw [Nat.add_mul] at scaled
        omega
      · rw [Nat.add_mul] at scaled ⊢
        rw [Nat.add_mul] at scaled
        omega
    · have rank : ((result.lookahead.toNat + zP.avail_in.toNat) * 131078 +
          (if result.status = BUSY_STATE then 65541 + result.pending.toNat
           else result.pending.toNat + (if result.wrap = 1 then 4 else 0))) <
          ((d.lookahead.toNat + z0.avail_in.toNat) * 131078 +
          (if d.status = BUSY_STATE then 65541 + d.pending.toNat
           else d.pending.toNat + (if d.wrap = 1 then 4 else 0))) ∧ result.status ≠ INIT_STATE := by
        rcases caller_output_storage_cases boundary.good buffers with null | ⟨ob, oo, pointer⟩ |
            ⟨owner, oo, pointer⟩
        · exact absurd null nonnull
        · obtain ⟨_u, _p, rcF, afterF, zF, resF, runF, stateF, _b, _a, _al, less, _empty, startedF⟩ :=
            boundary.finish_progress buffers pointer room valid accepted initial
          obtain ⟨codesF, heapsF⟩ := Prod.mk.inj (Except.ok.inj (runF.symm.trans run'))
          subst rcF afterF
          have streamsF : zF = zP := Option.some.inj (stateF.good.live.hz.symm.trans stateA.good.live.hz)
          have statesF : resF = result := Option.some.inj (stateF.good.live.hs.symm.trans stateA.good.live.hs)
          subst zF resF
          exact ⟨less rfl, startedF⟩
        · obtain ⟨_u, _p, rcF, afterF, zF, resF, runF, stateF, _b, _a, _al, less, _empty, startedF⟩ :=
            boundary.foreign_finish_progress buffers pointer room valid accepted initial
          obtain ⟨codesF, heapsF⟩ := Prod.mk.inj (Except.ok.inj (runF.symm.trans run'))
          subst rcF afterF
          have streamsF : zF = zP := Option.some.inj (stateF.good.live.hz.symm.trans stateA.good.live.hz)
          have statesF : resF = result := Option.some.inj (stateF.good.live.hs.symm.trans stateA.good.live.hs)
          subst zF resF
          exact ⟨less rfl, startedF⟩
      obtain ⟨less, startedA⟩ := rank
      unfold finishMeasure
      rw [ite_eq_right initial, ite_eq_right startedA, ← restA, length]
      exact less
  · subst ended
    right
    refine ⟨rfl, ?_⟩
    obtain ⟨_finish, _status, drained, _pending, _bits⟩ :=
      boundary.generic_stream_end_run_control buffers run' stateA.good
    rw [drained] at restA
    simp only [UInt32.toNat_zero] at restA
    omega

/-- **The measure along a finishing continuation.** Every unfinished call lowers the measure; the
continuation stays a default history; once it ends it has accepted the whole fixed input. -/
theorem chain_progress {r : ZStreamRef} {accepted source : List UInt8} {k : Nat} {start after : Heap}
    {initial final : DataLog}
    (chain : DefaultFinishChain r accepted source k start initial after final) :
    ∀ N, DefaultDeflateHistory r start initial → initial.finished = false → initial.input = accepted →
      (∀ ds z d config, DefaultFinishBoundary start r ds z d config → finishMeasure d source.length ≤ N) →
      DefaultDeflateHistory r after final ∧ ∃ j, j ≤ source.length ∧ final.input = accepted ++ source.take j ∧
        (final.finished = false → ∃ ds z d config, DefaultFinishBoundary after r ds z d config ∧
          k + finishMeasure d (source.length - j) ≤ N) ∧
        (final.finished = true → j = source.length ∧ final.result = Z_STREAM_END) := by
  induction chain with
  | refl h log =>
    intro N history unfinished inputEq bound
    refine ⟨history, 0, Nat.zero_le _, by rw [inputEq]; simp, fun _ => ?_, fun done => ?_⟩
    · obtain ⟨ds, z, d, config, state, _⟩ := (history_generic history).exact_encoding
      have le := bound ds z d config state.protocol
      exact ⟨ds, z, d, config, state.protocol, by simpa using le⟩
    · rw [unfinished] at done
      cases done
  | caller _ edit ih =>
    intro N history unfinished inputEq bound
    obtain ⟨historyA, j, jle, inEq, going, ended⟩ := ih N history unfinished inputEq bound
    refine ⟨historyA.caller edit, j, jle, inEq, fun unf => ?_, ended⟩
    obtain ⟨ds, z, d, config, boundary, le⟩ := going unf
    obtain ⟨zg, _getG, boundaryG⟩ := boundary.rebuffer edit
    exact ⟨ds, zg, d, config, boundaryG, le⟩
  | @step k start initial h log after z rc input output used _ unfinishedLog get nonnull room protocol
      inputEq observed ih =>
    intro N history unfinished initialEq bound
    obtain ⟨historyH, j, jle, inEq, going, _ended⟩ := ih N history unfinished initialEq bound
    obtain ⟨ds, zb, d, config, boundary, le⟩ := going unfinishedLog
    have sameZ : zb = z := Option.some.inj (boundary.good.live.hz.symm.trans get)
    subst zb
    have offset : log.input.length - accepted.length = j := by
      rw [inEq]; simp only [List.length_append, List.length_take]; omega
    rw [offset] at inputEq
    subst inputEq
    obtain ⟨z', result, boundaryA, _getA, usedLe, outcome⟩ :=
      finish_call_measure boundary get nonnull room protocol observed
    have restLen : (source.drop j).length = source.length - j := List.length_drop
    have historyA : DefaultDeflateHistory r after
        (deflateLogStep log Z_FINISH rc (source.drop j) output used) := .step historyH observed
    have inputA : (deflateLogStep log Z_FINISH rc (source.drop j) output used).input =
        accepted ++ source.take (j + used) := by
      change log.input ++ (source.drop j).take used = _
      rw [inEq, List.append_assoc, ← List.take_add]
    refine ⟨historyA, j + used, by omega, inputA, ?_, ?_⟩
    · intro unf
      rcases outcome with ⟨ok, less⟩ | ⟨ended, _⟩
      · refine ⟨ds, z', result, config, boundaryA, ?_⟩
        rw [restLen] at less
        have restEq : source.length - (j + used) = source.length - j - used := by omega
        rw [restEq]
        omega
      · subst ended
        change (log.finished || (Z_STREAM_END == Z_STREAM_END)) = false at unf
        simp at unf
    · intro fin
      rcases outcome with ⟨ok, _⟩ | ⟨ended, all⟩
      · subst ok
        change (log.finished || (Z_OK == Z_STREAM_END)) = true at fin
        rw [unfinishedLog] at fin
        cases fin
      · subst ended
        rw [restLen] at all
        exact ⟨by omega, rfl⟩

/-- **`Goal.deflate_finish_ends`.** -/
theorem deflate_finish_ends : Goal.deflate_finish_ends := by
  intro r h log z input history unfinished _get _buffers _snapshot _protocol
  obtain ⟨ds0, z0, d0, config0, state, _⟩ := (history_generic history).exact_encoding
  refine ⟨finishMeasure d0 input.length, ?_⟩
  intro k after final chain
  obtain ⟨historyA, j, _jle, inEq, going, ended⟩ :=
    chain_progress chain (finishMeasure d0 input.length) history unfinished rfl (by
      intro ds z d config boundary
      have sameZ : z = z0 := Option.some.inj (boundary.good.live.hz.symm.trans state.protocol.good.live.hz)
      subst sameZ
      have kinds := boundary.good.live.zst.symm.trans state.protocol.good.live.zst
      simp only [Option.some.injEq, StateRef.deflate.injEq] at kinds
      subst kinds
      have sameD : d = d0 := Option.some.inj (boundary.good.live.hs.symm.trans state.protocol.good.live.hs)
      rw [sameD]; exact Nat.le_refl _)
  refine ⟨fun unf => ?_, fun fin => ?_⟩
  · obtain ⟨_, _, _, _, _, le⟩ := going unf
    omega
  · obtain ⟨jEq, result⟩ := ended fin
    refine ⟨by rw [inEq, jEq, List.take_length], ?_⟩
    exact ended_decodes historyA result

/-- **`Goal.stream_roundtrip_total`**: the unconditional stream round trip. -/
theorem stream_roundtrip_total : Goal.stream_roundtrip_total :=
  ⟨deflate_finish_ends, inflate_chain_ends⟩

end ZlibF.Spec.Public.Proofs.RoundTrip

#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.deflate_finish_ends
#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.stream_roundtrip_total
