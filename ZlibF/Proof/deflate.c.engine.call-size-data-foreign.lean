import ZlibF.Proof.«deflate.c.engine.call-size-data»
import ZlibF.Proof.«deflate.c.engine.call-size-tail-foreign»
import ZlibF.Proof.«deflate.c.engine.strategy-size-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-buffered-ready»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-wide-controls»

/-! # The size of the data part of a BUSY call into a foreign output pointer

The twins of `deflate.c.engine.call-size-data.lean` for a caller output pointer into another deflate state's `depth`
array.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of the data part of a `BUSY_STATE` call.** -/
theorem foreign_busy_data_tail_size {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (bits : config.windowBits = 15) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (companion : SizeCompanion d xs)
    (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (run : publicDataTail (some r) (some (.tab ds)) flush h = .ok (rc, after)) :
    ∃ used produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      StreamAccounting z z' used produced ∧
      (flush = Z_FINISH → rc = Z_OK → z'.avail_out = 0) ∧
      BusySizeOutcome after r ds z' result flush rc (origin + fillEnd d + used) base (heldBytes d) produced := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  have strategyB := boundary.strategy publish
  -- the strategy call and its return, for either flush
  have afterStrategy : ∀ ret middle, deflate_slow (some (.tab ds)) flush h = .ok (ret, middle) →
      publicStrategyReturn (some r) (some (.tab ds)) flush ret middle = .ok (rc, after) →
      ∃ used produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
        StreamAccounting z z' used produced ∧
        (flush = Z_FINISH → rc = Z_OK → z'.avail_out = 0) ∧
        BusySizeOutcome after r ds z' result flush rc (origin + fillEnd d + used) base (heldBytes d) produced := by
    intro ret middle strategyRun returnRun
    obtain ⟨used, produced, zm, dm, getM, stateM, accountM, outcome⟩ :=
      foreign_slow_strategy_run_size strategyB boundary.end_frontier buffers positive pointer memory wrap bits publish
        inputValid companion clean strategyRun
    have controls : dm.status = d.status := by
      rcases clean with noFlush | finish
      · subst noFlush
        obtain ⟨_used, _produced, other, _z', otherD, _base', _ys, _extended, _nextOrigin, otherRun, otherState,
            otherControls, _rest⟩ :=
          default_foreign_deflate_slow_no_flush_buffered_ready boundary buffers positive pointer memory wrap publish inputValid
        obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (otherRun.symm.trans strategyRun))
        subst heaps
        have same : otherD = dm := Option.some.inj (otherState.good.live.hs.symm.trans stateM)
        subst same
        exact otherControls.status
      · subst finish
        exact (default_foreign_deflate_slow_finish_ready_run_controls strategyB boundary.end_frontier buffers positive pointer memory
          wrap publish inputValid strategyRun stateM).status
    rcases outcome with ⟨more, roomOut, input1, origin1, base1, ys1, state1, companion1, endpoint1, size1⟩ |
        ⟨finishFlag, good2, buffers2, shape, bits2, ready2, wrap2, _covered, size2, drained2⟩
    · subst more
      obtain ⟨result, stateA, getA, boundaryA, heldA, statusA, fillA, companionA⟩ :=
        need_more_return_size state1 returnRun
      refine ⟨used, produced, zm, result, getA, stateA, accountM, fun finish _ => roomOut finish, Or.inl ⟨?_, input1, origin1, base1, ys1,
        boundaryA.toContentBoundary, ?_, companionA companion1, ?_⟩⟩
      · rw [statusA, controls, status]
      · rw [fillA]; exact endpoint1
      · rw [heldA]; exact size1
    · subst finishFlag
      rcases shape with ⟨started, empty⟩ | ⟨done, remaining⟩
      · subst started
        rw [public_strategy_finish_started getM stateM empty] at returnRun
        obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj returnRun)
        subst heaps
        have goodA := last_flush_good (finish_status_good good2) (-1)
        have owed : owedTrailer { dm with status := FINISH_STATE, last_flush := -1 } = 4 := by
          unfold owedTrailer
          simp [wrap2]
        refine ⟨used, produced, zm, _, goodA.live.hz, goodA.live.hs, accountM, fun _ _ => empty, Or.inr ⟨rfl, ?_, ?_, rfl, drained2⟩⟩
        · rw [owed]
          change produced + heldBytes dm + 4 + base + 5 * (base / 16383) ≤ _
          omega
        · intro _ none
          rw [owed] at none
          cases none
      · subst done
        rw [public_strategy_finish_done getM stateM] at returnRun
        obtain ⟨d0, pb, buf, trees0⟩ := good2.trees
        have same : d0 = dm := Option.some.inj (trees0.base.dstate.symm.trans stateM)
        subst same
        have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + produced) := by
          rw [accountM.2.2.2.2.2.1, pointer]
          rfl
        have ready := ready2 remaining
        obtain ⟨tailProduced, z3, d3, get3, state3, _good3, account3, size3, wrap3, status3, rc3, room3⟩ :=
          foreign_trailer_run_size (finish_status_good good2) (finish_status_trees trees0)
            (finish_status_buffers good2 buffers2) pointerM wrap2 ready.1 ready.2.1 bits2 returnRun
        refine ⟨used + 0, produced + tailProduced, z3, d3, get3, state3, stream_accounting_trans accountM account3, fun _ ok => room3 ok,
          Or.inr ⟨status3, ?_, ?_, rfl, ?_⟩⟩
        · have owed : owedTrailer d3 = 0 := by
            unfold owedTrailer
            rw [wrap3]
            rfl
          rw [owed]
          simp only [Nat.add_zero]
          omega
        · intro none _
          have pendingZero : d3.pending.toNat = 0 := by unfold heldBytes at none; omega
          have zero : d3.pending = 0 := UInt64.toNat_inj.mp pendingZero
          rw [rc3, zero]
          rfl
        · have count := account3.2.2.1
          have drainedN : zm.avail_in.toNat = 0 := by rw [drained2]; rfl
          apply UInt32.toNat_inj.mp
          change z3.avail_in.toNat = 0
          omega
  rcases clean with noFlush | finish
  · subst noFlush
    by_cases active : z.avail_in ≠ 0 ∨ d.lookahead ≠ 0
    · rw [public_busy_no_flush_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy
        active] at run
      obtain ⟨ret, middle, strategyRun, returnRun⟩ := size_bind_split run
      exact afterStrategy ret middle strategyRun returnRun
    · have empty : z.avail_in = 0 := by
        by_cases zero : z.avail_in = 0
        · exact zero
        · exact False.elim (active (Or.inl zero))
      have look : d.lookahead = 0 := by
        by_cases zero : d.lookahead = 0
        · exact zero
        · exact False.elim (active (Or.inr zero))
      rw [public_default_empty_data boundary.good status empty look] at run
      obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj run)
      subst heaps
      refine ⟨0, 0, z, d, boundary.good.live.hz, boundary.good.live.hs, stream_accounting_zero z, fun f => absurd f (by decide),
        Or.inl ⟨status, input, origin, base, xs, boundary.toContentBoundary, rfl, companion, by omega⟩⟩
  · subst finish
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy] at run
    obtain ⟨ret, middle, strategyRun, returnRun⟩ := size_bind_split run
    exact afterStrategy ret middle strategyRun returnRun

end Zlib.Deflate.Engine.Proofs
