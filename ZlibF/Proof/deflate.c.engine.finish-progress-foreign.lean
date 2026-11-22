import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-call»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-buffered»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-public-busy-finish-phase»
import ZlibF.Proof.«deflate.c.engine.public-finish-progress»
import ZlibF.Proof.«deflate.c.engine.call-size-finishing-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-accepted-protocol»

/-! # FINISH progress for a caller output pointer into another deflate state

The twins of `slow_finish_loop_progress`, `deflate_slow_finish_progress` and
`deflate_slow_finish_buffered_progress` for an output pointer into another deflate state's
`depth` array: a `need_more` return strictly lowers unread input plus lookahead.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxHeartbeats 3000000 in
/-- The full real FINISH loop terminates within fuel, preserving initialized
content and EOF frontiers through any number of full blocks and refills.
Zero initial output is admitted with explicit publication readiness.
It stops at a real output test or true EOF. Final literal settlement and
final block publication occur after this loop. -/
theorem foreign_slow_finish_loop_progress {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced final after z' result base' ys extended nextOrigin,
      cwhile forever (deflate_slow_body (some (.tab ds)) Z_FINISH) {} h = .ok (final, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (final.ret = some need_more ∨ (final.ret = none ∧ final.brk = true)) ∧
      (final.ret = some need_more → z'.avail_out = 0) ∧
      (final.brk = true → result.lookahead = 0 ∧ z'.avail_in = 0) ∧
      (final.ret = none → PublishReady result) ∧
      (final.ret = some need_more →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) := by
  let startEnd := origin + fillEnd d
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys accepted delivered,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ StreamAccounting z currentZ accepted delivered ∧
      currentOrigin + fillEnd currentD = startEnd + accepted ∧
      (∀ i, i < startEnd → currentInput i = input i) ∧ base ≤ currentBase ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none ∨ st.ret = some need_more) ∧ (st.ret = none → PublishReady currentD) ∧
      (st.ret = some need_more → currentZ.avail_out = 0) ∧
      (st.brk = true → currentD.lookahead = 0 ∧ currentZ.avail_in = 0) ∧
      currentD.lookahead.toNat + currentZ.avail_in.toNat ≤ d.lookahead.toNat + z.avail_in.toNat ∧
      (st.ret = some need_more →
        currentD.lookahead.toNat + currentZ.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat)
  let rank : LoopS → Heap → Nat := fun st heap => if st.brk || st.ret.isSome then 0 else
    ((heap.dstates ds).map (fun state => state.lookahead.toNat)).getD 0 +
      ((r.get heap).map (fun stream => stream.avail_in.toNat)).getD 0 + 1
  let Q : LoopS → Heap → Prop := fun st heap => Inv st heap ∧ (st.ret = some need_more ∨ (st.ret = none ∧ st.brk = true))
  have step : ∀ st heap, Inv st heap → ∃ c st1 heap1,
      forever st heap = .ok ((c, st1), heap1) ∧ (c = false → Q st1 heap1) ∧
      (c = true → ∃ st2 heap2, deflate_slow_body (some (.tab ds)) Z_FINISH st1 heap1 = .ok (st2, heap2) ∧
        Inv st2 heap2 ∧ rank st2 heap2 < rank st heap) := by
    intro st heap inv
    have initialInv := inv
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, delivered,
      state, endS, buffersS, accountS, endpointS, agreesS, baseS, validS, retS, outputS, _stopS, _eofS, remainingS, _strictS⟩ := inv
    refine ⟨!(st.brk || st.ret.isSome), st, heap, rfl, ?_, ?_⟩
    · intro stopped
      refine ⟨initialInv, ?_⟩
      rcases retS with running | returned
      · right
        refine ⟨running, ?_⟩
        cases brkEq : st.brk with
        | false => simp [brkEq, running] at stopped
        | true => rfl
      · exact Or.inl returned
    · intro continued
      have running : st.ret = none := by
        rcases retS with running | returned
        · exact running
        · simp [returned] at continued
      have brkS : st.brk = false := by
        cases brkEq : st.brk with
        | false => rfl
        | true => simp [brkEq] at continued
      have pointerS : currentZ.next_out = .ref (.dstate_depth owner) (oo + delivered) := by
        rw [accountS.2.2.2.2.2.1, pointer]
        rfl
      obtain ⟨used, produced, next, after, nextZ, result, nextBase, nextYs, nextInput, nextOrigin,
        bodyRun, stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, reasonA, retA, outputA, decrease, breakA⟩ :=
        default_foreign_slow_finish_ready_step state endS buffersS positive pointerS memory wrap (outputS running) validS st
      have retNext : next.ret = none ∨ next.ret = some need_more := by
        rcases retA with same | returned
        · exact Or.inl (same.trans running)
        · exact Or.inr returned
      have agrees : ∀ i, i < startEnd → nextInput i = input i := by
        intro i before
        exact (agreesA i (by omega)).trans (agreesS i before)
      have stopA : next.ret = some need_more → nextZ.avail_out = 0 := by
        intro returned
        rcases reasonA returned with old | empty
        · rw [running] at old; cases old
        · exact empty
      have eofA : next.brk = true → result.lookahead = 0 ∧ nextZ.avail_in = 0 := by
        intro broke
        rcases breakA broke with old | eof
        · rw [brkS] at old; cases old
        · exact eof
      have remainingA : result.lookahead.toNat + nextZ.avail_in.toNat ≤
          currentD.lookahead.toNat + currentZ.avail_in.toNat := by
        by_cases broke : next.brk = true
        · obtain ⟨lookZero, inputZero⟩ := eofA broke
          simp only [lookZero, inputZero, UInt32.toNat_zero, Nat.zero_add, Nat.zero_le]
        · have less := decrease running (Or.inl (Bool.eq_false_iff.mpr broke))
          omega
      have strictA : next.ret = some need_more → result.lookahead.toNat + nextZ.avail_in.toNat <
          d.lookahead.toNat + z.avail_in.toNat := by
        intro returned
        have less := decrease running (Or.inr returned)
        omega
      have account := stream_accounting_trans accountS accountA
      have nextInv : Inv next after :=
        ⟨nextZ, result, nextInput, nextOrigin, nextBase, nextYs, accepted + used, delivered + produced,
          stateA, endA, buffersA, account, by omega, agrees, Nat.le_trans baseS baseA,
          input_valid_accounting_output validS accountA, retNext, outputA, stopA, eofA, by omega, strictA⟩
      refine ⟨next, after, bodyRun, nextInv, ?_⟩
      have beforeRank : rank st heap = currentD.lookahead.toNat + currentZ.avail_in.toNat + 1 := by
        simp [rank, running, brkS, state.good.live.hs, state.good.live.hz]
      rw [beforeRank]
      rcases retNext with nextRunning | returned
      · by_cases broke : next.brk = true
        · simp [rank, broke]
        · have nextBrk : next.brk = false := Bool.eq_false_iff.mpr broke
          have afterRank : rank next after = result.lookahead.toNat + nextZ.avail_in.toNat + 1 := by
            simp [rank, nextRunning, nextBrk, stateA.good.live.hs, stateA.good.live.hz]
          rw [afterRank]
          have less := decrease running (Or.inl nextBrk)
          omega
      · simp [rank, returned]
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, 0, boundary, frontier, buffers, stream_accounting_zero z,
      by simp [startEnd], fun _ _ => rfl, Nat.le_refl _, inputValid, Or.inl rfl, fun _ => publish,
      (fun impossible => by cases impossible), (fun impossible => by cases impossible),
      Nat.le_refl _, (fun impossible => by cases impossible)⟩
  have bound : rank {} h < fuel := by
    have remaining := remaining_below_fuel boundary.toContentBoundary
    simpa [rank, boundary.good.live.hs, boundary.good.live.hz] using remaining
  obtain ⟨final, after, loop, finalInv, stopped⟩ := while_heap_rank Inv rank Q step initial bound
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, produced, stateA, endA, buffersA, accountA,
    endpointA, agreesA, baseA, _validA, _retA, outputA, stopA, eofA, _remainingA, strictA⟩ := finalInv
  exact ⟨used, produced, final, after, z', result, base', ys, extended, nextOrigin,
    loop, stateA, endA, buffersA, accountA, agreesA, endpointA, baseA, stopped, stopA, eofA, outputA, strictA⟩


/-- The FINISH strategy call with strict `need_more` progress. -/
theorem foreign_deflate_slow_finish_progress {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (ret ≠ need_more → result.lookahead = 0 ∧ result.bi_valid.toInt = 0) ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = finish_started ∧ z'.avail_out = 0 ∧ z'.avail_in = 0) ∨
       (ret = finish_done ∧ 0 < z'.avail_out.toNat ∧ z'.avail_in = 0)) ∧
      (ret = need_more →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) := by
  obtain ⟨used, produced, final, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      loop, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, stopped, stopOutput, stopInput, outputL, strictL⟩ :=
    foreign_slow_finish_loop_progress boundary frontier buffers positive pointer memory wrap publish inputValid
  rcases stopped with returned | ⟨running, broke⟩
  · refine ⟨used, produced, need_more, loopHeap, loopZ, loopD, loopBase, loopSymbols, extended, nextOrigin,
      ?_, stateL, endL, buffersL, accountL, agreesL, endpointL, baseL, (fun impossible => False.elim (impossible rfl)), Or.inl ⟨rfl, stopOutput returned⟩,
      fun _ => strictL returned⟩
    rw [deflate_slow_eof_tail_source, bind_app, loop]
    simp only [returned]
    rfl
  · have eof := stopInput broke
    have readyL := outputL running
    have localState : StrategyBoundary loopHeap r ds loopZ loopD extended nextOrigin loopBase loopSymbols (engineConfig loopD) := by
      rw [stateL.configuration]
      exact stateL
    have pointerL : loopZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountL.2.2.2.2.2.1, pointer]
      rfl
    have levelL : loopD.level = config.level := congrArg EngineConfig.level stateL.configuration
    have memoryL : loopD.lit_bufsize = config.memory := congrArg EngineConfig.memory stateL.configuration
    have wrapL : loopD.wrap = config.wrap := congrArg EngineConfig.wrap stateL.configuration
    obtain ⟨tailProduced,after,z',result,tailSymbols,_before,_written,_remaining,_kind,_body,_padding,
        tailRun,contentA,buffersA,accountA,clearA,configA,lookA,startA,_availableA,insertA,bitsA,phaseA,_symbols,
        finalA,_rest⟩ :=
      default_foreign_slow_eof_finish_tail_encoding localState endL buffersL eof.1 (by rw [levelL];exact positive)
        pointerL readyL.2.1 (by rw [memoryL];exact memory) readyL.1 (wrapL.trans wrap)
    have zeroA : result.lookahead=0 ∧ result.bi_valid.toInt=0 := by
      have lower := contentA.good.inv.bits.1
      exact ⟨lookA,by omega⟩
    have configuration : engineConfig result = config := Eq.trans configA stateL.configuration
    have strictA : result.sym_next.toNat < result.sym_end.toNat := by
      obtain ⟨_, _, trees, ledger, _⟩ := contentA.symbols
      have count := ledger.count
      have extent := trees.base.sym_end
      have lower := trees.base.lit_lo
      simp only [List.length_nil, Nat.mul_zero] at count
      omega
    have stateA : StrategyBoundary after r ds z' result extended nextOrigin (loopBase + represented tailSymbols) [] config :=
      ⟨contentA, configuration, clearA, bitsA, strictA, phaseA⟩
    have endA : EndFrontier after result := by
      have topEq : min result.strstart.toNat (fillEnd result - 2) = result.strstart.toNat - result.insert.toNat := by
        dsimp only [fillEnd]
        rw [lookA, insertA, startA]
        change min loopD.strstart.toNat (loopD.strstart.toNat + 0 - 2) = loopD.strstart.toNat - min loopD.strstart.toNat 2
        omega
      unfold EndFrontier
      rw [topEq]
      exact contentA.frontier
    have inputA : z'.avail_in = 0 := by
      have count := accountA.2.2.1
      rw [eof.2] at count
      apply UInt32.toNat_inj.mp
      change z'.avail_in.toNat = 0
      change z'.avail_in.toNat + 0 = 0 at count
      omega
    refine ⟨used, produced + tailProduced, if z'.avail_out == 0 then finish_started else finish_done,
      after, z', result, loopBase + represented tailSymbols, [], extended, nextOrigin,
      ?_, stateA, endA, buffersA, ?_, agreesL, ?_, Nat.le_trans baseL (Nat.le_add_right _ _), (fun _ => zeroA), ?_, ?_⟩
    · rw [deflate_slow_eof_tail_source, bind_app, loop]
      simp only [running]
      exact tailRun
    · simpa only [Nat.add_zero] using stream_accounting_trans accountL accountA
    · have endEq : fillEnd result = fillEnd loopD := by
        dsimp only [fillEnd]
        rw [startA, lookA, eof.1]
      rw [endEq]
      exact endpointL
    · by_cases empty : z'.avail_out = 0
      · right; left
        exact ⟨by simp [empty], empty, inputA⟩
      · right; right
        have nonzero : z'.avail_out.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        exact ⟨by simp [empty], by omega, inputA⟩
    · intro impossible
      split at impossible
      · cases (by decide : finish_started ≠ need_more) impossible
      · cases (by decide : finish_done ≠ need_more) impossible


/-- The buffered boundary has the same strict `need_more` progress. -/
theorem foreign_deflate_slow_finish_buffered_progress {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced ret after z' result base' ys extended nextOrigin,
      deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧ StrategyControls d result ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      (ret ≠ need_more → result.lookahead = 0 ∧ result.bi_valid.toInt = 0) ∧
      ((ret = need_more ∧ z'.avail_out = 0) ∨
       (ret = finish_started ∧ z'.avail_out = 0 ∧ z'.avail_in = 0) ∨
       (ret = finish_done ∧ 0 < z'.avail_out.toNat ∧ z'.avail_in = 0)) ∧
      (ret = need_more →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) := by
  obtain ⟨used, produced, ret, after, z', result, base', ys, extended, nextOrigin,
      run, stateA, controls, resume, buffersA, account, agrees, endpoint, baseLe, zero, classification⟩ :=
    default_foreign_deflate_slow_finish_buffered boundary buffers positive pointer memory wrap publish inputValid
  obtain ⟨_usedP, _producedP, retP, afterP, zP, resultP, _baseP, _ysP, _extendedP, _originP,
      runP, stateP, _endP, _buffersP, _accountP, _agreesP, _endpointP, _baseLeP, _zeroP, _classificationP, strict⟩ :=
    foreign_deflate_slow_finish_progress (boundary.strategy publish) boundary.end_frontier buffers
      positive pointer memory wrap publish inputValid
  obtain ⟨code, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
  subst retP afterP
  have streams : zP = z' := Option.some.inj (stateP.good.live.hz.symm.trans stateA.good.live.hz)
  have states : resultP = result := Option.some.inj (stateP.good.live.hs.symm.trans stateA.good.live.hs)
  subst zP resultP
  exact ⟨used, produced, ret, after, z', result, base', ys, extended, nextOrigin,
    run, stateA, controls, resume, buffersA, account, agrees, endpoint, baseLe, zero, classification, strict⟩

/-- The public data tail with FINISH progress. -/
theorem foreign_public_busy_slow_finish_progress {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used produced rc after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = d.last_flush) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) ∧
      (result.status = BUSY_STATE →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) := by
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]
    decide
  obtain ⟨used, produced, ret, middle, middleZ, middleD, middleBase, ys, extended, nextOrigin,
      strategyRun, stateM, controlsM, resumeM, buffersM, accountM, _agreesM, _endpointM, _baseM, finishing, classification, strictM⟩ :=
    foreign_deflate_slow_finish_buffered_progress boundary buffers positive pointer memory wrap publish inputValid
  have sourceRun : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, strategyRun]
  rcases classification with ⟨returned, exhausted⟩ | ⟨returned, exhausted, _empty⟩ | ⟨returned, remaining, empty⟩
  · subst ret
    have run := public_strategy_need_more stateM.good.live.hz stateM.good.live.hs exhausted
    have stateF := last_flush_buffered_boundary stateM (-1)
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers stateM.good buffersM (-1), accountM, Or.inl rfl, stateF.bits,
      Or.inl ⟨extended, nextOrigin, middleBase, ys, stateF, controlsM.status.trans status⟩, Or.inl rfl, ?_,
      fun _ => strictM rfl, ?_⟩
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · intro impossible
      have wrong : BUSY_STATE = FINISH_STATE := (controlsM.status.trans status).symm.trans impossible
      cases (by decide : BUSY_STATE ≠ FINISH_STATE) wrong
  · subst ret
    have emptyS := _empty
    have finished := finishing (by decide)
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    have stateS := buffered_finish_status stateM
    have stateF := last_flush_buffered_boundary stateS (-1)
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    have phase := finishing_phase_of_buffered stateF rfl finished.1 finished.2 wrapM
    have run := public_strategy_finish_started stateM.good.live.hz stateM.good.live.hs exhausted
    refine ⟨used, produced, Z_OK, _, middleZ, _, sourceRun.trans run, stateF.good,
      last_flush_buffers goodS buffersS (-1), accountM, Or.inl rfl, stateF.bits, Or.inr phase, Or.inl rfl, ?_, ?_,
      fun _ => emptyS⟩
    · intro impossible
      cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
    · intro impossible
      cases (by decide : FINISH_STATE ≠ BUSY_STATE) impossible
  · subst ret
    have finished := finishing (by decide)
    have ready := resumeM remaining
    have goodS := finish_status_good stateM.good
    have buffersS := finish_status_buffers stateM.good buffersM
    obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateM.symbols
    have treesS := finish_status_trees trees
    have pointerM : middleZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountM.2.2.2.2.2.1, pointer]
      rfl
    have wrapM : middleD.wrap = 1 := (congrArg EngineConfig.wrap stateM.configuration).trans wrap
    obtain ⟨trailerProduced, after, z', result, _written, _pendingBits, trailerRun, goodA, buffersA, accountA,
      _sizes, _amount, _left, wrapA, bitsA, fields, _bytes, _pendingA, _trailerBits,
      _adlerA, _inputA, _outputA, _allocA, _nextA, _preciseA, _tailA⟩ :=
      foreign_zlib_trailer_publish_encoding goodS treesS buffersS pointerM wrapM ready.1 ready.2.1 finished.2
    have phase : FinishingPhase result config := by
      refine ⟨by rw [fields], by rw [fields]; exact finished.1, bitsA, ?_, Or.inr wrapA, ?_⟩
      · rw [wrapA, fields]
        change { engineConfig middleD with wrap := -1 } = { config with wrap := -1 }
        rw [stateM.configuration]
      · intro positiveWrap
        rw [wrapA] at positiveWrap
        cases (show (-1 : Int32) ≠ 1 from by decide) positiveWrap
    have run := public_strategy_finish_done stateM.good.live.hz stateM.good.live.hs
    refine ⟨used, produced + trailerProduced, if result.pending != 0 then Z_OK else Z_STREAM_END,
      after, z', result, sourceRun.trans (run.trans trailerRun), goodA, buffersA, ?_, ?_, ?_, Or.inr phase, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero] using stream_accounting_trans accountM accountA
    · by_cases queued : result.pending = 0 <;> simp [queued]
    · rw [bitsA]
      decide
    · right
      rw [fields]
      exact controlsM.last_flush
    · intro ended
      have drained : result.pending = 0 := by
        by_cases queued : result.pending = 0
        · exact queued
        · simp [queued, show Z_OK ≠ Z_STREAM_END from by decide] at ended
      have inputA : z'.avail_in = 0 := by
        have count := accountA.2.2.1
        rw [empty] at count
        apply UInt32.toNat_inj.mp
        change z'.avail_in.toNat = 0
        change z'.avail_in.toNat + 0 = 0 at count
        omega
      exact ⟨phase.status, wrapA, inputA, phase.lookahead, drained, bitsA⟩
    · intro impossible
      have code : FINISH_STATE = BUSY_STATE := phase.status.symm.trans impossible
      cases (by decide : FINISH_STATE ≠ BUSY_STATE) code
    · intro _
      apply UInt32.toNat_inj.mp
      have count := accountA.2.2.1
      rw [empty] at count
      change z'.avail_in.toNat + 0 = 0 at count
      exact count

/-- The public BUSY FINISH call with progress. -/
theorem foreign_public_busy_finish_progress {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (output : 0 < z.avail_out.toNat)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) ∧ result.bi_valid.toInt < 8 ∧
      PublicFinishPhase after r ds z' result config ∧ (result.last_flush = -1 ∨ result.last_flush = Z_FINISH) ∧
      (rc = Z_STREAM_END → result.status = FINISH_STATE ∧ result.wrap = -1 ∧
        z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.pending = 0 ∧ result.bi_valid.toInt = 0) ∧
      (result.status = BUSY_STATE →
        result.lookahead.toNat + z'.avail_in.toNat < d.lookahead.toNat + z.avail_in.toNat ∨
        (result.lookahead.toNat + z'.avail_in.toNat = d.lookahead.toNat + z.avail_in.toNat ∧
          result.pending.toNat < d.pending.toNat)) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro impossible; cases impossible
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; contradiction
  have boundary0 := last_flush_buffered_boundary boundary Z_FINISH
  have buffers0 := last_flush_buffers boundary.good buffers Z_FINISH
  by_cases queued : d.pending = 0
  · have ready : PublishReady { d with last_flush := Z_FINISH } :=
      ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨used, produced, rc, after, z', result, run, goodA, buffersA, account, allowed, bits, phase, last, ended,
        strict, emptyA⟩ :=
      foreign_public_busy_slow_finish_progress boundary0 buffers0 status level strategy pointer memory wrap ready inputValid
    have entry := public_busy_finish_entry boundary.good status queued nonnull positive inputValid lower upper
    exact ⟨used, produced, rc, after, z', result, entry.trans run, goodA, buffersA, account, allowed, bits, phase, last,
      ended, fun busy => Or.inl (strict busy), emptyA⟩
  · obtain ⟨before, pending⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, after, z', result, _written, _remaining, _base, run, stateA, buffersA, account, _sizes, _storage,
          _outA, last, pendingCount, bits, fields, _bytes, _pendingA, _bitsA, _frameA⟩ :=
        public_pending_buffered_exhausted_foreign Z_FINISH boundary buffers pointer inputValid (by decide) (by decide)
          (fun _ => rfl) output enough pending
      refine ⟨0, z.avail_out.toNat, Z_OK, after, z', result, run, stateA.good, buffersA, account, Or.inl rfl, bits,
        Or.inl ⟨input, origin, base, xs, stateA, ?_⟩, Or.inl last, ?_, ?_, ?_⟩
      · rw [fields]; exact status
      · intro impossible
        cases (show Z_OK ≠ Z_STREAM_END from by decide) impossible
      · intro _
        right
        have look : result.lookahead = d.lookahead := by rw [fields]
        have inputCount := account.2.2.1
        constructor
        · rw [look]
          omega
        · omega
      · intro impossible
        have sameStatus : result.status = BUSY_STATE := by rw [fields]; exact status
        cases (by decide : BUSY_STATE ≠ FINISH_STATE) (sameStatus.symm.trans impossible)
    · have pending0 := last_flush_pending_bits boundary.good pending Z_FINISH
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
          accountM, _sizesM, _storageM, amount, _pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM, _frameM⟩ :=
        flush_pending_buffered_foreign_boundary boundary0 buffers0 pointer pending0
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.dstate_depth owner) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      obtain ⟨used, laterProduced, rc, after, z', result, tailRun, goodA, buffersA, accountA, allowed, bits, phase, last,
          ended, strict, emptyA⟩ :=
        foreign_public_busy_slow_finish_progress stateM buffersM statusM levelM strategyM pointerM memory wrap (readyM left)
          (input_valid_accounting_output inputValid accountM)
      have entry := public_pending_finish_continue boundary.good stateM.good nonnull positive inputValid queued flushRun
        (by intro zero; rw [zero] at left; contradiction) (by
          intro impossible; rw [statusM] at impossible; cases (show BUSY_STATE ≠ FINISH_STATE from by decide) impossible)
      have lastM : dm.last_flush = Z_FINISH := by rw [fields]
      rw [lastM] at last
      refine ⟨used, produced + laterProduced, rc, after, z', result,
        entry.trans ((public_busy_header_skip stateM.good statusM).trans tailRun), goodA, buffersA, ?_,
        allowed, bits, phase, last, ended, ?_, emptyA⟩
      · simpa only [Nat.zero_add] using stream_accounting_trans accountM accountA
      · intro busy
        left
        have decrease := strict busy
        have look : dm.lookahead = d.lookahead := by rw [fields]
        have inputCount := accountM.2.2.1
        rw [look] at decrease
        omega


/-- **The FINISH rank for a foreign output pointer**: the twin of
`DefaultFinishBoundary.finish_progress`. -/
theorem DefaultFinishBoundary.foreign_finish_progress {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0)
    (started : d.status ≠ INIT_STATE) :
    let rank := fun (stream : ZStream) (state : DeflateState) =>
      (state.lookahead.toNat + stream.avail_in.toNat) * 131078 +
        (if state.status = BUSY_STATE then 65541 + state.pending.toNat
         else state.pending.toNat + (if state.wrap = 1 then 4 else 0))
    ∃ used produced rc after z' result,
      deflate (some r) Z_FINISH h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_OK → rank z' result < rank z d) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) ∧ result.status ≠ INIT_STATE := by
  dsimp only
  obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed, _ended⟩ :=
    boundary.foreign_finish buffers pointer output valid accepted
  have startedA : result.status ≠ INIT_STATE := by
    rcases stateA.phase with ⟨_input, _origin, _base, start, _state⟩ | phaseA
    · -- a FINISH call never returns to INIT_STATE
      exfalso
      rcases boundary.phase with ⟨_i, _o, _b, startD, _s⟩ | working | finishing
      · exact started startD.status
      · obtain ⟨input, origin, base, xs, state, status⟩ := working
        have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
        have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
        obtain ⟨_u, _p, rcP, afterP, zP, resultP, runP, goodP, _b, _a, _al, _bits, phaseP, _last, _ended⟩ :=
          default_foreign_public_busy_finish_phase state buffers status level strategy pointer boundary.configuration.memory
            boundary.configuration.wrap output valid boundary.lower boundary.upper
        obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
        subst afterP
        have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans stateA.good.live.hs)
        subst resultP
        exact public_finish_phase_started phaseP start.status
      · obtain ⟨_produced, _rc, afterP, _zP, resultP, runP, goodP, _b, _a, _al, phaseP, _last, _empty, _ended⟩ :=
          public_default_foreign_finishing_phase boundary.good buffers finishing pointer (accepted finishing.status)
            output boundary.lower boundary.upper
        obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
        subst afterP
        have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans stateA.good.live.hs)
        subst resultP
        have initial := start.status
        rw [phaseP.status] at initial
        exact (by decide : FINISH_STATE ≠ INIT_STATE) initial
    · exact public_finish_phase_started phaseA
  refine ⟨used, produced, rc, after, z', result, run, stateA, buffersA, account, allowed, ?_⟩
  rcases boundary.phase with ⟨_input, _origin, _base, start, _state⟩ | working | finishing
  · exact False.elim (started start.status)
  · obtain ⟨input, origin, base, xs, state, status⟩ := working
    have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
    have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
    obtain ⟨_usedP, _producedP, rcP, afterP, zP, resultP, runP, goodP, _buffersP, _accountP,
        _allowedP, _bitsP, phaseP, _lastP, _endedP, progress, emptyP⟩ :=
      foreign_public_busy_finish_progress state buffers status level strategy pointer boundary.configuration.memory
        boundary.configuration.wrap output valid boundary.lower boundary.upper
    obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
    subst rcP afterP
    have streams : zP = z' := Option.some.inj (goodP.live.hz.symm.trans stateA.good.live.hz)
    have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans stateA.good.live.hs)
    subst zP resultP
    refine ⟨?_, emptyP, startedA⟩
    have pendingA := default_memory_pending_count stateA.good phaseP boundary.configuration.memory
    intro _ok
    rw [status, ite_eq_left rfl]
    rcases phaseP with ⟨_inputA, _originA, _baseA, _xsA, _stateA, statusA⟩ | phaseA
    · rw [ite_eq_left statusA]
      rcases progress statusA with less | ⟨equal, less⟩ <;> omega
    · have busyA : result.status ≠ BUSY_STATE := by rw [phaseA.status]; decide
      have emptyA := emptyP phaseA.status
      rw [ite_eq_right busyA, phaseA.lookahead, emptyA]
      simp only [UInt32.toNat_zero, Nat.zero_add, Nat.zero_mul, Nat.zero_add]
      split <;> omega
  · have empty := accepted finishing.status
    obtain ⟨producedP, rcP, afterP, zP, resultP, runP, goodP, accountP, roomP, statusP, sizeP⟩ :=
      foreign_public_finishing_size_execution boundary.good buffers finishing pointer empty output
        boundary.lower boundary.upper
    obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (runP.symm.trans run))
    subst rcP afterP
    have streams : zP = z' := Option.some.inj (goodP.live.hz.symm.trans stateA.good.live.hz)
    have states : resultP = result := Option.some.inj (goodP.live.hs.symm.trans stateA.good.live.hs)
    subst zP resultP
    have emptyA : z'.avail_in = 0 := by
      apply UInt32.toNat_inj.mp
      have count := accountP.2.2.1
      rw [empty] at count
      change z'.avail_in.toNat + 0 = 0 at count
      exact count
    refine ⟨?_, fun _ => emptyA, startedA⟩
    intro ok
    have room := roomP ok
    have outCount := accountP.2.2.2.1
    rw [room] at outCount
    have bitsA : result.bi_valid.toInt = 0 := by
      rcases stateA.phase with ⟨_i, _o, _b, startA, _s⟩ | ⟨_i, _o, _b, _xs, _s, busyA⟩ | finishingA
      · exact absurd startA.status startedA
      · rw [statusP] at busyA; exact absurd busyA (by decide)
      · exact finishingA.bits
    have heldD : heldBytes d = d.pending.toNat := by
      unfold heldBytes; rw [finishing.bits]; rfl
    have heldA : heldBytes result = result.pending.toNat := by
      unfold heldBytes; rw [bitsA]; rfl
    have beforeBusy : d.status ≠ BUSY_STATE := by rw [finishing.status]; decide
    have afterBusy : result.status ≠ BUSY_STATE := by rw [statusP]; decide
    have lookA : result.lookahead = 0 := by
      rcases stateA.phase with ⟨_i, _o, _b, startA, _s⟩ | ⟨_i, _o, _b, _xs, _s, busyA⟩ | finishingA
      · exact absurd startA.status startedA
      · exact absurd busyA afterBusy
      · exact finishingA.lookahead
    rw [ite_eq_right beforeBusy, ite_eq_right afterBusy, finishing.lookahead, empty, lookA, emptyA]
    unfold owedTrailer at sizeP
    simp only [UInt32.toNat_zero, Nat.zero_add, Nat.zero_mul]
    rw [heldD, heldA] at sizeP
    simp only [UInt32.toNat_zero] at outCount
    omega

end Zlib.Deflate.Engine.Proofs
