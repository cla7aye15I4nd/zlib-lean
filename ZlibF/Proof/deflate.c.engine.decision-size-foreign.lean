import ZlibF.Proof.«deflate.c.engine.decision-size»
import ZlibF.Proof.«deflate.c.engine.flush-macro-size-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-boundary»

/-! # The size of a slow decision into a foreign output pointer

The twins of `deflate.c.engine.decision-size.lean` for a caller output pointer into another deflate state's `depth`
array.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Both selected-match paths: the size of the decision. The block of a flush is the symbols so
far and the match. -/
theorem foreign_slow_match_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base produced : Nat} {z returned : ZStream} {d d' : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d)
    (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some returned) (state : after.dstates ds = some d')
    (account : StreamAccounting z returned 0 produced) :
    DecisionSize d d' produced (xs ++ [emittedMatch d]) ∧ DecisionCompanion d d' ∧
      (d'.sym_next = 0 ∨ SymbolBoundary after ds d' (xs ++ [emittedMatch d])) := by
  obtain ⟨head, emittedHeap, emitted, emitRun, emittedBoundary, emittedFrontier, emittedBuffers, emitFrame,
      emittedFlag, emittedStart, _emittedLook, _emittedEnd, emittedCount, emittedEndCount, _storage⟩ :=
    slow_match_emit_search_boundary cut buffers selected strict candidate
  have resetE : emitted.match_length = MIN_MATCH_u - 1 :=
    slow_match_emit_length emitRun emittedBoundary.good.live.hs
  have notThree : ¬ (emitted.match_length = 3) := by rw [resetE]; decide
  have readyE := ready.slow emitFrame
  have configE := ConfigFrame.slow emitFrame
  have clearE := clear.slow emitFrame
  by_cases full : (d.sym_next + 3 == d.sym_end) = true
  · obtain ⟨amount, other, otherZ, otherD, flushRun, boundaryA, _endA, _buffersA, accountA, _clearA,
        _frameA, _lowA, _phaseA⟩ :=
      default_foreign_flush_nonfinal_end_boundary emittedBoundary emittedFrontier emittedBuffers
        (by rw [configE.level]; exact positive) pointer readyE.2.1
        (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega) clearE emittedFlag
    have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if otherZ.avail_out == 0 then { st with hash_head := head, bflush := true, ret := some need_more }
          else { st with hash_head := head, bflush := true }), other) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, full, ite_true, flushRun]
      by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
    have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
    subst heaps
    obtain ⟨wb, body, startA, keepA, emptiedA, size, nullCost, storedCost, _final⟩ :=
      foreign_flush_control_run_size_effects emittedBoundary emittedBuffers
        (by rw [configE.level]; exact positive) pointer readyE.2.1
        (by rw [configE.memory]; exact memory) readyE.1 (by have low := readyE.2.2; omega)
        clearE emittedFlag false flushRun live state account
    obtain ⟨_pbE, _bufE, treesE, ledgerE, _balanceE⟩ := emittedBoundary.symbols
    have countE := ledgerE.count
    have endE := treesE.base.sym_end
    have memE : emitted.lit_bufsize.toNat = 16384 := by rw [configE.memory]; exact memory
    have fullEq : d.sym_next + 3 = d.sym_end := beq_iff_eq.mp full
    have endD : emitted.sym_end.toNat = d.sym_end.toNat := by rw [emittedEndCount]
    have fullNat : d.sym_next.toNat + 3 = d.sym_end.toNat := by
      rw [← fullEq, UInt32.toNat_add]
      simp only [UInt32.reduceToNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    have bitsEq : emitted.bi_valid = d.bi_valid := by rw [emitFrame]
    have startEq : emitted.block_start = d.block_start := by rw [emitFrame]
    have sourceEq : defaultStoredSource emitted wb = defaultStoredSource d wb := by
      unfold defaultStoredSource
      rw [startEq]
    rw [bitsEq] at size storedCost
    rw [sourceEq] at nullCost storedCost
    have balanceE : BlockBalance emitted (xs ++ [emittedMatch d]) 0 := by
      obtain ⟨_, _, _, _, balance⟩ := emittedBoundary.symbols
      simpa only [deferredCredit, emittedFlag, ite_true] using balance
    unfold BlockBalance at balanceE
    have startD : d'.block_start.toInt = emitted.strstart.toNat := by
      rw [startA]; exact position_block_start _
    refine ⟨Or.inr ⟨?_, ledgerE.valid, emptiedA, ?_, ?_, wb, body, size, nullCost, storedCost⟩, ?_, Or.inl emptiedA⟩
    · omega
    · rw [startD, ← startEq]
      omega
    · rw [startD]
      omega
    · intro _ _
      refine ⟨fun three => absurd (keepA.1.symm.trans three) notThree, fun negative => ?_⟩
      exact absurd negative (by rw [startA]; exact block_start_position_nonneg _)
  · have nonfull := Bool.eq_false_iff.mpr full
    have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
        .ok ({ st with hash_head := head, bflush := false }, emittedHeap) := by
      rw [slow_decision_match_source cut.good.live.hs selected flush st candidate]
      simp only [bind_app, emitRun, nonfull, Bool.false_eq_true, ite_false, pure_app]
    have heaps : emittedHeap = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
    subst heaps
    have sameZ : z = returned := Option.some.inj (emittedBoundary.good.live.hz.symm.trans live)
    subst sameZ
    have sameD : emitted = d' := Option.some.inj (emittedBoundary.good.live.hs.symm.trans state)
    subst sameD
    have none : produced = 0 := by
      have output := account.2.2.2.1
      omega
    refine ⟨Or.inl ⟨none, ?_, ?_, ?_⟩, ?_, Or.inr emittedBoundary.symbols⟩
    · rw [emitFrame]
    · rw [emitFrame]
    · rw [emitFrame]
    · intro _ floor
      refine ⟨fun three => absurd three notThree, fun negative => ?_⟩
      have startSame : emitted.block_start = d.block_start := by rw [emitFrame]
      have wSame : emitted.w_size = d.w_size := by rw [emitFrame]
      rw [startSame] at negative
      rw [wSame]
      have := floor negative
      omega

/-- The literal path when its tally fills the symbol buffer: a block of exactly 16383 symbols. -/
theorem foreign_slow_literal_full_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base produced : Nat} {z returned : ZStream} {d d' : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some returned) (state : after.dstates ds = some d')
    (account : StreamAccounting z returned 0 produced) :
    DecisionSize d d' produced (xs ++ [emittedLiteral d wa]) ∧ DecisionCompanion d d' ∧ d'.sym_next = 0 := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have previousByte := cut.deferred available
  have balance1 : BlockBalance d xs 1 := by simpa only [deferredCredit, available, ite_false] using balance
  have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_false] using cut.accounted
  let c := wa[d.strstart.toNat - 1]!
  let dt := literalState d c
  let packed := literalBytes buf d c
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := Nat.le_of_eq full
  have goodT : DGood ht r ds z dt := literal_good_after cut.good trees c room
  have treesT : TreesInvAt ht ds dt pb packed := tally_literal_trees trees c room
  have tallyFrame := pending_state_byte_frame h ds pb d dt packed trees.base.pbuf
  have tallyOwned := stream_owned_keys cut.good goodT rfl rfl rfl rfl
  have buffersT : StreamBuffers ht r := stream_buffers_private_read cut.good.live.hz goodT.live.hz buffers
    tallyFrame (fun b owned => (stream_owned_deflate cut.good b).mpr owned) tallyOwned (stream_accounting_zero z) rfl
  have getT : ht.bytes w = some wa := pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have ledgerT : SymbolLedger packed dt (xs ++ [emittedLiteral d wa]) := ledger_literal trees.base ledger room c
  have balanceT : BlockBalance dt (xs ++ [emittedLiteral d wa]) 0 := by
    simpa only [dt, c, emittedLiteral, show (1 : Int) - 1 = 0 from rfl] using balance_literal balance1 c
  have accountedT : base + represented (xs ++ [emittedLiteral d wa]) = origin + dt.strstart.toNat := by
    rw [represented_snoc, show (emittedLiteral d wa).bytes = 1 from rfl]
    exact accounted
  have meaning := literal_input_meaning cut.deferred available cut.view
  have oldEnd : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← oldEnd] at meaning
  have traceT := cut.trace.snoc meaning
  have clearT : BlockInit.BlockClear dt := ⟨clear.bl, clear.opt, clear.fixed⟩
  have flag : (d.sym_next + 3 == d.sym_end) = true := by
    apply beq_iff_eq.mpr
    apply UInt32.toNat_inj.mp
    rw [← full]
    exact literal_count trees.base room c
  have tally : tally_lit (some (.tab ds)) c h = .ok (true, ht) := by
    simpa only [flag] using tally_literal_run trees.base c room
  have bitsT : dt.bi_valid.toInt ≤ 7 := by
    change d.bi_valid.toInt ≤ 7
    have low := ready.2.2
    omega
  obtain ⟨emittedHeap, z', emitted, amount, blockBody, emitRun, goodE, accountE, startE, keepE, emptiedE, size, nullCost, storedCost, _finalE⟩ :=
    foreign_flush_macro_size goodT treesT buffersT positive pointer ready.2.1 memory ready.1
      bitsT ledgerT clearT traceT cut.window getT cut.range balanceT accountedT cut.view false
  have emitRun0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 ht = .ok ((), emittedHeap) := emitRun
  let finalD := advanceOne emitted
  let finalHeap := setD emittedHeap ds finalD
  have write : wr (some (.tab ds)) advanceOne emittedHeap = .ok ((), finalHeap) := by
    simp only [wrD_eq, goodE.live.hs, finalHeap, finalD]
  have output : zrd (some r) (·.avail_out) finalHeap = .ok (z'.avail_out, finalHeap) := by
    simp only [zrd_eq, finalHeap, ZStreamRef.get_setD, goodE.live.hz]
  have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
      .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
        else { st with hash_head := candidate, bflush := true }), finalHeap) := by
    obtain ⟨size, _⟩ := window_extent cut.good cut.window cut.bytes
    have fit : d.strstart.toNat - 1 < wa.size := by have range := cut.range; dsimp only [fillEnd] at range; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [cut.window, u32_sub_one previousByte]
      simpa [OkOn, fit, c] using index8_ok (off := 0) (i := d.strstart.toNat - 1) cut.bytes (by omega)
    unfold slowDecision
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, branch, Bool.false_eq_true, ite_false,
      hasLiteral, ite_true, read, tally, emitRun0]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head := candidate, bflush := true, ret := some need_more }
      return { st with hash_head := candidate, bflush := true }) emittedHeap = _
    rw [bind_app, write]
    simp only [cut.good.live.back, bind_app, output]
    by_cases fullOut : (z'.avail_out == 0) = true <;> simp [fullOut]
  have getFinal : r.get finalHeap = some z' := by
    simpa only [finalHeap, ZStreamRef.get_setD] using goodE.live.hz
  have heaps : finalHeap = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
  subst heaps
  have sameZ : z' = returned := Option.some.inj (getFinal.symm.trans live)
  subst sameZ
  have sameD : finalD = d' := by
    have getD : finalHeap.dstates ds = some finalD := by simp only [finalHeap, setD_dstates_same]
    exact Option.some.inj (getD.symm.trans state)
  subst sameD
  have count : produced = amount := (stream_accounting_counts_unique account accountE).2
  subst count
  have bitsT' : dt.bi_valid = d.bi_valid := rfl
  have startT : dt.block_start = d.block_start := rfl
  have sourceEq : ∀ wb, defaultStoredSource dt wb = defaultStoredSource d wb := by
    intro wb
    unfold defaultStoredSource
    rw [startT]
  have countT := ledgerT.count
  have endT := treesT.base.sym_end
  have lengthFull : (xs ++ [emittedLiteral d wa]).length = 16383 := by
    have countE : dt.sym_next.toNat = d.sym_next.toNat + 3 := literal_count trees.base room c
    have endEq : dt.sym_end = d.sym_end := rfl
    have memT : dt.lit_bufsize.toNat = 16384 := memory
    rw [endEq] at endT
    omega
  have advanced : finalD.pending = emitted.pending ∧ finalD.bi_valid = emitted.bi_valid := ⟨rfl, rfl⟩
  have startFinal : finalD.block_start = emitted.block_start := rfl
  have startD : finalD.block_start.toInt = dt.strstart.toNat := by
    rw [startFinal, startE]; exact position_block_start _
  unfold BlockBalance at balanceT
  refine ⟨Or.inr ⟨lengthFull, ledgerT.valid, emptiedE, ?_, ?_, w, blockBody, ?_, ?_, ?_⟩, ?_, emptiedE⟩
  · rw [startD, ← startT]
    omega
  · rw [startD]
    exact Int.le_refl _
  · rw [advanced.1, advanced.2, ← bitsT']
    exact size
  · intro absent
    exact nullCost ((sourceEq w).trans absent)
  · intro present
    rw [← bitsT']
    exact storedCost (fun absent => present ((sourceEq w).symm.trans absent))
  · intro fresh _
    refine ⟨fun three => ?_, fun negative => ?_⟩
    · change emitted.match_length = 3 at three
      have lengthT : dt.match_length = d.match_length := rfl
      have startTm : dt.match_start = d.match_start := rfl
      rw [keepE.1, lengthT] at three
      change emitted.strstart + 1 - 1 - emitted.match_start ≤ TOO_FAR
      rw [keepE.2.1, keepE.2.2, startTm, show dt.strstart = d.strstart from rfl,
        ZlibF.Math.DeflateBound.advanced_short_distance]
      exact fresh three
    · change emitted.block_start.toInt < 0 at negative
      exact absurd negative (by rw [startE]; exact block_start_position_nonneg _)

/-- **The size of every strategy decision**: selected match, literal and defer. -/
theorem foreign_slow_decision_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base produced : Nat} {z returned : ZStream} {d d' : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some returned) (state : after.dstates ds = some d')
    (account : StreamAccounting z returned 0 produced) :
    ∃ ys, DecisionSize d d' produced ys ∧
      (ys = xs ∨ ys = xs ++ [emittedLiteral d wa] ∨
        (3 ≤ d.prev_length.toNat ∧ ys = xs ++ [emittedMatch d])) ∧ DecisionCompanion d d' ∧
      (d'.sym_next = 0 ∨ SymbolBoundary after ds d' ys) := by
  by_cases selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true
  · have large : 3 ≤ d.prev_length.toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
      exact UInt32.le_iff_toNat_le.mp selected.1
    obtain ⟨size, companion, after_list⟩ := foreign_slow_match_run_size_effects cut buffers selected strict positive pointer memory
      ready clear run live state account
    exact ⟨_, size, Or.inr (Or.inr ⟨large, rfl⟩), companion, after_list⟩
  · have branch := Bool.eq_false_iff.mpr selected
    by_cases available : d.match_available = 0
    · obtain ⟨other, otherD, facts⟩ :=
        slow_defer_search_boundary cut buffers lookahead branch available strict flush st candidate
      have keepA := facts.2.2.2.2.2.2.2.2.2.2
      obtain ⟨tested, boundaryA, _endA, _buffersA, frameA, startN, _⟩ := facts
      have startSame : otherD.block_start = d.block_start := by rw [frameA]
      have wSame : otherD.w_size = d.w_size := by rw [frameA]
      have lengthSame : otherD.match_length = d.match_length := keepA.1
      have matchSame : otherD.match_start = d.match_start := keepA.2
      have startU : otherD.strstart = d.strstart + 1 := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, startN]
        simp only [UInt32.reduceToNat]
        have window := cut.range
        dsimp only [fillEnd] at window
        have wsz := cut.good.inv.wsz
        have sizes := slide_window_sizes cut.good
        rw [Nat.mod_eq_of_lt (by omega)]
      have companion : DecisionCompanion d otherD := by
        intro fresh floor
        refine ⟨fun three => ?_, fun negative => ?_⟩
        · rw [lengthSame] at three
          rw [startU, matchSame, ZlibF.Math.DeflateBound.advanced_short_distance]
          exact fresh three
        · rw [startSame] at negative
          rw [wSame]
          have := floor negative
          omega
      have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      subst heaps
      have sameZ : z = returned := Option.some.inj (boundaryA.good.live.hz.symm.trans live)
      have sameD : otherD = d' := Option.some.inj (boundaryA.good.live.hs.symm.trans state)
      subst sameD
      exact ⟨xs, quiet_decision_size xs sameZ.symm frameA account, Or.inl rfl, companion, Or.inr boundaryA.symbols⟩
    · have room := literal_room cut.good.inv strict
      by_cases full : d.sym_next.toNat + 3 = d.sym_end.toNat
      · obtain ⟨size, companion, emptied⟩ := foreign_slow_literal_full_run_size_effects cut buffers lookahead branch available full
          positive pointer memory ready clear run live state account
        exact ⟨_, size, Or.inr (Or.inl rfl), companion, Or.inl emptied⟩
      · have space : d.sym_next.toNat + 3 < d.sym_end.toNat := by omega
        obtain ⟨other, otherD, facts⟩ :=
          slow_literal_search_boundary cut buffers lookahead branch available space flush st candidate
        have keepA := facts.2.2.2.2.2.2.2.2.2.2
        obtain ⟨tested, boundaryA, _endA, _buffersA, frameA, startN, _⟩ := facts
        have startSame : otherD.block_start = d.block_start := by rw [frameA]
        have wSame : otherD.w_size = d.w_size := by rw [frameA]
        have lengthSame : otherD.match_length = d.match_length := keepA.1
        have matchSame : otherD.match_start = d.match_start := keepA.2
        have startU : otherD.strstart = d.strstart + 1 := by
          apply UInt32.toNat_inj.mp
          rw [UInt32.toNat_add, startN]
          simp only [UInt32.reduceToNat]
          have window := cut.range
          dsimp only [fillEnd] at window
          have wsz := cut.good.inv.wsz
          have sizes := slide_window_sizes cut.good
          rw [Nat.mod_eq_of_lt (by omega)]
        have companion : DecisionCompanion d otherD := by
          intro fresh floor
          refine ⟨fun three => ?_, fun negative => ?_⟩
          · rw [lengthSame] at three
            rw [startU, matchSame, ZlibF.Math.DeflateBound.advanced_short_distance]
            exact fresh three
          · rw [startSame] at negative
            rw [wSame]
            have := floor negative
            omega
        have heaps : other = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        subst heaps
        have sameZ : z = returned := Option.some.inj (boundaryA.good.live.hz.symm.trans live)
        have sameD : otherD = d' := Option.some.inj (boundaryA.good.live.hs.symm.trans state)
        subst sameD
        exact ⟨xs ++ [emittedLiteral d wa], quiet_decision_size _ sameZ.symm frameA account, Or.inr (Or.inl rfl),
          companion, Or.inr boundaryA.symbols⟩

/-- **The size of the initialized search and its decision.** -/
theorem foreign_slow_search_decision_run_size_effects {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z returned : ZStream} {d d' : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (live : r.get after = some returned) (state : after.dstates ds = some d')
    (account : StreamAccounting z returned 0 produced)
    (listQuality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (matchQuality : d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR) :
    ∃ ys, DecisionSize d d' produced ys ∧ (∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
      ((d.block_start.toInt < 0 → d.w_size.toNat - 262 ≤ d.strstart.toNat) →
        (d'.match_length = 3 → d'.strstart - 1 - d'.match_start ≤ TOO_FAR) ∧
        (d'.block_start.toInt < 0 → d'.w_size.toNat - 262 ≤ d'.strstart.toNat)) ∧
      (d'.sym_next = 0 ∨ SymbolBoundary after ds d' ys) := by
  obtain ⟨w, wa, head, found, searched, searchRun, cut, searchFrame, searchedBuffers, _storage, prevEq⟩ :=
    slow_search_initialized_boundary boundary.toContentBoundary frontier buffers room
  have slowFrame : SlowRecordFrame d searched := by unfold SlowRecordFrame; rw [searchFrame]
  have configS : engineConfig searched = config := Eq.trans (ConfigFrame.slow slowFrame) boundary.configuration
  have levelS : searched.level = config.level := congrArg EngineConfig.level configS
  have memoryS : searched.lit_bufsize = config.memory := congrArg EngineConfig.memory configS
  have positiveS : 1 ≤ searched.lookahead.toNat := by rw [searchFrame]; exact lookahead
  have strictS : searched.sym_next.toNat < searched.sym_end.toNat := by rw [searchFrame]; exact boundary.strict
  have readyS := ready.slow slowFrame
  have clearS := boundary.clear.slow slowFrame
  have decisionRun : slowDecision (some (.tab ds)) flush st head found = .ok (next, after) := by
    unfold slowSearchDecision at run
    simpa only [bind_app, searchRun] using run
  obtain ⟨ys, size, shape, companion, afterList⟩ := foreign_slow_decision_run_size_effects cut searchedBuffers positiveS strictS
    (by rw [levelS]; exact positive) pointer (by rw [memoryS]; exact memory) readyS clearS decisionRun live state account
  have strSearch : searched.strstart = d.strstart := by rw [searchFrame]
  have quality : ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096 := by
    rcases shape with same | literal | ⟨large, matched⟩
    · subst same; exact listQuality
    · subst literal
      intro s member nonzero
      rcases List.mem_append.mp member with old | fresh
      · exact listQuality s old nonzero
      · simp only [List.mem_singleton] at fresh
        subst fresh
        exact absurd rfl nonzero
    · subst matched
      intro s member
      rcases List.mem_append.mp member with old | fresh
      · exact listQuality s old
      · simp only [List.mem_singleton] at fresh
        subst fresh
        have same : emittedMatch searched = retainedMatchSymbol d := by
          unfold emittedMatch retainedMatchSymbol
          rw [prevEq.1, prevEq.2, strSearch]
        rw [same]
        exact retained_match_short_quality d matchQuality (by rw [← prevEq.1]; exact large)
  have bitsS : searched.bi_valid = d.bi_valid := by rw [slowFrame]
  have pendS : searched.pending = d.pending := by rw [slowFrame]
  have startS : searched.block_start = d.block_start := by rw [slowFrame]
  obtain ⟨fresher, freshGet, freshBound⟩ := slow_search_short_quality boundary.good.live.hs searchRun
  have sameFresh : fresher = searched := Option.some.inj (freshGet.symm.trans cut.good.live.hs)
  rw [sameFresh] at freshBound
  have floorS : (d.block_start.toInt < 0 → d.w_size.toNat - 262 ≤ d.strstart.toNat) →
      (searched.block_start.toInt < 0 → searched.w_size.toNat - 262 ≤ searched.strstart.toNat) := by
    intro floor negative
    have b : searched.block_start = d.block_start := by rw [searchFrame]
    have w : searched.w_size = d.w_size := by rw [searchFrame]
    rw [b] at negative
    rw [w, strSearch]
    exact floor negative
  refine ⟨ys, ?_, quality, fun floor => companion freshBound (floorS floor), afterList⟩
  rcases size with ⟨none, pend, bits, start⟩ | ⟨len, valid, emptied, start, later, wb, body, eq, nullCost, storedCost⟩
  · exact Or.inl ⟨none, pend.trans pendS, bits.trans bitsS, start.trans startS⟩
  · have sourceEq : defaultStoredSource searched wb = defaultStoredSource d wb := by
      unfold defaultStoredSource; rw [startS]
    rw [bitsS] at eq storedCost
    rw [sourceEq] at nullCost storedCost
    rw [startS] at start
    have strS : searched.strstart = d.strstart := by rw [searchFrame]
    rw [strS] at later
    exact Or.inr ⟨len, valid, emptied, start, later, wb, body, eq, nullCost, storedCost⟩

end Zlib.Deflate.Engine.Proofs
