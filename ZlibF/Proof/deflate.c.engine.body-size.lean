import ZlibF.Proof.«deflate.c.engine.decision-size»
import ZlibF.Proof.«deflate.c.engine.body-prefix»

/-! # The size of one `deflate_slow` iteration

A `deflate_slow_body` run at a publication-ready strategy boundary refills the window (no output;
a slide keeps `base`), returns early, or searches and decides. Its emitted bytes plus `base` plus
5 per 16383 bytes of `base` do not grow, and it keeps the companion clauses: the match quality of
the boundary's symbols, the lazy candidate bound and the slide floor.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The size ledger's companion at a strategy boundary: the boundary's symbols keep the level-6
match quality, a three-byte lazy candidate is within `TOO_FAR`, and a negative block start comes
with a position of at least `w_size - 262` (only a slide makes it negative). -/
def SizeCompanion (d : DeflateState) (xs : List Symbol) : Prop :=
  (∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) ∧
  (d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR) ∧
  (d.block_start.toInt < 0 → d.w_size.toNat - 262 ≤ d.strstart.toNat)

/-- The emitted size of a state, in bytes: pending bytes and held bits rounded up. -/
def heldBytes (d : DeflateState) : Nat := d.pending.toNat + (d.bi_valid.toInt.toNat + 7) / 8

/-- The list of a boundary after a decision: empty after a flush, the decision's list otherwise. -/
theorem after_list_quality {h : Heap} {ds : Nat} {d : DeflateState} {ys zs : List Symbol}
    (afterList : d.sym_next = 0 ∨ SymbolBoundary h ds d ys) (target : SymbolBoundary h ds d zs)
    (quality : ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∀ s ∈ zs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096 := by
  rcases afterList with empty | boundary
  · obtain ⟨_, _, _, ledger, _⟩ := target
    have count := ledger.count
    rw [empty] at count
    have none : zs.length = 0 := by
      simp only [UInt32.toNat_zero] at count
      omega
    rw [List.length_eq_zero_iff] at none
    subst none
    intro s member
    cases member
  · rw [← symbol_boundary_unique boundary target]
    exact quality

/-- **One established search and decision from a ready boundary** as a step of the size ledger,
with the companion kept. The after boundary is any strategy boundary of the resulting state with
the same origin. -/
theorem slow_search_decision_step_size {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base base' produced : Nat}
    {z returned : ZStream} {d d' : DeflateState} {xs ys : List Symbol} {input extended : Nat → UInt8}
    {config : EngineConfig} {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (ready : PublishReady d) (window : d.w_size.toNat = 32768)
    (companion : SizeCompanion d xs)
    (run : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after))
    (stateA : StrategyBoundary after r ds returned d' extended origin base' ys config)
    (account : StreamAccounting z returned 0 produced) :
    produced + heldBytes d' + base + 5 * (base / 16383) ≤ heldBytes d + base' + 5 * (base' / 16383) ∧
      SizeCompanion d' ys := by
  obtain ⟨listQ, matchQ, floor⟩ := companion
  obtain ⟨zs, size, quality, keep, afterList⟩ :=
    slow_search_decision_run_size_effects boundary frontier buffers lookahead room positive pointer memory ready
      run stateA.good.live.hz stateA.good.live.hs account listQ matchQ
  have at0 := content_base_eq boundary.toContentBoundary
  have at1 := content_base_eq stateA.toContentBoundary
  have pending : d.pending = 0 := ready.1
  have slid : d.block_start.toInt < 0 → 32506 ≤ d.strstart.toNat := by
    intro negative
    have := floor negative
    omega
  have step := decision_size_step size pending quality slid at0 at1
  obtain ⟨matchQ', floor'⟩ := keep floor
  refine ⟨?_, after_list_quality afterList stateA.symbols quality, matchQ', floor'⟩
  unfold heldBytes
  omega

/-- **One established `deflate_slow_body` iteration** from a publication-ready strategy boundary, as
a step of the size ledger, with the companion kept. The after boundary is any strategy boundary of
the resulting state whose origin satisfies the iteration's endpoint equation. -/
theorem slow_body_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base nextOrigin base' used produced : Nat}
    {z returned : ZStream} {d d' : DeflateState} {xs ys : List Symbol} {input extended : Nat → UInt8}
    {config : EngineConfig} {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) (window : d.w_size.toNat = 32768)
    (companion : SizeCompanion d xs)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (stateA : StrategyBoundary after r ds returned d' extended nextOrigin base' ys config)
    (accountA : StreamAccounting z returned used produced)
    (endpointA : nextOrigin + fillEnd d' = origin + fillEnd d + used) :
    produced + heldBytes d' + base + 5 * (base / 16383) ≤ heldBytes d + base' + 5 * (base' / 16383) ∧
      SizeCompanion d' ys := by
  have actualWrap : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨usedF, filledHeap, filledZ, filled, extendedF, originF, fillRun, filledState, filledFrontier,
        fillAccount, filledBuffers, startF, lookF, _agreesF, stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have fillComp := fill_run_companion boundary.toPendingBoundary short actualWrap buffers inputValid fillRun
      filledState.good.live.hs
    obtain ⟨listQ, matchQ, floor⟩ := companion
    have companionF : SizeCompanion filled xs := ⟨listQ, fillComp.1 matchQ, fillComp.2 floor⟩
    have pointerEq : filledZ.next_out = z.next_out := by rw [fillAccount.2.2.2.2.2.1, advance_zero]
    have pointerF : filledZ.next_out = .ref (.blk ob) oo := pointerEq.trans pointer
    have endpointF : originF + fillEnd filled = origin + fillEnd d + usedF := by
      dsimp only [fillEnd]
      omega
    have readyF : PublishReady filled := publish.fill frameF
    have heldF : heldBytes filled = heldBytes d := by
      unfold heldBytes
      rw [frameF]
    have windowF : filled.w_size.toNat = 32768 := by rw [frameF]; exact window
    have baseF := content_base_eq filledState.toContentBoundary
    have baseD := content_base_eq boundary.toContentBoundary
    have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
    -- a run that stops right after the refill
    have stopped : ∀ value, deflate_slow_body (some (.tab ds)) flush st h = .ok (value, filledHeap) →
        produced + heldBytes d' + base + 5 * (base / 16383) ≤ heldBytes d + base' + 5 * (base' / 16383) ∧
          SizeCompanion d' ys := by
      intro value stopRun
      have heaps : filledHeap = after := (Prod.mk.inj (Except.ok.inj (stopRun.symm.trans run))).2
      subst heaps
      have sameZ : filledZ = returned := Option.some.inj (filledState.good.live.hz.symm.trans stateA.good.live.hz)
      subst sameZ
      have sameD : filled = d' := Option.some.inj (filledState.good.live.hs.symm.trans stateA.good.live.hs)
      subst sameD
      have counts := stream_accounting_counts_unique accountA fillAccount
      have origins : nextOrigin = originF := by omega
      subst origins
      have baseA := content_base_eq stateA.toContentBoundary
      have bases : base' = base := by omega
      subst bases
      have lists := symbol_boundary_unique filledState.toContentBoundary.symbols stateA.toContentBoundary.symbols
      subst lists
      refine ⟨?_, companionF⟩
      rw [heldF]
      omega
    by_cases wait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = true
    · apply stopped { st with ret := some need_more }
      rw [slow_body_search_decision_source]
      simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
        fillRun, filledState.good.live.hs, wait, ite_true, pure_app]
    · have notWait : (filled.lookahead < MIN_LOOKAHEAD_u && flush == Z_NO_FLUSH) = false :=
        Bool.eq_false_iff.mpr wait
      by_cases empty : filled.lookahead = 0
      · apply stopped { st with brk := true }
        rw [slow_body_search_decision_source]
        simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
          fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false]
        simp only [empty, beq_self_eq_true, ite_true, pure_app]
      · have nonzero : 1 ≤ filled.lookahead.toNat := by
          have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
          omega
        have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short actualWrap buffers
          inputValid fillRun filledState.good.live.hs
        have decisionRun : slowSearchDecision (some (.tab ds)) flush st filledHeap = .ok (next, after) := by
          have source := run
          rw [slow_body_search_decision_source] at source
          simp only [bind_app, rdD_eq, boundary.good.live.hs, small, ite_true,
            fillRun, filledState.good.live.hs, notWait, Bool.false_eq_true, ite_false] at source
          have nonEmpty : (filled.lookahead == 0) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact empty
          simpa only [nonEmpty, Bool.false_eq_true, ite_false] using source
        obtain ⟨producedS, nextS, afterS, zS, resultS, baseS, ysS, suffixRun, stateS, _endS, _buffersS,
            suffixAccount, _progress, _less, endpointS, _rest⟩ :=
          slow_search_decision_ready_boundary filledState filledFrontier filledBuffers nonzero (fun _ => roomF)
            positive pointerF memory readyF flush st
        have heaps : afterS = after := (Prod.mk.inj (Except.ok.inj (suffixRun.symm.trans decisionRun))).2
        subst heaps
        have sameZ : zS = returned := Option.some.inj (stateS.good.live.hz.symm.trans stateA.good.live.hz)
        subst sameZ
        have sameD : resultS = d' := Option.some.inj (stateS.good.live.hs.symm.trans stateA.good.live.hs)
        subst sameD
        have total := stream_accounting_trans fillAccount suffixAccount
        have counts := stream_accounting_counts_unique accountA total
        have produce : produced = producedS := by omega
        subst produce
        have origins : nextOrigin = originF := by omega
        subst origins
        have stateA' : StrategyBoundary afterS r ds zS resultS extended nextOrigin base' ys config := stateA
        have baseStep := slow_search_decision_step_size filledState filledFrontier filledBuffers nonzero
          (fun _ => roomF) positive pointerF memory readyF windowF companionF decisionRun stateA suffixAccount
        rw [heldF] at baseStep
        exact baseStep
  · have ready : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    have decisionRun : slowSearchDecision (some (.tab ds)) flush st h = .ok (next, after) :=
      (slow_ready_body_source boundary.good.live.hs ready flush st).symm.trans run
    obtain ⟨producedS, nextS, afterS, zS, resultS, baseS, ysS, suffixRun, stateS, _endS, _buffersS,
        suffixAccount, _progress, _less, endpointS, _rest⟩ :=
      slow_search_decision_ready_boundary boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish flush st
    have heaps : afterS = after := (Prod.mk.inj (Except.ok.inj (suffixRun.symm.trans decisionRun))).2
    subst heaps
    have sameZ : zS = returned := Option.some.inj (stateS.good.live.hz.symm.trans stateA.good.live.hz)
    subst sameZ
    have sameD : resultS = d' := Option.some.inj (stateS.good.live.hs.symm.trans stateA.good.live.hs)
    subst sameD
    have counts := stream_accounting_counts_unique accountA suffixAccount
    have produce : produced = producedS := counts.2
    subst produce
    have origins : nextOrigin = origin := by omega
    subst origins
    exact slow_search_decision_step_size boundary frontier buffers (by omega) (fun _ => room) positive pointer
      memory publish window companion decisionRun stateA suffixAccount

end Zlib.Deflate.Engine.Proofs
