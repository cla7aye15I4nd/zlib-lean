import ZlibF.Proof.«deflate.c.engine.decision-counters»
import ZlibF.Proof.«deflate.c.engine.flush-macro-size»
import ZlibF.Proof.«deflate.c.engine.short-match-budget»

/-! # The size of a strategy decision

A `deflate_slow` decision records one symbol. When that fills the symbol buffer, it flushes the
block: the block then has exactly `16383` symbols, and its tag and body are bounded as in
`flush_default_cost`. Otherwise it emits nothing: no byte is delivered and the pending bytes and
held bits are unchanged. These are the decision steps of the size ledger.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A `UInt32` position written to `block_start` reads back as itself. -/
theorem position_block_start (x : UInt32) : x.toUInt64.toInt64.toInt = (x.toNat : Int) := by
  rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
  · simp
  · have bound := UInt32.toNat_lt x
    simp
    omega

/-- What a decision emits: nothing (the block start unchanged), or one full block of the symbols
`ys` (16383 of them), after which the block starts `represented ys` bytes later. -/
def DecisionSize (d d' : DeflateState) (produced : Nat) (ys : List Symbol) : Prop :=
  (produced = 0 ∧ d'.pending = d.pending ∧ d'.bi_valid = d.bi_valid ∧ d'.block_start = d.block_start) ∨
  (ys.length = 16383 ∧ (∀ s ∈ ys, s.Valid) ∧ d'.sym_next = 0 ∧
    d'.block_start.toInt = d.block_start.toInt + represented ys ∧
    (d.strstart.toNat : Int) ≤ d'.block_start.toInt ∧
    ∃ (w : Nat) (body : List Bool),
    produced + d'.pending.toNat + (d'.bi_valid.toInt.toNat + 7) / 8 =
      (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ∧
    (defaultStoredSource d w = .null → 3 + body.length ≤ 8 * ((fixedCost ys + 10) / 8)) ∧
    (defaultStoredSource d w ≠ .null →
      (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + represented ys + 5))

/-- What a decision keeps of the size ledger's two state clauses, given the fresh search match's
`TOO_FAR` bound: the lazy candidate's bound and the slide floor. -/
def DecisionCompanion (d d' : DeflateState) : Prop :=
  (d.match_length = 3 → d.strstart - d.match_start ≤ TOO_FAR) →
  (d.block_start.toInt < 0 → d.w_size.toNat - 262 ≤ d.strstart.toNat) →
  (d'.match_length = 3 → d'.strstart - 1 - d'.match_start ≤ TOO_FAR) ∧
  (d'.block_start.toInt < 0 → d'.w_size.toNat - 262 ≤ d'.strstart.toNat)

theorem slow_match_advance_length {h after : Heap} {ds : Nat} {mi hh v : UInt32} {e : DeflateState}
    (run : slowMatchAdvance (some (.tab ds)) mi hh h = .ok (v, after))
    (state : after.dstates ds = some e) : e.match_length = MIN_MATCH_u - 1 := by
  unfold slowMatchAdvance at run
  simp only [bind_app] at run
  cases h1 : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead - (d.prev_length - 1), prev_length := d.prev_length - 2 }) h with
  | error err => simp [h1] at run
  | ok p1 =>
    rcases p1 with ⟨u1, g1⟩
    simp only [h1] at run
    cases h2 : cdoWhile (slowMatchBody (some (.tab ds)) mi) (slowMatchCond (some (.tab ds))) hh g1 with
    | error err => simp [h2] at run
    | ok p2 =>
      rcases p2 with ⟨x, g2⟩
      simp only [h2] at run
      cases hg : g2.dstates ds with
      | none => simp [wrD_eq, hg] at run
      | some e0 =>
        simp only [wrD_eq, hg, pure_app] at run
        have := (Prod.mk.inj (Except.ok.inj run)).2
        subst this
        simp [setD] at state
        rw [← state]

/-- After an emitted match the lazy candidate is reset: `match_length = MIN_MATCH - 1`. -/
theorem slow_match_emit_length {h after : Heap} {ds : Nat} {hh : UInt32} {v : Bool × UInt32} {e : DeflateState}
    (run : slowMatchEmit (some (.tab ds)) hh h = .ok (v, after))
    (state : after.dstates ds = some e) : e.match_length = MIN_MATCH_u - 1 := by
  unfold slowMatchEmit at run
  simp only [bind_app] at run
  cases h1 : ldDeflateState (some (.tab ds)) h with
  | error err => simp [h1] at run
  | ok p1 =>
    rcases p1 with ⟨d, g1⟩
    simp only [h1] at run
    cases h2 : tally_dist (some (.tab ds)) (d.strstart - 1 - d.prev_match) (d.prev_length - MIN_MATCH_u) g1 with
    | error err => simp [h2] at run
    | ok p2 =>
      rcases p2 with ⟨b, g2⟩
      simp only [h2] at run
      cases h3 : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hh g2 with
      | error err => simp [h3] at run
      | ok p3 =>
        rcases p3 with ⟨y, g3⟩
        simp only [h3, pure_app] at run
        have := (Prod.mk.inj (Except.ok.inj run)).2
        subst this
        exact slow_match_advance_length h3 state

theorem block_start_position_nonneg (x : UInt32) : ¬ (x.toUInt64.toInt64.toInt < 0) := by
  rw [position_block_start]
  omega

/-- Both selected-match paths: the size of the decision. The block of a flush is the symbols so
far and the match. -/
theorem slow_match_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z returned : ZStream} {d d' : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
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
      flush_nonfinal_end_boundary emittedBoundary emittedFrontier emittedBuffers
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
      flush_control_run_size_effects emittedBoundary emittedBuffers
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
theorem slow_literal_full_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z returned : ZStream} {d d' : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
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
    flush_macro_size goodT treesT buffersT positive pointer ready.2.1 memory ready.1
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

/-- A decision that keeps the stream and the record frame emits nothing. -/
theorem quiet_decision_size {z z' : ZStream} {d d' : DeflateState} {produced : Nat} (ys : List Symbol)
    (stream : z' = z) (frame : SlowRecordFrame d d') (account : StreamAccounting z z' 0 produced) :
    DecisionSize d d' produced ys := by
  subst stream
  have none : produced = 0 := by
    have output := account.2.2.2.1
    omega
  refine Or.inl ⟨none, ?_, ?_, ?_⟩ <;> rw [frame]

/-- **The size of every strategy decision**: selected match, literal and defer. -/
theorem slow_decision_run_size_effects {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z returned : ZStream} {d d' : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
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
    obtain ⟨size, companion, after_list⟩ := slow_match_run_size_effects cut buffers selected strict positive pointer memory
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
      · obtain ⟨size, companion, emptied⟩ := slow_literal_full_run_size_effects cut buffers lookahead branch available full
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
theorem slow_search_decision_run_size_effects {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z returned : ZStream} {d d' : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush : Int32} {st next : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
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
  obtain ⟨ys, size, shape, companion, afterList⟩ := slow_decision_run_size_effects cut searchedBuffers positiveS strictS
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

theorem length_le_represented (xs : List Symbol) : xs.length ≤ represented xs := by
  induction xs with
  | nil => simp [represented]
  | cons s rest ih =>
    simp only [represented, List.length_cons, Symbol.bytes]
    split <;> omega

/-- **One decision as a step of the size ledger.** The emitted bytes (delivered, pending, held bits
rounded up) grow by at most the block bytes the block start advances, plus 5 for every multiple of
16383 that `base` passes. The inputs: the decision's size, no pending byte before it, the match
quality of a flushed block, and `SlidFloor` (a block start below 0 means `strstart ≥ 32506`). -/
theorem decision_size_step {d d' : DeflateState} {produced : Nat} {ys : List Symbol} {origin base base' : Nat}
    (size : DecisionSize d d' produced ys) (pending : d.pending = 0)
    (quality : ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (slid : d.block_start.toInt < 0 → 32506 ≤ d.strstart.toNat)
    (at0 : (base : Int) = origin + d.block_start.toInt) (at1 : (base' : Int) = origin + d'.block_start.toInt) :
    produced + d'.pending.toNat + (d'.bi_valid.toInt.toNat + 7) / 8 + base + 5 * (base / 16383) ≤
      d.pending.toNat + (d.bi_valid.toInt.toNat + 7) / 8 + base' + 5 * (base' / 16383) := by
  rcases size with ⟨none, pend, bits, start⟩ | ⟨len, valid, _emptied, start, later, w, body, eq, nullCost, storedCost⟩
  · rw [pend, bits]
    have same : base = base' := by
      rw [start] at at1
      omega
    subst same
    omega
  · have pend0 : d.pending.toNat = 0 := by rw [pending]; rfl
    have rep := length_le_represented ys
    have advance : base' = base + represented ys := by omega
    have step : base / 16383 + 1 ≤ (base + represented ys) / 16383 := by omega
    by_cases present : defaultStoredSource d w = .null
    · have negative : d.block_start.toInt < 0 := by
        unfold defaultStoredSource at present
        by_cases nonneg : 0 ≤ d.block_start.toInt
        · rw [ite_eq_left nonneg] at present
          cases present
        · omega
      have floor := slid negative
      have large : 32506 ≤ represented ys := by omega
      have cheap := slid_fixed_cost valid quality (by omega) large
      have bound := nullCost present
      rw [advance]
      omega
    · have bound := storedCost present
      rw [advance]
      omega

/-- **A packed symbol list is determined by its bytes.** Two lists of valid symbols packed at the
same place in the same buffer, of the same length, are equal: a distance (at most 32768) is its two
low bytes, a value (below 256) its byte. -/
theorem packed_symbols_unique {buf : Array UInt8} {b : Nat} {xs ys : List Symbol}
    (px : PackedSymbols buf b xs) (py : PackedSymbols buf b ys)
    (vx : ∀ s ∈ xs, s.Valid) (vy : ∀ s ∈ ys, s.Valid) (len : xs.length = ys.length) : xs = ys := by
  apply List.ext_getElem len
  intro i hi hj
  obtain ⟨a1, a2, a3⟩ := px i xs[i] (List.getElem?_eq_getElem hi)
  obtain ⟨b1, b2, b3⟩ := py i ys[i] (List.getElem?_eq_getElem hj)
  have vxi := vx _ (List.getElem_mem hi)
  have vyi := vy _ (List.getElem_mem hj)
  rw [a1] at b1
  rw [a2] at b2
  rw [a3] at b3
  have low := congrArg UInt8.toNat b1
  have high := congrArg UInt8.toNat b2
  have value := congrArg UInt8.toNat b3
  simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt16.toNat_ofNat] at low high value
  unfold Symbol.Valid at vxi vyi
  cases hx : xs[i] with
  | mk dx vx' =>
    cases hy : ys[i] with
    | mk dy vy' =>
      rw [hx] at low high value vxi
      rw [hy] at low high value vyi
      simp only at low high value vxi vyi
      simp [Nat.shiftRight_eq_div_pow] at low high value
      have distance : dx = dy := by omega
      have val : vx' = vy' := by omega
      rw [distance, val]

/-- **At a content boundary, `base` is where the block starts.** `BlockBalance` and the accounting
equation give `base = origin + block_start` (in integers; `block_start` is negative after a slide
while `origin` has grown by the same amount). -/
theorem content_base_eq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {input : Nat → UInt8} {origin base : Nat} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) :
    (base : Int) = origin + d.block_start.toInt := by
  obtain ⟨_pb, _buf, _trees, _ledger, balance⟩ := boundary.symbols
  have accounted := boundary.accounted
  unfold BlockBalance at balance
  rw [deferred_credit_nat] at balance
  omega

/-- **Two ledgers of one state hold the same symbols.** The pending buffer is the state's, and a
packed list of valid symbols of a given length is determined by its bytes. -/
theorem symbol_boundary_unique {h : Heap} {ds : Nat} {d : DeflateState} {xs ys : List Symbol}
    (one : SymbolBoundary h ds d xs) (two : SymbolBoundary h ds d ys) : xs = ys := by
  obtain ⟨b1, buf1, t1, l1, _⟩ := one
  obtain ⟨b2, buf2, t2, l2, _⟩ := two
  have pointers := t1.base.pbuf.symm.trans t2.base.pbuf
  simp only [Ptr.ref.injEq, BRef.blk.injEq] at pointers
  obtain ⟨blocks, _⟩ := pointers
  subst blocks
  have arrays : buf1 = buf2 := Option.some.inj (t1.base.bytes.symm.trans t2.base.bytes)
  subst arrays
  have c1 := l1.count
  have c2 := l2.count
  exact packed_symbols_unique l1.packed l2.packed l1.valid l2.valid (by omega)

end Zlib.Deflate.Engine.Proofs
