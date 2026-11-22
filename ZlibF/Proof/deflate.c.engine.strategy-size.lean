import ZlibF.Proof.«deflate.c.engine.finish-size»
import ZlibF.Proof.«deflate.c.engine.finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.eof-tail»

/-! # The size of one `deflate_slow` call

A `deflate_slow` call with `Z_NO_FLUSH` or `Z_FINISH` from a publication-ready strategy boundary
either returns `need_more` from its loop, at a strategy boundary where the size ledger and its
companion hold, or (with `Z_FINISH`) breaks at the end of the input and flushes the final block,
which costs at most the uncovered bytes plus 5.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of a `deflate_slow` call.** -/
theorem slow_strategy_run_size {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {flush : Int32} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (bits : config.windowBits = 15)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (companion : SizeCompanion d xs) (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (ret, after)) :
    ∃ used produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      StreamAccounting z z' used produced ∧
      ((ret = need_more ∧ (flush = Z_FINISH → z'.avail_out = 0) ∧ ∃ extended nextOrigin base' ys,
          StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧
          SizeCompanion result ys ∧ nextOrigin + fillEnd result = origin + fillEnd d + used ∧
          produced + heldBytes result + base + 5 * (base / 16383) ≤
            heldBytes d + base' + 5 * (base' / 16383)) ∨
       (flush = Z_FINISH ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
          ((ret = finish_started ∧ z'.avail_out = 0) ∨ (ret = finish_done ∧ 0 < z'.avail_out.toNat)) ∧
          result.bi_valid.toInt = 0 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
          result.wrap = 1 ∧
          base ≤ origin + fillEnd d + used ∧
          produced + heldBytes result + base + 5 * (base / 16383) ≤
            heldBytes d + (origin + fillEnd d + used) + 5 * ((origin + fillEnd d + used) / 16383) + 5 ∧
          z'.avail_in = 0)) := by
  rw [deflate_slow_eof_tail_source, bind_app] at run
  cases loopRun : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h with
  | error e => simp only [loopRun] at run; cases run
  | ok pair =>
    obtain ⟨final, middle⟩ := pair
    simp only [loopRun] at run
    obtain ⟨used, produced, z1, d1, input1, origin1, base1, ys1, state1, end1, buffers1, account1,
        endpoint1, ready1, companion1, size1⟩ :=
      slow_loop_run_size boundary frontier buffers positive pointer memory wrap bits publish inputValid
        companion loopRun
    have stopped : (final.ret = some need_more ∧ (flush = Z_FINISH → z1.avail_out = 0)) ∨
        (flush = Z_FINISH ∧ final.ret = none ∧
        d1.lookahead = 0 ∧ z1.avail_in = 0) := by
      rcases clean with noFlush | finish
      · subst noFlush
        exact Or.inl ⟨slow_no_flush_loop_run_control boundary frontier buffers positive pointer memory wrap
          publish inputValid loopRun, fun f => absurd f (by decide)⟩
      · subst finish
        obtain ⟨_used, _produced, otherFinal, other, otherZ, otherD, _base', _ys, _extended, _nextOrigin,
            otherRun, otherState, _end, _buffers, _account, _agrees, _endpoint, _baseLe, stops, needOut,
            broke, _ready⟩ :=
          slow_finish_ready_loop boundary frontier buffers positive pointer memory wrap publish inputValid
        have pairs := Prod.mk.inj (Except.ok.inj (otherRun.symm.trans loopRun))
        obtain ⟨finals, heaps⟩ := pairs
        subst finals heaps
        have sameZ : otherZ = z1 := Option.some.inj (otherState.good.live.hz.symm.trans state1.good.live.hz)
        have sameD : otherD = d1 := Option.some.inj (otherState.good.live.hs.symm.trans state1.good.live.hs)
        subst sameZ sameD
        rcases stops with more | ⟨none, brk⟩
        · exact Or.inl ⟨more, fun _ => needOut more⟩
        · exact Or.inr ⟨rfl, none, (broke brk).1, (broke brk).2⟩
    rcases stopped with ⟨more, roomOut⟩ | ⟨finish, none, empty, drained⟩
    · rw [more] at run
      simp only [pure_app] at run
      obtain ⟨rets, heaps⟩ := Prod.mk.inj (Except.ok.inj run)
      subst heaps
      refine ⟨used, produced, z1, d1, state1.good.live.hz, state1.good.live.hs, account1,
        Or.inl ⟨rets.symm, roomOut, input1, origin1, base1, ys1, state1, companion1, endpoint1, size1⟩⟩
    · rw [none] at run
      simp only [] at run
      subst finish
      have publish1 := ready1 none
      have levelL : d1.level = config.level := congrArg EngineConfig.level state1.configuration
      have memoryL : d1.lit_bufsize = config.memory := congrArg EngineConfig.memory state1.configuration
      have wrapL : d1.wrap = config.wrap := congrArg EngineConfig.wrap state1.configuration
      have pointer1 : z1.next_out = .ref (.blk ob) (oo + produced) := by
        rw [account1.2.2.2.2.2.1, pointer]
        rfl
      obtain ⟨tailProduced, z2, d2, get2, state2, good2, buffers2, account2, shape, bits2, ready2, wrap2,
          covered, size2⟩ :=
        slow_eof_finish_size state1 end1 buffers1 empty (by rw [levelL]; exact positive) pointer1
          publish1.2.1 (by rw [memoryL]; exact memory) publish1.1 (wrapL.trans wrap)
          (boundary_window state1 bits) companion1 run
      have account := stream_accounting_trans account1 account2
      refine ⟨used + 0, produced + tailProduced, z2, d2, get2, state2, account, Or.inr ⟨rfl, good2, buffers2,
        shape, bits2, ready2, wrap2.trans (wrapL.trans wrap), ?_, ?_, ?_⟩⟩
      · have accounted := boundary.accounted
        have credit : 0 ≤ pendingCredit d := Nat.zero_le _
        have fill : d.strstart.toNat ≤ fillEnd d := by unfold fillEnd; omega
        omega
      · have grow : base1 / 16383 ≤ (origin + fillEnd d + used) / 16383 :=
          Nat.div_le_div_right (by omega)
        omega
      · have count := account2.2.2.1
        have drainedN : z1.avail_in.toNat = 0 := by rw [drained]; rfl
        apply UInt32.toNat_inj.mp
        change z2.avail_in.toNat = 0
        omega

end Zlib.Deflate.Engine.Proofs
