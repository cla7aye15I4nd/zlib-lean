import ZlibF.Proof.«deflate.c.engine.fill-end-frontier»
import ZlibF.Proof.«deflate.c.engine.fill-comparison-room»

/-! # Every actual FINISH body preserves the initialized strategy boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Full actual refill supplies the same initialized boundary and the
stronger EOF frontier on one returned heap. -/
theorem fill_window_strategy_end_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (short : d.lookahead.toNat < 262) (wrap : config.wrap = 1)
    (buffers : StreamBuffers h r) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base xs config ∧ EndFrontier after result ∧
      StreamAccounting z z' used 0 ∧ StreamBuffers after r ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  obtain ⟨used, after, z', result, extended, nextOrigin, run, state, account, buffersA,
      startA, lookA, agreesA, stoppedA, frameA⟩ :=
    fill_window_strategy_boundary boundary short wrap buffers inputValid
  have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
  have endA := fill_window_run_end_frontier boundary.toPendingBoundary frontier short wrapD buffers inputValid run state.good.live.hs
  exact ⟨used, after, z', result, extended, nextOrigin, run, state, endA, account, buffersA,
    startA, lookA, agreesA, stoppedA, frameA⟩

/-- Actual FINISH refill stop tests either break at zero lookahead or
execute the proved search/decision suffix on the returned heap. -/
theorem slow_finish_body_after_fill {h filledHeap : Heap} {ds : Nat} {d filled : DeflateState}
    (live : h.dstates ds = some d) (filledLive : filledHeap.dstates ds = some filled)
    (short : d.lookahead.toNat < 262)
    (run : fill_window (some (.tab ds)) h = .ok ((), filledHeap)) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) Z_FINISH st h =
      if filled.lookahead == 0 then .ok ({ st with brk := true }, filledHeap)
      else slowSearchDecision (some (.tab ds)) Z_FINISH st filledHeap := by
  have small : d.lookahead < MIN_LOOKAHEAD_u := UInt32.lt_iff_toNat_lt.mpr short
  rw [slow_body_search_decision_source]
  simp only [bind_app, rdD_eq, live, small, ite_true, run, filledLive,
    show (Z_FINISH == Z_NO_FLUSH) = false from rfl, Bool.and_false, Bool.false_eq_true, ite_false]
  by_cases zero : (filled.lookahead == 0) = true <;> simp [zero, pure_app]

end Zlib.Deflate.Engine.Proofs
