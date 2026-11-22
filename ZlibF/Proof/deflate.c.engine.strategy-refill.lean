import ZlibF.Proof.«deflate.c.borrow-stable-private-search»
import ZlibF.Proof.«deflate.c.engine.strategy-boundary»
import ZlibF.Proof.«deflate.c.engine.slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.slow-caller-storage»
import ZlibF.Proof.«deflate.c.engine.loop-accounting»

/-! # Real refill and full ready decisions share the strategy boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Refill, pending insertion, sliding and padding retain configuration
and the publication phase. Exact input accounting transfers the condition
on remaining caller output to the same returned stream. -/
theorem fill_window_strategy_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (short : d.lookahead.toNat < 262) (wrap : config.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base xs config ∧
      StreamAccounting z z' used 0 ∧ StreamBuffers after r ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  have wrapEq : d.wrap = config.wrap := congrArg EngineConfig.wrap boundary.configuration
  obtain ⟨used, after, z', result, extended, nextOrigin, run, state, account, buffersA, _storage,
    startA, lookA, _wrapA, _originA, agreesA, stoppedA, frameA⟩ :=
    fill_window_content_buffers boundary.toContentBoundary short (wrapEq.trans wrap) buffers inputValid
  have configA := ConfigFrame.fill frameA
  have lowA : result.bi_valid.toInt < 8 := by rw [frameA]; exact boundary.bits
  have strictA : result.sym_next.toNat < result.sym_end.toNat := by rw [frameA]; exact boundary.strict
  have phaseA : 0 < z'.avail_out.toNat → PublishReady result := by
    intro space
    have count := account.2.2.2.1
    exact PublishReady.fill (boundary.resume (by omega)) frameA
  exact ⟨used, after, z', result, extended, nextOrigin, run,
    ⟨state, Eq.trans configA boundary.configuration, boundary.clear.fill frameA, lowA, strictA, phaseA⟩,
    account, buffersA, startA, lookA, agreesA, stoppedA, frameA⟩

end Zlib.Deflate.Engine.Proofs
