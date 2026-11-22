import ZlibF.Proof.«deflate.c.engine.slow-boundary»
import ZlibF.Proof.«deflate.c.engine.fill-slide-empty»
import ZlibF.Spec.Functional.Checksums

/-! # Input refill preserves the same initialized slow boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An empty-input call preserves the boundary while doing any required
padding. Neither insert=0 nor an already padded window is assumed. -/
theorem fill_window_empty_slow_boundary {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : SlowBoundary h r ds z d input origin xs) (empty : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    ∃ after, fill_window (some (.tab ds)) h = .ok ((), after) ∧
      SlowBoundary after r ds z (paddedState d) input origin xs := by
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  let output := fillRange wa (paddingStart d) (paddingCount d) 0
  let after := paddedHeap h ds w d wa
  have goodA := padded_good boundary.good win get boundary.range
  have chainsA := padded_chains boundary.good boundary.chains win get boundary.range
  have loop := do_once (fill_body_no_input boundary.good empty noSlide) (fill_cond_break (some (.tab ds)) h)
  have pad := fill_high_water_complete boundary.good win get (window_writable boundary.good win) boundary.range
  have run : fill_window (some (.tab ds)) h = .ok ((), after) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, boundary.good.live.hs, loop]
    exact pad
  have distinct := window_pending_separate boundary.good win trees.base.pbuf
  have pendingA : (paddedState d).pending_buf = .ref (.blk b) 0 := trees.base.pbuf
  have dataA : after.bytes b = some buf := by
    simpa only [after, paddedHeap, setD_bytes, upd_ne _ _ _ _ distinct.symm] using trees.base.bytes
  have ledgerA : SymbolLedger buf (paddedState d) xs := ledger.keep rfl rfl rfl rfl
  have balanceA : BlockBalance (paddedState d) xs (deferredCredit (paddedState d)) := balance
  have symbolA := symbol_boundary_of_ledger goodA pendingA dataA ledgerA balanceA
  refine ⟨after, run, goodA, chainsA, boundary.range, boundary.history, boundary.deferred, symbolA,
    w, output, win, ?_, ?_, ?_⟩
  · simp [after, output, paddedHeap]
  · intro i bound
    rw [padded_prefix boundary.good win get boundary.range i bound]
    exact view i bound
  · intro large
    exact padded_form boundary.good win get boundary.range large (form large)

end Zlib.Deflate.Engine.Proofs
