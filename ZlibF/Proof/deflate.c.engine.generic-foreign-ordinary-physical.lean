import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-final-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finish-ready-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-ready-step»
import ZlibF.Proof.«deflate.c.engine.ordinary-call-full-storage»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_no_flush_ready_loop_run_control {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h = .ok (final, after)) :
    final.ret = some need_more := by
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys offset,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ currentZ.next_out = .ref (.dstate_depth owner) offset ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ st.brk = false ∧ (st.ret = none ∨ st.ret = some need_more)
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _brk running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, offset,
      state, endS, buffersS, pointerS, validS, readyS, brkS, _retS⟩ := inv
    obtain ⟨used, produced, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      bodyRun, stateA, endA, buffersA, accountA, _agrees, _endpoint, _base,
      brkA, retA, readyA, _less, _reason⟩ :=
      default_foreign_slow_no_flush_ready_step state endS buffersS positive pointerS memory wrap (readyS running) validS st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have pointerA : nextZ.next_out = .ref (.dstate_depth owner) (offset + produced) := by
      rw [accountA.2.2.2.2.2.1, pointerS]
      rfl
    have retNext : expected.ret = none ∨ expected.ret = some need_more := by
      rcases retA with same | returned
      · exact Or.inl (same.trans running)
      · exact Or.inr returned
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, offset + produced,
      stateA, endA, buffersA, pointerA, input_valid_accounting_output validS accountA,
      readyA,brkA.trans brkS, retNext⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, oo, boundary, frontier, buffers, pointer, inputValid,
      fun _ => publish,rfl,Or.inl rfl⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) step initial run
  obtain ⟨_z, _d, _input, _origin, _base, _ys, _offset, _state, _end, _buffers, _pointer,
    _valid, _ready,brkA,retA⟩ := post
  have stopped := forever_run_stopped run
  rcases retA with running | returned
  · simp only [brkA, running, Option.isSome_none, Bool.or_self, Bool.false_eq_true] at stopped
  · exact returned

end Zlib.Deflate.Engine.Proofs
