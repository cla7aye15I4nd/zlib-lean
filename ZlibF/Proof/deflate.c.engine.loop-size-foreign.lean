import ZlibF.Proof.«deflate.c.engine.loop-size»
import ZlibF.Proof.«deflate.c.engine.body-size-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-composable»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-continuation-ready»

/-! # The size of the slow loop into a foreign output pointer

The twins of `deflate.c.engine.loop-size.lean` for a caller output pointer into another deflate state's `depth`
array.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of the complete loop** from a publication-ready strategy boundary with the
companion, at a 32 KiB window: there is a final strategy boundary, the loop's delivered bytes
`produced` and the held bytes there, plus the starting `base` and its block term, are at most the
starting held bytes plus the final `base'` and its block term; the companion holds there. -/
theorem foreign_slow_loop_run_size {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {final : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (bits : config.windowBits = 15)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (companion : SizeCompanion d xs)
    (run : cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h = .ok (final, after)) :
    ∃ used produced z' result extended nextOrigin base' ys,
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used produced ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧
      (final.ret = none → PublishReady result) ∧ SizeCompanion result ys ∧
      produced + heldBytes result + base + 5 * (base / 16383) ≤ heldBytes d + base' + 5 * (base' / 16383) := by
  let startEnd := origin + fillEnd d
  let Inv : LoopS → Heap → Prop := fun st heap =>
    ∃ currentZ currentD currentInput currentOrigin currentBase ys accepted produced,
      StrategyBoundary heap r ds currentZ currentD currentInput currentOrigin currentBase ys config ∧
      EndFrontier heap currentD ∧ StreamBuffers heap r ∧ StreamAccounting z currentZ accepted produced ∧
      currentOrigin + fillEnd currentD = startEnd + accepted ∧
      (currentZ.avail_in ≠ 0 → currentZ.next_in ≠ .null) ∧
      (st.ret = none → PublishReady currentD) ∧ SizeCompanion currentD ys ∧
      produced + heldBytes currentD + base + 5 * (base / 16383) ≤
        heldBytes d + currentBase + 5 * (currentBase / 16383)
  have step : ∀ st heap, Inv st heap → st.brk = false → st.ret = none →
      ∀ next middle, deflate_slow_body (some (.tab ds)) flush st heap = .ok (next, middle) → Inv next middle := by
    intro st heap inv _notBreak running next middle actual
    obtain ⟨currentZ, currentD, currentInput, currentOrigin, currentBase, ys, accepted, produced,
      state, endS, buffersS, accountS, endpointS, validS, readyS, companionS, sizeS⟩ := inv
    have pointerS : currentZ.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [accountS.2.2.2.2.2.1, pointer]
      rfl
    have publishS := readyS running
    obtain ⟨used, emitted, expected, other, nextZ, nextD, nextBase, nextYs, nextInput, nextOrigin,
      _pendingBefore, _written, _remaining, _blockBits, bodyRun, stateA, endA, buffersA, accountA,
      _lengthA, _agreesA, endpointA, _baseA, _returnsA, _continuesA, _lessA, _breakA, _reasonA,
      _pendingB, _bytesA, _pendingA, _wireA, _prefixA, _positionA⟩ :=
      default_foreign_slow_body_composable_prefix (offset := currentD.bi_valid.toInt.toNat) state endS buffersS positive pointerS
        memory wrap publishS validS rfl flush st
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actual))
    have readyA := default_foreign_slow_body_run_ready_phase state endS buffersS positive pointerS memory wrap publishS validS
      actual stateA.good.live.hs
    have window := boundary_window state bits
    obtain ⟨sizeA, companionA⟩ := foreign_slow_body_run_size_effects state endS buffersS positive pointerS memory wrap
      publishS validS window companionS actual stateA accountA endpointA
    exact ⟨nextZ, nextD, nextInput, nextOrigin, nextBase, nextYs, accepted + used, produced + emitted,
      stateA, endA, buffersA, stream_accounting_trans accountS accountA, by omega,
      input_valid_accounting_output validS accountA, readyA, companionA, by omega⟩
  have initial : Inv {} h :=
    ⟨z, d, input, origin, base, xs, 0, 0, boundary, frontier, buffers,
      stream_accounting_zero z, by simp [startEnd], inputValid, fun _ => publish, companion, by omega⟩
  have post := forever_run_invariant Inv (deflate_slow_body (some (.tab ds)) flush) step initial run
  obtain ⟨z', result, extended, nextOrigin, base', ys, used, produced,
    stateA, endA, buffersA, accountA, endpointA, _validA, readyA, companionA, sizeA⟩ := post
  exact ⟨used, produced, z', result, extended, nextOrigin, base', ys, stateA, endA, buffersA, accountA,
    endpointA, readyA, companionA, sizeA⟩

end Zlib.Deflate.Engine.Proofs
