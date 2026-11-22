import ZlibF.Proof.«deflate.c.engine.fill-resume»
import ZlibF.Proof.«deflate.c.engine.slow-body»

/-! # Resumed input extends the same logical matching history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def extendInput (old : Nat → UInt8) (limit : Nat) (incoming : Array UInt8) (offset : Nat) : Nat → UInt8 :=
  fun i => if i < limit then old i else bfn incoming (offset + (i - limit))

theorem logical_history_extend {input extended : Nat → UInt8} {origin : Nat} {d : DeflateState}
    (history : LazyHistory input origin d)
    (agree : ∀ i, i < origin + fillEnd d → extended i = input i) : LazyHistory extended origin d := by
  refine ⟨history.1, ?_⟩
  intro large
  obtain ⟨start, available, room, distance, positive, bound, machine, earlier, bytes⟩ := history.2 large
  refine ⟨start, available, room, distance, positive, bound, machine, earlier, ?_⟩
  intro j hj
  have target : origin + d.strstart.toNat - 1 + j < origin + fillEnd d := by
    dsimp only [fillEnd]
    omega
  have source : origin + d.strstart.toNat - 1 - distance + j < origin + fillEnd d := by omega
  rw [agree _ source, agree _ target]
  exact bytes j hj

theorem copy_range_inside (destination source : Array UInt8) (offset sourceOffset count i : Nat)
    (fit : offset + count ≤ destination.size) (inside : offset ≤ i ∧ i < offset + count)
    (sourceFit : sourceOffset + (i - offset) < source.size) :
    bfn (copyRange destination source offset sourceOffset count) i = bfn source (sourceOffset + (i - offset)) := by
  unfold bfn
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    getElem?_copyRange destination source offset sourceOffset count i fit]
  simp [inside, sourceFit]

theorem resumed_input_view {d : DeflateState} {wa ia : Array UInt8} {input : Nat → UInt8}
    {origin io n : Nat} (fit : fillEnd d + n ≤ wa.size) (sourceFit : io + n ≤ ia.size)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) :
    ∀ i, i < fillEnd d + n →
      bfn (copyRange wa ia (fillEnd d) io n) i = extendInput input (origin + fillEnd d) ia io (origin + i) := by
  intro i hi
  by_cases before : i < fillEnd d
  · rw [copy_range_prefix wa ia (fillEnd d) io n fit i before, view i before]
    simp only [extendInput, show origin + i < origin + fillEnd d from by omega, ite_true]
  · rw [copy_range_inside wa ia (fillEnd d) io n i fit (by omega) (by omega)]
    simp only [extendInput, show ¬ origin + i < origin + fillEnd d from by omega, ite_false]
    congr 2
    omega

end Zlib.Deflate.Engine.Proofs
