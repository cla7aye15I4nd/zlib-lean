import ZlibF.Zlib.«deflate.c»

/-! # The actual public rank expression is total on the protocol range -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate
set_option autoImplicit false

/-- Init and accepted calls keep last_flush in this range. The arithmetic
check in the actual entry is total throughout that range. -/
theorem public_rank_request_total (f : Int32) (lower : -2 ≤ f.toInt) (upper : f.toInt ≤ 5) :
    ∃ value, RANK f = pure value := by
  have values : f = -2 ∨ f = -1 ∨ f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 := by
    have : f.toInt = -2 ∨ f.toInt = -1 ∨ f.toInt = 0 ∨ f.toInt = 1 ∨
        f.toInt = 2 ∨ f.toInt = 3 ∨ f.toInt = 4 ∨ f.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact this
  rcases values with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl⟩

/-- On the protocol range, evaluating both ranks gives the same result and
heap as first testing the C short-circuit guard on available input. -/
theorem public_duplicate_guard_eq (available : UInt32) (flush previous : Int32)
    (requested : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5)
    (saved : -2 ≤ previous.toInt ∧ previous.toInt ≤ 5) :
    (do return available == 0 && (← RANK flush) ≤ (← RANK previous) && flush != Z_FINISH : M Bool) =
    (do if available == 0 then
          return (← RANK flush) ≤ (← RANK previous) && flush != Z_FINISH
        return false : M Bool) := by
  obtain ⟨_, hf⟩ := public_rank_request_total flush (by omega) requested.2
  obtain ⟨_, hp⟩ := public_rank_request_total previous saved.1 saved.2
  funext h
  by_cases empty : available = 0 <;> simp [empty, hf, hp, bind_app, pure_app]

/-- An arbitrary stored integer can fault in the eager guard even when the
patched C skips rank arithmetic because input is available. -/
example (h : Heap) :
    (do return (1 : UInt32) == 0 && (← RANK 0) ≤ (← RANK 2147483647) &&
        (0 : Int32) != Z_FINISH : M Bool) h = .error (.ub "signed int overflow") ∧
    (do if (1 : UInt32) == 0 then
          return (← RANK 0) ≤ (← RANK 2147483647) && (0 : Int32) != Z_FINISH
        return false : M Bool) h = .ok (false, h) := ⟨rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs
