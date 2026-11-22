import Std

/-! # Arithmetic for a cumulative default compressor output budget

These lemmas do not assert a bound on translated deflate execution. The
actual block selection and history must establish the counted-block budget.
-/

namespace ZlibF.Math.DeflateBound
set_option autoImplicit false

/-- Five bytes per full default symbol block and eleven wrapper/final
bytes fit within the default bound formula's overhead. The producer of
this counted-block estimate remains an execution-level obligation. -/
theorem stored_blocks_to_default_budget (n : Nat) :
    5 * (n / 16383) + 11 ≤ n / 4096 + n / 16384 + n / 33554432 + 13 := by
  omega

/-- The same comparison including the uncompressed input length. -/
theorem counted_blocks_to_default_bound (n : Nat) :
    n + 5 * (n / 16383) + 11 ≤ n + n / 4096 + n / 16384 + n / 33554432 + 13 := by
  have overhead := stored_blocks_to_default_budget n
  omega

/-- From `2^28` bytes on, the counted-block budget is strictly below the default bound formula.
(Equality occurs below `2^25` only; the threshold `2^28` is where the comparison is linear.) -/
theorem counted_blocks_below_default_bound (n : Nat) (large : 268435456 ≤ n) :
    n + 5 * (n / 16383) + 11 < n + n / 4096 + n / 16384 + n / 33554432 + 13 := by
  omega

/-- A counted-block budget above `UINT_MAX` is strictly below the default bound formula. -/
theorem counted_blocks_below_default_bound_of_wide (n : Nat)
    (wide : 4294967295 < n + 5 * (n / 16383) + 11) :
    n + 5 * (n / 16383) + 11 < n + n / 4096 + n / 16384 + n / 33554432 + 13 :=
  counted_blocks_below_default_bound n (by omega)

/-- Sliding both source positions preserves the lazy candidate distance
in the actual unsigned machine arithmetic. -/
theorem shifted_short_distance (start position window : UInt32) :
    (start - window) - 1 - (position - window) = start - 1 - position := by
  simp only [UInt32.sub_eq_add_neg, UInt32.neg_add, UInt32.neg_neg]
  calc
    _ = (start + -1 + -position) + (window + -window) := by ac_rfl
    _ = _ := by rw [UInt32.add_right_neg, UInt32.add_zero]

/-- Advancing the cursor by one converts a fresh search distance to
the next lazy candidate distance, including unsigned wrap. -/
theorem advanced_short_distance (start position : UInt32) :
    (start + 1) - 1 - position = start - position := by
  rw [UInt32.add_sub_cancel]


end ZlibF.Math.DeflateBound
