import ZlibF.Spec.Functional.RoundTrip

/-! # The unsaturated `compressBound` sum

`unsaturatedBound` is the sum inside `compressBound`; the two agree as long as `compressBound`
does not saturate.
-/

namespace ZlibF.Spec.Public.Proofs
open ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Below the saturation point, `compressBound` is the unsaturated sum. -/
theorem compressBound_eq_unsaturated (m : Nat) (small : unsaturatedBound m < 18446744073709551616) :
    Api.compressBound m = unsaturatedBound m := by
  have unfolded : Api.compressBound m =
      if unsaturatedBound m ≥ 18446744073709551616 then 18446744073709551615 else unsaturatedBound m := by
    unfold Api.compressBound unsaturatedBound
    rfl
  rw [unfolded, ite_eq_right (by omega)]

end ZlibF.Spec.Public.Proofs
