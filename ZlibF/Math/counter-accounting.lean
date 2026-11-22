import Std

namespace ZlibF.Math.CounterAccounting
set_option autoImplicit false

/-- A bounded 32-bit remaining count gives an exact 64-bit difference. -/
theorem difference_cast (base remaining : UInt32) (bound : remaining.toNat ≤ base.toNat) :
    (base - remaining).toUInt64 + remaining.toUInt64 = base.toUInt64 := by
  have numeric : (base - remaining).toNat + remaining.toNat = base.toNat := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bound), Nat.sub_add_cancel bound]
  have words := congrArg UInt64.ofNat numeric
  simpa only [UInt64.ofNat_add, UInt64.ofNat_uInt32ToNat] using words

/-- Charging a produced prefix and rebasing to the remaining count
conserves the total-plus-base ledger, even when the 64-bit total wraps. -/
theorem charge_rebase (total : UInt64) (base remaining : UInt32)
    (bound : remaining.toNat ≤ base.toNat) :
    total + (base - remaining).toUInt64 + remaining.toUInt64 = total + base.toUInt64 := by
  rw [UInt64.add_assoc, difference_cast base remaining bound]

end ZlibF.Math.CounterAccounting
