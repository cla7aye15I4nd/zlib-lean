import ZlibF.Spec.Common.Inflate.InflateFastOrigin
import ZlibF.Spec.Safety.Inflate.FastOrigin
import ZlibF.Proof.«inffast.c.dist»

/-! Pulling a byte and dropping bits keep the origin equations, for `inffast.c.origin` and
`inffast.c.distance-origin-dodist`. -/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.Origin
open ZlibF.Spec

/-- Pulling the actual input byte preserves both origin equations. -/
theorem pull_preserves_origin : Goal.pull_preserves_origin := by
  intro e hold bits input used P available
  have byteBound : (e.IN.getD input 0).toNat + 1 ≤ 256 := by
    have := (e.IN.getD input 0).toNat_lt
    omega
  have normalized : hold + (e.IN.getD input 0).toNat * 2 ^ bits < 2 ^ (bits + 8) := by
    calc
      hold + (e.IN.getD input 0).toNat * 2 ^ bits <
          2 ^ bits + (e.IN.getD input 0).toNat * 2 ^ bits := Nat.add_lt_add_right P.normalized _
      _ = ((e.IN.getD input 0).toNat + 1) * 2 ^ bits := by rw [Nat.add_mul]; omega
      _ ≤ 256 * 2 ^ bits := Nat.mul_le_mul_right _ byteBound
      _ = 2 ^ (bits + 8) := by rw [Nat.pow_add, Nat.mul_comm]
  refine ⟨by have := P.inputLower; omega, by omega, normalized, ?_, ?_⟩
  · have := P.accounting
    have := P.inputLower
    omega
  · rw [Sg_pull e hold bits input P.normalized available]
    exact P.stream

/-- Dropping low bits consumes exactly that many original entry bits. -/
theorem drop_preserves_origin : Goal.drop_preserves_origin := by
  intro e hold bits input used count P available
  refine ⟨P.inputLower, P.inputUpper, ?_, ?_, ?_⟩
  · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos count)).mpr
    rw [← Nat.pow_add, Nat.sub_add_cancel available]
    exact P.normalized
  · have := P.accounting
    omega
  · rw [Sg_drop hold bits input count available, P.stream, List.drop_drop]

end Zlib.Inffast.Proofs
