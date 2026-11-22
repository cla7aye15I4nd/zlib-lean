import ZlibF.Proof.«deflate.c.engine.static-budget»
import ZlibF.Math.DeflateStreamBudget

/-! # Fixed-code cost measured against actual represented input bytes

The ledger is the real symbol buffer/frequency relation. The three-byte
match quality condition must still be derived over complete source loops
and histories. It is internal data, not a proposed public precondition.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Trees
open Zlib.Trees.Proofs (fixedLiteralWords fixedDistanceWords)
open Zlib.Trees.Proofs.Out (payloadSymBits dcodeN lcodeN codeBits natBits_length distance_payload_fields)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
/-- The translated distance-code table needs at most ten extra bits
for the distance accepted by the default short-match filter. -/
theorem near_distance_extra (d : Nat) (small : d < 4096) :
    extra_dbits_tab[dcodeN d]!.toInt.toNat ≤ 10 := by
  have table : ∀ i : Fin 288,
      extra_dbits_tab[dist_code_tab[i.val]!.toNat]!.toInt.toNat ≤ 10 := by decide +kernel
  by_cases low : d < 256
  · simpa only [dcodeN, low, ite_true] using table ⟨d, by omega⟩
  · simpa only [dcodeN, low, ite_false] using table ⟨256 + d / 128, by omega⟩

/-- Length-three and length-four fixed matches use twelve code bits
plus their actual distance extras. -/
theorem short_fixed_symbol_cost (dist lc : Nat) (nonzero : dist ≠ 0)
    (distance : dist ≤ 32768) (short : lc < 2) :
    (payloadSymBits fixedLiteralWords fixedDistanceWords (dist, lc)).length =
      12 + extra_dbits_tab[dcodeN (dist - 1)]!.toInt.toNat := by
  have dk := (distance_payload_fields (dist - 1) (by omega)).1
  have fixed := (Zlib.Trees.Proofs.fixed_distance_fits (dcodeN (dist - 1)) dk).2
  have cases : lc = 0 ∨ lc = 1 := by omega
  rcases cases with rfl | rfl <;>
    simp only [payloadSymBits, nonzero, ite_false, codeBits, natBits_length, List.length_append, fixed] <;>
    change 7 + 0 + 5 + _ = _ <;> omega

/-- A legal symbol passing the short-match quality rule has a fixed
wire cost controlled by the number of represented input bytes. -/
theorem filtered_fixed_cost (s : Symbol) (valid : s.Valid)
    (quality : s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    2 * (payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value)).length ≤
      13 * s.bytes + 5 := by
  by_cases literal : s.distance = 0
  · have bound := Zlib.Trees.Proofs.fixed_literal_fits s.value valid.2
    simp only [payloadSymBits, literal, ite_true, codeBits, natBits_length, Symbol.bytes]
    omega
  · by_cases shortest : s.value = 0
    · have near := near_distance_extra (s.distance - 1) (by have := quality literal shortest; omega)
      rw [short_fixed_symbol_cost s.distance s.value literal valid.1 (by omega)]
      simp only [Symbol.bytes, literal, ite_false, shortest]
      omega
    · by_cases next : s.value = 1
      · have fields := distance_payload_fields (s.distance - 1) (by have := valid.1; omega)
        rw [short_fixed_symbol_cost s.distance s.value literal valid.1 (by omega)]
        simp only [Symbol.bytes, literal, ite_false, next]
        omega
      · have bound := Zlib.Trees.Proofs.fixed_payload_symbol_length s.distance s.value valid.1 valid.2
        simp only [Symbol.bytes, literal, ite_false]
        omega

/-- The per-symbol byte estimate sums over a complete symbol list. -/
theorem filtered_static_cost_sum (xs : List Symbol)
    (valid : ∀ s ∈ xs, s.Valid)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    2 * ((xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
      (xs.map staticDistanceSymbolCost).sum) ≤ 13 * represented xs + 5 * xs.length := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih =>
    have head := filtered_fixed_cost s (valid s (by simp)) (quality s (by simp))
    rw [← static_symbol_cost s (valid s (by simp))] at head
    have tail := ih (fun t member => valid t (by simp [member]))
      (fun t member => quality t (by simp [member]))
    simp only [List.map_cons, List.sum_cons, represented, List.length_cons]
    omega

end Zlib.Deflate.Engine.Proofs
