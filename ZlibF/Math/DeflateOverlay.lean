import ZlibF.Math.HuffmanFibPush

/-!
# Prefix accounting for the shared pending/symbol buffer

Each consumed symbol releases three bytes. Its encoded bit cost may exceed
24, so a whole-block excess budget bounds every prefix. The coefficient
6257/1000 and header bound 2283 are the targets of the reference FibPush
argument. This file proves their arithmetic consequences; it does not
assume a callee contract or claim that a translated block establishes them.
-/

namespace Zlib.Trees.Overlay
set_option autoImplicit false

/-- Total positive excess over the 24 bits released by one symbol. -/
def bitExcess (costs : List Nat) : Nat :=
  (costs.map (fun bits => bits - 24)).sum

/-- A prefix costs no more than 24 bits per consumed symbol plus the
whole block's excess. No bound on an individual symbol is needed. -/
theorem prefix_bits_le (costs : List Nat) :
    ∀ k, (costs.take k).sum ≤ 24 * k + bitExcess costs := by
  induction costs with
  | nil => intro k; simp [bitExcess]
  | cons bits rest ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have bound := ih k
      simp only [List.take_succ_cons, List.sum_cons]
      simp only [bitExcess, List.map_cons, List.sum_cons]
      rw [Nat.mul_succ]
      unfold bitExcess at bound
      omega

end Zlib.Trees.Overlay
