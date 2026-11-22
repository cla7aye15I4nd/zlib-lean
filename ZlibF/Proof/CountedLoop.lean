import ZlibF.Proof.HeapWP

namespace C
open Std.WP
open scoped HeapWP

/-- Follow a read-only loop's states for exactly `n` successful iterations.
The final false condition also consumes one unit of fuel. -/
theorem cwhile_steps_spec {σ : Type} {h : Heap} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (state : Nat → σ) (n : Nat) (bound : n < fuel)
    (test : ∀ j, j ≤ n → OkOn h (cond (state j)) (decide (j < n), state j))
    (step : ∀ j, j < n → OkOn h (body (state j)) (state (j + 1))) :
    ⦃ fun s => s = h ⦄ cwhile cond body (state 0) ⦃ fun x s => x = state n ∧ s = h ⦄ := by
  apply okOn_iff_triple.mp
  suffices ∃ x, OkOn h (cwhile cond body (state 0)) x ∧ x = state n by
    obtain ⟨_, run, rfl⟩ := this
    exact run
  refine cwhile_ok (fun k s => ∃ j, j + k = n ∧ s = state j) _ ?_ ?_
    (k := n) ⟨0, Nat.zero_add _, rfl⟩ bound
  · rintro k _ ⟨j, hj, rfl⟩
    exact ⟨_, _, by simpa [show j < n by omega] using test j (by omega),
      step j (by omega), j + 1, by omega, rfl⟩
  · rintro _ ⟨j, hj, rfl⟩
    obtain rfl : j = n := by omega
    exact ⟨_, by simpa using test j (Nat.le_refl _), rfl⟩

end C
