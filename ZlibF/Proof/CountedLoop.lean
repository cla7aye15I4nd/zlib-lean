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

/-- Follow a heap-mutating `cwhile` loop across `n` iterations using an indexed loop invariant.
The final false condition consumes one additional unit of fuel. -/
theorem cwhile_inv_spec {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : Nat → σ → Heap → Prop) (s₀ : σ) (n : Nat) (bound : n < fuel)
    (test : ∀ j s h, j ≤ n → Inv j s h → cond s h = .ok ((decide (j < n), s), h))
    (step : ∀ j s h, j < n → Inv j s h → ∃ s' h', body s h = .ok (s', h') ∧ Inv (j + 1) s' h') :
    ⦃ fun h => Inv 0 s₀ h ⦄ cwhile cond body s₀ ⦃ fun x h => Inv n x h ⦄ := by
  refine ⟨fun h₀ hInv0 => ?_⟩
  obtain ⟨s', h', hrun, hPost⟩ := cwhile_run (fun k s h => ∃ j, j + k = n ∧ Inv j s h) (Inv n)
    (fun k s h ⟨j, hj, hInv⟩ => by
      have hc := test j s h (by omega) hInv
      simp only [show decide (j < n) = true by simp [show j < n by omega]] at hc
      obtain ⟨s', h', hb, hInv'⟩ := step j s h (by omega) hInv
      exact ⟨s, h, s', h', hc, hb, j + 1, by omega, hInv'⟩)
    (fun s h ⟨j, hj, hInv⟩ => by
      have hjn : j = n := by omega
      have hc := test n s h (Nat.le_refl n) (hjn ▸ hInv)
      simp only [Nat.lt_irrefl, decide_false] at hc
      exact ⟨s, h, hc, hjn ▸ hInv⟩)
    ⟨0, Nat.zero_add n, hInv0⟩ bound
  rw [wp_run, hrun]
  exact hPost

/-- Follow a heap-mutating `cdoWhile` loop across `n + 1` body executions using an indexed invariant. -/
theorem cdoWhile_inv_spec {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (Inv : Nat → σ → Heap → Prop) (s₀ : σ) (n : Nat) (bound : n < fuel)
    (step : ∀ j s h, j ≤ n → Inv j s h → ∃ s' h', body s h = .ok (s', h') ∧ Inv (j + 1) s' h')
    (test : ∀ j s h, j ≤ n → Inv (j + 1) s h → cond s h = .ok ((decide (j < n), s), h)) :
    ⦃ fun h => Inv 0 s₀ h ⦄ cdoWhile body cond s₀ ⦃ fun x h => Inv (n + 1) x h ⦄ := by
  refine ⟨fun h₀ hInv0 => ?_⟩
  obtain ⟨s', h', hrun, hPost⟩ := cdoWhile_run (fun k s h => ∃ j, j + k = n ∧ Inv j s h) (Inv (n + 1))
    (fun k s h ⟨j, hj, hInv⟩ => by
      obtain ⟨s1, h1, hb, hInv1⟩ := step j s h (by omega) hInv
      have hc := test j s1 h1 (by omega) hInv1
      simp only [show decide (j < n) = true by simp [show j < n by omega]] at hc
      exact ⟨s1, h1, s1, h1, hb, hc, j + 1, by omega, hInv1⟩)
    (fun s h ⟨j, hj, hInv⟩ => by
      have hjn : j = n := by omega
      obtain ⟨s1, h1, hb, hInv1⟩ := step n s h (Nat.le_refl n) (hjn ▸ hInv)
      have hc := test n s1 h1 (Nat.le_refl n) hInv1
      simp only [Nat.lt_irrefl, decide_false] at hc
      exact ⟨s1, h1, s1, h1, hb, hc, hInv1⟩)
    ⟨0, Nat.zero_add n, hInv0⟩ bound
  rw [wp_run, hrun]
  exact hPost

/-- Follow a read-only `cdoWhile` loop for `n + 1` body executions on a fixed heap. -/
theorem cdoWhile_steps_spec {σ : Type} {h : Heap} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (state : Nat → σ) (n : Nat) (bound : n < fuel)
    (step : ∀ j, j ≤ n → OkOn h (body (state j)) (state (j + 1)))
    (test : ∀ j, j ≤ n → OkOn h (cond (state (j + 1))) (decide (j < n), state (j + 1))) :
    ⦃ fun s => s = h ⦄ cdoWhile body cond (state 0) ⦃ fun x s => x = state (n + 1) ∧ s = h ⦄ := by
  have hloop := cdoWhile_inv_spec (body := body) (cond := cond)
    (fun j s hs => s = state j ∧ hs = h) (state 0) n bound
    (fun j s hs hj ⟨hs_eq, hh_eq⟩ => by
      rw [hs_eq, hh_eq]
      exact ⟨state (j + 1), h, step j hj, rfl, rfl⟩)
    (fun j s hs hj ⟨hs_eq, hh_eq⟩ => by
      rw [hs_eq, hh_eq]
      exact test j hj)
  exact ⟨fun hs hh => hloop.le_wp hs ⟨rfl, hh⟩⟩

end C