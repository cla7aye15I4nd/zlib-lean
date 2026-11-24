import ZlibF.Runtime.ControlFlow

/-! Simulation rules for the two representations of the table builder's loop locals. -/
namespace Zlib.Inftrees.TableABI
open C

/-- Every returning execution has the same heap and corresponding locals. -/
def Sim {α β : Type} (embed : α → β) (old : M α) (actual : M β) : Prop :=
  ∀ {h s H}, old h = .ok (s, H) → actual h = .ok (embed s, H)

theorem bind_assoc_table {α β γ : Type} (m : M α) (k : α → M β) (f : β → M γ) :
    ((m >>= k) >>= f) = (m >>= fun x => k x >>= f) := by
  funext H
  simp only [bind_app]
  cases m H <;> rfl

/-- A loop with a pure guard can carry extra locals unchanged. -/
theorem while_sim {α β : Type} (embed : α → β) (test : α → Bool)
    (c₀ : α → M (Bool × α)) (c₁ : β → M (Bool × β))
    (old : α → M α) (actual : β → M β)
    (guards : ∀ x h, c₀ x h = .ok ((test x, x), h) ∧ c₁ (embed x) h = .ok ((test x, embed x), h))
    (step : ∀ x, Sim embed (old x) (actual (embed x))) (x : α) :
    Sim embed (cwhile c₀ old x) (cwhile c₁ actual (embed x)) := by
  unfold cwhile
  generalize fuel = n
  induction n generalizing x with
  | zero => intro h s H run; cases run
  | succ n ih =>
    intro h s H run
    rw [cwhile.go, bind_ok (guards x h).1] at run
    rw [cwhile.go, bind_ok (guards x h).2]
    cases g : test x <;> simp only [g, Bool.false_eq_true, ↓reduceIte] at run ⊢
    · cases run; rfl
    · rw [bind_app] at run
      cases body : old x h with
      | error fault => simp [body] at run
      | ok pair =>
        obtain ⟨next, mid⟩ := pair
        simp only [body] at run
        rw [bind_ok (step x body)]
        exact ih next run

theorem doWhile_sim {α β : Type} (embed : α → β) (test : α → Bool)
    (old : α → M α) (actual : β → M β) (c₀ : α → M (Bool × α)) (c₁ : β → M (Bool × β))
    (guards : ∀ x h, c₀ x h = .ok ((test x, x), h) ∧ c₁ (embed x) h = .ok ((test x, embed x), h))
    (step : ∀ x, Sim embed (old x) (actual (embed x))) (x : α) :
    Sim embed (cdoWhile old c₀ x) (cdoWhile actual c₁ (embed x)) := by
  unfold cdoWhile
  generalize fuel = n
  induction n generalizing x with
  | zero => intro h s H run; cases run
  | succ n ih =>
    intro h s H run
    rw [cdoWhile.go, bind_app] at run
    cases read : old x h with
    | error fault => simp [read] at run
    | ok p =>
      obtain ⟨v, mid⟩ := p
      simp only [read] at run
      rw [bind_ok (guards v mid).1] at run
      rw [cdoWhile.go, bind_ok (step x read), bind_ok (guards v mid).2]
      cases t : test v <;> simp only [t, Bool.false_eq_true, ↓reduceIte] at run ⊢
      · cases run; rfl
      · exact ih v run

end Zlib.Inftrees.TableABI
