import ZlibF.Runtime.ControlFlow

/-! Heap-monad and loop equations shared by the C-ABI correspondence proofs. -/
namespace ZlibF.Proof.StandaloneCAbi.Control
open C

theorem m_bind_app {α β : Type} (m : M α) (f : α → M β) (h : Heap) :
    (m >>= f) h = match m h with
      | .ok (a, h1) => f a h1
      | .error e => .error e := rfl

theorem m_pure_bind {α β : Type} (a : α) (f : α → M β) (h : Heap) :
    ((pure a : M α) >>= f) h = f a h := rfl

theorem m_bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) (h : Heap) :
    ((m >>= f) >>= g) h = (m >>= fun a => f a >>= g) h := by
  simp only [m_bind_app]
  cases m h <;> rfl

theorem m_pure_bind_eq {α β : Type} (a : α) (f : α → M β) :
    ((pure a : M α) >>= f) = f a := rfl

theorem m_bind_assoc_eq {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  funext h; exact m_bind_assoc m f g h

theorem m_bind_pure_eq {α : Type} (m : M α) : (m >>= pure) = m := by
  funext h; simp only [m_bind_app]
  cases m h with
  | error e => rfl
  | ok p => cases p; rfl

theorem ite_bind_eq {α β : Type} (c : Prop) [Decidable c] (t e : M α) (k : α → M β) :
    ((if c then t else e) >>= k) = (if c then t >>= k else e >>= k) := by
  split <;> rfl

theorem m_bind_congr {α β : Type} {m₁ m₂ : M α} {k₁ k₂ : α → M β} {h : Heap}
    (hm : m₁ h = m₂ h) (hk : ∀ a h₁, m₂ h = .ok (a, h₁) → k₁ a h₁ = k₂ a h₁) :
    (m₁ >>= k₁) h = (m₂ >>= k₂) h := by
  rw [m_bind_app, m_bind_app, hm]
  cases h₂ : m₂ h with
  | error e => rfl
  | ok p => exact hk p.1 p.2 h₂

theorem m_bind_ok {α₁ α₂ β : Type} {m₁ : M α₁} {m₂ : M α₂}
    {k₁ : α₁ → M β} {k₂ : α₂ → M β} {h : Heap} {res : β × Heap}
    (hok : (m₂ >>= k₂) h = .ok res)
    (hm : ∀ a₂ h₁, m₂ h = .ok (a₂, h₁) →
      ∃ a₁, m₁ h = .ok (a₁, h₁) ∧ (k₂ a₂ h₁ = .ok res → k₁ a₁ h₁ = .ok res)) :
    (m₁ >>= k₁) h = .ok res := by
  rw [m_bind_app] at hok ⊢
  cases h₂ : m₂ h with
  | error e => simp [h₂] at hok
  | ok p =>
    simp only [h₂] at hok
    rcases hm p.1 p.2 h₂ with ⟨a₁, h₁, hk⟩
    rw [h₁]
    exact hk hok

theorem m_bind_ok_same {α β : Type} {m₁ m₂ : M α}
    {k₁ k₂ : α → M β} {h : Heap} {res : β × Heap}
    (hm : m₁ h = m₂ h)
    (hok : (m₂ >>= k₂) h = .ok res)
    (hk : ∀ a h₁, m₂ h = .ok (a, h₁) → k₂ a h₁ = .ok res → k₁ a h₁ = .ok res) :
    (m₁ >>= k₁) h = .ok res :=
  m_bind_ok hok fun a h₁ h₂ => ⟨a, hm ▸ h₂, hk a h₁ h₂⟩

theorem cwhile_go_succ {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (n : Nat) (s : σ) (h : Heap) :
    C.cwhile.go cond body (n + 1) s h =
      match cond s h with
      | .error e => .error e
      | .ok ((false, s1), h1) => .ok (s1, h1)
      | .ok ((true, s1), h1) =>
        match body s1 h1 with
        | .error e => .error e
        | .ok (s2, h2) => C.cwhile.go cond body n s2 h2 := by
  rw [C.cwhile.go]; simp only [bind_app]
  rcases h1 : cond s h with e | ⟨⟨c, s1⟩, h1'⟩
  · rfl
  · cases c
    · simp
    · simp only [ite_true, bind_app]
      cases body s1 h1' <;> rfl

theorem cdoWhile_go_succ {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (n : Nat) (s : σ) (h : Heap) :
    C.cdoWhile.go body cond (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (s1, h1) =>
        match cond s1 h1 with
        | .error e => .error e
        | .ok ((false, s2), h2) => .ok (s2, h2)
        | .ok ((true, s2), h2) => C.cdoWhile.go body cond n s2 h2 := by
  rw [C.cdoWhile.go]; simp only [bind_app]
  rcases hb : body s h with e | ⟨sb, h1⟩
  · rfl
  · simp only
    rcases hc : cond sb h1 with e | ⟨⟨c, s2⟩, h2⟩
    · rfl
    · cases c <;> simp

end ZlibF.Proof.StandaloneCAbi.Control
