import ZlibF.Runtime.ControlFlow

namespace C

/-- Every returning execution relates its initial and final heaps. -/
def Preserves (R : Heap → Heap → Prop) {α : Type} (m : M α) : Prop :=
  ∀ h v after, m h = .ok (v, after) → R h after

namespace Preserves
variable {R : Heap → Heap → Prop}
variable (refl : ∀ h, R h h) (trans : ∀ {a b c}, R a b → R b c → R a c)

include refl in
private theorem pure (v : α) : Preserves R (Pure.pure v) := by
  intro h x after run
  cases run
  exact refl _

include trans in
theorem bind {m : M α} {k : α → M β} (hm : Preserves R m) (hk : ∀ v, Preserves R (k v)) :
    Preserves R (m >>= k) := by
  intro h v after run
  rw [bind_app] at run
  cases action : m h with
  | error e => rw [action] at run; cases run
  | ok pair =>
    obtain ⟨x, mid⟩ := pair
    rw [action] at run
    exact trans (hm _ _ _ action) (hk x _ _ _ run)

private theorem ite (c : Prop) [Decidable c] {m n : M α}
    (left : Preserves R m) (right : Preserves R n) : Preserves R (if c then m else n) := by
  split <;> assumption

include refl trans in
theorem cforEverRet {σ ρ : Type} (body : σ → M (LoopStep σ ρ)) (s : σ) (k : σ → M ρ)
    (hb : ∀ s, Preserves R (body s)) (hk : ∀ s, Preserves R (k s)) : Preserves R (C.cforEverRet body s k) := by
  have go (n : Nat) (t : σ) : Preserves R (cforEver.go body n t) := by
    induction n generalizing t with
    | zero => intro h v after hr; cases hr
    | succ n ih =>
      rw [cforEver.go]
      apply bind (R := R) (fun x y => trans x y) (hb t)
      intro step
      cases step <;> first | exact ih _ | exact pure (R := R) refl _
  apply bind (R := R) (fun x y => trans x y) (go fuel s)
  intro result
  cases result with
  | error => exact pure (R := R) refl _
  | ok t => exact hk t

include refl trans in
theorem cwhileBrk {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ Empty))
    (s : σ) (hc : ∀ s, Preserves R (cond s)) (hb : ∀ s, Preserves R (body s)) :
    Preserves R (C.cwhileBrk cond body s) := by
  have go (n : Nat) (t : σ) : Preserves R (cwhileCtrl.go cond body n t) := by
    induction n generalizing t with
    | zero => intro h v after hr; cases hr
    | succ n ih =>
      rw [cwhileCtrl.go]
      apply bind (R := R) (fun x y => trans x y) (hc t)
      rintro ⟨c, u⟩
      apply ite
      · apply bind (R := R) (fun x y => trans x y) (hb u)
        intro step
        cases step <;> first | exact ih _ | exact pure (R := R) refl _
      · exact pure (R := R) refl _
  apply bind (R := R) (fun x y => trans x y) (go fuel s)
  rintro (x | t)
  · exact nomatch x
  · exact pure (R := R) refl _

include refl trans in
theorem cdoWhileBrk {σ : Type} (body : σ → M (LoopStep σ Empty)) (cond : σ → M (Bool × σ))
    (s : σ) (hb : ∀ s, Preserves R (body s)) (hc : ∀ s, Preserves R (cond s)) :
    Preserves R (C.cdoWhileBrk body cond s) := by
  have go (n : Nat) (t : σ) : Preserves R (cdoWhileCtrl.go body cond n t) := by
    induction n generalizing t with
    | zero => intro h v after hr; cases hr
    | succ n ih =>
      rw [cdoWhileCtrl.go]
      apply bind (R := R) (fun x y => trans x y) (hb t)
      intro step
      cases step with
      | next u | cont u =>
        apply bind (R := R) (fun x y => trans x y) (hc u)
        rintro ⟨c, v⟩
        exact ite _ (ih v) (pure (R := R) refl _)
      | brk => exact pure (R := R) refl _
      | ret => exact pure (R := R) refl _
  apply bind (R := R) (fun x y => trans x y) (go fuel s)
  rintro (x | t)
  · exact nomatch x
  · exact pure (R := R) refl _

end Preserves
end C
