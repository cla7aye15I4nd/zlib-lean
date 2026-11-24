import ZlibF.Proof.ControlFlowFrame
import ZlibF.Proof.«gzfs.borrow-stable»

/-! Actual loop composition for the external borrow observation. -/
namespace C.LibcBorrow

theorem StableM.cwhile_go {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, StableM (cond s)) (hb : ∀ s, StableM (body s)) (n : Nat) (s : σ) :
    StableM (cwhile.go cond body n s) := by
  induction n generalizing s with
  | zero => intro h v after hr; cases hr
  | succ n ih =>
    rw [cwhile.go]
    apply StableM.bind (hc s)
    rintro ⟨c, s'⟩
    apply StableM.ite
    · exact StableM.bind (hb s') (fun t => ih t)
    · exact StableM.pure _

theorem StableM.cwhile {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (hc : ∀ s, StableM (cond s)) (hb : ∀ s, StableM (body s)) (s : σ) :
    StableM (C.cwhile cond body s) := StableM.cwhile_go cond body hc hb fuel s

theorem StableM.cdoWhile_go {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, StableM (body s)) (hc : ∀ s, StableM (cond s)) (n : Nat) (s : σ) :
    StableM (cdoWhile.go body cond n s) := by
  induction n generalizing s with
  | zero => intro h v after hr; cases hr
  | succ n ih =>
    rw [cdoWhile.go]
    apply StableM.bind (hb s)
    intro s'
    apply StableM.bind (hc s')
    rintro ⟨c, t⟩
    exact StableM.ite _ (ih t) (StableM.pure _)

theorem StableM.cdoWhile {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (hb : ∀ s, StableM (body s)) (hc : ∀ s, StableM (cond s)) (s : σ) :
    StableM (C.cdoWhile body cond s) := StableM.cdoWhile_go body cond hb hc fuel s

theorem StableM.cforEverRet {σ ρ : Type} (body : σ → M (LoopStep σ ρ)) (s : σ) (k : σ → M ρ)
    (hb : ∀ s, StableM (body s)) (hk : ∀ s, StableM (k s)) : StableM (C.cforEverRet body s k) :=
  Preserves.cforEverRet (R := (fun a b => b.libcErrorBorrow = a.libcErrorBorrow)) (fun _ => rfl) (fun h₁ h₂ => h₂.trans h₁) body s k hb hk

theorem StableM.cwhileBrk {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ Empty))
    (s : σ) (hc : ∀ s, StableM (cond s)) (hb : ∀ s, StableM (body s)) :
    StableM (C.cwhileBrk cond body s) :=
  Preserves.cwhileBrk (R := (fun a b => b.libcErrorBorrow = a.libcErrorBorrow)) (fun _ => rfl) (fun h₁ h₂ => h₂.trans h₁) cond body s hc hb

theorem StableM.cdoWhileBrk {σ : Type} (body : σ → M (LoopStep σ Empty)) (cond : σ → M (Bool × σ))
    (s : σ) (hb : ∀ s, StableM (body s)) (hc : ∀ s, StableM (cond s)) :
    StableM (C.cdoWhileBrk body cond s) :=
  Preserves.cdoWhileBrk (R := (fun a b => b.libcErrorBorrow = a.libcErrorBorrow)) (fun _ => rfl) (fun h₁ h₂ => h₂.trans h₁) body cond s hb hc

#print axioms StableM.cwhile
#print axioms StableM.cdoWhile
end C.LibcBorrow
