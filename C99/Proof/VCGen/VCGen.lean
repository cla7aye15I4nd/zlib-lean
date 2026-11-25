import C99.Proof.VCGen.AnnAST

/-!
# Verified Functional CPS VCGen (`C99.Proof.VCGen.VCGen`)

Pure functional verification condition generator for C99 (`vcExprL`, `vcExprR`,
`vcExprAgg`, `vcExprDiscard`, `vcStmt`, `vcStmtSafe`, `vcFn`, `vcFnSafe`)
inspired by Verus VIR-to-SMT passification, proved 100% sound inside Lean's
kernel against `C99.Sem.WPTerm` and `WPSafe` (`SafeUntil` + conditional
`WPTerm`). Zero `MetaM` stepping tactics, zero axioms, 100% domain-agnostic.
-/

namespace C99.Proof.VCGen

open C99 C99.Sem C99.Proof

/-! ## Basic Memory / Cast Helpers -/

theorem writePlace_rval_cast {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v cv : Val} {vty : CTy}
    (ht : ValScalarTyped ty cv)
    (hc : Sem.castVal m ty v = some cv)
    (hw : Sem.writeVal m b off ty cv = some m') :
    Sem.writePlace tags m b off ty (.rval v vty) = some (.rval cv ty, m') := by
  unfold Sem.writePlace
  unfold ValScalarTyped at ht
  cases hu : ty.unqual <;> simp [hu] at ht
  case int | enumTy | ptr | fnPtr =>
    simp [hc, hw, bind, Option.bind, pure, Pure.pure]
  case vaList =>
    subst ht
    unfold Sem.castVal at hc
    simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, Bool.false_eq_true, ↓reduceIte] at hc
    cases v with
    | vaList valid =>
      cases valid
      · simp at hc
      · simp at hc; simp [hw, bind, Option.bind, pure, Pure.pure]
    | _ => simp at hc

/-! ## Conditional Termination & Safety (`SafeUntil`, `WPSafe`, `WPRules`) -/

def runStateIsReturned : RunState → Bool
  | .returned _ _ _ => true
  | _ => false

def runStateReadBudgetIsSome : RunState → Bool
  | .running _ _ _ _ os _ => os.readBudget.isSome
  | .returned _ _ os => os.readBudget.isSome
  | .ub => false

private theorem not_isUB_of_stepDet_some {prog : Prog} {cfg : PointerConfig}
    {s : RunState} {d : Sem.DetStep} (hd : Sem.stepDet prog cfg s = some d) :
    ¬ s.isUB := by
  cases s with
  | ub => cases hd
  | returned _ _ _ => cases hd
  | running _ _ _ _ _ _ => exact Bool.false_ne_true

private theorem not_returned_of_stepDet_some {prog : Prog} {cfg : PointerConfig}
    {s : RunState} {d : Sem.DetStep} (hd : Sem.stepDet prog cfg s = some d)
    {v : Val} {m : Mem} {os : OSState} (hret : s = .returned v m os) : False := by
  subst hret
  cases hd

/-- Coinductive weakest precondition guaranteeing absence of UB, postcondition `Q`
at any `.returned` state, and allowing premature stopping at states satisfying `R`. -/
def SafeUntil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (R : RunState → Prop) (s0 : RunState) : Prop :=
  ∃ Inv : RunState → Prop, Inv s0 ∧
    ∀ s, Inv s →
      R s ∨
      ((∀ v m os, s = .returned v m os → Q v m os) ∧
       ¬ s.isUB ∧
       ∀ s', Sem.Step prog cfg ext s s' → Inv s')

theorem SafeUntil.cases {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    (h : SafeUntil prog cfg ext Q R s) :
    R s ∨
      ((∀ v m os, s = .returned v m os → Q v m os) ∧
       ¬ s.isUB ∧
       ∀ s', Sem.Step prog cfg ext s s' → SafeUntil prog cfg ext Q R s') := by
  rcases h with ⟨Inv, hs, hinv⟩
  rcases hinv s hs with hr | ⟨hq, hnot, hrun⟩
  · exact Or.inl hr
  · exact Or.inr ⟨hq, hnot, fun s' hst => ⟨Inv, hrun s' hst, hinv⟩⟩

theorem SafeUntil.done {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState} (hr : R s) :
    SafeUntil prog cfg ext Q R s :=
  ⟨fun u => u = s, rfl, fun _ hu => Or.inl (hu ▸ hr)⟩

theorem SafeUntil.returned {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {v : Val} {m : Mem} {os : OSState}
    (hq : Q v m os) :
    SafeUntil prog cfg ext Q R (.returned v m os) :=
  ⟨fun u => u = .returned v m os, rfl, fun u hu => by
    subst hu
    exact Or.inr ⟨fun _ _ _ h => by cases h; exact hq, Bool.false_ne_true,
      fun _ hst => False.elim (step_not_returned hst)⟩⟩

theorem SafeUntil.step {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    (hret : ∀ v m os, s = .returned v m os → Q v m os)
    (hnot : ¬ s.isUB)
    (hnext : ∀ s', Sem.Step prog cfg ext s s' → SafeUntil prog cfg ext Q R s') :
    SafeUntil prog cfg ext Q R s := by
  refine ⟨fun u => u = s ∨ SafeUntil prog cfg ext Q R u, Or.inl rfl, fun u hu => ?_⟩
  rcases hu with rfl | hsu
  · exact Or.inr ⟨hret, hnot, fun s' hst => Or.inr (hnext s' hst)⟩
  · rcases SafeUntil.cases hsu with hr | ⟨hq, hnot', hrun⟩
    · exact Or.inl hr
    · exact Or.inr ⟨hq, hnot', fun s' hst => Or.inr (hrun s' hst)⟩

theorem SafeUntil.star_inv {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s s' : RunState}
    (h : SafeUntil prog cfg ext Q (fun _ => False) s)
    (hstar : Sem.Star (Sem.Step prog cfg ext) s s') :
    SafeUntil prog cfg ext Q (fun _ => False) s' := by
  induction hstar with
  | refl => exact h
  | @tail y z _ hstep ih =>
    rcases SafeUntil.cases ih with hfalse | ⟨_, _, hrun⟩
    · exact False.elim hfalse
    · exact hrun z hstep

theorem SafeUntil.safe {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    (h : SafeUntil prog cfg ext Q (fun _ => False) s) :
    Sem.Safe prog cfg ext s := by
  intro s' hstar
  rcases SafeUntil.cases (h.star_inv hstar) with hf | ⟨_, hnot, _⟩
  · exact False.elim hf
  · exact hnot

theorem SafeUntil.post {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState} {v : Val} {m : Mem} {os : OSState}
    (h : SafeUntil prog cfg ext Q (fun _ => False) s)
    (hstar : Sem.Star (Sem.Step prog cfg ext) s (.returned v m os)) :
    Q v m os := by
  rcases SafeUntil.cases (h.star_inv hstar) with hf | ⟨hq, _, _⟩
  · exact False.elim hf
  · exact hq v m os rfl

theorem SafeUntil.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q1 Q2 : Val → Mem → OSState → Prop} {R1 R2 : RunState → Prop} {s : RunState}
    (hmQ : ∀ v m os, Q1 v m os → Q2 v m os)
    (hmR : ∀ u, R1 u → R2 u)
    (h : SafeUntil prog cfg ext Q1 R1 s) :
    SafeUntil prog cfg ext Q2 R2 s := by
  rcases h with ⟨Inv, hs, hinv⟩
  refine ⟨Inv, hs, fun u hu => ?_⟩
  rcases hinv u hu with hr | ⟨hq, hnot, hrun⟩
  · exact Or.inl (hmR u hr)
  · exact Or.inr ⟨fun v m os heq => hmQ v m os (hq v m os heq), hnot, hrun⟩

theorem SafeUntil.bind {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R1 R2 : RunState → Prop} {s0 : RunState}
    (h1 : SafeUntil prog cfg ext Q R1 s0)
    (h2 : ∀ s, R1 s → SafeUntil prog cfg ext Q R2 s) :
    SafeUntil prog cfg ext Q R2 s0 := by
  refine ⟨fun u => SafeUntil prog cfg ext Q R1 u ∨ SafeUntil prog cfg ext Q R2 u, Or.inl h1, fun u hu => ?_⟩
  have from_r2 : ∀ w, SafeUntil prog cfg ext Q R2 w →
      R2 w ∨ ((∀ v m os, w = .returned v m os → Q v m os) ∧ ¬ w.isUB ∧
        ∀ s', Sem.Step prog cfg ext w s' →
          SafeUntil prog cfg ext Q R1 s' ∨ SafeUntil prog cfg ext Q R2 s') := by
    intro w hw
    rcases SafeUntil.cases hw with hr | ⟨hq, hnot, hrun⟩
    · exact Or.inl hr
    · exact Or.inr ⟨hq, hnot, fun s' hst => Or.inr (hrun s' hst)⟩
  rcases hu with hu1 | hu2
  · rcases SafeUntil.cases hu1 with hr1 | ⟨hq, hnot, hrun⟩
    · exact from_r2 u (h2 u hr1)
    · exact Or.inr ⟨hq, hnot, fun s' hst => Or.inl (hrun s' hst)⟩
  · exact from_r2 u hu2

/-- One-step safety invariant for unbounded loops in `SafeUntil`. -/
def SafeNext (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (R : RunState → Prop) (s : RunState) : Prop :=
  (∀ v m os, s = .returned v m os → Q v m os) ∧ ¬ s.isUB ∧
    ∀ s', Sem.Step prog cfg ext s s' → SafeUntil prog cfg ext Q R s'

theorem SafeNext.to_safeUntil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    (h : SafeNext prog cfg ext Q R s) : SafeUntil prog cfg ext Q R s :=
  SafeUntil.step h.1 h.2.1 h.2.2

theorem SafeUntil.loop_wf_unbounded {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P R : RunState → Prop} {s0 : RunState}
    (hp : P s0)
    (hstep : ∀ s, P s → SafeNext prog cfg ext Q (fun u => P u ∨ R u) s) :
    SafeUntil prog cfg ext Q R s0 := by
  refine ⟨fun u => P u ∨ SafeUntil prog cfg ext Q (fun w => P w ∨ R w) u, Or.inl hp, fun u hu => ?_⟩
  have from_p : ∀ s, P s →
      (∀ v m os, s = .returned v m os → Q v m os) ∧ ¬ s.isUB ∧
        ∀ s', Sem.Step prog cfg ext s s' →
          P s' ∨ SafeUntil prog cfg ext Q (fun w => P w ∨ R w) s' := by
    intro s hps
    obtain ⟨hret, hnot, hnx⟩ := hstep s hps
    exact ⟨hret, hnot, fun s' hst => Or.inr (hnx s' hst)⟩
  rcases hu with hpu | hsu
  · exact Or.inr (from_p u hpu)
  · rcases SafeUntil.cases hsu with (hpu | hru) | ⟨hq, hnot, hrun⟩
    · exact Or.inr (from_p u hpu)
    · exact Or.inl hru
    · exact Or.inr ⟨hq, hnot, fun s' hst => Or.inr (hrun s' hst)⟩

theorem SafeNext.of_det_state {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s s' : RunState}
    (hd : Sem.stepDet prog cfg s = some (.next s'))
    (hw : SafeUntil prog cfg ext Q R s') :
    SafeNext prog cfg ext Q R s := by
  refine ⟨fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret),
    not_isUB_of_stepDet_some hd, fun s'' hstep => ?_⟩
  cases hstep with
  | det hd' =>
    rw [hd] at hd'
    cases hd'
    exact hw
  | det_ub hd' =>
    rw [hd] at hd'
    cases hd'
  | strLit hd' | localDecl hd' | localDecl_ub hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'
    cases hd'

theorem SafeUntil.of_det_state {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s s' : RunState}
    (hd : Sem.stepDet prog cfg s = some (.next s'))
    (hw : SafeUntil prog cfg ext Q R s') :
    SafeUntil prog cfg ext Q R s :=
  (SafeNext.of_det_state hd hw).to_safeUntil

theorem SafeUntil.of_det {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop}
    {ctrl ctrl' : Control} {env env' : Env} {blks blks' : List BlockId}
    {m m' : Mem} {os os' : OSState} {k k' : Cont}
    (hd : Sem.stepDet prog cfg (.running ctrl env blks m os k) =
      some (.next (.running ctrl' env' blks' m' os' k')))
    (hw : SafeUntil prog cfg ext Q R (.running ctrl' env' blks' m' os' k')) :
    SafeUntil prog cfg ext Q R (.running ctrl env blks m os k) :=
  SafeUntil.of_det_state hd hw

theorem SafeNext.of_exprPure {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop}
    {es es' : ExprState} {ctx : ExprCtx} {mods mods' : ModSet}
    {env : Env} {blks : List BlockId} {m m' : Mem} {os : OSState} {k : Cont}
    (h : Sem.stepExprPure prog cfg env m mods es = some (es', m', mods'))
    (hw : SafeUntil prog cfg ext Q R (.running (.expr es' ctx mods') env blks m' os k)) :
    SafeNext prog cfg ext Q R (.running (.expr es ctx mods) env blks m os k) :=
  SafeNext.of_det_state (stepDet_exprPure h) hw

theorem SafeUntil.of_exprPure {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop}
    {es es' : ExprState} {ctx : ExprCtx} {mods mods' : ModSet}
    {env : Env} {blks : List BlockId} {m m' : Mem} {os : OSState} {k : Cont}
    (h : Sem.stepExprPure prog cfg env m mods es = some (es', m', mods'))
    (hw : SafeUntil prog cfg ext Q R (.running (.expr es' ctx mods') env blks m' os k)) :
    SafeUntil prog cfg ext Q R (.running (.expr es ctx mods) env blks m os k) :=
  (SafeNext.of_exprPure h hw).to_safeUntil

theorem SafeNext.of_strLit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {str : String} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocStr str fs ctx mods env blks m os k))
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (hw : ∀ (base : UInt64) (bid : BlockId) (m' : Mem),
      m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') →
      SafeUntil prog cfg ext Q R
        (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods)
          env blks m' os k)) :
    SafeNext prog cfg ext Q R s := by
  let alloc0 := m.alloc (str.utf8ByteSize + 1) 1 .ro .global 0
    (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)
  refine ⟨fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret),
    not_isUB_of_stepDet_some hd, fun s' hstep => ?_⟩
  cases hstep with
  | strLit hd' _ halloc' =>
    rw [hd] at hd'; cases hd'; exact hw _ _ _ halloc'
  | det hd' | det_ub hd' | localDecl hd' | localDecl_ub hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem SafeUntil.of_strLit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {str : String} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocStr str fs ctx mods env blks m os k))
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (hw : ∀ (base : UInt64) (bid : BlockId) (m' : Mem),
      m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') →
      SafeUntil prog cfg ext Q R
        (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods)
          env blks m' os k)) :
    SafeUntil prog cfg ext Q R s :=
  (SafeNext.of_strLit hd hsz hw).to_safeUntil

theorem SafeUntil.of_localDecl_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {d : VarDecl} {rest : List VarDecl} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocLocal d none rest env blks m os k))
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      SafeUntil prog cfg ext Q R
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os k)) :
    SafeUntil prog cfg ext Q R s := by
  let hba0 : (0 : UInt64).toNat % max 1 (alignofTy prog.tags d.ty) = 0 := Nat.zero_mod _
  let alloc0 := m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
    .rw .stack 0 (fun _ => .undef) hsz hal hba0
  refine SafeUntil.step (fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret))
    (not_isUB_of_stepDet_some hd) fun s' hstep => ?_
  cases hstep with
  | localDecl hd' _ _ hba' halloc' hwr' =>
    rw [hd] at hd'; cases hd'; cases hwr'; exact hw _ _ _ hba' halloc'
  | localDecl_ub hd' hbad =>
    rw [hd] at hd'; cases hd'
    exact False.elim (hbad 0 alloc0.2 alloc0.1 alloc0.2 hsz hal hba0 rfl rfl)
  | det hd' | det_ub hd' | strLit hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem SafeNext.of_localDecl_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {d : VarDecl} {rest : List VarDecl} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocLocal d none rest env blks m os k))
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      SafeUntil prog cfg ext Q R
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os k)) :
    SafeNext prog cfg ext Q R s := by
  let hba0 : (0 : UInt64).toNat % max 1 (alignofTy prog.tags d.ty) = 0 := Nat.zero_mod _
  let alloc0 := m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
    .rw .stack 0 (fun _ => .undef) hsz hal hba0
  refine ⟨fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret),
    not_isUB_of_stepDet_some hd, fun s' hstep => ?_⟩
  cases hstep with
  | localDecl hd' _ _ hba' halloc' hwr' =>
    rw [hd] at hd'; cases hd'; cases hwr'; exact hw _ _ _ hba' halloc'
  | localDecl_ub hd' hbad =>
    rw [hd] at hd'; cases hd'
    exact False.elim (hbad 0 alloc0.2 alloc0.1 alloc0.2 hsz hal hba0 rfl rfl)
  | det hd' | det_ub hd' | strLit hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem SafeNext.of_localDecl_some {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {d : VarDecl} {rv : ExprRes} {rest : List VarDecl} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocLocal d (some rv) rest env blks m os k))
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      ∃ r m2, Sem.writePlace prog.tags m1 bid 0 d.ty.stripConst rv = some (r, m2) ∧
        SafeUntil prog cfg ext Q R
          (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os k)) :
    SafeNext prog cfg ext Q R s := by
  let hba0 : (0 : UInt64).toNat % max 1 (alignofTy prog.tags d.ty) = 0 := Nat.zero_mod _
  let alloc0 := m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
    .rw .stack 0 (fun _ => .undef) hsz hal hba0
  obtain ⟨r0, m20, hwr0, _⟩ := hw 0 alloc0.1 alloc0.2 hba0 rfl
  refine ⟨fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret),
    not_isUB_of_stepDet_some hd, fun s' hstep => ?_⟩
  cases hstep with
  | localDecl hd' _ _ hba' halloc' hwr' =>
    rw [hd] at hd'; cases hd'
    obtain ⟨r', hr'⟩ := hwr'
    obtain ⟨r, m2, hwr, hnext⟩ := hw _ _ _ hba' halloc'
    rw [hwr] at hr'; cases hr'; exact hnext
  | localDecl_ub hd' hbad =>
    rw [hd] at hd'; cases hd'
    exact False.elim (hbad 0 alloc0.2 alloc0.1 m20 hsz hal hba0 rfl ⟨r0, hwr0⟩)
  | det hd' | det_ub hd' | strLit hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem SafeUntil.of_localDecl_some {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {d : VarDecl} {rv : ExprRes} {rest : List VarDecl} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocLocal d (some rv) rest env blks m os k))
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      ∃ r m2, Sem.writePlace prog.tags m1 bid 0 d.ty.stripConst rv = some (r, m2) ∧
        SafeUntil prog cfg ext Q R
          (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os k)) :
    SafeUntil prog cfg ext Q R s := by
  let hba0 : (0 : UInt64).toNat % max 1 (alignofTy prog.tags d.ty) = 0 := Nat.zero_mod _
  let alloc0 := m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
    .rw .stack 0 (fun _ => .undef) hsz hal hba0
  obtain ⟨r0, m20, hwr0, _⟩ := hw 0 alloc0.1 alloc0.2 hba0 rfl
  refine SafeUntil.step (fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret))
    (not_isUB_of_stepDet_some hd) fun s' hstep => ?_
  cases hstep with
  | localDecl hd' _ _ hba' halloc' hwr' =>
    rw [hd] at hd'; cases hd'
    obtain ⟨r', hr'⟩ := hwr'
    obtain ⟨r, m2, hwr, hnext⟩ := hw _ _ _ hba' halloc'
    rw [hwr] at hr'; cases hr'; exact hnext
  | localDecl_ub hd' hbad =>
    rw [hd] at hd'; cases hd'
    exact False.elim (hbad 0 alloc0.2 alloc0.1 m20 hsz hal hba0 rfl ⟨r0, hwr0⟩)
  | det hd' | det_ub hd' | strLit hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem SafeUntil.of_call_internal {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {sym : String} {fnTy : CTy} {fn : FnDef} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hwit : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv0, callBlks0, m0'))
    (hw : ∀ base callEnv callBlks m',
      Sem.pushCallParams prog.tags m base 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv, callBlks, m') →
      SafeUntil prog cfg ext Q R
        (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k))) :
    SafeUntil prog cfg ext Q R s := by
  obtain ⟨callEnv0, callBlks0, m0', hpush0⟩ := hwit
  refine SafeUntil.step (fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret))
    (not_isUB_of_stepDet_some hd) fun s' hstep => ?_
  cases hstep with
  | call_internal hd' hfn' hcoerce' hpush' =>
    rw [hd] at hd'; cases hd'; rw [hfn] at hfn'; cases hfn'; rw [hcoerce] at hcoerce'; cases hcoerce'
    exact hw _ _ _ _ hpush'
  | call_internal_ub hd' hfn' hbad =>
    rw [hd] at hd'; cases hd'; rw [hfn] at hfn'; cases hfn'
    exact False.elim (hbad coerced (fun _ => 0) callEnv0 callBlks0 m0' hcoerce hpush0)
  | call_ext hd' hnfn' | call_ext_ub hd' hnfn' =>
    rw [hd] at hd'; cases hd'; rw [hfn] at hnfn'; cases hnfn'
  | det hd' | det_ub hd' | strLit hd' | localDecl hd' | localDecl_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem SafeUntil.of_call_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    {sym : String} {fnTy retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hnfn : prog.fns sym = none)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hnoub : ¬ ext sym coerced m os .ub)
    (hw : ∀ ret m' os', ext sym coerced m os (.ok ret m' os') →
      SafeUntil prog cfg ext Q R (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    SafeUntil prog cfg ext Q R s := by
  refine SafeUntil.step (fun _ _ _ hret => False.elim (not_returned_of_stepDet_some hd hret))
    (not_isUB_of_stepDet_some hd) fun s' hstep => ?_
  cases hstep with
  | call_ext hd' hnfn' hsig' hcoerce' hext' =>
    rw [hd] at hd'; cases hd'; rw [hsig] at hsig'; cases hsig'; rw [hcoerce] at hcoerce'; cases hcoerce'
    rename_i out'
    cases out' with
    | ok ret' m' os' => exact hw ret' m' os' hext'
    | ub => exact False.elim (hnoub hext')
  | call_ext_ub hd' hnfn' hbad =>
    rw [hd] at hd'; cases hd'
    exact False.elim (hbad ⟨retTy, paramTys, variadic, coerced, hsig, hcoerce⟩)
  | call_internal hd' hfn' | call_internal_ub hd' hfn' =>
    rw [hd] at hd'; cases hd'; rw [hnfn] at hfn'; cases hfn'
  | det hd' | det_ub hd' | strLit hd' | localDecl hd' | localDecl_ub hd' =>
    rw [hd] at hd'; cases hd'

theorem WPTerm.to_safeUntil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : RunState → Prop} {s : RunState}
    (hw : WPTerm prog cfg ext Q s) : SafeUntil prog cfg ext Q R s := by
  induction hw with
  | returned hq => exact SafeUntil.returned hq
  | step hnot hex _ ih =>
    exact SafeUntil.step
      (fun _ _ _ hret => let ⟨_, hst⟩ := hex; False.elim (step_not_returned (hret ▸ hst)))
      hnot ih

/-- Weakest precondition combining safety (`SafeUntil Q (fun _ => False)`) with
conditional termination (`readBudget.isSome = true → WPTerm Q`). -/
def WPSafe (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (s : RunState) : Prop :=
  SafeUntil prog cfg ext Q (fun _ => False) s ∧
    (runStateReadBudgetIsSome s = true → WPTerm prog cfg ext Q s)

theorem WPSafe.safe {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState} (h : WPSafe prog cfg ext Q s) :
    Sem.Safe prog cfg ext s :=
  h.1.safe

theorem WPSafe.post {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState} {v : Val} {m : Mem} {os : OSState}
    (h : WPSafe prog cfg ext Q s) (hstar : Sem.Star (Sem.Step prog cfg ext) s (.returned v m os)) :
    Q v m os :=
  h.1.post hstar

theorem WPSafe.terminatesSafely {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState} (h : WPSafe prog cfg ext Q s)
    (hbud : runStateReadBudgetIsSome s = true) :
    Sem.TerminatesSafely prog cfg ext s :=
  (h.2 hbud).terminatesSafely

/-- Shared operational-step rules satisfied by both `WPTerm` and `SafeUntil · R`. -/
structure WPRules (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (W : (Val → Mem → OSState → Prop) → RunState → Prop) : Prop where
  of_det_state : ∀ {Q s s'},
    Sem.stepDet prog cfg s = some (.next s') → W Q s' → W Q s
  of_exprPure : ∀ {Q es es' ctx mods mods' env blks m m' os k},
    Sem.stepExprPure prog cfg env m mods es = some (es', m', mods') →
    W Q (.running (.expr es' ctx mods') env blks m' os k) →
    W Q (.running (.expr es ctx mods) env blks m os k)
  of_strLit : ∀ {Q s str fs ctx mods env blks m os k}
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit),
    Sem.stepDet prog cfg s = some (.allocStr str fs ctx mods env blks m os k) →
    (∀ (base : UInt64) (bid : BlockId) (m' : Mem),
      m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') →
      W Q (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods) env blks m' os k)) →
    W Q s
  of_localDecl_none : ∀ {Q s d rest env blks m os k}
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty)),
    Sem.stepDet prog cfg s = some (.allocLocal d none rest env blks m os k) →
    (∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      W Q (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os k)) →
    W Q s
  of_localDecl_some : ∀ {Q s d rv rest env blks m os k}
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty)),
    Sem.stepDet prog cfg s = some (.allocLocal d (some rv) rest env blks m os k) →
    (∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      ∃ r m2, Sem.writePlace prog.tags m1 bid 0 d.ty.stripConst rv = some (r, m2) ∧
        W Q (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os k)) →
    W Q s

theorem WPRules.wpTerm (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :
    WPRules prog cfg ext (WPTerm prog cfg ext) where
  of_det_state hd hw := WPTerm.of_det_state hd hw
  of_exprPure h hw := WPTerm.of_exprPure h hw
  of_strLit hsz hd hw := WPTerm.of_strLit hd hsz hw
  of_localDecl_none hsz hal hd hw := WPTerm.of_localDecl_none hd hsz hal hw
  of_localDecl_some hsz hal hd hw := WPTerm.of_localDecl_some hd hsz hal hw

theorem WPRules.safeUntil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (R : RunState → Prop) :
    WPRules prog cfg ext (fun Q s => SafeUntil prog cfg ext Q R s) where
  of_det_state hd hw := SafeUntil.of_det_state hd hw
  of_exprPure h hw := SafeUntil.of_exprPure h hw
  of_strLit hsz hd hw := SafeUntil.of_strLit hd hsz hw
  of_localDecl_none hsz hal hd hw := SafeUntil.of_localDecl_none hd hsz hal hw
  of_localDecl_some hsz hal hd hw := SafeUntil.of_localDecl_some hd hsz hal hw

/-! ## Modular Function Call Contracts (`CallContract`, `CallSpec`, `CallSafeSpec`) -/

/-- Pure pre/post specification metadata shared across terminating and safe VCGen. -/
structure CallContract where
  sym : String
  paramTys : List CTy
  retTy : CTy
  variadic : Bool := false
  pre : Mem → OSState → List Val → Prop
  post : Mem → OSState → List Val → Val → Mem → OSState → Prop
  pre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
    m_clean.nextBlock ≤ m.nextBlock →
    (∀ b ∈ bs, m_clean.blocks b = none) →
    (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
    (∀ b ∈ bs, b < m.nextBlock) →
    (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
    pre m_clean os args → pre m os args
  post_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
    m_clean.nextBlock ≤ m.nextBlock →
    (∀ b ∈ bs, m_clean.blocks b = none) →
    (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
    (∀ b ∈ bs, b < m.nextBlock) →
    (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
    pre m_clean os args →
    post m os args rv m' os' →
    m.nextBlock ≤ m'.nextBlock ∧
    (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
    (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
      ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack)
  post_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val}
    (bs : List BlockId),
    m_clean.nextBlock ≤ m.nextBlock →
    (∀ b ∈ bs, m_clean.blocks b = none) →
    (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
    (∀ b ∈ bs, b < m.nextBlock) →
    (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
    pre m_clean os args →
    post m os args rv m_after os' →
    post m_clean os args rv (dropBlks m_after bs) os'

abbrev ContractEnv := String → Option CallContract

theorem post_stack_of_preserve {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hpres : ∀ {m : Mem} {os : OSState} {args : List Val} {rv : Val} {m' : Mem} {os' : OSState},
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) :
    ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack) := by
  intro _ m m' _ _ _ _ _ _ _ _ _ _ _ hpost
  obtain ⟨hle, hstk⟩ := hpres hpost
  exact ⟨hle, fun b _ blk hbm hk => hstk b blk hbm hk,
    fun b blk hbm hk => ⟨blk, hstk b blk hbm hk, hk⟩⟩

/-- Terminating modular function call contract (`WPTerm` and `SafeUntil`). -/
structure CallSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) extends CallContract where
  sound : ∀ {s : RunState} {fnTy : CTy} {ptys : List CTy} {argVals : List (Val × CTy)} {args : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop},
    Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
    fnTy.unqual = .fnPtr retTy ptys variadic →
    ptys.map CTy.unqual = paramTys.map CTy.unqual →
    Sem.coerceCallArgs m paramTys variadic argVals = some args →
    pre m os args →
    (∀ rv m' os', post m os args rv m' os' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv retTy) fs) ctx []) env blks m' os' k)) →
    WPTerm prog cfg ext Q s
  sound_safe : ∀ {s : RunState} {fnTy : CTy} {ptys : List CTy} {argVals : List (Val × CTy)} {args : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop} {R : RunState → Prop},
    Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
    fnTy.unqual = .fnPtr retTy ptys variadic →
    ptys.map CTy.unqual = paramTys.map CTy.unqual →
    Sem.coerceCallArgs m paramTys variadic argVals = some args →
    pre m os args →
    (∀ rv m' os', post m os args rv m' os' →
      SafeUntil prog cfg ext Q R (.running (.expr (.ret (.rval rv retTy) fs) ctx []) env blks m' os' k)) →
    SafeUntil prog cfg ext Q R s

abbrev SpecEnv (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :=
  String → Option (CallSpec prog cfg ext)

def SpecEnv.toContracts {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SpecEnv prog cfg ext) : ContractEnv :=
  fun s => (specs s).map CallSpec.toCallContract

@[simp] theorem SpecEnv.toContracts_apply {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SpecEnv prog cfg ext) (s : String) :
    specs.toContracts s = (specs s).map CallSpec.toCallContract := rfl

/-- Conditionally terminating modular function call contract (`SafeUntil` unconditionally,
and `WPTerm` whenever `os.readBudget.isSome = true`). -/
structure CallSafeSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) extends CallContract where
  sound_safe : ∀ {s : RunState} {fnTy : CTy} {ptys : List CTy} {argVals : List (Val × CTy)} {args : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop} {R : RunState → Prop},
    Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
    fnTy.unqual = .fnPtr retTy ptys variadic →
    ptys.map CTy.unqual = paramTys.map CTy.unqual →
    Sem.coerceCallArgs m paramTys variadic argVals = some args →
    pre m os args →
    (∀ rv m' os', post m os args rv m' os' →
      SafeUntil prog cfg ext Q R (.running (.expr (.ret (.rval rv retTy) fs) ctx []) env blks m' os' k)) →
    SafeUntil prog cfg ext Q R s
  sound_term : ∀ {s : RunState} {fnTy : CTy} {ptys : List CTy} {argVals : List (Val × CTy)} {args : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop},
    os.readBudget.isSome = true →
    Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
    fnTy.unqual = .fnPtr retTy ptys variadic →
    ptys.map CTy.unqual = paramTys.map CTy.unqual →
    Sem.coerceCallArgs m paramTys variadic argVals = some args →
    pre m os args →
    (∀ rv m' os', post m os args rv m' os' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv retTy) fs) ctx []) env blks m' os' k)) →
    WPTerm prog cfg ext Q s

abbrev SafeSpecEnv (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :=
  String → Option (CallSafeSpec prog cfg ext)

def SafeSpecEnv.toContracts {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SafeSpecEnv prog cfg ext) : ContractEnv :=
  fun s => (specs s).map CallSafeSpec.toCallContract

@[simp] theorem SafeSpecEnv.toContracts_apply {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SafeSpecEnv prog cfg ext) (s : String) :
    specs.toContracts s = (specs s).map CallSafeSpec.toCallContract := rfl

def CallSpec.toSafeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : CallSpec prog cfg ext) : CallSafeSpec prog cfg ext where
  toCallContract := c.toCallContract
  sound_safe := c.sound_safe
  sound_term := fun _ => c.sound

def CallSafeSpec.toTermSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : CallSafeSpec prog cfg ext) : CallSpec prog cfg ext where
  sym := c.sym
  paramTys := c.paramTys
  retTy := c.retTy
  variadic := c.variadic
  pre := fun m os args => os.readBudget.isSome = true ∧ c.pre m os args
  post := c.post
  pre_mono := fun bs hnb hbs hag hlt hstk ⟨hbud, hpre⟩ => ⟨hbud, c.pre_mono bs hnb hbs hag hlt hstk hpre⟩
  post_stack := fun bs hnb hbs hag hlt hstk ⟨_, hpre⟩ hp => c.post_stack bs hnb hbs hag hlt hstk hpre hp
  post_drop := fun bs hnb hbs hag hlt hstk ⟨_, hpre⟩ hp => c.post_drop bs hnb hbs hag hlt hstk hpre hp
  sound := fun hd hsig hptys hco ⟨hbud, hpre⟩ hcont =>
    c.sound_term hbud hd hsig hptys hco hpre hcont
  sound_safe := fun hd hsig hptys hco ⟨_, hpre⟩ hcont =>
    c.sound_safe hd hsig hptys hco hpre hcont

def SafeSpecEnv.toTermSpecs {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SafeSpecEnv prog cfg ext) : SpecEnv prog cfg ext :=
  fun s => (specs s).map CallSafeSpec.toTermSpec

@[simp] theorem SafeSpecEnv.toTermSpecs_apply {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SafeSpecEnv prog cfg ext) (s : String) :
    specs.toTermSpecs s = (specs s).map CallSafeSpec.toTermSpec := rfl

def CallContractsSound (prog : Prog) (cfg : PointerConfig)
    (W : (Val → Mem → OSState → Prop) → RunState → Prop) (contracts : ContractEnv) : Prop :=
  ∀ {sym : String} {c : CallContract}, contracts sym = some c → c.sym = sym →
    ∀ {s : RunState} {fnTy : CTy} {ptys : List CTy} {argVals : List (Val × CTy)} {args : List Val}
      {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
      {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop},
      Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
      fnTy.unqual = .fnPtr c.retTy ptys c.variadic →
      ptys.map CTy.unqual = c.paramTys.map CTy.unqual →
      Sem.coerceCallArgs m c.paramTys c.variadic argVals = some args →
      c.pre m os args →
      (∀ rv m' os', c.post m os args rv m' os' →
        W Q (.running (.expr (.ret (.rval rv c.retTy) fs) ctx []) env blks m' os' k)) →
      W Q s

theorem SpecEnv.contractsSound_wpTerm {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SpecEnv prog cfg ext) :
    CallContractsSound prog cfg (WPTerm prog cfg ext) specs.toContracts := by
  intro sym c hc hsym_eq s fnTy ptys argVals args fs ctx env blks m os k Q hd hsig hptys hco hpre hcont
  cases hs : specs sym with
  | none => simp [SpecEnv.toContracts, hs] at hc
  | some sp =>
    simp only [SpecEnv.toContracts, hs, Option.map_some, Option.some.injEq] at hc
    have hsym : sp.sym = sym := (congrArg CallContract.sym hc).trans hsym_eq
    rw [← hc] at hsig hptys hco hpre hcont
    rw [← hsym] at hd
    exact sp.sound hd hsig hptys hco hpre hcont

theorem SpecEnv.contractsSound_safeUntil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SpecEnv prog cfg ext) (R : RunState → Prop) :
    CallContractsSound prog cfg (fun Q s => SafeUntil prog cfg ext Q R s) specs.toContracts := by
  intro sym c hc hsym_eq s fnTy ptys argVals args fs ctx env blks m os k Q hd hsig hptys hco hpre hcont
  cases hs : specs sym with
  | none => simp [SpecEnv.toContracts, hs] at hc
  | some sp =>
    simp only [SpecEnv.toContracts, hs, Option.map_some, Option.some.injEq] at hc
    have hsym : sp.sym = sym := (congrArg CallContract.sym hc).trans hsym_eq
    rw [← hc] at hsig hptys hco hpre hcont
    rw [← hsym] at hd
    exact sp.sound_safe hd hsig hptys hco hpre hcont

theorem SafeSpecEnv.contractsSound_safeUntil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (specs : SafeSpecEnv prog cfg ext) (R : RunState → Prop) :
    CallContractsSound prog cfg (fun Q s => SafeUntil prog cfg ext Q R s) specs.toContracts := by
  intro sym c hc hsym_eq s fnTy ptys argVals args fs ctx env blks m os k Q hd hsig hptys hco hpre hcont
  cases hs : specs sym with
  | none => simp [SafeSpecEnv.toContracts, hs] at hc
  | some sp =>
    simp only [SafeSpecEnv.toContracts, hs, Option.map_some, Option.some.injEq] at hc
    have hsym : sp.sym = sym := (congrArg CallContract.sym hc).trans hsym_eq
    rw [← hc] at hsig hptys hco hpre hcont
    rw [← hsym] at hd
    exact sp.sound_safe hd hsig hptys hco hpre hcont

/-! ## Pure Functional Expression VCGen (`vcExprL`, `vcExprR`, `vcExprAgg`, `vcExprDiscard`) -/

def isFnCTy : CTy → Bool
  | t => match t.unqual with | .fnPtr .. => true | _ => false

def isScalarPlaceTy : CTy → Bool
  | t => match t.unqual with
    | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ _ | .vaList => true
    | _ => false

def isNonAggRvalTy : CTy → Bool
  | t => match t.unqual with
    | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ | .array _ _ => false
    | _ => true

def isAggTy : CTy → Bool
  | t => match t.unqual with
    | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ => true
    | _ => false

def vcBranch (v : Val) (Kt Kf : Prop) : Prop :=
  match vcTruthy v with
  | some P => (P → Kt) ∧ (¬ P → Kf)
  | none => False

def vcUnary (op : UnOp) (v : Val) (K : Val → CTy → Prop) : Prop :=
  match v with
  | .int k bv =>
    let u := vcIntUnOp op k bv
    u.1 ∧ K u.2.1 u.2.2
  | _ =>
    match Sem.evalUnary op v with
    | some (rv, rt) => K rv rt
    | none => False

def vcCast (m : Mem) (target : CTy) (v : Val) (K : Val → CTy → Prop) : Prop :=
  match vcPureCast? target v with
  | some rv => K rv target
  | none =>
    match Sem.castVal m target v with
    | some rv => K rv target
    | none => False

def vcBinary (cfg : PointerConfig) (tags : TypeEnv) (m : Mem)
    (op : BinOp) (v1 : Val) (t1 : CTy) (v2 : Val) (t2 : CTy) (K : Val → CTy → Prop) : Prop :=
  match v1, v2, t1.intKind?, t2.intKind? with
  | .int k1 bv1, .int k2 bv2, some k1', some k2' =>
    if _ : k1 = k1' ∧ k2 = k2' then
      let b := vcIntBinOp op k1 bv1 k2 bv2
      b.1 ∧ K b.2.1 b.2.2
    else False
  | _, _, _, _ =>
    if (t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) && (op == .eq || op == .ne) then
      match vcPtrEqBool? v1 v2 with
      | some eq =>
        let b := if op == .eq then eq else !eq
        K (.int .i32 (if b then 1 else 0)) (.int .i32)
      | none => False
    else
      match Sem.applyBinary cfg tags m op v1 t1 v2 t2 with
      | some (rv, rt) => K rv rt
      | none => False

def vcStrLit (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat))
    (str : String)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  ∃ hsz : str.utf8ByteSize + 1 < ptrDiffLimit,
    ∀ (bid : BlockId) (hle : s.mem.nextBlock ≤ bid) (base : UInt64),
      let m' := allocAt s.mem bid hle (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)
      K (.ptr bid 0) (.ptr (.const_ (.int .i8))) { s with mem := m' } mv mh

def vcReadHeapPlace (prog : Prog) (s : SymState) (mv : List String)
    (mh : List (BlockId × Int64 × Nat)) (b : BlockId) (off : Int64) (ty : CTy)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  match ty.unqual with
  | .array _ _ => K (.ptr b off) ty.decay s mv mh
  | _ =>
    isNonAggRvalTy ty ∧
    (∃ blk, s.mem.blocks b = some blk) ∧
    (∀ p ∈ mh, p.1 ≠ b ∨ p.2.1.toInt + (p.2.2 : Int) ≤ off.toInt ∨
      off.toInt + (sizeofTy prog.tags ty : Int) ≤ p.2.1.toInt) ∧
    match Sem.readVal prog.tags s.mem b off ty with
    | some rv => K rv ty.decay s mv mh
    | none => False

def vcReadAggPlace (prog : Prog) (s : SymState) (mv : List String)
    (mh : List (BlockId × Int64 × Nat)) (b : BlockId) (off : Int64) (ty : CTy)
    (K : List MemByte → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  let sz := sizeofTy prog.tags ty
  isAggTy ty ∧
  (∃ blk, s.mem.blocks b = some blk) ∧
  (∀ p ∈ mh, p.1 ≠ b ∨ p.2.1.toInt + (p.2.2 : Int) ≤ off.toInt ∨ off.toInt + (sz : Int) ≤ p.2.1.toInt) ∧
  match s.mem.readBytes b off sz with
  | some bs => K bs ty s mv mh
  | none => False

def vcReadDiscardPlace (prog : Prog) (s : SymState) (mv : List String)
    (mh : List (BlockId × Int64 × Nat)) (b : BlockId) (off : Int64) (ty : CTy)
    (K : SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  match ty.unqual with
  | .array _ _ => K s mv mh
  | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ =>
    vcReadAggPlace prog s mv mh b off ty fun _ _ s1 mv1 mh1 => K s1 mv1 mh1
  | _ =>
    vcReadHeapPlace prog s mv mh b off ty fun _ _ s1 mv1 mh1 => K s1 mv1 mh1

def vcAssignPlaceFinish (prog : Prog) (cfg : PointerConfig) (op : AssignOp)
    (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat))
    (b : BlockId) (off : Int64) (fty : CTy) (rval : Val) (rty : CTy)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  let sz := sizeofTy prog.tags fty
  (∃ blk, s.mem.blocks b = some blk) ∧
  (∀ p ∈ mh, p.1 ≠ b ∨ p.2.1.toInt + (p.2.2 : Int) ≤ off.toInt ∨ off.toInt + (sz : Int) ≤ p.2.1.toInt) ∧
  match Sem.assignOpToBin? op with
  | none =>
    vcCast s.mem fty rval fun cv _ =>
      ValScalarTyped fty cv ∧
      match Sem.writeVal s.mem b off fty cv with
      | some m' => K cv fty { s with mem := m' } mv ((b, off, sz) :: mh)
      | none => False
  | some bop =>
    match Sem.readVal prog.tags s.mem b off fty with
    | none => False
    | some oldV =>
      vcBinary cfg prog.tags s.mem bop oldV fty rval rty fun rawV _ =>
        vcCast s.mem fty rawV fun cv _ =>
          ValScalarTyped fty cv ∧
          match Sem.writeVal s.mem b off fty cv with
          | some m' => K cv fty { s with mem := m' } mv ((b, off, sz) :: mh)
          | none => False

abbrev vcAssignArrowFinish := vcAssignPlaceFinish

def vcWriteAggPlace (prog : Prog)
    (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat))
    (b : BlockId) (off : Int64) (fty : CTy) (bs : List MemByte)
    (K : List MemByte → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  let sz := sizeofTy prog.tags fty
  isAggTy fty ∧
  (∃ blk, s.mem.blocks b = some blk) ∧
  (∀ p ∈ mh, p.1 ≠ b ∨ p.2.1.toInt + (p.2.2 : Int) ≤ off.toInt ∨ off.toInt + (sz : Int) ≤ p.2.1.toInt) ∧
  bs.length = sz ∧
  match s.mem.writeBytes b off bs with
  | some m' => K bs fty { s with mem := m' } mv ((b, off, sz) :: mh)
  | none => False

def vcIncDecPlaceFinish (prog : Prog) (cfg : PointerConfig) (op : IncDecOp)
    (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat))
    (b : BlockId) (off : Int64) (lty : CTy)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) : Prop :=
  let sz := sizeofTy prog.tags lty
  let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
  (∃ blk, s.mem.blocks b = some blk) ∧
  (∀ p ∈ mh, p.1 ≠ b ∨ p.2.1.toInt + (p.2.2 : Int) ≤ off.toInt ∨ off.toInt + (sz : Int) ≤ p.2.1.toInt) ∧
  match Sem.readVal prog.tags s.mem b off lty with
  | none => False
  | some oldV =>
    vcBinary cfg prog.tags s.mem .add oldV lty (.int .i32 (BitVec.ofInt IntKind.i32.bits d)) (.int .i32) fun newV _ =>
      match Sem.writeVal s.mem b off lty newV with
      | none => False
      | some m' =>
        let retV := match op with | .preInc | .preDec => newV | _ => oldV
        K retV lty { s with mem := m' } mv ((b, off, sz) :: mh)

def vcBindVal (v : Val) (K : Val → Prop) : Prop :=
  match v with
  | .int k bv => ∀ bv' : BitVec k.bits, bv' = bv → K (.int k bv')
  | .ptr b off => ∀ off' : Int64, off' = off → K (.ptr b off')
  | _ => K v

theorem vcBindVal_elim {v : Val} {K : Val → Prop} (h : vcBindVal v K) : K v := by
  cases v with
  | int k bv => exact h bv rfl
  | ptr b off => exact h off rfl
  | _ => exact h

mutual
def vcExprL (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat)) :
    CExpr → (BlockId → Int64 → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) → Prop
  | .paren e, K => vcExprL prog cfg contracts baseEnv s mv mh e K
  | .var x, K =>
    s.regs.lookup x = none ∧
    match s.stack.lookup x with
    | some (b, ty) => K b 0 ty s mv mh
    | none =>
      match baseEnv.lookup x with
      | some (b, ty) => K b 0 ty s mv mh
      | none => False
  | .deref e, K =>
    vcExprR prog cfg contracts baseEnv s mv mh e fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr el, .ptr b off => K b off el s1 mv1 mh1
      | _, _ => False
  | .index base idx, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
        match pty.unqual, Sem.valAsInt? iv with
        | .ptr el, some (_, idxInt) =>
          match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
          | some (.ptr b off) => K b off el s2 mv2 mh2
          | _ => False
        | _, _ => False
  | .member base fld, K =>
    vcExprL prog cfg contracts baseEnv s mv mh base fun b off sty s1 mv1 mh1 =>
      match fieldLayout? prog.tags sty fld with
      | some (foff, fty) => K b (Int64.ofInt (off.toInt + foff)) fty s1 mv1 mh1
      | none => False
  | .arrow base fld, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr sty, .ptr b off =>
        match fieldLayout? prog.tags sty fld with
        | some (foff, fty) => K b (Int64.ofInt (off.toInt + foff)) fty s1 mv1 mh1
        | none => False
      | _, _ => False
  | _, _ => False
termination_by e => (sizeOf e, 0)

def vcExprR (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat)) :
    CExpr → (Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) → Prop
  | .paren e, K => vcExprR prog cfg contracts baseEnv s mv mh e K
  | .lit val k _ _ _, K => K (Sem.ofIntCast k val) (.int k) s mv mh
  | .strLit str, K => vcStrLit s mv mh str K
  | .sizeOfTy ty, K => K (.int .u64 (BitVec.ofNat IntKind.u64.bits (sizeofTy prog.tags ty))) (.int .u64) s mv mh
  | .sizeOfExpr e, K =>
    match Sem.exprType? prog.tags (s.typeEnv baseEnv) prog.fnProtos e with
    | some ty => K (.int .u64 (BitVec.ofNat IntKind.u64.bits (sizeofTy prog.tags ty))) (.int .u64) s mv mh
    | none => False
  | .var x, K =>
    match s.regs.lookup x with
    | some (v, ty) =>
      isScalarPlaceTy ty ∧ x ∉ mv ∧ v ≠ .undef ∧ K v ty.decay s mv mh
    | none =>
      match s.stack.lookup x with
      | some (b, ty) => vcReadHeapPlace prog s mv mh b 0 ty K
      | none =>
        match baseEnv.lookup x with
        | some (b, ty) => vcReadHeapPlace prog s mv mh b 0 ty K
        | none =>
          match Sem.enumConst? prog.tags x with
          | some ev => K (Sem.ofIntCast .i32 ev) (.int .i32) s mv mh
          | none =>
            match prog.fnProtos x with
            | some (r, ps, va) => K (.fnPtr x) (.fnPtr r ps va) s mv mh
            | none => False
  | .unary op e, K =>
    vcExprR prog cfg contracts baseEnv s mv mh e fun v _ s1 mv1 mh1 =>
      vcUnary op v fun rv rt => K rv rt s1 mv1 mh1
  | .cast target e, K =>
    vcExprR prog cfg contracts baseEnv s mv mh e fun v _ s1 mv1 mh1 =>
      vcCast s1.mem target v fun cv _ => K cv target s1 mv1 mh1
  | .binary op l r, K =>
    vcExprR prog cfg contracts baseEnv s mv mh l fun v1 t1 s1 mv1 mh1 =>
      vcExprR prog cfg contracts baseEnv s1 mv1 mh1 r fun v2 t2 s2 mv2 mh2 =>
        vcBinary cfg prog.tags s2.mem op v1 t1 v2 t2 fun rv rt => K rv rt s2 mv2 mh2
  | .logAnd l r, K =>
    vcExprR prog cfg contracts baseEnv s mv mh l fun v1 _ s1 mv1 mh1 =>
      vcBranch v1
        (vcExprR prog cfg contracts baseEnv s1 [] [] r fun v2 _ s2 mv2 mh2 =>
          vcBranch v2 (K (.int .i32 1) (.int .i32) s2 mv2 mh2) (K (.int .i32 0) (.int .i32) s2 mv2 mh2))
        (K (.int .i32 0) (.int .i32) s1 mv1 mh1)
  | .logOr l r, K =>
    vcExprR prog cfg contracts baseEnv s mv mh l fun v1 _ s1 mv1 mh1 =>
      vcBranch v1
        (K (.int .i32 1) (.int .i32) s1 mv1 mh1)
        (vcExprR prog cfg contracts baseEnv s1 [] [] r fun v2 _ s2 mv2 mh2 =>
          vcBranch v2 (K (.int .i32 1) (.int .i32) s2 mv2 mh2) (K (.int .i32 0) (.int .i32) s2 mv2 mh2))
  | .cond c t f, K =>
    vcExprR prog cfg contracts baseEnv s mv mh c fun vc _ s1 _ _ =>
      vcBranch vc
        (vcExprR prog cfg contracts baseEnv s1 [] [] t K)
        (vcExprR prog cfg contracts baseEnv s1 [] [] f K)
  | .comma l r, K =>
    vcExprDiscard prog cfg contracts baseEnv s mv mh l fun s1 _ _ =>
      vcExprR prog cfg contracts baseEnv s1 [] [] r K
  | .addrOf l, K =>
    vcExprL prog cfg contracts baseEnv s mv mh l fun b off ty s1 mv1 mh1 =>
      K (.ptr b off) (.ptr ty) s1 mv1 mh1
  | .deref e, K =>
    vcExprR prog cfg contracts baseEnv s mv mh e fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr el, .ptr b off => vcReadHeapPlace prog s1 mv1 mh1 b off el K
      | .fnPtr rt ps va, .fnPtr sym => K (.fnPtr sym) (.fnPtr rt ps va) s1 mv1 mh1
      | _, _ => False
  | .index base idx, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
        match pty.unqual, Sem.valAsInt? iv with
        | .ptr el, some (_, idxInt) =>
          match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
          | some (.ptr b off) => vcReadHeapPlace prog s2 mv2 mh2 b off el K
          | _ => False
        | _, _ => False
  | .member base fld, K =>
    vcExprL prog cfg contracts baseEnv s mv mh base fun b off sty s1 mv1 mh1 =>
      match fieldLayout? prog.tags sty fld with
      | some (foff, fty) =>
        vcReadHeapPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
      | none => False
  | .arrow base fld, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr sty, .ptr b off =>
        match fieldLayout? prog.tags sty fld with
        | some (foff, fty) =>
          vcReadHeapPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
        | none => False
      | _, _ => False
  | .incDec op (.var x), K =>
    match s.regs.lookup x with
    | some (oldV, lty) =>
      let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
      x ∉ mv ∧ oldV ≠ .undef ∧ lty.isConst = false ∧
      vcBinary cfg prog.tags s.mem .add oldV lty (.int .i32 (BitVec.ofInt IntKind.i32.bits d)) (.int .i32) fun newV _ =>
        vcCast s.mem lty newV fun cv _ =>
          ValScalarTyped lty cv ∧
          vcBindVal cv fun nv =>
            let retV := match op with | .preInc | .preDec => newV | _ => oldV
            K retV lty { s with regs := s.regs.set x nv lty } (x :: mv) mh
    | none =>
      vcExprL prog cfg contracts baseEnv s mv mh (.var x) fun b off lty s1 mv1 mh1 =>
        vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 b off lty K
  | .incDec op lhs, K =>
    vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
      vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 b off lty K
  | .assign op (.var x) rhs, K =>
    match s.regs.lookup x with
    | some (_, lty) =>
      vcExprR prog cfg contracts baseEnv s mv mh rhs fun rval rty s1 mv1 mh1 =>
        x ∉ mv1 ∧ lty.isConst = false ∧
        match s1.regs.lookup x with
        | none => False
        | some (oldV, lty1) =>
          lty1 = lty ∧
          match Sem.assignOpToBin? op with
          | none =>
            vcCast s1.mem lty rval fun cv _ =>
              ValScalarTyped lty cv ∧
              vcBindVal cv fun nv =>
                K nv lty { s1 with regs := s1.regs.set x nv lty } (x :: mv1) mh1
          | some bop =>
            oldV ≠ .undef ∧
            vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
              vcCast s1.mem lty rawV fun cv _ =>
                ValScalarTyped lty cv ∧
                vcBindVal cv fun nv =>
                  K nv lty { s1 with regs := s1.regs.set x nv lty } (x :: mv1) mh1
    | none =>
      vcExprL prog cfg contracts baseEnv s mv mh (.var x) fun b off lty s1 mv1 mh1 =>
        vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
          vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K
  | .assign op lhs rhs, K =>
    vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
      vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
        vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K
  | .call fn args, K =>
    vcExprR prog cfg contracts baseEnv s mv mh fn fun fnV fnTy sFn mvFn mhFn =>
      match fnV, fnTy.unqual with
      | .fnPtr sym, .fnPtr rt ptys va =>
        match contracts sym with
        | none => False
        | some spec =>
          spec.sym = sym ∧
          rt = spec.retTy ∧
          ptys.map CTy.unqual = spec.paramTys.map CTy.unqual ∧
          va = spec.variadic ∧
          vcCallArgs prog cfg contracts baseEnv sFn mvFn mhFn args [] fun sArgs argVals =>
            match Sem.coerceCallArgs sArgs.mem spec.paramTys spec.variadic argVals with
            | some coerced =>
              spec.pre sArgs.mem sArgs.os coerced ∧
              ∀ rv m' os', spec.post sArgs.mem sArgs.os coerced rv m' os' →
                K rv spec.retTy { sArgs with mem := m', os := os' } [] []
            | none => False
      | _, _ => False
  | .vaStart ap _, K =>
    s.regs.lookup ap = none ∧
    match s.stack.lookup ap with
    | some (b, ty) =>
      ty.isVaList = true ∧
      match s.mem.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) (.byte 1)) with
      | some m' => K .void .void { s with mem := m' } mv mh
      | none => False
    | none =>
      match baseEnv.lookup ap with
      | some (b, ty) =>
        ty.isVaList = true ∧
        match s.mem.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) (.byte 1)) with
        | some m' => K .void .void { s with mem := m' } mv mh
        | none => False
      | none => False
  | .vaEnd ap, K =>
    s.regs.lookup ap = none ∧
    match s.stack.lookup ap with
    | some (b, ty) =>
      ty.isVaList = true ∧
      match s.mem.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) .undef) with
      | some m' => K .void .void { s with mem := m' } mv mh
      | none => False
    | none =>
      match baseEnv.lookup ap with
      | some (b, ty) =>
        ty.isVaList = true ∧
        match s.mem.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) .undef) with
        | some m' => K .void .void { s with mem := m' } mv mh
        | none => False
      | none => False
termination_by e => (sizeOf e, 0)

def vcExprAgg (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat)) :
    CExpr → (List MemByte → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) → Prop
  | .paren e, K => vcExprAgg prog cfg contracts baseEnv s mv mh e K
  | .var x, K =>
    s.regs.lookup x = none ∧
    match s.stack.lookup x with
    | some (b, ty) => vcReadAggPlace prog s mv mh b 0 ty K
    | none =>
      match baseEnv.lookup x with
      | some (b, ty) => vcReadAggPlace prog s mv mh b 0 ty K
      | none => False
  | .deref e, K =>
    vcExprR prog cfg contracts baseEnv s mv mh e fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr el, .ptr b off => vcReadAggPlace prog s1 mv1 mh1 b off el K
      | _, _ => False
  | .index base idx, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
        match pty.unqual, Sem.valAsInt? iv with
        | .ptr el, some (_, idxInt) =>
          match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
          | some (.ptr b off) => vcReadAggPlace prog s2 mv2 mh2 b off el K
          | _ => False
        | _, _ => False
  | .member base fld, K =>
    vcExprL prog cfg contracts baseEnv s mv mh base fun b off sty s1 mv1 mh1 =>
      match fieldLayout? prog.tags sty fld with
      | some (foff, fty) =>
        vcReadAggPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
      | none => False
  | .arrow base fld, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr sty, .ptr b off =>
        match fieldLayout? prog.tags sty fld with
        | some (foff, fty) =>
          vcReadAggPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
        | none => False
      | _, _ => False
  | .cond c t f, K =>
    vcExprR prog cfg contracts baseEnv s mv mh c fun vc _ s1 _ _ =>
      vcBranch vc
        (vcExprAgg prog cfg contracts baseEnv s1 [] [] t K)
        (vcExprAgg prog cfg contracts baseEnv s1 [] [] f K)
  | .comma l r, K =>
    vcExprDiscard prog cfg contracts baseEnv s mv mh l fun s1 _ _ =>
      vcExprAgg prog cfg contracts baseEnv s1 [] [] r K
  | .assign op lhs rhs, K =>
    if op == .eq then
      vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
        vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
          vcWriteAggPlace prog s2 mv2 mh2 b off lty bs K
    else False
  | _, _ => False
termination_by e => (sizeOf e, 0)

def vcExprDiscard (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat)) :
    CExpr → (SymState → List String → List (BlockId × Int64 × Nat) → Prop) → Prop
  | .paren e, K => vcExprDiscard prog cfg contracts baseEnv s mv mh e K
  | .comma l r, K =>
    vcExprDiscard prog cfg contracts baseEnv s mv mh l fun s1 _ _ =>
      vcExprDiscard prog cfg contracts baseEnv s1 [] [] r K
  | .cond c t f, K =>
    vcExprR prog cfg contracts baseEnv s mv mh c fun vc _ s1 _ _ =>
      vcBranch vc
        (vcExprDiscard prog cfg contracts baseEnv s1 [] [] t K)
        (vcExprDiscard prog cfg contracts baseEnv s1 [] [] f K)
  | .var x, K =>
    match s.regs.lookup x with
    | some (v, ty) =>
      isScalarPlaceTy ty ∧ x ∉ mv ∧ v ≠ .undef ∧ K s mv mh
    | none =>
      match s.stack.lookup x with
      | some (b, ty) => vcReadDiscardPlace prog s mv mh b 0 ty K
      | none =>
        match baseEnv.lookup x with
        | some (b, ty) => vcReadDiscardPlace prog s mv mh b 0 ty K
        | none =>
          match Sem.enumConst? prog.tags x with
          | some _ => K s mv mh
          | none =>
            match prog.fnProtos x with
            | some _ => K s mv mh
            | none => False
  | .deref e, K =>
    vcExprR prog cfg contracts baseEnv s mv mh e fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr el, .ptr b off => vcReadDiscardPlace prog s1 mv1 mh1 b off el K
      | .fnPtr _ _ _, .fnPtr _ => K s1 mv1 mh1
      | _, _ => False
  | .index base idx, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
        match pty.unqual, Sem.valAsInt? iv with
        | .ptr el, some (_, idxInt) =>
          match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
          | some (.ptr b off) => vcReadDiscardPlace prog s2 mv2 mh2 b off el K
          | _ => False
        | _, _ => False
  | .member base fld, K =>
    vcExprL prog cfg contracts baseEnv s mv mh base fun b off sty s1 mv1 mh1 =>
      match fieldLayout? prog.tags sty fld with
      | some (foff, fty) =>
        vcReadDiscardPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
      | none => False
  | .arrow base fld, K =>
    vcExprR prog cfg contracts baseEnv s mv mh base fun p pty s1 mv1 mh1 =>
      match pty.unqual, p with
      | .ptr sty, .ptr b off =>
        match fieldLayout? prog.tags sty fld with
        | some (foff, fty) =>
          vcReadDiscardPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
        | none => False
      | _, _ => False
  | .assign op (.var x) rhs, K =>
    match s.regs.lookup x with
    | some (_, lty) =>
      vcExprR prog cfg contracts baseEnv s mv mh rhs fun rval rty s1 mv1 mh1 =>
        x ∉ mv1 ∧ lty.isConst = false ∧
        match s1.regs.lookup x with
        | none => False
        | some (oldV, lty1) =>
          lty1 = lty ∧
          match Sem.assignOpToBin? op with
          | none =>
            vcCast s1.mem lty rval fun cv _ =>
              ValScalarTyped lty cv ∧
              vcBindVal cv fun nv =>
                K { s1 with regs := s1.regs.set x nv lty } (x :: mv1) mh1
          | some bop =>
            oldV ≠ .undef ∧
            vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
              vcCast s1.mem lty rawV fun cv _ =>
                ValScalarTyped lty cv ∧
                vcBindVal cv fun nv =>
                  K { s1 with regs := s1.regs.set x nv lty } (x :: mv1) mh1
    | none =>
      vcExprL prog cfg contracts baseEnv s mv mh (.var x) fun b off lty s1 mv1 mh1 =>
        if isAggTy lty then
          op = .eq ∧
          vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
            vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
        else
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
  | .assign op lhs rhs, K =>
    vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
      if isAggTy lty then
        op = .eq ∧
        vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
          vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
      else
        vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
          vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
  | e, K => vcExprR prog cfg contracts baseEnv s mv mh e fun _ _ s1 mv1 mh1 => K s1 mv1 mh1
termination_by e => (sizeOf e, 1)

def vcCallArgs (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (s : SymState) (mv : List String) (mh : List (BlockId × Int64 × Nat)) :
    List CExpr → List (Val × CTy) → (SymState → List (Val × CTy) → Prop) → Prop
  | [], done, K => K s done
  | arg :: rest, done, K =>
    vcExprR prog cfg contracts baseEnv s mv mh arg fun v ty s1 mv1 mh1 =>
      vcCallArgs prog cfg contracts baseEnv s1 mv1 mh1 rest (done ++ [(v, ty)]) K
termination_by args => (sizeOf args, 0)
end

/-! ## Pure Functional Statement VCGen (`vcStmt`, `vcStmtSafe`, `vcFn`, `vcFnSafe`) -/

structure ContPost where
  normal : SymState → Prop
  onBreak : SymState → Prop
  onContinue : SymState → Prop
  onReturn : Val → Mem → OSState → Prop
  onGoto : String → SymState → Prop := fun _ _ => False

def vcDeclList (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (k : ContPost) : List (VarDecl × Bool) → SymState → Prop
  | [], s => k.normal s
  | (d, isStk) :: rest, s =>
    if d.isStatic then vcDeclList prog cfg contracts baseEnv k rest s
    else if isStk then
      match d.init? with
      | none =>
        ∃ (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
          (hal : 0 < max 1 (alignofTy prog.tags d.ty)),
          s.regs.lookup d.name = none ∧
          ∀ (bid : BlockId) (hle : s.mem.nextBlock ≤ bid) (base : UInt64)
            (_hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
            let m' := allocAt s.mem bid hle (max 1 (sizeofTy prog.tags d.ty))
              (max 1 (alignofTy prog.tags d.ty)) .rw .stack base (fun _ => .undef) hsz hal _hba
            vcDeclList prog cfg contracts baseEnv k rest
              { s with stack := (d.name, bid, d.ty) :: s.stack, mem := m' }
      | some (.expr e) =>
        if isAggTy d.ty then
          vcExprAgg prog cfg contracts baseEnv s [] [] e fun bs _ s1 _ _ =>
            ∃ (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
              (hal : 0 < max 1 (alignofTy prog.tags d.ty)),
              bs.length = sizeofTy prog.tags d.ty ∧
              s1.regs.lookup d.name = none ∧
              ∀ (bid : BlockId) (hle : s1.mem.nextBlock ≤ bid) (base : UInt64)
                (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
                let m1 := allocAt s1.mem bid hle (max 1 (sizeofTy prog.tags d.ty))
                  (max 1 (alignofTy prog.tags d.ty)) .rw .stack base (fun _ => .undef) hsz hal hba
                match m1.writeBytes bid 0 bs with
                | none => False
                | some m2 =>
                  vcDeclList prog cfg contracts baseEnv k rest
                    { s1 with stack := (d.name, bid, d.ty) :: s1.stack, mem := m2 }
        else
          vcExprR prog cfg contracts baseEnv s [] [] e fun rv _ s1 _ _ =>
            vcCast s1.mem d.ty.stripConst rv fun cv _ =>
              ∃ (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
                (hal : 0 < max 1 (alignofTy prog.tags d.ty)),
                ValScalarTyped d.ty cv ∧
                s1.regs.lookup d.name = none ∧
                ∀ (bid : BlockId) (hle : s1.mem.nextBlock ≤ bid) (base : UInt64)
                  (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
                  let m1 := allocAt s1.mem bid hle (max 1 (sizeofTy prog.tags d.ty))
                    (max 1 (alignofTy prog.tags d.ty)) .rw .stack base (fun _ => .undef) hsz hal hba
                  match Sem.writeVal m1 bid 0 d.ty.stripConst cv with
                  | none => False
                  | some m2 =>
                    vcDeclList prog cfg contracts baseEnv k rest
                      { s1 with stack := (d.name, bid, d.ty) :: s1.stack, mem := m2 }
      | some _ => False
    else match d.init? with
    | none =>
      max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit ∧
      0 < max 1 (alignofTy prog.tags d.ty) ∧
      s.stack.lookup d.name = none ∧
      vcDeclList prog cfg contracts baseEnv k rest { s with regs := (d.name, .undef, d.ty) :: s.regs }
    | some (.expr e) =>
      vcExprR prog cfg contracts baseEnv s [] [] e fun rv _ s1 _ _ =>
        vcCast s1.mem d.ty.stripConst rv fun cv _ =>
          max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit ∧
          0 < max 1 (alignofTy prog.tags d.ty) ∧
          s1.stack.lookup d.name = none ∧
          ValScalarTyped d.ty cv ∧
          vcBindVal cv fun v0 =>
            vcDeclList prog cfg contracts baseEnv k rest { s1 with regs := (d.name, v0, d.ty) :: s1.regs }
    | some _ => False

mutual
def vcFramesCont (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) :
    List AnnStmt.GotoFrame → ContPost
  | [] => k
  | .stmts tl :: rest =>
    let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy k s rest
    if tl.isEmpty then kRest
    else
      { kRest with
        normal := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy kRest s1 tl
        onGoto := fun lbl s1 =>
          match hgt : AnnStmt.findGotoAnnList lbl tl with
          | some (tgt, fs) =>
            have _hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf tl :=
              AnnStmt.findGotoAnnList_sizeOf_lt hgt
            vcStmtGen strict prog cfg contracts baseEnv retTy
              (vcFramesCont strict prog cfg contracts baseEnv retTy kRest s1 fs) s1 tgt
          | none =>
            AnnStmt.annHasLabelList lbl tl = false ∧ kRest.onGoto lbl s1 }
  | .blockEnd :: rest =>
    let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy k s rest
    let regLen0 := s.regs.length
    let stkLen0 := s.stack.length
    { normal := fun s' => kRest.normal (s'.exitBlock regLen0 stkLen0)
      onBreak := fun s' => kRest.onBreak (s'.exitBlock regLen0 stkLen0)
      onContinue := fun s' => kRest.onContinue (s'.exitBlock regLen0 stkLen0)
      onReturn := kRest.onReturn
      onGoto := fun lbl s' => kRest.onGoto lbl (s'.exitBlock regLen0 stkLen0) }
  | .switchCont :: rest =>
    let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy k s rest
    { kRest with onBreak := kRest.normal }
termination_by fs => AnnStmt.framesSize fs

def vcStmtGen (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) : AnnStmt → Prop
  | .nop => k.normal s
  | .expr e => vcExprDiscard prog cfg contracts baseEnv s [] [] e fun s1 _ _ => k.normal s1
  | .decl d => vcDeclList prog cfg contracts baseEnv k [(d, false)] s
  | .decls ds => vcDeclList prog cfg contracts baseEnv k (ds.map (·, false)) s
  | .stackDecl d => vcDeclList prog cfg contracts baseEnv k [(d, true)] s
  | .stackDecls ds => vcDeclList prog cfg contracts baseEnv k (ds.map (·, true)) s
  | .mixedDecls ds => vcDeclList prog cfg contracts baseEnv k ds s
  | .block [] => k.normal s
  | .block ss =>
    let regLen0 := s.regs.length
    let stkLen0 := s.stack.length
    let kBlk : ContPost :=
      { normal := fun s' => k.normal (s'.exitBlock regLen0 stkLen0)
        onBreak := fun s' => k.onBreak (s'.exitBlock regLen0 stkLen0)
        onContinue := fun s' => k.onContinue (s'.exitBlock regLen0 stkLen0)
        onReturn := k.onReturn
        onGoto := fun lbl s' => k.onGoto lbl (s'.exitBlock regLen0 stkLen0) }
    vcStmtListGen strict prog cfg contracts baseEnv retTy kBlk s ss
  | .ifStmt c t f? =>
    vcExprR prog cfg contracts baseEnv s [] [] c fun vc _ s1 _ _ =>
      vcBranch vc
        (vcStmtGen strict prog cfg contracts baseEnv retTy k s1 t)
        (match f? with | some f => vcStmtGen strict prog cfg contracts baseEnv retTy k s1 f | none => k.normal s1)
  | .ifJoin c t f? J =>
    vcExprR prog cfg contracts baseEnv s [] [] c fun vc _ s1 _ _ =>
      let kJoin : ContPost := { k with normal := J }
      vcBranch vc
        (vcStmtGen strict prog cfg contracts baseEnv retTy kJoin s1 t)
        (match f? with | some f => vcStmtGen strict prog cfg contracts baseEnv retTy kJoin s1 f | none => J s1) ∧
      (∀ s2, J s2 → k.normal s2)
  | .whileLoop c body Inv meas =>
    (if strict then Inv s (meas s) s else Inv s 0 s) ∧
    ∀ n s1, (if strict then Inv s n s1 else n = 0 ∧ Inv s 0 s1) →
      vcExprR prog cfg contracts baseEnv s1 [] [] c fun vc _ s2 _ _ =>
        vcBranch vc
          (vcStmtGen strict prog cfg contracts baseEnv retTy
            { normal := fun s3 => (if strict then meas s3 < n ∧ Inv s (meas s3) s3 else Inv s 0 s3)
              onBreak := k.normal
              onContinue := fun s3 => (if strict then meas s3 < n ∧ Inv s (meas s3) s3 else Inv s 0 s3)
              onReturn := k.onReturn
              onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
            s2 body)
          (k.normal s2)
  | .doWhileLoop body c Inv meas =>
    (if strict then Inv s (meas s) s else Inv s 0 s) ∧
    ∀ n s1, (if strict then Inv s n s1 else n = 0 ∧ Inv s 0 s1) →
      let afterBody := fun s2 =>
        vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
          vcBranch vc
            (if strict then meas s3 < n ∧ Inv s (meas s3) s3 else Inv s 0 s3)
            (k.normal s3)
      vcStmtGen strict prog cfg contracts baseEnv retTy
        { normal := afterBody
          onBreak := k.normal
          onContinue := afterBody
          onReturn := k.onReturn
          onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
        s1 body
  | .doWhileGotos body c Inv gotoSpecs meas =>
    (if strict then Inv s (meas s) s else Inv s 0 s) ∧
    (∀ n s1, (if strict then Inv s n s1 else n = 0 ∧ Inv s 0 s1) →
      let afterBody := fun s2 =>
        vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
          vcBranch vc
            (if strict then meas s3 < n ∧ Inv s (meas s3) s3 else Inv s 0 s3)
            (k.normal s3)
      vcStmtGen strict prog cfg contracts baseEnv retTy
        { normal := afterBody
          onBreak := k.normal
          onContinue := afterBody
          onReturn := k.onReturn
          onGoto := fun lbl s3 =>
            match gotoSpecs.lookup lbl with
            | some GSpec => (if strict then meas s3 < n ∧ GSpec s (meas s3) s3 else GSpec s 0 s3)
            | none => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
        s1 body) ∧
    (∀ p ∈ gotoSpecs,
      match hgt : AnnStmt.findGotoAnn p.1 body with
      | none => False
      | some (tgt, fs) =>
        have _hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf body :=
          AnnStmt.findGotoAnn_sizeOf_lt hgt
        ∀ n sG, (if strict then p.2 s n sG else n = 0 ∧ p.2 s 0 sG) →
          let afterBody := fun s2 =>
            vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
              vcBranch vc
                (if strict then meas s3 < n ∧ Inv s (meas s3) s3 else Inv s 0 s3)
                (k.normal s3)
          let kLoop : ContPost :=
            { normal := afterBody
              onBreak := k.normal
              onContinue := afterBody
              onReturn := k.onReturn
              onGoto := fun lbl s3 =>
                match gotoSpecs.lookup lbl with
                | some GSpec => (if strict then meas s3 < n ∧ GSpec s (meas s3) s3 else GSpec s 0 s3)
                | none => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
          vcStmtGen strict prog cfg contracts baseEnv retTy
            (vcFramesCont strict prog cfg contracts baseEnv retTy kLoop sG fs) sG tgt)
  | .forLoop init? c? stp? body Inv meas =>
    (match init? with
     | none => if strict then Inv s (meas s) s else Inv s 0 s
     | some init =>
       vcExprDiscard prog cfg contracts baseEnv s [] [] init fun s0 _ _ =>
         if strict then Inv s (meas s0) s0 else Inv s 0 s0) ∧
    ∀ n s1, (if strict then Inv s n s1 else n = 0 ∧ Inv s 0 s1) →
      let afterBody := fun s2 =>
        match stp? with
        | none => if strict then meas s2 < n ∧ Inv s (meas s2) s2 else Inv s 0 s2
        | some stp =>
          vcExprDiscard prog cfg contracts baseEnv s2 [] [] stp fun s3 _ _ =>
            if strict then meas s3 < n ∧ Inv s (meas s3) s3 else Inv s 0 s3
      let kLoop : ContPost :=
        { normal := afterBody
          onBreak := k.normal
          onContinue := afterBody
          onReturn := k.onReturn
          onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
      match c? with
      | some c =>
        vcExprR prog cfg contracts baseEnv s1 [] [] c fun vc _ s2 _ _ =>
          vcBranch vc
            (vcStmtGen strict prog cfg contracts baseEnv retTy kLoop s2 body)
            (k.normal s2)
      | none =>
        vcStmtGen strict prog cfg contracts baseEnv retTy kLoop s1 body
  | .switchStmt scrut body =>
    vcExprR prog cfg contracts baseEnv s [] [] scrut fun v _ s1 _ _ =>
      ∃ k_int iv, Sem.valAsInt? v = some (k_int, iv) ∧
        match htgt : AnnStmt.findSwitchAnnTarget iv body with
        | none =>
          Sem.findSwitchTarget iv body.erase = none ∧ k.normal s1
        | some tgt =>
          have _hlt : sizeOf tgt < sizeOf body := AnnStmt.findSwitchAnnTarget_sizeOf_lt htgt
          Sem.findSwitchTarget iv body.erase = some tgt.erase ∧
          vcStmtGen strict prog cfg contracts baseEnv retTy { k with onBreak := k.normal } s1 tgt
  | .caseStmt _ body => vcStmtGen strict prog cfg contracts baseEnv retTy k s body
  | .defaultStmt body => vcStmtGen strict prog cfg contracts baseEnv retTy k s body
  | .labelStmt _ body => vcStmtGen strict prog cfg contracts baseEnv retTy k s body
  | .gotoStmt lbl => k.onGoto lbl s
  | .breakStmt => k.onBreak s
  | .continueStmt => k.onContinue s
  | .returnStmt none => retTy.isVoid = true ∧ k.onReturn .void s.exitFn s.os
  | .returnStmt (some e) =>
    vcExprR prog cfg contracts baseEnv s [] [] e fun rv _ s1 _ _ =>
      if retTy.isVoid then k.onReturn .void s1.exitFn s1.os
      else vcCast s1.mem retTy rv fun cv _ => k.onReturn cv s1.exitFn s1.os
termination_by stmt => sizeOf stmt

def vcStmtListGen (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) : List AnnStmt → Prop
  | [] => k.normal s
  | [hd] => vcStmtGen strict prog cfg contracts baseEnv retTy k s hd
  | hd :: tl =>
    let kRest : ContPost :=
      { k with
        normal := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy k s1 tl
        onGoto := fun lbl s1 =>
          match hgt : AnnStmt.findGotoAnnList lbl tl with
          | some (tgt, fs) =>
            have _hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf tl :=
              AnnStmt.findGotoAnnList_sizeOf_lt hgt
            vcStmtGen strict prog cfg contracts baseEnv retTy
              (vcFramesCont strict prog cfg contracts baseEnv retTy k s1 fs) s1 tgt
          | none =>
            AnnStmt.annHasLabelList lbl tl = false ∧ k.onGoto lbl s1 }
    vcStmtGen strict prog cfg contracts baseEnv retTy kRest s hd
termination_by ss => sizeOf ss
end

private theorem vcFramesCont_nil (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) :
    vcFramesCont strict prog cfg contracts baseEnv retTy k s [] = k := by
  rw [vcFramesCont]

private theorem vcFramesCont_stmts_nil (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (rest : List AnnStmt.GotoFrame) :
    vcFramesCont strict prog cfg contracts baseEnv retTy k s (.stmts [] :: rest) =
      vcFramesCont strict prog cfg contracts baseEnv retTy k s rest := by
  rw [vcFramesCont]; rfl

private theorem vcFramesCont_stmts_cons (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (t0 : AnnStmt) (ttl : List AnnStmt)
    (rest : List AnnStmt.GotoFrame) :
    vcFramesCont strict prog cfg contracts baseEnv retTy k s (.stmts (t0 :: ttl) :: rest) =
      let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy k s rest
      { kRest with
        normal := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy kRest s1 (t0 :: ttl)
        onGoto := fun lbl s1 =>
          match hgt : AnnStmt.findGotoAnnList lbl (t0 :: ttl) with
          | some (tgt, fs) =>
            have _hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf (t0 :: ttl) :=
              AnnStmt.findGotoAnnList_sizeOf_lt hgt
            vcStmtGen strict prog cfg contracts baseEnv retTy
              (vcFramesCont strict prog cfg contracts baseEnv retTy kRest s1 fs) s1 tgt
          | none =>
            AnnStmt.annHasLabelList lbl (t0 :: ttl) = false ∧ kRest.onGoto lbl s1 } := by
  rw [vcFramesCont]; rfl

private theorem vcFramesCont_blockEnd (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (rest : List AnnStmt.GotoFrame) :
    vcFramesCont strict prog cfg contracts baseEnv retTy k s (.blockEnd :: rest) =
      let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy k s rest
      { normal := fun s' => kRest.normal (s'.exitBlock s.regs.length s.stack.length)
        onBreak := fun s' => kRest.onBreak (s'.exitBlock s.regs.length s.stack.length)
        onContinue := fun s' => kRest.onContinue (s'.exitBlock s.regs.length s.stack.length)
        onReturn := kRest.onReturn
        onGoto := fun lbl s' => kRest.onGoto lbl (s'.exitBlock s.regs.length s.stack.length) } := by
  rw [vcFramesCont]

private theorem vcFramesCont_switchCont (strict : Bool) (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (rest : List AnnStmt.GotoFrame) :
    vcFramesCont strict prog cfg contracts baseEnv retTy k s (.switchCont :: rest) =
      let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy k s rest
      { kRest with onBreak := kRest.normal } := by
  rw [vcFramesCont]

def vcStmt {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SpecEnv prog cfg ext)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (stmt : AnnStmt) : Prop :=
  vcStmtGen true prog cfg specs.toContracts baseEnv retTy k s stmt

def vcStmtList {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SpecEnv prog cfg ext)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (ss : List AnnStmt) : Prop :=
  vcStmtListGen true prog cfg specs.toContracts baseEnv retTy k s ss

def vcStmtSafe {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SafeSpecEnv prog cfg ext)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (stmt : AnnStmt) : Prop :=
  vcStmtGen false prog cfg specs.toContracts baseEnv retTy k s stmt

def vcStmtSafeList {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SafeSpecEnv prog cfg ext)
    (baseEnv : Env) (retTy : CTy) (k : ContPost) (s : SymState) (ss : List AnnStmt) : Prop :=
  vcStmtListGen false prog cfg specs.toContracts baseEnv retTy k s ss

def fnEntryPost (fn : FnDef)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (m : Mem) (os : OSState) (args : List Val) : ContPost :=
  { normal := fun s' =>
      if fn.retTy.isVoid then post m os args .void s'.exitFn s'.os
      else post m os args .undef s'.exitFn s'.os
    onBreak := fun _ => False
    onContinue := fun _ => False
    onReturn := fun rv m' os' => post m os args rv m' os'
    onGoto := fun _ _ => False }

def fnEntryState (fn : FnDef) (m : Mem) (os : OSState) (args : List Val) : SymState :=
  { regs := (fn.params.zip (args.take fn.params.length)).reverse.map (fun (p, v) => (p.name, v, p.ty))
    stack := []
    mem := m
    os := os }

def vcFn {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SpecEnv prog cfg ext)
    (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop) : Prop :=
  ∀ m os args,
    (∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2) →
    (if fn.variadic then fn.params.length ≤ args.length else args.length = fn.params.length) →
    pre m os args →
    vcStmt prog cfg specs (prog.fnStatics fn.name ++ prog.globalEnv) fn.retTy
      (fnEntryPost fn post m os args) (fnEntryState fn m os args) annBody

def vcFnSafeSplit {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SafeSpecEnv prog cfg ext)
    (fn : FnDef) (annSafe annTerm : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop) : Prop :=
  ∀ m os args,
    (∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2) →
    (if fn.variadic then fn.params.length ≤ args.length else args.length = fn.params.length) →
    pre m os args →
    (os.readBudget.isSome = false →
      vcStmtSafe prog cfg specs (prog.fnStatics fn.name ++ prog.globalEnv) fn.retTy
        (fnEntryPost fn post m os args) (fnEntryState fn m os args) annSafe) ∧
    (os.readBudget.isSome = true →
      vcStmt prog cfg specs.toTermSpecs (prog.fnStatics fn.name ++ prog.globalEnv) fn.retTy
        (fnEntryPost fn post m os args) (fnEntryState fn m os args) annTerm)

def vcFnSafe {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig) (specs : SafeSpecEnv prog cfg ext)
    (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop) : Prop :=
  vcFnSafeSplit prog cfg specs fn annBody annBody pre post

/-! ## Expression Soundness (`vcExpr_sound_aux_gen`) -/

theorem vcBranch_elim {v : Val} {Kt Kf : Prop} (h : vcBranch v Kt Kf) :
    ∃ b : Bool, Sem.isTruthy v = some b ∧ (b = true → Kt) ∧ (b = false → Kf) := by
  unfold vcBranch at h
  cases hvt : vcTruthy v with
  | none => simp [hvt] at h
  | some P =>
    simp only [hvt] at h
    by_cases hP : P
    · exact ⟨true, (isTruthy_some_true_iff hvt).mpr hP, (fun _ => h.1 hP),
        (fun hf => False.elim (by cases hf))⟩
    · exact ⟨false, (isTruthy_some_false_iff hvt).mpr hP,
        (fun ht => False.elim (by cases ht)), (fun _ => h.2 hP)⟩

theorem vcUnary_sound {op : UnOp} {v : Val} {K : Val → CTy → Prop} (h : vcUnary op v K) :
    ∃ rv rt, Sem.evalUnary op v = some (rv, rt) ∧ K rv rt := by
  unfold vcUnary at h
  cases v with
  | int k bv => exact ⟨_, _, vcIntUnOp_sound op k bv h.1, h.2⟩
  | null | ptr _ _ | fnPtr _ | undef | vaList _ | void =>
    cases he : Sem.evalUnary op _ <;> simp [he] at h
    exact ⟨_, _, rfl, h⟩

theorem vcCast_sound_clean {s : SymState} {target : CTy} {v : Val} {K : Val → CTy → Prop}
    (h : vcCast s.mem target v K) :
    ∃ cv, Sem.castVal s.mem target v = some cv ∧ K cv target := by
  unfold vcCast at h
  cases hc : vcPureCast? target v with
  | some rv =>
    simp only [hc] at h
    exact ⟨rv, vcPureCast?_sound s.mem hc, h⟩
  | none =>
    simp only [hc] at h
    cases hs : Sem.castVal s.mem target v with
    | none => simp [hs] at h
    | some rv =>
      simp only [hs] at h
      exact ⟨rv, rfl, h⟩

theorem vcCast_sound {tags : TypeEnv} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {target : CTy} {v : Val} {K : Val → CTy → Prop} (h : vcCast s.mem target v K) :
    ∃ cv, Sem.castVal m target v = some cv ∧ K cv target := by
  obtain ⟨cv, hc_s, hk⟩ := vcCast_sound_clean h
  exact ⟨cv, hr.castVal_mem hc_s, hk⟩

private theorem vcBinaryFallback_sound {cfg : PointerConfig} {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {op : BinOp} {v1 : Val} {t1 : CTy} {v2 : Val} {t2 : CTy} {K : Val → CTy → Prop}
    (h : (if (t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) && (op == .eq || op == .ne) then
      match vcPtrEqBool? v1 v2 with
      | some eq =>
        let b := if op == .eq then eq else !eq
        K (.int .i32 (if b then 1 else 0)) (.int .i32)
      | none => False
    else
      match Sem.applyBinary cfg tags s.mem op v1 t1 v2 t2 with
      | some (rv, rt) => K rv rt
      | none => False)) :
    ∃ rv rt, Sem.applyBinary cfg tags m op v1 t1 v2 t2 = some (rv, rt) ∧ K rv rt := by
  by_cases hc : ((t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) && (op == .eq || op == .ne)) = true
  · simp only [hc, ↓reduceIte] at h
    rcases Bool.and_eq_true _ _ |>.mp hc with ⟨htp, hop_b⟩
    cases hp : vcPtrEqBool? v1 v2 with
    | none => simp [hp] at h
    | some eq =>
      simp only [hp] at h
      have hop : op = .eq ∨ op = .ne := by cases op <;> simp at hop_b <;> simp
      have hcmp := evalPtrCmp_eq_of_vcPtrEqBool? m hop hp
      have hbin : Sem.applyBinary cfg tags m op v1 t1 v2 t2 =
          some (.int .i32 (if (if op == .eq then eq else !eq) then 1 else 0), .int .i32) := by
        have hif : Sem.applyBinary cfg tags m op v1 t1 v2 t2 =
            (Sem.evalPtrCmp m op v1 v2).map (·, .int .i32) := by
          unfold Sem.applyBinary
          simp only [Bool.or_eq_true] at htp
          rcases htp with ((h1 | h2) | h3) | h4
          · simp only [h1, Bool.true_or, ↓reduceIte]; rcases hop with rfl | rfl <;> rfl
          · simp only [h2, Bool.true_or, Bool.or_true, ↓reduceIte]; rcases hop with rfl | rfl <;> rfl
          · cases hu : t1.unqual <;> simp only [isFnCTy, hu] at h3 <;> try cases h3
            simp only [hu, Bool.true_or, Bool.or_true, ↓reduceIte]
            rcases hop with rfl | rfl <;> rfl
          · cases hu : t2.unqual <;> simp only [isFnCTy, hu] at h4 <;> try cases h4
            simp only [hu, Bool.or_true, ↓reduceIte]
            rcases hop with rfl | rfl <;> rfl
        rw [hif, hcmp]
        rcases hop with rfl | rfl <;> rfl
      exact ⟨_, _, hbin, h⟩
  · have hcf : ((t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) && (op == .eq || op == .ne)) = false :=
      Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
    cases ha : Sem.applyBinary cfg tags s.mem op v1 t1 v2 t2 with
    | none => simp [ha] at h
    | some p =>
      simp only [ha] at h
      exact ⟨p.1, p.2, hr.applyBinary_mem ha, h⟩

theorem vcBinary_sound {cfg : PointerConfig} {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m)
    {op : BinOp} {v1 : Val} {t1 : CTy} {v2 : Val} {t2 : CTy} {K : Val → CTy → Prop}
    (h : vcBinary cfg tags s.mem op v1 t1 v2 t2 K) :
    ∃ rv rt, Sem.applyBinary cfg tags m op v1 t1 v2 t2 = some (rv, rt) ∧ K rv rt := by
  unfold vcBinary at h
  split at h
  · next k1 bv1 k2 bv2 k1' k2' hk1 hk2 =>
    dsimp only at h
    by_cases heq : k1 = k1' ∧ k2 = k2'
    · simp only [heq] at h
      have ht1 : t1.intKind? = some k1 := heq.1 ▸ hk1
      have ht2 : t2.intKind? = some k2 := heq.2 ▸ hk2
      exact ⟨_, _, vcIntBinOp_sound ht1 ht2 h.1, h.2⟩
    · simp only [heq] at h; cases h
  · exact vcBinaryFallback_sound hr h

theorem vcReadHeapPlace_sound {prog : Prog} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {b : BlockId} {off : Int64} {ty : CTy}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (h : vcReadHeapPlace prog s mv mh b off ty K) :
    ∃ rv, Sem.readPlace prog.tags m mods .rval b off ty = some (.rval rv ty.decay) ∧ K rv ty.decay s mv mh := by
  unfold vcReadHeapPlace at h
  cases hu : ty.unqual with
  | array el len =>
    simp only [hu] at h
    refine ⟨.ptr b off, ?_, h⟩
    unfold Sem.readPlace
    rw [hu]
  | int _ | enumTy _ _ | ptr _ | fnPtr _ _ _ | vaList | void | const_ _ | typedef _ _ =>
    simp only [hu] at h
    rcases h with ⟨_, ⟨blk, hbm⟩, hdisj, hrv⟩
    obtain ⟨hb_not, _, hrd_eq⟩ := hr.read_mem (off := off) (ty := ty) hbm
    have hnc := hm.no_conflict_heap hb_not off (sizeofTy prog.tags ty) hdisj
    cases hrd : Sem.readVal prog.tags s.mem b off ty with
    | none => simp [hrd] at hrv
    | some rv =>
      simp only [hrd] at hrv
      refine ⟨rv, ?_, hrv⟩
      unfold Sem.readPlace
      rw [hu]
      simp only [hnc, Bool.not_false, guard_true, hrd_eq, hrd, bind, Option.bind, Option.map_some]
  | structTy _ | unionTy _ | anonStruct _ | anonUnion _ =>
    simp only [hu, isNonAggRvalTy] at h
    cases h.1

theorem vcReadAggPlace_sound {prog : Prog} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {b : BlockId} {off : Int64} {ty : CTy}
    {K : List MemByte → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (h : vcReadAggPlace prog s mv mh b off ty K) :
    ∃ bs, Sem.readPlace prog.tags m mods .rval b off ty = some (.structVal bs ty) ∧ K bs ty s mv mh := by
  unfold vcReadAggPlace at h
  rcases h with ⟨hagg, ⟨blk, hbm⟩, hdisj, hbs⟩
  obtain ⟨hb_not, hpl_eq⟩ := hr.readPlace_mem (mods := mods) (w := .rval) (off := off) (ty := ty) hbm
  have hnc := hm.no_conflict_heap hb_not off (sizeofTy prog.tags ty) hdisj
  cases hrd : s.mem.readBytes b off (sizeofTy prog.tags ty) with
  | none => simp [hrd] at hbs
  | some bs =>
    simp only [hrd] at hbs
    refine ⟨bs, ?_, hbs⟩
    rw [hpl_eq]
    unfold Sem.readPlace
    unfold isAggTy at hagg
    cases hu : ty.unqual <;> simp [hu] at hagg
    all_goals simp only [hnc, Bool.not_false, guard_true, hrd, bind, Option.bind, Option.map_some]

theorem vcReadDiscardPlace_sound {prog : Prog} {baseEnv : Env} {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {b : BlockId} {off : Int64} {ty : CTy}
    {K : SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (h : vcReadDiscardPlace prog s mv mh b off ty K) :
    ∃ res, Sem.readPlace prog.tags m mods .rval b off ty = some res ∧ K s mv mh := by
  unfold vcReadDiscardPlace at h
  cases hu : ty.unqual with
  | array el len =>
    simp only [hu] at h
    exact ⟨.rval (.ptr b off) ty.decay, by unfold Sem.readPlace; rw [hu], h⟩
  | structTy _ | unionTy _ | anonStruct _ | anonUnion _ =>
    simp only [hu] at h
    obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr hm h
    exact ⟨.structVal bs ty, hrd, hk⟩
  | int _ | enumTy _ _ | ptr _ | fnPtr _ _ _ | vaList | void | const_ _ | typedef _ _ =>
    simp only [hu] at h
    have h' : vcReadHeapPlace prog s mv mh b off ty (fun _ _ s1 mv1 mh1 => K s1 mv1 mh1) := by
      simpa [vcReadHeapPlace, hu] using h
    obtain ⟨rv, hrd, hk⟩ := vcReadHeapPlace_sound hr hm h'
    exact ⟨.rval rv ty.decay, hrd, hk⟩

theorem vcAssignPlaceFinish_sound {prog : Prog} {cfg : PointerConfig} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {op : AssignOp} {b : BlockId} {off : Int64} {fty : CTy} {rval : Val} {rty : CTy}
    {fs : List ExprFrame}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (h : vcAssignPlaceFinish prog cfg op s mv mh b off fty rval rty K) :
    ∃ rv rt s' mv' mh' m' mods',
      Sem.stepExprPure prog cfg env m mods (.ret (.rval rval rty) (.assignRhsF op b off fty :: fs)) =
        some (.ret (.rval rv rt) fs, m', mods') ∧
      s'.os = s.os ∧
      Refines prog.tags baseEnv cur outer s' env blks m' ∧
      ModsOK cur outer mv' mh' mods' ∧
      K rv rt s' mv' mh' := by
  rcases h with ⟨⟨blk, hbm⟩, hdisj, hbody⟩
  obtain ⟨hb_not, _, hrd_eq⟩ := hr.read_mem (off := off) (ty := fty) hbm
  have hnc := hm.no_conflict_heap hb_not off (sizeofTy prog.tags fty) hdisj
  have hm_cons := hm.cons_heap hb_not off (sizeofTy prog.tags fty)
  cases hop : Sem.assignOpToBin? op with
  | none =>
    simp only [hop] at hbody
    obtain ⟨cv, hcast, ht, hwbody⟩ := vcCast_sound hr hbody
    cases hw : Sem.writeVal s.mem b off fty cv with
    | none => simp [hw] at hwbody
    | some m_clean' =>
      simp only [hw] at hwbody
      obtain ⟨m', _, hwm', _, hr'⟩ := hr.write_mem hw
      have hwp : Sem.writePlace prog.tags m b off fty (.rval rval rty) = some (.rval cv fty, m') :=
        writePlace_rval_cast ht hcast hwm'
      refine ⟨cv, fty, { s with mem := m_clean' }, mv, (b, off, sizeofTy prog.tags fty) :: mh,
        m', ⟨b, off, sizeofTy prog.tags fty⟩ :: mods, ?_, rfl, hr', hm_cons, hwbody⟩
      unfold Sem.stepExprPure
      simp only [hnc, Bool.not_false, guard_true, hop, hwp, bind, Option.bind, pure, Pure.pure]
  | some bop =>
    simp only [hop] at hbody
    cases hrd : Sem.readVal prog.tags s.mem b off fty with
    | none => simp [hrd] at hbody
    | some oldV =>
      simp only [hrd] at hbody
      obtain ⟨rawV, rawTy, hbin, hcastVC⟩ := vcBinary_sound hr hbody
      obtain ⟨cv, hcast, ht, hwbody⟩ := vcCast_sound hr hcastVC
      cases hw : Sem.writeVal s.mem b off fty cv with
      | none => simp [hw] at hwbody
      | some m_clean' =>
        simp only [hw] at hwbody
        obtain ⟨m', _, hwm', _, hr'⟩ := hr.write_mem hw
        have hwp : Sem.writePlace prog.tags m b off fty (.rval rawV fty) = some (.rval cv fty, m') :=
          writePlace_rval_cast ht hcast hwm'
        refine ⟨cv, fty, { s with mem := m_clean' }, mv, (b, off, sizeofTy prog.tags fty) :: mh,
          m', ⟨b, off, sizeofTy prog.tags fty⟩ :: mods, ?_, rfl, hr', hm_cons, hwbody⟩
        unfold Sem.stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hop, hrd_eq, hrd, hbin, hwp,
          bind, Option.bind, pure, Pure.pure]

theorem vcWriteAggPlace_sound {prog : Prog} {cfg : PointerConfig} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {b : BlockId} {off : Int64} {fty sty : CTy} {bs : List MemByte}
    {fs : List ExprFrame}
    {K : List MemByte → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (h : vcWriteAggPlace prog s mv mh b off fty bs K) :
    ∃ s' mv' mh' m' mods',
      Sem.stepExprPure prog cfg env m mods (.ret (.structVal bs sty) (.assignRhsF .eq b off fty :: fs)) =
        some (.ret (.structVal bs fty) fs, m', mods') ∧
      s'.os = s.os ∧
      Refines prog.tags baseEnv cur outer s' env blks m' ∧
      ModsOK cur outer mv' mh' mods' ∧
      K bs fty s' mv' mh' := by
  unfold vcWriteAggPlace at h
  rcases h with ⟨_, ⟨blk, hbm⟩, hdisj, hbs_len, hwbody⟩
  obtain ⟨hb_not, _⟩ := hr.mem_blocks_some hbm
  have hnc := hm.no_conflict_heap hb_not off (sizeofTy prog.tags fty) hdisj
  have hm_cons := hm.cons_heap hb_not off (sizeofTy prog.tags fty)
  cases hw : s.mem.writeBytes b off bs with
  | none => simp [hw] at hwbody
  | some m_clean' =>
    simp only [hw] at hwbody
    obtain ⟨m', _, _, hwp_fn, hr'⟩ := hr.writeBytes_mem hw
    have hwp := hwp_fn fty sty hbs_len
    refine ⟨{ s with mem := m_clean' }, mv, (b, off, sizeofTy prog.tags fty) :: mh,
      m', ⟨b, off, sizeofTy prog.tags fty⟩ :: mods, ?_, rfl, hr', hm_cons, hwbody⟩
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp,
      bind, Option.bind, pure, Pure.pure]

theorem vcIncDecPlaceFinish_sound {prog : Prog} {cfg : PointerConfig} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {op : IncDecOp} {b : BlockId} {off : Int64} {lty : CTy}
    {fs : List ExprFrame}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (h : vcIncDecPlaceFinish prog cfg op s mv mh b off lty K) :
    ∃ rv rt s' mv' mh' m' mods',
      Sem.stepExprPure prog cfg env m mods (.ret (.lval b off lty) (.incDecF op :: fs)) =
        some (.ret (.rval rv rt) fs, m', mods') ∧
      s'.os = s.os ∧
      Refines prog.tags baseEnv cur outer s' env blks m' ∧
      ModsOK cur outer mv' mh' mods' ∧
      K rv rt s' mv' mh' := by
  unfold vcIncDecPlaceFinish at h
  rcases h with ⟨⟨blk, hbm⟩, hdisj, hbody⟩
  obtain ⟨hb_not, _, hrd_eq⟩ := hr.read_mem (off := off) (ty := lty) hbm
  have hnc := hm.no_conflict_heap hb_not off (sizeofTy prog.tags lty) hdisj
  have hm_cons := hm.cons_heap hb_not off (sizeofTy prog.tags lty)
  cases hrd : Sem.readVal prog.tags s.mem b off lty with
  | none => simp [hrd] at hbody
  | some oldV =>
    simp only [hrd] at hbody
    obtain ⟨newV, _, hbin, hwrbody⟩ := vcBinary_sound hr hbody
    cases hw : Sem.writeVal s.mem b off lty newV with
    | none => simp [hw] at hwrbody
    | some m_clean' =>
      simp only [hw] at hwrbody
      obtain ⟨m', _, hwm', _, hr'⟩ := hr.write_mem hw
      refine ⟨_, lty, { s with mem := m_clean' }, mv, (b, off, sizeofTy prog.tags lty) :: mh,
        m', ⟨b, off, sizeofTy prog.tags lty⟩ :: mods, ?_, rfl, hr', hm_cons, hwrbody⟩
      unfold Sem.stepExprPure
      simp only [hnc, Bool.not_false, guard_true, hrd_eq, hrd, bind, Option.bind, pure, Pure.pure]
      cases op <;> ·
        simp only at hbin ⊢
        have hbin' : Sem.applyBinary cfg prog.tags m .add oldV lty (.int .i32 (BitVec.ofInt 32 _)) (.int .i32) =
            some (newV, _) := hbin
        rw [hbin']; simp only; rw [hwm']

private theorem stepExprPure_incDec_lval (prog : Prog) (cfg : PointerConfig) (env : Env)
    (m m' : Mem) (mods : ModSet) (x : String) (b : BlockId) (lty : CTy)
    (oldV newV : Val) (op : IncDecOp) (d : Int) (fs : List ExprFrame)
    (hd : d = match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1)
    (henv : env.lookup x = some (b, lty))
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hrd : Sem.readVal prog.tags m b 0 lty = some oldV)
    (hbin : ∃ t, Sem.applyBinary cfg prog.tags m .add oldV lty
      (.int .i32 (BitVec.ofInt 32 d)) (.int .i32) = some (newV, t))
    (hwm : Sem.writeVal m b 0 lty newV = some m') :
    Sem.stepExprPure prog cfg env m mods (.eval .rval (.incDec op (.var x)) fs) =
      some (.eval .lval (.var x) (.incDecF op :: fs), m, mods) ∧
    Sem.stepExprPure prog cfg env m mods (.eval .lval (.var x) (.incDecF op :: fs)) =
      some (.ret (.lval b 0 lty) (.incDecF op :: fs), m, mods) ∧
    Sem.stepExprPure prog cfg env m mods (.ret (.lval b 0 lty) (.incDecF op :: fs)) =
      some (.ret (.rval (match op with | .preInc | .preDec => newV | _ => oldV) lty) fs,
        m', ⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) := by
  rcases hbin with ⟨t, hbin⟩
  refine ⟨rfl, ?_, ?_⟩
  · unfold Sem.stepExprPure; simp [henv]
  · unfold Sem.stepExprPure
    dsimp only [bind, Option.bind, guard, Pure.pure]
    simp only [hnc, Bool.not_false, ↓reduceIte]
    rw [hrd]; dsimp only
    cases op <;> ·
      simp only at hd hbin ⊢
      subst hd
      have hbin' : Sem.applyBinary cfg prog.tags m .add oldV lty
          (.int .i32 (BitVec.ofInt 32 _)) (.int .i32) = some (newV, t) := hbin
      rw [hbin']; dsimp only; rw [hwm]

private theorem vcExpr_var_lookup_nonreg {tags : TypeEnv} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur outer s env blks m) {x : String}
    (hreg : s.regs.lookup x = none) :
    match s.stack.lookup x with
    | some p => env.lookup x = some p
    | none => env.lookup x = baseEnv.lookup x := by
  cases hstk : s.stack.lookup x with
  | some p => exact (hr.lookup_stk hstk).2.1
  | none => exact hr.lookup_none hreg hstk

private theorem vcIncDecReg_steps_sound {prog : Prog} {cfg : PointerConfig} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (hm : ModsOK cur outer mv mh mods)
    {op : IncDecOp} {x : String} {oldV : Val} {lty : CTy}
    (hl : s.regs.lookup x = some (oldV, lty))
    (fs : List ExprFrame)
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hvc : x ∉ mv ∧ oldV ≠ .undef ∧ lty.isConst = false ∧
      vcBinary cfg prog.tags s.mem .add oldV lty
        (.int .i32 (BitVec.ofInt IntKind.i32.bits
          (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1)))
        (.int .i32) fun newV _ =>
        vcCast s.mem lty newV fun cv _ =>
          ValScalarTyped lty cv ∧
          vcBindVal cv fun nv =>
            K (match op with | .preInc | .preDec => newV | _ => oldV) lty
              { s with regs := s.regs.set x nv lty } (x :: mv) mh) :
    ∃ rv cv m' b,
      Sem.stepExprPure prog cfg env m mods (.eval .rval (.incDec op (.var x)) fs) =
        some (.eval .lval (.var x) (.incDecF op :: fs), m, mods) ∧
      Sem.stepExprPure prog cfg env m mods (.eval .lval (.var x) (.incDecF op :: fs)) =
        some (.ret (.lval b 0 lty) (.incDecF op :: fs), m, mods) ∧
      Sem.stepExprPure prog cfg env m mods (.ret (.lval b 0 lty) (.incDecF op :: fs)) =
        some (.ret (.rval rv lty) fs, m', ⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) ∧
      Refines prog.tags baseEnv cur outer { s with regs := s.regs.set x cv lty } env blks m' ∧
      ModsOK cur outer (x :: mv) mh (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) ∧
      K rv lty { s with regs := s.regs.set x cv lty } (x :: mv) mh := by
  rcases hvc with ⟨hnot_mv, hne_undef, hnc_ty, hbinVC⟩
  obtain ⟨newV, newTy, hbin, hcastVC⟩ := vcBinary_sound hr hbinVC
  obtain ⟨cv, hcast, ht, hk_all⟩ := vcCast_sound hr hcastVC
  obtain ⟨sl0, _, _, _, henv0, hrd⟩ := hr.lookup_reg hl
  obtain ⟨sl, hsl, m', hn_eq, ht_eq, henv, hwm, _, hr'⟩ := hr.write_reg hl hnc_ty ht
  have hblk : sl0.blk = sl.blk := by
    rw [henv0, Option.some.injEq, Prod.mk.injEq] at henv; exact henv.1
  rw [hblk] at hrd
  have hcompat : (∃ (k1 : IntKind) (bv1 : BitVec k1.bits), newV = .int k1 bv1) ∨ newV = cv :=
    castVal_applyBinary_add_compat hbin hcast
  rw [← writeVal_castVal_eq ht hcast hcompat] at hwm
  have hnc_mod : mods.conflicts sl.blk 0 (sizeofTy prog.tags lty) = false :=
    hm.no_conflict_var (nodup_regBlks_of_nodup hr.nodup_blks) hsl (hn_eq ▸ hnot_mv) 0 (sizeofTy prog.tags lty)
  have hm' := hn_eq ▸ hm.cons_var hsl 0 (sizeofTy prog.tags lty)
  have hkv := vcBindVal_elim hk_all
  cases op
  · obtain ⟨hs1, hs2, hs3⟩ := stepExprPure_incDec_lval prog cfg env m m' mods x sl.blk lty
      oldV newV .preInc 1 fs rfl henv hnc_mod (hrd hne_undef) ⟨newTy, hbin⟩ hwm
    exact ⟨newV, cv, m', sl.blk, hs1, hs2, hs3, hr', hm', hkv⟩
  · obtain ⟨hs1, hs2, hs3⟩ := stepExprPure_incDec_lval prog cfg env m m' mods x sl.blk lty
      oldV newV .preDec (-1) fs rfl henv hnc_mod (hrd hne_undef) ⟨newTy, hbin⟩ hwm
    exact ⟨newV, cv, m', sl.blk, hs1, hs2, hs3, hr', hm', hkv⟩
  · obtain ⟨hs1, hs2, hs3⟩ := stepExprPure_incDec_lval prog cfg env m m' mods x sl.blk lty
      oldV newV .postInc 1 fs rfl henv hnc_mod (hrd hne_undef) ⟨newTy, hbin⟩ hwm
    exact ⟨oldV, cv, m', sl.blk, hs1, hs2, hs3, hr', hm', hkv⟩
  · obtain ⟨hs1, hs2, hs3⟩ := stepExprPure_incDec_lval prog cfg env m m' mods x sl.blk lty
      oldV newV .postDec (-1) fs rfl henv hnc_mod (hrd hne_undef) ⟨newTy, hbin⟩ hwm
    exact ⟨oldV, cv, m', sl.blk, hs1, hs2, hs3, hr', hm', hkv⟩

private theorem vcAssignReg_finish_sound {prog : Prog} {cfg : PointerConfig} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId}
    {x : String} {lty : CTy} {sl0 : FrameSlot}
    (hsl0 : sl0 ∈ allRegSlots cur outer) (hname0 : sl0.name = x)
    (henv0 : env.lookup x = some (sl0.blk, lty))
    {s1 : SymState} {mv1 : List String} {mh1 : List (BlockId × Int64 × Nat)} {m1 : Mem} {mods1 : ModSet}
    (hr1 : Refines prog.tags baseEnv cur outer s1 env blks m1)
    (hm1 : ModsOK cur outer mv1 mh1 mods1)
    {op : AssignOp} {rval : Val} {rty : CTy} {fs : List ExprFrame}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hk1 : x ∉ mv1 ∧ lty.isConst = false ∧
      match s1.regs.lookup x with
      | none => False
      | some (oldV, lty1) =>
        lty1 = lty ∧
        match Sem.assignOpToBin? op with
        | none =>
          vcCast s1.mem lty rval fun cv _ =>
            ValScalarTyped lty cv ∧
            vcBindVal cv fun nv =>
              K nv lty { s1 with regs := s1.regs.set x nv lty } (x :: mv1) mh1
        | some bop =>
          oldV ≠ .undef ∧
          vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
            vcCast s1.mem lty rawV fun cv _ =>
              ValScalarTyped lty cv ∧
              vcBindVal cv fun nv =>
                K nv lty { s1 with regs := s1.regs.set x nv lty } (x :: mv1) mh1) :
    ∃ (cv : Val) (m2 : Mem),
      Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval rval rty) (.assignRhsF op sl0.blk 0 lty :: fs)) =
        some (.ret (.rval cv lty) fs, m2, ⟨sl0.blk, 0, sizeofTy prog.tags lty⟩ :: mods1) ∧
      Refines prog.tags baseEnv cur outer { s1 with regs := s1.regs.set x cv lty } env blks m2 ∧
      ModsOK cur outer (x :: mv1) mh1 (⟨sl0.blk, 0, sizeofTy prog.tags lty⟩ :: mods1) ∧
      K cv lty { s1 with regs := s1.regs.set x cv lty } (x :: mv1) mh1 := by
  rcases hk1 with ⟨hnot_mv1, hnc_ty, hreg1⟩
  cases hl1 : s1.regs.lookup x with
  | none => simp [hl1] at hreg1
  | some p1 =>
    rcases p1 with ⟨oldV, lty1⟩
    simp only [hl1] at hreg1
    rcases hreg1 with ⟨rfl, hrest⟩
    obtain ⟨sl1, hsl1, hname1, _, henv1, hrd1⟩ := hr1.lookup_reg hl1
    have hblk1 : sl1.blk = sl0.blk := by
      rw [henv0, Option.some.injEq, Prod.mk.injEq] at henv1; exact henv1.1.symm
    have hnc_mod : mods1.conflicts sl0.blk 0 (sizeofTy prog.tags lty1) = false := by
      rw [← hblk1]
      exact hm1.no_conflict_var (nodup_regBlks_of_nodup hr1.nodup_blks) hsl1 (hname1 ▸ hnot_mv1) 0 (sizeofTy prog.tags lty1)
    cases hop : Sem.assignOpToBin? op with
    | none =>
      simp only [hop] at hrest
      obtain ⟨cv, hcast, ht, hk_all⟩ := vcCast_sound hr1 hrest
      obtain ⟨sl2, _, m2, _, _, henv2, hwm, _, hr2⟩ := hr1.write_reg hl1 hnc_ty ht
      have hblk2 : sl2.blk = sl0.blk := by
        rw [henv0, Option.some.injEq, Prod.mk.injEq] at henv2; exact henv2.1.symm
      rw [hblk2] at hwm
      have hwp := writePlace_rval_cast (tags := prog.tags) (vty := rty) ht hcast hwm
      refine ⟨cv, m2, ?_, hr2, hname0 ▸ hm1.cons_var hsl0 0 (sizeofTy prog.tags lty1), vcBindVal_elim hk_all⟩
      unfold Sem.stepExprPure
      simp only [hnc_mod, Bool.not_false, guard_true, hop, hwp, bind, Option.bind, pure, Pure.pure]
    | some bop =>
      simp only [hop] at hrest
      rcases hrest with ⟨hne_undef, hbinVC⟩
      obtain ⟨rawV, rawTy, hbin, hcastVC⟩ := vcBinary_sound hr1 hbinVC
      obtain ⟨cv, hcast, ht, hk_all⟩ := vcCast_sound hr1 hcastVC
      obtain ⟨sl2, _, m2, _, _, henv2, hwm, _, hr2⟩ := hr1.write_reg hl1 hnc_ty ht
      have hblk2 : sl2.blk = sl0.blk := by
        rw [henv0, Option.some.injEq, Prod.mk.injEq] at henv2; exact henv2.1.symm
      rw [hblk2] at hwm
      have hwp := writePlace_rval_cast (tags := prog.tags) (vty := lty1) ht hcast hwm
      refine ⟨cv, m2, ?_, hr2, hname0 ▸ hm1.cons_var hsl0 0 (sizeofTy prog.tags lty1), vcBindVal_elim hk_all⟩
      unfold Sem.stepExprPure
      dsimp only [bind, Option.bind, guard, Pure.pure]
      simp only [hnc_mod, Bool.not_false, ↓reduceIte, hop]
      rw [hblk1] at hrd1
      rw [hrd1 hne_undef]; dsimp only; rw [hbin]; dsimp only; rw [hwp]

private theorem vcVaOp_step_sound {prog : Prog} {cfg : PointerConfig} {baseEnv : Env}
    {cur : FrameScope} {outer : List FrameScope}
    {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {mods : ModSet}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    (ap : String) (bytes : List MemByte) (e : CExpr) (fs : List ExprFrame)
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hstep_va : ∀ (m_in m_out : Mem) (p : BlockId × CTy),
      env.lookup ap = some p → p.2.isVaList = true → m_in.writeBytes p.1 0 bytes = some m_out →
      Sem.stepExprPure prog cfg env m_in mods (.eval .rval e fs) =
        some (.ret (.rval .void .void) fs, m_out, mods))
    (hvc : s.regs.lookup ap = none ∧
      match s.stack.lookup ap with
      | some (b, ty) => ty.isVaList = true ∧
        match s.mem.writeBytes b 0 bytes with
        | some m' => K .void .void { s with mem := m' } mv mh
        | none => False
      | none =>
        match baseEnv.lookup ap with
        | some (b, ty) => ty.isVaList = true ∧
          match s.mem.writeBytes b 0 bytes with
          | some m' => K .void .void { s with mem := m' } mv mh
          | none => False
        | none => False) :
    ∃ (m_clean' m' : Mem),
      Sem.stepExprPure prog cfg env m mods (.eval .rval e fs) =
        some (.ret (.rval .void .void) fs, m', mods) ∧
      Refines prog.tags baseEnv cur outer { s with mem := m_clean' } env blks m' ∧
      K .void .void { s with mem := m_clean' } mv mh := by
  rcases hvc with ⟨hreg_none, hlookup⟩
  have henv_match := vcExpr_var_lookup_nonreg hr hreg_none
  cases hstk : s.stack.lookup ap with
  | some p =>
    simp only [hstk] at hlookup henv_match
    rcases hlookup with ⟨hva, hwr_vc⟩
    cases hw : s.mem.writeBytes p.1 0 bytes with
    | none => simp [hw] at hwr_vc
    | some m_clean' =>
      simp only [hw] at hwr_vc
      obtain ⟨m', _, hwm', _, hr'⟩ := hr.writeBytes_mem hw
      exact ⟨m_clean', m', hstep_va m m' p henv_match hva hwm', hr', hwr_vc⟩
  | none =>
    simp only [hstk] at hlookup henv_match
    cases hbase : baseEnv.lookup ap with
    | none => simp [hbase] at hlookup
    | some p =>
      simp only [hbase] at hlookup
      have henv : env.lookup ap = some p := henv_match.trans hbase
      rcases hlookup with ⟨hva, hwr_vc⟩
      cases hw : s.mem.writeBytes p.1 0 bytes with
      | none => simp [hw] at hwr_vc
      | some m_clean' =>
        simp only [hw] at hwr_vc
        obtain ⟨m', _, hwm', _, hr'⟩ := hr.writeBytes_mem hw
        exact ⟨m_clean', m', hstep_va m m' p henv hva hwm', hr', hwr_vc⟩

private theorem vcCallArgs_finish_sound {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    {contracts : ContractEnv} (hcs : CallContractsSound prog cfg W contracts)
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont} {fs : List ExprFrame}
    {sym : String} {spec : CallContract} {fnTy : CTy} {ptys : List CTy}
    (hsp : contracts sym = some spec) (hsym_eq : spec.sym = sym)
    (hfn_ty : fnTy.unqual = .fnPtr spec.retTy ptys spec.variadic)
    (hptys_eq : ptys.map CTy.unqual = spec.paramTys.map CTy.unqual)
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hcont : ∀ v ty s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K v ty s' mv' mh' →
      W Q (.running (.expr (.ret (.rval v ty) fs) ctx mods') env blks m' s'.os k)) :
    ∀ sCall sArgs argVals mArgs,
      Refines prog.tags baseEnv cur outer sArgs env blks mArgs →
      Sem.stepDet prog cfg sCall = some (.callFn sym fnTy argVals fs ctx env blks mArgs sArgs.os k) →
      (match Sem.coerceCallArgs sArgs.mem spec.paramTys spec.variadic argVals with
        | some coerced =>
          spec.pre sArgs.mem sArgs.os coerced ∧
          ∀ rv m' os', spec.post sArgs.mem sArgs.os coerced rv m' os' →
            K rv spec.retTy { sArgs with mem := m', os := os' } [] []
        | none => False) →
      W Q sCall := by
  intro sCall sArgs argVals mArgs hrA hdet hpost_vc
  cases hco : Sem.coerceCallArgs sArgs.mem spec.paramTys spec.variadic argVals with
  | none => simp [hco] at hpost_vc
  | some coerced =>
    simp only [hco] at hpost_vc
    have hco_m := hrA.coerceCallArgs_mem hco
    have hregs_lt : ∀ b ∈ allRegBlks cur outer, b < mArgs.nextBlock :=
      fun b hb => hrA.reg_lt_nextBlock hb
    have hregs_stk : ∀ b ∈ allRegBlks cur outer, ∃ blk, mArgs.blocks b = some blk ∧ blk.kind = .stack := by
      intro b hb
      obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hb
      obtain ⟨blk0, hm0, hk0, _⟩ := hrA.regs_match.blocks_some hsl
      exact ⟨blk0, hm0, hk0⟩
    have hpre_m : spec.pre mArgs sArgs.os coerced :=
      spec.pre_mono (allRegBlks cur outer) hrA.nextBlock_le
        (fun b hb => hrA.slots_absent b hb) hrA.blocks_agree hregs_lt hregs_stk hpost_vc.1
    refine hcs hsp hsym_eq hdet hfn_ty hptys_eq hco_m hpre_m
      (fun rv m_after os' hsp_post => ?_)
    obtain ⟨hnext, hregs_stay, hstack_stay⟩ := spec.post_stack (allRegBlks cur outer) hrA.nextBlock_le
      (fun b hb => hrA.slots_absent b hb) hrA.blocks_agree hregs_lt hregs_stk hpost_vc.1 hsp_post
    have hregs_after : ∀ b ∈ allRegBlks cur outer, ∀ blk, mArgs.blocks b = some blk →
        m_after.blocks b = some blk := by
      intro b hb blk hbm
      obtain ⟨sl, hsl, hblk_eq⟩ := List.mem_map.mp hb
      obtain ⟨blk0, hm0, hk0, _⟩ := hrA.regs_match.blocks_some hsl
      rw [hblk_eq] at hm0
      rw [hbm] at hm0; cases hm0
      exact hregs_stay b hb blk hbm hk0
    have hr_after := hrA.after_call (os' := os') hregs_after hstack_stay
    have hdrop_post := spec.post_drop (allRegBlks cur outer) hrA.nextBlock_le
      (fun b hb => hrA.slots_absent b hb) hrA.blocks_agree hregs_lt hregs_stk hpost_vc.1 hsp_post
    exact hcont rv spec.retTy
      { sArgs with mem := dropBlks m_after (allRegBlks cur outer), os := os' }
      [] [] m_after [] hr_after (ModsOK.nil cur outer [] [])
      (hpost_vc.2 rv _ os' hdrop_post)

private theorem vcExprR_incDec_lval {prog : Prog} {cfg : PointerConfig} {contracts : ContractEnv}
    {baseEnv : Env} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {op : IncDecOp} {lhs : CExpr} {K}
    (hnonreg : ¬ ∃ x p, lhs = .var x ∧ s.regs.lookup x = some p) :
    vcExprR prog cfg contracts baseEnv s mv mh (.incDec op lhs) K →
      vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
        vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 b off lty K := by
  cases lhs with
  | var x =>
    cases hl : s.regs.lookup x with
    | some p => exact absurd ⟨x, p, rfl, hl⟩ hnonreg
    | none => intro h; (conv at h => unfold vcExprR); simp only [hl] at h; exact h
  | _ => intro h; (conv at h => unfold vcExprR); exact h

private theorem vcExprR_assign_lval {prog : Prog} {cfg : PointerConfig} {contracts : ContractEnv}
    {baseEnv : Env} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {op : AssignOp} {lhs rhs : CExpr} {K}
    (hnonreg : ¬ ∃ x p, lhs = .var x ∧ s.regs.lookup x = some p) :
    vcExprR prog cfg contracts baseEnv s mv mh (.assign op lhs rhs) K →
      vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
        vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
          vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K := by
  cases lhs with
  | var x =>
    cases hl : s.regs.lookup x with
    | some p => exact absurd ⟨x, p, rfl, hl⟩ hnonreg
    | none => intro h; (conv at h => unfold vcExprR); simp only [hl] at h; exact h
  | _ => intro h; (conv at h => unfold vcExprR); exact h

private theorem vcExprDiscard_assign_lval {prog : Prog} {cfg : PointerConfig} {contracts : ContractEnv}
    {baseEnv : Env} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {op : AssignOp} {lhs rhs : CExpr} {K}
    (hnonreg : ¬ ∃ x p, lhs = .var x ∧ s.regs.lookup x = some p) :
    vcExprDiscard prog cfg contracts baseEnv s mv mh (.assign op lhs rhs) K →
      vcExprL prog cfg contracts baseEnv s mv mh lhs fun b off lty s1 mv1 mh1 =>
        if isAggTy lty then
          op = .eq ∧
          vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
            vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
        else
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3 := by
  cases lhs with
  | var x =>
    cases hl : s.regs.lookup x with
    | some p => exact absurd ⟨x, p, rfl, hl⟩ hnonreg
    | none => intro h; (conv at h => unfold vcExprDiscard); simp only [hl] at h; exact h
  | _ => intro h; (conv at h => unfold vcExprDiscard); exact h

private inductive ExprWorkKind where
  | lval
  | rval
  | agg
  | discard
  | callArgs

private noncomputable def exprWorkMeasure : (Σ k : ExprWorkKind, match k with
    | .callArgs => List CExpr
    | _ => CExpr) → Nat × Nat
  | ⟨.lval, e⟩ => (sizeOf e, 0)
  | ⟨.rval, e⟩ => (sizeOf e, 0)
  | ⟨.agg, e⟩ => (sizeOf e, 0)
  | ⟨.discard, e⟩ => (sizeOf e, 1)
  | ⟨.callArgs, es⟩ => (sizeOf es, 0)

private theorem vcExpr_sound_aux_gen {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig)
    (W : (Val → Mem → OSState → Prop) → RunState → Prop)
    (hrules : WPRules prog cfg ext W)
    (contracts : ContractEnv) (hcs : CallContractsSound prog cfg W contracts)
    (baseEnv : Env) (Q : Val → Mem → OSState → Prop) (cur : FrameScope) (outer : List FrameScope)
    (env : Env) (blks : List BlockId) (ctx : ExprCtx) (k : Cont) :
    (w : Σ wk : ExprWorkKind, match wk with | .callArgs => List CExpr | _ => CExpr) →
      match w with
      | ⟨.lval, e⟩ =>
        ∀ s mv mh m mods fs K,
          Refines prog.tags baseEnv cur outer s env blks m →
          ModsOK cur outer mv mh mods →
          vcExprL prog cfg contracts baseEnv s mv mh e K →
          (∀ b off ty s' mv' mh' m' mods',
            Refines prog.tags baseEnv cur outer s' env blks m' →
            ModsOK cur outer mv' mh' mods' →
            K b off ty s' mv' mh' →
            W Q (.running (.expr (.ret (.lval b off ty) fs) ctx mods') env blks m' s'.os k)) →
          W Q (.running (.expr (.eval .lval e fs) ctx mods) env blks m s.os k)
      | ⟨.rval, e⟩ =>
        ∀ s mv mh m mods fs K,
          Refines prog.tags baseEnv cur outer s env blks m →
          ModsOK cur outer mv mh mods →
          vcExprR prog cfg contracts baseEnv s mv mh e K →
          (∀ v ty s' mv' mh' m' mods',
            Refines prog.tags baseEnv cur outer s' env blks m' →
            ModsOK cur outer mv' mh' mods' →
            K v ty s' mv' mh' →
            W Q (.running (.expr (.ret (.rval v ty) fs) ctx mods') env blks m' s'.os k)) →
          W Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k)
      | ⟨.agg, e⟩ =>
        ∀ s mv mh m mods fs K,
          Refines prog.tags baseEnv cur outer s env blks m →
          ModsOK cur outer mv mh mods →
          vcExprAgg prog cfg contracts baseEnv s mv mh e K →
          (∀ bs ty s' mv' mh' m' mods',
            Refines prog.tags baseEnv cur outer s' env blks m' →
            ModsOK cur outer mv' mh' mods' →
            K bs ty s' mv' mh' →
            W Q (.running (.expr (.ret (.structVal bs ty) fs) ctx mods') env blks m' s'.os k)) →
          W Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k)
      | ⟨.discard, e⟩ =>
        ∀ s mv mh m mods fs K,
          Refines prog.tags baseEnv cur outer s env blks m →
          ModsOK cur outer mv mh mods →
          vcExprDiscard prog cfg contracts baseEnv s mv mh e K →
          (∀ res s' mv' mh' m' mods',
            Refines prog.tags baseEnv cur outer s' env blks m' →
            ModsOK cur outer mv' mh' mods' →
            K s' mv' mh' →
            W Q (.running (.expr (.ret res fs) ctx mods') env blks m' s'.os k)) →
          W Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k)
      | ⟨.callArgs, args⟩ =>
        ∀ arg0 rest, args = arg0 :: rest →
        ∀ sym fnTy done s mv mh m mods fs K,
          Refines prog.tags baseEnv cur outer s env blks m →
          ModsOK cur outer mv mh mods →
          vcCallArgs prog cfg contracts baseEnv s mv mh (arg0 :: rest) done K →
          (∀ sCall sArgs argVals mArgs,
            Refines prog.tags baseEnv cur outer sArgs env blks mArgs →
            Sem.stepDet prog cfg sCall = some (.callFn sym fnTy argVals fs ctx env blks mArgs sArgs.os k) →
            K sArgs argVals →
            W Q sCall) →
          W Q
            (.running (.expr (.eval .rval arg0 (.callArgF sym fnTy done rest :: fs)) ctx mods) env blks m s.os k)
  | ⟨.lval, e⟩ => by
    intro s mv mh m mods fs K hr hm hvc hcont
    cases e with
    | paren e1 =>
      unfold vcExprL at hvc
      exact hrules.of_exprPure rfl
        (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.lval, e1⟩ s mv mh m mods fs K hr hm hvc hcont)
    | var x =>
      unfold vcExprL at hvc
      rcases hvc with ⟨hreg_none, hlookup⟩
      have henv_match := vcExpr_var_lookup_nonreg hr hreg_none
      cases hstk : s.stack.lookup x with
      | some p =>
        simp only [hstk] at hlookup henv_match
        exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv_match])
          (hcont p.1 0 p.2 s mv mh m mods hr hm hlookup)
      | none =>
        simp only [hstk] at hlookup henv_match
        cases hbase : baseEnv.lookup x with
        | none => simp [hbase] at hlookup
        | some p =>
          simp only [hbase] at hlookup
          have henv : env.lookup x = some p := henv_match.trans hbase
          exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv])
            (hcont p.1 0 p.2 s mv mh m mods hr hm hlookup)
    | deref e1 =>
      unfold vcExprL at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, e1⟩ s mv mh m mods (.derefF .lval :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      cases p <;> simp only at hk1
      all_goals try cases hk1
      next el b off =>
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.derefF .lval :: fs)) =
            some (.ret (.lval b off el) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hu, Sem.readPlace]
        exact hrules.of_exprPure hstep (hcont b off el s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
    | index base idx =>
      unfold vcExprL at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.indexBaseF .lval idx :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, idx⟩ s1 mv1 mh1 m1 mods1 (.indexIdxF .lval p pty :: fs) _ hr1 hm1 hk1 ?_
      intro iv ty_iv s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      cases hu : pty.unqual <;> simp only [hu] at hk2
      all_goals try cases hk2
      cases hvi : Sem.valAsInt? iv with
      | none => simp [hvi] at hk2
      | some ip =>
        simp only [hvi] at hk2
        next el =>
        cases hadd : Sem.evalPtrAdd cfg prog.tags s2.mem p el ip.2 with
        | none => simp [hadd] at hk2
        | some pv =>
          cases pv <;> simp only [hadd] at hk2
          all_goals try cases hk2
          next b off =>
          have hadd_m := hr2.evalPtrAdd_mem hadd
          have hstep : Sem.stepExprPure prog cfg env m2 mods2
              (.ret (.rval iv ty_iv) (.indexIdxF .lval p pty :: fs)) =
              some (.ret (.lval b off el) fs, m2, mods2) := by
            unfold Sem.stepExprPure; simp [hu, hvi, hadd_m, Sem.readPlace]
          exact hrules.of_exprPure hstep (hcont b off el s2 mv2 mh2 m2 mods2 hr2 hm2 hk2)
    | member base fld =>
      unfold vcExprL at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.lval, base⟩ s mv mh m mods (.memberF .lval fld :: fs) _ hr hm hvc ?_
      intro b off sty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off sty) (.memberF .lval fld :: fs)) =
            some (.ret (.lval b (Int64.ofInt (off.toInt + fp.1)) fp.2) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hfl, Sem.readPlace]
        exact hrules.of_exprPure hstep (hcont b (Int64.ofInt (off.toInt + fp.1)) fp.2 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
    | arrow base fld =>
      unfold vcExprL at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.arrowF .lval fld :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      cases p <;> simp only at hk1
      all_goals try cases hk1
      next sty b off =>
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.arrowF .lval fld :: fs)) =
            some (.ret (.lval b (Int64.ofInt (off.toInt + fp.1)) fp.2) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hu, hfl, Sem.readPlace]
        exact hrules.of_exprPure hstep (hcont b (Int64.ofInt (off.toInt + fp.1)) fp.2 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
    | lit _ _ _ _ _ | strLit _ | sizeOfTy _ | sizeOfExpr _ | unary _ _ | binary _ _ _
    | logAnd _ _ | logOr _ _ | cond _ _ _ | comma _ _ | cast _ _ | addrOf _
    | assign _ _ _ | incDec _ _ | call _ _ | vaStart _ _ | vaEnd _ =>
      unfold vcExprL at hvc; cases hvc
  | ⟨.rval, e⟩ => by
    intro s mv mh m mods fs K hr hm hvc hcont
    cases e with
    | paren e1 =>
      unfold vcExprR at hvc
      exact hrules.of_exprPure rfl
        (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.rval, e1⟩ s mv mh m mods fs K hr hm hvc hcont)
    | lit val lk suf rad sym? =>
      unfold vcExprR at hvc
      exact hrules.of_exprPure rfl (hcont _ _ s mv mh m mods hr hm hvc)
    | strLit str =>
      unfold vcExprR at hvc
      rcases hvc with ⟨hsz, halloc_vc⟩
      refine hrules.of_strLit hsz rfl fun base bid m' halloc => ?_
      have hle : s.mem.nextBlock ≤ bid :=
        Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
      have hr' := hr.alloc_strLit hsz halloc hle
      exact hcont (.ptr bid 0) (.ptr (.const_ (.int .i8)))
        { s with mem := (allocAt s.mem bid hle (str.utf8ByteSize + 1) 1 .ro .global base
          (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)) }
        mv mh m' mods hr' hm (halloc_vc bid hle base)
    | sizeOfTy ty =>
      unfold vcExprR at hvc
      exact hrules.of_exprPure rfl (hcont _ _ s mv mh m mods hr hm hvc)
    | sizeOfExpr e1 =>
      unfold vcExprR at hvc
      cases het : Sem.exprType? prog.tags (s.typeEnv baseEnv) prog.fnProtos e1 with
      | none => simp [het] at hvc
      | some ty =>
        simp only [het] at hvc
        rw [hr.exprType?_eq e1] at het
        have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.sizeOfExpr e1) fs) =
            some (.ret (.rval (.int .u64 (BitVec.ofNat 64 (sizeofTy prog.tags ty))) (.int .u64)) fs, m, mods) := by
          unfold Sem.stepExprPure; simp [het]
        exact hrules.of_exprPure hstep (hcont _ _ s mv mh m mods hr hm hvc)
    | var x =>
      unfold vcExprR at hvc
      cases hl : s.regs.lookup x with
      | some p =>
        rcases p with ⟨v, ty⟩
        simp only [hl] at hvc
        rcases hvc with ⟨hscal, hnot_mv, hne_undef, hk⟩
        obtain ⟨sl, hsl, hname, hty, henv, hrd⟩ := hr.lookup_reg hl
        have hnc : mods.conflicts sl.blk 0 (sizeofTy prog.tags ty) = false :=
          hm.no_conflict_var (nodup_regBlks_of_nodup hr.nodup_blks) hsl (hname ▸ hnot_mv) 0 (sizeofTy prog.tags ty)
        have hrd_place : Sem.readPlace prog.tags m mods .rval sl.blk 0 ty = some (.rval v ty.decay) := by
          unfold Sem.readPlace
          unfold isScalarPlaceTy at hscal
          cases hu : ty.unqual <;> simp [hu] at hscal
          all_goals simp only [hnc, Bool.not_false, guard_true, hrd hne_undef,
            bind, Option.bind, Option.map_some]
        have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
            some (.ret (.rval v ty.decay) fs, m, mods) := by
          unfold Sem.stepExprPure
          simp only [henv, hrd_place, Option.map_some]
        exact hrules.of_exprPure hstep (hcont v ty.decay s mv mh m mods hr hm hk)
      | none =>
        simp only [hl] at hvc
        have henv_match := vcExpr_var_lookup_nonreg hr hl
        cases hstk : s.stack.lookup x with
        | some p =>
          simp only [hstk] at hvc henv_match
          obtain ⟨rv, hrd_place, hk⟩ := vcReadHeapPlace_sound hr hm hvc
          have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
              some (.ret (.rval rv p.2.decay) fs, m, mods) := by
            unfold Sem.stepExprPure; simp only [henv_match, hrd_place, Option.map_some]
          exact hrules.of_exprPure hstep (hcont rv p.2.decay s mv mh m mods hr hm hk)
        | none =>
          simp only [hstk] at hvc henv_match
          cases hbase : baseEnv.lookup x with
          | some p =>
            simp only [hbase] at hvc
            have henv : env.lookup x = some p := henv_match.trans hbase
            obtain ⟨rv, hrd_place, hk⟩ := vcReadHeapPlace_sound hr hm hvc
            have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
                some (.ret (.rval rv p.2.decay) fs, m, mods) := by
              unfold Sem.stepExprPure; simp only [henv, hrd_place, Option.map_some]
            exact hrules.of_exprPure hstep (hcont rv p.2.decay s mv mh m mods hr hm hk)
          | none =>
            simp only [hbase] at hvc
            have henv : env.lookup x = none := henv_match.trans hbase
            cases hec : Sem.enumConst? prog.tags x with
            | some ev =>
              simp only [hec] at hvc
              have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
                  some (.ret (.rval (Sem.ofIntCast .i32 ev) (.int .i32)) fs, m, mods) := by
                unfold Sem.stepExprPure; simp [henv, hec]
              exact hrules.of_exprPure hstep (hcont _ _ s mv mh m mods hr hm hvc)
            | none =>
              simp only [hec] at hvc
              cases hfp : prog.fnProtos x with
              | none => simp [hfp] at hvc
              | some p =>
                rcases p with ⟨r, ps, va⟩
                simp only [hfp] at hvc
                have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
                    some (.ret (.rval (.fnPtr x) (.fnPtr r ps va)) fs, m, mods) := by
                  unfold Sem.stepExprPure; simp [henv, hec, hfp]
                exact hrules.of_exprPure hstep (hcont _ _ s mv mh m mods hr hm hvc)
    | unary op e1 =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, e1⟩ s mv mh m mods (.unaryF op :: fs) _ hr hm hvc ?_
      intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      obtain ⟨rv, rt, hev, hkr⟩ := vcUnary_sound hk1
      have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.unaryF op :: fs)) =
          some (.ret (.rval rv rt) fs, m1, mods1) := by
        unfold Sem.stepExprPure; simp [hev]
      exact hrules.of_exprPure hstep (hcont rv rt s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
    | cast target e1 =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, e1⟩ s mv mh m mods (.castF target :: fs) _ hr hm hvc ?_
      intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      obtain ⟨cv, hcast, hkr⟩ := vcCast_sound hr1 hk1
      have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.castF target :: fs)) =
          some (.ret (.rval cv target) fs, m1, mods1) := by
        unfold Sem.stepExprPure; simp [hcast]
      exact hrules.of_exprPure hstep (hcont cv target s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
    | binary op l r =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, l⟩ s mv mh m mods (.binLhsF op r :: fs) _ hr hm hvc ?_
      intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, r⟩ s1 mv1 mh1 m1 mods1 (.binRhsF op v1 t1 :: fs) _ hr1 hm1 hk1 ?_
      intro v2 t2 s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      obtain ⟨rv, rt, hbin, hkr⟩ := vcBinary_sound hr2 hk2
      have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.binRhsF op v1 t1 :: fs)) =
          some (.ret (.rval rv rt) fs, m2, mods2) := by
        unfold Sem.stepExprPure; simp [hbin]
      exact hrules.of_exprPure hstep (hcont rv rt s2 mv2 mh2 m2 mods2 hr2 hm2 hkr)
    | logAnd l r =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, l⟩ s mv mh m mods (.logAndF r :: fs) _ hr hm hvc ?_
      intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      obtain ⟨b1, hb1, ht1, hf1⟩ := vcBranch_elim hk1
      cases b1
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logAndF r :: fs)) =
            some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont (.int .i32 0) (.int .i32) s1 mv1 mh1 m1 mods1 hr1 hm1 (hf1 rfl))
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logAndF r :: fs)) =
            some (.eval .rval r (.logAndEndF :: fs), m1, []) := by
          unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
        refine hrules.of_exprPure hstep ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.rval, r⟩ s1 [] [] m1 [] (.logAndEndF :: fs) _ hr1 (ModsOK.nil cur outer [] []) (ht1 rfl) ?_
        intro v2 t2 s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
        obtain ⟨b2, hb2, ht2, hf2⟩ := vcBranch_elim hk2
        cases b2
        · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logAndEndF :: fs)) =
              some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m2, mods2) := by
            unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
          exact hrules.of_exprPure hstep2 (hcont (.int .i32 0) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (hf2 rfl))
        · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logAndEndF :: fs)) =
              some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m2, mods2) := by
            unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
          exact hrules.of_exprPure hstep2 (hcont (.int .i32 1) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (ht2 rfl))
    | logOr l r =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, l⟩ s mv mh m mods (.logOrF r :: fs) _ hr hm hvc ?_
      intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      obtain ⟨b1, hb1, ht1, hf1⟩ := vcBranch_elim hk1
      cases b1
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logOrF r :: fs)) =
            some (.eval .rval r (.logOrEndF :: fs), m1, []) := by
          unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
        refine hrules.of_exprPure hstep ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.rval, r⟩ s1 [] [] m1 [] (.logOrEndF :: fs) _ hr1 (ModsOK.nil cur outer [] []) (hf1 rfl) ?_
        intro v2 t2 s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
        obtain ⟨b2, hb2, ht2, hf2⟩ := vcBranch_elim hk2
        cases b2
        · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logOrEndF :: fs)) =
              some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m2, mods2) := by
            unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
          exact hrules.of_exprPure hstep2 (hcont (.int .i32 0) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (hf2 rfl))
        · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logOrEndF :: fs)) =
              some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m2, mods2) := by
            unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
          exact hrules.of_exprPure hstep2 (hcont (.int .i32 1) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (ht2 rfl))
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logOrF r :: fs)) =
            some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont (.int .i32 1) (.int .i32) s1 mv1 mh1 m1 mods1 hr1 hm1 (ht1 rfl))
    | cond c t f =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, c⟩ s mv mh m mods (.condF t f :: fs) _ hr hm hvc ?_
      intro vc tc s1 _ _ m1 mods1 hr1 _ hk1
      obtain ⟨bc, hbc, ht, hf⟩ := vcBranch_elim hk1
      cases bc
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
            some (.eval .rval f fs, m1, []) := by
          unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep
          (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.rval, f⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) (hf rfl) hcont)
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
            some (.eval .rval t fs, m1, []) := by
          unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep
          (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.rval, t⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) (ht rfl) hcont)
    | comma l r =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.discard, l⟩ s mv mh m mods (.commaF r :: fs) _ hr hm hvc ?_
      intro res s1 _ _ m1 _ hr1 _ hk1
      refine hrules.of_exprPure (by cases res <;> rfl) ?_
      exact vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, r⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) hk1 hcont
    | addrOf l =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.lval, l⟩ s mv mh m mods (.addrOfF :: fs) _ hr hm hvc ?_
      intro b off ty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      exact hrules.of_exprPure rfl (hcont (.ptr b off) (.ptr ty) s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
    | deref e1 =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, e1⟩ s mv mh m mods (.derefF .rval :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      · cases p <;> simp only at hk1
        all_goals try cases hk1
        next el b off =>
        obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) =
            some (.ret (.rval rv el.decay) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hu, hrd_place]
        exact hrules.of_exprPure hstep (hcont rv el.decay s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
      · cases p <;> simp only at hk1
        all_goals try cases hk1
        next rt ps va sym =>
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.fnPtr sym) pty) (.derefF .rval :: fs)) =
            some (.ret (.rval (.fnPtr sym) (.fnPtr rt ps va)) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hu]
        exact hrules.of_exprPure hstep (hcont (.fnPtr sym) (.fnPtr rt ps va) s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
    | index base idx =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.indexBaseF .rval idx :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, idx⟩ s1 mv1 mh1 m1 mods1 (.indexIdxF .rval p pty :: fs) _ hr1 hm1 hk1 ?_
      intro iv ty_iv s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      cases hu : pty.unqual <;> simp only [hu] at hk2
      all_goals try cases hk2
      cases hvi : Sem.valAsInt? iv with
      | none => simp [hvi] at hk2
      | some ip =>
        simp only [hvi] at hk2
        next el =>
        cases hadd : Sem.evalPtrAdd cfg prog.tags s2.mem p el ip.2 with
        | none => simp [hadd] at hk2
        | some pv =>
          cases pv <;> simp only [hadd] at hk2
          all_goals try cases hk2
          next b off =>
          have hadd_m := hr2.evalPtrAdd_mem hadd
          obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr2 hm2 hk2
          have hstep : Sem.stepExprPure prog cfg env m2 mods2
              (.ret (.rval iv ty_iv) (.indexIdxF .rval p pty :: fs)) =
              some (.ret (.rval rv el.decay) fs, m2, mods2) := by
            unfold Sem.stepExprPure; simp [hu, hvi, hadd_m, hrd_place]
          exact hrules.of_exprPure hstep (hcont rv el.decay s2 mv2 mh2 m2 mods2 hr2 hm2 hkr)
    | member base fld =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.lval, base⟩ s mv mh m mods (.memberF .rval fld :: fs) _ hr hm hvc ?_
      intro b off sty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off sty) (.memberF .rval fld :: fs)) =
            some (.ret (.rval rv fp.2.decay) fs, m1, mods1) := by
          unfold Sem.stepExprPure
          simp only [hfl, hrd_place, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont rv fp.2.decay s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
    | arrow base fld =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.arrowF .rval fld :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      cases p <;> simp only at hk1
      all_goals try cases hk1
      next sty b off =>
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) =
            some (.ret (.rval rv fp.2.decay) fs, m1, mods1) := by
          unfold Sem.stepExprPure
          simp only [hu, hfl, hrd_place, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont rv fp.2.decay s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
    | incDec op lhs =>
      by_cases hreg : ∃ x p, lhs = .var x ∧ s.regs.lookup x = some p
      · rcases hreg with ⟨x, ⟨oldV, lty⟩, rfl, hl⟩
        unfold vcExprR at hvc
        dsimp only at hvc
        simp only [hl] at hvc
        obtain ⟨rv, cv, m', b, hs1, hs2, hs3, hr', hm', hk'⟩ :=
          vcIncDecReg_steps_sound hr hm hl fs hvc
        exact hrules.of_exprPure hs1 (hrules.of_exprPure hs2 (hrules.of_exprPure hs3
          (hcont rv lty { s with regs := s.regs.set x cv lty } (x :: mv) mh m'
            (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) hr' hm' hk')))
      · have hvc' := vcExprR_incDec_lval hreg hvc
        refine hrules.of_exprPure rfl ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.lval, lhs⟩ s mv mh m mods (.incDecF op :: fs) _ hr hm hvc' ?_
        intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        obtain ⟨rv, rt, s2, mv2, mh2, m2, mods2, hstep, hs_os, hr2, hm2, hk2⟩ :=
          vcIncDecPlaceFinish_sound hr1 hm1 hk1
        rw [← hs_os]
        exact hrules.of_exprPure hstep (hcont rv rt s2 mv2 mh2 m2 mods2 hr2 hm2 hk2)
    | assign op lhs rhs =>
      by_cases hreg : ∃ x p, lhs = .var x ∧ s.regs.lookup x = some p
      · rcases hreg with ⟨x, ⟨v0, lty0⟩, rfl, hl0⟩
        unfold vcExprR at hvc
        simp only [hl0] at hvc
        obtain ⟨sl0, hsl0, hname0, _, henv0, _⟩ := hr.lookup_reg hl0
        have h1 : Sem.stepExprPure prog cfg env m mods (.eval .lval (.var x) (.assignLhsF op rhs :: fs)) =
            some (.ret (.lval sl0.blk 0 lty0) (.assignLhsF op rhs :: fs), m, mods) := by
          unfold Sem.stepExprPure; simp [henv0]
        refine hrules.of_exprPure rfl (hrules.of_exprPure h1 (hrules.of_exprPure rfl ?_))
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.rval, rhs⟩ s mv mh m mods (.assignRhsF op sl0.blk 0 lty0 :: fs) _ hr hm hvc ?_
        intro rval rty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        obtain ⟨cv, m2, hstep, hr2, hm2, hk2⟩ :=
          vcAssignReg_finish_sound hsl0 hname0 henv0 hr1 hm1 hk1
        exact hrules.of_exprPure hstep
          (hcont cv lty0 { s1 with regs := s1.regs.set x cv lty0 } (x :: mv1) mh1 m2
            (⟨sl0.blk, 0, sizeofTy prog.tags lty0⟩ :: mods1) hr2 hm2 hk2)
      · have hvc' := vcExprR_assign_lval hreg hvc
        refine hrules.of_exprPure rfl ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.lval, lhs⟩ s mv mh m mods (.assignLhsF op rhs :: fs) _ hr hm hvc' ?_
        intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        refine hrules.of_exprPure rfl ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.rval, rhs⟩ s1 mv1 mh1 m1 mods1 (.assignRhsF op b off lty :: fs) _ hr1 hm1 hk1 ?_
        intro rval rty s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
        obtain ⟨rv, rt, s3, mv3, mh3, m3, mods3, hstep_rhs, hs_os, hr3, hm3, hk3⟩ :=
          vcAssignPlaceFinish_sound hr2 hm2 hk2
        rw [← hs_os]
        exact hrules.of_exprPure hstep_rhs (hcont rv rt s3 mv3 mh3 m3 mods3 hr3 hm3 hk3)
    | call fn args =>
      unfold vcExprR at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, fn⟩ s mv mh m mods (.callFnF args :: fs) _ hr hm hvc ?_
      intro fnV fnTy sFn mvFn mhFn mFn modsFn hrFn hmFn hkFn
      cases fnV
      all_goals try cases hkFn
      next sym =>
        cases hfn_ty : fnTy.unqual <;> simp only [hfn_ty] at hkFn
        all_goals try cases hkFn
        next rt ptys va =>
      cases hsp : contracts sym with
      | none => simp [hsp] at hkFn
      | some spec =>
        simp only [hsp] at hkFn
        rcases hkFn with ⟨hsym_eq, hrt_eq, hptys_eq, hva_eq, hargs_vc⟩
        subst hrt_eq hva_eq
        let hcall_fn := vcCallArgs_finish_sound hcs hsp hsym_eq hfn_ty hptys_eq hcont
        cases args with
        | nil =>
          unfold vcCallArgs at hargs_vc
          exact hcall_fn _ sFn [] mFn hrFn rfl hargs_vc
        | cons arg0 rest =>
          refine hrules.of_exprPure rfl ?_
          exact vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.callArgs, arg0 :: rest⟩ arg0 rest rfl sym fnTy []
            sFn mvFn mhFn mFn modsFn fs _ hrFn hmFn hargs_vc hcall_fn
    | vaStart ap lastParam =>
      unfold vcExprR at hvc
      obtain ⟨m_clean', m', hstep, hr', hk'⟩ := vcVaOp_step_sound hr ap
        (List.replicate (sizeofTy prog.tags .vaList) (.byte 1)) (.vaStart ap lastParam) fs
        (fun _ _ p h1 h2 h3 => by unfold Sem.stepExprPure; simp only [h1, h2, guard_true, h3,
          bind, Option.bind, pure, Pure.pure]) hvc
      exact hrules.of_exprPure hstep (hcont .void .void { s with mem := m_clean' } mv mh m' mods hr' hm hk')
    | vaEnd ap =>
      unfold vcExprR at hvc
      obtain ⟨m_clean', m', hstep, hr', hk'⟩ := vcVaOp_step_sound hr ap
        (List.replicate (sizeofTy prog.tags .vaList) .undef) (.vaEnd ap) fs
        (fun _ _ p h1 h2 h3 => by unfold Sem.stepExprPure; simp only [h1, h2, guard_true, h3,
          bind, Option.bind, pure, Pure.pure]) hvc
      exact hrules.of_exprPure hstep (hcont .void .void { s with mem := m_clean' } mv mh m' mods hr' hm hk')
  | ⟨.agg, e⟩ => by
    intro s mv mh m mods fs K hr hm hvc hcont
    cases e with
    | paren e1 =>
      unfold vcExprAgg at hvc
      exact hrules.of_exprPure rfl
        (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.agg, e1⟩ s mv mh m mods fs K hr hm hvc hcont)
    | var x =>
      unfold vcExprAgg at hvc
      rcases hvc with ⟨hreg_none, hlookup⟩
      have henv_match := vcExpr_var_lookup_nonreg hr hreg_none
      cases hstk : s.stack.lookup x with
      | some p =>
        simp only [hstk] at hlookup henv_match
        obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr hm hlookup
        have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
            some (.ret (.structVal bs p.2) fs, m, mods) := by
          unfold Sem.stepExprPure; simp [henv_match, hrd]
        exact hrules.of_exprPure hstep (hcont bs p.2 s mv mh m mods hr hm hk)
      | none =>
        simp only [hstk] at hlookup henv_match
        cases hbase : baseEnv.lookup x with
        | none => simp [hbase] at hlookup
        | some p =>
          simp only [hbase] at hlookup
          have henv : env.lookup x = some p := henv_match.trans hbase
          obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr hm hlookup
          have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
              some (.ret (.structVal bs p.2) fs, m, mods) := by
            unfold Sem.stepExprPure; simp [henv, hrd]
          exact hrules.of_exprPure hstep (hcont bs p.2 s mv mh m mods hr hm hk)
    | deref e1 =>
      unfold vcExprAgg at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, e1⟩ s mv mh m mods (.derefF .rval :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      cases p with
      | ptr b off =>
        next el =>
        obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) =
            some (.ret (.structVal bs el) fs, m1, mods1) := by
          unfold Sem.stepExprPure
          simp only [hu, hrd, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont bs el s1 mv1 mh1 m1 mods1 hr1 hm1 hk)
      | _ => cases hk1
    | index base idx =>
      unfold vcExprAgg at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.indexBaseF .rval idx :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, idx⟩ s1 mv1 mh1 m1 mods1 (.indexIdxF .rval p pty :: fs) _ hr1 hm1 hk1 ?_
      intro iv ty_iv s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      cases hu : pty.unqual <;> simp only [hu] at hk2
      all_goals try cases hk2
      cases hvi : Sem.valAsInt? iv with
      | none => simp [hvi] at hk2
      | some ip =>
        simp only [hvi] at hk2
        next el =>
        cases hadd : Sem.evalPtrAdd cfg prog.tags s2.mem p el ip.2 with
        | none => simp [hadd] at hk2
        | some pv =>
          cases pv with
          | ptr b off =>
            simp only [hadd] at hk2
            have hadd_m := hr2.evalPtrAdd_mem hadd
            obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr2 hm2 hk2
            have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval iv ty_iv) (.indexIdxF .rval p pty :: fs)) =
                some (.ret (.structVal bs el) fs, m2, mods2) := by
              unfold Sem.stepExprPure
              simp only [hu, hvi, hadd_m, hrd, bind, Option.bind, pure, Pure.pure]
            exact hrules.of_exprPure hstep (hcont bs el s2 mv2 mh2 m2 mods2 hr2 hm2 hk)
          | _ => simp only [hadd] at hk2
    | member base fld =>
      unfold vcExprAgg at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.lval, base⟩ s mv mh m mods (.memberF .rval fld :: fs) _ hr hm hvc ?_
      intro b off sty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off sty) (.memberF .rval fld :: fs)) =
            some (.ret (.structVal bs fp.2) fs, m1, mods1) := by
          unfold Sem.stepExprPure
          simp only [hfl, hrd, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont bs fp.2 s1 mv1 mh1 m1 mods1 hr1 hm1 hk)
    | arrow base fld =>
      unfold vcExprAgg at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.arrowF .rval fld :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      cases p with
      | ptr b off =>
        next sty =>
        cases hfl : fieldLayout? prog.tags sty fld with
        | none => simp [hfl] at hk1
        | some fp =>
          simp only [hfl] at hk1
          obtain ⟨bs, hrd, hk⟩ := vcReadAggPlace_sound hr1 hm1 hk1
          have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) =
              some (.ret (.structVal bs fp.2) fs, m1, mods1) := by
            unfold Sem.stepExprPure
            simp only [hu, hfl, hrd, bind, Option.bind, pure, Pure.pure]
          exact hrules.of_exprPure hstep (hcont bs fp.2 s1 mv1 mh1 m1 mods1 hr1 hm1 hk)
      | _ => cases hk1
    | cond c t f =>
      unfold vcExprAgg at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, c⟩ s mv mh m mods (.condF t f :: fs) _ hr hm hvc ?_
      intro vc tc s1 _ _ m1 mods1 hr1 _ hk1
      obtain ⟨bc, hbc, ht, hf⟩ := vcBranch_elim hk1
      cases bc
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
            some (.eval .rval f fs, m1, []) := by
          unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep
          (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.agg, f⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) (hf rfl) hcont)
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
            some (.eval .rval t fs, m1, []) := by
          unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep
          (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.agg, t⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) (ht rfl) hcont)
    | comma l r =>
      unfold vcExprAgg at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.discard, l⟩ s mv mh m mods (.commaF r :: fs) _ hr hm hvc ?_
      intro res s1 _ _ m1 _ hr1 _ hk1
      refine hrules.of_exprPure (by cases res <;> rfl) ?_
      exact vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.agg, r⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) hk1 hcont
    | assign op lhs rhs =>
      cases op with
      | eq =>
        unfold vcExprAgg at hvc
        simp only [beq_self_eq_true, ↓reduceIte] at hvc
        refine hrules.of_exprPure rfl ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.lval, lhs⟩ s mv mh m mods (.assignLhsF .eq rhs :: fs) _ hr hm hvc ?_
        intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        refine hrules.of_exprPure rfl ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.agg, rhs⟩ s1 mv1 mh1 m1 mods1 (.assignRhsF .eq b off lty :: fs) _ hr1 hm1 hk1 ?_
        intro bs sty s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
        obtain ⟨s3, mv3, mh3, m3, mods3, hstep, hs_os, hr3, hm3, hk3⟩ :=
          vcWriteAggPlace_sound hr2 hm2 hk2
        rw [← hs_os]
        exact hrules.of_exprPure hstep (hcont bs lty s3 mv3 mh3 m3 mods3 hr3 hm3 hk3)
      | _ => unfold vcExprAgg at hvc; cases hvc
    | lit _ _ _ _ _ | strLit _ | sizeOfTy _ | sizeOfExpr _ | unary _ _ | binary _ _ _
    | logAnd _ _ | logOr _ _ | cast _ _ | addrOf _ | incDec _ _ | call _ _ | vaStart _ _ | vaEnd _ =>
      unfold vcExprAgg at hvc; cases hvc
  | ⟨.discard, e⟩ => by
    intro s mv mh m mods fs K hr hm hvc hcont
    cases e with
    | paren e1 =>
      unfold vcExprDiscard at hvc
      exact hrules.of_exprPure rfl
        (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.discard, e1⟩ s mv mh m mods fs K hr hm hvc hcont)
    | comma l r =>
      unfold vcExprDiscard at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.discard, l⟩ s mv mh m mods (.commaF r :: fs) _ hr hm hvc ?_
      intro res s1 _ _ m1 _ hr1 _ hk1
      refine hrules.of_exprPure (by cases res <;> rfl) ?_
      exact vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.discard, r⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) hk1 hcont
    | cond c t f =>
      unfold vcExprDiscard at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, c⟩ s mv mh m mods (.condF t f :: fs) _ hr hm hvc ?_
      intro vc tc s1 _ _ m1 mods1 hr1 _ hk1
      obtain ⟨bc, hbc, ht, hf⟩ := vcBranch_elim hk1
      cases bc
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
            some (.eval .rval f fs, m1, []) := by
          unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep
          (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.discard, f⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) (hf rfl) hcont)
      · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
            some (.eval .rval t fs, m1, []) := by
          unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep
          (vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.discard, t⟩ s1 [] [] m1 [] fs K hr1 (ModsOK.nil cur outer [] []) (ht rfl) hcont)
    | var x =>
      unfold vcExprDiscard at hvc
      cases hl : s.regs.lookup x with
      | some p =>
        rcases p with ⟨v, ty⟩
        simp only [hl] at hvc
        rcases hvc with ⟨hscal, hnot_mv, hne_undef, hk⟩
        obtain ⟨sl, hsl, hname, hty, henv, hrd⟩ := hr.lookup_reg hl
        have hnc : mods.conflicts sl.blk 0 (sizeofTy prog.tags ty) = false :=
          hm.no_conflict_var (nodup_regBlks_of_nodup hr.nodup_blks) hsl (hname ▸ hnot_mv) 0 (sizeofTy prog.tags ty)
        have hrd_place : Sem.readPlace prog.tags m mods .rval sl.blk 0 ty = some (.rval v ty.decay) := by
          unfold Sem.readPlace; unfold isScalarPlaceTy at hscal
          cases hu : ty.unqual <;> simp [hu] at hscal
          all_goals simp only [hnc, Bool.not_false, guard_true, hrd hne_undef,
            bind, Option.bind, Option.map_some]
        exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv, hrd_place])
          (hcont (.rval v ty.decay) s mv mh m mods hr hm hk)
      | none =>
        simp only [hl] at hvc
        have henv_match := vcExpr_var_lookup_nonreg hr hl
        cases hstk : s.stack.lookup x with
        | some p =>
          simp only [hstk] at hvc henv_match
          obtain ⟨res, hrd_place, hk⟩ := vcReadDiscardPlace_sound hr hm hvc
          exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv_match, hrd_place])
            (hcont res s mv mh m mods hr hm hk)
        | none =>
          simp only [hstk] at hvc henv_match
          cases hbase : baseEnv.lookup x with
          | some p =>
            simp only [hbase] at hvc
            have henv : env.lookup x = some p := henv_match.trans hbase
            obtain ⟨res, hrd_place, hk⟩ := vcReadDiscardPlace_sound hr hm hvc
            exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv, hrd_place])
              (hcont res s mv mh m mods hr hm hk)
          | none =>
            simp only [hbase] at hvc
            have henv : env.lookup x = none := henv_match.trans hbase
            cases hec : Sem.enumConst? prog.tags x with
            | some ev =>
              simp only [hec] at hvc
              exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv, hec])
                (hcont (.rval (Sem.ofIntCast .i32 ev) (.int .i32)) s mv mh m mods hr hm hvc)
            | none =>
              simp only [hec] at hvc
              cases hfp : prog.fnProtos x with
              | none => simp [hfp] at hvc
              | some p =>
                simp only [hfp] at hvc
                exact hrules.of_exprPure (by unfold Sem.stepExprPure; simp [henv, hec, hfp])
                  (hcont (.rval (.fnPtr x) (.fnPtr p.1 p.2.1 p.2.2)) s mv mh m mods hr hm hvc)
    | deref e1 =>
      unfold vcExprDiscard at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, e1⟩ s mv mh m mods (.derefF .rval :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      · cases p <;> simp only at hk1
        all_goals try cases hk1
        next el b off =>
        obtain ⟨res, hrd_place, hk⟩ := vcReadDiscardPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) =
            some (.ret res fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hu, hrd_place]
        exact hrules.of_exprPure hstep (hcont res s1 mv1 mh1 m1 mods1 hr1 hm1 hk)
      · cases p <;> simp only at hk1
        all_goals try cases hk1
        next rt ps va sym =>
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.fnPtr sym) pty) (.derefF .rval :: fs)) =
            some (.ret (.rval (.fnPtr sym) (.fnPtr rt ps va)) fs, m1, mods1) := by
          unfold Sem.stepExprPure; simp [hu]
        exact hrules.of_exprPure hstep (hcont _ s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
    | index base idx =>
      unfold vcExprDiscard at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.indexBaseF .rval idx :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, idx⟩ s1 mv1 mh1 m1 mods1 (.indexIdxF .rval p pty :: fs) _ hr1 hm1 hk1 ?_
      intro iv ty_iv s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      cases hu : pty.unqual <;> simp only [hu] at hk2
      all_goals try cases hk2
      cases hvi : Sem.valAsInt? iv with
      | none => simp [hvi] at hk2
      | some ip =>
        simp only [hvi] at hk2
        next el =>
        cases hadd : Sem.evalPtrAdd cfg prog.tags s2.mem p el ip.2 with
        | none => simp [hadd] at hk2
        | some pv =>
          cases pv <;> simp only [hadd] at hk2
          all_goals try cases hk2
          next b off =>
          have hadd_m := hr2.evalPtrAdd_mem hadd
          obtain ⟨res, hrd_place, hk⟩ := vcReadDiscardPlace_sound hr2 hm2 hk2
          have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval iv ty_iv) (.indexIdxF .rval p pty :: fs)) =
              some (.ret res fs, m2, mods2) := by
            unfold Sem.stepExprPure
            simp only [hu, hvi, hadd_m, hrd_place, bind, Option.bind, pure, Pure.pure]
          exact hrules.of_exprPure hstep (hcont res s2 mv2 mh2 m2 mods2 hr2 hm2 hk)
    | member base fld =>
      unfold vcExprDiscard at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.lval, base⟩ s mv mh m mods (.memberF .rval fld :: fs) _ hr hm hvc ?_
      intro b off sty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        obtain ⟨res, hrd_place, hk⟩ := vcReadDiscardPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off sty) (.memberF .rval fld :: fs)) =
            some (.ret res fs, m1, mods1) := by
          unfold Sem.stepExprPure
          simp only [hfl, hrd_place, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont res s1 mv1 mh1 m1 mods1 hr1 hm1 hk)
    | arrow base fld =>
      unfold vcExprDiscard at hvc
      refine hrules.of_exprPure rfl ?_
      refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, base⟩ s mv mh m mods (.arrowF .rval fld :: fs) _ hr hm hvc ?_
      intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      cases hu : pty.unqual <;> simp only [hu] at hk1
      all_goals try cases hk1
      cases p <;> simp only at hk1
      all_goals try cases hk1
      next sty b off =>
      cases hfl : fieldLayout? prog.tags sty fld with
      | none => simp [hfl] at hk1
      | some fp =>
        simp only [hfl] at hk1
        obtain ⟨res, hrd_place, hk⟩ := vcReadDiscardPlace_sound hr1 hm1 hk1
        have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) =
            some (.ret res fs, m1, mods1) := by
          unfold Sem.stepExprPure
          simp only [hu, hfl, hrd_place, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep (hcont res s1 mv1 mh1 m1 mods1 hr1 hm1 hk)
    | assign op lhs rhs =>
      by_cases hreg : ∃ x p, lhs = .var x ∧ s.regs.lookup x = some p
      · rcases hreg with ⟨x, ⟨v0, lty0⟩, rfl, hl0⟩
        unfold vcExprDiscard at hvc
        simp only [hl0] at hvc
        obtain ⟨sl0, hsl0, hname0, _, henv0, _⟩ := hr.lookup_reg hl0
        have h1 : Sem.stepExprPure prog cfg env m mods (.eval .lval (.var x) (.assignLhsF op rhs :: fs)) =
            some (.ret (.lval sl0.blk 0 lty0) (.assignLhsF op rhs :: fs), m, mods) := by
          unfold Sem.stepExprPure; simp [henv0]
        refine hrules.of_exprPure rfl (hrules.of_exprPure h1 (hrules.of_exprPure rfl ?_))
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.rval, rhs⟩ s mv mh m mods (.assignRhsF op sl0.blk 0 lty0 :: fs) _ hr hm hvc ?_
        intro rval rty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        obtain ⟨cv, m2, hstep, hr2, hm2, hk2⟩ :=
          vcAssignReg_finish_sound (K := fun _ _ s' mv' mh' => K s' mv' mh') hsl0 hname0 henv0 hr1 hm1 hk1
        exact hrules.of_exprPure hstep
          (hcont (.rval cv lty0) { s1 with regs := s1.regs.set x cv lty0 } (x :: mv1) mh1 m2
            (⟨sl0.blk, 0, sizeofTy prog.tags lty0⟩ :: mods1) hr2 hm2 hk2)
      · have hvc' := vcExprDiscard_assign_lval hreg hvc
        refine hrules.of_exprPure rfl ?_
        refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
          ⟨.lval, lhs⟩ s mv mh m mods (.assignLhsF op rhs :: fs) _ hr hm hvc' ?_
        intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        by_cases hagg : isAggTy lty = true
        · simp only [hagg, ↓reduceIte] at hk1
          rcases hk1 with ⟨rfl, hk_agg⟩
          refine hrules.of_exprPure rfl ?_
          refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.agg, rhs⟩ s1 mv1 mh1 m1 mods1 (.assignRhsF .eq b off lty :: fs) _ hr1 hm1 hk_agg ?_
          intro bs sty s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
          obtain ⟨s3, mv3, mh3, m3, mods3, hstep_rhs, hs_os, hr3, hm3, hk3⟩ :=
            vcWriteAggPlace_sound hr2 hm2 hk2
          rw [← hs_os]
          exact hrules.of_exprPure hstep_rhs (hcont _ s3 mv3 mh3 m3 mods3 hr3 hm3 hk3)
        · have haggf : isAggTy lty = false := Bool.eq_false_iff.mpr hagg
          simp only [haggf, Bool.false_eq_true, ↓reduceIte] at hk1
          refine hrules.of_exprPure rfl ?_
          refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.rval, rhs⟩ s1 mv1 mh1 m1 mods1 (.assignRhsF op b off lty :: fs) _ hr1 hm1 hk1 ?_
          intro rval rty s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
          obtain ⟨rv, rt, s3, mv3, mh3, m3, mods3, hstep_rhs, hs_os, hr3, hm3, hk3⟩ :=
            vcAssignPlaceFinish_sound hr2 hm2 hk2
          rw [← hs_os]
          exact hrules.of_exprPure hstep_rhs (hcont _ s3 mv3 mh3 m3 mods3 hr3 hm3 hk3)
    | lit _ _ _ _ _ | strLit _ | sizeOfTy _ | sizeOfExpr _ | unary _ _ | binary _ _ _
    | logAnd _ _ | logOr _ _ | cast _ _ | addrOf _ | incDec _ _ | call _ _ | vaStart _ _ | vaEnd _ =>
      unfold vcExprDiscard at hvc
      exact vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.rval, _⟩ s mv mh m mods fs _ hr hm hvc
        (fun v ty s' mv' mh' m' mods' hr' hm' hk' => hcont (.rval v ty) s' mv' mh' m' mods' hr' hm' hk')
  | ⟨.callArgs, args⟩ => by
    intro arg0 rest hcons fnName fnTy done s mv mh m mods fs K hr hm hvc hcont
    subst hcons
    unfold vcCallArgs at hvc
    refine vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
      ⟨.rval, arg0⟩ s mv mh m mods (.callArgF fnName fnTy done rest :: fs) _ hr hm hvc ?_
    intro v1 ty1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    cases rest with
    | nil =>
      unfold vcCallArgs at hk1
      exact hcont _ s1 (done ++ [(v1, ty1)]) m1 hr1 (by cases v1 <;> rfl) hk1
    | cons arg1 tl =>
      refine hrules.of_exprPure rfl ?_
      exact vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
        ⟨.callArgs, arg1 :: tl⟩ arg1 tl rfl fnName fnTy (done ++ [(v1, ty1)]) s1 mv1 mh1 m1 mods1 fs K hr1 hm1 hk1 hcont
termination_by w => exprWorkMeasure w

theorem vcExprL_sound_gen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop} (hrules : WPRules prog cfg ext W)
    {contracts : ContractEnv} (hcs : CallContractsSound prog cfg W contracts) {baseEnv : Env}
    {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont}
    {e : CExpr} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {m : Mem} {mods : ModSet} {fs : List ExprFrame}
    {K : BlockId → Int64 → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hm : ModsOK cur outer mv mh mods)
    (hvc : vcExprL prog cfg contracts baseEnv s mv mh e K)
    (hcont : ∀ b off ty s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K b off ty s' mv' mh' →
      W Q (.running (.expr (.ret (.lval b off ty) fs) ctx mods') env blks m' s'.os k)) :
    W Q (.running (.expr (.eval .lval e fs) ctx mods) env blks m s.os k) :=
  vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
    ⟨.lval, e⟩ s mv mh m mods fs K hr hm hvc hcont

theorem vcExprR_sound_gen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop} (hrules : WPRules prog cfg ext W)
    {contracts : ContractEnv} (hcs : CallContractsSound prog cfg W contracts) {baseEnv : Env}
    {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont}
    {e : CExpr} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {m : Mem} {mods : ModSet} {fs : List ExprFrame}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hm : ModsOK cur outer mv mh mods)
    (hvc : vcExprR prog cfg contracts baseEnv s mv mh e K)
    (hcont : ∀ v ty s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K v ty s' mv' mh' →
      W Q (.running (.expr (.ret (.rval v ty) fs) ctx mods') env blks m' s'.os k)) :
    W Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k) :=
  vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
    ⟨.rval, e⟩ s mv mh m mods fs K hr hm hvc hcont

theorem vcExprAgg_sound_gen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop} (hrules : WPRules prog cfg ext W)
    {contracts : ContractEnv} (hcs : CallContractsSound prog cfg W contracts) {baseEnv : Env}
    {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont}
    {e : CExpr} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {m : Mem} {mods : ModSet} {fs : List ExprFrame}
    {K : List MemByte → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hm : ModsOK cur outer mv mh mods)
    (hvc : vcExprAgg prog cfg contracts baseEnv s mv mh e K)
    (hcont : ∀ bs ty s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K bs ty s' mv' mh' →
      W Q (.running (.expr (.ret (.structVal bs ty) fs) ctx mods') env blks m' s'.os k)) :
    W Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k) :=
  vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
    ⟨.agg, e⟩ s mv mh m mods fs K hr hm hvc hcont

theorem vcExprDiscard_sound_gen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop} (hrules : WPRules prog cfg ext W)
    {contracts : ContractEnv} (hcs : CallContractsSound prog cfg W contracts) {baseEnv : Env}
    {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont}
    {e : CExpr} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {m : Mem} {mods : ModSet} {fs : List ExprFrame}
    {K : SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hm : ModsOK cur outer mv mh mods)
    (hvc : vcExprDiscard prog cfg contracts baseEnv s mv mh e K)
    (hcont : ∀ res s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K s' mv' mh' →
      W Q (.running (.expr (.ret res fs) ctx mods') env blks m' s'.os k)) :
    W Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k) :=
  vcExpr_sound_aux_gen prog cfg W hrules contracts hcs baseEnv Q cur outer env blks ctx k
    ⟨.discard, e⟩ s mv mh m mods fs K hr hm hvc hcont

theorem vcExprR_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {baseEnv : Env}
    {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont}
    {e : CExpr} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {m : Mem} {mods : ModSet} {fs : List ExprFrame}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hm : ModsOK cur outer mv mh mods)
    (hvc : vcExprR prog cfg specs.toContracts baseEnv s mv mh e K)
    (hcont : ∀ v ty s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K v ty s' mv' mh' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) fs) ctx mods') env blks m' s'.os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k) :=
  vcExprR_sound_gen (WPRules.wpTerm prog cfg ext) (specs.contractsSound_wpTerm) hr hm hvc hcont

theorem vcExprR_safeNext {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {R : RunState → Prop}
    (hcs : CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) contracts)
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop} {cur : FrameScope} {outer : List FrameScope}
    {env : Env} {blks : List BlockId} {ctx : ExprCtx} {k : Cont}
    {e : CExpr} {s : SymState} {mv : List String} {mh : List (BlockId × Int64 × Nat)}
    {m : Mem} {mods : ModSet} {fs : List ExprFrame}
    {K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hm : ModsOK cur outer mv mh mods)
    (hvc : vcExprR prog cfg contracts baseEnv s mv mh e K)
    (hcont : ∀ v ty s' mv' mh' m' mods',
      Refines prog.tags baseEnv cur outer s' env blks m' →
      ModsOK cur outer mv' mh' mods' →
      K v ty s' mv' mh' →
      SafeUntil prog cfg ext Q R (.running (.expr (.ret (.rval v ty) fs) ctx mods') env blks m' s'.os k)) :
    SafeNext prog cfg ext Q R (.running (.expr (.eval .rval e fs) ctx mods) env blks m s.os k) := by
  let hrules := WPRules.safeUntil prog cfg ext R
  cases e with
  | paren e1 =>
    unfold vcExprR at hvc
    exact SafeNext.of_exprPure rfl (vcExprR_sound_gen hrules hcs hr hm hvc hcont)
  | lit _ _ _ _ _ =>
    unfold vcExprR at hvc
    exact SafeNext.of_exprPure rfl (hcont _ _ s mv mh m mods hr hm hvc)
  | strLit str =>
    unfold vcExprR at hvc
    rcases hvc with ⟨hsz, halloc_vc⟩
    refine SafeNext.of_strLit rfl hsz fun base bid m' halloc => ?_
    have hle : s.mem.nextBlock ≤ bid :=
      Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
    have hr' := hr.alloc_strLit hsz halloc hle
    exact hcont (.ptr bid 0) (.ptr (.const_ (.int .i8)))
      { s with mem := (allocAt s.mem bid hle (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)) }
      mv mh m' mods hr' hm (halloc_vc bid hle base)
  | sizeOfTy _ =>
    unfold vcExprR at hvc
    exact SafeNext.of_exprPure rfl (hcont _ _ s mv mh m mods hr hm hvc)
  | sizeOfExpr e1 =>
    unfold vcExprR at hvc
    cases het : Sem.exprType? prog.tags (s.typeEnv baseEnv) prog.fnProtos e1 with
    | none => simp [het] at hvc
    | some ty =>
      simp only [het] at hvc
      rw [hr.exprType?_eq e1] at het
      have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.sizeOfExpr e1) fs) =
          some (.ret (.rval (.int .u64 (BitVec.ofNat 64 (sizeofTy prog.tags ty))) (.int .u64)) fs, m, mods) := by
        unfold Sem.stepExprPure; simp [het]
      exact SafeNext.of_exprPure hstep (hcont _ _ s mv mh m mods hr hm hvc)
  | var x =>
    unfold vcExprR at hvc
    cases hl : s.regs.lookup x with
    | some p =>
      rcases p with ⟨v, ty⟩
      simp only [hl] at hvc
      rcases hvc with ⟨hscal, hnot_mv, hne_undef, hk⟩
      obtain ⟨sl, hsl, hname, _, henv, hrd⟩ := hr.lookup_reg hl
      have hnc : mods.conflicts sl.blk 0 (sizeofTy prog.tags ty) = false :=
        hm.no_conflict_var (nodup_regBlks_of_nodup hr.nodup_blks) hsl (hname ▸ hnot_mv) 0 (sizeofTy prog.tags ty)
      have hrd_place : Sem.readPlace prog.tags m mods .rval sl.blk 0 ty = some (.rval v ty.decay) := by
        unfold Sem.readPlace; unfold isScalarPlaceTy at hscal
        cases hu : ty.unqual <;> simp [hu] at hscal
        all_goals simp only [hnc, Bool.not_false, guard_true, hrd hne_undef,
          bind, Option.bind, Option.map_some]
      have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
          some (.ret (.rval v ty.decay) fs, m, mods) := by
        unfold Sem.stepExprPure; simp only [henv, hrd_place, Option.map_some]
      exact SafeNext.of_exprPure hstep (hcont v ty.decay s mv mh m mods hr hm hk)
    | none =>
      simp only [hl] at hvc
      have henv_match := vcExpr_var_lookup_nonreg hr hl
      cases hstk : s.stack.lookup x with
      | some p =>
        simp only [hstk] at hvc henv_match
        obtain ⟨rv, hrd_place, hk⟩ := vcReadHeapPlace_sound hr hm hvc
        have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
            some (.ret (.rval rv p.2.decay) fs, m, mods) := by
          unfold Sem.stepExprPure; simp only [henv_match, hrd_place, Option.map_some]
        exact SafeNext.of_exprPure hstep (hcont rv p.2.decay s mv mh m mods hr hm hk)
      | none =>
        simp only [hstk] at hvc henv_match
        cases hbase : baseEnv.lookup x with
        | some p =>
          simp only [hbase] at hvc
          have henv : env.lookup x = some p := henv_match.trans hbase
          obtain ⟨rv, hrd_place, hk⟩ := vcReadHeapPlace_sound hr hm hvc
          have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
              some (.ret (.rval rv p.2.decay) fs, m, mods) := by
            unfold Sem.stepExprPure; simp only [henv, hrd_place, Option.map_some]
          exact SafeNext.of_exprPure hstep (hcont rv p.2.decay s mv mh m mods hr hm hk)
        | none =>
          simp only [hbase] at hvc
          have henv : env.lookup x = none := henv_match.trans hbase
          cases hec : Sem.enumConst? prog.tags x with
          | some ev =>
            simp only [hec] at hvc
            have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
                some (.ret (.rval (Sem.ofIntCast .i32 ev) (.int .i32)) fs, m, mods) := by
              unfold Sem.stepExprPure; simp [henv, hec]
            exact SafeNext.of_exprPure hstep (hcont _ _ s mv mh m mods hr hm hvc)
          | none =>
            simp only [hec] at hvc
            cases hfp : prog.fnProtos x with
            | none => simp [hfp] at hvc
            | some p =>
              rcases p with ⟨r, ps, va⟩
              simp only [hfp] at hvc
              have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
                  some (.ret (.rval (.fnPtr x) (.fnPtr r ps va)) fs, m, mods) := by
                unfold Sem.stepExprPure; simp [henv, hec, hfp]
              exact SafeNext.of_exprPure hstep (hcont _ _ s mv mh m mods hr hm hvc)
  | unary op e1 =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    obtain ⟨rv, rt, hev, hkr⟩ := vcUnary_sound hk1
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.unaryF op :: fs)) =
        some (.ret (.rval rv rt) fs, m1, mods1) := by
      unfold Sem.stepExprPure; simp [hev]
    exact hrules.of_exprPure hstep (hcont rv rt s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
  | cast target e1 =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    obtain ⟨cv, hcast, hkr⟩ := vcCast_sound hr1 hk1
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.castF target :: fs)) =
        some (.ret (.rval cv target) fs, m1, mods1) := by
      unfold Sem.stepExprPure; simp [hcast]
    exact hrules.of_exprPure hstep (hcont cv target s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
  | binary op l r =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    refine hrules.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr1 hm1 hk1 ?_
    intro v2 t2 s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
    obtain ⟨rv, rt, hbin, hkr⟩ := vcBinary_sound hr2 hk2
    have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.binRhsF op v1 t1 :: fs)) =
        some (.ret (.rval rv rt) fs, m2, mods2) := by
      unfold Sem.stepExprPure; simp [hbin]
    exact hrules.of_exprPure hstep (hcont rv rt s2 mv2 mh2 m2 mods2 hr2 hm2 hkr)
  | logAnd l r =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    obtain ⟨b1, hb1, ht1, hf1⟩ := vcBranch_elim hk1
    cases b1
    · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logAndF r :: fs)) =
          some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m1, mods1) := by
        unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
      exact hrules.of_exprPure hstep (hcont (.int .i32 0) (.int .i32) s1 mv1 mh1 m1 mods1 hr1 hm1 (hf1 rfl))
    · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logAndF r :: fs)) =
          some (.eval .rval r (.logAndEndF :: fs), m1, []) := by
        unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
      refine hrules.of_exprPure hstep ?_
      refine vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur outer [] []) (ht1 rfl) ?_
      intro v2 t2 s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      obtain ⟨b2, hb2, ht2, hf2⟩ := vcBranch_elim hk2
      cases b2
      · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logAndEndF :: fs)) =
            some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m2, mods2) := by
          unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep2 (hcont (.int .i32 0) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (hf2 rfl))
      · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logAndEndF :: fs)) =
            some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m2, mods2) := by
          unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep2 (hcont (.int .i32 1) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (ht2 rfl))
  | logOr l r =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro v1 t1 s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    obtain ⟨b1, hb1, ht1, hf1⟩ := vcBranch_elim hk1
    cases b1
    · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logOrF r :: fs)) =
          some (.eval .rval r (.logOrEndF :: fs), m1, []) := by
        unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
      refine hrules.of_exprPure hstep ?_
      refine vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur outer [] []) (hf1 rfl) ?_
      intro v2 t2 s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      obtain ⟨b2, hb2, ht2, hf2⟩ := vcBranch_elim hk2
      cases b2
      · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logOrEndF :: fs)) =
            some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m2, mods2) := by
          unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep2 (hcont (.int .i32 0) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (hf2 rfl))
      · have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logOrEndF :: fs)) =
            some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m2, mods2) := by
          unfold Sem.stepExprPure; simp [hb2, bind, Option.bind, pure, Pure.pure]
        exact hrules.of_exprPure hstep2 (hcont (.int .i32 1) (.int .i32) s2 mv2 mh2 m2 mods2 hr2 hm2 (ht2 rfl))
    · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logOrF r :: fs)) =
          some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m1, mods1) := by
        unfold Sem.stepExprPure; simp [hb1, bind, Option.bind, pure, Pure.pure]
      exact hrules.of_exprPure hstep (hcont (.int .i32 1) (.int .i32) s1 mv1 mh1 m1 mods1 hr1 hm1 (ht1 rfl))
  | cond c t f =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro vc tc s1 _ _ m1 mods1 hr1 _ hk1
    obtain ⟨bc, hbc, ht, hf⟩ := vcBranch_elim hk1
    cases bc
    · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
          some (.eval .rval f fs, m1, []) := by
        unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
      exact hrules.of_exprPure hstep
        (vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur outer [] []) (hf rfl) hcont)
    · have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval vc tc) (.condF t f :: fs)) =
          some (.eval .rval t fs, m1, []) := by
        unfold Sem.stepExprPure; simp [hbc, bind, Option.bind, pure, Pure.pure]
      exact hrules.of_exprPure hstep
        (vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur outer [] []) (ht rfl) hcont)
  | comma l r =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprDiscard_sound_gen hrules hcs hr hm hvc ?_
    intro res s1 _ _ m1 _ hr1 _ hk1
    refine hrules.of_exprPure (by cases res <;> rfl) ?_
    exact vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur outer [] []) hk1 hcont
  | addrOf l =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprL_sound_gen hrules hcs hr hm hvc ?_
    intro b off ty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    exact hrules.of_exprPure rfl (hcont (.ptr b off) (.ptr ty) s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
  | deref e1 =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    cases hu : pty.unqual <;> simp only [hu] at hk1
    all_goals try cases hk1
    · cases p <;> simp only at hk1
      all_goals try cases hk1
      next el b off =>
      obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr1 hm1 hk1
      have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) =
          some (.ret (.rval rv el.decay) fs, m1, mods1) := by
        unfold Sem.stepExprPure; simp [hu, hrd_place]
      exact hrules.of_exprPure hstep (hcont rv el.decay s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
    · cases p <;> simp only at hk1
      all_goals try cases hk1
      next rt ps va sym =>
      have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.fnPtr sym) pty) (.derefF .rval :: fs)) =
          some (.ret (.rval (.fnPtr sym) (.fnPtr rt ps va)) fs, m1, mods1) := by
        unfold Sem.stepExprPure; simp [hu]
      exact hrules.of_exprPure hstep (hcont (.fnPtr sym) (.fnPtr rt ps va) s1 mv1 mh1 m1 mods1 hr1 hm1 hk1)
  | index base idx =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    refine hrules.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr1 hm1 hk1 ?_
    intro iv ty_iv s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
    cases hu : pty.unqual <;> simp only [hu] at hk2
    all_goals try cases hk2
    cases hvi : Sem.valAsInt? iv with
    | none => simp [hvi] at hk2
    | some ip =>
      simp only [hvi] at hk2
      next el =>
      cases hadd : Sem.evalPtrAdd cfg prog.tags s2.mem p el ip.2 with
      | none => simp [hadd] at hk2
      | some pv =>
        cases pv <;> simp only [hadd] at hk2
        all_goals try cases hk2
        next b off =>
        have hadd_m := hr2.evalPtrAdd_mem hadd
        obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr2 hm2 hk2
        have hstep : Sem.stepExprPure prog cfg env m2 mods2
            (.ret (.rval iv ty_iv) (.indexIdxF .rval p pty :: fs)) =
            some (.ret (.rval rv el.decay) fs, m2, mods2) := by
          unfold Sem.stepExprPure; simp [hu, hvi, hadd_m, hrd_place]
        exact hrules.of_exprPure hstep (hcont rv el.decay s2 mv2 mh2 m2 mods2 hr2 hm2 hkr)
  | member base fld =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprL_sound_gen hrules hcs hr hm hvc ?_
    intro b off sty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    cases hfl : fieldLayout? prog.tags sty fld with
    | none => simp [hfl] at hk1
    | some fp =>
      simp only [hfl] at hk1
      obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr1 hm1 hk1
      have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off sty) (.memberF .rval fld :: fs)) =
          some (.ret (.rval rv fp.2.decay) fs, m1, mods1) := by
        unfold Sem.stepExprPure
        simp only [hfl, hrd_place, bind, Option.bind, pure, Pure.pure]
      exact hrules.of_exprPure hstep (hcont rv fp.2.decay s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
  | arrow base fld =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro p pty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
    cases hu : pty.unqual <;> simp only [hu] at hk1
    all_goals try cases hk1
    cases p <;> simp only at hk1
    all_goals try cases hk1
    next sty b off =>
    cases hfl : fieldLayout? prog.tags sty fld with
    | none => simp [hfl] at hk1
    | some fp =>
      simp only [hfl] at hk1
      obtain ⟨rv, hrd_place, hkr⟩ := vcReadHeapPlace_sound hr1 hm1 hk1
      have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) =
          some (.ret (.rval rv fp.2.decay) fs, m1, mods1) := by
        unfold Sem.stepExprPure
        simp only [hu, hfl, hrd_place, bind, Option.bind, pure, Pure.pure]
      exact hrules.of_exprPure hstep (hcont rv fp.2.decay s1 mv1 mh1 m1 mods1 hr1 hm1 hkr)
  | incDec op lhs =>
    cases lhs with
    | var x =>
      unfold vcExprR at hvc
      dsimp only at hvc
      cases hl : s.regs.lookup x with
      | some p =>
        rcases p with ⟨oldV, lty⟩
        simp only [hl] at hvc
        obtain ⟨rv, cv, m', b, hs1, hs2, hs3, hr', hm', hk'⟩ :=
          vcIncDecReg_steps_sound hr hm hl fs hvc
        exact SafeNext.of_exprPure hs1 (hrules.of_exprPure hs2 (hrules.of_exprPure hs3
          (hcont rv lty { s with regs := s.regs.set x cv lty } (x :: mv) mh m'
            (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) hr' hm' hk')))
      | none =>
        simp only [hl] at hvc
        refine SafeNext.of_exprPure rfl ?_
        refine vcExprL_sound_gen hrules hcs hr hm hvc ?_
        intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        obtain ⟨rv, rt, s2, mv2, mh2, m2, mods2, hstep, hs_os, hr2, hm2, hk2⟩ :=
          vcIncDecPlaceFinish_sound hr1 hm1 hk1
        rw [← hs_os]
        exact hrules.of_exprPure hstep (hcont rv rt s2 mv2 mh2 m2 mods2 hr2 hm2 hk2)
    | _ =>
      unfold vcExprR at hvc
      refine SafeNext.of_exprPure rfl ?_
      refine vcExprL_sound_gen hrules hcs hr hm hvc ?_
      intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      obtain ⟨rv, rt, s2, mv2, mh2, m2, mods2, hstep, hs_os, hr2, hm2, hk2⟩ :=
        vcIncDecPlaceFinish_sound hr1 hm1 hk1
      rw [← hs_os]
      exact hrules.of_exprPure hstep (hcont rv rt s2 mv2 mh2 m2 mods2 hr2 hm2 hk2)
  | assign op lhs rhs =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    cases lhs with
    | var x =>
      cases hl0 : s.regs.lookup x with
      | some p0 =>
        rcases p0 with ⟨v0, lty0⟩
        simp only [hl0] at hvc
        obtain ⟨sl0, hsl0, hname0, _, henv0, _⟩ := hr.lookup_reg hl0
        have h1 : Sem.stepExprPure prog cfg env m mods (.eval .lval (.var x) (.assignLhsF op rhs :: fs)) =
            some (.ret (.lval sl0.blk 0 lty0) (.assignLhsF op rhs :: fs), m, mods) := by
          unfold Sem.stepExprPure; simp [henv0]
        refine hrules.of_exprPure h1 (hrules.of_exprPure rfl ?_)
        refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
        intro rval rty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        obtain ⟨cv, m2, hstep, hr2, hm2, hk2⟩ :=
          vcAssignReg_finish_sound hsl0 hname0 henv0 hr1 hm1 hk1
        exact hrules.of_exprPure hstep
          (hcont cv lty0 { s1 with regs := s1.regs.set x cv lty0 } (x :: mv1) mh1 m2
            (⟨sl0.blk, 0, sizeofTy prog.tags lty0⟩ :: mods1) hr2 hm2 hk2)
      | none =>
        simp only [hl0] at hvc
        refine vcExprL_sound_gen hrules hcs hr hm hvc ?_
        intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
        refine hrules.of_exprPure rfl ?_
        refine vcExprR_sound_gen hrules hcs hr1 hm1 hk1 ?_
        intro rval rty s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
        obtain ⟨rv, rt, s3, mv3, mh3, m3, mods3, hstep_rhs, hs_os, hr3, hm3, hk3⟩ :=
          vcAssignPlaceFinish_sound hr2 hm2 hk2
        rw [← hs_os]
        exact hrules.of_exprPure hstep_rhs (hcont rv rt s3 mv3 mh3 m3 mods3 hr3 hm3 hk3)
    | _ =>
      refine vcExprL_sound_gen hrules hcs hr hm hvc ?_
      intro b off lty s1 mv1 mh1 m1 mods1 hr1 hm1 hk1
      refine hrules.of_exprPure rfl ?_
      refine vcExprR_sound_gen hrules hcs hr1 hm1 hk1 ?_
      intro rval rty s2 mv2 mh2 m2 mods2 hr2 hm2 hk2
      obtain ⟨rv, rt, s3, mv3, mh3, m3, mods3, hstep_rhs, hs_os, hr3, hm3, hk3⟩ :=
        vcAssignPlaceFinish_sound hr2 hm2 hk2
      rw [← hs_os]
      exact hrules.of_exprPure hstep_rhs (hcont rv rt s3 mv3 mh3 m3 mods3 hr3 hm3 hk3)
  | call fn args =>
    unfold vcExprR at hvc
    refine SafeNext.of_exprPure rfl ?_
    refine vcExprR_sound_gen hrules hcs hr hm hvc ?_
    intro fnV fnTy sFn mvFn mhFn mFn modsFn hrFn hmFn hkFn
    cases fnV
    all_goals try cases hkFn
    next sym =>
      cases hfn_ty : fnTy.unqual <;> simp only [hfn_ty] at hkFn
      all_goals try cases hkFn
      next rt ptys va =>
      cases hsp : contracts sym with
      | none => simp [hsp] at hkFn
      | some spec =>
        simp only [hsp] at hkFn
        rcases hkFn with ⟨hsym_eq, hrt_eq, hptys_eq, hva_eq, hargs_vc⟩
        subst hrt_eq hva_eq
        let hcall_fn := vcCallArgs_finish_sound hcs hsp hsym_eq hfn_ty hptys_eq hcont
        cases args with
        | nil =>
          unfold vcCallArgs at hargs_vc
          exact hcall_fn _ sFn [] mFn hrFn rfl hargs_vc
        | cons arg0 rest =>
          refine hrules.of_exprPure rfl ?_
          exact vcExpr_sound_aux_gen prog cfg _ hrules contracts hcs baseEnv Q cur outer env blks ctx k
            ⟨.callArgs, arg0 :: rest⟩ arg0 rest rfl sym fnTy []
            sFn mvFn mhFn mFn modsFn fs _ hrFn hmFn hargs_vc hcall_fn
  | vaStart ap lastParam =>
    unfold vcExprR at hvc
    obtain ⟨m_clean', m', hstep, hr', hk'⟩ := vcVaOp_step_sound hr ap
      (List.replicate (sizeofTy prog.tags .vaList) (.byte 1)) (.vaStart ap lastParam) fs
      (fun _ _ p h1 h2 h3 => by unfold Sem.stepExprPure; simp only [h1, h2, guard_true, h3,
        bind, Option.bind, pure, Pure.pure]) hvc
    exact SafeNext.of_exprPure hstep (hcont .void .void { s with mem := m_clean' } mv mh m' mods hr' hm hk')
  | vaEnd ap =>
    unfold vcExprR at hvc
    obtain ⟨m_clean', m', hstep, hr', hk'⟩ := vcVaOp_step_sound hr ap
      (List.replicate (sizeofTy prog.tags .vaList) .undef) (.vaEnd ap) fs
      (fun _ _ p h1 h2 h3 => by unfold Sem.stepExprPure; simp only [h1, h2, guard_true, h3,
        bind, Option.bind, pure, Pure.pure]) hvc
    exact SafeNext.of_exprPure hstep (hcont .void .void { s with mem := m_clean' } mv mh m' mods hr' hm hk')

/-! ## Helper Lemmas for Statements & Function Calls -/

theorem castVal_valScalarTyped {m : Mem} {ty : CTy} {v cv : Val}
    (hsc : isScalarPlaceTy ty = true) (hc : Sem.castVal m ty v = some cv) :
    ValScalarTyped ty cv := by
  unfold isScalarPlaceTy at hsc
  unfold ValScalarTyped
  unfold Sem.castVal Sem.ofIntCast at hc
  dsimp only at hc
  cases hu : ty.unqual with
  | int k =>
    simp only [hu] at hc ⊢
    have hv : (CTy.int k).isVoid = false := rfl
    have hk : (CTy.int k).intKind? = some k := rfl
    simp only [hv, Bool.false_eq_true, ↓reduceIte, hk] at hc
    cases v with
    | int _ _ => cases hc; exact ⟨_, rfl⟩
    | null => cases hc; exact ⟨_, rfl⟩
    | ptr b off =>
      cases hm : m.addrOf b off with
      | none => simp [hm] at hc
      | some _ => simp [hm] at hc; cases hc; exact ⟨_, rfl⟩
    | _ => simp at hc
  | enumTy tag isU =>
    simp only [hu] at hc ⊢
    have hv : (CTy.enumTy tag isU).isVoid = false := rfl
    have hk : (CTy.enumTy tag isU).intKind? = some (if isU then .u32 else .i32) := rfl
    simp only [hv, Bool.false_eq_true, ↓reduceIte, hk] at hc
    cases v with
    | int _ _ => cases hc; exact ⟨_, rfl⟩
    | null => cases hc; exact ⟨_, rfl⟩
    | ptr b off =>
      cases hm : m.addrOf b off with
      | none => simp [hm] at hc
      | some _ => simp [hm] at hc; cases hc; exact ⟨_, rfl⟩
    | _ => simp at hc
  | ptr el =>
    simp only [hu] at hc ⊢
    have hv : (CTy.ptr el).isVoid = false := rfl
    have hk : (CTy.ptr el).intKind? = none := rfl
    simp only [hv, hk, Bool.false_eq_true, ↓reduceIte] at hc
    cases v with
    | null => cases hc; exact .inl rfl
    | ptr pb poff => cases hc; exact .inr ⟨pb, poff, rfl⟩
    | int _ bv1 =>
      by_cases hz : (bv1.toNat == 0) = true
      · simp [hz] at hc; cases hc; exact .inl rfl
      · have hzf : (bv1.toNat == 0) = false := Bool.eq_false_iff.mpr hz
        simp [hzf] at hc
    | _ => simp at hc
  | fnPtr r ps var =>
    simp only [hu] at hc ⊢
    have hv : (CTy.fnPtr r ps var).isVoid = false := rfl
    have hk : (CTy.fnPtr r ps var).intKind? = none := rfl
    simp only [hv, hk, Bool.false_eq_true, ↓reduceIte] at hc
    cases v with
    | null => cases hc; exact .inl rfl
    | fnPtr sym => cases hc; exact .inr ⟨sym, rfl⟩
    | int _ bv1 =>
      by_cases hz : (bv1.toNat == 0) = true
      · simp [hz] at hc; cases hc; exact .inl rfl
      · have hzf : (bv1.toNat == 0) = false := Bool.eq_false_iff.mpr hz
        simp [hzf] at hc
    | _ => simp at hc
  | vaList =>
    simp only [hu] at hc ⊢
    have hv : CTy.vaList.isVoid = false := rfl
    have hk : CTy.vaList.intKind? = none := rfl
    simp only [hv, hk, Bool.false_eq_true, ↓reduceIte] at hc
    cases v with
    | vaList b =>
      cases b with
      | true => cases hc; rfl
      | false => simp at hc
    | _ => simp at hc
  | _ => simp [hu] at hsc

private theorem mapM_loop_zip_scalar (m : Mem) (params : List Param) (argVals : List (Val × CTy))
    (acc out : List Val)
    (hlen : argVals.length = params.length)
    (hsc : ∀ p ∈ params, isScalarPlaceTy p.ty = true)
    (hm : List.mapM.loop (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1)
      ((params.map (·.ty)).zip argVals) acc = some out) :
    ∃ bs, bs.length = params.length ∧ out = acc.reverse ++ bs ∧
      ∀ pv ∈ params.zip bs, ValScalarTyped pv.1.ty pv.2 := by
  induction params generalizing argVals acc with
  | nil =>
    cases argVals with
    | nil =>
      cases hm
      exact ⟨[], rfl, by simp, fun pv hp => by cases hp⟩
    | cons _ _ => cases hlen
  | cons p pt ih =>
    cases argVals with
    | nil => cases hlen
    | cons a atail =>
      unfold List.mapM.loop at hm
      simp only [List.map_cons, List.zip_cons_cons, bind, Option.bind] at hm
      cases hca : Sem.castVal m p.ty a.1 with
      | none => simp [hca] at hm
      | some cv =>
        simp only [hca] at hm
        have hp_sc : ValScalarTyped p.ty cv :=
          castVal_valScalarTyped (hsc p (.head _)) hca
        obtain ⟨bs, hbs_len, hout, hrest⟩ :=
          ih atail (cv :: acc) (by simpa using hlen) (fun q hq => hsc q (.tail _ hq)) hm
        refine ⟨cv :: bs, by simp [hbs_len], ?_, ?_⟩
        · simpa [List.append_assoc] using hout
        · intro pv hpv
          rcases List.mem_cons.mp hpv with rfl | htail
          · exact hp_sc
          · exact hrest pv htail

theorem coerceCallArgs_scalar {m : Mem} {params : List Param} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    (hsc : ∀ p ∈ params, isScalarPlaceTy p.ty = true)
    (hco : Sem.coerceCallArgs m (params.map (·.ty)) variadic argVals = some coerced) :
    (if variadic then params.length ≤ coerced.length else coerced.length = params.length) ∧
    ∀ pv ∈ params.zip (coerced.take params.length), ValScalarTyped pv.1.ty pv.2 := by
  unfold Sem.coerceCallArgs at hco
  cases variadic with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind, List.length_map] at hco ⊢
    by_cases hlen : (argVals.length == params.length) = true
    · simp only [hlen, guard_true] at hco
      have hlen_eq : argVals.length = params.length := eq_of_beq hlen
      obtain ⟨bs, hbs_len, hout, hzip⟩ :=
        mapM_loop_zip_scalar m params argVals [] coerced hlen_eq hsc hco
      simp only [List.reverse_nil, List.nil_append] at hout
      rw [hout]
      have htake : bs.take params.length = bs := List.take_of_length_le (Nat.le_of_eq hbs_len)
      simpa [hbs_len, htake] using hzip
    · have hlf : (argVals.length == params.length) = false := Bool.eq_false_iff.mpr hlen
      simp [hlf, guard] at hco
  | true =>
    simp only [↓reduceIte, bind, Option.bind, List.length_map] at hco ⊢
    by_cases hle : params.length ≤ argVals.length
    · simp only [hle, guard_true] at hco
      cases hmap : List.mapM (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1)
          ((params.map (·.ty)).zip (argVals.take params.length)) with
      | none => simp [hmap] at hco
      | some fixed =>
        simp only [hmap] at hco
        cases hco
        have hlen_take : (argVals.take params.length).length = params.length := List.length_take_of_le hle
        obtain ⟨bs, hbs_len, hfixed, hzip⟩ :=
          mapM_loop_zip_scalar m params (argVals.take params.length) [] fixed hlen_take hsc hmap
        simp only [List.reverse_nil, List.nil_append] at hfixed
        rw [hfixed]
        have htake_append :
            (bs ++ List.map (fun (x : Val × CTy) => Sem.promoteVariadicArg x.1) (argVals.drop params.length)).take
              params.length = bs := by
          rw [List.take_append_of_le_length (Nat.le_of_eq hbs_len.symm),
            List.take_of_length_le (Nat.le_of_eq hbs_len)]
        refine ⟨by simp [hbs_len], ?_⟩
        rwa [htake_append]
    · simp only [hle, guard] at hco; cases hco

theorem coerceCallArgs_nonvar_scalar {m : Mem} {params : List Param} {argVals : List (Val × CTy)}
    {coerced : List Val}
    (hsc : ∀ p ∈ params, isScalarPlaceTy p.ty = true)
    (hco : Sem.coerceCallArgs m (params.map (·.ty)) false argVals = some coerced) :
    coerced.length = params.length ∧
    ∀ pv ∈ params.zip coerced, ValScalarTyped pv.1.ty pv.2 := by
  obtain ⟨hlen, hvt⟩ := coerceCallArgs_scalar hsc hco
  have hlen' : coerced.length = params.length := hlen
  refine ⟨hlen', ?_⟩
  rwa [List.take_of_length_le (Nat.le_of_eq hlen')] at hvt

private theorem mapM_loop_of_valScalar (m : Mem) (params : List Param) (args acc : List Val)
    (hlen : args.length = params.length)
    (ht : ∀ pv ∈ params.zip args, ValScalarTyped pv.1.ty pv.2) :
    List.mapM.loop (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1)
      ((params.map (·.ty)).zip (args.map (·, .void))) acc = some (acc.reverse ++ args) := by
  induction params generalizing args acc with
  | nil =>
    cases args with
    | nil => simp [List.mapM.loop]
    | cons _ _ => cases hlen
  | cons p pt ih =>
    cases args with
    | nil => cases hlen
    | cons a atail =>
      have ha : ValScalarTyped p.ty a := ht (p, a) (.head _)
      unfold List.mapM.loop
      simp only [List.map_cons, List.zip_cons_cons, bind, Option.bind, ha.castVal_self m]
      have hrec := ih atail (a :: acc) (by simpa using hlen) (fun pv hpv => ht pv (.tail _ hpv))
      simpa [List.append_assoc] using hrec

private theorem mapM_of_valScalar (m : Mem) (params : List Param) (args : List Val)
    (hlen : args.length = params.length)
    (ht : ∀ pv ∈ params.zip args, ValScalarTyped pv.1.ty pv.2) :
    List.mapM (m := Option) (fun (p : CTy × Val × CTy) => Sem.castVal m p.1 p.2.1)
      ((params.map (·.ty)).zip (args.map (·, .void))) = some args := by
  unfold List.mapM
  simpa using mapM_loop_of_valScalar m params args [] hlen ht

theorem coerceCallArgs_of_valScalarTyped {m : Mem} {params : List Param} {args : List Val}
    (hlen : args.length = params.length)
    (ht : ∀ pv ∈ params.zip args, ValScalarTyped pv.1.ty pv.2) :
    Sem.coerceCallArgs m (params.map (·.ty)) false (args.map (·, .void)) = some args := by
  unfold Sem.coerceCallArgs
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind, List.length_map, hlen, beq_self_eq_true, guard_true]
  exact mapM_of_valScalar m params args hlen ht

theorem coerceCallArgs_variadic_of_valScalarTyped {m : Mem} {params : List Param} {args : List Val}
    (hle : params.length ≤ args.length)
    (ht : ∀ pv ∈ params.zip (args.take params.length), ValScalarTyped pv.1.ty pv.2)
    (hprom : ∀ a ∈ args.drop params.length, Sem.promoteVariadicArg a = a) :
    Sem.coerceCallArgs m (params.map (·.ty)) true (args.map (·, .void)) = some args := by
  unfold Sem.coerceCallArgs
  simp only [↓reduceIte, bind, Option.bind, List.length_map, hle, guard_true]
  have htake_map : (args.map (·, CTy.void)).take params.length = (args.take params.length).map (·, CTy.void) := by
    simp [List.map_take]
  have hdrop_map : (args.map (·, CTy.void)).drop params.length = (args.drop params.length).map (·, CTy.void) := by
    simp [List.map_drop]
  rw [htake_map, mapM_of_valScalar m params (args.take params.length) (List.length_take_of_le hle) ht]
  dsimp only
  rw [hdrop_map, List.map_map]
  have hmap_id : List.map ((fun (x : Val × CTy) => Sem.promoteVariadicArg x.1) ∘ (·, CTy.void))
      (args.drop params.length) = args.drop params.length := by
    suffices hgo : ∀ ds : List Val, (∀ a ∈ ds, Sem.promoteVariadicArg a = a) →
        List.map ((fun (x : Val × CTy) => Sem.promoteVariadicArg x.1) ∘ (·, CTy.void)) ds = ds from
      hgo (args.drop params.length) hprom
    intro ds hds
    induction ds with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, Function.comp_apply]
      rw [hds hd (.head _), ih (fun a ha => hds a (.tail _ ha))]
  simp only [pure, Pure.pure]
  rw [hmap_id, List.take_append_drop]

/-! ## Generic Continuation & Declaration Soundness -/

def framesScopes (cur : FrameScope) (outer : List FrameScope) :
    List AnnStmt.GotoFrame → FrameScope × List FrameScope
  | [] => (cur, outer)
  | .stmts _ :: rest => framesScopes cur outer rest
  | .blockEnd :: rest =>
    let (c', o') := framesScopes cur outer rest
    ([], c' :: o')
  | .switchCont :: rest => framesScopes cur outer rest

private theorem framesScopes_allSlots_lengths (cur : FrameScope) (outer : List FrameScope)
    (fs : List AnnStmt.GotoFrame) :
    (allRegSlots (framesScopes cur outer fs).1 (framesScopes cur outer fs).2).length =
      (allRegSlots cur outer).length ∧
    (allStkSlots (framesScopes cur outer fs).1 (framesScopes cur outer fs).2).length =
      (allStkSlots cur outer).length := by
  induction fs with
  | nil => exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    cases hd with
    | stmts _ => exact ih
    | switchCont => exact ih
    | blockEnd =>
      dsimp only [framesScopes, allRegSlots, allStkSlots, allSlots]
      simp only [List.nil_append, List.flatten_cons]
      exact ih

theorem Refines.exitBlock_exitFn {tags : TypeEnv} {baseEnv : Env} {cur sc : FrameScope}
    {outer : List FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines tags baseEnv cur (sc :: outer) s env blks m) :
    (s.exitBlock (allRegSlots sc outer).length (allStkSlots sc outer).length).exitFn = s.exitFn := by
  have hstk_eq : allStkSlots cur (sc :: outer) = stkSlots cur ++ allStkSlots sc outer := by
    simp [allStkSlots, allSlots, stkSlots_append]
  have hreg_eq : allRegSlots cur (sc :: outer) = regSlots cur ++ allRegSlots sc outer := by
    simp [allRegSlots, allSlots, regSlots_append]
  have hreg_len : s.regs.length - (allRegSlots sc outer).length = (regSlots cur).length := by
    have hl := hr.regs_match.length_eq
    rw [hreg_eq, List.length_append] at hl
    rw [← hl]; exact Nat.add_sub_cancel _ _
  have hstk_len : s.stack.length - (allStkSlots sc outer).length = (stkSlots cur).length := by
    have hl := hr.stk_match.length_eq
    rw [hstk_eq, List.length_append] at hl
    rw [← hl]; exact Nat.add_sub_cancel _ _
  simp only [SymState.exitBlock, SymState.exitFn, hreg_len, hstk_len, freeStack_append]
  congr 1
  rw [← List.map_append, List.take_append_drop]

structure ContOKGen (prog : Prog) (cfg : PointerConfig)
    (W : (Val → Mem → OSState → Prop) → RunState → Prop)
    (baseEnv : Env) (Q : Val → Mem → OSState → Prop)
    (retTy : CTy) (outer : List FrameScope) (kp : ContPost) (k : Cont) : Prop where
  retTy_eq : k.topRetTy = retTy
  normal : ∀ cur s env blks m,
    Refines prog.tags baseEnv cur outer s env blks m →
    kp.normal s →
    W Q (.running (.stmt .nop) env blks m s.os k)
  onBreak : ∀ cur s env blks m,
    Refines prog.tags baseEnv cur outer s env blks m →
    kp.onBreak s →
    ∃ e' b' m' k', Sem.unwindBreak m env blks k = some (e', b', m', k') ∧
      W Q (.running (.stmt .nop) e' b' m' s.os k')
  onContinue : ∀ cur s env blks m,
    Refines prog.tags baseEnv cur outer s env blks m →
    kp.onContinue s →
    ∃ c? stp? b d e' b' m' k',
      Sem.unwindContinue m env blks k = some (c?, stp?, b, d, e', b', m', k') ∧
      W Q (Sem.loopNext c? stp? b d e' b' m' s.os k')
  onReturn : ∀ cur s env blks m rv,
    Refines prog.tags baseEnv cur outer s env blks m →
    kp.onReturn rv s.exitFn s.os →
    ∃ re rb rt m' fs rctx rk,
      Sem.unwindReturn m blks k = some (re, rb, rt, m', fs, rctx, rk) ∧
      W Q
        (if retTy.isVoid then
          .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' s.os rk
         else
          .running (.expr (.ret (.rval rv retTy) fs) rctx []) re rb m' s.os rk)
  onGoto : ∀ lbl cur s env blks m,
    Refines prog.tags baseEnv cur outer s env blks m →
    kp.onGoto lbl s →
    ∃ s' e' b' m' k',
      Sem.gotoInCont lbl m env blks k = some (s', e', b', m', k') ∧
      W Q (.running (.stmt s') e' b' m' s.os k')

abbrev ContOK (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :=
  ContOKGen prog cfg (WPTerm prog cfg ext)

theorem ContOKGen.stmts_nil {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    {hrules : WPRules prog cfg ext W}
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    (hk : ContOKGen prog cfg W baseEnv Q retTy outer kp k) :
    ContOKGen prog cfg W baseEnv Q retTy outer kp (.stmts [] k) where
  retTy_eq := hk.retTy_eq
  normal := fun cur s env blks m hr hn =>
    hrules.of_det_state rfl (hk.normal cur s env blks m hr hn)
  onBreak := fun cur s env blks m hr hb => by
    unfold Sem.unwindBreak; exact hk.onBreak cur s env blks m hr hb
  onContinue := fun cur s env blks m hr hc => by
    unfold Sem.unwindContinue; exact hk.onContinue cur s env blks m hr hc
  onReturn := fun cur s env blks m rv hr hret => by
    unfold Sem.unwindReturn; exact hk.onReturn cur s env blks m rv hr hret
  onGoto := fun lbl cur s env blks m hr hg => by
    unfold Sem.gotoInCont Sem.findInStmts; exact hk.onGoto lbl cur s env blks m hr hg

theorem ContOKGen.stmts_prepend {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    (hk : ContOKGen prog cfg W baseEnv Q retTy outer kp k)
    (ss : List CStmt) (kn : SymState → Prop) (kg : String → SymState → Prop)
    (hn : ∀ cur s env blks m,
      Refines prog.tags baseEnv cur outer s env blks m →
      kn s →
      W Q (.running (.stmt .nop) env blks m s.os (.stmts ss k)))
    (hgoto : ∀ lbl cur s env blks m,
      Refines prog.tags baseEnv cur outer s env blks m →
      kg lbl s →
      ∃ s' e' b' m' k',
        Sem.gotoInCont lbl m env blks (.stmts ss k) = some (s', e', b', m', k') ∧
        W Q (.running (.stmt s') e' b' m' s.os k')) :
    ContOKGen prog cfg W baseEnv Q retTy outer { kp with normal := kn, onGoto := kg } (.stmts ss k) where
  retTy_eq := hk.retTy_eq
  normal := hn
  onBreak := fun cur s env blks m hr hb => by
    unfold Sem.unwindBreak; exact hk.onBreak cur s env blks m hr hb
  onContinue := fun cur s env blks m hr hc => by
    unfold Sem.unwindContinue; exact hk.onContinue cur s env blks m hr hc
  onReturn := fun cur s env blks m rv hr hret => by
    unfold Sem.unwindReturn; exact hk.onReturn cur s env blks m rv hr hret
  onGoto := hgoto

theorem ContOKGen.switchCont {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    {hrules : WPRules prog cfg ext W}
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    (hk : ContOKGen prog cfg W baseEnv Q retTy outer kp k) :
    ContOKGen prog cfg W baseEnv Q retTy outer { kp with onBreak := kp.normal } (.switchCont k) where
  retTy_eq := hk.retTy_eq
  normal := fun cur s env blks m hr hn =>
    hrules.of_det_state rfl (hk.normal cur s env blks m hr hn)
  onBreak := fun cur s env blks m hr hb =>
    ⟨env, blks, m, k, rfl, hk.normal cur s env blks m hr hb⟩
  onContinue := fun cur s env blks m hr hc => by
    unfold Sem.unwindContinue; exact hk.onContinue cur s env blks m hr hc
  onReturn := fun cur s env blks m rv hr hret => by
    unfold Sem.unwindReturn; exact hk.onReturn cur s env blks m rv hr hret
  onGoto := fun lbl cur s env blks m hr hg => by
    unfold Sem.gotoInCont; exact hk.onGoto lbl cur s env blks m hr hg

theorem ContOKGen.blockEnd {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    {hrules : WPRules prog cfg ext W}
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {cur0 : FrameScope} {outer : List FrameScope}
    {s0 : SymState} {env0 : Env} {blks0 : List BlockId} {m0 : Mem}
    (hr0 : Refines prog.tags baseEnv cur0 outer s0 env0 blks0 m0)
    {kp : ContPost} {k : Cont}
    (hk : ContOKGen prog cfg W baseEnv Q retTy outer kp k) :
    ContOKGen prog cfg W baseEnv Q retTy (cur0 :: outer)
      { normal := fun s' => kp.normal (s'.exitBlock s0.regs.length s0.stack.length)
        onBreak := fun s' => kp.onBreak (s'.exitBlock s0.regs.length s0.stack.length)
        onContinue := fun s' => kp.onContinue (s'.exitBlock s0.regs.length s0.stack.length)
        onReturn := kp.onReturn
        onGoto := fun lbl s' => kp.onGoto lbl (s'.exitBlock s0.regs.length s0.stack.length) }
      (.blockEnd env0 blks0 k) := by
  have hreg0 : s0.regs.length = (allRegSlots cur0 outer).length := hr0.regs_match.length_eq.symm
  have hstk0 : s0.stack.length = (allStkSlots cur0 outer).length := hr0.stk_match.length_eq.symm
  refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
  · intro cur' s' env' blks' m' hr' hn
    dsimp only at hn
    rw [hr'.blks_eq]
    refine hrules.of_det_state rfl ?_
    have hrex := hr'.exit_block hreg0 hstk0
    rw [← hr0.env_eq, ← hr0.blks_eq] at hrex
    exact hk.normal cur0 (s'.exitBlock s0.regs.length s0.stack.length) env0 blks0
      (m'.freeStack cur'.blks) hrex hn
  · intro cur' s' env' blks' m' hr' hb
    dsimp only at hb
    rw [hr'.blks_eq]
    have hrex := hr'.exit_block hreg0 hstk0
    rw [← hr0.env_eq, ← hr0.blks_eq] at hrex
    obtain ⟨e', b', m'', k', hu, hw⟩ :=
      hk.onBreak cur0 (s'.exitBlock s0.regs.length s0.stack.length) env0 blks0
        (m'.freeStack cur'.blks) hrex hb
    exact ⟨e', b', m'', k', hu, hw⟩
  · intro cur' s' env' blks' m' hr' hc
    dsimp only at hc
    rw [hr'.blks_eq]
    have hrex := hr'.exit_block hreg0 hstk0
    rw [← hr0.env_eq, ← hr0.blks_eq] at hrex
    obtain ⟨c?, stp?, b, d, e', b', m'', k', hu, hw⟩ :=
      hk.onContinue cur0 (s'.exitBlock s0.regs.length s0.stack.length) env0 blks0
        (m'.freeStack cur'.blks) hrex hc
    exact ⟨c?, stp?, b, d, e', b', m'', k', hu, hw⟩
  · intro cur' s' env' blks' m' rv hr' hret
    rw [hr'.blks_eq]
    have hrex := hr'.exit_block rfl rfl
    have hex_fn := hr'.exitBlock_exitFn
    rw [← hex_fn] at hret
    obtain ⟨re, rb, rt, m'', fs, rctx, rk, hu, hw⟩ :=
      hk.onReturn cur0 (s'.exitBlock (allRegSlots cur0 outer).length (allStkSlots cur0 outer).length)
        (slotsEnv (allSlots cur0 outer) baseEnv) cur0.blks (m'.freeStack cur'.blks) rv hrex hret
    refine ⟨re, rb, rt, m'', fs, rctx, rk, ?_, hw⟩
    unfold Sem.unwindReturn
    rwa [← hr0.blks_eq] at hu
  · intro lbl cur' s' env' blks' m' hr' hg
    dsimp only at hg
    rw [hr'.blks_eq]
    have hrex := hr'.exit_block hreg0 hstk0
    rw [← hr0.env_eq, ← hr0.blks_eq] at hrex
    obtain ⟨s', e', b', m'', k', hgoto, hw⟩ :=
      hk.onGoto lbl cur0 (s'.exitBlock s0.regs.length s0.stack.length) env0 blks0
        (m'.freeStack cur'.blks) hrex hg
    exact ⟨s', e', b', m'', k', hgoto, hw⟩

theorem ContOKGen.callFrame {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    {hrules : WPRules prog cfg ext W}
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {fn : FnDef} {m0 : Mem} {os0 : OSState} {args : List Val}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hpost_ext : ∀ rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (re : Env) (rb : List BlockId) (fs : List ExprFrame) (ctx : ExprCtx) (k : Cont)
    (hcont : ∀ rv m' os', post m0 os0 args rv m' os' →
      W Q (.running (.expr (.ret (.rval rv fn.retTy) fs) ctx []) re rb m' os' k)) :
    ContOKGen prog cfg W baseEnv Q fn.retTy []
      (fnEntryPost fn post m0 os0 args)
      (.callFrame re rb fn.retTy fn.body fs ctx k) where
  retTy_eq := rfl
  normal := fun cur' s' env' blks' m' hr' hn => by
    obtain ⟨hnb, hle, heq⟩ := hr'.free_all_scopes
    dsimp only [Refines.freeAllScopes] at hnb heq
    rw [← hr'.blks_eq] at hnb heq
    have hnext_exit : s'.exitFn.nextBlock ≤ (m'.freeStack blks').nextBlock := by
      simp only [SymState.exitFn, freeStack_nextBlock]; exact hle
    dsimp only [fnEntryPost] at hn
    cases hv : fn.retTy.isVoid with
    | true =>
      simp only [hv, ↓reduceIte] at hn
      have hp' := hpost_ext .void s'.exitFn (m'.freeStack blks') s'.os hnext_exit heq hn
      refine hrules.of_det_state ?_ (hcont .void (m'.freeStack blks') s'.os hp')
      unfold Sem.stepDet; simp [hv]
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at hn
      have hp' := hpost_ext .undef s'.exitFn (m'.freeStack blks') s'.os hnext_exit heq hn
      refine hrules.of_det_state ?_ (hcont .undef (m'.freeStack blks') s'.os hp')
      unfold Sem.stepDet; simp [hv]
  onBreak := fun _ _ _ _ _ _ hb => False.elim hb
  onContinue := fun _ _ _ _ _ _ hc => False.elim hc
  onReturn := fun cur' s' env' blks' m' rv hr' hret => by
    obtain ⟨hnb, hle, heq⟩ := hr'.free_all_scopes
    dsimp only [Refines.freeAllScopes] at hnb heq
    rw [← hr'.blks_eq] at hnb heq
    have hnext_exit : s'.exitFn.nextBlock ≤ (m'.freeStack blks').nextBlock := by
      simp only [SymState.exitFn, freeStack_nextBlock]; exact hle
    dsimp only [fnEntryPost] at hret
    have hp' := hpost_ext rv s'.exitFn (m'.freeStack blks') s'.os hnext_exit heq hret
    refine ⟨re, rb, fn.retTy, m'.freeStack blks', fs, ctx, k, rfl, ?_⟩
    cases hv : fn.retTy.isVoid with
    | true =>
      rcases hret_ty with hfalse | ⟨hvoid, hrv_void⟩
      · rw [hv] at hfalse; cases hfalse
      · have hrv := hrv_void m0 os0 args rv (m'.freeStack blks') s'.os hp'
        simpa [hv, hvoid, hrv] using hcont rv (m'.freeStack blks') s'.os hp'
    | false =>
      simpa [hv] using hcont rv (m'.freeStack blks') s'.os hp'
  onGoto := fun _ _ _ _ _ _ _ hg => False.elim hg

theorem vcDeclList_sound_gen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    (hrules : WPRules prog cfg ext W)
    {contracts : ContractEnv} (hcs : CallContractsSound prog cfg W contracts) {baseEnv : Env}
    {Q : Val → Mem → OSState → Prop} {retTy : CTy} {outer : List FrameScope}
    {kp : ContPost} {k : Cont} (hk : ContOKGen prog cfg W baseEnv Q retTy outer kp k)
    (ds : List (VarDecl × Bool)) {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} :
    Refines prog.tags baseEnv cur outer s env blks m →
    vcDeclList prog cfg contracts baseEnv kp ds s →
    W Q (.running (.stmt (.decls (ds.map Prod.fst))) env blks m s.os k) := by
  induction ds generalizing cur s env blks m with
  | nil =>
    intro hr hvc
    unfold vcDeclList at hvc
    exact hrules.of_det_state rfl (hk.normal cur s env blks m hr hvc)
  | cons hd rest ih =>
    intro hr hvc
    rcases hd with ⟨d, isStk⟩
    unfold vcDeclList at hvc
    by_cases hs : d.isStatic = true
    · simp only [hs, ↓reduceIte] at hvc
      refine hrules.of_det_state ?_ (ih hr hvc)
      unfold Sem.stepDet; simp [hs]
    · have hsf : d.isStatic = false := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ↓reduceIte] at hvc
      by_cases hstk : isStk = true
      · simp only [hstk, ↓reduceIte] at hvc
        cases hi : d.init? with
        | none =>
          simp only [hi] at hvc
          rcases hvc with ⟨hsz, hal, hreg_none, hrest⟩
          have hdet : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
              some (.allocLocal d none (rest.map Prod.fst) env blks m s.os k) := by
            unfold Sem.stepDet; simp [hsf, hi]
          refine hrules.of_localDecl_none hsz hal hdet fun base bid m1 hba halloc => ?_
          have hle : s.mem.nextBlock ≤ bid :=
            Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
          exact ih (s := { s with
            stack := (d.name, bid, d.ty) :: s.stack
            mem := allocAt s.mem bid hle (max 1 (sizeofTy prog.tags d.ty))
              (max 1 (alignofTy prog.tags d.ty)) .rw .stack base (fun _ => .undef) hsz hal hba })
            (hr.alloc_stk_none hreg_none hsz hal hba halloc hle) (hrest bid hle base hba)
        | some init =>
          cases init with
          | expr e =>
            simp only [hi] at hvc
            have hdet1 : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
                some (.next (.running (.expr (.eval .rval e []) (.varInit d (rest.map Prod.fst)) []) env blks m s.os k)) := by
              unfold Sem.stepDet; simp [hsf, hi]
            refine hrules.of_det_state hdet1 ?_
            by_cases hagg : isAggTy d.ty = true
            · simp only [hagg, ↓reduceIte] at hvc
              refine vcExprAgg_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
              intro bs sty s1 _ _ m1 mods1 hr1 _ ⟨hsz, hal, hbs_len, hreg_none, hrest⟩
              have hdet2 : Sem.stepDet prog cfg
                  (.running (.expr (.ret (.structVal bs sty) []) (.varInit d (rest.map Prod.fst)) mods1) env blks m1 s1.os k) =
                  some (.allocLocal d (some (.structVal bs sty)) (rest.map Prod.fst) env blks m1 s1.os k) := rfl
              refine hrules.of_localDecl_some hsz hal hdet2 fun base bid m_al hba halloc => ?_
              have hle : s1.mem.nextBlock ≤ bid :=
                Nat.le_trans hr1.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
              obtain ⟨r, m2, ms2, hwr, hwms, hr2⟩ :=
                hr1.alloc_stk_some_agg hreg_none hsz hal hba hbs_len halloc hle
              have hrest' := hrest bid hle base hba
              rw [hwms] at hrest'
              dsimp only at hrest'
              exact ⟨r, m2, hwr,
                ih (s := { s1 with stack := (d.name, bid, d.ty) :: s1.stack, mem := ms2 }) hr2 hrest'⟩
            · have haggf : isAggTy d.ty = false := Bool.eq_false_iff.mpr hagg
              simp only [haggf, Bool.false_eq_true, ↓reduceIte] at hvc
              refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
              intro rv rty s1 _ _ m1 mods1 hr1 _ hcastVC
              obtain ⟨cv, hcast_s, hsz, hal, ht, hreg_none, hrest⟩ := vcCast_sound_clean hcastVC
              have hdet2 : Sem.stepDet prog cfg
                  (.running (.expr (.ret (.rval rv rty) []) (.varInit d (rest.map Prod.fst)) mods1) env blks m1 s1.os k) =
                  some (.allocLocal d (some (.rval rv rty)) (rest.map Prod.fst) env blks m1 s1.os k) := by
                cases rv <;> rfl
              refine hrules.of_localDecl_some hsz hal hdet2 fun base bid m_al hba halloc => ?_
              have hle : s1.mem.nextBlock ≤ bid :=
                Nat.le_trans hr1.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
              have hts : ValScalarTyped d.ty.stripConst cv := by
                unfold ValScalarTyped at ht ⊢; rwa [stripConst_unqual]
              obtain ⟨r, m2, ms2, hwr, hwms, hr2⟩ :=
                hr1.alloc_stk_some_scalar (vty := rty) hreg_none hsz hal hba hcast_s hts halloc hle
              have hrest' := hrest bid hle base hba
              rw [hwms] at hrest'
              dsimp only at hrest'
              exact ⟨r, m2, hwr,
                ih (s := { s1 with stack := (d.name, bid, d.ty) :: s1.stack, mem := ms2 }) hr2 hrest'⟩
          | _ => simp [hi] at hvc
      · have hstkf : isStk = false := Bool.eq_false_iff.mpr hstk
        simp only [hstkf, Bool.false_eq_true, ↓reduceIte] at hvc
        cases hi : d.init? with
        | none =>
          simp only [hi] at hvc
          rcases hvc with ⟨hsz, hal, hstk_none, hrest⟩
          have hdet : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
              some (.allocLocal d none (rest.map Prod.fst) env blks m s.os k) := by
            unfold Sem.stepDet; simp [hsf, hi]
          refine hrules.of_localDecl_none hsz hal hdet fun base bid m1 hba halloc => ?_
          exact ih (s := { s with regs := (d.name, .undef, d.ty) :: s.regs })
            (hr.alloc_none (x := d.name) hstk_none hsz hal hba halloc) hrest
        | some init =>
          cases init with
          | expr e =>
            simp only [hi] at hvc
            have hdet1 : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
                some (.next (.running (.expr (.eval .rval e []) (.varInit d (rest.map Prod.fst)) []) env blks m s.os k)) := by
              unfold Sem.stepDet; simp [hsf, hi]
            refine hrules.of_det_state hdet1 ?_
            refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
            intro rv rty s1 _ _ m1 mods1 hr1 _ hcastVC
            obtain ⟨cv, hcast, hsz, hal, hstk_none, ht, hk_all⟩ := vcCast_sound hr1 hcastVC
            have hdet2 : Sem.stepDet prog cfg
                (.running (.expr (.ret (.rval rv rty) []) (.varInit d (rest.map Prod.fst)) mods1) env blks m1 s1.os k) =
                some (.allocLocal d (some (.rval rv rty)) (rest.map Prod.fst) env blks m1 s1.os k) := by
              cases rv <;> rfl
            refine hrules.of_localDecl_some hsz hal hdet2 fun base bid m_al hba halloc => ?_
            have hagree : ∀ b blk, m1.blocks b = some blk → m_al.blocks b = some blk := by
              intro b blk hb
              have hne : b ≠ m1.nextBlock := fun heq => by
                have hfresh := m1.fresh b (Nat.le_of_eq heq.symm)
                rw [hb] at hfresh; cases hfresh
              have hm_al : m_al = (m1.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
                  .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
              rw [hm_al, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hb]
            have hcast_al : Sem.castVal m_al d.ty.stripConst rv = some cv :=
              castVal_of_blocks_agree hagree hcast
            obtain ⟨m2, hwm, hr2⟩ := hr1.alloc_some_writeVal (x := d.name) hstk_none ht hsz hal hba halloc
            have hts : ValScalarTyped d.ty.stripConst cv := by
              unfold ValScalarTyped at ht ⊢; rwa [stripConst_unqual]
            have hwp := writePlace_rval_cast (tags := prog.tags) (vty := rty) hts hcast_al hwm
            exact ⟨.rval cv d.ty.stripConst, m2, hwp,
              ih (s := { s1 with regs := (d.name, cv, d.ty) :: s1.regs }) hr2 (vcBindVal_elim hk_all)⟩
          | _ => simp [hi] at hvc

private theorem list_lookup_some_mem {α : Type} (l : List (String × α)) {k : String} {v : α}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    unfold List.lookup at h
    by_cases heq : (k == a) = true
    · simp only [heq, Option.some.injEq] at h
      have hka : k = a := eq_of_beq heq
      subst hka h
      exact .head _
    · have hnef : (k == a) = false := Bool.eq_false_iff.mpr heq
      simp only [hnef] at h
      exact .tail _ (ih h)

theorem ContOKGen.safeUntil_mono_R {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop} {retTy : CTy} {outer : List FrameScope}
    {kp : ContPost} {k : Cont} {R1 R2 : RunState → Prop}
    (hm : ∀ u, R1 u → R2 u)
    (hk : ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R1 s) baseEnv Q retTy outer kp k) :
    ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R2 s) baseEnv Q retTy outer kp k where
  retTy_eq := hk.retTy_eq
  normal cur s env blks m hr hn := (hk.normal cur s env blks m hr hn).mono (fun _ _ _ h => h) hm
  onBreak cur s env blks m hr hb :=
    let ⟨e', b', m', k', hu, hw⟩ := hk.onBreak cur s env blks m hr hb
    ⟨e', b', m', k', hu, hw.mono (fun _ _ _ h => h) hm⟩
  onContinue cur s env blks m hr hc :=
    let ⟨c?, stp?, b, d, e', b', m', k', hu, hw⟩ := hk.onContinue cur s env blks m hr hc
    ⟨c?, stp?, b, d, e', b', m', k', hu, hw.mono (fun _ _ _ h => h) hm⟩
  onReturn cur s env blks m rv hr hret :=
    let ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s env blks m rv hr hret
    ⟨re, rb, rt, m', fs, rctx, rk, hu, hw.mono (fun _ _ _ h => h) hm⟩
  onGoto lbl cur s env blks m hr hg :=
    let ⟨s', e', b', m', k', hu, hw⟩ := hk.onGoto lbl cur s env blks m hr hg
    ⟨s', e', b', m', k', hu, hw.mono (fun _ _ _ h => h) hm⟩

theorem vcDeclList_safeNext {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {R : RunState → Prop} {contracts : ContractEnv}
    (hcs : CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) contracts)
    {baseEnv : Env} {Q : Val → Mem → OSState → Prop} {retTy : CTy} {outer : List FrameScope}
    {kp : ContPost} {k : Cont}
    (hk : ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) baseEnv Q retTy outer kp k)
    (ds : List (VarDecl × Bool)) {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem}
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcDeclList prog cfg contracts baseEnv kp ds s) :
    SafeNext prog cfg ext Q R (.running (.stmt (.decls (ds.map Prod.fst))) env blks m s.os k) := by
  let hrules := WPRules.safeUntil prog cfg ext R
  cases ds with
  | nil =>
    unfold vcDeclList at hvc
    exact SafeNext.of_det_state rfl (hk.normal cur s env blks m hr hvc)
  | cons hd rest =>
    rcases hd with ⟨d, isStk⟩
    unfold vcDeclList at hvc
    by_cases hs : d.isStatic = true
    · simp only [hs, ↓reduceIte] at hvc
      refine SafeNext.of_det_state (by unfold Sem.stepDet; simp [hs]; rfl) ?_
      exact vcDeclList_sound_gen hrules hcs hk rest hr hvc
    · have hsf : d.isStatic = false := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ↓reduceIte] at hvc
      by_cases hstk : isStk = true
      · simp only [hstk, ↓reduceIte] at hvc
        cases hi : d.init? with
        | none =>
          simp only [hi] at hvc
          rcases hvc with ⟨hsz, hal, hreg_none, hrest⟩
          have hdet : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
              some (.allocLocal d none (rest.map Prod.fst) env blks m s.os k) := by
            unfold Sem.stepDet; simp [hsf, hi]
          refine SafeNext.of_localDecl_none hdet hsz hal fun base bid m1 hba halloc => ?_
          have hle : s.mem.nextBlock ≤ bid :=
            Nat.le_trans hr.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
          exact vcDeclList_sound_gen hrules hcs hk rest
            (s := { s with
              stack := (d.name, bid, d.ty) :: s.stack
              mem := allocAt s.mem bid hle (max 1 (sizeofTy prog.tags d.ty))
                (max 1 (alignofTy prog.tags d.ty)) .rw .stack base (fun _ => .undef) hsz hal hba })
            (hr.alloc_stk_none hreg_none hsz hal hba halloc hle) (hrest bid hle base hba)
        | some init =>
          cases init with
          | expr e =>
            simp only [hi] at hvc
            have hdet1 : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
                some (.next (.running (.expr (.eval .rval e []) (.varInit d (rest.map Prod.fst)) []) env blks m s.os k)) := by
              unfold Sem.stepDet; simp [hsf, hi]
            refine SafeNext.of_det_state hdet1 ?_
            by_cases hagg : isAggTy d.ty = true
            · simp only [hagg, ↓reduceIte] at hvc
              refine vcExprAgg_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
              intro bs sty s1 _ _ m1 mods1 hr1 _ ⟨hsz, hal, hbs_len, hreg_none, hrest⟩
              have hdet2 : Sem.stepDet prog cfg
                  (.running (.expr (.ret (.structVal bs sty) []) (.varInit d (rest.map Prod.fst)) mods1) env blks m1 s1.os k) =
                  some (.allocLocal d (some (.structVal bs sty)) (rest.map Prod.fst) env blks m1 s1.os k) := rfl
              refine hrules.of_localDecl_some hsz hal hdet2 fun base bid m_al hba halloc => ?_
              have hle : s1.mem.nextBlock ≤ bid :=
                Nat.le_trans hr1.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
              obtain ⟨r, m2, ms2, hwr, hwms, hr2⟩ :=
                hr1.alloc_stk_some_agg hreg_none hsz hal hba hbs_len halloc hle
              have hrest' := hrest bid hle base hba
              rw [hwms] at hrest'
              dsimp only at hrest'
              exact ⟨r, m2, hwr,
                vcDeclList_sound_gen hrules hcs hk rest
                  (s := { s1 with stack := (d.name, bid, d.ty) :: s1.stack, mem := ms2 }) hr2 hrest'⟩
            · have haggf : isAggTy d.ty = false := Bool.eq_false_iff.mpr hagg
              simp only [haggf, Bool.false_eq_true, ↓reduceIte] at hvc
              refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
              intro rv rty s1 _ _ m1 mods1 hr1 _ hcastVC
              obtain ⟨cv, hcast_s, hsz, hal, ht, hreg_none, hrest⟩ := vcCast_sound_clean hcastVC
              have hdet2 : Sem.stepDet prog cfg
                  (.running (.expr (.ret (.rval rv rty) []) (.varInit d (rest.map Prod.fst)) mods1) env blks m1 s1.os k) =
                  some (.allocLocal d (some (.rval rv rty)) (rest.map Prod.fst) env blks m1 s1.os k) := by
                cases rv <;> rfl
              refine hrules.of_localDecl_some hsz hal hdet2 fun base bid m_al hba halloc => ?_
              have hle : s1.mem.nextBlock ≤ bid :=
                Nat.le_trans hr1.nextBlock_le (Nat.le_of_eq (congrArg Prod.fst halloc))
              have hts : ValScalarTyped d.ty.stripConst cv := by
                unfold ValScalarTyped at ht ⊢; rwa [stripConst_unqual]
              obtain ⟨r, m2, ms2, hwr, hwms, hr2⟩ :=
                hr1.alloc_stk_some_scalar (vty := rty) hreg_none hsz hal hba hcast_s hts halloc hle
              have hrest' := hrest bid hle base hba
              rw [hwms] at hrest'
              dsimp only at hrest'
              exact ⟨r, m2, hwr,
                vcDeclList_sound_gen hrules hcs hk rest
                  (s := { s1 with stack := (d.name, bid, d.ty) :: s1.stack, mem := ms2 }) hr2 hrest'⟩
          | _ => simp [hi] at hvc
      · have hstkf : isStk = false := Bool.eq_false_iff.mpr hstk
        simp only [hstkf, Bool.false_eq_true, ↓reduceIte] at hvc
        cases hi : d.init? with
        | none =>
          simp only [hi] at hvc
          rcases hvc with ⟨hsz, hal, hstk_none, hrest⟩
          have hdet : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
              some (.allocLocal d none (rest.map Prod.fst) env blks m s.os k) := by
            unfold Sem.stepDet; simp [hsf, hi]
          refine SafeNext.of_localDecl_none hdet hsz hal fun base bid m1 hba halloc => ?_
          exact vcDeclList_sound_gen hrules hcs hk rest
            (s := { s with regs := (d.name, .undef, d.ty) :: s.regs })
            (hr.alloc_none (x := d.name) hstk_none hsz hal hba halloc) hrest
        | some init =>
          cases init with
          | expr e =>
            simp only [hi] at hvc
            have hdet1 : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest.map Prod.fst))) env blks m s.os k) =
                some (.next (.running (.expr (.eval .rval e []) (.varInit d (rest.map Prod.fst)) []) env blks m s.os k)) := by
              unfold Sem.stepDet; simp [hsf, hi]
            refine SafeNext.of_det_state hdet1 ?_
            refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
            intro rv rty s1 _ _ m1 mods1 hr1 _ hcastVC
            obtain ⟨cv, hcast, hsz, hal, hstk_none, ht, hk_all⟩ := vcCast_sound hr1 hcastVC
            have hdet2 : Sem.stepDet prog cfg
                (.running (.expr (.ret (.rval rv rty) []) (.varInit d (rest.map Prod.fst)) mods1) env blks m1 s1.os k) =
                some (.allocLocal d (some (.rval rv rty)) (rest.map Prod.fst) env blks m1 s1.os k) := by
              cases rv <;> rfl
            refine hrules.of_localDecl_some hsz hal hdet2 fun base bid m_al hba halloc => ?_
            have hagree : ∀ b blk, m1.blocks b = some blk → m_al.blocks b = some blk := by
              intro b blk hb
              have hne : b ≠ m1.nextBlock := fun heq => by
                have hfresh := m1.fresh b (Nat.le_of_eq heq.symm)
                rw [hb] at hfresh; cases hfresh
              have hm_al : m_al = (m1.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
                  .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd halloc).symm
              rw [hm_al, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hb]
            have hcast_al : Sem.castVal m_al d.ty.stripConst rv = some cv :=
              castVal_of_blocks_agree hagree hcast
            obtain ⟨m2, hwm, hr2⟩ := hr1.alloc_some_writeVal (x := d.name) hstk_none ht hsz hal hba halloc
            have hts : ValScalarTyped d.ty.stripConst cv := by
              unfold ValScalarTyped at ht ⊢; rwa [stripConst_unqual]
            have hwp := writePlace_rval_cast (tags := prog.tags) (vty := rty) hts hcast_al hwm
            exact ⟨.rval cv d.ty.stripConst, m2, hwp,
              vcDeclList_sound_gen hrules hcs hk rest
                (s := { s1 with regs := (d.name, cv, d.ty) :: s1.regs }) hr2 (vcBindVal_elim hk_all)⟩
          | _ => simp [hi] at hvc

private theorem whileLoop_safeNext {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig)
    (contracts : ContractEnv) (baseEnv : Env) (Q : Val → Mem → OSState → Prop) (R : RunState → Prop)
    (retTy : CTy) (hcs_safe : ∀ R', CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R' s) contracts)
    (outer : List FrameScope) (kp : ContPost) (k : Cont)
    (cur : FrameScope) (s : SymState) (env : Env) (blks : List BlockId) (m : Mem)
    (c : CExpr) (body : AnnStmt) (Inv : SymState → Nat → SymState → Prop)
    (hk : ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hinv0 : Inv s 0 s)
    (hstep_vc : ∀ n s1, n = 0 ∧ Inv s 0 s1 →
      vcExprR prog cfg contracts baseEnv s1 [] [] c fun vc _ s2 _ _ =>
        vcBranch vc
          (vcStmtGen false prog cfg contracts baseEnv retTy
            { normal := fun s3 => Inv s 0 s3
              onBreak := kp.normal
              onContinue := fun s3 => Inv s 0 s3
              onReturn := kp.onReturn
              onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
            s2 body)
          (kp.normal s2))
    (hsound_body : ∀ (R' : RunState → Prop) kp' k' cur' s' env' blks' m',
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp' k' →
      Refines prog.tags baseEnv cur' outer s' env' blks' m' →
      vcStmtGen false prog cfg contracts baseEnv retTy kp' s' body →
      SafeUntil prog cfg ext Q R' (.running (.stmt body.erase) env' blks' m' s'.os k')) :
    SafeNext prog cfg ext Q R (.running (.stmt (.whileStmt c body.erase)) env blks m s.os k) := by
  let kBody : ContPost :=
    { normal := fun s3 => Inv s 0 s3
      onBreak := kp.normal
      onContinue := fun s3 => Inv s 0 s3
      onReturn := kp.onReturn
      onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
  let P : RunState → Prop := fun st =>
    ∃ cur' s1 env' blks' m',
      Refines prog.tags baseEnv cur' outer s1 env' blks' m' ∧ Inv s 0 s1 ∧
      st = .running (.expr (.eval .rval c []) (.forCond c none body.erase) []) env' blks' m' s1.os k
  let R' : RunState → Prop := fun u => P u ∨ R u
  have hk' : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp k :=
    hk.safeUntil_mono_R (fun _ => Or.inr)
  have hstep_p : ∀ st, P st → SafeNext prog cfg ext Q R' st := by
    rintro st ⟨cur', s1, env', blks', m', hr1, hinv1, rfl⟩
    refine vcExprR_safeNext (hcs_safe R') hr1 (ModsOK.nil cur' outer [] []) (hstep_vc 0 s1 ⟨rfl, hinv1⟩) ?_
    intro vc _ s2 _ _ m2 _ hr2 _ hbr
    obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
    refine SafeUntil.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hk'.normal cur' s2 env' blks' m2 hr2 (hf rfl)
    · simp only [↓reduceIte]
      have hkLoop : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kBody
          (.loop (some c) none body.erase false k) := by
        refine ⟨hk'.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
        · intro cur3 s3 env3 blks3 m3 hr3 hinv3
          exact SafeUntil.of_det_state rfl (SafeUntil.done (.inl ⟨cur3, s3, env3, blks3, m3, hr3, hinv3, rfl⟩))
        · intro cur3 s3 env3 blks3 m3 hr3 hb3
          exact ⟨env3, blks3, m3, k, rfl, hk'.normal cur3 s3 env3 blks3 m3 hr3 hb3⟩
        · intro cur3 s3 env3 blks3 m3 hr3 hinv3
          exact ⟨some c, none, body.erase, false, env3, blks3, m3, k, rfl,
            SafeUntil.done (.inl ⟨cur3, s3, env3, blks3, m3, hr3, hinv3, rfl⟩)⟩
        · intro cur3 s3 env3 blks3 m3 rv hr3 hret3
          unfold Sem.unwindReturn
          exact hk'.onReturn cur3 s3 env3 blks3 m3 rv hr3 hret3
        · intro lbl cur3 s3 env3 blks3 m3 hr3 ⟨hna, hkg⟩
          unfold Sem.gotoInCont
          rw [AnnStmt.annHasLabel_erase_none hna env3 blks3 _]
          exact hk'.onGoto lbl cur3 s3 env3 blks3 m3 hr3 hkg
      exact hsound_body R' kBody (.loop (some c) none body.erase false k) cur' s2 env' blks' m2 hkLoop hr2 (ht rfl)
  refine SafeNext.of_det_state rfl ?_
  refine vcExprR_sound_gen (WPRules.safeUntil prog cfg ext R) (hcs_safe R) hr (ModsOK.nil cur outer [] [])
    (hstep_vc 0 s ⟨rfl, hinv0⟩) ?_
  intro vc _ s2 _ _ m2 _ hr2 _ hbr
  obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
  refine SafeUntil.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hk.normal cur s2 env blks m2 hr2 (hf rfl)
  · simp only [↓reduceIte]
    have hkLoop : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R u) baseEnv Q retTy outer kBody
        (.loop (some c) none body.erase false k) := by
      refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
      · intro cur3 s3 env3 blks3 m3 hr3 hinv3
        refine SafeUntil.of_det_state rfl ?_
        exact SafeUntil.loop_wf_unbounded ⟨cur3, s3, env3, blks3, m3, hr3, hinv3, rfl⟩ hstep_p
      · intro cur3 s3 env3 blks3 m3 hr3 hb3
        exact ⟨env3, blks3, m3, k, rfl, hk.normal cur3 s3 env3 blks3 m3 hr3 hb3⟩
      · intro cur3 s3 env3 blks3 m3 hr3 hinv3
        refine ⟨some c, none, body.erase, false, env3, blks3, m3, k, rfl, ?_⟩
        exact SafeUntil.loop_wf_unbounded ⟨cur3, s3, env3, blks3, m3, hr3, hinv3, rfl⟩ hstep_p
      · intro cur3 s3 env3 blks3 m3 rv hr3 hret3
        unfold Sem.unwindReturn
        exact hk.onReturn cur3 s3 env3 blks3 m3 rv hr3 hret3
      · intro lbl cur3 s3 env3 blks3 m3 hr3 ⟨hna, hkg⟩
        unfold Sem.gotoInCont
        rw [AnnStmt.annHasLabel_erase_none hna env3 blks3 _]
        exact hk.onGoto lbl cur3 s3 env3 blks3 m3 hr3 hkg
    exact hsound_body R kBody (.loop (some c) none body.erase false k) cur s2 env blks m2 hkLoop hr2 (ht rfl)

private theorem doWhileLoop_safeNext {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig)
    (contracts : ContractEnv) (baseEnv : Env) (Q : Val → Mem → OSState → Prop) (R : RunState → Prop)
    (retTy : CTy) (hcs_safe : ∀ R', CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R' s) contracts)
    (outer : List FrameScope) (kp : ContPost) (k : Cont)
    (cur : FrameScope) (s : SymState) (env : Env) (blks : List BlockId) (m : Mem)
    (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop)
    (hk : ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hinv0 : Inv s 0 s)
    (hstep_vc : ∀ n s1, n = 0 ∧ Inv s 0 s1 →
      let afterBody := fun s2 =>
        vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
          vcBranch vc (Inv s 0 s3) (kp.normal s3)
      vcStmtGen false prog cfg contracts baseEnv retTy
        { normal := afterBody
          onBreak := kp.normal
          onContinue := afterBody
          onReturn := kp.onReturn
          onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
        s1 body)
    (hsound_body_next : ∀ (R' : RunState → Prop) kp' k' cur' s' env' blks' m',
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp' k' →
      (∀ cur2 s2 env2 blks2 m2,
        Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
        kp'.normal s2 →
        SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os k')) →
      Refines prog.tags baseEnv cur' outer s' env' blks' m' →
      vcStmtGen false prog cfg contracts baseEnv retTy kp' s' body →
      SafeNext prog cfg ext Q R' (.running (.stmt body.erase) env' blks' m' s'.os k')) :
    SafeNext prog cfg ext Q R (.running (.stmt (.doWhileStmt body.erase c)) env blks m s.os k) := by
  let afterBody : SymState → Prop := fun s2 =>
    vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
      vcBranch vc (Inv s 0 s3) (kp.normal s3)
  let kLoop : ContPost :=
    { normal := afterBody
      onBreak := kp.normal
      onContinue := afterBody
      onReturn := kp.onReturn
      onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
  let P : RunState → Prop := fun st =>
    ∃ cur' s1 env' blks' m',
      Refines prog.tags baseEnv cur' outer s1 env' blks' m' ∧ Inv s 0 s1 ∧
      st = .running (.stmt body.erase) env' blks' m' s1.os (.loop (some c) none body.erase true k)
  let R' : RunState → Prop := fun u => P u ∨ R u
  have hk' : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp k :=
    hk.safeUntil_mono_R (fun _ => Or.inr)
  have hcond_next : ∀ cur2 s2 env2 blks2 m2,
      Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
      afterBody s2 →
      SafeNext prog cfg ext Q R'
        (.running (.expr (.eval .rval c []) (.doWhileCond body.erase c) []) env2 blks2 m2 s2.os k) := by
    intro cur2 s2 env2 blks2 m2 hr2 hab
    refine vcExprR_safeNext (hcs_safe R') hr2 (ModsOK.nil cur2 outer [] []) hab ?_
    intro vc _ s3 _ _ m3 _ hr3 _ hbr
    obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
    refine SafeUntil.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hk'.normal cur2 s3 env2 blks2 m3 hr3 (hf rfl)
    · simp only [↓reduceIte]
      exact SafeUntil.done (.inl ⟨cur2, s3, env2, blks2, m3, hr3, ht rfl, rfl⟩)
  have hkLoop : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kLoop
      (.loop (some c) none body.erase true k) := by
    refine ⟨hk'.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
    · intro cur2 s2 env2 blks2 m2 hr2 hab
      exact (SafeNext.of_det_state rfl (hcond_next cur2 s2 env2 blks2 m2 hr2 hab).to_safeUntil).to_safeUntil
    · intro cur2 s2 env2 blks2 m2 hr2 hb2
      exact ⟨env2, blks2, m2, k, rfl, hk'.normal cur2 s2 env2 blks2 m2 hr2 hb2⟩
    · intro cur2 s2 env2 blks2 m2 hr2 hab
      refine ⟨some c, none, body.erase, true, env2, blks2, m2, k, rfl, ?_⟩
      exact (hcond_next cur2 s2 env2 blks2 m2 hr2 hab).to_safeUntil
    · intro cur2 s2 env2 blks2 m2 rv hr2 hret2
      unfold Sem.unwindReturn
      exact hk'.onReturn cur2 s2 env2 blks2 m2 rv hr2 hret2
    · intro lbl cur2 s2 env2 blks2 m2 hr2 ⟨hna, hkg⟩
      unfold Sem.gotoInCont
      rw [AnnStmt.annHasLabel_erase_none hna env2 blks2 _]
      exact hk'.onGoto lbl cur2 s2 env2 blks2 m2 hr2 hkg
  have hk_norm_next : ∀ cur2 s2 env2 blks2 m2,
      Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
      kLoop.normal s2 →
      SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os (.loop (some c) none body.erase true k)) := by
    intro cur2 s2 env2 blks2 m2 hr2 hab
    exact SafeNext.of_det_state rfl (hcond_next cur2 s2 env2 blks2 m2 hr2 hab).to_safeUntil
  have hstep_p : ∀ st, P st → SafeNext prog cfg ext Q R' st := by
    rintro st ⟨cur', s1, env', blks', m', hr1, hinv1, rfl⟩
    exact hsound_body_next R' kLoop (.loop (some c) none body.erase true k)
      cur' s1 env' blks' m' hkLoop hk_norm_next hr1 (hstep_vc 0 s1 ⟨rfl, hinv1⟩)
  exact SafeNext.of_det_state rfl
    (SafeUntil.loop_wf_unbounded ⟨cur, s, env, blks, m, hr, hinv0, rfl⟩ hstep_p)

private theorem doWhileGotos_safeNext {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig)
    (contracts : ContractEnv) (baseEnv : Env) (Q : Val → Mem → OSState → Prop) (R : RunState → Prop)
    (retTy : CTy) (hcs_safe : ∀ R', CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R' s) contracts)
    (outer : List FrameScope) (kp : ContPost) (k : Cont)
    (cur : FrameScope) (s : SymState) (env : Env) (blks : List BlockId) (m : Mem)
    (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop)
    (gotoSpecs : List (String × (SymState → Nat → SymState → Prop)))
    (hk : ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hinv0 : Inv s 0 s)
    (hstep_vc : ∀ n s1, n = 0 ∧ Inv s 0 s1 →
      let afterBody := fun s2 =>
        vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
          vcBranch vc (Inv s 0 s3) (kp.normal s3)
      vcStmtGen false prog cfg contracts baseEnv retTy
        { normal := afterBody
          onBreak := kp.normal
          onContinue := afterBody
          onReturn := kp.onReturn
          onGoto := fun lbl s3 =>
            match gotoSpecs.lookup lbl with
            | some GSpec => GSpec s 0 s3
            | none => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
        s1 body)
    (hgoto_vc : ∀ p ∈ gotoSpecs,
      match AnnStmt.findGotoAnn p.1 body with
      | none => False
      | some (tgt, fs) =>
        ∀ n sG, n = 0 ∧ p.2 s 0 sG →
          let afterBody := fun s2 =>
            vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
              vcBranch vc (Inv s 0 s3) (kp.normal s3)
          let kLoop : ContPost :=
            { normal := afterBody
              onBreak := kp.normal
              onContinue := afterBody
              onReturn := kp.onReturn
              onGoto := fun lbl s3 =>
                match gotoSpecs.lookup lbl with
                | some GSpec => GSpec s 0 s3
                | none => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
          vcStmtGen false prog cfg contracts baseEnv retTy
            (vcFramesCont false prog cfg contracts baseEnv retTy kLoop sG fs) sG tgt)
    (hsound_body_next : ∀ (R' : RunState → Prop) kp' k' cur' s' env' blks' m',
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp' k' →
      (∀ cur2 s2 env2 blks2 m2,
        Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
        kp'.normal s2 →
        SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os k')) →
      Refines prog.tags baseEnv cur' outer s' env' blks' m' →
      vcStmtGen false prog cfg contracts baseEnv retTy kp' s' body →
      SafeNext prog cfg ext Q R' (.running (.stmt body.erase) env' blks' m' s'.os k'))
    (hsound_tgt_next : ∀ tgt fs (R' : RunState → Prop) outer' kp' k' cur' s' env' blks' m',
      sizeOf tgt + AnnStmt.framesSize fs < sizeOf body →
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer' kp' k' →
      (∀ cur2 s2 env2 blks2 m2,
        Refines prog.tags baseEnv cur2 outer' s2 env2 blks2 m2 →
        kp'.normal s2 →
        SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os k')) →
      Refines prog.tags baseEnv cur' outer' s' env' blks' m' →
      vcStmtGen false prog cfg contracts baseEnv retTy kp' s' tgt →
      SafeNext prog cfg ext Q R' (.running (.stmt tgt.erase) env' blks' m' s'.os k'))
    (hframes_ok : ∀ (tgt : AnnStmt) fs (R' : RunState → Prop) kp' k' cur' s' env' blks' m',
      sizeOf tgt + AnnStmt.framesSize fs < sizeOf body →
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp' k' →
      Refines prog.tags baseEnv cur' outer s' env' blks' m' →
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy
        (framesScopes cur' outer fs).2
        (vcFramesCont false prog cfg contracts baseEnv retTy kp' s' fs)
        (AnnStmt.gotoFramesCont env' blks' k' fs).2 ∧
      Refines prog.tags baseEnv (framesScopes cur' outer fs).1 (framesScopes cur' outer fs).2
        s' env' (AnnStmt.gotoFramesCont env' blks' k' fs).1 m' ∧
      ((∀ cur2 s2 env2 blks2 m2,
          Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
          kp'.normal s2 →
          SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os k')) →
        ∀ cur2 s2 env2 blks2 m2,
          Refines prog.tags baseEnv cur2 (framesScopes cur' outer fs).2 s2 env2 blks2 m2 →
          (vcFramesCont false prog cfg contracts baseEnv retTy kp' s' fs).normal s2 →
          SafeNext prog cfg ext Q R'
            (.running (.stmt .nop) env2 blks2 m2 s2.os (AnnStmt.gotoFramesCont env' blks' k' fs).2))) :
    SafeNext prog cfg ext Q R (.running (.stmt (.doWhileStmt body.erase c)) env blks m s.os k) := by
  let afterBody : SymState → Prop := fun s2 =>
    vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
      vcBranch vc (Inv s 0 s3) (kp.normal s3)
  let kLoop : ContPost :=
    { normal := afterBody
      onBreak := kp.normal
      onContinue := afterBody
      onReturn := kp.onReturn
      onGoto := fun lbl s3 =>
        match gotoSpecs.lookup lbl with
        | some GSpec => GSpec s 0 s3
        | none => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
  let P : RunState → Prop := fun st =>
    (∃ cur' s1 env' blks' m',
      Refines prog.tags baseEnv cur' outer s1 env' blks' m' ∧ Inv s 0 s1 ∧
      st = .running (.stmt body.erase) env' blks' m' s1.os (.loop (some c) none body.erase true k)) ∨
    (∃ lbl GSpec tgt fs cur' sG env' blks' m',
      (lbl, GSpec) ∈ gotoSpecs ∧
      AnnStmt.findGotoAnn lbl body = some (tgt, fs) ∧
      Refines prog.tags baseEnv cur' outer sG env' blks' m' ∧ GSpec s 0 sG ∧
      st = .running (.stmt tgt.erase) env'
        (AnnStmt.gotoFramesCont env' blks' (.loop (some c) none body.erase true k) fs).1 m' sG.os
        (AnnStmt.gotoFramesCont env' blks' (.loop (some c) none body.erase true k) fs).2)
  let R' : RunState → Prop := fun u => P u ∨ R u
  have hk' : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp k :=
    hk.safeUntil_mono_R (fun _ => Or.inr)
  have hcond_next : ∀ cur2 s2 env2 blks2 m2,
      Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
      afterBody s2 →
      SafeNext prog cfg ext Q R'
        (.running (.expr (.eval .rval c []) (.doWhileCond body.erase c) []) env2 blks2 m2 s2.os k) := by
    intro cur2 s2 env2 blks2 m2 hr2 hab
    refine vcExprR_safeNext (hcs_safe R') hr2 (ModsOK.nil cur2 outer [] []) hab ?_
    intro vc _ s3 _ _ m3 _ hr3 _ hbr
    obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
    refine SafeUntil.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hk'.normal cur2 s3 env2 blks2 m3 hr3 (hf rfl)
    · simp only [↓reduceIte]
      exact SafeUntil.done (.inl (.inl ⟨cur2, s3, env2, blks2, m3, hr3, ht rfl, rfl⟩))
  have hkLoop : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kLoop
      (.loop (some c) none body.erase true k) := by
    refine ⟨hk'.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
    · intro cur2 s2 env2 blks2 m2 hr2 hab
      exact (SafeNext.of_det_state rfl (hcond_next cur2 s2 env2 blks2 m2 hr2 hab).to_safeUntil).to_safeUntil
    · intro cur2 s2 env2 blks2 m2 hr2 hb2
      exact ⟨env2, blks2, m2, k, rfl, hk'.normal cur2 s2 env2 blks2 m2 hr2 hb2⟩
    · intro cur2 s2 env2 blks2 m2 hr2 hab
      refine ⟨some c, none, body.erase, true, env2, blks2, m2, k, rfl, ?_⟩
      exact (hcond_next cur2 s2 env2 blks2 m2 hr2 hab).to_safeUntil
    · intro cur2 s2 env2 blks2 m2 rv hr2 hret2
      unfold Sem.unwindReturn
      exact hk'.onReturn cur2 s2 env2 blks2 m2 rv hr2 hret2
    · intro lbl cur2 s2 env2 blks2 m2 hr2 hkg
      dsimp only [kLoop] at hkg
      cases hgl : gotoSpecs.lookup lbl with
      | none =>
        simp only [hgl] at hkg
        unfold Sem.gotoInCont
        rw [AnnStmt.annHasLabel_erase_none hkg.1 env2 blks2 _]
        exact hk'.onGoto lbl cur2 s2 env2 blks2 m2 hr2 hkg.2
      | some GSpec =>
        simp only [hgl] at hkg
        have hmem := list_lookup_some_mem gotoSpecs hgl
        have hgs := hgoto_vc (lbl, GSpec) hmem
        split at hgs
        · cases hgs
        · rename_i tgt fs hgt
          have hfind := AnnStmt.findGotoAnn_erase hgt env2 blks2 (.loop (some c) none body.erase true k)
          refine ⟨tgt.erase, env2,
            (AnnStmt.gotoFramesCont env2 blks2 (.loop (some c) none body.erase true k) fs).1, m2,
            (AnnStmt.gotoFramesCont env2 blks2 (.loop (some c) none body.erase true k) fs).2, ?_, ?_⟩
          · unfold Sem.gotoInCont; rw [hfind]
          · exact SafeUntil.done (.inl (.inr ⟨lbl, GSpec, tgt, fs, cur2, s2, env2, blks2, m2, hmem, hgt, hr2, hkg, rfl⟩))
  have hk_norm_next : ∀ cur2 s2 env2 blks2 m2,
      Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
      kLoop.normal s2 →
      SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os (.loop (some c) none body.erase true k)) := by
    intro cur2 s2 env2 blks2 m2 hr2 hab
    exact SafeNext.of_det_state rfl (hcond_next cur2 s2 env2 blks2 m2 hr2 hab).to_safeUntil
  have hstep_p : ∀ st, P st → SafeNext prog cfg ext Q R' st := by
    rintro st (⟨cur', s1, env', blks', m', hr1, hinv1, rfl⟩ |
      ⟨lbl, GSpec, tgt, fs, cur', sG, env', blks', m', hmem, hgt, hrG, hgs, rfl⟩)
    · exact hsound_body_next R' kLoop (.loop (some c) none body.erase true k)
        cur' s1 env' blks' m' hkLoop hk_norm_next hr1 (hstep_vc 0 s1 ⟨rfl, hinv1⟩)
    · have hgt_vc := hgoto_vc (lbl, GSpec) hmem
      split at hgt_vc
      · cases hgt_vc
      · rename_i tgt' fs' hgt'
        rw [hgt] at hgt'; cases hgt'
        have hvc_tgt := hgt_vc 0 sG ⟨rfl, hgs⟩
        have hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf body := AnnStmt.findGotoAnn_sizeOf_lt hgt
        obtain ⟨hkF, hrF, hnextF⟩ :=
          hframes_ok tgt fs R' kLoop (.loop (some c) none body.erase true k) cur' sG env' blks' m' hlt hkLoop hrG
        exact hsound_tgt_next tgt fs R' (framesScopes cur' outer fs).2
          (vcFramesCont false prog cfg contracts baseEnv retTy kLoop sG fs)
          (AnnStmt.gotoFramesCont env' blks' (.loop (some c) none body.erase true k) fs).2
          (framesScopes cur' outer fs).1 sG env'
          (AnnStmt.gotoFramesCont env' blks' (.loop (some c) none body.erase true k) fs).1 m'
          hlt hkF (hnextF hk_norm_next) hrF hvc_tgt
  exact SafeNext.of_det_state rfl
    (SafeUntil.loop_wf_unbounded (.inl ⟨cur, s, env, blks, m, hr, hinv0, rfl⟩) hstep_p)

private def forHdrState (c? stp? : Option CExpr) (body : CStmt)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont) : RunState :=
  match c? with
  | some c => .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k
  | none => .running (.stmt body) env blks m os (.loop none stp? body false k)

private def forAfterBody (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (stp? : Option CExpr) (P : SymState → Prop) (s2 : SymState) : Prop :=
  match stp? with
  | none => P s2
  | some stp => vcExprDiscard prog cfg contracts baseEnv s2 [] [] stp fun s3 _ _ => P s3

private theorem stepDet_forStep (prog : Prog) (cfg : PointerConfig) (res : ExprRes)
    (c? stp? : Option CExpr) (body : CStmt) (mods : ModSet) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (k : Cont) :
    Sem.stepDet prog cfg
      (.running (.expr (.ret res []) (.forStep c? stp? body) mods) env blks m os k) =
      some (.next (forHdrState c? stp? body env blks m os k)) := by
  cases res with
  | rval v _ => cases v <;> cases c? <;> rfl
  | lval _ _ _ | structVal _ _ => cases c? <;> rfl

private theorem stepDet_forStmt_none (prog : Prog) (cfg : PointerConfig)
    (c? stp? : Option CExpr) (body : CStmt) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (k : Cont) :
    Sem.stepDet prog cfg (.running (.stmt (.forStmt none c? stp? body)) env blks m os k) =
      some (.next (forHdrState c? stp? body env blks m os k)) := by
  cases c? <;> rfl

private theorem loopNext_none_eq_forHdrState (c? : Option CExpr) (body : CStmt)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont) :
    Sem.loopNext c? none body false env blks m os k =
      forHdrState c? none body env blks m os k := by
  cases c? <;> rfl

private theorem forLoop_safeNext {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig)
    (contracts : ContractEnv) (baseEnv : Env) (Q : Val → Mem → OSState → Prop) (R : RunState → Prop)
    (retTy : CTy) (hcs_safe : ∀ R', CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R' s) contracts)
    (outer : List FrameScope) (kp : ContPost) (k : Cont)
    (cur : FrameScope) (s : SymState) (env : Env) (blks : List BlockId) (m : Mem)
    (init? c? stp? : Option CExpr) (body : AnnStmt) (Inv : SymState → Nat → SymState → Prop)
    (hk : ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hinit_vc : match init? with
      | none => Inv s 0 s
      | some init => vcExprDiscard prog cfg contracts baseEnv s [] [] init fun s0 _ _ => Inv s 0 s0)
    (hstep_vc : ∀ s1, Inv s 0 s1 →
      let kLoop : ContPost :=
        { normal := forAfterBody prog cfg contracts baseEnv stp? (Inv s 0)
          onBreak := kp.normal
          onContinue := forAfterBody prog cfg contracts baseEnv stp? (Inv s 0)
          onReturn := kp.onReturn
          onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
      match c? with
      | some c =>
        vcExprR prog cfg contracts baseEnv s1 [] [] c fun vc _ s2 _ _ =>
          vcBranch vc (vcStmtGen false prog cfg contracts baseEnv retTy kLoop s2 body) (kp.normal s2)
      | none => vcStmtGen false prog cfg contracts baseEnv retTy kLoop s1 body)
    (hsound_body : ∀ (R' : RunState → Prop) kp' k' cur' s' env' blks' m',
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp' k' →
      Refines prog.tags baseEnv cur' outer s' env' blks' m' →
      vcStmtGen false prog cfg contracts baseEnv retTy kp' s' body →
      SafeUntil prog cfg ext Q R' (.running (.stmt body.erase) env' blks' m' s'.os k'))
    (hsound_body_next : ∀ (R' : RunState → Prop) kp' k' cur' s' env' blks' m',
      ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp' k' →
      (∀ cur2 s2 env2 blks2 m2,
        Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
        kp'.normal s2 →
        SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os k')) →
      Refines prog.tags baseEnv cur' outer s' env' blks' m' →
      vcStmtGen false prog cfg contracts baseEnv retTy kp' s' body →
      SafeNext prog cfg ext Q R' (.running (.stmt body.erase) env' blks' m' s'.os k')) :
    SafeNext prog cfg ext Q R (.running (.stmt (.forStmt init? c? stp? body.erase)) env blks m s.os k) := by
  let kLoop : ContPost :=
    { normal := forAfterBody prog cfg contracts baseEnv stp? (Inv s 0)
      onBreak := kp.normal
      onContinue := forAfterBody prog cfg contracts baseEnv stp? (Inv s 0)
      onReturn := kp.onReturn
      onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
  let P : RunState → Prop := fun st =>
    ∃ cur' s1 env' blks' m',
      Refines prog.tags baseEnv cur' outer s1 env' blks' m' ∧ Inv s 0 s1 ∧
      st = forHdrState c? stp? body.erase env' blks' m' s1.os k
  let R' : RunState → Prop := fun u => P u ∨ R u
  have hk' : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kp k :=
    hk.safeUntil_mono_R (fun _ => Or.inr)
  have hafter : ∀ cur2 s2 env2 blks2 m2,
      Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
      forAfterBody prog cfg contracts baseEnv stp? (Inv s 0) s2 →
      SafeUntil prog cfg ext Q R' (Sem.loopNext c? stp? body.erase false env2 blks2 m2 s2.os k) := by
    intro cur2 s2 env2 blks2 m2 hr2 hab
    cases stp? with
    | none =>
      dsimp only [forAfterBody] at hab
      rw [loopNext_none_eq_forHdrState]
      exact SafeUntil.done (.inl ⟨cur2, s2, env2, blks2, m2, hr2, hab, rfl⟩)
    | some stp =>
      dsimp only [forAfterBody] at hab
      change SafeUntil prog cfg ext Q R'
        (.running (.expr (.eval .rval stp []) (.forStep c? (some stp) body.erase) []) env2 blks2 m2 s2.os k)
      refine vcExprDiscard_sound_gen (WPRules.safeUntil prog cfg ext R') (hcs_safe R') hr2
          (ModsOK.nil cur2 outer [] []) hab ?_
      intro res s3 _ _ m3 _ hr3 _ hinv3
      exact SafeUntil.of_det_state (stepDet_forStep prog cfg res c? (some stp) body.erase _ env2 blks2 m3 s3.os k)
        (SafeUntil.done (.inl ⟨cur2, s3, env2, blks2, m3, hr3, hinv3, rfl⟩))
  have hkLoop : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R' u) baseEnv Q retTy outer kLoop
      (.loop c? stp? body.erase false k) := by
    refine ⟨hk'.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
    · intro cur2 s2 env2 blks2 m2 hr2 hab
      exact SafeUntil.of_det_state rfl (hafter cur2 s2 env2 blks2 m2 hr2 hab)
    · intro cur2 s2 env2 blks2 m2 hr2 hb2
      exact ⟨env2, blks2, m2, k, rfl, hk'.normal cur2 s2 env2 blks2 m2 hr2 hb2⟩
    · intro cur2 s2 env2 blks2 m2 hr2 hab
      exact ⟨c?, stp?, body.erase, false, env2, blks2, m2, k, rfl,
        hafter cur2 s2 env2 blks2 m2 hr2 hab⟩
    · intro cur2 s2 env2 blks2 m2 rv hr2 hret2
      unfold Sem.unwindReturn
      exact hk'.onReturn cur2 s2 env2 blks2 m2 rv hr2 hret2
    · intro lbl cur2 s2 env2 blks2 m2 hr2 ⟨hna, hkg⟩
      unfold Sem.gotoInCont
      rw [AnnStmt.annHasLabel_erase_none hna env2 blks2 (.loop c? stp? body.erase false k)]
      exact hk'.onGoto lbl cur2 s2 env2 blks2 m2 hr2 hkg
  have hk_norm_next : ∀ cur2 s2 env2 blks2 m2,
      Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
      kLoop.normal s2 →
      SafeNext prog cfg ext Q R' (.running (.stmt .nop) env2 blks2 m2 s2.os (.loop c? stp? body.erase false k)) := by
    intro cur2 s2 env2 blks2 m2 hr2 hab
    exact SafeNext.of_det_state rfl (hafter cur2 s2 env2 blks2 m2 hr2 hab)
  have hstep_p : ∀ st, P st → SafeNext prog cfg ext Q R' st := by
    rintro st ⟨cur', s1, env', blks', m', hr1, hinv1, rfl⟩
    have hvc1 := hstep_vc s1 hinv1
    clear hstep_vc
    cases c? with
    | some c =>
      dsimp only [forHdrState] at hvc1 ⊢
      refine vcExprR_safeNext (hcs_safe R') hr1 (ModsOK.nil cur' outer [] []) hvc1 ?_
      intro vc _ s2 _ _ m2 _ hr2 _ hbr
      obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
      refine SafeUntil.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hk'.normal cur' s2 env' blks' m2 hr2 (hf rfl)
      · simp only [↓reduceIte]
        have hvc_b : vcStmtGen false prog cfg contracts baseEnv retTy kLoop s2 body := ht rfl
        exact hsound_body R' kLoop (.loop (some c) stp? body.erase false k) cur' s2 env' blks' m2 hkLoop hr2 hvc_b
    | none =>
      dsimp only [forHdrState] at hvc1 ⊢
      exact hsound_body_next R' kLoop (.loop none stp? body.erase false k)
        cur' s1 env' blks' m' hkLoop hk_norm_next hr1 hvc1
  cases init? with
  | none =>
    dsimp only at hinit_vc
    refine SafeNext.of_det_state (stepDet_forStmt_none prog cfg c? stp? body.erase env blks m s.os k) ?_
    exact SafeUntil.loop_wf_unbounded ⟨cur, s, env, blks, m, hr, hinit_vc, rfl⟩ hstep_p
  | some init =>
    dsimp only at hinit_vc
    refine SafeNext.of_det_state rfl ?_
    refine vcExprDiscard_sound_gen (WPRules.safeUntil prog cfg ext R) (hcs_safe R) hr
      (ModsOK.nil cur outer [] []) hinit_vc ?_
    intro res s0 _ _ m0 _ hr0 _ hinv_s0
    exact SafeUntil.of_det_state (stepDet_forStep prog cfg res c? stp? body.erase _ env blks m0 s0.os k)
      (SafeUntil.loop_wf_unbounded ⟨cur, s0, env, blks, m0, hr0, hinv_s0, rfl⟩ hstep_p)

/-! ## Unified Statement Soundness (`vcStmtGen_sound_aux`) -/

private theorem vcStmtGen_sound_aux {ext : ExtHandler} (prog : Prog) (cfg : PointerConfig)
    (contracts : ContractEnv) (baseEnv : Env)
    (Q : Val → Mem → OSState → Prop) (retTy : CTy) (strict : Bool)
    (hcs_term : strict = true → CallContractsSound prog cfg (WPTerm prog cfg ext) contracts)
    (hcs_safe : ∀ R, CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) contracts) :
    (x : (AnnStmt × Bool) ⊕ List AnnStmt ⊕ List AnnStmt.GotoFrame) →
      match x with
      | .inl (stmt, false) =>
        ∀ W, WPRules prog cfg ext W → CallContractsSound prog cfg W contracts →
          ((strict = true ∧ (W = WPTerm prog cfg ext ∨ ∃ R, W = fun Q' s => SafeUntil prog cfg ext Q' R s)) ∨
           (strict = false ∧ ∃ R, W = fun Q' s => SafeUntil prog cfg ext Q' R s)) →
          ∀ outer kp k cur s env blks m,
          ContOKGen prog cfg W baseEnv Q retTy outer kp k →
          Refines prog.tags baseEnv cur outer s env blks m →
          vcStmtGen strict prog cfg contracts baseEnv retTy kp s stmt →
          W Q (.running (.stmt stmt.erase) env blks m s.os k)
      | .inl (stmt, true) =>
        strict = false →
        ∀ R, CallContractsSound prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) contracts →
          ∀ outer kp k cur s env blks m,
          ContOKGen prog cfg (fun Q' s => SafeUntil prog cfg ext Q' R s) baseEnv Q retTy outer kp k →
          (∀ cur' s' env' blks' m',
            Refines prog.tags baseEnv cur' outer s' env' blks' m' →
            kp.normal s' →
            SafeNext prog cfg ext Q R (.running (.stmt .nop) env' blks' m' s'.os k)) →
          Refines prog.tags baseEnv cur outer s env blks m →
          vcStmtGen false prog cfg contracts baseEnv retTy kp s stmt →
          SafeNext prog cfg ext Q R (.running (.stmt stmt.erase) env blks m s.os k)
      | .inr (.inl ss) =>
        ∀ W, WPRules prog cfg ext W → CallContractsSound prog cfg W contracts →
          ((strict = true ∧ (W = WPTerm prog cfg ext ∨ ∃ R, W = fun Q' s => SafeUntil prog cfg ext Q' R s)) ∨
           (strict = false ∧ ∃ R, W = fun Q' s => SafeUntil prog cfg ext Q' R s)) →
          ∀ outer kp k cur s env blks m,
          ContOKGen prog cfg W baseEnv Q retTy outer kp k →
          Refines prog.tags baseEnv cur outer s env blks m →
          vcStmtListGen strict prog cfg contracts baseEnv retTy kp s ss →
          W Q (.running (.stmt .nop) env blks m s.os (.stmts (AnnStmt.eraseList ss) k))
      | .inr (.inr fs) =>
        ∀ W, WPRules prog cfg ext W → CallContractsSound prog cfg W contracts →
          ((strict = true ∧ (W = WPTerm prog cfg ext ∨ ∃ R, W = fun Q' s => SafeUntil prog cfg ext Q' R s)) ∨
           (strict = false ∧ ∃ R, W = fun Q' s => SafeUntil prog cfg ext Q' R s)) →
          ∀ outer kp k cur s env blks m,
          ContOKGen prog cfg W baseEnv Q retTy outer kp k →
          Refines prog.tags baseEnv cur outer s env blks m →
          ContOKGen prog cfg W baseEnv Q retTy (framesScopes cur outer fs).2
            (vcFramesCont strict prog cfg contracts baseEnv retTy kp s fs)
            (AnnStmt.gotoFramesCont env blks k fs).2 ∧
          Refines prog.tags baseEnv (framesScopes cur outer fs).1 (framesScopes cur outer fs).2
            s env (AnnStmt.gotoFramesCont env blks k fs).1 m ∧
          (∀ R, W = (fun Q' u => SafeUntil prog cfg ext Q' R u) →
            (∀ cur' s' env' blks' m',
              Refines prog.tags baseEnv cur' outer s' env' blks' m' →
              kp.normal s' →
              SafeNext prog cfg ext Q R (.running (.stmt .nop) env' blks' m' s'.os k)) →
            ∀ cur' s' env' blks' m',
              Refines prog.tags baseEnv cur' (framesScopes cur outer fs).2 s' env' blks' m' →
              (vcFramesCont strict prog cfg contracts baseEnv retTy kp s fs).normal s' →
              SafeNext prog cfg ext Q R
                (.running (.stmt .nop) env' blks' m' s'.os (AnnStmt.gotoFramesCont env blks k fs).2))
  | .inl (stmt, false) => by
    intro W hrules hcs hmode outer kp k cur s env blks m hk hr hvc
    cases stmt with
    | nop =>
      unfold vcStmtGen at hvc
      exact hk.normal cur s env blks m hr hvc
    | expr e =>
      unfold vcStmtGen at hvc
      refine hrules.of_det_state rfl ?_
      refine vcExprDiscard_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro res s1 _ _ m1 _ hr1 _ hkn
      have hdisc : ∀ mods', Sem.stepDet prog cfg
          (.running (.expr (.ret res []) .discard mods') env blks m1 s1.os k) =
          some (.next (.running (.stmt .nop) env blks m1 s1.os k)) := by
        intro mods'; cases res with | rval v _ => cases v <;> rfl | _ => rfl
      exact hrules.of_det_state (hdisc _) (hk.normal cur s1 env blks m1 hr1 hkn)
    | decl d =>
      unfold vcStmtGen at hvc
      refine hrules.of_det_state rfl ?_
      exact vcDeclList_sound_gen hrules hcs hk [(d, false)] hr hvc
    | decls ds =>
      unfold vcStmtGen at hvc
      have hmap : (ds.map (·, false)).map Prod.fst = ds := by simp [List.map_map, Function.comp_def]
      have h := vcDeclList_sound_gen hrules hcs hk (ds.map (·, false)) hr hvc
      rwa [hmap] at h
    | stackDecl d =>
      unfold vcStmtGen at hvc
      refine hrules.of_det_state rfl ?_
      exact vcDeclList_sound_gen hrules hcs hk [(d, true)] hr hvc
    | stackDecls ds =>
      unfold vcStmtGen at hvc
      have hmap : (ds.map (·, true)).map Prod.fst = ds := by simp [List.map_map, Function.comp_def]
      have h := vcDeclList_sound_gen hrules hcs hk (ds.map (·, true)) hr hvc
      rwa [hmap] at h
    | mixedDecls ds =>
      unfold vcStmtGen at hvc
      exact vcDeclList_sound_gen hrules hcs hk ds hr hvc
    | block ss =>
      cases ss with
      | nil =>
        unfold vcStmtGen at hvc
        exact hrules.of_det_state rfl (hk.normal cur s env blks m hr hvc)
      | cons hd tl =>
        unfold vcStmtGen at hvc
        dsimp only at hvc
        let kBlk : ContPost :=
          { normal := fun s' => kp.normal (s'.exitBlock s.regs.length s.stack.length)
            onBreak := fun s' => kp.onBreak (s'.exitBlock s.regs.length s.stack.length)
            onContinue := fun s' => kp.onContinue (s'.exitBlock s.regs.length s.stack.length)
            onReturn := kp.onReturn
            onGoto := fun lbl s' => kp.onGoto lbl (s'.exitBlock s.regs.length s.stack.length) }
        have hkBlk := ContOKGen.blockEnd (hrules := hrules) hr hk
        have hrEnter := hr.enter_block
        cases tl with
        | nil =>
          unfold vcStmtListGen at hvc
          dsimp only [AnnStmt.erase, AnnStmt.eraseList]
          refine hrules.of_det_state (by unfold Sem.stepDet; rfl) ?_
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
            (.inl (hd, false)) W hrules hcs hmode (cur :: outer) kBlk (.blockEnd env blks k) [] s env [] m
            hkBlk hrEnter hvc
        | cons t1 ts =>
          unfold vcStmtListGen at hvc
          dsimp only [AnnStmt.erase, AnnStmt.eraseList]
          refine hrules.of_det_state (by unfold Sem.stepDet; simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]; rfl) ?_
          let kn : SymState → Prop := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy kBlk s1 (t1 :: ts)
          let kg : String → SymState → Prop := fun lbl s1 =>
            match hgt : AnnStmt.findGotoAnnList lbl (t1 :: ts) with
            | some (tgt, fs) =>
              vcStmtGen strict prog cfg contracts baseEnv retTy
                (vcFramesCont strict prog cfg contracts baseEnv retTy kBlk s1 fs) s1 tgt
            | none => AnnStmt.annHasLabelList lbl (t1 :: ts) = false ∧ kBlk.onGoto lbl s1
          have hkRest := hkBlk.stmts_prepend (AnnStmt.eraseList (t1 :: ts)) kn kg
            (fun cur1 s1 env1 blks1 m1 hr1 hkn1 =>
              vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                (.inr (.inl (t1 :: ts))) W hrules hcs hmode (cur :: outer) kBlk (.blockEnd env blks k)
                cur1 s1 env1 blks1 m1 hkBlk hr1 hkn1)
            (fun lbl cur1 s1 env1 blks1 m1 hr1 hkg => by
              dsimp only [kg] at hkg
              split at hkg
              · rename_i tgt fs hgt
                have hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf (t1 :: ts) :=
                  AnnStmt.findGotoAnnList_sizeOf_lt hgt
                have hfind := AnnStmt.findGotoAnnList_erase hgt env1 blks1 (.blockEnd env blks k)
                obtain ⟨hkF, hrF, _⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                  (.inr (.inr fs)) W hrules hcs hmode (cur :: outer) kBlk (.blockEnd env blks k)
                  cur1 s1 env1 blks1 m1 hkBlk hr1
                refine ⟨tgt.erase, env1, (AnnStmt.gotoFramesCont env1 blks1 (.blockEnd env blks k) fs).1, m1,
                  (AnnStmt.gotoFramesCont env1 blks1 (.blockEnd env blks k) fs).2, ?_, ?_⟩
                · unfold Sem.gotoInCont; rw [hfind]
                · exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                    (.inl (tgt, false)) W hrules hcs hmode _ _ _ _ s1 env1 _ m1 hkF hrF hkg
              · rename_i hgt
                have hnone := AnnStmt.annHasLabelList_erase_none hkg.1 env1 blks1 (.blockEnd env blks k)
                unfold Sem.gotoInCont
                rw [hnone]
                exact hkBlk.onGoto lbl cur1 s1 env1 blks1 m1 hr1 hkg.2)
          change vcStmtGen strict prog cfg contracts baseEnv retTy
            { kBlk with normal := kn, onGoto := kg } s hd at hvc
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
            (.inl (hd, false)) W hrules hcs hmode (cur :: outer)
            { kBlk with normal := kn, onGoto := kg }
            (.stmts (AnnStmt.eraseList (t1 :: ts)) (.blockEnd env blks k))
            [] s env [] m hkRest hrEnter hvc
    | ifStmt c t f? =>
      unfold vcStmtGen at hvc
      rw [AnnStmt.erase_ifStmt]
      refine hrules.of_det_state rfl ?_
      refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro vc _ s1 _ _ m1 _ hr1 _ hbr
      obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
      refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases f? with
        | none => exact hk.normal cur s1 env blks m1 hr1 (hf rfl)
        | some f =>
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
            (.inl (f, false)) W hrules hcs hmode outer kp k cur s1 env blks m1 hk hr1 (hf rfl)
      · simp only [↓reduceIte]
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
          (.inl (t, false)) W hrules hcs hmode outer kp k cur s1 env blks m1 hk hr1 (ht rfl)
    | ifJoin c t f? J =>
      unfold vcStmtGen at hvc
      rw [AnnStmt.erase_ifJoin]
      refine hrules.of_det_state rfl ?_
      refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro vc _ s1 _ _ m1 _ hr1 _ ⟨hbr, hJoin⟩
      have hkJoin : ContOKGen prog cfg W baseEnv Q retTy outer { kp with normal := J } k :=
        ⟨hk.retTy_eq, fun cur' s' env' blks' m' hr' hj => hk.normal cur' s' env' blks' m' hr' (hJoin s' hj),
         hk.onBreak, hk.onContinue, hk.onReturn, hk.onGoto⟩
      obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
      refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases f? with
        | none => exact hkJoin.normal cur s1 env blks m1 hr1 (hf rfl)
        | some f =>
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
            (.inl (f, false)) W hrules hcs hmode outer { kp with normal := J } k cur s1 env blks m1 hkJoin hr1 (hf rfl)
      · simp only [↓reduceIte]
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
          (.inl (t, false)) W hrules hcs hmode outer { kp with normal := J } k cur s1 env blks m1 hkJoin hr1 (ht rfl)
    | whileLoop c body Inv meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinv0, hstep_vc⟩
      cases hst : strict with
      | true =>
        subst hst
        simp only [↓reduceIte] at hinv0 hstep_vc
        let CInv : Nat → Env → List BlockId → Mem → OSState → Prop := fun n env' blks' m' os' =>
          ∃ cur' s', s'.os = os' ∧ Refines prog.tags baseEnv cur' outer s' env' blks' m' ∧ Inv s n s'
        let mkLoopK : (Nat → Env → List BlockId → Mem → OSState → Prop) → Nat → ContPost →
            ContPost := fun _ n => fun _ =>
          { normal := fun s3 => meas s3 < n ∧ Inv s (meas s3) s3
            onBreak := kp.normal
            onContinue := fun s3 => meas s3 < n ∧ Inv s (meas s3) s3
            onReturn := kp.onReturn
            onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
        have hloop : ∀ n env' blks' m' os', CInv n env' blks' m' os' →
            W Q (.running (.expr (.eval .rval c []) (.forCond c none body.erase) []) env' blks' m' os' k) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            rintro env' blks' m' os' ⟨cur', s1, rfl, hr1, hinv1⟩
            refine vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur' outer [] []) (hstep_vc n s1 hinv1) ?_
            intro vc _ s2 _ _ m2 _ hr2 _ hbr
            obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
            refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact hk.normal cur' s2 env' blks' m2 hr2 (hf rfl)
            · simp only [↓reduceIte]
              let kLoop : ContPost := mkLoopK CInv n kp
              have hkLoop : ContOKGen prog cfg W baseEnv Q retTy outer kLoop
                  (.loop (some c) none body.erase false k) := by
                refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
                · intro cur3 s3 env3 blks3 m3 hr3 ⟨hlt, hinv3⟩
                  refine hrules.of_det_state rfl ?_
                  exact ih (meas s3) hlt env3 blks3 m3 s3.os ⟨cur3, s3, rfl, hr3, hinv3⟩
                · intro cur3 s3 env3 blks3 m3 hr3 hb3
                  exact ⟨env3, blks3, m3, k, rfl, hk.normal cur3 s3 env3 blks3 m3 hr3 hb3⟩
                · intro cur3 s3 env3 blks3 m3 hr3 ⟨hlt, hinv3⟩
                  refine ⟨some c, none, body.erase, false, env3, blks3, m3, k, rfl, ?_⟩
                  exact ih (meas s3) hlt env3 blks3 m3 s3.os ⟨cur3, s3, rfl, hr3, hinv3⟩
                · intro cur3 s3 env3 blks3 m3 rv hr3 hret3
                  unfold Sem.unwindReturn
                  exact hk.onReturn cur3 s3 env3 blks3 m3 rv hr3 hret3
                · intro lbl cur3 s3 env3 blks3 m3 hr3 hgt
                  rcases hgt with ⟨hna, hkg⟩
                  unfold Sem.gotoInCont
                  rw [AnnStmt.annHasLabel_erase_none hna env3 blks3 (.loop (some c) none body.erase false k)]
                  exact hk.onGoto lbl cur3 s3 env3 blks3 m3 hr3 hkg
              exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
                (.inl (body, false)) W hrules hcs hmode outer kLoop (.loop (some c) none body.erase false k)
                cur' s2 env' blks' m2 hkLoop hr2 (ht rfl)
        refine hrules.of_det_state rfl ?_
        refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) (hstep_vc (meas s) s hinv0) ?_
        intro vc _ s2 _ _ m2 _ hr2 _ hbr
        obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
        refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hk.normal cur s2 env blks m2 hr2 (hf rfl)
        · simp only [↓reduceIte]
          let kLoop : ContPost := mkLoopK CInv (meas s) kp
          have hkLoop : ContOKGen prog cfg W baseEnv Q retTy outer kLoop
              (.loop (some c) none body.erase false k) := by
            refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
            · intro cur3 s3 env3 blks3 m3 hr3 ⟨_, hinv3⟩
              refine hrules.of_det_state rfl ?_
              exact hloop (meas s3) env3 blks3 m3 s3.os ⟨cur3, s3, rfl, hr3, hinv3⟩
            · intro cur3 s3 env3 blks3 m3 hr3 hb3
              exact ⟨env3, blks3, m3, k, rfl, hk.normal cur3 s3 env3 blks3 m3 hr3 hb3⟩
            · intro cur3 s3 env3 blks3 m3 hr3 ⟨_, hinv3⟩
              refine ⟨some c, none, body.erase, false, env3, blks3, m3, k, rfl, ?_⟩
              exact hloop (meas s3) env3 blks3 m3 s3.os ⟨cur3, s3, rfl, hr3, hinv3⟩
            · intro cur3 s3 env3 blks3 m3 rv hr3 hret3
              unfold Sem.unwindReturn
              exact hk.onReturn cur3 s3 env3 blks3 m3 rv hr3 hret3
            · intro lbl cur3 s3 env3 blks3 m3 hr3 hgt
              rcases hgt with ⟨hna, hkg⟩
              unfold Sem.gotoInCont
              rw [AnnStmt.annHasLabel_erase_none hna env3 blks3 (.loop (some c) none body.erase false k)]
              exact hk.onGoto lbl cur3 s3 env3 blks3 m3 hr3 hkg
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
            (.inl (body, false)) W hrules hcs hmode outer kLoop (.loop (some c) none body.erase false k)
            cur s2 env blks m2 hkLoop hr2 (ht rfl)
      | false =>
        subst hst
        simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 hstep_vc
        rcases hmode with ⟨hbad, _⟩ | ⟨_, R, rfl⟩
        · cases hbad
        refine (whileLoop_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
          c body Inv hk hr hinv0 hstep_vc ?_).to_safeUntil
        intro R' kp' k' cur' s' env' blks' m' hk' hr' hvc'
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
          (.inl (body, false)) (fun Q' u => SafeUntil prog cfg ext Q' R' u)
          (WPRules.safeUntil prog cfg ext R') (hcs_safe R') (.inr ⟨rfl, R', rfl⟩)
          outer kp' k' cur' s' env' blks' m' hk' hr' hvc'
    | doWhileLoop body c Inv meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinv0, hstep_vc⟩
      cases hst : strict with
      | true =>
        subst hst
        simp only [↓reduceIte] at hinv0 hstep_vc
        let CInv : Nat → Env → List BlockId → Mem → OSState → Prop := fun n env' blks' m' os' =>
          ∃ cur' s', s'.os = os' ∧ Refines prog.tags baseEnv cur' outer s' env' blks' m' ∧ Inv s n s'
        have hloop : ∀ n env' blks' m' os', CInv n env' blks' m' os' →
            W Q (.running (.stmt body.erase) env' blks' m' os' (.loop (some c) none body.erase true k)) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            rintro env' blks' m' os' ⟨cur', s1, rfl, hr1, hinv1⟩
            let afterBody : SymState → Prop := fun s2 =>
              vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
                vcBranch vc (meas s3 < n ∧ Inv s (meas s3) s3) (kp.normal s3)
            let kLoop : ContPost :=
              { normal := afterBody
                onBreak := kp.normal
                onContinue := afterBody
                onReturn := kp.onReturn
                onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
            have hafter : ∀ cur2 s2 env2 blks2 m2,
                Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
                afterBody s2 →
                W Q (.running (.expr (.eval .rval c []) (.doWhileCond body.erase c) []) env2 blks2 m2 s2.os k) := by
              intro cur2 s2 env2 blks2 m2 hr2 hab
              refine vcExprR_sound_gen hrules hcs hr2 (ModsOK.nil cur2 outer [] []) hab ?_
              intro vc _ s3 _ _ m3 _ hr3 _ hbr
              obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
              refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
              cases b
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact hk.normal cur2 s3 env2 blks2 m3 hr3 (hf rfl)
              · simp only [↓reduceIte]
                obtain ⟨hlt, hinv3⟩ := ht rfl
                exact ih (meas s3) hlt env2 blks2 m3 s3.os ⟨cur2, s3, rfl, hr3, hinv3⟩
            have hkLoop : ContOKGen prog cfg W baseEnv Q retTy outer kLoop
                (.loop (some c) none body.erase true k) := by
              refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
              · intro cur2 s2 env2 blks2 m2 hr2 hab
                exact hrules.of_det_state rfl (hafter cur2 s2 env2 blks2 m2 hr2 hab)
              · intro cur2 s2 env2 blks2 m2 hr2 hb2
                exact ⟨env2, blks2, m2, k, rfl, hk.normal cur2 s2 env2 blks2 m2 hr2 hb2⟩
              · intro cur2 s2 env2 blks2 m2 hr2 hab
                exact ⟨some c, none, body.erase, true, env2, blks2, m2, k, rfl,
                  hafter cur2 s2 env2 blks2 m2 hr2 hab⟩
              · intro cur2 s2 env2 blks2 m2 rv hr2 hret2
                unfold Sem.unwindReturn
                exact hk.onReturn cur2 s2 env2 blks2 m2 rv hr2 hret2
              · intro lbl cur2 s2 env2 blks2 m2 hr2 ⟨hna, hkg⟩
                unfold Sem.gotoInCont
                rw [AnnStmt.annHasLabel_erase_none hna env2 blks2 _]
                exact hk.onGoto lbl cur2 s2 env2 blks2 m2 hr2 hkg
            exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
              (.inl (body, false)) W hrules hcs hmode outer kLoop (.loop (some c) none body.erase true k)
              cur' s1 env' blks' m' hkLoop hr1 (hstep_vc n s1 hinv1)
        exact hrules.of_det_state rfl (hloop (meas s) env blks m s.os ⟨cur, s, rfl, hr, hinv0⟩)
      | false =>
        subst hst
        simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 hstep_vc
        rcases hmode with ⟨hbad, _⟩ | ⟨_, R, rfl⟩
        · cases hbad
        refine (doWhileLoop_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
          body c Inv hk hr hinv0 hstep_vc ?_).to_safeUntil
        intro R' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
          (.inl (body, true)) rfl R' (hcs_safe R') outer kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
    | doWhileGotos body c Inv gotoSpecs meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinv0, hstep_vc, hgoto_vc⟩
      cases hst : strict with
      | true =>
        subst hst
        simp only [↓reduceIte] at hinv0 hstep_vc
        let afterBodyF : Nat → SymState → Prop := fun n s2 =>
          vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
            vcBranch vc (meas s3 < n ∧ Inv s (meas s3) s3) (kp.normal s3)
        let kLoopF : Nat → ContPost := fun n =>
          { normal := afterBodyF n
            onBreak := kp.normal
            onContinue := afterBodyF n
            onReturn := kp.onReturn
            onGoto := fun lbl s3 =>
              match gotoSpecs.lookup lbl with
              | some GSpec => meas s3 < n ∧ GSpec s (meas s3) s3
              | none => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
        have hloop : ∀ n,
            (∀ env' blks' m' os' cur' s1, s1.os = os' →
              Refines prog.tags baseEnv cur' outer s1 env' blks' m' → Inv s n s1 →
              W Q (.running (.stmt body.erase) env' blks' m' os' (.loop (some c) none body.erase true k))) ∧
            (∀ lbl GSpec tgt fs env' blks' m' cur' sG,
              (lbl, GSpec) ∈ gotoSpecs →
              AnnStmt.findGotoAnn lbl body = some (tgt, fs) →
              Refines prog.tags baseEnv cur' outer sG env' blks' m' → GSpec s n sG →
              W Q (.running (.stmt tgt.erase) env'
                (AnnStmt.gotoFramesCont env' blks' (.loop (some c) none body.erase true k) fs).1 m' sG.os
                (AnnStmt.gotoFramesCont env' blks' (.loop (some c) none body.erase true k) fs).2)) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            have mkKLoop : ContOKGen prog cfg W baseEnv Q retTy outer (kLoopF n)
                (.loop (some c) none body.erase true k) := by
              refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
              · intro cur2 s2 env2 blks2 m2 hr2 hab
                refine hrules.of_det_state rfl ?_
                refine vcExprR_sound_gen hrules hcs hr2 (ModsOK.nil cur2 outer [] []) hab ?_
                intro vc _ s3 _ _ m3 _ hr3 _ hbr
                obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
                refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
                cases b
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hk.normal cur2 s3 env2 blks2 m3 hr3 (hf rfl)
                · simp only [↓reduceIte]
                  obtain ⟨hlt, hinv3⟩ := ht rfl
                  exact (ih (meas s3) hlt).1 env2 blks2 m3 s3.os cur2 s3 rfl hr3 hinv3
              · intro cur2 s2 env2 blks2 m2 hr2 hb2
                exact ⟨env2, blks2, m2, k, rfl, hk.normal cur2 s2 env2 blks2 m2 hr2 hb2⟩
              · intro cur2 s2 env2 blks2 m2 hr2 hab
                refine ⟨some c, none, body.erase, true, env2, blks2, m2, k, rfl, ?_⟩
                refine vcExprR_sound_gen hrules hcs hr2 (ModsOK.nil cur2 outer [] []) hab ?_
                intro vc _ s3 _ _ m3 _ hr3 _ hbr
                obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
                refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
                cases b
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hk.normal cur2 s3 env2 blks2 m3 hr3 (hf rfl)
                · simp only [↓reduceIte]
                  obtain ⟨hlt, hinv3⟩ := ht rfl
                  exact (ih (meas s3) hlt).1 env2 blks2 m3 s3.os cur2 s3 rfl hr3 hinv3
              · intro cur2 s2 env2 blks2 m2 rv hr2 hret2
                unfold Sem.unwindReturn
                exact hk.onReturn cur2 s2 env2 blks2 m2 rv hr2 hret2
              · intro lbl cur2 s2 env2 blks2 m2 hr2 hkg
                dsimp only [kLoopF] at hkg
                cases hgl : gotoSpecs.lookup lbl with
                | none =>
                  simp only [hgl] at hkg
                  unfold Sem.gotoInCont
                  rw [AnnStmt.annHasLabel_erase_none hkg.1 env2 blks2 _]
                  exact hk.onGoto lbl cur2 s2 env2 blks2 m2 hr2 hkg.2
                | some GSpec =>
                  simp only [hgl] at hkg
                  have hmem := list_lookup_some_mem gotoSpecs hgl
                  have hgs := hgoto_vc (lbl, GSpec) hmem
                  split at hgs
                  · cases hgs
                  · rename_i tgt fs hgt
                    have hfind := AnnStmt.findGotoAnn_erase hgt env2 blks2 (.loop (some c) none body.erase true k)
                    refine ⟨tgt.erase, env2,
                      (AnnStmt.gotoFramesCont env2 blks2 (.loop (some c) none body.erase true k) fs).1, m2,
                      (AnnStmt.gotoFramesCont env2 blks2 (.loop (some c) none body.erase true k) fs).2, ?_, ?_⟩
                    · unfold Sem.gotoInCont; rw [hfind]
                    · obtain ⟨hlt, hinvG⟩ := hkg
                      exact (ih (meas s2) hlt).2 lbl GSpec tgt fs env2 blks2 m2 cur2 s2 hmem hgt hr2 hinvG
            refine ⟨?_, ?_⟩
            · intro env' blks' m' os' cur' s1 rfl hr1 hinv1
              have hvc_body : vcStmtGen true prog cfg contracts baseEnv retTy (kLoopF n) s1 body :=
                hstep_vc n s1 hinv1
              exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
                (.inl (body, false)) W hrules hcs hmode outer (kLoopF n)
                (.loop (some c) none body.erase true k) cur' s1 env' blks' m' mkKLoop hr1 hvc_body
            · intro lbl GSpec tgt fs env' blks' m' cur' sG hmem hgt hrG hinvG
              have hgs := hgoto_vc (lbl, GSpec) hmem
              split at hgs
              · cases hgs
              · rename_i tgt' fs' hgt'
                rw [hgt] at hgt'; cases hgt'
                have hvc_tgt : vcStmtGen true prog cfg contracts baseEnv retTy
                    (vcFramesCont true prog cfg contracts baseEnv retTy (kLoopF n) sG fs) sG tgt :=
                  hgs n sG hinvG
                have hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf body :=
                  AnnStmt.findGotoAnn_sizeOf_lt hgt
                obtain ⟨hkF, hrF, _⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
                  (.inr (.inr fs)) W hrules hcs hmode outer (kLoopF n)
                  (.loop (some c) none body.erase true k) cur' sG env' blks' m' mkKLoop hrG
                exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
                  (.inl (tgt, false)) W hrules hcs hmode _ _ _ _ sG env' _ m' hkF hrF hvc_tgt
        exact hrules.of_det_state rfl ((hloop (meas s)).1 env blks m s.os cur s rfl hr hinv0)
      | false =>
        subst hst
        simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 hstep_vc
        rcases hmode with ⟨hbad, _⟩ | ⟨_, R, rfl⟩
        · cases hbad
        refine (doWhileGotos_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
          body c Inv gotoSpecs hk hr hinv0
          (fun n s1 hs1 => hstep_vc n s1 hs1)
          (fun p hp => by
            have hg := hgoto_vc p hp
            split at hg
            · exact False.elim hg
            · rename_i tgt fs hgt
              rw [hgt]
              simpa only [Bool.false_eq_true, ↓reduceIte] using hg)
          ?_ ?_ ?_).to_safeUntil
        · intro R' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
            (.inl (body, true)) rfl R' (hcs_safe R') outer kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
        · intro tgt fs R' outer' kp' k' cur' s' env' blks' m' hlt hk' hn' hr' hvc'
          have : sizeOf tgt < sizeOf (AnnStmt.doWhileGotos body c Inv gotoSpecs meas) := by
            simp only [AnnStmt.doWhileGotos.sizeOf_spec]; omega
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
            (.inl (tgt, true)) rfl R' (hcs_safe R') outer' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
        · intro tgt fs R' kp' k' cur' s' env' blks' m' hlt hk' hr'
          have : AnnStmt.framesSize fs < sizeOf (AnnStmt.doWhileGotos body c Inv gotoSpecs meas) := by
            simp only [AnnStmt.doWhileGotos.sizeOf_spec]; omega
          obtain ⟨hkF, hrF, hnextF⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
            (.inr (.inr fs)) (fun Q' u => SafeUntil prog cfg ext Q' R' u)
            (WPRules.safeUntil prog cfg ext R') (hcs_safe R') (.inr ⟨rfl, R', rfl⟩)
            outer kp' k' cur' s' env' blks' m' hk' hr'
          exact ⟨hkF, hrF, hnextF R' rfl⟩
    | forLoop init? c? stp? body Inv meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinit_vc, hstep_vc⟩
      cases hst : strict with
      | true =>
        subst hst
        simp only [↓reduceIte] at hinit_vc hstep_vc
        have hloop : ∀ n env' blks' m' os' cur' s1, s1.os = os' →
            Refines prog.tags baseEnv cur' outer s1 env' blks' m' → Inv s n s1 →
            W Q (forHdrState c? stp? body.erase env' blks' m' os' k) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
            rintro env' blks' m' os' cur' s1 rfl hr1 hinv1
            let afterBody := forAfterBody prog cfg contracts baseEnv stp? (fun s3 => meas s3 < n ∧ Inv s (meas s3) s3)
            let kLoop : ContPost :=
              { normal := afterBody
                onBreak := kp.normal
                onContinue := afterBody
                onReturn := kp.onReturn
                onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ kp.onGoto lbl s3 }
            have hafter : ∀ cur2 s2 env2 blks2 m2,
                Refines prog.tags baseEnv cur2 outer s2 env2 blks2 m2 →
                afterBody s2 →
                W Q (Sem.loopNext c? stp? body.erase false env2 blks2 m2 s2.os k) := by
              intro cur2 s2 env2 blks2 m2 hr2 hab
              cases stp? with
              | none =>
                dsimp only [afterBody, forAfterBody] at hab
                rw [loopNext_none_eq_forHdrState]
                exact ih (meas s2) hab.1 env2 blks2 m2 s2.os cur2 s2 rfl hr2 hab.2
              | some stp =>
                dsimp only [afterBody, forAfterBody] at hab
                change W Q (.running (.expr (.eval .rval stp []) (.forStep c? (some stp) body.erase) [])
                  env2 blks2 m2 s2.os k)
                refine vcExprDiscard_sound_gen hrules hcs hr2 (ModsOK.nil cur2 outer [] []) hab ?_
                intro res s3 _ _ m3 _ hr3 _ ⟨hlt, hinv3⟩
                exact hrules.of_det_state
                  (stepDet_forStep prog cfg res c? (some stp) body.erase _ env2 blks2 m3 s3.os k)
                  (ih (meas s3) hlt env2 blks2 m3 s3.os cur2 s3 rfl hr3 hinv3)
            have hkLoop : ContOKGen prog cfg W baseEnv Q retTy outer kLoop (.loop c? stp? body.erase false k) := by
              refine ⟨hk.retTy_eq, ?_, ?_, ?_, ?_, ?_⟩
              · intro cur2 s2 env2 blks2 m2 hr2 hab
                exact hrules.of_det_state rfl (hafter cur2 s2 env2 blks2 m2 hr2 hab)
              · intro cur2 s2 env2 blks2 m2 hr2 hb2
                exact ⟨env2, blks2, m2, k, rfl, hk.normal cur2 s2 env2 blks2 m2 hr2 hb2⟩
              · intro cur2 s2 env2 blks2 m2 hr2 hab
                exact ⟨c?, stp?, body.erase, false, env2, blks2, m2, k, rfl, hafter cur2 s2 env2 blks2 m2 hr2 hab⟩
              · intro cur2 s2 env2 blks2 m2 rv hr2 hret2
                unfold Sem.unwindReturn
                exact hk.onReturn cur2 s2 env2 blks2 m2 rv hr2 hret2
              · intro lbl cur2 s2 env2 blks2 m2 hr2 ⟨hna, hkg⟩
                unfold Sem.gotoInCont
                rw [AnnStmt.annHasLabel_erase_none hna env2 blks2 (.loop c? stp? body.erase false k)]
                exact hk.onGoto lbl cur2 s2 env2 blks2 m2 hr2 hkg
            have hvc1 := hstep_vc n s1 hinv1
            clear hstep_vc
            cases c? with
            | some c =>
              dsimp only [forHdrState] at hvc1 ⊢
              refine vcExprR_sound_gen hrules hcs hr1 (ModsOK.nil cur' outer [] []) hvc1 ?_
              intro vc _ s2 _ _ m2 _ hr2 _ hbr
              obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
              refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
              cases b
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact hk.normal cur' s2 env' blks' m2 hr2 (hf rfl)
              · simp only [↓reduceIte]
                have hvc_b : vcStmtGen true prog cfg contracts baseEnv retTy kLoop s2 body := ht rfl
                exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
                  (.inl (body, false)) W hrules hcs hmode outer kLoop (.loop (some c) stp? body.erase false k)
                  cur' s2 env' blks' m2 hkLoop hr2 hvc_b
            | none =>
              dsimp only [forHdrState] at hvc1 ⊢
              exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy true hcs_term hcs_safe
                (.inl (body, false)) W hrules hcs hmode outer kLoop (.loop none stp? body.erase false k)
                cur' s1 env' blks' m' hkLoop hr1 hvc1
        cases init? with
        | none =>
          dsimp only at hinit_vc
          exact hrules.of_det_state
            (stepDet_forStmt_none prog cfg c? stp? body.erase env blks m s.os k)
            (hloop (meas s) env blks m s.os cur s rfl hr hinit_vc)
        | some init =>
          dsimp only at hinit_vc
          refine hrules.of_det_state rfl ?_
          refine vcExprDiscard_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hinit_vc ?_
          intro res s0 _ _ m0 _ hr0 _ hinv_s0
          exact hrules.of_det_state
            (stepDet_forStep prog cfg res c? stp? body.erase _ env blks m0 s0.os k)
            (hloop (meas s0) env blks m0 s0.os cur s0 rfl hr0 hinv_s0)
      | false =>
        subst hst
        simp only [Bool.false_eq_true, ↓reduceIte] at hinit_vc hstep_vc
        rcases hmode with ⟨hbad, _⟩ | ⟨_, R, rfl⟩
        · cases hbad
        refine (forLoop_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
          init? c? stp? body Inv hk hr hinit_vc
          (fun s1 hs1 => hstep_vc 0 s1 ⟨rfl, hs1⟩) ?_ ?_).to_safeUntil
        · intro R' kp' k' cur' s' env' blks' m' hk' hr' hvc'
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
            (.inl (body, false)) (fun Q' u => SafeUntil prog cfg ext Q' R' u)
            (WPRules.safeUntil prog cfg ext R') (hcs_safe R') (.inr ⟨rfl, R', rfl⟩)
            outer kp' k' cur' s' env' blks' m' hk' hr' hvc'
        · intro R' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hcs_term hcs_safe
            (.inl (body, true)) rfl R' (hcs_safe R') outer kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
    | switchStmt scrut body =>
      unfold vcStmtGen at hvc
      rw [AnnStmt.erase_switchStmt]
      refine hrules.of_det_state rfl ?_
      refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro v ty_scrut s1 _ _ m1 mods_scrut hr1 _ ⟨k_int, iv, hval, hsw⟩
      cases hv_eq : v with
      | int ik bv =>
        subst hv_eq
        split at hsw
        · have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval (.int ik bv) ty_scrut) []) (.switchScrut body.erase) mods_scrut) env blks m1 s1.os k) =
              some (.next (.running (.stmt .nop) env blks m1 s1.os k)) := by
            unfold Sem.stepDet; simp [hval, hsw.1]
          exact hrules.of_det_state hdet (hk.normal cur s1 env blks m1 hr1 hsw.2)
        · rename_i tgt htgt
          have hlt : sizeOf tgt < sizeOf body := AnnStmt.findSwitchAnnTarget_sizeOf_lt htgt
          have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval (.int ik bv) ty_scrut) []) (.switchScrut body.erase) mods_scrut) env blks m1 s1.os k) =
              some (.next (.running (.stmt tgt.erase) env blks m1 s1.os (.switchCont k))) := by
            unfold Sem.stepDet; simp [hval, hsw.1]
          exact hrules.of_det_state hdet
            (vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
              (.inl (tgt, false)) W hrules hcs hmode outer { kp with onBreak := kp.normal } (.switchCont k)
              cur s1 env blks m1 (hk.switchCont (hrules := hrules)) hr1 hsw.2)
      | null | ptr _ _ | fnPtr _ | undef | vaList _ | void =>
        simp only [hv_eq, Sem.valAsInt?] at hval; cases hval
    | caseStmt _ body =>
      unfold vcStmtGen at hvc
      refine hrules.of_det_state rfl ?_
      exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
        (.inl (body, false)) W hrules hcs hmode outer kp k cur s env blks m hk hr hvc
    | defaultStmt body =>
      unfold vcStmtGen at hvc
      refine hrules.of_det_state rfl ?_
      exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
        (.inl (body, false)) W hrules hcs hmode outer kp k cur s env blks m hk hr hvc
    | labelStmt _ body =>
      unfold vcStmtGen at hvc
      refine hrules.of_det_state rfl ?_
      exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
        (.inl (body, false)) W hrules hcs hmode outer kp k cur s env blks m hk hr hvc
    | gotoStmt lbl =>
      unfold vcStmtGen at hvc
      obtain ⟨s', e', b', m', k', hgoto, hw⟩ := hk.onGoto lbl cur s env blks m hr hvc
      exact hrules.of_det_state (by unfold Sem.stepDet; simp [hgoto]) hw
    | breakStmt =>
      unfold vcStmtGen at hvc
      obtain ⟨e', b', m', k', hb, hw⟩ := hk.onBreak cur s env blks m hr hvc
      exact hrules.of_det_state (by unfold Sem.stepDet; simp [hb]) hw
    | continueStmt =>
      unfold vcStmtGen at hvc
      obtain ⟨c?, stp?, b, d, e', b', m', k', hc, hw⟩ := hk.onContinue cur s env blks m hr hvc
      exact hrules.of_det_state (by unfold Sem.stepDet; simp [hc]) hw
    | returnStmt val? =>
      cases val? with
      | none =>
        unfold vcStmtGen at hvc
        rcases hvc with ⟨hvoid, hret⟩
        obtain ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s env blks m .void hr hret
        have hdet : Sem.stepDet prog cfg (.running (.stmt (.returnStmt none)) env blks m s.os k) =
            some (.next (.running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' s.os rk)) := by
          unfold Sem.stepDet; simp [hk.retTy_eq, hvoid, hu]
        exact hrules.of_det_state hdet (by simpa [hvoid] using hw)
      | some e =>
        unfold vcStmtGen at hvc
        refine hrules.of_det_state rfl ?_
        refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
        intro rv rty_e s1 _ _ m1 mods_e hr1 _ hk1
        cases hv : retTy.isVoid with
        | true =>
          simp only [hv, ↓reduceIte] at hk1
          obtain ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s1 env blks m1 .void hr1 hk1
          have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval rv rty_e) []) .returnVal mods_e) env blks m1 s1.os k) =
              some (.next (.running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' s1.os rk)) := by
            cases rv <;> (unfold Sem.stepDet; simp [hk.retTy_eq, hv, hu]; try rfl)
          exact hrules.of_det_state hdet (by simpa [hv] using hw)
        | false =>
          simp only [hv, Bool.false_eq_true, ↓reduceIte] at hk1
          obtain ⟨cv, hcast, hk_ret⟩ := vcCast_sound hr1 hk1
          obtain ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s1 env blks m1 cv hr1 hk_ret
          have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval rv rty_e) []) .returnVal mods_e) env blks m1 s1.os k) =
              some (.next (.running (.expr (.ret (.rval cv retTy) fs) rctx []) re rb m' s1.os rk)) := by
            cases rv <;> (unfold Sem.stepDet; simp [hk.retTy_eq, hv, hcast, hu]; try rfl)
          exact hrules.of_det_state hdet (by simpa [hv] using hw)
  | .inl (stmt, true) => by
    intro hstrict R hcs outer kp k cur s env blks m hk hk_norm_next hr hvc
    let hrules := WPRules.safeUntil prog cfg ext R
    let hno_term : false = true → CallContractsSound prog cfg (WPTerm prog cfg ext) contracts :=
      fun h => absurd h Bool.false_ne_true
    have hmode : (false = true ∧ ((fun Q' u => SafeUntil prog cfg ext Q' R u) = WPTerm prog cfg ext ∨
        ∃ R', (fun Q' u => SafeUntil prog cfg ext Q' R u) = fun Q' s => SafeUntil prog cfg ext Q' R' s)) ∨
        (false = false ∧ ∃ R', (fun Q' u => SafeUntil prog cfg ext Q' R u) = fun Q' s => SafeUntil prog cfg ext Q' R' s) :=
      .inr ⟨rfl, R, rfl⟩
    cases stmt with
    | nop =>
      unfold vcStmtGen at hvc
      exact hk_norm_next cur s env blks m hr hvc
    | expr e =>
      unfold vcStmtGen at hvc
      refine SafeNext.of_det_state rfl ?_
      refine vcExprDiscard_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro res s1 _ _ m1 _ hr1 _ hkn
      have hdisc : ∀ mods', Sem.stepDet prog cfg
          (.running (.expr (.ret res []) .discard mods') env blks m1 s1.os k) =
          some (.next (.running (.stmt .nop) env blks m1 s1.os k)) := by
        intro mods'; cases res with | rval v _ => cases v <;> rfl | _ => rfl
      exact SafeUntil.of_det_state (hdisc _) (hk.normal cur s1 env blks m1 hr1 hkn)
    | decl d =>
      unfold vcStmtGen at hvc
      exact SafeNext.of_det_state rfl (vcDeclList_sound_gen hrules hcs hk [(d, false)] hr hvc)
    | decls ds =>
      unfold vcStmtGen at hvc
      have hmap : (ds.map (·, false)).map Prod.fst = ds := by simp [List.map_map, Function.comp_def]
      have h := vcDeclList_safeNext hcs hk (ds.map (·, false)) hr hvc
      rwa [hmap] at h
    | stackDecl d =>
      unfold vcStmtGen at hvc
      exact SafeNext.of_det_state rfl (vcDeclList_sound_gen hrules hcs hk [(d, true)] hr hvc)
    | stackDecls ds =>
      unfold vcStmtGen at hvc
      have hmap : (ds.map (·, true)).map Prod.fst = ds := by simp [List.map_map, Function.comp_def]
      have h := vcDeclList_safeNext hcs hk (ds.map (·, true)) hr hvc
      rwa [hmap] at h
    | mixedDecls ds =>
      unfold vcStmtGen at hvc
      exact vcDeclList_safeNext hcs hk ds hr hvc
    | block ss =>
      cases ss with
      | nil =>
        unfold vcStmtGen at hvc
        exact SafeNext.of_det_state rfl (hk.normal cur s env blks m hr hvc)
      | cons hd tl =>
        unfold vcStmtGen at hvc
        dsimp only at hvc
        let kBlk : ContPost :=
          { normal := fun s' => kp.normal (s'.exitBlock s.regs.length s.stack.length)
            onBreak := fun s' => kp.onBreak (s'.exitBlock s.regs.length s.stack.length)
            onContinue := fun s' => kp.onContinue (s'.exitBlock s.regs.length s.stack.length)
            onReturn := kp.onReturn
            onGoto := fun lbl s' => kp.onGoto lbl (s'.exitBlock s.regs.length s.stack.length) }
        have hkBlk := ContOKGen.blockEnd (hrules := hrules) hr hk
        have hrEnter := hr.enter_block
        cases tl with
        | nil =>
          unfold vcStmtListGen at hvc
          dsimp only [AnnStmt.erase, AnnStmt.eraseList]
          refine SafeNext.of_det_state (by unfold Sem.stepDet; rfl) ?_
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
            (.inl (hd, false)) _ hrules hcs hmode (cur :: outer) kBlk (.blockEnd env blks k) [] s env [] m
            hkBlk hrEnter hvc
        | cons t1 ts =>
          unfold vcStmtListGen at hvc
          dsimp only [AnnStmt.erase, AnnStmt.eraseList]
          refine SafeNext.of_det_state (by unfold Sem.stepDet; simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]; rfl) ?_
          let kn : SymState → Prop := fun s1 => vcStmtListGen false prog cfg contracts baseEnv retTy kBlk s1 (t1 :: ts)
          let kg : String → SymState → Prop := fun lbl s1 =>
            match hgt : AnnStmt.findGotoAnnList lbl (t1 :: ts) with
            | some (tgt, fs) =>
              vcStmtGen false prog cfg contracts baseEnv retTy
                (vcFramesCont false prog cfg contracts baseEnv retTy kBlk s1 fs) s1 tgt
            | none => AnnStmt.annHasLabelList lbl (t1 :: ts) = false ∧ kBlk.onGoto lbl s1
          have hkRest := hkBlk.stmts_prepend (AnnStmt.eraseList (t1 :: ts)) kn kg
            (fun cur1 s1 env1 blks1 m1 hr1 hkn1 =>
              vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
                (.inr (.inl (t1 :: ts))) _ hrules hcs hmode (cur :: outer) kBlk (.blockEnd env blks k)
                cur1 s1 env1 blks1 m1 hkBlk hr1 hkn1)
            (fun lbl cur1 s1 env1 blks1 m1 hr1 hkg => by
              dsimp only [kg] at hkg
              split at hkg
              · rename_i tgt fs hgt
                have hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf (t1 :: ts) :=
                  AnnStmt.findGotoAnnList_sizeOf_lt hgt
                have hfind := AnnStmt.findGotoAnnList_erase hgt env1 blks1 (.blockEnd env blks k)
                obtain ⟨hkF, hrF, _⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
                  (.inr (.inr fs)) _ hrules hcs hmode (cur :: outer) kBlk (.blockEnd env blks k)
                  cur1 s1 env1 blks1 m1 hkBlk hr1
                refine ⟨tgt.erase, env1, (AnnStmt.gotoFramesCont env1 blks1 (.blockEnd env blks k) fs).1, m1,
                  (AnnStmt.gotoFramesCont env1 blks1 (.blockEnd env blks k) fs).2, ?_, ?_⟩
                · unfold Sem.gotoInCont; rw [hfind]
                · exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
                    (.inl (tgt, false)) _ hrules hcs hmode _ _ _ _ s1 env1 _ m1 hkF hrF hkg
              · rename_i hgt
                have hnone := AnnStmt.annHasLabelList_erase_none hkg.1 env1 blks1 (.blockEnd env blks k)
                unfold Sem.gotoInCont; rw [hnone]
                exact hkBlk.onGoto lbl cur1 s1 env1 blks1 m1 hr1 hkg.2)
          change vcStmtGen false prog cfg contracts baseEnv retTy
            { kBlk with normal := kn, onGoto := kg } s hd at hvc
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
            (.inl (hd, false)) _ hrules hcs hmode (cur :: outer)
            { kBlk with normal := kn, onGoto := kg }
            (.stmts (AnnStmt.eraseList (t1 :: ts)) (.blockEnd env blks k))
            [] s env [] m hkRest hrEnter hvc
    | ifStmt c t f? =>
      unfold vcStmtGen at hvc
      rw [AnnStmt.erase_ifStmt]
      refine SafeNext.of_det_state rfl ?_
      refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro vc _ s1 _ _ m1 _ hr1 _ hbr
      obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
      refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases f? with
        | none => exact hk.normal cur s1 env blks m1 hr1 (hf rfl)
        | some f =>
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
            (.inl (f, false)) _ hrules hcs hmode outer kp k cur s1 env blks m1 hk hr1 (hf rfl)
      · simp only [↓reduceIte]
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (t, false)) _ hrules hcs hmode outer kp k cur s1 env blks m1 hk hr1 (ht rfl)
    | ifJoin c t f? J =>
      unfold vcStmtGen at hvc
      rw [AnnStmt.erase_ifJoin]
      refine SafeNext.of_det_state rfl ?_
      refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro vc _ s1 _ _ m1 _ hr1 _ ⟨hbr, hJoin⟩
      have hkJoin : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R u)
          baseEnv Q retTy outer { kp with normal := J } k :=
        ⟨hk.retTy_eq, fun cur' s' env' blks' m' hr' hj => hk.normal cur' s' env' blks' m' hr' (hJoin s' hj),
         hk.onBreak, hk.onContinue, hk.onReturn, hk.onGoto⟩
      obtain ⟨b, hb_truth, ht, hf⟩ := vcBranch_elim hbr
      refine hrules.of_det_state (by cases vc <;> (unfold Sem.stepDet; simp [hb_truth]; try rfl)) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases f? with
        | none => exact hkJoin.normal cur s1 env blks m1 hr1 (hf rfl)
        | some f =>
          exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
            (.inl (f, false)) _ hrules hcs hmode outer { kp with normal := J } k cur s1 env blks m1 hkJoin hr1 (hf rfl)
      · simp only [↓reduceIte]
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (t, false)) _ hrules hcs hmode outer { kp with normal := J } k cur s1 env blks m1 hkJoin hr1 (ht rfl)
    | whileLoop c body Inv meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinv0, hstep_vc⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 hstep_vc
      refine whileLoop_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
        c body Inv hk hr hinv0 hstep_vc ?_
      intro R' kp' k' cur' s' env' blks' m' hk' hr' hvc'
      exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
        (.inl (body, false)) (fun Q' u => SafeUntil prog cfg ext Q' R' u)
        (WPRules.safeUntil prog cfg ext R') (hcs_safe R') (.inr ⟨rfl, R', rfl⟩)
        outer kp' k' cur' s' env' blks' m' hk' hr' hvc'
    | doWhileLoop body c Inv meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinv0, hstep_vc⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 hstep_vc
      refine doWhileLoop_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
        body c Inv hk hr hinv0 hstep_vc ?_
      intro R' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
      exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
        (.inl (body, true)) rfl R' (hcs_safe R') outer kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
    | doWhileGotos body c Inv gotoSpecs meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinv0, hstep_vc, hgoto_vc⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hinv0 hstep_vc
      refine doWhileGotos_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
        body c Inv gotoSpecs hk hr hinv0
        (fun n s1 hs1 => hstep_vc n s1 hs1)
        (fun p hp => by
          have hg := hgoto_vc p hp
          split at hg
          · exact False.elim hg
          · rename_i tgt fs hgt
            rw [hgt]
            simpa only [Bool.false_eq_true, ↓reduceIte] using hg)
        ?_ ?_ ?_
      · intro R' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (body, true)) rfl R' (hcs_safe R') outer kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
      · intro tgt fs R' outer' kp' k' cur' s' env' blks' m' hlt hk' hn' hr' hvc'
        have : sizeOf tgt < sizeOf (AnnStmt.doWhileGotos body c Inv gotoSpecs meas) := by
          simp only [AnnStmt.doWhileGotos.sizeOf_spec]; omega
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (tgt, true)) rfl R' (hcs_safe R') outer' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
      · intro tgt fs R' kp' k' cur' s' env' blks' m' hlt hk' hr'
        have : AnnStmt.framesSize fs < sizeOf (AnnStmt.doWhileGotos body c Inv gotoSpecs meas) := by
          simp only [AnnStmt.doWhileGotos.sizeOf_spec]; omega
        obtain ⟨hkF, hrF, hnextF⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inr (.inr fs)) (fun Q' u => SafeUntil prog cfg ext Q' R' u)
          (WPRules.safeUntil prog cfg ext R') (hcs_safe R') (.inr ⟨rfl, R', rfl⟩)
          outer kp' k' cur' s' env' blks' m' hk' hr'
        exact ⟨hkF, hrF, hnextF R' rfl⟩
    | forLoop init? c? stp? body Inv meas =>
      unfold vcStmtGen at hvc
      rcases hvc with ⟨hinit_vc, hstep_vc⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hinit_vc hstep_vc
      refine forLoop_safeNext prog cfg contracts baseEnv Q R retTy hcs_safe outer kp k cur s env blks m
        init? c? stp? body Inv hk hr hinit_vc
        (fun s1 hs1 => hstep_vc 0 s1 ⟨rfl, hs1⟩) ?_ ?_
      · intro R' kp' k' cur' s' env' blks' m' hk' hr' hvc'
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (body, false)) (fun Q' u => SafeUntil prog cfg ext Q' R' u)
          (WPRules.safeUntil prog cfg ext R') (hcs_safe R') (.inr ⟨rfl, R', rfl⟩)
          outer kp' k' cur' s' env' blks' m' hk' hr' hvc'
      · intro R' kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (body, true)) rfl R' (hcs_safe R') outer kp' k' cur' s' env' blks' m' hk' hn' hr' hvc'
    | switchStmt scrut body =>
      unfold vcStmtGen at hvc
      rw [AnnStmt.erase_switchStmt]
      refine SafeNext.of_det_state rfl ?_
      refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
      intro v ty_scrut s1 _ _ m1 mods_scrut hr1 _ ⟨k_int, iv, hval, hsw⟩
      cases hv_eq : v with
      | int ik bv =>
        subst hv_eq
        split at hsw
        · have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval (.int ik bv) ty_scrut) []) (.switchScrut body.erase) mods_scrut) env blks m1 s1.os k) =
              some (.next (.running (.stmt .nop) env blks m1 s1.os k)) := by
            unfold Sem.stepDet; simp [hval, hsw.1]
          exact SafeUntil.of_det_state hdet (hk.normal cur s1 env blks m1 hr1 hsw.2)
        · rename_i tgt htgt
          have hlt : sizeOf tgt < sizeOf body := AnnStmt.findSwitchAnnTarget_sizeOf_lt htgt
          have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval (.int ik bv) ty_scrut) []) (.switchScrut body.erase) mods_scrut) env blks m1 s1.os k) =
              some (.next (.running (.stmt tgt.erase) env blks m1 s1.os (.switchCont k))) := by
            unfold Sem.stepDet; simp [hval, hsw.1]
          exact SafeUntil.of_det_state hdet
            (vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
              (.inl (tgt, false)) _ hrules hcs hmode outer { kp with onBreak := kp.normal } (.switchCont k)
              cur s1 env blks m1 (hk.switchCont (hrules := hrules)) hr1 hsw.2)
      | null | ptr _ _ | fnPtr _ | undef | vaList _ | void =>
        simp only [hv_eq, Sem.valAsInt?] at hval; cases hval
    | caseStmt _ body =>
      unfold vcStmtGen at hvc
      exact SafeNext.of_det_state rfl
        (vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (body, false)) _ hrules hcs hmode outer kp k cur s env blks m hk hr hvc)
    | defaultStmt body =>
      unfold vcStmtGen at hvc
      exact SafeNext.of_det_state rfl
        (vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (body, false)) _ hrules hcs hmode outer kp k cur s env blks m hk hr hvc)
    | labelStmt _ body =>
      unfold vcStmtGen at hvc
      exact SafeNext.of_det_state rfl
        (vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy false hno_term hcs_safe
          (.inl (body, false)) _ hrules hcs hmode outer kp k cur s env blks m hk hr hvc)
    | gotoStmt lbl =>
      unfold vcStmtGen at hvc
      obtain ⟨s', e', b', m', k', hgoto, hw⟩ := hk.onGoto lbl cur s env blks m hr hvc
      exact SafeNext.of_det_state (by unfold Sem.stepDet; simp [hgoto]) hw
    | breakStmt =>
      unfold vcStmtGen at hvc
      obtain ⟨e', b', m', k', hb, hw⟩ := hk.onBreak cur s env blks m hr hvc
      exact SafeNext.of_det_state (by unfold Sem.stepDet; simp [hb]) hw
    | continueStmt =>
      unfold vcStmtGen at hvc
      obtain ⟨c?, stp?, b, d, e', b', m', k', hc, hw⟩ := hk.onContinue cur s env blks m hr hvc
      exact SafeNext.of_det_state (by unfold Sem.stepDet; simp [hc]) hw
    | returnStmt val? =>
      cases val? with
      | none =>
        unfold vcStmtGen at hvc
        rcases hvc with ⟨hvoid, hret⟩
        obtain ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s env blks m .void hr hret
        have hdet : Sem.stepDet prog cfg (.running (.stmt (.returnStmt none)) env blks m s.os k) =
            some (.next (.running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' s.os rk)) := by
          unfold Sem.stepDet; simp [hk.retTy_eq, hvoid, hu]
        exact SafeNext.of_det_state hdet (by simpa [hvoid] using hw)
      | some e =>
        unfold vcStmtGen at hvc
        refine SafeNext.of_det_state rfl ?_
        refine vcExprR_sound_gen hrules hcs hr (ModsOK.nil cur outer [] []) hvc ?_
        intro rv rty_e s1 _ _ m1 mods_e hr1 _ hk1
        cases hv : retTy.isVoid with
        | true =>
          simp only [hv, ↓reduceIte] at hk1
          obtain ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s1 env blks m1 .void hr1 hk1
          have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval rv rty_e) []) .returnVal mods_e) env blks m1 s1.os k) =
              some (.next (.running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' s1.os rk)) := by
            cases rv <;> (unfold Sem.stepDet; simp [hk.retTy_eq, hv, hu]; try rfl)
          exact SafeUntil.of_det_state hdet (by simpa [hv] using hw)
        | false =>
          simp only [hv, Bool.false_eq_true, ↓reduceIte] at hk1
          obtain ⟨cv, hcast, hk_ret⟩ := vcCast_sound hr1 hk1
          obtain ⟨re, rb, rt, m', fs, rctx, rk, hu, hw⟩ := hk.onReturn cur s1 env blks m1 cv hr1 hk_ret
          have hdet : Sem.stepDet prog cfg
              (.running (.expr (.ret (.rval rv rty_e) []) .returnVal mods_e) env blks m1 s1.os k) =
              some (.next (.running (.expr (.ret (.rval cv retTy) fs) rctx []) re rb m' s1.os rk)) := by
            cases rv <;> (unfold Sem.stepDet; simp [hk.retTy_eq, hv, hcast, hu]; try rfl)
          exact SafeUntil.of_det_state hdet (by simpa [hv] using hw)
  | .inr (.inl ss) => by
    intro W hrules hcs hmode outer kp k cur s env blks m hk hr hvc
    cases ss with
    | nil =>
      unfold vcStmtListGen at hvc
      exact hrules.of_det_state rfl (hk.normal cur s env blks m hr hvc)
    | cons hd tl =>
      cases tl with
      | nil =>
        unfold vcStmtListGen at hvc
        dsimp only [AnnStmt.eraseList]
        refine hrules.of_det_state (by unfold Sem.stepDet; rfl) ?_
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
          (.inl (hd, false)) W hrules hcs hmode outer kp (.stmts [] k) cur s env blks m
          (hk.stmts_nil (hrules := hrules)) hr hvc
      | cons t1 ts =>
        unfold vcStmtListGen at hvc
        dsimp only [AnnStmt.eraseList]
        refine hrules.of_det_state (by unfold Sem.stepDet; rfl) ?_
        let kn : SymState → Prop := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy kp s1 (t1 :: ts)
        let kg : String → SymState → Prop := fun lbl s1 =>
          match hgt : AnnStmt.findGotoAnnList lbl (t1 :: ts) with
          | some (tgt, fs) =>
            vcStmtGen strict prog cfg contracts baseEnv retTy
              (vcFramesCont strict prog cfg contracts baseEnv retTy kp s1 fs) s1 tgt
          | none => AnnStmt.annHasLabelList lbl (t1 :: ts) = false ∧ kp.onGoto lbl s1
        have hkRest := hk.stmts_prepend (AnnStmt.eraseList (t1 :: ts)) kn kg
          (fun cur1 s1 env1 blks1 m1 hr1 hkn1 =>
            vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
              (.inr (.inl (t1 :: ts))) W hrules hcs hmode outer kp k cur1 s1 env1 blks1 m1 hk hr1 hkn1)
          (fun lbl cur1 s1 env1 blks1 m1 hr1 hkg => by
            dsimp only [kg] at hkg
            split at hkg
            · rename_i tgt fs hgt
              have hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf (t1 :: ts) :=
                AnnStmt.findGotoAnnList_sizeOf_lt hgt
              have hfind := AnnStmt.findGotoAnnList_erase hgt env1 blks1 k
              obtain ⟨hkF, hrF, _⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                (.inr (.inr fs)) W hrules hcs hmode outer kp k cur1 s1 env1 blks1 m1 hk hr1
              refine ⟨tgt.erase, env1, (AnnStmt.gotoFramesCont env1 blks1 k fs).1, m1,
                (AnnStmt.gotoFramesCont env1 blks1 k fs).2, ?_, ?_⟩
              · unfold Sem.gotoInCont; rw [hfind]
              · exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                  (.inl (tgt, false)) W hrules hcs hmode _ _ _ _ s1 env1 _ m1 hkF hrF hkg
            · rename_i hgt
              have hnone := AnnStmt.annHasLabelList_erase_none hkg.1 env1 blks1 k
              unfold Sem.gotoInCont; rw [hnone]
              exact hk.onGoto lbl cur1 s1 env1 blks1 m1 hr1 hkg.2)
        change vcStmtGen strict prog cfg contracts baseEnv retTy { kp with normal := kn, onGoto := kg } s hd at hvc
        exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
          (.inl (hd, false)) W hrules hcs hmode outer { kp with normal := kn, onGoto := kg }
          (.stmts (AnnStmt.eraseList (t1 :: ts)) k) cur s env blks m hkRest hr hvc
  | .inr (.inr fs) => by
    intro W hrules hcs hmode outer kp k cur s env blks m hk hr
    cases fs with
    | nil =>
      rw [vcFramesCont_nil]
      refine ⟨hk, hr, ?_⟩
      intro R hW hk_norm_next cur' s' env' blks' m' hr' hn'
      subst hW
      exact hk_norm_next cur' s' env' blks' m' hr' hn'
    | cons hd rest =>
      have hlt_rest : AnnStmt.framesSize rest < AnnStmt.framesSize (hd :: rest) := by
        cases hd <;> simp <;> omega
      obtain ⟨hkRest, hrRest, hnextRest⟩ :=
        vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
          (.inr (.inr rest)) W hrules hcs hmode outer kp k cur s env blks m hk hr
      cases hd with
      | stmts tl =>
        cases tl with
        | nil =>
          rw [vcFramesCont_stmts_nil]
          exact ⟨hkRest, hrRest, hnextRest⟩
        | cons t0 ttl =>
          rw [vcFramesCont_stmts_cons]
          dsimp only [framesScopes, AnnStmt.gotoFramesCont, List.isEmpty, Bool.false_eq_true, ↓reduceIte]
          let kRest := vcFramesCont strict prog cfg contracts baseEnv retTy kp s rest
          let k' := (AnnStmt.gotoFramesCont env blks k rest).2
          let kn : SymState → Prop := fun s1 =>
            vcStmtListGen strict prog cfg contracts baseEnv retTy kRest s1 (t0 :: ttl)
          let kg : String → SymState → Prop := fun lbl s1 =>
            match hgt : AnnStmt.findGotoAnnList lbl (t0 :: ttl) with
            | some (tgt, fs') =>
              vcStmtGen strict prog cfg contracts baseEnv retTy
                (vcFramesCont strict prog cfg contracts baseEnv retTy kRest s1 fs') s1 tgt
            | none => AnnStmt.annHasLabelList lbl (t0 :: ttl) = false ∧ kRest.onGoto lbl s1
          have hkOut := hkRest.stmts_prepend (AnnStmt.eraseList (t0 :: ttl)) kn kg
            (fun cur1 s1 env1 blks1 m1 hr1 hkn1 =>
              vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                (.inr (.inl (t0 :: ttl))) W hrules hcs hmode _ kRest k' cur1 s1 env1 blks1 m1 hkRest hr1 hkn1)
            (fun lbl cur1 s1 env1 blks1 m1 hr1 hkg => by
              dsimp only [kg] at hkg
              split at hkg
              · rename_i tgt fs' hgt
                have hlt : sizeOf tgt + AnnStmt.framesSize fs' < sizeOf (t0 :: ttl) :=
                  AnnStmt.findGotoAnnList_sizeOf_lt hgt
                have hfind := AnnStmt.findGotoAnnList_erase hgt env1 blks1 k'
                obtain ⟨hkF, hrF, _⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                  (.inr (.inr fs')) W hrules hcs hmode _ kRest k' cur1 s1 env1 blks1 m1 hkRest hr1
                refine ⟨tgt.erase, env1, (AnnStmt.gotoFramesCont env1 blks1 k' fs').1, m1,
                  (AnnStmt.gotoFramesCont env1 blks1 k' fs').2, ?_, ?_⟩
                · unfold Sem.gotoInCont; rw [hfind]
                · exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                    (.inl (tgt, false)) W hrules hcs hmode _ _ _ _ s1 env1 _ m1 hkF hrF hkg
              · rename_i hgt
                have hnone := AnnStmt.annHasLabelList_erase_none hkg.1 env1 blks1 k'
                unfold Sem.gotoInCont; rw [hnone]
                exact hkRest.onGoto lbl cur1 s1 env1 blks1 m1 hr1 hkg.2)
          refine ⟨hkOut, hrRest, ?_⟩
          intro R hW hk_norm_next cur' s' env' blks' m' hr' hn'
          subst hW
          cases ttl with
          | nil =>
            unfold vcStmtListGen at hn'
            dsimp only [AnnStmt.eraseList]
            refine SafeNext.of_det_state rfl ?_
            exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
              (.inl (t0, false)) _ hrules hcs hmode _ kRest (.stmts [] k')
              cur' s' env' blks' m' (hkRest.stmts_nil (hrules := hrules)) hr' hn'
          | cons t1 ts =>
            unfold vcStmtListGen at hn'
            dsimp only [AnnStmt.eraseList]
            refine SafeNext.of_det_state rfl ?_
            let kn1 : SymState → Prop := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy kRest s1 (t1 :: ts)
            let kg1 : String → SymState → Prop := fun lbl s1 =>
              match hgt : AnnStmt.findGotoAnnList lbl (t1 :: ts) with
              | some (tgt, fs') =>
                vcStmtGen strict prog cfg contracts baseEnv retTy
                  (vcFramesCont strict prog cfg contracts baseEnv retTy kRest s1 fs') s1 tgt
              | none => AnnStmt.annHasLabelList lbl (t1 :: ts) = false ∧ kRest.onGoto lbl s1
            have hk1 := hkRest.stmts_prepend (AnnStmt.eraseList (t1 :: ts)) kn1 kg1
              (fun cur1 s1 env1 blks1 m1 hr1 hkn1 =>
                vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                  (.inr (.inl (t1 :: ts))) _ hrules hcs hmode _ kRest k' cur1 s1 env1 blks1 m1 hkRest hr1 hkn1)
              (fun lbl cur1 s1 env1 blks1 m1 hr1 hkg => by
                dsimp only [kg1] at hkg
                split at hkg
                · rename_i tgt fs' hgt
                  have hlt : sizeOf tgt + AnnStmt.framesSize fs' < sizeOf (t1 :: ts) :=
                    AnnStmt.findGotoAnnList_sizeOf_lt hgt
                  have hfind := AnnStmt.findGotoAnnList_erase hgt env1 blks1 k'
                  obtain ⟨hkF, hrF, _⟩ := vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                    (.inr (.inr fs')) _ hrules hcs hmode _ kRest k' cur1 s1 env1 blks1 m1 hkRest hr1
                  refine ⟨tgt.erase, env1, (AnnStmt.gotoFramesCont env1 blks1 k' fs').1, m1,
                    (AnnStmt.gotoFramesCont env1 blks1 k' fs').2, ?_, ?_⟩
                  · unfold Sem.gotoInCont; rw [hfind]
                  · exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
                      (.inl (tgt, false)) _ hrules hcs hmode _ _ _ _ s1 env1 _ m1 hkF hrF hkg
                · rename_i hgt
                  have hnone := AnnStmt.annHasLabelList_erase_none hkg.1 env1 blks1 k'
                  unfold Sem.gotoInCont; rw [hnone]
                  exact hkRest.onGoto lbl cur1 s1 env1 blks1 m1 hr1 hkg.2)
            change vcStmtGen strict prog cfg contracts baseEnv retTy { kRest with normal := kn1, onGoto := kg1 } s' t0 at hn'
            exact vcStmtGen_sound_aux prog cfg contracts baseEnv Q retTy strict hcs_term hcs_safe
              (.inl (t0, false)) _ hrules hcs hmode _ { kRest with normal := kn1, onGoto := kg1 }
              (.stmts (AnnStmt.eraseList (t1 :: ts)) k') cur' s' env' blks' m' hk1 hr' hn'
      | blockEnd =>
        rw [vcFramesCont_blockEnd]
        dsimp only [framesScopes, AnnStmt.gotoFramesCont]
        refine ⟨ContOKGen.blockEnd (hrules := hrules) hrRest hkRest, hrRest.enter_block, ?_⟩
        intro R hW _ cur' s' env' blks' m' hr' hn'
        subst hW
        rw [hr'.blks_eq]
        refine SafeNext.of_det_state rfl ?_
        have hreg0 : s.regs.length = (allRegSlots (framesScopes cur outer rest).1 (framesScopes cur outer rest).2).length :=
          hrRest.regs_match.length_eq.symm
        have hstk0 : s.stack.length = (allStkSlots (framesScopes cur outer rest).1 (framesScopes cur outer rest).2).length :=
          hrRest.stk_match.length_eq.symm
        have hrex := hr'.exit_block hreg0 hstk0
        rw [← hrRest.env_eq, ← hrRest.blks_eq] at hrex
        exact hkRest.normal (framesScopes cur outer rest).1 (s'.exitBlock s.regs.length s.stack.length)
          env (AnnStmt.gotoFramesCont env blks k rest).1 (m'.freeStack cur'.blks) hrex hn'
      | switchCont =>
        rw [vcFramesCont_switchCont]
        dsimp only [framesScopes, AnnStmt.gotoFramesCont]
        refine ⟨hkRest.switchCont (hrules := hrules), hrRest, ?_⟩
        intro R hW _ cur' s' env' blks' m' hr' hn'
        subst hW
        exact SafeNext.of_det_state rfl (hkRest.normal cur' s' env' blks' m' hr' hn')
termination_by x => match x with
  | .inl (stmt, _) => sizeOf stmt
  | .inr (.inl ss) => sizeOf ss
  | .inr (.inr fs) => AnnStmt.framesSize fs
decreasing_by
  all_goals try simp_wf
  all_goals try simp only [AnnStmt.framesSize_stmts, List.cons.sizeOf_spec] at *
  all_goals omega

/-! ## Public Statement & Function Soundness Theorems -/

theorem vcStmt_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {stmt : AnnStmt}
    (hk : ContOKGen prog cfg (WPTerm prog cfg ext) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcStmt prog cfg specs baseEnv retTy kp s stmt) :
    WPTerm prog cfg ext Q (.running (.stmt stmt.erase) env blks m s.os k) :=
  vcStmtGen_sound_aux prog cfg specs.toContracts baseEnv Q retTy true
    (fun _ => specs.contractsSound_wpTerm) specs.contractsSound_safeUntil
    (.inl (stmt, false)) (WPTerm prog cfg ext) (WPRules.wpTerm prog cfg ext)
    specs.contractsSound_wpTerm (.inl ⟨rfl, Or.inl rfl⟩)
    outer kp k cur s env blks m hk hr hvc

theorem vcStmtList_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {ss : List AnnStmt}
    (hk : ContOKGen prog cfg (WPTerm prog cfg ext) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcStmtList prog cfg specs baseEnv retTy kp s ss) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m s.os (.stmts (AnnStmt.eraseList ss) k)) :=
  vcStmtGen_sound_aux prog cfg specs.toContracts baseEnv Q retTy true
    (fun _ => specs.contractsSound_wpTerm) specs.contractsSound_safeUntil
    (.inr (.inl ss)) (WPTerm prog cfg ext) (WPRules.wpTerm prog cfg ext)
    specs.contractsSound_wpTerm (.inl ⟨rfl, Or.inl rfl⟩)
    outer kp k cur s env blks m hk hr hvc

theorem vcStmt_safeUntil_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {R : RunState → Prop} {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {stmt : AnnStmt}
    (hk : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R u) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcStmt prog cfg specs baseEnv retTy kp s stmt) :
    SafeUntil prog cfg ext Q R (.running (.stmt stmt.erase) env blks m s.os k) :=
  vcStmtGen_sound_aux prog cfg specs.toContracts baseEnv Q retTy true
    (fun _ => specs.contractsSound_wpTerm) specs.contractsSound_safeUntil
    (.inl (stmt, false)) (fun Q' u => SafeUntil prog cfg ext Q' R u)
    (WPRules.safeUntil prog cfg ext R) (specs.contractsSound_safeUntil R)
    (.inl ⟨rfl, Or.inr ⟨R, rfl⟩⟩) outer kp k cur s env blks m hk hr hvc

theorem vcStmtSafe_safeUntil_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {R : RunState → Prop} {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {stmt : AnnStmt}
    (hk : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R u) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcStmtSafe prog cfg specs baseEnv retTy kp s stmt) :
    SafeUntil prog cfg ext Q R (.running (.stmt stmt.erase) env blks m s.os k) :=
  vcStmtGen_sound_aux prog cfg specs.toContracts baseEnv Q retTy false
    (fun h => absurd h Bool.false_ne_true) specs.contractsSound_safeUntil
    (.inl (stmt, false)) (fun Q' u => SafeUntil prog cfg ext Q' R u)
    (WPRules.safeUntil prog cfg ext R) (specs.contractsSound_safeUntil R)
    (.inr ⟨rfl, R, rfl⟩) outer kp k cur s env blks m hk hr hvc

theorem vcStmtSafeList_safeUntil_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {R : RunState → Prop} {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {ss : List AnnStmt}
    (hk : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' R u) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcStmtSafeList prog cfg specs baseEnv retTy kp s ss) :
    SafeUntil prog cfg ext Q R (.running (.stmt .nop) env blks m s.os (.stmts (AnnStmt.eraseList ss) k)) :=
  vcStmtGen_sound_aux prog cfg specs.toContracts baseEnv Q retTy false
    (fun h => absurd h Bool.false_ne_true) specs.contractsSound_safeUntil
    (.inr (.inl ss)) (fun Q' u => SafeUntil prog cfg ext Q' R u)
    (WPRules.safeUntil prog cfg ext R) (specs.contractsSound_safeUntil R)
    (.inr ⟨rfl, R, rfl⟩) outer kp k cur s env blks m hk hr hvc

theorem vcStmtSafe_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {baseEnv : Env} {Q : Val → Mem → OSState → Prop}
    {retTy : CTy} {outer : List FrameScope} {kp : ContPost} {k : Cont}
    {cur : FrameScope} {s : SymState} {env : Env} {blks : List BlockId} {m : Mem} {stmt : AnnStmt}
    (hk : ContOKGen prog cfg (fun Q' u => SafeUntil prog cfg ext Q' (fun _ => False) u) baseEnv Q retTy outer kp k)
    (hr : Refines prog.tags baseEnv cur outer s env blks m)
    (hvc : vcStmtSafe prog cfg specs baseEnv retTy kp s stmt) :
    SafeUntil prog cfg ext Q (fun _ => False) (.running (.stmt stmt.erase) env blks m s.os k) :=
  vcStmtSafe_safeUntil_sound hk hr hvc

private theorem vcFn_call_sound_aux {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {W : (Val → Mem → OSState → Prop) → RunState → Prop}
    (hrules : WPRules prog cfg ext W)
    (hof_call : ∀ {s sym fnTy fn argVals coerced fs ctx env blks m os k Q},
      Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
      prog.fns sym = some fn →
      Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced →
      (∃ callEnv0 callBlks0 m0',
        Sem.pushCallParams prog.tags m (fun _ => 0) 0
          (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
            some (callEnv0, callBlks0, m0')) →
      (∀ base callEnv callBlks m',
        Sem.pushCallParams prog.tags m base 0
          (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
            some (callEnv, callBlks, m') →
        W Q (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k))) →
      W Q s)
    {fn : FnDef} {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    {s : RunState} {fnTy : CTy} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hd : Sem.stepDet prog cfg s = some (.callFn fn.name fnTy argVals fs ctx env blks m os k))
    (hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hcont : ∀ rv m' os', post m os coerced rv m' os' →
      W Q (.running (.expr (.ret (.rval rv fn.retTy) fs) ctx []) env blks m' os' k))
    (hbody : ∀ {cur' : FrameScope} {callEnv : Env} {callBlks : List BlockId} {m' : Mem},
      Refines prog.tags ((prog.fnStatics fn.name) ++ prog.globalEnv) cur' []
        (fnEntryState fn m os coerced) callEnv callBlks m' →
      ContOKGen prog cfg W ((prog.fnStatics fn.name) ++ prog.globalEnv) Q fn.retTy []
        (fnEntryPost fn post m os coerced) (.callFrame env blks fn.retTy fn.body fs ctx k) →
      W Q (.running (.stmt fn.body) callEnv callBlks m' os
        (.callFrame env blks fn.retTy fn.body fs ctx k))) :
    W Q s := by
  obtain ⟨_, hvt⟩ := coerceCallArgs_scalar hsc hco
  have hr_init := Refines.init prog.tags ((prog.fnStatics fn.name) ++ prog.globalEnv) m os
  obtain ⟨cEnv0, cBlks0, cm0', hpush0⟩ := pushCallParams_exists_of_scalar prog.tags
    ((prog.fnStatics fn.name) ++ prog.globalEnv) []
    { regs := [], stack := [], mem := m, os := os }
    ((prog.fnStatics fn.name) ++ prog.globalEnv) [] m 0 hr_init rfl
    (fn.params.zip (coerced.take fn.params.length)) hvt
  refine hof_call hd hfn hco ⟨cEnv0, cBlks0, cm0', hpush0⟩ fun _ callEnv callBlks m' hpush => ?_
  obtain ⟨cur', hr'⟩ := hr_init.of_pushCallParams rfl hvt hpush
  have hr'' : Refines prog.tags ((prog.fnStatics fn.name) ++ prog.globalEnv) cur' []
      (fnEntryState fn m os coerced) callEnv callBlks m' := by
    simpa only [fnEntryState, List.append_nil] using hr'
  exact hbody hr'' (ContOKGen.callFrame (hrules := hrules) (hpost_ext m os coerced) hret_ty env blks fs ctx k hcont)

theorem vcFn_call_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFn prog cfg specs fn annBody pre post)
    {s : RunState} {fnTy : CTy} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop}
    (hd : Sem.stepDet prog cfg s = some (.callFn fn.name fnTy argVals fs ctx env blks m os k))
    (hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hpre : pre m os coerced)
    (hcont : ∀ rv m' os', post m os coerced rv m' os' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv fn.retTy) fs) ctx []) env blks m' os' k)) :
    WPTerm prog cfg ext Q s := by
  obtain ⟨hlen, hvt⟩ := coerceCallArgs_scalar hsc hco
  refine vcFn_call_sound_aux (WPRules.wpTerm prog cfg ext) (fun h1 h2 h3 h4 h5 => WPTerm.of_call_internal h1 h2 h3 h4 h5)
    hfn hsc hret_ty hpost_ext hd hco hcont fun hr'' hkcf => ?_
  have hw := vcStmt_sound hkcf hr'' (hvc m os coerced hvt hlen hpre)
  rwa [herase] at hw

theorem vcFn_safeUntil_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFn prog cfg specs fn annBody pre post)
    {s : RunState} {fnTy : CTy} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop} {R : RunState → Prop}
    (hd : Sem.stepDet prog cfg s = some (.callFn fn.name fnTy argVals fs ctx env blks m os k))
    (hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hpre : pre m os coerced)
    (hcont : ∀ rv m' os', post m os coerced rv m' os' →
      SafeUntil prog cfg ext Q R (.running (.expr (.ret (.rval rv fn.retTy) fs) ctx []) env blks m' os' k)) :
    SafeUntil prog cfg ext Q R s := by
  obtain ⟨hlen, hvt⟩ := coerceCallArgs_scalar hsc hco
  refine vcFn_call_sound_aux (WPRules.safeUntil prog cfg ext R)
    (fun h1 h2 h3 h4 h5 => SafeUntil.of_call_internal h1 h2 h3 h4 h5)
    hfn hsc hret_ty hpost_ext hd hco hcont fun hr'' hkcf => ?_
  have hw := vcStmt_safeUntil_sound hkcf hr'' (hvc m os coerced hvt hlen hpre)
  rwa [herase] at hw

theorem vcFnSafeSplit_safeUntil_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annSafe annTerm : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post)
    {s : RunState} {fnTy : CTy} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop} {R : RunState → Prop}
    (hd : Sem.stepDet prog cfg s = some (.callFn fn.name fnTy argVals fs ctx env blks m os k))
    (hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hpre : pre m os coerced)
    (hcont : ∀ rv m' os', post m os coerced rv m' os' →
      SafeUntil prog cfg ext Q R (.running (.expr (.ret (.rval rv fn.retTy) fs) ctx []) env blks m' os' k)) :
    SafeUntil prog cfg ext Q R s := by
  obtain ⟨hlen, hvt⟩ := coerceCallArgs_scalar hsc hco
  have hsplit := hvc m os coerced hvt hlen hpre
  refine vcFn_call_sound_aux (WPRules.safeUntil prog cfg ext R)
    (fun h1 h2 h3 h4 h5 => SafeUntil.of_call_internal h1 h2 h3 h4 h5)
    hfn hsc hret_ty hpost_ext hd hco hcont fun hr'' hkcf => ?_
  cases hbud : os.readBudget.isSome with
  | false =>
    have hw := vcStmtSafe_safeUntil_sound hkcf hr'' (hsplit.1 hbud)
    rwa [herase_safe] at hw
  | true =>
    have hw := vcStmt_safeUntil_sound hkcf hr'' (hsplit.2 hbud)
    rwa [herase_term] at hw

theorem vcFnSafeSplit_term_sound {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annSafe annTerm : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post)
    {s : RunState} {fnTy : CTy} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont} {Q : Val → Mem → OSState → Prop}
    (hbud : os.readBudget.isSome = true)
    (hd : Sem.stepDet prog cfg s = some (.callFn fn.name fnTy argVals fs ctx env blks m os k))
    (hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hpre : pre m os coerced)
    (hcont : ∀ rv m' os', post m os coerced rv m' os' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv fn.retTy) fs) ctx []) env blks m' os' k)) :
    WPTerm prog cfg ext Q s := by
  obtain ⟨hlen, hvt⟩ := coerceCallArgs_scalar hsc hco
  refine vcFn_call_sound_aux (WPRules.wpTerm prog cfg ext) (fun h1 h2 h3 h4 h5 => WPTerm.of_call_internal h1 h2 h3 h4 h5)
    hfn hsc hret_ty hpost_ext hd hco hcont fun hr'' hkcf => ?_
  have hw := vcStmt_sound hkcf hr'' ((hvc m os coerced hvt hlen hpre).2 hbud)
  rwa [herase_term] at hw

def CallSpec.of_vcFn_frame {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    (specs : SpecEnv prog cfg ext) (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hvc : vcFn prog cfg specs fn annBody pre post) :
    CallSpec prog cfg ext where
  sym := fn.name
  paramTys := fn.params.map (·.ty)
  retTy := fn.retTy
  variadic := fn.variadic
  pre := pre
  post := post
  pre_mono := hpre_mono
  post_stack := hpost_stack
  post_drop := hpost_drop
  sound := fun hd _ _ hco hpre hcont =>
    vcFn_call_sound hfn herase hsc hret_ty hpost_ext hvc hd hco hpre hcont
  sound_safe := fun hd _ _ hco hpre hcont =>
    vcFn_safeUntil_sound hfn herase hsc hret_ty hpost_ext hvc hd hco hpre hcont

def CallSpec.of_vcFn {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    (specs : SpecEnv prog cfg ext) (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpres : ∀ {m : Mem} {os : OSState} {args : List Val} {rv : Val} {m' : Mem} {os' : OSState},
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk)
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hvc : vcFn prog cfg specs fn annBody pre post) :
    CallSpec prog cfg ext :=
  CallSpec.of_vcFn_frame specs fn annBody pre post hfn herase hsc hret_ty hpost_ext
    hpre_mono (post_stack_of_preserve (pre := pre) (post := post) hpres) hpost_drop hvc

def CallSafeSpec.of_vcFnSafeSplit_frame {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    (specs : SafeSpecEnv prog cfg ext) (fn : FnDef) (annSafe annTerm : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hfn : prog.fns fn.name = some fn)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hvc : vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post) :
    CallSafeSpec prog cfg ext where
  sym := fn.name
  paramTys := fn.params.map (·.ty)
  retTy := fn.retTy
  variadic := fn.variadic
  pre := pre
  post := post
  pre_mono := hpre_mono
  post_stack := hpost_stack
  post_drop := hpost_drop
  sound_safe := fun hd _ _ hco hpre hcont =>
    vcFnSafeSplit_safeUntil_sound hfn herase_safe herase_term hsc hret_ty hpost_ext hvc hd hco hpre hcont
  sound_term := fun hbud hd _ _ hco hpre hcont =>
    vcFnSafeSplit_term_sound hfn herase_term hsc hret_ty hpost_ext hvc hbud hd hco hpre hcont

def CallSafeSpec.of_vcFnSafe_frame {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    (specs : SafeSpecEnv prog cfg ext) (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hvc : vcFnSafe prog cfg specs fn annBody pre post) :
    CallSafeSpec prog cfg ext :=
  CallSafeSpec.of_vcFnSafeSplit_frame specs fn annBody annBody pre post hfn herase herase hsc hret_ty hpost_ext
    hpre_mono hpost_stack hpost_drop hvc

def CallSafeSpec.of_vcFnSafe {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    (specs : SafeSpecEnv prog cfg ext) (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpres : ∀ {m : Mem} {os : OSState} {args : List Val} {rv : Val} {m' : Mem} {os' : OSState},
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk)
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hvc : vcFnSafe prog cfg specs fn annBody pre post) :
    CallSafeSpec prog cfg ext :=
  CallSafeSpec.of_vcFnSafe_frame specs fn annBody pre post hfn herase hsc hret_ty hpost_ext
    hpre_mono (post_stack_of_preserve (pre := pre) (post := post) hpres) hpost_drop hvc

def CallSafeSpec.of_vcFn {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    (specs : SpecEnv prog cfg ext) (fn : FnDef) (annBody : AnnStmt)
    (pre : Mem → OSState → List Val → Prop)
    (post : Mem → OSState → List Val → Val → Mem → OSState → Prop)
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args → pre m os args)
    (hpres : ∀ {m : Mem} {os : OSState} {args : List Val} {rv : Val} {m' : Mem} {os' : OSState},
      post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk)
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      pre m_clean os args →
      post m os args rv m_after os' →
      post m_clean os args rv (dropBlks m_after bs) os')
    (hvc : vcFn prog cfg specs fn annBody pre post) :
    CallSafeSpec prog cfg ext :=
  (CallSpec.of_vcFn specs fn annBody pre post hfn herase hsc hret_ty hpost_ext hpre_mono hpres hpost_drop hvc).toSafeSpec

def callEntryState (fn : FnDef) (m : Mem) (os : OSState) (args : List Val) : RunState :=
  match args.reverse with
  | [] =>
    .running
      (.expr (.ret (.rval (.fnPtr fn.name) (.fnPtr fn.retTy (fn.params.map (·.ty)) fn.variadic))
        [.callFnF []]) .returnVal [])
      [] [] m os (.stop fn.retTy)
  | last :: rest =>
    .running
      (.expr (.ret (.rval last .void)
        [.callArgF fn.name (.fnPtr fn.retTy (fn.params.map (·.ty)) fn.variadic)
          (rest.reverse.map (·, .void)) []])
        .returnVal [])
      [] [] m os (.stop fn.retTy)

private theorem stepDet_callEntryState (prog : Prog) (cfg : PointerConfig)
    (fn : FnDef) (m : Mem) (os : OSState) (args : List Val) :
    Sem.stepDet prog cfg (callEntryState fn m os args) =
      some (.callFn fn.name (.fnPtr fn.retTy (fn.params.map (·.ty)) fn.variadic)
        (args.map (·, .void)) [] .returnVal [] [] m os (.stop fn.retTy)) := by
  unfold callEntryState
  cases hr : args.reverse with
  | nil =>
    have ha : args = [] := List.reverse_eq_nil_iff.mp hr
    subst ha
    rfl
  | cons last rest =>
    have ha : args = rest.reverse ++ [last] := by
      have h := congrArg List.reverse hr
      simpa using h
    conv => rhs; rw [ha, List.map_append, List.map_cons, List.map_nil]
    dsimp only
    cases last <;> rfl

private theorem runStateReadBudgetIsSome_callEntryState (fn : FnDef) (m : Mem) (os : OSState)
    (args : List Val) :
    runStateReadBudgetIsSome (callEntryState fn m os args) = os.readBudget.isSome := by
  unfold callEntryState
  cases args.reverse <;> rfl

private theorem callState_ret_det {prog : Prog} {cfg : PointerConfig}
    {fn : FnDef} {m0 m' : Mem} {os0 os' : OSState} {args : List Val}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    {rv : Val} (hp : post m0 os0 args rv m' os') :
    Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval rv fn.retTy) []) .returnVal []) [] [] m' os' (.stop fn.retTy)) =
      some (.next (.returned rv m' os')) := by
  rcases hret_ok with ⟨hvoid, hrv_void⟩ | ⟨hnonvoid, hval⟩
  · have hrv := hrv_void m0 os0 args rv m' os' hp
    unfold Sem.stepDet
    simp [hvoid, hrv, Sem.Cont.topRetTy, CTy.isVoid, CTy.unqual, Sem.unwindReturn]
  · have hcast := (hval m0 os0 args rv m' os' hp).castVal_self m'
    unfold Sem.stepDet
    simp [Sem.Cont.topRetTy, hnonvoid, hcast, Sem.unwindReturn]

theorem vcFn_callState_variadic {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hva : fn.variadic = true)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFn prog cfg specs fn annBody pre post)
    {m : Mem} {os : OSState} {args : List Val}
    (hle : fn.params.length ≤ args.length)
    (hvt : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2)
    (hprom : ∀ a ∈ args.drop fn.params.length, Sem.promoteVariadicArg a = a)
    (hpre : pre m os args) :
    WPTerm prog cfg ext (fun rv m' os' => post m os args rv m' os') (callEntryState fn m os args) := by
  have hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) := by
    rcases hret_ok with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h1
  have hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic (args.map (·, .void)) = some args := by
    rw [hva]
    exact coerceCallArgs_variadic_of_valScalarTyped hle hvt hprom
  exact vcFn_call_sound hfn herase hsc hret_ty hpost_ext hvc
    (stepDet_callEntryState prog cfg fn m os args) hco hpre
    fun rv m' os' hp => WPTerm.of_det_state (callState_ret_det hret_ok hp) (WPTerm.returned hp)

theorem vcFn_callState {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonva : fn.variadic = false)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFn prog cfg specs fn annBody pre post)
    {m : Mem} {os : OSState} {args : List Val}
    (hlen : args.length = fn.params.length)
    (hvt : ∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2)
    (hpre : pre m os args) :
    WPTerm prog cfg ext (fun rv m' os' => post m os args rv m' os') (callEntryState fn m os args) := by
  have hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) := by
    rcases hret_ok with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h1
  have hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic (args.map (·, .void)) = some args := by
    rw [hnonva]
    exact coerceCallArgs_of_valScalarTyped hlen hvt
  exact vcFn_call_sound hfn herase hsc hret_ty hpost_ext hvc
    (stepDet_callEntryState prog cfg fn m os args) hco hpre
    fun rv m' os' hp => WPTerm.of_det_state (callState_ret_det hret_ok hp) (WPTerm.returned hp)

theorem vcFnSafeSplit_callState_variadic {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annSafe annTerm : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hva : fn.variadic = true)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post)
    {m : Mem} {os : OSState} {args : List Val}
    (hle : fn.params.length ≤ args.length)
    (hvt : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2)
    (hprom : ∀ a ∈ args.drop fn.params.length, Sem.promoteVariadicArg a = a)
    (hpre : pre m os args) :
    WPSafe prog cfg ext (fun rv m' os' => post m os args rv m' os') (callEntryState fn m os args) := by
  have hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) := by
    rcases hret_ok with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h1
  have hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic (args.map (·, .void)) = some args := by
    rw [hva]
    exact coerceCallArgs_variadic_of_valScalarTyped hle hvt hprom
  refine ⟨?_, fun hbud => ?_⟩
  · exact vcFnSafeSplit_safeUntil_sound hfn herase_safe herase_term hsc hret_ty hpost_ext hvc
      (stepDet_callEntryState prog cfg fn m os args) hco hpre
      fun rv m' os' hp => SafeUntil.of_det_state (callState_ret_det hret_ok hp) (SafeUntil.returned hp)
  · rw [runStateReadBudgetIsSome_callEntryState] at hbud
    exact vcFnSafeSplit_term_sound hfn herase_term hsc hret_ty hpost_ext hvc hbud
      (stepDet_callEntryState prog cfg fn m os args) hco hpre
      fun rv m' os' hp => WPTerm.of_det_state (callState_ret_det hret_ok hp) (WPTerm.returned hp)

theorem vcFnSafeSplit_callState {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annSafe annTerm : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonva : fn.variadic = false)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post)
    {m : Mem} {os : OSState} {args : List Val}
    (hlen : args.length = fn.params.length)
    (hvt : ∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2)
    (hpre : pre m os args) :
    WPSafe prog cfg ext (fun rv m' os' => post m os args rv m' os') (callEntryState fn m os args) := by
  have hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) := by
    rcases hret_ok with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h1
  have hco : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic (args.map (·, .void)) = some args := by
    rw [hnonva]
    exact coerceCallArgs_of_valScalarTyped hlen hvt
  refine ⟨?_, fun hbud => ?_⟩
  · exact vcFnSafeSplit_safeUntil_sound hfn herase_safe herase_term hsc hret_ty hpost_ext hvc
      (stepDet_callEntryState prog cfg fn m os args) hco hpre
      fun rv m' os' hp => SafeUntil.of_det_state (callState_ret_det hret_ok hp) (SafeUntil.returned hp)
  · rw [runStateReadBudgetIsSome_callEntryState] at hbud
    exact vcFnSafeSplit_term_sound hfn herase_term hsc hret_ty hpost_ext hvc hbud
      (stepDet_callEntryState prog cfg fn m os args) hco hpre
      fun rv m' os' hp => WPTerm.of_det_state (callState_ret_det hret_ok hp) (WPTerm.returned hp)

theorem vcFnSafe_callState_variadic {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hva : fn.variadic = true)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFnSafe prog cfg specs fn annBody pre post)
    {m : Mem} {os : OSState} {args : List Val}
    (hle : fn.params.length ≤ args.length)
    (hvt : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2)
    (hprom : ∀ a ∈ args.drop fn.params.length, Sem.promoteVariadicArg a = a)
    (hpre : pre m os args) :
    WPSafe prog cfg ext (fun rv m' os' => post m os args rv m' os') (callEntryState fn m os args) :=
  vcFnSafeSplit_callState_variadic hfn hva herase herase hsc hret_ok hpost_ext hvc hle hvt hprom hpre

theorem vcFnSafe_callState {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonva : fn.variadic = false)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : vcFnSafe prog cfg specs fn annBody pre post)
    {m : Mem} {os : OSState} {args : List Val}
    (hlen : args.length = fn.params.length)
    (hvt : ∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2)
    (hpre : pre m os args) :
    WPSafe prog cfg ext (fun rv m' os' => post m os args rv m' os') (callEntryState fn m os args) :=
  vcFnSafeSplit_callState hfn hnonva herase herase hsc hret_ok hpost_ext hvc hlen hvt hpre

end C99.Proof.VCGen
