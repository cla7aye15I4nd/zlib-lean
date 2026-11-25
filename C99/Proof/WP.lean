import C99.Proof.Mem

/-!
# Weakest-Precondition Reasoning for `C99.Sem` (`C99.Proof.WP`)

Application-agnostic terminating weakest precondition (`WPTerm`) over `C99.Sem.Step`,
soundness bridges (`Safe`, `TerminatesSafely`, postcondition extraction),
single-step elimination lemmas for every `Step` constructor, `pushCallParams`
frame/allocation helpers, well-founded loop rules (`while`, `do-while`, `for`),
and deterministic stepping tactics (`wp_det`, `wp_steps`).
-/

namespace C99.Proof

open C99 C99.Sem

/-! ## `Star` Utilities & Basic `Step` Inversion -/

theorem star_trans {α : Type} {R : α → α → Prop} {x y z : α}
    (h1 : Star R x y) (h2 : Star R y z) : Star R x z := by
  induction h2 with
  | refl => exact h1
  | tail _ hr ih => exact .tail ih hr

theorem star_head {α : Type} {R : α → α → Prop} {x y z : α}
    (h1 : R x y) (h2 : Star R y z) : Star R x z :=
  star_trans (.tail (.refl x) h1) h2

theorem step_not_returned {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {v : Val} {m : Mem} {os : OSState} {s' : RunState}
    (h : Step prog cfg ext (.returned v m os) s') : False := by
  cases h with
  | det hd | strLit hd | localDecl hd | localDecl_ub hd
  | call_internal hd | call_internal_ub hd | call_ext hd | call_ext_ub hd =>
    cases hd

theorem step_not_ub {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {s' : RunState} (h : Step prog cfg ext .ub s') : False := by
  cases h with
  | det hd | strLit hd | localDecl hd | localDecl_ub hd
  | call_internal hd | call_internal_ub hd | call_ext hd | call_ext_ub hd =>
    cases hd

private theorem not_isUB_of_stepDet_some {prog : Prog} {cfg : PointerConfig}
    {s : RunState} {d : DetStep} (hd : stepDet prog cfg s = some d) : ¬ s.isUB := by
  cases s with
  | ub => cases hd
  | returned _ _ _ => cases hd
  | running _ _ _ _ _ _ => exact Bool.false_ne_true

/-! ## Terminating Weakest Precondition (`WPTerm`) & Soundness Bridges -/

/-- Inductive weakest precondition guaranteeing safety and finite termination in
`.returned v m os` satisfying `Q v m os`. -/
inductive WPTerm (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) : RunState → Prop where
  | returned {v m os} : Q v m os → WPTerm prog cfg ext Q (.returned v m os)
  | step {s : RunState} :
      ¬ s.isUB →
      (∃ s', Step prog cfg ext s s') →
      (∀ s', Step prog cfg ext s s' → WPTerm prog cfg ext Q s') →
      WPTerm prog cfg ext Q s

theorem WPTerm.star_inv {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s s' : RunState}
    (hw : WPTerm prog cfg ext Q s) (hstar : Star (Step prog cfg ext) s s') :
    WPTerm prog cfg ext Q s' := by
  induction hstar with
  | refl => exact hw
  | tail _ hstep ih =>
    cases ih with
    | returned _ => exact False.elim (step_not_returned hstep)
    | step _ _ hnext => exact hnext _ hstep

theorem WPTerm.safe {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    (hw : WPTerm prog cfg ext Q s) : Safe prog cfg ext s := by
  intro s' hstar
  cases hw.star_inv hstar with
  | returned _ => exact Bool.false_ne_true
  | step hnot _ _ => exact hnot

theorem WPTerm.terminatesSafely {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    (hw : WPTerm prog cfg ext Q s) : TerminatesSafely prog cfg ext s := by
  refine ⟨hw.safe, ?_⟩
  induction hw with
  | returned _ => exact ⟨_, _, _, .refl _⟩
  | step _ hex _ ih =>
    obtain ⟨s', hstep⟩ := hex
    obtain ⟨v, m, os, hstar⟩ := ih s' hstep
    exact ⟨v, m, os, star_head hstep hstar⟩

theorem WPTerm.post {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState} {v : Val} {m : Mem} {os : OSState}
    (hw : WPTerm prog cfg ext Q s) (hstar : Star (Step prog cfg ext) s (.returned v m os)) :
    Q v m os := by
  cases hw.star_inv hstar with
  | returned hq => exact hq
  | step _ hex _ =>
    obtain ⟨_, hstep⟩ := hex
    exact False.elim (step_not_returned hstep)

theorem WPTerm.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q1 Q2 : Val → Mem → OSState → Prop} {s : RunState}
    (hm : ∀ v m os, Q1 v m os → Q2 v m os) (hw : WPTerm prog cfg ext Q1 s) :
    WPTerm prog cfg ext Q2 s := by
  induction hw with
  | returned hq => exact .returned (hm _ _ _ hq)
  | step hnot hex _ ih => exact .step hnot hex (fun s' hs => ih s' hs)

/-! ## Single-Step Elimination Lemmas -/

theorem WPTerm.of_det_state {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s s' : RunState}
    (hd : stepDet prog cfg s = some (.next s'))
    (hw : WPTerm prog cfg ext Q s') :
    WPTerm prog cfg ext Q s := by
  refine .step (not_isUB_of_stepDet_some hd) ⟨s', .det hd⟩ ?_
  intro s'' hstep
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

theorem WPTerm.of_det {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ctrl : Control} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    {s' : RunState}
    (hd : stepDet prog cfg (.running ctrl env blks m os k) = some (.next s'))
    (hw : WPTerm prog cfg ext Q s') :
    WPTerm prog cfg ext Q (.running ctrl env blks m os k) :=
  WPTerm.of_det_state hd hw

private theorem stepDet_eval_lval (prog : Prog) (cfg : PointerConfig)
    (e : CExpr) (fs : List ExprFrame) (ctx : ExprCtx) (mods : ModSet)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont) :
    stepDet prog cfg (.running (.expr (.eval .lval e fs) ctx mods) env blks m os k) =
      (stepExprPure prog cfg env m mods (.eval .lval e fs)).map
        (fun (es', m', mods') => .next (.running (.expr es' ctx mods') env blks m' os k)) := rfl

private theorem stepDet_eval_rval_other (prog : Prog) (cfg : PointerConfig)
    (e : CExpr) (hnot : ∀ s, e ≠ .strLit s)
    (fs : List ExprFrame) (ctx : ExprCtx) (mods : ModSet)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont) :
    stepDet prog cfg (.running (.expr (.eval .rval e fs) ctx mods) env blks m os k) =
      (stepExprPure prog cfg env m mods (.eval .rval e fs)).map
        (fun (es', m', mods') => .next (.running (.expr es' ctx mods') env blks m' os k)) := by
  cases e <;> first | exact False.elim (hnot _ rfl) | rfl

private theorem stepExprPure_ret_nil (prog : Prog) (cfg : PointerConfig)
    (env : Env) (m : Mem) (mods : ModSet) (rv : ExprRes) :
    stepExprPure prog cfg env m mods (.ret rv []) = none := by
  cases rv with
  | lval _ _ _ | structVal _ _ => rfl
  | rval v _ => cases v <;> rfl

private theorem stepDet_ret_cons_other (prog : Prog) (cfg : PointerConfig)
    (rv : ExprRes) (f : ExprFrame) (rest : List ExprFrame)
    (h1 : ∀ sym fnTy, ¬ (f = .callFnF [] ∧ rv = .rval (.fnPtr sym) fnTy))
    (h2 : ∀ sym fnTy done v ty, ¬ (f = .callArgF sym fnTy done [] ∧ rv = .rval v ty))
    (ctx : ExprCtx) (mods : ModSet) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (k : Cont) :
    stepDet prog cfg (.running (.expr (.ret rv (f :: rest)) ctx mods) env blks m os k) =
      (stepExprPure prog cfg env m mods (.ret rv (f :: rest))).map
        (fun (es', m', mods') => .next (.running (.expr es' ctx mods') env blks m' os k)) := by
  cases rv with
  | lval _ _ _ | structVal _ _ =>
    cases f with
    | callFnF args => cases args <;> rfl
    | callArgF _ _ _ todo => cases todo <;> rfl
    | _ => rfl
  | rval v _ =>
    cases f with
    | callFnF args =>
      cases args with
      | nil => cases v <;> first | exact False.elim (h1 _ _ ⟨rfl, rfl⟩) | rfl
      | cons _ _ => cases v <;> rfl
    | callArgF _ _ _ todo =>
      cases todo with
      | nil => exact False.elim (h2 _ _ _ _ _ ⟨rfl, rfl⟩)
      | cons _ _ => cases v <;> rfl
    | _ => cases v <;> rfl

theorem stepDet_exprPure {prog : Prog} {cfg : PointerConfig}
    {es es' : ExprState} {ctx : ExprCtx} {mods mods' : ModSet}
    {env : Env} {blks : List BlockId} {m m' : Mem} {os : OSState} {k : Cont}
    (h : stepExprPure prog cfg env m mods es = some (es', m', mods')) :
    stepDet prog cfg (.running (.expr es ctx mods) env blks m os k) =
      some (.next (.running (.expr es' ctx mods') env blks m' os k)) := by
  cases es with
  | eval w e fs =>
    cases w with
    | lval => rw [stepDet_eval_lval, h]; rfl
    | rval =>
      rw [stepDet_eval_rval_other _ _ _ (fun s he => by subst he; unfold stepExprPure at h; cases h), h]; rfl
  | ret rv fs =>
    cases fs with
    | nil => rw [stepExprPure_ret_nil] at h; cases h
    | cons f rest =>
      rw [stepDet_ret_cons_other _ _ rv f rest
        (fun sym fnTy ⟨hf, hrv⟩ => by subst hf hrv; unfold stepExprPure at h; cases h)
        (fun sym fnTy done v ty ⟨hf, hrv⟩ => by subst hf hrv; unfold stepExprPure at h; cases h), h]
      rfl

theorem WPTerm.of_exprPure {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {es es' : ExprState} {ctx : ExprCtx} {mods mods' : ModSet}
    {env : Env} {blks : List BlockId} {m m' : Mem} {os : OSState} {k : Cont}
    (h : stepExprPure prog cfg env m mods es = some (es', m', mods'))
    (hw : WPTerm prog cfg ext Q (.running (.expr es' ctx mods') env blks m' os k)) :
    WPTerm prog cfg ext Q (.running (.expr es ctx mods) env blks m os k) :=
  WPTerm.of_det (stepDet_exprPure h) hw

theorem WPTerm.of_strLit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    {str : String} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hd : stepDet prog cfg s = some (.allocStr str fs ctx mods env blks m os k))
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (hw : ∀ (base : UInt64) (bid : BlockId) (m' : Mem),
      m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods)
          env blks m' os k)) :
    WPTerm prog cfg ext Q s := by
  let alloc0 := m.alloc (str.utf8ByteSize + 1) 1 .ro .global 0
    (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)
  refine .step (not_isUB_of_stepDet_some hd) ⟨_, .strLit hd hsz (base := 0) (bid := alloc0.1) (m' := alloc0.2) rfl⟩ ?_
  intro s' hstep
  cases hstep with
  | strLit hd' _ halloc' =>
    rw [hd] at hd'
    cases hd'
    exact hw _ _ _ halloc'
  | det hd' | det_ub hd' | localDecl hd' | localDecl_ub hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'
    cases hd'

theorem WPTerm.of_localDecl_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    {d : VarDecl} {rest : List VarDecl} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : stepDet prog cfg s = some (.allocLocal d none rest env blks m os k))
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os k)) :
    WPTerm prog cfg ext Q s := by
  let hba0 : (0 : UInt64).toNat % max 1 (alignofTy prog.tags d.ty) = 0 := Nat.zero_mod _
  let alloc0 := m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
    .rw .stack 0 (fun _ => .undef) hsz hal hba0
  refine .step (not_isUB_of_stepDet_some hd)
    ⟨_, .localDecl hd hsz hal (base := 0) (bid := alloc0.1) (m1 := alloc0.2) (m2 := alloc0.2) hba0 rfl rfl⟩ ?_
  intro s' hstep
  cases hstep with
  | localDecl hd' _ _ hba' halloc' hwr' =>
    rw [hd] at hd'
    cases hd'
    cases hwr'
    exact hw _ _ _ hba' halloc'
  | localDecl_ub hd' hbad =>
    rw [hd] at hd'
    cases hd'
    exact False.elim (hbad 0 alloc0.2 alloc0.1 alloc0.2 hsz hal hba0 rfl rfl)
  | det hd' | det_ub hd' | strLit hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'
    cases hd'

theorem WPTerm.of_localDecl_some {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    {d : VarDecl} {rv : ExprRes} {rest : List VarDecl} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : stepDet prog cfg s = some (.allocLocal d (some rv) rest env blks m os k))
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      ∃ r m2, writePlace prog.tags m1 bid 0 d.ty.stripConst rv = some (r, m2) ∧
        WPTerm prog cfg ext Q
          (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os k)) :
    WPTerm prog cfg ext Q s := by
  let hba0 : (0 : UInt64).toNat % max 1 (alignofTy prog.tags d.ty) = 0 := Nat.zero_mod _
  let alloc0 := m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
    .rw .stack 0 (fun _ => .undef) hsz hal hba0
  obtain ⟨r0, m20, hwr0, _⟩ := hw 0 alloc0.1 alloc0.2 hba0 rfl
  refine .step (not_isUB_of_stepDet_some hd)
    ⟨_, .localDecl hd hsz hal (base := 0) (bid := alloc0.1) (m1 := alloc0.2) (m2 := m20) hba0 rfl ⟨r0, hwr0⟩⟩ ?_
  intro s' hstep
  cases hstep with
  | localDecl hd' _ _ hba' halloc' hwr' =>
    rw [hd] at hd'
    cases hd'
    obtain ⟨r', hr'⟩ := hwr'
    obtain ⟨r, m2, hwr, hnext⟩ := hw _ _ _ hba' halloc'
    rw [hwr] at hr'
    cases hr'
    exact hnext
  | localDecl_ub hd' hbad =>
    rw [hd] at hd'
    cases hd'
    exact False.elim (hbad 0 alloc0.2 alloc0.1 m20 hsz hal hba0 rfl ⟨r0, hwr0⟩)
  | det hd' | det_ub hd' | strLit hd'
  | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
    rw [hd] at hd'
    cases hd'

theorem WPTerm.of_call_internal {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    {sym : String} {fnTy : CTy} {fn : FnDef} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hcoerce : coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hwit : ∃ callEnv0 callBlks0 m0',
      pushCallParams prog.tags m (fun _ => 0) 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv0, callBlks0, m0'))
    (hw : ∀ base callEnv callBlks m',
      pushCallParams prog.tags m base 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv, callBlks, m') →
      WPTerm prog cfg ext Q
        (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k))) :
    WPTerm prog cfg ext Q s := by
  obtain ⟨callEnv0, callBlks0, m0', hpush0⟩ := hwit
  refine .step (not_isUB_of_stepDet_some hd)
    ⟨_, .call_internal hd hfn hcoerce hpush0⟩ ?_
  intro s' hstep
  cases hstep with
  | call_internal hd' hfn' hcoerce' hpush' =>
    rw [hd] at hd'
    cases hd'
    rw [hfn] at hfn'
    cases hfn'
    rw [hcoerce] at hcoerce'
    cases hcoerce'
    exact hw _ _ _ _ hpush'
  | call_internal_ub hd' hfn' hbad =>
    rw [hd] at hd'
    cases hd'
    rw [hfn] at hfn'
    cases hfn'
    exact False.elim (hbad coerced (fun _ => 0) callEnv0 callBlks0 m0' hcoerce hpush0)
  | call_ext hd' hnfn' | call_ext_ub hd' hnfn' =>
    rw [hd] at hd'
    cases hd'
    rw [hfn] at hnfn'
    cases hnfn'
  | det hd' | det_ub hd' | strLit hd' | localDecl hd' | localDecl_ub hd' =>
    rw [hd] at hd'
    cases hd'

theorem WPTerm.of_call_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : RunState}
    {sym : String} {fnTy retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Cont}
    (hd : stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hnfn : prog.fns sym = none)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : coerceCallArgs m paramTys variadic argVals = some coerced)
    (hex : ∃ ret m' os', ext sym coerced m os (.ok ret m' os'))
    (hnoub : ¬ ext sym coerced m os .ub)
    (hw : ∀ ret m' os', ext sym coerced m os (.ok ret m' os') →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    WPTerm prog cfg ext Q s := by
  obtain ⟨ret0, m0', os0', hext0⟩ := hex
  refine .step (not_isUB_of_stepDet_some hd)
    ⟨_, .call_ext hd hnfn hsig hcoerce hext0⟩ ?_
  intro s' hstep
  cases hstep with
  | call_ext hd' hnfn' hsig' hcoerce' hext' =>
    rw [hd] at hd'
    cases hd'
    rw [hsig] at hsig'
    cases hsig'
    rw [hcoerce] at hcoerce'
    cases hcoerce'
    rename_i out'
    cases out' with
    | ok ret' m' os' => exact hw ret' m' os' hext'
    | ub => exact False.elim (hnoub hext')
  | call_ext_ub hd' hnfn' hbad =>
    rw [hd] at hd'
    cases hd'
    exact False.elim (hbad ⟨retTy, paramTys, variadic, coerced, hsig, hcoerce⟩)
  | call_internal hd' hfn' | call_internal_ub hd' hfn' =>
    rw [hd] at hd'
    cases hd'
    rw [hnfn] at hfn'
    cases hfn'
  | det hd' | det_ub hd' | strLit hd' | localDecl hd' | localDecl_ub hd' =>
    rw [hd] at hd'
    cases hd'

/-! ## Type Qualifier, Scalar Write, and `pushCallParams` Frame Lemmas -/

@[simp] theorem stripConst_isConst : ∀ ty : CTy, ty.stripConst.isConst = false
  | .typedef _ t => by simp [CTy.stripConst, CTy.isConst, stripConst_isConst t]
  | .const_ t => by simp [CTy.stripConst, stripConst_isConst t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

@[simp] theorem stripConst_unqual : ∀ ty : CTy, ty.stripConst.unqual = ty.unqual
  | .typedef _ t => by simp [CTy.stripConst, CTy.unqual, stripConst_unqual t]
  | .const_ t => by simp [CTy.stripConst, CTy.unqual, stripConst_unqual t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

theorem alignofAux_unqual (env : TypeEnv) (fuel : Nat) :
    ∀ ty : CTy, alignofAux env fuel ty.unqual = alignofAux env fuel ty
  | .const_ t => by simp [CTy.unqual, alignofAux, alignofAux_unqual env fuel t]
  | .typedef _ t => by simp [CTy.unqual, alignofAux, alignofAux_unqual env fuel t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

theorem sizeofAux_unqual (env : TypeEnv) (fuel : Nat) :
    ∀ ty : CTy, sizeofAux env fuel ty.unqual = sizeofAux env fuel ty
  | .const_ t => by simp [CTy.unqual, sizeofAux, sizeofAux_unqual env fuel t]
  | .typedef _ t => by simp [CTy.unqual, sizeofAux, sizeofAux_unqual env fuel t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

theorem alignofTy_unqual (env : TypeEnv) (ty : CTy) :
    alignofTy env ty.unqual = alignofTy env ty :=
  alignofAux_unqual env (env.length + 1) ty

theorem sizeofTy_unqual (env : TypeEnv) (ty : CTy) :
    sizeofTy env ty.unqual = sizeofTy env ty :=
  sizeofAux_unqual env (env.length + 1) ty

@[simp] theorem sizeofTy_int (env : TypeEnv) (k : IntKind) :
    sizeofTy env (.int k) = k.bytes := by
  unfold sizeofTy sizeofAux; rfl

@[simp] theorem alignofTy_int (env : TypeEnv) (k : IntKind) :
    alignofTy env (.int k) = k.align := by
  unfold alignofTy alignofAux; rfl

@[simp] theorem sizeofTy_ptr (env : TypeEnv) (el : CTy) :
    sizeofTy env (.ptr el) = 8 := by
  unfold sizeofTy sizeofAux; rfl

@[simp] theorem alignofTy_ptr (env : TypeEnv) (el : CTy) :
    alignofTy env (.ptr el) = 8 := by
  unfold alignofTy alignofAux; rfl

theorem writeVal_writeBytes {m m' : Mem} {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (h : writeVal m b off ty v = some m') :
    ∃ bs, m.writeBytes b off bs = some m' := by
  unfold writeVal at h
  by_cases hc : ty.isConst
  · simp [hc, bind, Option.bind, guard] at h
  · simp only [hc, Bool.not_false, guard_true, bind, Option.bind] at h
    cases hblk : m.blocks b with
    | none => simp [hblk] at h
    | some blk =>
      simp only [hblk] at h
      cases hty : ty.unqual with
      | int k =>
        simp only [hty, CTy.unqual, CTy.intKind?] at h
        cases ha : Mem.isAligned blk off k.align with
        | false =>
          dsimp only [guard, bind, Option.bind] at h
          rw [ha] at h
          cases h
        | true =>
          simp only [ha, guard_true] at h
          cases hvi : valAsInt? v with
          | none => simp [hvi] at h
          | some p => simp only [hvi] at h; exact ⟨_, h⟩
      | enumTy tag isU =>
        simp only [hty, CTy.unqual, CTy.intKind?] at h
        cases ha : Mem.isAligned blk off (if isU then IntKind.u32 else IntKind.i32).align with
        | false =>
          dsimp only [guard, bind, Option.bind] at h
          rw [ha] at h
          cases h
        | true =>
          simp only [ha, guard_true] at h
          cases hvi : valAsInt? v with
          | none => simp [hvi] at h
          | some p => simp only [hvi] at h; exact ⟨_, h⟩
      | ptr _ =>
        simp only [hty] at h
        cases ha : Mem.isAligned blk off 8 with
        | false =>
          rw [ha] at h
          cases h
        | true =>
          simp only [ha, guard_true] at h
          cases v with
          | null => exact ⟨_, h⟩
          | ptr pb poff => exact ⟨_, h⟩
          | int _ bv =>
            by_cases hz : bv.toNat == 0
            · simp only [hz, ↓reduceIte] at h; exact ⟨_, h⟩
            · simp [hz] at h
          | _ => cases h
      | fnPtr _ _ _ =>
        simp only [hty] at h
        cases ha : Mem.isAligned blk off 8 with
        | false =>
          rw [ha] at h
          cases h
        | true =>
          simp only [ha, guard_true] at h
          cases v with
          | null => exact ⟨_, h⟩
          | fnPtr s => exact ⟨_, h⟩
          | int _ bv =>
            by_cases hz : bv.toNat == 0
            · simp only [hz, ↓reduceIte] at h; exact ⟨_, h⟩
            · simp [hz] at h
          | _ => cases h
      | vaList =>
        simp only [hty] at h
        cases v with
        | vaList valid =>
          cases valid with
          | false => cases h
          | true => exact ⟨_, h⟩
        | _ => cases h
      | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
        simp [hty] at h

theorem writePlace_writeBytes {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {rv : ExprRes} {res : ExprRes}
    (h : writePlace tags m b off ty rv = some (res, m')) :
    ∃ bs, m.writeBytes b off bs = some m' := by
  cases rv with
  | lval _ _ _ => cases h
  | structVal bs _ =>
    unfold writePlace at h
    dsimp only at h
    by_cases hlen : bs.length == sizeofTy tags ty
    · simp only [hlen, ↓reduceIte, Option.map] at h
      cases hm : m.writeBytes b off bs with
      | none => simp [hm] at h
      | some m1 => simp only [hm] at h; cases h; exact ⟨bs, hm⟩
    · simp [hlen] at h
  | rval v _ =>
    unfold writePlace at h
    dsimp only [bind, Option.bind, pure, Pure.pure] at h
    cases hty : ty.unqual <;> simp only [hty] at h
    all_goals
      first
      | (cases hc : castVal m ty v with
         | none => simp [hc] at h
         | some cv =>
           simp only [hc] at h
           cases hw : writeVal m b off ty cv with
           | none => simp [hw] at h
           | some m1 => simp only [hw] at h; cases h; exact writeVal_writeBytes hw)
      | (cases hw : writeVal m b off ty v with
         | none => simp [hw] at h
         | some m1 => simp only [hw] at h; cases h; exact writeVal_writeBytes hw)

theorem writeVal_nextBlock {m m' : Mem} {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (h : writeVal m b off ty v = some m') : m'.nextBlock = m.nextBlock := by
  obtain ⟨_, hm⟩ := writeVal_writeBytes h
  exact writeBytes_nextBlock hm

theorem writeVal_blocks_ne {m m' : Mem} {b b' : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (h : writeVal m b off ty v = some m') (hne : b' ≠ b) :
    m'.blocks b' = m.blocks b' := by
  obtain ⟨_, hm⟩ := writeVal_writeBytes h
  exact writeBytes_blocks_ne hm hne

theorem writeVal_blocks_eq {m m' : Mem} {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    {blk : Block} (hb : m.blocks b = some blk) (h : writeVal m b off ty v = some m') :
    ∃ bs, m.writeBytes b off bs = some m' ∧
      m'.blocks b = some { blk with bytes := (fun i =>
        if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + bs.length then bs[i - off.toInt.toNat]?.getD .undef
        else blk.bytes i) } := by
  obtain ⟨bs, hm⟩ := writeVal_writeBytes h
  exact ⟨bs, hm, writeBytes_blocks_eq hb hm⟩

@[simp] theorem pushCallParams_zero (tags : TypeEnv) (m : Mem) (base : Nat → UInt64)
    (idx : Nat) (env : Env) (blks : List BlockId) :
    pushCallParams tags m base idx [] env blks = some (env, blks, m) := rfl

theorem pushCallParams_cons {tags : TypeEnv} {m m2 : Mem} {base : Nat → UInt64}
    {idx : Nat} {p : Param} {v : Val} {rest : List (Param × Val)}
    {env : Env} {blks : List BlockId}
    (hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags p.ty))
    (hba : (base idx).toNat % max 1 (alignofTy tags p.ty) = 0)
    (hwr : writeVal
      (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack (base idx) (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 p.ty.stripConst v = some m2) :
    pushCallParams tags m base idx ((p, v) :: rest) env blks =
      pushCallParams tags m2 base (idx + 1) rest ((p.name, m.nextBlock, p.ty) :: env) (m.nextBlock :: blks) := by
  conv => lhs; unfold pushCallParams
  simp [hsz, hal, hba, hwr, Option.bind]

theorem pushCallParams_cons_inv {tags : TypeEnv} {m m' : Mem} {base : Nat → UInt64}
    {idx : Nat} {p : Param} {v : Val} {rest : List (Param × Val)}
    {env callEnv : Env} {blks callBlks : List BlockId}
    (h : pushCallParams tags m base idx ((p, v) :: rest) env blks = some (callEnv, callBlks, m')) :
    ∃ (hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit)
      (hal : 0 < max 1 (alignofTy tags p.ty))
      (hba : (base idx).toNat % max 1 (alignofTy tags p.ty) = 0)
      (m2 : Mem),
      writeVal
        (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
          .rw .stack (base idx) (fun _ => .undef) hsz hal hba).2
        m.nextBlock 0 p.ty.stripConst v = some m2 ∧
      pushCallParams tags m2 base (idx + 1) rest
        ((p.name, m.nextBlock, p.ty) :: env) (m.nextBlock :: blks) = some (callEnv, callBlks, m') := by
  conv at h => lhs; unfold pushCallParams
  dsimp only at h
  split at h
  · split at h
    · split at h
      · rw [alloc_fst] at h
        cases hw : writeVal
          (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
            .rw .stack (base idx) (fun _ => .undef) ‹_› ‹_› ‹_›).2
          m.nextBlock 0 p.ty.stripConst v with
        | none => rw [hw] at h; cases h
        | some m2 =>
          rw [hw] at h
          exact ⟨‹_›, ‹_›, ‹_›, m2, hw, h⟩
      · cases h
    · cases h
  · cases h

theorem pushCallParams_localFrameMem {tags : TypeEnv} {m0 m m' : Mem} {base : Nat → UInt64}
    {idx : Nat} {pvs : List (Param × Val)} {env callEnv : Env} {blks callBlks : List BlockId}
    (hf : LocalFrameMem m0 m blks)
    (h : pushCallParams tags m base idx pvs env blks = some (callEnv, callBlks, m')) :
    LocalFrameMem m0 m' callBlks := by
  induction pvs generalizing m idx env blks with
  | nil =>
    simp only [pushCallParams_zero, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, rfl⟩
    exact hf
  | cons pv rest ih =>
    rcases pv with ⟨p, v⟩
    obtain ⟨hsz, hal, hba, m2, hwr, hrest⟩ := pushCallParams_cons_inv h
    let allocRes := m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
      .rw .stack (base idx) (fun _ => .undef) hsz hal hba
    have hfa : LocalFrameMem m0 allocRes.2 (m.nextBlock :: blks) :=
      hf.alloc_stack rfl
    obtain ⟨bs, hbs⟩ := writeVal_writeBytes hwr
    have hblk : allocRes.2.blocks m.nextBlock = some ⟨max 1 (sizeofTy tags p.ty),
        max 1 (alignofTy tags p.ty), .rw, .stack, base idx, (fun _ => .undef), hsz, hal, hba⟩ :=
      alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
    have hfw : LocalFrameMem m0 m2 (m.nextBlock :: blks) :=
      hfa.write_stack (.head _) hblk hbs
    exact ih hfw hrest

theorem pushCallParams_one {tags : TypeEnv} {m0 m m2 : Mem} {base : Nat → UInt64}
    {idx : Nat} {p : Param} {v : Val} {env : Env} {blks : List BlockId}
    (hf : LocalFrameMem m0 m blks)
    (hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags p.ty))
    (hba : (base idx).toNat % max 1 (alignofTy tags p.ty) = 0)
    (hwr : writeVal
      (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack (base idx) (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 p.ty.stripConst v = some m2) :
    pushCallParams tags m base idx [(p, v)] env blks =
      some ((p.name, m.nextBlock, p.ty) :: env, m.nextBlock :: blks, m2) ∧
    LocalFrameMem m0 m2 (m.nextBlock :: blks) := by
  have heq : pushCallParams tags m base idx [(p, v)] env blks =
      some ((p.name, m.nextBlock, p.ty) :: env, m.nextBlock :: blks, m2) := by
    rw [pushCallParams_cons hsz hal hba hwr, pushCallParams_zero]
  exact ⟨heq, pushCallParams_localFrameMem hf heq⟩

@[simp] theorem coerceCallArgs_nil (m : Mem) :
    coerceCallArgs m [] false [] = some [] := by
  simp [coerceCallArgs, pure, Pure.pure]

theorem coerceCallArgs_cons_nonvariadic {m : Mem} {pty : CTy} {ptys : List CTy}
    {v : Val} {vty : CTy} {rest : List (Val × CTy)} {cv : Val} {crest : List Val}
    (hc : castVal m pty v = some cv)
    (hrest : coerceCallArgs m ptys false rest = some crest) :
    coerceCallArgs m (pty :: ptys) false ((v, vty) :: rest) = some (cv :: crest) := by
  simp only [coerceCallArgs, Bool.false_eq_true, ↓reduceIte, List.length_cons,
    bind, Option.bind] at hrest ⊢
  rcases Option.bind_eq_some_iff.mp hrest with ⟨_, hlen, hmap⟩
  have hlen' : rest.length = ptys.length := by
    rw [guard_eq_some] at hlen
    exact beq_iff_eq.mp hlen
  simp only [beq_iff_eq, hlen', List.zip_cons_cons, List.mapM_cons, hc,
    bind, Option.bind, pure, Pure.pure, guard_true]
  have hmap' : (ptys.zip rest).mapM (fun (p, (x, _)) => castVal m p x) = some crest := by
    simpa [hlen'] using hmap
  simp [hmap']

/-! ## Scalar Parameter Writability Helpers -/

theorem writeVal_fresh_int {tags : TypeEnv} {m : Mem} {ty : CTy} {k : IntKind}
    {ba : UInt64} {v : Val} {iv : Int}
    (hk : ty.unqual = .int k)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : ba.toNat % max 1 (alignofTy tags ty) = 0)
    (hvi : valAsInt? v = some (k, iv)) :
    ∃ m', writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 ty.stripConst v = some m' := by
  have hsz_eq : sizeofTy tags ty = k.bytes := by
    rw [← sizeofTy_unqual, hk]; simp
  have hal_eq : alignofTy tags ty = k.align := by
    rw [← alignofTy_unqual, hk]; simp
  have hszk : k.bytes ≤ max 1 (sizeofTy tags ty) := by
    rw [hsz_eq]; exact Nat.le_max_right _ _
  have halk : k.align = max 1 (alignofTy tags ty) := by
    rw [hal_eq]; cases k <;> rfl
  have hblk : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock =
      some ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, ba,
        (fun _ => .undef), hsz, hal, hba⟩ := alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  refine writeVal_int_some (stripConst_isConst ty) (by rw [stripConst_unqual, hk]) hblk rfl ?_ ?_ hvi
  · rw [isAligned_iff]
    refine ⟨Int.le_refl _, by cases k <;> decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero, halk]
    exact hba
  · rw [inBounds_iff]
    refine ⟨Int.le_refl _, ?_⟩
    simpa [Int64.toInt_zero] using hszk

theorem writeVal_fresh_ptr {tags : TypeEnv} {m : Mem} {ty el : CTy}
    {ba : UInt64} {v : Val}
    (hptr : ty.unqual = .ptr el)
    (hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy tags ty))
    (hba : ba.toNat % max 1 (alignofTy tags ty) = 0)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff) :
    ∃ m', writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 ty.stripConst v = some m' := by
  have hsz_eq : sizeofTy tags ty = 8 := by rw [← sizeofTy_unqual, hptr]; simp
  have hal_eq : alignofTy tags ty = 8 := by rw [← alignofTy_unqual, hptr]; simp
  have hblk : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock =
      some ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, ba,
        (fun _ => .undef), hsz, hal, hba⟩ := alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  refine writeVal_ptr_some (stripConst_isConst ty) (by rw [stripConst_unqual, hptr]) hblk rfl ?_ ?_ hv
  · rw [isAligned_iff]
    refine ⟨Int.le_refl _, by decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
    simpa [hal_eq] using hba
  · rw [inBounds_iff]
    refine ⟨Int.le_refl _, ?_⟩
    simp [Int64.toInt_zero, hsz_eq]

/-! ## Context Bisimulation (`whileCond` vs `forCond`) -/

private inductive ContCtxRel (c1 c2 : ExprCtx) : Cont → Cont → Prop where
  | refl (k : Cont) : ContCtxRel c1 c2 k k
  | stmts {ss : List CStmt} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 → ContCtxRel c1 c2 (.stmts ss k1) (.stmts ss k2)
  | blockEnd {env : Env} {blks : List BlockId} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 → ContCtxRel c1 c2 (.blockEnd env blks k1) (.blockEnd env blks k2)
  | loop {cond? step? : Option CExpr} {body : CStmt} {isDo : Bool} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 →
      ContCtxRel c1 c2 (.loop cond? step? body isDo k1) (.loop cond? step? body isDo k2)
  | switchCont {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 → ContCtxRel c1 c2 (.switchCont k1) (.switchCont k2)
  | callFrame_swap {re : Env} {rb : List BlockId} {rt : CTy} {fnBody : CStmt}
      {fs : List ExprFrame} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 →
      ContCtxRel c1 c2 (.callFrame re rb rt fnBody fs c1 k1) (.callFrame re rb rt fnBody fs c2 k2)
  | callFrame_same {re : Env} {rb : List BlockId} {rt : CTy} {fnBody : CStmt}
      {fs : List ExprFrame} {ctx : ExprCtx} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 →
      ContCtxRel c1 c2 (.callFrame re rb rt fnBody fs ctx k1) (.callFrame re rb rt fnBody fs ctx k2)

private inductive StateCtxRel (c1 c2 : ExprCtx) : RunState → RunState → Prop where
  | returned (v : Val) (m : Mem) (os : OSState) :
      StateCtxRel c1 c2 (.returned v m os) (.returned v m os)
  | ub : StateCtxRel c1 c2 .ub .ub
  | stmt {s : CStmt} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 →
      StateCtxRel c1 c2 (.running (.stmt s) env blks m os k1) (.running (.stmt s) env blks m os k2)
  | expr_swap {es : ExprState} {mods : ModSet} {env : Env} {blks : List BlockId}
      {m : Mem} {os : OSState} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 →
      StateCtxRel c1 c2
        (.running (.expr es c1 mods) env blks m os k1)
        (.running (.expr es c2 mods) env blks m os k2)
  | expr_same {es : ExprState} {ctx : ExprCtx} {mods : ModSet} {env : Env} {blks : List BlockId}
      {m : Mem} {os : OSState} {k1 k2 : Cont} :
      ContCtxRel c1 c2 k1 k2 →
      StateCtxRel c1 c2
        (.running (.expr es ctx mods) env blks m os k1)
        (.running (.expr es ctx mods) env blks m os k2)

private theorem ContCtxRel.topRetTy_eq {c1 c2 : ExprCtx} {k1 k2 : Cont}
    (hk : ContCtxRel c1 c2 k1 k2) : k1.topRetTy = k2.topRetTy := by
  induction hk with
  | refl => rfl
  | stmts _ ih | blockEnd _ ih | loop _ ih | switchCont _ ih => exact ih
  | callFrame_swap _ | callFrame_same _ => rfl

private theorem ContCtxRel.unwindBreak_rel {c1 c2 : ExprCtx} {m : Mem} {env : Env}
    {blks : List BlockId} {k1 k2 : Cont} (hk : ContCtxRel c1 c2 k1 k2) :
    (unwindBreak m env blks k1 = none ∧ unwindBreak m env blks k2 = none) ∨
    (∃ e' b' m' k1' k2',
      unwindBreak m env blks k1 = some (e', b', m', k1') ∧
      unwindBreak m env blks k2 = some (e', b', m', k2') ∧
      ContCtxRel c1 c2 k1' k2') := by
  induction hk generalizing m env blks with
  | refl k =>
    cases h : unwindBreak m env blks k with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some r => exact Or.inr ⟨r.1, r.2.1, r.2.2.1, r.2.2.2, r.2.2.2, rfl, rfl, .refl _⟩
  | stmts _ ih => exact ih
  | blockEnd _ ih => exact ih
  | loop hk' => exact Or.inr ⟨env, blks, m, _, _, rfl, rfl, hk'⟩
  | switchCont hk' => exact Or.inr ⟨env, blks, m, _, _, rfl, rfl, hk'⟩
  | callFrame_swap _ | callFrame_same _ => exact Or.inl ⟨rfl, rfl⟩

private theorem ContCtxRel.unwindContinue_rel {c1 c2 : ExprCtx} {m : Mem} {env : Env}
    {blks : List BlockId} {k1 k2 : Cont} (hk : ContCtxRel c1 c2 k1 k2) :
    (unwindContinue m env blks k1 = none ∧ unwindContinue m env blks k2 = none) ∨
    (∃ co st b d e' bl' m' k1' k2',
      unwindContinue m env blks k1 = some (co, st, b, d, e', bl', m', k1') ∧
      unwindContinue m env blks k2 = some (co, st, b, d, e', bl', m', k2') ∧
      ContCtxRel c1 c2 k1' k2') := by
  induction hk generalizing m env blks with
  | refl k =>
    cases h : unwindContinue m env blks k with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some r =>
      exact Or.inr ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1,
        r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2, r.2.2.2.2.2.2.2, rfl, rfl, .refl _⟩
  | stmts _ ih | blockEnd _ ih | switchCont _ ih => exact ih
  | loop hk' => exact Or.inr ⟨_, _, _, _, env, blks, m, _, _, rfl, rfl, hk'⟩
  | callFrame_swap _ | callFrame_same _ => exact Or.inl ⟨rfl, rfl⟩

private theorem ContCtxRel.unwindReturn_rel {c1 c2 : ExprCtx} {m : Mem} {blks : List BlockId}
    {k1 k2 : Cont} (hk : ContCtxRel c1 c2 k1 k2) :
    (unwindReturn m blks k1 = none ∧ unwindReturn m blks k2 = none) ∨
    (∃ re rb rt m' fs ctx1 ctx2 k1' k2',
      unwindReturn m blks k1 = some (re, rb, rt, m', fs, ctx1, k1') ∧
      unwindReturn m blks k2 = some (re, rb, rt, m', fs, ctx2, k2') ∧
      (ctx1 = ctx2 ∨ (ctx1 = c1 ∧ ctx2 = c2)) ∧
      ContCtxRel c1 c2 k1' k2') := by
  induction hk generalizing m blks with
  | refl k =>
    cases h : unwindReturn m blks k with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some r =>
      exact Or.inr ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1,
        r.2.2.2.2.2.1, r.2.2.2.2.2.2, r.2.2.2.2.2.2, rfl, rfl, Or.inl rfl, .refl _⟩
  | stmts _ ih | blockEnd _ ih | loop _ ih | switchCont _ ih => exact ih
  | callFrame_swap hk' =>
    exact Or.inr ⟨_, _, _, m.freeStack blks, _, c1, c2, _, _, rfl, rfl, Or.inr ⟨rfl, rfl⟩, hk'⟩
  | callFrame_same hk' =>
    exact Or.inr ⟨_, _, _, m.freeStack blks, _, _, _, _, _, rfl, rfl, Or.inl rfl, hk'⟩

mutual
private theorem findInStmts_ctxRel (c1 c2 : ExprCtx) (lbl : String)
    (env : Env) (blks : List BlockId) {k1 k2 : Cont} (hk : ContCtxRel c1 c2 k1 k2) :
    ∀ ss : List CStmt,
      (findInStmts lbl env blks k1 ss = none ∧ findInStmts lbl env blks k2 ss = none) ∨
      (∃ s' e' b' k1' k2',
        findInStmts lbl env blks k1 ss = some (s', e', b', k1') ∧
        findInStmts lbl env blks k2 ss = some (s', e', b', k2') ∧
        ContCtxRel c1 c2 k1' k2')
  | [] => Or.inl ⟨rfl, rfl⟩
  | hd :: tl => by
    have hk' : ContCtxRel c1 c2 (if tl.isEmpty then k1 else .stmts tl k1)
        (if tl.isEmpty then k2 else .stmts tl k2) := by
      cases tl
      · exact hk
      · exact .stmts hk
    have h1 : findInStmts lbl env blks k1 (hd :: tl) =
        match findInStmt lbl env blks hd (if tl.isEmpty then k1 else .stmts tl k1) with
        | some res => some res | none => findInStmts lbl env blks k1 tl := rfl
    have h2 : findInStmts lbl env blks k2 (hd :: tl) =
        match findInStmt lbl env blks hd (if tl.isEmpty then k2 else .stmts tl k2) with
        | some res => some res | none => findInStmts lbl env blks k2 tl := rfl
    rcases findInStmt_ctxRel c1 c2 lbl env blks hd hk' with
      ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hs1, hs2, hkr⟩
    · rcases findInStmts_ctxRel c1 c2 lbl env blks hk tl with
        ⟨tn1, tn2⟩ | ⟨s', e', b', k1', k2', ts1, ts2, tkr⟩
      · exact Or.inl ⟨by rw [h1, hn1, tn1], by rw [h2, hn2, tn2]⟩
      · exact Or.inr ⟨s', e', b', k1', k2', by rw [h1, hn1, ts1], by rw [h2, hn2, ts2], tkr⟩
    · exact Or.inr ⟨s', e', b', k1', k2', by rw [h1, hs1], by rw [h2, hs2], hkr⟩

private theorem findInStmt_ctxRel (c1 c2 : ExprCtx) (lbl : String)
    (env : Env) (blks : List BlockId) :
    ∀ (s : CStmt) {k1 k2 : Cont}, ContCtxRel c1 c2 k1 k2 →
      (findInStmt lbl env blks s k1 = none ∧ findInStmt lbl env blks s k2 = none) ∨
      (∃ s' e' b' k1' k2',
        findInStmt lbl env blks s k1 = some (s', e', b', k1') ∧
        findInStmt lbl env blks s k2 = some (s', e', b', k2') ∧
        ContCtxRel c1 c2 k1' k2')
  | .labelStmt l body, k1, k2, hk => by
    have h1 : findInStmt lbl env blks (.labelStmt l body) k1 =
        if l == lbl then some (body, env, blks, k1) else findInStmt lbl env blks body k1 := rfl
    have h2 : findInStmt lbl env blks (.labelStmt l body) k2 =
        if l == lbl then some (body, env, blks, k2) else findInStmt lbl env blks body k2 := rfl
    by_cases hl : l == lbl
    · exact Or.inr ⟨body, env, blks, k1, k2, by simp [h1, hl], by simp [h2, hl], hk⟩
    · simpa [h1, h2, hl] using findInStmt_ctxRel c1 c2 lbl env blks body hk
  | .block ss, k1, k2, hk =>
    findInStmts_ctxRel c1 c2 lbl env [] (.blockEnd hk) ss
  | .ifStmt c t f?, k1, k2, hk => by
    have hif_none : ∀ (k : Cont), findInStmt lbl env blks (.ifStmt c t none) k =
        match findInStmt lbl env blks t k with | some res => some res | none => none := by
      intro k
      delta findInStmt
      dsimp only [CStmt.brecOn, CStmt.brecOn.go]
      rfl
    have hif_some : ∀ (f : CStmt) (k : Cont), findInStmt lbl env blks (.ifStmt c t (some f)) k =
        match findInStmt lbl env blks t k with
        | some res => some res | none => findInStmt lbl env blks f k := by
      intro f k
      delta findInStmt
      dsimp only [CStmt.brecOn, CStmt.brecOn.go]
      rfl
    rcases findInStmt_ctxRel c1 c2 lbl env blks t hk with
      ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hs1, hs2, hkr⟩
    · cases f? with
      | none =>
        exact Or.inl ⟨by rw [hif_none, hn1], by rw [hif_none, hn2]⟩
      | some f =>
        rcases findInStmt_ctxRel c1 c2 lbl env blks f hk with
          ⟨fn1, fn2⟩ | ⟨s', e', b', k1', k2', fs1, fs2, fkr⟩
        · exact Or.inl ⟨by rw [hif_some, hn1, fn1], by rw [hif_some, hn2, fn2]⟩
        · exact Or.inr ⟨s', e', b', k1', k2', by rw [hif_some, hn1, fs1], by rw [hif_some, hn2, fs2], fkr⟩
    · cases f? with
      | none =>
        exact Or.inr ⟨s', e', b', k1', k2', by rw [hif_none, hs1], by rw [hif_none, hs2], hkr⟩
      | some f =>
        exact Or.inr ⟨s', e', b', k1', k2', by rw [hif_some, hs1], by rw [hif_some, hs2], hkr⟩
  | .whileStmt c body, k1, k2, hk =>
    findInStmt_ctxRel c1 c2 lbl env blks body (.loop hk)
  | .doWhileStmt body c, k1, k2, hk =>
    findInStmt_ctxRel c1 c2 lbl env blks body (.loop hk)
  | .forStmt _ c? stp? body, k1, k2, hk =>
    findInStmt_ctxRel c1 c2 lbl env blks body (.loop hk)
  | .switchStmt _ body, k1, k2, hk =>
    findInStmt_ctxRel c1 c2 lbl env blks body (.switchCont hk)
  | .caseStmt _ body, k1, k2, hk =>
    findInStmt_ctxRel c1 c2 lbl env blks body hk
  | .defaultStmt body, k1, k2, hk =>
    findInStmt_ctxRel c1 c2 lbl env blks body hk
  | .nop, _, _, _ | .expr _, _, _, _ | .decl _, _, _, _ | .decls _, _, _, _
  | .breakStmt, _, _, _ | .continueStmt, _, _, _ | .returnStmt _, _, _, _
  | .gotoStmt _, _, _, _ => Or.inl ⟨rfl, rfl⟩
end

private theorem ContCtxRel.gotoInCont_rel {c1 c2 : ExprCtx} (lbl : String)
    {m : Mem} {env : Env} {blks : List BlockId} {k1 k2 : Cont} (hk : ContCtxRel c1 c2 k1 k2) :
    (gotoInCont lbl m env blks k1 = none ∧ gotoInCont lbl m env blks k2 = none) ∨
    (∃ s' e' b' m' k1' k2',
      gotoInCont lbl m env blks k1 = some (s', e', b', m', k1') ∧
      gotoInCont lbl m env blks k2 = some (s', e', b', m', k2') ∧
      ContCtxRel c1 c2 k1' k2') := by
  induction hk generalizing m env blks with
  | refl k =>
    cases h : gotoInCont lbl m env blks k with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some r => exact Or.inr ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2, r.2.2.2.2, rfl, rfl, .refl _⟩
  | stmts hk' ih =>
    rename_i ss k1' k2'
    rcases findInStmts_ctxRel c1 c2 lbl env blks hk' ss with
      ⟨hn1, hn2⟩ | ⟨s', e', b', kr1, kr2, hs1, hs2, hkr⟩
    · rcases ih with ⟨gn1, gn2⟩ | ⟨s', e', b', m', kr1, kr2, gs1, gs2, gkr⟩
      · exact Or.inl ⟨by unfold gotoInCont; rw [hn1]; exact gn1, by unfold gotoInCont; rw [hn2]; exact gn2⟩
      · exact Or.inr ⟨s', e', b', m', kr1, kr2,
          by unfold gotoInCont; rw [hn1]; exact gs1, by unfold gotoInCont; rw [hn2]; exact gs2, gkr⟩
    · exact Or.inr ⟨s', e', b', m, kr1, kr2,
        by unfold gotoInCont; rw [hs1], by unfold gotoInCont; rw [hs2], hkr⟩
  | blockEnd _ ih => exact ih
  | loop hk' ih =>
    rename_i cond? step? body isDo k1' k2'
    rcases findInStmt_ctxRel c1 c2 lbl env blks body (.loop hk') with
      ⟨hn1, hn2⟩ | ⟨s', e', b', kr1, kr2, hs1, hs2, hkr⟩
    · rcases ih with ⟨gn1, gn2⟩ | ⟨s', e', b', m', kr1, kr2, gs1, gs2, gkr⟩
      · exact Or.inl ⟨by unfold gotoInCont; rw [hn1]; exact gn1, by unfold gotoInCont; rw [hn2]; exact gn2⟩
      · exact Or.inr ⟨s', e', b', m', kr1, kr2,
          by unfold gotoInCont; rw [hn1]; exact gs1, by unfold gotoInCont; rw [hn2]; exact gs2, gkr⟩
    · exact Or.inr ⟨s', e', b', m, kr1, kr2,
        by unfold gotoInCont; rw [hs1], by unfold gotoInCont; rw [hs2], hkr⟩
  | switchCont _ ih => exact ih
  | @callFrame_swap _ _ _ fnBody _ _ _ hk' _ =>
    rcases findInStmt_ctxRel c1 c2 lbl env blks fnBody (.callFrame_swap hk') with
      ⟨hn1, hn2⟩ | ⟨s', e', b', kr1, kr2, hs1, hs2, hkr⟩
    · exact Or.inl ⟨by unfold gotoInCont; rw [hn1], by unfold gotoInCont; rw [hn2]⟩
    · exact Or.inr ⟨s', e', b', m, kr1, kr2,
        by unfold gotoInCont; rw [hs1], by unfold gotoInCont; rw [hs2], hkr⟩
  | @callFrame_same _ _ _ fnBody _ _ _ _ hk' _ =>
    rcases findInStmt_ctxRel c1 c2 lbl env blks fnBody (.callFrame_same hk') with
      ⟨hn1, hn2⟩ | ⟨s', e', b', kr1, kr2, hs1, hs2, hkr⟩
    · exact Or.inl ⟨by unfold gotoInCont; rw [hn1], by unfold gotoInCont; rw [hn2]⟩
    · exact Or.inr ⟨s', e', b', m, kr1, kr2,
        by unfold gotoInCont; rw [hs1], by unfold gotoInCont; rw [hs2], hkr⟩

private theorem stateCtxRel_isUB {c1 c2 : ExprCtx} {s1 s2 : RunState}
    (h : StateCtxRel c1 c2 s1 s2) : s1.isUB = s2.isUB := by
  cases h <;> rfl

private theorem stepDet_forCond_whileCond_ret {prog : Prog} {cfg : PointerConfig}
    {c : CExpr} {body : CStmt} {rv : ExprRes} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k1 k2 : Cont}
    (hk : ContCtxRel (.forCond c none body) (.whileCond c body) k1 k2) :
    (stepDet prog cfg (.running (.expr (.ret rv []) (.forCond c none body) mods) env blks m os k1) = none ∧
     stepDet prog cfg (.running (.expr (.ret rv []) (.whileCond c body) mods) env blks m os k2) = none) ∨
    (∃ s1' s2',
      stepDet prog cfg (.running (.expr (.ret rv []) (.forCond c none body) mods) env blks m os k1) = some (.next s1') ∧
      stepDet prog cfg (.running (.expr (.ret rv []) (.whileCond c body) mods) env blks m os k2) = some (.next s2') ∧
      StateCtxRel (.forCond c none body) (.whileCond c body) s1' s2') := by
  cases rv with
  | lval _ _ _ | structVal _ _ =>
    exact Or.inl ⟨rfl, rfl⟩
  | rval v _ =>
    cases htr : isTruthy v with
    | none => exact Or.inl ⟨by unfold stepDet; simp [htr], by unfold stepDet; simp [htr]⟩
    | some b =>
      cases b with
      | false =>
        refine Or.inr ⟨.running (.stmt .nop) env blks m os k1, .running (.stmt .nop) env blks m os k2, ?_, ?_, .stmt hk⟩
        · unfold stepDet; simp [htr]
        · unfold stepDet; simp [htr]
      | true =>
        refine Or.inr ⟨.running (.stmt body) env blks m os (.loop (some c) none body false k1),
          .running (.stmt body) env blks m os (.loop (some c) none body false k2), ?_, ?_, .stmt (.loop hk)⟩
        · unfold stepDet; simp [htr]
        · unfold stepDet; simp [htr]

private theorem stepDet_ctx_ret_same {c1 c2 : ExprCtx} {prog : Prog} {cfg : PointerConfig}
    {rv : ExprRes} {ctx : ExprCtx} {mods : ModSet} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k1 k2 : Cont} (hk : ContCtxRel c1 c2 k1 k2) :
    (stepDet prog cfg (.running (.expr (.ret rv []) ctx mods) env blks m os k1) = none ∧
     stepDet prog cfg (.running (.expr (.ret rv []) ctx mods) env blks m os k2) = none) ∨
    (∃ s1' s2',
      stepDet prog cfg (.running (.expr (.ret rv []) ctx mods) env blks m os k1) = some (.next s1') ∧
      stepDet prog cfg (.running (.expr (.ret rv []) ctx mods) env blks m os k2) = some (.next s2') ∧
      StateCtxRel c1 c2 s1' s2') ∨
    (∃ d init? rest env' blks' m' os' kr1 kr2,
      stepDet prog cfg (.running (.expr (.ret rv []) ctx mods) env blks m os k1) =
        some (.allocLocal d init? rest env' blks' m' os' kr1) ∧
      stepDet prog cfg (.running (.expr (.ret rv []) ctx mods) env blks m os k2) =
        some (.allocLocal d init? rest env' blks' m' os' kr2) ∧
      ContCtxRel c1 c2 kr1 kr2) := by
  cases ctx with
  | discard =>
    cases rv with
    | lval _ _ _ | structVal _ _ =>
      exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
        .running (.stmt .nop) env blks m os k2, rfl, rfl, .stmt hk⟩
    | rval v _ =>
      cases v <;>
        exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
          .running (.stmt .nop) env blks m os k2, rfl, rfl, .stmt hk⟩
  | returnVal =>
    cases rv with
    | lval _ _ _ | structVal _ _ => exact Or.inl ⟨rfl, rfl⟩
    | rval v _ =>
      have hrt := hk.topRetTy_eq
      by_cases hv : k1.topRetTy.isVoid
      · have hv2 : k2.topRetTy.isVoid := by rw [← hrt]; exact hv
        rcases hk.unwindReturn_rel (m := m) (blks := blks) with
          ⟨hn1, hn2⟩ | ⟨re, rb, rt, m', fs, ctx1, ctx2, kr1, kr2, hu1, hu2, hctx, hkr⟩
        · refine Or.inr <| Or.inl ⟨.returned .void (m.freeStack blks) os,
            .returned .void (m.freeStack blks) os, ?_, ?_, .returned _ _ _⟩
          · unfold stepDet; simp [hv, hn1]
          · unfold stepDet; simp [hv2, hn2]
        · rcases hctx with rfl | ⟨hc1, hc2⟩
          · refine Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval .void .void) fs) ctx1 []) re rb m' os kr1,
              .running (.expr (.ret (.rval .void .void) fs) ctx1 []) re rb m' os kr2, ?_, ?_, .expr_same hkr⟩
            · unfold stepDet; simp [hv, hu1]
            · unfold stepDet; simp [hv2, hu2]
          · have hu1' : unwindReturn m blks k1 = some (re, rb, rt, m', fs, c1, kr1) := hc1 ▸ hu1
            have hu2' : unwindReturn m blks k2 = some (re, rb, rt, m', fs, c2, kr2) := hc2 ▸ hu2
            refine Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval .void .void) fs) c1 []) re rb m' os kr1,
              .running (.expr (.ret (.rval .void .void) fs) c2 []) re rb m' os kr2, ?_, ?_, .expr_swap hkr⟩
            · unfold stepDet; simp [hv, hu1']
            · unfold stepDet; simp [hv2, hu2']
      · have hv2 : ¬ k2.topRetTy.isVoid := by rw [← hrt]; exact hv
        rw [hrt] at hv
        cases hcast : castVal m k2.topRetTy v with
        | none =>
          exact Or.inl ⟨by unfold stepDet; simp [hrt, hv, hcast], by unfold stepDet; simp [hv2, hcast]⟩
        | some cv =>
          rcases hk.unwindReturn_rel (m := m) (blks := blks) with
            ⟨hn1, hn2⟩ | ⟨re, rb, rt, m', fs, ctx1, ctx2, kr1, kr2, hu1, hu2, hctx, hkr⟩
          · refine Or.inr <| Or.inl ⟨.returned cv (m.freeStack blks) os,
              .returned cv (m.freeStack blks) os, ?_, ?_, .returned _ _ _⟩
            · unfold stepDet; simp [hrt, hv, hcast, hn1]
            · unfold stepDet; simp [hv2, hcast, hn2]
          · rcases hctx with rfl | ⟨hc1, hc2⟩
            · refine Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval cv k1.topRetTy) fs) ctx1 []) re rb m' os kr1,
                .running (.expr (.ret (.rval cv k2.topRetTy) fs) ctx1 []) re rb m' os kr2,
                ?_, ?_, by rw [hrt]; exact .expr_same hkr⟩
              · unfold stepDet; simp [hrt, hv, hcast, hu1]
              · unfold stepDet; simp [hv2, hcast, hu2]
            · have hu1' : unwindReturn m blks k1 = some (re, rb, rt, m', fs, c1, kr1) := hc1 ▸ hu1
              have hu2' : unwindReturn m blks k2 = some (re, rb, rt, m', fs, c2, kr2) := hc2 ▸ hu2
              refine Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval cv k1.topRetTy) fs) c1 []) re rb m' os kr1,
                .running (.expr (.ret (.rval cv k2.topRetTy) fs) c2 []) re rb m' os kr2,
                ?_, ?_, by rw [hrt]; exact .expr_swap hkr⟩
              · unfold stepDet; simp [hrt, hv, hcast, hu1']
              · unfold stepDet; simp [hv2, hcast, hu2']
  | varInit d rest =>
    cases rv with
    | lval _ _ _ | structVal _ _ =>
      exact Or.inr <| Or.inr ⟨d, some _, rest, env, blks, m, os, k1, k2, rfl, rfl, hk⟩
    | rval v _ =>
      cases v <;>
        exact Or.inr <| Or.inr ⟨d, some _, rest, env, blks, m, os, k1, k2, rfl, rfl, hk⟩
  | branch t f =>
    cases rv with
    | lval _ _ _ | structVal _ _ => exact Or.inl ⟨rfl, rfl⟩
    | rval v _ =>
      cases htr : isTruthy v with
      | none => exact Or.inl ⟨by unfold stepDet; simp [htr], by unfold stepDet; simp [htr]⟩
      | some b =>
        refine Or.inr <| Or.inl ⟨.running (.stmt (if b then t else f)) env blks m os k1,
          .running (.stmt (if b then t else f)) env blks m os k2, ?_, ?_, .stmt hk⟩
        · unfold stepDet; simp [htr]
        · unfold stepDet; simp [htr]
  | whileCond c body =>
    cases rv with
    | lval _ _ _ | structVal _ _ => exact Or.inl ⟨rfl, rfl⟩
    | rval v _ =>
      cases htr : isTruthy v with
      | none => exact Or.inl ⟨by unfold stepDet; simp [htr], by unfold stepDet; simp [htr]⟩
      | some b =>
        cases b with
        | false =>
          refine Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
            .running (.stmt .nop) env blks m os k2, ?_, ?_, .stmt hk⟩
          · unfold stepDet; simp [htr]
          · unfold stepDet; simp [htr]
        | true =>
          refine Or.inr <| Or.inl ⟨.running (.stmt body) env blks m os (.loop (some c) none body false k1),
            .running (.stmt body) env blks m os (.loop (some c) none body false k2), ?_, ?_, .stmt (.loop hk)⟩
          · unfold stepDet; simp [htr]
          · unfold stepDet; simp [htr]
  | doWhileCond body c =>
    cases rv with
    | lval _ _ _ | structVal _ _ => exact Or.inl ⟨rfl, rfl⟩
    | rval v _ =>
      cases htr : isTruthy v with
      | none => exact Or.inl ⟨by unfold stepDet; simp [htr], by unfold stepDet; simp [htr]⟩
      | some b =>
        cases b with
        | false =>
          refine Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
            .running (.stmt .nop) env blks m os k2, ?_, ?_, .stmt hk⟩
          · unfold stepDet; simp [htr]
          · unfold stepDet; simp [htr]
        | true =>
          refine Or.inr <| Or.inl ⟨.running (.stmt body) env blks m os (.loop (some c) none body true k1),
            .running (.stmt body) env blks m os (.loop (some c) none body true k2), ?_, ?_, .stmt (.loop hk)⟩
          · unfold stepDet; simp [htr]
          · unfold stepDet; simp [htr]
  | forCond c stp? body =>
    cases rv with
    | lval _ _ _ | structVal _ _ => exact Or.inl ⟨rfl, rfl⟩
    | rval v _ =>
      cases htr : isTruthy v with
      | none => exact Or.inl ⟨by unfold stepDet; simp [htr], by unfold stepDet; simp [htr]⟩
      | some b =>
        cases b with
        | false =>
          refine Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
            .running (.stmt .nop) env blks m os k2, ?_, ?_, .stmt hk⟩
          · unfold stepDet; simp [htr]
          · unfold stepDet; simp [htr]
        | true =>
          refine Or.inr <| Or.inl ⟨.running (.stmt body) env blks m os (.loop (some c) stp? body false k1),
            .running (.stmt body) env blks m os (.loop (some c) stp? body false k2), ?_, ?_, .stmt (.loop hk)⟩
          · unfold stepDet; simp [htr]
          · unfold stepDet; simp [htr]
  | forStep c? stp? body =>
    cases c? with
    | none =>
      cases rv with
      | lval _ _ _ | structVal _ _ =>
        exact Or.inr <| Or.inl ⟨.running (.stmt body) env blks m os (.loop none stp? body false k1),
          .running (.stmt body) env blks m os (.loop none stp? body false k2), rfl, rfl, .stmt (.loop hk)⟩
      | rval v _ =>
        cases v <;>
          exact Or.inr <| Or.inl ⟨.running (.stmt body) env blks m os (.loop none stp? body false k1),
            .running (.stmt body) env blks m os (.loop none stp? body false k2), rfl, rfl, .stmt (.loop hk)⟩
    | some c =>
      cases rv with
      | lval _ _ _ | structVal _ _ =>
        exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k1,
          .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
      | rval v _ =>
        cases v <;>
          exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k1,
            .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
  | switchScrut body =>
    cases rv with
    | lval _ _ _ | structVal _ _ => exact Or.inl ⟨rfl, rfl⟩
    | rval v _ =>
      cases hvi : valAsInt? v with
      | none => exact Or.inl ⟨by unfold stepDet; simp [hvi], by unfold stepDet; simp [hvi]⟩
      | some p =>
        cases hsw : findSwitchTarget p.2 body with
        | none =>
          refine Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
            .running (.stmt .nop) env blks m os k2, ?_, ?_, .stmt hk⟩
          · unfold stepDet; simp [hvi, hsw]
          · unfold stepDet; simp [hvi, hsw]
        | some tgt =>
          refine Or.inr <| Or.inl ⟨.running (.stmt tgt) env blks m os (.switchCont k1),
            .running (.stmt tgt) env blks m os (.switchCont k2), ?_, ?_, .stmt (.switchCont hk)⟩
          · unfold stepDet; simp [hvi, hsw]
          · unfold stepDet; simp [hvi, hsw]

private theorem stepDet_ctx_expr_sim {c : CExpr} {body : CStmt} {prog : Prog} {cfg : PointerConfig}
    {es : ExprState} {ctx1 ctx2 : ExprCtx} {mods : ModSet} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k1 k2 : Cont}
    (hctx : ctx1 = ctx2 ∨ (ctx1 = .forCond c none body ∧ ctx2 = .whileCond c body))
    (hk : ContCtxRel (.forCond c none body) (.whileCond c body) k1 k2) :
    (stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) = none ∧
     stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) = none) ∨
    (∃ s1' s2',
      stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) = some (.next s1') ∧
      stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) = some (.next s2') ∧
      StateCtxRel (.forCond c none body) (.whileCond c body) s1' s2') ∨
    (∃ str fs cx1 cx2 mods' env' blks' m' os' kr1 kr2,
      stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) =
        some (.allocStr str fs cx1 mods' env' blks' m' os' kr1) ∧
      stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) =
        some (.allocStr str fs cx2 mods' env' blks' m' os' kr2) ∧
      (cx1 = cx2 ∨ (cx1 = .forCond c none body ∧ cx2 = .whileCond c body)) ∧
      ContCtxRel (.forCond c none body) (.whileCond c body) kr1 kr2) ∨
    (∃ d init? rest env' blks' m' os' kr1 kr2,
      stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) =
        some (.allocLocal d init? rest env' blks' m' os' kr1) ∧
      stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) =
        some (.allocLocal d init? rest env' blks' m' os' kr2) ∧
      ContCtxRel (.forCond c none body) (.whileCond c body) kr1 kr2) ∨
    (∃ sym fnTy argVals fs cx1 cx2 env' blks' m' os' kr1 kr2,
      stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) =
        some (.callFn sym fnTy argVals fs cx1 env' blks' m' os' kr1) ∧
      stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) =
        some (.callFn sym fnTy argVals fs cx2 env' blks' m' os' kr2) ∧
      (cx1 = cx2 ∨ (cx1 = .forCond c none body ∧ cx2 = .whileCond c body)) ∧
      ContCtxRel (.forCond c none body) (.whileCond c body) kr1 kr2) := by
  have stepFromMap :
      stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) =
        (stepExprPure prog cfg env m mods es).map
          (fun (es', m', mods') => .next (.running (.expr es' ctx1 mods') env blks m' os k1)) →
      stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) =
        (stepExprPure prog cfg env m mods es).map
          (fun (es', m', mods') => .next (.running (.expr es' ctx2 mods') env blks m' os k2)) →
      (stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) = none ∧
       stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) = none) ∨
      (∃ s1' s2',
        stepDet prog cfg (.running (.expr es ctx1 mods) env blks m os k1) = some (.next s1') ∧
        stepDet prog cfg (.running (.expr es ctx2 mods) env blks m os k2) = some (.next s2') ∧
        StateCtxRel (.forCond c none body) (.whileCond c body) s1' s2') := by
    intro heq1 heq2
    cases hsp : stepExprPure prog cfg env m mods es with
    | none => exact Or.inl ⟨by simp [heq1, hsp], by simp [heq2, hsp]⟩
    | some p =>
      rcases p with ⟨es', m', mods'⟩
      refine Or.inr ⟨.running (.expr es' ctx1 mods') env blks m' os k1,
        .running (.expr es' ctx2 mods') env blks m' os k2,
        by simp [heq1, hsp], by simp [heq2, hsp], ?_⟩
      rcases hctx with rfl | ⟨rfl, rfl⟩
      · exact .expr_same hk
      · exact .expr_swap hk
  cases es with
  | eval w e fs =>
    cases w with
    | lval =>
      rcases stepFromMap (stepDet_eval_lval _ _ _ _ _ _ _ _ _ _ _)
          (stepDet_eval_lval _ _ _ _ _ _ _ _ _ _ _) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    | rval =>
      cases e with
      | strLit s =>
        exact Or.inr <| Or.inr <| Or.inl
          ⟨s, fs, ctx1, ctx2, mods, env, blks, m, os, k1, k2, rfl, rfl, hctx, hk⟩
      | _ =>
        rcases stepFromMap
            (stepDet_eval_rval_other _ _ _ (fun _ hc => by cases hc) _ _ _ _ _ _ _ _)
            (stepDet_eval_rval_other _ _ _ (fun _ hc => by cases hc) _ _ _ _ _ _ _ _) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  | ret rv fs =>
    cases fs with
    | nil =>
      rcases hctx with rfl | ⟨rfl, rfl⟩
      · rcases stepDet_ctx_ret_same hk (prog := prog) (cfg := cfg) (rv := rv) (ctx := ctx1)
            (mods := mods) (env := env) (blks := blks) (m := m) (os := os) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases stepDet_forCond_whileCond_ret hk (prog := prog) (cfg := cfg) (rv := rv)
            (mods := mods) (env := env) (blks := blks) (m := m) (os := os) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    | cons f rest =>
      by_cases hfn : ∃ sym fnTy, f = .callFnF [] ∧ rv = .rval (.fnPtr sym) fnTy
      · rcases hfn with ⟨sym, fnTy, rfl, rfl⟩
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr
          ⟨sym, fnTy, [], rest, ctx1, ctx2, env, blks, m, os, k1, k2, rfl, rfl, hctx, hk⟩
      · by_cases harg : ∃ sym fnTy done v ty, f = .callArgF sym fnTy done [] ∧ rv = .rval v ty
        · rcases harg with ⟨sym, fnTy, done, v, ty, rfl, rfl⟩
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr
            ⟨sym, fnTy, done ++ [(v, ty)], rest, ctx1, ctx2, env, blks, m, os, k1, k2, ?_, ?_, hctx, hk⟩
          · cases v <;> rfl
          · cases v <;> rfl
        · rcases stepFromMap
              (stepDet_ret_cons_other _ _ rv f rest
                (fun sym fnTy hc => hfn ⟨sym, fnTy, hc⟩)
                (fun sym fnTy done v ty hc => harg ⟨sym, fnTy, done, v, ty, hc⟩) _ _ _ _ _ _ _)
              (stepDet_ret_cons_other _ _ rv f rest
                (fun sym fnTy hc => hfn ⟨sym, fnTy, hc⟩)
                (fun sym fnTy done v ty hc => harg ⟨sym, fnTy, done, v, ty, hc⟩) _ _ _ _ _ _ _) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)

private theorem stepDet_ctx_sim {c : CExpr} {body : CStmt} {prog : Prog} {cfg : PointerConfig}
    {s1 s2 : RunState} (hrel : StateCtxRel (.forCond c none body) (.whileCond c body) s1 s2) :
    (stepDet prog cfg s1 = none ∧ stepDet prog cfg s2 = none) ∨
    (∃ s1' s2', stepDet prog cfg s1 = some (.next s1') ∧ stepDet prog cfg s2 = some (.next s2') ∧
      StateCtxRel (.forCond c none body) (.whileCond c body) s1' s2') ∨
    (∃ str fs ctx1 ctx2 mods env blks m os k1 k2,
      stepDet prog cfg s1 = some (.allocStr str fs ctx1 mods env blks m os k1) ∧
      stepDet prog cfg s2 = some (.allocStr str fs ctx2 mods env blks m os k2) ∧
      (ctx1 = ctx2 ∨ (ctx1 = .forCond c none body ∧ ctx2 = .whileCond c body)) ∧
      ContCtxRel (.forCond c none body) (.whileCond c body) k1 k2) ∨
    (∃ d init? rest env blks m os k1 k2,
      stepDet prog cfg s1 = some (.allocLocal d init? rest env blks m os k1) ∧
      stepDet prog cfg s2 = some (.allocLocal d init? rest env blks m os k2) ∧
      ContCtxRel (.forCond c none body) (.whileCond c body) k1 k2) ∨
    (∃ sym fnTy argVals fs ctx1 ctx2 env blks m os k1 k2,
      stepDet prog cfg s1 = some (.callFn sym fnTy argVals fs ctx1 env blks m os k1) ∧
      stepDet prog cfg s2 = some (.callFn sym fnTy argVals fs ctx2 env blks m os k2) ∧
      (ctx1 = ctx2 ∨ (ctx1 = .forCond c none body ∧ ctx2 = .whileCond c body)) ∧
      ContCtxRel (.forCond c none body) (.whileCond c body) k1 k2) := by
  cases hrel with
  | returned => exact Or.inl ⟨rfl, rfl⟩
  | ub => exact Or.inl ⟨rfl, rfl⟩
  | stmt hk =>
    rename_i s env blks m os k1 k2
    cases s with
    | nop =>
      cases hk with
      | refl =>
        cases k1 with
        | stmts ss rest =>
          cases ss with
          | nil =>
            exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os rest,
              .running (.stmt .nop) env blks m os rest, rfl, rfl, .stmt (.refl _)⟩
          | cons s' ss' =>
            exact Or.inr <| Or.inl ⟨.running (.stmt s') env blks m os (.stmts ss' rest),
              .running (.stmt s') env blks m os (.stmts ss' rest), rfl, rfl, .stmt (.refl _)⟩
        | switchCont rest =>
          exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os rest,
            .running (.stmt .nop) env blks m os rest, rfl, rfl, .stmt (.refl _)⟩
        | blockEnd se sb rest =>
          exact Or.inr <| Or.inl ⟨.running (.stmt .nop) se sb (m.freeStack blks) os rest,
            .running (.stmt .nop) se sb (m.freeStack blks) os rest, rfl, rfl, .stmt (.refl _)⟩
        | loop co st b d rest =>
          cases d <;> cases st <;> cases co <;>
            exact Or.inr <| Or.inl ⟨loopNext _ _ b _ env blks m os rest,
              loopNext _ _ b _ env blks m os rest, rfl, rfl, by
                first | exact .stmt (.refl _) | exact .expr_same (.refl _)⟩
        | stop rt =>
          exact Or.inr <| Or.inl ⟨.returned (if rt.isVoid then .void else .undef) (m.freeStack blks) os,
            .returned (if rt.isVoid then .void else .undef) (m.freeStack blks) os, rfl, rfl, .returned _ _ _⟩
        | callFrame re rb rt _ fs ctx rest =>
          exact Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) ctx []) re rb (m.freeStack blks) os rest,
            .running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) ctx []) re rb (m.freeStack blks) os rest, rfl, rfl, .expr_same (.refl _)⟩
      | stmts hk' =>
        rename_i ss k1' k2'
        cases ss with
        | nil =>
          exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1',
            .running (.stmt .nop) env blks m os k2', rfl, rfl, .stmt hk'⟩
        | cons s' ss' =>
          exact Or.inr <| Or.inl ⟨.running (.stmt s') env blks m os (.stmts ss' k1'),
            .running (.stmt s') env blks m os (.stmts ss' k2'), rfl, rfl, .stmt (.stmts hk')⟩
      | switchCont hk' =>
        exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os _,
          .running (.stmt .nop) env blks m os _, rfl, rfl, .stmt hk'⟩
      | blockEnd hk' =>
        exact Or.inr <| Or.inl ⟨.running (.stmt .nop) _ _ (m.freeStack blks) os _,
          .running (.stmt .nop) _ _ (m.freeStack blks) os _, rfl, rfl, .stmt hk'⟩
      | loop hk' =>
        rename_i co st b d _ _
        cases d <;> cases st <;> cases co <;>
          exact Or.inr <| Or.inl ⟨loopNext _ _ b _ env blks m os _,
            loopNext _ _ b _ env blks m os _, rfl, rfl, by
              first | exact .stmt (.loop hk') | exact .expr_same hk'⟩
      | callFrame_swap hk' =>
        rename_i re rb rt _ fs _ _
        exact Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) (.forCond c none body) []) re rb (m.freeStack blks) os _,
          .running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) (.whileCond c body) []) re rb (m.freeStack blks) os _, rfl, rfl, .expr_swap hk'⟩
      | callFrame_same hk' =>
        rename_i re rb rt _ fs ctx _ _
        exact Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) ctx []) re rb (m.freeStack blks) os _,
          .running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) ctx []) re rb (m.freeStack blks) os _, rfl, rfl, .expr_same hk'⟩
    | expr e =>
      exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval e []) .discard []) env blks m os k1,
        .running (.expr (.eval .rval e []) .discard []) env blks m os k2, rfl, rfl, .expr_same hk⟩
    | decl d =>
      exact Or.inr <| Or.inl ⟨.running (.stmt (.decls [d])) env blks m os k1,
        .running (.stmt (.decls [d])) env blks m os k2, rfl, rfl, .stmt hk⟩
    | decls ds =>
      cases ds with
      | nil =>
        exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
          .running (.stmt .nop) env blks m os k2, rfl, rfl, .stmt hk⟩
      | cons d rest =>
        cases hs : d.isStatic with
        | true =>
          refine Or.inr <| Or.inl ⟨.running (.stmt (.decls rest)) env blks m os k1,
            .running (.stmt (.decls rest)) env blks m os k2, ?_, ?_, .stmt hk⟩
          · unfold stepDet; simp [hs]
          · unfold stepDet; simp [hs]
        | false =>
          cases hi : d.init? with
          | none =>
            exact Or.inr <| Or.inr <| Or.inr <| Or.inl
              ⟨d, none, rest, env, blks, m, os, k1, k2,
                by unfold stepDet; simp [hs, hi], by unfold stepDet; simp [hs, hi], hk⟩
          | some iv =>
            cases iv with
            | expr e =>
              refine Or.inr <| Or.inl ⟨.running (.expr (.eval .rval e []) (.varInit d rest) []) env blks m os k1,
                .running (.expr (.eval .rval e []) (.varInit d rest) []) env blks m os k2, ?_, ?_, .expr_same hk⟩
              · unfold stepDet; simp [hs, hi]
              · unfold stepDet; simp [hs, hi]
            | _ => exact Or.inl ⟨by unfold stepDet; simp [hs, hi], by unfold stepDet; simp [hs, hi]⟩
    | block ss =>
      cases ss with
      | nil =>
        exact Or.inr <| Or.inl ⟨.running (.stmt .nop) env blks m os k1,
          .running (.stmt .nop) env blks m os k2, rfl, rfl, .stmt hk⟩
      | cons hd tl =>
        cases tl with
        | nil =>
          exact Or.inr <| Or.inl ⟨.running (.stmt hd) env [] m os (.blockEnd env blks k1),
            .running (.stmt hd) env [] m os (.blockEnd env blks k2), rfl, rfl, .stmt (.blockEnd hk)⟩
        | cons t ts =>
          exact Or.inr <| Or.inl ⟨.running (.stmt hd) env [] m os (.stmts (t :: ts) (.blockEnd env blks k1)),
            .running (.stmt hd) env [] m os (.stmts (t :: ts) (.blockEnd env blks k2)), rfl, rfl, .stmt (.stmts (.blockEnd hk))⟩
    | ifStmt c' t f? =>
      exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval c' []) (.branch t (f?.getD .nop)) []) env blks m os k1,
        .running (.expr (.eval .rval c' []) (.branch t (f?.getD .nop)) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
    | whileStmt c' b =>
      exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval c' []) (.whileCond c' b) []) env blks m os k1,
        .running (.expr (.eval .rval c' []) (.whileCond c' b) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
    | doWhileStmt b c' =>
      exact Or.inr <| Or.inl ⟨.running (.stmt b) env blks m os (.loop (some c') none b true k1),
        .running (.stmt b) env blks m os (.loop (some c') none b true k2), rfl, rfl, .stmt (.loop hk)⟩
    | switchStmt sc b =>
      exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval sc []) (.switchScrut b) []) env blks m os k1,
        .running (.expr (.eval .rval sc []) (.switchScrut b) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
    | caseStmt _ b | defaultStmt b | labelStmt _ b =>
      exact Or.inr <| Or.inl ⟨.running (.stmt b) env blks m os k1,
        .running (.stmt b) env blks m os k2, rfl, rfl, .stmt hk⟩
    | forStmt init? c? stp? b =>
      cases init? with
      | some init =>
        exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval init []) (.forStep c? stp? b) []) env blks m os k1,
          .running (.expr (.eval .rval init []) (.forStep c? stp? b) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
      | none =>
        cases c? with
        | some c' =>
          exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval c' []) (.forCond c' stp? b) []) env blks m os k1,
            .running (.expr (.eval .rval c' []) (.forCond c' stp? b) []) env blks m os k2, rfl, rfl, .expr_same hk⟩
        | none =>
          exact Or.inr <| Or.inl ⟨.running (.stmt b) env blks m os (.loop none stp? b false k1),
            .running (.stmt b) env blks m os (.loop none stp? b false k2), rfl, rfl, .stmt (.loop hk)⟩
    | breakStmt =>
      rcases hk.unwindBreak_rel (m := m) (env := env) (blks := blks) with
        ⟨hn1, hn2⟩ | ⟨e', b', m', k1', k2', hu1, hu2, hkr⟩
      · exact Or.inl ⟨by unfold stepDet; simp [hn1], by unfold stepDet; simp [hn2]⟩
      · refine Or.inr <| Or.inl ⟨.running (.stmt .nop) e' b' m' os k1',
          .running (.stmt .nop) e' b' m' os k2', ?_, ?_, .stmt hkr⟩
        · unfold stepDet; simp [hu1]
        · unfold stepDet; simp [hu2]
    | continueStmt =>
      rcases hk.unwindContinue_rel (m := m) (env := env) (blks := blks) with
        ⟨hn1, hn2⟩ | ⟨co, st, b, d, e', bl', m', k1', k2', hu1, hu2, hkr⟩
      · exact Or.inl ⟨by unfold stepDet; simp [hn1], by unfold stepDet; simp [hn2]⟩
      · let s1' := loopNext co st b d e' bl' m' os k1'
        let s2' := loopNext co st b d e' bl' m' os k2'
        cases d <;> cases st <;> cases co <;>
          refine Or.inr <| Or.inl ⟨s1', s2', by unfold stepDet; simp [hu1, s1'], by unfold stepDet; simp [hu2, s2'], ?_⟩ <;>
          dsimp only [s1', s2', loopNext] <;>
          first | exact .stmt (.loop hkr) | exact .expr_same hkr
    | gotoStmt lbl =>
      rcases hk.gotoInCont_rel lbl (m := m) (env := env) (blks := blks) with
        ⟨hn1, hn2⟩ | ⟨s', e', b', m', k1', k2', hg1, hg2, hkr⟩
      · exact Or.inl ⟨by unfold stepDet; simp [hn1], by unfold stepDet; simp [hn2]⟩
      · refine Or.inr <| Or.inl ⟨.running (.stmt s') e' b' m' os k1',
          .running (.stmt s') e' b' m' os k2', ?_, ?_, .stmt hkr⟩
        · unfold stepDet; simp [hg1]
        · unfold stepDet; simp [hg2]
    | returnStmt val? =>
      cases val? with
      | some e =>
        exact Or.inr <| Or.inl ⟨.running (.expr (.eval .rval e []) .returnVal []) env blks m os k1,
          .running (.expr (.eval .rval e []) .returnVal []) env blks m os k2, rfl, rfl, .expr_same hk⟩
      | none =>
        have hrt := hk.topRetTy_eq
        by_cases hv : k1.topRetTy.isVoid
        · have hv2 : k2.topRetTy.isVoid := by rw [← hrt]; exact hv
          rcases hk.unwindReturn_rel (m := m) (blks := blks) with
            ⟨hn1, hn2⟩ | ⟨re, rb, rt, m', fs, ctx1, ctx2, kr1, kr2, hu1, hu2, hctx, hkr⟩
          · refine Or.inr <| Or.inl ⟨.returned .void (m.freeStack blks) os,
              .returned .void (m.freeStack blks) os, ?_, ?_, .returned _ _ _⟩
            · unfold stepDet; simp [hv, hn1]
            · unfold stepDet; simp [hv2, hn2]
          · rcases hctx with rfl | ⟨hc1, hc2⟩
            · refine Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval .void .void) fs) ctx1 []) re rb m' os kr1,
                .running (.expr (.ret (.rval .void .void) fs) ctx1 []) re rb m' os kr2, ?_, ?_, .expr_same hkr⟩
              · unfold stepDet; simp [hv, hu1]
              · unfold stepDet; simp [hv2, hu2]
            · have hu1' : unwindReturn m blks k1 = some (re, rb, rt, m', fs, .forCond c none body, kr1) := hc1 ▸ hu1
              have hu2' : unwindReturn m blks k2 = some (re, rb, rt, m', fs, .whileCond c body, kr2) := hc2 ▸ hu2
              refine Or.inr <| Or.inl ⟨.running (.expr (.ret (.rval .void .void) fs) (.forCond c none body) []) re rb m' os kr1,
                .running (.expr (.ret (.rval .void .void) fs) (.whileCond c body) []) re rb m' os kr2, ?_, ?_, .expr_swap hkr⟩
              · unfold stepDet; simp [hv, hu1']
              · unfold stepDet; simp [hv2, hu2']
        · have hv2 : ¬ k2.topRetTy.isVoid := by rw [← hrt]; exact hv
          exact Or.inl ⟨by unfold stepDet; simp [hv], by unfold stepDet; simp [hv2]⟩
  | expr_swap hk =>
    exact stepDet_ctx_expr_sim (Or.inr ⟨rfl, rfl⟩) hk
  | expr_same hk =>
    exact stepDet_ctx_expr_sim (Or.inl rfl) hk

private theorem step_ctx_fwd {c : CExpr} {body : CStmt} {prog : Prog} {cfg : PointerConfig}
    {ext : ExtHandler} {s1 s2 s1' : RunState}
    (hrel : StateCtxRel (.forCond c none body) (.whileCond c body) s1 s2)
    (hstep : Step prog cfg ext s1 s1') :
    ∃ s2', Step prog cfg ext s2 s2' := by
  have hsim := stepDet_ctx_sim (c := c) (body := body) (prog := prog) (cfg := cfg) hrel
  cases hstep with
  | det hd =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, s2', hs1, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨s2', .det hs2⟩
  | det_ub hd =>
    rcases hsim with ⟨hs1, hn2⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    cases hrel with
    | stmt _ | expr_swap _ | expr_same _ => exact ⟨.ub, .det_ub hn2⟩
  | strLit hd hsz halloc =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ |
        ⟨str, fs, ctx1, ctx2, mods, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨_, .strLit hs2 hsz halloc⟩
  | localDecl hd hsz hal hba halloc hwr =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨d, init?, rest, env, blks, m, os, k1, k2, hs1, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨_, .localDecl hs2 hsz hal hba halloc hwr⟩
  | localDecl_ub hd hbad =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨d, init?, rest, env, blks, m, os, k1, k2, hs1, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨.ub, .localDecl_ub hs2 hbad⟩
  | call_internal hd hfn hcoerce hpush =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨_, .call_internal hs2 hfn hcoerce hpush⟩
  | call_internal_ub hd hfn hbad =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨.ub, .call_internal_ub hs2 hfn hbad⟩
  | call_ext hd hnfn hsig hcoerce hext =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨_, .call_ext hs2 hnfn hsig hcoerce hext⟩
  | call_ext_ub hd hnfn hbad =>
    rcases hsim with ⟨hs1, _⟩ | ⟨_, _, hs1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hs1, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ <;>
      rw [hd] at hs1 <;> cases hs1
    exact ⟨.ub, .call_ext_ub hs2 hnfn hbad⟩

private theorem step_ctx_bwd {c : CExpr} {body : CStmt} {prog : Prog} {cfg : PointerConfig}
    {ext : ExtHandler} {s1 s2 s2' : RunState}
    (hrel : StateCtxRel (.forCond c none body) (.whileCond c body) s1 s2)
    (hstep : Step prog cfg ext s2 s2') :
    ∃ s1', Step prog cfg ext s1 s1' ∧ StateCtxRel (.forCond c none body) (.whileCond c body) s1' s2' := by
  have hsim := stepDet_ctx_sim (c := c) (body := body) (prog := prog) (cfg := cfg) hrel
  cases hstep with
  | det hd =>
    rcases hsim with ⟨_, hs2⟩ | ⟨s1', _, hs1, hs2, hrel'⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    exact ⟨s1', .det hs1, hrel'⟩
  | det_ub hd =>
    rcases hsim with ⟨hn1, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    cases hrel with
    | stmt _ | expr_swap _ | expr_same _ => exact ⟨.ub, .det_ub hn1, .ub⟩
  | strLit hd hsz halloc =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ |
        ⟨str, fs, ctx1, ctx2, mods, env, blks, m, os, k1, k2, hs1, hs2, hctx, hk⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    rcases hctx with rfl | ⟨rfl, rfl⟩
    · exact ⟨_, .strLit hs1 hsz halloc, .expr_same hk⟩
    · exact ⟨_, .strLit hs1 hsz halloc, .expr_swap hk⟩
  | localDecl hd hsz hal hba halloc hwr =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨d, init?, rest, env, blks, m, os, k1, k2, hs1, hs2, hk⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    exact ⟨_, .localDecl hs1 hsz hal hba halloc hwr, .stmt hk⟩
  | localDecl_ub hd hbad =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨d, init?, rest, env, blks, m, os, k1, k2, hs1, hs2, hk⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    exact ⟨.ub, .localDecl_ub hs1 hbad, .ub⟩
  | call_internal hd hfn hcoerce hpush =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, hctx, hk⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    rcases hctx with rfl | ⟨rfl, rfl⟩
    · exact ⟨_, .call_internal hs1 hfn hcoerce hpush, .stmt (.callFrame_same hk)⟩
    · exact ⟨_, .call_internal hs1 hfn hcoerce hpush, .stmt (.callFrame_swap hk)⟩
  | call_internal_ub hd hfn hbad =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    exact ⟨.ub, .call_internal_ub hs1 hfn hbad, .ub⟩
  | call_ext hd hnfn hsig hcoerce hext =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, hctx, hk⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    rename_i out' _
    cases out' with
    | ub => exact ⟨.ub, .call_ext hs1 hnfn hsig hcoerce hext, .ub⟩
    | ok ret m' os' =>
      rcases hctx with rfl | ⟨rfl, rfl⟩
      · exact ⟨_, .call_ext hs1 hnfn hsig hcoerce hext, .expr_same hk⟩
      · exact ⟨_, .call_ext hs1 hnfn hsig hcoerce hext, .expr_swap hk⟩
  | call_ext_ub hd hnfn hbad =>
    rcases hsim with ⟨_, hs2⟩ | ⟨_, _, _, hs2, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hs2, _⟩ |
        ⟨sym, fnTy, argVals, fs, ctx1, ctx2, env, blks, m, os, k1, k2, hs1, hs2, _, _⟩ <;>
      rw [hd] at hs2 <;> cases hs2
    exact ⟨.ub, .call_ext_ub hs1 hnfn hbad, .ub⟩

private theorem wpTerm_ctx_sim {c : CExpr} {body : CStmt} {prog : Prog} {cfg : PointerConfig}
    {ext : ExtHandler} {Q : Val → Mem → OSState → Prop} {s1 s2 : RunState}
    (hw : WPTerm prog cfg ext Q s1)
    (hrel : StateCtxRel (.forCond c none body) (.whileCond c body) s1 s2) :
    WPTerm prog cfg ext Q s2 := by
  induction hw generalizing s2 with
  | returned hq =>
    cases hrel
    exact .returned hq
  | step hnot hex _ ih =>
    obtain ⟨s1', hs1'⟩ := hex
    obtain ⟨s2', hs2'⟩ := step_ctx_fwd hrel hs1'
    refine .step (by rw [← stateCtxRel_isUB hrel]; exact hnot) ⟨s2', hs2'⟩ ?_
    intro s2'' hs2''
    obtain ⟨s1'', hs1'', hrel''⟩ := step_ctx_bwd hrel hs2''
    exact ih s1'' hs1'' hrel''

theorem WPTerm.whileCond_of_forCond {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {c : CExpr} {body : CStmt}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval c []) (.forCond c none body) []) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval c []) (.whileCond c body) []) env blks m os k) :=
  wpTerm_ctx_sim hw (.expr_swap (.refl k))

/-! ## Well-Founded Loop Rules (`while`, `do-while`, `for`) -/

/-- Well-founded `Nat` induction for `while (c) body`. Both the initial test and subsequent
loop-back tests use the uniform `.forCond c none body` continuation via `whileCond_of_forCond`. -/
theorem WPTerm.while_wf {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {c : CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState} {k : Cont}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      (∀ n' env' blks' m' os', n' < n → Inv n' env' blks' m' os' →
        WPTerm prog cfg ext Q
          (.running (.expr (.eval .rval c []) (.forCond c none body) []) env' blks' m' os' k)) →
      WPTerm prog cfg ext Q
        (.running (.expr (.eval .rval c []) (.forCond c none body) []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.whileStmt c body)) env0 blks0 m0 os0 k) := by
  refine WPTerm.of_det (by rfl) (WPTerm.whileCond_of_forCond ?_)
  induction n0 using Nat.strongRecOn generalizing env0 blks0 m0 os0 with
  | ind n ih =>
    exact hstep n env0 blks0 m0 os0 hinit (fun n' env' blks' m' os' hlt hinv' => ih n' hlt hinv')

/-- Well-founded `Nat` induction for `do body while (c);`. -/
theorem WPTerm.doWhile_wf {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {body : CStmt} {c : CExpr} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState} {k : Cont}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      (∀ n' env' blks' m' os', n' < n → Inv n' env' blks' m' os' →
        WPTerm prog cfg ext Q
          (.running (.stmt body) env' blks' m' os' (.loop (some c) none body true k))) →
      WPTerm prog cfg ext Q
        (.running (.stmt body) env blks m os (.loop (some c) none body true k))) :
    WPTerm prog cfg ext Q (.running (.stmt (.doWhileStmt body c)) env0 blks0 m0 os0 k) := by
  refine WPTerm.of_det (by rfl) ?_
  induction n0 using Nat.strongRecOn generalizing env0 blks0 m0 os0 with
  | ind n ih =>
    exact hstep n env0 blks0 m0 os0 hinit (fun n' env' blks' m' os' hlt hinv' => ih n' hlt hinv')

/-- Canonical loop-entry state for a `for` loop after initialization or step. -/
def forLoopEntry (c? stp? : Option CExpr) (body : CStmt)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont) : RunState :=
  match c? with
  | some c => .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k
  | none => .running (.stmt body) env blks m os (.loop none stp? body false k)

/-- Well-founded `Nat` induction for `for (init?; c?; stp?) body` (including `for (;;)` with
`break`/`return`). -/
theorem WPTerm.for_wf {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {init? c? stp? : Option CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState} {k : Cont}
    (hinit : match init? with
      | none => Inv n0 env0 blks0 m0 os0
      | some init =>
        (∀ env1 blks1 m1 os1, Inv n0 env1 blks1 m1 os1 →
          WPTerm prog cfg ext Q (forLoopEntry c? stp? body env1 blks1 m1 os1 k)) →
        WPTerm prog cfg ext Q
          (.running (.expr (.eval .rval init []) (.forStep c? stp? body) []) env0 blks0 m0 os0 k))
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      (∀ n' env' blks' m' os', n' < n → Inv n' env' blks' m' os' →
        WPTerm prog cfg ext Q (forLoopEntry c? stp? body env' blks' m' os' k)) →
      WPTerm prog cfg ext Q (forLoopEntry c? stp? body env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.forStmt init? c? stp? body)) env0 blks0 m0 os0 k) := by
  have hloop : ∀ n env blks m os, Inv n env blks m os →
      WPTerm prog cfg ext Q (forLoopEntry c? stp? body env blks m os k) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro env blks m os hinv
      exact hstep n env blks m os hinv (fun n' env' blks' m' os' hlt hinv' => ih n' hlt env' blks' m' os' hinv')
  cases init? with
  | none =>
    cases c? with
    | none => exact WPTerm.of_det (by rfl) (hloop n0 env0 blks0 m0 os0 hinit)
    | some c => exact WPTerm.of_det (by rfl) (hloop n0 env0 blks0 m0 os0 hinit)
  | some init =>
    exact WPTerm.of_det (by rfl) (hinit (fun env1 blks1 m1 os1 hinv1 => hloop n0 env1 blks1 m1 os1 hinv1))

/-- Specialized `for` induction when `init? = none`. -/
theorem WPTerm.for_none_wf {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {c? stp? : Option CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState} {k : Cont}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      (∀ n' env' blks' m' os', n' < n → Inv n' env' blks' m' os' →
        WPTerm prog cfg ext Q (forLoopEntry c? stp? body env' blks' m' os' k)) →
      WPTerm prog cfg ext Q (forLoopEntry c? stp? body env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.forStmt none c? stp? body)) env0 blks0 m0 os0 k) :=
  WPTerm.for_wf Inv hinit hstep

/-! ## Deterministic Stepping Tactics (`wp_det`, `wp_steps`) -/

/-- Advance one deterministic `stepDet` transition when `stepDet` reduces definitionally to `some (.next _)`. -/
macro "wp_det" : tactic =>
  `(tactic| refine WPTerm.of_det rfl ?_)

/-- Repeatedly advance deterministic `stepDet` transitions as long as `stepDet` reduces cleanly. -/
macro "wp_steps" : tactic =>
  `(tactic| repeat wp_det)

/-- Advance one deterministic `stepDet` transition using explicit simplification lemmas `lemmas`
(e.g. environment lookups, memory reads/writes, `castVal`). -/
macro "wp_det_using" "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine WPTerm.of_det ?_ ?_; · unfold stepDet; unfold stepExprPure; simp only [$lemmas,*]; rfl))

end C99.Proof
