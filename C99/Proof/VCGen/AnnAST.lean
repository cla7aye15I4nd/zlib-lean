import C99.Proof.VCGen.State

/-!
# Annotated AST for Functional VCGen (`C99.Proof.VCGen.AnnAST`)

Mirrors `C99.CStmt` with optional loop invariants/measures (`whileLoop`,
`doWhileLoop`) and linear control-flow join annotations (`ifJoin`), plus a
zero-overhead structural wrapper `ofCStmt` for loop-free blocks (`DO16`, `switch`,
straight-line code). 100% zlib-agnostic.
-/

namespace C99.Proof.VCGen

open C99

inductive AnnStmt where
  | nop
  | expr (e : CExpr)
  | decl (d : VarDecl)
  | decls (ds : List VarDecl)
  | stackDecl (d : VarDecl)
  | stackDecls (ds : List VarDecl)
  | mixedDecls (ds : List (VarDecl × Bool))
  | block (ss : List AnnStmt)
  | ifStmt (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt)
  | ifJoin (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) (J : SymState → Prop)
  | whileLoop (c : CExpr) (body : AnnStmt) (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat)
  | doWhileLoop (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat)
  | doWhileGotos (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop)
      (gotoSpecs : List (String × (SymState → Nat → SymState → Prop))) (meas : SymState → Nat)
  | forLoop (init? c? stp? : Option CExpr) (body : AnnStmt)
      (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat)
  | switchStmt (scrut : CExpr) (body : AnnStmt)
  | caseStmt (val : Int) (body : AnnStmt)
  | defaultStmt (body : AnnStmt)
  | labelStmt (lbl : String) (body : AnnStmt)
  | gotoStmt (lbl : String)
  | breakStmt
  | continueStmt
  | returnStmt (val? : Option CExpr)

namespace AnnStmt

mutual
def erase : AnnStmt → CStmt
  | .nop => .nop
  | .expr e => .expr e
  | .decl d => .decl d
  | .decls ds => .decls ds
  | .stackDecl d => .decl d
  | .stackDecls ds => .decls ds
  | .mixedDecls ds => .decls (ds.map Prod.fst)
  | .block ss => .block (eraseList ss)
  | .ifStmt c t f? => .ifStmt c (erase t) (match f? with | none => none | some f => some (erase f))
  | .ifJoin c t f? _ => .ifStmt c (erase t) (match f? with | none => none | some f => some (erase f))
  | .whileLoop c body _ _ => .whileStmt c (erase body)
  | .doWhileLoop body c _ _ => .doWhileStmt (erase body) c
  | .doWhileGotos body c _ _ _ => .doWhileStmt (erase body) c
  | .forLoop init? c? stp? body _ _ => .forStmt init? c? stp? (erase body)
  | .switchStmt scrut body => .switchStmt scrut (erase body)
  | .caseStmt v body => .caseStmt v (erase body)
  | .defaultStmt body => .defaultStmt (erase body)
  | .labelStmt lbl body => .labelStmt lbl (erase body)
  | .gotoStmt lbl => .gotoStmt lbl
  | .breakStmt => .breakStmt
  | .continueStmt => .continueStmt
  | .returnStmt val? => .returnStmt val?

def eraseList : List AnnStmt → List CStmt
  | [] => []
  | s :: ss => erase s :: eraseList ss
end

mutual
def ofCStmtWithStack (stkNames : List String) : CStmt → AnnStmt
  | .nop => .nop
  | .expr e => .expr e
  | .decl d => if stkNames.contains d.name then .stackDecl d else .decl d
  | .decls ds =>
    if ds.any (fun d => stkNames.contains d.name) then
      .mixedDecls (ds.map fun d => (d, stkNames.contains d.name))
    else .decls ds
  | .block ss => .block (ofCStmtListWithStack stkNames ss)
  | .ifStmt c t f? =>
    .ifStmt c (ofCStmtWithStack stkNames t)
      (match f? with | none => none | some f => some (ofCStmtWithStack stkNames f))
  | .switchStmt scrut body => .switchStmt scrut (ofCStmtWithStack stkNames body)
  | .caseStmt v body => .caseStmt v (ofCStmtWithStack stkNames body)
  | .defaultStmt body => .defaultStmt (ofCStmtWithStack stkNames body)
  | .labelStmt lbl body => .labelStmt lbl (ofCStmtWithStack stkNames body)
  | .gotoStmt lbl => .gotoStmt lbl
  | .breakStmt => .breakStmt
  | .continueStmt => .continueStmt
  | .returnStmt val? => .returnStmt val?
  | .whileStmt c body => .whileLoop c (ofCStmtWithStack stkNames body) (fun _ _ _ => False) (fun _ => 0)
  | .doWhileStmt body c => .doWhileLoop (ofCStmtWithStack stkNames body) c (fun _ _ _ => False) (fun _ => 0)
  | .forStmt init? c? stp? body =>
    .forLoop init? c? stp? (ofCStmtWithStack stkNames body) (fun _ _ _ => False) (fun _ => 0)

def ofCStmtListWithStack (stkNames : List String) : List CStmt → List AnnStmt
  | [] => []
  | s :: ss => ofCStmtWithStack stkNames s :: ofCStmtListWithStack stkNames ss
end

abbrev ofCStmt : CStmt → AnnStmt := ofCStmtWithStack []
abbrev ofCStmtList : List CStmt → List AnnStmt := ofCStmtListWithStack []

@[simp] theorem erase_nop : erase .nop = .nop := rfl
@[simp] theorem erase_expr (e : CExpr) : erase (.expr e) = .expr e := rfl
@[simp] theorem erase_decl (d : VarDecl) : erase (.decl d) = .decl d := rfl
@[simp] theorem erase_decls (ds : List VarDecl) : erase (.decls ds) = .decls ds := rfl
@[simp] theorem erase_stackDecl (d : VarDecl) : erase (.stackDecl d) = .decl d := rfl
@[simp] theorem erase_stackDecls (ds : List VarDecl) : erase (.stackDecls ds) = .decls ds := rfl
@[simp] theorem erase_mixedDecls (ds : List (VarDecl × Bool)) :
    erase (.mixedDecls ds) = .decls (ds.map Prod.fst) := rfl
@[simp] theorem erase_block (ss : List AnnStmt) : erase (.block ss) = .block (eraseList ss) := rfl
@[simp] theorem erase_ifStmt (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) :
    erase (.ifStmt c t f?) = .ifStmt c (erase t) (f?.map erase) := by
  cases f? <;> rfl
@[simp] theorem erase_ifJoin (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) (J : SymState → Prop) :
    erase (.ifJoin c t f? J) = .ifStmt c (erase t) (f?.map erase) := by
  cases f? <;> rfl
@[simp] theorem erase_whileLoop (c : CExpr) (body : AnnStmt) (Inv : SymState → Nat → SymState → Prop)
    (meas : SymState → Nat) :
    erase (.whileLoop c body Inv meas) = .whileStmt c (erase body) := rfl
@[simp] theorem erase_doWhileLoop (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop)
    (meas : SymState → Nat) :
    erase (.doWhileLoop body c Inv meas) = .doWhileStmt (erase body) c := rfl
@[simp] theorem erase_doWhileGotos (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop)
    (gotoSpecs : List (String × (SymState → Nat → SymState → Prop))) (meas : SymState → Nat) :
    erase (.doWhileGotos body c Inv gotoSpecs meas) = .doWhileStmt (erase body) c := rfl
@[simp] theorem erase_forLoop (init? c? stp? : Option CExpr) (body : AnnStmt)
    (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat) :
    erase (.forLoop init? c? stp? body Inv meas) = .forStmt init? c? stp? (erase body) := rfl
@[simp] theorem erase_switchStmt (scrut : CExpr) (body : AnnStmt) :
    erase (.switchStmt scrut body) = .switchStmt scrut (erase body) := rfl
@[simp] theorem erase_caseStmt (v : Int) (body : AnnStmt) :
    erase (.caseStmt v body) = .caseStmt v (erase body) := rfl
@[simp] theorem erase_defaultStmt (body : AnnStmt) :
    erase (.defaultStmt body) = .defaultStmt (erase body) := rfl
@[simp] theorem erase_labelStmt (lbl : String) (body : AnnStmt) :
    erase (.labelStmt lbl body) = .labelStmt lbl (erase body) := rfl
@[simp] theorem erase_gotoStmt (lbl : String) :
    erase (.gotoStmt lbl) = .gotoStmt lbl := rfl
@[simp] theorem erase_breakStmt : erase .breakStmt = .breakStmt := rfl
@[simp] theorem erase_continueStmt : erase .continueStmt = .continueStmt := rfl
@[simp] theorem erase_returnStmt (val? : Option CExpr) : erase (.returnStmt val?) = .returnStmt val? := rfl

@[simp] theorem eraseList_nil : eraseList [] = [] := rfl
@[simp] theorem eraseList_cons (s : AnnStmt) (ss : List AnnStmt) :
    eraseList (s :: ss) = erase s :: eraseList ss := rfl

@[simp] theorem eraseList_isEmpty (ss : List AnnStmt) :
    (eraseList ss).isEmpty = ss.isEmpty := by
  cases ss <;> rfl

mutual
def findSwitchAnnList (scrut : Int) (wantDef : Bool) : List AnnStmt → Option (List AnnStmt)
  | [] => none
  | hd :: tl => match findSwitchAnn scrut wantDef hd with
    | some found => some (found :: tl)
    | none => findSwitchAnnList scrut wantDef tl

def findSwitchAnn (scrut : Int) (wantDef : Bool) : AnnStmt → Option AnnStmt
  | .caseStmt v body =>
    if !wantDef && v == scrut then some body else findSwitchAnn scrut wantDef body
  | .defaultStmt body =>
    if wantDef then some body else findSwitchAnn scrut wantDef body
  | .labelStmt _ body =>
    findSwitchAnn scrut wantDef body
  | .block ss => (findSwitchAnnList scrut wantDef ss).map .block
  | .ifStmt _ t f? | .ifJoin _ t f? _ =>
    match findSwitchAnn scrut wantDef t with
    | some s => some s
    | none => match f? with
      | some f => findSwitchAnn scrut wantDef f
      | none => none
  | _ => none
end

def findSwitchAnnTarget (scrut : Int) (s : AnnStmt) : Option AnnStmt :=
  (findSwitchAnn scrut false s).orElse fun _ => findSwitchAnn scrut true s

private theorem findSwitchAnn_caseStmt (scrut : Int) (wantDef : Bool) (v : Int) (body : AnnStmt) :
    findSwitchAnn scrut wantDef (.caseStmt v body) =
      if !wantDef && v == scrut then some body else findSwitchAnn scrut wantDef body := rfl
private theorem findSwitchAnn_defaultStmt (scrut : Int) (wantDef : Bool) (body : AnnStmt) :
    findSwitchAnn scrut wantDef (.defaultStmt body) =
      if wantDef then some body else findSwitchAnn scrut wantDef body := rfl
private theorem findSwitchAnn_labelStmt (scrut : Int) (wantDef : Bool) (lbl : String) (body : AnnStmt) :
    findSwitchAnn scrut wantDef (.labelStmt lbl body) = findSwitchAnn scrut wantDef body := rfl
private theorem findSwitchAnn_block (scrut : Int) (wantDef : Bool) (ss : List AnnStmt) :
    findSwitchAnn scrut wantDef (.block ss) = (findSwitchAnnList scrut wantDef ss).map .block := rfl
private theorem findSwitchAnn_ifStmt (scrut : Int) (wantDef : Bool) (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) :
    findSwitchAnn scrut wantDef (.ifStmt c t f?) =
      match findSwitchAnn scrut wantDef t with
      | some s => some s
      | none => match f? with | some f => findSwitchAnn scrut wantDef f | none => none := by
  cases f? <;> · delta findSwitchAnn; dsimp only [AnnStmt.brecOn, AnnStmt.brecOn.go]
private theorem findSwitchAnn_ifJoin (scrut : Int) (wantDef : Bool) (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) (J : SymState → Prop) :
    findSwitchAnn scrut wantDef (.ifJoin c t f? J) =
      match findSwitchAnn scrut wantDef t with
      | some s => some s
      | none => match f? with | some f => findSwitchAnn scrut wantDef f | none => none := by
  cases f? <;> · delta findSwitchAnn; dsimp only [AnnStmt.brecOn, AnnStmt.brecOn.go]
private theorem findSwitchAnnList_cons (scrut : Int) (wantDef : Bool) (hd : AnnStmt) (tl : List AnnStmt) :
    findSwitchAnnList scrut wantDef (hd :: tl) =
      match findSwitchAnn scrut wantDef hd with
      | some found => some (found :: tl)
      | none => findSwitchAnnList scrut wantDef tl := rfl

private theorem sem_findSwitchStmt_caseStmt (scrut : Int) (wantDef : Bool) (v : Int) (body : CStmt) :
    Sem.findSwitchStmt scrut wantDef (.caseStmt v body) =
      if !wantDef && v == scrut then some body else Sem.findSwitchStmt scrut wantDef body := rfl
private theorem sem_findSwitchStmt_defaultStmt (scrut : Int) (wantDef : Bool) (body : CStmt) :
    Sem.findSwitchStmt scrut wantDef (.defaultStmt body) =
      if wantDef then some body else Sem.findSwitchStmt scrut wantDef body := rfl
private theorem sem_findSwitchStmt_labelStmt (scrut : Int) (wantDef : Bool) (lbl : String) (body : CStmt) :
    Sem.findSwitchStmt scrut wantDef (.labelStmt lbl body) = Sem.findSwitchStmt scrut wantDef body := rfl
private theorem sem_findSwitchStmt_block (scrut : Int) (wantDef : Bool) (ss : List CStmt) :
    Sem.findSwitchStmt scrut wantDef (.block ss) = (Sem.findSwitchList scrut wantDef ss).map .block := rfl
private theorem sem_findSwitchStmt_ifStmt (scrut : Int) (wantDef : Bool) (c : CExpr) (t : CStmt) (f? : Option CStmt) :
    Sem.findSwitchStmt scrut wantDef (.ifStmt c t f?) =
      match Sem.findSwitchStmt scrut wantDef t with
      | some s => some s
      | none => match f? with | some f => Sem.findSwitchStmt scrut wantDef f | none => none := by
  cases f? <;> · delta Sem.findSwitchStmt; dsimp only [CStmt.brecOn, CStmt.brecOn.go]; rfl
private theorem sem_findSwitchList_cons (scrut : Int) (wantDef : Bool) (hd : CStmt) (tl : List CStmt) :
    Sem.findSwitchList scrut wantDef (hd :: tl) =
      match Sem.findSwitchStmt scrut wantDef hd with
      | some found => some (found :: tl)
      | none => Sem.findSwitchList scrut wantDef tl := rfl

private theorem findSwitchAnn_erase_aux (scrut : Int) (wantDef : Bool) :
    (x : AnnStmt ⊕ List AnnStmt) →
      match x with
      | .inl s => Sem.findSwitchStmt scrut wantDef (erase s) = (findSwitchAnn scrut wantDef s).map erase
      | .inr ss => Sem.findSwitchList scrut wantDef (eraseList ss) = (findSwitchAnnList scrut wantDef ss).map eraseList
  | .inl s => by
    dsimp only
    cases s with
    | caseStmt v body =>
      rw [erase_caseStmt, sem_findSwitchStmt_caseStmt, findSwitchAnn_caseStmt]
      by_cases hc : (!wantDef && v == scrut) = true
      · simp [hc]
      · have hcf : (!wantDef && v == scrut) = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ↓reduceIte]
        exact findSwitchAnn_erase_aux scrut wantDef (.inl body)
    | defaultStmt body =>
      rw [erase_defaultStmt, sem_findSwitchStmt_defaultStmt, findSwitchAnn_defaultStmt]
      cases wantDef
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact findSwitchAnn_erase_aux scrut false (.inl body)
      · simp
    | labelStmt lbl body =>
      rw [erase_labelStmt, sem_findSwitchStmt_labelStmt, findSwitchAnn_labelStmt]
      exact findSwitchAnn_erase_aux scrut wantDef (.inl body)
    | block ss =>
      rw [erase_block, sem_findSwitchStmt_block, findSwitchAnn_block]
      rw [findSwitchAnn_erase_aux scrut wantDef (.inr ss)]
      cases findSwitchAnnList scrut wantDef ss <;> rfl
    | ifStmt c t f? =>
      rw [erase_ifStmt, sem_findSwitchStmt_ifStmt, findSwitchAnn_ifStmt]
      rw [findSwitchAnn_erase_aux scrut wantDef (.inl t)]
      cases findSwitchAnn scrut wantDef t with
      | some res => rfl
      | none =>
        cases f? with
        | none => rfl
        | some f => simpa using findSwitchAnn_erase_aux scrut wantDef (.inl f)
    | ifJoin c t f? J =>
      rw [erase_ifJoin, sem_findSwitchStmt_ifStmt, findSwitchAnn_ifJoin]
      rw [findSwitchAnn_erase_aux scrut wantDef (.inl t)]
      cases findSwitchAnn scrut wantDef t with
      | some res => rfl
      | none =>
        cases f? with
        | none => rfl
        | some f => simpa using findSwitchAnn_erase_aux scrut wantDef (.inl f)
    | nop | expr _ | decl _ | decls _ | stackDecl _ | stackDecls _ | mixedDecls _
    | whileLoop _ _ _ _ | doWhileLoop _ _ _ _ | doWhileGotos _ _ _ _ _
    | forLoop _ _ _ _ _ _ | switchStmt _ _ | gotoStmt _ | breakStmt | continueStmt | returnStmt _ =>
      rfl
  | .inr ss => by
    dsimp only
    cases ss with
    | nil => rfl
    | cons hd tl =>
      rw [eraseList_cons, sem_findSwitchList_cons, findSwitchAnnList_cons]
      rw [findSwitchAnn_erase_aux scrut wantDef (.inl hd)]
      cases findSwitchAnn scrut wantDef hd with
      | some res => rfl
      | none => exact findSwitchAnn_erase_aux scrut wantDef (.inr tl)
termination_by x => match x with | .inl s => sizeOf s | .inr ss => sizeOf ss

theorem findSwitchAnn_erase (scrut : Int) (wantDef : Bool) (s : AnnStmt) :
    Sem.findSwitchStmt scrut wantDef (erase s) = (findSwitchAnn scrut wantDef s).map erase :=
  findSwitchAnn_erase_aux scrut wantDef (.inl s)

theorem findSwitchAnnTarget_erase (scrut : Int) (s : AnnStmt) :
    Sem.findSwitchTarget scrut (erase s) = (findSwitchAnnTarget scrut s).map erase := by
  unfold Sem.findSwitchTarget findSwitchAnnTarget Option.orElse
  rw [findSwitchAnn_erase scrut false s, findSwitchAnn_erase scrut true s]
  cases findSwitchAnn scrut false s <;> rfl

private theorem findSwitchAnn_sizeOf_aux (scrut : Int) (wantDef : Bool) :
    (x : AnnStmt ⊕ List AnnStmt) →
      match x with
      | .inl s => ∀ tgt, findSwitchAnn scrut wantDef s = some tgt → sizeOf tgt < sizeOf s
      | .inr ss => ∀ tgts, findSwitchAnnList scrut wantDef ss = some tgts → sizeOf tgts < sizeOf ss
  | .inl s => by
    dsimp only
    intro tgt h
    cases s with
    | caseStmt v body =>
      rw [findSwitchAnn_caseStmt] at h
      by_cases hc : (!wantDef && v == scrut) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h; simp +arith
      · have hcf : (!wantDef && v == scrut) = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ↓reduceIte] at h
        have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl body) tgt h
        simp only [caseStmt.sizeOf_spec]
        omega
    | defaultStmt body =>
      rw [findSwitchAnn_defaultStmt] at h
      cases wantDef
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hlt := findSwitchAnn_sizeOf_aux scrut false (.inl body) tgt h
        simp only [defaultStmt.sizeOf_spec]
        omega
      · simp only [↓reduceIte, Option.some.injEq] at h
        subst h; simp +arith
    | labelStmt lbl body =>
      rw [findSwitchAnn_labelStmt] at h
      have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl body) tgt h
      simp only [labelStmt.sizeOf_spec]
      omega
    | block ss =>
      rw [findSwitchAnn_block] at h
      cases hs : findSwitchAnnList scrut wantDef ss with
      | none => simp [hs] at h
      | some res =>
        simp only [hs, Option.map_some, Option.some.injEq] at h
        subst h
        have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inr ss) res hs
        simp +arith [hlt]
    | ifStmt c t f? =>
      rw [findSwitchAnn_ifStmt] at h
      cases ht : findSwitchAnn scrut wantDef t with
      | some res =>
        simp only [ht, Option.some.injEq] at h
        subst h
        have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl t) res ht
        simp only [ifStmt.sizeOf_spec]
        omega
      | none =>
        simp only [ht] at h
        cases f? with
        | none => cases h
        | some f =>
          have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl f) tgt h
          simp only [ifStmt.sizeOf_spec, Option.some.sizeOf_spec]
          omega
    | ifJoin c t f? J =>
      rw [findSwitchAnn_ifJoin] at h
      cases ht : findSwitchAnn scrut wantDef t with
      | some res =>
        simp only [ht, Option.some.injEq] at h
        subst h
        have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl t) res ht
        simp only [ifJoin.sizeOf_spec]
        omega
      | none =>
        simp only [ht] at h
        cases f? with
        | none => cases h
        | some f =>
          have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl f) tgt h
          simp only [ifJoin.sizeOf_spec, Option.some.sizeOf_spec]
          omega
    | nop | expr _ | decl _ | decls _ | stackDecl _ | stackDecls _ | mixedDecls _
    | whileLoop _ _ _ _ | doWhileLoop _ _ _ _ | doWhileGotos _ _ _ _ _
    | forLoop _ _ _ _ _ _ | switchStmt _ _ | gotoStmt _ | breakStmt | continueStmt | returnStmt _ => cases h
  | .inr ss => by
    dsimp only
    intro tgts h
    cases ss with
    | nil => cases h
    | cons hd tl =>
      rw [findSwitchAnnList_cons] at h
      cases h1 : findSwitchAnn scrut wantDef hd with
      | some found =>
        simp only [h1, Option.some.injEq] at h
        subst h
        have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inl hd) found h1
        simp only [List.cons.sizeOf_spec]
        omega
      | none =>
        simp only [h1] at h
        have hlt := findSwitchAnn_sizeOf_aux scrut wantDef (.inr tl) tgts h
        simp only [List.cons.sizeOf_spec]
        omega
termination_by x => match x with | .inl s => sizeOf s | .inr ss => sizeOf ss

theorem findSwitchAnnTarget_sizeOf_lt {scrut : Int} {s tgt : AnnStmt}
    (h : findSwitchAnnTarget scrut s = some tgt) :
    sizeOf tgt < sizeOf s := by
  unfold findSwitchAnnTarget Option.orElse at h
  cases hf : findSwitchAnn scrut false s with
  | some res =>
    simp only [hf, Option.some.injEq] at h
    have hlt := findSwitchAnn_sizeOf_aux scrut false (.inl s) res hf
    rwa [← h]
  | none =>
    simp only [hf] at h
    exact findSwitchAnn_sizeOf_aux scrut true (.inl s) tgt h

/-! ## Forward and Loop-Internal `goto` Resolution -/

inductive GotoFrame where
  | stmts (tl : List AnnStmt)
  | blockEnd
  | switchCont

noncomputable def framesSize : List GotoFrame → Nat
  | [] => 0
  | .stmts tl :: rest => 1 + sizeOf tl + framesSize rest
  | .blockEnd :: rest => 1 + framesSize rest
  | .switchCont :: rest => 1 + framesSize rest

@[simp] theorem framesSize_nil : framesSize [] = 0 := rfl
@[simp] theorem framesSize_stmts (tl : List AnnStmt) (rest : List GotoFrame) :
    framesSize (.stmts tl :: rest) = 1 + sizeOf tl + framesSize rest := rfl
@[simp] theorem framesSize_blockEnd (rest : List GotoFrame) :
    framesSize (.blockEnd :: rest) = 1 + framesSize rest := rfl
@[simp] theorem framesSize_switchCont (rest : List GotoFrame) :
    framesSize (.switchCont :: rest) = 1 + framesSize rest := rfl

theorem framesSize_append (f1 f2 : List GotoFrame) :
    framesSize (f1 ++ f2) = framesSize f1 + framesSize f2 := by
  induction f1 with
  | nil => simp
  | cons hd tl ih => cases hd <;> simp [ih] <;> omega

mutual
def annHasLabelList (lbl : String) : List AnnStmt → Bool
  | [] => false
  | hd :: tl => annHasLabel lbl hd || annHasLabelList lbl tl

def annHasLabel (lbl : String) : AnnStmt → Bool
  | .labelStmt l body => l == lbl || annHasLabel lbl body
  | .block ss => annHasLabelList lbl ss
  | .ifStmt _ t f? | .ifJoin _ t f? _ =>
    annHasLabel lbl t || match f? with | none => false | some f => annHasLabel lbl f
  | .whileLoop _ body _ _ | .doWhileLoop body _ _ _ | .doWhileGotos body _ _ _ _
  | .forLoop _ _ _ body _ _ | .switchStmt _ body | .caseStmt _ body | .defaultStmt body =>
    annHasLabel lbl body
  | _ => false
end

private theorem annHasLabel_labelStmt (lbl l : String) (body : AnnStmt) :
    annHasLabel lbl (.labelStmt l body) = (l == lbl || annHasLabel lbl body) := rfl
private theorem annHasLabel_block (lbl : String) (ss : List AnnStmt) :
    annHasLabel lbl (.block ss) = annHasLabelList lbl ss := rfl
private theorem annHasLabel_ifStmt (lbl : String) (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) :
    annHasLabel lbl (.ifStmt c t f?) =
      (annHasLabel lbl t || match f? with | none => false | some f => annHasLabel lbl f) := by
  cases f? <;> rfl
private theorem annHasLabel_ifJoin (lbl : String) (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) (J : SymState → Prop) :
    annHasLabel lbl (.ifJoin c t f? J) =
      (annHasLabel lbl t || match f? with | none => false | some f => annHasLabel lbl f) := by
  cases f? <;> rfl
private theorem annHasLabel_whileLoop (lbl : String) (c : CExpr) (body : AnnStmt) (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat) :
    annHasLabel lbl (.whileLoop c body Inv meas) = annHasLabel lbl body := rfl
private theorem annHasLabel_doWhileLoop (lbl : String) (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat) :
    annHasLabel lbl (.doWhileLoop body c Inv meas) = annHasLabel lbl body := rfl
private theorem annHasLabel_doWhileGotos (lbl : String) (body : AnnStmt) (c : CExpr) (Inv : SymState → Nat → SymState → Prop)
    (gotoSpecs : List (String × (SymState → Nat → SymState → Prop))) (meas : SymState → Nat) :
    annHasLabel lbl (.doWhileGotos body c Inv gotoSpecs meas) = annHasLabel lbl body := rfl
private theorem annHasLabel_forLoop (lbl : String) (i? c? s? : Option CExpr) (body : AnnStmt)
    (Inv : SymState → Nat → SymState → Prop) (meas : SymState → Nat) :
    annHasLabel lbl (.forLoop i? c? s? body Inv meas) = annHasLabel lbl body := rfl
private theorem annHasLabel_switchStmt (lbl : String) (scrut : CExpr) (body : AnnStmt) :
    annHasLabel lbl (.switchStmt scrut body) = annHasLabel lbl body := rfl
private theorem annHasLabel_caseStmt (lbl : String) (v : Int) (body : AnnStmt) :
    annHasLabel lbl (.caseStmt v body) = annHasLabel lbl body := rfl
private theorem annHasLabel_defaultStmt (lbl : String) (body : AnnStmt) :
    annHasLabel lbl (.defaultStmt body) = annHasLabel lbl body := rfl
private theorem annHasLabelList_cons (lbl : String) (hd : AnnStmt) (tl : List AnnStmt) :
    annHasLabelList lbl (hd :: tl) = (annHasLabel lbl hd || annHasLabelList lbl tl) := rfl

private theorem sem_findInStmt_labelStmt (lbl : String) (env : Env) (blks : List BlockId)
    (l : String) (body : CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.labelStmt l body) k =
      if l == lbl then some (body, env, blks, k) else Sem.findInStmt lbl env blks body k := rfl
private theorem sem_findInStmt_block (lbl : String) (env : Env) (blks : List BlockId)
    (ss : List CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.block ss) k = Sem.findInStmts lbl env [] (.blockEnd env blks k) ss := rfl
private theorem sem_findInStmt_ifStmt (lbl : String) (env : Env) (blks : List BlockId)
    (c : CExpr) (t : CStmt) (f? : Option CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.ifStmt c t f?) k =
      match Sem.findInStmt lbl env blks t k with
      | some res => some res
      | none => match f? with | some f => Sem.findInStmt lbl env blks f k | none => none := by
  cases f? <;> · delta Sem.findInStmt; dsimp only [CStmt.brecOn, CStmt.brecOn.go]; rfl
private theorem sem_findInStmt_whileStmt (lbl : String) (env : Env) (blks : List BlockId)
    (c : CExpr) (body : CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.whileStmt c body) k =
      Sem.findInStmt lbl env blks body (.loop (some c) none body false k) := rfl
private theorem sem_findInStmt_doWhileStmt (lbl : String) (env : Env) (blks : List BlockId)
    (body : CStmt) (c : CExpr) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.doWhileStmt body c) k =
      Sem.findInStmt lbl env blks body (.loop (some c) none body true k) := rfl
private theorem sem_findInStmt_forStmt (lbl : String) (env : Env) (blks : List BlockId)
    (i? c? s? : Option CExpr) (body : CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.forStmt i? c? s? body) k =
      Sem.findInStmt lbl env blks body (.loop c? s? body false k) := rfl
private theorem sem_findInStmt_switchStmt (lbl : String) (env : Env) (blks : List BlockId)
    (scrut : CExpr) (body : CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.switchStmt scrut body) k =
      Sem.findInStmt lbl env blks body (.switchCont k) := rfl
private theorem sem_findInStmt_caseStmt (lbl : String) (env : Env) (blks : List BlockId)
    (v : Int) (body : CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.caseStmt v body) k = Sem.findInStmt lbl env blks body k := rfl
private theorem sem_findInStmt_defaultStmt (lbl : String) (env : Env) (blks : List BlockId)
    (body : CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (.defaultStmt body) k = Sem.findInStmt lbl env blks body k := rfl
private theorem sem_findInStmts_cons (lbl : String) (env : Env) (blks : List BlockId) (kBlk : Sem.Cont)
    (hd : CStmt) (tl : List CStmt) :
    Sem.findInStmts lbl env blks kBlk (hd :: tl) =
      let k' := if tl.isEmpty then kBlk else .stmts tl kBlk
      match Sem.findInStmt lbl env blks hd k' with
      | some res => some res | none => Sem.findInStmts lbl env blks kBlk tl := rfl

private theorem annHasLabel_erase_none_aux (lbl : String) :
    (x : AnnStmt ⊕ List AnnStmt) →
      match x with
      | .inl s => ∀ env blks k, annHasLabel lbl s = false →
        Sem.findInStmt lbl env blks (erase s) k = none
      | .inr ss => ∀ env blks k, annHasLabelList lbl ss = false →
        Sem.findInStmts lbl env blks k (eraseList ss) = none
  | .inl s => by
    intro env blks k h
    cases s with
    | labelStmt l body =>
      rw [annHasLabel_labelStmt, Bool.or_eq_false_iff] at h
      have hne : (l == lbl) = false := h.1
      rw [erase_labelStmt, sem_findInStmt_labelStmt]
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks k h.2
    | block ss =>
      rw [annHasLabel_block] at h
      rw [erase_block, sem_findInStmt_block]
      exact annHasLabel_erase_none_aux lbl (.inr ss) env [] (.blockEnd env blks k) h
    | ifStmt c t f? =>
      rw [annHasLabel_ifStmt, Bool.or_eq_false_iff] at h
      rw [erase_ifStmt, sem_findInStmt_ifStmt, annHasLabel_erase_none_aux lbl (.inl t) env blks k h.1]
      cases f? with
      | none => rfl
      | some f => simpa using annHasLabel_erase_none_aux lbl (.inl f) env blks k h.2
    | ifJoin c t f? J =>
      rw [annHasLabel_ifJoin, Bool.or_eq_false_iff] at h
      rw [erase_ifJoin, sem_findInStmt_ifStmt, annHasLabel_erase_none_aux lbl (.inl t) env blks k h.1]
      cases f? with
      | none => rfl
      | some f => simpa using annHasLabel_erase_none_aux lbl (.inl f) env blks k h.2
    | whileLoop c body _ _ =>
      rw [annHasLabel_whileLoop] at h
      rw [erase_whileLoop, sem_findInStmt_whileStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | doWhileLoop body c _ _ =>
      rw [annHasLabel_doWhileLoop] at h
      rw [erase_doWhileLoop, sem_findInStmt_doWhileStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | doWhileGotos body c _ _ _ =>
      rw [annHasLabel_doWhileGotos] at h
      rw [erase_doWhileGotos, sem_findInStmt_doWhileStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | forLoop init? c? stp? body _ _ =>
      rw [annHasLabel_forLoop] at h
      rw [erase_forLoop, sem_findInStmt_forStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | switchStmt scrut body =>
      rw [annHasLabel_switchStmt] at h
      rw [erase_switchStmt, sem_findInStmt_switchStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | caseStmt v body =>
      rw [annHasLabel_caseStmt] at h
      rw [erase_caseStmt, sem_findInStmt_caseStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | defaultStmt body =>
      rw [annHasLabel_defaultStmt] at h
      rw [erase_defaultStmt, sem_findInStmt_defaultStmt]
      exact annHasLabel_erase_none_aux lbl (.inl body) env blks _ h
    | nop | expr _ | decl _ | decls _ | stackDecl _ | stackDecls _ | mixedDecls _
    | gotoStmt _ | breakStmt | continueStmt | returnStmt _ => rfl
  | .inr ss => by
    intro env blks k h
    cases ss with
    | nil => rfl
    | cons hd tl =>
      rw [annHasLabelList_cons, Bool.or_eq_false_iff] at h
      rw [eraseList_cons, sem_findInStmts_cons]
      dsimp only
      rw [annHasLabel_erase_none_aux lbl (.inl hd) env blks _ h.1]
      exact annHasLabel_erase_none_aux lbl (.inr tl) env blks k h.2
termination_by x => match x with | .inl s => sizeOf s | .inr ss => sizeOf ss

theorem annHasLabel_erase_none {lbl : String} {s : AnnStmt} (h : annHasLabel lbl s = false)
    (env : Env) (blks : List BlockId) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (erase s) k = none :=
  annHasLabel_erase_none_aux lbl (.inl s) env blks k h

theorem annHasLabelList_erase_none {lbl : String} {ss : List AnnStmt} (h : annHasLabelList lbl ss = false)
    (env : Env) (blks : List BlockId) (k : Sem.Cont) :
    Sem.findInStmts lbl env blks k (eraseList ss) = none :=
  annHasLabel_erase_none_aux lbl (.inr ss) env blks k h

mutual
def findGotoAnnList (lbl : String) : List AnnStmt → Option (AnnStmt × List GotoFrame)
  | [] => none
  | hd :: tl =>
    match findGotoAnn lbl hd with
    | some (tgt, fs) => some (tgt, if tl.isEmpty then fs else fs ++ [.stmts tl])
    | none => if annHasLabel lbl hd then none else findGotoAnnList lbl tl

def findGotoAnn (lbl : String) : AnnStmt → Option (AnnStmt × List GotoFrame)
  | .labelStmt l body =>
    if l == lbl then some (body, []) else findGotoAnn lbl body
  | .block ss =>
    (findGotoAnnList lbl ss).map fun (tgt, fs) => (tgt, fs ++ [.blockEnd])
  | .ifStmt _ t f? | .ifJoin _ t f? _ =>
    match findGotoAnn lbl t with
    | some res => some res
    | none =>
      if annHasLabel lbl t then none
      else match f? with
        | some f => findGotoAnn lbl f
        | none => none
  | .switchStmt _ body =>
    (findGotoAnn lbl body).map fun (tgt, fs) => (tgt, fs ++ [.switchCont])
  | .caseStmt _ body | .defaultStmt body =>
    findGotoAnn lbl body
  | _ => none
end

private theorem findGotoAnn_labelStmt (lbl l : String) (body : AnnStmt) :
    findGotoAnn lbl (.labelStmt l body) =
      if l == lbl then some (body, []) else findGotoAnn lbl body := rfl
private theorem findGotoAnn_block (lbl : String) (ss : List AnnStmt) :
    findGotoAnn lbl (.block ss) =
      (findGotoAnnList lbl ss).map fun (tgt, fs) => (tgt, fs ++ [GotoFrame.blockEnd]) := rfl
private theorem findGotoAnn_ifStmt (lbl : String) (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) :
    findGotoAnn lbl (.ifStmt c t f?) =
      match findGotoAnn lbl t with
      | some res => some res
      | none => if annHasLabel lbl t then none else match f? with | some f => findGotoAnn lbl f | none => none := by
  cases f? <;> · delta findGotoAnn; dsimp only [AnnStmt.brecOn, AnnStmt.brecOn.go]
private theorem findGotoAnn_ifJoin (lbl : String) (c : CExpr) (t : AnnStmt) (f? : Option AnnStmt) (J : SymState → Prop) :
    findGotoAnn lbl (.ifJoin c t f? J) =
      match findGotoAnn lbl t with
      | some res => some res
      | none => if annHasLabel lbl t then none else match f? with | some f => findGotoAnn lbl f | none => none := by
  cases f? <;> · delta findGotoAnn; dsimp only [AnnStmt.brecOn, AnnStmt.brecOn.go]
private theorem findGotoAnn_switchStmt (lbl : String) (scrut : CExpr) (body : AnnStmt) :
    findGotoAnn lbl (.switchStmt scrut body) =
      (findGotoAnn lbl body).map fun (tgt, fs) => (tgt, fs ++ [GotoFrame.switchCont]) := rfl
private theorem findGotoAnn_caseStmt (lbl : String) (v : Int) (body : AnnStmt) :
    findGotoAnn lbl (.caseStmt v body) = findGotoAnn lbl body := rfl
private theorem findGotoAnn_defaultStmt (lbl : String) (body : AnnStmt) :
    findGotoAnn lbl (.defaultStmt body) = findGotoAnn lbl body := rfl
private theorem findGotoAnnList_cons (lbl : String) (hd : AnnStmt) (tl : List AnnStmt) :
    findGotoAnnList lbl (hd :: tl) =
      match findGotoAnn lbl hd with
      | some (tgt, fs) => some (tgt, if tl.isEmpty then fs else fs ++ [GotoFrame.stmts tl])
      | none => if annHasLabel lbl hd then none else findGotoAnnList lbl tl := rfl

def gotoFramesCont (env : Env) (blks : List BlockId) (k : Sem.Cont) :
    List GotoFrame → List BlockId × Sem.Cont
  | [] => (blks, k)
  | GotoFrame.stmts tl :: rest =>
    let (b', k') := gotoFramesCont env blks k rest
    if tl.isEmpty then (b', k') else (b', Sem.Cont.stmts (eraseList tl) k')
  | GotoFrame.blockEnd :: rest =>
    let (b', k') := gotoFramesCont env blks k rest
    ([], Sem.Cont.blockEnd env b' k')
  | GotoFrame.switchCont :: rest =>
    let (b', k') := gotoFramesCont env blks k rest
    (b', Sem.Cont.switchCont k')

theorem gotoFramesCont_append (env : Env) (blks : List BlockId) (k : Sem.Cont)
    (f1 f2 : List GotoFrame) :
    gotoFramesCont env blks k (f1 ++ f2) =
      let (b2, k2) := gotoFramesCont env blks k f2
      gotoFramesCont env b2 k2 f1 := by
  induction f1 with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | stmts tl' => simp only [List.cons_append, gotoFramesCont, ih]
    | blockEnd => simp only [List.cons_append, gotoFramesCont, ih]
    | switchCont => simp only [List.cons_append, gotoFramesCont, ih]

private theorem findGotoAnn_erase_aux (lbl : String) :
    (x : AnnStmt ⊕ List AnnStmt) →
      match x with
      | .inl s => ∀ tgt fs env blks k, findGotoAnn lbl s = some (tgt, fs) →
        Sem.findInStmt lbl env blks (erase s) k =
          some (erase tgt, env, (gotoFramesCont env blks k fs).1, (gotoFramesCont env blks k fs).2)
      | .inr ss => ∀ tgt fs env blks k, findGotoAnnList lbl ss = some (tgt, fs) →
        Sem.findInStmts lbl env blks k (eraseList ss) =
          some (erase tgt, env, (gotoFramesCont env blks k fs).1, (gotoFramesCont env blks k fs).2)
  | .inl s => by
    intro tgt fs env blks k h
    cases s with
    | labelStmt l body =>
      rw [findGotoAnn_labelStmt] at h
      rw [erase_labelStmt, sem_findInStmt_labelStmt]
      by_cases hl : (l == lbl) = true
      · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [hl, gotoFramesCont]
      · have hlf : (l == lbl) = false := Bool.eq_false_iff.mpr hl
        simp only [hlf, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact findGotoAnn_erase_aux lbl (.inl body) tgt fs env blks k h
    | block ss =>
      rw [findGotoAnn_block] at h
      cases hs : findGotoAnnList lbl ss with
      | none => simp [hs] at h
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [erase_block, sem_findInStmt_block, gotoFramesCont_append]
        exact findGotoAnn_erase_aux lbl (.inr ss) t' f' env [] (.blockEnd env blks k) hs
    | ifStmt c t f? =>
      rw [findGotoAnn_ifStmt] at h
      rw [erase_ifStmt, sem_findInStmt_ifStmt]
      cases ht : findGotoAnn lbl t with
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [findGotoAnn_erase_aux lbl (.inl t) t' f' env blks k ht]
      | none =>
        simp only [ht] at h
        by_cases ha : annHasLabel lbl t = true
        · simp [ha] at h
        · have haf : annHasLabel lbl t = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, ↓reduceIte] at h
          rw [annHasLabel_erase_none haf env blks k]
          cases f? with
          | none => cases h
          | some f => simpa using findGotoAnn_erase_aux lbl (.inl f) tgt fs env blks k h
    | ifJoin c t f? J =>
      rw [findGotoAnn_ifJoin] at h
      rw [erase_ifJoin, sem_findInStmt_ifStmt]
      cases ht : findGotoAnn lbl t with
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [findGotoAnn_erase_aux lbl (.inl t) t' f' env blks k ht]
      | none =>
        simp only [ht] at h
        by_cases ha : annHasLabel lbl t = true
        · simp [ha] at h
        · have haf : annHasLabel lbl t = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, ↓reduceIte] at h
          rw [annHasLabel_erase_none haf env blks k]
          cases f? with
          | none => cases h
          | some f => simpa using findGotoAnn_erase_aux lbl (.inl f) tgt fs env blks k h
    | switchStmt scrut body =>
      rw [findGotoAnn_switchStmt] at h
      cases hb : findGotoAnn lbl body with
      | none => simp [hb] at h
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [erase_switchStmt, sem_findInStmt_switchStmt, gotoFramesCont_append]
        exact findGotoAnn_erase_aux lbl (.inl body) t' f' env blks (.switchCont k) hb
    | caseStmt v body =>
      rw [findGotoAnn_caseStmt] at h
      rw [erase_caseStmt, sem_findInStmt_caseStmt]
      exact findGotoAnn_erase_aux lbl (.inl body) tgt fs env blks k h
    | defaultStmt body =>
      rw [findGotoAnn_defaultStmt] at h
      rw [erase_defaultStmt, sem_findInStmt_defaultStmt]
      exact findGotoAnn_erase_aux lbl (.inl body) tgt fs env blks k h
    | nop | expr _ | decl _ | decls _ | stackDecl _ | stackDecls _ | mixedDecls _
    | whileLoop _ _ _ _ | doWhileLoop _ _ _ _ | doWhileGotos _ _ _ _ _
    | forLoop _ _ _ _ _ _ | gotoStmt _ | breakStmt | continueStmt | returnStmt _ => cases h
  | .inr ss => by
    intro tgt fs env blks k h
    cases ss with
    | nil => cases h
    | cons hd tl =>
      rw [findGotoAnnList_cons] at h
      cases h1 : findGotoAnn lbl hd with
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [eraseList_cons, sem_findInStmts_cons]
        dsimp only
        rw [eraseList_isEmpty, findGotoAnn_erase_aux lbl (.inl hd) t' f' env blks _ h1]
        by_cases he : tl.isEmpty = true
        · simp [he]
        · have hef : tl.isEmpty = false := Bool.eq_false_iff.mpr he
          simp [hef, gotoFramesCont_append, gotoFramesCont]
      | none =>
        simp only [h1] at h
        by_cases ha : annHasLabel lbl hd = true
        · simp [ha] at h
        · have haf : annHasLabel lbl hd = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, ↓reduceIte] at h
          rw [eraseList_cons, sem_findInStmts_cons]
          dsimp only
          rw [annHasLabel_erase_none haf env blks _]
          exact findGotoAnn_erase_aux lbl (.inr tl) tgt fs env blks k h
termination_by x => match x with | .inl s => sizeOf s | .inr ss => sizeOf ss

theorem findGotoAnn_erase {lbl : String} {s tgt : AnnStmt} {fs : List GotoFrame}
    (h : findGotoAnn lbl s = some (tgt, fs)) (env : Env) (blks : List BlockId) (k : Sem.Cont) :
    Sem.findInStmt lbl env blks (erase s) k =
      some (erase tgt, env, (gotoFramesCont env blks k fs).1, (gotoFramesCont env blks k fs).2) :=
  findGotoAnn_erase_aux lbl (.inl s) tgt fs env blks k h

theorem findGotoAnnList_erase {lbl : String} {ss : List AnnStmt} {tgt : AnnStmt} {fs : List GotoFrame}
    (h : findGotoAnnList lbl ss = some (tgt, fs)) (env : Env) (blks : List BlockId) (k : Sem.Cont) :
    Sem.findInStmts lbl env blks k (eraseList ss) =
      some (erase tgt, env, (gotoFramesCont env blks k fs).1, (gotoFramesCont env blks k fs).2) :=
  findGotoAnn_erase_aux lbl (.inr ss) tgt fs env blks k h

private theorem findGotoAnn_sizeOf_aux (lbl : String) :
    (x : AnnStmt ⊕ List AnnStmt) →
      match x with
      | .inl s => ∀ tgt fs, findGotoAnn lbl s = some (tgt, fs) →
        sizeOf tgt + framesSize fs < sizeOf s
      | .inr ss => ∀ tgt fs, findGotoAnnList lbl ss = some (tgt, fs) →
        sizeOf tgt + framesSize fs < sizeOf ss
  | .inl s => by
    dsimp only
    intro tgt fs h
    cases s with
    | labelStmt l body =>
      rw [findGotoAnn_labelStmt] at h
      by_cases hl : (l == lbl) = true
      · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp +arith
      · have hlf : (l == lbl) = false := Bool.eq_false_iff.mpr hl
        simp only [hlf, Bool.false_eq_true, ↓reduceIte] at h
        have hlt := findGotoAnn_sizeOf_aux lbl (.inl body) tgt fs h
        simp only [labelStmt.sizeOf_spec]
        omega
    | block ss =>
      rw [findGotoAnn_block] at h
      cases hs : findGotoAnnList lbl ss with
      | none => simp [hs] at h
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hlt := findGotoAnn_sizeOf_aux lbl (.inr ss) t' f' hs
        rw [framesSize_append]
        simp only [block.sizeOf_spec, framesSize_blockEnd, framesSize_nil]
        omega
    | ifStmt c t f? =>
      rw [findGotoAnn_ifStmt] at h
      cases ht : findGotoAnn lbl t with
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hlt := findGotoAnn_sizeOf_aux lbl (.inl t) t' f' ht
        simp only [ifStmt.sizeOf_spec]
        omega
      | none =>
        simp only [ht] at h
        by_cases ha : annHasLabel lbl t = true
        · simp [ha] at h
        · have haf : annHasLabel lbl t = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, ↓reduceIte] at h
          cases f? with
          | none => cases h
          | some f =>
            have hlt := findGotoAnn_sizeOf_aux lbl (.inl f) tgt fs h
            simp only [ifStmt.sizeOf_spec, Option.some.sizeOf_spec]
            omega
    | ifJoin c t f? J =>
      rw [findGotoAnn_ifJoin] at h
      cases ht : findGotoAnn lbl t with
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hlt := findGotoAnn_sizeOf_aux lbl (.inl t) t' f' ht
        simp only [ifJoin.sizeOf_spec]
        omega
      | none =>
        simp only [ht] at h
        by_cases ha : annHasLabel lbl t = true
        · simp [ha] at h
        · have haf : annHasLabel lbl t = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, ↓reduceIte] at h
          cases f? with
          | none => cases h
          | some f =>
            have hlt := findGotoAnn_sizeOf_aux lbl (.inl f) tgt fs h
            simp only [ifJoin.sizeOf_spec, Option.some.sizeOf_spec]
            omega
    | switchStmt scrut body =>
      rw [findGotoAnn_switchStmt] at h
      cases hb : findGotoAnn lbl body with
      | none => simp [hb] at h
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hlt := findGotoAnn_sizeOf_aux lbl (.inl body) t' f' hb
        rw [framesSize_append]
        simp only [switchStmt.sizeOf_spec, framesSize_switchCont, framesSize_nil]
        omega
    | caseStmt v body =>
      rw [findGotoAnn_caseStmt] at h
      have hlt := findGotoAnn_sizeOf_aux lbl (.inl body) tgt fs h
      simp only [caseStmt.sizeOf_spec]
      omega
    | defaultStmt body =>
      rw [findGotoAnn_defaultStmt] at h
      have hlt := findGotoAnn_sizeOf_aux lbl (.inl body) tgt fs h
      simp only [defaultStmt.sizeOf_spec]
      omega
    | nop | expr _ | decl _ | decls _ | stackDecl _ | stackDecls _ | mixedDecls _
    | whileLoop _ _ _ _ | doWhileLoop _ _ _ _ | doWhileGotos _ _ _ _ _
    | forLoop _ _ _ _ _ _ | gotoStmt _ | breakStmt | continueStmt | returnStmt _ => cases h
  | .inr ss => by
    dsimp only
    intro tgt fs h
    cases ss with
    | nil => cases h
    | cons hd tl =>
      rw [findGotoAnnList_cons] at h
      cases h1 : findGotoAnn lbl hd with
      | some res =>
        rcases res with ⟨t', f'⟩
        simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hlt := findGotoAnn_sizeOf_aux lbl (.inl hd) t' f' h1
        simp only [List.cons.sizeOf_spec]
        split
        · omega
        · rw [framesSize_append]
          simp only [framesSize_stmts, framesSize_nil]
          omega
      | none =>
        simp only [h1] at h
        by_cases ha : annHasLabel lbl hd = true
        · simp [ha] at h
        · have haf : annHasLabel lbl hd = false := Bool.eq_false_iff.mpr ha
          simp only [haf, Bool.false_eq_true, ↓reduceIte] at h
          have hlt := findGotoAnn_sizeOf_aux lbl (.inr tl) tgt fs h
          simp only [List.cons.sizeOf_spec]
          omega
termination_by x => match x with | .inl s => sizeOf s | .inr ss => sizeOf ss

theorem findGotoAnn_sizeOf_lt {lbl : String} {s tgt : AnnStmt} {fs : List GotoFrame}
    (h : findGotoAnn lbl s = some (tgt, fs)) :
    sizeOf tgt + framesSize fs < sizeOf s :=
  findGotoAnn_sizeOf_aux lbl (.inl s) tgt fs h

theorem findGotoAnnList_sizeOf_lt {lbl : String} {ss : List AnnStmt} {tgt : AnnStmt} {fs : List GotoFrame}
    (h : findGotoAnnList lbl ss = some (tgt, fs)) :
    sizeOf tgt + framesSize fs < sizeOf ss :=
  findGotoAnn_sizeOf_aux lbl (.inr ss) tgt fs h

end AnnStmt

end C99.Proof.VCGen
