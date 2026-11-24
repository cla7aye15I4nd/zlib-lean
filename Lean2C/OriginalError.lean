import Lean2C.ErrorIndex
import Lean2C.Soundness
import ZlibF.Proof.«zutil.c»

/-! The guarded table lookup in patched and independently generated zutil.c. -/

namespace Lean2C.OriginalError
open CSource Semantics Soundness C
open Zlib.Zutil (zError z_errmsg)
set_option autoImplicit false

private def err : Value := .var .i32 "err"
private def below : Value := .op .i32 "<" err (.op .i32 "-" (.num .i32 0) (.num .i32 6))
private def above : Value := .op .i32 ">" err (.num .i32 2)
private def guardExpr : Value := .op .i32 "||" below above
def indexExpr : Value :=
  .choose guardExpr (.num .i32 9) (.op .i32 "-" (.num .i32 2) err)
private def lookupExpr (i : Value) : Value :=
  .index (.ptr .u8) (.var (.ptr (.ptr (.named "char"))) "z_errmsg") i

def original : List (String × Ty) × List Stmt :=
  ([("err", .i32)], [.ret (lookupExpr indexExpr)])

def standalone : List (String × Ty) × List Stmt :=
  ([("err", .i32)], [.decl .i32 "i" (some indexExpr), .ret (lookupExpr (.var .i32 "i"))])

section
variable (f : FnTable) (g : CEnv) (fuel : Nat) (env : CEnv) (h : Heap) (x : Int32)

private abbrev EV (e : Value) (v : CVal) := evalValue f g fuel env h e = .ok (v,env,h)

private theorem guard_eval (param : env.lookup "err" = some (.i32 x)) :
    EV f g fuel env h guardExpr (.bool (x < -6 || x > 2)) := by
  have word : EV f g fuel env h err (.i32 x) := evalValue_var _ _ _ _ _ _ _ _ param
  have low : EV f g fuel env h below (.bool (x < -6)) :=
    evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl word
      (evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
        (evalValue_num _ _ _ _ _ _ _ _ rfl) (evalValue_num _ _ _ _ _ _ _ _ rfl)
        (show evalBinOp .i32 "-" (.i32 0) (.i32 6) h = .ok (.i32 (-6)) from rfl)) rfl
  have high : EV f g fuel env h above (.bool (x > 2)) :=
    evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl word
      (evalValue_num _ _ _ _ _ _ _ _ rfl) rfl
  unfold EV guardExpr
  rw [evalValue]
  unfold EV at low high
  simp only [show ("||" == "&&") = false from rfl, beq_self_eq_true, Bool.false_eq_true,
    ↓reduceIte, low, high, CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases decide (x < -6) <;> rfl

private theorem checked_difference (inside : ¬ (x < -6 || x > 2) = true) :
    evalBinOp .i32 "-" (.i32 2) (.i32 x) h = .ok (.i32 (2 - x)) := by
  obtain ⟨diff, lo, hi⟩ := ErrorIndex.difference_on_domain x inside
  have valid : inSignedRange 32 (2 - x.toInt) = true := by
    change (decide (-2147483648 ≤ 2 - x.toInt) && decide (2 - x.toInt < 2147483648)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have cast : Int32.ofInt (2 - x.toInt) = 2 - x := by rw [← diff, Int32.ofInt_toInt]
  simp [evalBinOp, checkedSigned, valid, cast, Bind.bind, Except.bind]

private theorem index_eval (param : env.lookup "err" = some (.i32 x)) :
    EV f g fuel env h indexExpr (.i32 (ErrorIndex.index x)) := by
  have guard := guard_eval f g fuel env h x param
  have word : EV f g fuel env h err (.i32 x) := evalValue_var _ _ _ _ _ _ _ _ param
  unfold EV at guard ⊢
  unfold indexExpr
  rw [evalValue]
  simp only [guard, CVal.toBool?, Bind.bind, Except.bind]
  by_cases outside : (x < -6 || x > 2) = true
  · simp only [outside, ErrorIndex.index, ↓reduceIte]
    exact evalValue_num _ _ _ _ _ _ _ _ rfl
  · have within : (x < -6 || x > 2) = false := Bool.eq_false_iff.mpr outside
    simp only [within, ErrorIndex.index, Bool.false_eq_true, ↓reduceIte]
    exact evalValue_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
      (evalValue_num _ _ _ _ _ _ _ _ rfl) word (checked_difference h x outside)

end

/-- The result of returning a string address from a C function. -/
def result (action : M BPtr) (h : Heap) : StmtOutcome :=
  match action h with
  | .ok (p, after) => .ret (.ptr p) after
  | .error fault => .fault fault

private theorem table_run (x : Int32) (h : Heap) :
    readStringSlot z_errmsg (ErrorIndex.index x).toInt h =
    (do return CVal.ptr (← zError x) : M CVal) h := by
  obtain ⟨lo,hi⟩ := ErrorIndex.inBounds x
  have nonneg : 0 ≤ (ErrorIndex.index x).toInt := by simpa using Int32.le_iff_toInt_le.mp lo
  have top := Int32.lt_iff_toInt_lt.mp hi
  change (ErrorIndex.index x).toInt < 10 at top
  have valid : (ErrorIndex.index x).toInt.toNat < z_errmsg.size := by
    change (ErrorIndex.index x).toInt.toNat < 10
    omega
  unfold readStringSlot zError Zlib.Zutil.errorMessage
  change _ = (do return CVal.ptr (← (match z_errmsg[(ErrorIndex.index x).toInt.toNat]? with
    | some s => Zlib.Zutil.strLit s | none => ub "z_errmsg index outside its array")) : M CVal) h
  simp only [Int.not_lt.mpr nonneg, ↓reduceIte, Array.getElem?_eq_getElem valid]
  rfl

private theorem lookup_run (f : FnTable) (g env : CEnv) (fuel : Nat) (x : Int32) (h : Heap)
    (i : Value) (globals : g.lookup "z_errmsg" = some (.stringTable z_errmsg))
    (localFree : env.lookup "z_errmsg" = none)
    (offset : EV f g fuel env h i (.i32 (ErrorIndex.index x))) :
    execStmts f g fuel env h [.ret (lookupExpr i)] = result (zError x) h := by
  have tab : evalValue f g fuel env h (.var (.ptr (.ptr (.named "char"))) "z_errmsg") =
      .ok (.stringTable z_errmsg, env, h) := by
    rw [evalValue]; simp [localFree, globals]
  unfold EV at offset
  unfold lookupExpr result
  rw [execStmts, execStmt, evalValue]
  simp only [tab, offset, CVal.toInt?, Bind.bind, Except.bind, table_run]
  cases run : zError x h with
  | error fault => rfl
  | ok p => cases p; rfl

/-- The source expression implements the public Lean entry for every signed argument. -/
theorem original_sound (f : FnTable) (g : CEnv) (fuel : Nat) (x : Int32) (h : Heap)
    (globals : g.lookup "z_errmsg" = some (.stringTable z_errmsg)) :
    runCFn f g fuel original [.i32 x] h = result (zError x) h := by
  unfold runCFn original
  simp [bindParams, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact lookup_run f g _ fuel x h indexExpr globals rfl (index_eval _ _ _ _ _ x rfl)

/-- Storing the index in the generated int temporary preserves the lookup and the final heap. -/
theorem standalone_sound (f : FnTable) (g : CEnv) (fuel : Nat) (x : Int32) (h : Heap)
    (globals : g.lookup "z_errmsg" = some (.stringTable z_errmsg)) :
    runCFn f g fuel standalone [.i32 x] h = result (zError x) h := by
  unfold runCFn standalone
  simp [bindParams, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [execStmts, execStmt]
  have val := index_eval f g fuel [("err", .i32 x)] h x rfl
  unfold EV at val
  simp [val]
  apply lookup_run _ _ _ _ _ _ _ globals rfl
  exact evalValue_var _ _ _ _ _ _ _ _ rfl

theorem same_zError (f : FnTable) (g : CEnv) (fuel : Nat) (x : Int32) (h : Heap)
    (globals : g.lookup "z_errmsg" = some (.stringTable z_errmsg)) :
    runCFn f g fuel original [.i32 x] h = runCFn f g fuel standalone [.i32 x] h := by
  rw [original_sound f g fuel x h globals, standalone_sound f g fuel x h globals]

/-- Both compiled bodies return a pointer to the expected NUL-terminated, read-only
message and preserve the entire heap for every signed int, including its extremes. -/
theorem zError_safe (f : FnTable) (g : CEnv) (fuel : Nat) (x : Int32) (h : Heap)
    (globals : g.lookup "z_errmsg" = some (.stringTable z_errmsg)) :
    ∃ p, runCFn f g fuel original [.i32 x] h = .ret (.ptr p) h ∧
      runCFn f g fuel standalone [.i32 x] h = .ret (.ptr p) h ∧
      Zlib.Zutil.Spec.CString h p (Zlib.Zutil.Spec.errText x.toInt) := by
  obtain ⟨i, after, exec, text, heap⟩ := Zlib.Zutil.Proofs.zError_correct h x
  change after = h at heap
  subst after
  change zError x h = _ at exec
  rw [original_sound f g fuel x h globals, standalone_sound f g fuel x h globals]
  exact ⟨_, by rw [result, exec], by rw [result, exec], text⟩

#print axioms same_zError
#print axioms zError_safe

end Lean2C.OriginalError
