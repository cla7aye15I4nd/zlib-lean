import Lean2C.Semantics
import ZlibF.Zlib.«compress.c»
import ZlibF.Zlib.«zutil.c»
import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«adler32.c»
import ZlibF.Spec.Safety.Queries
import ZlibF.Spec.Safety.Checksums
import ZlibF.Spec.Functional.Queries

/-!
# Soundness and C99 UB-freedom for `Lean2C` lowering

Connects the C99 LP64 operational semantics (`Lean2C.Semantics`) to Lean's execution
monad `C.M` and `C.Heap` primitives:
1. Bit-exactness and zero C99 §6.5.7 shift UB for masked and guarded shift lowering.
2. Heap load/store simulation (`readHeap`/`writeHeap` ↔ `C.load8`/`load64`/`store8`/`store64`)
   and relational `while` / `do-while` loop simulation (`execStmt` ↔ `C.cwhile` / `C.cdoWhile`).
3. End-to-end `runCFn` soundness, C99 UB-freedom, and `Goal.*` safety transfer for the
   lowered C ASTs of `compressBound_z`, `compressBound`, `zlibCompileFlags`, `byte_swap`,
   and `adler32_combine_`.
-/

namespace Lean2C.Soundness
open Lean2C.CSource Lean2C.Semantics C
set_option autoImplicit false

/-! ## Scalar conversion and compositional evaluator rules -/

@[simp] private theorem uint8_ofInt_toNat (x : UInt8) : UInt8.ofInt (x.toNat : Int) = x := by
  have h1 : ((x.toNat : Int) % (2 ^ 8 : Int)).toNat = x.toNat := by
    rw [show (2 ^ 8 : Int) = ((256 : Nat) : Int) by decide, ← Int.natCast_emod,
      Int.toNat_natCast]
    exact Nat.mod_eq_of_lt x.toNat_lt
  rw [UInt8.ofInt, h1, UInt8.ofNat_toNat]

@[simp] private theorem uint32_ofInt_toNat (x : UInt32) : UInt32.ofInt (x.toNat : Int) = x := by
  have h1 : ((x.toNat : Int) % (2 ^ 32 : Int)).toNat = x.toNat := by
    rw [show (2 ^ 32 : Int) = ((4294967296 : Nat) : Int) by decide, ← Int.natCast_emod,
      Int.toNat_natCast]
    exact Nat.mod_eq_of_lt x.toNat_lt
  rw [UInt32.ofInt, h1, UInt32.ofNat_toNat]

@[simp] private theorem uint64_ofInt_toNat (x : UInt64) : UInt64.ofInt (x.toNat : Int) = x := by
  have h1 : ((x.toNat : Int) % (2 ^ 64 : Int)).toNat = x.toNat := by
    rw [show (2 ^ 64 : Int) = ((18446744073709551616 : Nat) : Int) by decide, ← Int.natCast_emod,
      Int.toNat_natCast]
    exact Nat.mod_eq_of_lt x.toNat_lt
  rw [UInt64.ofInt, h1, UInt64.ofNat_toNat]

@[simp] private theorem int64_ofInt_toInt (x : Int64) : Int64.ofInt x.toInt = x := by
  apply Int64.toInt_inj.mp
  rw [Int64.toInt_ofInt]
  have h1 : -(2 ^ 63 : Int) ≤ x.toInt := x.toBitVec.le_toInt
  have h2 : x.toInt < 2 ^ 63 := x.toBitVec.toInt_lt
  simp only [Int64.size, Int.bmod]
  split <;> omega

private theorem uint64_ofInt_eq_toUInt64 (x : Int64) (hx : 0 ≤ x.toInt) :
    UInt64.ofInt x.toInt = x.toUInt64 := by
  have hlt : x.toInt < 2 ^ 63 := x.toBitVec.toInt_lt
  apply UInt64.toNat_inj.mp
  rw [UInt64.ofInt]
  change (x.toInt % (2 ^ 64 : Int)).toNat % 2 ^ 64 = x.toBitVec.toNat
  have hb : x.toBitVec.toNat < 2 ^ 64 := x.toBitVec.isLt
  have hi : x.toInt = x.toBitVec.toInt := rfl
  rw [BitVec.toInt_eq_toNat_cond] at hi
  split at hi <;> omega

@[simp] private theorem evalCast_u32_self {x : UInt32} :
    evalCast .u32 (.u32 x) = .ok (.u32 x) := by
  simp [evalCast, CVal.toInt?, ofIntForTy]

@[simp] private theorem evalCast_u64_self {x : UInt64} :
    evalCast .u64 (.u64 x) = .ok (.u64 x) := by
  simp [evalCast, CVal.toInt?, ofIntForTy]

@[simp] private theorem evalCast_i64_self {x : Int64} :
    evalCast .i64 (.i64 x) = .ok (.i64 x) := by
  simp [evalCast, CVal.toInt?, ofIntForTy]

@[simp] private theorem evalCast_i32_self {x : Int32} :
    evalCast .i32 (.i32 x) = .ok (.i32 x) := by
  simp only [evalCast, CVal.toInt?, ofIntForTy]
  congr 2
  apply Int32.toInt_inj.mp
  rw [Int32.toInt_ofInt]
  have h1 : -(2 ^ 31 : Int) ≤ x.toInt := x.toBitVec.le_toInt
  have h2 : x.toInt < 2 ^ 31 := x.toBitVec.toInt_lt
  simp only [Int32.size, Int.bmod]
  split <;> omega

@[simp] private theorem evalCast_u64_u32 (x : UInt32) :
    evalCast .u64 (.u32 x) = .ok (.u64 x.toUInt64) := by
  simp [evalCast, CVal.toInt?, ofIntForTy]
  apply UInt64.toNat_inj.mp
  rw [UInt64.ofInt, UInt32.toNat_toUInt64]
  change ((x.toNat : Int) % (2 ^ 64 : Int)).toNat % 2 ^ 64 = x.toNat
  rw [show (2 ^ 64 : Int) = ((18446744073709551616 : Nat) : Int) by decide, ← Int.natCast_emod,
    Int.toNat_natCast]
  have hx := x.toNat_lt
  have h1 : x.toNat < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt h1]
  exact Nat.mod_eq_of_lt (by omega)

@[simp] private theorem evalCast_u32_u64 (x : UInt64) :
    evalCast .u32 (.u64 x) = .ok (.u32 x.toUInt32) := by
  simp [evalCast, CVal.toInt?, ofIntForTy]
  apply UInt32.toNat_inj.mp
  rw [UInt32.ofInt, UInt64.toNat_toUInt32]
  change ((x.toNat : Int) % (2 ^ 32 : Int)).toNat % 2 ^ 32 = x.toNat % 2 ^ 32
  rw [show (2 ^ 32 : Int) = ((4294967296 : Nat) : Int) by decide, ← Int.natCast_emod,
    Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

private theorem bool_if_false {α : Type _} (t e : α) :
    (if false = true then t else e) = e := rfl

private theorem effWidth_32 : (if (32 : Nat) < 32 then 32 else 32) = 32 := rfl
private theorem effWidth_64 : (if (64 : Nat) < 32 then 32 else 64) = 64 := rfl

private theorem int32_toInt_ofNat_lt (n : Nat) (hn : n < 2 ^ 31) :
    (Int32.ofNat n).toInt = (n : Int) := by
  have h : Int32.ofNat n = Int32.ofInt n := rfl
  rw [h, Int32.toInt_ofInt]
  simp only [Int32.size, Int.bmod]
  split <;> omega

private theorem evalCast_u32_i32_of_nat (n : Nat) (hn : n < 2 ^ 31) :
    evalCast .u32 (.i32 (Int32.ofNat n)) = .ok (.u32 (UInt32.ofNat n)) := by
  have hi := int32_toInt_ofNat_lt n hn
  have hu : UInt32.ofInt (n : Int) = UInt32.ofNat n := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.ofInt]
    change ((n : Int) % (2 ^ 32 : Int)).toNat % 2 ^ 32 = n % 2 ^ 32
    rw [show (2 ^ 32 : Int) = ((4294967296 : Nat) : Int) by decide, ← Int.natCast_emod,
      Int.toNat_natCast]
    simp only [Nat.mod_eq_of_lt (by omega : n < 4294967296)]
  simp [evalCast, CVal.toInt?, ofIntForTy, hi, hu]

private theorem evalCast_u64_i32_of_nat (n : Nat) (hn : n < 2 ^ 31) :
    evalCast .u64 (.i32 (Int32.ofNat n)) = .ok (.u64 (UInt64.ofNat n)) := by
  have hi := int32_toInt_ofNat_lt n hn
  have hu : UInt64.ofInt (n : Int) = UInt64.ofNat n := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.ofInt]
    change ((n : Int) % (2 ^ 64 : Int)).toNat % 2 ^ 64 = n % 2 ^ 64
    rw [show (2 ^ 64 : Int) = ((18446744073709551616 : Nat) : Int) by decide, ← Int.natCast_emod,
      Int.toNat_natCast]
    simp only [Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
  simp [evalCast, CVal.toInt?, ofIntForTy, hi, hu]

private theorem cenv_lookup_set_ne (env : CEnv) {k name : String} (hne : (k == name) = false)
    (v : CVal) : CEnv.lookup (CEnv.set env k v) name = CEnv.lookup env name := by
  induction env with
  | nil => simp [CEnv.set, CEnv.lookup, hne]
  | cons hd tl ih =>
    rcases hd with ⟨k', old⟩
    by_cases hk : k' = k
    · subst hk; simp [CEnv.set, CEnv.lookup, hne]
    · have hkf : (k' == k) = false := beq_false_of_ne hk
      by_cases hkn : k' = name
      · subst hkn; simp [CEnv.set, hkf, CEnv.lookup]
      · have hknf : (k' == name) = false := beq_false_of_ne hkn
        simp [CEnv.set, hkf, CEnv.lookup, hknf, ih]

private theorem evalValue_var (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv)
    (h : C.Heap) (ty : Ty) (x : String) (v : CVal) (hx : env.lookup x = some v) :
    evalValue fns globals fuel env h (.var ty x) = .ok (v, env, h) := by
  rw [evalValue]; simp [hx]

private theorem evalValue_global (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv)
    (h : C.Heap) (ty : Ty) (x : String) (v : CVal) (hx : env.lookup x = none)
    (hg : globals.lookup x = some v) :
    evalValue fns globals fuel env h (.var ty x) = .ok (v, env, h) := by
  rw [evalValue]; simp [hx, hg]

private theorem evalValue_num (fns : FnTable) (globals : CEnv) (fuel : Nat) (env : CEnv)
    (h : C.Heap) (ty : Ty) (n : Nat) (v : CVal) (hn : evalNum ty n = .ok v) :
    evalValue fns globals fuel env h (.num ty n) = .ok (v, env, h) := by
  rw [evalValue]; simp [hn, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalValue_cast (fns : FnTable) (globals : CEnv) (fuel : Nat) (env env1 : CEnv)
    (h h1 : C.Heap) (ty : Ty) (a : Value) (va v : CVal)
    (ha : evalValue fns globals fuel env h a = .ok (va, env1, h1))
    (hc : evalCast ty va = .ok v) :
    evalValue fns globals fuel env h (.cast ty a) = .ok (v, env1, h1) := by
  rw [evalValue]; simp [ha, hc, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalValue_op (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 env2 : CEnv) (h h1 h2 : C.Heap) (ty : Ty) (op : String) (l r : Value)
    (lv rv res : CVal)
    (hnot1 : (op == "&&") = false) (hnot2 : (op == "||") = false)
    (hl : evalValue fns globals fuel env h l = .ok (lv, env1, h1))
    (hr : evalValue fns globals fuel env1 h1 r = .ok (rv, env2, h2))
    (hb : evalBinOp ty op lv rv h2 = .ok res) :
    evalValue fns globals fuel env h (.op ty op l r) = .ok (res, env2, h2) := by
  rw [evalValue]; simp [hnot1, hnot2, hl, hr, hb, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalValue_choose_t (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 env2 : CEnv) (h h1 h2 : C.Heap) (c t f : Value) (cv res : CVal)
    (hc : evalValue fns globals fuel env h c = .ok (cv, env1, h1))
    (htb : cv.toBool? = some true)
    (ht : evalValue fns globals fuel env1 h1 t = .ok (res, env2, h2)) :
    evalValue fns globals fuel env h (.choose c t f) = .ok (res, env2, h2) := by
  rw [evalValue]; simp [hc, htb, ht, Bind.bind, Except.bind]

private theorem evalValue_choose_f (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 env2 : CEnv) (h h1 h2 : C.Heap) (c t f : Value) (cv res : CVal)
    (hc : evalValue fns globals fuel env h c = .ok (cv, env1, h1))
    (htb : cv.toBool? = some false)
    (hf : evalValue fns globals fuel env1 h1 f = .ok (res, env2, h2)) :
    evalValue fns globals fuel env h (.choose c t f) = .ok (res, env2, h2) := by
  rw [evalValue]; simp [hc, htb, hf, Bind.bind, Except.bind]

private theorem evalArgs_singleton (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (a : Value) (av : CVal)
    (ha : evalValue fns globals fuel env h a = .ok (av, env1, h1)) :
    evalArgs fns globals fuel env h [a] = .ok ([av], env1, h1) := by
  rw [evalArgs.eq_def]
  simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [evalArgs.eq_def]

private theorem execStmts_decl_some (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (ty : Ty) (name : String) (initExpr : Value)
    (iv cv : CVal) (rest : List Stmt)
    (he : evalValue fns globals fuel env h initExpr = .ok (iv, env1, h1))
    (hc : evalCast ty iv = .ok cv) :
    execStmts fns globals fuel env h (Stmt.decl ty name (some initExpr) :: rest) =
      execStmts fns globals fuel (env1.set name cv) h1 rest := by
  rw [execStmts, execStmt]; simp [he, hc]

private theorem execStmts_decl_none (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (ty : Ty) (name : String) (rest : List Stmt) :
    execStmts fns globals fuel env h (Stmt.decl ty name none :: rest) =
      execStmts fns globals fuel (env.set name .void) h rest := by
  rw [execStmts, execStmt]

private theorem execStmts_assign_var (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (ty : Ty) (name : String) (rhs : Value)
    (rv cv : CVal) (rest : List Stmt)
    (he : evalValue fns globals fuel env h rhs = .ok (rv, env1, h1))
    (hc : evalCast ty rv = .ok cv) :
    execStmts fns globals fuel env h (Stmt.assign (.var ty name) rhs :: rest) =
      execStmts fns globals fuel (env1.set name cv) h1 rest := by
  rw [execStmts, execStmt]; simp [he, hc]

private theorem execStmts_branch_t (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (cond : Value) (cv : CVal)
    (yes no rest : List Stmt)
    (hc : evalValue fns globals fuel env h cond = .ok (cv, env1, h1))
    (htb : cv.toBool? = some true) :
    execStmts fns globals fuel env h (Stmt.branch cond yes no :: rest) =
      match execStmts fns globals fuel env1 h1 yes with
      | .next env2 h2 => execStmts fns globals fuel env2 h2 rest
      | .brk env2 h2 => .brk env2 h2
      | .ret rv h2 => .ret rv h2
      | .fault f => .fault f := by
  rw [execStmts, execStmt]; simp only [hc, htb]; rfl

private theorem execStmts_branch_f (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (cond : Value) (cv : CVal)
    (yes no rest : List Stmt)
    (hc : evalValue fns globals fuel env h cond = .ok (cv, env1, h1))
    (htb : cv.toBool? = some false) :
    execStmts fns globals fuel env h (Stmt.branch cond yes no :: rest) =
      match execStmts fns globals fuel env1 h1 no with
      | .next env2 h2 => execStmts fns globals fuel env2 h2 rest
      | .brk env2 h2 => .brk env2 h2
      | .ret rv h2 => .ret rv h2
      | .fault f => .fault f := by
  rw [execStmts, execStmt]; simp only [hc, htb]; rfl

private theorem execStmts_ret (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (e : Value) (rv : CVal) (rest : List Stmt)
    (he : evalValue fns globals fuel env h e = .ok (rv, env1, h1)) :
    execStmts fns globals fuel env h (Stmt.ret e :: rest) = .ret rv h1 := by
  rw [execStmts, execStmt]; simp [he]

private theorem execStmts_if_assign_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (cond eT eF : Value) (name : String) (b : Bool)
    (vT vF : UInt64) (rest : List Stmt)
    (hc : evalValue fns globals fuel env h cond = .ok (.bool b, env, h))
    (hT : evalValue fns globals fuel env h eT = .ok (.u64 vT, env, h))
    (hF : evalValue fns globals fuel env h eF = .ok (.u64 vF, env, h)) :
    execStmts fns globals fuel env h
      (Stmt.branch cond [Stmt.assign (.var .u64 name) eT] [Stmt.assign (.var .u64 name) eF] :: rest) =
      execStmts fns globals fuel (env.set name (.u64 (if b then vT else vF))) h rest := by
  cases b
  · rw [execStmts_branch_f fns globals fuel env env h h cond (.bool false) _ _ rest hc rfl]
    rw [execStmts_assign_var fns globals fuel env env h h .u64 name eF (.u64 vF) (.u64 vF) []
      hF evalCast_u64_self]
    rw [execStmts]
    rfl
  · rw [execStmts_branch_t fns globals fuel env env h h cond (.bool true) _ _ rest hc rfl]
    rw [execStmts_assign_var fns globals fuel env env h h .u64 name eT (.u64 vT) (.u64 vT) []
      hT evalCast_u64_self]
    rw [execStmts]
    rfl

private theorem evalBinOp_u64_add (x y : UInt64) (h : C.Heap) :
    evalBinOp .u64 "+" (.u64 x) (.u64 y) h = .ok (.u64 (x + y)) := by
  unfold evalBinOp; simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u64_sub (x y : UInt64) (h : C.Heap) :
    evalBinOp .u64 "-" (.u64 x) (.u64 y) h = .ok (.u64 (x - y)) := by
  unfold evalBinOp; simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u64_mul (x y : UInt64) (h : C.Heap) :
    evalBinOp .u64 "*" (.u64 x) (.u64 y) h = .ok (.u64 (x * y)) := by
  unfold evalBinOp; simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u64_mod (x y : UInt64) (hy : y ≠ 0) (h : C.Heap) :
    evalBinOp .u64 "%" (.u64 x) (.u64 y) h = .ok (.u64 (x % y)) := by
  have hb : (y == 0) = false := beq_false_of_ne hy
  unfold evalBinOp; simp [hb, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u64_or (x y : UInt64) (h : C.Heap) :
    evalBinOp .u64 "|" (.u64 x) (.u64 y) h = .ok (.u64 (x ||| y)) := by
  unfold evalBinOp; simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u32_or (x y : UInt32) (h : C.Heap) :
    evalBinOp .u32 "|" (.u32 x) (.u32 y) h = .ok (.u32 (x ||| y)) := by
  unfold evalBinOp; simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u32_and (x y : UInt32) (h : C.Heap) :
    evalBinOp .u32 "&" (.u32 x) (.u32 y) h = .ok (.u32 (x &&& y)) := by
  unfold evalBinOp; simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem evalBinOp_u32_shl (x : UInt32) (k : Nat) (hk : k < 32) (h : C.Heap) :
    evalBinOp .u32 "<<" (.u32 x) (.i32 (Int32.ofNat k)) h = .ok (.u32 (x <<< UInt32.ofNat k)) := by
  have hi := int32_toInt_ofNat_lt k (by omega)
  have hb : (decide ((k : Int) < 0) || decide (Int.ofNat (if (32 : Nat) < 32 then 32 else 32) ≤ (k : Int))) = false := by
    rw [effWidth_32]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "<<" = false from rfl,
    show ("<<" == "<<" || "<<" == ">>") = true from rfl, bitWidth?, CVal.toInt?, hi, hb,
    Bool.false_or, bool_if_false, evalCast_u32_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Int.toNat_natCast]
  rfl

private theorem evalBinOp_u32_shr (x : UInt32) (k : Nat) (hk : k < 32) (h : C.Heap) :
    evalBinOp .u32 ">>" (.u32 x) (.i32 (Int32.ofNat k)) h = .ok (.u32 (x >>> UInt32.ofNat k)) := by
  have hi := int32_toInt_ofNat_lt k (by omega)
  have hb : (decide ((k : Int) < 0) || decide (Int.ofNat (if (32 : Nat) < 32 then 32 else 32) ≤ (k : Int))) = false := by
    rw [effWidth_32]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains ">>" = false from rfl,
    show (">>" == "<<") = false from rfl, show (">>" == ">>") = true from rfl,
    bitWidth?, CVal.toInt?, hi, hb,
    Bool.false_or, bool_if_false, evalCast_u32_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Int.toNat_natCast]
  rfl

private theorem evalBinOp_u64_shl (x : UInt64) (k : Nat) (hk : k < 64) (h : C.Heap) :
    evalBinOp .u64 "<<" (.u64 x) (.i32 (Int32.ofNat k)) h = .ok (.u64 (x <<< UInt64.ofNat k)) := by
  have hi := int32_toInt_ofNat_lt k (by omega)
  have hb : (decide ((k : Int) < 0) || decide (Int.ofNat (if (64 : Nat) < 32 then 32 else 64) ≤ (k : Int))) = false := by
    rw [effWidth_64]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "<<" = false from rfl,
    show ("<<" == "<<" || "<<" == ">>") = true from rfl, bitWidth?, CVal.toInt?, hi, hb,
    Bool.false_or, bool_if_false, evalCast_u64_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Int.toNat_natCast]
  rfl

private theorem evalBinOp_u64_shr (x : UInt64) (k : Nat) (hk : k < 64) (h : C.Heap) :
    evalBinOp .u64 ">>" (.u64 x) (.i32 (Int32.ofNat k)) h = .ok (.u64 (x >>> UInt64.ofNat k)) := by
  have hi := int32_toInt_ofNat_lt k (by omega)
  have hb : (decide ((k : Int) < 0) || decide (Int.ofNat (if (64 : Nat) < 32 then 32 else 64) ≤ (k : Int))) = false := by
    rw [effWidth_64]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains ">>" = false from rfl,
    show (">>" == "<<") = false from rfl, show (">>" == ">>") = true from rfl,
    bitWidth?, CVal.toInt?, hi, hb,
    Bool.false_or, bool_if_false, evalCast_u64_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Int.toNat_natCast]
  rfl

private theorem uint32_ofNat_mod32 (n : UInt32) : UInt32.ofNat (n.toNat % 32) = n % 32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod]
  change (n.toNat % 32) % 2 ^ 32 = n.toNat % (32 : UInt32).toNat
  have hlt : n.toNat % 32 < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hlt]; rfl

private theorem uint64_ofNat_mod64 (n : UInt64) : UInt64.ofNat (n.toNat % 64) = n % 64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod]
  change (n.toNat % 64) % 2 ^ 64 = n.toNat % (64 : UInt64).toNat
  have hlt : n.toNat % 64 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hlt]; rfl

/-! ## 1. Shift lowering soundness (zero C99 §6.5.7 UB and bit-exactness) -/

theorem uint32_shl_mod (x n : UInt32) :
    x <<< UInt32.ofNat (n % 32).toNat = x <<< n := by
  rw [UInt32.toNat_mod, show (32 : UInt32).toNat = 32 from rfl, uint32_ofNat_mod32]
  apply UInt32.toBitVec_inj.mp; simp

theorem uint32_shr_mod (x n : UInt32) :
    x >>> UInt32.ofNat (n % 32).toNat = x >>> n := by
  rw [UInt32.toNat_mod, show (32 : UInt32).toNat = 32 from rfl, uint32_ofNat_mod32]
  apply UInt32.toBitVec_inj.mp; simp

theorem uint64_shl_mod (x n : UInt64) :
    x <<< UInt64.ofNat (n % 64).toNat = x <<< n := by
  rw [UInt64.toNat_mod, show (64 : UInt64).toNat = 64 from rfl, uint64_ofNat_mod64]
  apply UInt64.toBitVec_inj.mp; simp

theorem uint64_shr_mod (x n : UInt64) :
    x >>> UInt64.ofNat (n % 64).toNat = x >>> n := by
  rw [UInt64.toNat_mod, show (64 : UInt64).toNat = 64 from rfl, uint64_ofNat_mod64]
  apply UInt64.toBitVec_inj.mp; simp

private theorem uint32_shl_mod_nat (x n : UInt32) :
    x <<< UInt32.ofNat (n.toNat % 32) = x <<< n := by
  rw [uint32_ofNat_mod32]
  apply UInt32.toBitVec_inj.mp; simp

private theorem uint32_shr_mod_nat (x n : UInt32) :
    x >>> UInt32.ofNat (n.toNat % 32) = x >>> n := by
  rw [uint32_ofNat_mod32]
  apply UInt32.toBitVec_inj.mp; simp

private theorem uint64_shl_mod_nat (x n : UInt64) :
    x <<< UInt64.ofNat (n.toNat % 64) = x <<< n := by
  rw [uint64_ofNat_mod64]
  apply UInt64.toBitVec_inj.mp; simp

private theorem uint64_shr_mod_nat (x n : UInt64) :
    x >>> UInt64.ofNat (n.toNat % 64) = x >>> n := by
  rw [uint64_ofNat_mod64]
  apply UInt64.toBitVec_inj.mp; simp

private theorem mod_lt_32 (n : UInt32) : (n % 32).toNat < 32 := by
  rw [UInt32.toNat_mod]; exact Nat.mod_lt _ (by decide)

private theorem mod_lt_64 (n : UInt64) : (n % 64).toNat < 64 := by
  rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide)

theorem evalValue_mod_shl_u32 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x n : String) (vx vn : UInt32)
    (hx : env.lookup x = some (.u32 vx)) (hn : env.lookup n = some (.u32 vn)) :
    evalValue fns globals fuel env h
      (.op .u32 "<<" (.var .u32 x) (.op .u32 "%" (.var .u32 n) (.num .i32 32))) =
    .ok (.u32 (vx <<< vn), env, h) := by
  have hcast32 : evalCast .u32 (.i32 32) = .ok (.u32 32) := evalCast_u32_i32_of_nat 32 (by decide)
  have hz32 : ((32 : UInt32) == 0) = false := by decide
  have hmod : evalValue fns globals fuel env h (.op .u32 "%" (.var .u32 n) (.num .i32 32)) =
      .ok (.u32 (vn % 32), env, h) := by
    refine evalValue_op fns globals fuel env env env h h h .u32 "%" _ _ (.u32 vn) (.i32 32) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hn) (evalValue_num _ _ _ _ _ .i32 32 (.i32 32) rfl) ?_
    unfold evalBinOp
    simp only [show ("%" == "<<" || "%" == ">>") = false from rfl,
      show ["<", "<=", ">", ">=", "==", "!="].contains "%" = false from rfl,
      Bool.false_or, hz32, bool_if_false, evalCast_u32_self, hcast32,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine evalValue_op fns globals fuel env env env h h h .u32 "<<" _ _ (.u32 vx) (.u32 (vn % 32)) _
    rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx) hmod ?_
  have hlt : (vn % 32).toNat < 32 := mod_lt_32 vn
  have hb : (decide (Int.ofNat (vn % 32).toNat < 0) ||
      decide (Int.ofNat (if (32 : Nat) < 32 then 32 else 32) ≤ Int.ofNat (vn % 32).toNat)) = false := by
    rw [effWidth_32]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "<<" = false from rfl,
    show ("<<" == "<<" || "<<" == ">>") = true from rfl,
    bitWidth?, CVal.toInt?, hb, Bool.false_or, bool_if_false, evalCast_u32_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  change Except.ok (CVal.u32 (vx <<< UInt32.ofNat (vn % 32).toNat)) = Except.ok (CVal.u32 (vx <<< vn))
  rw [uint32_shl_mod]

theorem evalValue_mod_shr_u32 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x n : String) (vx vn : UInt32)
    (hx : env.lookup x = some (.u32 vx)) (hn : env.lookup n = some (.u32 vn)) :
    evalValue fns globals fuel env h
      (.op .u32 ">>" (.var .u32 x) (.op .u32 "%" (.var .u32 n) (.num .i32 32))) =
    .ok (.u32 (vx >>> vn), env, h) := by
  have hcast32 : evalCast .u32 (.i32 32) = .ok (.u32 32) := evalCast_u32_i32_of_nat 32 (by decide)
  have hz32 : ((32 : UInt32) == 0) = false := by decide
  have hmod : evalValue fns globals fuel env h (.op .u32 "%" (.var .u32 n) (.num .i32 32)) =
      .ok (.u32 (vn % 32), env, h) := by
    refine evalValue_op fns globals fuel env env env h h h .u32 "%" _ _ (.u32 vn) (.i32 32) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hn) (evalValue_num _ _ _ _ _ .i32 32 (.i32 32) rfl) ?_
    unfold evalBinOp
    simp only [show ("%" == "<<" || "%" == ">>") = false from rfl,
      show ["<", "<=", ">", ">=", "==", "!="].contains "%" = false from rfl,
      Bool.false_or, hz32, bool_if_false, evalCast_u32_self, hcast32,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine evalValue_op fns globals fuel env env env h h h .u32 ">>" _ _ (.u32 vx) (.u32 (vn % 32)) _
    rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx) hmod ?_
  have hlt : (vn % 32).toNat < 32 := mod_lt_32 vn
  have hb : (decide (Int.ofNat (vn % 32).toNat < 0) ||
      decide (Int.ofNat (if (32 : Nat) < 32 then 32 else 32) ≤ Int.ofNat (vn % 32).toNat)) = false := by
    rw [effWidth_32]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains ">>" = false from rfl,
    show (">>" == "<<") = false from rfl, show (">>" == ">>") = true from rfl,
    bitWidth?, CVal.toInt?, hb, Bool.false_or, bool_if_false, evalCast_u32_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  change Except.ok (CVal.u32 (vx >>> UInt32.ofNat (vn % 32).toNat)) = Except.ok (CVal.u32 (vx >>> vn))
  rw [uint32_shr_mod]

theorem evalValue_mod_shl_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x n : String) (vx vn : UInt64)
    (hx : env.lookup x = some (.u64 vx)) (hn : env.lookup n = some (.u64 vn)) :
    evalValue fns globals fuel env h
      (.op .u64 "<<" (.var .u64 x) (.op .u64 "%" (.var .u64 n) (.num .i32 64))) =
    .ok (.u64 (vx <<< vn), env, h) := by
  have hcast64 : evalCast .u64 (.i32 64) = .ok (.u64 64) := evalCast_u64_i32_of_nat 64 (by decide)
  have hz64 : ((64 : UInt64) == 0) = false := by decide
  have hmod : evalValue fns globals fuel env h (.op .u64 "%" (.var .u64 n) (.num .i32 64)) =
      .ok (.u64 (vn % 64), env, h) := by
    refine evalValue_op fns globals fuel env env env h h h .u64 "%" _ _ (.u64 vn) (.i32 64) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hn) (evalValue_num _ _ _ _ _ .i32 64 (.i32 64) rfl) ?_
    unfold evalBinOp
    simp only [show ("%" == "<<" || "%" == ">>") = false from rfl,
      show ["<", "<=", ">", ">=", "==", "!="].contains "%" = false from rfl,
      Bool.false_or, hz64, bool_if_false, evalCast_u64_self, hcast64,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine evalValue_op fns globals fuel env env env h h h .u64 "<<" _ _ (.u64 vx) (.u64 (vn % 64)) _
    rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx) hmod ?_
  have hlt : (vn % 64).toNat < 64 := mod_lt_64 vn
  have hb : (decide (Int.ofNat (vn % 64).toNat < 0) ||
      decide (Int.ofNat (if (64 : Nat) < 32 then 32 else 64) ≤ Int.ofNat (vn % 64).toNat)) = false := by
    rw [effWidth_64]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "<<" = false from rfl,
    show ("<<" == "<<" || "<<" == ">>") = true from rfl,
    bitWidth?, CVal.toInt?, hb, Bool.false_or, bool_if_false, evalCast_u64_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  change Except.ok (CVal.u64 (vx <<< UInt64.ofNat (vn % 64).toNat)) = Except.ok (CVal.u64 (vx <<< vn))
  rw [uint64_shl_mod]

theorem evalValue_mod_shr_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x n : String) (vx vn : UInt64)
    (hx : env.lookup x = some (.u64 vx)) (hn : env.lookup n = some (.u64 vn)) :
    evalValue fns globals fuel env h
      (.op .u64 ">>" (.var .u64 x) (.op .u64 "%" (.var .u64 n) (.num .i32 64))) =
    .ok (.u64 (vx >>> vn), env, h) := by
  have hcast64 : evalCast .u64 (.i32 64) = .ok (.u64 64) := evalCast_u64_i32_of_nat 64 (by decide)
  have hz64 : ((64 : UInt64) == 0) = false := by decide
  have hmod : evalValue fns globals fuel env h (.op .u64 "%" (.var .u64 n) (.num .i32 64)) =
      .ok (.u64 (vn % 64), env, h) := by
    refine evalValue_op fns globals fuel env env env h h h .u64 "%" _ _ (.u64 vn) (.i32 64) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hn) (evalValue_num _ _ _ _ _ .i32 64 (.i32 64) rfl) ?_
    unfold evalBinOp
    simp only [show ("%" == "<<" || "%" == ">>") = false from rfl,
      show ["<", "<=", ">", ">=", "==", "!="].contains "%" = false from rfl,
      Bool.false_or, hz64, bool_if_false, evalCast_u64_self, hcast64,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine evalValue_op fns globals fuel env env env h h h .u64 ">>" _ _ (.u64 vx) (.u64 (vn % 64)) _
    rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx) hmod ?_
  have hlt : (vn % 64).toNat < 64 := mod_lt_64 vn
  have hb : (decide (Int.ofNat (vn % 64).toNat < 0) ||
      decide (Int.ofNat (if (64 : Nat) < 32 then 32 else 64) ≤ Int.ofNat (vn % 64).toNat)) = false := by
    rw [effWidth_64]
    simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  unfold evalBinOp evalShiftOp
  simp only [show ["<", "<=", ">", ">=", "==", "!="].contains ">>" = false from rfl,
    show (">>" == "<<") = false from rfl, show (">>" == ">>") = true from rfl,
    bitWidth?, CVal.toInt?, hb, Bool.false_or, bool_if_false, evalCast_u64_self,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  change Except.ok (CVal.u64 (vx >>> UInt64.ofNat (vn % 64).toNat)) = Except.ok (CVal.u64 (vx >>> vn))
  rw [uint64_shr_mod]

theorem evalValue_guarded_shr_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x n : String) (vx vn : UInt64) (fb : Value)
    (vfb : CVal) (env' : CEnv) (h' : C.Heap)
    (hx : env.lookup x = some (.u64 vx)) (hn : env.lookup n = some (.u64 vn))
    (hfb : evalValue fns globals fuel env h fb = .ok (vfb, env', h')) :
    evalValue fns globals fuel env h
      (.choose (.op .bool "<" (.var .u64 n) (.num .i32 64))
        (.op .u64 ">>" (.var .u64 x) (.var .u64 n)) fb) =
    if vn < 64 then .ok (.u64 (vx >>> vn), env, h) else .ok (vfb, env', h') := by
  have hi64 : (Int32.ofNat 64).toInt = 64 := int32_toInt_ofNat_lt 64 (by decide)
  have hu64 : (UInt64.ofInt 64 : UInt64) = 64 := rfl
  have hcond : evalValue fns globals fuel env h (.op .bool "<" (.var .u64 n) (.num .i32 64)) =
      .ok (.bool (decide (vn < 64)), env, h) := by
    refine evalValue_op fns globals fuel env env env h h h .bool "<" _ _ (.u64 vn) (.i32 64) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hn) (evalValue_num _ _ _ _ _ .i32 64 (.i32 64) rfl) ?_
    unfold evalBinOp evalRelOp
    simp only [CVal.toInt?, Bind.bind, Except.bind, Pure.pure, Except.pure]
    change Except.ok (CVal.bool (decide (vn < UInt64.ofInt (Int32.ofNat 64).toInt))) =
      Except.ok (CVal.bool (decide (vn < 64)))
    rw [hi64, hu64]
  by_cases hlt : vn < 64
  · simp only [hlt, ite_true]
    have hnat : vn.toNat < 64 := UInt64.lt_iff_toNat_lt.mp hlt
    have hof : UInt64.ofNat vn.toNat = vn := UInt64.ofNat_toNat
    have hb : (decide (Int.ofNat vn.toNat < 0) ||
        decide (Int.ofNat (if (64 : Nat) < 32 then 32 else 64) ≤ Int.ofNat vn.toNat)) = false := by
      rw [effWidth_64]
      simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hshr : evalValue fns globals fuel env h (.op .u64 ">>" (.var .u64 x) (.var .u64 n)) =
        .ok (.u64 (vx >>> vn), env, h) := by
      refine evalValue_op fns globals fuel env env env h h h .u64 ">>" _ _ (.u64 vx) (.u64 vn) _
        rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx) (evalValue_var _ _ _ _ _ _ _ _ hn) ?_
      unfold evalBinOp evalShiftOp
      simp only [show ["<", "<=", ">", ">=", "==", "!="].contains ">>" = false from rfl,
        show (">>" == "<<") = false from rfl, show (">>" == ">>") = true from rfl,
        bitWidth?, CVal.toInt?, hb, Bool.false_or, bool_if_false, evalCast_u64_self,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      change Except.ok (CVal.u64 (vx >>> UInt64.ofNat vn.toNat)) = Except.ok (CVal.u64 (vx >>> vn))
      rw [hof]
    exact evalValue_choose_t fns globals fuel env env env h h h _ _ _ _ _
      hcond (by simp [CVal.toBool?, hlt]) hshr
  · simp only [hlt, ite_false]
    exact evalValue_choose_f fns globals fuel env env env' h h h' _ _ _ _ _
      hcond (by simp [CVal.toBool?, hlt]) hfb

theorem evalValue_guarded_shl_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x n : String) (vx vn : UInt64) (fb : Value)
    (vfb : CVal) (env' : CEnv) (h' : C.Heap)
    (hx : env.lookup x = some (.u64 vx)) (hn : env.lookup n = some (.u64 vn))
    (hfb : evalValue fns globals fuel env h fb = .ok (vfb, env', h')) :
    evalValue fns globals fuel env h
      (.choose (.op .bool "<" (.var .u64 n) (.num .i32 64))
        (.op .u64 "<<" (.var .u64 x) (.var .u64 n)) fb) =
    if vn < 64 then .ok (.u64 (vx <<< vn), env, h) else .ok (vfb, env', h') := by
  have hi64 : (Int32.ofNat 64).toInt = 64 := int32_toInt_ofNat_lt 64 (by decide)
  have hu64 : (UInt64.ofInt 64 : UInt64) = 64 := rfl
  have hcond : evalValue fns globals fuel env h (.op .bool "<" (.var .u64 n) (.num .i32 64)) =
      .ok (.bool (decide (vn < 64)), env, h) := by
    refine evalValue_op fns globals fuel env env env h h h .bool "<" _ _ (.u64 vn) (.i32 64) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hn) (evalValue_num _ _ _ _ _ .i32 64 (.i32 64) rfl) ?_
    unfold evalBinOp evalRelOp
    simp only [CVal.toInt?, Bind.bind, Except.bind, Pure.pure, Except.pure]
    change Except.ok (CVal.bool (decide (vn < UInt64.ofInt (Int32.ofNat 64).toInt))) =
      Except.ok (CVal.bool (decide (vn < 64)))
    rw [hi64, hu64]
  by_cases hlt : vn < 64
  · simp only [hlt, ite_true]
    have hnat : vn.toNat < 64 := UInt64.lt_iff_toNat_lt.mp hlt
    have hof : UInt64.ofNat vn.toNat = vn := UInt64.ofNat_toNat
    have hb : (decide (Int.ofNat vn.toNat < 0) ||
        decide (Int.ofNat (if (64 : Nat) < 32 then 32 else 64) ≤ Int.ofNat vn.toNat)) = false := by
      rw [effWidth_64]
      simp only [Int.ofNat_eq_natCast, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hshl : evalValue fns globals fuel env h (.op .u64 "<<" (.var .u64 x) (.var .u64 n)) =
        .ok (.u64 (vx <<< vn), env, h) := by
      refine evalValue_op fns globals fuel env env env h h h .u64 "<<" _ _ (.u64 vx) (.u64 vn) _
        rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx) (evalValue_var _ _ _ _ _ _ _ _ hn) ?_
      unfold evalBinOp evalShiftOp
      simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "<<" = false from rfl,
        show ("<<" == "<<" || "<<" == ">>") = true from rfl,
        bitWidth?, CVal.toInt?, hb, Bool.false_or, bool_if_false, evalCast_u64_self,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      change Except.ok (CVal.u64 (vx <<< UInt64.ofNat vn.toNat)) = Except.ok (CVal.u64 (vx <<< vn))
      rw [hof]
    exact evalValue_choose_t fns globals fuel env env env h h h _ _ _ _ _
      hcond (by simp [CVal.toBool?, hlt]) hshl
  · simp only [hlt, ite_false]
    exact evalValue_choose_f fns globals fuel env env env' h h h' _ _ _ _ _
      hcond (by simp [CVal.toBool?, hlt]) hfb

/-! ## 2. Heap load/store and counted loop simulation -/

theorem evalValue_load_u8 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (ptrExpr : Value) (p : C.BPtr) (v : UInt8)
    (hp : evalValue fns globals fuel env h ptrExpr = .ok (.ptr p, env1, h1))
    (hload : C.load8 p h1 = .ok (v, h1)) :
    evalValue fns globals fuel env h (.load .u8 ptrExpr) = .ok (.u8 v, env1, h1) := by
  unfold evalValue
  simp only [hp, readHeap, hload, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem evalValue_load_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 : CEnv) (h h1 : C.Heap) (ptrExpr : Value) (p : C.BPtr) (v : UInt64)
    (hp : evalValue fns globals fuel env h ptrExpr = .ok (.ptr p, env1, h1))
    (hload : C.load64 p h1 = .ok (v, h1)) :
    evalValue fns globals fuel env h (.load .u64 ptrExpr) = .ok (.u64 v, env1, h1) := by
  unfold evalValue
  simp only [hp, readHeap, hload, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem execStmt_store_u8 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 env2 : CEnv) (h h1 h2 h3 : C.Heap) (ptrExpr rhs : Value) (p : C.BPtr) (v : UInt8)
    (hp : evalValue fns globals fuel env h ptrExpr = .ok (.ptr p, env1, h1))
    (hr : evalValue fns globals fuel env1 h1 rhs = .ok (.u8 v, env2, h2))
    (hstore : C.store8 p v h2 = .ok ((), h3)) :
    execStmt fns globals fuel env h (.assign (.load .u8 ptrExpr) rhs) = .next env2 h3 := by
  unfold execStmt
  simp only [hp, hr, writeHeap, evalCast, CVal.toInt?, ofIntForTy, Int.ofNat_eq_natCast,
    uint8_ofInt_toNat, hstore, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem execStmt_store_u64 (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env env1 env2 : CEnv) (h h1 h2 h3 : C.Heap) (ptrExpr rhs : Value) (p : C.BPtr) (v : UInt64)
    (hp : evalValue fns globals fuel env h ptrExpr = .ok (.ptr p, env1, h1))
    (hr : evalValue fns globals fuel env1 h1 rhs = .ok (.u64 v, env2, h2))
    (hstore : C.store64 p v h2 = .ok ((), h3)) :
    execStmt fns globals fuel env h (.assign (.load .u64 ptrExpr) rhs) = .next env2 h3 := by
  unfold execStmt
  simp only [hp, hr, writeHeap, evalCast, CVal.toInt?, ofIntForTy, Int.ofNat_eq_natCast,
    uint64_ofInt_toNat, hstore, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem execStmt_while_sim {σ : Type} (fns : FnTable) (globals : CEnv)
    (cond : Value) (body : List Stmt) (mCond : σ → C.M (Bool × σ)) (mBody : σ → C.M σ)
    (R : CEnv → σ → C.Heap → Prop)
    (hstep : ∀ k env s h, R env s h →
      ∃ b env1 h1 s1, evalValue fns globals k env h cond = .ok (.bool b, env1, h1) ∧
        mCond s h = .ok ((b, s1), h1) ∧
        (b = false → R env1 s1 h1) ∧
        (b = true → ∃ env2 h2 s2,
          execStmts fns globals k env1 h1 body = .next env2 h2 ∧
          mBody s1 h1 = .ok (s2, h2) ∧ R env2 s2 h2)) :
    ∀ n env s h, R env s h →
      ∀ s' h', C.cwhile.go mCond mBody n s h = .ok (s', h') →
        ∃ env', execStmt fns globals n env h (.loop cond body) = .next env' h' ∧ R env' s' h' := by
  intro n
  induction n with
  | zero =>
    intro env s h _ s' h' hrun
    simp [C.cwhile.go] at hrun
  | succ n ih =>
    intro env s h hR s' h' hrun
    obtain ⟨b, env1, h1, s1, hcond, hmcond, hfalse, htrue⟩ := hstep n env s h hR
    cases b with
    | false =>
      simp [C.cwhile.go, hmcond] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨env1, by simp [execStmt, hcond, CVal.toBool?], hfalse rfl⟩
    | true =>
      obtain ⟨env2, h2, s2, hbody, hmbody, hR2⟩ := htrue rfl
      simp [C.cwhile.go, hmcond, hmbody] at hrun
      obtain ⟨env', hexec, hR'⟩ := ih env2 s2 h2 hR2 s' h' hrun
      exact ⟨env', by simp [execStmt, hcond, CVal.toBool?, hbody, hexec], hR'⟩

theorem execStmt_doWhile_sim {σ : Type} (fns : FnTable) (globals : CEnv)
    (body : List Stmt) (cond : Value) (mBody : σ → C.M σ) (mCond : σ → C.M (Bool × σ))
    (R : CEnv → σ → C.Heap → Prop)
    (hstep : ∀ k env s h, R env s h →
      ∃ env1 h1 s1 b env2 h2 s2,
        execStmts fns globals k env h body = .next env1 h1 ∧
        mBody s h = .ok (s1, h1) ∧
        evalValue fns globals k env1 h1 cond = .ok (.bool b, env2, h2) ∧
        mCond s1 h1 = .ok ((b, s2), h2) ∧
        R env2 s2 h2) :
    ∀ n env s h, R env s h →
      ∀ s' h', C.cdoWhile.go mBody mCond n s h = .ok (s', h') →
        ∃ env', execStmt fns globals n env h (.doLoop body cond) = .next env' h' ∧ R env' s' h' := by
  intro n
  induction n with
  | zero =>
    intro env s h _ s' h' hrun
    simp [C.cdoWhile.go] at hrun
  | succ n ih =>
    intro env s h hR s' h' hrun
    obtain ⟨env1, h1, s1, b, env2, h2, s2, hbody, hmbody, hcond, hmcond, hR2⟩ := hstep n env s h hR
    cases b with
    | false =>
      simp [C.cdoWhile.go, hmbody, hmcond] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨env2, by simp [execStmt, hbody, hcond, CVal.toBool?], hR2⟩
    | true =>
      simp [C.cdoWhile.go, hmbody, hmcond] at hrun
      obtain ⟨env', hexec, hR'⟩ := ih env2 s2 h2 hR2 s' h' hrun
      exact ⟨env', by simp [execStmt, hbody, hcond, CVal.toBool?, hexec], hR'⟩

/-! ## 3. Exact lowered C ASTs for `compressBound_z`, `compressBound`, `zlibCompileFlags`, `byte_swap`, and `adler32_combine_` -/

/-- Exact lowered AST of `Zlib.Compress.compressBound_z` (`abi := false`). -/
def compressBound_z_c : List (String × Ty) × List Stmt :=
  ([("sourceLen", .u64)],
   [Stmt.decl .u64 "bound"
      (some (.op .u64 "+"
        (.op .u64 "+"
          (.op .u64 "+"
            (.op .u64 "+" (.var .u64 "sourceLen")
              (.op .u64 ">>" (.var .u64 "sourceLen") (.num .i32 12)))
            (.op .u64 ">>" (.var .u64 "sourceLen") (.num .i32 14)))
          (.op .u64 ">>" (.var .u64 "sourceLen") (.num .i32 25)))
        (.num .u64 13))),
    Stmt.branch (.op .bool "<" (.var .u64 "bound") (.var .u64 "sourceLen"))
      [Stmt.ret (.num .u64 18446744073709551615)]
      [Stmt.ret (.var .u64 "bound")]])

/-- Exact lowered AST of `Zlib.Compress.compressBound` (`abi := true`). -/
def compressBound_c : List (String × Ty) × List Stmt :=
  ([("sourceLen", .u64)],
   [Stmt.ret (.call .u64 "compressBound_z" [.var .u64 "sourceLen"])])

/-- Exact lowered AST of `Zlib.Zutil.zlibCompileFlags` (`abi := true`). -/
def zlibCompileFlags_c : List (String × Ty) × List Stmt :=
  ([],
   [Stmt.decl .u64 "flags" (some (.num .u64 0)),
    Stmt.decl .i32 "sz" (some (.num .i32 4)),
    Stmt.decl .u64 "flags_0"
      (some (.choose (.op .bool "==" (.var .i32 "sz") (.num .i32 2)) (.var .u64 "flags")
        (.choose (.op .bool "==" (.var .i32 "sz") (.num .i32 4)) (.op .u64 "+" (.var .u64 "flags") (.num .u64 1))
          (.choose (.op .bool "==" (.var .i32 "sz") (.num .i32 8)) (.op .u64 "+" (.var .u64 "flags") (.num .u64 2))
            (.op .u64 "+" (.var .u64 "flags") (.num .u64 3)))))),
    Stmt.decl .i32 "sz_0" (some (.num .i32 8)),
    Stmt.decl .u64 "flags_1"
      (some (.choose (.op .bool "==" (.var .i32 "sz_0") (.num .i32 2)) (.var .u64 "flags_0")
        (.choose (.op .bool "==" (.var .i32 "sz_0") (.num .i32 4))
          (.op .u64 "+" (.var .u64 "flags_0") (.op .u64 "<<" (.num .u64 1) (.num .i32 2)))
          (.choose (.op .bool "==" (.var .i32 "sz_0") (.num .i32 8))
            (.op .u64 "+" (.var .u64 "flags_0") (.op .u64 "<<" (.num .u64 2) (.num .i32 2)))
            (.op .u64 "+" (.var .u64 "flags_0") (.op .u64 "<<" (.num .u64 3) (.num .i32 2))))))),
    Stmt.decl .i32 "sz_1" (some (.num .i32 8)),
    Stmt.decl .u64 "flags_2"
      (some (.choose (.op .bool "==" (.var .i32 "sz_1") (.num .i32 2)) (.var .u64 "flags_1")
        (.choose (.op .bool "==" (.var .i32 "sz_1") (.num .i32 4))
          (.op .u64 "+" (.var .u64 "flags_1") (.op .u64 "<<" (.num .u64 1) (.num .i32 4)))
          (.choose (.op .bool "==" (.var .i32 "sz_1") (.num .i32 8))
            (.op .u64 "+" (.var .u64 "flags_1") (.op .u64 "<<" (.num .u64 2) (.num .i32 4)))
            (.op .u64 "+" (.var .u64 "flags_1") (.op .u64 "<<" (.num .u64 3) (.num .i32 4))))))),
    Stmt.decl .i32 "sz_2" (some (.num .i32 8)),
    Stmt.decl .u64 "flags_3"
      (some (.choose (.op .bool "==" (.var .i32 "sz_2") (.num .i32 2)) (.var .u64 "flags_2")
        (.choose (.op .bool "==" (.var .i32 "sz_2") (.num .i32 4))
          (.op .u64 "+" (.var .u64 "flags_2") (.op .u64 "<<" (.num .u64 1) (.num .i32 6)))
          (.choose (.op .bool "==" (.var .i32 "sz_2") (.num .i32 8))
            (.op .u64 "+" (.var .u64 "flags_2") (.op .u64 "<<" (.num .u64 2) (.num .i32 6)))
            (.op .u64 "+" (.var .u64 "flags_2") (.op .u64 "<<" (.num .u64 3) (.num .i32 6))))))),
    Stmt.ret (.var .u64 "flags_3")])

/-- Exact lowered AST of `Zlib.Crc32.byte_swap` (`abi := false`). -/
def byte_swap_c : List (String × Ty) × List Stmt :=
  ([("word", .u32)],
   [Stmt.ret
      (.op .u32 "|"
        (.op .u32 "|"
          (.op .u32 "|"
            (.op .u32 ">>" (.op .u32 "&" (.var .u32 "word") (.num .u32 4278190080)) (.num .i32 24))
            (.op .u32 ">>" (.op .u32 "&" (.var .u32 "word") (.num .i32 16711680)) (.num .i32 8)))
          (.op .u32 "<<" (.op .u32 "&" (.var .u32 "word") (.num .i32 65280)) (.num .i32 8)))
        (.op .u32 "<<" (.op .u32 "&" (.var .u32 "word") (.num .i32 255)) (.num .i32 24)))])

/-- Exact lowered AST of `Zlib.Adler32.adler32_combine_` (`abi := true`). -/
def adler32_combine_c : List (String × Ty) × List Stmt :=
  ([("adler1", .u64), ("adler2", .u64), ("len2", .i64)],
   [Stmt.branch (.op .bool "<" (.var .i64 "len2") (.num .i64 0))
      [Stmt.ret (.num .u64 4294967295)]
      [Stmt.decl .i64 "len2_0" (some (.op .i64 "%" (.var .i64 "len2") (.num .i64 65521))),
       Stmt.decl .u32 "rem" (some (.cast .u32 (.cast .u64 (.var .i64 "len2_0")))),
       Stmt.decl .u64 "sum1" (some (.op .u64 "&" (.var .u64 "adler1") (.num .i32 65535))),
       Stmt.decl .u64 "sum2"
         (some (.op .u64 "*" (.cast .u64 (.var .u32 "rem")) (.var .u64 "sum1"))),
       Stmt.decl .u64 "sum2_0" (some (.op .u64 "%" (.var .u64 "sum2") (.var .u64 "BASE"))),
       Stmt.decl .u64 "sum1_0"
         (some (.op .u64 "+" (.var .u64 "sum1")
           (.op .u64 "-"
             (.op .u64 "+" (.op .u64 "&" (.var .u64 "adler2") (.num .i32 65535)) (.var .u64 "BASE"))
             (.num .u64 1)))),
       Stmt.decl .u64 "sum2_1"
         (some (.op .u64 "+" (.var .u64 "sum2_0")
           (.op .u64 "-"
             (.op .u64 "+"
               (.op .u64 "+"
                 (.op .u64 "&" (.op .u64 ">>" (.var .u64 "adler1") (.num .i32 16)) (.num .i32 65535))
                 (.op .u64 "&" (.op .u64 ">>" (.var .u64 "adler2") (.num .i32 16)) (.num .i32 65535)))
               (.var .u64 "BASE"))
             (.cast .u64 (.var .u32 "rem"))))),
       Stmt.decl .u64 "sum1_1" (some (.var .u64 "sum1_0")),
       Stmt.decl .u64 "sum1_2" none,
       Stmt.branch (.op .bool ">=" (.var .u64 "sum1_1") (.var .u64 "BASE"))
         [Stmt.assign (.var .u64 "sum1_2") (.op .u64 "-" (.var .u64 "sum1_1") (.var .u64 "BASE"))]
         [Stmt.assign (.var .u64 "sum1_2") (.var .u64 "sum1_1")],
       Stmt.decl .u64 "sum1_3" none,
       Stmt.branch (.op .bool ">=" (.var .u64 "sum1_2") (.var .u64 "BASE"))
         [Stmt.assign (.var .u64 "sum1_3") (.op .u64 "-" (.var .u64 "sum1_2") (.var .u64 "BASE"))]
         [Stmt.assign (.var .u64 "sum1_3") (.var .u64 "sum1_2")],
       Stmt.decl .u64 "sum2_2" (some (.var .u64 "sum2_1")),
       Stmt.decl .u64 "sum2_3" none,
       Stmt.branch (.op .bool ">=" (.var .u64 "sum2_2") (.op .u64 "<<" (.var .u64 "BASE") (.num .i32 1)))
         [Stmt.assign (.var .u64 "sum2_3")
           (.op .u64 "-" (.var .u64 "sum2_2") (.op .u64 "<<" (.var .u64 "BASE") (.num .i32 1)))]
         [Stmt.assign (.var .u64 "sum2_3") (.var .u64 "sum2_2")],
       Stmt.decl .u64 "sum2_4" none,
       Stmt.branch (.op .bool ">=" (.var .u64 "sum2_3") (.var .u64 "BASE"))
         [Stmt.assign (.var .u64 "sum2_4") (.op .u64 "-" (.var .u64 "sum2_3") (.var .u64 "BASE"))]
         [Stmt.assign (.var .u64 "sum2_4") (.var .u64 "sum2_3")],
       Stmt.ret
         (.op .u64 "|" (.var .u64 "sum1_3") (.op .u64 "<<" (.var .u64 "sum2_4") (.num .i32 16)))]])

/-! ## 4. End-to-end `runCFn` soundness and UB-freedom theorems -/

private theorem eval_u64_const_shift_r (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x : String) (vx : UInt64) (k : Nat) (hk : k < 64)
    (hx : env.lookup x = some (.u64 vx)) :
    evalValue fns globals fuel env h (.op .u64 ">>" (.var .u64 x) (.num .i32 k)) =
      .ok (.u64 (vx >>> UInt64.ofNat k), env, h) :=
  evalValue_op fns globals fuel env env env h h h .u64 ">>" _ _ (.u64 vx) (.i32 (Int32.ofNat k)) _
    rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx)
    (evalValue_num _ _ _ _ _ .i32 k (.i32 (Int32.ofNat k)) (by simp [evalNum, show k < 2 ^ 31 by omega]))
    (evalBinOp_u64_shr vx k hk h)

private theorem eval_u64_var_shift_l (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (x : String) (vx : UInt64) (k : Nat) (hk : k < 64)
    (hx : env.lookup x = some (.u64 vx)) :
    evalValue fns globals fuel env h (.op .u64 "<<" (.var .u64 x) (.num .i32 k)) =
      .ok (.u64 (vx <<< UInt64.ofNat k), env, h) :=
  evalValue_op fns globals fuel env env env h h h .u64 "<<" _ _ (.u64 vx) (.i32 (Int32.ofNat k)) _
    rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx)
    (evalValue_num _ _ _ _ _ .i32 k (.i32 (Int32.ofNat k)) (by simp [evalNum, show k < 2 ^ 31 by omega]))
    (evalBinOp_u64_shl vx k hk h)

private theorem eval_u64_add (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (e1 e2 : Value) (v1 v2 : UInt64)
    (h1 : evalValue fns globals fuel env h e1 = .ok (.u64 v1, env, h))
    (h2 : evalValue fns globals fuel env h e2 = .ok (.u64 v2, env, h)) :
    evalValue fns globals fuel env h (.op .u64 "+" e1 e2) = .ok (.u64 (v1 + v2), env, h) :=
  evalValue_op fns globals fuel env env env h h h .u64 "+" e1 e2 (.u64 v1) (.u64 v2) _
    rfl rfl h1 h2 (evalBinOp_u64_add v1 v2 h)

private theorem eval_u64_sub (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (e1 e2 : Value) (v1 v2 : UInt64)
    (h1 : evalValue fns globals fuel env h e1 = .ok (.u64 v1, env, h))
    (h2 : evalValue fns globals fuel env h e2 = .ok (.u64 v2, env, h)) :
    evalValue fns globals fuel env h (.op .u64 "-" e1 e2) = .ok (.u64 (v1 - v2), env, h) :=
  evalValue_op fns globals fuel env env env h h h .u64 "-" e1 e2 (.u64 v1) (.u64 v2) _
    rfl rfl h1 h2 (evalBinOp_u64_sub v1 v2 h)

private theorem eval_u64_ge (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (env : CEnv) (h : C.Heap) (e1 e2 : Value) (v1 v2 : UInt64)
    (h1 : evalValue fns globals fuel env h e1 = .ok (.u64 v1, env, h))
    (h2 : evalValue fns globals fuel env h e2 = .ok (.u64 v2, env, h)) :
    evalValue fns globals fuel env h (.op .bool ">=" e1 e2) = .ok (.bool (decide (v2 ≤ v1)), env, h) := by
  refine evalValue_op fns globals fuel env env env h h h .bool ">=" e1 e2 (.u64 v1) (.u64 v2) _
    rfl rfl h1 h2 ?_
  unfold evalBinOp evalRelOp
  simp only [CVal.toInt?, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

/-- `compressBound_z_c` runs to return on all inputs with zero C99 UB and agrees with
`Zlib.Compress.compressBound_z`. -/
theorem compressBound_z_c_sound (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (sourceLen : UInt64) (h : C.Heap) :
    runCFn fns globals fuel compressBound_z_c [.u64 sourceLen] h =
      .ret (.u64 (Zlib.Compress.compressBound_z sourceLen)) h := by
  let env0 : CEnv := [("sourceLen", .u64 sourceLen)]
  let b : UInt64 := sourceLen + (sourceLen >>> 12) + (sourceLen >>> 14) + (sourceLen >>> 25) + 13
  let env1 : CEnv := [("sourceLen", .u64 sourceLen), ("bound", .u64 b)]
  have hbind : bindParams compressBound_z_c.1 [.u64 sourceLen] = .ok env0 := by
    simp [compressBound_z_c, bindParams, Bind.bind, Except.bind, Pure.pure, Except.pure, env0]
  have hs0 : evalValue fns globals fuel env0 h (.var .u64 "sourceLen") = .ok (.u64 sourceLen, env0, h) :=
    evalValue_var _ _ _ _ _ _ _ _ rfl
  have hs12 := eval_u64_const_shift_r fns globals fuel env0 h "sourceLen" sourceLen 12 (by decide) rfl
  have hs14 := eval_u64_const_shift_r fns globals fuel env0 h "sourceLen" sourceLen 14 (by decide) rfl
  have hs25 := eval_u64_const_shift_r fns globals fuel env0 h "sourceLen" sourceLen 25 (by decide) rfl
  have h13 : evalValue fns globals fuel env0 h (.num .u64 13) = .ok (.u64 13, env0, h) :=
    evalValue_num _ _ _ _ _ .u64 13 (.u64 13) rfl
  have hbound : evalValue fns globals fuel env0 h
      (.op .u64 "+" (.op .u64 "+" (.op .u64 "+" (.op .u64 "+" (.var .u64 "sourceLen")
        (.op .u64 ">>" (.var .u64 "sourceLen") (.num .i32 12)))
        (.op .u64 ">>" (.var .u64 "sourceLen") (.num .i32 14)))
        (.op .u64 ">>" (.var .u64 "sourceLen") (.num .i32 25))) (.num .u64 13)) =
      .ok (.u64 b, env0, h) :=
    eval_u64_add _ _ _ _ _ _ _ _ _
      (eval_u64_add _ _ _ _ _ _ _ _ _
        (eval_u64_add _ _ _ _ _ _ _ _ _
          (eval_u64_add _ _ _ _ _ _ _ _ _ hs0 hs12) hs14) hs25) h13
  have hb_look : env1.lookup "bound" = some (.u64 b) := rfl
  have hs_look : env1.lookup "sourceLen" = some (.u64 sourceLen) := rfl
  have hcmp : evalValue fns globals fuel env1 h (.op .bool "<" (.var .u64 "bound") (.var .u64 "sourceLen")) =
      .ok (.bool (decide (b < sourceLen)), env1, h) := by
    refine evalValue_op fns globals fuel env1 env1 env1 h h h .bool "<" _ _ (.u64 b) (.u64 sourceLen) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hb_look) (evalValue_var _ _ _ _ _ _ _ _ hs_look) ?_
    unfold evalBinOp evalRelOp
    simp only [CVal.toInt?, Bind.bind, Except.bind, Pure.pure, Except.pure]; rfl
  unfold runCFn
  rw [hbind]
  dsimp only [compressBound_z_c]
  rw [execStmts_decl_some fns globals fuel env0 env0 h h .u64 "bound" _ (.u64 b) (.u64 b) _
    hbound evalCast_u64_self]
  change execStmts fns globals fuel env1 h _ = _
  unfold Zlib.Compress.compressBound_z
  by_cases hlt : b < sourceLen
  · rw [execStmts_branch_t fns globals fuel env1 env1 h h _ _ _ _ _ hcmp (by simp [CVal.toBool?, hlt])]
    rw [execStmts_ret fns globals fuel env1 env1 h h _ _ []
      (evalValue_num _ _ _ _ _ .u64 18446744073709551615 (.u64 18446744073709551615) rfl)]
    simp [hlt, b]
  · rw [execStmts_branch_f fns globals fuel env1 env1 h h _ _ _ _ _ hcmp (by simp [CVal.toBool?, hlt])]
    rw [execStmts_ret fns globals fuel env1 env1 h h _ _ [] (evalValue_var _ _ _ _ _ _ _ _ hb_look)]
    simp [hlt, b]

/-- `compressBound_c` runs to return with zero C99 UB when linked against `compressBound_z_c`,
agreeing with `Zlib.Compress.compressBound`. -/
theorem compressBound_c_sound (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (hfns : fns "compressBound_z" = some compressBound_z_c)
    (hfuel : 1 ≤ fuel) (sourceLen : UInt64) (h : C.Heap) :
    runCFn fns globals fuel compressBound_c [.u64 sourceLen] h =
      .ret (.u64 (Zlib.Compress.compressBound sourceLen)) h := by
  obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  have hsub := compressBound_z_c_sound fns globals fuel' sourceLen h
  unfold runCFn at hsub
  simp only [bindParams, evalCast_u64_self, Bind.bind, Except.bind, Pure.pure, Except.pure,
    compressBound_z_c] at hsub
  unfold runCFn compressBound_c Zlib.Compress.compressBound
  simp only [bindParams, evalCast_u64_self, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hcall : evalValue fns globals (fuel' + 1) [("sourceLen", .u64 sourceLen)] h
      (.call .u64 "compressBound_z" [.var .u64 "sourceLen"]) =
      .ok (.u64 (Zlib.Compress.compressBound_z sourceLen), [("sourceLen", .u64 sourceLen)], h) := by
    rw [evalValue]
    rw [evalArgs_singleton fns globals (fuel' + 1) _ _ h h _ (.u64 sourceLen)
      (evalValue_var _ _ _ _ _ _ _ _ rfl)]
    simp only [hfns, compressBound_z_c, List.length_cons, List.length_nil, ne_eq, not_true_eq_false,
      ite_false, bindParams, evalCast_u64_self, Bind.bind, Except.bind, Pure.pure, Except.pure,
      hsub]
  exact execStmts_ret _ _ _ _ _ _ _ _ _ [] hcall

/-- `zlibCompileFlags_c` runs to return on all heaps with zero C99 UB and agrees with
`C.run Zlib.Zutil.zlibCompileFlags h`. -/
theorem zlibCompileFlags_c_sound (fns : FnTable) (globals : CEnv) (fuel : Nat) (h : C.Heap) :
    ∃ flags, C.run Zlib.Zutil.zlibCompileFlags h = .ok (flags, h) ∧
      runCFn fns globals fuel zlibCompileFlags_c [] h = .ret (.u64 flags) h := by
  refine ⟨(1 : UInt64) + ((2 : UInt64) <<< 2) + ((2 : UInt64) <<< 4) + ((2 : UInt64) <<< 6), ?_, ?_⟩
  · unfold C.run Zlib.Zutil.zlibCompileFlags; rfl
  · have h_i32_eq_tf : ∀ (env : CEnv) x (vx k : Nat),
        vx < 2 ^ 31 → k < 2 ^ 31 → env.lookup x = some (.i32 (Int32.ofNat vx)) →
        evalValue fns globals fuel env h (.op .bool "==" (.var .i32 x) (.num .i32 k)) =
          .ok (.bool (vx == k), env, h) := by
      intro env x vx k hvx hk hx
      refine evalValue_op fns globals fuel env env env h h h .bool "==" _ _
        (.i32 (Int32.ofNat vx)) (.i32 (Int32.ofNat k)) _
        rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx)
        (evalValue_num _ _ _ _ _ .i32 k (.i32 (Int32.ofNat k)) (by simp [evalNum, hk])) ?_
      unfold evalBinOp evalRelOp
      simp only [CVal.toInt?, int32_toInt_ofNat_lt vx hvx, int32_toInt_ofNat_lt k hk,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      have heq : (Int32.ofNat vx == Int32.ofNat k) = (vx == k) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        constructor
        · intro he
          have hi := congrArg Int32.toInt he
          rw [int32_toInt_ofNat_lt vx hvx, int32_toInt_ofNat_lt k hk] at hi
          exact Int.ofNat.inj hi
        · intro he; subst he; rfl
      change Except.ok (CVal.bool (Int32.ofNat vx == Int32.ofNat k)) = Except.ok (CVal.bool (vx == k))
      rw [heq]
    have h_u64_shift_add : ∀ (env : CEnv) x (vx : UInt64) (a sh : Nat),
        sh < 64 → env.lookup x = some (.u64 vx) →
        evalValue fns globals fuel env h
          (.op .u64 "+" (.var .u64 x) (.op .u64 "<<" (.num .u64 a) (.num .i32 sh))) =
          .ok (.u64 (vx + ((UInt64.ofNat a) <<< UInt64.ofNat sh)), env, h) := by
      intro env x vx a sh hsh hx
      refine eval_u64_add _ _ _ _ _ _ _ _ _ (evalValue_var _ _ _ _ _ _ _ _ hx) ?_
      refine evalValue_op fns globals fuel env env env h h h .u64 "<<" _ _
        (.u64 (UInt64.ofNat a)) (.i32 (Int32.ofNat sh)) _
        rfl rfl (evalValue_num _ _ _ _ _ .u64 a (.u64 (UInt64.ofNat a)) rfl)
        (evalValue_num _ _ _ _ _ .i32 sh (.i32 (Int32.ofNat sh))
          (by simp [evalNum, show sh < 2 ^ 31 by omega]))
        (evalBinOp_u64_shl (UInt64.ofNat a) sh hsh h)
    unfold runCFn zlibCompileFlags_c
    simp only [bindParams]
    rw [execStmts_decl_some fns globals fuel [] [] h h .u64 "flags" _ (.u64 0) (.u64 0) _
      (evalValue_num _ _ _ _ _ .u64 0 (.u64 0) rfl) evalCast_u64_self]
    rw [execStmts_decl_some fns globals fuel _ _ h h .i32 "sz" _ (.i32 4) (.i32 4) _
      (evalValue_num _ _ _ _ _ .i32 4 (.i32 4) rfl) evalCast_i32_self]
    let zenv0 := (CEnv.set [] "flags" (.u64 0)).set "sz" (.i32 4)
    have hf0 : evalValue fns globals fuel zenv0 h
        (.choose (.op .bool "==" (.var .i32 "sz") (.num .i32 2)) (.var .u64 "flags")
          (.choose (.op .bool "==" (.var .i32 "sz") (.num .i32 4))
            (.op .u64 "+" (.var .u64 "flags") (.num .u64 1))
            (.choose (.op .bool "==" (.var .i32 "sz") (.num .i32 8))
              (.op .u64 "+" (.var .u64 "flags") (.num .u64 2))
              (.op .u64 "+" (.var .u64 "flags") (.num .u64 3))))) =
        .ok (.u64 1, zenv0, h) := by
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv0 "sz" 4 2 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_t _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv0 "sz" 4 4 (by decide) (by decide) (by decide)) rfl ?_
      exact eval_u64_add _ _ _ _ _ _ _ _ _
        (evalValue_var _ _ _ zenv0 h .u64 "flags" (.u64 0) (by decide))
        (evalValue_num _ _ _ _ _ .u64 1 (.u64 1) rfl)
    rw [execStmts_decl_some _ _ _ zenv0 zenv0 h h .u64 "flags_0" _ _ _ _ hf0 evalCast_u64_self]
    rw [execStmts_decl_some _ _ _ _ _ h h .i32 "sz_0" _ (.i32 8) (.i32 8) _
      (evalValue_num _ _ _ _ _ .i32 8 (.i32 8) rfl) evalCast_i32_self]
    let zenv1 := (zenv0.set "flags_0" (.u64 1)).set "sz_0" (.i32 8)
    have hf1 : evalValue fns globals fuel zenv1 h
        (.choose (.op .bool "==" (.var .i32 "sz_0") (.num .i32 2)) (.var .u64 "flags_0")
          (.choose (.op .bool "==" (.var .i32 "sz_0") (.num .i32 4))
            (.op .u64 "+" (.var .u64 "flags_0") (.op .u64 "<<" (.num .u64 1) (.num .i32 2)))
            (.choose (.op .bool "==" (.var .i32 "sz_0") (.num .i32 8))
              (.op .u64 "+" (.var .u64 "flags_0") (.op .u64 "<<" (.num .u64 2) (.num .i32 2)))
              (.op .u64 "+" (.var .u64 "flags_0") (.op .u64 "<<" (.num .u64 3) (.num .i32 2)))))) =
        .ok (.u64 ((1 : UInt64) + ((2 : UInt64) <<< 2)), zenv1, h) := by
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv1 "sz_0" 8 2 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv1 "sz_0" 8 4 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_t _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv1 "sz_0" 8 8 (by decide) (by decide) (by decide)) rfl ?_
      exact h_u64_shift_add zenv1 "flags_0" 1 2 2 (by decide) (by decide)
    rw [execStmts_decl_some _ _ _ zenv1 zenv1 h h .u64 "flags_1" _ _ _ _ hf1 evalCast_u64_self]
    rw [execStmts_decl_some _ _ _ _ _ h h .i32 "sz_1" _ (.i32 8) (.i32 8) _
      (evalValue_num _ _ _ _ _ .i32 8 (.i32 8) rfl) evalCast_i32_self]
    let zenv2 := (zenv1.set "flags_1" (.u64 ((1 : UInt64) + ((2 : UInt64) <<< 2)))).set "sz_1" (.i32 8)
    have hf2 : evalValue fns globals fuel zenv2 h
        (.choose (.op .bool "==" (.var .i32 "sz_1") (.num .i32 2)) (.var .u64 "flags_1")
          (.choose (.op .bool "==" (.var .i32 "sz_1") (.num .i32 4))
            (.op .u64 "+" (.var .u64 "flags_1") (.op .u64 "<<" (.num .u64 1) (.num .i32 4)))
            (.choose (.op .bool "==" (.var .i32 "sz_1") (.num .i32 8))
              (.op .u64 "+" (.var .u64 "flags_1") (.op .u64 "<<" (.num .u64 2) (.num .i32 4)))
              (.op .u64 "+" (.var .u64 "flags_1") (.op .u64 "<<" (.num .u64 3) (.num .i32 4)))))) =
        .ok (.u64 ((1 : UInt64) + ((2 : UInt64) <<< 2) + ((2 : UInt64) <<< 4)), zenv2, h) := by
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv2 "sz_1" 8 2 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv2 "sz_1" 8 4 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_t _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv2 "sz_1" 8 8 (by decide) (by decide) (by decide)) rfl ?_
      exact h_u64_shift_add zenv2 "flags_1" _ 2 4 (by decide) (by decide)
    rw [execStmts_decl_some _ _ _ zenv2 zenv2 h h .u64 "flags_2" _ _ _ _ hf2 evalCast_u64_self]
    rw [execStmts_decl_some _ _ _ _ _ h h .i32 "sz_2" _ (.i32 8) (.i32 8) _
      (evalValue_num _ _ _ _ _ .i32 8 (.i32 8) rfl) evalCast_i32_self]
    let zenv3 :=
      (zenv2.set "flags_2" (.u64 ((1 : UInt64) + ((2 : UInt64) <<< 2) + ((2 : UInt64) <<< 4)))).set
        "sz_2" (.i32 8)
    have hf3 : evalValue fns globals fuel zenv3 h
        (.choose (.op .bool "==" (.var .i32 "sz_2") (.num .i32 2)) (.var .u64 "flags_2")
          (.choose (.op .bool "==" (.var .i32 "sz_2") (.num .i32 4))
            (.op .u64 "+" (.var .u64 "flags_2") (.op .u64 "<<" (.num .u64 1) (.num .i32 6)))
            (.choose (.op .bool "==" (.var .i32 "sz_2") (.num .i32 8))
              (.op .u64 "+" (.var .u64 "flags_2") (.op .u64 "<<" (.num .u64 2) (.num .i32 6)))
              (.op .u64 "+" (.var .u64 "flags_2") (.op .u64 "<<" (.num .u64 3) (.num .i32 6)))))) =
        .ok (.u64 ((1 : UInt64) + ((2 : UInt64) <<< 2) + ((2 : UInt64) <<< 4) + ((2 : UInt64) <<< 6)),
          zenv3, h) := by
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv3 "sz_2" 8 2 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_f _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv3 "sz_2" 8 4 (by decide) (by decide) (by decide)) rfl ?_
      refine evalValue_choose_t _ _ _ _ _ _ h h h _ _ _ _ _
        (h_i32_eq_tf zenv3 "sz_2" 8 8 (by decide) (by decide) (by decide)) rfl ?_
      exact h_u64_shift_add zenv3 "flags_2" _ 2 6 (by decide) (by decide)
    rw [execStmts_decl_some _ _ _ zenv3 zenv3 h h .u64 "flags_3" _ _ _ _ hf3 evalCast_u64_self]
    let zenv4 :=
      zenv3.set "flags_3"
        (.u64 ((1 : UInt64) + ((2 : UInt64) <<< 2) + ((2 : UInt64) <<< 4) + ((2 : UInt64) <<< 6)))
    exact execStmts_ret _ _ _ zenv4 zenv4 h h _ _ []
      (evalValue_var _ _ _ zenv4 h .u64 "flags_3" _ (by decide))

/-- `byte_swap_c` runs to return on all `UInt32` inputs with zero C99 UB and agrees with
`Zlib.Crc32.byte_swap`. -/
theorem byte_swap_c_sound (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (word : UInt32) (h : C.Heap) :
    runCFn fns globals fuel byte_swap_c [.u32 word] h =
      .ret (.u32 (Zlib.Crc32.byte_swap word)) h := by
  let env0 : CEnv := [("word", .u32 word)]
  have hw : evalValue fns globals fuel env0 h (.var .u32 "word") = .ok (.u32 word, env0, h) :=
    evalValue_var _ _ _ _ _ _ _ _ rfl
  have hm0 : evalBinOp .u32 "&" (.u32 word) (.u32 4278190080) h =
      .ok (.u32 (word &&& 0xff000000)) := evalBinOp_u32_and word 0xff000000 h
  have hm1 : evalBinOp .u32 "&" (.u32 word) (.i32 (Int32.ofNat 16711680)) h =
      .ok (.u32 (word &&& 0xff0000)) := by
    unfold evalBinOp
    simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "&" = false from rfl,
      show ("&" == "<<" || "&" == ">>") = false from rfl, Bool.false_or, bool_if_false,
      evalCast_u32_self, evalCast_u32_i32_of_nat 16711680 (by decide),
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  have hm2 : evalBinOp .u32 "&" (.u32 word) (.i32 (Int32.ofNat 65280)) h =
      .ok (.u32 (word &&& 0xff00)) := by
    unfold evalBinOp
    simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "&" = false from rfl,
      show ("&" == "<<" || "&" == ">>") = false from rfl, Bool.false_or, bool_if_false,
      evalCast_u32_self, evalCast_u32_i32_of_nat 65280 (by decide),
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  have hm3 : evalBinOp .u32 "&" (.u32 word) (.i32 (Int32.ofNat 255)) h =
      .ok (.u32 (word &&& 0xff)) := by
    unfold evalBinOp
    simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "&" = false from rfl,
      show ("&" == "<<" || "&" == ">>") = false from rfl, Bool.false_or, bool_if_false,
      evalCast_u32_self, evalCast_u32_i32_of_nat 255 (by decide),
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  have hp0 : evalValue fns globals fuel env0 h
      (.op .u32 ">>" (.op .u32 "&" (.var .u32 "word") (.num .u32 4278190080)) (.num .i32 24)) =
      .ok (.u32 ((word &&& 0xff000000) >>> 24), env0, h) :=
    evalValue_op fns globals fuel env0 env0 env0 h h h .u32 ">>" _ _ _ _ _ rfl rfl
      (evalValue_op _ _ _ _ _ _ h h h .u32 "&" _ _ _ _ _ rfl rfl hw
        (evalValue_num _ _ _ _ _ .u32 4278190080 (.u32 4278190080) rfl) hm0)
      (evalValue_num _ _ _ _ _ .i32 24 (.i32 24) rfl)
      (evalBinOp_u32_shr _ 24 (by decide) h)
  have hp1 : evalValue fns globals fuel env0 h
      (.op .u32 ">>" (.op .u32 "&" (.var .u32 "word") (.num .i32 16711680)) (.num .i32 8)) =
      .ok (.u32 ((word &&& 0xff0000) >>> 8), env0, h) :=
    evalValue_op fns globals fuel env0 env0 env0 h h h .u32 ">>" _ _ _ _ _ rfl rfl
      (evalValue_op _ _ _ _ _ _ h h h .u32 "&" _ _ _ _ _ rfl rfl hw
        (evalValue_num _ _ _ _ _ .i32 16711680 (.i32 16711680) rfl) hm1)
      (evalValue_num _ _ _ _ _ .i32 8 (.i32 8) rfl)
      (evalBinOp_u32_shr _ 8 (by decide) h)
  have hp2 : evalValue fns globals fuel env0 h
      (.op .u32 "<<" (.op .u32 "&" (.var .u32 "word") (.num .i32 65280)) (.num .i32 8)) =
      .ok (.u32 ((word &&& 0xff00) <<< 8), env0, h) :=
    evalValue_op fns globals fuel env0 env0 env0 h h h .u32 "<<" _ _ _ _ _ rfl rfl
      (evalValue_op _ _ _ _ _ _ h h h .u32 "&" _ _ _ _ _ rfl rfl hw
        (evalValue_num _ _ _ _ _ .i32 65280 (.i32 65280) rfl) hm2)
      (evalValue_num _ _ _ _ _ .i32 8 (.i32 8) rfl)
      (evalBinOp_u32_shl _ 8 (by decide) h)
  have hp3 : evalValue fns globals fuel env0 h
      (.op .u32 "<<" (.op .u32 "&" (.var .u32 "word") (.num .i32 255)) (.num .i32 24)) =
      .ok (.u32 ((word &&& 0xff) <<< 24), env0, h) :=
    evalValue_op fns globals fuel env0 env0 env0 h h h .u32 "<<" _ _ _ _ _ rfl rfl
      (evalValue_op _ _ _ _ _ _ h h h .u32 "&" _ _ _ _ _ rfl rfl hw
        (evalValue_num _ _ _ _ _ .i32 255 (.i32 255) rfl) hm3)
      (evalValue_num _ _ _ _ _ .i32 24 (.i32 24) rfl)
      (evalBinOp_u32_shl _ 24 (by decide) h)
  have hor := evalValue_op fns globals fuel env0 env0 env0 h h h .u32 "|" _ _ _ _ _ rfl rfl
    (evalValue_op fns globals fuel env0 env0 env0 h h h .u32 "|" _ _ _ _ _ rfl rfl
      (evalValue_op fns globals fuel env0 env0 env0 h h h .u32 "|" _ _ _ _ _ rfl rfl
        hp0 hp1 (evalBinOp_u32_or _ _ h))
      hp2 (evalBinOp_u32_or _ _ h))
    hp3 (evalBinOp_u32_or _ _ h)
  unfold runCFn byte_swap_c Zlib.Crc32.byte_swap
  simp only [bindParams, evalCast_u32_self, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact execStmts_ret _ _ _ _ _ _ _ _ _ [] hor

/-- `adler32_combine_c` runs to return on all inputs under `defaultCGlobals` with zero C99 UB
(signed remainder safety on `len2 ≥ 0`, division/shift safety, and heap preservation) and agrees
with `C.run (Zlib.Adler32.adler32_combine_ adler1 adler2 len2) h`. -/
theorem adler32_combine_c_sound (fns : FnTable) (fuel : Nat)
    (adler1 adler2 : UInt64) (len2 : Int64) (h : C.Heap) :
    ∃ res, C.run (Zlib.Adler32.adler32_combine_ adler1 adler2 len2) h = .ok (res, h) ∧
      runCFn fns defaultCGlobals fuel adler32_combine_c
        [.u64 adler1, .u64 adler2, .i64 len2] h = .ret (.u64 res) h := by
  let env0 : CEnv := [("adler1", .u64 adler1), ("adler2", .u64 adler2), ("len2", .i64 len2)]
  have hbind : bindParams adler32_combine_c.1 [.u64 adler1, .u64 adler2, .i64 len2] = .ok env0 := by
    simp [adler32_combine_c, bindParams, evalCast_u64_self, evalCast_i64_self,
      Bind.bind, Except.bind, Pure.pure, Except.pure, env0]
  have hcmp0 : evalValue fns defaultCGlobals fuel env0 h
      (.op .bool "<" (.var .i64 "len2") (.num .i64 0)) =
      .ok (.bool (decide (len2 < 0)), env0, h) := by
    refine evalValue_op fns defaultCGlobals fuel env0 env0 env0 h h h .bool "<" _ _
      (.i64 len2) (.i64 (Int64.ofNat 0)) _
      rfl rfl (evalValue_var _ _ _ _ _ _ _ _ rfl)
      (evalValue_num _ _ _ _ _ .i64 0 (.i64 0) rfl) ?_
    unfold evalBinOp evalRelOp
    simp only [CVal.toInt?, Bind.bind, Except.bind, Pure.pure, Except.pure]; rfl
  by_cases hneg : len2 < 0
  · refine ⟨0xffffffff, ?_, ?_⟩
    · unfold C.run Zlib.Adler32.adler32_combine_; simp [hneg]
    · unfold runCFn; rw [hbind]; dsimp only [adler32_combine_c]
      rw [execStmts_branch_t fns defaultCGlobals fuel env0 env0 h h _ _ _ _ _ hcmp0
        (by simp [CVal.toBool?, hneg])]
      rw [execStmts_ret _ _ _ _ _ _ _ _ _ []
        (evalValue_num _ _ _ _ _ .u64 4294967295 (.u64 0xffffffff) rfl)]
  · have hnonneg : 0 ≤ len2.toInt := by
      have hn : ¬ len2.toInt < (0 : Int64).toInt := fun lt => hneg (Int64.lt_iff_toInt_lt.mpr lt)
      have hz : (0 : Int64).toInt = 0 := rfl
      omega
    have htmod_nonneg : 0 ≤ Int.tmod len2.toInt 65521 := by
      rw [Int.tmod_eq_emod_of_nonneg hnonneg]
      exact Int.emod_nonneg _ (by decide)
    have htmod_lt : Int.tmod len2.toInt 65521 < 65521 := by
      rw [Int.tmod_eq_emod_of_nonneg hnonneg]
      exact Int.emod_lt_of_pos _ (by decide)
    have hmod_eq : Int64.ofInt (Int.tmod len2.toInt 65521) = len2 % 65521 := by
      apply Int64.toInt_inj.mp
      rw [Int64.toInt_mod, Int64.toInt_ofInt]
      simp only [Int64.size, Int.bmod]
      have hc : (65521 : Int64).toInt = 65521 := rfl
      rw [hc]
      split <;> omega
    let len2Mod : Int64 := len2 % 65521
    have hlen2Mod_nonneg : 0 ≤ len2Mod.toInt := by
      dsimp only [len2Mod]
      rw [← hmod_eq, Int64.toInt_ofInt]
      simp only [Int64.size, Int.bmod]
      split <;> omega
    let rem : UInt32 := len2Mod.toUInt64.toUInt32
    let base : UInt64 := 65521
    let sum1 : UInt64 := adler1 &&& (0xffff : UInt64)
    let sum2 : UInt64 := (rem.toUInt64 * sum1) % base
    let sum1a : UInt64 := sum1 + ((adler2 &&& (0xffff : UInt64)) + base - 1)
    let sum2a : UInt64 :=
      sum2 + (((adler1 >>> 16) &&& (0xffff : UInt64)) + ((adler2 >>> 16) &&& (0xffff : UInt64)) + base - rem.toUInt64)
    let sum1b : UInt64 := if sum1a >= base then sum1a - base else sum1a
    let sum1c : UInt64 := if sum1b >= base then sum1b - base else sum1b
    let sum2b : UInt64 := if sum2a >= base <<< 1 then sum2a - (base <<< 1) else sum2a
    let sum2c : UInt64 := if sum2b >= base then sum2b - base else sum2b
    refine ⟨sum1c ||| (sum2c <<< 16), ?_, ?_⟩
    · unfold C.run Zlib.Adler32.adler32_combine_
      rw [ite_eq_right (fun hn => absurd hn hneg)]
      dsimp only
      repeat' split
      all_goals
        dsimp only [sum1c, sum1b, sum2c, sum2b, sum2a, sum1a, sum2, sum1, rem, base, len2Mod]
        try simp only [Zlib.Adler32.BASE, ge_iff_le] at *
        simp only [C.pure_app, *, ite_true, ite_false]
        repeat' split
        all_goals first | rfl | contradiction
    · have hmodEval : evalBinOp .i64 "%" (.i64 len2) (.i64 (Int64.ofNat 65521)) h =
          .ok (.i64 len2Mod) := by
        have hc : (Int64.ofNat 65521).toInt = 65521 := rfl
        have hnz : ((65521 : Int) == 0) = false := by decide
        have hm : (len2.toInt == -Int.ofNat (2 ^ 63) && (65521 : Int) == -1) = false := by
          simp
        unfold evalBinOp
        simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "%" = false from rfl,
          show ("%" == "<<" || "%" == ">>") = false from rfl, Bool.false_or,
          evalCast_i64_self, hc, hnz, hm, bool_if_false,
          Bind.bind, Except.bind, Pure.pure, Except.pure, hmod_eq]
        rfl
      have hlen2_0_e : evalValue fns defaultCGlobals fuel env0 h
          (.op .i64 "%" (.var .i64 "len2") (.num .i64 65521)) = .ok (.i64 len2Mod, env0, h) :=
        evalValue_op fns defaultCGlobals fuel env0 env0 env0 h h h .i64 "%" _ _
          (.i64 len2) (.i64 (Int64.ofNat 65521)) _ rfl rfl
          (evalValue_var _ _ _ _ _ _ _ _ rfl)
          (evalValue_num _ _ _ _ _ .i64 65521 (.i64 65521) rfl)
          hmodEval
      unfold runCFn; rw [hbind]; dsimp only [adler32_combine_c]
      rw [execStmts_branch_f fns defaultCGlobals fuel env0 env0 h h _ _ _ _ _ hcmp0
        (by simp [CVal.toBool?, hneg])]
      -- len2_0
      rw [execStmts_decl_some fns defaultCGlobals fuel env0 env0 h h .i64 "len2_0" _ _ _ _
        hlen2_0_e evalCast_i64_self]
      -- rem
      let env1 := env0.set "len2_0" (.i64 len2Mod)
      have hcast_u64 : evalCast .u64 (.i64 len2Mod) = .ok (.u64 len2Mod.toUInt64) := by
        simp [evalCast, CVal.toInt?, ofIntForTy, uint64_ofInt_eq_toUInt64 len2Mod hlen2Mod_nonneg]
      have hrem_e : evalValue fns defaultCGlobals fuel env1 h
          (.cast .u32 (.cast .u64 (.var .i64 "len2_0"))) = .ok (.u32 rem, env1, h) :=
        evalValue_cast _ _ _ _ _ h h .u32 _ (.u64 len2Mod.toUInt64) (.u32 rem)
          (evalValue_cast _ _ _ _ _ h h .u64 _ (.i64 len2Mod) (.u64 len2Mod.toUInt64)
            (evalValue_var _ _ _ _ _ _ _ _ rfl) hcast_u64)
          (evalCast_u32_u64 _)
      rw [execStmts_decl_some _ _ _ env1 env1 h h .u32 "rem" _ _ _ _ hrem_e evalCast_u32_self]
      -- sum1
      let env2 := env1.set "rem" (.u32 rem)
      have h65535 : evalCast .u64 (.i32 (Int32.ofNat 65535)) = .ok (.u64 0xffff) :=
        evalCast_u64_i32_of_nat 65535 (by decide)
      have hand65535 : ∀ env x (vx : UInt64), env.lookup x = some (.u64 vx) →
          evalValue fns defaultCGlobals fuel env h (.op .u64 "&" (.var .u64 x) (.num .i32 65535)) =
            .ok (.u64 (vx &&& 0xffff), env, h) := by
        intro env x vx hx
        refine evalValue_op fns defaultCGlobals fuel env env env h h h .u64 "&" _ _
          (.u64 vx) (.i32 (Int32.ofNat 65535)) _ rfl rfl (evalValue_var _ _ _ _ _ _ _ _ hx)
          (evalValue_num _ _ _ _ _ .i32 65535 (.i32 65535) rfl) ?_
        unfold evalBinOp
        simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "&" = false from rfl,
          show ("&" == "<<" || "&" == ">>") = false from rfl, Bool.false_or, bool_if_false,
          evalCast_u64_self, h65535, Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [execStmts_decl_some _ _ _ env2 env2 h h .u64 "sum1" _ _ _ _ (hand65535 _ "adler1" adler1 rfl)
        evalCast_u64_self]
      -- sum2
      let env3 := env2.set "sum1" (.u64 sum1)
      have hsum2_e : evalValue fns defaultCGlobals fuel env3 h
          (.op .u64 "*" (.cast .u64 (.var .u32 "rem")) (.var .u64 "sum1")) =
          .ok (.u64 (rem.toUInt64 * sum1), env3, h) :=
        evalValue_op fns defaultCGlobals fuel env3 env3 env3 h h h .u64 "*" _ _
          (.u64 rem.toUInt64) (.u64 sum1) _ rfl rfl
          (evalValue_cast _ _ _ _ _ h h .u64 _ (.u32 rem) _ (evalValue_var _ _ _ _ _ _ _ _ rfl)
            (evalCast_u64_u32 rem))
          (evalValue_var _ _ _ _ _ _ _ _ rfl) (evalBinOp_u64_mul _ _ h)
      rw [execStmts_decl_some _ _ _ env3 env3 h h .u64 "sum2" _ _ _ _ hsum2_e evalCast_u64_self]
      -- sum2_0
      let env4 := env3.set "sum2" (.u64 (rem.toUInt64 * sum1))
      have hbase_gl : ∀ env, env.lookup "BASE" = none →
          evalValue fns defaultCGlobals fuel env h (.var .u64 "BASE") = .ok (.u64 base, env, h) :=
        fun env hn => evalValue_global _ _ _ env h .u64 "BASE" (.u64 base) hn rfl
      have hsum2_0_e : evalValue fns defaultCGlobals fuel env4 h
          (.op .u64 "%" (.var .u64 "sum2") (.var .u64 "BASE")) = .ok (.u64 sum2, env4, h) :=
        evalValue_op fns defaultCGlobals fuel env4 env4 env4 h h h .u64 "%" _ _
          (.u64 (rem.toUInt64 * sum1)) (.u64 base) _ rfl rfl
          (evalValue_var _ _ _ _ _ _ _ _ rfl) (hbase_gl _ rfl)
          (evalBinOp_u64_mod _ base (by decide) h)
      rw [execStmts_decl_some _ _ _ env4 env4 h h .u64 "sum2_0" _ _ _ _ hsum2_0_e evalCast_u64_self]
      -- sum1_0
      let env5 := env4.set "sum2_0" (.u64 sum2)
      have hsum1_0_e : evalValue fns defaultCGlobals fuel env5 h
          (.op .u64 "+" (.var .u64 "sum1")
            (.op .u64 "-"
              (.op .u64 "+" (.op .u64 "&" (.var .u64 "adler2") (.num .i32 65535)) (.var .u64 "BASE"))
              (.num .u64 1))) = .ok (.u64 sum1a, env5, h) :=
        eval_u64_add _ _ _ _ _ _ _ _ _ (evalValue_var _ _ _ _ _ _ _ _ rfl)
          (eval_u64_sub _ _ _ _ _ _ _ _ _
            (eval_u64_add _ _ _ _ _ _ _ _ _ (hand65535 _ "adler2" adler2 rfl) (hbase_gl _ rfl))
            (evalValue_num _ _ _ _ _ .u64 1 (.u64 1) rfl))
      rw [execStmts_decl_some _ _ _ env5 env5 h h .u64 "sum1_0" _ _ _ _ hsum1_0_e evalCast_u64_self]
      -- sum2_1
      let env6 := env5.set "sum1_0" (.u64 sum1a)
      have hsh16 : ∀ env x (vx : UInt64), env.lookup x = some (.u64 vx) →
          evalValue fns defaultCGlobals fuel env h
            (.op .u64 "&" (.op .u64 ">>" (.var .u64 x) (.num .i32 16)) (.num .i32 65535)) =
            .ok (.u64 ((vx >>> 16) &&& 0xffff), env, h) := by
        intro env x vx hx
        refine evalValue_op fns defaultCGlobals fuel env env env h h h .u64 "&" _ _
          (.u64 (vx >>> UInt64.ofNat 16)) (.i32 (Int32.ofNat 65535)) _ rfl rfl
          (eval_u64_const_shift_r _ _ _ _ _ x vx 16 (by decide) hx)
          (evalValue_num _ _ _ _ _ .i32 65535 (.i32 65535) rfl) ?_
        unfold evalBinOp
        simp only [show ["<", "<=", ">", ">=", "==", "!="].contains "&" = false from rfl,
          show ("&" == "<<" || "&" == ">>") = false from rfl, Bool.false_or, bool_if_false,
          evalCast_u64_self, h65535, Bind.bind, Except.bind, Pure.pure, Except.pure]
        rfl
      have hsum2_1_e : evalValue fns defaultCGlobals fuel env6 h
          (.op .u64 "+" (.var .u64 "sum2_0")
            (.op .u64 "-"
              (.op .u64 "+"
                (.op .u64 "+"
                  (.op .u64 "&" (.op .u64 ">>" (.var .u64 "adler1") (.num .i32 16)) (.num .i32 65535))
                  (.op .u64 "&" (.op .u64 ">>" (.var .u64 "adler2") (.num .i32 16)) (.num .i32 65535)))
                (.var .u64 "BASE"))
              (.cast .u64 (.var .u32 "rem")))) = .ok (.u64 sum2a, env6, h) :=
        eval_u64_add _ _ _ _ _ _ _ _ _ (evalValue_var _ _ _ _ _ _ _ _ rfl)
          (eval_u64_sub _ _ _ _ _ _ _ _ _
            (eval_u64_add _ _ _ _ _ _ _ _ _
              (eval_u64_add _ _ _ _ _ _ _ _ _ (hsh16 _ "adler1" adler1 rfl) (hsh16 _ "adler2" adler2 rfl))
              (hbase_gl _ rfl))
            (evalValue_cast _ _ _ _ _ h h .u64 _ (.u32 rem) _ (evalValue_var _ _ _ _ _ _ _ _ rfl)
              (evalCast_u64_u32 rem)))
      rw [execStmts_decl_some _ _ _ env6 env6 h h .u64 "sum2_1" _ _ _ _ hsum2_1_e evalCast_u64_self]
      -- sum1_1 & sum1_2
      let env7 := env6.set "sum2_1" (.u64 sum2a)
      rw [execStmts_decl_some _ _ _ env7 env7 h h .u64 "sum1_1" _ _ _ _
        (evalValue_var _ _ _ _ _ _ _ _ rfl) evalCast_u64_self]
      let env8 := env7.set "sum1_1" (.u64 sum1a)
      rw [execStmts_decl_none _ _ _ env8 h .u64 "sum1_2"]
      let env9 := env8.set "sum1_2" .void
      -- branch 1: sum1_1 >= BASE
      rw [execStmts_if_assign_u64 fns defaultCGlobals fuel env9 h _ _ _ "sum1_2" (decide (base ≤ sum1a))
        (sum1a - base) sum1a _
        (eval_u64_ge fns defaultCGlobals fuel env9 h (.var .u64 "sum1_1") (.var .u64 "BASE")
          sum1a base (evalValue_var _ _ _ _ _ _ _ _ rfl) (hbase_gl _ rfl))
        (eval_u64_sub _ _ _ _ _ _ _ _ _ (evalValue_var _ _ _ _ _ _ _ _ rfl) (hbase_gl _ rfl))
        (evalValue_var _ _ _ _ _ _ _ _ rfl)]
      have h_s1b : sum1b = (if decide (base ≤ sum1a) = true then sum1a - base else sum1a) := by
        simp only [sum1b, decide_eq_true_eq]
      rw [← h_s1b]
      -- sum1_3
      let env10 := env9.set "sum1_2" (.u64 sum1b)
      rw [execStmts_decl_none _ _ _ env10 h .u64 "sum1_3"]
      let env11 := env10.set "sum1_3" .void
      have hsum1_2_l11 : env11.lookup "sum1_2" = some (.u64 sum1b) := by
        dsimp only [env11, env10]
        rw [cenv_lookup_set_ne]
        · exact CEnv.lookup_set_same _ _ _
        · decide
      have hbase_l11 : env11.lookup "BASE" = none := by
        dsimp only [env11, env10, env9, env8, env7, env6, env5, env4, env3, env2, env1]
        iterate 11 (rw [cenv_lookup_set_ne]; all_goals try decide)
        rfl
      -- branch 2: sum1_2 >= BASE
      rw [execStmts_if_assign_u64 fns defaultCGlobals fuel env11 h _ _ _ "sum1_3" (decide (base ≤ sum1b))
        (sum1b - base) sum1b _
        (eval_u64_ge fns defaultCGlobals fuel env11 h (.var .u64 "sum1_2") (.var .u64 "BASE")
          sum1b base (evalValue_var _ _ _ env11 h .u64 "sum1_2" (.u64 sum1b) hsum1_2_l11)
          (hbase_gl _ hbase_l11))
        (eval_u64_sub _ _ _ _ _ _ _ _ _
          (evalValue_var _ _ _ env11 h .u64 "sum1_2" (.u64 sum1b) hsum1_2_l11)
          (hbase_gl _ hbase_l11))
        (evalValue_var _ _ _ env11 h .u64 "sum1_2" (.u64 sum1b) hsum1_2_l11)]
      have h_s1c : sum1c = (if decide (base ≤ sum1b) = true then sum1b - base else sum1b) := by
        simp only [sum1c, decide_eq_true_eq]
      rw [← h_s1c]
      -- sum2_2 & sum2_3
      let env12 := env11.set "sum1_3" (.u64 sum1c)
      have hsum2_1_l12 : env12.lookup "sum2_1" = some (.u64 sum2a) := by
        dsimp only [env12, env11, env10, env9, env8, env7]
        iterate 5 (rw [cenv_lookup_set_ne]; all_goals try decide)
        exact CEnv.lookup_set_same _ _ _
      rw [execStmts_decl_some _ _ _ env12 env12 h h .u64 "sum2_2" _ _ _ _
        (evalValue_var _ _ _ env12 h .u64 "sum2_1" (.u64 sum2a) hsum2_1_l12) evalCast_u64_self]
      let env13 := env12.set "sum2_2" (.u64 sum2a)
      rw [execStmts_decl_none _ _ _ env13 h .u64 "sum2_3"]
      let env14 := env13.set "sum2_3" .void
      have hsum2_2_l14 : env14.lookup "sum2_2" = some (.u64 sum2a) := by
        dsimp only [env14, env13]
        rw [cenv_lookup_set_ne]
        · exact CEnv.lookup_set_same _ _ _
        · decide
      -- branch 3: sum2_2 >= BASE <<< 1
      have hbase2 : ∀ env, env.lookup "BASE" = none →
          evalValue fns defaultCGlobals fuel env h (.op .u64 "<<" (.var .u64 "BASE") (.num .i32 1)) =
            .ok (.u64 (base <<< 1), env, h) := fun env hn =>
        evalValue_op fns defaultCGlobals fuel env env env h h h .u64 "<<" _ _
          (.u64 base) (.i32 (Int32.ofNat 1)) _ rfl rfl (hbase_gl env hn)
          (evalValue_num _ _ _ _ _ .i32 1 (.i32 1) rfl)
          (evalBinOp_u64_shl base 1 (by decide) h)
      have hbase_l14 : env14.lookup "BASE" = none := by
        dsimp only [env14, env13, env12]
        iterate 3 (rw [cenv_lookup_set_ne]; all_goals try decide)
        exact hbase_l11
      rw [execStmts_if_assign_u64 fns defaultCGlobals fuel env14 h _ _ _ "sum2_3" (decide (base <<< 1 ≤ sum2a))
        (sum2a - (base <<< 1)) sum2a _
        (eval_u64_ge fns defaultCGlobals fuel env14 h (.var .u64 "sum2_2")
          (.op .u64 "<<" (.var .u64 "BASE") (.num .i32 1))
          sum2a (base <<< 1) (evalValue_var _ _ _ env14 h .u64 "sum2_2" (.u64 sum2a) hsum2_2_l14) (hbase2 _ hbase_l14))
        (eval_u64_sub _ _ _ _ _ _ _ _ _
          (evalValue_var _ _ _ env14 h .u64 "sum2_2" (.u64 sum2a) hsum2_2_l14) (hbase2 _ hbase_l14))
        (evalValue_var _ _ _ env14 h .u64 "sum2_2" (.u64 sum2a) hsum2_2_l14)]
      have h_s2b : sum2b = (if decide (base <<< 1 ≤ sum2a) = true then sum2a - (base <<< 1) else sum2a) := by
        simp only [sum2b, decide_eq_true_eq]
      rw [← h_s2b]
      -- sum2_4
      let env15 := env14.set "sum2_3" (.u64 sum2b)
      rw [execStmts_decl_none _ _ _ env15 h .u64 "sum2_4"]
      let env16 := env15.set "sum2_4" .void
      have hsum2_3_l16 : env16.lookup "sum2_3" = some (.u64 sum2b) := by
        dsimp only [env16, env15]
        rw [cenv_lookup_set_ne]
        · exact CEnv.lookup_set_same _ _ _
        · decide
      have hbase_l16 : env16.lookup "BASE" = none := by
        dsimp only [env16, env15]
        iterate 2 (rw [cenv_lookup_set_ne]; all_goals try decide)
        exact hbase_l14
      -- branch 4: sum2_3 >= BASE
      rw [execStmts_if_assign_u64 fns defaultCGlobals fuel env16 h _ _ _ "sum2_4" (decide (base ≤ sum2b))
        (sum2b - base) sum2b _
        (eval_u64_ge fns defaultCGlobals fuel env16 h (.var .u64 "sum2_3") (.var .u64 "BASE")
          sum2b base (evalValue_var _ _ _ env16 h .u64 "sum2_3" (.u64 sum2b) hsum2_3_l16) (hbase_gl _ hbase_l16))
        (eval_u64_sub _ _ _ _ _ _ _ _ _
          (evalValue_var _ _ _ env16 h .u64 "sum2_3" (.u64 sum2b) hsum2_3_l16) (hbase_gl _ hbase_l16))
        (evalValue_var _ _ _ env16 h .u64 "sum2_3" (.u64 sum2b) hsum2_3_l16)]
      have h_s2c : sum2c = (if decide (base ≤ sum2b) = true then sum2b - base else sum2b) := by
        simp only [sum2c, decide_eq_true_eq]
      rw [← h_s2c]
      -- final return: sum1_3 | (sum2_4 << 16)
      let env17 := env16.set "sum2_4" (.u64 sum2c)
      have hsum1_3_l17 : env17.lookup "sum1_3" = some (.u64 sum1c) := by
        dsimp only [env17, env16, env15, env14, env13, env12]
        iterate 5 (rw [cenv_lookup_set_ne]; all_goals try decide)
        exact CEnv.lookup_set_same _ _ _
      have hsum2_4_l17 : env17.lookup "sum2_4" = some (.u64 sum2c) := by
        dsimp only [env17]; exact CEnv.lookup_set_same _ _ _
      have hret_e : evalValue fns defaultCGlobals fuel env17 h
          (.op .u64 "|" (.var .u64 "sum1_3") (.op .u64 "<<" (.var .u64 "sum2_4") (.num .i32 16))) =
          .ok (.u64 (sum1c ||| (sum2c <<< 16)), env17, h) :=
        evalValue_op fns defaultCGlobals fuel env17 env17 env17 h h h .u64 "|" _ _
          (.u64 sum1c) (.u64 (sum2c <<< 16)) _ rfl rfl
          (evalValue_var _ _ _ env17 h .u64 "sum1_3" (.u64 sum1c) hsum1_3_l17)
          (eval_u64_var_shift_l _ _ _ env17 h "sum2_4" sum2c 16 (by decide) hsum2_4_l17)
          (evalBinOp_u64_or _ _ h)
      rw [execStmts_ret _ _ _ env17 env17 h h _ _ [] hret_e]

/-! ## 5. C-level safety transfer corollaries -/

theorem compressBound_c_spec (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (hfns : fns "compressBound_z" = some compressBound_z_c)
    (hfuel : 1 ≤ fuel) (hspec : ZlibF.Spec.Public.Goal.compressBound)
    (sourceLen : UInt64) (h : C.Heap) :
    ∃ v, runCFn fns globals fuel compressBound_c [.u64 sourceLen] h = .ret (.u64 v) h ∧
      v.toNat = ZlibF.Spec.Api.compressBound sourceLen.toNat :=
  ⟨Zlib.Compress.compressBound sourceLen,
    compressBound_c_sound fns globals fuel hfns hfuel sourceLen h,
    hspec sourceLen⟩

theorem zlibCompileFlags_c_safety (fns : FnTable) (globals : CEnv) (fuel : Nat)
    (hsafe : ZlibF.Spec.Public.Goal.zlibCompileFlags_safety) (h : C.Heap) :
    ∃ flags, C.run Zlib.Zutil.zlibCompileFlags h = .ok (flags, h) ∧
      runCFn fns globals fuel zlibCompileFlags_c [] h = .ret (.u64 flags) h := by
  obtain ⟨_, _⟩ := hsafe h
  exact zlibCompileFlags_c_sound fns globals fuel h

theorem adler32_combine_c_safety (fns : FnTable) (fuel : Nat)
    (hsafe : ZlibF.Spec.Public.Goal.adler32_combine_safety)
    (h : C.Heap) (adler1 adler2 : UInt64) (len2 : Int64) :
    ∃ res, C.run (Zlib.Adler32.adler32_combine adler1 adler2 len2) h = .ok (res, h) ∧
      runCFn fns defaultCGlobals fuel adler32_combine_c
        [.u64 adler1, .u64 adler2, .i64 len2] h = .ret (.u64 res) h := by
  obtain ⟨_, _⟩ := hsafe h adler1 adler2 len2
  exact adler32_combine_c_sound fns fuel adler1 adler2 len2 h

#print axioms evalValue_mod_shl_u32
#print axioms evalValue_guarded_shr_u64
#print axioms evalValue_load_u8
#print axioms execStmt_store_u8
#print axioms execStmt_while_sim
#print axioms execStmt_doWhile_sim
#print axioms compressBound_z_c_sound
#print axioms compressBound_c_sound
#print axioms zlibCompileFlags_c_sound
#print axioms byte_swap_c_sound
#print axioms adler32_combine_c_sound
#print axioms compressBound_c_spec
#print axioms zlibCompileFlags_c_safety
#print axioms adler32_combine_c_safety

end Lean2C.Soundness
