import C99.Proof.Mem
import C99.Proof.WP
import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgSpec
import Zlib.Zutil

/-!
# Safety & Allocation Proofs for `zutil.c` (`zcalloc`, `zcfree`, `zError`)

Provides:
- `HeapBodySpec` and `HeapBodySpec.call`: generalization of `FuncBodySpec` for functions
  that allocate or free heap blocks (without requiring `ROExt m m'`).
- `Libc.ExtStep` / `zlibExt` rules for `"malloc"`, `"calloc"`, and `"free"`.
- `zcalloc_spec` and `zcalloc_spec_of`: WP spec for `zcalloc` (always dispatches to
  `malloc((items * size) % 2^32)` since `sizeof(uInt) = 4 > 2`), returning either `.null`
  with unchanged blocks or a fresh `.rw` `.heap` block of size `(items * size) % 2^32`.
- `zcfree_spec` and `zcfree_spec_of`: WP spec for `zcfree`, preserving blocks on `.null`
  and dropping the `.heap` block on `.ptr b 0`.
- `ZErrmsgReady` and `zError_spec` / `zError_spec_of`: WP spec for `zError`, returning a
  valid NUL-terminated `CString` into one of the 10 `.ro .global` `z_errmsg` strings.
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec

/-! ## 1. Heap-Mutating Function-Body Spec Combinator -/

/-- Generalization of `FuncBodySpec` allowing heap allocations/frees between `m` and `m'`
while still guaranteeing safety, bounded termination, and caller stack-frame unwinding. -/
def HeapBodySpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (fn : FnDef)
    (Pre : Mem → List Val → Prop)
    (Post : Mem → List Val → Val → Mem → Prop) : Prop :=
  ∀ (args : List Val) (env : Env) (blks : List BlockId)
    (m m1 : Mem) (os : OSState)
    (base : Nat → UInt64) (callEnv : Env) (callBlks : List BlockId)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont)
    (Q : Val → Mem → OSState → Prop),
    Pre m args →
    args.length = fn.params.length →
    Sem.pushCallParams prog.tags m base 0 (fn.params.zip args)
        (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv, callBlks, m1) →
    (∀ ret m', Post m args ret m' →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os k)) →
    WPTerm prog cfg ext Q
      (.running (.stmt fn.body) callEnv callBlks m1 os
        (.callFrame env blks fn.retTy fn.body fs ctx k))

theorem HeapBodySpec.call
    {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (hspec : HeapBodySpec prog cfg ext fn Pre Post)
    {s : Sem.RunState} {sym : String} {fnTy : CTy} {argVals : List (Val × CTy)}
    {coerced : List Val} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    (hstep : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false argVals = some coerced)
    (hpre : Pre m coerced)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hcont : ∀ ret m', Post m coerced ret m' →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os k)) :
    WPTerm prog cfg ext Q s := by
  have ⟨hlenC, _⟩ := coerceCallArgs_length hcoerce
  simp only [List.length_map] at hlenC
  have htake : List.take fn.params.length coerced = coerced :=
    List.take_of_length_le (by omega)
  have hawt : Zlib.Spec.ArgsWellTyped (fn.params.map (·.ty)) false coerced :=
    coerceCallArgs_produces_argsWellTyped hcoerce
  have hex0 : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip coerced)
        (prog.fnStatics sym ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') := by
    rw [← hsym]
    exact pushCallParams_exists_base0 prog.tags hsimp hawt
  apply WPTerm.of_call_internal hstep hfn (by simpa [hnonvar] using hcoerce)
    (by simpa [htake] using hex0)
  intro base callEnv callBlks m1 hpush
  rw [htake, ← hsym] at hpush
  exact hspec coerced env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlenC hpush hcont

/-! ## 2. `zlibExt` & `Libc.ExtStep` Rules (`malloc`, `calloc`, `free`) -/

theorem zlibExt_malloc (userExt : ExtHandler) :
    Zlib.Spec.zlibExt userExt "malloc" = Libc.ExtStep "malloc" := by
  funext args m os out
  simp [Zlib.Spec.zlibExt, Zlib.Spec.isStdLibcSym, stdLibcProtos]

theorem zlibExt_calloc (userExt : ExtHandler) :
    Zlib.Spec.zlibExt userExt "calloc" = Libc.ExtStep "calloc" := by
  funext args m os out
  simp [Zlib.Spec.zlibExt, Zlib.Spec.isStdLibcSym, stdLibcProtos]

theorem zlibExt_free (userExt : ExtHandler) :
    Zlib.Spec.zlibExt userExt "free" = Libc.ExtStep "free" := by
  funext args m os out
  simp [Zlib.Spec.zlibExt, Zlib.Spec.isStdLibcSym, stdLibcProtos]

/-- Exact postcondition of a valid `malloc(n)` transition in `C99.Libc.ExtStep`. -/
def MallocOutcome (n : Nat) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  ((ret = .null ∧ m' = m) ∨
   (∃ (bid : BlockId) (blk : Block),
     ret = .ptr bid 0 ∧
     bid = m.nextBlock ∧
     m.blocks bid = none ∧
     m'.nextBlock = m.nextBlock + 1 ∧
     m'.blocks bid = some blk ∧
     blk.kind = .heap ∧
     blk.perm = .rw ∧
     blk.size = n ∧
     blk.align = 16 ∧
     blk.baseAddr.toNat % 16 = 0 ∧
     (∀ i, blk.bytes i = .undef) ∧
     (∀ b < m.nextBlock, m'.blocks b = m.blocks b) ∧
     (∀ b ≠ bid, m'.blocks b = m.blocks b)))

theorem extStep_malloc_has_outcome (n : BitVec 64) (m : Mem) (os : OSState) :
    ∃ ret m' os', Libc.ExtStep "malloc" [.int .u64 n] m os (.ok ret m' os') := by
  refine ⟨.null, m, os, ?_⟩
  have hn : BitVec.ofNat 64 n.toNat = n := by
    apply BitVec.eq_of_toNat_eq
    simp
  simpa [Libc.ExtStep, hn] using Libc.ExtOk.malloc_null n.toNat m os

theorem extStep_malloc_not_ub (n : BitVec 64) (m : Mem) (os : OSState) :
    ¬ Libc.ExtStep "malloc" [.int .u64 n] m os .ub :=
  fun hub => hub (extStep_malloc_has_outcome n m os)

theorem extStep_malloc_ok_inv {n : BitVec 64} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (h : Libc.ExtStep "malloc" [.int .u64 n] m os (.ok ret m' os')) :
    MallocOutcome n.toNat m os ret m' os' := by
  have hok : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "malloc" → args = [.int .u64 n] → MallocOutcome n.toNat mA osA retA mB osB := by
    intro fn args mA osA retA mB osB hext
    cases hext <;> intro hfn hargs
    case malloc_null =>
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    case malloc_ok k hsz base hba bid halloc =>
      injection hargs with hhead
      injection hhead with _ hbv
      have hkn : k = n.toNat := by
        have hto := congrArg BitVec.toNat hbv
        have hlt64 : k < 2 ^ 64 := Nat.lt_trans hsz (by rw [ptrDiffLimit_val]; decide)
        simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] using hto
      subst hkn
      have hbid : bid = mA.nextBlock := (congrArg Prod.fst halloc).symm
      have hmB : mB = (mA.alloc n.toNat 16 .rw .heap base (fun _ => .undef) hsz (by decide) hba).2 :=
        (congrArg Prod.snd halloc).symm
      subst hbid hmB
      refine ⟨rfl, Or.inr ⟨mA.nextBlock, ⟨n.toNat, 16, .rw, .heap, base, (fun _ => .undef), hsz, by decide, hba⟩,
        rfl, rfl, mA.fresh mA.nextBlock (Nat.le_refl _), rfl,
        alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl, rfl, rfl, rfl, hba,
        fun _ => rfl,
        fun b hb => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hb),
        fun b hne => alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne⟩⟩
    case lseek_ok =>
      subst hfn
      exact absurd (by assumption : "malloc" = "lseek" ∨ "malloc" = "lseek64") (by decide)
    case printf_zero =>
      subst hfn
      exact absurd (by assumption : "malloc" = "snprintf" ∨ "malloc" = "vsnprintf") (by decide)
    case printf_ok =>
      subst hfn
      exact absurd (by assumption : "malloc" = "snprintf" ∨ "malloc" = "vsnprintf") (by decide)
    all_goals exact absurd hfn (by decide)
  exact hok h rfl rfl

/-- Precondition for `free(ptr)`: either `NULL` or base offset `0` of a live `.heap` block. -/
def FreePre (m : Mem) (ptr : Val) : Prop :=
  ptr = .null ∨ ∃ b blk, ptr = .ptr b 0 ∧ m.blocks b = some blk ∧ blk.kind = .heap

/-- Exact postcondition of a valid `free(ptr)` transition in `C99.Libc.ExtStep`. -/
def FreeOutcome (ptr : Val) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .void ∧ os' = os ∧
  ((ptr = .null ∧ m' = m) ∨
   (∃ b blk, ptr = .ptr b 0 ∧ m.blocks b = some blk ∧ blk.kind = .heap ∧
     m.free b = some m' ∧ m'.nextBlock = m.nextBlock ∧ m'.blocks b = none ∧
     ∀ b' ≠ b, m'.blocks b' = m.blocks b'))

theorem mem_free_eq_some {m : Mem} {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) (hk : blk.kind = .heap) :
    ∃ m', m.free b = some m' := by
  simp [Mem.free, hb, hk]

theorem mem_free_inv {m m' : Mem} {b : BlockId} (h : m.free b = some m') :
    (∃ blk, m.blocks b = some blk ∧ blk.kind = .heap) ∧
    m'.nextBlock = m.nextBlock ∧ m'.blocks b = none ∧ ∀ b' ≠ b, m'.blocks b' = m.blocks b' := by
  simp only [Mem.free] at h
  cases hb : m.blocks b with
  | none => simp [hb] at h
  | some blk =>
    simp only [hb] at h
    cases hk : blk.kind with
    | heap =>
      simp only [hk, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst m'
      refine ⟨⟨blk, rfl, hk⟩, rfl, by simp, fun b' hne => ?_⟩
      simp [beq_false_of_ne hne]
    | stack | global =>
      simp [hk] at h

theorem extStep_free_has_outcome {m : Mem} {ptr : Val} (os : OSState) (hp : FreePre m ptr) :
    ∃ ret m' os', Libc.ExtStep "free" [ptr] m os (.ok ret m' os') := by
  rcases hp with rfl | ⟨b, blk, rfl, hb, hk⟩
  · exact ⟨.void, m, os, Libc.ExtOk.free_null m os⟩
  · obtain ⟨m', hfree⟩ := mem_free_eq_some hb hk
    exact ⟨.void, m', os, Libc.ExtOk.free_ok b m m' os hfree⟩

theorem extStep_free_not_ub {m : Mem} {ptr : Val} (os : OSState) (hp : FreePre m ptr) :
    ¬ Libc.ExtStep "free" [ptr] m os .ub :=
  fun hub => hub (extStep_free_has_outcome os hp)

theorem extStep_free_ok_inv {ptr : Val} {m : Mem} {os : OSState}
    {ret : Val} {m' : Mem} {os' : OSState}
    (h : Libc.ExtStep "free" [ptr] m os (.ok ret m' os')) :
    FreeOutcome ptr m os ret m' os' := by
  have hok : ∀ {fn args mA osA retA mB osB}, Libc.ExtOk fn args mA osA retA mB osB →
      fn = "free" → args = [ptr] → FreeOutcome ptr mA osA retA mB osB := by
    intro fn args mA osA retA mB osB hext
    cases hext <;> intro hfn hargs
    case free_null =>
      injection hargs with hhead
      exact ⟨rfl, rfl, Or.inl ⟨hhead.symm, rfl⟩⟩
    case free_ok b hfree =>
      injection hargs with hhead
      obtain ⟨⟨blk, hb, hk⟩, hnext, hnone, hpres⟩ := mem_free_inv hfree
      exact ⟨rfl, rfl, Or.inr ⟨b, blk, hhead.symm, hb, hk, hfree, hnext, hnone, hpres⟩⟩
    case lseek_ok =>
      subst hfn
      exact absurd (by assumption : "free" = "lseek" ∨ "free" = "lseek64") (by decide)
    case printf_zero =>
      subst hfn
      exact absurd (by assumption : "free" = "snprintf" ∨ "free" = "vsnprintf") (by decide)
    case printf_ok =>
      subst hfn
      exact absurd (by assumption : "free" = "snprintf" ∨ "free" = "vsnprintf") (by decide)
    all_goals exact absurd hfn (by decide)
  exact hok h rfl rfl

/-! ## 3. Shared Lookup & Stack-Slot Helpers for `zutil.c` -/

private def enumListHas (name : String) : List (String × Option Int) → Bool
  | [] => false
  | (k, _) :: tl => (k == name) || enumListHas name tl

private def envHasEnumConst (name : String) : TypeEnv → Bool
  | [] => false
  | (_, .enumDef items _) :: rest => enumListHas name items || envHasEnumConst name rest
  | _ :: rest => envHasEnumConst name rest

private theorem enumConst_none_of_false {tags : TypeEnv} {name : String}
    (h : envHasEnumConst name tags = false) : enumConst? tags name = none := by
  induction tags with
  | nil => simp [enumConst?]
  | cons hd tl ih =>
    rcases hd with ⟨tag, defn⟩
    cases defn with
    | structDef _ => simpa [enumConst?] using ih h
    | unionDef _ => simpa [enumConst?] using ih h
    | enumDef items isU =>
      unfold envHasEnumConst at h
      simp only [Bool.or_eq_false_iff] at h
      have htail := ih h.2
      have hitems := h.1
      clear h
      have hscan : ∀ nextVal items0, enumListHas name items0 = false →
          enumConst?.scan tl name nextVal items0 = none := by
        intro nextVal items0 hi
        induction items0 generalizing nextVal with
        | nil => simpa [enumConst?.scan] using htail
        | cons it rest ihr =>
          rcases it with ⟨k, v?⟩
          unfold enumListHas at hi
          simp only [Bool.or_eq_false_iff] at hi
          have hne : (k == name) = false := hi.1
          simp [enumConst?.scan, hne, ihr _ hi.2]
      simpa [enumConst?] using hscan 0 items hitems

theorem enumConst_progTags_malloc (tags : TypeEnv) (ht : tags = (progOfTUs Zlib.allFiles).tags) :
    enumConst? tags "malloc" = none := by
  rw [ht, progOfTUs_tags]
  exact enumConst_none_of_false (by decide)

theorem enumConst_progTags_free (tags : TypeEnv) (ht : tags = (progOfTUs Zlib.allFiles).tags) :
    enumConst? tags "free" = none := by
  rw [ht, progOfTUs_tags]
  exact enumConst_none_of_false (by decide)

private theorem readVal_u32_of_write_fresh {tags : TypeEnv} {m m' : Mem}
    {ty : CTy} {ba : UInt64} {v : BitVec 32}
    {hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags ty)}
    {hba : ba.toNat % max 1 (alignofTy tags ty) = 0}
    (hty : ty.unqual = .int .u32)
    (hwr : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 ty.stripConst (.int .u32 v) = some m') :
    Sem.readVal tags m' m.nextBlock 0 ty = some (.int .u32 v) := by
  have hblk : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock =
      some ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, ba,
        (fun _ => .undef), hsz, hal, hba⟩ := alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hwr_u32 : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 (.int .u32) (.int .u32 v) = some m' := by
    have hc : ty.stripConst.isConst = false := stripConst_isConst ty
    have hu : ty.stripConst.unqual = .int .u32 := by rw [stripConst_unqual, hty]
    unfold Sem.writeVal at hwr ⊢
    simp only [hc, Bool.not_false, guard_true, hu] at hwr
    exact hwr
  have hrd := readVal_writeVal_same_int tags hblk hwr_u32
  simp only [Sem.readVal, hty, CTy.unqual] at hrd ⊢
  exact hrd

private theorem readVal_i32_of_write_fresh {tags : TypeEnv} {m m' : Mem}
    {ty : CTy} {ba : UInt64} {v : BitVec 32}
    {hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags ty)}
    {hba : ba.toNat % max 1 (alignofTy tags ty) = 0}
    (hty : ty.unqual = .int .i32)
    (hwr : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 ty.stripConst (.int .i32 v) = some m') :
    Sem.readVal tags m' m.nextBlock 0 ty = some (.int .i32 v) := by
  have hblk : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock =
      some ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, ba,
        (fun _ => .undef), hsz, hal, hba⟩ := alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hwr_i32 : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 (.int .i32) (.int .i32 v) = some m' := by
    have hc : ty.stripConst.isConst = false := stripConst_isConst ty
    have hu : ty.stripConst.unqual = .int .i32 := by rw [stripConst_unqual, hty]
    unfold Sem.writeVal at hwr ⊢
    simp only [hc, Bool.not_false, guard_true, hu] at hwr
    exact hwr
  have hrd := readVal_writeVal_same_int tags hblk hwr_i32
  simp only [Sem.readVal, hty, CTy.unqual] at hrd ⊢
  exact hrd

private theorem isAligned_with_bytes (blk : Block) (f : Nat → MemByte) (off : Int64) (align : Nat)
    (h : Mem.isAligned blk off align = true) :
    Mem.isAligned { blk with bytes := f } off align = true := by
  simpa [Mem.isAligned] using h

private theorem blockId_lt_add2 {b n0 n1 n2 : Nat}
    (h1 : n1 = n0 + 1) (h2 : n2 = n1 + 1) (hlt : b < n2) (hge : ¬ b < n0) :
    b = n0 ∨ b = n1 := by omega

private theorem blockId_lt_add3 {b n0 n1 n2 n3 : Nat}
    (h1 : n1 = n0 + 1) (h2 : n2 = n1 + 1) (h3 : n3 = n2 + 1) (hlt : b < n3) (hge : ¬ b < n0) :
    b = n0 ∨ b = n1 ∨ b = n2 := by omega

private theorem blockId_le_add3 {bid n0 n1 n2 n3 : Nat}
    (hb : bid = n3) (h1 : n1 = n0 + 1) (h2 : n2 = n1 + 1) (h3 : n3 = n2 + 1) :
    n0 ≤ bid := by omega

private theorem readVal_ptr_of_write_fresh {tags : TypeEnv} {m m' : Mem}
    {ty el : CTy} {ba : UInt64} {v : Val}
    {hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags ty)}
    {hba : ba.toNat % max 1 (alignofTy tags ty) = 0}
    (hty : ty.unqual = .ptr el)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hwr : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 ty.stripConst v = some m') :
    Sem.readVal tags m' m.nextBlock 0 ty = some v := by
  let blk0 : Block := ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, ba,
    (fun _ => .undef), hsz, hal, hba⟩
  have hblk : (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba).2.blocks m.nextBlock =
      some blk0 := alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hc : ty.stripConst.isConst = false := stripConst_isConst ty
  have hu : ty.stripConst.unqual = .ptr el := by rw [stripConst_unqual, hty]
  unfold Sem.writeVal at hwr
  simp only [hc, Bool.not_false, hblk, hu, bind, Option.bind, guard, Pure.pure] at hwr
  have hal8 : Mem.isAligned blk0 0 8 = true := by
    cases hg : Mem.isAligned blk0 0 8 <;> simp_all
  simp only [hal8, ↓reduceIte] at hwr
  rcases hv with rfl | ⟨pb, poff, rfl⟩
  · have hrb := readBytes_writeBytes_same hblk hwr
    have hblk' := writeBytes_blocks_eq hblk hwr
    unfold Sem.readVal
    simp only [hty, hblk', bind, Option.bind]
    rw [isAligned_with_bytes blk0 _ 0 8 hal8]
    simp only [guard_true]
    rw [show (8 : Nat) = Mem.encodeNull.length from rfl, hrb]
    dsimp [pure]
    rw [decodePtr_encodeNull]
  · have hrb := readBytes_writeBytes_same hblk hwr
    have hblk' := writeBytes_blocks_eq hblk hwr
    unfold Sem.readVal
    simp only [hty, hblk', bind, Option.bind]
    rw [isAligned_with_bytes blk0 _ 0 8 hal8]
    simp only [guard_true]
    rw [show (8 : Nat) = (Mem.encodePtr pb poff).length from rfl, hrb]
    dsimp [pure]
    rw [decodePtr_encodePtr]

/-! ## 4. `zcalloc` -/

/-- Exact postcondition for `zcalloc(opaque, items, size)` after stack unwinding:
either `.null` with all blocks preserved (`ROExt m m'`), or a fresh `.rw .heap` block
`bid` of size `(items * size) % 2^32` with all other blocks identical to `m`. -/
def ZcallocPost (m : Mem) (items size : BitVec 32) (ret : Val) (m' : Mem) : Prop :=
  (ret = .null ∧ ROExt m m' ∧ ∀ b, m'.blocks b = m.blocks b) ∨
  (∃ (bid : BlockId) (blk : Block),
    ret = .ptr bid 0 ∧
    m.blocks bid = none ∧
    m.nextBlock ≤ bid ∧
    m'.nextBlock = bid + 1 ∧
    m'.blocks bid = some blk ∧
    blk.kind = .heap ∧
    blk.perm = .rw ∧
    blk.size = (items.toNat * size.toNat) % 2 ^ 32 ∧
    blk.align = 16 ∧
    blk.baseAddr.toNat % 16 = 0 ∧
    (∀ i, blk.bytes i = .undef) ∧
    (∀ b < m.nextBlock, m'.blocks b = m.blocks b) ∧
    (∀ b ≠ bid, m'.blocks b = m.blocks b))

theorem ZcallocPost.framePreserved {m m' : Mem} {items size : BitVec 32} {ret : Val}
    (hp : ZcallocPost m items size ret m') :
    Zlib.Spec.FramePreserved m m' (fun b => ∃ bid, ret = .ptr bid 0 ∧ b = bid) := by
  rcases hp with ⟨rfl, _, hblks⟩ | ⟨bid, blk, rfl, hnone, _, _, hsome, _, _, _, _, _, _, _, hne⟩
  · exact ⟨fun b _ _ => hblks b, fun b blk hn hs _ => by rw [hblks b, hn] at hs; cases hs⟩
  · refine ⟨?_, ?_⟩
    · intro b _ hnot
      have hne' : b ≠ bid := fun heq => hnot ⟨bid, rfl, heq⟩
      exact hne b hne'
    · intro b blk' hn hs hnot
      have hne' : b ≠ bid := fun heq => hnot ⟨bid, rfl, heq⟩
      rw [hne b hne', hn] at hs
      cases hs

theorem ZcallocPost.noHeapLeak {m m' : Mem} {items size : BitVec 32} {ret : Val}
    (hp : ZcallocPost m items size ret m') (owned : Zlib.Spec.BlockSet) :
    Zlib.Spec.NoHeapLeak m m' (fun b => owned b ∨ ∃ bid, ret = .ptr bid 0 ∧ b = bid) := by
  rcases hp with ⟨_, _, hblks⟩ | ⟨bid, _, rfl, _, _, _, _, _, _, _, _, _, _, _, hne⟩
  · intro b blk hs _
    left
    rw [hblks b] at hs
    simp [hs]
  · intro b blk hs _
    by_cases hbb : b = bid
    · right; exact Or.inr ⟨bid, rfl, hbb⟩
    · left
      rw [hne b hbb] at hs
      simp [hs]

theorem ZcallocPost.baseInv {m0 m m' : Mem} {os0 os : OSState} {v : Zlib.Spec.ClientView}
    {owned owned' : Zlib.Spec.BlockSet} {items size : BitVec 32} {ret : Val}
    (hb : BaseInv m0 os0 v owned m os)
    (hp : ZcallocPost m items size ret m')
    (hown : ∀ b, owned' b ↔ owned b ∨ ∃ bid, ret = .ptr bid 0 ∧ b = bid)
    (hempty : v.isEmpty → ∀ b, ¬ owned' b) :
    BaseInv m0 os0 v owned' m' os := by
  rcases hp with ⟨rfl, _, hblks⟩ | ⟨bid, blk, rfl, hnone, _, _, hsome, _, _, _, _, _, _, _, hne⟩
  · refine ⟨fun b hm0 hne0 => by rw [hblks b]; exact hb.roGlobals b hm0 hne0,
      hb.errnoBlkEq, ?_, ?_, hempty⟩
    · rcases hb.errnoValid with ⟨eblk, heblk, he⟩
      exact ⟨eblk, by rw [hblks os.errnoBlk]; exact heblk, he⟩
    · intro b hb'
      rw [hown] at hb'
      rcases hb' with ho | ⟨_, hcontra, _⟩
      · rw [hblks b]; exact hb.ownedActive b ho
      · cases hcontra
  · have hbid_ne_m0 : ∀ b, (m0.blocks b).isSome = true → b ≠ bid := by
      intro b hm0 heq
      subst heq
      rcases Option.isSome_iff_exists.mp hm0 with ⟨gblk, hgblk⟩
      have hne0 : b ≠ os0.errnoBlk → m.blocks b = m0.blocks b := hb.roGlobals b hm0
      by_cases hb0 : b = os0.errnoBlk
      · subst hb0
        rcases hb.errnoValid with ⟨eblk, heblk, _⟩
        rw [hb.errnoBlkEq, hnone] at heblk
        cases heblk
      · rw [hne0 hb0, hgblk] at hnone
        cases hnone
    have hbid_ne_err : os.errnoBlk ≠ bid := by
      rcases hb.errnoValid with ⟨eblk, heblk, _⟩
      intro heq
      rw [heq, hnone] at heblk
      cases heblk
    refine ⟨?_, hb.errnoBlkEq, ?_, ?_, hempty⟩
    · intro b hm0 hne0
      rw [hne b (hbid_ne_m0 b hm0)]
      exact hb.roGlobals b hm0 hne0
    · rcases hb.errnoValid with ⟨eblk, heblk, he⟩
      exact ⟨eblk, by rw [hne os.errnoBlk hbid_ne_err]; exact heblk, he⟩
    · intro b hb'
      rw [hown] at hb'
      rcases hb' with ho | ⟨bid', hinj, hbb⟩
      · have hact := hb.ownedActive b ho
        have hnb : b ≠ bid := fun heq => by subst heq; simp [hnone] at hact
        rw [hne b hnb]
        exact hact
      · cases hinj
        subst hbb
        simp [hsome]

theorem zcalloc_params_simple :
    ∀ p ∈ Zlib.Zutil.zutilTU_fn_zcalloc.params, IsSimpleParamTy p.ty := by
  intro p hp
  simp only [Zlib.Zutil.zutilTU_fn_zcalloc, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]

theorem zcalloc_spec_of {prog : Prog} {userExt : ExtHandler}
    (hfns : prog.fns "malloc" = none)
    (hproto : prog.fnProtos "malloc" = some (.ptr .void, [.int .u64], false))
    (henum : enumConst? prog.tags "malloc" = none)
    (hstat : (prog.fnStatics "zcalloc").lookup "malloc" = none)
    (hglob : prog.globalEnv.lookup "malloc" = none) :
    HeapBodySpec prog zlibPointerConfig (Zlib.Spec.zlibExt userExt) Zlib.Zutil.zutilTU_fn_zcalloc
      (fun _ args => ∃ op items size,
        args = [op, .int .u32 items, .int .u32 size] ∧ (op = .null ∨ ∃ b off, op = .ptr b off))
      (fun m args ret m' => match args with
        | [_, .int .u32 items, .int .u32 size] => ZcallocPost m items size ret m'
        | _ => False) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  rcases hpre with ⟨op, items, size, rfl, hop⟩
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  dsimp only [Zlib.Zutil.zutilTU_fn_zcalloc] at hpush
  rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons, List.zip_nil_right] at hpush
  obtain ⟨hsz0, hal0, hba0, m_op, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_it, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m_sz, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  simp only [pushCallParams_zero, Option.some.injEq, Prod.mk.injEq] at hpush3
  rcases hpush3 with ⟨rfl, hcallBlks, hm1_eq⟩
  subst m_sz
  have hm_op_next : m_op.nextBlock = m.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr0, alloc_snd_nextBlock]
  have hm_it_next : m_it.nextBlock = m_op.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr1, alloc_snd_nextBlock]
  have hm1_next : m1.nextBlock = m_it.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr2, alloc_snd_nextBlock]
  have hlt01 : m.nextBlock < m_op.nextBlock := hm_op_next ▸ Nat.lt_succ_self _
  have hlt12 : m_op.nextBlock < m_it.nextBlock := hm_it_next ▸ Nat.lt_succ_self _
  have hlt02 : m.nextBlock < m_it.nextBlock := Nat.lt_trans hlt01 hlt12
  have hne01 : m.nextBlock ≠ m_op.nextBlock := Nat.ne_of_lt hlt01
  have hne02 : m.nextBlock ≠ m_it.nextBlock := Nat.ne_of_lt hlt02
  have hne12 : m_op.nextBlock ≠ m_it.nextBlock := Nat.ne_of_lt hlt12
  have hrd_op_0 : Sem.readVal prog.tags m_op m.nextBlock 0 (.typedef "voidpf" (.ptr .void)) = some op :=
    readVal_ptr_of_write_fresh rfl hop hwr0
  have hrd_op_1 : Sem.readVal prog.tags m_it m.nextBlock 0 (.typedef "voidpf" (.ptr .void)) = some op := by
    have heq : m_it.blocks m.nextBlock = m_op.blocks m.nextBlock := by
      rw [writeVal_blocks_ne hwr1 hne01, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne01]
    rw [readVal_eq_of_blocks_eq prog.tags heq]; exact hrd_op_0
  have hrd_op : Sem.readVal prog.tags m1 m.nextBlock 0 (.typedef "voidpf" (.ptr .void)) = some op := by
    have heq : m1.blocks m.nextBlock = m_it.blocks m.nextBlock := by
      rw [writeVal_blocks_ne hwr2 hne02, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne02]
    rw [readVal_eq_of_blocks_eq prog.tags heq]; exact hrd_op_1
  have hrd_it_1 : Sem.readVal prog.tags m_it m_op.nextBlock 0 (.int .u32) = some (.int .u32 items) :=
    readVal_u32_of_write_fresh rfl hwr1
  have hrd_it : Sem.readVal prog.tags m1 m_op.nextBlock 0 (.int .u32) = some (.int .u32 items) := by
    have heq : m1.blocks m_op.nextBlock = m_it.blocks m_op.nextBlock := by
      rw [writeVal_blocks_ne hwr2 hne12, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne12]
    rw [readVal_eq_of_blocks_eq prog.tags heq]; exact hrd_it_1
  have hrd_sz : Sem.readVal prog.tags m1 m_it.nextBlock 0 (.int .u32) = some (.int .u32 size) :=
    readVal_u32_of_write_fresh rfl hwr2
  -- Step `(void)opaque;`
  wp_steps
  refine WPTerm.of_exprPure
    (es' := .ret (.rval op (.ptr .void)) [.castF .void]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [List.lookup, ModSet.conflicts, hrd_op, CTy.decay, CTy.unqual]
  have hcast_void : Sem.castVal m1 .void op = some .void := by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid]
  refine WPTerm.of_exprPure
    (es' := .ret (.rval .void .void) []) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure; dsimp only; rw [hcast_void]; rfl
  -- Step `sizeof(uInt) > 2 ? (voidpf)malloc(items * size) : (voidpf)calloc(items, size)`
  wp_steps
  have huIntSz : sizeofTy prog.tags (.typedef "uInt" (.int .u32)) = 4 := by
    rw [← sizeofTy_unqual]; simp [CTy.unqual]; rfl
  rw [huIntSz]
  wp_steps
  -- Resolve `malloc` function pointer
  have hluNone : ((("size", m_it.nextBlock, CTy.int .u32) ::
      ("items", m_op.nextBlock, CTy.int .u32) ::
      ("opaque", m.nextBlock, CTy.typedef "voidpf" (CTy.ptr .void)) ::
      (prog.fnStatics "zcalloc" ++ prog.globalEnv)).lookup "malloc") = none := by
    simp only [List.lookup, show ("malloc" == "size") = false from rfl,
      show ("malloc" == "items") = false from rfl,
      show ("malloc" == "opaque") = false from rfl]
    rw [lookup_append_none hstat, hglob]
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.fnPtr "malloc") (.fnPtr (.ptr .void) [.int .u64] false))
      [.callFnF [.binary .mul (.var "items") (.var "size")],
       .castF (.typedef "voidpf" (.ptr .void))]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure
    simp [hluNone, henum, hproto]
  wp_steps
  -- Read `items` and `size`
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.int .u32 items) (.int .u32))
      [.binLhsF .mul (.var "size"),
       .callArgF "malloc" (.fnPtr (.ptr .void) [.int .u64] false) [] [],
       .castF (.typedef "voidpf" (.ptr .void))]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [List.lookup, show ("items" == "size") = false from rfl,
      ModSet.conflicts, hrd_it, CTy.decay, CTy.unqual]
  wp_steps
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.int .u32 size) (.int .u32))
      [.binRhsF .mul (.int .u32 items) (.int .u32),
       .callArgF "malloc" (.fnPtr (.ptr .void) [.int .u64] false) [] [],
       .castF (.typedef "voidpf" (.ptr .void))]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [List.lookup, ModSet.conflicts, hrd_sz, CTy.decay, CTy.unqual]
  let prod32 : BitVec 32 := BitVec.ofInt 32 ((items.toNat : Int) * (size.toNat : Int))
  have hmul : Sem.applyBinary zlibPointerConfig prog.tags m1 .mul
      (.int .u32 items) (.int .u32) (.int .u32 size) (.int .u32) =
      some (.int .u32 prod32, .int .u32) := by
    unfold Sem.applyBinary Sem.evalIntBinary
    have hua : IntKind.usualArith .u32 .u32 = .u32 := rfl
    simp only [CTy.isPtr, CTy.unqual, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      Sem.valAsInt?, bind, Option.bind]
    rw [hua]
    have hsig : IntKind.u32.signed = false := rfl
    simp only [hsig, Bool.false_eq_true, ↓reduceIte, Sem.ofIntExact, pure, Pure.pure, prod32]
    have hm1_it : ((BitVec.ofInt IntKind.u32.bits (items.toNat : Int)).toNat : Int) = (items.toNat : Int) := by
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast items.isLt),
        Int.toNat_natCast]
    have hm1_sz : ((BitVec.ofInt IntKind.u32.bits (size.toNat : Int)).toNat : Int) = (size.toNat : Int) := by
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast size.isLt),
        Int.toNat_natCast]
    rw [hm1_it, hm1_sz]
    rfl
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.int .u32 prod32) (.int .u32))
      [.callArgF "malloc" (.fnPtr (.ptr .void) [.int .u64] false) [] [],
       .castF (.typedef "voidpf" (.ptr .void))]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure
    dsimp only
    rw [hmul]
    rfl
  -- External call `malloc(prod32)`
  let arg64 : BitVec 64 := BitVec.ofNat 64 prod32.toNat
  have hcoerce : Sem.coerceCallArgs m1 [.int .u64] false [(.int .u32 prod32, .int .u32)] =
      some [.int .u64 arg64] := by
    refine coerceCallArgs_cons_nonvariadic ?_ (coerceCallArgs_nil m1)
    simp only [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast]
    congr 1
  obtain ⟨ret0, m0', os0', hex0⟩ := extStep_malloc_has_outcome arg64 m1 os
  have hnoub : ¬ Zlib.Spec.zlibExt userExt "malloc" [.int .u64 arg64] m1 os .ub := by
    rw [zlibExt_malloc]
    exact extStep_malloc_not_ub arg64 m1 os
  let env1 : Env :=
    ("size", m_it.nextBlock, CTy.int .u32) ::
    ("items", m_op.nextBlock, CTy.int .u32) ::
    ("opaque", m.nextBlock, CTy.typedef "voidpf" (CTy.ptr .void)) ::
    (prog.fnStatics "zcalloc" ++ prog.globalEnv)
  let k1 : Cont := .stmts [] (.blockEnd env1 callBlks
    (.callFrame env blks Zlib.Zutil.zutilTU_fn_zcalloc.retTy
      Zlib.Zutil.zutilTU_fn_zcalloc.body fs ctx k))
  have hdet : Sem.stepDet prog zlibPointerConfig
      (.running (.expr (.ret (.rval (.int .u32 prod32) (.int .u32))
          [.callArgF "malloc" (.fnPtr (.ptr .void) [.int .u64] false) [] [],
           .castF (.typedef "voidpf" (.ptr .void))]) .returnVal [])
        env1 [] m1 os k1) =
      some (.callFn "malloc" (.fnPtr (.ptr .void) [.int .u64] false)
        [(.int .u32 prod32, .int .u32)] [.castF (.typedef "voidpf" (.ptr .void))]
        .returnVal env1 [] m1 os k1) := rfl
  refine WPTerm.of_call_ext (fnTy := .fnPtr (.ptr .void) [.int .u64] false)
    hdet hfns rfl hcoerce
    ⟨ret0, m0', os0', by rw [zlibExt_malloc]; exact hex0⟩ hnoub ?_
  intro ret m2 os2 hext
  rw [zlibExt_malloc] at hext
  obtain ⟨hos2, hmalloc⟩ := extStep_malloc_ok_inv hext
  subst os2
  have hprod_nat : arg64.toNat = (items.toNat * size.toNat) % 2 ^ 32 := by
    have hp : prod32.toNat = (items.toNat * size.toNat) % 2 ^ 32 := by
      dsimp [prod32]
      rw [← Int.natCast_mul, BitVec.toNat_ofInt, ← Int.natCast_emod, Int.toNat_natCast]
    have hlt64 : prod32.toNat < 2 ^ 64 := Nat.lt_trans prod32.isLt (by decide)
    dsimp [arg64]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, hp]
  -- Cast `(voidpf)ret` and unwind call frame
  rcases hmalloc with ⟨rfl, hm2_eq⟩ |
      ⟨bid, blk, rfl, hbid_eq, _, hm2_next, hm2_bid, hkind, hperm, hsz_blk, hal_blk,
       hba_blk, hbytes, hm2_lt, hm2_ne⟩
  · -- Null return
    subst m2
    refine WPTerm.of_exprPure
      (es' := .ret (.rval .null (.typedef "voidpf" (.ptr .void))) []) (m' := m1) (mods' := []) ?_ ?_
    · unfold Sem.stepExprPure
      dsimp only
      rw [castVal_unqual]; simp [CTy.unqual]
    have hro : ROExt m (m1.freeStack callBlks) := LocalFrameMem.roExt_freeStack hf1
    have hblks : ∀ b, (m1.freeStack callBlks).blocks b = m.blocks b := by
      intro b
      by_cases hlt : b < m.nextBlock
      · exact hro.2.1 b hlt
      · have hm_none : m.blocks b = none := m.fresh b (Nat.le_of_not_lt hlt)
        rw [hm_none]
        by_cases hm1 : b < m1.nextBlock
        · cases hblk_m1 : (m1.freeStack callBlks).blocks b with
          | none => rfl
          | some blk' =>
            have hro' := hro.2.2 b blk' (Nat.le_of_not_lt hlt) hblk_m1
            have hmem_or := hf1.2.2.2.2 b blk' (Nat.le_of_not_lt hlt) (by
              by_cases hmem : b ∈ callBlks
              · obtain ⟨_, blk0, hb0, hk0⟩ := hf1.2.2.2.1 b hmem
                rw [freeStack_blocks_mem_stack m1 callBlks hmem hb0 hk0] at hblk_m1
                cases hblk_m1
              · rw [freeStack_blocks_not_mem m1 callBlks hmem] at hblk_m1
                exact hblk_m1)
            rcases hmem_or with ⟨hk0, hmem⟩ | ⟨_, hro_perm⟩
            · exfalso
              have h0 : blk'.kind = .stack := hk0
              have h1 : blk'.kind = .global := hro'.1
              rw [h1] at h0
              cases h0
            · exfalso
              by_cases hmem : b ∈ callBlks
              · obtain ⟨_, blk0, hb0, hk0⟩ := hf1.2.2.2.1 b hmem
                rw [freeStack_blocks_mem_stack m1 callBlks hmem hb0 hk0] at hblk_m1
                cases hblk_m1
              · rw [freeStack_blocks_not_mem m1 callBlks hmem] at hblk_m1
                rcases hf1.2.2.2.2 b blk' (Nat.le_of_not_lt hlt) hblk_m1 with ⟨hk_s, _⟩ | ⟨hk_g, _⟩
                · exact absurd (hk_s.symm.trans hro'.1) (by decide)
                · have hnat := blockId_lt_add3 hm_op_next hm_it_next hm1_next hm1 hlt
                  rw [← hcallBlks] at hmem
                  rcases hnat with rfl | rfl | rfl
                  · exact hmem (.tail _ (.tail _ (.head _)))
                  · exact hmem (.tail _ (.head _))
                  · exact hmem (.head _)
        · exact (m1.freeStack callBlks).fresh b (Nat.le_of_not_lt hm1)
    refine WPTerm.of_det
      (s' := .running (.expr (.ret (.rval .null Zlib.Zutil.zutilTU_fn_zcalloc.retTy) fs) ctx [])
        env blks (m1.freeStack callBlks) os k) ?_
      (hcont .null (m1.freeStack callBlks) (Or.inl ⟨rfl, hro, hblks⟩))
    unfold Sem.stepDet
    dsimp only [k1, env1]
    simp [Zlib.Zutil.zutilTU_fn_zcalloc, Sem.Cont.topRetTy, CTy.isVoid, CTy.unqual,
      Sem.unwindReturn, Sem.castVal, CTy.intKind?, freeStack_nil]
  · -- Heap block `bid` allocated
    refine WPTerm.of_exprPure
      (es' := .ret (.rval (.ptr bid 0) (.typedef "voidpf" (.ptr .void))) []) (m' := m2) (mods' := []) ?_ ?_
    · unfold Sem.stepExprPure
      dsimp only
      rw [castVal_unqual]; simp [CTy.unqual]
    have hbid_ge : m.nextBlock ≤ bid :=
      blockId_le_add3 hbid_eq hm_op_next hm_it_next hm1_next
    have hm_none : m.blocks bid = none := m.fresh bid hbid_ge
    have hfree_eq : ∀ b, (m2.freeStack callBlks).blocks b =
        if b = bid then some blk else m.blocks b := by
      intro b
      by_cases hbb : b = bid
      · subst hbb
        simp only [↓reduceIte]
        exact freeStack_blocks_mem_nonstack m2 callBlks hm2_bid (by rw [hkind]; decide)
      · simp only [hbb, ↓reduceIte]
        by_cases hmem : b ∈ callBlks
        · obtain ⟨_, blk0, hb0, hk0⟩ := hf1.2.2.2.1 b hmem
          have hlt0 : b < m1.nextBlock := lt_nextBlock_of_some hb0
          have hne0 : b ≠ bid := by rw [hbid_eq]; exact Nat.ne_of_lt hlt0
          have hm2b : m2.blocks b = some blk0 := by rw [hm2_ne b hne0, hb0]
          rw [freeStack_blocks_mem_stack m2 callBlks hmem hm2b hk0]
          have hge0 := (hf1.2.2.2.1 b hmem).1
          exact (m.fresh b hge0).symm
        · rw [freeStack_blocks_not_mem m2 callBlks hmem, hm2_ne b hbb]
          by_cases hlt : b < m.nextBlock
          · exact hf1.2.1 b hlt
          · have hm_none' : m.blocks b = none := m.fresh b (Nat.le_of_not_lt hlt)
            rw [hm_none']
            by_cases hm1 : b < m1.nextBlock
            · exfalso
              have hnat := blockId_lt_add3 hm_op_next hm_it_next hm1_next hm1 hlt
              rw [← hcallBlks] at hmem
              rcases hnat with rfl | rfl | rfl
              · exact hmem (.tail _ (.tail _ (.head _)))
              · exact hmem (.tail _ (.head _))
              · exact hmem (.head _)
            · exact m1.fresh b (Nat.le_of_not_lt hm1)
    have hpost : ZcallocPost m items size (.ptr bid 0) (m2.freeStack callBlks) := by
      refine Or.inr ⟨bid, blk, rfl, hm_none, hbid_ge, ?_, ?_, hkind, hperm,
        by rw [hsz_blk, hprod_nat]; rfl, hal_blk, hba_blk, hbytes, ?_, ?_⟩
      · rw [freeStack_nextBlock, hm2_next, hbid_eq]
      · simp only [hfree_eq bid, ↓reduceIte]
      · intro b hlt
        have hne : b ≠ bid := Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hbid_ge)
        simp only [hfree_eq b, hne, ↓reduceIte]
      · intro b hne
        simp only [hfree_eq b, hne, ↓reduceIte]
    refine WPTerm.of_det
      (s' := .running (.expr (.ret (.rval (.ptr bid 0) Zlib.Zutil.zutilTU_fn_zcalloc.retTy) fs) ctx [])
        env blks (m2.freeStack callBlks) os k) ?_
      (hcont (.ptr bid 0) (m2.freeStack callBlks) hpost)
    unfold Sem.stepDet
    dsimp only [k1, env1]
    simp [Zlib.Zutil.zutilTU_fn_zcalloc, Sem.Cont.topRetTy, CTy.isVoid, CTy.unqual,
      Sem.unwindReturn, Sem.castVal, CTy.intKind?, freeStack_nil]

theorem zcalloc_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    HeapBodySpec prog zlibPointerConfig (Zlib.Spec.zlibExt userExt) Zlib.Zutil.zutilTU_fn_zcalloc
      (fun _ args => ∃ op items size,
        args = [op, .int .u32 items, .int .u32 size] ∧ (op = .null ∨ ∃ b off, op = .ptr b off))
      (fun m args ret m' => match args with
        | [_, .int .u32 items, .int .u32 size] => ZcallocPost m items size ret m'
        | _ => False) :=
  zcalloc_spec_of (prog_fns_malloc hlib) (prog_fnProtos_malloc hlib)
    (enumConst_progTags_malloc prog.tags hlib.prog_tags_eq)
    (by rw [prog_fnStatics_zcalloc hlib]; rfl)
    (by rw [hlib.globalEnv_eq]; exact hlib.gEnv_lookup_none "malloc" (by decide))

/-! ## 5. `zcfree` -/

/-- Exact postcondition for `zcfree(opaque, ptr)` after stack unwinding. -/
def ZcfreePost (m : Mem) (ptr : Val) (ret : Val) (m' : Mem) : Prop :=
  ret = .void ∧
  ((ptr = .null ∧ ROExt m m' ∧ ∀ b, m'.blocks b = m.blocks b) ∨
   (∃ b blk, ptr = .ptr b 0 ∧ m.blocks b = some blk ∧ blk.kind = .heap ∧
     m.nextBlock ≤ m'.nextBlock ∧
     m'.blocks b = none ∧
     (∀ b' ≠ b, m'.blocks b' = m.blocks b')))

theorem ZcfreePost.framePreserved {m m' : Mem} {ptr ret : Val}
    (hp : ZcfreePost m ptr ret m') :
    Zlib.Spec.FramePreserved m m' (Zlib.Spec.writes [ptr]) := by
  rcases hp with ⟨rfl, ⟨rfl, _, hblks⟩ | ⟨b, _, rfl, _, _, _, hnone, hne⟩⟩
  · exact ⟨fun b _ _ => hblks b, fun b blk hn hs _ => by rw [hblks b, hn] at hs; cases hs⟩
  · refine ⟨?_, ?_⟩
    · intro b' _ hnot
      have hneb : b' ≠ b := fun heq => hnot ⟨.ptr b 0, by simp, by simp [PtrBlock, heq]⟩
      exact hne b' hneb
    · intro b' blk' hn hs hnot
      have hneb : b' ≠ b := fun heq => hnot ⟨.ptr b 0, by simp, by simp [PtrBlock, heq]⟩
      rw [hne b' hneb, hn] at hs
      cases hs

theorem ZcfreePost.noHeapLeak {m m' : Mem} {ptr ret : Val}
    (hp : ZcfreePost m ptr ret m') (owned : Zlib.Spec.BlockSet) :
    Zlib.Spec.NoHeapLeak m m' owned := by
  rcases hp with ⟨_, ⟨_, _, hblks⟩ | ⟨b, _, rfl, _, _, _, hnone, hne⟩⟩
  · intro b' blk hs _; left; rw [hblks b'] at hs; simp [hs]
  · intro b' blk hs _
    by_cases hbb : b' = b
    · subst hbb; rw [hnone] at hs; cases hs
    · left; rw [hne b' hbb] at hs; simp [hs]

theorem zcfree_params_simple :
    ∀ p ∈ Zlib.Zutil.zutilTU_fn_zcfree.params, IsSimpleParamTy p.ty := by
  intro p hp
  simp only [Zlib.Zutil.zutilTU_fn_zcfree, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]

theorem zcfree_spec_of {prog : Prog} {userExt : ExtHandler}
    (hfns : prog.fns "free" = none)
    (hproto : prog.fnProtos "free" = some (.void, [.ptr .void], false))
    (henum : enumConst? prog.tags "free" = none)
    (hstat : (prog.fnStatics "zcfree").lookup "free" = none)
    (hglob : prog.globalEnv.lookup "free" = none) :
    HeapBodySpec prog zlibPointerConfig (Zlib.Spec.zlibExt userExt) Zlib.Zutil.zutilTU_fn_zcfree
      (fun m args => ∃ op ptr,
        args = [op, ptr] ∧ (op = .null ∨ ∃ b off, op = .ptr b off) ∧ FreePre m ptr)
      (fun m args ret m' => match args with
        | [_, ptr] => ZcfreePost m ptr ret m'
        | _ => False) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  rcases hpre with ⟨op, ptr, rfl, hop, hptr⟩
  have hptr_val : ptr = .null ∨ ∃ pb poff, ptr = .ptr pb poff := by
    rcases hptr with rfl | ⟨b, _, rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨b, 0, rfl⟩
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  dsimp only [Zlib.Zutil.zutilTU_fn_zcfree] at hpush
  rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_nil_right] at hpush
  obtain ⟨hsz0, hal0, hba0, m_op, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_ptr, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  simp only [pushCallParams_zero, Option.some.injEq, Prod.mk.injEq] at hpush2
  rcases hpush2 with ⟨rfl, hcallBlks, hm1_eq⟩
  subst m_ptr
  have hm_op_next : m_op.nextBlock = m.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr0, alloc_snd_nextBlock]
  have hm1_next : m1.nextBlock = m_op.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr1, alloc_snd_nextBlock]
  have hlt01 : m.nextBlock < m_op.nextBlock := hm_op_next ▸ Nat.lt_succ_self _
  have hne01 : m.nextBlock ≠ m_op.nextBlock := Nat.ne_of_lt hlt01
  have hrd_op_0 : Sem.readVal prog.tags m_op m.nextBlock 0 (.typedef "voidpf" (.ptr .void)) = some op :=
    readVal_ptr_of_write_fresh rfl hop hwr0
  have hrd_op : Sem.readVal prog.tags m1 m.nextBlock 0 (.typedef "voidpf" (.ptr .void)) = some op := by
    have heq : m1.blocks m.nextBlock = m_op.blocks m.nextBlock := by
      rw [writeVal_blocks_ne hwr1 hne01, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne01]
    rw [readVal_eq_of_blocks_eq prog.tags heq]; exact hrd_op_0
  have hrd_ptr : Sem.readVal prog.tags m1 m_op.nextBlock 0 (.typedef "voidpf" (.ptr .void)) = some ptr :=
    readVal_ptr_of_write_fresh rfl hptr_val hwr1
  -- Step `(void)opaque;`
  wp_steps
  refine WPTerm.of_exprPure
    (es' := .ret (.rval op (.ptr .void)) [.castF .void]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [List.lookup, ModSet.conflicts, hrd_op, CTy.decay, CTy.unqual]
  have hcast_void : Sem.castVal m1 .void op = some .void := by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid]
  refine WPTerm.of_exprPure
    (es' := .ret (.rval .void .void) []) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure; dsimp only; rw [hcast_void]; rfl
  -- Step `free(ptr);`
  wp_steps
  have hluNone : ((("ptr", m_op.nextBlock, CTy.typedef "voidpf" (CTy.ptr .void)) ::
      ("opaque", m.nextBlock, CTy.typedef "voidpf" (CTy.ptr .void)) ::
      (prog.fnStatics "zcfree" ++ prog.globalEnv)).lookup "free") = none := by
    simp only [List.lookup, show ("free" == "ptr") = false from rfl,
      show ("free" == "opaque") = false from rfl]
    rw [lookup_append_none hstat, hglob]
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.fnPtr "free") (.fnPtr .void [.ptr .void] false))
      [.callFnF [.var "ptr"]]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure
    simp [hluNone, henum, hproto]
  wp_steps
  refine WPTerm.of_exprPure
    (es' := .ret (.rval ptr (.ptr .void))
      [.callArgF "free" (.fnPtr .void [.ptr .void] false) [] []]) (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [List.lookup, ModSet.conflicts, hrd_ptr, CTy.decay, CTy.unqual]
  have hcoerce : Sem.coerceCallArgs m1 [.ptr .void] false [(ptr, .ptr .void)] = some [ptr] := by
    refine coerceCallArgs_cons_nonvariadic ?_ (coerceCallArgs_nil m1)
    rcases hptr_val with rfl | ⟨pb, poff, rfl⟩ <;> simp
  have hfreePre_m1 : FreePre m1 ptr := by
    rcases hptr with rfl | ⟨b, blk, rfl, hb, hk⟩
    · exact Or.inl rfl
    · have hlt : b < m.nextBlock := lt_nextBlock_of_some hb
      exact Or.inr ⟨b, blk, rfl, by rw [hf1.2.1 b hlt, hb], hk⟩
  obtain ⟨ret0, m0', os0', hex0⟩ := extStep_free_has_outcome os hfreePre_m1
  have hnoub : ¬ Zlib.Spec.zlibExt userExt "free" [ptr] m1 os .ub := by
    rw [zlibExt_free]
    exact extStep_free_not_ub os hfreePre_m1
  let env1 : Env :=
    ("ptr", m_op.nextBlock, CTy.typedef "voidpf" (CTy.ptr .void)) ::
    ("opaque", m.nextBlock, CTy.typedef "voidpf" (CTy.ptr .void)) ::
    (prog.fnStatics "zcfree" ++ prog.globalEnv)
  let k1 : Cont := .stmts [] (.blockEnd env1 callBlks
    (.callFrame env blks Zlib.Zutil.zutilTU_fn_zcfree.retTy
      Zlib.Zutil.zutilTU_fn_zcfree.body fs ctx k))
  have hdet_of : ∀ v : Val, v = .null ∨ (∃ pb poff, v = .ptr pb poff) →
      Sem.stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval v (.ptr .void))
            [.callArgF "free" (.fnPtr .void [.ptr .void] false) [] []]) .discard [])
          env1 [] m1 os k1) =
        some (.callFn "free" (.fnPtr .void [.ptr .void] false) [(v, .ptr .void)] [] .discard
          env1 [] m1 os k1) := by
    rintro v (rfl | ⟨pb, poff, rfl⟩) <;> rfl
  have hdet := hdet_of ptr hptr_val
  refine WPTerm.of_call_ext (fnTy := .fnPtr .void [.ptr .void] false)
    hdet hfns rfl hcoerce
    ⟨ret0, m0', os0', by rw [zlibExt_free]; exact hex0⟩ hnoub ?_
  intro ret m2 os2 hext
  rw [zlibExt_free] at hext
  obtain ⟨rfl, hos2, hfreeOut⟩ := extStep_free_ok_inv hext
  subst os2
  wp_steps
  rcases hfreeOut with ⟨rfl, hm2_eq⟩ | ⟨b, blk, rfl, hm1_b, hk, hfree, hm2_next, hm2_none, hm2_ne⟩
  · -- `ptr = .null`
    subst m2
    have hro : ROExt m (m1.freeStack callBlks) := LocalFrameMem.roExt_freeStack hf1
    have hblks : ∀ b', (m1.freeStack callBlks).blocks b' = m.blocks b' := by
      intro b'
      by_cases hlt : b' < m.nextBlock
      · exact hro.2.1 b' hlt
      · have hm_none : m.blocks b' = none := m.fresh b' (Nat.le_of_not_lt hlt)
        rw [hm_none]
        by_cases hm1 : b' < m1.nextBlock
        · have hnat := blockId_lt_add2 hm_op_next hm1_next hm1 hlt
          rcases hnat with h | h
          · have hmem : b' ∈ callBlks := by rw [← hcallBlks, h]; exact .tail _ (.head _)
            obtain ⟨_, blk0, hb0, hk0⟩ := hf1.2.2.2.1 b' hmem
            exact freeStack_blocks_mem_stack m1 callBlks hmem hb0 hk0
          · have hmem : b' ∈ callBlks := by rw [← hcallBlks, h]; exact .head _
            obtain ⟨_, blk0, hb0, hk0⟩ := hf1.2.2.2.1 b' hmem
            exact freeStack_blocks_mem_stack m1 callBlks hmem hb0 hk0
        · exact (m1.freeStack callBlks).fresh b' (Nat.le_of_not_lt hm1)
    exact hcont .void (m1.freeStack callBlks) ⟨rfl, Or.inl ⟨rfl, hro, hblks⟩⟩
  · -- `ptr = .ptr b 0`
    rcases hptr with hcontra | ⟨b', blk', heq', hm_b, hk'⟩
    · cases hcontra
    · cases heq'
      have hfree_eq : ∀ b', (m2.freeStack callBlks).blocks b' =
          if b' = b then none else m.blocks b' := by
        intro b'
        by_cases hbb : b' = b
        · rw [hbb]
          simp only [↓reduceIte]
          by_cases hmem : b ∈ callBlks
          · have hlt := lt_nextBlock_of_some hm_b
            have hge := (hf1.2.2.2.1 b hmem).1
            exact False.elim (Nat.not_lt_of_le hge hlt)
          · rw [freeStack_blocks_not_mem m2 callBlks hmem, hm2_none]
        · simp only [hbb, ↓reduceIte]
          by_cases hmem : b' ∈ callBlks
          · obtain ⟨_, blk0, hb0, hk0⟩ := hf1.2.2.2.1 b' hmem
            have hge := (hf1.2.2.2.1 b' hmem).1
            have hlt_b : b < m.nextBlock := lt_nextBlock_of_some hm_b
            have hneb' : b' ≠ b := by omega
            have hm2_b' : m2.blocks b' = some blk0 := by rw [hm2_ne b' hneb', hb0]
            rw [freeStack_blocks_mem_stack m2 callBlks hmem hm2_b' hk0]
            exact (m.fresh b' hge).symm
          · rw [freeStack_blocks_not_mem m2 callBlks hmem, hm2_ne b' hbb]
            by_cases hlt : b' < m.nextBlock
            · exact hf1.2.1 b' hlt
            · have hm_none' : m.blocks b' = none := m.fresh b' (Nat.le_of_not_lt hlt)
              rw [hm_none']
              by_cases hm1 : b' < m1.nextBlock
              · exfalso
                have hnat := blockId_lt_add2 hm_op_next hm1_next hm1 hlt
                rw [← hcallBlks] at hmem
                rcases hnat with rfl | rfl
                · exact hmem (.tail _ (.head _))
                · exact hmem (.head _)
              · exact m1.fresh b' (Nat.le_of_not_lt hm1)
      have hpost : ZcfreePost m (.ptr b 0) .void (m2.freeStack callBlks) := by
        refine ⟨rfl, Or.inr ⟨b, blk', rfl, hm_b, hk', ?_, ?_, ?_⟩⟩
        · rw [freeStack_nextBlock, hm2_next]; exact hf1.1
        · simp only [hfree_eq b, ↓reduceIte]
        · intro b' hne; simp only [hfree_eq b', hne, ↓reduceIte]
      exact hcont .void (m2.freeStack callBlks) hpost

theorem zcfree_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    HeapBodySpec prog zlibPointerConfig (Zlib.Spec.zlibExt userExt) Zlib.Zutil.zutilTU_fn_zcfree
      (fun m args => ∃ op ptr,
        args = [op, ptr] ∧ (op = .null ∨ ∃ b off, op = .ptr b off) ∧ FreePre m ptr)
      (fun m args ret m' => match args with
        | [_, ptr] => ZcfreePost m ptr ret m'
        | _ => False) :=
  zcfree_spec_of (prog_fns_free hlib) (prog_fnProtos_free hlib)
    (enumConst_progTags_free prog.tags hlib.prog_tags_eq)
    (by rw [prog_fnStatics_zcfree hlib]; rfl)
    (by rw [hlib.globalEnv_eq]; exact hlib.gEnv_lookup_none "free" (by decide))

/-! ## 6. `zError` & `z_errmsg` Table Invariant -/

/-- `z_errmsg[10]` table and its 10 `.ro .global` NUL-terminated string blocks exist in `m`. -/
def ZErrmsgReady (tags : TypeEnv) (gEnv : Env) (m : Mem) : Prop :=
  ∃ b blk,
    gEnv.lookup "z_errmsg" = some (b, .array zErrmsgElemTy (some 10)) ∧
    m.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    blk.size = 80 ∧ blk.align = 8 ∧
    (∀ i < 10, ∃ sb sblk len,
      Sem.readVal tags m b (Int64.ofNat (8 * i)) (.ptr (.const_ (.int .i8))) = some (.ptr sb 0) ∧
      m.blocks sb = some sblk ∧ sblk.perm = .ro ∧ sblk.kind = .global ∧
      m.strlenAt sb 0 = some len)

theorem ZErrmsgReady.roExt {tags : TypeEnv} {gEnv : Env} {m m' : Mem}
    (hro : ROExt m m') (hz : ZErrmsgReady tags gEnv m) :
    ZErrmsgReady tags gEnv m' := by
  rcases hz with ⟨b, blk, hlu, hblk, hperm, hkind, hsz, hal, hentries⟩
  have hm_b : m'.blocks b = some blk := by
    rw [hro.2.1 b (lt_nextBlock_of_some hblk), hblk]
  refine ⟨b, blk, hlu, hm_b, hperm, hkind, hsz, hal, fun i hi => ?_⟩
  obtain ⟨sb, sblk, len, hrv, hsb, hsperm, hskind, hstr⟩ := hentries i hi
  have hm_sb : m'.blocks sb = some sblk := by
    rw [hro.2.1 sb (lt_nextBlock_of_some hsb), hsb]
  refine ⟨sb, sblk, len, ?_, hm_sb, hsperm, hskind, ?_⟩
  · rw [readVal_eq_of_blocks_eq tags (hm_b.trans hblk.symm)]; exact hrv
  · unfold Mem.strlenAt at hstr ⊢; rw [hm_sb, hsb] at *; exact hstr

theorem ZErrmsgReady.clientFrame {tags : TypeEnv} {gEnv : Env} {m0 m m' : Mem}
    {os os' : OSState} {v : Zlib.Spec.ClientView} {owned : Zlib.Spec.BlockSet}
    (hcf : Zlib.Spec.ClientFrame tags m0 v owned m m' os os')
    (hz : ZErrmsgReady tags gEnv m) :
    ZErrmsgReady tags gEnv m' := by
  rcases hcf with ⟨_, _, hprot, _⟩
  rcases hz with ⟨b, blk, hlu, hblk, hperm, hkind, hsz, hal, hentries⟩
  have hprot_b : Zlib.Spec.LibProtected m0 owned os m b :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨blk, hblk, hkind, hperm⟩)))
  have hm_b : m'.blocks b = some blk := by rw [hprot b hprot_b, hblk]
  refine ⟨b, blk, hlu, hm_b, hperm, hkind, hsz, hal, fun i hi => ?_⟩
  obtain ⟨sb, sblk, len, hrv, hsb, hsperm, hskind, hstr⟩ := hentries i hi
  have hprot_sb : Zlib.Spec.LibProtected m0 owned os m sb :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨sblk, hsb, hskind, hsperm⟩)))
  have hm_sb : m'.blocks sb = some sblk := by rw [hprot sb hprot_sb, hsb]
  refine ⟨sb, sblk, len, ?_, hm_sb, hsperm, hskind, ?_⟩
  · rw [readVal_eq_of_blocks_eq tags (hm_b.trans hblk.symm)]; exact hrv
  · unfold Mem.strlenAt at hstr ⊢; rw [hm_sb, hsb] at *; exact hstr

def zErrorIdx (err : BitVec 32) : Nat :=
  if err.toInt < -6 ∨ err.toInt > 2 then 9 else (2 - err.toInt).toNat

theorem zErrorIdx_lt (err : BitVec 32) : zErrorIdx err < 10 := by
  unfold zErrorIdx
  split <;> omega

theorem zError_params_simple :
    ∀ p ∈ Zlib.Zutil.zutilTU_fn_zError.params, IsSimpleParamTy p.ty := by
  intro p hp
  simp only [Zlib.Zutil.zutilTU_fn_zError, List.mem_singleton] at hp
  subst hp
  simp [IsSimpleParamTy, CTy.unqual]

theorem zError_spec_of {prog : Prog} {ext : ExtHandler}
    (hstat : (prog.fnStatics "zError").lookup "z_errmsg" = none) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Zutil.zutilTU_fn_zError
      (fun m args => ZErrmsgReady prog.tags prog.globalEnv m ∧
        ∃ err : BitVec 32, args = [.int .i32 err])
      (fun _ _ ret m' => Zlib.Spec.CString m' ret ∧
        ∃ sb sblk, ret = .ptr sb 0 ∧ m'.blocks sb = some sblk ∧
          sblk.perm = .ro ∧ sblk.kind = .global) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  change ZErrmsgReady prog.tags prog.globalEnv m ∧ ∃ err : BitVec IntKind.i32.bits, args = [.int .i32 err] at hpre
  rcases hpre with ⟨hz, err, rfl⟩
  rcases hz with ⟨b_tab, blk_tab, hlu_tab, hblk_tab, hperm_tab, hkind_tab, hsz_tab, hal_tab, hentries⟩
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  dsimp only [Zlib.Zutil.zutilTU_fn_zError] at hpush
  rw [List.zip_cons_cons, List.zip_nil_right] at hpush
  obtain ⟨hsz_p, hal_p, hba_p, m_err, hwr_p, hpush1⟩ := pushCallParams_cons_inv hpush
  simp only [pushCallParams_zero, Option.some.injEq, Prod.mk.injEq] at hpush1
  rcases hpush1 with ⟨rfl, rfl, hm1_eq⟩
  subst m_err
  have hrd_err : Sem.readVal prog.tags m1 m.nextBlock 0 (.int .i32) = some (.int .i32 err) :=
    readVal_i32_of_write_fresh rfl hwr_p
  have hlt_tab : b_tab < m.nextBlock := lt_nextBlock_of_some hblk_tab
  have hm1_tab : m1.blocks b_tab = some blk_tab := by rw [hf1.2.1 b_tab hlt_tab, hblk_tab]
  have hlu_zerr : (("err", m.nextBlock, CTy.int .i32) ::
      (prog.fnStatics "zError" ++ prog.globalEnv)).lookup "z_errmsg" =
      some (b_tab, .array zErrmsgElemTy (some 10)) := by
    rw [lookup_cons_ne _ (by decide), lookup_append_none hstat]
    exact hlu_tab
  -- Shared indexing + return continuation for `idx = zErrorIdx err < 10`
  obtain ⟨idx, hidx_eq⟩ : ∃ idx, idx = zErrorIdx err := ⟨zErrorIdx err, rfl⟩
  have hidx_lt : idx < 10 := by rw [hidx_eq]; exact zErrorIdx_lt err
  have hidx_cont : ∀ _ : idx = zErrorIdx err, WPTerm prog zlibPointerConfig ext Q
      (.running
        (.expr (.ret (.rval (.int .i32 (BitVec.ofInt IntKind.i32.bits idx)) (.int .i32))
          [.indexIdxF .rval (.ptr b_tab 0) (.ptr zErrmsgElemTy)]) .returnVal [])
        (("err", m.nextBlock, CTy.int .i32) :: (prog.fnStatics "zError" ++ prog.globalEnv))
        [] m1 os (.blockEnd (("err", m.nextBlock, CTy.int .i32) :: (prog.fnStatics "zError" ++ prog.globalEnv))
          [m.nextBlock] (.callFrame env blks Zlib.Zutil.zutilTU_fn_zError.retTy
            Zlib.Zutil.zutilTU_fn_zError.body fs ctx k))) := by
    intro _
    obtain ⟨sb, sblk, len, hrv_m, hsb_m, hsperm, hskind, hstr_m⟩ := hentries idx hidx_lt
    have hlt_sb : sb < m.nextBlock := lt_nextBlock_of_some hsb_m
    have hidx_i64 : (BitVec.ofInt IntKind.i32.bits idx).toInt = (idx : Int) := by
      rw [BitVec.toInt_ofInt]
      change ((idx : Int)).bmod (2 ^ 32) = (idx : Int)
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have hzElemSz : sizeofTy prog.tags zErrmsgElemTy = 8 := by simp [zErrmsgElemTy]
    have hevalAdd : Sem.evalPtrAdd zlibPointerConfig prog.tags m1
        (.ptr b_tab 0) zErrmsgElemTy (BitVec.ofInt IntKind.i32.bits idx).toInt =
        some (.ptr b_tab (Int64.ofNat (8 * idx))) := by
      rw [hidx_i64]
      unfold Sem.evalPtrAdd
      by_cases hz : idx = 0
      · rw [hz]
        simp [zlibPointerConfig]
      · have hne0 : ((idx : Int) == 0) = false := beq_false_of_ne (by omega)
        have hmax8 : max 1 ((8 : Nat) : Int) = 8 := by decide
        simp only [hne0, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hm1_tab, hzElemSz,
          hmax8, bind, Option.bind, pure, Pure.pure]
        have hbounds : 0 ≤ (0 : Int64).toInt + (idx : Int) * 8 ∧
            (0 : Int64).toInt + (idx : Int) * 8 ≤ (blk_tab.size : Int) := by
          simp [Int64.toInt_zero, hsz_tab]; omega
        rw [decide_eq_true hbounds.1, decide_eq_true hbounds.2]
        simp only [Bool.and_self, guard_true, Option.some.injEq]
        congr 1
        apply Int64.toInt_inj.mp
        have hlt63_1 : (0 : Int64).toInt + (idx : Int) * 8 < 2 ^ 63 := by
          simp [Int64.toInt_zero]; omega
        have hlt63_2 : ((8 * idx : Nat) : Int) < 2 ^ 63 := by omega
        rw [int64_ofInt_toInt (by simp [Int64.toInt_zero]; omega) hlt63_1]
        change _ = (Int64.ofInt ((8 * idx : Nat) : Int)).toInt
        rw [int64_ofInt_toInt (by omega) hlt63_2]
        simp [Int64.toInt_zero]; omega
    have hrv_m1 : Sem.readVal prog.tags m1 b_tab (Int64.ofNat (8 * idx)) zErrmsgElemTy =
        some (.ptr sb 0) := by
      rw [readVal_eq_of_blocks_eq prog.tags (hm1_tab.trans hblk_tab.symm)]
      unfold Sem.readVal at hrv_m ⊢
      simpa [zErrmsgElemTy, CTy.unqual] using hrv_m
    have hstep_idx : Sem.stepExprPure prog zlibPointerConfig
        (("err", m.nextBlock, CTy.int .i32) :: (prog.fnStatics "zError" ++ prog.globalEnv)) m1 []
        (.ret (.rval (.int .i32 (BitVec.ofInt IntKind.i32.bits idx)) (.int .i32))
          [.indexIdxF .rval (.ptr b_tab 0) (.ptr zErrmsgElemTy)]) =
        some (.ret (.rval (.ptr sb 0) zErrmsgElemTy.decay) [], m1, []) := by
      unfold Sem.stepExprPure Sem.readPlace
      simp only [CTy.unqual, Sem.valAsInt?, IntKind.signed, ↓reduceIte, ModSet.conflicts,
        List.any_nil, Bool.not_false, guard_true, bind, Option.bind, pure, Pure.pure]
      rw [hevalAdd]
      dsimp only
      rw [show zErrmsgElemTy.unqual = .ptr (.const_ (.int .i8)) from rfl]
      dsimp only
      rw [hrv_m1]
      rfl
    refine WPTerm.of_exprPure hstep_idx ?_
    have hro : ROExt m (m1.freeStack [m.nextBlock]) := LocalFrameMem.roExt_freeStack hf1
    have hsb_m' : (m1.freeStack [m.nextBlock]).blocks sb = some sblk := by
      rw [hro.2.1 sb hlt_sb, hsb_m]
    have hstr_m' : (m1.freeStack [m.nextBlock]).strlenAt sb 0 = some len := by
      unfold Mem.strlenAt at hstr_m ⊢
      rw [hsb_m', hsb_m] at *
      exact hstr_m
    have hpost : Zlib.Spec.CString (m1.freeStack [m.nextBlock]) (.ptr sb 0) ∧
        ∃ sb' sblk', Val.ptr sb 0 = Val.ptr sb' 0 ∧
          (m1.freeStack [m.nextBlock]).blocks sb' = some sblk' ∧
          sblk'.perm = .ro ∧ sblk'.kind = .global :=
      ⟨⟨sb, 0, len, rfl, hstr_m'⟩, sb, sblk, rfl, hsb_m', hsperm, hskind⟩
    refine WPTerm.of_det
      (s' := .running (.expr (.ret (.rval (.ptr sb 0) Zlib.Zutil.zutilTU_fn_zError.retTy) fs) ctx [])
        env blks (m1.freeStack [m.nextBlock]) os k) ?_
      (hcont (.ptr sb 0) (m1.freeStack [m.nextBlock]) hro hpost)
    unfold Sem.stepDet
    simp [Zlib.Zutil.zutilTU_fn_zError, Sem.Cont.topRetTy, CTy.isVoid, CTy.unqual,
      Sem.unwindReturn, castVal_ptr_ptr, freeStack_nil]
  -- Enter `return ERR_MSG(err);` and evaluate `z_errmsg`
  wp_steps
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.ptr b_tab 0) (.ptr zErrmsgElemTy))
      [.indexBaseF .rval
        (.cond
          (.logOr
            (.binary .lt (.paren (.var "err")) (.unary .neg (.lit 6 .i32 .none .dec none)))
            (.binary .gt (.paren (.var "err")) (.lit 2 .i32 .none .dec none)))
          (.lit 9 .i32 .none .dec none)
          (.binary .sub (.lit 2 .i32 .none .dec none) (.paren (.var "err"))))])
    (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [hlu_zerr, CTy.decay, CTy.unqual]
  wp_steps
  -- Evaluate `err < -6`
  refine WPTerm.of_exprPure
    (es' := .ret (.rval (.int .i32 err) (.int .i32))
      [.binLhsF .lt (.unary .neg (.lit 6 .i32 .none .dec none)),
       .logOrF (.binary .gt (.paren (.var "err")) (.lit 2 .i32 .none .dec none)),
       .condF (.lit 9 .i32 .none .dec none)
         (.binary .sub (.lit 2 .i32 .none .dec none) (.paren (.var "err"))),
       .indexIdxF .rval (.ptr b_tab 0) (.ptr zErrmsgElemTy)])
    (m' := m1) (mods' := []) ?_ ?_
  · unfold Sem.stepExprPure Sem.readPlace
    simp [List.lookup, ModSet.conflicts, hrd_err, CTy.decay, CTy.unqual]
  wp_steps
  have hltCmp :
      Sem.cmpOrd .lt
        (if (IntKind.i32.usualArith IntKind.i32.promote).signed = true then
          (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toInt
        else
          ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toNat)
        (if (IntKind.i32.usualArith IntKind.i32.promote).signed = true then
          (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.promote.signed = true then
              (BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toInt
            else
              ↑(BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toNat)).toInt
        else
          ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.promote.signed = true then
              (BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toInt
            else
              ↑(BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toNat)).toNat) =
      decide (err.toInt < -6) := by
    have hL :
        (if (IntKind.i32.usualArith IntKind.i32.promote).signed = true then
          (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toInt
        else
          ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toNat) = err.toInt := by
      rw [show IntKind.i32.promote = .i32 from rfl,
          show IntKind.i32.usualArith .i32 = .i32 from rfl,
          show IntKind.i32.signed = true from rfl]
      simp only [↓reduceIte, BitVec.ofInt_toInt]
    have hR :
        (if (IntKind.i32.usualArith IntKind.i32.promote).signed = true then
          (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.promote.signed = true then
              (BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toInt
            else
              ↑(BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toNat)).toInt
        else
          ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32.promote).bits
            (if IntKind.i32.promote.signed = true then
              (BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toInt
            else
              ↑(BitVec.ofInt IntKind.i32.promote.bits
                (-if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 6).toInt
                  else ↑(BitVec.ofInt IntKind.i32.bits 6).toNat)).toNat)).toNat) = -6 := by
      decide
    rw [hL, hR]
    rfl
  rw [hltCmp]
  by_cases hlt6 : err.toInt < -6
  · have hlt6_32 : @BitVec.toInt 32 err < -6 := hlt6
    have hidx9 : idx = 9 := by simp [hidx_eq, zErrorIdx, hlt6_32]
    rw [decide_eq_true hlt6]
    wp_steps
    simp only [List.isEmpty_nil, ↓reduceIte]
    have hfin := hidx_cont hidx_eq
    rw [hidx9] at hfin
    simpa [show Sem.ofIntCast .i32 9 = .int .i32 (BitVec.ofInt IntKind.i32.bits ↑(9 : Nat)) from rfl] using hfin
  · rw [decide_eq_false hlt6]
    wp_steps
    -- Evaluate `err > 2`
    refine WPTerm.of_exprPure (m' := m1) (mods' := [])
      (es' := .ret (.rval (.int .i32 err) (.int .i32))
        [.binLhsF .gt (.lit 2 .i32 .none .dec none),
         .logOrEndF,
         .condF (.lit 9 .i32 .none .dec none)
           (.binary .sub (.lit 2 .i32 .none .dec none) (.paren (.var "err"))),
         .indexIdxF .rval (.ptr b_tab 0) (.ptr zErrmsgElemTy)]) ?_ ?_
    · unfold Sem.stepExprPure Sem.readPlace
      simp [List.lookup, ModSet.conflicts, hrd_err, CTy.decay, CTy.unqual]
    wp_steps
    have hgtCmp :
        Sem.cmpOrd .gt
          (if (IntKind.i32.usualArith IntKind.i32).signed = true then
            (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toInt
          else
            ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toNat)
          (if (IntKind.i32.usualArith IntKind.i32).signed = true then
            (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 2).toInt
                else ↑(BitVec.ofInt IntKind.i32.bits 2).toNat)).toInt
          else
            ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 2).toInt
                else ↑(BitVec.ofInt IntKind.i32.bits 2).toNat)).toNat) =
        decide (err.toInt > 2) := by
      have hL :
          (if (IntKind.i32.usualArith IntKind.i32).signed = true then
            (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toInt
          else
            ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then err.toInt else ↑err.toNat)).toNat) = err.toInt := by
        rw [show IntKind.i32.usualArith .i32 = .i32 from rfl,
            show IntKind.i32.signed = true from rfl]
        simp only [↓reduceIte, BitVec.ofInt_toInt]
      have hR :
          (if (IntKind.i32.usualArith IntKind.i32).signed = true then
            (BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 2).toInt
                else ↑(BitVec.ofInt IntKind.i32.bits 2).toNat)).toInt
          else
            ↑(BitVec.ofInt (IntKind.i32.usualArith IntKind.i32).bits
              (if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 2).toInt
                else ↑(BitVec.ofInt IntKind.i32.bits 2).toNat)).toNat) = 2 := by
        decide
      rw [hL, hR]
      rfl
    rw [hgtCmp]
    have hlt6_32 : ¬ @BitVec.toInt 32 err < -6 := hlt6
    by_cases hgt2 : err.toInt > 2
    · have hgt2_32 : @BitVec.toInt 32 err > 2 := hgt2
      have hidx9 : idx = 9 := by simp [hidx_eq, zErrorIdx, hlt6_32, hgt2_32]
      rw [decide_eq_true hgt2]
      wp_steps
      simp only [List.isEmpty_nil, ↓reduceIte]
      have hfin := hidx_cont hidx_eq
      rw [hidx9] at hfin
      simpa [show Sem.ofIntCast .i32 9 = .int .i32 (BitVec.ofInt IntKind.i32.bits ↑(9 : Nat)) from rfl] using hfin
    · have hgt2_32 : ¬ @BitVec.toInt 32 err > 2 := hgt2
      have hidx_sub : (idx : Int) = 2 - err.toInt := by
        have h : idx = (2 - @BitVec.toInt 32 err).toNat := by simp [hidx_eq, zErrorIdx, hlt6_32, hgt2_32]
        rw [h]
        have hge : 0 ≤ 2 - @BitVec.toInt 32 err := by omega
        exact Int.toNat_of_nonneg hge
      rw [decide_eq_false hgt2]
      wp_steps
      refine WPTerm.of_exprPure (m' := m1) (mods' := [])
        (es' := .ret (.rval (.int .i32 err) (.int .i32))
          [.binRhsF .sub (Sem.ofIntCast .i32 2) (.int .i32),
           .indexIdxF .rval (.ptr b_tab 0) (.ptr zErrmsgElemTy)]) ?_ ?_
      · unfold Sem.stepExprPure Sem.readPlace
        simp [List.lookup, ModSet.conflicts, hrd_err, CTy.decay, CTy.unqual]
      have hsubEval : Sem.applyBinary zlibPointerConfig prog.tags m1 .sub
          (Sem.ofIntCast .i32 2) (.int .i32) (.int .i32 err) (.int .i32) =
          some (.int .i32 (BitVec.ofInt IntKind.i32.bits idx), .int .i32) := by
        unfold Sem.applyBinary Sem.evalIntBinary
        rw [show Sem.ofIntCast .i32 2 = .int .i32 (BitVec.ofInt IntKind.i32.bits 2) from rfl]
        have hrange : IntKind.i32.inRange (2 - err.toInt) = true := by
          change (-2147483648 ≤ 2 - err.toInt && 2 - err.toInt ≤ 2147483647) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        simp only [CTy.isPtr, CTy.unqual, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
          Sem.valAsInt?, bind, Option.bind]
        rw [show IntKind.i32.usualArith .i32 = .i32 from rfl,
            show IntKind.i32.signed = true from rfl,
            show (BitVec.ofInt IntKind.i32.bits 2).toInt = 2 from by decide]
        simp only [↓reduceIte, BitVec.ofInt_toInt,
          show (BitVec.ofInt IntKind.i32.bits 2).toInt = 2 from by decide,
          Sem.ofIntExact, hrange, pure, Pure.pure]
        simp [hidx_sub]
      simp only [List.isEmpty_nil, ↓reduceIte]
      refine WPTerm.of_exprPure (m' := m1) (mods' := [])
        (es' := .ret (.rval (.int .i32 (BitVec.ofInt IntKind.i32.bits idx)) (.int .i32))
          [.indexIdxF .rval (.ptr b_tab 0) (.ptr zErrmsgElemTy)]) ?_ (hidx_cont hidx_eq)
      unfold Sem.stepExprPure
      dsimp only
      rw [hsubEval]
      rfl

theorem zError_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Zutil.zutilTU_fn_zError
      (fun m args => ZErrmsgReady prog.tags prog.globalEnv m ∧
        ∃ err : BitVec 32, args = [.int .i32 err])
      (fun _ _ ret m' => Zlib.Spec.CString m' ret ∧
        ∃ sb sblk, ret = .ptr sb 0 ∧ m'.blocks sb = some sblk ∧
          sblk.perm = .ro ∧ sblk.kind = .global) :=
  zError_spec_of (by rw [prog_fnStatics_zError hlib]; rfl)

end Zlib.Proof
