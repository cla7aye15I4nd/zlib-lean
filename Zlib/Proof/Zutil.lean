import C99.Proof
import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgSpec
import Zlib.Zutil

/-!
# Safety Proofs for `zutil.c` (`zlibVersion`, `zlibCompileFlags`)
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec

/-! ## `zlibVersion` -/

theorem zlibVersion_spec
    {prog : Prog} {ext : ExtHandler} :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Zutil.zutilTU_fn_zlibVersion
      (fun _ args => args = [])
      (fun _ _ ret m' => Zlib.Spec.CString m' ret) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  subst hpre
  simp only [Zlib.Zutil.zutilTU_fn_zlibVersion, List.zip_nil_right, pushCallParams_zero,
    Option.some.injEq, Prod.mk.injEq] at hpush
  rcases hpush with ⟨rfl, rfl, rfl⟩
  wp_steps
  have hsz : "1.4.0.1-motley".utf8ByteSize + 1 < ptrDiffLimit := by decide
  refine WPTerm.of_strLit (hd := rfl) hsz ?_
  intro base' bid m2 halloc
  have hro : ROExt m m2 := ROExt.of_strLit hsz halloc
  have hnonnul : ∀ i < "1.4.0.1-motley".utf8ByteSize,
      ("1.4.0.1-motley".toUTF8[i]?).getD 0 ≠ 0 := by decide
  have hend : ("1.4.0.1-motley".toUTF8["1.4.0.1-motley".utf8ByteSize]?).getD 0 = 0 := by decide
  have hstr : m2.strlenAt bid 0 = some "1.4.0.1-motley".utf8ByteSize :=
    strlenAt_alloc_strLit hsz halloc hnonnul hend
  have hcstr : Zlib.Spec.CString m2 (.ptr bid 0) :=
    ⟨bid, 0, "1.4.0.1-motley".utf8ByteSize, rfl, hstr⟩
  refine WPTerm.of_det
    (s' := .running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx [])
      env blks m2 os k) ?_ (hcont (.ptr bid 0) m2 hro hcstr)
  unfold Sem.stepDet
  simp [Zlib.Zutil.zutilTU_fn_zlibVersion, Sem.Cont.topRetTy, CTy.isVoid, CTy.unqual,
    Sem.unwindReturn, castVal_ptr_ptr, freeStack_nil]

theorem zlibVersion_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Zutil.zlibVersion_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO
    (prog_fns_zlibVersion hlib) rfl ⟨rfl, rfl⟩ (prog_fnProtos_zlibVersion hlib)
    rfl (fun p hp => by cases hp) zlibVersion_spec ?_ ?_
  · intro v owned m os args _ _ hawt
    rcases hawt with ⟨hlen, _⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Zutil.zlibVersion_contract,
      Zlib.Zutil.zutilTU_fn_zlibVersion, List.map_nil, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  · intro v owned m args ret m' _ hawt _ hcstr
    rcases hawt with ⟨hlen, _⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Zutil.zlibVersion_contract,
      Zlib.Zutil.zutilTU_fn_zlibVersion, List.map_nil, List.length_nil] at hlen
    obtain rfl : args = [] := List.eq_nil_of_length_eq_zero hlen
    simp only [Zlib.Zutil.zutilTU_fn_zlibVersion, CTy.isVoid, CTy.unqual,
      Bool.false_eq_true, ↓reduceIte]
    rcases hcstr with ⟨b, off, len, rfl, hstr⟩
    refine ⟨.ptr b off, castVal_ptr_ptr m' _ b off, ?_⟩
    exact ⟨⟨b, off, len, rfl, hstr⟩, rfl⟩

/-! ## `zlibCompileFlags` -/

private abbrev uLongCTy : CTy := .typedef "uLong" (.int .u64)

private theorem uLongCTy_sizeof (tags : TypeEnv) : sizeofTy tags uLongCTy = 8 := by
  rw [← sizeofTy_unqual]; simp [CTy.unqual]; rfl

private theorem uLongCTy_alignof (tags : TypeEnv) : alignofTy tags uLongCTy = 8 := by
  rw [← alignofTy_unqual]; simp [CTy.unqual]; rfl

private theorem uIntCTy_sizeof (tags : TypeEnv) :
    sizeofTy tags (.typedef "uInt" (.int .u32)) = 4 := by
  rw [← sizeofTy_unqual]; simp [CTy.unqual]; rfl

private theorem voidpfCTy_sizeof (tags : TypeEnv) :
    sizeofTy tags (.typedef "voidpf" (.ptr .void)) = 8 := by
  rw [← sizeofTy_unqual]; simp [CTy.unqual]

private theorem zOffTCTy_sizeof (tags : TypeEnv) :
    sizeofTy tags (.typedef "z_off_t" (.int .i64)) = 8 := by
  rw [← sizeofTy_unqual]; simp [CTy.unqual]; rfl

private theorem writeVal_uLong_exists {m : Mem} {bid : BlockId} {blk : Block}
    (hb : m.blocks bid = some blk) (hperm : blk.perm = .rw)
    (hsz : blk.size = 8) (hal : blk.align = 8) (v : BitVec IntKind.u64.bits) :
    ∃ m', Sem.writeVal m bid 0 uLongCTy (.int .u64 v) = some m' ∧
      (∃ blk', m'.blocks bid = some blk' ∧ blk'.perm = .rw ∧
        blk'.size = 8 ∧ blk'.align = 8) ∧
      (∀ tags, Sem.readVal tags m' bid 0 uLongCTy = some (.int .u64 v)) ∧
      (∀ m0 blks, LocalFrameMem m0 m blks → bid ∈ blks → LocalFrameMem m0 m' blks) := by
  have halign : Mem.isAligned blk 0 8 = true := by
    rw [isAligned_iff]
    refine ⟨Int.le_refl _, by decide, ?_⟩
    have hba := blk.baseAligned
    rw [hal] at hba
    simpa [Int64.toInt_zero] using hba
  have hin : Mem.inBounds blk 0 8 = true := by
    rw [inBounds_iff]
    refine ⟨Int.le_refl _, ?_⟩
    simp [Int64.toInt_zero, hsz]
  obtain ⟨m', hm'⟩ := writeVal_int_some (m := m) (b := bid) (off := 0) (blk := blk)
    (ty := uLongCTy) (k := .u64) (v := .int .u64 v) (iv := v.toNat)
    rfl rfl hb hperm halign hin rfl
  have hm'_eq : Sem.writeVal m bid 0 (.int .u64) (.int .u64 v) = some m' := hm'
  obtain ⟨bs, hbs⟩ := writeVal_writeBytes hm'
  obtain ⟨_, _, hblkeq⟩ := writeVal_blocks_eq hb hm'
  refine ⟨m', hm', ⟨_, hblkeq, hperm, hsz, hal⟩, ?_, ?_⟩
  · intro tags
    exact readVal_writeVal_same_int tags hb hm'_eq
  · intro m0 blks hf hmem
    exact hf.write_stack hmem hb hbs

private theorem wp_assignEq_zero_uLong {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m m' : Mem} {os : OSState} {k : Cont} {bid : BlockId} {fs : List ExprFrame}
    (hwr : Sem.writeVal m bid 0 uLongCTy (.int .u64 0) = some m')
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 0) uLongCTy) fs) ctx [⟨bid, 0, 8⟩]) env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (ofIntCast .i32 0) (.int .i32))
        (.assignRhsF .eq bid 0 uLongCTy :: fs)) ctx []) env blks m os k) := by
  refine WPTerm.of_exprPure ?_ hw
  unfold Sem.stepExprPure Sem.writePlace
  simp only [uLongCTy_sizeof, ModSet.conflicts, List.any_nil, Bool.not_false, guard_true,
    assignOpToBin?, CTy.unqual, bind, Option.bind, pure, Pure.pure]
  have hcast : Sem.castVal m uLongCTy (ofIntCast .i32 0) = some (.int .u64 0) := by
    rw [castVal_unqual]; simp [CTy.unqual, ofIntCast]
  rw [hcast]
  simp only [hwr]

private theorem wp_assignAdd_i32_uLong {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {ctx : ExprCtx} {env : Env} {blks : List BlockId}
    {m m' : Mem} {os : OSState} {k : Cont} {bid : BlockId} {fs : List ExprFrame}
    {cur : BitVec 64} {rhs : BitVec 32} {newBv : BitVec 64}
    (hrd : Sem.readVal prog.tags m bid 0 uLongCTy = some (.int .u64 cur))
    (hnew : BitVec.ofInt 64 ((cur.toNat : Int) + ((BitVec.ofInt 64 rhs.toInt).toNat : Int)) = newBv)
    (hwr : Sem.writeVal m bid 0 uLongCTy (.int .u64 newBv) = some m')
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 newBv) uLongCTy) fs) ctx [⟨bid, 0, 8⟩]) env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 rhs) (.int .i32))
        (.assignRhsF .addEq bid 0 uLongCTy :: fs)) ctx []) env blks m os k) := by
  refine WPTerm.of_exprPure ?_ hw
  unfold Sem.stepExprPure Sem.writePlace
  have hbin : Sem.applyBinary cfg prog.tags m .add (.int .u64 cur) uLongCTy (.int .i32 rhs) (.int .i32) =
      some (.int .u64 newBv, .int .u64) := by
    unfold Sem.applyBinary Sem.evalIntBinary
    simp only [CTy.isPtr, CTy.unqual, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      Sem.valAsInt?, bind, Option.bind]
    have hua : IntKind.usualArith .u64 .i32 = .u64 := rfl
    rw [hua]
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, Sem.ofIntExact,
      pure, Pure.pure]
    have hcur : (BitVec.ofInt 64 (cur.toNat : Int)).toNat = cur.toNat := by simp
    rw [hcur, hnew]
  have hcast : Sem.castVal m uLongCTy (.int .u64 newBv) = some (.int .u64 newBv) := by
    rw [castVal_unqual]; exact castVal_int_self _ _ _
  simp only [uLongCTy_sizeof, ModSet.conflicts, List.any_nil, Bool.not_false, guard_true,
    assignOpToBin?, hrd, hbin, CTy.unqual, bind, Option.bind, pure, Pure.pure]
  rw [hcast]
  simp only [hwr]

private theorem wp_readVar_uLong {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    {x : String} {bid : BlockId} {v : BitVec IntKind.u64.bits} {fs : List ExprFrame}
    (hlu : env.lookup x = some (bid, uLongCTy))
    (hmods : mods = [])
    (hrd : Sem.readVal prog.tags m bid 0 uLongCTy = some (.int .u64 v))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 v) (.int .u64)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) := by
  subst hmods
  refine WPTerm.of_exprPure ?_ hw
  unfold Sem.stepExprPure Sem.readPlace
  simp [hlu, ModSet.conflicts, hrd, CTy.decay, CTy.unqual]

theorem zlibCompileFlags_spec
    {prog : Prog} {ext : ExtHandler} :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Zutil.zutilTU_fn_zlibCompileFlags
      (fun _ args => args = [])
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  subst hpre
  simp only [Zlib.Zutil.zutilTU_fn_zlibCompileFlags, List.zip_nil_right, pushCallParams_zero,
    Option.some.injEq, Prod.mk.injEq] at hpush
  rcases hpush with ⟨rfl, rfl, rfl⟩
  have hf0 : LocalFrameMem m m [] := LocalFrameMem.init m
  -- Enter function body block and declare `uLong flags;`
  wp_steps
  have hszF : max 1 (sizeofTy prog.tags uLongCTy) < ptrDiffLimit := by
    rw [uLongCTy_sizeof]; decide
  have halF : 0 < max 1 (alignofTy prog.tags uLongCTy) := by
    rw [uLongCTy_alignof]; decide
  refine WPTerm.of_localDecl_none (hd := rfl) hszF halF ?_
  intro baseF bid m1 hbaF hallocF
  have hf1 : LocalFrameMem m m1 [bid] := hf0.alloc_stack hallocF
  have hbm1 : m1.blocks bid =
      some ⟨max 1 (sizeofTy prog.tags uLongCTy), max 1 (alignofTy prog.tags uLongCTy),
        .rw, .stack, baseF, (fun _ => .undef), hszF, halF, hbaF⟩ := by
    have hbid : bid = m.nextBlock := (congrArg Prod.fst hallocF).symm
    have hm1_eq : m1 = (m.alloc (max 1 (sizeofTy prog.tags uLongCTy))
        (max 1 (alignofTy prog.tags uLongCTy)) .rw .stack baseF (fun _ => .undef)
        hszF halF hbaF).2 := (congrArg Prod.snd hallocF).symm
    rw [hbid, hm1_eq]
    exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz1 : max 1 (sizeofTy prog.tags uLongCTy) = 8 := by rw [uLongCTy_sizeof]; rfl
  have hal1 : max 1 (alignofTy prog.tags uLongCTy) = 8 := by rw [uLongCTy_alignof]; rfl
  wp_steps
  -- `flags = 0;`
  obtain ⟨m2, hwr2, ⟨blk2, hbm2, hperm2, hsz2, hal2⟩, hrd2, hfm2⟩ :=
    writeVal_uLong_exists hbm1 rfl hsz1 hal1 0
  have hf2 : LocalFrameMem m m2 [bid] := hfm2 m [bid] hf1 (.head _)
  refine wp_assignEq_zero_uLong hwr2 ?_
  wp_steps
  -- Switch 1: `switch ((int)(sizeof(uInt)))` -> case 4: `flags += 1;`
  rw [uIntCTy_sizeof]
  wp_steps
  obtain ⟨m3, hwr3, ⟨blk3, hbm3, hperm3, hsz3, hal3⟩, hrd3, hfm3⟩ :=
    writeVal_uLong_exists hbm2 hperm2 hsz2 hal2 1
  have hf3 : LocalFrameMem m m3 [bid] := hfm3 m [bid] hf2 (.head _)
  refine wp_assignAdd_i32_uLong (hrd2 prog.tags) rfl hwr3 ?_
  wp_steps
  -- Switch 2: `switch ((int)(sizeof(uLong)))` -> case 8: `flags += 2 << 2;`
  rw [uLongCTy_sizeof]
  wp_steps
  obtain ⟨m4, hwr4, ⟨blk4, hbm4, hperm4, hsz4, hal4⟩, hrd4, hfm4⟩ :=
    writeVal_uLong_exists hbm3 hperm3 hsz3 hal3 9
  have hf4 : LocalFrameMem m m4 [bid] := hfm4 m [bid] hf3 (.head _)
  refine wp_assignAdd_i32_uLong (hrd3 prog.tags) rfl hwr4 ?_
  wp_steps
  -- Switch 3: `switch ((int)(sizeof(voidpf)))` -> case 8: `flags += 2 << 4;`
  rw [voidpfCTy_sizeof]
  wp_steps
  obtain ⟨m5, hwr5, ⟨blk5, hbm5, hperm5, hsz5, hal5⟩, hrd5, hfm5⟩ :=
    writeVal_uLong_exists hbm4 hperm4 hsz4 hal4 41
  have hf5 : LocalFrameMem m m5 [bid] := hfm5 m [bid] hf4 (.head _)
  refine wp_assignAdd_i32_uLong (hrd4 prog.tags) rfl hwr5 ?_
  wp_steps
  -- Switch 4: `switch ((int)(sizeof(z_off_t)))` -> case 8: `flags += 2 << 6;`
  rw [zOffTCTy_sizeof]
  wp_steps
  obtain ⟨m6, hwr6, _, hrd6, hfm6⟩ :=
    writeVal_uLong_exists hbm5 hperm5 hsz5 hal5 169
  have hf6 : LocalFrameMem m m6 [bid] := hfm6 m [bid] hf5 (.head _)
  refine wp_assignAdd_i32_uLong (hrd5 prog.tags) rfl hwr6 ?_
  wp_steps
  -- `return flags;`
  refine wp_readVar_uLong rfl rfl (hrd6 prog.tags) ?_
  have hro : ROExt m (m6.freeStack [bid]) := LocalFrameMem.roExt_freeStack hf6
  refine WPTerm.of_det
    (s' := .running (.expr (.ret (.rval (.int .u64 169) uLongCTy) fs) ctx []) env blks
      (m6.freeStack [bid]) os k) ?_
    (hcont (.int .u64 169) (m6.freeStack [bid]) hro ⟨169, rfl⟩)
  unfold Sem.stepDet
  simp only [Zlib.Zutil.zutilTU_fn_zlibCompileFlags, Sem.Cont.topRetTy, CTy.isVoid, CTy.unqual,
    Sem.unwindReturn, freeStack_nil, ↓reduceIte, Bool.false_eq_true, Option.bind]
  have hcast : Sem.castVal m6 (CTy.typedef "uLong" (CTy.int IntKind.u64))
      (.int .u64 (169 : BitVec IntKind.u64.bits)) =
      some (.int .u64 (169 : BitVec IntKind.u64.bits)) := by
    rw [castVal_unqual]; exact castVal_int_self _ _ _
  rw [hcast]
  rfl

theorem zlibCompileFlags_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Zutil.zlibCompileFlags_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO
    (prog_fns_zlibCompileFlags hlib) rfl ⟨rfl, rfl⟩ (prog_fnProtos_zlibCompileFlags hlib)
    rfl (fun p hp => by cases hp) zlibCompileFlags_spec ?_ ?_
  · intro v owned m os args _ _ hawt
    rcases hawt with ⟨hlen, _⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Zutil.zlibCompileFlags_contract,
      Zlib.Zutil.zutilTU_fn_zlibCompileFlags, List.map_nil, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  · intro v owned m args ret m' _ hawt _ hpost
    rcases hawt with ⟨hlen, _⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Zutil.zlibCompileFlags_contract,
      Zlib.Zutil.zutilTU_fn_zlibCompileFlags, List.map_nil, List.length_nil] at hlen
    obtain rfl : args = [] := List.eq_nil_of_length_eq_zero hlen
    simp only [Zlib.Zutil.zutilTU_fn_zlibCompileFlags, CTy.isVoid, CTy.unqual,
      Bool.false_eq_true, ↓reduceIte]
    rcases hpost with ⟨bv, rfl⟩
    refine ⟨.int .u64 bv, ?_, rfl⟩
    simpa [castVal_unqual, CTy.unqual] using castVal_int_self m' .u64 bv

end Zlib.Proof
