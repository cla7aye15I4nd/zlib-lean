import C99.Proof.Mem
import C99.Proof.WP
import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgSpec
import Zlib.Compress

/-!
# Safety Proofs for `compress.c` (`compressBound_z`, `compressBound`)
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec

/-! ## Shared Helpers for `z_size_t` / `uLong` (`uint64_t`) Operations -/

private abbrev zSizeTCTy : CTy := .typedef "z_size_t" (.int .u64)
private abbrev uLongCTy : CTy := .typedef "uLong" (.int .u64)

private theorem zSizeTCTy_sizeof (tags : TypeEnv) : sizeofTy tags zSizeTCTy = 8 := by
  rw [← sizeofTy_unqual]; simp [CTy.unqual]; rfl

private theorem zSizeTCTy_alignof (tags : TypeEnv) : alignofTy tags zSizeTCTy = 8 := by
  rw [← alignofTy_unqual]; simp [CTy.unqual]; rfl

private theorem wp_readVar_zSizeT {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    {x : String} {bid : BlockId} {v : BitVec IntKind.u64.bits} {fs : List ExprFrame}
    (hlu : env.lookup x = some (bid, zSizeTCTy))
    (hmods : mods = [])
    (hrd : Sem.readVal prog.tags m bid 0 zSizeTCTy = some (.int .u64 v))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 v) (.int .u64)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) := by
  subst hmods
  refine WPTerm.of_exprPure ?_ hw
  unfold Sem.stepExprPure Sem.readPlace
  simp [hlu, ModSet.conflicts, hrd, CTy.decay, CTy.unqual]

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

private theorem wp_varInit_zSizeT {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {d : VarDecl} (frameBlks : List BlockId)
    {env : Env} {blks : List BlockId} {m0 m : Mem} {os : OSState} {k : Cont}
    {v : BitVec IntKind.u64.bits} {vty : CTy}
    (hd : d.ty = zSizeTCTy)
    (hf : LocalFrameMem m0 m (blks ++ frameBlks))
    (hw : ∀ (bv : BitVec IntKind.u64.bits) (bid : BlockId) (m' : Mem),
      bid = m.nextBlock →
      LocalFrameMem m0 m' ((bid :: blks) ++ frameBlks) →
      Sem.readVal prog.tags m' bid 0 zSizeTCTy = some (.int .u64 bv) →
      (∀ b' ≠ bid, m'.blocks b' = m.blocks b') →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls [])) ((d.name, bid, d.ty) :: env) (bid :: blks) m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 v) vty) []) (.varInit d []) []) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [hd, zSizeTCTy_sizeof]; decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [hd, zSizeTCTy_alignof]; decide
  refine WPTerm.of_localDecl_some (hd := rfl) hsz hal ?_
  intro baseB bid m1 hba halloc
  have hwr_ex := writeVal_fresh_int (tags := prog.tags) (m := m) (ty := d.ty)
    (k := .u64) (ba := baseB) (v := .int .u64 v) (iv := v.toNat)
    (by rw [hd]; rfl) hsz hal hba rfl
  rcases hwr_ex with ⟨m2, hwr⟩
  have hm1_eq : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty))
      (max 1 (alignofTy prog.tags d.ty)) .rw .stack baseB (fun _ => .undef)
      hsz hal hba).2 := (congrArg Prod.snd halloc).symm
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hwr' : Sem.writeVal m1 bid 0 d.ty.stripConst (.int .u64 v) = some m2 := by
    rw [hm1_eq, hbid]; exact hwr
  have hcast : Sem.castVal m1 d.ty.stripConst (.int .u64 v) = some (.int .u64 v) := by
    rw [castVal_unqual, stripConst_unqual, hd]
    exact castVal_int_self _ _ _
  have hwpPlace : Sem.writePlace prog.tags m1 bid 0 d.ty.stripConst (.rval (.int .u64 v) vty) =
      some (.rval (.int .u64 v) d.ty.stripConst, m2) := by
    unfold Sem.writePlace
    have hunq : d.ty.stripConst.unqual = .int .u64 := by rw [stripConst_unqual, hd]; rfl
    simp only [hunq, hcast, hwr', bind, Option.bind, pure, Pure.pure]
  refine ⟨.rval (.int .u64 v) d.ty.stripConst, m2, hwpPlace, ?_⟩
  have hf1 : LocalFrameMem m0 m1 ((bid :: blks) ++ frameBlks) := hf.alloc_stack halloc
  obtain ⟨bs, hbs⟩ := writeVal_writeBytes hwr'
  have hblk1 : m1.blocks bid = some ⟨max 1 (sizeofTy prog.tags d.ty),
      max 1 (alignofTy prog.tags d.ty), .rw, .stack, baseB, (fun _ => .undef),
      hsz, hal, hba⟩ := by
    rw [hm1_eq, hbid]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hf2 : LocalFrameMem m0 m2 ((bid :: blks) ++ frameBlks) := hf1.write_stack (.head _) hblk1 hbs
  have hrd : Sem.readVal prog.tags m2 bid 0 zSizeTCTy = some (.int .u64 v) := by
    have hwr_u64 : Sem.writeVal m1 bid 0 (.int .u64) (.int .u64 v) = some m2 := by
      have hc : d.ty.stripConst.isConst = false := stripConst_isConst d.ty
      have hu : d.ty.stripConst.unqual = .int .u64 := by rw [stripConst_unqual, hd]; rfl
      unfold Sem.writeVal at hwr' ⊢
      simp only [hc, Bool.not_false, guard_true, hu] at hwr'
      exact hwr'
    exact readVal_writeVal_same_int prog.tags hblk1 hwr_u64
  have hpres : ∀ b' ≠ bid, m2.blocks b' = m.blocks b' := by
    intro b' hne
    rw [writeVal_blocks_ne hwr' hne, hm1_eq,
      alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (by rw [← hbid]; exact hne)]
  exact hw v bid m2 hbid hf2 hrd hpres

private theorem wp_cast_u64_uLong {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    {v : BitVec IntKind.u64.bits} {ty : CTy} {fs : List ExprFrame}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 v) uLongCTy) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 v) ty) (.castF uLongCTy :: fs)) ctx mods)
        env blks m os k) := by
  refine WPTerm.of_exprPure ?_ hw
  have hcast : Sem.castVal m uLongCTy (.int .u64 v) = some (.int .u64 v) := by
    rw [castVal_unqual]; exact castVal_int_self _ _ _
  dsimp only [Sem.stepExprPure]
  rw [hcast]
  rfl

private theorem evalIntBinary_lt_u64 (a b : BitVec IntKind.u64.bits) :
    Sem.evalIntBinary .lt (.int .u64 a) (.int .u64 b) =
      some (.int .i32 (if decide ((a.toNat : Int) < (b.toNat : Int)) then 1 else 0), .int .i32) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .u64 = .u64 := rfl
  simp only [Sem.valAsInt?, IntKind.signed, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
  rw [hua]
  simp [Sem.cmpOrd]

private theorem evalIntBinary_ne_u64_self (a : BitVec IntKind.u64.bits) :
    Sem.evalIntBinary .ne (.int .u64 a) (.int .u64 a) = some (.int .i32 0, .int .i32) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .u64 = .u64 := rfl
  simp only [Sem.valAsInt?, IntKind.signed, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
  rw [hua]
  simp [Sem.cmpOrd]

/-! ## `compressBound_z` -/

theorem compressBound_z_spec
    {prog : Prog} {ext : ExtHandler} :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Compress.compressTU_fn_compressBound_z
      (fun _ args => ∃ bv : BitVec 64, args = [.int .u64 bv])
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  rcases hpre with ⟨bv, rfl⟩
  obtain ⟨(srcBv : BitVec IntKind.u64.bits), hsrcEq⟩ :
      ∃ x : BitVec IntKind.u64.bits, Val.int .u64 bv = Val.int .u64 x := ⟨bv, rfl⟩
  rw [hsrcEq] at hpush
  dsimp only [Zlib.Compress.compressTU_fn_compressBound_z] at hpush
  rw [List.zip_cons_cons, List.zip_nil_right] at hpush
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hszS, halS, hbaS, m2, hwrS, hpushRest⟩ := pushCallParams_cons_inv hpush
  simp only [pushCallParams_zero, Option.some.injEq, Prod.mk.injEq] at hpushRest
  rcases hpushRest with ⟨rfl, rfl, hm12⟩
  subst hm12
  have hnext2 : m2.nextBlock = m.nextBlock + 1 := by
    rw [writeVal_nextBlock hwrS, alloc_snd_nextBlock]
  have hrdS : Sem.readVal prog.tags m2 m.nextBlock 0 zSizeTCTy = some (.int .u64 srcBv) :=
    readVal_writeVal_same_int prog.tags (alloc_blocks_eq _ _ _ _ _ _ _ _ _ _) hwrS
  wp_steps
  -- `sourceLen + (sourceLen >> 12) + (sourceLen >> 14) + (sourceLen >> 25) + 13`
  refine wp_readVar_zSizeT rfl rfl hrdS ?_
  wp_steps
  refine wp_readVar_zSizeT rfl rfl hrdS ?_
  wp_steps
  refine wp_readVar_zSizeT rfl rfl hrdS ?_
  wp_steps
  refine wp_readVar_zSizeT rfl rfl hrdS ?_
  wp_steps
  -- `z_size_t bound = ...;`
  refine wp_varInit_zSizeT [m.nextBlock] (m0 := m) rfl hf1 ?_
  intro boundBv bid m4 hbid hf4 hrdB hm4_pres
  have hneBid : m.nextBlock ≠ bid := by
    rw [hbid, hnext2]; exact Nat.ne_of_lt (Nat.lt_succ_self _)
  have hrdS4 : Sem.readVal prog.tags m4 m.nextBlock 0 zSizeTCTy = some (.int .u64 srcBv) := by
    rw [readVal_eq_of_blocks_eq prog.tags (hm4_pres m.nextBlock hneBid)]
    exact hrdS
  wp_steps
  -- `return bound < sourceLen ? (z_size_t)-1 : bound;`
  refine wp_readVar_zSizeT rfl rfl hrdB ?_
  wp_steps
  refine wp_readVar_zSizeT rfl rfl hrdS4 ?_
  refine WPTerm.of_exprPure (m' := m4) (mods' := []) (es' := .ret (.rval (.int .i32
      (if decide ((boundBv.toNat : Int) < (srcBv.toNat : Int)) then 1 else 0)) (.int .i32))
      [.condF (.cast zSizeTCTy (.unary .neg (.lit 1))) (.var "bound")]) ?_ ?_
  · unfold Sem.stepExprPure Sem.applyBinary
    simp [CTy.isPtr, CTy.unqual, evalIntBinary_lt_u64]
  have hf4_sub : LocalFrameMem m (m4.freeStack [bid]) [m.nextBlock] :=
    LocalFrameMem.freeStack_sub hf4
  have hro : ROExt m ((m4.freeStack [bid]).freeStack [m.nextBlock]) :=
    LocalFrameMem.roExt_freeStack hf4_sub
  by_cases hcmp : (boundBv.toNat : Int) < (srcBv.toNat : Int)
  · have hdec : decide ((boundBv.toNat : Int) < (srcBv.toNat : Int)) = true :=
      decide_eq_true hcmp
    rw [hdec]
    dsimp only
    wp_steps
    exact hcont _ ((m4.freeStack [bid]).freeStack [m.nextBlock]) hro ⟨_, rfl⟩
  · have hdec : decide ((boundBv.toNat : Int) < (srcBv.toNat : Int)) = false :=
      decide_eq_false hcmp
    rw [hdec]
    dsimp only
    wp_steps
    refine wp_readVar_zSizeT rfl rfl hrdB ?_
    refine WPTerm.of_det
      (s' := .running (.expr (.ret (.rval (.int .u64 boundBv) zSizeTCTy) fs) ctx [])
        env blks ((m4.freeStack [bid]).freeStack [m.nextBlock]) os k) ?_
      (hcont (.int .u64 boundBv) ((m4.freeStack [bid]).freeStack [m.nextBlock]) hro ⟨boundBv, rfl⟩)
    unfold Sem.stepDet
    simp only [Zlib.Compress.compressTU_fn_compressBound_z, Sem.Cont.topRetTy,
      CTy.isVoid, CTy.unqual, Sem.unwindReturn, ↓reduceIte, Bool.false_eq_true, Option.bind]
    have hcast : Sem.castVal m4 zSizeTCTy (.int .u64 boundBv) = some (.int .u64 boundBv) := by
      rw [castVal_unqual]; exact castVal_int_self _ _ _
    rw [hcast]
    rfl

theorem compressBound_z_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Compress.compressBound_z_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO
    (prog_fns_compressBound_z hlib) rfl ⟨rfl, rfl⟩ (prog_fnProtos_compressBound_z hlib)
    rfl (fun p hp => by
      simp only [Zlib.Compress.compressTU_fn_compressBound_z, List.mem_singleton] at hp
      subst hp
      exact isSimpleParamTy_iff.mpr (Or.inl ⟨.u64, rfl⟩))
    compressBound_z_spec ?_ ?_
  · intro v owned m os args _ _ hawt
    rcases hawt with ⟨hlen, hval⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Compress.compressBound_z_contract,
      Zlib.Compress.compressTU_fn_compressBound_z, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil] at hlen hval
    cases args with
    | nil => cases hlen
    | cons a rest =>
      cases rest with
      | cons _ _ => cases hlen
      | nil =>
        have hv0 := hval 0 (by decide)
        simp only [List.getElem?_cons_zero, List.getElem_cons_zero, ValHasCTy, CTy.unqual] at hv0
        rcases hv0 with ⟨bv, rfl⟩
        exact ⟨bv, rfl⟩
  · intro v owned m args ret m' _ hawt _ hpost
    rcases hawt with ⟨hlen, hval⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Compress.compressBound_z_contract,
      Zlib.Compress.compressTU_fn_compressBound_z, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil] at hlen hval
    cases args with
    | nil => cases hlen
    | cons a rest =>
      cases rest with
      | cons _ _ => cases hlen
      | nil =>
        have hv0 := hval 0 (by decide)
        simp only [List.getElem?_cons_zero, List.getElem_cons_zero, ValHasCTy, CTy.unqual] at hv0
        rcases hv0 with ⟨abv, rfl⟩
        simp only [Zlib.Compress.compressTU_fn_compressBound_z, CTy.isVoid, CTy.unqual,
          Bool.false_eq_true, ↓reduceIte]
        rcases hpost with ⟨rbv, rfl⟩
        refine ⟨.int .u64 rbv, ?_, ?_⟩
        · rw [castVal_unqual]; exact castVal_int_self _ _ _
        · dsimp [Zlib.Compress.compressBound_z_contract]

/-! ## `compressBound` -/

private theorem enumConst_scan_eq_none (rest : TypeEnv) (name : String)
    (hrest : enumConst? rest name = none) :
    ∀ (items : List (String × Option Int)) (nextVal : Int),
      items.all (fun (k, _) => k != name) = true →
      enumConst?.scan rest name nextVal items = none := by
  intro items
  induction items with
  | nil =>
    intro nextVal _
    unfold enumConst?.scan
    exact hrest
  | cons hd tl ih =>
    intro nextVal hall
    rcases hd with ⟨k, v?⟩
    unfold enumConst?.scan
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hne : (k == name) = false := by
      have := hall.1
      simp only [bne_iff_ne, ne_eq] at this
      exact beq_false_of_ne this
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact ih _ hall.2

private theorem enumConst_eq_none_of_all (name : String) :
    ∀ (tags : TypeEnv),
      tags.all (fun | (_, .enumDef items _) => items.all (fun (k, _) => k != name) | _ => true) = true →
      enumConst? tags name = none
  | [], _ => by unfold enumConst?; rfl
  | (tag, defn) :: rest, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hrest := enumConst_eq_none_of_all name rest hall.2
    cases defn with
    | structDef _ | unionDef _ =>
      unfold enumConst?
      exact hrest
    | enumDef items isU =>
      unfold enumConst?
      exact enumConst_scan_eq_none rest name hrest items 0 hall.1

private theorem enumConst_progTags_compressBound_z (tags : TypeEnv)
    (htags : tags = (progOfTUs Zlib.allFiles).tags) :
    enumConst? tags "compressBound_z" = none := by
  subst htags
  apply enumConst_eq_none_of_all
  decide

theorem compressBound_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Compress.compressTU_fn_compressBound
      (fun _ args => ∃ bv : BitVec 64, args = [.int .u64 bv])
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _ hpush hcont
  rcases hpre with ⟨bv, rfl⟩
  obtain ⟨(srcBv : BitVec IntKind.u64.bits), hsrcEq⟩ :
      ∃ x : BitVec IntKind.u64.bits, Val.int .u64 bv = Val.int .u64 x := ⟨bv, rfl⟩
  rw [hsrcEq] at hpush
  dsimp only [Zlib.Compress.compressTU_fn_compressBound] at hpush
  rw [List.zip_cons_cons, List.zip_nil_right] at hpush
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hszS, halS, hbaS, m2, hwrS, hpushRest⟩ := pushCallParams_cons_inv hpush
  simp only [pushCallParams_zero, Option.some.injEq, Prod.mk.injEq] at hpushRest
  rcases hpushRest with ⟨rfl, rfl, hm12⟩
  subst hm12
  have hrdS : Sem.readVal prog.tags m2 m.nextBlock 0 uLongCTy = some (.int .u64 srcBv) :=
    readVal_writeVal_same_int prog.tags (alloc_blocks_eq _ _ _ _ _ _ _ _ _ _) hwrS
  wp_steps
  -- Resolve `compressBound_z` as function pointer via `prog.fnProtos`
  have hluNone : ((("sourceLen", m.nextBlock, uLongCTy) ::
      (prog.fnStatics "compressBound" ++ prog.globalEnv)).lookup "compressBound_z") = none := by
    rw [prog_fnStatics_compressBound hlib, List.nil_append, hlib.globalEnv_eq,
      lookup_cons_ne _ (by decide)]
    exact hlib.gEnv_lookup_none "compressBound_z" (by decide)
  have henumNone : enumConst? prog.tags "compressBound_z" = none :=
    enumConst_progTags_compressBound_z prog.tags hlib.prog_tags_eq
  have hproto : prog.fnProtos "compressBound_z" =
      some (fnDefSig Zlib.Compress.compressTU_fn_compressBound_z) :=
    prog_fnProtos_compressBound_z hlib
  refine WPTerm.of_exprPure
    (m' := m2) (mods' := [])
    (es' := .ret (.rval (.fnPtr "compressBound_z")
      (.fnPtr zSizeTCTy [zSizeTCTy] false))
      [.callFnF [.var "sourceLen"]]) ?_ ?_
  · unfold Sem.stepExprPure
    simp only [hluNone, henumNone, hproto, fnDefSig, Zlib.Compress.compressTU_fn_compressBound_z,
      List.map_cons, List.map_nil]
    rfl
  wp_steps
  -- Evaluate argument `sourceLen`
  refine wp_readVar_uLong rfl rfl hrdS ?_
  -- Internal call `compressBound_z(sourceLen)`
  have hcoerce : Sem.coerceCallArgs m2
      (Zlib.Compress.compressTU_fn_compressBound_z.params.map (·.ty)) false
      [(.int .u64 srcBv, .int .u64)] = some [.int .u64 srcBv] := by
    simp only [Zlib.Compress.compressTU_fn_compressBound_z, List.map_cons, List.map_nil]
    refine coerceCallArgs_cons_nonvariadic ?_ (coerceCallArgs_nil m2)
    rw [castVal_unqual]; exact castVal_int_self _ _ _
  refine FuncBodySpec.call compressBound_z_spec
    (sym := "compressBound_z")
    (fnTy := .fnPtr zSizeTCTy [zSizeTCTy] false)
    (argVals := [(.int .u64 srcBv, .int .u64)])
    (coerced := [.int .u64 srcBv])
    (by rfl) (prog_fns_compressBound_z hlib)
    rfl rfl hcoerce ⟨srcBv, rfl⟩ (fun p hp => by
      simp only [Zlib.Compress.compressTU_fn_compressBound_z, List.mem_singleton] at hp
      subst hp
      exact isSimpleParamTy_iff.mpr (Or.inl ⟨.u64, rfl⟩)) ?_
  intro ret m3 hro23 hpost3
  rcases hpost3 with ⟨rbv, hret⟩
  obtain ⟨(boundBv : BitVec IntKind.u64.bits), rfl⟩ :
      ∃ x : BitVec IntKind.u64.bits, ret = Val.int .u64 x := ⟨rbv, hret⟩
  have hf3 : LocalFrameMem m m3 [m.nextBlock] := hf1.of_roExt hro23
  -- Allocate `z_size_t bound = ret;`
  refine wp_varInit_zSizeT [m.nextBlock] (m0 := m) rfl hf3 ?_
  intro boundBv2 bid m4 hbid hf4 hrdB _
  wp_steps
  -- `return (uLong)bound != bound ? (uLong)-1 : (uLong)bound;`
  refine wp_readVar_zSizeT rfl rfl hrdB ?_
  refine wp_cast_u64_uLong ?_
  wp_steps
  refine wp_readVar_zSizeT rfl rfl hrdB ?_
  refine WPTerm.of_exprPure
    (m' := m4) (mods' := [])
    (es' := .ret (.rval (.int .i32 0) (.int .i32))
      [.condF (.cast uLongCTy (.unary .neg (.lit 1))) (.cast uLongCTy (.var "bound"))]) ?_ ?_
  · unfold Sem.stepExprPure Sem.applyBinary
    simp [CTy.isPtr, CTy.unqual, evalIntBinary_ne_u64_self]
  wp_steps
  -- Else branch: `(uLong)bound`
  refine wp_readVar_zSizeT rfl rfl hrdB ?_
  refine wp_cast_u64_uLong ?_
  have hf4_sub : LocalFrameMem m (m4.freeStack [bid]) [m.nextBlock] :=
    LocalFrameMem.freeStack_sub hf4
  have hro : ROExt m ((m4.freeStack [bid]).freeStack [m.nextBlock]) :=
    LocalFrameMem.roExt_freeStack hf4_sub
  refine WPTerm.of_det
    (s' := .running (.expr (.ret (.rval (.int .u64 boundBv2) uLongCTy) fs) ctx [])
      env blks ((m4.freeStack [bid]).freeStack [m.nextBlock]) os k) ?_
    (hcont (.int .u64 boundBv2) ((m4.freeStack [bid]).freeStack [m.nextBlock]) hro ⟨boundBv2, rfl⟩)
  unfold Sem.stepDet
  simp only [Zlib.Compress.compressTU_fn_compressBound, Sem.Cont.topRetTy,
    CTy.isVoid, CTy.unqual, Sem.unwindReturn, ↓reduceIte, Bool.false_eq_true, Option.bind]
  have hcastRet : Sem.castVal m4 uLongCTy (.int .u64 boundBv2) = some (.int .u64 boundBv2) := by
    rw [castVal_unqual]; exact castVal_int_self _ _ _
  rw [hcastRet]
  rfl

theorem compressBound_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Compress.compressBound_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO
    (prog_fns_compressBound hlib) rfl ⟨rfl, rfl⟩ (prog_fnProtos_compressBound hlib)
    rfl (fun p hp => by
      simp only [Zlib.Compress.compressTU_fn_compressBound, List.mem_singleton] at hp
      subst hp
      exact isSimpleParamTy_iff.mpr (Or.inl ⟨.u64, rfl⟩))
    (compressBound_spec hlib) ?_ ?_
  · intro v owned m os args _ _ hawt
    rcases hawt with ⟨hlen, hval⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Compress.compressBound_contract,
      Zlib.Compress.compressTU_fn_compressBound, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil] at hlen hval
    cases args with
    | nil => cases hlen
    | cons a rest =>
      cases rest with
      | cons _ _ => cases hlen
      | nil =>
        have hv0 := hval 0 (by decide)
        simp only [List.getElem?_cons_zero, List.getElem_cons_zero, ValHasCTy, CTy.unqual] at hv0
        rcases hv0 with ⟨bv, rfl⟩
        exact ⟨bv, rfl⟩
  · intro v owned m args ret m' _ hawt _ hpost
    rcases hawt with ⟨hlen, hval⟩
    simp only [Bool.false_eq_true, ↓reduceIte, Zlib.Compress.compressBound_contract,
      Zlib.Compress.compressTU_fn_compressBound, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil] at hlen hval
    cases args with
    | nil => cases hlen
    | cons a rest =>
      cases rest with
      | cons _ _ => cases hlen
      | nil =>
        have hv0 := hval 0 (by decide)
        simp only [List.getElem?_cons_zero, List.getElem_cons_zero, ValHasCTy, CTy.unqual] at hv0
        rcases hv0 with ⟨abv, rfl⟩
        simp only [Zlib.Compress.compressTU_fn_compressBound, CTy.isVoid, CTy.unqual,
          Bool.false_eq_true, ↓reduceIte]
        rcases hpost with ⟨rbv, rfl⟩
        refine ⟨.int .u64 rbv, ?_, ?_⟩
        · rw [castVal_unqual]; exact castVal_int_self _ _ _
        · dsimp [Zlib.Compress.compressBound_contract]

end Zlib.Proof
