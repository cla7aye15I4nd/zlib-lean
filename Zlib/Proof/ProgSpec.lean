import C99.Proof.Mem
import C99.Proof.WP
import Zlib.Proof.ProgLookup
import Zlib.Spec.Safety

/-!
# Shared Specification & WP Combinators for Zlib Safety Proofs

Defines:
- `ROExt` bridges to `FramePreserved` and `NoHeapLeak`.
- `BaseInv`: client-frame-stable and `ROExt`-stable core library memory invariant
  (preserved globals from `initLibz`, active `errno` block, owned-block consistency).
- `castVal` / `coerceCallArgs` / `pushCallParams` bridges for well-typed C ABI calls.
- `FuncBodySpec`: reusable function body WP specification supporting both internal
  C calls (`FuncBodySpec.call`, `FuncBodySpec.call_simple`) and top-level
  public `ContractSafe` proofs (`FuncBodySpec.to_contractSafe`).
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec

/-! ## 1. Read-Only Extension & `FramePreserved` / `NoHeapLeak` -/

theorem freeStack_nil (m : Mem) : m.freeStack [] = m := by
  cases m
  simp [Mem.freeStack]

theorem roExt_framePreserved {m m' : Mem} (hro : ROExt m m') (allowed : BlockSet) :
    Zlib.Spec.FramePreserved m m' allowed := by
  refine ⟨?_, ?_⟩
  · intro b hsome _
    rcases Option.isSome_iff_exists.mp hsome with ⟨blk, hblk⟩
    exact hro.2.1 b (lt_nextBlock_of_some hblk)
  · intro b blk hnone hsome _
    cases Nat.lt_or_ge b m.nextBlock with
    | inl hlt =>
      rw [hro.2.1 b hlt] at hsome
      rw [hnone] at hsome
      cases hsome
    | inr hge =>
      exact hro.2.2 b blk hge hsome

theorem roExt_noHeapLeak {m m' : Mem} (hro : ROExt m m') (owned' : BlockSet) :
    Zlib.Spec.NoHeapLeak m m' owned' := by
  intro b blk hsome hheap
  cases Nat.lt_or_ge b m.nextBlock with
  | inl hlt =>
    left
    rw [hro.2.1 b hlt] at hsome
    simp [hsome]
  | inr hge =>
    have hroBlk := hro.2.2 b blk hge hsome
    rw [hroBlk.1] at hheap
    cases hheap

theorem readVal_eq_of_blocks_eq (tags : TypeEnv) {m1 m2 : Mem} {b : BlockId}
    (hb : m1.blocks b = m2.blocks b) (off : Int64) (ty : CTy) :
    Sem.readVal tags m1 b off ty = Sem.readVal tags m2 b off ty := by
  unfold Sem.readVal Mem.readBytes
  rw [hb]

theorem LocalFrameMem.freeStack_all {m0 m : Mem} {drop : List BlockId}
    (hf : LocalFrameMem m0 m drop) : LocalFrameMem m0 (m.freeStack drop) [] :=
  LocalFrameMem.freeStack_sub (drop := drop) (keep := []) (by simpa using hf)

theorem LocalFrameMem.roExt_freeStack {m0 m : Mem} {drop : List BlockId}
    (hf : LocalFrameMem m0 m drop) : ROExt m0 (m.freeStack drop) :=
  LocalFrameMem.to_roExt (LocalFrameMem.freeStack_all hf)

/-! ## 2. Base Library Memory Invariant -/

/-- Core invariant shared by all waves of the `zlib` safety proof. Every field
depends only on protected globals, `errno`, `owned` heap blocks, and `ClientView`
emptiness, so it is preserved both by client activity (`ClientFrame`) and by
read-only library execution (`ROExt`). -/
structure BaseInv (m0 : Mem) (os0 : OSState)
    (v : Zlib.Spec.ClientView) (owned : Zlib.Spec.BlockSet)
    (m : Mem) (os : OSState) : Prop where
  roGlobals : ∀ b, (m0.blocks b).isSome = true → b ≠ os0.errnoBlk → m.blocks b = m0.blocks b
  errnoBlkEq : os.errnoBlk = os0.errnoBlk
  errnoValid : ∃ blk, m.blocks os.errnoBlk = some blk ∧
    blk.size = 4 ∧ blk.align = 4 ∧ blk.perm = .rw ∧ blk.kind = .global
  ownedActive : ∀ b, owned b → (m.blocks b).isSome = true
  emptyNoOwned : v.isEmpty → ∀ b, ¬ owned b

theorem BaseInv.init {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    BaseInv m0 os0 Zlib.Spec.ClientView.empty (fun _ => False) m0 os0 := by
  refine ⟨fun _ _ _ => rfl, rfl, ?_, fun _ h => False.elim h, fun _ _ h => False.elim h⟩
  rcases hlib.errno_blk with ⟨blk, hblk, hsz, hal, hperm, hkind, _⟩
  exact ⟨blk, hblk, hsz, hal, hperm, hkind⟩

theorem BaseInv.clientFrame {tags : TypeEnv} {m0 : Mem} {os0 : OSState}
    {v : Zlib.Spec.ClientView} {owned : Zlib.Spec.BlockSet}
    {m m' : Mem} {os os' : OSState}
    (hb : BaseInv m0 os0 v owned m os)
    (hcf : Zlib.Spec.ClientFrame tags m0 v owned m m' os os') :
    BaseInv m0 os0 v owned m' os' := by
  rcases hcf with ⟨herrnoEq, _, hprot, _⟩
  refine ⟨?_, ?_, ?_, ?_, hb.emptyNoOwned⟩
  · intro b hm0 hne
    have hlibP : Zlib.Spec.LibProtected m0 owned os m b := Or.inr (Or.inr (Or.inr (Or.inl hm0)))
    rw [hprot b hlibP, hb.roGlobals b hm0 hne]
  · rw [herrnoEq, hb.errnoBlkEq]
  · have hlibP : Zlib.Spec.LibProtected m0 owned os m os.errnoBlk := Or.inr (Or.inl rfl)
    rw [herrnoEq, hprot os.errnoBlk hlibP]
    exact hb.errnoValid
  · intro b hown
    have hlibP : Zlib.Spec.LibProtected m0 owned os m b := Or.inl hown
    rw [hprot b hlibP]
    exact hb.ownedActive b hown

theorem BaseInv.roExt {m0 : Mem} {os0 : OSState}
    {v : Zlib.Spec.ClientView} {owned : Zlib.Spec.BlockSet}
    {m m' : Mem} {os : OSState}
    (hb : BaseInv m0 os0 v owned m os)
    (hro : ROExt m m') :
    BaseInv m0 os0 v owned m' os := by
  refine ⟨?_, hb.errnoBlkEq, ?_, ?_, hb.emptyNoOwned⟩
  · intro b hm0 hne
    have hm := hb.roGlobals b hm0 hne
    have hmIsSome : (m.blocks b).isSome = true := by rw [hm]; exact hm0
    rcases Option.isSome_iff_exists.mp hmIsSome with ⟨blk, hblk⟩
    rw [hro.2.1 b (lt_nextBlock_of_some hblk), hm]
  · rcases hb.errnoValid with ⟨blk, hblk, hsz, hal, hperm, hkind⟩
    exact ⟨blk, by rw [hro.2.1 os.errnoBlk (lt_nextBlock_of_some hblk)]; exact hblk,
      hsz, hal, hperm, hkind⟩
  · intro b hown
    rcases Option.isSome_iff_exists.mp (hb.ownedActive b hown) with ⟨blk, hblk⟩
    rw [hro.2.1 b (lt_nextBlock_of_some hblk)]
    simp [hblk]

section GlobalAccessors

variable {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
  {v : Zlib.Spec.ClientView} {owned : Zlib.Spec.BlockSet} {m : Mem} {os : OSState}

theorem BaseInv.global_block_eq_of_m0_size_ne (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os) {b : BlockId} {blk : Block}
    (hblk : m0.blocks b = some blk) (hsz : blk.size ≠ 4) :
    m.blocks b = some blk := by
  by_cases hne : b = os0.errnoBlk
  · subst hne
    rcases hlib.errno_blk with ⟨eblk, heblk, hesz, _⟩
    rw [hblk] at heblk
    cases heblk
    exact False.elim (hsz hesz)
  · rw [hb.roGlobals b (by simp [hblk]) hne, hblk]

theorem BaseInv.crc_table (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os) :
    ∃ b blk,
      gEnv.lookup "crc_table" = some (b, .array crcConstTy (some 256)) ∧
      m.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
      blk.size = 1024 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) := by
  rcases hlib.crc_table_prop with ⟨b, blk, hlu, hblk, hperm, hkind, hsz, hal, hbytes⟩
  have hm : m.blocks b = some blk :=
    BaseInv.global_block_eq_of_m0_size_ne hlib hb hblk (by rw [hsz]; decide)
  exact ⟨b, blk, hlu, hm, hperm, hkind, hsz, hal, hbytes⟩

theorem BaseInv.crc_braid2_table (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os) :
    ∃ b blk,
      gEnv.lookup "crc_braid2_table" = some (b, .array (.array crcConstTy (some 256)) (some 4)) ∧
      m.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
      blk.size = 4096 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) := by
  rcases hlib.crc_braid2_table_prop with ⟨b, blk, hlu, hblk, hperm, hkind, hsz, hal, hbytes⟩
  have hm : m.blocks b = some blk :=
    BaseInv.global_block_eq_of_m0_size_ne hlib hb hblk (by rw [hsz]; decide)
  exact ⟨b, blk, hlu, hm, hperm, hkind, hsz, hal, hbytes⟩

theorem BaseInv.crc_braid5_table (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os) :
    ∃ b blk,
      gEnv.lookup "crc_braid5_table" = some (b, .array (.array crcConstTy (some 256)) (some 4)) ∧
      m.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
      blk.size = 4096 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) := by
  rcases hlib.crc_braid5_table_prop with ⟨b, blk, hlu, hblk, hperm, hkind, hsz, hal, hbytes⟩
  have hm : m.blocks b = some blk :=
    BaseInv.global_block_eq_of_m0_size_ne hlib hb hblk (by rw [hsz]; decide)
  exact ⟨b, blk, hlu, hm, hperm, hkind, hsz, hal, hbytes⟩

theorem BaseInv.x2n_table (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os) :
    ∃ b blk,
      gEnv.lookup "x2n_table" = some (b, .array crcConstTy (some 32)) ∧
      m.blocks b = some blk ∧ blk.perm = .ro ∧ blk.kind = .global ∧
      blk.size = 128 ∧ blk.align = 4 ∧ (∀ i, ∃ u : UInt8, blk.bytes i = .byte u) ∧
      (∀ i < 32, ∃ bv : BitVec 32,
        Sem.readVal prog.tags m b (Int64.ofNat (4 * i)) (.int .u32) = some (.int .u32 bv) ∧
        bv = BitVec.ofInt 32 Zlib.Tables.crc32H_vals_x2n_table[i]! ∧
        bv.toNat ≠ 0) := by
  rcases hlib.x2n_table_prop with ⟨b, blk, hlu, hblk, hperm, hkind, hsz, hal, hbytes, hread⟩
  have hm : m.blocks b = some blk :=
    BaseInv.global_block_eq_of_m0_size_ne hlib hb hblk (by rw [hsz]; decide)
  refine ⟨b, blk, hlu, hm, hperm, hkind, hsz, hal, hbytes, ?_⟩
  intro i hi
  rcases hread i hi with ⟨bv, hrv, hval, hnz⟩
  refine ⟨bv, ?_, hval, hnz⟩
  rw [readVal_eq_of_blocks_eq prog.tags (hb := hm.trans hblk.symm)]
  exact hrv

end GlobalAccessors

/-! ## 3. Well-Typed Call Arguments, `castVal`, `coerceCallArgs`, and `pushCallParams` -/

theorem unqual_idemp (ty : CTy) : ty.unqual.unqual = ty.unqual := by
  match ty with
  | .const_ t => simp [CTy.unqual, unqual_idemp t]
  | .typedef _ t => simp [CTy.unqual, unqual_idemp t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList =>
    simp [CTy.unqual]

/-- Parameter types handled uniformly for zero-overhead stack parameter allocation
across scalar/pointer C functions. -/
def IsSimpleParamTy (ty : CTy) : Prop :=
  match ty.unqual with
  | .int _ => True
  | .ptr _ => True
  | _ => False

theorem isSimpleParamTy_iff {ty : CTy} :
    IsSimpleParamTy ty ↔ (∃ k, ty.unqual = .int k) ∨ (∃ el, ty.unqual = .ptr el) := by
  unfold IsSimpleParamTy
  cases ty.unqual <;> simp

theorem castVal_unqual (m : Mem) (ty : CTy) (v : Val) :
    Sem.castVal m ty v = Sem.castVal m ty.unqual v := by
  unfold Sem.castVal
  simp [unqual_idemp]

theorem valHasCTy_unqual {ty : CTy} {v : Val} :
    Zlib.Spec.ValHasCTy ty v ↔ Zlib.Spec.ValHasCTy ty.unqual v := by
  unfold Zlib.Spec.ValHasCTy
  simp [unqual_idemp]

theorem castVal_of_valHasCTy {m : Mem} {ty : CTy} {v : Val}
    (ht : match ty.unqual with
      | .void | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ | .vaList => True
      | _ => False)
    (hv : Zlib.Spec.ValHasCTy ty v) :
    Sem.castVal m ty v = some v := by
  rw [castVal_unqual]
  rw [valHasCTy_unqual] at hv
  revert ht hv
  refine (match h : ty.unqual with
    | .void => fun _ hv => by
      unfold Zlib.Spec.ValHasCTy at hv
      simp [CTy.unqual] at hv
      subst hv
      simp [Sem.castVal, CTy.unqual, CTy.isVoid]
    | .int k => fun _ hv => by
      unfold Zlib.Spec.ValHasCTy at hv
      simp [CTy.unqual] at hv
      rcases hv with ⟨bv, rfl⟩
      simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast]
      cases k.signed <;> simp
    | .enumTy tag isU => fun _ hv => by
      unfold Zlib.Spec.ValHasCTy at hv
      simp [CTy.unqual] at hv
      cases isU
      · simp at hv
        rcases hv with ⟨bv, rfl⟩
        simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast, IntKind.signed]
      · simp at hv
        rcases hv with ⟨bv, rfl⟩
        simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast, IntKind.signed]
    | .ptr el => fun _ hv => by
      unfold Zlib.Spec.ValHasCTy at hv
      simp [CTy.unqual] at hv
      rcases hv with rfl | ⟨b, off, rfl⟩ <;> simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]
    | .fnPtr r ps va => fun _ hv => by
      unfold Zlib.Spec.ValHasCTy at hv
      simp [CTy.unqual] at hv
      rcases hv with rfl | ⟨s, rfl⟩ <;> simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]
    | .vaList => fun _ hv => by
      unfold Zlib.Spec.ValHasCTy at hv
      simp [CTy.unqual] at hv
      subst hv
      simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]
    | .array _ _ | .structTy _ | .unionTy _ | .anonStruct _
    | .anonUnion _ | .const_ _ | .typedef _ _ => fun ht _ => False.elim ht)

theorem castVal_produces_valHasCTy {m : Mem} :
    ∀ {ty : CTy} {v cv : Val},
      Sem.castVal m ty v = some cv → Zlib.Spec.ValHasCTy ty cv
  | .const_ t, v, cv, hc => by
    rw [castVal_unqual] at hc
    rw [valHasCTy_unqual]
    simp only [CTy.unqual] at hc ⊢
    rw [← castVal_unqual] at hc
    rw [← valHasCTy_unqual]
    exact castVal_produces_valHasCTy hc
  | .typedef _ t, v, cv, hc => by
    rw [castVal_unqual] at hc
    rw [valHasCTy_unqual]
    simp only [CTy.unqual] at hc ⊢
    rw [← castVal_unqual] at hc
    rw [← valHasCTy_unqual]
    exact castVal_produces_valHasCTy hc
  | .void, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid] at hc
    subst hc
    simp [Zlib.Spec.ValHasCTy, CTy.unqual]
  | .int k, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
    cases v <;> simp at hc
    · subst hc; unfold Sem.ofIntCast Zlib.Spec.ValHasCTy; simp [CTy.unqual]
    · rcases hc with ⟨a, _, rfl⟩; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    · subst hc; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
  | .enumTy tag isU, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
    cases v <;> simp at hc
    · subst hc; unfold Sem.ofIntCast Zlib.Spec.ValHasCTy; simp [CTy.unqual]
    · rcases hc with ⟨a, _, rfl⟩; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    · subst hc; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
  | .ptr el, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
    cases v <;> simp at hc
    · rcases hc with ⟨_, rfl⟩; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    · subst hc; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    · subst hc; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
  | .fnPtr r ps va, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
    cases v <;> simp at hc
    · rcases hc with ⟨_, rfl⟩; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    · subst hc; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    · subst hc; simp [Zlib.Spec.ValHasCTy, CTy.unqual]
  | .vaList, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
    cases v with
    | vaList fl =>
      cases fl <;> simp at hc
      subst hc
      simp [Zlib.Spec.ValHasCTy, CTy.unqual]
    | _ => simp at hc
  | .array _ _, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
  | .structTy _, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
  | .unionTy _, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
  | .anonStruct _, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
  | .anonUnion _, v, cv, hc => by
    simp [Sem.castVal, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc

private theorem mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {out : List β}, l.mapM f = some out → out.length = l.length
  | [], out, h => by
    rw [List.mapM_nil] at h
    cases h
    rfl
  | x :: xs, out, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some ys =>
        have hout : out = y :: ys := by
          simpa [hx, hxs] using h.symm
        subst hout
        simp [mapM_option_length hxs]

theorem coerceCallArgs_length {m : Mem} {ptys : List CTy}
    {argVals : List (Val × CTy)} {coerced : List Val}
    (hc : Sem.coerceCallArgs m ptys false argVals = some coerced) :
    coerced.length = ptys.length ∧ argVals.length = ptys.length := by
  unfold Sem.coerceCallArgs at hc
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at hc
  cases hbeq : (argVals.length == ptys.length) with
  | false =>
    simp [hbeq, guard] at hc
  | true =>
    have hlen : argVals.length = ptys.length := Nat.eq_of_beq_eq_true hbeq
    simp only [hbeq, guard, ↓reduceIte] at hc
    have hmap : coerced.length = (ptys.zip argVals).length := mapM_option_length hc
    rw [List.length_zip, hlen, Nat.min_self] at hmap
    exact ⟨hmap, hlen⟩

private theorem mapM_castVal_of_list {m : Mem} :
    ∀ {ptys cParamTys : List CTy} {args : List Val},
      ptys.map CTy.unqual = cParamTys.map CTy.unqual →
      args.length = cParamTys.length →
      (∀ i (hi : i < cParamTys.length),
        match args[i]? with
        | some v => Zlib.Spec.ValHasCTy cParamTys[i] v
        | none => False) →
      (∀ p ∈ ptys, match p.unqual with
        | .void | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ | .vaList => True
        | _ => False) →
      List.mapM (fun (x : CTy × (Val × CTy)) => Sem.castVal m x.1 x.2.1)
          (ptys.zip (args.map (fun v => (v, .void)))) = some args
  | [], [], [], _, _, _, _ => rfl
  | p :: ps, cp :: cps, a :: as, hmap, hlen, hval, hsimple => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    have hs0 := hsimple p (by simp)
    have hv0 := hval 0 (by simp)
    simp only [List.getElem?_cons_zero, List.getElem_cons_zero] at hv0
    have hvP : Zlib.Spec.ValHasCTy p a := by
      rw [valHasCTy_unqual, hmap.1, ← valHasCTy_unqual]
      exact hv0
    have hcast : Sem.castVal m p a = some a := castVal_of_valHasCTy hs0 hvP
    have htail : List.mapM (fun (x : CTy × (Val × CTy)) => Sem.castVal m x.1 x.2.1)
        (ps.zip (as.map (fun v => (v, .void)))) = some as := by
      apply mapM_castVal_of_list hmap.2 (by simp at hlen; exact hlen)
      · intro i hi
        have h := hval (i + 1) (by simp; omega)
        simp only [List.getElem?_cons_succ, List.getElem_cons_succ] at h
        exact h
      · intro q hq
        exact hsimple q (by simp [hq])
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, bind, Option.bind,
      pure, Pure.pure, hcast, htail]
  | _ :: _, [], _, hmap, _, _, _ => by simp at hmap
  | [], _ :: _, _, hmap, _, _, _ => by simp at hmap
  | _ :: _, _ :: _, [], _, hlen, _, _ => by simp at hlen

theorem coerceCallArgs_of_argsWellTyped {m : Mem} {ptys cParamTys : List CTy} {args : List Val}
    (hmap : ptys.map CTy.unqual = cParamTys.map CTy.unqual)
    (hawt : Zlib.Spec.ArgsWellTyped cParamTys false args)
    (htys : ∀ p ∈ ptys, match p.unqual with
      | .void | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ | .vaList => True
      | _ => False) :
    Sem.coerceCallArgs m ptys false (args.map (fun v => (v, .void))) = some args := by
  rcases hawt with ⟨hlen, hval⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hlen
  have hplen : ptys.length = cParamTys.length := by
    have := congrArg List.length hmap
    simp at this
    exact this
  unfold Sem.coerceCallArgs
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind, List.length_map,
    hlen, hplen, beq_self_eq_true, guard, pure, Pure.pure]
  exact mapM_castVal_of_list hmap hlen hval htys

private theorem mapM_castVal_produces_valHasCTy {m : Mem} :
    ∀ {ptys : List CTy} {argVals : List (Val × CTy)} {coerced : List Val},
      ptys.length = argVals.length →
      List.mapM (fun (x : CTy × (Val × CTy)) => Sem.castVal m x.1 x.2.1)
        (ptys.zip argVals) = some coerced →
      ∀ i (hi : i < ptys.length),
        match coerced[i]? with
        | some v => Zlib.Spec.ValHasCTy ptys[i] v
        | none => False
  | [], [], [], _, _, i, hi => by simp at hi
  | p :: ps, (v, _) :: rest, c :: cs, hlen, hmap, i, hi => by
    simp only [List.zip_cons_cons, List.mapM_cons, bind, Option.bind, pure, Pure.pure] at hmap
    cases hc : Sem.castVal m p v with
    | none => simp [hc] at hmap
    | some cv =>
      simp only [hc] at hmap
      cases hm : List.mapM (fun (x : CTy × (Val × CTy)) => Sem.castVal m x.1 x.2.1) (ps.zip rest) with
      | none => simp [hm] at hmap
      | some crest =>
        simp only [hm, Option.some.injEq, List.cons.injEq] at hmap
        rcases hmap with ⟨rfl, rfl⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, List.getElem_cons_zero]
          exact castVal_produces_valHasCTy hc
        | succ j =>
          simp only [List.getElem?_cons_succ, List.getElem_cons_succ]
          exact mapM_castVal_produces_valHasCTy (by simp at hlen; exact hlen) hm j (by simp at hi; omega)
  | _ :: _, (_ :: _), [], hlen, hmap, _, _ => by
    have := mapM_option_length hmap
    rw [List.length_zip, hlen, Nat.min_self] at this
    simp at this
  | _ :: _, [], _, hlen, _, _, _ => by simp at hlen
  | [], _ :: _, _, hlen, _, _, _ => by simp at hlen

theorem coerceCallArgs_produces_argsWellTyped {m : Mem} {ptys : List CTy}
    {argVals : List (Val × CTy)} {coerced : List Val}
    (hc : Sem.coerceCallArgs m ptys false argVals = some coerced) :
    Zlib.Spec.ArgsWellTyped ptys false coerced := by
  have ⟨hlenC, hlenA⟩ := coerceCallArgs_length hc
  unfold Sem.coerceCallArgs at hc
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind, hlenA, beq_self_eq_true,
    guard, pure, Pure.pure] at hc
  refine ⟨by simp [hlenC], mapM_castVal_produces_valHasCTy hlenA.symm hc⟩

private theorem sizeofTy_pos_lt_of_simple (tags : TypeEnv) {ty : CTy}
    (hs : IsSimpleParamTy ty) :
    max 1 (C99.sizeofTy tags ty) < C99.ptrDiffLimit ∧ 0 < max 1 (C99.alignofTy tags ty) := by
  rw [← sizeofTy_unqual, ← alignofTy_unqual]
  rcases isSimpleParamTy_iff.mp hs with ⟨k, hk⟩ | ⟨el, hel⟩
  · rw [hk, sizeofTy_int, alignofTy_int]
    cases k <;> decide
  · rw [hel, sizeofTy_ptr, alignofTy_ptr]
    decide

private theorem pushCallParams_idx0 (tags : TypeEnv) :
    ∀ (idx : Nat) (l : List (Param × Val)) (e : Env) (b : List BlockId) (mm : Mem),
      Sem.pushCallParams tags mm (fun _ => 0) idx l e b =
      Sem.pushCallParams tags mm (fun _ => 0) 0 l e b
  | _, [], _, _, _ => rfl
  | idx, hd :: tl, e, b, mm => by
    unfold Sem.pushCallParams
    dsimp only
    split
    · split
      · split
        · exact congrArg (Option.bind _) (funext fun m2 => by
            rw [pushCallParams_idx0 tags (idx + 1) tl _ _ m2, pushCallParams_idx0 tags (0 + 1) tl _ _ m2])
        · rfl
      · rfl
    · rfl

private theorem pushCallParams_exists_go (tags : TypeEnv) :
    ∀ (ps : List Param) (vs : List Val) (m : Mem) (env : Env) (blks : List BlockId),
      vs.length = ps.length →
      (∀ p ∈ ps, IsSimpleParamTy p.ty) →
      (∀ i (hi : i < ps.length), match vs[i]? with | some v => Zlib.Spec.ValHasCTy ps[i].ty v | none => False) →
      ∃ callEnv callBlks m',
        Sem.pushCallParams tags m (fun _ => 0) 0 (ps.zip vs) env blks = some (callEnv, callBlks, m')
  | [], [], m, env, blks, _, _, _ => ⟨env, blks, m, rfl⟩
  | p :: ps, v :: vs, m, env, blks, hlen, hsimp, hval => by
    have hsp := hsimp p (by simp)
    have ⟨hsz, hal⟩ := sizeofTy_pos_lt_of_simple tags hsp
    have hba : ((0 : UInt64).toNat) % max 1 (C99.alignofTy tags p.ty) = 0 := by
      simp
    have hv0 := hval 0 (by simp)
    simp only [List.getElem?_cons_zero, List.getElem_cons_zero] at hv0
    have hwr : ∃ m2, Sem.writeVal
        (m.alloc (max 1 (C99.sizeofTy tags p.ty)) (max 1 (C99.alignofTy tags p.ty))
          .rw .stack 0 (fun _ => .undef) hsz hal hba).snd
        m.nextBlock 0 p.ty.stripConst v = some m2 := by
      rcases isSimpleParamTy_iff.mp hsp with ⟨k, hk⟩ | ⟨el, hel⟩
      · rw [valHasCTy_unqual, hk] at hv0
        unfold Zlib.Spec.ValHasCTy at hv0
        simp [CTy.unqual] at hv0
        rcases hv0 with ⟨bv, rfl⟩
        exact writeVal_fresh_int hk hsz hal hba (by rfl)
      · rw [valHasCTy_unqual, hel] at hv0
        unfold Zlib.Spec.ValHasCTy at hv0
        simp [CTy.unqual] at hv0
        exact writeVal_fresh_ptr hel hsz hal hba hv0
    rcases hwr with ⟨m2, hm2⟩
    have hstep := pushCallParams_cons (tags := tags) (base := fun _ => 0) (idx := 0)
      (p := p) (v := v) (rest := ps.zip vs) (env := env) (blks := blks) hsz hal hba hm2
    have ⟨ce, cb, m', hrest⟩ := pushCallParams_exists_go tags ps vs m2
      ((p.name, m.nextBlock, p.ty) :: env) (m.nextBlock :: blks)
      (by simp at hlen; exact hlen)
      (fun q hq => hsimp q (by simp [hq]))
      (fun i hi => by
        have h := hval (i + 1) (by simp; omega)
        simp only [List.getElem?_cons_succ, List.getElem_cons_succ] at h
        exact h)
    refine ⟨ce, cb, m', ?_⟩
    simpa [List.zip_cons_cons, hstep, pushCallParams_idx0] using hrest
  | _ :: _, [], _, _, _, hlen, _, _ => by simp at hlen
  | [], _ :: _, _, _, _, hlen, _, _ => by simp at hlen

theorem pushCallParams_exists_base0 (tags : TypeEnv) {fn : FnDef} {args : List Val}
    {m : Mem} {env : Env}
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hawt : Zlib.Spec.ArgsWellTyped (fn.params.map (·.ty)) false args) :
    ∃ callEnv callBlks m',
      Sem.pushCallParams tags m (fun _ => 0) 0 (fn.params.zip args) env [] = some (callEnv, callBlks, m') := by
  rcases hawt with ⟨hlen, hval⟩
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_map] at hlen
  exact pushCallParams_exists_go tags fn.params args m env [] hlen hsimp (by
    intro i hi
    have h := hval i (by simp [hi])
    cases hget : args[i]? with
    | none => simp [hget] at h
    | some v => simp [hget] at h ⊢; exact h)

/-! ## 4. Reusable Function Body Specs & `ContractSafe` Bridges -/

/-- Function-body WP specification over coerced argument values `args`.
Allows proving a function once and using it both at internal call sites (`FuncBodySpec.call`)
and at public contract boundaries (`FuncBodySpec.to_contractSafe`). -/
def FuncBodySpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
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
    (∀ ret m', ROExt m m' → Post m args ret m' →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os k)) →
    WPTerm prog cfg ext Q
      (.running (.stmt fn.body) callEnv callBlks m1 os
        (.callFrame env blks fn.retTy fn.body fs ctx k))

theorem FuncBodySpec.call
    {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (hspec : FuncBodySpec prog cfg ext fn Pre Post)
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
    (hcont : ∀ ret m', ROExt m m' → Post m coerced ret m' →
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

private theorem args_map_void_reverse (args : List Val) :
    match args.reverse with
    | [] => args = []
    | last :: revInit => revInit.reverse.map (fun v => (v, CTy.void)) ++ [(last, CTy.void)] =
        args.map (fun v => (v, CTy.void)) := by
  split
  · rename_i hr
    have := congrArg List.reverse hr
    simpa using this
  · rename_i last revInit hr
    have hrev : args = revInit.reverse ++ [last] := by
      have := congrArg List.reverse hr
      simpa using this
    rw [hrev, List.map_append, List.map_singleton]

private theorem map_unqual_length {a b : List CTy}
    (h : a.map CTy.unqual = b.map CTy.unqual) : a.length = b.length := by
  have := congrArg List.length h
  simpa using this

private theorem simple_is_cast_ok {ty : CTy} (h : IsSimpleParamTy ty) :
    match ty.unqual with
    | .void | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ | .vaList => True
    | _ => False := by
  rcases isSimpleParamTy_iff.mp h with ⟨k, hk⟩ | ⟨el, hel⟩
  · simp [hk]
  · simp [hel]

theorem FuncBodySpec.to_contractSafe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    {c : FnContract Zlib.Spec.ClientView} {fn : FnDef}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os)
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hnonvar : c.variadic = false ∧ fn.variadic = false)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, false))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hbody : FuncBodySpec prog zlibPointerConfig ext fn Pre Post)
    (hpreImp : ∀ v owned m os args,
      BaseInv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped c.paramTys false args →
      Pre m args)
    (hpostImp : ∀ v owned m args ret m',
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped c.paramTys false args →
      ROExt m m' →
      Post m args ret m' →
      (if protoRetTy.isVoid = true then
        c.post prog.tags owned v m args .void m' v
      else
        ∃ cv, Sem.castVal m' protoRetTy ret = some cv ∧
          c.post prog.tags owned v m args cv m' v)) :
    Zlib.Spec.ContractSafe prog gEnv ext Inv userWrite c := by
  intro v owned m os args s0 hInv hpre hawt hcs
  have hawt' : Zlib.Spec.ArgsWellTyped c.paramTys false args := by
    simpa [hnonvar.1] using hawt
  have hb : BaseInv m0 os0 v owned m os := hInvBase v owned m os hInv
  have hPre : Pre m args := hpreImp v owned m os args hb hpre hawt'
  have hmapTy : (fn.params.map (·.ty)).map CTy.unqual = c.paramTys.map CTy.unqual := by
    simpa [List.map_map, Function.comp_def] using hptys
  have hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false
      (args.map (fun x => (x, .void))) = some args :=
    coerceCallArgs_of_argsWellTyped hmapTy hawt' (fun p hp => by
      simp only [List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      exact simple_is_cast_ok (hsimple q hq))
  let Q : Val → Mem → OSState → Prop := fun retFinal mFinal osFinal =>
    osFinal = os ∧ ROExt m mFinal ∧ c.post prog.tags owned v m args retFinal mFinal v
  have hretStop : ∀ ret m', ROExt m m' → Post m args ret m' →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) []) .returnVal [])
          gEnv [] m' os (.stop protoRetTy)) := by
    intro ret m' hro hpost
    have hp := hpostImp v owned m args ret m' hpre hawt' hro hpost
    by_cases hvoid : protoRetTy.isVoid = true
    · rw [hvoid] at hp
      simp only [ite_true] at hp
      refine WPTerm.of_det (s' := .returned .void m' os) ?_ (WPTerm.returned ⟨rfl, hro, hp⟩)
      unfold Sem.stepDet Sem.unwindReturn Sem.Cont.topRetTy
      simp [hvoid, freeStack_nil]
    · have hfvoid : protoRetTy.isVoid = false := by
        cases h : protoRetTy.isVoid
        · rfl
        · exact False.elim (hvoid h)
      rw [hfvoid] at hp
      simp only [Bool.false_eq_true, ite_false] at hp
      rcases hp with ⟨cv, hcast, hcpost⟩
      refine WPTerm.of_det (s' := .returned cv m' os) ?_ (WPTerm.returned ⟨rfl, hro, hcpost⟩)
      unfold Sem.stepDet Sem.unwindReturn Sem.Cont.topRetTy
      simp [hvoid, hcast, freeStack_nil]
  have hstepCall : ∃ fnTy argVals,
      Sem.stepDet prog zlibPointerConfig s0 =
        some (.callFn c.fnName fnTy argVals [] .returnVal gEnv [] m os (.stop protoRetTy)) ∧
      argVals = args.map (fun x => (x, CTy.void)) := by
    unfold Zlib.Spec.callState at hcs
    simp only [hproto, bind, Option.bind, pure, Pure.pure] at hcs
    have hm := args_map_void_reverse args
    revert hcs hm
    cases args.reverse with
    | nil =>
      intro hcs heq
      cases hcs
      refine ⟨protoRetTy.fnPtr protoParamTys false, [], ?_, by simp [heq]⟩
      unfold Sem.stepDet
      rfl
    | cons last revInit =>
      intro hcs heq
      cases hcs
      refine ⟨protoRetTy.fnPtr protoParamTys false,
        revInit.reverse.map (fun x => (x, CTy.void)) ++ [(last, CTy.void)], ?_, heq⟩
      unfold Sem.stepDet
      simp only []
  rcases hstepCall with ⟨fnTy, argVals, hstep, hargVals⟩
  rw [hargVals] at hstep
  have hwp : WPTerm prog zlibPointerConfig ext Q s0 :=
    FuncBodySpec.call hbody hstep hfn hname hnonvar.2 hcoerce hPre hsimple hretStop
  refine ⟨WPTerm.safe hwp, fun _ => WPTerm.terminatesSafely hwp, ?_⟩
  intro retFinal mFinal osFinal hstar
  rcases WPTerm.post hwp hstar with ⟨hos, hro, hcpost⟩
  have hInvF : Inv v owned mFinal osFinal := by
    rw [hos]
    exact hInvRO v owned m mFinal os hInv hro
  exact ⟨owned, v, hcpost, hInvF,
    roExt_framePreserved hro _, roExt_noHeapLeak hro _,
    fun hv => (hInvBase v owned mFinal osFinal hInvF).emptyNoOwned hv⟩

end Zlib.Proof
