import C99.Proof.VCGen
import Zlib.Proof.ProgLookupAll
import Zlib.Proof.Invariant
import Zlib.Proof.Zutil
import Zlib.Proof.ZutilAlloc
import Zlib.Proof.CompressBound
import Zlib.Proof.Adler32
import Zlib.Proof.Crc32

/-!
# Bridge Between Functional CPS VCGen (`C99.Proof.VCGen`) and `Zlib.Proof.Invariant` v2

Connects:
1. Memory, frame, buffer, ABI typing, `StructCell`/`HasField` layout predicates, and
   `writeVal` / `StructCell.writeField_some` range preservation between
   `C99.Proof.VCGen`, `Zlib.Spec`, and `Zlib.Proof.Invariant` v2.
2. Bidirectional function specification adapters:
   - Forward: `vcFn` / `vcFnSafeSplit` / `vcFnSafe` → `Zlib.Proof.CallWPTermSpec`,
     `Zlib.Proof.CallSafeSpec`, and `Zlib.Spec.ContractSafe`.
   - Reverse: `Zlib.Proof.CallWPTermSpec`, `Zlib.Proof.FuncBodySpec`,
     `Zlib.Proof.HeapBodySpec` → `C99.Proof.VCGen.CallSpec`, and unconditional
     `Zlib.Proof.CallSafeSpec` → `C99.Proof.VCGen.CallSafeSpec`.
3. `SpecEnv` / `SafeSpecEnv` composition combinators (`empty*`, `insert*`) with `@[simp]` lemmas.
4. Ready-to-use VCGen callee wrappers for Wave 1 functions (`zcalloc`, `zcfree`,
   `zError`, `zlibCompileFlags`, `compressBound_z`, `compressBound`, `adler32_combine_`,
   `adler32_z`, `adler32`, `crc32_z`, `crc32`) and indirect `SafeUserCallbacks`
   (`in_func`, `out_func`) callbacks.
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof C99.Proof.VCGen Zlib.Spec

/-! ## 1. Memory, Frame, & Layout Bridges -/

theorem MemUnchanged.to_memBlocksUnchanged {m m' : Mem}
    (h : C99.Proof.VCGen.MemUnchanged m m') : MemBlocksUnchanged m m' := h

theorem MemBlocksUnchanged.to_memUnchanged {m m' : Mem}
    (h : MemBlocksUnchanged m m') : C99.Proof.VCGen.MemUnchanged m m' := h

theorem memUnchanged_iff_memBlocksUnchanged {m m' : Mem} :
    C99.Proof.VCGen.MemUnchanged m m' ↔ MemBlocksUnchanged m m' := Iff.rfl

theorem memUnchanged_to_preservesBlockMeta {m m' : Mem}
    (h : C99.Proof.VCGen.MemUnchanged m m') (b : BlockId) :
    PreservesBlockMeta m m' b := by
  intro blk hb
  exact ⟨blk, by rw [h.2 b]; exact hb, rfl, rfl, rfl, rfl, rfl⟩

theorem memUnchanged_to_preservesOutsideRange {m m' : Mem}
    (h : C99.Proof.VCGen.MemUnchanged m m') (b : BlockId) (off : Int64) (len : Nat) :
    PreservesOutsideRange m m' b off len := by
  refine ⟨memUnchanged_to_preservesBlockMeta h b, fun blk hb => ?_⟩
  exact ⟨blk, by rw [h.2 b]; exact hb, fun _ _ => rfl⟩

theorem roExt_of_memUnchanged {m m' : Mem}
    (h : C99.Proof.VCGen.MemUnchanged m m') : C99.Proof.ROExt m m' :=
  h.roExt

theorem framePreserved_of_memUnchanged {m m' : Mem} {allowed : BlockSet}
    (h : C99.Proof.VCGen.MemUnchanged m m') : Zlib.Spec.FramePreserved m m' allowed := by
  refine ⟨fun b _ _ => h.2 b, fun b blk hnone hsome _ => ?_⟩
  rw [h.2 b, hnone] at hsome
  cases hsome

theorem noHeapLeak_of_blocks_eq {m m' : Mem} {owned' : BlockSet}
    (h : ∀ b, m'.blocks b = m.blocks b) : Zlib.Spec.NoHeapLeak m m' owned' := by
  intro b blk hsome _
  left
  rw [h b] at hsome
  simp [hsome]

theorem noHeapLeak_of_blocks_eq_allowed {m m' : Mem} {allowed : BlockSet}
    (h : ∀ b, ¬ allowed b → m'.blocks b = m.blocks b)
    (hall_existing : ∀ b, allowed b → (m.blocks b).isSome) {owned' : BlockSet} :
    Zlib.Spec.NoHeapLeak m m' owned' := by
  intro b blk hsome _
  left
  by_cases ha : allowed b
  · exact hall_existing b ha
  · rw [h b ha] at hsome
    simp [hsome]

theorem writeBytes_preservesBlockMeta {m m' : Mem} {b : BlockId} {off : Int64}
    {bs : List MemByte} {blk : Block}
    (hb : m.blocks b = some blk) (hw : m.writeBytes b off bs = some m') (b' : BlockId) :
    PreservesBlockMeta m m' b' := by
  intro blk' hblk'
  by_cases hbb : b' = b
  · subst hbb
    rw [hb, Option.some.injEq] at hblk'
    subst blk'
    exact ⟨_, writeBytes_blocks_eq hb hw, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨blk', ?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [writeBytes_blocks_ne hw hbb]
    exact hblk'

theorem writeBytes_preservesOutsideRange_ne {m m' : Mem} {b b' : BlockId}
    {off : Int64} {bs : List MemByte}
    (hw : m.writeBytes b off bs = some m') (hne : b' ≠ b) (off' : Int64) (len' : Nat) :
    PreservesOutsideRange m m' b' off' len' := by
  refine ⟨?_, ?_⟩
  · intro blk' hblk'
    exact ⟨blk', by rw [writeBytes_blocks_ne hw hne]; exact hblk', rfl, rfl, rfl, rfl, rfl⟩
  · intro blk' hblk'
    exact ⟨blk', by rw [writeBytes_blocks_ne hw hne]; exact hblk', fun _ _ => rfl⟩

theorem writeBytes_preservesOutsideRange {m m' : Mem} {b : BlockId}
    {off : Int64} {bs : List MemByte} {blk : Block}
    (hb : m.blocks b = some blk) (hw : m.writeBytes b off bs = some m')
    (b' : BlockId) (off' : Int64) (len' : Nat)
    (hsub : b' = b → 0 ≤ off.toInt ∧ off'.toInt ≤ off.toInt ∧
      off.toInt + bs.length ≤ off'.toInt + len') :
    PreservesOutsideRange m m' b' off' len' := by
  by_cases hbb : b' = b
  · subst hbb
    obtain ⟨_, hlo, hhi⟩ := hsub rfl
    refine ⟨writeBytes_preservesBlockMeta hb hw b', fun blk' hblk' => ?_⟩
    rw [hb, Option.some.injEq] at hblk'
    subst blk'
    refine ⟨_, writeBytes_blocks_eq hb hw, fun i hi => ?_⟩
    dsimp only
    split
    · rename_i hrng
      have : False := by rcases hi with hlt | hge <;> omega
      exact False.elim this
    · rfl
  · exact writeBytes_preservesOutsideRange_ne hw hbb off' len'

private theorem writeVal_exists_writeBytes {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (hw : Sem.writeVal m b off ty v = some m') :
    ∃ blk bs, m.blocks b = some blk ∧ m.writeBytes b off bs = some m' := by
  unfold Sem.writeVal at hw
  dsimp only [guard, pure, failure, bind, Option.bind] at hw
  by_cases hnc : ty.isConst = true
  · simp [hnc] at hw
  · simp only [hnc, Bool.not_false, ↓reduceIte] at hw
    cases hb : m.blocks b with
    | none => simp [hb] at hw
    | some blk =>
      simp only [hb] at hw
      cases hu : ty.unqual with
      | «int» k =>
        simp only [hu, CTy.intKind?, CTy.unqual] at hw
        by_cases hal : Mem.isAligned blk off k.align = true
        · simp only [hal, ↓reduceIte] at hw
          cases hvi : Sem.valAsInt? v with
          | none => simp [hvi] at hw
          | some p => simp only [hvi] at hw; exact ⟨blk, _, rfl, hw⟩
        · simp [hal] at hw
      | enumTy tag isU =>
        simp only [hu, CTy.intKind?, CTy.unqual] at hw
        by_cases hal : Mem.isAligned blk off (if isU = true then IntKind.u32 else IntKind.i32).align = true
        · simp only [hal, ↓reduceIte] at hw
          cases hvi : Sem.valAsInt? v with
          | none => simp [hvi] at hw
          | some p => simp only [hvi] at hw; exact ⟨blk, _, rfl, hw⟩
        · simp [hal] at hw
      | ptr _ =>
        simp only [hu] at hw
        by_cases hal : Mem.isAligned blk off 8 = true
        · simp only [hal, ↓reduceIte] at hw
          cases v with
          | null => exact ⟨blk, _, rfl, hw⟩
          | ptr pb po => exact ⟨blk, _, rfl, hw⟩
          | «int» k bv =>
            by_cases hz : (bv.toNat == 0) = true
            · simp only [hz, ↓reduceIte] at hw; exact ⟨blk, _, rfl, hw⟩
            · simp [hz] at hw
          | _ => cases hw
        · simp [hal] at hw
      | fnPtr _ _ _ =>
        simp only [hu] at hw
        by_cases hal : Mem.isAligned blk off 8 = true
        · simp only [hal, ↓reduceIte] at hw
          cases v with
          | null => exact ⟨blk, _, rfl, hw⟩
          | fnPtr s => exact ⟨blk, _, rfl, hw⟩
          | «int» k bv =>
            by_cases hz : (bv.toNat == 0) = true
            · simp only [hz, ↓reduceIte] at hw; exact ⟨blk, _, rfl, hw⟩
            · simp [hz] at hw
          | _ => cases hw
        · simp [hal] at hw
      | vaList =>
        simp only [hu] at hw
        cases v with
        | vaList valid =>
          cases valid
          · cases hw
          · exact ⟨blk, _, rfl, hw⟩
        | _ => cases hw
      | _ => simp only [hu] at hw; cases hw

theorem writeVal_scalar_preservesBlockMeta {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val}
    (hw : Sem.writeVal m b off ty v = some m') (b' : BlockId) :
    PreservesBlockMeta m m' b' := by
  obtain ⟨blk, bs, hb, hwb⟩ := writeVal_exists_writeBytes hw
  exact writeBytes_preservesBlockMeta hb hwb b'

theorem readable_iff_bufSlice {m : Mem} {p : Val} {len : Nat} :
    Zlib.Spec.Readable m p len ↔ ∃ b off, p = .ptr b off ∧ C99.Proof.VCGen.BufSlice m b off len := by
  constructor
  · rintro ⟨b, off, blk, rfl, hblk, hin, hconcr⟩
    exact ⟨b, off, rfl, blk, hblk, hin, hconcr⟩
  · rintro ⟨b, off, rfl, blk, hblk, hin, hconcr⟩
    exact ⟨b, off, blk, rfl, hblk, hin, hconcr⟩

theorem writable_iff_bufSlice_rw {m : Mem} {p : Val} {len : Nat} :
    Zlib.Spec.Writable m p len ↔
      ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ blk.perm = .rw ∧
        Mem.inBounds blk off len = true := by
  constructor
  · rintro ⟨b, off, blk, rfl, hblk, hperm, hin⟩
    exact ⟨b, off, blk, rfl, hblk, hperm, hin⟩
  · rintro ⟨b, off, blk, rfl, hblk, hperm, hin⟩
    exact ⟨b, off, blk, rfl, hblk, hperm, hin⟩

theorem isScalarPlaceTy_of_isSimpleParamTy {ty : CTy} (h : IsSimpleParamTy ty) :
    C99.Proof.VCGen.isScalarPlaceTy ty = true := by
  unfold IsSimpleParamTy at h
  unfold C99.Proof.VCGen.isScalarPlaceTy
  cases hu : ty.unqual <;> simp only [hu] at h ⊢ <;> first | rfl | cases h

private theorem valHasCTy_to_valScalarTyped {ty : CTy} {v : Val}
    (hsc : C99.Proof.VCGen.isScalarPlaceTy ty = true) (h : Zlib.Spec.ValHasCTy ty v) :
    C99.Proof.VCGen.ValScalarTyped ty v := by
  unfold Zlib.Spec.ValHasCTy at h
  unfold C99.Proof.VCGen.ValScalarTyped
  unfold C99.Proof.VCGen.isScalarPlaceTy at hsc
  cases hu : ty.unqual <;> simp only [hu] at h hsc ⊢ <;> first | exact h | cases hsc

theorem argsWellTyped_of_params_scalar {prog : Prog} {params : List Param} {args : List Val}
    (hsc : ∀ p ∈ params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hvt : Zlib.Spec.ArgsWellTyped prog (params.map (·.ty)) false args) :
    args.length = params.length ∧
      ∀ pv ∈ params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2 := by
  rcases hvt with ⟨hlen, hidx, _⟩
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_map] at hlen hidx
  refine ⟨hlen, ?_⟩
  have hrec : ∀ (ps : List Param) (vs : List Val),
      ps.length = vs.length →
      (∀ p ∈ ps, C99.Proof.VCGen.isScalarPlaceTy p.ty = true) →
      (∀ i (_ : i < ps.length), ∃ v, vs[i]? = some v ∧ Zlib.Spec.ValHasCTy ps[i].ty v) →
      ∀ pv ∈ ps.zip vs, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2 := by
    intro ps
    induction ps with
    | nil => intro vs _ _ _ pv hpv; cases hpv
    | cons p pt ih =>
      intro vs hl hs hi pv hpv
      cases vs with
      | nil => cases hl
      | cons v vt =>
        obtain ⟨v0, hv0, h0⟩ := hi 0 (Nat.zero_lt_succ _)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv0
        subst hv0
        have hp_typed := valHasCTy_to_valScalarTyped (hs p (.head _)) h0
        rcases List.mem_cons.mp hpv with rfl | htail
        · exact hp_typed
        · refine ih vt (by simpa using hl) (fun q hq => hs q (.tail _ hq)) ?_ pv htail
          intro i hii
          obtain ⟨vi, hvi, hci⟩ := hi (i + 1) (Nat.succ_lt_succ hii)
          exact ⟨vi, by simpa using hvi, by simpa using hci⟩
  refine hrec params args hlen.symm hsc (fun i hi => ?_)
  have hmi := hidx i (by simpa using hi)
  cases hget : args[i]? with
  | none => simp [hget] at hmi
  | some v => exact ⟨v, rfl, by simpa [hget, List.getElem_map] using hmi⟩

theorem argsWellTyped_take_of_params_scalar {prog : Prog} {params : List Param} {args : List Val}
    (hsc : ∀ p ∈ params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hvt : Zlib.Spec.ArgsWellTyped prog (params.map (·.ty)) true args) :
    params.length ≤ args.length ∧
      ∀ pv ∈ params.zip (args.take params.length), C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2 := by
  rcases hvt with ⟨hlen, hidx, _⟩
  simp only [↓reduceIte, List.length_map] at hlen hidx
  refine ⟨hlen, ?_⟩
  have htake_len : (args.take params.length).length = params.length := by
    simp [List.length_take, Nat.min_eq_left hlen]
  have hrec : ∀ (ps : List Param) (vs : List Val),
      ps.length = vs.length →
      (∀ p ∈ ps, C99.Proof.VCGen.isScalarPlaceTy p.ty = true) →
      (∀ i (_ : i < ps.length), ∃ v, vs[i]? = some v ∧ Zlib.Spec.ValHasCTy ps[i].ty v) →
      ∀ pv ∈ ps.zip vs, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2 := by
    intro ps
    induction ps with
    | nil => intro vs _ _ _ pv hpv; cases hpv
    | cons p pt ih =>
      intro vs hl hs hi pv hpv
      cases vs with
      | nil => cases hl
      | cons v vt =>
        obtain ⟨v0, hv0, h0⟩ := hi 0 (Nat.zero_lt_succ _)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv0
        subst hv0
        have hp_typed := valHasCTy_to_valScalarTyped (hs p (.head _)) h0
        rcases List.mem_cons.mp hpv with rfl | htail
        · exact hp_typed
        · refine ih vt (by simpa using hl) (fun q hq => hs q (.tail _ hq)) ?_ pv htail
          intro i hii
          obtain ⟨vi, hvi, hci⟩ := hi (i + 1) (Nat.succ_lt_succ hii)
          exact ⟨vi, by simpa using hvi, by simpa using hci⟩
  refine hrec params (args.take params.length) htake_len.symm hsc (fun i hi => ?_)
  have hmi := hidx i (by simpa using hi)
  rw [List.getElem?_take_of_lt hi]
  cases hget : args[i]? with
  | none => simp [hget] at hmi
  | some v => exact ⟨v, rfl, by simpa [hget, List.getElem_map] using hmi⟩

theorem size_lt_scalar (tags : TypeEnv) (ty : CTy) (v : Val)
    (ht : C99.Proof.VCGen.ValScalarTyped ty v) :
    max 1 (sizeofTy tags ty) < ptrDiffLimit :=
  ht.size_lt_ptrDiffLimit

theorem align_pos_scalar (tags : TypeEnv) (ty : CTy) (v : Val)
    (ht : C99.Proof.VCGen.ValScalarTyped ty v) :
    0 < max 1 (alignofTy tags ty) :=
  ht.align_pos

theorem i64_toInt_ofInt {x : Int} (h : IntKind.i64.inRange x = true) :
    (BitVec.ofInt IntKind.i64.bits x).toInt = x := by
  simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.bits, IntKind.signed,
    ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
  change (BitVec.ofInt 64 x).toInt = x
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem structCell_blk {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st : String} {rq : Bool} (h : C99.Proof.VCGen.StructCell tags m b off st rq) :
    ∃ blk, m.blocks b = some blk :=
  let ⟨blk, hblk, _⟩ := h; ⟨blk, hblk⟩

theorem hasField_elim {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {v : Val} {foff : Nat} {fty : CTy}
    (hf : C99.Proof.VCGen.HasField tags m b off structTag fld v)
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty)) :
    Sem.readVal tags m b (Int64.ofInt (off.toInt + ↑foff)) fty = some v := by
  rcases hf with ⟨foff', fty', hfl', hrd⟩
  rw [hfl] at hfl'
  cases hfl'
  exact hrd

theorem structCell_weaken_rw {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64} {st : String}
    (h : C99.Proof.VCGen.StructCell tags m b off st true) :
    C99.Proof.VCGen.StructCell tags m b off st false :=
  let ⟨blk, hblk, _, hi, ha⟩ := h; ⟨blk, hblk, (fun hf => by cases hf), hi, ha⟩

theorem structCell_of_mono {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {st : String} {rq : Bool}
    (hs : C99.Proof.VCGen.StructCell tags m1 b off st rq)
    (hm : ∀ b' blk, m1.blocks b' = some blk → m2.blocks b' = some blk) :
    C99.Proof.VCGen.StructCell tags m2 b off st rq :=
  let ⟨blk, hblk, _⟩ := hs
  StructCell.of_blocks_eq hs ((hm b blk hblk).trans hblk.symm)

theorem hasField_of_mono {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {v : Val}
    (hs : ∃ rq, C99.Proof.VCGen.StructCell tags m1 b off st rq)
    (hf : C99.Proof.VCGen.HasField tags m1 b off st fld v)
    (hm : ∀ b' blk, m1.blocks b' = some blk → m2.blocks b' = some blk) :
    C99.Proof.VCGen.HasField tags m2 b off st fld v := by
  obtain ⟨_, hcell⟩ := hs
  obtain ⟨blk, hblk, _⟩ := hcell
  exact HasField.of_blocks_eq hf ((hm b blk hblk).trans hblk.symm)

theorem StructCell.of_typedCell {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64} {st : String}
    (ht : Zlib.Spec.TypedCell tags m (.ptr b off) (.structTy st)) :
    C99.Proof.VCGen.StructCell tags m b off st true := by
  rcases ht with ⟨b', off', blk, hpeq, hblk, hperm, hin, hal⟩
  cases hpeq
  exact ⟨blk, hblk, fun _ => hperm, hin, hal⟩

theorem structCell_rw_iff_typedCell {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64} {st : String} :
    C99.Proof.VCGen.StructCell tags m b off st true ↔
      Zlib.Spec.TypedCell tags m (.ptr b off) (.structTy st) := by
  constructor
  · rintro ⟨blk, hblk, hperm, hin, hal⟩
    exact ⟨b, off, blk, rfl, hblk, hperm rfl, hin, hal⟩
  · exact StructCell.of_typedCell

theorem HasField.of_readField? {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {v : Val}
    (hr : Zlib.Spec.readField? tags m (.ptr b off) st fld = some v) :
    C99.Proof.VCGen.HasField tags m b off st fld v := by
  unfold Zlib.Spec.readField? at hr
  cases hfl : fieldLayout? tags (.structTy st) fld with
  | none => simp [hfl, Option.bind] at hr
  | some p =>
    simp only [hfl, bind, Option.bind] at hr
    exact ⟨p.1, p.2, hfl, hr⟩

theorem HasField.to_readField? {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {v : Val}
    (hf : C99.Proof.VCGen.HasField tags m b off st fld v) :
    Zlib.Spec.readField? tags m (.ptr b off) st fld = some v := by
  rcases hf with ⟨foff, fty, hfl, hrd⟩
  unfold Zlib.Spec.readField?
  simp only [hfl, bind, Option.bind]
  exact hrd

theorem readField?_iff_hasField {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {v : Val} :
    Zlib.Spec.readField? tags m (.ptr b off) st fld = some v ↔
      C99.Proof.VCGen.HasField tags m b off st fld v :=
  ⟨HasField.of_readField?, HasField.to_readField?⟩

theorem HasField.to_readNatField? {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {k : IntKind} {bv : BitVec k.bits}
    (hnn : k.signed = false ∨ 0 ≤ bv.toInt)
    (hf : C99.Proof.VCGen.HasField tags m b off st fld (.int k bv)) :
    Zlib.Spec.readNatField? tags m (.ptr b off) st fld = some bv.toNat := by
  unfold Zlib.Spec.readNatField?
  rw [HasField.to_readField? hf]
  dsimp only [bind, Option.bind]
  rcases hnn with hs | hle
  · simp [hs]
  · by_cases hs : (!k.signed) = true
    · simp [hs]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, hle]
      have hlt : 2 * bv.toNat < 2 ^ k.bits := by
        by_cases hlt : 2 * bv.toNat < 2 ^ k.bits
        · exact hlt
        · exfalso
          have hlt2 : (bv.toNat : Int) < ↑(2 ^ k.bits) := Int.ofNat_lt.mpr bv.isLt
          have hneg : bv.toInt < 0 := by
            rw [BitVec.toInt_eq_toNat_cond]
            simp [hlt]
            omega
          omega
      have hto : bv.toInt = (bv.toNat : Int) := by
        rw [BitVec.toInt_eq_toNat_cond]
        simp [hlt]
      rw [hto, Int.toNat_natCast]

theorem HasField.to_readIntField? {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {k : IntKind} {bv : BitVec k.bits}
    (hf : C99.Proof.VCGen.HasField tags m b off st fld (.int k bv)) :
    readIntField? tags m (.ptr b off) st fld = some bv.toInt := by
  unfold readIntField?
  rw [HasField.to_readField? hf]
  rfl

theorem StructCell.writeField_some_preserves {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {structTag fld : String} {foff : Nat} {fty : CTy} {v : Val}
    (hc : C99.Proof.VCGen.StructCell tags m b off structTag true)
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hnc : fty.isConst = false)
    (hle : foff + sizeofTy tags fty ≤ sizeofTy tags (.structTy structTag))
    (hal1 : alignofTy tags fty ∣ alignofTy tags (.structTy structTag))
    (hal2 : alignofTy tags fty ∣ foff)
    (hv : C99.Proof.VCGen.ValScalarTyped fty v) :
    ∃ m',
      Sem.writeVal m b (Int64.ofInt (off.toInt + ↑foff)) fty v = some m' ∧
      C99.Proof.VCGen.StructCell tags m' b off structTag true ∧
      C99.Proof.VCGen.HasField tags m' b off structTag fld v ∧
      (∀ b', PreservesBlockMeta m m' b') ∧
      (∀ b' off' len', b' ≠ b → PreservesOutsideRange m m' b' off' len') ∧
      (∀ len', 0 ≤ off.toInt → 0 ≤ off.toInt + ↑foff →
        (Int64.ofInt (off.toInt + ↑foff)).toInt = off.toInt + ↑foff →
        sizeofTy tags (.structTy structTag) ≤ len' →
        PreservesOutsideRange m m' b off len') := by
  obtain ⟨m', hwr, hc', hf', bs, hbs_len, hwb⟩ :=
    C99.Proof.VCGen.StructCell.writeField_some hc hfl hnc hle hal1 hal2 hv
  obtain ⟨blk, hblk, _, _, _⟩ := hc
  refine ⟨m', hwr, hc', hf', fun b' => writeBytes_preservesBlockMeta hblk hwb b',
    fun b' off' len' hne => writeBytes_preservesOutsideRange_ne hwb hne off' len', ?_⟩
  intro len' _ hsum0 hfit hsz
  refine writeBytes_preservesOutsideRange hblk hwb b off len' fun _ => ?_
  rw [hfit, hbs_len]
  refine ⟨hsum0, by omega, by omega⟩

/-! ## 2. Bidirectional Adapters (`C99.Proof.VCGen` ↔ `Zlib.Proof.Invariant` v2) -/

section LiftHelpers

private def DetStepLift (env : Env) (blks : List BlockId) (rt : CTy) (fnBody : CStmt)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont) :
    Option Sem.DetStep → Option Sem.DetStep → Prop
  | none, d2 => d2 = none
  | some (.next s1'), d2 =>
      ∃ s2', d2 = some (.next s2') ∧ RunStateLift env blks rt fnBody fs ctx k s1' s2'
  | some (.allocStr str fs' ctx' mods' e' b' m' os' k1'), d2 =>
      ∃ k2', ContLift env blks rt fnBody fs ctx k k1' k2' ∧
        d2 = some (.allocStr str fs' ctx' mods' e' b' m' os' k2')
  | some (.allocLocal d i? rest e' b' m' os' k1'), d2 =>
      ∃ k2', ContLift env blks rt fnBody fs ctx k k1' k2' ∧
        d2 = some (.allocLocal d i? rest e' b' m' os' k2')
  | some (.callFn sym fty args fs' ctx' e' b' m' os' k1'), d2 =>
      ∃ k2', ContLift env blks rt fnBody fs ctx k k1' k2' ∧
        d2 = some (.callFn sym fty args fs' ctx' e' b' m' os' k2')

private theorem stepDet_ret_rval_nil (prog : Prog) (cfg : PointerConfig)
    (v : Val) (rty : CTy) (ctx : Sem.ExprCtx) (mods : ModSet)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval v rty) []) ctx mods) env blks m os k) =
      match ctx with
      | .discard => some (.next (.running (.stmt .nop) env blks m os k))
      | .returnVal =>
        have rt := k.topRetTy
        if rt.isVoid then some (.next (match Sem.unwindReturn m blks k with
          | some (re, rb, _, m', fs, rctx, rk) => .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' os rk
          | none => .returned .void (m.freeStack blks) os))
        else (Sem.castVal m rt v).map fun cv => .next (match Sem.unwindReturn m blks k with
          | some (re, rb, _, m', fs, rctx, rk) => .running (.expr (.ret (.rval cv rt) fs) rctx []) re rb m' os rk
          | none => .returned cv (m.freeStack blks) os)
      | .varInit d rest => some (.allocLocal d (some (.rval v rty)) rest env blks m os k)
      | .branch t f => (Sem.isTruthy v).map fun b => .next (.running (.stmt (if b then t else f)) env blks m os k)
      | .whileCond c body => (Sem.isTruthy v).map fun b =>
        .next (if b then .running (.stmt body) env blks m os (.loop (some c) none body false k)
               else .running (.stmt .nop) env blks m os k)
      | .doWhileCond body c => (Sem.isTruthy v).map fun b =>
        .next (if b then .running (.stmt body) env blks m os (.loop (some c) none body true k)
               else .running (.stmt .nop) env blks m os k)
      | .forCond c stp? body => (Sem.isTruthy v).map fun b =>
        .next (if b then .running (.stmt body) env blks m os (.loop (some c) stp? body false k)
               else .running (.stmt .nop) env blks m os k)
      | .forStep c? stp? body => some (.next (match c? with
        | some c => .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k
        | none => .running (.stmt body) env blks m os (.loop none stp? body false k)))
      | .switchScrut body => (Sem.valAsInt? v).map fun (_, iv) =>
        .next (match Sem.findSwitchTarget iv body with
          | some tgt => .running (.stmt tgt) env blks m os (.switchCont k)
          | none => .running (.stmt .nop) env blks m os k) := by
  cases v <;> unfold Sem.stepDet <;> cases ctx <;> rfl

private theorem stepDet_decls_cons (prog : Prog) (cfg : PointerConfig)
    (d : VarDecl) (rest : List VarDecl)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env blks m os k) =
      if d.isStatic then some (.next (.running (.stmt (.decls rest)) env blks m os k))
      else match d.init? with
        | none => some (.allocLocal d none rest env blks m os k)
        | some (.expr e) => some (.next (.running (.expr (.eval .rval e []) (.varInit d rest) []) env blks m os k))
        | some _ => none := rfl

private theorem unqual_not_qual :
    ∀ t : CTy, (∀ to, t.unqual ≠ .const_ to) ∧ (∀ nm u, t.unqual ≠ .typedef nm u)
  | .const_ t => unqual_not_qual t
  | .typedef _ t => unqual_not_qual t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _ | .anonStruct _
  | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList =>
    ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩

private theorem castVal_idem_anyMem {m m' : Mem} {rt : CTy} {v cv : Val}
    (h : Sem.castVal m rt v = some cv) : Sem.castVal m' rt cv = some cv := by
  unfold Sem.castVal at h
  cases hu : rt.unqual with
  | «void» =>
    simp only [hu, CTy.isVoid, CTy.unqual, ↓reduceIte, Option.some.injEq] at h
    subst h
    rw [castVal_unqual, hu]
    rfl
  | «int» k =>
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte] at h
    cases v with
    | «int» k1 bv =>
      cases h
      rw [castVal_unqual, hu]
      exact C99.Proof.castVal_int_self m' k _
    | null =>
      cases h
      rw [castVal_unqual, hu]
      exact C99.Proof.castVal_int_self m' k 0
    | ptr b off =>
      cases ha : m.addrOf b off with
      | none => simp [ha] at h
      | some a =>
        simp only [ha, Option.map_some, Option.some.injEq] at h
        subst h
        rw [castVal_unqual, hu]
        exact C99.Proof.castVal_int_self m' k (BitVec.ofNat k.bits a.toNat)
    | _ => cases h
  | enumTy nm isU =>
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte] at h
    cases v with
    | «int» k1 bv =>
      cases h
      unfold Sem.castVal
      simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte, Sem.ofIntCast]
      have hself := C99.Proof.castVal_int_self m' (if isU = true then IntKind.u32 else IntKind.i32)
        (BitVec.ofInt (if isU = true then IntKind.u32 else IntKind.i32).bits
          (if k1.signed = true then bv.toInt else ↑bv.toNat))
      unfold Sem.castVal at hself
      simpa [CTy.isVoid, CTy.intKind?, CTy.unqual, Sem.ofIntCast] using hself
    | null =>
      cases h
      unfold Sem.castVal
      simp [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Sem.ofIntCast]
    | ptr b off =>
      cases ha : m.addrOf b off with
      | none => simp [ha] at h
      | some a =>
        simp only [ha, Option.map_some, Option.some.injEq] at h
        subst h
        unfold Sem.castVal
        simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte]
        have hself := C99.Proof.castVal_int_self m' (if isU = true then IntKind.u32 else IntKind.i32)
          (BitVec.ofNat (if isU = true then IntKind.u32 else IntKind.i32).bits a.toNat)
        unfold Sem.castVal at hself
        simpa [CTy.isVoid, CTy.intKind?, CTy.unqual, Sem.ofIntCast] using hself
    | _ => cases h
  | ptr _ =>
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte] at h
    unfold Sem.castVal
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte]
    cases v with
    | null => cases h; rfl
    | ptr _ _ => cases h; rfl
    | «int» _ bv =>
      by_cases hz : (bv.toNat == 0) = true
      · simp only [hz, ↓reduceIte] at h; cases h; rfl
      · simp [hz] at h
    | _ => cases h
  | fnPtr _ _ _ =>
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte] at h
    unfold Sem.castVal
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte]
    cases v with
    | null => cases h; rfl
    | fnPtr _ => cases h; rfl
    | «int» _ bv =>
      by_cases hz : (bv.toNat == 0) = true
      · simp only [hz, ↓reduceIte] at h; cases h; rfl
      · simp [hz] at h
    | _ => cases h
  | vaList =>
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte] at h
    unfold Sem.castVal
    simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte]
    cases v with
    | vaList valid =>
      cases valid
      · cases h
      · cases h; rfl
    | _ => cases h
  | const_ _ => exact False.elim ((unqual_not_qual rt).1 _ hu)
  | typedef _ _ => exact False.elim ((unqual_not_qual rt).2 _ _ hu)
  | _ => simp only [hu, CTy.isVoid, CTy.intKind?, CTy.unqual, Bool.false_eq_true, ↓reduceIte] at h; cases h

private theorem stepDet_eval_rval_nonStrLit (prog : Prog) (cfg : PointerConfig)
    (ex : CExpr) (hns : ∀ s, ex ≠ .strLit s) (efs : List Sem.ExprFrame) (cctx : Sem.ExprCtx) (mods : ModSet)
    (e : Env) (b : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg (.running (.expr (.eval .rval ex efs) cctx mods) e b m os k) =
      (Sem.stepExprPure prog cfg e m mods (.eval .rval ex efs)).map fun p =>
        .next (.running (.expr p.1 cctx p.2.2) e b p.2.1 os k) := by
  cases ex with
  | strLit s => exact False.elim (hns s rfl)
  | _ => unfold Sem.stepDet; dsimp only

private theorem stepDet_eval_lval (prog : Prog) (cfg : PointerConfig)
    (ex : CExpr) (efs : List Sem.ExprFrame) (cctx : Sem.ExprCtx) (mods : ModSet)
    (e : Env) (b : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg (.running (.expr (.eval .lval ex efs) cctx mods) e b m os k) =
      (Sem.stepExprPure prog cfg e m mods (.eval .lval ex efs)).map fun p =>
        .next (.running (.expr p.1 cctx p.2.2) e b p.2.1 os k) := by
  unfold Sem.stepDet; dsimp only

private theorem stepDet_contLift {prog : Prog} {cfg : PointerConfig}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    {ctrl : Sem.Control} {e : Env} {b : List BlockId} {m : Mem} {os : OSState} {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) :
    DetStepLift env blks rt fnBody fs ctx k
      (Sem.stepDet prog cfg (.running ctrl e b m os k1))
      (Sem.stepDet prog cfg (.running ctrl e b m os k2)) := by
  have ht := ContLift.topRetTy hk
  cases ctrl with
  | expr es cctx mods =>
    cases es with
    | eval lv ex efs =>
      cases lv
      · by_cases hs : ∃ s, ex = .strLit s
        · obtain ⟨s, rfl⟩ := hs; exact ⟨k2, hk, rfl⟩
        · have hns : ∀ s, ex ≠ .strLit s := fun s h => hs ⟨s, h⟩
          rw [stepDet_eval_rval_nonStrLit prog cfg ex hns, stepDet_eval_rval_nonStrLit prog cfg ex hns]
          dsimp only [DetStepLift]
          cases Sem.stepExprPure prog cfg e m mods (.eval .rval ex efs) with
          | none => rfl
          | some p => exact ⟨_, rfl, RunStateLift.inside hk⟩
      · rw [stepDet_eval_lval, stepDet_eval_lval]
        dsimp only [DetStepLift]
        cases Sem.stepExprPure prog cfg e m mods (.eval .lval ex efs) with
        | none => rfl
        | some p => exact ⟨_, rfl, RunStateLift.inside hk⟩
    | ret rv rfs =>
      cases rfs with
      | cons f rfs' =>
        let stepPureCase : Prop := DetStepLift env blks rt fnBody fs ctx k
            (Sem.stepDet prog cfg (.running (.expr (.ret rv (f :: rfs')) cctx mods) e b m os k1))
            (Sem.stepDet prog cfg (.running (.expr (.ret rv (f :: rfs')) cctx mods) e b m os k2))
        have fromPure : Sem.stepDet prog cfg (.running (.expr (.ret rv (f :: rfs')) cctx mods) e b m os k1) =
              ((Sem.stepExprPure prog cfg e m mods (.ret rv (f :: rfs'))).map fun p =>
                .next (.running (.expr p.1 cctx p.2.2) e b p.2.1 os k1)) →
            Sem.stepDet prog cfg (.running (.expr (.ret rv (f :: rfs')) cctx mods) e b m os k2) =
              ((Sem.stepExprPure prog cfg e m mods (.ret rv (f :: rfs'))).map fun p =>
                .next (.running (.expr p.1 cctx p.2.2) e b p.2.1 os k2)) →
            stepPureCase := by
          intro h1 h2
          change DetStepLift _ _ _ _ _ _ _ _ _
          rw [h1, h2]
          cases Sem.stepExprPure prog cfg e m mods (.ret rv (f :: rfs')) with
          | none => rfl
          | some p => exact ⟨_, rfl, RunStateLift.inside hk⟩
        cases rv with
        | lval _ _ _ => exact fromPure rfl rfl
        | structVal _ _ => exact fromPure rfl rfl
        | rval v vty =>
          cases f with
          | callFnF fargs =>
            cases fargs with
            | nil =>
              cases v with
              | fnPtr sym => exact ⟨k2, hk, rfl⟩
              | _ => exact fromPure rfl rfl
            | cons _ _ => exact fromPure (by cases v <;> rfl) (by cases v <;> rfl)
          | callArgF sym fnTy done rest =>
            cases rest with
            | nil => cases v <;> exact ⟨k2, hk, rfl⟩
            | cons _ _ => exact fromPure (by cases v <;> rfl) (by cases v <;> rfl)
          | _ => exact fromPure (by cases v <;> rfl) (by cases v <;> rfl)
      | nil =>
        cases rv with
        | lval _ _ _ =>
          unfold Sem.stepDet
          cases cctx with
          | discard => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | varInit _ _ => exact ⟨k2, hk, rfl⟩
          | forStep c? _ _ =>
            cases c?
            · exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
            · exact ⟨_, rfl, RunStateLift.inside hk⟩
          | _ => rfl
        | structVal _ _ =>
          unfold Sem.stepDet
          cases cctx with
          | discard => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | varInit _ _ => exact ⟨k2, hk, rfl⟩
          | forStep c? _ _ =>
            cases c?
            · exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
            · exact ⟨_, rfl, RunStateLift.inside hk⟩
          | _ => rfl
        | rval v rty =>
          rw [stepDet_ret_rval_nil, stepDet_ret_rval_nil]
          cases cctx with
          | discard => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | varInit d rest => exact ⟨k2, hk, rfl⟩
          | branch t f =>
            cases Sem.isTruthy v with
            | none => rfl
            | some _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | whileCond c body =>
            cases Sem.isTruthy v with
            | none => rfl
            | some bv =>
              cases bv
              · exact ⟨_, rfl, RunStateLift.inside hk⟩
              · exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
          | doWhileCond body c =>
            cases Sem.isTruthy v with
            | none => rfl
            | some bv =>
              cases bv
              · exact ⟨_, rfl, RunStateLift.inside hk⟩
              · exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
          | forCond c stp? body =>
            cases Sem.isTruthy v with
            | none => rfl
            | some bv =>
              cases bv
              · exact ⟨_, rfl, RunStateLift.inside hk⟩
              · exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
          | forStep c? stp? body =>
            cases c?
            · exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
            · exact ⟨_, rfl, RunStateLift.inside hk⟩
          | switchScrut body =>
            cases Sem.valAsInt? v with
            | none => rfl
            | some p =>
              rcases p with ⟨_, iv⟩
              dsimp only [Option.map]
              split
              · exact ⟨_, rfl, RunStateLift.inside (ContLift.switchCont hk)⟩
              · exact ⟨_, rfl, RunStateLift.inside hk⟩
          | returnVal =>
            dsimp only [DetStepLift]
            rw [ht]
            by_cases hvoid : k2.topRetTy.isVoid = true
            · simp only [hvoid, ↓reduceIte]
              rcases ContLift.unwindReturn m b hk with
                ⟨m', hu1, hu2, hrt1, hrt2⟩ | ⟨re, rb, rt', m', fs', ctx', k1', k2', hkl, hu1, hu2⟩
              · rw [hu1, hu2]
                have hrtv : rt.isVoid = true := by rw [← hrt2]; exact hvoid
                exact ⟨_, rfl, RunStateLift.exitedVoid hrtv (Or.inl rfl)⟩
              · rw [hu1, hu2]
                exact ⟨_, rfl, RunStateLift.inside hkl⟩
            · simp only [hvoid, Bool.false_eq_true, ↓reduceIte]
              cases hcv : Sem.castVal m k2.topRetTy v with
              | none => rfl
              | some cv =>
                simp only [Option.map_some]
                rcases ContLift.unwindReturn m b hk with
                  ⟨m', hu1, hu2, hrt1, hrt2⟩ | ⟨re, rb, rt', m', fs', ctx', k1', k2', hkl, hu1, hu2⟩
                · rw [hu1, hu2]
                  have hrtv : rt.isVoid = false := Bool.eq_false_iff.mpr (by rw [← hrt2]; exact hvoid)
                  have hcv_rt : Sem.castVal m rt v = some cv := by rw [← hrt2]; exact hcv
                  rw [hrt2]
                  exact ⟨_, rfl, RunStateLift.exitedVal hrtv (castVal_idem_anyMem hcv_rt)⟩
                · rw [hu1, hu2]
                  exact ⟨_, rfl, RunStateLift.inside hkl⟩
  | stmt s =>
    cases s with
    | nop =>
      cases hk with
      | base =>
        unfold Sem.stepDet
        dsimp only [DetStepLift]
        by_cases hvoid : rt.isVoid = true
        · simp only [hvoid, ↓reduceIte]
          exact ⟨_, rfl, RunStateLift.exitedVoid hvoid (Or.inr rfl)⟩
        · have hnot : rt.isVoid = false := Bool.eq_false_iff.mpr hvoid
          simp only [hnot, Bool.false_eq_true, ↓reduceIte]
          exact ⟨_, rfl, RunStateLift.exitedUndef hnot⟩
      | stmts hrest =>
        rename_i ss _ _
        cases ss with
        | nil => exact ⟨_, rfl, RunStateLift.inside hrest⟩
        | cons _ _ => exact ⟨_, rfl, RunStateLift.inside (ContLift.stmts hrest)⟩
      | switchCont hrest => exact ⟨_, rfl, RunStateLift.inside hrest⟩
      | blockEnd hrest => exact ⟨_, rfl, RunStateLift.inside hrest⟩
      | loop hrest =>
        rename_i c? stp? body isDo _ _
        dsimp only [DetStepLift]
        cases isDo with
        | true =>
          cases c? with
          | some _ => exact ⟨_, rfl, RunStateLift.inside hrest⟩
          | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hrest)⟩
        | false =>
          cases stp? with
          | some _ => exact ⟨_, rfl, RunStateLift.inside hrest⟩
          | none =>
            cases c? with
            | some _ => exact ⟨_, rfl, RunStateLift.inside hrest⟩
            | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hrest)⟩
      | callFrame hrest => exact ⟨_, rfl, RunStateLift.inside hrest⟩
    | expr _ | ifStmt _ _ _ | whileStmt _ _ | switchStmt _ _ | caseStmt _ _ | defaultStmt _
    | labelStmt _ _ =>
      exact ⟨_, rfl, RunStateLift.inside hk⟩
    | returnStmt r? =>
      cases r? with
      | some _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
      | none =>
        unfold Sem.stepDet
        dsimp only [DetStepLift]
        rw [ht]
        by_cases hvoid : k2.topRetTy.isVoid = true
        · simp only [hvoid, ↓reduceIte]
          rcases ContLift.unwindReturn m b hk with
            ⟨m', hu1, hu2, hrt1, hrt2⟩ | ⟨re, rb, rt', m', fs', ctx', k1', k2', hkl, hu1, hu2⟩
          · rw [hu1, hu2]
            have hrtv : rt.isVoid = true := by rw [← hrt2]; exact hvoid
            exact ⟨_, rfl, RunStateLift.exitedVoid hrtv (Or.inl rfl)⟩
          · rw [hu1, hu2]
            exact ⟨_, rfl, RunStateLift.inside hkl⟩
        · simp only [hvoid, Bool.false_eq_true, ↓reduceIte]
    | decl _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
    | decls ds =>
      cases ds with
      | nil => exact ⟨_, rfl, RunStateLift.inside hk⟩
      | cons d rest =>
        change DetStepLift env blks rt fnBody fs ctx k
          (Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) e b m os k1))
          (Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) e b m os k2))
        rw [stepDet_decls_cons, stepDet_decls_cons]
        dsimp only [DetStepLift]
        by_cases hs : d.isStatic = true
        · simp only [hs, ↓reduceIte]
          exact ⟨_, rfl, RunStateLift.inside hk⟩
        · simp only [hs, Bool.false_eq_true, ↓reduceIte]
          cases d.init? with
          | none => exact ⟨k2, hk, rfl⟩
          | some iv =>
            cases iv with
            | expr _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
            | list _ | intSeq _ _ => rfl
    | block ss =>
      cases ss with
      | nil => exact ⟨_, rfl, RunStateLift.inside hk⟩
      | cons hd tl =>
        dsimp only [DetStepLift]
        cases tl with
        | nil => exact ⟨_, rfl, RunStateLift.inside (ContLift.blockEnd hk)⟩
        | cons _ _ => exact ⟨_, rfl, RunStateLift.inside (ContLift.stmts (ContLift.blockEnd hk))⟩
    | doWhileStmt _ _ => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
    | forStmt init? c? _ _ =>
      cases init? with
      | some _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
      | none =>
        cases c? with
        | some _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
        | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
    | breakStmt =>
      unfold Sem.stepDet
      dsimp only [DetStepLift]
      rcases ContLift.unwindBreak m e b hk with
        ⟨hn1, hn2⟩ | ⟨e', b', m', k1', k2', hkl, hb1, hb2⟩
      · rw [hn1, hn2]; rfl
      · rw [hb1, hb2]; exact ⟨_, rfl, RunStateLift.inside hkl⟩
    | continueStmt =>
      unfold Sem.stepDet
      dsimp only [DetStepLift]
      rcases ContLift.unwindContinue m e b hk with
        ⟨hn1, hn2⟩ | ⟨c?, stp?, body, isDo, e', b', m', k1', k2', hkl, hc1, hc2⟩
      · rw [hn1, hn2]; rfl
      · rw [hc1, hc2]
        dsimp only [Option.map, Sem.loopNext]
        cases isDo with
        | true =>
          cases c? with
          | some _ => exact ⟨_, rfl, RunStateLift.inside hkl⟩
          | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hkl)⟩
        | false =>
          cases stp? with
          | some _ => exact ⟨_, rfl, RunStateLift.inside hkl⟩
          | none =>
            cases c? with
            | some _ => exact ⟨_, rfl, RunStateLift.inside hkl⟩
            | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hkl)⟩
    | gotoStmt lbl =>
      unfold Sem.stepDet
      dsimp only [DetStepLift]
      rcases ContLift.gotoInCont lbl m e b hk with
        ⟨hn1, hn2⟩ | ⟨s', e', b', m', k1', k2', hkl, hg1, hg2⟩
      · rw [hn1, hn2]; rfl
      · rw [hg1, hg2]; exact ⟨_, rfl, RunStateLift.inside hkl⟩

private theorem stepDet_ret_stop_void (prog : Prog) (cfg : PointerConfig)
    (env : Env) (rty rt : CTy) (m : Mem) (os : OSState) (hv : rt.isVoid = true) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval .void rty) []) .returnVal []) env [] m os (.stop rt)) =
      some (.next (.returned .void m os)) := by
  unfold Sem.stepDet
  dsimp only [bind, Option.bind]
  simp only [Sem.Cont.topRetTy, hv, ↓reduceIte, Sem.unwindReturn, freeStack_nil]

private theorem stepDet_ret_stop_val (prog : Prog) (cfg : PointerConfig)
    (env : Env) (rty rt : CTy) (v cv : Val) (m : Mem) (os : OSState)
    (hnot : rt.isVoid = false) (hcast : Sem.castVal m rt v = some cv) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval v rty) []) .returnVal []) env [] m os (.stop rt)) =
      some (.next (.returned cv m os)) := by
  unfold Sem.stepDet
  dsimp only [bind, Option.bind]
  simp only [Sem.Cont.topRetTy, hnot, Bool.false_eq_true, ↓reduceIte, Sem.unwindReturn,
    hcast, Option.map_some, freeStack_nil]

private theorem castVal_undef_nonvoid (m : Mem) {rt : CTy} (hnot : rt.isVoid = false) :
    Sem.castVal m rt .undef = none := by
  unfold Sem.castVal
  cases hu : rt.unqual with
  | const_ _ => exact False.elim ((unqual_not_qual rt).1 _ hu)
  | typedef _ _ => exact False.elim ((unqual_not_qual rt).2 _ _ hu)
  | _ => simp [CTy.isVoid, hu, CTy.intKind?, CTy.unqual] at hnot ⊢

private theorem stepDet_ret_stop_undef (prog : Prog) (cfg : PointerConfig)
    (rt : CTy) (m : Mem) (os : OSState) (hnot : rt.isVoid = false) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval .undef rt) []) .returnVal []) [] [] m os (.stop rt)) =
      none := by
  unfold Sem.stepDet
  dsimp only [bind, Option.bind]
  simp only [Sem.Cont.topRetTy, hnot, Bool.false_eq_true, ↓reduceIte, castVal_undef_nonvoid m hnot]
  rfl

private theorem reach_to_wpTerm {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : Sem.RunState}
    (hr : Reach prog cfg ext (fun u => C99.Proof.WPTerm prog cfg ext Q u) s) :
    C99.Proof.WPTerm prog cfg ext Q s := by
  induction hr with
  | done h => exact h
  | step hnub hex _ ih => exact .step hnub hex ih

private theorem reach_to_safeUntil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {R : Sem.RunState → Prop} {s : Sem.RunState}
    (hr : Reach prog cfg ext (fun u => C99.Proof.VCGen.SafeUntil prog cfg ext Q R u) s) :
    C99.Proof.VCGen.SafeUntil prog cfg ext Q R s := by
  induction hr with
  | done h => exact h
  | step hnub hex _ ih =>
    refine SafeUntil.step (fun _ _ _ heq => ?_) hnub ih
    subst heq
    obtain ⟨_, hst⟩ := hex
    exact False.elim (step_not_returned hst)

theorem wpTerm_runStateLift_wpTerm {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    (hvoid : rt.isVoid = true → rt = .void)
    {Q_bot Q_real : Val → Mem → OSState → Prop}
    {s1 s2 : Sem.RunState}
    (ht : C99.Proof.WPTerm prog cfg ext Q_bot s1)
    (hlift : RunStateLift env blks rt fnBody fs ctx k s1 s2)
    (hdone : ∀ ret m' os', Q_bot ret m' os' →
      C99.Proof.WPTerm prog cfg ext Q_real
        (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k)) :
    C99.Proof.WPTerm prog cfg ext Q_real s2 :=
  reach_to_wpTerm (wpTerm_runStateLift_reach hvoid ht hlift fun ret m' os' h => .done (hdone ret m' os' h))

theorem wpTerm_runStateLift_safeUntil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    (hvoid : rt.isVoid = true → rt = .void)
    {Q_bot Q_real : Val → Mem → OSState → Prop} {R : Sem.RunState → Prop}
    {s1 s2 : Sem.RunState}
    (ht : C99.Proof.WPTerm prog cfg ext Q_bot s1)
    (hlift : RunStateLift env blks rt fnBody fs ctx k s1 s2)
    (hdone : ∀ ret m' os', Q_bot ret m' os' →
      C99.Proof.VCGen.SafeUntil prog cfg ext Q_real R
        (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k)) :
    C99.Proof.VCGen.SafeUntil prog cfg ext Q_real R s2 :=
  reach_to_safeUntil (wpTerm_runStateLift_reach hvoid ht hlift fun ret m' os' h => .done (hdone ret m' os' h))

theorem safeUntil_runStateLift_safe {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    (hvoid : rt.isVoid = true → rt = .void)
    {Q_bot Q_real : Val → Mem → OSState → Prop}
    {s1_0 s2_0 : Sem.RunState}
    (hsu : C99.Proof.VCGen.SafeUntil prog cfg ext Q_bot (fun _ => False) s1_0)
    (hlift : RunStateLift env blks rt fnBody fs ctx k s1_0 s2_0)
    (hdone : ∀ ret m' os', Q_bot ret m' os' →
      Sem.Safe prog cfg ext (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k) ∧
      (∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext)
        (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k) (.returned r m'' os'') →
        Q_real r m'' os'')) :
    Sem.Safe prog cfg ext s2_0 ∧
    (∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext) s2_0 (.returned r m'' os'') → Q_real r m'' os'') := by
  let TailOK : Sem.RunState → Prop := fun s =>
    Sem.Safe prog cfg ext s ∧
    ∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext) s (.returned r m'' os'') → Q_real r m'' os''
  let Inv : Sem.RunState → Prop := fun s2 =>
    (∃ s1, C99.Proof.VCGen.SafeUntil prog cfg ext Q_bot (fun _ => False) s1 ∧
      RunStateLift env blks rt fnBody fs ctx k s1 s2) ∨ TailOK s2
  have hInv : ∀ s2, Inv s2 →
      ¬ s2.isUB ∧
      (∀ r m'' os'', s2 = .returned r m'' os'' → Q_real r m'' os'') ∧
      ∀ s2', Sem.Step prog cfg ext s2 s2' → Inv s2' := by
    intro s2 hs2
    rcases hs2 with ⟨s1, hs1, hlf⟩ | htail
    · cases hlf with
      | @exitedVoid m' os' rty hrt hrty =>
        have hrt_eq : rt = .void := hvoid hrt
        subst hrt_eq
        rcases hrty with rfl | rfl <;>
        · have hqb : Q_bot .void m' os' :=
            hs1.post (.tail (.refl _) (.det (stepDet_ret_stop_void prog cfg [] _ .void m' os' hrt)))
          have hd := hdone .void m' os' hqb
          refine ⟨Bool.false_ne_true, (fun _ _ _ heq => by cases heq), fun s2' hs2' => ?_⟩
          exact Or.inr ⟨fun s'' hst => hd.1 s'' (C99.Proof.star_head hs2' hst),
            fun r m'' os'' hst => hd.2 r m'' os'' (C99.Proof.star_head hs2' hst)⟩
      | @exitedVal v m' os' hnot hcast =>
        have hqb : Q_bot v m' os' :=
          hs1.post (.tail (.refl _) (.det (stepDet_ret_stop_val prog cfg [] rt rt v v m' os' hnot hcast)))
        have hd := hdone v m' os' hqb
        refine ⟨Bool.false_ne_true, (fun _ _ _ heq => by cases heq), fun s2' hs2' => ?_⟩
        exact Or.inr ⟨fun s'' hst => hd.1 s'' (C99.Proof.star_head hs2' hst),
          fun r m'' os'' hst => hd.2 r m'' os'' (C99.Proof.star_head hs2' hst)⟩
      | @exitedUndef m' os' hnot =>
        exact False.elim (hs1.safe .ub (.tail (.refl _) (.det_ub (stepDet_ret_stop_undef prog cfg rt m' os' hnot))) rfl)
      | @inside ctrl e b m os k1 k2 hk =>
        refine ⟨Bool.false_ne_true, (fun _ _ _ heq => by cases heq), fun s2' hs2' => Or.inl ?_⟩
        have hd := stepDet_contLift (prog := prog) (cfg := cfg) (ctrl := ctrl)
          (e := e) (b := b) (m := m) (os := os) hk
        cases hd1 : Sem.stepDet prog cfg (.running ctrl e b m os k1) with
        | none =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd
          exact False.elim (hs1.safe .ub (.tail (.refl _) (.det_ub hd1)) rfl)
        | some d1 =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd
          cases d1 with
          | next s1' =>
            obtain ⟨s2_det, hd2, hlift'⟩ := hd
            cases hs2' with
            | det hd2' =>
              rw [hd2] at hd2'; cases hd2'
              exact ⟨s1', hs1.star_inv (.tail (.refl _) (.det hd1)), hlift'⟩
            | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | allocStr str fs' ctx' mods' e' b' m' os' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | strLit hd2' hsz halloc =>
              rw [hd2] at hd2'; cases hd2'
              exact ⟨_, hs1.star_inv (.tail (.refl _) (.strLit hd1 hsz halloc)), RunStateLift.inside hk'⟩
            | det hd2' | det_ub hd2' | localDecl hd2' | localDecl_ub hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | allocLocal d i? rest e' b' m' os' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | localDecl hd2' hsz hal hba halloc hwr =>
              rw [hd2] at hd2'; cases hd2'
              exact ⟨_, hs1.star_inv (.tail (.refl _) (.localDecl hd1 hsz hal hba halloc hwr)),
                RunStateLift.inside hk'⟩
            | localDecl_ub hd2' hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim (hs1.safe .ub (.tail (.refl _) (.localDecl_ub hd1 hbad)) rfl)
            | det hd2' | det_ub hd2' | strLit hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | callFn sym fty args fs' ctx' e' b' m' os' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | call_internal hd2' hfn hcoerce hpush =>
              rw [hd2] at hd2'; cases hd2'
              exact ⟨_, hs1.star_inv (.tail (.refl _) (.call_internal hd1 hfn hcoerce hpush)),
                RunStateLift.inside (ContLift.callFrame hk')⟩
            | call_internal_ub hd2' hfn hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim (hs1.safe .ub (.tail (.refl _) (.call_internal_ub hd1 hfn hbad)) rfl)
            | call_ext hd2' hnfn hsig hcoerce hext =>
              rw [hd2] at hd2'; cases hd2'
              rename_i out'
              cases out' with
              | ub =>
                exact False.elim (hs1.safe .ub (.tail (.refl _) (.call_ext hd1 hnfn hsig hcoerce hext)) rfl)
              | ok ret m' os' =>
                exact ⟨_, hs1.star_inv (.tail (.refl _) (.call_ext hd1 hnfn hsig hcoerce hext)),
                  RunStateLift.inside hk'⟩
            | call_ext_ub hd2' hnfn hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim (hs1.safe .ub (.tail (.refl _) (.call_ext_ub hd1 hnfn hbad)) rfl)
            | det hd2' | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
    · refine ⟨htail.1 _ (.refl _), fun r m'' os'' heq => htail.2 r m'' os'' (by subst heq; exact .refl _),
        fun s2' hs2' => Or.inr ⟨fun s'' hst => htail.1 s'' (C99.Proof.star_head hs2' hst),
          fun r m'' os'' hst => htail.2 r m'' os'' (C99.Proof.star_head hs2' hst)⟩⟩
  have hstarInv : ∀ s', Sem.Star (Sem.Step prog cfg ext) s2_0 s' → Inv s' := by
    intro s' hstar
    induction hstar with
    | refl => exact Or.inl ⟨s1_0, hsu, hlift⟩
    | tail _ hstep ih => exact (hInv _ ih).2.2 _ hstep
  exact ⟨fun s' hstar => (hInv s' (hstarInv s' hstar)).1,
    fun r m'' os'' hstar => (hInv _ (hstarInv _ hstar)).2.1 r m'' os'' rfl⟩

end LiftHelpers

section ForwardAdapters

private theorem retTy_void_of_ret_ty {fn : FnDef}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void)) :
    fn.retTy.isVoid = true → fn.retTy = .void := by
  intro hv
  rcases hret_ty with hnv | ⟨hveq, _⟩
  · rw [hv] at hnv; cases hnv
  · exact hveq

theorem vcFn_to_callWPTermSpec {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvt : ∀ m os args, pre m os args → args.length = fn.params.length →
      ∀ pv ∈ fn.params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2)
    (hvc : C99.Proof.VCGen.vcFn prog cfg specs fn annBody pre post) :
    Zlib.Proof.CallWPTermSpec prog cfg ext fn pre post := by
  let _ := hfn
  let _ := hsc
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush hcont
  have hvt' := hvt m os args hpre hlen
  obtain ⟨cur, hr⟩ := C99.Proof.VCGen.Refines.of_pushCallParams
    (C99.Proof.VCGen.Refines.init prog.tags (prog.fnStatics fn.name ++ prog.globalEnv) m os)
    rfl hvt' hpush
  have hk : C99.Proof.VCGen.ContOKGen prog cfg (C99.Proof.WPTerm prog cfg ext)
      (prog.fnStatics fn.name ++ prog.globalEnv) Q fn.retTy []
      (C99.Proof.VCGen.fnEntryPost fn post m os args)
      (.callFrame env blks fn.retTy fn.body fs ctx k) := by
    refine C99.Proof.VCGen.ContOKGen.callFrame
      (hrules := C99.Proof.VCGen.WPRules.wpTerm prog cfg ext)
      (fun rv m1 m2 os' h1 h2 hp => hpost_ext m os args rv m1 m2 os' h1 h2 hp)
      hret_ty env blks fs ctx k hcont
  have hvt_take : ∀ pv ∈ fn.params.zip (args.take fn.params.length),
      C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2 := by
    simpa [List.take_of_length_le (Nat.le_of_eq hlen)] using hvt'
  have hlen_vc : if fn.variadic = true then fn.params.length ≤ args.length else args.length = fn.params.length := by
    cases fn.variadic <;> simp [hlen]
  have hr' : C99.Proof.VCGen.Refines prog.tags (prog.fnStatics fn.name ++ prog.globalEnv) cur []
      (fnEntryState fn m os args) callEnv callBlks m1 := by
    simpa [C99.Proof.VCGen.fnEntryState, List.take_of_length_le (Nat.le_of_eq hlen)] using hr
  have hw := C99.Proof.VCGen.vcStmt_sound hk hr' (hvc m os args hvt_take hlen_vc hpre)
  simpa [herase, C99.Proof.VCGen.fnEntryState, List.take_of_length_le (Nat.le_of_eq hlen)] using hw

theorem vcFn_to_callWPTermSpec_typed {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hvc : C99.Proof.VCGen.vcFn prog cfg specs fn annBody pre post) :
    Zlib.Proof.CallWPTermSpec prog cfg ext fn
      (fun m os args => pre m os args ∧
        ∀ pv ∈ fn.params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2)
      post :=
  vcFn_to_callWPTermSpec hfn herase hsc hret_ty hpost_ext (fun _ _ _ h _ => h.2)
    (fun m os args hvt hlen h => hvc m os args hvt hlen h.1)

theorem vcFnSafeSplit_to_callSafeSpec {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annSafe annTerm : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvt : ∀ m os args, pre m os args → args.length = fn.params.length →
      ∀ pv ∈ fn.params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2)
    (hvc : C99.Proof.VCGen.vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post) :
    Zlib.Proof.CallSafeSpec prog cfg ext fn pre post := by
  let _ := hfn
  let _ := hsc
  have hret_ty : fn.retTy.isVoid = false ∨
      (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) := by
    rcases hret_ok with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl h1
  have hvoid : fn.retTy.isVoid = true → fn.retTy = .void := retTy_void_of_ret_ty hret_ty
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush hcont
  have hvt' := hvt m os args hpre hlen
  have hvt_take : ∀ pv ∈ fn.params.zip (args.take fn.params.length),
      C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2 := by
    simpa [List.take_of_length_le (Nat.le_of_eq hlen)] using hvt'
  obtain ⟨cur, hr⟩ := C99.Proof.VCGen.Refines.of_pushCallParams
    (C99.Proof.VCGen.Refines.init prog.tags (prog.fnStatics fn.name ++ prog.globalEnv) m os)
    rfl hvt' hpush
  have hlen_vc : if fn.variadic = true then fn.params.length ≤ args.length else args.length = fn.params.length := by
    cases fn.variadic <;> simp [hlen]
  have hsplit := hvc m os args hvt_take hlen_vc hpre
  let Q_bot : Val → Mem → OSState → Prop := fun rv m' os' => post m os args rv m' os'
  have hbot_ret_det : ∀ rv m' os', Q_bot rv m' os' →
      Sem.stepDet prog cfg (.running (.expr (.ret (.rval rv fn.retTy) []) .returnVal []) [] [] m' os' (.stop fn.retTy)) =
        some (.next (.returned rv m' os')) := by
    intro rv m' os' hp
    rcases hret_ok with ⟨hveq, hrv⟩ | ⟨hnv, hscv⟩
    · have hveq' := hrv m os args rv m' os' hp
      subst hveq'
      have hvd : fn.retTy.isVoid = true := by simp [hveq, CTy.isVoid, CTy.unqual]
      exact stepDet_ret_stop_void prog cfg [] fn.retTy fn.retTy m' os' hvd
    · have hcast := C99.Proof.VCGen.ValScalarTyped.castVal_self m' (hscv m os args rv m' os' hp)
      exact stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy rv rv m' os' hnv hcast
  have hsu_bot : C99.Proof.VCGen.SafeUntil prog cfg ext Q_bot (fun _ => False)
      (.running (.stmt fn.body) callEnv callBlks m1 os (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) := by
    have hk_bot : C99.Proof.VCGen.ContOKGen prog cfg
        (fun Q' u => C99.Proof.VCGen.SafeUntil prog cfg ext Q' (fun _ => False) u)
        (prog.fnStatics fn.name ++ prog.globalEnv) Q_bot fn.retTy []
        (C99.Proof.VCGen.fnEntryPost fn post m os args)
        (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy)) :=
      C99.Proof.VCGen.ContOKGen.callFrame
        (hrules := C99.Proof.VCGen.WPRules.safeUntil prog cfg ext (fun _ => False))
        (fun rv m1 m2 os' h1 h2 hp => hpost_ext m os args rv m1 m2 os' h1 h2 hp)
        hret_ty [] [] [] .returnVal (.stop fn.retTy)
        fun rv m' os' hp => SafeUntil.of_det_state (hbot_ret_det rv m' os' hp) (SafeUntil.returned hp)
    cases hbd : os.readBudget.isSome with
    | false =>
      have hr' : C99.Proof.VCGen.Refines prog.tags (prog.fnStatics fn.name ++ prog.globalEnv) cur []
          (fnEntryState fn m os args) callEnv callBlks m1 := by
        simpa [C99.Proof.VCGen.fnEntryState, List.take_of_length_le (Nat.le_of_eq hlen)] using hr
      have hw := C99.Proof.VCGen.vcStmtSafe_safeUntil_sound hk_bot hr' (hsplit.1 hbd)
      rwa [herase_safe] at hw
    | true =>
      have hr' : C99.Proof.VCGen.Refines prog.tags (prog.fnStatics fn.name ++ prog.globalEnv) cur []
          (fnEntryState fn m os args) callEnv callBlks m1 := by
        simpa [C99.Proof.VCGen.fnEntryState, List.take_of_length_le (Nat.le_of_eq hlen)] using hr
      have hw := C99.Proof.VCGen.vcStmt_safeUntil_sound hk_bot hr' (hsplit.2 hbd)
      rwa [herase_term] at hw
  have hsafe_top := safeUntil_runStateLift_safe hvoid hsu_bot (RunStateLift.inside ContLift.base)
    fun rv m' os' hp => ⟨(hcont rv m' os' hp).safe, fun r m'' os'' hst => (hcont rv m' os' hp).post hst⟩
  refine ⟨hsafe_top.1, ?_, hsafe_top.2⟩
  intro hrb
  dsimp only [readBudgetIsSome] at hrb
  have hk_top : C99.Proof.VCGen.ContOKGen prog cfg (C99.Proof.WPTerm prog cfg ext)
      (prog.fnStatics fn.name ++ prog.globalEnv) Q fn.retTy []
      (C99.Proof.VCGen.fnEntryPost fn post m os args)
      (.callFrame env blks fn.retTy fn.body fs ctx k) :=
    C99.Proof.VCGen.ContOKGen.callFrame
      (hrules := C99.Proof.VCGen.WPRules.wpTerm prog cfg ext)
      (fun rv m1 m2 os' h1 h2 hp => hpost_ext m os args rv m1 m2 os' h1 h2 hp)
      hret_ty env blks fs ctx k fun rv m' os' hp =>
        (hcont rv m' os' hp).2.1 (hbud m os args rv m' os' hpre hrb hp)
  have hr' : C99.Proof.VCGen.Refines prog.tags (prog.fnStatics fn.name ++ prog.globalEnv) cur []
      (fnEntryState fn m os args) callEnv callBlks m1 := by
    simpa [C99.Proof.VCGen.fnEntryState, List.take_of_length_le (Nat.le_of_eq hlen)] using hr
  have hw := C99.Proof.VCGen.vcStmt_sound hk_top hr' (hsplit.2 hrb)
  rwa [herase_term] at hw

theorem vcFnSafeSplit_to_callSafeSpec_typed {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annSafe annTerm : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvc : C99.Proof.VCGen.vcFnSafeSplit prog cfg specs fn annSafe annTerm pre post) :
    Zlib.Proof.CallSafeSpec prog cfg ext fn
      (fun m os args => pre m os args ∧
        ∀ pv ∈ fn.params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2)
      post :=
  vcFnSafeSplit_to_callSafeSpec hfn herase_safe herase_term hsc hret_ok hpost_ext
    (fun m os args rv m' os' hp => hbud m os args rv m' os' hp.1)
    (fun _ _ _ h _ => h.2)
    (fun m os args hvt hlen h => hvc m os args hvt hlen h.1)

theorem vcFnSafe_to_callSafeSpec {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvt : ∀ m os args, pre m os args → args.length = fn.params.length →
      ∀ pv ∈ fn.params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2)
    (hvc : C99.Proof.VCGen.vcFnSafe prog cfg specs fn annBody pre post) :
    Zlib.Proof.CallSafeSpec prog cfg ext fn pre post :=
  vcFnSafeSplit_to_callSafeSpec hfn herase herase hsc hret_ok hpost_ext hbud hvt hvc

theorem vcFnSafe_to_callSafeSpec_typed {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (herase : annBody.erase = fn.body)
    (hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0 os0 args rv m1 m2 os', m1.nextBlock ≤ m2.nextBlock → (∀ b, m2.blocks b = m1.blocks b) →
      post m0 os0 args rv m1 os' → post m0 os0 args rv m2 os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvc : C99.Proof.VCGen.vcFnSafe prog cfg specs fn annBody pre post) :
    Zlib.Proof.CallSafeSpec prog cfg ext fn
      (fun m os args => pre m os args ∧
        ∀ pv ∈ fn.params.zip args, C99.Proof.VCGen.ValScalarTyped pv.1.ty pv.2)
      post :=
  vcFnSafeSplit_to_callSafeSpec_typed hfn herase herase hsc hret_ok hpost_ext hbud hvc

private theorem argsWellTyped_map_fnParams {prog : Prog} {params : List Param} {cParamTys : List CTy}
    {variadic : Bool} {args : List Val}
    (hptys : List.map (fun p => p.ty.unqual) params = List.map CTy.unqual cParamTys)
    (hawt : Zlib.Spec.ArgsWellTyped prog cParamTys variadic args) :
    Zlib.Spec.ArgsWellTyped prog (params.map (·.ty)) variadic args := by
  have hlen : params.length = cParamTys.length := by simpa using congrArg List.length hptys
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hawt.1
    cases variadic <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_map] at h1 ⊢ <;> omega
  · intro i hi
    simp only [List.length_map] at hi
    have hv := hawt.2.1 i (by omega)
    cases hget : args[i]? with
    | none => simp [hget] at hv
    | some av =>
      simp only [hget] at hv ⊢
      simp only [List.getElem_map]
      have hith := congrArg (·[i]?) hptys
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by omega : i < cParamTys.length),
        Option.map_some, Option.some.injEq] at hith
      rw [valHasCTy_unqual, hith, ← valHasCTy_unqual]
      exact hv
  · intro i hi
    simp only [List.length_map] at hi
    have hfp := hawt.2.2 i (by omega)
    simp only [List.getElem_map]
    have hith := congrArg (·[i]?) hptys
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (by omega : i < cParamTys.length),
      Option.map_some, Option.some.injEq] at hith
    cases hget : args[i]? with
    | none => simp [hget] at hfp ⊢
    | some av =>
      simp only [hith] at ⊢
      simp only [hget] at hfp
      exact hfp

theorem vcFnSafeSplit_to_contractSafe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView}
    {specs : SafeSpecEnv prog Zlib.Spec.zlibPointerConfig ext}
    {fn : FnDef} {annSafe annTerm : AnnStmt}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hnonvar : c.variadic = false ∧ fn.variadic = false)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, false))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0' os0' args' rv m1' m2' os', m1'.nextBlock ≤ m2'.nextBlock → (∀ b, m2'.blocks b = m1'.blocks b) →
      post m0' os0' args' rv m1' os' → post m0' os0' args' rv m2' os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvc : C99.Proof.VCGen.vcFnSafeSplit prog Zlib.Spec.zlibPointerConfig specs fn annSafe annTerm pre post)
    (hpreImp : ∀ v owned m os args,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      pre m os args)
    (hpostImp : ∀ v owned m os args ret m' os',
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      post m os args ret m' os' →
      ∃ cv,
        (if protoRetTy.isVoid = true then cv = .void
         else Sem.castVal m' protoRetTy ret = some cv) ∧
        (∃ owned' v',
          c.post prog.tags owned v m args cv m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          Zlib.Spec.FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          Zlib.Spec.NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c := by
  have hfn' : prog.fns fn.name = some fn := by rwa [hname]
  have hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true :=
    fun p hp => isScalarPlaceTy_of_isSimpleParamTy (hsimple p hp)
  have hcs := vcFnSafeSplit_to_callSafeSpec_typed hfn' herase_safe herase_term hsc hret_ok hpost_ext hbud hvc
  refine Zlib.Proof.CallSafeSpec.to_contractSafe hfn hname hnonvar hproto hptys hsimple hcs ?_ hpostImp
  intro v owned m os args hInv hpre hawt hargDisj
  exact ⟨hpreImp v owned m os args hInv hpre hawt hargDisj,
    (argsWellTyped_of_params_scalar hsc (argsWellTyped_map_fnParams hptys hawt)).2⟩

theorem vcFnSafe_to_contractSafe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView}
    {specs : SafeSpecEnv prog Zlib.Spec.zlibPointerConfig ext}
    {fn : FnDef} {annBody : AnnStmt}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hnonvar : c.variadic = false ∧ fn.variadic = false)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, false))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (herase : annBody.erase = fn.body)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0' os0' args' rv m1' m2' os', m1'.nextBlock ≤ m2'.nextBlock → (∀ b, m2'.blocks b = m1'.blocks b) →
      post m0' os0' args' rv m1' os' → post m0' os0' args' rv m2' os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvc : C99.Proof.VCGen.vcFnSafe prog Zlib.Spec.zlibPointerConfig specs fn annBody pre post)
    (hpreImp : ∀ v owned m os args,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      pre m os args)
    (hpostImp : ∀ v owned m os args ret m' os',
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      post m os args ret m' os' →
      ∃ cv,
        (if protoRetTy.isVoid = true then cv = .void
         else Sem.castVal m' protoRetTy ret = some cv) ∧
        (∃ owned' v',
          c.post prog.tags owned v m args cv m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          Zlib.Spec.FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          Zlib.Spec.NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c :=
  vcFnSafeSplit_to_contractSafe hfn hname hnonvar hproto hptys hsimple herase herase
    hret_ok hpost_ext hbud hvc hpreImp hpostImp

theorem vcFnSafeSplit_to_contractSafe_variadic
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView}
    {specs : SafeSpecEnv prog Zlib.Spec.zlibPointerConfig ext}
    {fn : FnDef} {annSafe annTerm : AnnStmt}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hvar : c.variadic = true ∧ fn.variadic = true)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, true))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (herase_safe : annSafe.erase = fn.body)
    (herase_term : annTerm.erase = fn.body)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0' os0' args' rv m1' m2' os', m1'.nextBlock ≤ m2'.nextBlock → (∀ b, m2'.blocks b = m1'.blocks b) →
      post m0' os0' args' rv m1' os' → post m0' os0' args' rv m2' os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvc : C99.Proof.VCGen.vcFnSafeSplit prog Zlib.Spec.zlibPointerConfig specs fn annSafe annTerm pre post)
    (hpreImp : ∀ v owned m os args,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      pre m os (args.take fn.params.length))
    (hpostImp : ∀ v owned m os args ret m' os',
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      post m os (args.take fn.params.length) ret m' os' →
      ∃ cv,
        (if protoRetTy.isVoid = true then cv = .void
         else Sem.castVal m' protoRetTy ret = some cv) ∧
        (∃ owned' v',
          c.post prog.tags owned v m args cv m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          Zlib.Spec.FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          Zlib.Spec.NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c := by
  have hfn' : prog.fns fn.name = some fn := by rwa [hname]
  have hsc : ∀ p ∈ fn.params, C99.Proof.VCGen.isScalarPlaceTy p.ty = true :=
    fun p hp => isScalarPlaceTy_of_isSimpleParamTy (hsimple p hp)
  have hcs := vcFnSafeSplit_to_callSafeSpec_typed hfn' herase_safe herase_term hsc hret_ok hpost_ext hbud hvc
  refine Zlib.Proof.CallSafeSpec.to_contractSafe_variadic hfn hname hvar hproto hptys hsimple hcs ?_ hpostImp
  intro v owned m os args hInv hpre hawt hargDisj
  exact ⟨hpreImp v owned m os args hInv hpre hawt hargDisj,
    (argsWellTyped_take_of_params_scalar hsc (argsWellTyped_map_fnParams hptys hawt)).2⟩

theorem vcFnSafe_to_contractSafe_variadic
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView}
    {specs : SafeSpecEnv prog Zlib.Spec.zlibPointerConfig ext}
    {fn : FnDef} {annBody : AnnStmt}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {pre : Mem → OSState → List Val → Prop}
    {post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hvar : c.variadic = true ∧ fn.variadic = true)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, true))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (herase : annBody.erase = fn.body)
    (hret_ok : (fn.retTy = .void ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' → rv = .void) ∨
      (fn.retTy.isVoid = false ∧ ∀ m0' os0' args' rv m1' os1', post m0' os0' args' rv m1' os1' →
        C99.Proof.VCGen.ValScalarTyped fn.retTy rv))
    (hpost_ext : ∀ m0' os0' args' rv m1' m2' os', m1'.nextBlock ≤ m2'.nextBlock → (∀ b, m2'.blocks b = m1'.blocks b) →
      post m0' os0' args' rv m1' os' → post m0' os0' args' rv m2' os')
    (hbud : ∀ m os args rv m' os',
      pre m os args → os.readBudget.isSome = true →
      post m os args rv m' os' → os'.readBudget.isSome = true)
    (hvc : C99.Proof.VCGen.vcFnSafe prog Zlib.Spec.zlibPointerConfig specs fn annBody pre post)
    (hpreImp : ∀ v owned m os args,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      pre m os (args.take fn.params.length))
    (hpostImp : ∀ v owned m os args ret m' os',
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      post m os (args.take fn.params.length) ret m' os' →
      ∃ cv,
        (if protoRetTy.isVoid = true then cv = .void
         else Sem.castVal m' protoRetTy ret = some cv) ∧
        (∃ owned' v',
          c.post prog.tags owned v m args cv m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          Zlib.Spec.FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          Zlib.Spec.NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c :=
  vcFnSafeSplit_to_contractSafe_variadic hfn hname hvar hproto hptys hsimple herase herase
    hret_ok hpost_ext hbud hvc hpreImp hpostImp

end ForwardAdapters

section ReverseAdapters

private theorem coerceCallArgs_length_param {m : Mem} {ptys : List CTy} {argVals : List (Val × CTy)}
    {args : List Val} (hco : Sem.coerceCallArgs m ptys false argVals = some args) :
    args.length = ptys.length := by
  have ⟨hl, _⟩ := coerceCallArgs_length hco
  exact hl

def callWPTermSpec_to_vcCallSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hvoid : fn.retTy.isVoid = true → fn.retTy = .void)
    (hret : ∀ m os args ret m' os', Pre m os args → Post m os args ret m' os' →
      if fn.retTy.isVoid then ret = .void else Sem.castVal m' fn.retTy ret = some ret)
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean os args → Pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean os args →
      Post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val}
      (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean os args →
      Post m os args rv m_after os' →
      Post m_clean os args rv (dropBlks m_after bs) os')
    (hspec : Zlib.Proof.CallWPTermSpec prog cfg ext fn Pre Post) :
    C99.Proof.VCGen.CallSpec prog cfg ext where
  sym := fn.name
  paramTys := fn.params.map (·.ty)
  retTy := fn.retTy
  variadic := fn.variadic
  pre := Pre
  post := Post
  pre_mono := hpre_mono
  post_stack := hpost_stack
  post_drop := hpost_drop
  sound := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q hd _ _ hco hpre hcont
    rw [hnonvar] at hco
    exact hspec.call hd hfn rfl hnonvar hco hpre hsimp hcont
  sound_safe := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q R hd _ _ hco hpre hcont
    rw [hnonvar] at hco
    have hlenC := coerceCallArgs_length_param hco
    simp only [List.length_map] at hlenC
    have htake : List.take fn.params.length args = args := List.take_of_length_le (by omega)
    have hawt : ArgsHaveCTy (fn.params.map (·.ty)) false args :=
      coerceCallArgs_produces_argsWellTyped hco
    have hex0 : ∃ callEnv0 callBlks0 m0',
        Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip args)
          (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') :=
      pushCallParams_exists_base0 prog.tags hsimp hawt
    have hcoV : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some args := by
      simpa [hnonvar] using hco
    refine SafeUntil.of_call_internal hd hfn hcoV (by simpa [htake] using hex0) ?_
    intro base callEnv callBlks m1 hpush
    rw [htake] at hpush
    have ht_bot : C99.Proof.WPTerm prog cfg ext (fun ret m' os' => Post m os args ret m' os')
        (.running (.stmt fn.body) callEnv callBlks m1 os
          (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) := by
      refine hspec args [] [] m m1 os base callEnv callBlks [] .returnVal (.stop fn.retTy) _
        hpre hlenC hpush ?_
      intro ret m' os' hpo
      have hrm := hret m os args ret m' os' hpre hpo
      by_cases hv : fn.retTy.isVoid = true
      · simp only [hv, ↓reduceIte] at hrm; subst hrm
        exact C99.Proof.WPTerm.of_det (stepDet_ret_stop_void prog cfg [] fn.retTy fn.retTy m' os' hv) (.returned hpo)
      · have hnv : fn.retTy.isVoid = false := Bool.eq_false_iff.mpr hv
        simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hrm
        exact C99.Proof.WPTerm.of_det (stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy ret ret m' os' hnv hrm) (.returned hpo)
    exact wpTerm_runStateLift_safeUntil hvoid ht_bot (RunStateLift.inside ContLift.base) hcont

def heapBodySpec_to_vcCallSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hvoid : fn.retTy.isVoid = true → fn.retTy = .void)
    (hret : ∀ m args ret m', Pre m args → Post m args ret m' →
      if fn.retTy.isVoid then ret = .void else Sem.castVal m' fn.retTy ret = some ret)
    (hpre_mono : ∀ {m_clean m : Mem} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean args → Pre m args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean args →
      Post m args rv m' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean args →
      Post m args rv m_after →
      Post m_clean args rv (dropBlks m_after bs))
    (hspec : HeapBodySpec prog cfg ext fn Pre Post) :
    C99.Proof.VCGen.CallSpec prog cfg ext :=
  callWPTermSpec_to_vcCallSpec
    (Pre := fun m _ args => Pre m args)
    (Post := fun m os args rv m' os' => os' = os ∧ Post m args rv m')
    hfn hnonvar hsimp hvoid
    (fun m _ args ret m' _ hp ⟨_, hpo⟩ => hret m args ret m' hp hpo)
    (fun bs h1 h2 h3 h4 h5 hp => hpre_mono bs h1 h2 h3 h4 h5 hp)
    (fun bs h1 h2 h3 h4 h5 hp ⟨_, hpo⟩ => hpost_stack bs h1 h2 h3 h4 h5 hp hpo)
    (fun bs h1 h2 h3 h4 h5 hp ⟨hos, hpo⟩ => ⟨hos, hpost_drop bs h1 h2 h3 h4 h5 hp hpo⟩)
    hspec.to_callWPTermSpec

private theorem roExt_post_stack_drop {m_clean m m_after : Mem} (bs : List BlockId)
    (h1 : m_clean.nextBlock ≤ m.nextBlock)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hro : C99.Proof.ROExt m m_after) :
    C99.Proof.ROExt m_clean (dropBlks m_after bs) := by
  refine ⟨Nat.le_trans h1 hro.1, fun b hlt => ?_, fun b blk hlt hblk => ?_⟩
  · by_cases hm : b ∈ bs
    · rw [h2 b hm]
      simp [dropBlks, hm]
    · rw [dropBlks_blocks_not_mem m_after bs hm, hro.2.1 b (Nat.lt_of_lt_of_le hlt h1), h3 b hm]
  · by_cases hm : b ∈ bs
    · simp [dropBlks, hm] at hblk
    · rw [dropBlks_blocks_not_mem m_after bs hm] at hblk
      by_cases bm : b < m.nextBlock
      · exfalso
        rw [hro.2.1 b bm, h3 b hm, m_clean.fresh b hlt] at hblk
        cases hblk
      · exact hro.2.2 b blk (Nat.le_of_not_lt bm) hblk

private theorem roExt_stack_pres {m m' : Mem} (hro : C99.Proof.ROExt m m') :
    m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk := by
  refine ⟨hro.1, fun b blk hb _ => ?_⟩
  rw [hro.2.1 b (lt_nextBlock_of_some hb), hb]

def funcBodySpec_to_vcCallSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hvoid : fn.retTy.isVoid = true → fn.retTy = .void)
    (hret : ∀ m args ret m', Pre m args → C99.Proof.ROExt m m' → Post m args ret m' →
      if fn.retTy.isVoid then ret = .void else Sem.castVal m' fn.retTy ret = some ret)
    (hpre_mono : ∀ {m_clean m : Mem} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean args → Pre m args)
    (hpost_drop : ∀ {m_clean m m_after : Mem} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean args →
      C99.Proof.ROExt m m_after →
      Post m args rv m_after →
      Post m_clean args rv (dropBlks m_after bs))
    (hspec : FuncBodySpec prog cfg ext fn Pre Post) :
    C99.Proof.VCGen.CallSpec prog cfg ext :=
  callWPTermSpec_to_vcCallSpec
    (Pre := fun m _ args => Pre m args)
    (Post := fun m os args rv m' os' => os' = os ∧ C99.Proof.ROExt m m' ∧ Post m args rv m')
    hfn hnonvar hsimp hvoid
    (fun m _ args ret m' _ hp ⟨_, hro, hpo⟩ => hret m args ret m' hp hro hpo)
    (fun bs h1 h2 h3 h4 h5 hp => hpre_mono bs h1 h2 h3 h4 h5 hp)
    (post_stack_of_preserve
      (pre := fun m _ args => Pre m args)
      (post := fun m os args rv m' os' => os' = os ∧ C99.Proof.ROExt m m' ∧ Post m args rv m')
      fun ⟨_, hro, _⟩ => roExt_stack_pres hro)
    (fun bs h1 h2 h3 h4 h5 hp ⟨hos, hro, hpo⟩ =>
      ⟨hos, roExt_post_stack_drop bs h1 h2 h3 hro, hpost_drop bs h1 h2 h3 h4 h5 hp hro hpo⟩)
    hspec.to_callWPTermSpec

def callSafeSpec_to_vcCallSafeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns fn.name = some fn)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hvoid : fn.retTy.isVoid = true → fn.retTy = .void)
    (hret : ∀ m os args ret m' os', Pre m os args → Post m os args ret m' os' →
      if fn.retTy.isVoid then ret = .void else Sem.castVal m' fn.retTy ret = some ret)
    (hpre_mono : ∀ {m_clean m : Mem} {os : OSState} {args : List Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean os args → Pre m os args)
    (hpost_stack : ∀ {m_clean m m' : Mem} {os os' : OSState} {args : List Val} {rv : Val} (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean os args →
      Post m os args rv m' os' →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b ∈ bs, ∀ blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack))
    (hpost_drop : ∀ {m_clean m m_after : Mem} {os os' : OSState} {args : List Val} {rv : Val}
      (bs : List BlockId),
      m_clean.nextBlock ≤ m.nextBlock →
      (∀ b ∈ bs, m_clean.blocks b = none) →
      (∀ b, b ∉ bs → m.blocks b = m_clean.blocks b) →
      (∀ b ∈ bs, b < m.nextBlock) →
      (∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack) →
      Pre m_clean os args →
      Post m os args rv m_after os' →
      Post m_clean os args rv (dropBlks m_after bs) os')
    (hspec : Zlib.Proof.CallSafeSpec prog cfg ext fn Pre Post) :
    C99.Proof.VCGen.CallSafeSpec prog cfg ext where
  sym := fn.name
  paramTys := fn.params.map (·.ty)
  retTy := fn.retTy
  variadic := fn.variadic
  pre := Pre
  post := Post
  pre_mono := hpre_mono
  post_stack := hpost_stack
  post_drop := hpost_drop
  sound_term := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q hbud hd _ _ hco hpre hcont
    rw [hnonvar] at hco
    have hlenC := coerceCallArgs_length_param hco
    simp only [List.length_map] at hlenC
    have htake : List.take fn.params.length args = args := List.take_of_length_le (by omega)
    have hawt : ArgsHaveCTy (fn.params.map (·.ty)) false args :=
      coerceCallArgs_produces_argsWellTyped hco
    have hex0 : ∃ callEnv0 callBlks0 m0',
        Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip args)
          (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') :=
      pushCallParams_exists_base0 prog.tags hsimp hawt
    have hcoV : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some args := by
      simpa [hnonvar] using hco
    refine C99.Proof.WPTerm.of_call_internal hd hfn hcoV (by simpa [htake] using hex0) ?_
    intro base callEnv callBlks m1 hpush
    rw [htake] at hpush
    let Q_bot : Val → Mem → OSState → Prop := fun rv m' os' => Post m os args rv m' os'
    have hwps_bot : Zlib.Proof.WPSafe prog cfg ext Q_bot
        (.running (.stmt fn.body) callEnv callBlks m1 os
          (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) := by
      refine hspec args [] [] m m1 os base callEnv callBlks [] .returnVal (.stop fn.retTy) Q_bot
        hpre hlenC hpush ?_
      intro ret m' os' hpo
      have hrm := hret m os args ret m' os' hpre hpo
      by_cases hv : fn.retTy.isVoid = true
      · simp only [hv, ↓reduceIte] at hrm; subst hrm
        exact Zlib.Proof.WPSafe.of_det (stepDet_ret_stop_void prog cfg [] fn.retTy fn.retTy m' os' hv)
          (Zlib.Proof.WPSafe.returned hpo)
      · have hnv : fn.retTy.isVoid = false := Bool.eq_false_iff.mpr hv
        simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hrm
        exact Zlib.Proof.WPSafe.of_det (stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy ret ret m' os' hnv hrm)
          (Zlib.Proof.WPSafe.returned hpo)
    have ht_bot : C99.Proof.WPTerm prog cfg ext Q_bot
        (.running (.stmt fn.body) callEnv callBlks m1 os
          (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) :=
      hwps_bot.2.1 hbud
    exact wpTerm_runStateLift_wpTerm hvoid ht_bot (RunStateLift.inside ContLift.base) hcont
  sound_safe := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q R hd _ _ hco hpre hcont
    rw [hnonvar] at hco
    have hlenC := coerceCallArgs_length_param hco
    simp only [List.length_map] at hlenC
    have htake : List.take fn.params.length args = args := List.take_of_length_le (by omega)
    have hawt : ArgsHaveCTy (fn.params.map (·.ty)) false args :=
      coerceCallArgs_produces_argsWellTyped hco
    have hex0 : ∃ callEnv0 callBlks0 m0',
        Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip args)
          (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') :=
      pushCallParams_exists_base0 prog.tags hsimp hawt
    have hcoV : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some args := by
      simpa [hnonvar] using hco
    refine SafeUntil.of_call_internal hd hfn hcoV (by simpa [htake] using hex0) ?_
    intro base callEnv callBlks m1 hpush
    rw [htake] at hpush
    let Q_bot : Val → Mem → OSState → Prop := fun rv m' os' => Post m os args rv m' os'
    have hwps_bot : Zlib.Proof.WPSafe prog cfg ext Q_bot
        (.running (.stmt fn.body) callEnv callBlks m1 os
          (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) := by
      refine hspec args [] [] m m1 os base callEnv callBlks [] .returnVal (.stop fn.retTy) Q_bot
        hpre hlenC hpush ?_
      intro ret m' os' hpo
      have hrm := hret m os args ret m' os' hpre hpo
      by_cases hv : fn.retTy.isVoid = true
      · simp only [hv, ↓reduceIte] at hrm; subst hrm
        exact Zlib.Proof.WPSafe.of_det (stepDet_ret_stop_void prog cfg [] fn.retTy fn.retTy m' os' hv)
          (Zlib.Proof.WPSafe.returned hpo)
      · have hnv : fn.retTy.isVoid = false := Bool.eq_false_iff.mpr hv
        simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hrm
        exact Zlib.Proof.WPSafe.of_det (stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy ret ret m' os' hnv hrm)
          (Zlib.Proof.WPSafe.returned hpo)
    let Inv : Sem.RunState → Prop := fun s2 =>
      (∃ s1, Sem.Safe prog cfg ext s1 ∧
        (∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext) s1 (.returned r m'' os'') → Q_bot r m'' os'') ∧
        RunStateLift env blks fn.retTy fn.body fs ctx k s1 s2) ∨
      C99.Proof.VCGen.SafeUntil prog cfg ext Q R s2
    refine ⟨Inv, Or.inl ⟨_, hwps_bot.1, hwps_bot.2.2, RunStateLift.inside ContLift.base⟩, ?_⟩
    intro u hu
    rcases hu with ⟨s1, hs1_safe, hs1_post, hlf⟩ | hsu
    · cases hlf with
      | @exitedVoid m' os' rty hrt hrty =>
        have hrt_eq : fn.retTy = .void := hvoid hrt
        have hrty_eq : rty = fn.retTy := by
          rcases hrty with rfl | rfl
          · exact hrt_eq.symm
          · rfl
        have hqb : Q_bot .void m' os' :=
          hs1_post .void m' os' (.tail (.refl _) (.det (stepDet_ret_stop_void prog cfg [] rty fn.retTy m' os' hrt)))
        have hcont' : C99.Proof.VCGen.SafeUntil prog cfg ext Q R
            (.running (.expr (.ret (.rval .void rty) fs) ctx []) env blks m' os' k) := by
          rw [hrty_eq]
          exact hcont .void m' os' hqb
        rcases SafeUntil.cases hcont' with hr | ⟨hq, hnot, hrun⟩
        · exact Or.inl hr
        · exact Or.inr ⟨hq, hnot, fun s' hst => Or.inr (hrun s' hst)⟩
      | @exitedVal v m' os' hnot hcast =>
        have hqb : Q_bot v m' os' :=
          hs1_post v m' os' (.tail (.refl _) (.det (stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy v v m' os' hnot hcast)))
        rcases SafeUntil.cases (hcont v m' os' hqb) with hr | ⟨hq, hnot', hrun⟩
        · exact Or.inl hr
        · exact Or.inr ⟨hq, hnot', fun s' hst => Or.inr (hrun s' hst)⟩
      | @exitedUndef m' os' hnot =>
        exact False.elim (hs1_safe .ub (.tail (.refl _) (.det_ub (stepDet_ret_stop_undef prog cfg fn.retTy m' os' hnot))) rfl)
      | @inside ctrl e b m_ os_ k1 k2 hk =>
        refine Or.inr ⟨(fun _ _ _ heq => by cases heq), Bool.false_ne_true, fun s2' hs2' => Or.inl ?_⟩
        have hd := stepDet_contLift (prog := prog) (cfg := cfg) (ctrl := ctrl)
          (e := e) (b := b) (m := m_) (os := os_) hk
        cases hd1 : Sem.stepDet prog cfg (.running ctrl e b m_ os_ k1) with
        | none =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd
          exact False.elim (hs1_safe .ub (.tail (.refl _) (.det_ub hd1)) rfl)
        | some d1 =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd
          cases d1 with
          | next s1_next =>
            obtain ⟨s2_det, hd2, hlift'⟩ := hd
            cases hs2' with
            | det hd2' =>
              rw [hd2] at hd2'; cases hd2'
              exact ⟨s1_next, fun w hw => hs1_safe w (star_head (.det hd1) hw),
                fun r mw osw hw => hs1_post r mw osw (star_head (.det hd1) hw), hlift'⟩
            | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | allocStr str fs' ctx' mods' e' b' m'' os'' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | strLit hd2' hsz halloc =>
              rw [hd2] at hd2'; cases hd2'
              have hstep1 : Sem.Step prog cfg ext (.running ctrl e b m_ os_ k1) _ := .strLit hd1 hsz halloc
              exact ⟨_, fun w hw => hs1_safe w (star_head hstep1 hw),
                fun r mw osw hw => hs1_post r mw osw (star_head hstep1 hw), RunStateLift.inside hk'⟩
            | det hd2' | det_ub hd2' | localDecl hd2' | localDecl_ub hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | allocLocal d i? rest e' b' m'' os'' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | localDecl hd2' hsz hal hba halloc hwr =>
              rw [hd2] at hd2'; cases hd2'
              have hstep1 : Sem.Step prog cfg ext (.running ctrl e b m_ os_ k1) _ := .localDecl hd1 hsz hal hba halloc hwr
              exact ⟨_, fun w hw => hs1_safe w (star_head hstep1 hw),
                fun r mw osw hw => hs1_post r mw osw (star_head hstep1 hw), RunStateLift.inside hk'⟩
            | localDecl_ub hd2' hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim (hs1_safe .ub (.tail (.refl _) (.localDecl_ub hd1 hbad)) rfl)
            | det hd2' | det_ub hd2' | strLit hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | callFn sym fty args_ fs' ctx' e' b' m'' os'' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | call_internal hd2' hfn' hcoerce hpush' =>
              rw [hd2] at hd2'; cases hd2'
              have hstep1 : Sem.Step prog cfg ext (.running ctrl e b m_ os_ k1) _ := .call_internal hd1 hfn' hcoerce hpush'
              exact ⟨_, fun w hw => hs1_safe w (star_head hstep1 hw),
                fun r mw osw hw => hs1_post r mw osw (star_head hstep1 hw), RunStateLift.inside (ContLift.callFrame hk')⟩
            | call_internal_ub hd2' hfn' hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim (hs1_safe .ub (.tail (.refl _) (.call_internal_ub hd1 hfn' hbad)) rfl)
            | call_ext hd2' hnfn hsig hcoerce hext =>
              rw [hd2] at hd2'; cases hd2'
              rename_i out'
              cases out' with
              | ub =>
                exact False.elim (hs1_safe .ub (.tail (.refl _) (.call_ext hd1 hnfn hsig hcoerce hext)) rfl)
              | ok ret m''' os''' =>
                have hstep1 : Sem.Step prog cfg ext (.running ctrl e b m_ os_ k1) _ := .call_ext hd1 hnfn hsig hcoerce hext
                exact ⟨_, fun w hw => hs1_safe w (star_head hstep1 hw),
                  fun r mw osw hw => hs1_post r mw osw (star_head hstep1 hw), RunStateLift.inside hk'⟩
            | call_ext_ub hd2' hnfn hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim (hs1_safe .ub (.tail (.refl _) (.call_ext_ub hd1 hnfn hbad)) rfl)
            | det hd2' | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
    · rcases SafeUntil.cases hsu with hr | ⟨hq, hnot, hrun⟩
      · exact Or.inl hr
      · exact Or.inr ⟨hq, hnot, fun s' hst => Or.inr (hrun s' hst)⟩

end ReverseAdapters

/-! ## 3. `SpecEnv` / `SafeSpecEnv` Composition Builders -/

def emptySpecEnv (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :
    C99.Proof.VCGen.SpecEnv prog cfg ext :=
  fun _ => none

@[simp] theorem emptySpecEnv_apply (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) (sym : String) :
    emptySpecEnv prog cfg ext sym = none := rfl

def insertSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SpecEnv prog cfg ext) :
    C99.Proof.VCGen.SpecEnv prog cfg ext :=
  fun sym => if sym == c.sym then some c else specs sym

@[simp] theorem insertSpec_apply {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SpecEnv prog cfg ext) (sym : String) :
    insertSpec c specs sym = if sym == c.sym then some c else specs sym := rfl

@[simp] theorem insertSpec_self {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SpecEnv prog cfg ext) :
    insertSpec c specs c.sym = some c := by
  simp [insertSpec]

@[simp] theorem insertSpec_ne {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SpecEnv prog cfg ext) {sym : String} (hne : sym ≠ c.sym) :
    insertSpec c specs sym = specs sym := by
  simp [insertSpec, hne]

def emptySafeSpecEnv (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :
    C99.Proof.VCGen.SafeSpecEnv prog cfg ext :=
  fun _ => none

@[simp] theorem emptySafeSpecEnv_apply (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) (sym : String) :
    emptySafeSpecEnv prog cfg ext sym = none := rfl

def insertSafeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSafeSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SafeSpecEnv prog cfg ext) :
    C99.Proof.VCGen.SafeSpecEnv prog cfg ext :=
  fun sym => if sym == c.sym then some c else specs sym

@[simp] theorem insertSafeSpec_apply {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSafeSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SafeSpecEnv prog cfg ext) (sym : String) :
    insertSafeSpec c specs sym = if sym == c.sym then some c else specs sym := rfl

@[simp] theorem insertSafeSpec_self {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSafeSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SafeSpecEnv prog cfg ext) :
    insertSafeSpec c specs c.sym = some c := by
  simp [insertSafeSpec]

@[simp] theorem insertSafeSpec_ne {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    (c : C99.Proof.VCGen.CallSafeSpec prog cfg ext)
    (specs : C99.Proof.VCGen.SafeSpecEnv prog cfg ext) {sym : String} (hne : sym ≠ c.sym) :
    insertSafeSpec c specs sym = specs sym := by
  simp [insertSafeSpec, hne]

/-! ## 4. Ready-to-Use VCGen Callee Wrappers (Wave 1 & Indirect Callbacks) -/

section Wave1Wrappers

private theorem readVal_blocks_eq_same {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64} {ty : CTy}
    (hb : m2.blocks b = m1.blocks b) :
    Sem.readVal tags m2 b off ty = Sem.readVal tags m1 b off ty := by
  have hr : ∀ len, m2.readBytes b off len = m1.readBytes b off len := by
    intro len
    unfold Mem.readBytes
    rw [hb]
  unfold Sem.readVal
  cases ty.unqual <;> simp only [hb, hr]

private theorem readVal_some_block_ne_none {tags : TypeEnv} {m : Mem} {b : BlockId}
    {off : Int64} {ty : CTy} {v : Val}
    (hnarr : ∀ el n, ty.unqual ≠ .array el n)
    (hr : Sem.readVal tags m b off ty = some v) :
    ∃ blk, m.blocks b = some blk := by
  cases hb : m.blocks b with
  | some blk => exact ⟨blk, rfl⟩
  | none =>
    unfold Sem.readVal at hr
    cases hu : ty.unqual with
    | array el n => exact False.elim (hnarr el n hu)
    | «int» _ | enumTy _ _ =>
      simp [hu, CTy.intKind?, CTy.unqual, hb, bind, Option.bind] at hr
    | ptr _ | fnPtr _ _ _ => simp [hu, hb, bind, Option.bind] at hr
    | vaList => simp [hu, Mem.readBytes, hb, bind, Option.bind] at hr
    | _ => simp [hu] at hr

private theorem readable_of_stack_mono {m_clean m : Mem} {p : Val} {len : Nat}
    (bs : List BlockId)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (h : Zlib.Spec.Readable m_clean p len) :
    Zlib.Spec.Readable m p len := by
  rcases h with ⟨b, off, blk, rfl, hblk, hin, hconcr⟩
  have hnb : b ∉ bs := fun hm => by rw [h2 b hm] at hblk; cases hblk
  exact ⟨b, off, blk, rfl, by rw [h3 b hnb]; exact hblk, hin, hconcr⟩

private theorem zcallocPost_stack_pres {m m' : Mem} {items size : BitVec 32} {ret : Val}
    (hp : ZcallocPost m items size ret m') :
    m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk := by
  rcases hp with ⟨_, hro, hblks⟩ | ⟨bid, _, _, hnone, hle, hnext, _, _, _, _, _, _, _, _, hne⟩
  · refine ⟨hro.1, fun b blk hb _ => by rw [hblks b]; exact hb⟩
  · refine ⟨by rw [hnext]; exact Nat.le_trans hle (Nat.le_succ bid), fun b blk hb _ => ?_⟩
    have hbb : b ≠ bid := fun heq => by rw [heq, hnone] at hb; cases hb
    rw [hne b hbb]; exact hb

private theorem zcallocPost_drop {m_clean m m_after : Mem} {items size : BitVec 32} {ret : Val}
    (bs : List BlockId)
    (h1 : m_clean.nextBlock ≤ m.nextBlock)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (h5 : ∀ b ∈ bs, ∃ blk, m.blocks b = some blk ∧ blk.kind = .stack)
    (hp : ZcallocPost m items size ret m_after) :
    ZcallocPost m_clean items size ret (dropBlks m_after bs) := by
  rcases hp with ⟨rfl, hro, hblks⟩ |
      ⟨bid, blk, rfl, hnone, hle, hnext, hsome, hk, hperm, hsz, hal, hba, hbytes, hlt, hne⟩
  · refine Or.inl ⟨rfl, roExt_post_stack_drop bs h1 h2 h3 hro, fun b => ?_⟩
    by_cases hm : b ∈ bs
    · rw [h2 b hm]; simp [dropBlks, hm]
    · rw [dropBlks_blocks_not_mem m_after bs hm, hblks b, h3 b hm]
  · have hbid_nmem : bid ∉ bs := fun hm => by
      obtain ⟨blk0, hb0, _⟩ := h5 bid hm
      rw [hnone] at hb0; cases hb0
    have hnone_clean : m_clean.blocks bid = none := by rw [← h3 bid hbid_nmem]; exact hnone
    refine Or.inr ⟨bid, blk, rfl, hnone_clean, Nat.le_trans h1 hle, ?_, ?_, hk, hperm, hsz, hal, hba, hbytes, ?_, ?_⟩
    · simp [dropBlks, hnext]
    · rw [dropBlks_blocks_not_mem m_after bs hbid_nmem]; exact hsome
    · intro b hb_lt
      by_cases hm : b ∈ bs
      · rw [h2 b hm]; simp [dropBlks, hm]
      · rw [dropBlks_blocks_not_mem m_after bs hm, hlt b (Nat.lt_of_lt_of_le hb_lt h1), h3 b hm]
    · intro b hb_ne
      by_cases hm : b ∈ bs
      · rw [h2 b hm]; simp [dropBlks, hm]
      · rw [dropBlks_blocks_not_mem m_after bs hm, hne b hb_ne, h3 b hm]

def zcalloc_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) :=
  heapBodySpec_to_vcCallSpec (prog_fns_zcalloc hlib) rfl zcalloc_params_simple
    (by simp [Zlib.Zutil.zutilTU_fn_zcalloc, CTy.isVoid, CTy.unqual])
    (by
      intro m args ret m' hpre hpo
      rcases hpre with ⟨op, items, size, rfl, _⟩
      rcases hpo with ⟨rfl, _⟩ | ⟨bid, _, rfl, _⟩ <;> rfl)
    (fun _ _ _ _ _ _ hp => hp)
    (fun bs _ _ _ _ _ hp hpo => by
      rcases hp with ⟨op, items, size, rfl, _⟩
      have hpres := zcallocPost_stack_pres hpo
      exact ⟨hpres.1, fun b _ blk hb hk => hpres.2 b blk hb hk,
        fun b blk hb hk => ⟨blk, hpres.2 b blk hb hk, hk⟩⟩)
    (fun bs h1 h2 h3 _ h5 hp hpo => by
      rcases hp with ⟨op, items, size, rfl, _⟩
      exact zcallocPost_drop bs h1 h2 h3 h5 hpo)
    (zcalloc_spec hlib)

def zcalloc_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) :=
  (zcalloc_vcTermSpec hlib).toSafeSpec

private theorem freePre_mono {m_clean m : Mem} {ptr : Val}
    (bs : List BlockId)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hp : FreePre m_clean ptr) :
    FreePre m ptr := by
  rcases hp with rfl | ⟨b, blk, rfl, hblk, hkind⟩
  · exact Or.inl rfl
  · have hnb : b ∉ bs := fun hm => by rw [h2 b hm] at hblk; cases hblk
    exact Or.inr ⟨b, blk, rfl, by rw [h3 b hnb]; exact hblk, hkind⟩

private theorem zcfreePost_stack_pres {m m' : Mem} {ptr ret : Val}
    (hp : FreePre m ptr) (hpo : ZcfreePost m ptr ret m') :
    m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk := by
  rcases hpo with ⟨rfl, hrest⟩
  rcases hp with rfl | ⟨b0, blk0, rfl, hblk0, hkind0⟩
  · rcases hrest with ⟨_, hro, hblks⟩ | ⟨_, _, heq, _⟩
    · exact ⟨hro.1, fun b blk hb _ => by rw [hblks b]; exact hb⟩
    · cases heq
  · rcases hrest with ⟨heq, _⟩ | ⟨bid, _, hinj, _, _, hlt, _, hne⟩
    · cases heq
    · cases hinj
      refine ⟨hlt, fun b blk hb hk => ?_⟩
      have hne0 : b ≠ b0 := fun heq => by
        subst heq
        rw [hblk0] at hb; cases hb
        rw [hkind0] at hk; cases hk
      rw [hne b hne0]; exact hb

private theorem zcfreePost_drop {m_clean m m_after : Mem} {ptr ret : Val}
    (bs : List BlockId)
    (h1 : m_clean.nextBlock ≤ m.nextBlock)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hp : FreePre m_clean ptr)
    (hpo : ZcfreePost m ptr ret m_after) :
    ZcfreePost m_clean ptr ret (dropBlks m_after bs) := by
  rcases hpo with ⟨rfl, hrest⟩
  refine ⟨rfl, ?_⟩
  rcases hp with rfl | ⟨b0, blk0, rfl, hblk0, hkind0⟩
  · rcases hrest with ⟨_, hro, hblks⟩ | ⟨_, _, heq, _⟩
    · refine Or.inl ⟨rfl, roExt_post_stack_drop bs h1 h2 h3 hro, fun b => ?_⟩
      by_cases hm : b ∈ bs
      · rw [h2 b hm]; simp [dropBlks, hm]
      · rw [dropBlks_blocks_not_mem m_after bs hm, hblks b, h3 b hm]
    · cases heq
  · rcases hrest with ⟨heq, _⟩ | ⟨bid, blk_m, hinj, hblk_m, hkind_m, hlt, hnone, hne⟩
    · cases heq
    · cases hinj
      have hnb : b0 ∉ bs := fun hm => by rw [h2 b0 hm] at hblk0; cases hblk0
      refine Or.inr ⟨b0, blk0, rfl, hblk0, hkind0, Nat.le_trans h1 hlt, ?_, ?_⟩
      · rw [dropBlks_blocks_not_mem m_after bs hnb]; exact hnone
      · intro b' hb_ne
        by_cases hm : b' ∈ bs
        · rw [h2 b' hm]; simp [dropBlks, hm]
        · rw [dropBlks_blocks_not_mem m_after bs hm, hne b' hb_ne, h3 b' hm]

def zcfree_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) :=
  heapBodySpec_to_vcCallSpec (prog_fns_zcfree hlib) rfl zcfree_params_simple
    (by simp [Zlib.Zutil.zutilTU_fn_zcfree, CTy.isVoid])
    (by
      intro m args ret m' hpre hpo
      rcases hpre with ⟨op, ptr, rfl, _, _⟩
      exact hpo.1)
    (fun bs _ h2 h3 _ _ hp => by
      rcases hp with ⟨op, ptr, rfl, hop, hf⟩
      exact ⟨op, ptr, rfl, hop, freePre_mono bs h2 h3 hf⟩)
    (fun bs _ h2 h3 _ _ hp hpo => by
      rcases hp with ⟨op, ptr, rfl, _, hf⟩
      have hf' := freePre_mono bs h2 h3 hf
      have hpres := zcfreePost_stack_pres hf' hpo
      exact ⟨hpres.1, fun b _ blk hb hk => hpres.2 b blk hb hk,
        fun b blk hb hk => ⟨blk, hpres.2 b blk hb hk, hk⟩⟩)
    (fun bs h1 h2 h3 _ _ hp hpo => by
      rcases hp with ⟨op, ptr, rfl, _, hf⟩
      exact zcfreePost_drop bs h1 h2 h3 hf hpo)
    (zcfree_spec hlib)

def zcfree_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) :=
  (zcfree_vcTermSpec hlib).toSafeSpec

private theorem zErrmsgReady_mono {tags : TypeEnv} {gEnv : Env} {m_clean m : Mem}
    (bs : List BlockId)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (hz : ZErrmsgReady tags gEnv m_clean) :
    ZErrmsgReady tags gEnv m := by
  rcases hz with ⟨b_arr, blk, hlu, hblk, hp, hk, hs, ha, harr⟩
  have hnb : b_arr ∉ bs := fun hm => by rw [h2 b_arr hm] at hblk; cases hblk
  have hbar_eq : m.blocks b_arr = m_clean.blocks b_arr := h3 b_arr hnb
  refine ⟨b_arr, blk, hlu, by rw [hbar_eq]; exact hblk, hp, hk, hs, ha, ?_⟩
  intro i hi
  obtain ⟨sb, sblk, len, hrs, hsblk, hsp, hsk, hlen⟩ := harr i hi
  have hsnb : sb ∉ bs := fun hm => by rw [h2 sb hm] at hsblk; cases hsblk
  refine ⟨sb, sblk, len, ?_, by rw [h3 sb hsnb]; exact hsblk, hsp, hsk, ?_⟩
  · rw [readVal_blocks_eq_same hbar_eq]; exact hrs
  · rw [C99.Proof.VCGen.strlenAt_of_blocks_eq (h3 sb hsnb)]; exact hlen

def zError_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_zError hlib) rfl zError_params_simple
    (by intro h; simp [Zlib.Zutil.zutilTU_fn_zError, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨hcs, sb, sblk, rfl, hblk, hperm, hk⟩
      simp [Zlib.Zutil.zutilTU_fn_zError, CTy.isVoid, CTy.unqual, Sem.castVal, CTy.intKind?])
    (fun bs _ h2 h3 _ _ hp => by
      rcases hp with ⟨hz, err, rfl⟩
      exact ⟨zErrmsgReady_mono bs h2 h3 hz, err, rfl⟩)
    (fun bs _ _ _ h4 h5 _ hro hpo => by
      rcases hpo with ⟨hcs, sb, sblk, rfl, hsblk, hperm, hk⟩
      have hsnb : sb ∉ bs := by
        intro hm
        obtain ⟨blk0, hblk0, hstk0⟩ := h5 sb hm
        have heq := hro.2.1 sb (h4 sb hm)
        rw [hsblk, hblk0, Option.some.injEq] at heq
        rw [← heq, hk] at hstk0
        cases hstk0
      rcases hcs with ⟨b', off', len', hpeq, hlen'⟩
      cases hpeq
      refine ⟨⟨sb, 0, len', rfl, ?_⟩, sb, sblk, rfl, ?_, hperm, hk⟩
      · rw [C99.Proof.VCGen.strlenAt_of_blocks_eq (dropBlks_blocks_not_mem _ bs hsnb)]; exact hlen'
      · rw [dropBlks_blocks_not_mem _ bs hsnb]; exact hsblk)
    (zError_spec hlib)

def zError_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (zError_vcTermSpec hlib).toSafeSpec

def zlibCompileFlags_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_zlibCompileFlags hlib) rfl
    (fun _ hp => by cases hp)
    (by intro h; simp [Zlib.Zutil.zutilTU_fn_zlibCompileFlags, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Zutil.zutilTU_fn_zlibCompileFlags, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ _ h => h)
    zlibCompileFlags_spec

def zlibCompileFlags_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (zlibCompileFlags_vcTermSpec hlib).toSafeSpec

def compressBound_z_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_compressBound_z hlib) rfl
    (fun p hp => by
      simp only [Zlib.Compress.compressTU_fn_compressBound_z, List.mem_singleton] at hp
      subst hp
      simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Compress.compressTU_fn_compressBound_z, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Compress.compressTU_fn_compressBound_z, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ _ h => h)
    compressBound_z_spec

def compressBound_z_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (compressBound_z_vcTermSpec hlib).toSafeSpec

def compressBound_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_compressBound hlib) rfl
    (fun p hp => by
      simp only [Zlib.Compress.compressTU_fn_compressBound, List.mem_singleton] at hp
      subst hp
      simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Compress.compressTU_fn_compressBound, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Compress.compressTU_fn_compressBound, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ _ h => h)
    (compressBound_spec hlib)

def compressBound_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (compressBound_vcTermSpec hlib).toSafeSpec

def adler32_combine__vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_adler32_combine_ hlib) rfl
    (fun p hp => by
      simp only [Zlib.Adler32.adler32TU_fn_adler32_combine_, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Adler32.adler32TU_fn_adler32_combine_, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Adler32.adler32TU_fn_adler32_combine_, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ _ h => h)
    (adler32_combine__spec prog ext)

def adler32_combine__vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (adler32_combine__vcTermSpec hlib).toSafeSpec

def adler32_z_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_adler32_z hlib) rfl
    (fun p hp => by
      simp only [Zlib.Adler32.adler32TU_fn_adler32_z, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Adler32.adler32TU_fn_adler32_z, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Adler32.adler32TU_fn_adler32_z, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun bs _ h2 h3 _ _ hp => by
      rcases hp with ⟨ad, buf, len, rfl, hptr, hr1, hrneq⟩
      refine ⟨ad, buf, len, rfl, hptr, fun h => readable_of_stack_mono bs h2 h3 (hr1 h), fun h => ?_⟩
      rcases hrneq h with rfl | h0 | hrb
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (readable_of_stack_mono bs h2 h3 hrb)))
    (fun _ _ _ _ _ _ _ _ h => h)
    (adler32_z_spec prog ext)

def adler32_z_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (adler32_z_vcTermSpec hlib).toSafeSpec

def adler32_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_adler32 hlib) rfl
    (fun p hp => by
      simp only [Zlib.Adler32.adler32TU_fn_adler32, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Adler32.adler32TU_fn_adler32, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Adler32.adler32TU_fn_adler32, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun bs _ h2 h3 _ _ hp => by
      rcases hp with ⟨ad, buf, len, rfl, hptr, hr1, hrneq⟩
      refine ⟨ad, buf, len, rfl, hptr, fun h => readable_of_stack_mono bs h2 h3 (hr1 h), fun h => ?_⟩
      rcases hrneq h with rfl | h0 | hrb
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (readable_of_stack_mono bs h2 h3 hrb)))
    (fun _ _ _ _ _ _ _ _ h => h)
    (adler32_spec ext hlib)

def adler32_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (adler32_vcTermSpec hlib).toSafeSpec

private theorem crcTableValid_mono {prog : Prog} {gEnv : Env} {m_clean m : Mem}
    (bs : List BlockId)
    (h1 : m_clean.nextBlock ≤ m.nextBlock)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (ht : CrcTableValid prog gEnv m_clean) :
    CrcTableValid prog gEnv m := by
  rcases ht with ⟨b, hlu, hlt, herr⟩
  obtain ⟨bv0, hrv0⟩ := herr 0 (by decide)
  obtain ⟨blk, hblk⟩ := readVal_some_block_ne_none (fun _ _ h => by cases h) hrv0
  have hnb : b ∉ bs := fun hm => by rw [h2 b hm] at hblk; cases hblk
  refine ⟨b, hlu, Nat.lt_of_lt_of_le hlt h1, fun idx hi => ?_⟩
  obtain ⟨bv, hrv⟩ := herr idx hi
  exact ⟨bv, by rw [readVal_blocks_eq_same (h3 b hnb)]; exact hrv⟩

private theorem crcBraidTableValid_mono {prog : Prog} {gEnv : Env} {m_clean m : Mem}
    {name : String} (bs : List BlockId)
    (h1 : m_clean.nextBlock ≤ m.nextBlock)
    (h2 : ∀ b ∈ bs, m_clean.blocks b = none)
    (h3 : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (ht : CrcBraidTableValid prog gEnv m_clean name) :
    CrcBraidTableValid prog gEnv m name := by
  rcases ht with ⟨b, hlu, hlt, herr⟩
  obtain ⟨bv0, hrv0⟩ := herr 0 (by decide) 0 (by decide)
  obtain ⟨blk, hblk⟩ := readVal_some_block_ne_none (fun _ _ h => by cases h) hrv0
  have hnb : b ∉ bs := fun hm => by rw [h2 b hm] at hblk; cases hblk
  refine ⟨b, hlu, Nat.lt_of_lt_of_le hlt h1, fun row hr idx hi => ?_⟩
  obtain ⟨bv, hrv⟩ := herr row hr idx hi
  exact ⟨bv, by rw [readVal_blocks_eq_same (h3 b hnb)]; exact hrv⟩

theorem crc32ZPre_of_baseInv {prog : Prog} {gEnv : Env} {m0 m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os)
    {crc : BitVec 64} {buf : Val} {len : BitVec 64}
    (hptr : buf = .null ∨ ∃ pb poff, buf = .ptr pb poff)
    (hrd : buf = .null ∨ len.toNat = 0 ∨ Zlib.Spec.Readable m buf len.toNat) :
    Crc32ZPre prog gEnv m [.int .u64 crc, buf, .int .u64 len] :=
  ⟨crc, buf, len, rfl, hptr, hrd,
    CrcTableValid.of_baseInv hlib hb (LocalFrameMem.init m),
    CrcBraidTableValid.of_baseInv_2 hlib hb (LocalFrameMem.init m),
    CrcBraidTableValid.of_baseInv_5 hlib hb (LocalFrameMem.init m)⟩

theorem crc32Pre_of_baseInv {prog : Prog} {gEnv : Env} {m0 m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m os)
    {crc : BitVec 64} {buf : Val} {len : BitVec 32}
    (hptr : buf = .null ∨ ∃ pb poff, buf = .ptr pb poff)
    (hrd : buf = .null ∨ len.toNat = 0 ∨ Zlib.Spec.Readable m buf len.toNat) :
    Crc32Pre prog gEnv m [.int .u64 crc, buf, .int .u32 len] :=
  ⟨crc, buf, len, rfl, hptr, hrd,
    CrcTableValid.of_baseInv hlib hb (LocalFrameMem.init m),
    CrcBraidTableValid.of_baseInv_2 hlib hb (LocalFrameMem.init m),
    CrcBraidTableValid.of_baseInv_5 hlib hb (LocalFrameMem.init m)⟩

def crc32_z_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_crc32_z hlib) rfl
    (fun p hp => by
      simp only [Zlib.Crc32.crc32TU_fn_crc32_z, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Crc32.crc32TU_fn_crc32_z, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Crc32.crc32TU_fn_crc32_z, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun bs h1 h2 h3 _ _ hp => by
      rcases hp with ⟨crc, buf, len, rfl, hptr, hrd, ht0, hb2, hb5⟩
      refine ⟨crc, buf, len, rfl, hptr, ?_, crcTableValid_mono bs h1 h2 h3 ht0,
        crcBraidTableValid_mono bs h1 h2 h3 hb2, crcBraidTableValid_mono bs h1 h2 h3 hb5⟩
      rcases hrd with rfl | h0 | hr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (readable_of_stack_mono bs h2 h3 hr)))
    (fun _ _ _ _ _ _ _ _ h => h)
    (crc32_z_spec ext hlib)

def crc32_z_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (crc32_z_vcTermSpec hlib).toSafeSpec

def crc32_vcTermSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSpec prog Zlib.Spec.zlibPointerConfig ext :=
  funcBodySpec_to_vcCallSpec (prog_fns_crc32 hlib) rfl
    (fun p hp => by
      simp only [Zlib.Crc32.crc32TU_fn_crc32, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual])
    (by intro h; simp [Zlib.Crc32.crc32TU_fn_crc32, CTy.isVoid, CTy.unqual] at h)
    (by
      intro m args ret m' _ _ hpo
      rcases hpo with ⟨bv, rfl⟩
      simpa [Zlib.Crc32.crc32TU_fn_crc32, CTy.isVoid, castVal_unqual, CTy.unqual] using
        C99.Proof.castVal_int_self m' .u64 bv)
    (fun bs h1 h2 h3 _ _ hp => by
      rcases hp with ⟨crc, buf, len, rfl, hptr, hrd, ht0, hb2, hb5⟩
      refine ⟨crc, buf, len, rfl, hptr, ?_, crcTableValid_mono bs h1 h2 h3 ht0,
        crcBraidTableValid_mono bs h1 h2 h3 hb2, crcBraidTableValid_mono bs h1 h2 h3 hb5⟩
      rcases hrd with rfl | h0 | hr
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (readable_of_stack_mono bs h2 h3 hr)))
    (fun _ _ _ _ _ _ _ _ h => h)
    (crc32_spec ext hlib)

def crc32_vcSpec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} (hlib : InitLibzProps prog gEnv m0 os0) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext :=
  (crc32_vcTermSpec hlib).toSafeSpec

end Wave1Wrappers

section IndirectCallbackWrappers

private def inFuncAllowed (tags : TypeEnv) (m0 : Mem) (v : ClientView)
    (owned userWrite : BlockSet) (os : OSState) (m : Mem) (args : List Val) : BlockSet :=
  fun b =>
    ¬ Zlib.Spec.LibProtected m0 owned os m b ∧ (∀ k, (b, k) ∉ v.streams) ∧
    (∀ sb, (sb, .inflateBack) ∈ v.streams →
      Zlib.Spec.PtrBlock ((Zlib.Spec.readField? tags m ((Zlib.Spec.readField? tags m (.ptr sb 0) "z_stream_s" "state").getD .null)
        "inflate_state" "window").getD .null) ≠ some b) ∧
    (userWrite b ∨ (m.blocks b).isNone ∨ (∃ op noff, args = [op, .ptr b noff]))

private theorem readField_mono_of_nonstack {tags : TypeEnv} {m1 m2 : Mem} {sb : BlockId} {off : Int64}
    {st fld : String} (hb : m2.blocks sb = m1.blocks sb) :
    Zlib.Spec.readField? tags m2 (.ptr sb off) st fld =
      Zlib.Spec.readField? tags m1 (.ptr sb off) st fld := by
  unfold Zlib.Spec.readField?
  cases hfl : fieldLayout? tags (.structTy st) fld with
  | none => rfl
  | some pf =>
    dsimp only [bind, Option.bind]
    rw [readVal_blocks_eq_same hb]

private theorem inFuncAllowed_mono {tags : TypeEnv} {m0 : Mem} {v : ClientView}
    {owned userWrite : BlockSet} {os : OSState} {m_clean m : Mem} {bs : List BlockId}
    {args : List Val} {b : BlockId}
    (h2 : ∀ x ∈ bs, m_clean.blocks x = none)
    (h3 : ∀ x, x ∉ bs → m.blocks x = m_clean.blocks x)
    (hstr : ∀ sb, (sb, .inflateBack) ∈ v.streams →
      (∃ sblk, m_clean.blocks sb = some sblk) ∧
      ∀ stp, Zlib.Spec.readField? tags m_clean (.ptr sb 0) "z_stream_s" "state" = some stp →
        ∀ stbid stoff, stp = .ptr stbid stoff → ∃ stblk, m_clean.blocks stbid = some stblk)
    (hb_nmem : b ∉ bs) :
    inFuncAllowed tags m0 v owned userWrite os m args b ↔
      inFuncAllowed tags m0 v owned userWrite os m_clean args b := by
  have heq_b : m.blocks b = m_clean.blocks b := h3 b hb_nmem
  have hlib_iff : Zlib.Spec.LibProtected m0 owned os m b ↔
      Zlib.Spec.LibProtected m0 owned os m_clean b := by
    simp [Zlib.Spec.LibProtected, heq_b]
  have hwin_iff : ∀ sb, (sb, .inflateBack) ∈ v.streams →
      Zlib.Spec.readField? tags m ((Zlib.Spec.readField? tags m (.ptr sb 0) "z_stream_s" "state").getD .null)
        "inflate_state" "window" =
      Zlib.Spec.readField? tags m_clean ((Zlib.Spec.readField? tags m_clean (.ptr sb 0) "z_stream_s" "state").getD .null)
        "inflate_state" "window" := by
    intro sb hsb
    obtain ⟨⟨sblk, hsblk⟩, hst⟩ := hstr sb hsb
    have hsnb : sb ∉ bs := fun hm => by rw [h2 sb hm] at hsblk; cases hsblk
    have hst_eq : Zlib.Spec.readField? tags m (.ptr sb 0) "z_stream_s" "state" =
        Zlib.Spec.readField? tags m_clean (.ptr sb 0) "z_stream_s" "state" :=
      readField_mono_of_nonstack (h3 sb hsnb)
    rw [hst_eq]
    cases hrf : Zlib.Spec.readField? tags m_clean (.ptr sb 0) "z_stream_s" "state" with
    | none => rfl
    | some stp =>
      simp only [Option.getD]
      cases stp with
      | ptr stbid stoff =>
        obtain ⟨stblk, hstblk⟩ := hst (.ptr stbid stoff) hrf stbid stoff rfl
        have hstnb : stbid ∉ bs := fun hm => by rw [h2 stbid hm] at hstblk; cases hstblk
        exact readField_mono_of_nonstack (h3 stbid hstnb)
      | _ => rfl
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, h2', h3', h4⟩
    refine ⟨fun hc => h1 (hlib_iff.mpr hc), h2', fun sb hsb => ?_, ?_⟩
    · rw [← hwin_iff sb hsb]; exact h3' sb hsb
    · rcases h4 with hu | hnone | harg
      · exact Or.inl hu
      · exact Or.inr (Or.inl (by rw [← heq_b]; exact hnone))
      · exact Or.inr (Or.inr harg)
  · rintro ⟨h1, h2', h3', h4⟩
    refine ⟨fun hc => h1 (hlib_iff.mp hc), h2', fun sb hsb => ?_, ?_⟩
    · rw [hwin_iff sb hsb]; exact h3' sb hsb
    · rcases h4 with hu | hnone | harg
      · exact Or.inl hu
      · exact Or.inr (Or.inl (by rw [heq_b]; exact hnone))
      · exact Or.inr (Or.inr harg)

/-- VCGen `CallSafeSpec` wrapper for an external `inflateBack` `in_func` callback `sym`
(`unsigned (*in_func)(void *, z_const unsigned char **)`), built unconditionally from
`SafeUserCallbacks`. Requires caller stack-preservation on `userExt` outside `nb` (so
`CallContract.post_stack` holds across VCGen stack frames). -/
def userCallback_inFunc_vcSpec
    {prog : Prog} {m0 : Mem} {v : ClientView} {owned userWrite : BlockSet}
    {userExt : ExtHandler} (sym : String)
    (hnfn : prog.fns sym = none) (hnl : sym ≠ "LSEEK") (hnstd : Zlib.Spec.isStdLibcSym sym = false)
    (hsafe : Zlib.Spec.SafeUserCallbacks prog.tags m0 v owned userWrite userExt)
    (huser_stk : ∀ args m os ret m' os',
      userExt sym args m os (.ok ret m' os') →
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        (∀ op nb noff, args = [op, .ptr nb noff] → b ≠ nb) →
        m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack)) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) where
  sym := sym
  paramTys := [.ptr .void, .ptr (.ptr (.const_ (.int .u8)))]
  retTy := .int .u32
  variadic := false
  pre := fun m os args =>
    ∃ op nb noff, args = [op, .ptr nb noff] ∧
      Zlib.Spec.Writable m (.ptr nb noff) 8 ∧
      (∀ sb, (sb, .inflateBack) ∈ v.streams →
        (∃ sblk, m.blocks sb = some sblk) ∧
        ∀ stp, Zlib.Spec.readField? prog.tags m (.ptr sb 0) "z_stream_s" "state" = some stp →
          ∀ stbid stoff, stp = .ptr stbid stoff →
            (∃ stblk, m.blocks stbid = some stblk) ∧ Zlib.Spec.LibProtected m0 owned os m stbid)
  post := fun m os args ret m' os' =>
    ∃ op nb noff, args = [op, .ptr nb noff] ∧
      os'.errnoBlk = os.errnoBlk ∧ os'.strerrorBlk = os.strerrorBlk ∧
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack → b ≠ nb → m'.blocks b = some blk) ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = .stack) ∧
      Zlib.Spec.FramePreserved m m' (inFuncAllowed prog.tags m0 v owned userWrite os m args) ∧
      Zlib.Spec.NoHeapLeak m m' owned ∧
      ∃ avail : BitVec 32, ret = .int .u32 avail ∧
        (avail.toNat = 0 ∨ ∃ bs pb po, m'.readBytes nb noff 8 = some bs ∧
          Mem.decodePtr bs = some (.ptr pb po) ∧ Zlib.Spec.Readable m' (.ptr pb po) avail.toNat ∧
          ¬ Zlib.Spec.LibProtected m0 owned os m' pb ∧ (∀ k, (pb, k) ∉ v.streams) ∧
          (∀ sb, (sb, .inflateBack) ∈ v.streams →
            Zlib.Spec.PtrBlock ((Zlib.Spec.readField? prog.tags m' ((Zlib.Spec.readField? prog.tags m' (.ptr sb 0) "z_stream_s" "state").getD .null)
              "inflate_state" "window").getD .null) ≠ some pb) ∧
          (∀ blk, m'.blocks pb = some blk → blk.kind ≠ .stack)) ∧
        (∀ k, os.readBudget = some k → ∃ k', os'.readBudget = some k' ∧ (avail.toNat > 0 → k' < k))
  pre_mono := by
    intro m_clean m os args bs _ h2 h3 _ _ hp
    rcases hp with ⟨op, nb, noff, rfl, hwr, hprot⟩
    rcases hwr with ⟨b0, off0, blk0, hinj, hblk0, hperm0, hin0⟩
    cases hinj
    have hnb_nmem : nb ∉ bs := fun hm => by rw [h2 nb hm] at hblk0; cases hblk0
    refine ⟨op, nb, noff, rfl, ⟨nb, noff, blk0, rfl, by rw [h3 nb hnb_nmem]; exact hblk0, hperm0, hin0⟩, ?_⟩
    intro sb hsb
    obtain ⟨⟨sblk, hsblk⟩, hst⟩ := hprot sb hsb
    have hsnb : sb ∉ bs := fun hm => by rw [h2 sb hm] at hsblk; cases hsblk
    refine ⟨⟨sblk, by rw [h3 sb hsnb]; exact hsblk⟩, ?_⟩
    intro stp hrf stbid stoff hpeq
    have hrf' : Zlib.Spec.readField? prog.tags m_clean (.ptr sb 0) "z_stream_s" "state" = some stp := by
      rwa [← readField_mono_of_nonstack (h3 sb hsnb)]
    obtain ⟨⟨stblk, hstblk⟩, hlib⟩ := hst stp hrf' stbid stoff hpeq
    have hstnb : stbid ∉ bs := fun hm => by rw [h2 stbid hm] at hstblk; cases hstblk
    refine ⟨⟨stblk, by rw [h3 stbid hstnb]; exact hstblk⟩, ?_⟩
    rcases hlib with ho | he | hs | hm0 | ⟨gblk, hgblk, hk, hp⟩
    · exact Or.inl ho
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm0)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨gblk, by rw [h3 stbid hstnb]; exact hgblk, hk, hp⟩)))
  post_stack := by
    intro m_clean m m' os os' args rv bs _ h2 _ _ _ hpre hpost
    rcases hpost with ⟨op, nb, noff, rfl, _, _, hle, hstk1, hstk2, _, _⟩
    refine ⟨hle, fun b hb blk hbm hk => ?_, hstk2⟩
    rcases hpre with ⟨op', nb', noff', hinj, hwr, _⟩
    cases hinj
    rcases hwr with ⟨_, _, blk', hinj', hblk', _, _⟩
    cases hinj'
    have hne : b ≠ nb := by
      intro heq; subst heq
      rw [h2 b hb] at hblk'; cases hblk'
    exact hstk1 b blk hbm hk hne
  post_drop := by
    intro m_clean m m_after os os' args rv bs h1 h2 h3 _ h5 hpre hpost
    rcases hpost with ⟨op, nb, noff, rfl, herr, hstr, hle, hstk1, hstk2, hfp, hnhl, avail, rfl, hbuf, hbud⟩
    rcases hpre with ⟨op_c, nb_c, noff_c, hinj_c, hwr_c, hprot_c⟩
    cases hinj_c
    rcases hwr_c with ⟨_, _, blk_nb, hinj_nb, hblk_nb, _, _⟩
    cases hinj_nb
    have hnb_nmem : nb ∉ bs := fun hm => by rw [h2 nb hm] at hblk_nb; cases hblk_nb
    have hprot_c' : ∀ sb, (sb, .inflateBack) ∈ v.streams →
        (∃ sblk, m_clean.blocks sb = some sblk) ∧
        ∀ stp, Zlib.Spec.readField? prog.tags m_clean (.ptr sb 0) "z_stream_s" "state" = some stp →
          ∀ stbid stoff, stp = .ptr stbid stoff → ∃ stblk, m_clean.blocks stbid = some stblk :=
      fun sb hsb => let ⟨h1', h2'⟩ := hprot_c sb hsb; ⟨h1', fun stp hr stbid stoff hp => (h2' stp hr stbid stoff hp).1⟩
    have hprot_m : ∀ sb, (sb, .inflateBack) ∈ v.streams →
        (∃ sblk, m.blocks sb = some sblk) ∧
        ∀ stp, Zlib.Spec.readField? prog.tags m (.ptr sb 0) "z_stream_s" "state" = some stp →
          ∀ stbid stoff, stp = .ptr stbid stoff →
            (∃ stblk, m.blocks stbid = some stblk) ∧ Zlib.Spec.LibProtected m0 owned os m stbid := by
      intro sb hsb
      obtain ⟨⟨sblk, hsblk⟩, hst⟩ := hprot_c sb hsb
      have hsnb : sb ∉ bs := fun hm => by rw [h2 sb hm] at hsblk; cases hsblk
      refine ⟨⟨sblk, by rw [h3 sb hsnb]; exact hsblk⟩, fun stp hrf stbid stoff hpeq => ?_⟩
      have hrf' : Zlib.Spec.readField? prog.tags m_clean (.ptr sb 0) "z_stream_s" "state" = some stp := by
        rwa [← readField_mono_of_nonstack (h3 sb hsnb)]
      obtain ⟨⟨stblk, hstblk⟩, hlib⟩ := hst stp hrf' stbid stoff hpeq
      have hstnb : stbid ∉ bs := fun hm => by rw [h2 stbid hm] at hstblk; cases hstblk
      refine ⟨⟨stblk, by rw [h3 stbid hstnb]; exact hstblk⟩, ?_⟩
      rcases hlib with ho | he | hs | hm0 | ⟨gblk, hgblk, hk, hp⟩
      · exact Or.inl ho
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl hs))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hm0)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨gblk, by rw [h3 stbid hstnb]; exact hgblk, hk, hp⟩)))
    refine ⟨op, nb, noff, rfl, herr, hstr, ?_, ?_, ?_, ?_, ?_, avail, rfl, ?_, hbud⟩
    · simp only [dropBlks]; exact Nat.le_trans h1 hle
    · intro b blk hbm hk hneb
      have hb_nmem : b ∉ bs := fun hm => by rw [h2 b hm] at hbm; cases hbm
      rw [dropBlks_blocks_not_mem m_after bs hb_nmem]
      exact hstk1 b blk (by rw [h3 b hb_nmem]; exact hbm) hk hneb
    · intro b blk hbm hk
      have hb_nmem : b ∉ bs := fun hm => by rw [h2 b hm] at hbm; cases hbm
      obtain ⟨blk', hbm', hk'⟩ := hstk2 b blk (by rw [h3 b hb_nmem]; exact hbm) hk
      exact ⟨blk', by rw [dropBlks_blocks_not_mem m_after bs hb_nmem]; exact hbm', hk'⟩
    · refine ⟨?_, ?_⟩
      · intro b hsome hna
        have hnb' : b ∉ bs := fun hm => by rw [h2 b hm] at hsome; cases hsome
        have hms : (m.blocks b).isSome = true := by rw [h3 b hnb']; exact hsome
        have hna_m : ¬ inFuncAllowed prog.tags m0 v owned userWrite os m [op, .ptr nb noff] b :=
          fun ha => hna ((inFuncAllowed_mono h2 h3 hprot_c' hnb').mp ha)
        rw [dropBlks_blocks_not_mem m_after bs hnb', hfp.1 b hms hna_m, h3 b hnb']
      · intro b blk hn hsome hna
        by_cases hm : b ∈ bs
        · simp [dropBlks, hm] at hsome
        · rw [dropBlks_blocks_not_mem m_after bs hm] at hsome
          have hmn : m.blocks b = none := by rw [h3 b hm]; exact hn
          have hna_m : ¬ inFuncAllowed prog.tags m0 v owned userWrite os m [op, .ptr nb noff] b :=
            fun ha => hna ((inFuncAllowed_mono h2 h3 hprot_c' hm).mp ha)
          exact hfp.2 b blk hmn hsome hna_m
    · intro b blk hsome hk
      by_cases hm : b ∈ bs
      · simp [dropBlks, hm] at hsome
      · rw [dropBlks_blocks_not_mem m_after bs hm] at hsome
        rcases hnhl b blk hsome hk with hprev | hown
        · left; rw [← h3 b hm]; exact hprev
        · exact Or.inr hown
    · rcases hbuf with h0 | ⟨rbs, pb, po, hrd, hdec, hpb_rd, hpb_prot, hpb_str, hpb_win, hpb_nstk⟩
      · exact Or.inl h0
      · have hpb_nmem : pb ∉ bs := by
          intro hm
          obtain ⟨blk0, hblk0, hk0⟩ := h5 pb hm
          obtain ⟨blk1, hblk1, hk1⟩ := hstk2 pb blk0 hblk0 hk0
          exact absurd hk1 (hpb_nstk blk1 hblk1)
        have hpb_eq : (dropBlks m_after bs).blocks pb = m_after.blocks pb :=
          dropBlks_blocks_not_mem m_after bs hpb_nmem
        have hnb_rd : (dropBlks m_after bs).readBytes nb noff 8 = m_after.readBytes nb noff 8 := by
          unfold Mem.readBytes
          rw [dropBlks_blocks_not_mem m_after bs hnb_nmem]
        refine Or.inr ⟨rbs, pb, po, by rw [hnb_rd]; exact hrd, hdec, ?_, ?_, hpb_str, ?_, ?_⟩
        · rcases hpb_rd with ⟨b', off', blk', hinj', hblk', hin', hconcr'⟩
          cases hinj'
          exact ⟨pb, po, blk', rfl, by rw [hpb_eq]; exact hblk', hin', hconcr'⟩
        · simpa [Zlib.Spec.LibProtected, hpb_eq] using hpb_prot
        · intro sb hsb
          obtain ⟨⟨sblk, hsblk⟩, hst⟩ := hprot_m sb hsb
          have hsnb : sb ∉ bs := fun hm => by
            obtain ⟨_, hsblk_c⟩ := (hprot_c sb hsb).1
            rw [h2 sb hm] at hsblk_c; cases hsblk_c
          have hna_sb : ¬ inFuncAllowed prog.tags m0 v owned userWrite os m [op, .ptr nb noff] sb :=
            fun ha => ha.2.1 .inflateBack hsb
          have hsbeq_a : m_after.blocks sb = m.blocks sb := hfp.1 sb (by simp [hsblk]) hna_sb
          have hsbeq_d : (dropBlks m_after bs).blocks sb = m_after.blocks sb :=
            dropBlks_blocks_not_mem m_after bs hsnb
          have hst_eq : Zlib.Spec.readField? prog.tags (dropBlks m_after bs) (.ptr sb 0) "z_stream_s" "state" =
              Zlib.Spec.readField? prog.tags m_after (.ptr sb 0) "z_stream_s" "state" :=
            readField_mono_of_nonstack hsbeq_d
          rw [hst_eq]
          have hst_m : Zlib.Spec.readField? prog.tags m_after (.ptr sb 0) "z_stream_s" "state" =
              Zlib.Spec.readField? prog.tags m (.ptr sb 0) "z_stream_s" "state" :=
            readField_mono_of_nonstack hsbeq_a
          cases hrf : Zlib.Spec.readField? prog.tags m_after (.ptr sb 0) "z_stream_s" "state" with
          | none =>
            simp [Zlib.Spec.readField?, Zlib.Spec.PtrBlock]
          | some stp =>
            cases stp with
            | ptr stbid stoff =>
              have hrf_m : Zlib.Spec.readField? prog.tags m (.ptr sb 0) "z_stream_s" "state" = some (.ptr stbid stoff) := by
                rwa [← hst_m]
              obtain ⟨_, _⟩ := hst (.ptr stbid stoff) hrf_m stbid stoff rfl
              have hstnb : stbid ∉ bs := by
                obtain ⟨_, hsblk_c⟩ := (hprot_c sb hsb).1
                have hsnb_c : sb ∉ bs := fun hm => by rw [h2 sb hm] at hsblk_c; cases hsblk_c
                have hrf_c : Zlib.Spec.readField? prog.tags m_clean (.ptr sb 0) "z_stream_s" "state" =
                    some (.ptr stbid stoff) := by
                  rwa [← readField_mono_of_nonstack (h3 sb hsnb_c)]
                obtain ⟨⟨stblk_c, hstblk_c⟩, _⟩ := (hprot_c sb hsb).2 _ hrf_c stbid stoff rfl
                exact fun hm => by rw [h2 stbid hm] at hstblk_c; cases hstblk_c
              have hwin_d : Zlib.Spec.readField? prog.tags (dropBlks m_after bs) (.ptr stbid stoff) "inflate_state" "window" =
                  Zlib.Spec.readField? prog.tags m_after (.ptr stbid stoff) "inflate_state" "window" :=
                readField_mono_of_nonstack (dropBlks_blocks_not_mem m_after bs hstnb)
              have hw0 := hpb_win sb hsb
              simpa [hrf, hwin_d] using hw0
            | _ =>
              simp [Zlib.Spec.readField?, Zlib.Spec.PtrBlock]
        · intro blk hbm'
          rw [hpb_eq] at hbm'
          exact hpb_nstk blk hbm'
  sound_safe := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q R hd hsig hptys hco hpre hcont
    rcases hpre with ⟨op, nb, noff, rfl, _, _⟩
    have hze : Zlib.Spec.zlibExt userExt sym = userExt sym := zlibExt_userExt hnl hnstd
    have hnoub : ¬ Zlib.Spec.zlibExt userExt sym [op, .ptr nb noff] m os .ub := by
      rw [hze]
      intro hub
      exact (hsafe.2 sym [op, .ptr nb noff] m os .ub hub).1 rfl
    have hco' : Sem.coerceCallArgs m ptys false argVals = some [op, .ptr nb noff] :=
      (C99.Proof.VCGen.Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    refine SafeUntil.of_call_ext hd hnfn hsig hco' hnoub ?_
    intro ret m' os' he
    rw [hze] at he
    have hcb := safeUserCallbacks_inFunc hsafe he
    have hfp := safeUserCallbacks_framePreserved hsafe he
    have hstk := huser_stk [op, .ptr nb noff] m os ret m' os' he
    refine hcont ret m' os' ⟨op, nb, noff, rfl, hfp.1, hfp.2.1, hstk.1, ?_, hstk.2.2,
      hfp.2.2.1, hfp.2.2.2, hcb⟩
    intro b blk hb hk hne
    exact hstk.2.1 b blk hb hk (fun op' nb' noff' heq => by cases heq; exact hne)
  sound_term := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q hbud hd hsig hptys hco hpre hcont
    rcases hpre with ⟨op, nb, noff, rfl, _, _⟩
    have hze : Zlib.Spec.zlibExt userExt sym = userExt sym := zlibExt_userExt hnl hnstd
    have hnoub : ¬ Zlib.Spec.zlibExt userExt sym [op, .ptr nb noff] m os .ub := by
      rw [hze]
      intro hub
      exact (hsafe.2 sym [op, .ptr nb noff] m os .ub hub).1 rfl
    have hco' : Sem.coerceCallArgs m ptys false argVals = some [op, .ptr nb noff] :=
      (C99.Proof.VCGen.Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    obtain ⟨ret0, m0', os0', hex0⟩ := hsafe.1 sym [op, .ptr nb noff] m os (by simpa using hbud) (Or.inl rfl)
    refine C99.Proof.WPTerm.of_call_ext hd hnfn hsig hco' ⟨ret0, m0', os0', by rw [hze]; exact hex0⟩ hnoub ?_
    intro ret m' os' he
    rw [hze] at he
    have hcb := safeUserCallbacks_inFunc hsafe he
    have hfp := safeUserCallbacks_framePreserved hsafe he
    have hstk := huser_stk [op, .ptr nb noff] m os ret m' os' he
    refine hcont ret m' os' ⟨op, nb, noff, rfl, hfp.1, hfp.2.1, hstk.1, ?_, hstk.2.2,
      hfp.2.2.1, hfp.2.2.2, hcb⟩
    intro b blk hb hk hne
    exact hstk.2.1 b blk hb hk (fun op' nb' noff' heq => by cases heq; exact hne)

/-- VCGen `CallSafeSpec` wrapper for an external `inflateBack` `out_func` callback `sym`
(`int (*out_func)(void *, unsigned char *, unsigned)`), built unconditionally from
`SafeUserCallbacks`. Requires caller stack-preservation on `userExt`. -/
def userCallback_outFunc_vcSpec
    {prog : Prog} {m0 : Mem} {v : ClientView} {owned userWrite : BlockSet}
    {userExt : ExtHandler} (sym : String)
    (hnfn : prog.fns sym = none) (hnl : sym ≠ "LSEEK") (hnstd : Zlib.Spec.isStdLibcSym sym = false)
    (hsafe : Zlib.Spec.SafeUserCallbacks prog.tags m0 v owned userWrite userExt)
    (huser_stk : ∀ args m os ret m' os',
      userExt sym args m os (.ok ret m' os') →
      m.nextBlock ≤ m'.nextBlock ∧
      ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) :
    C99.Proof.VCGen.CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) where
  sym := sym
  paramTys := [.ptr .void, .ptr (.int .u8), .int .u32]
  retTy := .int .i32
  variadic := false
  pre := fun m os args =>
    ∃ op buf len, args = [op, buf, .int .u32 len] ∧
      (∀ sb, (sb, .inflateBack) ∈ v.streams →
        (∃ sblk, m.blocks sb = some sblk) ∧
        ∀ stp, Zlib.Spec.readField? prog.tags m (.ptr sb 0) "z_stream_s" "state" = some stp →
          ∀ stbid stoff, stp = .ptr stbid stoff →
            (∃ stblk, m.blocks stbid = some stblk) ∧ Zlib.Spec.LibProtected m0 owned os m stbid)
  post := fun m os args ret m' os' =>
    ∃ op buf len, args = [op, buf, .int .u32 len] ∧
      os'.errnoBlk = os.errnoBlk ∧ os'.strerrorBlk = os.strerrorBlk ∧
      os'.readBudget = os.readBudget ∧
      m.nextBlock ≤ m'.nextBlock ∧
      (∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk) ∧
      Zlib.Spec.FramePreserved m m' (inFuncAllowed prog.tags m0 v owned userWrite os m args) ∧
      Zlib.Spec.NoHeapLeak m m' owned ∧
      ∃ r : BitVec 32, ret = .int .i32 r
  pre_mono := by
    intro m_clean m os args bs _ h2 h3 _ _ hp
    rcases hp with ⟨op, buf, len, rfl, hprot⟩
    refine ⟨op, buf, len, rfl, fun sb hsb => ?_⟩
    obtain ⟨⟨sblk, hsblk⟩, hst⟩ := hprot sb hsb
    have hsnb : sb ∉ bs := fun hm => by rw [h2 sb hm] at hsblk; cases hsblk
    refine ⟨⟨sblk, by rw [h3 sb hsnb]; exact hsblk⟩, fun stp hrf stbid stoff hpeq => ?_⟩
    have hrf' : Zlib.Spec.readField? prog.tags m_clean (.ptr sb 0) "z_stream_s" "state" = some stp := by
      rwa [← readField_mono_of_nonstack (h3 sb hsnb)]
    obtain ⟨⟨stblk, hstblk⟩, hlib⟩ := hst stp hrf' stbid stoff hpeq
    have hstnb : stbid ∉ bs := fun hm => by rw [h2 stbid hm] at hstblk; cases hstblk
    refine ⟨⟨stblk, by rw [h3 stbid hstnb]; exact hstblk⟩, ?_⟩
    rcases hlib with ho | he | hs | hm0 | ⟨gblk, hgblk, hk, hp⟩
    · exact Or.inl ho
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm0)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨gblk, by rw [h3 stbid hstnb]; exact hgblk, hk, hp⟩)))
  post_stack := by
    intro _ m m' _ _ _ _ _ _ _ _ _ _ _ hpost
    rcases hpost with ⟨_, _, _, _, _, _, _, hle, hstk, _⟩
    exact ⟨hle, fun b _ blk hb hk => hstk b blk hb hk, fun b blk hb hk => ⟨blk, hstk b blk hb hk, hk⟩⟩
  post_drop := by
    intro m_clean m m_after os os' args rv bs h1 h2 h3 _ _ hpre hpost
    rcases hpre with ⟨_, _, _, _, hprot_c⟩
    rcases hpost with ⟨op, buf, len, rfl, herr, hstr, hbud, hle, hstk, hfp, hnhl, r, rfl⟩
    have hprot_c' : ∀ sb, (sb, .inflateBack) ∈ v.streams →
        (∃ sblk, m_clean.blocks sb = some sblk) ∧
        ∀ stp, Zlib.Spec.readField? prog.tags m_clean (.ptr sb 0) "z_stream_s" "state" = some stp →
          ∀ stbid stoff, stp = .ptr stbid stoff → ∃ stblk, m_clean.blocks stbid = some stblk :=
      fun sb hsb => let ⟨h1', h2'⟩ := hprot_c sb hsb; ⟨h1', fun stp hr stbid stoff hp => (h2' stp hr stbid stoff hp).1⟩
    refine ⟨op, buf, len, rfl, herr, hstr, hbud, Nat.le_trans h1 hle, ?_, ?_, ?_, r, rfl⟩
    · intro b blk hbm hk
      have hb_nmem : b ∉ bs := fun hm => by rw [h2 b hm] at hbm; cases hbm
      rw [dropBlks_blocks_not_mem m_after bs hb_nmem]
      exact hstk b blk (by rw [h3 b hb_nmem]; exact hbm) hk
    · refine ⟨?_, ?_⟩
      · intro b hsome hna
        have hnb' : b ∉ bs := fun hm => by rw [h2 b hm] at hsome; cases hsome
        have hms : (m.blocks b).isSome = true := by rw [h3 b hnb']; exact hsome
        have hna_m : ¬ inFuncAllowed prog.tags m0 v owned userWrite os m [op, buf, .int .u32 len] b :=
          fun ha => hna ((inFuncAllowed_mono h2 h3 hprot_c' hnb').mp ha)
        rw [dropBlks_blocks_not_mem m_after bs hnb', hfp.1 b hms hna_m, h3 b hnb']
      · intro b blk hn hsome hna
        by_cases hm : b ∈ bs
        · simp [dropBlks, hm] at hsome
        · rw [dropBlks_blocks_not_mem m_after bs hm] at hsome
          have hmn : m.blocks b = none := by rw [h3 b hm]; exact hn
          have hna_m : ¬ inFuncAllowed prog.tags m0 v owned userWrite os m [op, buf, .int .u32 len] b :=
            fun ha => hna ((inFuncAllowed_mono h2 h3 hprot_c' hm).mp ha)
          exact hfp.2 b blk hmn hsome hna_m
    · intro b blk hsome hk
      by_cases hm : b ∈ bs
      · simp [dropBlks, hm] at hsome
      · rw [dropBlks_blocks_not_mem m_after bs hm] at hsome
        rcases hnhl b blk hsome hk with hprev | hown
        · left; rw [← h3 b hm]; exact hprev
        · exact Or.inr hown
  sound_safe := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q R hd hsig hptys hco hpre hcont
    rcases hpre with ⟨op, buf, len, rfl, _⟩
    have hze : Zlib.Spec.zlibExt userExt sym = userExt sym := zlibExt_userExt hnl hnstd
    have hnoub : ¬ Zlib.Spec.zlibExt userExt sym [op, buf, .int .u32 len] m os .ub := by
      rw [hze]
      intro hub
      exact (hsafe.2 sym [op, buf, .int .u32 len] m os .ub hub).1 rfl
    have hco' : Sem.coerceCallArgs m ptys false argVals = some [op, buf, .int .u32 len] :=
      (C99.Proof.VCGen.Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    refine SafeUntil.of_call_ext hd hnfn hsig hco' hnoub ?_
    intro ret m' os' he
    rw [hze] at he
    obtain ⟨⟨r, rfl⟩, hbud⟩ := safeUserCallbacks_outFunc hsafe he
    have hfp := safeUserCallbacks_framePreserved hsafe he
    have hstk := huser_stk [op, buf, .int .u32 len] m os (.int .i32 r) m' os' he
    refine hcont (.int .i32 r) m' os' ⟨op, buf, len, rfl, hfp.1, hfp.2.1, hbud, hstk.1, hstk.2,
      hfp.2.2.1, hfp.2.2.2, r, rfl⟩
  sound_term := by
    intro s fnTy ptys argVals args fs ctx env blks m os k Q hbud_os hd hsig hptys hco hpre hcont
    rcases hpre with ⟨op, buf, len, rfl, _⟩
    have hze : Zlib.Spec.zlibExt userExt sym = userExt sym := zlibExt_userExt hnl hnstd
    have hnoub : ¬ Zlib.Spec.zlibExt userExt sym [op, buf, .int .u32 len] m os .ub := by
      rw [hze]
      intro hub
      exact (hsafe.2 sym [op, buf, .int .u32 len] m os .ub hub).1 rfl
    have hco' : Sem.coerceCallArgs m ptys false argVals = some [op, buf, .int .u32 len] :=
      (C99.Proof.VCGen.Refines.coerceCallArgs_of_map_unqual hptys).trans hco
    obtain ⟨ret0, m0', os0', hex0⟩ :=
      hsafe.1 sym [op, buf, .int .u32 len] m os (by simpa using hbud_os) (Or.inr rfl)
    refine C99.Proof.WPTerm.of_call_ext hd hnfn hsig hco' ⟨ret0, m0', os0', by rw [hze]; exact hex0⟩ hnoub ?_
    intro ret m' os' he
    rw [hze] at he
    obtain ⟨⟨r, rfl⟩, hbud⟩ := safeUserCallbacks_outFunc hsafe he
    have hfp := safeUserCallbacks_framePreserved hsafe he
    have hstk := huser_stk [op, buf, .int .u32 len] m os (.int .i32 r) m' os' he
    refine hcont (.int .i32 r) m' os' ⟨op, buf, len, rfl, hfp.1, hfp.2.1, hbud, hstk.1, hstk.2,
      hfp.2.2.1, hfp.2.2.2, r, rfl⟩

end IndirectCallbackWrappers

end Zlib.Proof
