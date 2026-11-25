import C99.Proof
import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgSpec
import Zlib.Adler32

/-!
# Safety Proofs for `adler32.c` (`Zlib.Proof.Adler32`)

Proves safety and bounded termination (`FuncBodySpec` and `ContractSafe`) for
the 4 public APIs and 1 internal helper in `Zlib.Adler32`:
- `adler32_combine_` (`adler32_combine__spec`)
- `adler32_combine` (`adler32_combine_spec`, `adler32_combine_safe`)
- `adler32_combine64` (`adler32_combine64_spec`, `adler32_combine64_safe`)
- `adler32_z` (`adler32_z_spec`, `adler32_z_safe`)
- `adler32` (`adler32_spec`, `adler32_safe`)
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec Zlib.Adler32

/-! ## 1. `enumConst?`, `initLibz` Non-Global Lookup, and Arithmetic Helpers -/

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

private theorem enumConst_prog_adler32_combine_ (tags : TypeEnv)
    (ht : tags = (progOfTUs Zlib.allFiles).tags) :
    enumConst? tags "adler32_combine_" = none := by
  rw [ht, progOfTUs_tags]
  exact enumConst_none_of_false (by decide)

private theorem enumConst_prog_adler32_z (tags : TypeEnv)
    (ht : tags = (progOfTUs Zlib.allFiles).tags) :
    enumConst? tags "adler32_z" = none := by
  rw [ht, progOfTUs_tags]
  exact enumConst_none_of_false (by decide)

/-! ## 2. Readable Slice, Local Slot State, and `WPTerm` Step Helpers -/

private theorem Readable.advance {m : Mem} {pb : BlockId} {poff : Int64} {n k : Nat}
    (hr : Readable m (.ptr pb poff) n) (hk : k ≤ n) :
    ∃ blk, m.blocks pb = some blk ∧
      0 ≤ poff.toInt + (k : Int) ∧ poff.toInt + (k : Int) ≤ (blk.size : Int) ∧
      Readable m (.ptr pb (Int64.ofInt (poff.toInt + k))) (n - k) := by
  rcases hr with ⟨b, off, blk, heq, hblk, hin, hbytes⟩
  cases heq
  rw [inBounds_iff] at hin
  have hlt : poff.toInt + (k : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    omega
  have hoff : (Int64.ofInt (poff.toInt + k)).toInt = poff.toInt + k :=
    int64_ofInt_toInt (by omega) hlt
  refine ⟨blk, hblk, by omega, by omega, pb, Int64.ofInt (poff.toInt + k), blk, rfl, hblk, ?_, ?_⟩
  · rw [inBounds_iff, hoff]
    omega
  · intro i hi
    rw [hoff]
    have heqi : (poff.toInt + (k : Int)).toNat + i = poff.toInt.toNat + (k + i) := by omega
    rw [heqi]
    exact hbytes (k + i) (by omega)

private theorem readable_block_lt {m : Mem} {pb : BlockId} {poff : Int64} {n : Nat}
    (hr : Readable m (.ptr pb poff) n) : pb < m.nextBlock := by
  rcases hr with ⟨_, _, blk, heq, hblk, _⟩
  cases heq
  exact lt_nextBlock_of_some hblk

private theorem localFrameMem_blocks_eq_of_lt {m0 m : Mem} {blks : List BlockId}
    (hf : LocalFrameMem m0 m blks) {b : BlockId} (hlt : b < m0.nextBlock) :
    m.blocks b = m0.blocks b :=
  hf.2.1 b hlt

private theorem Readable.read_byte {tags : TypeEnv} {m0 m : Mem} {blks : List BlockId}
    {pb : BlockId} {poff : Int64} {n idx : Nat}
    (hf : LocalFrameMem m0 m blks)
    (hr : Readable m0 (.ptr pb poff) n) (hidx : idx < n) :
    ∃ blk, ∃ bv : BitVec 8, m.blocks pb = some blk ∧
      0 ≤ poff.toInt + (idx : Int) ∧ poff.toInt + (idx : Int) ≤ (blk.size : Int) ∧
      Sem.readVal tags m pb (Int64.ofInt (poff.toInt + idx))
        (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) = some (.int .u8 bv) := by
  have hlt_pb : pb < m0.nextBlock := readable_block_lt hr
  rcases hr with ⟨_, _, blk, heq, hblk, hin, hbytes⟩
  cases heq
  have hm_pb : m.blocks pb = some blk := by rw [localFrameMem_blocks_eq_of_lt hf hlt_pb, hblk]
  have hlt63 : poff.toInt + (idx : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    have := inBounds_iff.mp hin
    omega
  have hoff_in : Mem.inBounds blk (Int64.ofInt (poff.toInt + idx)) 1 = true :=
    inBounds_add hin (by omega)
  have hoff_toInt : (Int64.ofInt (poff.toInt + idx)).toInt = poff.toInt + idx :=
    int64_ofInt_toInt (by have := (inBounds_iff.mp hin).1; omega) hlt63
  have hal : Mem.isAligned blk (Int64.ofInt (poff.toInt + idx)) 1 = true :=
    isAligned_one (by rw [hoff_toInt]; have := (inBounds_iff.mp hin).1; omega)
  obtain ⟨bv, hrv⟩ := readVal_int_of_bytes tags (k := .u8) hm_pb hal hoff_in (fun i hi => by
    change i < 1 at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [Nat.add_zero, hoff_toInt]
    have heqn : (poff.toInt + (idx : Int)).toNat = poff.toInt.toNat + idx := by
      have := (inBounds_iff.mp hin).1
      omega
    rw [heqn]
    exact hbytes idx hidx)
  have hrv' : Sem.readVal tags m pb (Int64.ofInt (poff.toInt + idx))
      (.const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8)))) = some (.int .u8 bv) := by
    unfold Sem.readVal at hrv ⊢
    simpa [CTy.unqual] using hrv
  exact ⟨blk, bv, hm_pb, (by have := (inBounds_iff.mp hin).1; omega),
    (by have := (inBounds_iff.mp hin).2; omega), hrv'⟩

private theorem readVal_writeVal_same_ptr (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {ty el : CTy} {p : Val}
    (hptr : ty.unqual = .ptr el) (hnc : ty.isConst = false)
    (hp : p = .null ∨ ∃ pb poff, p = .ptr pb poff)
    (hb : m.blocks b = some blk)
    (hwr : Sem.writeVal m b off ty p = some m') :
    Sem.readVal tags m' b off ty = some p := by
  unfold Sem.writeVal at hwr
  simp only [hnc, Bool.not_false, guard_true, hb, hptr, bind, Option.bind] at hwr
  have hal : Mem.isAligned blk off 8 = true := by
    cases hg : Mem.isAligned blk off 8
    · simp [hg, guard] at hwr
    · rfl
  simp only [hal, guard_true] at hwr
  rcases hp with rfl | ⟨pb, poff, rfl⟩
  · have hwb : m.writeBytes b off Mem.encodeNull = some m' := hwr
    have hrd := readBytes_writeBytes_same hb hwb
    have hblk' := writeBytes_blocks_eq hb hwb
    have hal' : Mem.isAligned { blk with bytes := (fun i =>
        if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + Mem.encodeNull.length then
          Mem.encodeNull[i - off.toInt.toNat]?.getD .undef
        else blk.bytes i) } off 8 = true := by
      simpa [Mem.isAligned] using hal
    unfold Sem.readVal
    rw [hptr]
    simp only [hblk', hal', guard_true, bind, Option.bind]
    rw [← encodeNull_length, hrd]
    simp
  · have hwb : m.writeBytes b off (Mem.encodePtr pb poff) = some m' := hwr
    have hrd := readBytes_writeBytes_same hb hwb
    have hblk' := writeBytes_blocks_eq hb hwb
    have hal' : Mem.isAligned { blk with bytes := (fun i =>
        if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + (Mem.encodePtr pb poff).length then
          (Mem.encodePtr pb poff)[i - off.toInt.toNat]?.getD .undef
        else blk.bytes i) } off 8 = true := by
      simpa [Mem.isAligned] using hal
    unfold Sem.readVal
    rw [hptr]
    simp only [hblk', hal', guard_true, bind, Option.bind]
    rw [← encodePtr_length pb poff, hrd]
    simp

/-- Typed local/parameter integer slot in `(env, m)`. -/
private def IntSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty : CTy)
    (k : IntKind) (v : BitVec k.bits) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .int k ∧
  ty.isConst = false ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 k.align = true ∧ Mem.inBounds blk 0 k.bytes = true ∧
    Sem.readVal [] m b 0 ty = some (.int k v)

/-- Uninitialized writable local/parameter integer slot in `(env, m)`. -/
private def UninitIntSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty : CTy)
    (k : IntKind) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .int k ∧
  ty.isConst = false ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 k.align = true ∧ Mem.inBounds blk 0 k.bytes = true

/-- Typed local/parameter pointer slot in `(env, m)`. -/
private def PtrSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty el : CTy)
    (p : Val) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .ptr el ∧
  ty.isConst = false ∧
  (p = .null ∨ ∃ pb poff, p = .ptr pb poff) ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 8 = true ∧ Mem.inBounds blk 0 8 = true ∧
    Sem.readVal [] m b 0 ty = some p

private theorem IntSlot.to_uninit {env m name b ty k v} (h : IntSlot env m name b ty k v) :
    UninitIntSlot env m name b ty k :=
  ⟨h.1, h.2.1, h.2.2.1, let ⟨blk, h1, h2, h3, h4, _⟩ := h.2.2.2; ⟨blk, h1, h2, h3, h4⟩⟩

private theorem IntSlot.readVal_eq (tags : TypeEnv) {env m name b ty k v}
    (h : IntSlot env m name b ty k v) :
    Sem.readVal tags m b 0 ty = some (.int k v) := by
  rcases h.2.2.2 with ⟨_, _, _, _, _, hrv⟩
  have heq : Sem.readVal tags m b 0 ty = Sem.readVal [] m b 0 ty := by
    unfold Sem.readVal
    rw [h.2.1]
  rw [heq, hrv]

private theorem PtrSlot.readVal_eq (tags : TypeEnv) {env m name b ty el p}
    (h : PtrSlot env m name b ty el p) :
    Sem.readVal tags m b 0 ty = some p := by
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, hrv⟩
  have heq : Sem.readVal tags m b 0 ty = Sem.readVal [] m b 0 ty := by
    unfold Sem.readVal
    rw [h.2.1]
  rw [heq, hrv]

private theorem UninitIntSlot.write {m0 m : Mem} {blks : List BlockId} {env name b ty k}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hs : UninitIntSlot env m name b ty k) (v : BitVec k.bits) :
    ∃ m', Sem.writeVal m b 0 ty (.int k v) = some m' ∧
      LocalFrameMem m0 m' blks ∧ IntSlot env m' name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  have hiv : Sem.valAsInt? (.int k v) = some (k, if k.signed then v.toInt else (v.toNat : Int)) := rfl
  obtain ⟨m', hm'⟩ := writeVal_int_some hnc hk hblk hrw hal hin hiv
  obtain ⟨bs, hbs_wr, hblk'⟩ := writeVal_blocks_eq hblk hm'
  have hf' := hf.write_stack hmem hblk hbs_wr
  have hrv : Sem.readVal [] m' b 0 ty = some (.int k v) := by
    have hwr2 : Sem.writeVal m b 0 (.int k) (.int k v) = some m' := by
      unfold Sem.writeVal at hm' ⊢
      simpa [hnc, hk, CTy.isConst, CTy.unqual, CTy.intKind?] using hm'
    have hrd := readVal_writeVal_same_int [] hblk hwr2
    unfold Sem.readVal at hrd ⊢
    simpa [hk, CTy.unqual, CTy.intKind?] using hrd
  refine ⟨m', hm', hf', hlu, hk, hnc, _, hblk', hrw, by simpa [Mem.isAligned] using hal, ?_, hrv⟩
  rw [inBounds_iff] at hin ⊢
  exact hin

private theorem PtrSlot.write {m0 m : Mem} {blks : List BlockId} {env name b ty el p}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hs : PtrSlot env m name b ty el p) {p' : Val}
    (hp' : p' = .null ∨ ∃ pb poff, p' = .ptr pb poff) :
    ∃ m', Sem.writeVal m b 0 ty p' = some m' ∧
      LocalFrameMem m0 m' blks ∧ PtrSlot env m' name b ty el p' := by
  rcases hs with ⟨hlu, hptr, hnc, _, blk, hblk, hrw, hal, hin, _⟩
  obtain ⟨m', hm'⟩ := writeVal_ptr_some hnc hptr hblk hrw hal hin hp'
  obtain ⟨bs, hbs_wr, hblk'⟩ := writeVal_blocks_eq hblk hm'
  have hf' := hf.write_stack hmem hblk hbs_wr
  have hrv := readVal_writeVal_same_ptr [] hptr hnc hp' hblk hm'
  refine ⟨m', hm', hf', hlu, hptr, hnc, hp', _, hblk', hrw, by simpa [Mem.isAligned] using hal, ?_, hrv⟩
  rw [inBounds_iff] at hin ⊢
  exact hin

private theorem IntSlot.preserve_blocks {env m m' name b ty k v}
    (hs : IntSlot env m name b ty k v) (hbeq : m'.blocks b = m.blocks b) :
    IntSlot env m' name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  refine ⟨hlu, hk, hnc, blk, hbeq.trans hblk, hrw, hal, hin, ?_⟩
  rw [← readVal_eq_of_blocks_eq [] hbeq.symm 0 ty]
  exact hrv

private theorem PtrSlot.preserve_blocks {env m m' name b ty el p}
    (hs : PtrSlot env m name b ty el p) (hbeq : m'.blocks b = m.blocks b) :
    PtrSlot env m' name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  refine ⟨hlu, hptr, hnc, hp, blk, hbeq.trans hblk, hrw, hal, hin, ?_⟩
  rw [← readVal_eq_of_blocks_eq [] hbeq.symm 0 ty]
  exact hrv

private theorem IntSlot.preserve_ne {env m m' name b b' ty k v ty' v'}
    (hs : IntSlot env m name b ty k v) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    IntSlot env m' name b ty k v :=
  hs.preserve_blocks (writeVal_blocks_ne hwr hne)

private theorem UninitIntSlot.preserve_ne {env m m' name b b' ty k ty' v'}
    (hs : UninitIntSlot env m name b ty k) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    UninitIntSlot env m' name b ty k := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  exact ⟨hlu, hk, hnc, blk, by rw [writeVal_blocks_ne hwr hne, hblk], hrw, hal, hin⟩

private theorem PtrSlot.preserve_ne {env m m' name b b' ty el p ty' v'}
    (hs : PtrSlot env m name b ty el p) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    PtrSlot env m' name b ty el p :=
  hs.preserve_blocks (writeVal_blocks_ne hwr hne)

private theorem localFrameMem_roExt_unwind2 {m m' : Mem} (blks1 blks2 : List BlockId)
    (hf : LocalFrameMem m m' (blks1 ++ blks2)) :
    ROExt m ((m'.freeStack blks1).freeStack blks2) :=
  LocalFrameMem.roExt_freeStack (hf.freeStack_sub)

private theorem IntSlot.preserve_alloc {env m m1 name b ty k v sz al p kind ba init h1 h2 h3 bid}
    (hs : IntSlot env m name b ty k v)
    (ha : m.alloc sz al p kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    IntSlot ((nm', bid, ty') :: env) m1 name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  have hm1 : m1 = (m.alloc sz al p kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  have hbeq : m.blocks b = m1.blocks b := by
    rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne]
  refine ⟨by rw [lookup_cons_ne env hnm, hlu], hk, hnc, blk, hbeq.symm.trans hblk, hrw, hal, hin, ?_⟩
  rw [← readVal_eq_of_blocks_eq [] hbeq 0 ty]
  exact hrv

private theorem PtrSlot.preserve_alloc {env m m1 name b ty el p sz al perm kind ba init h1 h2 h3 bid}
    (hs : PtrSlot env m name b ty el p)
    (ha : m.alloc sz al perm kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    PtrSlot ((nm', bid, ty') :: env) m1 name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  have hm1 : m1 = (m.alloc sz al perm kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  have hbeq : m.blocks b = m1.blocks b := by
    rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne]
  refine ⟨by rw [lookup_cons_ne env hnm, hlu], hptr, hnc, hp, blk, hbeq.symm.trans hblk, hrw, hal, hin, ?_⟩
  rw [← readVal_eq_of_blocks_eq [] hbeq 0 ty]
  exact hrv

private theorem UninitIntSlot.preserve_alloc {env m m1 name b ty k sz al perm kind ba init h1 h2 h3 bid}
    (hs : UninitIntSlot env m name b ty k)
    (ha : m.alloc sz al perm kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    UninitIntSlot ((nm', bid, ty') :: env) m1 name b ty k := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  have hm1 : m1 = (m.alloc sz al perm kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  exact ⟨by rw [lookup_cons_ne env hnm, hlu], hk, hnc, blk,
    by rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hblk], hrw, hal, hin⟩

private theorem UninitIntSlot.of_alloc_int {tags : TypeEnv} {env : Env} {m m1 : Mem} {d : VarDecl}
    {k : IntKind} (hk : d.ty.unqual = .int k) (hnc : d.ty.isConst = false)
    {ba : UInt64} {bid : BlockId}
    {hsz : max 1 (sizeofTy tags d.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags d.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags d.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba = (bid, m1)) :
    UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty k := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
    .rw .stack ba (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hsz_eq : sizeofTy tags d.ty = k.bytes := by rw [← sizeofTy_unqual, hk]; simp
  have hal_eq : alignofTy tags d.ty = k.align := by rw [← alignofTy_unqual, hk]; simp
  have halk : k.align = max 1 (alignofTy tags d.ty) := by rw [hal_eq]; cases k <;> rfl
  have hszk : k.bytes ≤ max 1 (sizeofTy tags d.ty) := by rw [hsz_eq]; exact Nat.le_max_right _ _
  subst bid
  refine ⟨lookup_cons_eq env, hk, hnc, _, by rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl, ?_, ?_⟩
  · rw [isAligned_iff]
    refine ⟨Int.le_refl _, by cases k <;> decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero, halk]
    exact hba
  · rw [inBounds_iff]
    refine ⟨Int.le_refl _, ?_⟩
    simpa [Int64.toInt_zero] using hszk

private theorem IntSlot.of_pushCallParam {tags : TypeEnv} {m m2 : Mem} {p : Param} {k : IntKind}
    (hk : p.ty.unqual = .int k) (hnc : p.ty.isConst = false)
    {ba : UInt64} {v : BitVec k.bits}
    {hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags p.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags p.ty) = 0}
    (hwr : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 p.ty.stripConst (.int k v) = some m2)
    (env : Env) :
    IntSlot ((p.name, m.nextBlock, p.ty) :: env) m2 p.name m.nextBlock p.ty k v := by
  let m1 := (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
    .rw .stack ba (fun _ => .undef) hsz hal hba).2
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy tags p.ty),
      max 1 (alignofTy tags p.ty), .rw, .stack, ba, (fun _ => .undef), hsz, hal, hba⟩ :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_eq : sizeofTy tags p.ty = k.bytes := by rw [← sizeofTy_unqual, hk]; simp
  have hal_eq : alignofTy tags p.ty = k.align := by rw [← alignofTy_unqual, hk]; simp
  have halk : k.align = max 1 (alignofTy tags p.ty) := by rw [hal_eq]; cases k <;> rfl
  have hszk : k.bytes ≤ max 1 (sizeofTy tags p.ty) := by rw [hsz_eq]; exact Nat.le_max_right _ _
  have hwr' : Sem.writeVal m1 m.nextBlock 0 (.int k) (.int k v) = some m2 := by
    unfold Sem.writeVal at hwr ⊢
    simpa [stripConst_isConst, stripConst_unqual, hk, CTy.isConst, CTy.unqual, CTy.intKind?] using hwr
  have hrd := readVal_writeVal_same_int [] hblk1 hwr'
  have hrv : Sem.readVal [] m2 m.nextBlock 0 p.ty = some (.int k v) := by
    unfold Sem.readVal at hrd ⊢
    simpa [hk, CTy.unqual, CTy.intKind?] using hrd
  obtain ⟨bs, _, hblk2⟩ := writeVal_blocks_eq hblk1 hwr'
  refine ⟨lookup_cons_eq env, hk, hnc, _, hblk2, rfl, ?_, ?_, hrv⟩
  · rw [isAligned_iff]
    refine ⟨Int.le_refl _, by cases k <;> decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero, halk]
    exact hba
  · rw [inBounds_iff]
    refine ⟨Int.le_refl _, ?_⟩
    simpa [Int64.toInt_zero] using hszk

private theorem PtrSlot.of_pushCallParam {tags : TypeEnv} {m m2 : Mem} {p : Param} {el : CTy}
    (hptr : p.ty.unqual = .ptr el) (hnc : p.ty.isConst = false)
    {ba : UInt64} {vp : Val} (hvp : vp = .null ∨ ∃ pb poff, vp = .ptr pb poff)
    {hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags p.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags p.ty) = 0}
    (hwr : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 p.ty.stripConst vp = some m2)
    (env : Env) :
    PtrSlot ((p.name, m.nextBlock, p.ty) :: env) m2 p.name m.nextBlock p.ty el vp := by
  let m1 := (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
    .rw .stack ba (fun _ => .undef) hsz hal hba).2
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy tags p.ty),
      max 1 (alignofTy tags p.ty), .rw, .stack, ba, (fun _ => .undef), hsz, hal, hba⟩ :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_eq : sizeofTy tags p.ty = 8 := by rw [← sizeofTy_unqual, hptr]; simp
  have hal_eq : alignofTy tags p.ty = 8 := by rw [← alignofTy_unqual, hptr]; simp
  have hwr' : Sem.writeVal m1 m.nextBlock 0 p.ty.stripConst vp = some m2 := hwr
  obtain ⟨bs, _, hblk2⟩ := writeVal_blocks_eq hblk1 hwr'
  have hal1 : Mem.isAligned ⟨max 1 (sizeofTy tags p.ty), max 1 (alignofTy tags p.ty), .rw, .stack, ba,
      (fun _ => .undef), hsz, hal, hba⟩ 0 8 = true := by
    rw [isAligned_iff]
    refine ⟨Int.le_refl _, by decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
    simpa [hal_eq] using hba
  have hrv_strip := readVal_writeVal_same_ptr [] (by rw [stripConst_unqual, hptr])
    (stripConst_isConst p.ty) hvp hblk1 hwr'
  have hrv : Sem.readVal [] m2 m.nextBlock 0 p.ty = some vp := by
    unfold Sem.readVal at hrv_strip ⊢
    simpa [stripConst_unqual, hptr] using hrv_strip
  refine ⟨lookup_cons_eq env, hptr, hnc, hvp, _, hblk2, rfl, hal1, ?_, hrv⟩
  rw [inBounds_iff]
  refine ⟨Int.le_refl _, ?_⟩
  simp [Int64.toInt_zero, hsz_eq]

private theorem nextBlock_lt_of_writeAlloc {tags : TypeEnv} {m m2 : Mem} {p : Param} {ty_sc : CTy}
    {ba : UInt64} {v : Val}
    {hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags p.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags p.ty) = 0}
    (hwr : Sem.writeVal
      (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba).2
      m.nextBlock 0 ty_sc v = some m2) :
    m.nextBlock < m2.nextBlock := by
  rw [writeVal_nextBlock hwr]
  simp

private theorem sizeofTy_eq_bytes {tags : TypeEnv} {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    sizeofTy tags ty = k.bytes := by
  rw [← sizeofTy_unqual, hk]; simp

private theorem sizeofTy_eq_ptr {tags : TypeEnv} {ty el : CTy} (hp : ty.unqual = .ptr el) :
    sizeofTy tags ty = 8 := by
  rw [← sizeofTy_unqual, hp]; simp

private theorem CTy.decay_of_int : ∀ {ty : CTy} {k : IntKind},
    ty.unqual = .int k → ty.decay.unqual = .int k
  | .const_ t, k, hk => by simp [CTy.decay, CTy.unqual] at hk ⊢; exact CTy.decay_of_int hk
  | .typedef _ t, k, hk => by simp [CTy.decay, CTy.unqual] at hk ⊢; exact CTy.decay_of_int hk
  | .int k', k, hk => by simp [CTy.decay, CTy.unqual] at hk ⊢; exact hk
  | .void, _, hk | .ptr _, _, hk | .array _ _, _, hk | .structTy _, _, hk | .unionTy _, _, hk
  | .anonStruct _, _, hk | .anonUnion _, _, hk | .enumTy _ _, _, hk | .fnPtr _ _ _, _, hk
  | .vaList, _, hk => by simp [CTy.unqual] at hk

private theorem CTy.decay_of_ptr : ∀ {ty el : CTy},
    ty.unqual = .ptr el → ty.decay.unqual = .ptr el
  | .const_ t, el, hp => by simp [CTy.decay, CTy.unqual] at hp ⊢; exact CTy.decay_of_ptr hp
  | .typedef _ t, el, hp => by simp [CTy.decay, CTy.unqual] at hp ⊢; exact CTy.decay_of_ptr hp
  | .ptr el', el, hp => by simp [CTy.decay, CTy.unqual] at hp ⊢; exact hp
  | .void, _, hp | .int _, _, hp | .array _ _, _, hp | .structTy _, _, hp | .unionTy _, _, hp
  | .anonStruct _, _, hp | .anonUnion _, _, hp | .enumTy _ _, _, hp | .fnPtr _ _ _, _, hp
  | .vaList, _, hp => by simp [CTy.unqual] at hp

private theorem CTy.decay_isPtr {ty el : CTy} (hp : ty.unqual = .ptr el) :
    ty.decay.isPtr = true := by
  simp [CTy.isPtr, CTy.decay_of_ptr hp]

private theorem CTy.decay_isPtr_false_of_int {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    ty.decay.isPtr = false := by
  simp [CTy.isPtr, CTy.decay_of_int hk]

private theorem CTy.decay_isFn_false_of_int {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    (match ty.decay.unqual with | .fnPtr .. => true | _ => false) = false := by
  simp [CTy.decay_of_int hk]

private theorem CTy.decay_isFn_false_of_ptr {ty el : CTy} (hp : ty.unqual = .ptr el) :
    (match ty.decay.unqual with | .fnPtr .. => true | _ => false) = false := by
  simp [CTy.decay_of_ptr hp]

private theorem readPlace_intSlot {tags : TypeEnv} {env : Env} {m : Mem} {mods : ModSet}
    {name : String} {b : BlockId} {ty : CTy} {k : IntKind} {v : BitVec k.bits}
    (hs : IntSlot env m name b ty k v) (hnc : mods.conflicts b 0 k.bytes = false) :
    readPlace tags m mods .rval b 0 ty = some (.rval (.int k v) ty.decay) := by
  unfold readPlace
  have hs1 := hs.2.1
  have hc : mods.conflicts b 0 (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_bytes hs1]; exact hnc
  have hrv := hs.readVal_eq tags
  rw [hs1]
  simp only [hc, Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv]

private theorem readPlace_ptrSlot {tags : TypeEnv} {env : Env} {m : Mem} {mods : ModSet}
    {name : String} {b : BlockId} {ty el : CTy} {p : Val}
    (hs : PtrSlot env m name b ty el p) (hnc : mods.conflicts b 0 8 = false) :
    readPlace tags m mods .rval b 0 ty = some (.rval p ty.decay) := by
  unfold readPlace
  have hs1 := hs.2.1
  have hc : mods.conflicts b 0 (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_ptr hs1]; exact hnc
  have hrv := hs.readVal_eq tags
  rw [hs1]
  simp only [hc, Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv]

private theorem writePlace_int {tags : TypeEnv} {m m' : Mem} {b : BlockId} {ty : CTy}
    {k : IntKind} {v : BitVec k.bits} {rty : CTy}
    (hk : ty.unqual = .int k) (hwr : Sem.writeVal m b 0 ty (.int k v) = some m') :
    writePlace tags m b 0 ty (.rval (.int k v) rty) = some (.rval (.int k v) ty, m') := by
  unfold writePlace
  have hcast : Sem.castVal m ty (.int k v) = some (.int k v) := by
    rw [castVal_unqual, hk]
    simp only [castVal_int, ofIntCast]
    by_cases hs : k.signed <;> simp [hs]
  simp only [hk, hcast, bind, Option.bind, pure, Pure.pure, hwr]

private theorem writePlace_ptr {tags : TypeEnv} {m m' : Mem} {b : BlockId} {ty el : CTy}
    {p : Val} (hp : p = .null ∨ ∃ pb poff, p = .ptr pb poff) {rty : CTy}
    (hptr : ty.unqual = .ptr el) (hwr : Sem.writeVal m b 0 ty p = some m') :
    writePlace tags m b 0 ty (.rval p rty) = some (.rval p ty, m') := by
  unfold writePlace
  have hcast : Sem.castVal m ty p = some p := by
    rw [castVal_unqual, hptr]
    rcases hp with rfl | ⟨pb, poff, rfl⟩ <;> simp
  simp only [hptr, hcast, bind, Option.bind, pure, Pure.pure, hwr]

private theorem modSet_conflicts_nil (b : BlockId) (o : Int64) (n : Nat) :
    ModSet.conflicts [] b o n = false := rfl

private theorem modSet_conflicts_cons_ne {b b' : BlockId} {o o' : Int64} {n n' : Nat} {ms : ModSet}
    (hne : b' ≠ b) (hrest : ms.conflicts b o n = false) :
    ModSet.conflicts (⟨b', o', n'⟩ :: ms) b o n = false := by
  unfold ModSet.conflicts
  simp only [List.any_cons, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
  exact ⟨Or.inl (beq_false_of_ne hne), hrest⟩

private theorem applyBinary_int {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {op : BinOp} {v1 v2 : Val} {t1 t2 : CTy} {k1 k2 : IntKind}
    (ht1 : t1.unqual = .int k1) (ht2 : t2.unqual = .int k2) :
    applyBinary cfg tags m op v1 t1 v2 t2 = evalIntBinary op v1 v2 := by
  unfold applyBinary
  simp [CTy.isPtr, ht1, ht2]

/-! ## 3. Pure Integer Evaluation & Statement Combinators -/

private theorem evalIntBinary_cmp (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (k1 k2 : IntKind) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    ∃ rbv : BitVec 32,
      evalIntBinary op (.int k1 v1) (.int k2 v2) = some (.int .i32 rbv, .int .i32) := by
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, Option.bind, pure, Pure.pure]
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem evalIntBinary_unsigned_arith (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    {k1 k2 : IntKind} (hs : (IntKind.usualArith k1 k2).signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    ∃ rbv : BitVec (IntKind.usualArith k1 k2).bits,
      evalIntBinary op (.int k1 v1) (.int k2 v2) =
        some (.int (IntKind.usualArith k1 k2) rbv, .int (IntKind.usualArith k1 k2)) := by
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, Option.bind, pure, Pure.pure]
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ofIntExact_unsigned hs]

private theorem evalIntBinary_unsigned_mod {k1 k2 : IntKind}
    (hs : (IntKind.usualArith k1 k2).signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hnz : (BitVec.ofInt (IntKind.usualArith k1 k2).bits
      (if k2.signed then v2.toInt else (v2.toNat : Int))).toNat ≠ 0) :
    ∃ rbv : BitVec (IntKind.usualArith k1 k2).bits,
      evalIntBinary .mod (.int k1 v1) (.int k2 v2) =
        some (.int (IntKind.usualArith k1 k2) rbv, .int (IntKind.usualArith k1 k2)) := by
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, Option.bind, pure, Pure.pure]
  have hne : (((BitVec.ofInt (IntKind.usualArith k1 k2).bits
      (if k2.signed then v2.toInt else (v2.toNat : Int))).toNat : Int) == 0) = false :=
    beq_false_of_ne (by omega)
  simp only [hs, Bool.false_eq_true, ↓reduceIte, hne, ofIntExact_unsigned hs]
  exact ⟨_, rfl⟩

private theorem evalIntBinary_unsigned_shift (op : BinOp)
    (hop : op = .shl ∨ op = .shr)
    {k1 k2 : IntKind} (hs : k1.promote.signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < (k1.promote.bits : Int)) :
    ∃ rbv : BitVec k1.promote.bits,
      evalIntBinary op (.int k1 v1) (.int k2 v2) = some (.int k1.promote rbv, .int k1.promote) := by
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, Option.bind, pure, Pure.pure]
  rcases hop with rfl | rfl <;> simp [hlo, hhi, hs]

private def PureIntEval (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (env : Env) (m : Mem) (mods : ModSet) (e : CExpr)
    (k : IntKind) (bv : BitVec k.bits) (rty : CTy) : Prop :=
  rty.unqual = .int k ∧
  ∀ fs ctx blks os k_cont Q,
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k bv) rty) fs) ctx mods) env blks m os k_cont) →
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval e fs) ctx mods) env blks m os k_cont)

private theorem pureIntEval_lit {prog cfg ext env m mods v k sfx rad sym} :
    PureIntEval prog cfg ext env m mods (.lit v k sfx rad sym) k (BitVec.ofInt k.bits v) (.int k) := by
  refine ⟨rfl, fun fs ctx blks os k_cont Q hw => ?_⟩
  exact WPTerm.of_exprPure (by simp [stepExprPure, ofIntCast]) hw

private theorem pureIntEval_paren {prog cfg ext env m mods e k bv rty}
    (he : PureIntEval prog cfg ext env m mods e k bv rty) :
    PureIntEval prog cfg ext env m mods (.paren e) k bv rty := by
  refine ⟨he.1, fun fs ctx blks os k_cont Q hw => ?_⟩
  exact WPTerm.of_exprPure rfl (he.2 fs ctx blks os k_cont Q hw)

private theorem pureIntEval_var {prog cfg ext env m mods x b ty k bv}
    (hs : IntSlot env m x b ty k bv) (hnc : mods.conflicts b 0 k.bytes = false) :
    PureIntEval prog cfg ext env m mods (.var x) k bv ty.decay := by
  refine ⟨CTy.decay_of_int hs.2.1, fun fs ctx blks os k_cont Q hw => ?_⟩
  refine WPTerm.of_exprPure ?_ hw
  simp [stepExprPure, hs.1, readPlace_intSlot hs hnc]

private theorem pureIntEval_var0 {prog cfg ext env m x b ty k bv}
    (hs : IntSlot env m x b ty k bv) :
    PureIntEval prog cfg ext env m [] (.var x) k bv ty.decay :=
  pureIntEval_var hs rfl

private theorem stepExprPure_eval_lval_var {prog cfg env m mods x b ty fs}
    (hlu : env.lookup x = some (b, ty)) :
    stepExprPure prog cfg env m mods (.eval .lval (.var x) fs) =
      some (.ret (.lval b 0 ty) fs, m, mods) := by
  simp [stepExprPure, hlu]

private theorem stepExprPure_ret_cast {prog cfg env m mods v ty0 cty fs cv}
    (hc : Sem.castVal m cty v = some cv) :
    stepExprPure prog cfg env m mods (.ret (.rval v ty0) (.castF cty :: fs)) =
      some (.ret (.rval cv cty) fs, m, mods) := by
  simp [stepExprPure, hc]

private theorem pureIntEval_cast_int {prog cfg ext env m mods cty e k1 bv1 rty1 k2}
    (hk2 : cty.unqual = .int k2)
    (he : PureIntEval prog cfg ext env m mods e k1 bv1 rty1) :
    PureIntEval prog cfg ext env m mods (.cast cty e) k2
      (BitVec.ofInt k2.bits (if k1.signed then bv1.toInt else (bv1.toNat : Int))) cty := by
  refine ⟨hk2, fun fs ctx blks os k_cont Q hw => ?_⟩
  refine WPTerm.of_exprPure rfl ?_
  refine he.2 (.castF cty :: fs) ctx blks os k_cont Q ?_
  have hc : Sem.castVal m cty (.int k1 bv1) =
      some (.int k2 (BitVec.ofInt k2.bits (if k1.signed then bv1.toInt else (bv1.toNat : Int)))) := by
    rw [castVal_unqual, hk2]
    simp [ofIntCast]
  exact WPTerm.of_exprPure (stepExprPure_ret_cast hc) hw

private theorem pureIntEval_bin {prog cfg ext env m mods op l r k1 bv1 t1 k2 bv2 t2 rk rbv}
    (hl : PureIntEval prog cfg ext env m mods l k1 bv1 t1)
    (hr : PureIntEval prog cfg ext env m mods r k2 bv2 t2)
    (hbin : evalIntBinary op (.int k1 bv1) (.int k2 bv2) = some (.int rk rbv, .int rk)) :
    PureIntEval prog cfg ext env m mods (.binary op l r) rk rbv (.int rk) := by
  refine ⟨rfl, fun fs ctx blks os k_cont Q hw => ?_⟩
  refine WPTerm.of_exprPure rfl ?_
  refine hl.2 (.binLhsF op r :: fs) ctx blks os k_cont Q ?_
  refine WPTerm.of_exprPure rfl ?_
  refine hr.2 (.binRhsF op (.int k1 bv1) t1 :: fs) ctx blks os k_cont Q ?_
  refine WPTerm.of_exprPure ?_ hw
  simp [stepExprPure, applyBinary_int hl.1 hr.1, hbin]

private theorem pureIntEval_bin_exists {prog cfg ext env m mods op l r k1 bv1 t1 k2 bv2 t2 rk}
    (hl : PureIntEval prog cfg ext env m mods l k1 bv1 t1)
    (hr : PureIntEval prog cfg ext env m mods r k2 bv2 t2)
    (hbin : ∃ rbv : BitVec rk.bits,
      evalIntBinary op (.int k1 bv1) (.int k2 bv2) = some (.int rk rbv, .int rk)) :
    ∃ rbv : BitVec rk.bits,
      PureIntEval prog cfg ext env m mods (.binary op l r) rk rbv (.int rk) :=
  let ⟨rbv, h⟩ := hbin
  ⟨rbv, pureIntEval_bin hl hr h⟩

private theorem castVal_int_eq_some {m : Mem} {ty : CTy} {k k1 : IntKind}
    (hk : ty.unqual = .int k) (bv : BitVec k1.bits) :
    Sem.castVal m ty (.int k1 bv) =
      some (.int k (BitVec.ofInt k.bits (if k1.signed then bv.toInt else (bv.toNat : Int)))) := by
  rw [castVal_unqual, hk]
  simp [ofIntCast]

private theorem wp_assign_eq_int {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty k rhs rk rbv rty}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : UninitIntSlot env m x b ty k)
    (hrhs : PureIntEval prog cfg ext env m [] rhs rk rbv rty)
    (hcont : ∀ v' m', LocalFrameMem m0 m' frameBlks → IntSlot env m' x b ty k v' →
      Sem.writeVal m b 0 ty (.int k v') = some m' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.assign .eq (.var x) rhs))) env blks m os k_cont) := by
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hs.1) ?_
  refine WPTerm.of_exprPure rfl ?_
  refine hrhs.2 [.assignRhsF .eq b 0 ty] .discard blks os k_cont Q ?_
  let v' : BitVec k.bits := BitVec.ofInt k.bits (if rk.signed then rbv.toInt else (rbv.toNat : Int))
  obtain ⟨m', hm', hf', hs'⟩ := hs.write hf hmem v'
  have hcast : Sem.castVal m ty (.int rk rbv) = some (.int k v') := castVal_int_eq_some hs.2.1 rbv
  have hwp : writePlace prog.tags m b 0 ty (.rval (.int rk rbv) rty) = some (.rval (.int k v') ty, m') := by
    unfold writePlace
    simp only [hs.2.1, hcast, bind, Option.bind, pure, Pure.pure, hm']
  have hc0 : ModSet.conflicts [] b 0 (sizeofTy prog.tags ty) = false := rfl
  have hstep : stepExprPure prog cfg env m [] (.ret (.rval (.int rk rbv) rty) [.assignRhsF .eq b 0 ty]) =
      some (.ret (.rval (.int k v') ty) [], m', [⟨b, 0, sizeofTy prog.tags ty⟩]) := by
    simp [stepExprPure, hc0, assignOpToBin?, hwp]
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hcont v' m' hf' hs' hm'))

private theorem wp_assign_op_int_val {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty k v aop bop rhs rk rbv rty ok obv}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : IntSlot env m x b ty k v)
    (haop : assignOpToBin? aop = some bop)
    (hrhs : PureIntEval prog cfg ext env m [] rhs rk rbv rty)
    (hbin : evalIntBinary bop (.int k v) (.int rk rbv) = some (.int ok obv, .int ok))
    (hcont : ∀ m', LocalFrameMem m0 m' frameBlks →
      IntSlot env m' x b ty k (BitVec.ofInt k.bits (if ok.signed then obv.toInt else (obv.toNat : Int))) →
      Sem.writeVal m b 0 ty
        (.int k (BitVec.ofInt k.bits (if ok.signed then obv.toInt else (obv.toNat : Int)))) = some m' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.assign aop (.var x) rhs))) env blks m os k_cont) := by
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hs.1) ?_
  refine WPTerm.of_exprPure rfl ?_
  refine hrhs.2 [.assignRhsF aop b 0 ty] .discard blks os k_cont Q ?_
  let v' : BitVec k.bits := BitVec.ofInt k.bits (if ok.signed then obv.toInt else (obv.toNat : Int))
  obtain ⟨m', hm', hf', hs'⟩ := hs.to_uninit.write hf hmem v'
  have hcast : Sem.castVal m ty (.int ok obv) = some (.int k v') := castVal_int_eq_some hs.2.1 obv
  have hwp : writePlace prog.tags m b 0 ty (.rval (.int ok obv) ty) = some (.rval (.int k v') ty, m') := by
    unfold writePlace
    simp only [hs.2.1, hcast, bind, Option.bind, pure, Pure.pure, hm']
  have hc0 : ModSet.conflicts [] b 0 (sizeofTy prog.tags ty) = false := rfl
  have hstep : stepExprPure prog cfg env m [] (.ret (.rval (.int rk rbv) rty) [.assignRhsF aop b 0 ty]) =
      some (.ret (.rval (.int k v') ty) [], m', [⟨b, 0, sizeofTy prog.tags ty⟩]) := by
    simp [stepExprPure, hc0, haop, hs.readVal_eq, applyBinary_int hs.2.1 hrhs.1, hbin, hwp]
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hcont m' hf' hs' hm'))

private theorem wp_assign_op_int {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty k v aop bop rhs rk rbv rty ok obv}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : IntSlot env m x b ty k v)
    (haop : assignOpToBin? aop = some bop)
    (hrhs : PureIntEval prog cfg ext env m [] rhs rk rbv rty)
    (hbin : evalIntBinary bop (.int k v) (.int rk rbv) = some (.int ok obv, .int ok))
    (hcont : ∀ v' m', LocalFrameMem m0 m' frameBlks → IntSlot env m' x b ty k v' →
      Sem.writeVal m b 0 ty (.int k v') = some m' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.assign aop (.var x) rhs))) env blks m os k_cont) :=
  wp_assign_op_int_val hf hmem hs haop hrhs hbin (fun m' hf' hs' hm' => hcont _ m' hf' hs' hm')

private theorem wp_if_int {prog cfg ext env blks m os k_cont Q cond t f? ck cbv rty}
    (hc : PureIntEval prog cfg ext env m [] cond ck cbv rty)
    (ht : cbv.toNat ≠ 0 → WPTerm prog cfg ext Q (.running (.stmt t) env blks m os k_cont))
    (hf : cbv.toNat = 0 → WPTerm prog cfg ext Q (.running (.stmt (f?.getD .nop)) env blks m os k_cont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.ifStmt cond t f?)) env blks m os k_cont) := by
  refine WPTerm.of_det rfl ?_
  refine hc.2 [] (.branch t (f?.getD .nop)) blks os k_cont Q ?_
  by_cases hnz : cbv.toNat = 0
  · refine WPTerm.of_det ?_ (hf hnz)
    unfold stepDet
    simp [isTruthy, hnz]
  · refine WPTerm.of_det ?_ (ht hnz)
    unfold stepDet
    simp [isTruthy, hnz]

private theorem wp_seq_step {prog cfg ext env blks m os k Q s1 ss}
    (hw : WPTerm prog cfg ext Q (.running (.stmt s1) env blks m os (.stmts ss k))) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.stmts (s1 :: ss) k)) :=
  WPTerm.of_det rfl hw

private theorem wp_seq_nil {prog cfg ext env blks m os k Q}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.stmts [] k)) :=
  WPTerm.of_det rfl hw

private theorem wp_blockEnd_free {prog cfg ext env savedEnv blks savedBlks m os k Q}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) savedEnv savedBlks (m.freeStack blks) os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.blockEnd savedEnv savedBlks k)) :=
  WPTerm.of_det rfl hw

/-- Uniform `StmtPres` wrapper for composing straight-line / block sub-statements cleanly. -/
private def StmtPres (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (P : Env → List BlockId → Mem → Prop)
    (R : Env → List BlockId → Mem → Prop) (s : CStmt) : Prop :=
  ∀ env blks m os k Q,
    P env blks m →
    (∀ m', R env blks m' → WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k)) →
    WPTerm prog cfg ext Q (.running (.stmt s) env blks m os k)

private theorem stmtPres_block2 {prog cfg ext P Q R s1 s2}
    (hs1 : StmtPres prog cfg ext P Q s1)
    (hs2 : StmtPres prog cfg ext Q R s2)
    (hp_nil : ∀ env blks m, P env blks m → P env [] m)
    (hr_nil : ∀ env blks m, R env [] m → R env blks m) :
    StmtPres prog cfg ext P R (.block [s1, s2]) := by
  intro env blks m os k Post hp hcont
  refine WPTerm.of_det rfl ?_
  refine hs1 env [] m os (.stmts [s2] (.blockEnd env blks k)) Post (hp_nil env blks m hp) ?_
  intro m1 hq1
  refine wp_seq_step ?_
  refine hs2 env [] m1 os (.stmts [] (.blockEnd env blks k)) Post hq1 ?_
  intro m2 hr2
  refine wp_seq_nil (wp_blockEnd_free ?_)
  rw [freeStack_nil]
  exact hcont m2 (hr_nil env blks m2 hr2)

private theorem wp_localDecl_none_int {prog cfg ext d rest env blks frameBlks m0 m os k_cont Q k}
    (hk : d.ty.unqual = .int k) (hnc : d.ty.isConst = false) (hnd : d.isStatic = false)
    (hi : d.init? = none)
    (hf : LocalFrameMem m0 m frameBlks)
    (hcont : ∀ bid m1,
      LocalFrameMem m0 m1 (bid :: frameBlks) →
      UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty k →
      (∀ {nm b ty k' v}, nm ≠ d.name → IntSlot env m nm b ty k' v →
        IntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k' v) →
      (∀ {nm b ty k'}, nm ≠ d.name → UninitIntSlot env m nm b ty k' →
        UninitIntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k') →
      (∀ {nm b ty el p}, nm ≠ d.name → PtrSlot env m nm b ty el p →
        PtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el p) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os k_cont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k_cont) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [← sizeofTy_unqual, hk, sizeofTy_int]
    cases k <;> decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [← alignofTy_unqual, hk, alignofTy_int]
    cases k <;> decide
  have hd : stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env blks m os k_cont) =
      some (.allocLocal d none rest env blks m os k_cont) := by
    unfold stepDet
    simp [hnd, hi]
  refine WPTerm.of_localDecl_none hd hsz hal ?_
  intro base bid m1 hba halloc
  exact hcont bid m1 (hf.alloc_stack halloc)
    (UninitIntSlot.of_alloc_int hk hnc halloc)
    (fun hnm hs => hs.preserve_alloc halloc hnm)
    (fun hnm hs => hs.preserve_alloc halloc hnm)
    (fun hnm hs => hs.preserve_alloc halloc hnm)

private theorem wp_decl_none_int_seq {prog cfg ext d srest env blks frameBlks m0 m os k_cont Q k}
    (hk : d.ty.unqual = .int k) (hnc : d.ty.isConst = false) (hnd : d.isStatic = false)
    (hi : d.init? = none)
    (hf : LocalFrameMem m0 m frameBlks)
    (hcont : ∀ bid m1,
      LocalFrameMem m0 m1 (bid :: frameBlks) →
      UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty k →
      (∀ {nm b ty k' v}, nm ≠ d.name → IntSlot env m nm b ty k' v →
        IntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k' v) →
      (∀ {nm b ty k'}, nm ≠ d.name → UninitIntSlot env m nm b ty k' →
        UninitIntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k') →
      (∀ {nm b ty el p}, nm ≠ d.name → PtrSlot env m nm b ty el p →
        PtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el p) →
      WPTerm prog cfg ext Q
        (.running (.stmt .nop) ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os (.stmts srest k_cont))) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.stmts (.decl d :: srest) k_cont)) := by
  refine wp_seq_step (WPTerm.of_det rfl ?_)
  refine wp_localDecl_none_int hk hnc hnd hi hf ?_
  intro bid m1 hf1 hu hi1 hu1 hp1
  exact WPTerm.of_det rfl (hcont bid m1 hf1 hu hi1 hu1 hp1)

private theorem wp_return_int {prog cfg ext env blks m os k_cont Q e rk rbv rty
    retEnv retBlks fnRetTy m' fs ctx k kret}
    (he : PureIntEval prog cfg ext env m [] e rk rbv rty)
    (htop : k_cont.topRetTy = fnRetTy)
    (hnv : fnRetTy.isVoid = false)
    (hkret : fnRetTy.unqual = .int kret)
    (hunw : unwindReturn m blks k_cont = some (retEnv, retBlks, fnRetTy, m', fs, ctx, k))
    (hcont : ∀ retBv : BitVec kret.bits,
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int kret retBv) fnRetTy) fs) ctx []) retEnv retBlks m' os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.returnStmt (some e))) env blks m os k_cont) := by
  refine WPTerm.of_det rfl ?_
  refine he.2 [] .returnVal blks os k_cont Q ?_
  let retBv : BitVec kret.bits :=
    BitVec.ofInt kret.bits (if rk.signed then rbv.toInt else (rbv.toNat : Int))
  have hcast : Sem.castVal m fnRetTy (.int rk rbv) = some (.int kret retBv) :=
    castVal_int_eq_some hkret rbv
  refine WPTerm.of_det ?_ (hcont retBv)
  unfold stepDet
  simp [htop, hnv, hcast, hunw]

private theorem wp_if_ge_sub_u32 {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty v lit litSfx litRad litSym}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : IntSlot env m x b ty .u64 v)
    (hc : ModSet.conflicts [] b 0 8 = false := rfl)
    (hcont : ∀ v' m', LocalFrameMem m0 m' frameBlks → IntSlot env m' x b ty .u64 v' →
      (∀ b' ≠ b, m'.blocks b' = m.blocks b') →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.ifStmt
        (.binary .ge (.var x) (.lit lit .u32 litSfx litRad litSym))
        (.expr (.assign .subEq (.var x) (.lit lit .u32 litSfx litRad litSym)))
        none)) env blks m os k_cont) := by
  obtain ⟨cbv, hcmp⟩ := evalIntBinary_cmp .ge (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    .u64 .u32 v (BitVec.ofInt 32 lit)
  have hcond : PureIntEval prog cfg ext env m []
      (.binary .ge (.var x) (.lit lit .u32 litSfx litRad litSym)) .i32 cbv (.int .i32) :=
    pureIntEval_bin (pureIntEval_var hs hc) pureIntEval_lit hcmp
  refine wp_if_int hcond ?_ ?_
  · intro _
    obtain ⟨obv, hsub⟩ := evalIntBinary_unsigned_arith .sub (Or.inr (Or.inl rfl))
      (k1 := .u64) (k2 := .u32) rfl v (BitVec.ofInt 32 lit)
    refine wp_assign_op_int hf hmem hs rfl pureIntEval_lit hsub ?_
    intro v' m' hf' hs' hm'
    exact hcont v' m' hf' hs' (fun _ hne => writeVal_blocks_ne hm' hne)
  · intro _
    exact hcont v m hf hs (fun _ _ => rfl)

private theorem wp_if_ge_sub_u64_shl {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty v lit litSfx litRad litSym sh}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : IntSlot env m x b ty .u64 v)
    (hsh_lo : (0 : Int) ≤ (BitVec.ofInt 32 sh).toInt)
    (hsh_lt : (BitVec.ofInt 32 sh).toInt < 64)
    (hc : ModSet.conflicts [] b 0 8 = false := rfl)
    (hcont : ∀ v' m', LocalFrameMem m0 m' frameBlks → IntSlot env m' x b ty .u64 v' →
      (∀ b' ≠ b, m'.blocks b' = m.blocks b') →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.ifStmt
        (.binary .ge (.var x) (CExpr.binary .shl (.cast (.int .u64) (.lit lit .u32 litSfx litRad litSym)) (.lit sh .i32 .none .dec none)).paren)
        (.expr (.assign .subEq (.var x) (CExpr.binary .shl (.cast (.int .u64) (.lit lit .u32 litSfx litRad litSym)) (.lit sh .i32 .none .dec none)).paren))
        none)) env blks m os k_cont) := by
  have hv_cast := pureIntEval_cast_int (prog := prog) (cfg := cfg) (ext := ext) (env := env) (m := m) (mods := [])
    (cty := .int .u64) (k2 := .u64) rfl
    (pureIntEval_lit (v := lit) (k := .u32) (sfx := litSfx) (rad := litRad) (sym := litSym))
  obtain ⟨vb, hvb⟩ := pureIntEval_bin_exists hv_cast pureIntEval_lit
    (evalIntBinary_unsigned_shift .shl (Or.inl rfl) (k1 := .u64) (k2 := .i32) rfl
      _ (BitVec.ofInt 32 sh) hsh_lo hsh_lt)
  have hvbp := pureIntEval_paren hvb
  obtain ⟨cbv, hcmp⟩ := evalIntBinary_cmp .ge (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    .u64 .u64 v vb
  have hcond := pureIntEval_bin (pureIntEval_var hs hc) hvbp hcmp
  refine wp_if_int hcond ?_ ?_
  · intro _
    obtain ⟨obv, hsub⟩ := evalIntBinary_unsigned_arith .sub (Or.inr (Or.inl rfl))
      (k1 := .u64) (k2 := .u64) rfl v vb
    refine wp_assign_op_int hf hmem hs rfl hvbp hsub ?_
    intro v' m' hf' hs' hm'
    exact hcont v' m' hf' hs' (fun _ hne => writeVal_blocks_ne hm' hne)
  · intro _
    exact hcont v m hf hs (fun _ _ => rfl)

private theorem wp_mod_u32_u64 {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty v lit litSfx litRad litSym}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : IntSlot env m x b ty .u64 v)
    (hnz : (BitVec.ofInt 64 (BitVec.ofInt 32 lit).toNat).toNat ≠ 0)
    (hcont : ∀ v' m', LocalFrameMem m0 m' frameBlks → IntSlot env m' x b ty .u64 v' →
      (∀ b' ≠ b, m'.blocks b' = m.blocks b') →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.expr (.assign .modEq (.var x) (.lit lit .u32 litSfx litRad litSym))))
        env blks m os k_cont) := by
  obtain ⟨obv, hmod⟩ := evalIntBinary_unsigned_mod (k1 := .u64) (k2 := .u32) rfl v (BitVec.ofInt 32 lit) hnz
  refine wp_assign_op_int hf hmem hs rfl pureIntEval_lit hmod ?_
  intro v' m' hf' hs' hm'
  exact hcont v' m' hf' hs' (fun _ hne => writeVal_blocks_ne hm' hne)

/-! ## 4. `adler32_combine_`, `adler32_combine`, and `adler32_combine64` -/

private theorem adler32_combine__body_eq :
    Zlib.Adler32.adler32TU_fn_adler32_combine_.body =
      CStmt.block [
        .decl { name := "sum1", ty := .int .u64 },
        .decl { name := "sum2", ty := .int .u64 },
        .decl { name := "rem", ty := .int .u32 },
        .ifStmt (.binary .lt (.var "len2") (.lit 0))
          (.returnStmt (some (.lit 4294967295 .u64 .UL .hex))) none,
        .expr (.assign .modEq (.var "len2") (.lit 65521 .u32 .U)),
        .expr (.assign .eq (.var "rem") (.cast (.int .u32) (.var "len2"))),
        .expr (.assign .eq (.var "sum1") (.binary .bitAnd (.var "adler1") (.lit 65535 .i32 .none .hex))),
        .expr (.assign .eq (.var "sum2") (.binary .mul (.var "rem") (.var "sum1"))),
        .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U)),
        .expr (.assign .addEq (.var "sum1")
          (.binary .sub
            (.binary .add
              (CExpr.binary .bitAnd (.var "adler2") (.lit 65535 .i32 .none .hex)).paren
              (.lit 65521 .u32 .U))
            (.lit 1))),
        .expr (.assign .addEq (.var "sum2")
          (.binary .sub
            (.binary .add
              (.binary .add
                (CExpr.binary .bitAnd (CExpr.binary .shr (.var "adler1") (.lit 16)).paren (.lit 65535 .i32 .none .hex)).paren
                (CExpr.binary .bitAnd (CExpr.binary .shr (.var "adler2") (.lit 16)).paren (.lit 65535 .i32 .none .hex)).paren)
              (.lit 65521 .u32 .U))
            (.var "rem"))),
        .ifStmt (.binary .ge (.var "sum1") (.lit 65521 .u32 .U))
          (.expr (.assign .subEq (.var "sum1") (.lit 65521 .u32 .U))) none,
        .ifStmt (.binary .ge (.var "sum1") (.lit 65521 .u32 .U))
          (.expr (.assign .subEq (.var "sum1") (.lit 65521 .u32 .U))) none,
        .ifStmt (.binary .ge (.var "sum2")
          (CExpr.binary .shl (.cast (.int .u64) (.lit 65521 .u32 .U)) (.lit 1)).paren)
          (.expr (.assign .subEq (.var "sum2")
            (CExpr.binary .shl (.cast (.int .u64) (.lit 65521 .u32 .U)) (.lit 1)).paren)) none,
        .ifStmt (.binary .ge (.var "sum2") (.lit 65521 .u32 .U))
          (.expr (.assign .subEq (.var "sum2") (.lit 65521 .u32 .U))) none,
        .returnStmt (some (.binary .bitOr (.var "sum1") (CExpr.binary .shl (.var "sum2") (.lit 16)).paren))
      ] := rfl

private theorem evalIntBinary_i64_lt_zero (v : BitVec 64) :
    evalIntBinary .lt (.int .i64 v) (.int .i32 0) =
      some (.int .i32 (if v.toInt < 0 then 1 else 0), .int .i32) := by
  unfold evalIntBinary
  have hval1 : valAsInt? (.int .i64 v) = some (.i64, v.toInt) := rfl
  have hval2 : valAsInt? (.int .i32 0) = some (.i32, 0) := rfl
  rw [hval1, hval2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .i64 .i32 = .i64 := rfl
  have h2 : (BitVec.ofInt 64 0).toInt = (0 : Int) := by decide
  rw [hu]
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, cmpOrd, BitVec.ofInt_toInt, h2]
  simp only [decide_eq_true_eq]

private theorem evalIntBinary_i64_mod_base {v : BitVec 64} (hnonneg : 0 ≤ v.toInt) :
    ∃ rbv : BitVec 64,
      evalIntBinary .mod (.int .i64 v) (.int .u32 (BitVec.ofInt 32 65521)) =
        some (.int .i64 rbv, .int .i64) := by
  unfold evalIntBinary
  have hval1 : valAsInt? (.int .i64 v) = some (.i64, v.toInt) := rfl
  have hval2 : valAsInt? (.int .u32 (BitVec.ofInt 32 65521)) =
      some (.u32, ((BitVec.ofInt 32 65521).toNat : Int)) := rfl
  rw [hval1, hval2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .i64 .u32 = .i64 := rfl
  have h2 : (BitVec.ofInt 64 ((BitVec.ofInt 32 65521).toNat : Int)).toInt = 65521 := by decide
  have hmod_lo : (0 : Int) ≤ v.toInt.tmod 65521 := Int.tmod_nonneg _ hnonneg
  have hmod_lt : v.toInt.tmod 65521 < 65521 := Int.tmod_lt_of_pos v.toInt (by decide)
  have hin : IntKind.i64.inRange (v.toInt.tmod 65521) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits]
    have h63 : (2 ^ (64 - 1) : Int) = 9223372036854775808 := by decide
    rw [h63]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [hu]
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, BitVec.ofInt_toInt, h2]
  simp only [show ((65521 : Int) == 0) = false from rfl, ofIntExact_signed (k := .i64) rfl hin]
  exact ⟨_, rfl⟩

theorem adler32_combine__spec (prog : Prog) (ext : ExtHandler) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Adler32.adler32TU_fn_adler32_combine_
      (fun _ args => ∃ (a1 a2 len2 : BitVec 64),
        args = [.int .u64 a1, .int .u64 a2, .int .i64 len2])
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨a1, a2, len2, hargs⟩ _ hpush hcont
  subst hargs
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hsz0, hal0, hba0, m2_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m3_p, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m4_p, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let env0 := prog.fnStatics Zlib.Adler32.adler32TU_fn_adler32_combine_.name ++ prog.globalEnv
  let b_adler1 := m.nextBlock
  let b_adler2 := m2_p.nextBlock
  let b_len2 := m3_p.nextBlock
  have hs_adler1_0 : IntSlot (("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0)
      m2_p "adler1" b_adler1 (.typedef "uLong" (.int .u64)) .u64 a1 :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr0 env0
  have hne_1_2_mid : b_adler1 ≠ m2_p.nextBlock := by
    have hlt : b_adler1 < m2_p.nextBlock := lt_nextBlock_of_some hs_adler1_0.2.2.2.choose_spec.1
    exact Nat.ne_of_lt hlt
  have hs_adler1_1 : IntSlot (("adler2", b_adler2, .typedef "uLong" (.int .u64)) ::
      ("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0)
      m3_p "adler1" b_adler1 (.typedef "uLong" (.int .u64)) .u64 a1 :=
    (hs_adler1_0.preserve_alloc rfl (by decide)).preserve_ne hwr1 hne_1_2_mid
  have hs_adler2_1 : IntSlot (("adler2", b_adler2, .typedef "uLong" (.int .u64)) ::
      ("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0)
      m3_p "adler2" b_adler2 (.typedef "uLong" (.int .u64)) .u64 a2 :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr1 _
  have hne_1_2 : b_adler1 ≠ b_len2 := by
    have h1 : b_adler1 < m2_p.nextBlock := lt_nextBlock_of_some hs_adler1_0.2.2.2.choose_spec.1
    have h2 : m2_p.nextBlock < m3_p.nextBlock := nextBlock_lt_of_writeAlloc hwr1
    exact Nat.ne_of_lt (Nat.lt_trans h1 h2)
  have hne_2_2 : b_adler2 ≠ b_len2 := by
    have h1 : b_adler2 < m3_p.nextBlock := lt_nextBlock_of_some hs_adler2_1.2.2.2.choose_spec.1
    exact Nat.ne_of_lt h1
  let env_params : Env := ("len2", b_len2, .typedef "z_off64_t" (.int .i64)) ::
    ("adler2", b_adler2, .typedef "uLong" (.int .u64)) ::
    ("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0
  have hs_adler1_2 : IntSlot env_params m1 "adler1" b_adler1 (.typedef "uLong" (.int .u64)) .u64 a1 :=
    (hs_adler1_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_1_2
  have hs_adler2_2 : IntSlot env_params m1 "adler2" b_adler2 (.typedef "uLong" (.int .u64)) .u64 a2 :=
    (hs_adler2_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_2_2
  have hs_len2_2 : IntSlot env_params m1 "len2" b_len2 (.typedef "z_off64_t" (.int .i64)) .i64 len2 :=
    IntSlot.of_pushCallParam (k := .i64) rfl rfl hwr2 _
  rw [adler32_combine__body_eq]
  refine WPTerm.of_det rfl (WPTerm.of_det rfl ?_)
  refine wp_localDecl_none_int (k := .u64) (frameBlks := [b_len2, b_adler2, b_adler1]) rfl rfl rfl rfl hf1 ?_
  intro b_sum1 m5 hf5 hu_sum1 hi_5 _ _
  have hs_a1_5 := hi_5 (by decide) hs_adler1_2
  have hs_a2_5 := hi_5 (by decide) hs_adler2_2
  have hs_l2_5 := hi_5 (by decide) hs_len2_2
  refine WPTerm.of_det rfl ?_
  refine wp_decl_none_int_seq (k := .u64) rfl rfl rfl rfl hf5 ?_
  intro b_sum2 m6 hf6 hu_sum2 hi_6 hu_6 _
  have hs_a1_6 := hi_6 (by decide) hs_a1_5
  have hs_a2_6 := hi_6 (by decide) hs_a2_5
  have hs_l2_6 := hi_6 (by decide) hs_l2_5
  have hu_s1_6 := hu_6 (by decide) hu_sum1
  refine wp_decl_none_int_seq (k := .u32) rfl rfl rfl rfl hf6 ?_
  intro b_rem m7 hf7 hu_rem hi_7 hu_7 _
  have hs_a1_7 := hi_7 (by decide) hs_a1_6
  have hs_a2_7 := hi_7 (by decide) hs_a2_6
  have hs_l2_7 := hi_7 (by decide) hs_l2_6
  have hu_s1_7 := hu_7 (by decide) hu_s1_6
  have hu_s2_7 := hu_7 (by decide) hu_sum2
  -- Distinctness of all 6 stack blocks from `hf7.2.2.1 : Nodup`
  have hnodup : ([b_rem, b_sum2, b_sum1, b_len2, b_adler2, b_adler1] : List BlockId).Nodup := hf7.2.2.1
  have hne_rem_s1 : b_rem ≠ b_sum1 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_rem_s2 : b_rem ≠ b_sum2 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_s1_s2 : b_sum1 ≠ b_sum2 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_l2_s1 : b_len2 ≠ b_sum1 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_l2_s2 : b_len2 ≠ b_sum2 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_l2_rem : b_len2 ≠ b_rem := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_a1_rem : b_adler1 ≠ b_rem := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_a2_rem : b_adler2 ≠ b_rem := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_a1_s1 : b_adler1 ≠ b_sum1 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_a2_s1 : b_adler2 ≠ b_sum1 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_a1_s2 : b_adler1 ≠ b_sum2 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_a2_s2 : b_adler2 ≠ b_sum2 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_l2_a1 : b_len2 ≠ b_adler1 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_l2_a2 : b_len2 ≠ b_adler2 := by intro h; rw [h] at hnodup; simp at hnodup
  refine wp_seq_step ?_
  -- Step: if (len2 < 0) return 0xffffffffUL;
  have hcond_lt : PureIntEval prog zlibPointerConfig ext _ m7 []
      (.binary .lt (.var "len2") (.lit 0)) .i32 (if len2.toInt < 0 then 1 else 0) (.int .i32) :=
    pureIntEval_bin (pureIntEval_var0 hs_l2_7) pureIntEval_lit (evalIntBinary_i64_lt_zero len2)
  refine wp_if_int hcond_lt ?_ ?_
  · intro _
    refine wp_return_int pureIntEval_lit rfl rfl rfl rfl ?_
    intro retBv
    exact hcont (.int .u64 retBv) _ (localFrameMem_roExt_unwind2 [b_rem, b_sum2, b_sum1] [b_len2, b_adler2, b_adler1] hf7) ⟨retBv, rfl⟩
  · intro hnotneg
    have hnonneg : 0 ≤ len2.toInt := by
      by_cases hlt : len2.toInt < 0
      · simp only [hlt, ↓reduceIte] at hnotneg
        exact absurd hnotneg (by decide)
      · omega
    refine WPTerm.of_det rfl ?_
    -- len2 %= 65521U;
    obtain ⟨l2_mod, hl2_mod⟩ := evalIntBinary_i64_mod_base hnonneg
    refine wp_assign_op_int hf7 (by simp) hs_l2_7 rfl pureIntEval_lit hl2_mod ?_
    intro len2' m8 hf8 hs_l2_8 hm8
    have hs_a1_8 := hs_a1_7.preserve_ne hm8 hne_l2_a1.symm
    have hs_a2_8 := hs_a2_7.preserve_ne hm8 hne_l2_a2.symm
    have hu_s1_8 := hu_s1_7.preserve_ne hm8 hne_l2_s1.symm
    have hu_s2_8 := hu_s2_7.preserve_ne hm8 hne_l2_s2.symm
    have hu_rem_8 := hu_rem.preserve_ne hm8 hne_l2_rem.symm
    refine wp_seq_step ?_
    -- rem = (unsigned)len2;
    refine wp_assign_eq_int hf8 (by simp) hu_rem_8
      (pureIntEval_cast_int (k2 := .u32) rfl (pureIntEval_var0 hs_l2_8)) ?_
    intro rem m9 hf9 hs_rem_9 hm9
    have hs_a1_9 := hs_a1_8.preserve_ne hm9 hne_a1_rem
    have hs_a2_9 := hs_a2_8.preserve_ne hm9 hne_a2_rem
    have hu_s1_9 := hu_s1_8.preserve_ne hm9 hne_rem_s1.symm
    have hu_s2_9 := hu_s2_8.preserve_ne hm9 hne_rem_s2.symm
    refine wp_seq_step ?_
    -- sum1 = adler1 & 0xffff;
    obtain ⟨s1_0, hs1_0⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_a1_9) pureIntEval_lit
      (evalIntBinary_unsigned_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (k1 := .u64) (k2 := .i32) rfl a1 (BitVec.ofInt 32 65535))
    refine wp_assign_eq_int hf9 (by simp) hu_s1_9 hs1_0 ?_
    intro sum1_1 m10 hf10 hs_s1_10 hm10
    have hs_a1_10 := hs_a1_9.preserve_ne hm10 hne_a1_s1
    have hs_a2_10 := hs_a2_9.preserve_ne hm10 hne_a2_s1
    have hs_rem_10 := hs_rem_9.preserve_ne hm10 hne_rem_s1
    have hu_s2_10 := hu_s2_9.preserve_ne hm10 hne_s1_s2.symm
    refine wp_seq_step ?_
    -- sum2 = rem * sum1;
    obtain ⟨s2_0, hs2_0⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_rem_10) (pureIntEval_var0 hs_s1_10)
      (evalIntBinary_unsigned_arith .mul (Or.inr (Or.inr (Or.inl rfl)))
        (k1 := .u32) (k2 := .u64) rfl rem sum1_1)
    refine wp_assign_eq_int hf10 (by simp) hu_s2_10 hs2_0 ?_
    intro sum2_1 m11 hf11 hs_s2_11 hm11
    have hs_a1_11 := hs_a1_10.preserve_ne hm11 hne_a1_s2
    have hs_a2_11 := hs_a2_10.preserve_ne hm11 hne_a2_s2
    have hs_rem_11 := hs_rem_10.preserve_ne hm11 hne_rem_s2
    have hs_s1_11 := hs_s1_10.preserve_ne hm11 hne_s1_s2
    refine wp_seq_step ?_
    -- sum2 %= 65521U;
    refine wp_mod_u32_u64 hf11 (by simp) hs_s2_11 (by decide) ?_
    intro sum2_2 m12 hf12 hs_s2_12 hm12_blocks
    have hs_a1_12 := hs_a1_11.preserve_blocks (hm12_blocks _ hne_a1_s2)
    have hs_a2_12 := hs_a2_11.preserve_blocks (hm12_blocks _ hne_a2_s2)
    have hs_rem_12 := hs_rem_11.preserve_blocks (hm12_blocks _ hne_rem_s2)
    have hs_s1_12 := hs_s1_11.preserve_blocks (hm12_blocks _ hne_s1_s2)
    refine wp_seq_step ?_
    -- sum1 += (adler2 & 0xffff) + 65521U - 1;
    obtain ⟨v_a2m, hv_a2m⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_a2_12) pureIntEval_lit
      (evalIntBinary_unsigned_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (k1 := .u64) (k2 := .i32) rfl a2 (BitVec.ofInt 32 65535))
    obtain ⟨v_add1, hv_add1⟩ := pureIntEval_bin_exists
      (pureIntEval_paren hv_a2m) pureIntEval_lit
      (evalIntBinary_unsigned_arith .add (Or.inl rfl) (k1 := .u64) (k2 := .u32) rfl v_a2m (BitVec.ofInt 32 65521))
    obtain ⟨v_sub1, hv_sub1⟩ := pureIntEval_bin_exists
      hv_add1 pureIntEval_lit
      (evalIntBinary_unsigned_arith .sub (Or.inr (Or.inl rfl)) (k1 := .u64) (k2 := .i32) rfl v_add1 (BitVec.ofInt 32 1))
    obtain ⟨v_s1_upd, hv_s1_upd⟩ := evalIntBinary_unsigned_arith .add (Or.inl rfl)
      (k1 := .u64) (k2 := .u64) rfl sum1_1 v_sub1
    refine wp_assign_op_int hf12 (by simp) hs_s1_12 rfl hv_sub1 hv_s1_upd ?_
    intro sum1_2 m13 hf13 hs_s1_13 hm13
    have hs_a1_13 := hs_a1_12.preserve_ne hm13 hne_a1_s1
    have hs_a2_13 := hs_a2_12.preserve_ne hm13 hne_a2_s1
    have hs_rem_13 := hs_rem_12.preserve_ne hm13 hne_rem_s1
    have hs_s2_13 := hs_s2_12.preserve_ne hm13 hne_s1_s2.symm
    refine wp_seq_step ?_
    -- sum2 += ((adler1 >> 16) & 0xffff) + ((adler2 >> 16) & 0xffff) + 65521U - rem;
    obtain ⟨v_sh1, hv_sh1⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_a1_13) pureIntEval_lit
      (evalIntBinary_unsigned_shift .shr (Or.inr rfl) (k1 := .u64) (k2 := .i32) rfl a1 (BitVec.ofInt 32 16)
        (by decide) (by decide))
    obtain ⟨v_m1, hv_m1⟩ := pureIntEval_bin_exists
      (pureIntEval_paren hv_sh1) pureIntEval_lit
      (evalIntBinary_unsigned_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (k1 := .u64) (k2 := .i32) rfl v_sh1 (BitVec.ofInt 32 65535))
    obtain ⟨v_sh2, hv_sh2⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_a2_13) pureIntEval_lit
      (evalIntBinary_unsigned_shift .shr (Or.inr rfl) (k1 := .u64) (k2 := .i32) rfl a2 (BitVec.ofInt 32 16)
        (by decide) (by decide))
    obtain ⟨v_m2, hv_m2⟩ := pureIntEval_bin_exists
      (pureIntEval_paren hv_sh2) pureIntEval_lit
      (evalIntBinary_unsigned_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (k1 := .u64) (k2 := .i32) rfl v_sh2 (BitVec.ofInt 32 65535))
    obtain ⟨v_add2a, hv_add2a⟩ := pureIntEval_bin_exists
      (pureIntEval_paren hv_m1) (pureIntEval_paren hv_m2)
      (evalIntBinary_unsigned_arith .add (Or.inl rfl) (k1 := .u64) (k2 := .u64) rfl v_m1 v_m2)
    obtain ⟨v_add2b, hv_add2b⟩ := pureIntEval_bin_exists
      hv_add2a pureIntEval_lit
      (evalIntBinary_unsigned_arith .add (Or.inl rfl) (k1 := .u64) (k2 := .u32) rfl v_add2a (BitVec.ofInt 32 65521))
    obtain ⟨v_sub2, hv_sub2⟩ := pureIntEval_bin_exists
      hv_add2b (pureIntEval_var0 hs_rem_13)
      (evalIntBinary_unsigned_arith .sub (Or.inr (Or.inl rfl)) (k1 := .u64) (k2 := .u32) rfl v_add2b rem)
    obtain ⟨v_s2_upd, hv_s2_upd⟩ := evalIntBinary_unsigned_arith .add (Or.inl rfl)
      (k1 := .u64) (k2 := .u64) rfl sum2_2 v_sub2
    refine wp_assign_op_int hf13 (by simp) hs_s2_13 rfl hv_sub2 hv_s2_upd ?_
    intro sum2_3 m14 hf14 hs_s2_14 hm14
    have hs_s1_14 := hs_s1_13.preserve_ne hm14 hne_s1_s2
    refine wp_seq_step ?_
    -- if (sum1 >= 65521U) sum1 -= 65521U;
    refine wp_if_ge_sub_u32 hf14 (by simp) hs_s1_14 rfl ?_
    intro sum1_3 m15 hf15 hs_s1_15 hm15_blocks
    have hs_s2_15 := hs_s2_14.preserve_blocks (hm15_blocks _ hne_s1_s2.symm)
    refine wp_seq_step ?_
    -- if (sum1 >= 65521U) sum1 -= 65521U;
    refine wp_if_ge_sub_u32 hf15 (by simp) hs_s1_15 rfl ?_
    intro sum1_4 m16 hf16 hs_s1_16 hm16_blocks
    have hs_s2_16 := hs_s2_15.preserve_blocks (hm16_blocks _ hne_s1_s2.symm)
    refine wp_seq_step ?_
    -- if (sum2 >= ((unsigned long)65521U << 1)) sum2 -= ((unsigned long)65521U << 1);
    refine wp_if_ge_sub_u64_shl hf16 (by simp) hs_s2_16 (by decide) (by decide) rfl ?_
    intro sum2_4 m17 hf17 hs_s2_17 hm17_blocks
    have hs_s1_17 := hs_s1_16.preserve_blocks (hm17_blocks _ hne_s1_s2)
    refine wp_seq_step ?_
    -- if (sum2 >= 65521U) sum2 -= 65521U;
    refine wp_if_ge_sub_u32 hf17 (by simp) hs_s2_17 rfl ?_
    intro sum2_5 m18 hf18 hs_s2_18 hm18_blocks
    have hs_s1_18 := hs_s1_17.preserve_blocks (hm18_blocks _ hne_s1_s2)
    refine wp_seq_step ?_
    obtain ⟨v_sh, hv_sh⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_s2_18) pureIntEval_lit
      (evalIntBinary_unsigned_shift .shl (Or.inl rfl) (k1 := .u64) (k2 := .i32) rfl
        sum2_5 (BitVec.ofInt 32 16) (by decide) (by decide))
    obtain ⟨v_ret, hv_ret⟩ := pureIntEval_bin_exists
      (pureIntEval_var0 hs_s1_18) (pureIntEval_paren hv_sh)
      (evalIntBinary_unsigned_arith .bitOr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        (k1 := .u64) (k2 := .u64) rfl sum1_4 v_sh)
    refine wp_return_int hv_ret rfl rfl rfl rfl ?_
    intro retBv
    exact hcont (.int .u64 retBv) _ (localFrameMem_roExt_unwind2 [b_rem, b_sum2, b_sum1] [b_len2, b_adler2, b_adler1] hf18) ⟨retBv, rfl⟩

private theorem adler32_combine_wrapper_spec
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} (ext : ExtHandler)
    (hlib : InitLibzProps prog gEnv m0 os0)
    (fn : FnDef)
    (hstatics : prog.fnStatics fn.name = [])
    (hretTy : fn.retTy = .typedef "uLong" (.int .u64))
    (hlen2Ty : ∃ nm, fn.params =
      [{ name := "adler1", ty := .typedef "uLong" (.int .u64) },
       { name := "adler2", ty := .typedef "uLong" (.int .u64) },
       { name := "len2", ty := .typedef nm (.int .i64) }])
    (hbody : fn.body = CStmt.block [
      .returnStmt (some (.call (.var "adler32_combine_") [.var "adler1", .var "adler2", .var "len2"]))]) :
    FuncBodySpec prog zlibPointerConfig ext fn
      (fun _ args => ∃ (a1 a2 len2 : BitVec 64),
        args = [.int .u64 a1, .int .u64 a2, .int .i64 len2])
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨a1, a2, len2, hargs⟩ _ hpush hcont
  subst hargs
  rcases hlen2Ty with ⟨len2Nm, hparams⟩
  rw [hparams] at hpush
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hsz0, hal0, hba0, m2_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m3_p, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m4_p, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let env0 := prog.fnStatics fn.name ++ prog.globalEnv
  let b_adler1 := m.nextBlock
  let b_adler2 := m2_p.nextBlock
  let b_len2 := m3_p.nextBlock
  have hs_adler1_0 : IntSlot (("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0)
      m2_p "adler1" b_adler1 (.typedef "uLong" (.int .u64)) .u64 a1 :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr0 env0
  have hne_1_2_mid : b_adler1 ≠ m2_p.nextBlock := by
    have hlt : b_adler1 < m2_p.nextBlock := lt_nextBlock_of_some hs_adler1_0.2.2.2.choose_spec.1
    exact Nat.ne_of_lt hlt
  have hs_adler1_1 : IntSlot (("adler2", b_adler2, .typedef "uLong" (.int .u64)) ::
      ("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0)
      m3_p "adler1" b_adler1 (.typedef "uLong" (.int .u64)) .u64 a1 :=
    (hs_adler1_0.preserve_alloc rfl (by decide)).preserve_ne hwr1 hne_1_2_mid
  have hs_adler2_1 : IntSlot (("adler2", b_adler2, .typedef "uLong" (.int .u64)) ::
      ("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0)
      m3_p "adler2" b_adler2 (.typedef "uLong" (.int .u64)) .u64 a2 :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr1 _
  have hne_1_2 : b_adler1 ≠ b_len2 := by
    have h1 : b_adler1 < m2_p.nextBlock := lt_nextBlock_of_some hs_adler1_0.2.2.2.choose_spec.1
    have h2 : m2_p.nextBlock < m3_p.nextBlock := nextBlock_lt_of_writeAlloc hwr1
    exact Nat.ne_of_lt (Nat.lt_trans h1 h2)
  have hne_2_2 : b_adler2 ≠ b_len2 := by
    have h1 : b_adler2 < m3_p.nextBlock := lt_nextBlock_of_some hs_adler2_1.2.2.2.choose_spec.1
    exact Nat.ne_of_lt h1
  let env_params : Env := ("len2", b_len2, .typedef len2Nm (.int .i64)) ::
    ("adler2", b_adler2, .typedef "uLong" (.int .u64)) ::
    ("adler1", b_adler1, .typedef "uLong" (.int .u64)) :: env0
  have hs_adler1_2 : IntSlot env_params m1 "adler1" b_adler1 (.typedef "uLong" (.int .u64)) .u64 a1 :=
    (hs_adler1_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_1_2
  have hs_adler2_2 : IntSlot env_params m1 "adler2" b_adler2 (.typedef "uLong" (.int .u64)) .u64 a2 :=
    (hs_adler2_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_2_2
  have hs_len2_2 : IntSlot env_params m1 "len2" b_len2 (.typedef len2Nm (.int .i64)) .i64 len2 :=
    IntSlot.of_pushCallParam (k := .i64) rfl rfl hwr2 _
  have hg_none : env0.lookup "adler32_combine_" = none := by
    dsimp [env0]
    rw [hstatics, hlib.globalEnv_eq]
    exact hlib.gEnv_lookup_none "adler32_combine_" (by decide)
  have henv_none : env_params.lookup "adler32_combine_" = none := by
    dsimp [env_params]
    rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
    exact hg_none
  have henum : enumConst? prog.tags "adler32_combine_" = none :=
    enumConst_prog_adler32_combine_ prog.tags hlib.prog_tags_eq
  have hproto := prog_fnProtos_adler32_combine_ hlib
  let fnTy := CTy.fnPtr Zlib.Adler32.adler32TU_fn_adler32_combine_.retTy
    (Zlib.Adler32.adler32TU_fn_adler32_combine_.params.map (·.ty))
    Zlib.Adler32.adler32TU_fn_adler32_combine_.variadic
  rw [hbody]
  refine WPTerm.of_det rfl ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  have hlu_fn : stepExprPure prog zlibPointerConfig env_params m1 []
      (.eval .rval (.var "adler32_combine_") [.callFnF [.var "adler1", .var "adler2", .var "len2"]]) =
      some (.ret (.rval (.fnPtr "adler32_combine_") fnTy) [.callFnF [.var "adler1", .var "adler2", .var "len2"]],
        m1, []) := by
    simp [stepExprPure, henv_none, henum, hproto, fnDefSig, fnTy]
  refine WPTerm.of_exprPure hlu_fn ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureIntEval_var0 hs_adler1_2).2
    [.callArgF "adler32_combine_" fnTy [] [.var "adler2", .var "len2"]]
    .returnVal [] os _ Q ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureIntEval_var0 hs_adler2_2).2
    [.callArgF "adler32_combine_" fnTy [(.int .u64 a1, (CTy.typedef "uLong" (.int .u64)).decay)] [.var "len2"]]
    .returnVal [] os _ Q ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureIntEval_var0 hs_len2_2).2
    [.callArgF "adler32_combine_" fnTy
      [(.int .u64 a1, (CTy.typedef "uLong" (.int .u64)).decay),
       (.int .u64 a2, (CTy.typedef "uLong" (.int .u64)).decay)] []]
    .returnVal [] os _ Q ?_
  have hcoerce : Sem.coerceCallArgs m1
      (Zlib.Adler32.adler32TU_fn_adler32_combine_.params.map (·.ty)) false
      [(.int .u64 a1, (CTy.typedef "uLong" (.int .u64)).decay),
       (.int .u64 a2, (CTy.typedef "uLong" (.int .u64)).decay),
       (.int .i64 len2, (CTy.typedef len2Nm (.int .i64)).decay)] =
      some [.int .u64 a1, .int .u64 a2, .int .i64 len2] := by
    simp [Zlib.Adler32.adler32TU_fn_adler32_combine_, Sem.coerceCallArgs, Sem.castVal,
      CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast, IntKind.signed, IntKind.bits,
      BitVec.ofInt_toInt]
  have hsimp : ∀ p ∈ Zlib.Adler32.adler32TU_fn_adler32_combine_.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Adler32.adler32TU_fn_adler32_combine_] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  refine FuncBodySpec.call (adler32_combine__spec prog ext) rfl (prog_fns_adler32_combine_ hlib)
    rfl rfl hcoerce ⟨a1, a2, len2, rfl⟩ hsimp ?_
  intro ret m' hro ⟨retBv, hret⟩
  subst hret
  have hcast : Sem.castVal m' (.typedef "uLong" (.int .u64)) (.int .u64 retBv) = some (.int .u64 retBv) := by
    rw [castVal_unqual]
    change Sem.castVal m' (.int .u64) (.int .u64 retBv) = some (.int .u64 retBv)
    exact castVal_int_self m' .u64 retBv
  refine WPTerm.of_det ?_ (hcont (.int .u64 retBv) (m'.freeStack [b_len2, b_adler2, b_adler1])
    (LocalFrameMem.roExt_freeStack (hf1.of_roExt hro)) ⟨retBv, rfl⟩)
  unfold stepDet
  simp [Cont.topRetTy, hretTy, CTy.isVoid, CTy.unqual, hcast, unwindReturn, freeStack_nil]
  rfl

private theorem argsWellTyped_u64_u64_i64 {paramTys : List CTy} {args : List Val}
    (hp : paramTys.map CTy.unqual = [.int .u64, .int .u64, .int .i64])
    (hawt : Zlib.Spec.ArgsWellTyped paramTys false args) :
    ∃ (a1 a2 len2 : BitVec 64), args = [.int .u64 a1, .int .u64 a2, .int .i64 len2] := by
  rcases hawt with ⟨hlen, hval⟩
  have hlen3 : args.length = 3 := by
    have hplen : paramTys.length = 3 := by
      have := congrArg List.length hp
      simpa using this
    simpa [hplen] using hlen
  cases args with | nil => simp at hlen3 | cons x0 xs0 =>
  cases xs0 with | nil => simp at hlen3 | cons x1 xs1 =>
  cases xs1 with | nil => simp at hlen3 | cons x2 xs2 =>
  cases xs2 with
  | cons _ _ => simp at hlen3
  | nil =>
    cases paramTys with | nil => simp at hp | cons p0 ps0 =>
    cases ps0 with | nil => simp at hp | cons p1 ps1 =>
    cases ps1 with | nil => simp at hp | cons p2 ps2 =>
    cases ps2 with
    | cons _ _ => simp at hp
    | nil =>
      simp only [List.map_cons, List.cons.injEq] at hp
      have hv0 := hval 0 (by simp)
      have hv1 := hval 1 (by simp)
      have hv2 := hval 2 (by simp)
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem_cons_zero,
        List.getElem_cons_succ, Zlib.Spec.ValHasCTy, hp.1, hp.2.1, hp.2.2.1] at hv0 hv1 hv2
      rcases hv0 with ⟨a1, rfl⟩
      rcases hv1 with ⟨a2, rfl⟩
      rcases hv2 with ⟨len2, rfl⟩
      exact ⟨a1, a2, len2, rfl⟩

theorem adler32_combine_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (zlibExt userExt) Inv userWrite
      Zlib.Adler32.adler32_combine_contract := by
  have hspec := adler32_combine_wrapper_spec (zlibExt userExt) hlib
    Zlib.Adler32.adler32TU_fn_adler32_combine
    (prog_fnStatics_adler32_combine hlib) rfl ⟨"z_off_t", rfl⟩ rfl
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_adler32_combine hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_adler32_combine hlib) rfl ?_ hspec ?_ ?_
  · intro p hp
    simp [Zlib.Adler32.adler32TU_fn_adler32_combine] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args _ _ hawt
    exact argsWellTyped_u64_u64_i64 rfl hawt
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨a1, a2, len2, rfl⟩ := argsWellTyped_u64_u64_i64 rfl hawt
    have hcast : Sem.castVal m' Zlib.Adler32.adler32_combine_contract.retTy (.int .u64 bv) =
        some (.int .u64 bv) := by
      rw [castVal_unqual]
      change Sem.castVal m' (.int .u64) (.int .u64 bv) = some (.int .u64 bv)
      exact castVal_int_self m' .u64 bv
    refine ⟨.int .u64 bv, hcast, ?_⟩
    simp [Zlib.Adler32.adler32_combine_contract]

theorem adler32_combine64_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (zlibExt userExt) Inv userWrite
      Zlib.Adler32.adler32_combine64_contract := by
  have hspec := adler32_combine_wrapper_spec (zlibExt userExt) hlib
    Zlib.Adler32.adler32TU_fn_adler32_combine64
    (prog_fnStatics_adler32_combine64 hlib) rfl ⟨"z_off64_t", rfl⟩ rfl
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_adler32_combine64 hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_adler32_combine64 hlib) rfl ?_ hspec ?_ ?_
  · intro p hp
    simp [Zlib.Adler32.adler32TU_fn_adler32_combine64] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args _ _ hawt
    exact argsWellTyped_u64_u64_i64 rfl hawt
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨a1, a2, len2, rfl⟩ := argsWellTyped_u64_u64_i64 rfl hawt
    have hcast : Sem.castVal m' Zlib.Adler32.adler32_combine64_contract.retTy (.int .u64 bv) =
        some (.int .u64 bv) := by
      rw [castVal_unqual]
      change Sem.castVal m' (.int .u64) (.int .u64 bv) = some (.int .u64 bv)
      exact castVal_int_self m' .u64 bv
    refine ⟨.int .u64 bv, hcast, ?_⟩
    simp [Zlib.Adler32.adler32_combine64_contract]

/-! ## 5. `DO1`–`DO16`, Pointer Arithmetic, and Loop Combinators for `adler32_z` -/

private abbrev bytefElTy : CTy := .const_ (.typedef "Bytef" (.typedef "Byte" (.int .u8)))
private abbrev bytefPtrTy : CTy := .ptr bytefElTy
private abbrev uLongTy : CTy := .typedef "uLong" (.int .u64)
private abbrev zSizeTy : CTy := .typedef "z_size_t" (.int .u64)

private def mkDO1 (idx : CExpr) : CStmt :=
  .block [
    .expr (.assign .addEq (.var "adler") ((CExpr.var "buf").paren.index idx)),
    .expr (.assign .addEq (.var "sum2") (.var "adler"))
  ]

private def mkDO2 (i : CExpr) : CStmt :=
  .block [mkDO1 i, mkDO1 (CExpr.binary .add i (.lit 1)).paren]

private def mkDO4 (i : CExpr) : CStmt :=
  .block [mkDO2 i, mkDO2 (CExpr.binary .add i (.lit 2)).paren]

private def mkDO8 (i : CExpr) : CStmt :=
  .block [mkDO4 i, mkDO4 (CExpr.binary .add i (.lit 4)).paren]

private def mkDO16 : CStmt :=
  .block [mkDO8 (.lit 0), mkDO8 (.lit 8)]

private theorem bv32_ofInt_toInt_small {iv : Int} (hlo : 0 ≤ iv) (hhi : iv < 1000) :
    (BitVec.ofInt 32 iv).toInt = iv := by
  rw [BitVec.toInt_ofInt]
  change iv.bmod (4294967296 : Nat) = iv
  exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem evalIntBinary_add_smallI32 {a b : Int}
    (ha0 : 0 ≤ a) (ha1 : a < 1000) (hb0 : 0 ≤ b) (hb1 : b < 1000) (hs : a + b < 1000) :
    evalIntBinary .add (.int .i32 (BitVec.ofInt 32 a)) (.int .i32 (BitVec.ofInt 32 b)) =
      some (.int .i32 (BitVec.ofInt 32 (a + b)), .int .i32) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .i32 (BitVec.ofInt 32 a)) = some (.i32, (BitVec.ofInt 32 a).toInt) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 b)) = some (.i32, (BitVec.ofInt 32 b).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .i32 .i32 = .i32 := rfl
  rw [hu]
  have ha_eq : (BitVec.ofInt 32 a).toInt = a := bv32_ofInt_toInt_small ha0 ha1
  have hb_eq : (BitVec.ofInt 32 b).toInt = b := bv32_ofInt_toInt_small hb0 hb1
  have ha2 : (BitVec.ofInt 32 (BitVec.ofInt 32 a).toInt).toInt = a := by rw [ha_eq]; exact ha_eq
  have hb2 : (BitVec.ofInt 32 (BitVec.ofInt 32 b).toInt).toInt = b := by rw [hb_eq]; exact hb_eq
  have hin : IntKind.i32.inRange (a + b) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits]
    have h31 : (2 ^ (32 - 1) : Int) = 2147483648 := by decide
    rw [h31]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, ha2, hb2, ofIntExact_signed (k := .i32) rfl hin]

private def evalSmallI32? : CExpr → Option Int
  | .lit n .i32 .none .dec none => if 0 ≤ n ∧ n < 1000 then some n else none
  | .paren e => evalSmallI32? e
  | .binary .add l r => do
    let a ← evalSmallI32? l
    let b ← evalSmallI32? r
    let s := a + b
    if 0 ≤ s ∧ s < 1000 then some s else none
  | _ => none

private theorem pureIntEval_smallI32 {prog cfg ext env m mods} :
    ∀ {e iv}, evalSmallI32? e = some iv →
      0 ≤ iv ∧ iv < 1000 ∧
      PureIntEval prog cfg ext env m mods e .i32 (BitVec.ofInt 32 iv) (.int .i32)
  | .lit n .i32 .none .dec none, iv, h => by
    simp only [evalSmallI32?] at h
    split at h
    · next hc =>
      cases h
      exact ⟨hc.1, hc.2, pureIntEval_lit⟩
    · cases h
  | .paren e, iv, h => by
    obtain ⟨h0, h1, he⟩ := pureIntEval_smallI32 (e := e) h
    exact ⟨h0, h1, pureIntEval_paren he⟩
  | .binary .add l r, iv, h => by
    simp only [evalSmallI32?, bind, Option.bind] at h
    cases hl : evalSmallI32? l with
    | none => simp [hl] at h
    | some a =>
      rw [hl] at h
      cases hr : evalSmallI32? r with
      | none => simp [hr] at h
      | some b =>
        rw [hr] at h
        dsimp only at h
        split at h
        · next hs =>
          cases h
          obtain ⟨ha0, ha1, hpl⟩ := pureIntEval_smallI32 (e := l) hl
          obtain ⟨hb0, hb1, hpr⟩ := pureIntEval_smallI32 (e := r) hr
          exact ⟨hs.1, hs.2, pureIntEval_bin hpl hpr (evalIntBinary_add_smallI32 ha0 ha1 hb0 hb1 hs.2)⟩
        · cases h
  | .lit _ .i32 .none .dec (some _), _, h | .lit _ .i32 .none .hex _, _, h
  | .lit _ .i32 .none .oct _, _, h | .lit _ .i32 .U _ _, _, h
  | .lit _ .i32 .L _ _, _, h | .lit _ .i32 .UL _ _, _, h
  | .lit _ .i32 .LL _ _, _, h | .lit _ .i32 .ULL _ _, _, h
  | .lit _ .u32 _ _ _, _, h | .lit _ .i64 _ _ _, _, h | .lit _ .u64 _ _ _, _, h
  | .lit _ .i8 _ _ _, _, h | .lit _ .u8 _ _ _, _, h | .lit _ .i16 _ _ _, _, h | .lit _ .u16 _ _ _, _, h
  | .strLit _, _, h | .var _, _, h | .sizeOfTy _, _, h | .sizeOfExpr _, _, h
  | .cast _ _, _, h | .unary _ _, _, h | .addrOf _, _, h | .deref _, _, h | .index _ _, _, h
  | .member _ _, _, h | .arrow _ _, _, h | .binary .sub _ _, _, h | .binary .mul _ _, _, h
  | .binary .div _ _, _, h | .binary .mod _ _, _, h | .binary .bitAnd _ _, _, h
  | .binary .bitOr _ _, _, h | .binary .bitXor _ _, _, h | .binary .shl _ _, _, h
  | .binary .shr _ _, _, h | .binary .eq _ _, _, h | .binary .ne _ _, _, h
  | .binary .lt _ _, _, h | .binary .le _ _, _, h | .binary .gt _ _, _, h | .binary .ge _ _, _, h
  | .logAnd _ _, _, h | .logOr _ _, _, h | .cond _ _ _, _, h | .comma _ _, _, h
  | .assign _ _ _, _, h | .incDec _ _, _, h | .call _ _, _, h | .vaStart _ _, _, h | .vaEnd _, _, h => by
    simp [evalSmallI32?] at h

private def PurePtrEval (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (env : Env) (m : Mem) (mods : ModSet) (e : CExpr)
    (el : CTy) (p : Val) (rty : CTy) : Prop :=
  rty.unqual = .ptr el ∧
  ∀ fs ctx blks os k_cont Q,
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval p rty) fs) ctx mods) env blks m os k_cont) →
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval e fs) ctx mods) env blks m os k_cont)

private theorem purePtrEval_var {prog cfg ext env m mods x b ty el p}
    (hs : PtrSlot env m x b ty el p) (hnc : mods.conflicts b 0 8 = false) :
    PurePtrEval prog cfg ext env m mods (.var x) el p ty.decay := by
  refine ⟨CTy.decay_of_ptr hs.2.1, fun fs ctx blks os k_cont Q hw => ?_⟩
  refine WPTerm.of_exprPure ?_ hw
  simp [stepExprPure, hs.1, readPlace_ptrSlot hs hnc]

private theorem purePtrEval_paren {prog cfg ext env m mods e el p rty}
    (he : PurePtrEval prog cfg ext env m mods e el p rty) :
    PurePtrEval prog cfg ext env m mods (.paren e) el p rty := by
  refine ⟨he.1, fun fs ctx blks os k_cont Q hw => ?_⟩
  exact WPTerm.of_exprPure rfl (he.2 fs ctx blks os k_cont Q hw)

private theorem sizeofTy_bytefEl (tags : TypeEnv) : sizeofTy tags bytefElTy = 1 := by
  rw [← sizeofTy_unqual]
  have hu : bytefElTy.unqual = .int .u8 := rfl
  rw [hu, sizeofTy_int]
  rfl

private theorem evalPtrAdd_byte_inBounds {tags : TypeEnv} {m : Mem} {pb : BlockId} {poff : Int64}
    {blk : Block} {d : Int}
    (hblk : m.blocks pb = some blk)
    (hlo : 0 ≤ poff.toInt + d) (hhi : poff.toInt + d ≤ (blk.size : Int)) :
    evalPtrAdd zlibPointerConfig tags m (.ptr pb poff) bytefElTy d =
      some (.ptr pb (Int64.ofInt (poff.toInt + d))) := by
  by_cases hd0 : d = 0
  · subst hd0
    have heq : Int64.ofInt (poff.toInt + 0) = poff := by
      rw [Int.add_zero, Int64.ofInt_toInt]
    unfold evalPtrAdd
    simp only [beq_self_eq_true, Bool.true_and, zlibPointerConfig, ↓reduceIte, heq]
  · have hb : (d == 0 && zlibPointerConfig.allowAddZeroAny) = false := by
      simp [beq_false_of_ne hd0]
    unfold evalPtrAdd
    rw [sizeofTy_bytefEl]
    have hmax1 : (max 1 ↑(1 : Nat) : Int) = 1 := rfl
    rw [hmax1]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hblk, Int.mul_one,
      decide_eq_true hlo, decide_eq_true hhi, Bool.and_self, guard_true,
      bind, Option.bind, pure, Pure.pure]

private theorem evalIntBinary_u64_add_u8 (v1 : BitVec 64) (v2 : BitVec 8) :
    ∃ obv : BitVec 64,
      evalIntBinary .add (.int .u64 v1) (.int .u8 v2) = some (.int .u64 obv, .int .u64) :=
  evalIntBinary_unsigned_arith .add (Or.inl rfl) (k1 := .u64) (k2 := .u8) rfl v1 v2

private theorem wp_adler_add_byte_index {prog ext env blks frameBlks m0 m os k_cont Q
    x_adler b_adler ty_adler v_adler pb poff remLen e_buf rty_buf e_idx iv}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b_adler ∈ frameBlks)
    (hs_a : IntSlot env m x_adler b_adler ty_adler .u64 v_adler)
    (hr : Readable m0 (.ptr pb poff) remLen)
    (hiv_lo : 0 ≤ iv) (hiv_hi : iv < 1000) (hiv_lt : iv.toNat < remLen)
    (he_buf : PurePtrEval prog zlibPointerConfig ext env m [] e_buf bytefElTy (.ptr pb poff) rty_buf)
    (he_idx : PureIntEval prog zlibPointerConfig ext env m [] e_idx .i32 (BitVec.ofInt 32 iv) (.int .i32))
    (hcont : ∀ v_adler' m',
      LocalFrameMem m0 m' frameBlks →
      IntSlot env m' x_adler b_adler ty_adler .u64 v_adler' →
      (∀ b' ≠ b_adler, m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .addEq (.var x_adler) (.index e_buf e_idx))))
        env blks m os k_cont) := by
  have hpb_lt : pb < m0.nextBlock := readable_block_lt hr
  have hba_ge : m0.nextBlock ≤ b_adler := (hf.2.2.2.1 b_adler hmem).1
  have hne_pb : pb ≠ b_adler := Nat.ne_of_lt (Nat.lt_of_lt_of_le hpb_lt hba_ge)
  obtain ⟨blk, byteBv, hblk, hlo, hhi, hrv_byte⟩ := Readable.read_byte hf hr hiv_lt
  have hidx_eq : iv = (iv.toNat : Int) := by omega
  have hlo' : 0 ≤ poff.toInt + (BitVec.ofInt 32 iv).toInt := by
    rw [bv32_ofInt_toInt_small hiv_lo hiv_hi]; omega
  have hhi' : poff.toInt + (BitVec.ofInt 32 iv).toInt ≤ (blk.size : Int) := by
    rw [bv32_ofInt_toInt_small hiv_lo hiv_hi]; omega
  have hptr_add : evalPtrAdd zlibPointerConfig prog.tags m (.ptr pb poff) bytefElTy
      (BitVec.ofInt 32 iv).toInt =
      some (.ptr pb (Int64.ofInt (poff.toInt + (iv.toNat : Int)))) := by
    have hp := evalPtrAdd_byte_inBounds (tags := prog.tags) hblk hlo' hhi'
    simpa [bv32_ofInt_toInt_small hiv_lo hiv_hi, ← hidx_eq] using hp
  have hrv_byte' : Sem.readVal prog.tags m pb (Int64.ofInt (poff.toInt + (iv.toNat : Int))) bytefElTy =
      some (.int .u8 byteBv) := hrv_byte
  have hrp_byte : readPlace prog.tags m [] .rval pb (Int64.ofInt (poff.toInt + (iv.toNat : Int))) bytefElTy =
      some (.rval (.int .u8 byteBv) bytefElTy.decay) := by
    unfold readPlace
    have hu : bytefElTy.unqual = .int .u8 := rfl
    rw [hu]
    simp only [sizeofTy_bytefEl]
    have hc : ModSet.conflicts [] pb (Int64.ofInt (poff.toInt + (iv.toNat : Int))) 1 = false := rfl
    rw [hc]
    simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv_byte']
  obtain ⟨obv, hadd⟩ := evalIntBinary_u64_add_u8 v_adler byteBv
  let v_adler' : BitVec 64 := BitVec.ofInt 64 obv.toNat
  obtain ⟨m', hm', hf', hs_a'⟩ := hs_a.to_uninit.write hf hmem v_adler'
  have hcast_a : Sem.castVal m ty_adler (.int .u64 obv) = some (.int .u64 v_adler') :=
    castVal_int_eq_some (k1 := .u64) hs_a.2.1 obv
  have hwp_a : writePlace prog.tags m b_adler 0 ty_adler (.rval (.int .u64 obv) ty_adler) =
      some (.rval (.int .u64 v_adler') ty_adler, m') := by
    unfold writePlace
    simp only [hs_a.2.1, hcast_a, bind, Option.bind, pure, Pure.pure, hm']
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hs_a.1) ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine he_buf.2 [.indexBaseF .rval e_idx, .assignRhsF .addEq b_adler 0 ty_adler]
    .discard blks os k_cont Q ?_
  refine WPTerm.of_exprPure rfl ?_
  refine he_idx.2 [.indexIdxF .rval (.ptr pb poff) rty_buf, .assignRhsF .addEq b_adler 0 ty_adler]
    .discard blks os k_cont Q ?_
  have hv_idx : valAsInt? (.int .i32 (BitVec.ofInt 32 iv)) =
      some (.i32, (BitVec.ofInt 32 iv).toInt) := rfl
  have hstep_idx : stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (.int .i32 (BitVec.ofInt 32 iv)) (.int .i32))
        [.indexIdxF .rval (.ptr pb poff) rty_buf, .assignRhsF .addEq b_adler 0 ty_adler]) =
      some (.ret (.rval (.int .u8 byteBv) bytefElTy.decay) [.assignRhsF .addEq b_adler 0 ty_adler],
        m, []) := by
    simp only [stepExprPure, he_buf.1, hv_idx, hptr_add, hrp_byte, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_exprPure hstep_idx ?_
  have hc0 : ModSet.conflicts [] b_adler 0 (sizeofTy prog.tags ty_adler) = false := rfl
  have hstep_wr : stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (.int .u8 byteBv) bytefElTy.decay) [.assignRhsF .addEq b_adler 0 ty_adler]) =
      some (.ret (.rval (.int .u64 v_adler') ty_adler) [], m', [⟨b_adler, 0, sizeofTy prog.tags ty_adler⟩]) := by
    have hdu : bytefElTy.decay.unqual = .int .u8 := rfl
    simp only [stepExprPure, hc0, Bool.not_false, guard_true, assignOpToBin?, hs_a.readVal_eq,
      applyBinary_int hs_a.2.1 hdu, hadd, hwp_a, bind, Option.bind, pure, Pure.pure]
  exact WPTerm.of_exprPure hstep_wr (WPTerm.of_det rfl
    (hcont v_adler' m' hf' hs_a' (fun _ hne => writeVal_blocks_ne hm' hne)))

private def DOInv (m0 m_entry : Mem) (frameBlks : List BlockId)
    (b_adler b_sum2 b_buf : BlockId) (ty_adler ty_sum2 ty_buf : CTy)
    (pb : BlockId) (poff : Int64)
    (env : Env) (_blks : List BlockId) (m : Mem) : Prop :=
  LocalFrameMem m0 m frameBlks ∧
  b_adler ∈ frameBlks ∧
  b_sum2 ∈ frameBlks ∧
  b_adler ≠ b_sum2 ∧
  b_buf ≠ b_adler ∧
  b_buf ≠ b_sum2 ∧
  (∃ va, IntSlot env m "adler" b_adler ty_adler .u64 va) ∧
  (∃ vs, IntSlot env m "sum2" b_sum2 ty_sum2 .u64 vs) ∧
  PtrSlot env m "buf" b_buf ty_buf bytefElTy (.ptr pb poff) ∧
  (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → m.blocks b' = m_entry.blocks b')

private theorem wp_do1_step {prog ext m0 m_entry frameBlks b_adler b_sum2 b_buf ty_adler ty_sum2 ty_buf
    pb poff remLen idx iv}
    (hr : Readable m0 (.ptr pb poff) remLen)
    (he_idx : evalSmallI32? idx = some iv) (hiv_lt : iv.toNat < remLen) :
    StmtPres prog zlibPointerConfig ext
      (DOInv m0 m_entry frameBlks b_adler b_sum2 b_buf ty_adler ty_sum2 ty_buf pb poff)
      (DOInv m0 m_entry frameBlks b_adler b_sum2 b_buf ty_adler ty_sum2 ty_buf pb poff)
      (mkDO1 idx) := by
  intro env blks m os k Q hinv hcont
  rcases hinv with ⟨hf, ha_mem, hs_mem, hne_as, hne_ba, hne_bs, ⟨va, hsa⟩, ⟨vs, hss⟩, hbuf, hm_eq⟩
  obtain ⟨hiv0, hiv1, hp_idx⟩ := pureIntEval_smallI32 (prog := prog) (cfg := zlibPointerConfig)
    (ext := ext) (env := env) (m := m) (mods := []) he_idx
  have hp_buf : PurePtrEval prog zlibPointerConfig ext env m []
      (.paren (.var "buf")) bytefElTy (.ptr pb poff) ty_buf.decay :=
    purePtrEval_paren (purePtrEval_var hbuf rfl)
  refine WPTerm.of_det rfl ?_
  refine wp_adler_add_byte_index hf ha_mem hsa hr hiv0 hiv1 hiv_lt hp_buf hp_idx ?_
  intro va' m1 hf1 hsa1 hm1
  have hss1 := hss.preserve_blocks (hm1 _ hne_as.symm)
  have hbuf1 := hbuf.preserve_blocks (hm1 _ hne_ba)
  refine wp_seq_step ?_
  obtain ⟨obv, hadd⟩ := evalIntBinary_unsigned_arith .add (Or.inl rfl)
    (k1 := .u64) (k2 := .u64) rfl vs va'
  refine wp_assign_op_int hf1 hs_mem hss1 rfl (pureIntEval_var0 hsa1) hadd ?_
  intro vs' m2 hf2 hss2 hm2
  have hsa2 := hsa1.preserve_ne hm2 hne_as
  have hbuf2 := hbuf1.preserve_ne hm2 hne_bs
  refine wp_seq_nil (wp_blockEnd_free ?_)
  rw [freeStack_nil]
  refine hcont m2 ⟨hf2, ha_mem, hs_mem, hne_as, hne_ba, hne_bs, ⟨va', hsa2⟩, ⟨vs', hss2⟩, hbuf2, ?_⟩
  intro b' hne1 hne2
  rw [writeVal_blocks_ne hm2 hne2, hm1 b' hne1, hm_eq b' hne1 hne2]

private inductive SafeDOBlock (avail : Nat) : CStmt → Prop where
  | leaf (idx : CExpr) (iv : Int) :
      evalSmallI32? idx = some iv →
      0 ≤ iv →
      iv.toNat < avail →
      SafeDOBlock avail (mkDO1 idx)
  | seq (s1 s2 : CStmt) :
      SafeDOBlock avail s1 →
      SafeDOBlock avail s2 →
      SafeDOBlock avail (.block [s1, s2])

private theorem safeDO_add_lit {e : CExpr} {iv d : Int}
    (he : evalSmallI32? e = some iv) (h0 : 0 ≤ iv) (hd0 : 0 ≤ d) (hs : iv + d < 1000) :
    evalSmallI32? (CExpr.binary .add e (.lit d .i32 .none .dec none)).paren = some (iv + d) := by
  have hd_lt : d < 1000 := by omega
  have hs0 : 0 ≤ iv + d := by omega
  simp [evalSmallI32?, he, hd0, hd_lt, hs0, hs]

private theorem safeDO2_of {avail : Nat} {i : CExpr} {iv : Int}
    (he : evalSmallI32? i = some iv) (h0 : 0 ≤ iv) (h1 : iv.toNat + 2 ≤ avail) (hlt : avail ≤ 1000) :
    SafeDOBlock avail (mkDO2 i) := by
  refine SafeDOBlock.seq _ _ (SafeDOBlock.leaf i iv he h0 (by omega)) ?_
  exact SafeDOBlock.leaf _ (iv + 1) (safeDO_add_lit he h0 (by omega) (by omega)) (by omega) (by omega)

private theorem safeDO4_of {avail : Nat} {i : CExpr} {iv : Int}
    (he : evalSmallI32? i = some iv) (h0 : 0 ≤ iv) (h1 : iv.toNat + 4 ≤ avail) (hlt : avail ≤ 1000) :
    SafeDOBlock avail (mkDO4 i) := by
  refine SafeDOBlock.seq _ _ (safeDO2_of he h0 (by omega) hlt) ?_
  exact safeDO2_of (safeDO_add_lit he h0 (by omega) (by omega)) (by omega) (by omega) hlt

private theorem safeDO8_of {avail : Nat} {i : CExpr} {iv : Int}
    (he : evalSmallI32? i = some iv) (h0 : 0 ≤ iv) (h1 : iv.toNat + 8 ≤ avail) (hlt : avail ≤ 1000) :
    SafeDOBlock avail (mkDO8 i) := by
  refine SafeDOBlock.seq _ _ (safeDO4_of he h0 (by omega) hlt) ?_
  exact safeDO4_of (safeDO_add_lit he h0 (by omega) (by omega)) (by omega) (by omega) hlt

private theorem stmtPres_safeDOBlock {prog ext m0 m_entry frameBlks b_adler b_sum2 b_buf
    ty_adler ty_sum2 ty_buf pb poff avail remLen s}
    (hs : SafeDOBlock avail s)
    (hr : Readable m0 (.ptr pb poff) remLen)
    (hle : avail ≤ remLen) :
    StmtPres prog zlibPointerConfig ext
      (DOInv m0 m_entry frameBlks b_adler b_sum2 b_buf ty_adler ty_sum2 ty_buf pb poff)
      (DOInv m0 m_entry frameBlks b_adler b_sum2 b_buf ty_adler ty_sum2 ty_buf pb poff)
      s := by
  induction hs with
  | leaf idx iv he _ hlt =>
    exact wp_do1_step hr he (Nat.lt_of_lt_of_le hlt hle)
  | seq _ _ _ _ ih1 ih2 =>
    exact stmtPres_block2 ih1 ih2 (fun _ _ _ h => h) (fun _ _ _ h => h)

private theorem safeDO16 : SafeDOBlock 16 mkDO16 :=
  SafeDOBlock.seq _ _
    (safeDO8_of (by rfl) (by decide) (by decide) (by decide))
    (safeDO8_of (by rfl) (by decide) (by decide) (by decide))

private theorem wp_ptr_addEq_lit {prog ext env blks frameBlks m0 m os k_cont Q
    x_buf b_buf ty_buf pb poff remLen n}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b_buf ∈ frameBlks)
    (hs_b : PtrSlot env m x_buf b_buf ty_buf bytefElTy (.ptr pb poff))
    (hr : Readable m0 (.ptr pb poff) remLen)
    (hn : (n : Int) ≥ 0) (hn_lt : (n : Int) < 1000) (hle : n.toNat ≤ remLen)
    (hcont : ∀ m',
      LocalFrameMem m0 m' frameBlks →
      PtrSlot env m' x_buf b_buf ty_buf bytefElTy (.ptr pb (Int64.ofInt (poff.toInt + n.toNat))) →
      Readable m0 (.ptr pb (Int64.ofInt (poff.toInt + n.toNat))) (remLen - n.toNat) →
      (∀ b' ≠ b_buf, m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .addEq (.var x_buf) (.lit n .i32 .none .dec none))))
        env blks m os k_cont) := by
  obtain ⟨blk, hblk, hlo, hhi, hr'⟩ := Readable.advance hr hle
  have hpb_lt : pb < m0.nextBlock := readable_block_lt hr
  have hm_blk : m.blocks pb = some blk := by
    rw [localFrameMem_blocks_eq_of_lt hf hpb_lt, hblk]
  have hn_eq : n = (n.toNat : Int) := by omega
  have hbv : (BitVec.ofInt 32 n).toInt = n := bv32_ofInt_toInt_small hn hn_lt
  have hptr_add : evalPtrAdd zlibPointerConfig prog.tags m (.ptr pb poff) bytefElTy
      (BitVec.ofInt 32 n).toInt =
      some (.ptr pb (Int64.ofInt (poff.toInt + n.toNat))) := by
    rw [hbv, hn_eq]
    exact evalPtrAdd_byte_inBounds hm_blk hlo hhi
  let poff' : Int64 := Int64.ofInt (poff.toInt + n.toNat)
  obtain ⟨m', hm', hf', hs_b'⟩ := hs_b.write hf hmem (Or.inr ⟨pb, poff', rfl⟩)
  have hwp : writePlace prog.tags m b_buf 0 ty_buf (.rval (.ptr pb poff') ty_buf) =
      some (.rval (.ptr pb poff') ty_buf, m') := by
    unfold writePlace
    have hcast : Sem.castVal m ty_buf (.ptr pb poff') = some (.ptr pb poff') := by
      rw [castVal_unqual, hs_b.2.1]; simp
    simp only [hs_b.2.1, hcast, bind, Option.bind, pure, Pure.pure, hm']
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hs_b.1) ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  have hc0 : ModSet.conflicts [] b_buf 0 (sizeofTy prog.tags ty_buf) = false := rfl
  have hvn : valAsInt? (.int .i32 (BitVec.ofInt 32 n)) = some (.i32, (BitVec.ofInt 32 n).toInt) := rfl
  have happ : applyBinary zlibPointerConfig prog.tags m .add (.ptr pb poff) ty_buf
      (.int .i32 (BitVec.ofInt 32 n)) (.int .i32) =
      some (.ptr pb poff', ty_buf.unqual) := by
    unfold applyBinary
    simp only [CTy.isPtr, hs_b.2.1, Bool.true_or, ↓reduceIte, hvn, hptr_add, Option.map_some]
    rfl
  have hstep : stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (.int .i32 (BitVec.ofInt 32 n)) (.int .i32)) [.assignRhsF .addEq b_buf 0 ty_buf]) =
      some (.ret (.rval (.ptr pb poff') ty_buf) [], m', [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩]) := by
    simp only [stepExprPure, hc0, Bool.not_false, guard_true, assignOpToBin?, hs_b.readVal_eq,
      happ, hwp, bind, Option.bind, pure, Pure.pure]
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl
    (hcont m' hf' hs_b' hr' (fun _ hne => writeVal_blocks_ne hm' hne)))

private theorem wp_purePtrCmp_zero {prog cfg ext env m mods x b ty el p}
    (hs : PtrSlot env m x b ty el p) (hnc : mods.conflicts b 0 8 = false) :
    PureIntEval prog cfg ext env m mods (.binary .eq (.var x) (.lit 0)) .i32
      (match p with | .null => 1 | _ => 0) (.int .i32) := by
  have hlu := hs.1
  have hptr := hs.2.1
  have hdecay := CTy.decay_isPtr hptr
  have hrp := readPlace_ptrSlot (tags := prog.tags) hs hnc
  rcases hs.2.2.2.1 with rfl | ⟨pb, poff, rfl⟩
  · refine ⟨rfl, fun fs ctx blks os k_cont Q hw => ?_⟩
    refine WPTerm.of_exprPure rfl ?_
    have hstep_v : stepExprPure prog cfg env m mods (.eval .rval (.var x) (.binLhsF .eq (.lit 0) :: fs)) =
        some (.ret (.rval .null ty.decay) (.binLhsF .eq (.lit 0) :: fs), m, mods) := by
      simp [stepExprPure, hlu, hrp]
    refine WPTerm.of_exprPure hstep_v ?_
    refine WPTerm.of_exprPure rfl ?_
    refine pureIntEval_lit.2 (.binRhsF .eq .null ty.decay :: fs) ctx blks os k_cont Q ?_
    have hcmp : applyBinary cfg prog.tags m .eq .null ty.decay
        (.int .i32 (BitVec.ofInt IntKind.i32.bits 0)) (.int .i32) =
        some (.int .i32 1, .int .i32) := by
      unfold applyBinary; simp [hdecay, evalPtrCmp]
    refine WPTerm.of_exprPure ?_ hw
    simp only [stepExprPure, hcmp, Option.map_some]
  · refine ⟨rfl, fun fs ctx blks os k_cont Q hw => ?_⟩
    refine WPTerm.of_exprPure rfl ?_
    have hstep_v : stepExprPure prog cfg env m mods (.eval .rval (.var x) (.binLhsF .eq (.lit 0) :: fs)) =
        some (.ret (.rval (.ptr pb poff) ty.decay) (.binLhsF .eq (.lit 0) :: fs), m, mods) := by
      simp [stepExprPure, hlu, hrp]
    refine WPTerm.of_exprPure hstep_v ?_
    refine WPTerm.of_exprPure rfl ?_
    refine pureIntEval_lit.2 (.binRhsF .eq (.ptr pb poff) ty.decay :: fs) ctx blks os k_cont Q ?_
    have hcmp : applyBinary cfg prog.tags m .eq (.ptr pb poff) ty.decay
        (.int .i32 (BitVec.ofInt IntKind.i32.bits 0)) (.int .i32) =
        some (.int .i32 0, .int .i32) := by
      unfold applyBinary; simp [hdecay, evalPtrCmp]
    refine WPTerm.of_exprPure ?_ hw
    simp only [stepExprPure, hcmp, Option.map_some]

private theorem evalIntBinary_5552_div_16 :
    evalIntBinary .div (.int .i32 (BitVec.ofInt 32 5552)) (.int .i32 (BitVec.ofInt 32 16)) =
      some (.int .i32 (BitVec.ofInt 32 347), .int .i32) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .i32 (BitVec.ofInt 32 5552)) = some (.i32, 5552) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 16)) = some (.i32, 16) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .i32 .i32 = .i32 := rfl
  have h1 : (BitVec.ofInt 32 5552).toInt = 5552 := by decide
  have h2 : (BitVec.ofInt 32 16).toInt = 16 := by decide
  have hin : IntKind.i32.inRange (Int.tdiv 5552 16) = true := by decide
  rw [hu]
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, h1, h2,
    show ((16 : Int) == 0) = false from rfl, ofIntExact_signed (k := .i32) rfl hin]
  rfl

private theorem evalIntBinary_u64_add_neg1 (v : BitVec 64) :
    evalIntBinary .add (.int .u64 v) (.int .i32 (BitVec.ofInt 32 (-1))) =
      some (.int .u64 (BitVec.ofInt 64 ((v.toNat : Int) + ((BitVec.ofInt 64 (-1)).toNat : Int))), .int .u64) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .u64 v) = some (.u64, (v.toNat : Int)) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 (-1))) =
      some (.i32, (BitVec.ofInt 32 (-1)).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hm1 : (BitVec.ofInt 32 (-1)).toInt = -1 := by decide
  have hv64 : BitVec.ofInt 64 (v.toNat : Int) = v := by simp
  rw [hu]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hm1, hv64,
    ofIntExact_unsigned (k := .u64) rfl]

private theorem u64_add_neg1_toNat {v : BitVec 64} (hpos : 0 < v.toNat) :
    (BitVec.ofInt 64 ((v.toNat : Int) + ((BitVec.ofInt 64 (-1)).toNat : Int))).toNat = v.toNat - 1 := by
  have h1 : ((BitVec.ofInt 64 (-1)).toNat : Int) = 18446744073709551615 := by decide
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  rw [h1, BitVec.toNat_ofInt, hpow]
  omega

private theorem wp_while_len_dec {prog ext env blks frameBlks m0 m_in os k_cont Q
    b_adler b_sum2 b_buf b_len ty_adler ty_sum2 ty_buf ty_len
    va0 vs0 pb0 poff0 len0}
    (hf0 : LocalFrameMem m0 m_in frameBlks)
    (ha_mem : b_adler ∈ frameBlks) (hs_mem : b_sum2 ∈ frameBlks)
    (hb_mem : b_buf ∈ frameBlks) (hl_mem : b_len ∈ frameBlks)
    (hne_ab : b_adler ≠ b_buf) (hne_al : b_adler ≠ b_len)
    (hne_as : b_adler ≠ b_sum2) (hne_sb : b_sum2 ≠ b_buf)
    (hne_sl : b_sum2 ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hsa0 : IntSlot env m_in "adler" b_adler ty_adler .u64 va0)
    (hss0 : IntSlot env m_in "sum2" b_sum2 ty_sum2 .u64 vs0)
    (hsb0 : PtrSlot env m_in "buf" b_buf ty_buf bytefElTy (.ptr pb0 poff0))
    (hsl0 : IntSlot env m_in "len" b_len ty_len .u64 len0)
    (hread0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb0 poff0) len0.toNat)
    (hcont : ∀ va' vs' len' pb' poff' m',
      LocalFrameMem m0 m' frameBlks →
      IntSlot env m' "adler" b_adler ty_adler .u64 va' →
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs' →
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb' poff') →
      IntSlot env m' "len" b_len ty_len .u64 len' →
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
        m'.blocks b' = m_in.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt (.incDec .postDec (.var "len"))
        (.block [
          .expr (.assign .addEq (.var "adler") (.deref (.incDec .postInc (.var "buf")))),
          .expr (.assign .addEq (.var "sum2") (.var "adler"))
        ]))) env blks m_in os k_cont) := by
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun n env' blks' m' os' =>
    env' = env ∧ blks' = blks ∧ os' = os ∧
    LocalFrameMem m0 m' frameBlks ∧
    ∃ va vs pb poff len,
      len.toNat = n ∧
      IntSlot env m' "adler" b_adler ty_adler .u64 va ∧
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs ∧
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len ∧
      (len.toNat = 0 ∨ Readable m0 (.ptr pb poff) len.toNat) ∧
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
        m'.blocks b' = m_in.blocks b')
  refine WPTerm.while_wf Inv
    (n0 := len0.toNat)
    ⟨rfl, rfl, rfl, hf0, va0, vs0, pb0, poff0, len0, rfl, hsa0, hss0, hsb0, hsl0, hread0,
      fun _ _ _ _ _ => rfl⟩
    ?_
  intro n env_l blks_l m' os' hinv ih
  rcases hinv with ⟨henv_l, hblks_l, hos_l, hf, va, vs, pb, poff, len, hn, hsa, hss, hsb, hsl, hread, hm_eq⟩
  subst henv_l hblks_l hos_l
  let len_dec : BitVec 64 := BitVec.ofInt 64 ((len.toNat : Int) + ((BitVec.ofInt 64 (-1)).toNat : Int))
  have hdec_app : applyBinary zlibPointerConfig prog.tags m' .add (.int .u64 len) ty_len
      (.int .i32 (BitVec.ofInt 32 (-1))) (.int .i32) = some (.int .u64 len_dec, .int .u64) := by
    rw [applyBinary_int hsl.2.1 (rfl : (CTy.int .i32).unqual = .int .i32)]
    exact evalIntBinary_u64_add_neg1 len
  obtain ⟨m1, hm1, hf1, hsl1⟩ := hsl.to_uninit.write hf hl_mem len_dec
  have hsa1 := hsa.preserve_ne hm1 hne_al
  have hss1 := hss.preserve_ne hm1 hne_sl
  have hsb1 := hsb.preserve_ne hm1 hne_bl
  have hm1_eq : ∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
      m1.blocks b' = m_in.blocks b' := by
    intro b' h1 h2 h3 h4
    rw [writeVal_blocks_ne hm1 h4, hm_eq b' h1 h2 h3 h4]
  have hc_len0 : ModSet.conflicts [] b_len 0 (sizeofTy prog.tags ty_len) = false := rfl
  have hstep_dec : stepExprPure prog zlibPointerConfig env_l m' []
      (.ret (.lval b_len 0 ty_len) [.incDecF .postDec]) =
      some (.ret (.rval (.int .u64 len) ty_len) [], m1, [⟨b_len, 0, sizeofTy prog.tags ty_len⟩]) := by
    have hrv_len := hsl.readVal_eq prog.tags
    simp only [stepExprPure, hc_len0, Bool.not_false, guard_true, hrv_len, hdec_app, hm1,
      bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hsl.1) ?_
  refine WPTerm.of_exprPure hstep_dec ?_
  by_cases hlen0 : len.toNat = 0
  · refine WPTerm.of_det ?_ (hcont va vs len_dec pb poff m1 hf1 hsa1 hss1 hsb1 hsl1 hm1_eq)
    unfold stepDet
    simp [isTruthy, hlen0]
  · have hpos : 0 < len.toNat := Nat.pos_of_ne_zero hlen0
    have hr : Readable m0 (.ptr pb poff) len.toNat := by
      rcases hread with h0 | hr
      · exact False.elim (hlen0 h0)
      · exact hr
    have hpb_lt : pb < m0.nextBlock := readable_block_lt hr
    have hba_ge : m0.nextBlock ≤ b_adler := (hf1.2.2.2.1 b_adler ha_mem).1
    have hbb_ge : m0.nextBlock ≤ b_buf := (hf1.2.2.2.1 b_buf hb_mem).1
    have hne_pb_b : pb ≠ b_buf := Nat.ne_of_lt (Nat.lt_of_lt_of_le hpb_lt hbb_ge)
    have hne_pb_a : pb ≠ b_adler := Nat.ne_of_lt (Nat.lt_of_lt_of_le hpb_lt hba_ge)
    obtain ⟨blk, hblk, hlo, hhi, hr_next⟩ := Readable.advance hr (by omega : 1 ≤ len.toNat)
    have hm1_pb : m1.blocks pb = some blk := by
      rw [localFrameMem_blocks_eq_of_lt hf1 hpb_lt, hblk]
    obtain ⟨_, byteBv, _, _, _, hrv_byte⟩ := Readable.read_byte hf1 hr (by omega : 0 < len.toNat)
    have hpoff0 : Int64.ofInt (poff.toInt + ((0 : Nat) : Int)) = poff := by
      simp [Int64.ofInt_toInt]
    rw [hpoff0] at hrv_byte
    let poff' : Int64 := Int64.ofInt (poff.toInt + 1)
    have hptr_add : evalPtrAdd zlibPointerConfig prog.tags m1 (.ptr pb poff) bytefElTy 1 =
        some (.ptr pb poff') :=
      evalPtrAdd_byte_inBounds hm1_pb hlo hhi
    have hv1 : valAsInt? (.int .i32 (BitVec.ofInt 32 1)) = some (.i32, 1) := rfl
    have hinc_app : applyBinary zlibPointerConfig prog.tags m1 .add (.ptr pb poff) ty_buf
        (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) = some (.ptr pb poff', ty_buf.unqual) := by
      unfold applyBinary
      simp only [CTy.isPtr, hsb1.2.1, Bool.true_or, ↓reduceIte, hv1, hptr_add, Option.map_some]
    obtain ⟨m2, hm2, hf2, hsb2⟩ := hsb1.write hf1 hb_mem (Or.inr ⟨pb, poff', rfl⟩)
    have hsa2 := hsa1.preserve_ne hm2 hne_ab
    have hss2 := hss1.preserve_ne hm2 hne_sb
    have hsl2 := hsl1.preserve_ne hm2 hne_bl.symm
    have hc_buf0 : ModSet.conflicts [] b_buf 0 (sizeofTy prog.tags ty_buf) = false := rfl
    have hstep_buf_inc : stepExprPure prog zlibPointerConfig env_l m1 []
        (.ret (.lval b_buf 0 ty_buf) [.incDecF .postInc, .derefF .rval, .assignRhsF .addEq b_adler 0 ty_adler]) =
        some (.ret (.rval (.ptr pb poff) ty_buf) [.derefF .rval, .assignRhsF .addEq b_adler 0 ty_adler],
          m2, [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩]) := by
      simp only [stepExprPure, hc_buf0, Bool.not_false, guard_true, hsb1.readVal_eq, hinc_app,
        hm2, bind, Option.bind, pure, Pure.pure]
    have hm2_pb : Sem.readVal prog.tags m2 pb poff bytefElTy = some (.int .u8 byteBv) := by
      have hbeq : m2.blocks pb = m1.blocks pb := writeVal_blocks_ne hm2 hne_pb_b
      rw [readVal_eq_of_blocks_eq prog.tags hbeq poff bytefElTy]
      exact hrv_byte
    have hrp_byte : readPlace prog.tags m2 [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩] .rval pb poff bytefElTy =
        some (.rval (.int .u8 byteBv) bytefElTy.decay) := by
      unfold readPlace
      have hu : bytefElTy.unqual = .int .u8 := rfl
      rw [hu]
      simp only [sizeofTy_bytefEl]
      have hc : ModSet.conflicts [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩] pb poff 1 = false :=
        modSet_conflicts_cons_ne hne_pb_b.symm rfl
      rw [hc]
      simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hm2_pb]
    have hstep_deref : stepExprPure prog zlibPointerConfig env_l m2 [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩]
        (.ret (.rval (.ptr pb poff) ty_buf) [.derefF .rval, .assignRhsF .addEq b_adler 0 ty_adler]) =
        some (.ret (.rval (.int .u8 byteBv) bytefElTy.decay) [.assignRhsF .addEq b_adler 0 ty_adler],
          m2, [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩]) := by
      simp only [stepExprPure, hsb1.2.1, hrp_byte, bind, Option.bind, pure, Pure.pure]
    obtain ⟨obv, hadd⟩ := evalIntBinary_u64_add_u8 va byteBv
    let va' : BitVec 64 := BitVec.ofInt 64 obv.toNat
    obtain ⟨m3, hm3, hf3, hsa3⟩ := hsa2.to_uninit.write hf2 ha_mem va'
    have hcast_a : Sem.castVal m2 ty_adler (.int .u64 obv) = some (.int .u64 va') :=
      castVal_int_eq_some (k1 := .u64) hsa2.2.1 obv
    have hwp_a : writePlace prog.tags m2 b_adler 0 ty_adler (.rval (.int .u64 obv) ty_adler) =
        some (.rval (.int .u64 va') ty_adler, m3) := by
      unfold writePlace
      simp only [hsa2.2.1, hcast_a, bind, Option.bind, pure, Pure.pure, hm3]
    have hstep_a_wr : stepExprPure prog zlibPointerConfig env_l m2 [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩]
        (.ret (.rval (.int .u8 byteBv) bytefElTy.decay) [.assignRhsF .addEq b_adler 0 ty_adler]) =
        some (.ret (.rval (.int .u64 va') ty_adler) [], m3,
          [⟨b_adler, 0, sizeofTy prog.tags ty_adler⟩, ⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩]) := by
      have hc : ModSet.conflicts [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩] b_adler 0
          (sizeofTy prog.tags ty_adler) = false := modSet_conflicts_cons_ne hne_ab.symm rfl
      have hdu : bytefElTy.decay.unqual = .int .u8 := rfl
      simp only [stepExprPure, hc, Bool.not_false, guard_true, assignOpToBin?, hsa2.readVal_eq,
        applyBinary_int hsa2.2.1 hdu, hadd, hwp_a, bind, Option.bind, pure, Pure.pure]
    have hss3 := hss2.preserve_ne hm3 hne_as.symm
    have hsb3 := hsb2.preserve_ne hm3 hne_ab.symm
    have hsl3 := hsl2.preserve_ne hm3 hne_al.symm
    let body : CStmt := .block [
      .expr (.assign .addEq (.var "adler") (.deref (.incDec .postInc (.var "buf")))),
      .expr (.assign .addEq (.var "sum2") (.var "adler"))
    ]
    have hdet : stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval (.int .u64 len) ty_len) [])
          (.forCond (.incDec .postDec (.var "len")) none body) [⟨b_len, 0, sizeofTy prog.tags ty_len⟩])
          env_l blks_l m1 os' k_cont) =
        some (.next (.running (.stmt body) env_l blks_l m1 os'
          (.loop (some (.incDec .postDec (.var "len"))) none body false k_cont))) := by
      unfold stepDet
      simp [isTruthy, hlen0]
    refine WPTerm.of_det hdet ?_
    refine WPTerm.of_det rfl ?_
    refine WPTerm.of_det rfl ?_
    refine WPTerm.of_exprPure rfl ?_
    refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hsa2.1) ?_
    refine WPTerm.of_exprPure rfl ?_
    refine WPTerm.of_exprPure rfl ?_
    refine WPTerm.of_exprPure rfl ?_
    refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hsb1.1) ?_
    refine WPTerm.of_exprPure hstep_buf_inc ?_
    refine WPTerm.of_exprPure hstep_deref ?_
    refine WPTerm.of_exprPure hstep_a_wr ?_
    refine WPTerm.of_det rfl ?_
    refine wp_seq_step ?_
    obtain ⟨os2, hadd_s2⟩ := evalIntBinary_unsigned_arith .add (Or.inl rfl)
      (k1 := .u64) (k2 := .u64) rfl vs va'
    refine wp_assign_op_int hf3 hs_mem hss3 rfl (pureIntEval_var0 hsa3) hadd_s2 ?_
    intro vs' m4 hf4 hss4 hm4
    have hsa4 := hsa3.preserve_ne hm4 hne_as
    have hsb4 := hsb3.preserve_ne hm4 hne_sb.symm
    have hsl4 := hsl3.preserve_ne hm4 hne_sl.symm
    refine wp_seq_nil (wp_blockEnd_free ?_)
    rw [freeStack_nil]
    refine WPTerm.of_det rfl ?_
    have hdec_lt : (len_dec : BitVec IntKind.u64.bits).toNat = len.toNat - 1 :=
      u64_add_neg1_toNat hpos
    have hm4_eq : ∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
        m4.blocks b' = m_in.blocks b' := by
      intro b' h1 h2 h3 h4
      rw [writeVal_blocks_ne hm4 h2, writeVal_blocks_ne hm3 h1,
        writeVal_blocks_ne hm2 h3, hm1_eq b' h1 h2 h3 h4]
    refine ih (len.toNat - 1) env_l blks_l m4 os' (by omega)
      ⟨rfl, rfl, rfl, hf4, va', vs', pb, poff', len_dec, hdec_lt, hsa4, hss4, hsb4, hsl4,
        Or.inr (hdec_lt.symm ▸ hr_next), hm4_eq⟩

/-! ## 6. `adler32_z` and `adler32` -/

private theorem adler32_z_body_eq :
    Zlib.Adler32.adler32TU_fn_adler32_z.body =
      CStmt.block [
        .decl { name := "sum2", ty := .int .u64 },
        .decl { name := "n", ty := .int .u32 },
        .expr (.assign .eq (.var "sum2")
          (.binary .bitAnd (CExpr.binary .shr (.var "adler") (.lit 16)).paren (.lit 65535 .i32 .none .hex))),
        .expr (.assign .andEq (.var "adler") (.lit 65535 .i32 .none .hex)),
        .ifStmt (.binary .eq (.var "len") (.lit 1))
          (.block [
            .expr (.assign .addEq (.var "adler") ((CExpr.var "buf").index (.lit 0))),
            .ifStmt (.binary .ge (.var "adler") (.lit 65521 .u32 .U))
              (.expr (.assign .subEq (.var "adler") (.lit 65521 .u32 .U))) none,
            .expr (.assign .addEq (.var "sum2") (.var "adler")),
            .ifStmt (.binary .ge (.var "sum2") (.lit 65521 .u32 .U))
              (.expr (.assign .subEq (.var "sum2") (.lit 65521 .u32 .U))) none,
            .returnStmt (some (.binary .bitOr (.var "adler") (CExpr.binary .shl (.var "sum2") (.lit 16)).paren))
          ]) none,
        .ifStmt (.binary .eq (.var "buf") (.lit 0))
          (.returnStmt (some (.lit 1 .i64 .L))) none,
        .ifStmt (.binary .lt (.var "len") (.lit 16))
          (.block [
            .whileStmt (.incDec .postDec (.var "len"))
              (.block [
                .expr (.assign .addEq (.var "adler") (.deref (.incDec .postInc (.var "buf")))),
                .expr (.assign .addEq (.var "sum2") (.var "adler"))
              ]),
            .ifStmt (.binary .ge (.var "adler") (.lit 65521 .u32 .U))
              (.expr (.assign .subEq (.var "adler") (.lit 65521 .u32 .U))) none,
            .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U)),
            .returnStmt (some (.binary .bitOr (.var "adler") (CExpr.binary .shl (.var "sum2") (.lit 16)).paren))
          ]) none,
        .whileStmt (.binary .ge (.var "len") (.lit 5552))
          (.block [
            .expr (.assign .subEq (.var "len") (.lit 5552)),
            .expr (.assign .eq (.var "n") (.binary .div (.lit 5552) (.lit 16))),
            .doWhileStmt
              (.block [mkDO16, .expr (.assign .addEq (.var "buf") (.lit 16))])
              (.incDec .preDec (.var "n")),
            .expr (.assign .modEq (.var "adler") (.lit 65521 .u32 .U)),
            .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U))
          ]),
        .ifStmt (.var "len")
          (.block [
            .whileStmt (.binary .ge (.var "len") (.lit 16))
              (.block [
                .expr (.assign .subEq (.var "len") (.lit 16)),
                mkDO16,
                .expr (.assign .addEq (.var "buf") (.lit 16))
              ]),
            .whileStmt (.incDec .postDec (.var "len"))
              (.block [
                .expr (.assign .addEq (.var "adler") (.deref (.incDec .postInc (.var "buf")))),
                .expr (.assign .addEq (.var "sum2") (.var "adler"))
              ]),
            .expr (.assign .modEq (.var "adler") (.lit 65521 .u32 .U)),
            .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U))
          ]) none,
        .returnStmt (some (.binary .bitOr (.var "adler") (CExpr.binary .shl (.var "sum2") (.lit 16)).paren))
      ] := rfl

private theorem evalIntBinary_u64_ge_i32 (v : BitVec 64) {k : Int} (h0 : 0 ≤ k) (h1 : k < 10000) :
    evalIntBinary .ge (.int .u64 v) (.int .i32 (BitVec.ofInt 32 k)) =
      some (.int .i32 (if k.toNat ≤ v.toNat then 1 else 0), .int .i32) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .u64 v) = some (.u64, (v.toNat : Int)) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 k)) =
      some (.i32, (BitVec.ofInt 32 k).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hk32 : (BitVec.ofInt 32 k).toInt = k := by
    rw [BitVec.toInt_ofInt]
    change k.bmod (4294967296 : Nat) = k
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hk64 : (BitVec.ofInt 64 k).toNat = k.toNat := by
    rw [BitVec.toNat_ofInt]
    have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
    rw [hpow]
    omega
  have hv64 : (BitVec.ofInt 64 (v.toNat : Int)).toNat = v.toNat := by simp
  rw [hu]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hk32, hk64, hv64, cmpOrd]
  by_cases hle : k.toNat ≤ v.toNat
  · have hle' : max k 0 ≤ (v.toNat : Int) := by omega
    simp [hle, hle']
  · have hgt' : ¬ (max k 0 ≤ (v.toNat : Int)) := by omega
    simp [hle, hgt']

private theorem evalIntBinary_u64_sub_i32 (v : BitVec IntKind.u64.bits) {k : Int} (h0 : 0 ≤ k) (h1 : k < 10000) :
    evalIntBinary .sub (.int .u64 v) (.int .i32 (BitVec.ofInt 32 k)) =
      some (.int .u64 (BitVec.ofInt IntKind.u64.bits ((v.toNat : Int) - (k.toNat : Int))), .int .u64) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .u64 v) = some (.u64, (v.toNat : Int)) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 k)) =
      some (.i32, (BitVec.ofInt 32 k).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hk32 : (BitVec.ofInt 32 k).toInt = k := by
    rw [BitVec.toInt_ofInt]
    change k.bmod (4294967296 : Nat) = k
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hpow : (2 ^ IntKind.u64.bits : Nat) = 18446744073709551616 := by decide
  have hk64 : (BitVec.ofInt IntKind.u64.bits k).toNat = k.toNat := by
    rw [BitVec.toNat_ofInt, hpow]
    omega
  have hv64 : (BitVec.ofInt IntKind.u64.bits (v.toNat : Int)).toNat = v.toNat := by
    have hv := v.isLt
    rw [BitVec.toNat_ofInt, hpow]
    omega
  rw [hu]
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hk32, hk64, hv64,
    ofIntExact_unsigned (k := .u64) rfl]

private theorem u64_sub_nat_toNat {v : BitVec IntKind.u64.bits} {k : Nat} (hk : k < 10000) (hle : k ≤ v.toNat) :
    (BitVec.ofInt IntKind.u64.bits ((v.toNat : Int) - (k : Int))).toNat = v.toNat - k := by
  have hv : v.toNat < 2 ^ IntKind.u64.bits := v.isLt
  have hpow : (2 ^ IntKind.u64.bits : Nat) = 18446744073709551616 := by decide
  rw [BitVec.toNat_ofInt, hpow]
  omega

private theorem evalIntBinary_u32_add_neg1 (v : BitVec 32) :
    evalIntBinary .add (.int .u32 v) (.int .i32 (BitVec.ofInt 32 (-1))) =
      some (.int .u32 (BitVec.ofInt 32 ((v.toNat : Int) + ((BitVec.ofInt 32 (-1)).toNat : Int))), .int .u32) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .u32 v) = some (.u32, (v.toNat : Int)) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 (-1))) =
      some (.i32, (BitVec.ofInt 32 (-1)).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .u32 .i32 = .u32 := rfl
  have hm1 : (BitVec.ofInt 32 (-1)).toInt = -1 := by decide
  have hv32 : BitVec.ofInt 32 (v.toNat : Int) = v := by simp
  rw [hu]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hm1, hv32,
    ofIntExact_unsigned (k := .u32) rfl]

private theorem u32_add_neg1_toNat {v : BitVec 32} (hpos : 0 < v.toNat) :
    (BitVec.ofInt 32 ((v.toNat : Int) + ((BitVec.ofInt 32 (-1)).toNat : Int))).toNat = v.toNat - 1 := by
  have h1 : ((BitVec.ofInt 32 (-1)).toNat : Int) = 4294967295 := by decide
  have hv : v.toNat < 2 ^ 32 := v.isLt
  have hpow : (2 ^ 32 : Nat) = 4294967296 := by decide
  rw [h1, BitVec.toNat_ofInt, hpow]
  omega

private theorem wp_eval_adler_or_sum2 {prog cfg ext env m b_adler b_sum2 ty_adler ty_sum2 va vs}
    (hsa : IntSlot env m "adler" b_adler ty_adler .u64 va)
    (hss : IntSlot env m "sum2" b_sum2 ty_sum2 .u64 vs) :
    ∃ rv : BitVec 64,
      PureIntEval prog cfg ext env m []
        (.binary .bitOr (.var "adler") (CExpr.binary .shl (.var "sum2") (.lit 16)).paren)
        .u64 rv (.int .u64) := by
  obtain ⟨v_sh, hv_sh⟩ := pureIntEval_bin_exists
    (pureIntEval_var0 hss) pureIntEval_lit
    (evalIntBinary_unsigned_shift .shl (Or.inl rfl) (k1 := .u64) (k2 := .i32) rfl
      vs (BitVec.ofInt 32 16) (by decide) (by decide))
  exact pureIntEval_bin_exists (pureIntEval_var0 hsa) (pureIntEval_paren hv_sh)
    (evalIntBinary_unsigned_arith .bitOr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (k1 := .u64) (k2 := .u64) rfl va v_sh)

private theorem wp_doWhile_n_dec {prog ext env blks frameBlks m0 m_in os k_cont Q
    b_adler b_sum2 b_buf b_len b_n ty_adler ty_sum2 ty_buf ty_len ty_n
    va0 vs0 pb0 poff0 len0 n0 tailLen}
    (hf0 : LocalFrameMem m0 m_in frameBlks)
    (ha_mem : b_adler ∈ frameBlks) (hs_mem : b_sum2 ∈ frameBlks)
    (hb_mem : b_buf ∈ frameBlks) (hn_mem : b_n ∈ frameBlks)
    (hne_as : b_adler ≠ b_sum2) (hne_ab : b_adler ≠ b_buf)
    (hne_al : b_adler ≠ b_len) (hne_an : b_adler ≠ b_n)
    (hne_sb : b_sum2 ≠ b_buf) (hne_sl : b_sum2 ≠ b_len)
    (hne_sn : b_sum2 ≠ b_n) (hne_bl : b_buf ≠ b_len)
    (hne_bn : b_buf ≠ b_n) (hne_ln : b_len ≠ b_n)
    (hsa0 : IntSlot env m_in "adler" b_adler ty_adler .u64 va0)
    (hss0 : IntSlot env m_in "sum2" b_sum2 ty_sum2 .u64 vs0)
    (hsb0 : PtrSlot env m_in "buf" b_buf ty_buf bytefElTy (.ptr pb0 poff0))
    (hsl0 : IntSlot env m_in "len" b_len ty_len .u64 len0)
    (hsn0 : IntSlot env m_in "n" b_n ty_n .u32 n0)
    (hn0_pos : 0 < n0.toNat)
    (hr0 : Readable m0 (.ptr pb0 poff0) (16 * n0.toNat + tailLen))
    (hcont : ∀ va' vs' pb' poff' n' m',
      LocalFrameMem m0 m' frameBlks →
      IntSlot env m' "adler" b_adler ty_adler .u64 va' →
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs' →
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb' poff') →
      IntSlot env m' "len" b_len ty_len .u64 len0 →
      IntSlot env m' "n" b_n ty_n .u32 n' →
      Readable m0 (.ptr pb' poff') tailLen →
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_n →
        m'.blocks b' = m_in.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.doWhileStmt
        (.block [mkDO16, .expr (.assign .addEq (.var "buf") (.lit 16))])
        (.incDec .preDec (.var "n")))) env blks m_in os k_cont) := by
  let doBody : CStmt := .block [mkDO16, .expr (.assign .addEq (.var "buf") (.lit 16))]
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun k_m env' blks' m' os' =>
    env' = env ∧ blks' = blks ∧ os' = os ∧
    LocalFrameMem m0 m' frameBlks ∧
    ∃ va vs pb poff curN,
      0 < curN.toNat ∧
      curN.toNat - 1 = k_m ∧
      IntSlot env m' "adler" b_adler ty_adler .u64 va ∧
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs ∧
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len0 ∧
      IntSlot env m' "n" b_n ty_n .u32 curN ∧
      Readable m0 (.ptr pb poff) (16 * curN.toNat + tailLen) ∧
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_n →
        m'.blocks b' = m_in.blocks b')
  refine WPTerm.doWhile_wf Inv
    (n0 := n0.toNat - 1)
    ⟨rfl, rfl, rfl, hf0, va0, vs0, pb0, poff0, n0, hn0_pos, rfl, hsa0, hss0, hsb0, hsl0, hsn0, hr0,
      fun _ _ _ _ _ => rfl⟩
    ?_
  intro k_m env_l blks_l m' os' hinv ih
  rcases hinv with ⟨henv_l, hblks_l, hos_l, hf, va, vs, pb, poff, curN, hNpos, hk_m,
    hsa, hss, hsb, hsl, hsn, hr, hm_eq⟩
  subst henv_l hblks_l hos_l
  refine WPTerm.of_det rfl ?_
  refine stmtPres_safeDOBlock safeDO16 hr (by omega : 16 ≤ 16 * curN.toNat + tailLen)
    env_l [] m' os' _ Q
    ⟨hf, ha_mem, hs_mem, hne_as, hne_ab.symm, hne_sb.symm, ⟨va, hsa⟩, ⟨vs, hss⟩, hsb,
      fun _ _ _ => rfl⟩ ?_
  intro m1 ⟨hf1, _, _, _, _, _, ⟨va1, hsa1⟩, ⟨vs1, hss1⟩, hsb1, hm1_eq⟩
  have hsl1 := hsl.preserve_blocks (hm1_eq _ hne_al.symm hne_sl.symm)
  have hsn1 := hsn.preserve_blocks (hm1_eq _ hne_an.symm hne_sn.symm)
  refine wp_seq_step ?_
  refine wp_ptr_addEq_lit hf1 hb_mem hsb1 hr (by decide) (by decide)
    (by omega : (16 : Int).toNat ≤ 16 * curN.toNat + tailLen) ?_
  intro m2 hf2 hsb2 hr2 hm2_blocks
  have hsa2 := hsa1.preserve_blocks (hm2_blocks _ hne_ab)
  have hss2 := hss1.preserve_blocks (hm2_blocks _ hne_sb)
  have hsl2 := hsl1.preserve_blocks (hm2_blocks _ hne_bl.symm)
  have hsn2 := hsn1.preserve_blocks (hm2_blocks _ hne_bn.symm)
  refine wp_seq_nil (wp_blockEnd_free ?_)
  rw [freeStack_nil]
  refine WPTerm.of_det rfl ?_
  let n_dec : BitVec IntKind.u32.bits :=
    BitVec.ofInt 32 ((curN.toNat : Int) + ((BitVec.ofInt 32 (-1)).toNat : Int))
  have hdec_app : applyBinary zlibPointerConfig prog.tags m2 .add (.int .u32 curN) ty_n
      (.int .i32 (BitVec.ofInt 32 (-1))) (.int .i32) = some (.int .u32 n_dec, .int .u32) := by
    rw [applyBinary_int hsn2.2.1 (rfl : (CTy.int .i32).unqual = .int .i32)]
    exact evalIntBinary_u32_add_neg1 curN
  obtain ⟨m3, hm3, hf3, hsn3⟩ := hsn2.to_uninit.write hf2 hn_mem n_dec
  have hsa3 := hsa2.preserve_ne hm3 hne_an
  have hss3 := hss2.preserve_ne hm3 hne_sn
  have hsb3 := hsb2.preserve_ne hm3 hne_bn
  have hsl3 := hsl2.preserve_ne hm3 hne_ln
  have hm3_eq : ∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_n →
      m3.blocks b' = m_in.blocks b' := by
    intro b' h1 h2 h3 h4
    rw [writeVal_blocks_ne hm3 h4, hm2_blocks b' h3, hm1_eq b' h1 h2, hm_eq b' h1 h2 h3 h4]
  have hc_n0 : ModSet.conflicts [] b_n 0 (sizeofTy prog.tags ty_n) = false := rfl
  have hstep_n : stepExprPure prog zlibPointerConfig env_l m2 []
      (.ret (.lval b_n 0 ty_n) [.incDecF .preDec]) =
      some (.ret (.rval (.int .u32 n_dec) ty_n) [], m3, [⟨b_n, 0, sizeofTy prog.tags ty_n⟩]) := by
    have hrv_n := hsn2.readVal_eq prog.tags
    simp only [stepExprPure, hc_n0, Bool.not_false, guard_true, hrv_n, hdec_app, hm3,
      bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hsn2.1) ?_
  refine WPTerm.of_exprPure hstep_n ?_
  have hn_dec_nat : n_dec.toNat = curN.toNat - 1 :=
    u32_add_neg1_toNat hNpos
  have hr2' : Readable m0 (.ptr pb (Int64.ofInt (poff.toInt + (16 : Nat))))
      (16 * (curN.toNat - 1) + tailLen) := by
    have heq_rem : 16 * curN.toNat + tailLen - (16 : Int).toNat = 16 * (curN.toNat - 1) + tailLen := by
      have : (16 : Int).toNat = 16 := by decide
      omega
    rw [← heq_rem]
    simpa [show ((16 : Int).toNat : Int) = (16 : Nat) from rfl] using hr2
  by_cases hn_zero : n_dec.toNat = 0
  · have htail_eq : 16 * (curN.toNat - 1) + tailLen = tailLen := by
      have : curN.toNat - 1 = 0 := by rw [← hn_dec_nat]; exact hn_zero
      omega
    rw [htail_eq] at hr2'
    refine WPTerm.of_det ?_ (hcont va1 vs1 pb (Int64.ofInt (poff.toInt + 16)) n_dec m3
      hf3 hsa3 hss3 hsb3 hsl3 hsn3 hr2' hm3_eq)
    unfold stepDet
    simp [isTruthy, IntKind.bits]
    exact hn_zero
  · have hpos' : 0 < n_dec.toNat := Nat.pos_of_ne_zero hn_zero
    have hdet : stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval (.int .u32 n_dec) ty_n) [])
          (.doWhileCond doBody (.incDec .preDec (.var "n"))) [⟨b_n, 0, sizeofTy prog.tags ty_n⟩])
          env_l blks_l m3 os' k_cont) =
        some (.next (.running (.stmt doBody) env_l blks_l m3 os'
          (.loop (some (.incDec .preDec (.var "n"))) none doBody true k_cont))) := by
      unfold stepDet
      simp [isTruthy, IntKind.bits]
      exact hn_zero
    refine WPTerm.of_det hdet ?_
    refine ih (n_dec.toNat - 1) env_l blks_l m3 os' (by omega)
      ⟨rfl, rfl, rfl, hf3, va1, vs1, pb, Int64.ofInt (poff.toInt + 16), n_dec, hpos', rfl,
        hsa3, hss3, hsb3, hsl3, hsn3, hn_dec_nat.symm ▸ hr2', hm3_eq⟩

private theorem wp_assign_subEq_u64_i32 {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty len}
    {k : Int} (hk0 : 0 ≤ k) (hk1 : k < 10000)
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : IntSlot env m x b ty .u64 len)
    (hcont : ∀ m', LocalFrameMem m0 m' frameBlks →
      IntSlot env m' x b ty .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int))) →
      Sem.writeVal m b 0 ty
        (.int .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))) = some m' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.expr (.assign .subEq (.var x) (.lit k)))) env blks m os k_cont) := by
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hs.1) ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureIntEval_lit (prog := prog) (cfg := cfg) (ext := ext) (env := env) (m := m) (mods := [])
    (v := k) (k := .i32) (sfx := .none) (rad := .dec) (sym := none)).2
    [.assignRhsF .subEq b 0 ty] .discard blks os k_cont Q ?_
  obtain ⟨m', hm', hf', hs'⟩ :=
    hs.to_uninit.write hf hmem (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))
  have hcast : Sem.castVal m ty (.int .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))) =
      some (.int .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))) := by
    rw [castVal_unqual, hs.2.1]
    exact castVal_int_self m .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))
  have hwp : writePlace prog.tags m b 0 ty
      (.rval (.int .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))) ty) =
      some (.rval (.int .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))) ty, m') := by
    unfold writePlace
    simp only [hs.2.1, hcast, bind, Option.bind, pure, Pure.pure, hm']
  have hbin := evalIntBinary_u64_sub_i32 len hk0 hk1
  have hru : (CTy.int .i32).unqual = .int .i32 := rfl
  have hc0 : ModSet.conflicts [] b 0 (sizeofTy prog.tags ty) = false := rfl
  have hstep : stepExprPure prog cfg env m []
      (.ret (.rval (.int .i32 (BitVec.ofInt 32 k)) (.int .i32)) [.assignRhsF .subEq b 0 ty]) =
      some (.ret (.rval (.int .u64 (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - (k.toNat : Int)))) ty) [],
        m', [⟨b, 0, sizeofTy prog.tags ty⟩]) := by
    unfold stepExprPure
    simp only [hc0, Bool.not_false, guard_true, assignOpToBin?, hs.readVal_eq,
      applyBinary_int hs.2.1 hru, hbin, bind, Option.bind, pure, Pure.pure]
    rw [hwp]
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hcont m' hf' hs' hm'))

private theorem wp_while_len_ge_16 {prog ext env blks frameBlks m0 m_in os k_cont Q
    b_adler b_sum2 b_buf b_len ty_adler ty_sum2 ty_buf ty_len
    va0 vs0 pb0 poff0 len0}
    (hf0 : LocalFrameMem m0 m_in frameBlks)
    (ha_mem : b_adler ∈ frameBlks) (hs_mem : b_sum2 ∈ frameBlks)
    (hb_mem : b_buf ∈ frameBlks) (hl_mem : b_len ∈ frameBlks)
    (hne_as : b_adler ≠ b_sum2) (hne_ab : b_adler ≠ b_buf) (hne_al : b_adler ≠ b_len)
    (hne_sb : b_sum2 ≠ b_buf) (hne_sl : b_sum2 ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hsa0 : IntSlot env m_in "adler" b_adler ty_adler .u64 va0)
    (hss0 : IntSlot env m_in "sum2" b_sum2 ty_sum2 .u64 vs0)
    (hsb0 : PtrSlot env m_in "buf" b_buf ty_buf bytefElTy (.ptr pb0 poff0))
    (hsl0 : IntSlot env m_in "len" b_len ty_len .u64 len0)
    (hread0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb0 poff0) len0.toNat)
    (hcont : ∀ va' vs' pb' poff' len' m',
      LocalFrameMem m0 m' frameBlks →
      IntSlot env m' "adler" b_adler ty_adler .u64 va' →
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs' →
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb' poff') →
      IntSlot env m' "len" b_len ty_len .u64 len' →
      (len'.toNat = 0 ∨ Readable m0 (.ptr pb' poff') len'.toNat) →
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
        m'.blocks b' = m_in.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt (.binary .ge (.var "len") (.lit 16))
        (.block [
          .expr (.assign .subEq (.var "len") (.lit 16)),
          mkDO16,
          .expr (.assign .addEq (.var "buf") (.lit 16))
        ]))) env blks m_in os k_cont) := by
  let body : CStmt := .block [
    .expr (.assign .subEq (.var "len") (.lit 16)),
    mkDO16,
    .expr (.assign .addEq (.var "buf") (.lit 16))
  ]
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun k_m env' blks' m' os' =>
    env' = env ∧ blks' = blks ∧ os' = os ∧
    LocalFrameMem m0 m' frameBlks ∧
    ∃ va vs pb poff len,
      len.toNat = k_m ∧
      IntSlot env m' "adler" b_adler ty_adler .u64 va ∧
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs ∧
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len ∧
      (len.toNat = 0 ∨ Readable m0 (.ptr pb poff) len.toNat) ∧
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
        m'.blocks b' = m_in.blocks b')
  refine WPTerm.while_wf Inv (n0 := len0.toNat)
    ⟨rfl, rfl, rfl, hf0, va0, vs0, pb0, poff0, len0, rfl, hsa0, hss0, hsb0, hsl0, hread0,
      fun _ _ _ _ _ => rfl⟩
    ?_
  intro k_m env_l blks_l m' os' hinv ih
  rcases hinv with ⟨henv_l, hblks_l, hos_l, hf, va, vs, pb, poff, len, hn, hsa, hss, hsb, hsl, hread, hm_eq⟩
  subst henv_l hblks_l hos_l
  have hcond : PureIntEval prog zlibPointerConfig ext env_l m' []
      (.binary .ge (.var "len") (.lit 16)) .i32
      (if (16 : Int).toNat ≤ len.toNat then 1 else 0) (.int .i32) :=
    pureIntEval_bin (pureIntEval_var0 hsl) pureIntEval_lit
      (evalIntBinary_u64_ge_i32 len (by decide) (by decide))
  refine hcond.2 [] (.forCond (.binary .ge (.var "len") (.lit 16)) none body) blks_l os' k_cont Q ?_
  by_cases hge : (16 : Int).toNat ≤ len.toNat
  · have hge16 : 16 ≤ len.toNat := by simpa using hge
    have hr : Readable m0 (.ptr pb poff) len.toNat := by
      rcases hread with h0 | hr
      · omega
      · exact hr
    have hdet : stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval (.int .i32 (if (16 : Int).toNat ≤ len.toNat then 1 else 0)) (.int .i32)) [])
          (.forCond (.binary .ge (.var "len") (.lit 16)) none body) []) env_l blks_l m' os' k_cont) =
        some (.next (.running (.stmt body) env_l blks_l m' os'
          (.loop (some (.binary .ge (.var "len") (.lit 16))) none body false k_cont))) := by
      unfold stepDet
      have hv_cond : (if (16 : Int).toNat ≤ len.toNat then (1 : BitVec IntKind.i32.bits) else 0) = 1 := by
        simp only [hge, ↓reduceIte]
      rw [hv_cond]
      simp [isTruthy, IntKind.bits]
    refine WPTerm.of_det hdet ?_
    refine WPTerm.of_det rfl ?_
    refine wp_assign_subEq_u64_i32 (by decide : (0 : Int) ≤ 16) (by decide : (16 : Int) < 10000)
      hf hl_mem hsl ?_
    intro m1 hf1 hsl1 hm1
    have hsa1 := hsa.preserve_ne hm1 hne_al
    have hss1 := hss.preserve_ne hm1 hne_sl
    have hsb1 := hsb.preserve_ne hm1 hne_bl
    refine wp_seq_step ?_
    refine stmtPres_safeDOBlock safeDO16 hr hge16 env_l [] m1 os' _ Q
      ⟨hf1, ha_mem, hs_mem, hne_as, hne_ab.symm, hne_sb.symm, ⟨va, hsa1⟩, ⟨vs, hss1⟩, hsb1,
        fun _ _ _ => rfl⟩ ?_
    intro m2 ⟨hf2, _, _, _, _, _, ⟨va2, hsa2⟩, ⟨vs2, hss2⟩, hsb2, hm2_eq⟩
    have hsl2 := hsl1.preserve_blocks (hm2_eq _ hne_al.symm hne_sl.symm)
    refine wp_seq_step ?_
    refine wp_ptr_addEq_lit hf2 hb_mem hsb2 hr (by decide) (by decide)
      (by omega : (16 : Int).toNat ≤ len.toNat) ?_
    intro m3 hf3 hsb3 hr3 hm3_blocks
    have hsa3 := hsa2.preserve_blocks (hm3_blocks _ hne_ab)
    have hss3 := hss2.preserve_blocks (hm3_blocks _ hne_sb)
    have hsl3 := hsl2.preserve_blocks (hm3_blocks _ hne_bl.symm)
    refine wp_seq_nil (wp_blockEnd_free ?_)
    rw [freeStack_nil]
    refine WPTerm.of_det rfl ?_
    let len_next : BitVec IntKind.u64.bits :=
      BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - ((16 : Int).toNat : Int))
    have hlen_next : len_next.toNat = len.toNat - 16 := by
      change (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - ((16 : Int).toNat : Int))).toNat =
        len.toNat - 16
      rw [show ((16 : Int).toNat : Int) = (16 : Nat) from rfl]
      exact u64_sub_nat_toNat (by decide) hge16
    have hr3' : Readable m0 (.ptr pb (Int64.ofInt (poff.toInt + 16))) len_next.toNat := by
      rw [hlen_next]
      simpa [show ((16 : Int).toNat : Int) = (16 : Nat) from rfl,
        show (16 : Int).toNat = 16 from rfl] using hr3
    have hm3_eq : ∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len →
        m3.blocks b' = m_in.blocks b' := by
      intro b' h1 h2 h3 h4
      rw [hm3_blocks b' h3, hm2_eq b' h1 h2, writeVal_blocks_ne hm1 h4, hm_eq b' h1 h2 h3 h4]
    refine ih len_next.toNat env_l blks_l m3 os' (by omega)
      ⟨rfl, rfl, rfl, hf3, va2, vs2, pb, Int64.ofInt (poff.toInt + 16), len_next, rfl,
        hsa3, hss3, hsb3, hsl3, Or.inr hr3', hm3_eq⟩
  · refine WPTerm.of_det ?_ (hcont va vs pb poff len m' hf hsa hss hsb hsl hread hm_eq)
    unfold stepDet
    have hlt16 : ¬ ((16 : Int).toNat ≤ len.toNat) := hge
    have h16' : ¬ (16 ≤ len.toNat) := by simpa using hlt16
    simp [isTruthy, h16']

private theorem UninitIntSlot.preserve_blocks {env m m' name b ty k}
    (hs : UninitIntSlot env m name b ty k) (hbeq : m'.blocks b = m.blocks b) :
    UninitIntSlot env m' name b ty k := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  exact ⟨hlu, hk, hnc, blk, hbeq.trans hblk, hrw, hal, hin⟩

private theorem readable_isPtr {m : Mem} {buf : Val} {n : Nat}
    (hr : Readable m buf n) : ∃ pb poff, buf = .ptr pb poff := by
  rcases hr with ⟨pb, poff, _, heq, _⟩
  exact ⟨pb, poff, heq⟩

private theorem evalIntBinary_u64_eq_i32 (v : BitVec IntKind.u64.bits) {k : Int} (h0 : 0 ≤ k) (h1 : k < 10000) :
    evalIntBinary .eq (.int .u64 v) (.int .i32 (BitVec.ofInt 32 k)) =
      some (.int .i32 (if v.toNat = k.toNat then 1 else 0), .int .i32) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .u64 v) = some (.u64, (v.toNat : Int)) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 k)) =
      some (.i32, (BitVec.ofInt 32 k).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hk32 : (BitVec.ofInt 32 k).toInt = k := by
    rw [BitVec.toInt_ofInt]
    change k.bmod (4294967296 : Nat) = k
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hpow : (2 ^ IntKind.u64.bits : Nat) = 18446744073709551616 := by decide
  have hk64 : (BitVec.ofInt IntKind.u64.bits k).toNat = k.toNat := by
    rw [BitVec.toNat_ofInt, hpow]
    omega
  have hv64 : (BitVec.ofInt IntKind.u64.bits (v.toNat : Int)).toNat = v.toNat := by
    have hv := v.isLt
    rw [BitVec.toNat_ofInt, hpow]
    omega
  rw [hu]
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hk32, hk64, hv64, cmpOrd]
  by_cases heq : v.toNat = k.toNat
  · simp [heq]
  · have h1' : ¬ ((v.toNat : Int) = max k 0) := by omega
    simp [heq, h1']

private theorem evalIntBinary_u64_lt_i32 (v : BitVec IntKind.u64.bits) {k : Int} (h0 : 0 ≤ k) (h1 : k < 10000) :
    evalIntBinary .lt (.int .u64 v) (.int .i32 (BitVec.ofInt 32 k)) =
      some (.int .i32 (if v.toNat < k.toNat then 1 else 0), .int .i32) := by
  unfold evalIntBinary
  have hv1 : valAsInt? (.int .u64 v) = some (.u64, (v.toNat : Int)) := rfl
  have hv2 : valAsInt? (.int .i32 (BitVec.ofInt 32 k)) =
      some (.i32, (BitVec.ofInt 32 k).toInt) := rfl
  rw [hv1, hv2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hu : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hk32 : (BitVec.ofInt 32 k).toInt = k := by
    rw [BitVec.toInt_ofInt]
    change k.bmod (4294967296 : Nat) = k
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hpow : (2 ^ IntKind.u64.bits : Nat) = 18446744073709551616 := by decide
  have hk64 : (BitVec.ofInt IntKind.u64.bits k).toNat = k.toNat := by
    rw [BitVec.toNat_ofInt, hpow]
    omega
  have hv64 : (BitVec.ofInt IntKind.u64.bits (v.toNat : Int)).toNat = v.toNat := by
    have hv := v.isLt
    rw [BitVec.toNat_ofInt, hpow]
    omega
  rw [hu]
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hk32, hk64, hv64, cmpOrd]
  by_cases hlt : v.toNat < k.toNat
  · have h1' : (v.toNat : Int) < max k 0 := by omega
    simp [hlt, h1']
  · have h1' : ¬ ((v.toNat : Int) < max k 0) := by omega
    simp [hlt, h1']

private theorem wp_assign_n_5552_div_16 {prog cfg ext env blks frameBlks m0 m os k_cont Q x b ty}
    (hf : LocalFrameMem m0 m frameBlks) (hmem : b ∈ frameBlks)
    (hs : UninitIntSlot env m x b ty .u32)
    (hcont : ∀ m', LocalFrameMem m0 m' frameBlks →
      IntSlot env m' x b ty .u32 (BitVec.ofInt IntKind.u32.bits 347) →
      Sem.writeVal m b 0 ty (.int .u32 (BitVec.ofInt IntKind.u32.bits 347)) = some m' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.expr (.assign .eq (.var x) (.binary .div (.lit 5552) (.lit 16)))))
        env blks m os k_cont) := by
  have hrhs : PureIntEval prog cfg ext env m [] (.binary .div (.lit 5552) (.lit 16))
      .i32 (BitVec.ofInt 32 347) (.int .i32) :=
    pureIntEval_bin pureIntEval_lit pureIntEval_lit evalIntBinary_5552_div_16
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine WPTerm.of_exprPure (stepExprPure_eval_lval_var hs.1) ?_
  refine WPTerm.of_exprPure rfl ?_
  refine hrhs.2 [.assignRhsF .eq b 0 ty] .discard blks os k_cont Q ?_
  obtain ⟨m', hm', hf', hs'⟩ := hs.write hf hmem (BitVec.ofInt IntKind.u32.bits 347)
  have hcast : Sem.castVal m ty (.int .i32 (BitVec.ofInt 32 347)) =
      some (.int .u32 (BitVec.ofInt IntKind.u32.bits 347)) :=
    (castVal_int_eq_some (m := m) (k := .u32) (k1 := .i32) hs.2.1 (BitVec.ofInt 32 347)).trans
      (congrArg (fun x : BitVec IntKind.u32.bits => some (Val.int .u32 x)) (by decide))
  have hwp : writePlace prog.tags m b 0 ty (.rval (.int .i32 (BitVec.ofInt 32 347)) (.int .i32)) =
      some (.rval (.int .u32 (BitVec.ofInt IntKind.u32.bits 347)) ty, m') := by
    unfold writePlace
    simp only [hs.2.1, hcast, bind, Option.bind, pure, Pure.pure, hm']
  have hc0 : ModSet.conflicts [] b 0 (sizeofTy prog.tags ty) = false := rfl
  have hstep : stepExprPure prog cfg env m []
      (.ret (.rval (.int .i32 (BitVec.ofInt 32 347)) (.int .i32)) [.assignRhsF .eq b 0 ty]) =
      some (.ret (.rval (.int .u32 (BitVec.ofInt IntKind.u32.bits 347)) ty) [],
        m', [⟨b, 0, sizeofTy prog.tags ty⟩]) := by
    unfold stepExprPure
    simp only [hc0, Bool.not_false, guard_true, assignOpToBin?, bind, Option.bind, pure, Pure.pure]
    rw [hwp]
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hcont m' hf' hs' hm'))

private theorem wp_while_len_ge_5552 {prog ext env blks frameBlks m0 m_in os k_cont Q
    b_adler b_sum2 b_buf b_len b_n ty_adler ty_sum2 ty_buf ty_len ty_n
    va0 vs0 pb0 poff0 len0}
    (hf0 : LocalFrameMem m0 m_in frameBlks)
    (ha_mem : b_adler ∈ frameBlks) (hs_mem : b_sum2 ∈ frameBlks)
    (hb_mem : b_buf ∈ frameBlks) (hl_mem : b_len ∈ frameBlks) (hn_mem : b_n ∈ frameBlks)
    (hne_as : b_adler ≠ b_sum2) (hne_ab : b_adler ≠ b_buf) (hne_al : b_adler ≠ b_len) (hne_an : b_adler ≠ b_n)
    (hne_sb : b_sum2 ≠ b_buf) (hne_sl : b_sum2 ≠ b_len) (hne_sn : b_sum2 ≠ b_n)
    (hne_bl : b_buf ≠ b_len) (hne_bn : b_buf ≠ b_n) (hne_ln : b_len ≠ b_n)
    (hsa0 : IntSlot env m_in "adler" b_adler ty_adler .u64 va0)
    (hss0 : IntSlot env m_in "sum2" b_sum2 ty_sum2 .u64 vs0)
    (hsb0 : PtrSlot env m_in "buf" b_buf ty_buf bytefElTy (.ptr pb0 poff0))
    (hsl0 : IntSlot env m_in "len" b_len ty_len .u64 len0)
    (hun0 : UninitIntSlot env m_in "n" b_n ty_n .u32)
    (hread0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb0 poff0) len0.toNat)
    (hcont : ∀ va' vs' pb' poff' len' m',
      LocalFrameMem m0 m' frameBlks →
      IntSlot env m' "adler" b_adler ty_adler .u64 va' →
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs' →
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb' poff') →
      IntSlot env m' "len" b_len ty_len .u64 len' →
      UninitIntSlot env m' "n" b_n ty_n .u32 →
      (len'.toNat = 0 ∨ Readable m0 (.ptr pb' poff') len'.toNat) →
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len → b' ≠ b_n →
        m'.blocks b' = m_in.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt (.binary .ge (.var "len") (.lit 5552))
        (.block [
          .expr (.assign .subEq (.var "len") (.lit 5552)),
          .expr (.assign .eq (.var "n") (.binary .div (.lit 5552) (.lit 16))),
          .doWhileStmt
            (.block [mkDO16, .expr (.assign .addEq (.var "buf") (.lit 16))])
            (.incDec .preDec (.var "n")),
          .expr (.assign .modEq (.var "adler") (.lit 65521 .u32 .U)),
          .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U))
        ]))) env blks m_in os k_cont) := by
  let body : CStmt := .block [
    .expr (.assign .subEq (.var "len") (.lit 5552)),
    .expr (.assign .eq (.var "n") (.binary .div (.lit 5552) (.lit 16))),
    .doWhileStmt
      (.block [mkDO16, .expr (.assign .addEq (.var "buf") (.lit 16))])
      (.incDec .preDec (.var "n")),
    .expr (.assign .modEq (.var "adler") (.lit 65521 .u32 .U)),
    .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U))
  ]
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun k_m env' blks' m' os' =>
    env' = env ∧ blks' = blks ∧ os' = os ∧
    LocalFrameMem m0 m' frameBlks ∧
    ∃ va vs pb poff len,
      len.toNat = k_m ∧
      IntSlot env m' "adler" b_adler ty_adler .u64 va ∧
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs ∧
      PtrSlot env m' "buf" b_buf ty_buf bytefElTy (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len ∧
      UninitIntSlot env m' "n" b_n ty_n .u32 ∧
      (len.toNat = 0 ∨ Readable m0 (.ptr pb poff) len.toNat) ∧
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len → b' ≠ b_n →
        m'.blocks b' = m_in.blocks b')
  refine WPTerm.while_wf Inv (n0 := len0.toNat)
    ⟨rfl, rfl, rfl, hf0, va0, vs0, pb0, poff0, len0, rfl, hsa0, hss0, hsb0, hsl0, hun0, hread0,
      fun _ _ _ _ _ _ => rfl⟩
    ?_
  intro k_m env_l blks_l m' os' hinv ih
  rcases hinv with ⟨henv_l, hblks_l, hos_l, hf, va, vs, pb, poff, len, hn, hsa, hss, hsb, hsl, hun, hread, hm_eq⟩
  subst henv_l hblks_l hos_l
  have hcond : PureIntEval prog zlibPointerConfig ext env_l m' []
      (.binary .ge (.var "len") (.lit 5552)) .i32
      (if (5552 : Int).toNat ≤ len.toNat then 1 else 0) (.int .i32) :=
    pureIntEval_bin (pureIntEval_var0 hsl) pureIntEval_lit
      (evalIntBinary_u64_ge_i32 len (by decide) (by decide))
  refine hcond.2 [] (.forCond (.binary .ge (.var "len") (.lit 5552)) none body) blks_l os' k_cont Q ?_
  by_cases hge : (5552 : Int).toNat ≤ len.toNat
  · have hge5552 : 5552 ≤ len.toNat := by simpa using hge
    have hr : Readable m0 (.ptr pb poff) len.toNat := by
      rcases hread with h0 | hr
      · omega
      · exact hr
    have hdet : stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval (.int .i32 (if (5552 : Int).toNat ≤ len.toNat then 1 else 0)) (.int .i32)) [])
          (.forCond (.binary .ge (.var "len") (.lit 5552)) none body) []) env_l blks_l m' os' k_cont) =
        some (.next (.running (.stmt body) env_l blks_l m' os'
          (.loop (some (.binary .ge (.var "len") (.lit 5552))) none body false k_cont))) := by
      unfold stepDet
      have hv_cond : (if (5552 : Int).toNat ≤ len.toNat then (1 : BitVec IntKind.i32.bits) else 0) = 1 := by
        simp only [hge, ↓reduceIte]
      rw [hv_cond]
      simp [isTruthy, IntKind.bits]
    refine WPTerm.of_det hdet ?_
    refine WPTerm.of_det rfl ?_
    refine wp_assign_subEq_u64_i32 (by decide : (0 : Int) ≤ 5552) (by decide : (5552 : Int) < 10000)
      hf hl_mem hsl ?_
    intro m1 hf1 hsl1 hm1
    have hsa1 := hsa.preserve_ne hm1 hne_al
    have hss1 := hss.preserve_ne hm1 hne_sl
    have hsb1 := hsb.preserve_ne hm1 hne_bl
    have hun1 := hun.preserve_ne hm1 hne_ln.symm
    let len_next : BitVec IntKind.u64.bits :=
      BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - ((5552 : Int).toNat : Int))
    have hlen_next : len_next.toNat = len.toNat - 5552 := by
      change (BitVec.ofInt IntKind.u64.bits ((len.toNat : Int) - ((5552 : Int).toNat : Int))).toNat =
        len.toNat - 5552
      rw [show ((5552 : Int).toNat : Int) = (5552 : Nat) from rfl]
      exact u64_sub_nat_toNat (by decide) hge5552
    refine wp_seq_step ?_
    refine wp_assign_n_5552_div_16 hf1 hn_mem hun1 ?_
    intro m2 hf2 hsn2 hm2
    have hsa2 := hsa1.preserve_ne hm2 hne_an
    have hss2 := hss1.preserve_ne hm2 hne_sn
    have hsb2 := hsb1.preserve_ne hm2 hne_bn
    have hsl2 := hsl1.preserve_ne hm2 hne_ln
    let n347 : BitVec IntKind.u32.bits := BitVec.ofInt IntKind.u32.bits 347
    have hn347_nat : n347.toNat = 347 := by decide
    have hn347_pos : 0 < n347.toNat := by omega
    have hr_do : Readable m0 (.ptr pb poff) (16 * n347.toNat + len_next.toNat) := by
      have heq : 16 * n347.toNat + len_next.toNat = len.toNat := by omega
      rw [heq]
      exact hr
    refine wp_seq_step ?_
    refine wp_doWhile_n_dec hf2 ha_mem hs_mem hb_mem hn_mem
      hne_as hne_ab hne_al hne_an hne_sb hne_sl hne_sn hne_bl hne_bn hne_ln
      hsa2 hss2 hsb2 hsl2 hsn2 hn347_pos hr_do ?_
    intro va3 vs3 pb3 poff3 n3 m3 hf3 hsa3 hss3 hsb3 hsl3 hsn3 hr3 hm3_blocks
    refine wp_seq_step ?_
    refine wp_mod_u32_u64 hf3 ha_mem hsa3 (by decide) ?_
    intro va4 m4 hf4 hsa4 hm4_blocks
    have hss4 := hss3.preserve_blocks (hm4_blocks _ hne_as.symm)
    have hsb4 := hsb3.preserve_blocks (hm4_blocks _ hne_ab.symm)
    have hsl4 := hsl3.preserve_blocks (hm4_blocks _ hne_al.symm)
    have hsn4 := hsn3.preserve_blocks (hm4_blocks _ hne_an.symm)
    refine wp_seq_step ?_
    refine wp_mod_u32_u64 hf4 hs_mem hss4 (by decide) ?_
    intro vs5 m5 hf5 hss5 hm5_blocks
    have hsa5 := hsa4.preserve_blocks (hm5_blocks _ hne_as)
    have hsb5 := hsb4.preserve_blocks (hm5_blocks _ hne_sb.symm)
    have hsl5 := hsl4.preserve_blocks (hm5_blocks _ hne_sl.symm)
    have hsn5 := hsn4.preserve_blocks (hm5_blocks _ hne_sn.symm)
    refine wp_seq_nil (wp_blockEnd_free ?_)
    rw [freeStack_nil]
    refine WPTerm.of_det rfl ?_
    have hm5_eq : ∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len → b' ≠ b_n →
        m5.blocks b' = m_in.blocks b' := by
      intro b' h1 h2 h3 h4 h5
      rw [hm5_blocks b' h2, hm4_blocks b' h1, hm3_blocks b' h1 h2 h3 h5,
        writeVal_blocks_ne hm2 h5, writeVal_blocks_ne hm1 h4, hm_eq b' h1 h2 h3 h4 h5]
    refine ih len_next.toNat env_l blks_l m5 os' (by omega)
      ⟨rfl, rfl, rfl, hf5, va4, vs5, pb3, poff3, len_next, rfl,
        hsa5, hss5, hsb5, hsl5, hsn5.to_uninit, Or.inr hr3, hm5_eq⟩
  · refine WPTerm.of_det ?_ (hcont va vs pb poff len m' hf hsa hss hsb hsl hun hread hm_eq)
    unfold stepDet
    have hlt5552 : ¬ ((5552 : Int).toNat ≤ len.toNat) := hge
    have h5552' : ¬ (5552 ≤ len.toNat) := by simpa using hlt5552
    simp [isTruthy, h5552']

private theorem wp_adler32_tail_branch {prog ext env blks frameBlks m0 m os k_cont Q
    b_adler b_sum2 b_buf b_len ty_adler ty_sum2 ty_buf ty_len
    va0 vs0 pb0 poff0 len0}
    (hf0 : LocalFrameMem m0 m frameBlks)
    (ha_mem : b_adler ∈ frameBlks) (hs_mem : b_sum2 ∈ frameBlks)
    (hb_mem : b_buf ∈ frameBlks) (hl_mem : b_len ∈ frameBlks)
    (hne_as : b_adler ≠ b_sum2) (hne_ab : b_adler ≠ b_buf) (hne_al : b_adler ≠ b_len)
    (hne_sb : b_sum2 ≠ b_buf) (hne_sl : b_sum2 ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hsa0 : IntSlot env m "adler" b_adler ty_adler .u64 va0)
    (hss0 : IntSlot env m "sum2" b_sum2 ty_sum2 .u64 vs0)
    (hsb0 : PtrSlot env m "buf" b_buf ty_buf bytefElTy (.ptr pb0 poff0))
    (hsl0 : IntSlot env m "len" b_len ty_len .u64 len0)
    (hread0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb0 poff0) len0.toNat)
    (hcont : ∀ va' vs' m',
      LocalFrameMem m0 m' frameBlks →
      IntSlot env m' "adler" b_adler ty_adler .u64 va' →
      IntSlot env m' "sum2" b_sum2 ty_sum2 .u64 vs' →
      (∀ b', b' ≠ b_adler → b' ≠ b_sum2 → b' ≠ b_buf → b' ≠ b_len → m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env blks m' os k_cont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.ifStmt (.var "len")
        (.block [
          .whileStmt (.binary .ge (.var "len") (.lit 16))
            (.block [
              .expr (.assign .subEq (.var "len") (.lit 16)),
              mkDO16,
              .expr (.assign .addEq (.var "buf") (.lit 16))
            ]),
          .whileStmt (.incDec .postDec (.var "len"))
            (.block [
              .expr (.assign .addEq (.var "adler") (.deref (.incDec .postInc (.var "buf")))),
              .expr (.assign .addEq (.var "sum2") (.var "adler"))
            ]),
          .expr (.assign .modEq (.var "adler") (.lit 65521 .u32 .U)),
          .expr (.assign .modEq (.var "sum2") (.lit 65521 .u32 .U))
        ]) none)) env blks m os k_cont) := by
  refine wp_if_int (pureIntEval_var0 hsl0) ?_ ?_
  · intro _
    refine WPTerm.of_det rfl ?_
    refine wp_while_len_ge_16 hf0 ha_mem hs_mem hb_mem hl_mem
      hne_as hne_ab hne_al hne_sb hne_sl hne_bl
      hsa0 hss0 hsb0 hsl0 hread0 ?_
    intro va1 vs1 pb1 poff1 len1 m1 hf1 hsa1 hss1 hsb1 hsl1 hread1 hm1_eq
    refine wp_seq_step ?_
    refine wp_while_len_dec hf1 ha_mem hs_mem hb_mem hl_mem
      hne_ab hne_al hne_as hne_sb hne_sl hne_bl
      hsa1 hss1 hsb1 hsl1 hread1 ?_
    intro va2 vs2 len2 pb2 poff2 m2 hf2 hsa2 hss2 hsb2 hsl2 hm2_eq
    refine wp_seq_step ?_
    refine wp_mod_u32_u64 hf2 ha_mem hsa2 (by decide) ?_
    intro va3 m3 hf3 hsa3 hm3_blocks
    have hss3 := hss2.preserve_blocks (hm3_blocks _ hne_as.symm)
    refine wp_seq_step ?_
    refine wp_mod_u32_u64 hf3 hs_mem hss3 (by decide) ?_
    intro vs4 m4 hf4 hss4 hm4_blocks
    have hsa4 := hsa3.preserve_blocks (hm4_blocks _ hne_as)
    refine wp_seq_nil (wp_blockEnd_free ?_)
    rw [freeStack_nil]
    refine hcont va3 vs4 m4 hf4 hsa4 hss4 ?_
    intro b' h1 h2 h3 h4
    rw [hm4_blocks b' h2, hm3_blocks b' h1, hm2_eq b' h1 h2 h3 h4, hm1_eq b' h1 h2 h3 h4]
  · intro _
    exact hcont va0 vs0 m hf0 hsa0 hss0 (fun _ _ _ _ _ => rfl)

theorem adler32_z_spec (prog : Prog) (ext : ExtHandler) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Adler32.adler32TU_fn_adler32_z
      (fun m args => ∃ (adler : BitVec 64) (buf : Val) (len : BitVec 64),
        args = [.int .u64 adler, buf, .int .u64 len] ∧
        (buf = .null ∨ ∃ pb poff, buf = .ptr pb poff) ∧
        (len.toNat = 1 → Readable m buf 1) ∧
        (len.toNat ≠ 1 → buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat))
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨adler, buf, len, hargs, hbuf_ptr, hread1, hread_neq1⟩ _ hpush hcont
  subst hargs
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hsz0, hal0, hba0, m2_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m3_p, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m4_p, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let env0 := prog.fnStatics Zlib.Adler32.adler32TU_fn_adler32_z.name ++ prog.globalEnv
  let b_adler := m.nextBlock
  let b_buf := m2_p.nextBlock
  let b_len := m3_p.nextBlock
  have hs_adler_0 : IntSlot (("adler", b_adler, uLongTy) :: env0)
      m2_p "adler" b_adler uLongTy .u64 adler :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr0 env0
  have hne_ab_mid : b_adler ≠ m2_p.nextBlock := by
    exact Nat.ne_of_lt (lt_nextBlock_of_some hs_adler_0.2.2.2.choose_spec.1)
  have hs_adler_1 : IntSlot (("buf", b_buf, bytefPtrTy) :: ("adler", b_adler, uLongTy) :: env0)
      m3_p "adler" b_adler uLongTy .u64 adler :=
    (hs_adler_0.preserve_alloc rfl (by decide)).preserve_ne hwr1 hne_ab_mid
  have hs_buf_1 : PtrSlot (("buf", b_buf, bytefPtrTy) :: ("adler", b_adler, uLongTy) :: env0)
      m3_p "buf" b_buf bytefPtrTy bytefElTy buf :=
    PtrSlot.of_pushCallParam rfl rfl hbuf_ptr hwr1 _
  have hne_a_l : b_adler ≠ b_len := by
    have h1 : b_adler < m2_p.nextBlock := lt_nextBlock_of_some hs_adler_0.2.2.2.choose_spec.1
    have h2 : m2_p.nextBlock < m3_p.nextBlock := nextBlock_lt_of_writeAlloc hwr1
    exact Nat.ne_of_lt (Nat.lt_trans h1 h2)
  have hne_b_l : b_buf ≠ b_len := by
    exact Nat.ne_of_lt (lt_nextBlock_of_some hs_buf_1.2.2.2.2.choose_spec.1)
  let env_params : Env := ("len", b_len, zSizeTy) ::
    ("buf", b_buf, bytefPtrTy) :: ("adler", b_adler, uLongTy) :: env0
  have hs_adler_2 : IntSlot env_params m1 "adler" b_adler uLongTy .u64 adler :=
    (hs_adler_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_a_l
  have hs_buf_2 : PtrSlot env_params m1 "buf" b_buf bytefPtrTy bytefElTy buf :=
    (hs_buf_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_b_l
  have hs_len_2 : IntSlot env_params m1 "len" b_len zSizeTy .u64 len :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr2 _
  rw [adler32_z_body_eq]
  refine WPTerm.of_det rfl (WPTerm.of_det rfl ?_)
  refine wp_localDecl_none_int (k := .u64) (frameBlks := [b_len, b_buf, b_adler]) rfl rfl rfl rfl hf1 ?_
  intro b_sum2 m5 hf5 hu_sum2 hi_5 _ hp_5
  have hs_a_5 := hi_5 (by decide) hs_adler_2
  have hs_b_5 := hp_5 (by decide) hs_buf_2
  have hs_l_5 := hi_5 (by decide) hs_len_2
  refine WPTerm.of_det rfl ?_
  refine wp_decl_none_int_seq (k := .u32) rfl rfl rfl rfl hf5 ?_
  intro b_n m6 hf6 hu_n hi_6 hu_6 hp_6
  have hs_a_6 := hi_6 (by decide) hs_a_5
  have hs_b_6 := hp_6 (by decide) hs_b_5
  have hs_l_6 := hi_6 (by decide) hs_l_5
  have hu_s2_6 := hu_6 (by decide) hu_sum2
  -- Distinctness of all 5 stack blocks from `hf6.2.2.1 : Nodup`
  have hnodup : ([b_n, b_sum2, b_len, b_buf, b_adler] : List BlockId).Nodup := hf6.2.2.1
  have hne_as : b_adler ≠ b_sum2 := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_ab : b_adler ≠ b_buf := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_al : b_adler ≠ b_len := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_an : b_adler ≠ b_n := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_sb : b_sum2 ≠ b_buf := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_sl : b_sum2 ≠ b_len := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_sn : b_sum2 ≠ b_n := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_bl : b_buf ≠ b_len := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_bn : b_buf ≠ b_n := by intro h; rw [h] at hnodup; simp at hnodup
  have hne_ln : b_len ≠ b_n := by intro h; rw [h] at hnodup; simp at hnodup
  refine wp_seq_step ?_
  -- sum2 = (adler >> 16) & 0xffff;
  obtain ⟨v_shr, hv_shr⟩ := pureIntEval_bin_exists
    (pureIntEval_var0 hs_a_6) pureIntEval_lit
    (evalIntBinary_unsigned_shift .shr (Or.inr rfl) (k1 := .u64) (k2 := .i32) rfl
      adler (BitVec.ofInt 32 16) (by decide) (by decide))
  obtain ⟨v_s2_0, hv_s2_0⟩ := pureIntEval_bin_exists
    (pureIntEval_paren hv_shr) pureIntEval_lit
    (evalIntBinary_unsigned_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (k1 := .u64) (k2 := .i32) rfl v_shr (BitVec.ofInt 32 65535))
  refine wp_assign_eq_int hf6 (by simp) hu_s2_6 hv_s2_0 ?_
  intro sum2_1 m7 hf7 hs_s2_7 hm7
  have hs_a_7 := hs_a_6.preserve_ne hm7 hne_as
  have hs_b_7 := hs_b_6.preserve_ne hm7 hne_sb.symm
  have hs_l_7 := hs_l_6.preserve_ne hm7 hne_sl.symm
  have hu_n_7 := hu_n.preserve_ne hm7 hne_sn.symm
  refine wp_seq_step ?_
  -- adler &= 0xffff;
  obtain ⟨obv_a, h_and⟩ := evalIntBinary_unsigned_arith .bitAnd
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (k1 := .u64) (k2 := .i32) rfl
    adler (BitVec.ofInt 32 65535)
  refine wp_assign_op_int hf7 (by simp) hs_a_7 rfl pureIntEval_lit h_and ?_
  intro adler_1 m8 hf8 hs_a_8 hm8
  have hs_s2_8 := hs_s2_7.preserve_ne hm8 hne_as.symm
  have hs_b_8 := hs_b_7.preserve_ne hm8 hne_ab.symm
  have hs_l_8 := hs_l_7.preserve_ne hm8 hne_al.symm
  have hu_n_8 := hu_n_7.preserve_ne hm8 hne_an.symm
  refine wp_seq_step ?_
  -- if (len == 1) { ... }
  have hcond_len1 : PureIntEval prog zlibPointerConfig ext _ m8 []
      (.binary .eq (.var "len") (.lit 1)) .i32
      (if len.toNat = (1 : Int).toNat then 1 else 0) (.int .i32) :=
    pureIntEval_bin (pureIntEval_var0 hs_l_8) pureIntEval_lit
      (evalIntBinary_u64_eq_i32 len (by decide) (by decide))
  refine wp_if_int hcond_len1 ?_ ?_
  · intro hcbv
    have hlen_eq1 : len.toNat = 1 := by
      by_cases h1 : len.toNat = (1 : Int).toNat
      · simpa using h1
      · simp only [h1, ↓reduceIte] at hcbv
        exact absurd (by decide : (0 : BitVec 32).toNat = 0) hcbv
    obtain ⟨pb0, poff0, rfl⟩ := readable_isPtr (hread1 hlen_eq1)
    have hr1 : Readable m (.ptr pb0 poff0) 1 := hread1 hlen_eq1
    refine WPTerm.of_det rfl ?_
    refine wp_adler_add_byte_index hf8 (by simp) hs_a_8 hr1 (by decide) (by decide) (by decide)
      (purePtrEval_var hs_b_8 rfl) pureIntEval_lit ?_
    intro adler_2 m9 hf9 hs_a_9 hm9_blocks
    have hs_s2_9 := hs_s2_8.preserve_blocks (hm9_blocks _ hne_as.symm)
    refine wp_seq_step ?_
    refine wp_if_ge_sub_u32 hf9 (by simp) hs_a_9 rfl ?_
    intro adler_3 m10 hf10 hs_a_10 hm10_blocks
    have hs_s2_10 := hs_s2_9.preserve_blocks (hm10_blocks _ hne_as.symm)
    refine wp_seq_step ?_
    obtain ⟨o_s2, hadd_s2⟩ := evalIntBinary_unsigned_arith .add (Or.inl rfl)
      (k1 := .u64) (k2 := .u64) rfl sum2_1 adler_3
    refine wp_assign_op_int hf10 (by simp) hs_s2_10 rfl (pureIntEval_var0 hs_a_10) hadd_s2 ?_
    intro sum2_2 m11 hf11 hs_s2_11 hm11
    have hs_a_11 := hs_a_10.preserve_ne hm11 hne_as
    refine wp_seq_step ?_
    refine wp_if_ge_sub_u32 hf11 (by simp) hs_s2_11 rfl ?_
    intro sum2_3 m12 hf12 hs_s2_12 hm12_blocks
    have hs_a_12 := hs_a_11.preserve_blocks (hm12_blocks _ hne_as)
    refine wp_seq_step ?_
    obtain ⟨rv, hrv⟩ := wp_eval_adler_or_sum2 hs_a_12 hs_s2_12
    refine wp_return_int hrv rfl rfl rfl rfl ?_
    intro retBv
    have hro : ROExt m (((m12.freeStack []).freeStack [b_n, b_sum2]).freeStack [b_len, b_buf, b_adler]) := by
      rw [freeStack_nil]
      exact localFrameMem_roExt_unwind2 [b_n, b_sum2] [b_len, b_buf, b_adler] hf12
    exact hcont (.int .u64 retBv) _ hro ⟨retBv, rfl⟩
  · intro hcbv
    have hlen_neq1 : len.toNat ≠ 1 := by
      by_cases h1 : len.toNat = (1 : Int).toNat
      · simp only [h1, ↓reduceIte] at hcbv
        exact absurd hcbv (by decide)
      · simpa using h1
    have hread_n1 := hread_neq1 hlen_neq1
    refine WPTerm.of_det rfl ?_
    -- if (buf == 0) return 1L;
    refine wp_if_int (wp_purePtrCmp_zero hs_b_8 rfl) ?_ ?_
    · intro _
      refine wp_return_int (pureIntEval_lit (v := 1) (k := .i64) (sfx := .L)) rfl rfl rfl rfl ?_
      intro retBv
      exact hcont (.int .u64 retBv) _ (localFrameMem_roExt_unwind2 [b_n, b_sum2] [b_len, b_buf, b_adler] hf8)
        ⟨retBv, rfl⟩
    · intro hnotNull
      rcases hbuf_ptr with rfl | ⟨pb, poff, rfl⟩
      · exact absurd hnotNull (by decide)
      have hread_ptr : len.toNat = 0 ∨ Readable m (.ptr pb poff) len.toNat := by
        rcases hread_n1 with hnull | h0 | hr
        · cases hnull
        · exact Or.inl h0
        · exact Or.inr hr
      refine WPTerm.of_det rfl ?_
      -- if (len < 16) { ... }
      have hcond_lt16 : PureIntEval prog zlibPointerConfig ext _ m8 []
          (.binary .lt (.var "len") (.lit 16)) .i32
          (if len.toNat < (16 : Int).toNat then 1 else 0) (.int .i32) :=
        pureIntEval_bin (pureIntEval_var0 hs_l_8) pureIntEval_lit
          (evalIntBinary_u64_lt_i32 len (by decide) (by decide))
      refine wp_if_int hcond_lt16 ?_ ?_
      · intro _
        refine WPTerm.of_det rfl ?_
        refine wp_while_len_dec hf8 (by simp) (by simp) (by simp) (by simp)
          hne_ab hne_al hne_as hne_sb hne_sl hne_bl
          hs_a_8 hs_s2_8 hs_b_8 hs_l_8 hread_ptr ?_
        intro adler_2 sum2_2 len_2 pb2 poff2 m9 hf9 hs_a_9 hs_s2_9 _ _ _
        refine wp_seq_step ?_
        refine wp_if_ge_sub_u32 hf9 (by simp) hs_a_9 rfl ?_
        intro adler_3 m10 hf10 hs_a_10 hm10_blocks
        have hs_s2_10 := hs_s2_9.preserve_blocks (hm10_blocks _ hne_as.symm)
        refine wp_seq_step ?_
        refine wp_mod_u32_u64 hf10 (by simp) hs_s2_10 (by decide) ?_
        intro sum2_3 m11 hf11 hs_s2_11 hm11_blocks
        have hs_a_11 := hs_a_10.preserve_blocks (hm11_blocks _ hne_as)
        refine wp_seq_step ?_
        obtain ⟨rv, hrv⟩ := wp_eval_adler_or_sum2 hs_a_11 hs_s2_11
        refine wp_return_int hrv rfl rfl rfl rfl ?_
        intro retBv
        have hro : ROExt m (((m11.freeStack []).freeStack [b_n, b_sum2]).freeStack [b_len, b_buf, b_adler]) := by
          rw [freeStack_nil]
          exact localFrameMem_roExt_unwind2 [b_n, b_sum2] [b_len, b_buf, b_adler] hf11
        exact hcont (.int .u64 retBv) _ hro ⟨retBv, rfl⟩
      · intro _
        refine WPTerm.of_det rfl ?_
        -- while (len >= 5552) { ... }
        refine wp_while_len_ge_5552 hf8 (by simp) (by simp) (by simp) (by simp) (by simp)
          hne_as hne_ab hne_al hne_an hne_sb hne_sl hne_sn hne_bl hne_bn hne_ln
          hs_a_8 hs_s2_8 hs_b_8 hs_l_8 hu_n_8 hread_ptr ?_
        intro adler_w sum2_w pb_w poff_w len_w m9 hf9 hs_a_9 hs_s2_9 hs_b_9 hs_l_9 _ hread_w _
        refine wp_seq_step ?_
        -- if (len) { ... }
        refine wp_adler32_tail_branch hf9 (by simp) (by simp) (by simp) (by simp)
          hne_as hne_ab hne_al hne_sb hne_sl hne_bl
          hs_a_9 hs_s2_9 hs_b_9 hs_l_9 hread_w ?_
        intro adler_f sum2_f m10 hf10 hs_a_10 hs_s2_10 _
        refine wp_seq_step ?_
        -- return adler | (sum2 << 16);
        obtain ⟨rv, hrv⟩ := wp_eval_adler_or_sum2 hs_a_10 hs_s2_10
        refine wp_return_int hrv rfl rfl rfl rfl ?_
        intro retBv
        exact hcont (.int .u64 retBv) _
          (localFrameMem_roExt_unwind2 [b_n, b_sum2] [b_len, b_buf, b_adler] hf10) ⟨retBv, rfl⟩

private theorem argsWellTyped_u64_ptr_int {k3 : IntKind} {paramTys : List CTy} {args : List Val} {el : CTy}
    (hp : paramTys.map CTy.unqual = [.int .u64, .ptr el, .int k3])
    (hawt : Zlib.Spec.ArgsWellTyped paramTys false args) :
    ∃ (a : BitVec 64) (buf : Val) (len : BitVec k3.bits),
      args = [.int .u64 a, buf, .int k3 len] ∧ (buf = .null ∨ ∃ pb poff, buf = .ptr pb poff) := by
  rcases hawt with ⟨hlen, hval⟩
  have hlen3 : args.length = 3 := by
    have hplen : paramTys.length = 3 := by
      have := congrArg List.length hp
      simpa using this
    simpa [hplen] using hlen
  cases args with | nil => simp at hlen3 | cons x0 xs0 =>
  cases xs0 with | nil => simp at hlen3 | cons x1 xs1 =>
  cases xs1 with | nil => simp at hlen3 | cons x2 xs2 =>
  cases xs2 with
  | cons _ _ => simp at hlen3
  | nil =>
    cases paramTys with | nil => simp at hp | cons p0 ps0 =>
    cases ps0 with | nil => simp at hp | cons p1 ps1 =>
    cases ps1 with | nil => simp at hp | cons p2 ps2 =>
    cases ps2 with
    | cons _ _ => simp at hp
    | nil =>
      simp only [List.map_cons, List.cons.injEq] at hp
      have hv0 := hval 0 (by simp)
      have hv1 := hval 1 (by simp)
      have hv2 := hval 2 (by simp)
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem_cons_zero,
        List.getElem_cons_succ, Zlib.Spec.ValHasCTy, hp.1, hp.2.1, hp.2.2.1] at hv0 hv1 hv2
      rcases hv0 with ⟨a, rfl⟩
      rcases hv2 with ⟨len, rfl⟩
      exact ⟨a, x1, len, rfl, hv1⟩

theorem adler32_z_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (zlibExt userExt) Inv userWrite
      Zlib.Adler32.adler32_z_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_adler32_z hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_adler32_z hlib) rfl ?_ (adler32_z_spec prog (zlibExt userExt)) ?_ ?_
  · intro p hp
    simp [Zlib.Adler32.adler32TU_fn_adler32_z] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args _ hpre hawt
    obtain ⟨adler, buf, len, rfl, hptr⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u64) (el := bytefElTy) rfl hawt
    simp only [Zlib.Adler32.adler32_z_contract] at hpre
    exact ⟨adler, buf, len, rfl, hptr, hpre.1, hpre.2⟩
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨adler, buf, len, rfl, _⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u64) (el := bytefElTy) rfl hawt
    have hcast : Sem.castVal m' Zlib.Adler32.adler32_z_contract.retTy (.int .u64 bv) =
        some (.int .u64 bv) := by
      rw [castVal_unqual]
      change Sem.castVal m' (.int .u64) (.int .u64 bv) = some (.int .u64 bv)
      exact castVal_int_self m' .u64 bv
    refine ⟨.int .u64 bv, hcast, ?_⟩
    simp [Zlib.Adler32.adler32_z_contract]

private theorem Readable.of_localFrameMem {m m' : Mem} {blks : List BlockId} {buf : Val} {n : Nat}
    (hf : LocalFrameMem m m' blks) (hr : Readable m buf n) : Readable m' buf n := by
  rcases hr with ⟨pb, poff, blk, heq, hblk, hin, hbytes⟩
  subst heq
  have hlt := readable_block_lt ⟨pb, poff, blk, rfl, hblk, hin, hbytes⟩
  have hbeq : m'.blocks pb = some blk := (localFrameMem_blocks_eq_of_lt hf hlt).trans hblk
  exact ⟨pb, poff, blk, rfl, hbeq, hin, hbytes⟩

theorem adler32_spec
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} (ext : ExtHandler)
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Adler32.adler32TU_fn_adler32
      (fun m args => ∃ (adler : BitVec 64) (buf : Val) (len : BitVec 32),
        args = [.int .u64 adler, buf, .int .u32 len] ∧
        (buf = .null ∨ ∃ pb poff, buf = .ptr pb poff) ∧
        (len.toNat = 1 → Readable m buf 1) ∧
        (len.toNat ≠ 1 → buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat))
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨adler, buf, len, hargs, hbuf_ptr, hread1, hread_neq1⟩ _ hpush hcont
  subst hargs
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hsz0, hal0, hba0, m2_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m3_p, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m4_p, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let uIntTy : CTy := .typedef "uInt" (.int .u32)
  let env0 := prog.fnStatics Zlib.Adler32.adler32TU_fn_adler32.name ++ prog.globalEnv
  let b_adler := m.nextBlock
  let b_buf := m2_p.nextBlock
  let b_len := m3_p.nextBlock
  have hs_adler_0 : IntSlot (("adler", b_adler, uLongTy) :: env0)
      m2_p "adler" b_adler uLongTy .u64 adler :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr0 env0
  have hne_ab_mid : b_adler ≠ m2_p.nextBlock :=
    Nat.ne_of_lt (lt_nextBlock_of_some hs_adler_0.2.2.2.choose_spec.1)
  have hs_adler_1 : IntSlot (("buf", b_buf, bytefPtrTy) :: ("adler", b_adler, uLongTy) :: env0)
      m3_p "adler" b_adler uLongTy .u64 adler :=
    (hs_adler_0.preserve_alloc rfl (by decide)).preserve_ne hwr1 hne_ab_mid
  have hs_buf_1 : PtrSlot (("buf", b_buf, bytefPtrTy) :: ("adler", b_adler, uLongTy) :: env0)
      m3_p "buf" b_buf bytefPtrTy bytefElTy buf :=
    PtrSlot.of_pushCallParam rfl rfl hbuf_ptr hwr1 _
  have hne_a_l : b_adler ≠ b_len := by
    have h1 : b_adler < m2_p.nextBlock := lt_nextBlock_of_some hs_adler_0.2.2.2.choose_spec.1
    have h2 : m2_p.nextBlock < m3_p.nextBlock := nextBlock_lt_of_writeAlloc hwr1
    exact Nat.ne_of_lt (Nat.lt_trans h1 h2)
  have hne_b_l : b_buf ≠ b_len :=
    Nat.ne_of_lt (lt_nextBlock_of_some hs_buf_1.2.2.2.2.choose_spec.1)
  let env_params : Env := ("len", b_len, uIntTy) ::
    ("buf", b_buf, bytefPtrTy) :: ("adler", b_adler, uLongTy) :: env0
  have hs_adler_2 : IntSlot env_params m1 "adler" b_adler uLongTy .u64 adler :=
    (hs_adler_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_a_l
  have hs_buf_2 : PtrSlot env_params m1 "buf" b_buf bytefPtrTy bytefElTy buf :=
    (hs_buf_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_b_l
  have hs_len_2 : IntSlot env_params m1 "len" b_len uIntTy .u32 len :=
    IntSlot.of_pushCallParam (k := .u32) rfl rfl hwr2 _
  have hg_none : env0.lookup "adler32_z" = none := by
    dsimp [env0]
    have hname : Zlib.Adler32.adler32TU_fn_adler32.name = "adler32" := rfl
    rw [hname, prog_fnStatics_adler32 hlib, hlib.globalEnv_eq]
    exact hlib.gEnv_lookup_none "adler32_z" (by decide)
  have henv_none : env_params.lookup "adler32_z" = none := by
    dsimp [env_params]
    rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
    exact hg_none
  have henum : enumConst? prog.tags "adler32_z" = none :=
    enumConst_prog_adler32_z prog.tags hlib.prog_tags_eq
  have hproto := prog_fnProtos_adler32_z hlib
  let fnTy := CTy.fnPtr Zlib.Adler32.adler32TU_fn_adler32_z.retTy
    (Zlib.Adler32.adler32TU_fn_adler32_z.params.map (·.ty))
    Zlib.Adler32.adler32TU_fn_adler32_z.variadic
  have hbody : Zlib.Adler32.adler32TU_fn_adler32.body = CStmt.block [
      .returnStmt (some (.call (.var "adler32_z") [.var "adler", .var "buf", .var "len"]))] := rfl
  rw [hbody]
  refine WPTerm.of_det rfl ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  have hlu_fn : stepExprPure prog zlibPointerConfig env_params m1 []
      (.eval .rval (.var "adler32_z") [.callFnF [.var "adler", .var "buf", .var "len"]]) =
      some (.ret (.rval (.fnPtr "adler32_z") fnTy) [.callFnF [.var "adler", .var "buf", .var "len"]],
        m1, []) := by
    simp [stepExprPure, henv_none, henum, hproto, fnDefSig, fnTy]
  refine WPTerm.of_exprPure hlu_fn ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureIntEval_var0 hs_adler_2).2
    [.callArgF "adler32_z" fnTy [] [.var "buf", .var "len"]]
    .returnVal [] os _ Q ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (purePtrEval_var hs_buf_2 rfl).2
    [.callArgF "adler32_z" fnTy [(.int .u64 adler, uLongTy.decay)] [.var "len"]]
    .returnVal [] os _ Q ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureIntEval_var0 hs_len_2).2
    [.callArgF "adler32_z" fnTy [(.int .u64 adler, uLongTy.decay), (buf, bytefPtrTy.decay)] []]
    .returnVal [] os _ Q ?_
  let len64 : BitVec 64 := BitVec.setWidth 64 len
  have hcoerce : Sem.coerceCallArgs m1
      (Zlib.Adler32.adler32TU_fn_adler32_z.params.map (·.ty)) false
      [(.int .u64 adler, uLongTy.decay), (buf, bytefPtrTy.decay), (.int .u32 len, uIntTy.decay)] =
      some [.int .u64 adler, buf, .int .u64 len64] := by
    rcases hbuf_ptr with rfl | ⟨pb, poff, rfl⟩ <;>
      simp [Sem.coerceCallArgs, Zlib.Adler32.adler32TU_fn_adler32_z, Sem.castVal, CTy.unqual,
        CTy.isVoid, CTy.intKind?, Sem.ofIntCast, IntKind.signed, IntKind.bits, len64]
  have hsimp : ∀ p ∈ Zlib.Adler32.adler32TU_fn_adler32_z.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Adler32.adler32TU_fn_adler32_z] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  have hlen64 : len64.toNat = len.toNat := by
    have hlt : len.toNat < 2 ^ 32 := len.isLt
    have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
    rw [BitVec.toNat_setWidth, hpow]
    omega
  refine FuncBodySpec.call (adler32_z_spec prog ext) rfl (prog_fns_adler32_z hlib)
    rfl rfl hcoerce ⟨adler, buf, len64, rfl, hbuf_ptr,
      fun h => Readable.of_localFrameMem hf1 (hread1 (hlen64.symm.trans h)),
      fun h => by
        rcases hread_neq1 (fun h' => h (hlen64.trans h')) with hnull | h0 | hr
        · exact Or.inl hnull
        · exact Or.inr (Or.inl (hlen64.trans h0))
        · exact Or.inr (Or.inr (hlen64 ▸ Readable.of_localFrameMem hf1 hr))⟩ hsimp ?_
  intro ret m' hro ⟨retBv, hret⟩
  subst hret
  have hcast : Sem.castVal m' uLongTy (.int .u64 retBv) = some (.int .u64 retBv) := by
    rw [castVal_unqual]
    change Sem.castVal m' (.int .u64) (.int .u64 retBv) = some (.int .u64 retBv)
    exact castVal_int_self m' .u64 retBv
  refine WPTerm.of_det ?_ (hcont (.int .u64 retBv) (m'.freeStack [b_len, b_buf, b_adler])
    (LocalFrameMem.roExt_freeStack (hf1.of_roExt hro)) ⟨retBv, rfl⟩)
  unfold stepDet
  simp [Cont.topRetTy, Zlib.Adler32.adler32TU_fn_adler32, CTy.isVoid, CTy.unqual, hcast,
    unwindReturn, freeStack_nil]
  rfl

theorem adler32_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (zlibExt userExt) Inv userWrite
      Zlib.Adler32.adler32_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_adler32 hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_adler32 hlib) rfl ?_ (adler32_spec (zlibExt userExt) hlib) ?_ ?_
  · intro p hp
    simp [Zlib.Adler32.adler32TU_fn_adler32] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args _ hpre hawt
    obtain ⟨adler, buf, len, rfl, hptr⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u32) (el := bytefElTy) rfl hawt
    simp only [Zlib.Adler32.adler32_contract] at hpre
    exact ⟨adler, buf, len, rfl, hptr, hpre.1, hpre.2⟩
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨adler, buf, len, rfl, _⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u32) (el := bytefElTy) rfl hawt
    have hcast : Sem.castVal m' Zlib.Adler32.adler32_contract.retTy (.int .u64 bv) =
        some (.int .u64 bv) := by
      rw [castVal_unqual]
      change Sem.castVal m' (.int .u64) (.int .u64 bv) = some (.int .u64 bv)
      exact castVal_int_self m' .u64 bv
    refine ⟨.int .u64 bv, hcast, ?_⟩
    simp [Zlib.Adler32.adler32_contract]

end Zlib.Proof





