import Zlib
import Zlib.Proof.ProgSpec
import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgLookupAll
import Zlib.Proof.ZutilAlloc
import Zlib.Proof.Zutil
import Zlib.Proof.CompressBound
import Zlib.Proof.Adler32
import Zlib.Proof.Crc32
import Zlib.Proof.Crc32Combine
import Zlib.Proof.Math.Inftrees
import Zlib.Proof.Math.Trees
import Zlib.Proof.Math.Gz
import C99.Proof.Mem
import C99.Proof.WP

/-!
# Phase 1 Unified Safety Invariant (`ZlibInv`) and Decoupled Cross-Module Spec Interfaces

This module establishes the Phase 1 foundation for Waves 2–4:
1. `HeapRwBlock`, `MemBlocksUnchanged`, `PreservesBlockMeta`, `PreservesOutsideRange`,
   `NonErrnoROGlobal`, `initLibz_nonErrnoROGlobal`, and `zErrmsgReady_of_initLibz`.
2. `CodeTableValid`, `InflateWitness` / `InflateStateInv`, `InflateBackWitness` / `InflateBackInv`,
   `DeflateWitness` / `DeflateStateInv`, `GzWitness` / `GzStateInvCore` / `GzStateInv`, and
   `InflateAccumulatorsInit` / `StreamAccumulatorsInit`, with zero dependence on
   client-mutable fields of external `z_stream_s` blocks (`next_in`, `avail_in`, `total_in`,
   `next_out`, `avail_out`, `total_out`, `msg`, `data_type`, `adler`, `reserved`).
3. `ZlibInv`, ownership partition & pairwise disjointness lemmas, `ZlibInv.empty_owned`,
   `ZlibInv.init`, `ZlibInv.toBaseInv`, `ZlibInv.roExt`, and `ZlibInv.clientFrame`.
4. `ZlibInv_to_ContractSafe` (non-variadic and variadic) and lifted `ContractSafe` proofs
   for all 15 Wave 1 contracts in `Zlib.allContracts`.
5. `CallWPTermSpec`, `CallSafeSpec`, `CallWPTermSpec.to_callWPSafe`, and `ZALLOC`/`ZFREE`/callback
   combinators (`zalloc_internal_call`, `zfree_internal_call`, `user_callback_wpTerm`,
   `user_callback_wpSafe`).
6. All 12 decoupled cross-module specification records (`InftreesSpecs`, `InffastSpecs`,
   `InflateCoreSpecs`, `InflateMainSpecs`, `InfbackSpecs`, `TreesSpecs`, `DeflateCoreSpecs`,
   `DeflateBlocksSpecs`, `DeflateMainSpecs`, `GzlibSpecs`, `GzreadSpecs`, `GzwriteSpecs`).
-/

namespace Zlib.Proof

open C99 Zlib.Spec

/-! ## 1. Memory, Field Helpers & `initLibz` Bridges -/

/-- A live mutable heap block with minimum byte size and alignment guarantees. -/
def HeapRwBlock (m : Mem) (b : BlockId) (minSize minAlign : Nat) : Prop :=
  ∃ blk, m.blocks b = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw ∧
    minSize ≤ blk.size ∧ minAlign ≤ blk.align

theorem mem_lt_nextBlock {m : Mem} {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) : b < m.nextBlock := by
  rcases Nat.lt_or_ge b m.nextBlock with hlt | hge
  · exact hlt
  · rw [m.fresh b hge] at hb
    cases hb

theorem HeapRwBlock.active {m : Mem} {b : BlockId} {ms ma : Nat}
    (h : HeapRwBlock m b ms ma) : (m.blocks b).isSome = true := by
  rcases h with ⟨blk, hb, _⟩
  simp [hb]

theorem HeapRwBlock.mono {m : Mem} {b : BlockId} {ms1 ms2 ma1 ma2 : Nat}
    (h : HeapRwBlock m b ms1 ma1) (hs : ms2 ≤ ms1) (ha : ma2 ≤ ma1) :
    HeapRwBlock m b ms2 ma2 := by
  rcases h with ⟨blk, hb, hk, hp, hsz, hal⟩
  exact ⟨blk, hb, hk, hp, Nat.le_trans hs hsz, Nat.le_trans ha hal⟩

theorem HeapRwBlock.congr_blocks {m m' : Mem} {b : BlockId} {ms ma : Nat}
    (heq : m'.blocks b = m.blocks b) (h : HeapRwBlock m b ms ma) :
    HeapRwBlock m' b ms ma := by
  rcases h with ⟨blk, hb, rest⟩
  exact ⟨blk, heq ▸ hb, rest⟩

theorem HeapRwBlock.roExt {m m' : Mem} {b : BlockId} {ms ma : Nat}
    (hro : C99.Proof.ROExt m m') (h : HeapRwBlock m b ms ma) : HeapRwBlock m' b ms ma := by
  rcases h with ⟨blk, hb, hk, hp, hsz, hal⟩
  exact ⟨blk, (hro.2.1 b (mem_lt_nextBlock hb)).trans hb, hk, hp, hsz, hal⟩

theorem readField?_congr_block (tags : TypeEnv) {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {st fld : String} (heq : m2.blocks b = m1.blocks b) :
    readField? tags m2 (.ptr b off) st fld = readField? tags m1 (.ptr b off) st fld := by
  unfold readField?
  cases C99.fieldLayout? tags (.structTy st) fld with
  | none => rfl
  | some p => exact readVal_eq_of_blocks_eq tags heq _ p.2

theorem readNatField?_congr_block (tags : TypeEnv) {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {st fld : String} (heq : m2.blocks b = m1.blocks b) :
    readNatField? tags m2 (.ptr b off) st fld = readNatField? tags m1 (.ptr b off) st fld := by
  unfold readNatField?
  rw [readField?_congr_block tags heq]

/-- Read any integer-valued struct field as a mathematical `Int`. -/
def readIntField? (tags : TypeEnv) (m : Mem) (p : Val) (st fld : String) : Option Int := do
  match ← readField? tags m p st fld with
  | .int _ bv => some bv.toInt
  | _ => none

theorem readIntField?_congr_block (tags : TypeEnv) {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {st fld : String} (heq : m2.blocks b = m1.blocks b) :
    readIntField? tags m2 (.ptr b off) st fld = readIntField? tags m1 (.ptr b off) st fld := by
  unfold readIntField?
  rw [readField?_congr_block tags heq]

theorem readable_congr_block {m1 m2 : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (heq : m2.blocks b = m1.blocks b) (h : Readable m1 (.ptr b off) len) :
    Readable m2 (.ptr b off) len := by
  rcases h with ⟨b', off', blk, hptr, hb, hin, hbytes⟩
  cases hptr
  exact ⟨b, off, blk, rfl, heq ▸ hb, hin, hbytes⟩

theorem writable_congr_block {m1 m2 : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (heq : m2.blocks b = m1.blocks b) (h : Writable m1 (.ptr b off) len) :
    Writable m2 (.ptr b off) len := by
  rcases h with ⟨b', off', blk, hptr, hb, hperm, hin⟩
  cases hptr
  exact ⟨b, off, blk, rfl, heq ▸ hb, hperm, hin⟩

theorem readable_roExt {m1 m2 : Mem} {p : Val} {len : Nat}
    (hro : C99.Proof.ROExt m1 m2) (h : Readable m1 p len) : Readable m2 p len := by
  rcases h with ⟨b, off, blk, rfl, hb, hin, hbytes⟩
  exact ⟨b, off, blk, rfl, (hro.2.1 b (mem_lt_nextBlock hb)).trans hb, hin, hbytes⟩

theorem writable_roExt {m1 m2 : Mem} {p : Val} {len : Nat}
    (hro : C99.Proof.ROExt m1 m2) (h : Writable m1 p len) : Writable m2 p len := by
  rcases h with ⟨b, off, blk, rfl, hb, hperm, hin⟩
  exact ⟨b, off, blk, rfl, (hro.2.1 b (mem_lt_nextBlock hb)).trans hb, hperm, hin⟩

theorem strlenAt_congr_block {m1 m2 : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (heq : m2.blocks b = m1.blocks b) (h : m1.strlenAt b off = some len) :
    m2.strlenAt b off = some len := by
  unfold Mem.strlenAt at h ⊢
  rw [heq]
  exact h

theorem strlenAt_roExt {m1 m2 : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (hro : C99.Proof.ROExt m1 m2) (h : m1.strlenAt b off = some len) :
    m2.strlenAt b off = some len := by
  cases hb : m1.blocks b with
  | none =>
    unfold Mem.strlenAt at h
    rw [hb] at h
    cases h
  | some blk =>
    exact strlenAt_congr_block (hro.2.1 b (mem_lt_nextBlock hb)) h

/-- `m'` leaves every block identical to `m` and only advances `nextBlock` (from freed locals). -/
def MemBlocksUnchanged (m m' : Mem) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧ ∀ b, m'.blocks b = m.blocks b

theorem MemBlocksUnchanged.refl (m : Mem) : MemBlocksUnchanged m m :=
  ⟨Nat.le_refl _, fun _ => rfl⟩

theorem MemBlocksUnchanged.trans {m1 m2 m3 : Mem}
    (h12 : MemBlocksUnchanged m1 m2) (h23 : MemBlocksUnchanged m2 m3) :
    MemBlocksUnchanged m1 m3 :=
  ⟨Nat.le_trans h12.1 h23.1, fun b => (h23.2 b).trans (h12.2 b)⟩

theorem MemBlocksUnchanged.to_roExt {m m' : Mem} (h : MemBlocksUnchanged m m') :
    C99.Proof.ROExt m m' := by
  refine ⟨h.1, fun b _ => h.2 b, ?_⟩
  intro b blk hle hs
  rw [h.2 b, m.fresh b hle] at hs
  cases hs

theorem MemBlocksUnchanged.to_framePreserved {m m' : Mem} (h : MemBlocksUnchanged m m')
    (allowed : BlockSet) : FramePreserved m m' allowed := by
  refine ⟨fun b _ _ => h.2 b, fun b blk hnone hsome _ => ?_⟩
  rw [h.2 b, hnone] at hsome
  cases hsome

theorem MemBlocksUnchanged.to_noHeapLeak {m m' : Mem} (h : MemBlocksUnchanged m m')
    (owned' : BlockSet) : NoHeapLeak m m' owned' := by
  intro b blk hsome _
  left
  rw [h.2 b] at hsome
  simp [hsome]

/-- `m'` preserves block existence and metadata (`size`, `align`, `perm`, `kind`, `baseAddr`) on `b`. -/
def PreservesBlockMeta (m m' : Mem) (b : BlockId) : Prop :=
  ∀ blk, m.blocks b = some blk →
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧
      blk'.perm = blk.perm ∧ blk'.kind = blk.kind ∧ blk'.baseAddr = blk.baseAddr

theorem PreservesBlockMeta.refl (m : Mem) (b : BlockId) : PreservesBlockMeta m m b :=
  fun blk hb => ⟨blk, hb, rfl, rfl, rfl, rfl, rfl⟩

theorem PreservesBlockMeta.trans {m1 m2 m3 : Mem} {b : BlockId}
    (h12 : PreservesBlockMeta m1 m2 b) (h23 : PreservesBlockMeta m2 m3 b) :
    PreservesBlockMeta m1 m3 b := by
  intro blk1 hb1
  obtain ⟨blk2, hb2, hsz1, hal1, hp1, hk1, hba1⟩ := h12 blk1 hb1
  obtain ⟨blk3, hb3, hsz2, hal2, hp2, hk2, hba2⟩ := h23 blk2 hb2
  exact ⟨blk3, hb3, hsz2.trans hsz1, hal2.trans hal1, hp2.trans hp1, hk2.trans hk1, hba2.trans hba1⟩

theorem PreservesBlockMeta.of_blocks_eq {m m' : Mem} {b : BlockId}
    (heq : m'.blocks b = m.blocks b) : PreservesBlockMeta m m' b :=
  fun blk hb => ⟨blk, heq ▸ hb, rfl, rfl, rfl, rfl, rfl⟩

theorem PreservesBlockMeta.writable {m m' : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (hpres : PreservesBlockMeta m m' b) (hw : Writable m (.ptr b off) len) :
    Writable m' (.ptr b off) len := by
  rcases hw with ⟨b', off', blk, hptr, hb, hperm, hin⟩
  cases hptr
  obtain ⟨blk', hb', hsz, _, hp, _, _⟩ := hpres blk hb
  refine ⟨b, off, blk', rfl, hb', hp.trans hperm, ?_⟩
  simpa [Mem.inBounds, hsz] using hin

theorem PreservesBlockMeta.typedCell {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} (hpres : PreservesBlockMeta m m' b) (htc : TypedCell tags m (.ptr b off) ty) :
    TypedCell tags m' (.ptr b off) ty := by
  rcases htc with ⟨b', off', blk, hptr, hb, hperm, hin, hal⟩
  cases hptr
  obtain ⟨blk', hb', hsz, _, hp, _, hba⟩ := hpres blk hb
  refine ⟨b, off, blk', rfl, hb', hp.trans hperm, ?_, ?_⟩
  · simpa [Mem.inBounds, hsz] using hin
  · simpa [Mem.isAligned, hba] using hal

/-- `m'` preserves block metadata on `b` and leaves all bytes outside `[off, off + len)` unchanged. -/
def PreservesOutsideRange (m m' : Mem) (b : BlockId) (off : Int64) (len : Nat) : Prop :=
  PreservesBlockMeta m m' b ∧
  ∀ blk, m.blocks b = some blk →
    ∃ blk', m'.blocks b = some blk' ∧
      ∀ i : Nat, ((i : Int) < off.toInt ∨ off.toInt + len ≤ (i : Int)) → blk'.bytes i = blk.bytes i

theorem PreservesOutsideRange.refl (m : Mem) (b : BlockId) (off : Int64) (len : Nat) :
    PreservesOutsideRange m m b off len :=
  ⟨PreservesBlockMeta.refl m b, fun blk hb => ⟨blk, hb, fun _ _ => rfl⟩⟩

theorem PreservesOutsideRange.of_blocks_eq {m m' : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (heq : m'.blocks b = m.blocks b) : PreservesOutsideRange m m' b off len :=
  ⟨PreservesBlockMeta.of_blocks_eq heq, fun blk hb => ⟨blk, heq ▸ hb, fun _ _ => rfl⟩⟩

theorem PreservesOutsideRange.trans {m1 m2 m3 : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (h12 : PreservesOutsideRange m1 m2 b off len)
    (h23 : PreservesOutsideRange m2 m3 b off len) :
    PreservesOutsideRange m1 m3 b off len := by
  refine ⟨h12.1.trans h23.1, fun blk1 hb1 => ?_⟩
  obtain ⟨blk2, hb2, hbytes12⟩ := h12.2 blk1 hb1
  obtain ⟨blk3, hb3, hbytes23⟩ := h23.2 blk2 hb2
  exact ⟨blk3, hb3, fun i hi => (hbytes23 i hi).trans (hbytes12 i hi)⟩

theorem PreservesOutsideRange.mono {m m' : Mem} {b : BlockId} {off1 off2 : Int64} {len1 len2 : Nat}
    (h : PreservesOutsideRange m m' b off2 len2)
    (hlo : off1.toInt ≤ off2.toInt) (hhi : off2.toInt + len2 ≤ off1.toInt + len1) :
    PreservesOutsideRange m m' b off1 len1 := by
  refine ⟨h.1, fun blk hb => ?_⟩
  obtain ⟨blk', hb', hbytes⟩ := h.2 blk hb
  exact ⟨blk', hb', fun i hi => hbytes i (by omega)⟩

theorem PreservesOutsideRange.readBytes_outside {m m' : Mem} {b : BlockId}
    {off roff : Int64} {len rlen : Nat}
    (hpres : PreservesOutsideRange m m' b off len)
    {blk : Block} (hb : m.blocks b = some blk)
    (h0 : 0 ≤ roff.toInt)
    (hdisj : roff.toInt + rlen ≤ off.toInt ∨ off.toInt + len ≤ roff.toInt) :
    m'.readBytes b roff rlen = m.readBytes b roff rlen := by
  obtain ⟨blk', hb', hsz, _, _, _, _⟩ := hpres.1 blk hb
  obtain ⟨blk'', hb'', hbytes⟩ := hpres.2 blk hb
  rw [hb'] at hb''
  cases hb''
  unfold Mem.readBytes
  have hin : Mem.inBounds blk' roff rlen = Mem.inBounds blk roff rlen := by
    simp [Mem.inBounds, hsz]
  simp only [hb', hb, hin, bind, Option.bind]
  cases Mem.inBounds blk roff rlen
  · rfl
  · simp only [guard, Pure.pure]
    apply congrArg some
    apply List.map_congr_left
    intro i hi
    have hlt : i < rlen := List.mem_range.mp hi
    exact hbytes (roff.toInt.toNat + i) (by omega)

private theorem cty_unqual_idem : ∀ ty : CTy, ty.unqual.unqual = ty.unqual
  | .const_ t => by simp [CTy.unqual, cty_unqual_idem t]
  | .typedef _ t => by simp [CTy.unqual, cty_unqual_idem t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

private theorem sizeofAux_unqual (tags : TypeEnv) (fuel : Nat) :
    ∀ ty : CTy, sizeofAux tags fuel ty.unqual = sizeofAux tags fuel ty
  | .const_ t => by simp [CTy.unqual, sizeofAux_unqual tags fuel t]
  | .typedef _ t => by simp [CTy.unqual, sizeofAux_unqual tags fuel t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

private theorem sizeofTy_unqual (tags : TypeEnv) (ty : CTy) :
    sizeofTy tags ty.unqual = sizeofTy tags ty :=
  sizeofAux_unqual tags (tags.length + 1) ty

theorem PreservesOutsideRange.readVal_outside (tags : TypeEnv) {m m' : Mem} {b : BlockId}
    {off roff : Int64} {len : Nat} {ty : CTy}
    (hpres : PreservesOutsideRange m m' b off len)
    {blk : Block} (hb : m.blocks b = some blk)
    (h0 : 0 ≤ roff.toInt)
    (hdisj : roff.toInt + sizeofTy tags ty ≤ off.toInt ∨ off.toInt + len ≤ roff.toInt) :
    Sem.readVal tags m' b roff ty = Sem.readVal tags m b roff ty := by
  obtain ⟨blk', hb', _, _, _, _, hba⟩ := hpres.1 blk hb
  have hsz : sizeofTy tags ty.unqual = sizeofTy tags ty := sizeofTy_unqual tags ty
  have hal : Mem.isAligned blk' roff = Mem.isAligned blk roff := by
    funext al
    simp [Mem.isAligned, hba]
  unfold Sem.readVal
  cases hut : ty.unqual with
  | array _ _ => rfl
  | «int» k =>
    have hk : k.bytes = sizeofTy tags ty := by
      rw [← hsz, hut]; simp [sizeofTy]
    have hrd := hpres.readBytes_outside hb h0 (hk ▸ hdisj)
    simp [CTy.unqual, CTy.intKind?, hb', hb, hal, hrd]
  | enumTy nm isU =>
    have hk : (if isU then IntKind.u32 else IntKind.i32).bytes = sizeofTy tags ty := by
      rw [← hsz, hut]; cases isU <;> simp [sizeofTy] <;> rfl
    have hrd := hpres.readBytes_outside hb h0 (hk ▸ hdisj)
    simp [CTy.unqual, CTy.intKind?, hb', hb, hal, hrd]
  | ptr _ =>
    have hk : (8 : Nat) = sizeofTy tags ty := by
      rw [← hsz, hut]; simp [sizeofTy]
    have hrd := hpres.readBytes_outside hb h0 (hk ▸ hdisj)
    simp [hb', hb, hal, hrd]
  | fnPtr _ _ _ =>
    have hk : (8 : Nat) = sizeofTy tags ty := by
      rw [← hsz, hut]; simp [sizeofTy]
    have hrd := hpres.readBytes_outside hb h0 (hk ▸ hdisj)
    simp [hb', hb, hal, hrd]
  | vaList =>
    have hk : (24 : Nat) = sizeofTy tags ty := by
      rw [← hsz, hut]; simp [sizeofTy]
    have hrd := hpres.readBytes_outside hb h0 (hk ▸ hdisj)
    simp [sizeofTy, hrd]
  | «void» => rfl
  | const_ _ => rfl
  | structTy _ => rfl
  | unionTy _ => rfl
  | anonStruct _ => rfl
  | anonUnion _ => rfl
  | typedef _ _ => rfl

private theorem readVal_writeVal_same_ptr' (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {tyw tyr elw elr : CTy} {v : Val}
    (hwptr : tyw.unqual = .ptr elw) (hrptr : tyr.unqual = .ptr elr)
    (hb : m.blocks b = some blk)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hwr : Sem.writeVal m b off tyw v = some m') :
    Sem.readVal tags m' b off tyr = some v := by
  unfold Sem.writeVal at hwr
  by_cases hc : tyw.isConst
  · simp [hc, bind, Option.bind, guard] at hwr
  · simp only [hc, Bool.not_false, C99.Proof.guard_true, hb, hwptr, bind, Option.bind] at hwr
    have hal : Mem.isAligned blk off 8 = true := by
      cases hg : Mem.isAligned blk off 8
      · simp [hg, guard] at hwr
      · rfl
    simp only [hal, C99.Proof.guard_true] at hwr
    rcases hv with rfl | ⟨pb, poff, rfl⟩
    · have hrd := C99.Proof.readBytes_writeBytes_same hb hwr
      have hblk' := C99.Proof.writeBytes_blocks_eq hb hwr
      have hal' : Mem.isAligned { blk with bytes := (fun i =>
          if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + Mem.encodeNull.length then
            Mem.encodeNull[i - off.toInt.toNat]?.getD .undef
          else blk.bytes i) } off 8 = true := by
        simpa [Mem.isAligned] using hal
      unfold Sem.readVal
      simp only [hrptr, hblk', hal', C99.Proof.guard_true, bind, Option.bind]
      rw [← C99.Proof.encodeNull_length, hrd]
      dsimp [pure]
      rw [C99.Proof.decodePtr_encodeNull]
    · have hrd := C99.Proof.readBytes_writeBytes_same hb hwr
      have hblk' := C99.Proof.writeBytes_blocks_eq hb hwr
      have hal' : Mem.isAligned { blk with bytes := (fun i =>
          if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + (Mem.encodePtr pb poff).length then
            (Mem.encodePtr pb poff)[i - off.toInt.toNat]?.getD .undef
          else blk.bytes i) } off 8 = true := by
        simpa [Mem.isAligned] using hal
      unfold Sem.readVal
      simp only [hrptr, hblk', hal', C99.Proof.guard_true, bind, Option.bind]
      rw [← C99.Proof.encodePtr_length pb poff, hrd]
      dsimp [pure]
      rw [C99.Proof.decodePtr_encodePtr]

theorem PreservesOutsideRange.readField?_outside (tags : TypeEnv) {m m' : Mem}
    {b : BlockId} {pOff off : Int64} {len : Nat} {st fld : String} {foff : Nat} {fty : CTy}
    (hpres : PreservesOutsideRange m m' b off len)
    {blk : Block} (hb : m.blocks b = some blk)
    (hfl : C99.fieldLayout? tags (.structTy st) fld = some (foff, fty))
    (h0 : 0 ≤ pOff.toInt + foff) (hhi : pOff.toInt + foff < 2 ^ 63)
    (hdisj : pOff.toInt + foff + sizeofTy tags fty ≤ off.toInt ∨
      off.toInt + len ≤ pOff.toInt + foff) :
    readField? tags m' (.ptr b pOff) st fld = readField? tags m (.ptr b pOff) st fld := by
  unfold readField?
  simp only [hfl, bind, Option.bind]
  have hroff : (Int64.ofInt (pOff.toInt + foff)).toInt = pOff.toInt + foff :=
    C99.Proof.int64_ofInt_toInt (by omega) hhi
  exact hpres.readVal_outside tags hb (by rw [hroff]; exact h0) (by rw [hroff]; exact hdisj)

theorem PreservesOutsideRange.readNatField?_outside (tags : TypeEnv) {m m' : Mem}
    {b : BlockId} {pOff off : Int64} {len : Nat} {st fld : String} {foff : Nat} {fty : CTy}
    (hpres : PreservesOutsideRange m m' b off len)
    {blk : Block} (hb : m.blocks b = some blk)
    (hfl : C99.fieldLayout? tags (.structTy st) fld = some (foff, fty))
    (h0 : 0 ≤ pOff.toInt + foff) (hhi : pOff.toInt + foff < 2 ^ 63)
    (hdisj : pOff.toInt + foff + sizeofTy tags fty ≤ off.toInt ∨
      off.toInt + len ≤ pOff.toInt + foff) :
    readNatField? tags m' (.ptr b pOff) st fld = readNatField? tags m (.ptr b pOff) st fld := by
  unfold readNatField?
  rw [hpres.readField?_outside tags hb hfl h0 hhi hdisj]

theorem PreservesOutsideRange.readIntField?_outside (tags : TypeEnv) {m m' : Mem}
    {b : BlockId} {pOff off : Int64} {len : Nat} {st fld : String} {foff : Nat} {fty : CTy}
    (hpres : PreservesOutsideRange m m' b off len)
    {blk : Block} (hb : m.blocks b = some blk)
    (hfl : C99.fieldLayout? tags (.structTy st) fld = some (foff, fty))
    (h0 : 0 ≤ pOff.toInt + foff) (hhi : pOff.toInt + foff < 2 ^ 63)
    (hdisj : pOff.toInt + foff + sizeofTy tags fty ≤ off.toInt ∨
      off.toInt + len ≤ pOff.toInt + foff) :
    readIntField? tags m' (.ptr b pOff) st fld = readIntField? tags m (.ptr b pOff) st fld := by
  unfold readIntField?
  rw [hpres.readField?_outside tags hb hfl h0 hhi hdisj]

theorem PreservesOutsideRange.readable_outside {m m' : Mem} {b : BlockId}
    {off roff : Int64} {len rlen : Nat}
    (hpres : PreservesOutsideRange m m' b off len)
    (hr : Readable m (.ptr b roff) rlen)
    (hdisj : roff.toInt + rlen ≤ off.toInt ∨ off.toInt + len ≤ roff.toInt) :
    Readable m' (.ptr b roff) rlen := by
  rcases hr with ⟨b', off', blk, hptr, hb, hin, hbytes⟩
  cases hptr
  obtain ⟨blk', hb', hsz, _, _, _, _⟩ := hpres.1 blk hb
  obtain ⟨blk'', hb'', hbe⟩ := hpres.2 blk hb
  rw [hb'] at hb''
  cases hb''
  have h0 : 0 ≤ roff.toInt := by
    simp [Mem.inBounds] at hin
    exact hin.1
  refine ⟨b, roff, blk', rfl, hb', by simpa [Mem.inBounds, hsz] using hin, fun i hi => ?_⟩
  rw [hbe (roff.toInt.toNat + i) (by omega)]
  exact hbytes i hi

/-- All blocks in `m` other than `errnoBlk` are read-only global blocks. -/
def NonErrnoROGlobal (errnoBlk : BlockId) (m : Mem) : Prop :=
  ∀ b blk, m.blocks b = some blk → b ≠ errnoBlk → blk.perm = .ro ∧ blk.kind = .global

section InitProofHelpers

open Lean Meta Elab Tactic in
local elab "unfold_lhs" h:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  let some (_, lhs, rhs) := decl.type.eq? | throwError "expected equality at {h}"
  let some lhs' ← unfoldDefinition? lhs | throwError "cannot unfold head of {lhs}"
  let newType ← mkEq lhs' rhs
  let goal ← getMainGoal
  let prf := mkFVar decl.fvarId
  let newGoal ← goal.assert decl.userName newType prf
  let (_, newGoal) ← newGoal.intro1P
  let newGoal ← newGoal.tryClear decl.fvarId
  replaceMainGoal [newGoal]

private theorem evalConstExpr_roExt {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    (e : CExpr) {m m' : Mem} {ns ns' : Nat} {v : Val} {ty : CTy}
    (h : Sem.evalConstExpr prog env m strBase ns e = some (v, ty, m', ns')) :
    C99.Proof.ROExt m m' := by
  cases e with
  | paren e0 => exact evalConstExpr_roExt e0 h
  | lit _ _ _ _ _ =>
    simp only [Sem.evalConstExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    exact C99.Proof.ROExt.refl _
  | strLit s =>
    simp only [Sem.evalConstExpr, bind, Option.bind, pure, Pure.pure] at h
    split at h
    · cases h
    · next p heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl, _⟩ := h
      unfold_lhs heq
      split at heq
      · split at heq
        · split at heq
          · cases heq
            refine ⟨Nat.le_succ _, fun b hb => C99.Proof.alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hb),
              fun b blk hge hblk => ?_⟩
            rcases Nat.eq_or_lt_of_le hge with heq_b | hgt
            · rw [← heq_b, C99.Proof.alloc_blocks_eq] at hblk
              cases hblk
              exact ⟨rfl, rfl⟩
            · rw [C99.Proof.alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_gt hgt), m.fresh b (Nat.le_of_lt hgt)] at hblk
              cases hblk
          · cases heq
        · cases heq
      · cases heq
  | var _ =>
    simp only [Sem.evalConstExpr] at h
    split at h
    · cases h; exact C99.Proof.ROExt.refl _
    · split at h
      · cases h; exact C99.Proof.ROExt.refl _
      · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        rcases h with ⟨_, _, _, _, rfl, _⟩
        exact C99.Proof.ROExt.refl _
  | addrOf a =>
    cases a with
    | var name =>
      simp only [Sem.evalConstExpr] at h
      cases hlu : env.lookup name <;> simp only [hlu, Option.map_none, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at h
      · cases h
      · obtain ⟨_, _, rfl, _⟩ := h
        exact C99.Proof.ROExt.refl _
    | _ => simp [Sem.evalConstExpr] at h
  | sizeOfTy _ =>
    simp only [Sem.evalConstExpr, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl, _⟩ := h
    exact C99.Proof.ROExt.refl _
  | cast _ e0 =>
    simp only [Sem.evalConstExpr, bind, Option.bind] at h
    cases heq : Sem.evalConstExpr prog env m strBase ns e0 with
    | none => simp [heq] at h
    | some p =>
      rcases p with ⟨v0, t0, m1, ns1⟩
      simp only [heq] at h
      split at h
      · cases h
      · simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, _⟩ := h
        exact evalConstExpr_roExt e0 heq
  | unary _ e0 =>
    simp only [Sem.evalConstExpr, bind, Option.bind] at h
    cases heq : Sem.evalConstExpr prog env m strBase ns e0 with
    | none => simp [heq] at h
    | some p =>
      rcases p with ⟨v0, t0, m1, ns1⟩
      simp only [heq] at h
      split at h
      · cases h
      · simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, rfl, _⟩ := h
        exact evalConstExpr_roExt e0 heq
  | binary _ l r =>
    simp only [Sem.evalConstExpr, bind, Option.bind] at h
    cases h1 : Sem.evalConstExpr prog env m strBase ns l with
    | none => simp [h1] at h
    | some p1 =>
      rcases p1 with ⟨v1, t1, m1, ns1⟩
      simp only [h1] at h
      cases h2 : Sem.evalConstExpr prog env m1 strBase ns1 r with
      | none => simp [h2] at h
      | some p2 =>
        rcases p2 with ⟨v2, t2, m2, ns2⟩
        simp only [h2] at h
        split at h
        · cases h
        · simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, rfl, _⟩ := h
          exact (evalConstExpr_roExt l h1).trans (evalConstExpr_roExt r h2)
  | sizeOfExpr _ | logAnd _ _ | logOr _ _ | cond _ _ _ | comma _ _ | deref _
  | index _ _ | member _ _ | arrow _ _ | assign _ _ _ | incDec _ _ | call _ _
  | vaStart _ _ | vaEnd _ => simp [Sem.evalConstExpr] at h
termination_by sizeOf e

private def WriteInitInv (bid : BlockId) (m m' : Mem) : Prop :=
  bid < m.nextBlock ∧
  m.nextBlock ≤ m'.nextBlock ∧
  (∀ b, b < m.nextBlock → b ≠ bid → m'.blocks b = m.blocks b) ∧
  (∀ b blk, m.nextBlock ≤ b → m'.blocks b = some blk → blk.kind = .global ∧ blk.perm = .ro) ∧
  (∀ blk, m'.blocks bid = some blk → ∃ blk0, m.blocks bid = some blk0 ∧ blk.kind = blk0.kind)

private theorem writeInitInv_refl {bid : BlockId} {m : Mem} (hb : bid < m.nextBlock) :
    WriteInitInv bid m m :=
  ⟨hb, Nat.le_refl _, fun _ _ _ => rfl,
    (fun b blk hge hblk => by rw [m.fresh b hge] at hblk; cases hblk),
    fun blk h => ⟨blk, h, rfl⟩⟩

private theorem writeInitInv_trans {bid : BlockId} {m1 m2 m3 : Mem}
    (h12 : WriteInitInv bid m1 m2) (h23 : WriteInitInv bid m2 m3) :
    WriteInitInv bid m1 m3 := by
  refine ⟨h12.1, Nat.le_trans h12.2.1 h23.2.1, fun b hlt hne => ?_, fun b blk hge hblk3 => ?_, fun blk hblk3 => ?_⟩
  · exact (h23.2.2.1 b (Nat.lt_of_lt_of_le hlt h12.2.1) hne).trans (h12.2.2.1 b hlt hne)
  · have hne : b ≠ bid := Nat.ne_of_gt (Nat.lt_of_lt_of_le h12.1 hge)
    rcases Nat.lt_or_ge b m2.nextBlock with hlt2 | hge2
    · rw [h23.2.2.1 b hlt2 hne] at hblk3
      exact h12.2.2.2.1 b blk hge hblk3
    · exact h23.2.2.2.1 b blk hge2 hblk3
  · obtain ⟨blk2, h2, hk2⟩ := h23.2.2.2.2 blk hblk3
    obtain ⟨blk1, h1, hk1⟩ := h12.2.2.2.2 blk2 h2
    exact ⟨blk1, h1, hk2.trans hk1⟩

private theorem writeInitInv_of_roExt {bid : BlockId} {m m' : Mem}
    (hb : bid < m.nextBlock) (hro : C99.Proof.ROExt m m') : WriteInitInv bid m m' :=
  ⟨hb, hro.1, fun b hlt _ => hro.2.1 b hlt, hro.2.2, fun blk hblk => by
    rw [hro.2.1 bid hb] at hblk
    exact ⟨blk, hblk, rfl⟩⟩

private theorem writeInitInv_of_writeBytes {bid : BlockId} {m m' : Mem} {off : Int64} {bs : List MemByte}
    (hbid : bid < m.nextBlock) (h : m.writeBytes bid off bs = some m') :
    WriteInitInv bid m m' := by
  have hnext : m'.nextBlock = m.nextBlock := C99.Proof.writeBytes_nextBlock h
  refine ⟨hbid, Nat.le_of_eq hnext.symm, fun b _ hne => C99.Proof.writeBytes_blocks_ne h hne,
    (fun b blk hge hblk => ?_), (fun blk hblk => ?_)⟩
  · have hne : b ≠ bid := Nat.ne_of_gt (Nat.lt_of_lt_of_le hbid hge)
    rw [C99.Proof.writeBytes_blocks_ne h hne, m.fresh b hge] at hblk
    cases hblk
  · unfold Mem.writeBytes at h
    split at h
    · cases h
    · next blk0 h0 =>
      split at h
      · cases h
        simp at hblk
        cases hblk
        exact ⟨blk0, h0, rfl⟩
      · cases h

private theorem writeInitInv_of_writeVal {bid : BlockId} {m m' : Mem} {off : Int64} {ty : CTy} {v : Val}
    (hbid : bid < m.nextBlock) (h : Sem.writeVal m bid off ty v = some m') :
    WriteInitInv bid m m' := by
  obtain ⟨bs, hbs⟩ := C99.Proof.writeVal_writeBytes h
  exact writeInitInv_of_writeBytes hbid hbs

mutual
private theorem writeInitList_writeInitInv {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {bid : BlockId} {off : Int64} {elem : CTy} {idx : Nat} {xs : List InitVal}
    {m m' : Mem} {ns ns' : Nat}
    (hb : bid < m.nextBlock)
    (h : Sem.writeInitList prog env m strBase bid off elem idx xs ns = some (m', ns')) :
    WriteInitInv bid m m' := by
  cases xs with
  | nil =>
    simp only [Sem.writeInitList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact writeInitInv_refl hb
  | cons iv rest =>
    unfold Sem.writeInitList at h
    dsimp only [bind, Option.bind] at h
    split at h
    · cases h
    · next a h1 =>
      rcases a with ⟨m1, ns1⟩
      dsimp only at h
      have h1' := writeInitVal_writeInitInv hb h1
      have h2' := writeInitList_writeInitInv (Nat.lt_of_lt_of_le hb h1'.2.1) h
      exact writeInitInv_trans h1' h2'
termination_by sizeOf xs

private theorem writeInitFields_writeInitInv {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {bid : BlockId} {baseOff offAcc : Nat} {flds : List (String × CTy)} {xs : List InitVal}
    {m m' : Mem} {ns ns' : Nat}
    (hb : bid < m.nextBlock)
    (h : Sem.writeInitFields prog env m strBase bid baseOff offAcc flds xs ns = some (m', ns')) :
    WriteInitInv bid m m' := by
  cases flds with
  | nil =>
    simp only [Sem.writeInitFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact writeInitInv_refl hb
  | cons f frest =>
    cases xs with
    | nil =>
      simp only [Sem.writeInitFields, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact writeInitInv_refl hb
    | cons iv irest =>
      unfold Sem.writeInitFields at h
      dsimp only [bind, Option.bind] at h
      split at h
      · cases h
      · next a h1 =>
        rcases a with ⟨m1, ns1⟩
        dsimp only at h
        have h1' := writeInitVal_writeInitInv hb h1
        have h2' := writeInitFields_writeInitInv (Nat.lt_of_lt_of_le hb h1'.2.1) h
        exact writeInitInv_trans h1' h2'
termination_by sizeOf xs

private theorem writeInitVal_writeInitInv {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {bid : BlockId} {off : Int64} {ty : CTy} {iv : InitVal}
    {m m' : Mem} {ns ns' : Nat}
    (hb : bid < m.nextBlock)
    (h : Sem.writeInitVal prog env m strBase bid off ty iv ns = some (m', ns')) :
    WriteInitInv bid m m' := by
  cases iv with
  | expr e =>
    cases e with
    | strLit s =>
      unfold Sem.writeInitVal at h
      cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only [bind, Option.bind] at h
      all_goals try (
        cases hev : Sem.evalConstExpr prog env m strBase ns (.strLit s) with
        | none => rw [hev] at h; cases h
        | some p =>
          rcases p with ⟨v, t, m1, ns1⟩
          rw [hev] at h
          dsimp only at h
          cases hwr : Sem.writeVal m1 bid off ty.stripConst v with
          | none => rw [hwr] at h; cases h
          | some m2 =>
            rw [hwr] at h
            cases h
            have hro := evalConstExpr_roExt (.strLit s) hev
            exact writeInitInv_trans (writeInitInv_of_roExt hb hro)
              (writeInitInv_of_writeVal (Nat.lt_of_lt_of_le hb hro.1) hwr))
      cases hwb : m.writeBytes bid off _ with
      | none => rw [hwb] at h; cases h
      | some m1 =>
        rw [hwb] at h
        cases h
        exact writeInitInv_of_writeBytes hb hwb
    | _ =>
      unfold Sem.writeInitVal at h
      dsimp only [bind, Option.bind] at h
      split at h
      · cases h
      · next p hev =>
        rcases p with ⟨v, t, m1, ns1⟩
        dsimp only at h
        cases hwr : Sem.writeVal m1 bid off ty.stripConst v with
        | none => simp [hwr] at h
        | some m2 =>
          simp only [hwr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have hro := evalConstExpr_roExt _ hev
          exact writeInitInv_trans (writeInitInv_of_roExt hb hro)
            (writeInitInv_of_writeVal (Nat.lt_of_lt_of_le hb hro.1) hwr)
  | list xs =>
    unfold Sem.writeInitVal at h
    cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only at h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact writeInitList_writeInitInv hb h
    · rename_i tag
      cases hlu : prog.tags.lookup tag with
      | none => simp [hlu] at h
      | some defn =>
        cases defn with
        | structDef flds => simp [hlu] at h; exact writeInitFields_writeInitInv hb h
        | unionDef _ | enumDef _ _ => simp [hlu] at h
    · rename_i tag
      cases xs with
      | nil => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact writeInitInv_refl hb
      | cons x _ =>
        cases hlu : prog.tags.lookup tag with
        | none => simp [hlu] at h
        | some defn =>
          cases defn with
          | unionDef flds =>
            cases flds with
            | nil => simp [hlu] at h
            | cons f _ => simp only [hlu] at h; exact writeInitVal_writeInitInv hb h
          | structDef _ | enumDef _ _ => simp [hlu] at h
    · exact writeInitFields_writeInitInv hb h
    · rename_i flds
      cases xs with
      | nil => simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact writeInitInv_refl hb
      | cons x _ =>
        cases flds with
        | nil => cases h
        | cons f _ => exact writeInitVal_writeInitInv hb h
    · cases h
    · cases h
    · cases h
    · cases h
  | intSeq _ _ =>
    unfold Sem.writeInitVal at h
    cases hty : ty.unqual <;> rw [hty] at h <;> dsimp only at h
    all_goals try cases h
    cases hk : ty.arrayLeafIntKind? with
    | none => simp [hk] at h
    | some _ =>
      simp only [hk, Option.map_eq_some_iff, Prod.mk.injEq] at h
      rcases h with ⟨m1, hwb, rfl, _⟩
      exact writeInitInv_of_writeBytes hb hwb
termination_by sizeOf iv
end

private theorem allocVarInit_roExt {prog : Prog} {env : Env} {m m' : Mem}
    {base strBase : Nat → UInt64} {idx ns ns' : Nat} {d : VarDecl}
    {bid : BlockId} {ty : CTy}
    (hroDecl : (Sem.resolveDeclTy d.ty d.init?).isReadOnly = true)
    (h : Sem.allocVarInit prog env m base strBase idx ns d = some (bid, ty, m', ns')) :
    C99.Proof.ROExt m m' := by
  have hpres := allocVarInit_preserves h
  have hrw : ∃ m1 m2,
      m1.nextBlock = m.nextBlock + 1 ∧
      bid = m.nextBlock ∧
      (∃ blk1, m1.blocks bid = some blk1 ∧ blk1.kind = .global) ∧
      WriteInitInv bid m1 m2 ∧
      m'.nextBlock = m2.nextBlock ∧
      (∀ b, b ≠ bid → m'.blocks b = m2.blocks b) ∧
      (∀ blk', m'.blocks bid = some blk' → ∃ blk2, m2.blocks bid = some blk2 ∧ blk'.perm = .ro ∧ blk'.kind = blk2.kind) := by
    unfold Sem.allocVarInit at h
    simp only [bind, Option.bind, pure, Pure.pure] at h
    split at h
    · cases h
    · next a halloc =>
      rcases a with ⟨bid0, m1⟩
      dsimp only at h
      unfold_lhs halloc
      have ha : bid0 = m.nextBlock ∧ m1.nextBlock = m.nextBlock + 1 ∧
          ∃ blk1, m1.blocks bid0 = some blk1 ∧ blk1.kind = .global := by
        split at halloc
        · split at halloc
          · split at halloc
            · cases halloc
              exact ⟨rfl, rfl, _, C99.Proof.alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl⟩
            · cases halloc
          · cases halloc
        · cases halloc
      rcases ha with ⟨rfl, hm1next, blk1, hblk1, hk1⟩
      have hbid1 : m.nextBlock < m1.nextBlock := by rw [hm1next]; exact Nat.lt_succ_self _
      cases hinit : d.init? with
      | none =>
        rw [hinit] at h
        dsimp only at h
        have hroNone : (Sem.resolveDeclTy d.ty none).isReadOnly = true := hinit ▸ hroDecl
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, _⟩ := h
          refine ⟨m1, m1, hm1next, rfl, ⟨blk1, hblk1, hk1⟩, writeInitInv_refl hbid1, rfl, ?_, ?_⟩
          · intro b hne; simp [beq_false_of_ne hne]
          · intro blk' h'
            simp only [beq_self_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h'
            rcases h' with ⟨blk2, h2, rfl⟩
            exact ⟨blk2, h2, rfl, rfl⟩
        · contradiction
      | some iv =>
        rw [hinit] at h
        dsimp only at h
        split at h
        · cases h
        · next p hwr =>
          rcases p with ⟨m2, ns2⟩
          dsimp only at h
          have hroSome : (Sem.resolveDeclTy d.ty (some iv)).isReadOnly = true := hinit ▸ hroDecl
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, _⟩ := h
            refine ⟨m1, m2, hm1next, rfl, ⟨blk1, hblk1, hk1⟩, writeInitVal_writeInitInv hbid1 hwr, rfl, ?_, ?_⟩
            · intro b hne; simp [beq_false_of_ne hne]
            · intro blk' h'
              simp only [beq_self_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h'
              rcases h' with ⟨blk2, h2, rfl⟩
              exact ⟨blk2, h2, rfl, rfl⟩
          · contradiction
  rcases hrw with ⟨m1, m2, hm1next, rfl, ⟨blk1, hblk1, hk1⟩, hw, _, hne, hbid⟩
  refine ⟨hpres.2.1, fun b hb => hpres.2.2 b hb, fun b blk hge hblk => ?_⟩
  by_cases hbb : b = m.nextBlock
  · subst hbb
    obtain ⟨blk2, hm2, hp', hk'⟩ := hbid blk hblk
    obtain ⟨blk0, h0, hk2⟩ := hw.2.2.2.2 blk2 hm2
    rw [hblk1] at h0; cases h0
    exact ⟨hk'.trans (hk2.trans hk1), hp'⟩
  · rw [hne b hbb] at hblk
    have hm1ge : m1.nextBlock ≤ b := by
      have h1 : m.nextBlock + 1 ≤ b := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hge (Ne.symm hbb))
      rw [hm1next]; exact h1
    exact hw.2.2.2.1 b blk hm1ge hblk

private theorem initGlobs_roExt {globBase strBase : Nat → UInt64} {prog0 : Prog}
    {idx ns ns' : Nat} {env env' : Env} {m m' : Mem}
    {xs : List (Linkage × VarDecl)}
    (hro : ∀ p ∈ xs, (Sem.resolveDeclTy p.2.ty p.2.init?).isReadOnly = true)
    (h : Sem.initProg.initGlobs globBase strBase prog0 idx ns env m xs = some (env', m', ns')) :
    C99.Proof.ROExt m m' := by
  induction xs generalizing idx ns env m with
  | nil =>
    simp only [Sem.initProg.initGlobs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    exact C99.Proof.ROExt.refl _
  | cons p rest ih =>
    unfold Sem.initProg.initGlobs at h
    dsimp only at h
    split at h
    · exact ih (fun q hq => hro q (List.mem_cons_of_mem _ hq)) h
    · dsimp only [bind, Option.bind] at h
      split at h
      · cases h
      · next a hal =>
        rcases a with ⟨bid, ty, m1, ns1⟩
        dsimp only at h
        have hr1 := allocVarInit_roExt (hro p (.head _)) hal
        have hr2 := ih (fun q hq => hro q (List.mem_cons_of_mem _ hq)) h
        exact hr1.trans hr2

private theorem foldlM_allocVarInit_roExt {prog0 : Prog} {gEnv : Env}
    {staticBase strBase : Nat → UInt64} {ds : List VarDecl}
    {sEnv sEnv' : Env} {m m' : Mem} {idx idx' ns ns' : Nat}
    (hro : ∀ d ∈ ds, (Sem.resolveDeclTy d.ty d.init?).isReadOnly = true)
    (h : ds.foldlM (fun (acc : Env × Mem × Nat × Nat) d => do
      let (bid, ty, mB, nB) ← Sem.allocVarInit prog0 gEnv acc.2.1 staticBase strBase acc.2.2.1 acc.2.2.2 d
      pure ((d.name, bid, ty) :: acc.1, mB, acc.2.2.1 + 1, nB)) (sEnv, m, idx, ns) =
        some (sEnv', m', idx', ns')) :
    C99.Proof.ROExt m m' := by
  induction ds generalizing sEnv m idx ns with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _, _⟩ := h
    exact C99.Proof.ROExt.refl _
  | cons d rest ih =>
    simp only [List.foldlM_cons, bind, Option.bind, pure, Pure.pure] at h
    cases hal : Sem.allocVarInit prog0 gEnv m staticBase strBase idx ns d with
    | none => rw [hal] at h; cases h
    | some a =>
      rcases a with ⟨bid, ty, m1, ns1⟩
      rw [hal] at h
      dsimp only at h
      have hr1 := allocVarInit_roExt (hro d (.head _)) hal
      have hr2 := ih (fun q hq => hro q (List.mem_cons_of_mem _ hq)) h
      exact hr1.trans hr2

private theorem initStatics_roExt {staticBase strBase : Nat → UInt64} {prog0 : Prog}
    {gEnv : Env} {idx ns : Nat} {m m' : Mem} {fnAcc fnAcc' : List (String × Env)}
    {fns : List FnDef}
    (hro : ∀ f ∈ fns, ∀ d ∈ Sem.collectFnStatics f.body,
      (Sem.resolveDeclTy d.ty d.init?).isReadOnly = true)
    (h : Sem.initProg.initStatics staticBase strBase prog0 gEnv idx ns m fnAcc fns = some (fnAcc', m')) :
    C99.Proof.ROExt m m' := by
  induction fns generalizing idx ns m fnAcc with
  | nil =>
    simp only [Sem.initProg.initStatics, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact C99.Proof.ROExt.refl _
  | cons f rest ih =>
    unfold Sem.initProg.initStatics at h
    dsimp only [bind, Option.bind] at h
    split at h
    · cases h
    · next a hfold =>
      rcases a with ⟨sEnv, m1, idx1, ns1⟩
      dsimp only at h
      have hr1 := foldlM_allocVarInit_roExt (hro f (.head _)) hfold
      have hr2 := ih (fun g hg => hro g (List.mem_cons_of_mem _ hg)) h
      exact hr1.trans hr2

private theorem zlib_globals_all_ro :
    ((Sem.progOfTUs Zlib.allFiles).globals.all fun p =>
      (Sem.resolveDeclTy p.2.ty p.2.init?).isReadOnly) = true := by
  decide

mutual
private def staticsAllROStmt : CStmt → Bool
  | .decl d => !d.isStatic || (Sem.resolveDeclTy d.ty d.init?).isReadOnly
  | .decls ds => ds.all fun d => !d.isStatic || (Sem.resolveDeclTy d.ty d.init?).isReadOnly
  | .block ss => staticsAllROList ss
  | .ifStmt _ t f? => staticsAllROStmt t && match f? with | some f => staticsAllROStmt f | none => true
  | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b | .switchStmt _ b
  | .caseStmt _ b | .defaultStmt b | .labelStmt _ b => staticsAllROStmt b
  | _ => true

private def staticsAllROList : List CStmt → Bool
  | [] => true
  | s :: ss => staticsAllROStmt s && staticsAllROList ss
end

mutual
private theorem collectFnStatics_ro_of_stmt :
    ∀ (s : CStmt), staticsAllROStmt s = true →
    ∀ d ∈ Sem.collectFnStatics s, (Sem.resolveDeclTy d.ty d.init?).isReadOnly = true
  | .decl d, h => by
    unfold staticsAllROStmt at h
    unfold Sem.collectFnStatics
    simp only [List.mem_ite_nil_right, List.mem_singleton]
    rintro d' ⟨hst, rfl⟩
    simp [hst] at h
    exact h
  | .decls ds, h => by
    unfold staticsAllROStmt at h
    unfold Sem.collectFnStatics
    intro d hd
    have hd' : d ∈ ds ∧ d.isStatic = true := by
      simpa [List.mem_filter] using hd
    have hall := List.all_eq_true.mp h d hd'.1
    simp [hd'.2] at hall
    exact hall
  | .block ss, h => by
    unfold staticsAllROStmt at h
    unfold Sem.collectFnStatics
    intro d hd
    have hmem : ∃ s' ∈ ss, d ∈ Sem.collectFnStatics s' := by
      simpa [List.mem_flatMap] using hd
    rcases hmem with ⟨s', hs', hd'⟩
    exact collectFnStatics_ro_of_list ss h s' hs' d hd'
  | .ifStmt _ t f?, h => by
    unfold staticsAllROStmt at h
    unfold Sem.collectFnStatics
    obtain ⟨ht, hf⟩ := (Bool.and_eq_true _ _).mp h
    intro d hd
    simp only [List.mem_append] at hd
    rcases hd with hdt | hdf
    · exact collectFnStatics_ro_of_stmt t ht d hdt
    · cases f? with
      | none => simp at hdf
      | some f => exact collectFnStatics_ro_of_stmt f hf d hdf
  | .whileStmt _ b, h | .doWhileStmt b _, h | .forStmt _ _ _ b, h | .switchStmt _ b, h
  | .caseStmt _ b, h | .defaultStmt b, h | .labelStmt _ b, h => by
    unfold staticsAllROStmt at h
    unfold Sem.collectFnStatics
    exact collectFnStatics_ro_of_stmt b h
  | .nop, _ | .expr _, _ | .returnStmt _, _ | .breakStmt, _ | .continueStmt, _ | .gotoStmt _, _ => by
    intro d hd
    unfold Sem.collectFnStatics at hd
    simp at hd

private theorem collectFnStatics_ro_of_list :
    ∀ (ss : List CStmt), staticsAllROList ss = true →
    ∀ s ∈ ss, ∀ d ∈ Sem.collectFnStatics s, (Sem.resolveDeclTy d.ty d.init?).isReadOnly = true
  | [], _, _, hs => by simp at hs
  | s :: rest, h, s', hs' => by
    unfold staticsAllROList at h
    obtain ⟨hs, hr⟩ := (Bool.and_eq_true _ _).mp h
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | hrest
    · exact collectFnStatics_ro_of_stmt s' hs
    · exact collectFnStatics_ro_of_list rest hr s' hrest
end

private def tuStaticsAllRO (tu : TU) : Bool :=
  (tu.items.filterMap fun | .fnDef f => some f | _ => none).all fun f => staticsAllROStmt f.body

private theorem zlib_tu_statics_ro (tu : TU) (htu : tu ∈ Zlib.allFiles) :
    tuStaticsAllRO tu = true := by
  rw [Zlib.allFiles, Zlib.allHeaders, Zlib.allTUs] at htu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htu
  rcases htu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have : Zlib.Headers.allABIHeaders.all tuStaticsAllRO = true := by decide
    exact List.all_eq_true.mp this tu h
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

private theorem zlib_fnStatics_all_ro :
    ∀ f ∈ (Zlib.allFiles.flatMap (·.items)).filterMap (fun
      | .fnDef f => some f
      | _ => none),
      ∀ d ∈ Sem.collectFnStatics f.body,
        (Sem.resolveDeclTy d.ty d.init?).isReadOnly = true := by
  intro f hf d hd
  simp only [List.mem_filterMap, List.mem_flatMap] at hf
  rcases hf with ⟨it, ⟨tu, htu, hitem⟩, hsome⟩
  cases it with
  | fnDef fn =>
    simp only at hsome
    cases hsome
    have htu_ro := zlib_tu_statics_ro tu htu
    unfold tuStaticsAllRO at htu_ro
    have hf_mem : f ∈ tu.items.filterMap (fun | .fnDef f => some f | _ => none) := by
      simp only [List.mem_filterMap]
      exact ⟨.fnDef f, hitem, rfl⟩
    exact collectFnStatics_ro_of_stmt f.body (List.all_eq_true.mp htu_ro f hf_mem) d hd
  | _ => simp only at hsome; cases hsome

private theorem initLibz_roExt_of_errno {globBase staticBase strBase : Nat → UInt64}
    {errnoBase : UInt64} {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (h : initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0)) :
    ∃ m_e, os0.errnoBlk = 0 ∧ m_e.nextBlock = 1 ∧
      (∀ b, b ≠ 0 → m_e.blocks b = none) ∧ C99.Proof.ROExt m_e m0 := by
  unfold initLibz at h
  dsimp only [bind, Option.bind, pure, Pure.pure] at h
  split at h
  · cases h
  · next a hinit =>
    rcases a with ⟨p, env, m, os⟩
    cases h
    unfold Sem.initProg at hinit
    dsimp only [bind, Option.bind, pure, Pure.pure] at hinit
    split at hinit
    · cases hinit
    · next pe hal_e =>
      rcases pe with ⟨eBid, m_e⟩
      dsimp only at hinit
      unfold_lhs hal_e
      have he : eBid = 0 ∧ m_e.nextBlock = 1 ∧ ∀ b, b ≠ 0 → m_e.blocks b = none := by
        split at hal_e
        · split at hal_e
          · split at hal_e
            · cases hal_e
              refine ⟨rfl, rfl, fun b hne => ?_⟩
              dsimp only
              rw [show (b == Mem.empty.nextBlock) = false from beq_false_of_ne hne]
              rfl
            · cases hal_e
          · cases hal_e
        · cases hal_e
      rcases he with ⟨rfl, hm_e_next, hm_e_ne⟩
      split at hinit
      · cases hinit
      · next pg hgl =>
        rcases pg with ⟨gEnv1, m1, ns1⟩
        dsimp only at hinit
        split at hinit
        · cases hinit
        · next ps hst =>
          rcases ps with ⟨fnStat, m2⟩
          cases hinit
          have hro_gl : C99.Proof.ROExt m_e m1 :=
            initGlobs_roExt (List.all_eq_true.mp zlib_globals_all_ro) hgl
          have hro_st : C99.Proof.ROExt m1 m2 :=
            initStatics_roExt zlib_fnStatics_all_ro hst
          exact ⟨m_e, rfl, hm_e_next, hm_e_ne, hro_gl.trans hro_st⟩

/-- Every block allocated during `initLibz` other than `os0.errnoBlk` is `.ro` `.global`. -/
theorem initLibz_nonErrnoROGlobal {globBase staticBase strBase : Nat → UInt64}
    {errnoBase : UInt64} {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (h : initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0)) :
    NonErrnoROGlobal os0.errnoBlk m0 := by
  obtain ⟨m_e, heq, hnext, _, hro⟩ := initLibz_roExt_of_errno h
  intro b blk hb hne_err
  rw [heq] at hne_err
  have hge : m_e.nextBlock ≤ b := by
    have hpos : 0 < b := Nat.pos_of_ne_zero hne_err
    rw [hnext]; exact hpos
  obtain ⟨hk, hp⟩ := hro.2.2 b blk hge hb
  exact ⟨hp, hk⟩

private theorem evalConstExpr_strPtr_ge_lim {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {s : String} {m m' : Mem} {ns ns' : Nat} {v : Val} {ty : CTy} {lim : BlockId}
    (hlim : lim ≤ m.nextBlock)
    (h : Sem.evalConstExpr prog env m strBase ns (.cast (.ptr (.const_ (.int .i8))) (.strLit s)) =
      some (v, ty, m', ns')) :
    ∃ sb, v = .ptr sb 0 ∧ lim ≤ sb := by
  unfold Sem.evalConstExpr at h
  dsimp only [bind, Option.bind, pure, Pure.pure] at h
  cases hev : Sem.evalConstExpr prog env m strBase ns (.strLit s) with
  | none => rw [hev] at h; cases h
  | some p =>
    rcases p with ⟨v0, t0, m1, ns1⟩
    rw [hev] at h
    dsimp only at h
    unfold Sem.evalConstExpr at hev
    simp only [bind, Option.bind, pure, Pure.pure] at hev
    split at hev
    · cases hev
    · next a halloc =>
      rcases a with ⟨sb, m1'⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hev
      unfold_lhs halloc
      split at halloc
      · split at halloc
        · split at halloc
          · cases halloc
            have hcast : ∀ mem, Sem.castVal mem (.ptr (.const_ (.int .i8))) (.ptr m.nextBlock 0) =
                some (.ptr m.nextBlock 0) := fun _ => rfl
            rw [hcast] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, _, _⟩ := h
            exact ⟨m.nextBlock, rfl, hlim⟩
          · cases halloc
        · cases halloc
      · cases halloc

private theorem readBytes_congr_slice {m1 m2 : Mem} {b1 b2 : BlockId} {off : Int64} {n : Nat}
    {blk1 blk2 : Block}
    (hb1 : m1.blocks b1 = some blk1) (hb2 : m2.blocks b2 = some blk2)
    (hsz : blk2.size = blk1.size)
    (hbytes : ∀ j < n, blk2.bytes (off.toInt.toNat + j) = blk1.bytes (off.toInt.toNat + j)) :
    m2.readBytes b2 off n = m1.readBytes b1 off n := by
  unfold Mem.readBytes
  have hin : Mem.inBounds blk2 off n = Mem.inBounds blk1 off n := by
    unfold Mem.inBounds; rw [hsz]
  dsimp only [bind, Option.bind, pure, Pure.pure]
  rw [hb1, hb2]
  dsimp only
  rw [hin]
  congr 2
  funext _
  congr 1
  apply List.map_congr_left
  intro j hj
  exact hbytes j (List.mem_range.mp hj)

private theorem readVal_ptr_congr_slice (tags : TypeEnv) {m1 m2 : Mem} {b1 b2 : BlockId}
    {off : Int64} {el : CTy} {blk1 blk2 : Block}
    (hb1 : m1.blocks b1 = some blk1) (hb2 : m2.blocks b2 = some blk2)
    (hsz : blk2.size = blk1.size) (hbase : blk2.baseAddr = blk1.baseAddr)
    (hbytes : ∀ j < 8, blk2.bytes (off.toInt.toNat + j) = blk1.bytes (off.toInt.toNat + j)) :
    Sem.readVal tags m2 b2 off (.ptr el) = Sem.readVal tags m1 b1 off (.ptr el) := by
  unfold Sem.readVal
  dsimp only [CTy.unqual, sizeofTy, alignofTy, bind, Option.bind, pure, Pure.pure]
  rw [hb1, hb2]
  have hal_eq : Mem.isAligned blk2 off 8 = Mem.isAligned blk1 off 8 := by
    unfold Mem.isAligned; rw [hbase]
  dsimp only
  rw [hal_eq]
  simp only [readBytes_congr_slice hb1 hb2 hsz hbytes]

private theorem writeBytes_preserves_before {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    {blk : Block} {n : Nat}
    (hb : m.blocks b = some blk) (h : m.writeBytes b off bs = some m')
    (_h0 : 0 ≤ off.toInt) (hge : n ≤ off.toInt.toNat) :
    ∃ blk', m'.blocks b = some blk' ∧ blk'.size = blk.size ∧ blk'.align = blk.align ∧
      blk'.baseAddr = blk.baseAddr ∧ ∀ i < n, blk'.bytes i = blk.bytes i := by
  refine ⟨_, C99.Proof.writeBytes_blocks_eq hb h, rfl, rfl, rfl, fun i hi => ?_⟩
  have hnat : off.toNatClampNeg = off.toInt.toNat := rfl
  have hn : ¬ (off.toNatClampNeg ≤ i ∧ i < off.toNatClampNeg + bs.length) := by omega
  simp [hn]

private theorem int64_ofNat_toInt_small {n : Nat} (hlt : n < ptrDiffLimit) :
    (Int64.ofNat n).toInt = (n : Int) ∧ (Int64.ofNat n).toInt.toNat = n := by
  have hlim : ptrDiffLimit = 2 ^ 63 := rfl
  have hn : (n : Int) < 2 ^ 63 := by omega
  have hmod : (Int64.ofNat n).toInt = (n : Int) := by
    change (Int64.ofInt (n : Int)).toInt = (n : Int)
    rw [Int64.toInt_ofInt]
    have hsz : (Int64.size : Int) = 2 ^ 64 := rfl
    exact Int.bmod_eq_of_le (by omega) (by omega)
  exact ⟨hmod, by rw [hmod]; exact Int.toNat_natCast n⟩

private theorem writeInitList_zErrmsg_ge_lim {prog : Prog} {env : Env} {strBase : Nat → UInt64}
    {bid : BlockId} {idx : Nat} {strs : List String} {m m' : Mem} {ns ns' : Nat} {lim : BlockId}
    {blk0 : Block}
    (htags : prog.tags = (Sem.progOfTUs Zlib.allFiles).tags)
    (hb : m.blocks bid = some blk0) (hblt : bid < m.nextBlock) (hlim : lim ≤ m.nextBlock)
    (hsz : blk0.size = 8 * (idx + strs.length)) (hal : blk0.align = 8)
    (h : Sem.writeInitList prog env m strBase bid 0 zErrmsgElemTy idx
      (strs.map fun s => .expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s))) ns = some (m', ns')) :
    ∃ blk', m'.blocks bid = some blk' ∧ blk'.size = blk0.size ∧ blk'.align = blk0.align ∧
      blk'.baseAddr = blk0.baseAddr ∧
      (∀ i < 8 * idx, blk'.bytes i = blk0.bytes i) ∧
      ∀ i < strs.length, ∃ sb,
        Sem.readVal prog.tags m' bid (Int64.ofNat (8 * (idx + i))) (.ptr (.const_ (.int .i8))) =
          some (.ptr sb 0) ∧ lim ≤ sb := by
  induction strs generalizing idx m ns blk0 with
  | nil =>
    simp only [List.map_nil, Sem.writeInitList, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨blk0, hb, rfl, rfl, rfl, fun _ _ => rfl, fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩
  | cons s rest ih =>
    simp only [List.map_cons] at h
    unfold Sem.writeInitList at h
    dsimp only [bind, Option.bind] at h
    have hesz : sizeofTy prog.tags zErrmsgElemTy = 8 := by
      rw [htags, zErrmsgElemTy, sizeofTy_const, sizeofTy_ptr]
    cases hstep : Sem.writeInitVal prog env m strBase bid
        (Int64.ofInt ((0 : Int64).toInt + ↑idx * ↑(sizeofTy prog.tags zErrmsgElemTy))) zErrmsgElemTy
        (.expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s))) ns with
    | none => rw [hstep] at h; cases h
    | some p1 =>
      rcases p1 with ⟨m2, ns2⟩
      rw [hstep] at h
      dsimp only at h
      unfold Sem.writeInitVal at hstep
      dsimp only [CTy.unqual, CTy.stripConst, bind, Option.bind] at hstep
      cases hev : Sem.evalConstExpr prog env m strBase ns (.cast (.ptr (.const_ (.int .i8))) (.strLit s)) with
      | none => rw [hev] at hstep; cases hstep
      | some p0 =>
        rcases p0 with ⟨v0, t0, m1, ns1⟩
        rw [hev] at hstep
        dsimp only at hstep
        have hidx_lt : 8 * idx < ptrDiffLimit := by
          have := blk0.sizeLt
          simp only [List.length_cons] at hsz
          omega
        have hzero : (0 : Int64).toInt = 0 := rfl
        have hcast_off : Int64.ofInt ((0 : Int64).toInt + ↑idx * ↑(sizeofTy prog.tags zErrmsgElemTy)) =
            Int64.ofNat (8 * idx) := by
          rw [hesz, hzero, Int.zero_add, Int.mul_comm]
          rfl
        have hstrip : zErrmsgElemTy.stripConst = (.ptr (.const_ (.int .i8))) := rfl
        change Option.map (fun x => (x, ns1)) (Sem.writeVal m1 bid _ zErrmsgElemTy.stripConst v0) = some (m2, ns2) at hstep
        rw [hcast_off, hstrip] at hstep
        cases hwr : Sem.writeVal m1 bid (Int64.ofNat (8 * idx)) (.ptr (.const_ (.int .i8))) v0 with
        | none => rw [hwr] at hstep; cases hstep
        | some m2' =>
          rw [hwr] at hstep
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, _⟩ := hstep
          obtain ⟨sb, rfl, hsb_ge⟩ := evalConstExpr_strPtr_ge_lim hlim hev
          have hpres1 := evalConstExpr_preserves _ hev
          have hb1 : m1.blocks bid = some blk0 := by rw [hpres1.2 bid hblt, hb]
          have hrd2 : Sem.readVal prog.tags m2' bid (Int64.ofNat (8 * idx)) (.ptr (.const_ (.int .i8))) =
              some (.ptr sb 0) :=
            readVal_writeVal_same_ptr' prog.tags rfl rfl hb1 (Or.inr ⟨sb, 0, rfl⟩) hwr
          obtain ⟨bs, hbs⟩ := C99.Proof.writeVal_writeBytes hwr
          have hnext2 : m2'.nextBlock = m1.nextBlock := C99.Proof.writeBytes_nextBlock hbs
          have hblt2 : bid < m2'.nextBlock := by rw [hnext2]; exact Nat.lt_of_lt_of_le hblt hpres1.1
          have hlim2 : lim ≤ m2'.nextBlock := by rw [hnext2]; exact Nat.le_trans hlim hpres1.1
          obtain ⟨hoff_i, hoff_n⟩ := int64_ofNat_toInt_small hidx_lt
          obtain ⟨blk2, hblk2, hsz2, hal2, hba2, hpre2⟩ :=
            writeBytes_preserves_before (n := 8 * idx) hb1 hbs (by omega) (by omega)
          have hsz_rest : blk2.size = 8 * ((idx + 1) + rest.length) := by
            rw [hsz2, hsz]; simp [List.length_cons]; omega
          have hal_rest : blk2.align = 8 := hal2.trans hal
          obtain ⟨blk', hblk', hsz', hal', hba', hpre', hptrs'⟩ := ih hblk2 hblt2 hlim2 hsz_rest hal_rest h
          refine ⟨blk', hblk', hsz'.trans hsz2, hal'.trans hal2, hba'.trans hba2, ?_, fun i hi => ?_⟩
          · intro j hj
            exact (hpre' j (by omega)).trans (hpre2 j hj)
          · cases i with
            | zero =>
              refine ⟨sb, ?_, hsb_ge⟩
              rw [Nat.add_zero]
              have hslice := readVal_ptr_congr_slice prog.tags (el := .const_ (.int .i8)) hblk2 hblk' hsz' hba' (fun j hj => by
                exact hpre' ((Int64.ofNat (8 * idx)).toInt.toNat + j) (by rw [hoff_n]; omega))
              rw [hslice, hrd2]
            | succ i' =>
              have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
              have hidx_eq : idx + (i' + 1) = (idx + 1) + i' := by omega
              rw [hidx_eq]
              exact hptrs' i' hi'

/-- `ZErrmsgReady` holds immediately on the initial memory produced by `initLibz`. -/
theorem zErrmsgReady_of_initLibz {globBase staticBase strBase : Nat → UInt64}
    {errnoBase : UInt64} {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (h : initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0)) :
    ZErrmsgReady prog.tags gEnv m0 := by
  have hprops := initLibz_props h
  have hnon := initLibz_nonErrnoROGlobal h
  obtain ⟨b, blk, hlu, hm0b, hperm, hkind, hsz, hal, hptrs⟩ := hprops.z_errmsg_prop
  have hsb_ne : ∀ i < 10, ∃ sb,
      Sem.readVal prog.tags m0 b (Int64.ofNat (8 * i)) (.ptr (.const_ (.int .i8))) =
        some (.ptr sb 0) ∧ sb ≠ os0.errnoBlk := by
    unfold initLibz at h
    dsimp only [bind, Option.bind, pure, Pure.pure] at h
    split at h
    · cases h
    · next a hinit =>
      rcases a with ⟨p, env, m, os⟩
      cases h
      unfold Sem.initProg at hinit
      dsimp only [bind, Option.bind, pure, Pure.pure] at hinit
      split at hinit
      · cases hinit
      · next pe hal_e =>
        rcases pe with ⟨eBid, m_e⟩
        dsimp only at hinit
        unfold_lhs hal_e
        have he : eBid = 0 ∧ m_e.nextBlock = 1 := by
          split at hal_e
          · split at hal_e
            · split at hal_e
              · cases hal_e; exact ⟨rfl, rfl⟩
              · cases hal_e
            · cases hal_e
          · cases hal_e
        rcases he with ⟨rfl, hm_e_next⟩
        split at hinit
        · cases hinit
        · next pg hgl =>
          rcases pg with ⟨gEnv1, m1, ns1⟩
          dsimp only at hinit
          split at hinit
          · cases hinit
          · next ps hst =>
            rcases ps with ⟨fnStat, m2⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at hinit
            rcases hinit with ⟨hprog_eq, hgEnv_eq, hm0_eq, hos0_eq⟩
            have hfirst : ∃ restGlobs, (Sem.progOfTUs Zlib.allFiles).globals =
                (.export_, Zlib.Zutil.zutilTU_global_z_errmsg) :: restGlobs := by
              refine ⟨(Zlib.allTUs.drop 2).flatMap tuGlobals, ?_⟩
              rw [progOfTUs_globals, Zlib.allFiles, List.flatMap_append]
              have hnil1 : Zlib.allHeaders.flatMap tuGlobals = [] := rfl
              have hall_tus : Zlib.allTUs.flatMap tuGlobals =
                  tuGlobals Zlib.Gzclose.gzcloseTU ++
                    (tuGlobals Zlib.Zutil.zutilTU ++ (Zlib.allTUs.drop 2).flatMap tuGlobals) := rfl
              have hnil2 : tuGlobals Zlib.Gzclose.gzcloseTU = [] := rfl
              have hze : tuGlobals Zlib.Zutil.zutilTU = [(.export_, Zlib.Zutil.zutilTU_global_z_errmsg)] := rfl
              rw [hnil1, List.nil_append, hall_tus, hnil2, List.nil_append, hze, List.cons_append, List.nil_append]
            rcases hfirst with ⟨restGlobs, hfirst⟩
            rw [hfirst] at hgl
            unfold Sem.initProg.initGlobs at hgl
            have hnone : (List.lookup Zlib.Zutil.zutilTU_global_z_errmsg.name
                ([("errno", 0, .int .i32)] : Env)).isSome = false := rfl
            simp only [hnone, Bool.false_eq_true, ↓reduceIte, bind, Option.bind] at hgl
            split at hgl
            · cases hgl
            · next pze hal_ze =>
              rcases pze with ⟨bid_z, ty_z, m_z, ns_z⟩
              dsimp only at hgl
              have hpres_ze := allocVarInit_preserves hal_ze
              have hbid_z_eq : bid_z = 1 := by rw [hpres_ze.1, hm_e_next]
              have hgl_pres := initGlobs_preserves hgl
              have hst_pres := initStatics_preserves hst
              have hlu_z : List.lookup "z_errmsg" gEnv1 = some (bid_z, ty_z) := by
                apply hgl_pres.2
                rfl
              have hlu1 : List.lookup "z_errmsg" gEnv1 = some (b, .array zErrmsgElemTy (some 10)) := by
                simpa [hgEnv_eq] using hlu
              rw [hlu1] at hlu_z; cases hlu_z
              have hb_one : b = 1 := hbid_z_eq
              unfold Sem.allocVarInit at hal_ze
              simp only [bind, Option.bind, pure, Pure.pure] at hal_ze
              split at hal_ze
              · cases hal_ze
              · next az haz =>
                rcases az with ⟨b0, mz1⟩
                dsimp only at hal_ze
                unfold_lhs haz
                have haz_p : b0 = 1 ∧ mz1.nextBlock = 2 ∧
                    ∃ blk1, mz1.blocks 1 = some blk1 ∧ blk1.size = 80 ∧ blk1.align = 8 := by
                  split at haz
                  · split at haz
                    · split at haz
                      · cases haz
                        have hbeq : (1 == m_e.nextBlock) = true := by rw [hm_e_next]; rfl
                        have hres_z : Sem.resolveDeclTy Zlib.Zutil.zutilTU_global_z_errmsg.ty
                            Zlib.Zutil.zutilTU_global_z_errmsg.init? = .array zErrmsgElemTy (some 10) := rfl
                        refine ⟨hm_e_next, ?_, ?_⟩
                        · change m_e.nextBlock + 1 = 2; rw [hm_e_next]
                        · dsimp only
                          rw [hbeq]
                          refine ⟨_, rfl, ?_, ?_⟩
                          · change max 1 (sizeofTy (Sem.progOfTUs Zlib.allFiles).tags
                              (Sem.resolveDeclTy Zlib.Zutil.zutilTU_global_z_errmsg.ty
                                Zlib.Zutil.zutilTU_global_z_errmsg.init?)) = 80
                            rw [hres_z, sizeofTy_array_some, zErrmsgElemTy, sizeofTy_const, sizeofTy_ptr]
                            decide
                          · change max 1 (alignofTy (Sem.progOfTUs Zlib.allFiles).tags
                              (Sem.resolveDeclTy Zlib.Zutil.zutilTU_global_z_errmsg.ty
                                Zlib.Zutil.zutilTU_global_z_errmsg.init?)) = 8
                            rw [hres_z, alignofTy_array, zErrmsgElemTy, alignofTy_const, alignofTy_ptr]
                            rfl
                      · cases haz
                    · cases haz
                  · cases haz
                rcases haz_p with ⟨rfl, hmz1_next, blk1, hblk1, hsz1, hal1⟩
                have hinit_z : Zlib.Zutil.zutilTU_global_z_errmsg.init? =
                    some (.list (zErrmsgStrs.map fun s => .expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s)))) := rfl
                have hty_z : Sem.resolveDeclTy Zlib.Zutil.zutilTU_global_z_errmsg.ty
                    (some (.list (zErrmsgStrs.map fun s => .expr (.cast (.ptr (.const_ (.int .i8))) (.strLit s))))) =
                    .array zErrmsgElemTy (some zErrmsgStrs.length) := rfl
                rw [hinit_z] at hal_ze
                dsimp only at hal_ze
                split at hal_ze
                · cases hal_ze
                · next pw hwr =>
                  rcases pw with ⟨mz2, nsz2⟩
                  dsimp only at hal_ze
                  unfold Sem.writeInitVal at hwr
                  rw [hty_z] at hwr
                  dsimp only [CTy.unqual] at hwr
                  have hlen10 : zErrmsgStrs.length = 10 := rfl
                  obtain ⟨blk2, hblk2, hsz2, hal2, hba2, _, hptrs_ge⟩ :=
                    writeInitList_zErrmsg_ge_lim (prog := Sem.progOfTUs Zlib.allFiles) (lim := 1)
                      rfl hblk1 (by rw [hmz1_next]; decide) (by rw [hmz1_next]; decide)
                      (by rw [hlen10]; exact hsz1) hal1 hwr
                  split at hal_ze
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hal_ze
                    obtain ⟨_, _, hm_z_eq, _⟩ := hal_ze
                    have hblk_z : ∃ blk_f, m_z.blocks 1 = some blk_f ∧ blk_f.size = blk2.size ∧
                        blk_f.align = blk2.align ∧ blk_f.baseAddr = blk2.baseAddr ∧
                        ∀ j, blk_f.bytes j = blk2.bytes j := by
                      refine ⟨{ blk2 with perm := .ro }, ?_, rfl, rfl, rfl, fun _ => rfl⟩
                      rw [← hm_z_eq]
                      dsimp only
                      simp [hblk2]
                    rcases hblk_z with ⟨blk_f, hblkf, hszf, half, hbaf, hbf⟩
                    have hblt_z : 1 < m_z.nextBlock := by
                      by_cases hlt : 1 < m_z.nextBlock
                      · exact hlt
                      · exfalso
                        have hnone := m_z.fresh 1 (Nat.not_lt.mp hlt)
                        rw [hnone] at hblkf
                        cases hblkf
                    have hmem_z : m2.blocks 1 = m_z.blocks 1 := by
                      rw [hst_pres.2 1 (Nat.lt_of_lt_of_le hblt_z hgl_pres.1.1),
                          hgl_pres.1.2 1 hblt_z]
                    intro i hi
                    obtain ⟨sb, hrd2, hsb_ge⟩ := hptrs_ge i hi
                    rw [Nat.zero_add] at hrd2
                    have hrd_f : Sem.readVal (Sem.progOfTUs Zlib.allFiles).tags m_z 1 (Int64.ofNat (8 * i))
                        (.ptr (.const_ (.int .i8))) = some (.ptr sb 0) := by
                      have := readVal_ptr_congr_slice (Sem.progOfTUs Zlib.allFiles).tags
                        (off := Int64.ofNat (8 * i)) (el := .const_ (.int .i8)) hblk2 hblkf hszf hbaf
                        (fun j _ => hbf _)
                      rw [this, hrd2]
                    have hrd_m2 : Sem.readVal (Sem.progOfTUs Zlib.allFiles).tags m2 1 (Int64.ofNat (8 * i))
                        (.ptr (.const_ (.int .i8))) = some (.ptr sb 0) := by
                      rw [readVal_eq_of_blocks_eq _ hmem_z]
                      exact hrd_f
                    refine ⟨sb, ?_, ?_⟩
                    · dsimp only
                      rw [← hprog_eq, ← hm0_eq, hb_one]
                      exact hrd_m2
                    · dsimp only
                      rw [← hos0_eq]
                      exact Nat.ne_of_gt hsb_ge
                  · contradiction
  refine ⟨b, blk, hlu, hm0b, hperm, hkind, hsz, hal, fun i hi => ?_⟩
  obtain ⟨sb, len, hrd, hstr⟩ := hptrs i hi
  obtain ⟨sb', hrd', hne⟩ := hsb_ne i hi
  rw [hrd] at hrd'; cases hrd'
  cases hsblk : m0.blocks sb with
  | none => unfold Mem.strlenAt at hstr; rw [hsblk] at hstr; cases hstr
  | some sblk =>
    obtain ⟨hsperm, hskind⟩ := hnon sb sblk hsblk hne
    exact ⟨sb, sblk, len, hrd, hsblk, hsperm, hskind, hstr⟩

end InitProofHelpers

/-! ## 2. Code Tables, Inflate / InflateBack / Deflate Stream Invariants -/

/-- Well-formedness of one compiled `code` table entry `{ op : u8, bits : u8, val : u16 }`. -/
def CodeSlotEntryValid (isRoot isDist : Bool) (count root : Nat) (op bits val : Nat) : Prop :=
  1 ≤ bits ∧ bits ≤ 15 ∧
  if op &&& 16 ≠ 0 then
    (op &&& 15) ≤ 15 ∧ op &&& 64 = 0 ∧
    1 ≤ val ∧
    if isDist then val + ((1 <<< (op &&& 15)) - 1) ≤ 32768
    else val + ((1 <<< (op &&& 15)) - 1) ≤ 258
  else if op &&& 64 = 0 ∧ op ≠ 0 then
    isRoot = true ∧ 1 ≤ op ∧ bits = root ∧ op + root ≤ 15 ∧ val + (1 <<< op) ≤ count
  else
    (op = 0 ∧ isDist = false ∧ val ≤ 258) ∨ (op &&& 64) ≠ 0

/-- Valid compiled Huffman decoding table (`code[count]`) rooted at `p` with `root` root bits. -/
def CodeTableValid (tags : TypeEnv) (m : Mem) (p : Val) (root count : Nat) (isDist : Bool) : Prop :=
  1 ≤ root ∧ root ≤ 15 ∧ 2 ^ root ≤ count ∧ count ≤ 1732 ∧
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧
    Mem.inBounds blk off (4 * count) = true ∧ Mem.isAligned blk off 2 = true ∧
    ∀ i < count, ∃ op bits val : Nat,
      Sem.readVal tags m b (Int64.ofInt (off.toInt + 4 * i)) (.int .u8) =
        some (.int .u8 (BitVec.ofNat 8 op)) ∧
      Sem.readVal tags m b (Int64.ofInt (off.toInt + 4 * i + 1)) (.int .u8) =
        some (.int .u8 (BitVec.ofNat 8 bits)) ∧
      Sem.readVal tags m b (Int64.ofInt (off.toInt + 4 * i + 2)) (.int .u16) =
        some (.int .u16 (BitVec.ofNat 16 val)) ∧
      op < 256 ∧ bits < 256 ∧ val < 65536 ∧
      CodeSlotEntryValid (decide (i < 2 ^ root)) isDist count root op bits val

theorem CodeTableValid.congr_block {tags : TypeEnv} {m1 m2 : Mem} {p : Val}
    {root count : Nat} {isDist : Bool} {b : BlockId}
    (hp : PtrBlock p = some b) (heq : m2.blocks b = m1.blocks b)
    (h : CodeTableValid tags m1 p root count isDist) :
    CodeTableValid tags m2 p root count isDist := by
  rcases h with ⟨h1, h2, h3, h4, b', off, blk, rfl, hb, hin, hal, hslots⟩
  simp only [PtrBlock, Option.some.injEq] at hp
  subst hp
  refine ⟨h1, h2, h3, h4, b', off, blk, rfl, heq ▸ hb, hin, hal, fun i hi => ?_⟩
  rcases hslots i hi with ⟨op, bits, val, ho, hbi, hva, h1', h2', h3', hslot⟩
  refine ⟨op, bits, val, ?_, ?_, ?_, h1', h2', h3', hslot⟩
  · rw [readVal_eq_of_blocks_eq tags heq]; exact ho
  · rw [readVal_eq_of_blocks_eq tags heq]; exact hbi
  · rw [readVal_eq_of_blocks_eq tags heq]; exact hva

theorem CodeTableValid.roExt {tags : TypeEnv} {m1 m2 : Mem} {p : Val}
    {root count : Nat} {isDist : Bool} (hro : C99.Proof.ROExt m1 m2)
    (h : CodeTableValid tags m1 p root count isDist) :
    CodeTableValid tags m2 p root count isDist := by
  rcases h with ⟨h1, h2, h3, h4, b, off, blk, rfl, hb, hin, hal, hslots⟩
  exact CodeTableValid.congr_block rfl (hro.2.1 b (mem_lt_nextBlock hb))
    ⟨h1, h2, h3, h4, b, off, blk, rfl, hb, hin, hal, hslots⟩

private theorem bitVec_ofNat_inj8 {a b : Nat} (ha : a < 256) (hb : b < 256)
    (h : BitVec.ofNat 8 a = BitVec.ofNat 8 b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

private theorem bitVec_ofNat_inj16 {a b : Nat} (ha : a < 65536) (hb : b < 65536)
    (h : BitVec.ofNat 16 a = BitVec.ofNat 16 b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

private theorem int64_ofNat_eq_ofInt (n : Nat) :
    Int64.ofNat n = Int64.ofInt ((0 : Int64).toInt + (n : Int)) := by
  have h0 : (0 : Int64).toInt = 0 := rfl
  rw [h0, Int.zero_add]
  rfl

private theorem lenfix_extra_props :
    ∀ op, op ≤ 21 → 16 ≤ op → op &&& 16 ≠ 0 ∧ op &&& 15 ≤ 15 ∧ op &&& 64 = 0 := by
  decide

private theorem distfix_extra_props :
    ∀ op, op ≤ 29 → 16 ≤ op → op &&& 16 ≠ 0 ∧ op &&& 15 ≤ 15 ∧ op &&& 64 = 0 := by
  decide

theorem codeTableValid_of_lenfix {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (hall : InitLibzAllProps prog gEnv m0 os0) (hb : BaseInv m0 os0 v owned m os)
    {b_lf : BlockId}
    (hlu : gEnv.lookup "lenfix" = some (b_lf, codeConstTy.array (some 512))) :
    CodeTableValid prog.tags m (.ptr b_lf 0) 9 512 false := by
  rcases hall.lenfix_prop with ⟨b', blk, hlu', hm0b, _, _, hsz, hal, _, hslots⟩
  rw [hlu] at hlu'; cases hlu'
  have hmb : m.blocks b_lf = some blk := BaseInv.global_block_eq_of_m0_size_ne hall.base hb hm0b (by omega)
  refine ⟨by decide, by decide, by decide, by decide, b_lf, 0, blk, rfl, hmb, ?_, ?_, fun i hi => ?_⟩
  · simp [Mem.inBounds, hsz]
  · have hba := blk.baseAligned
    rw [hal] at hba
    simp [Mem.isAligned, hba]
  · rcases hslots i hi with ⟨op, bits, val, _, _, _, hro, hrb, hrv, hbits7, hbits9, hkind⟩
    have hop_lt : op < 256 := by rcases hkind with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, h21, _⟩ <;> omega
    have hbits_lt : bits < 256 := by omega
    have hval_lt : val < 65536 := by
      rcases hkind with ⟨_, hv⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, hv⟩
      · omega
      · decide
      · decide
      · have hpos : 0 < (1 <<< (op &&& 15)) := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_pos (by decide)
        omega
    refine ⟨op, bits, val, ?_, ?_, ?_, hop_lt, hbits_lt, hval_lt, ?_⟩
    · rw [readVal_eq_of_blocks_eq prog.tags (hmb.trans hm0b.symm)]
      simpa [int64_ofNat_eq_ofInt] using hro
    · rw [readVal_eq_of_blocks_eq prog.tags (hmb.trans hm0b.symm)]
      have hcast : Int64.ofNat (4 * i + 1) = Int64.ofInt ((0 : Int64).toInt + 4 * ↑i + 1) := by
        have h0 : (0 : Int64).toInt = 0 := rfl
        rw [h0, Int.zero_add]; congr 1
      simpa [hcast] using hrb
    · rw [readVal_eq_of_blocks_eq prog.tags (hmb.trans hm0b.symm)]
      have hcast : Int64.ofNat (4 * i + 2) = Int64.ofInt ((0 : Int64).toInt + 4 * ↑i + 2) := by
        have h0 : (0 : Int64).toInt = 0 := rfl
        rw [h0, Int.zero_add]; congr 1
      simpa [hcast] using hrv
    · refine ⟨by omega, by omega, ?_⟩
      rcases hkind with ⟨rfl, hv⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨h16, h21, hv, hbound⟩
      · simp; omega
      · simp
      · simp
      · obtain ⟨h16', h15, h64⟩ := lenfix_extra_props op h21 h16
        have hpos : 0 < (1 <<< (op &&& 15)) := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_pos (by decide)
        simp only [h16', h15, h64, ne_eq, not_false_eq_true, Bool.false_eq_true, ↓reduceIte, true_and]
        omega

theorem codeTableValid_of_distfix {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (hall : InitLibzAllProps prog gEnv m0 os0) (hb : BaseInv m0 os0 v owned m os)
    {b_df : BlockId}
    (hlu : gEnv.lookup "distfix" = some (b_df, codeConstTy.array (some 32))) :
    CodeTableValid prog.tags m (.ptr b_df 0) 5 32 true := by
  rcases hall.distfix_prop with ⟨b', blk, hlu', hm0b, _, _, hsz, hal, _, hslots⟩
  rw [hlu] at hlu'; cases hlu'
  have hmb : m.blocks b_df = some blk := BaseInv.global_block_eq_of_m0_size_ne hall.base hb hm0b (by omega)
  refine ⟨by decide, by decide, by decide, by decide, b_df, 0, blk, rfl, hmb, ?_, ?_, fun i hi => ?_⟩
  · simp [Mem.inBounds, hsz]
  · have hba := blk.baseAligned
    rw [hal] at hba
    simp [Mem.isAligned, hba]
  · rcases hslots i hi with ⟨op, bits, val, _, _, _, hro, hrb, hrv, hbits5, hkind⟩
    have hop_lt : op < 256 := by rcases hkind with ⟨rfl, _⟩ | ⟨_, h29, _⟩ <;> omega
    have hbits_lt : bits < 256 := by omega
    have hval_lt : val < 65536 := by
      rcases hkind with ⟨_, rfl⟩ | ⟨_, _, _, hv⟩
      · decide
      · have hpos : 0 < (1 <<< (op &&& 15)) := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_pos (by decide)
        omega
    refine ⟨op, bits, val, ?_, ?_, ?_, hop_lt, hbits_lt, hval_lt, ?_⟩
    · rw [readVal_eq_of_blocks_eq prog.tags (hmb.trans hm0b.symm)]
      simpa [int64_ofNat_eq_ofInt] using hro
    · rw [readVal_eq_of_blocks_eq prog.tags (hmb.trans hm0b.symm)]
      have hcast : Int64.ofNat (4 * i + 1) = Int64.ofInt ((0 : Int64).toInt + 4 * ↑i + 1) := by
        have h0 : (0 : Int64).toInt = 0 := rfl
        rw [h0, Int.zero_add]; congr 1
      simpa [hcast] using hrb
    · rw [readVal_eq_of_blocks_eq prog.tags (hmb.trans hm0b.symm)]
      have hcast : Int64.ofNat (4 * i + 2) = Int64.ofInt ((0 : Int64).toInt + 4 * ↑i + 2) := by
        have h0 : (0 : Int64).toInt = 0 := rfl
        rw [h0, Int.zero_add]; congr 1
      simpa [hcast] using hrv
    · refine ⟨by omega, by omega, ?_⟩
      rcases hkind with ⟨rfl, _⟩ | ⟨h16, h29, h1v, hbound⟩
      · simp
      · obtain ⟨h16', h15, h64⟩ := distfix_extra_props op h29 h16
        have hpos : 0 < (1 <<< (op &&& 15)) := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_pos (by decide)
        simp only [h16', h15, h64, ne_eq, not_false_eq_true, ↓reduceIte, true_and]
        exact ⟨h1v, by omega⟩

/-- Permutation table `order[0..18]` used by `inflate` in `LENLENS` (`mode = 16197`). -/
def inflateOrder : List Nat :=
  [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Owned heap block IDs of one live `inflate` stream. -/
structure InflateWitness where
  stBid : BlockId
  win? : Option BlockId
  deriving DecidableEq, Repr

def InflateWitness.ownedList (iw : InflateWitness) : List BlockId :=
  iw.stBid :: iw.win?.toList

/-- Full memory invariant for an initialized `inflate` stream at `strmPtr`
(either external caller `(.ptr b 0)` or embedded `(.ptr gzBid 136)`).
Does NOT constrain client-mutable `z_stream_s` fields (`next_in`, `avail_in`,
`total_in`, `next_out`, `avail_out`, `total_out`, `msg`, `data_type`, `adler`, `reserved`). -/
def InflateStateInv (tags : TypeEnv) (gEnv : Env) (m : Mem)
    (strmPtr : Val) (iw : InflateWitness) : Prop :=
  HeapRwBlock m iw.stBid 8328 8 ∧
  (∀ wb, iw.win? = some wb → wb ≠ iw.stBid) ∧
  readField? tags m strmPtr "z_stream_s" "state" = some (.ptr iw.stBid 0) ∧
  readField? tags m strmPtr "z_stream_s" "zalloc" = some (.fnPtr "zcalloc") ∧
  readField? tags m strmPtr "z_stream_s" "zfree" = some (.fnPtr "zcfree") ∧
  (∃ op, readField? tags m strmPtr "z_stream_s" "opaque" = some op ∧
    (op = .null ∨ ∃ ob ooff, op = .ptr ob ooff)) ∧
  let st : Val := .ptr iw.stBid 0
  readField? tags m st "inflate_state" "strm" = some strmPtr ∧
  (∃ mode, readNatField? tags m st "inflate_state" "mode" = some mode ∧
    16180 ≤ mode ∧ mode ≤ 16211) ∧
  (∃ last_, readIntField? tags m st "inflate_state" "last" = some last_) ∧
  (∃ wrap, readIntField? tags m st "inflate_state" "wrap" = some wrap ∧
    0 ≤ wrap ∧ wrap ≤ 7 ∧ wrap ≠ 4) ∧
  (∃ reqwrap, readIntField? tags m st "inflate_state" "reqwrap" = some reqwrap ∧
    0 ≤ reqwrap ∧ reqwrap ≤ 7 ∧ reqwrap ≠ 4) ∧
  (∃ havedict, readIntField? tags m st "inflate_state" "havedict" = some havedict) ∧
  (∃ flags, readIntField? tags m st "inflate_state" "flags" = some flags) ∧
  (∃ dmax, readNatField? tags m st "inflate_state" "dmax" = some dmax) ∧
  (∃ check, readNatField? tags m st "inflate_state" "check" = some check) ∧
  (∃ total, readNatField? tags m st "inflate_state" "total" = some total) ∧
  (∃ hd, readField? tags m st "inflate_state" "head" = some hd ∧
    (hd = .null ∨ ∃ hb hoff, hd = .ptr hb hoff)) ∧
  (∃ reqbits wbits wsize whave wnext wrap reqwrap mode,
    readNatField? tags m st "inflate_state" "reqbits" = some reqbits ∧
    readNatField? tags m st "inflate_state" "wbits" = some wbits ∧
    readNatField? tags m st "inflate_state" "wsize" = some wsize ∧
    readNatField? tags m st "inflate_state" "whave" = some whave ∧
    readNatField? tags m st "inflate_state" "wnext" = some wnext ∧
    readIntField? tags m st "inflate_state" "wrap" = some wrap ∧
    readIntField? tags m st "inflate_state" "reqwrap" = some reqwrap ∧
    readNatField? tags m st "inflate_state" "mode" = some mode ∧
    (reqbits = 0 ∨ (8 ≤ reqbits ∧ reqbits ≤ 15)) ∧
    (wbits = 0 ∨ (8 ≤ wbits ∧ wbits ≤ 15)) ∧
    (reqwrap = 0 → 8 ≤ reqbits) ∧
    (wrap = 0 → 8 ≤ wbits) ∧
    (16181 ≤ mode ∧ mode ≤ 16208 → 8 ≤ wbits) ∧
    match iw.win? with
    | none =>
      readField? tags m st "inflate_state" "window" = some .null ∧
      wsize = 0 ∧ whave = 0 ∧ wnext = 0
    | some wb =>
      8 ≤ wbits ∧ wbits ≤ 15 ∧
      readField? tags m st "inflate_state" "window" = some (.ptr wb 0) ∧
      ∃ wblk, m.blocks wb = some wblk ∧ wblk.kind = .heap ∧ wblk.perm = .rw ∧
        2 ^ wbits ≤ wblk.size ∧ 1 ≤ wblk.align ∧
        ((wsize = 0 ∧ whave = 0 ∧ wnext = 0) ∨
         (wsize = 2 ^ wbits ∧ whave ≤ wsize ∧ wnext < wsize ∧
           (whave < wsize → wnext = whave) ∧
           ∀ j < whave, ∃ u : UInt8, wblk.bytes j = .byte u))) ∧
  (∃ hold bits length_ offset_ extra lenbits distbits ncode nlen ndist have_ sane back was,
    readNatField? tags m st "inflate_state" "hold" = some hold ∧
    readNatField? tags m st "inflate_state" "bits" = some bits ∧ bits ≤ 39 ∧
    readNatField? tags m st "inflate_state" "length" = some length_ ∧
    readNatField? tags m st "inflate_state" "offset" = some offset_ ∧
    readNatField? tags m st "inflate_state" "extra" = some extra ∧
    readNatField? tags m st "inflate_state" "lenbits" = some lenbits ∧
    readNatField? tags m st "inflate_state" "distbits" = some distbits ∧
    readNatField? tags m st "inflate_state" "ncode" = some ncode ∧
    readNatField? tags m st "inflate_state" "nlen" = some nlen ∧
    readNatField? tags m st "inflate_state" "ndist" = some ndist ∧
    readNatField? tags m st "inflate_state" "have" = some have_ ∧
    readIntField? tags m st "inflate_state" "sane" = some sane ∧ sane = 1 ∧
    readIntField? tags m st "inflate_state" "back" = some back ∧ -1 ≤ back ∧ back ≤ 256 ∧
    readNatField? tags m st "inflate_state" "was" = some was) ∧
  (∃ nextIdx : Nat, nextIdx ≤ 1732 ∧
    readField? tags m st "inflate_state" "next" =
      some (.ptr iw.stBid (Int64.ofNat (1384 + 4 * nextIdx)))) ∧
  (∃ lcode dcode,
    readField? tags m st "inflate_state" "lencode" = some lcode ∧
    readField? tags m st "inflate_state" "distcode" = some dcode ∧
    ((lcode = .ptr iw.stBid 1384 ∧
        ∃ doff : Nat, dcode = .ptr iw.stBid (Int64.ofNat (1384 + 4 * doff)) ∧ doff ≤ 1732) ∨
      (∃ b_lf blk_lf b_df blk_df,
        gEnv.lookup "lenfix" = some (b_lf, codeConstTy.array (some 512)) ∧
        m.blocks b_lf = some blk_lf ∧ blk_lf.kind = .global ∧ blk_lf.perm = .ro ∧
        lcode = .ptr b_lf 0 ∧
        gEnv.lookup "distfix" = some (b_df, codeConstTy.array (some 32)) ∧
        m.blocks b_df = some blk_df ∧ blk_df.kind = .global ∧ blk_df.perm = .ro ∧
        dcode = .ptr b_df 0))) ∧
  (∀ mode, readNatField? tags m st "inflate_state" "mode" = some mode →
    (mode = 16197 →
      ∃ ncode nlen ndist have_ : Nat,
        readNatField? tags m st "inflate_state" "ncode" = some ncode ∧
        readNatField? tags m st "inflate_state" "nlen" = some nlen ∧
        readNatField? tags m st "inflate_state" "ndist" = some ndist ∧
        readNatField? tags m st "inflate_state" "have" = some have_ ∧
        ncode ≤ 19 ∧ 257 ≤ nlen ∧ nlen ≤ 286 ∧ 1 ≤ ndist ∧ ndist ≤ 30 ∧ have_ ≤ ncode ∧
        ∀ j < have_, ∃ v : BitVec 16,
          Sem.readVal tags m iw.stBid
            (Int64.ofNat (168 + 2 * inflateOrder[j]?.getD 0)) (.int .u16) =
            some (.int .u16 v) ∧ v.toNat ≤ 15) ∧
    (mode = 16198 →
      ∃ nlen ndist have_ lenbits count : Nat,
        readNatField? tags m st "inflate_state" "nlen" = some nlen ∧
        readNatField? tags m st "inflate_state" "ndist" = some ndist ∧
        readNatField? tags m st "inflate_state" "have" = some have_ ∧
        readNatField? tags m st "inflate_state" "lenbits" = some lenbits ∧
        257 ≤ nlen ∧ nlen ≤ 286 ∧ 1 ≤ ndist ∧ ndist ≤ 30 ∧ have_ ≤ nlen + ndist ∧
        lenbits ≤ 7 ∧
        CodeTableValid tags m (.ptr iw.stBid 1384) lenbits count false ∧ count ≤ 128 ∧
        ∀ i < have_, ∃ v : BitVec 16,
          Sem.readVal tags m iw.stBid (Int64.ofNat (168 + 2 * i)) (.int .u16) = some (.int .u16 v) ∧
          v.toNat ≤ 15) ∧
    (16199 ≤ mode ∧ mode ≤ 16205 →
      ∃ (lcode dcode : Val) (lenbits distbits length_ offset_ extra was : Nat),
        readField? tags m st "inflate_state" "lencode" = some lcode ∧
        readField? tags m st "inflate_state" "distcode" = some dcode ∧
        readNatField? tags m st "inflate_state" "lenbits" = some lenbits ∧
        readNatField? tags m st "inflate_state" "distbits" = some distbits ∧
        readNatField? tags m st "inflate_state" "length" = some length_ ∧
        readNatField? tags m st "inflate_state" "offset" = some offset_ ∧
        readNatField? tags m st "inflate_state" "extra" = some extra ∧
        readNatField? tags m st "inflate_state" "was" = some was ∧
        lenbits ≤ 10 ∧ distbits ≤ 8 ∧
        (∃ lcount, CodeTableValid tags m lcode lenbits lcount false ∧
          (lcode = .ptr iw.stBid 1384 → lcount ≤ 1332)) ∧
        (∃ dcount, CodeTableValid tags m dcode distbits dcount true) ∧
        (mode = 16201 → 1 ≤ length_ ∧ extra ≤ 15 ∧ length_ + (1 <<< extra) - 1 ≤ 258) ∧
        (mode = 16202 → 1 ≤ length_ ∧ length_ ≤ 258 ∧ was = length_) ∧
        (mode = 16203 → 1 ≤ length_ ∧ length_ ≤ 258 ∧ extra ≤ 15 ∧
          1 ≤ offset_ ∧ offset_ + (1 <<< extra) - 1 ≤ 32768 ∧ length_ ≤ was ∧ was ≤ 258) ∧
        (mode = 16204 → 1 ≤ length_ ∧ length_ ≤ 258 ∧
          1 ≤ offset_ ∧ offset_ ≤ 32768 ∧ length_ ≤ was ∧ was ≤ 258)))

/-- Ownership and state invariant for `inflateBack` stream (window block is caller-owned). -/
structure InflateBackWitness where
  stBid : BlockId
  winBid : BlockId
  winOff : Int64
  wbits : Nat
  deriving DecidableEq, Repr

def InflateBackWitness.ownedList (ibw : InflateBackWitness) : List BlockId :=
  [ibw.stBid]

def InflateBackInv (tags : TypeEnv) (m : Mem)
    (strmPtr : Val) (ibw : InflateBackWitness) : Prop :=
  HeapRwBlock m ibw.stBid 8328 8 ∧
  PtrBlock strmPtr ≠ some ibw.winBid ∧ ibw.winBid ≠ ibw.stBid ∧
  8 ≤ ibw.wbits ∧ ibw.wbits ≤ 15 ∧
  Writable m (.ptr ibw.winBid ibw.winOff) (2 ^ ibw.wbits) ∧
  readField? tags m strmPtr "z_stream_s" "state" = some (.ptr ibw.stBid 0) ∧
  readField? tags m strmPtr "z_stream_s" "zalloc" = some (.fnPtr "zcalloc") ∧
  readField? tags m strmPtr "z_stream_s" "zfree" = some (.fnPtr "zcfree") ∧
  (∃ op, readField? tags m strmPtr "z_stream_s" "opaque" = some op ∧
    (op = .null ∨ ∃ ob ooff, op = .ptr ob ooff)) ∧
  let st : Val := .ptr ibw.stBid 0
  readField? tags m st "inflate_state" "window" = some (.ptr ibw.winBid ibw.winOff) ∧
  readNatField? tags m st "inflate_state" "wbits" = some ibw.wbits ∧
  readNatField? tags m st "inflate_state" "wsize" = some (2 ^ ibw.wbits) ∧
  readNatField? tags m st "inflate_state" "wnext" = some 0 ∧
  (∃ whave, readNatField? tags m st "inflate_state" "whave" = some whave ∧
    whave ≤ 2 ^ ibw.wbits) ∧
  readNatField? tags m st "inflate_state" "sane" = some 1 ∧
  readNatField? tags m st "inflate_state" "dmax" = some 32768

/-- Owned heap block IDs of one live `deflate` stream (`state`, `window`, `prev`, `head`, `pending_buf`). -/
structure DeflateWitness where
  stBid : BlockId
  winBid : BlockId
  prevBid : BlockId
  headBid : BlockId
  pbufBid : BlockId
  deriving DecidableEq, Repr

def DeflateWitness.ownedList (dw : DeflateWitness) : List BlockId :=
  [dw.stBid, dw.winBid, dw.prevBid, dw.headBid, dw.pbufBid]

/-- Every match chain starting from `head[0..hsize-1]` within the un-overwritten window
horizon `wsize` below `bound` stays initialized, strictly decreases along `prev`, and stays `≤ bound`. -/
def ValidPrevChain (tags : TypeEnv) (m : Mem) (headBid prevBid : BlockId)
    (hsize wsize bound : Nat) : Prop :=
  (∀ i < hsize, ∃ hv : BitVec 16,
    Sem.readVal tags m headBid (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 hv) ∧
    hv.toNat ≤ bound) ∧
  (∀ p : Nat, 0 < p → p ≤ bound → bound < p + wsize →
    ((∃ i < hsize,
        Sem.readVal tags m headBid (Int64.ofNat (2 * i)) (.int .u16) =
          some (.int .u16 (BitVec.ofNat 16 p))) ∨
      (∃ q : Nat, 0 < q ∧ q ≤ bound ∧ bound < q + wsize ∧
        Sem.readVal tags m prevBid (Int64.ofNat (2 * (q % wsize))) (.int .u16) =
          some (.int .u16 (BitVec.ofNat 16 p)))) →
    ∃ pv : BitVec 16,
      Sem.readVal tags m prevBid (Int64.ofNat (2 * (p % wsize))) (.int .u16) =
        some (.int .u16 pv) ∧
      pv.toNat < p)

theorem ValidPrevChain.congr_blocks {tags : TypeEnv} {m1 m2 : Mem}
    {headBid prevBid : BlockId} {hsize wsize bound : Nat}
    (hhd : m2.blocks headBid = m1.blocks headBid)
    (hprv : m2.blocks prevBid = m1.blocks prevBid)
    (h : ValidPrevChain tags m1 headBid prevBid hsize wsize bound) :
    ValidPrevChain tags m2 headBid prevBid hsize wsize bound := by
  refine ⟨fun i hi => ?_, fun p hp0 hple hphor hreach => ?_⟩
  · rcases h.1 i hi with ⟨hv, hrv, hle⟩
    exact ⟨hv, by rw [readVal_eq_of_blocks_eq tags hhd]; exact hrv, hle⟩
  · have hreach1 : (∃ i < hsize,
        Sem.readVal tags m1 headBid (Int64.ofNat (2 * i)) (.int .u16) =
          some (.int .u16 (BitVec.ofNat 16 p))) ∨
      (∃ q : Nat, 0 < q ∧ q ≤ bound ∧ bound < q + wsize ∧
        Sem.readVal tags m1 prevBid (Int64.ofNat (2 * (q % wsize))) (.int .u16) =
          some (.int .u16 (BitVec.ofNat 16 p))) := by
      rcases hreach with ⟨i, hi, hrv⟩ | ⟨q, hq0, hqle, hqhor, hrv⟩
      · left; exact ⟨i, hi, by rw [← readVal_eq_of_blocks_eq tags hhd]; exact hrv⟩
      · right; exact ⟨q, hq0, hqle, hqhor, by rw [← readVal_eq_of_blocks_eq tags hprv]; exact hrv⟩
    rcases h.2 p hp0 hple hphor hreach1 with ⟨pv, hrv, hlt⟩
    exact ⟨pv, by rw [readVal_eq_of_blocks_eq tags hprv]; exact hrv, hlt⟩

/-- Full memory invariant for an initialized `deflate` stream at `strmPtr`.
`prev` bytes outside active chains are NOT constrained to be initialized (see `slide_hash` exception);
client-mutable `z_stream_s` fields (`next_in`, `avail_in`, `total_in`, `next_out`, `avail_out`,
`total_out`, `msg`, `data_type`, `reserved`) are NOT constrained (`adler` is initialized by
`deflateResetKeep`/`deflateCopy` and preserved by `ClientFrame`). -/
def DeflateStateInv (tags : TypeEnv) (gEnv : Env) (m : Mem)
    (strmPtr : Val) (dw : DeflateWitness) : Prop :=
  dw.ownedList.Nodup ∧
  HeapRwBlock m dw.stBid 5968 8 ∧
  readField? tags m strmPtr "z_stream_s" "state" = some (.ptr dw.stBid 0) ∧
  readField? tags m strmPtr "z_stream_s" "zalloc" = some (.fnPtr "zcalloc") ∧
  readField? tags m strmPtr "z_stream_s" "zfree" = some (.fnPtr "zcfree") ∧
  (∃ op, readField? tags m strmPtr "z_stream_s" "opaque" = some op ∧
    (op = .null ∨ ∃ ob ooff, op = .ptr ob ooff)) ∧
  (∃ ad, readNatField? tags m strmPtr "z_stream_s" "adler" = some ad) ∧
  let s : Val := .ptr dw.stBid 0
  readField? tags m s "internal_state" "strm" = some strmPtr ∧
  (∃ status, readIntField? tags m s "internal_state" "status" = some status ∧
    status ∈ ([42, 57, 69, 73, 91, 103, 113, 666] : List Int)) ∧
  (∃ wrap, readIntField? tags m s "internal_state" "wrap" = some wrap ∧ -2 ≤ wrap ∧ wrap ≤ 2) ∧
  (∃ gzhd, readField? tags m s "internal_state" "gzhead" = some gzhd ∧
    (gzhd = .null ∨ ∃ hb hoff, gzhd = .ptr hb hoff)) ∧
  (∃ gzidx method lastFlush level strategy,
    readNatField? tags m s "internal_state" "gzindex" = some gzidx ∧
    readNatField? tags m s "internal_state" "method" = some method ∧ method = 8 ∧
    readIntField? tags m s "internal_state" "last_flush" = some lastFlush ∧
    readIntField? tags m s "internal_state" "level" = some level ∧ 0 ≤ level ∧ level ≤ 9 ∧
    readIntField? tags m s "internal_state" "strategy" = some strategy ∧ 0 ≤ strategy ∧ strategy ≤ 4) ∧
  (∃ wbits wsize wmask winSize,
    readNatField? tags m s "internal_state" "w_bits" = some wbits ∧
    readNatField? tags m s "internal_state" "w_size" = some wsize ∧
    readNatField? tags m s "internal_state" "w_mask" = some wmask ∧
    readNatField? tags m s "internal_state" "window_size" = some winSize ∧
    9 ≤ wbits ∧ wbits ≤ 15 ∧ wsize = 2 ^ wbits ∧ wmask = wsize - 1 ∧ winSize = 2 * wsize ∧
    readField? tags m s "internal_state" "window" = some (.ptr dw.winBid 0) ∧
    HeapRwBlock m dw.winBid winSize 1 ∧
    readField? tags m s "internal_state" "prev" = some (.ptr dw.prevBid 0) ∧
    HeapRwBlock m dw.prevBid (2 * wsize) 2 ∧
    (∃ insH hbits hsize hmask hshift hblk,
      readNatField? tags m s "internal_state" "ins_h" = some insH ∧
      readNatField? tags m s "internal_state" "hash_bits" = some hbits ∧
      readNatField? tags m s "internal_state" "hash_size" = some hsize ∧
      readNatField? tags m s "internal_state" "hash_mask" = some hmask ∧
      readNatField? tags m s "internal_state" "hash_shift" = some hshift ∧
      8 ≤ hbits ∧ hbits ≤ 16 ∧ hsize = 2 ^ hbits ∧ hmask = hsize - 1 ∧
      1 ≤ hshift ∧ hshift ≤ hbits ∧ insH < hsize ∧
      readField? tags m s "internal_state" "head" = some (.ptr dw.headBid 0) ∧
      m.blocks dw.headBid = some hblk ∧ hblk.kind = .heap ∧ hblk.perm = .rw ∧
      2 * hsize ≤ hblk.size ∧ 2 ≤ hblk.align ∧
      (∀ i < hsize, ∃ hv : BitVec 16,
        Sem.readVal tags m dw.headBid (Int64.ofNat (2 * i)) (.int .u16) = some (.int .u16 hv))) ∧
    (∃ blockStart matchLen prevMatch matchAvail strstart matchStart lookahead prevLen
        maxChain maxLazy goodMatch niceMatch insert slid highWater wblk,
      readIntField? tags m s "internal_state" "block_start" = some blockStart ∧
      readNatField? tags m s "internal_state" "match_length" = some matchLen ∧
      readNatField? tags m s "internal_state" "prev_match" = some prevMatch ∧
      readIntField? tags m s "internal_state" "match_available" = some matchAvail ∧
      readNatField? tags m s "internal_state" "strstart" = some strstart ∧
      readNatField? tags m s "internal_state" "match_start" = some matchStart ∧
      readNatField? tags m s "internal_state" "lookahead" = some lookahead ∧
      readNatField? tags m s "internal_state" "prev_length" = some prevLen ∧
      readNatField? tags m s "internal_state" "max_chain_length" = some maxChain ∧
      readNatField? tags m s "internal_state" "max_lazy_match" = some maxLazy ∧
      readNatField? tags m s "internal_state" "good_match" = some goodMatch ∧
      readIntField? tags m s "internal_state" "nice_match" = some niceMatch ∧
      readNatField? tags m s "internal_state" "insert" = some insert ∧
      readIntField? tags m s "internal_state" "slid" = some slid ∧
      readNatField? tags m s "internal_state" "high_water" = some highWater ∧
      insert ≤ strstart ∧ strstart + lookahead ≤ winSize ∧ highWater ≤ winSize ∧
      strstart + lookahead ≤ highWater ∧
      -((winSize : Int)) ≤ blockStart ∧ blockStart ≤ (strstart : Int) ∧
      (matchAvail = 0 ∨ matchAvail = 1) ∧ (matchAvail = 1 → 1 ≤ strstart) ∧
      prevLen ≤ 258 ∧ matchLen ≤ 258 ∧ (slid = 0 ∨ slid = 1) ∧
      (matchAvail = 1 ∧ 3 ≤ matchLen →
        let d := (BitVec.ofNat 32 strstart - 1#32 - BitVec.ofNat 32 matchStart).toNat
        1 ≤ d ∧ d ≤ wsize - 262) ∧
      m.blocks dw.winBid = some wblk ∧
      ∀ j < highWater, ∃ u : UInt8, wblk.bytes j = .byte u)) ∧
  (∃ litBuf pbufSize pOutOff pending symNext symEnd optLen staticLen matches_ biBuf biValid biUsed pblk,
    readNatField? tags m s "internal_state" "lit_bufsize" = some litBuf ∧
    readNatField? tags m s "internal_state" "pending_buf_size" = some pbufSize ∧
    readField? tags m s "internal_state" "pending_buf" = some (.ptr dw.pbufBid 0) ∧
    readField? tags m s "internal_state" "pending_out" = some (.ptr dw.pbufBid (Int64.ofNat pOutOff)) ∧
    readNatField? tags m s "internal_state" "pending" = some pending ∧
    readField? tags m s "internal_state" "sym_buf" = some (.ptr dw.pbufBid (Int64.ofNat litBuf)) ∧
    readNatField? tags m s "internal_state" "sym_next" = some symNext ∧
    readNatField? tags m s "internal_state" "sym_end" = some symEnd ∧
    readNatField? tags m s "internal_state" "opt_len" = some optLen ∧
    readNatField? tags m s "internal_state" "static_len" = some staticLen ∧
    readNatField? tags m s "internal_state" "matches" = some matches_ ∧
    readNatField? tags m s "internal_state" "bi_buf" = some biBuf ∧
    readIntField? tags m s "internal_state" "bi_valid" = some biValid ∧
    readIntField? tags m s "internal_state" "bi_used" = some biUsed ∧
    128 ≤ litBuf ∧ litBuf ≤ 32768 ∧
    pbufSize = 4 * litBuf ∧ symEnd = (litBuf - 1) * 3 ∧ symNext ≤ symEnd ∧
    pOutOff + pending ≤ pbufSize ∧ 0 ≤ biValid ∧ biValid ≤ 16 ∧
    m.blocks dw.pbufBid = some pblk ∧ pblk.kind = .heap ∧ pblk.perm = .rw ∧
    pbufSize ≤ pblk.size ∧ 1 ≤ pblk.align ∧
    (∀ j < pending, ∃ u : UInt8, pblk.bytes (pOutOff + j) = .byte u) ∧
    (∀ j < symNext, ∃ u : UInt8, pblk.bytes (litBuf + j) = .byte u)) ∧
  (∃ b_sld b_sdd b_sbld,
    gEnv.lookup "static_l_desc" = some (b_sld, staticTreeDescConstTy) ∧
    gEnv.lookup "static_d_desc" = some (b_sdd, staticTreeDescConstTy) ∧
    gEnv.lookup "static_bl_desc" = some (b_sbld, staticTreeDescConstTy) ∧
    Sem.readVal tags m dw.stBid 2904 (.ptr ctDataCTy) = some (.ptr dw.stBid 212) ∧
    Sem.readVal tags m dw.stBid 2920 (.ptr (.const_ (.typedef "static_tree_desc" (.structTy "static_tree_desc_s")))) =
      some (.ptr b_sld 0) ∧
    Sem.readVal tags m dw.stBid 2928 (.ptr ctDataCTy) = some (.ptr dw.stBid 2504) ∧
    Sem.readVal tags m dw.stBid 2944 (.ptr (.const_ (.typedef "static_tree_desc" (.structTy "static_tree_desc_s")))) =
      some (.ptr b_sdd 0) ∧
    Sem.readVal tags m dw.stBid 2952 (.ptr ctDataCTy) = some (.ptr dw.stBid 2748) ∧
    Sem.readVal tags m dw.stBid 2968 (.ptr (.const_ (.typedef "static_tree_desc" (.structTy "static_tree_desc_s")))) =
      some (.ptr b_sbld 0)) ∧
  (∃ lmc dmc blmc heapLen heapMax,
    Sem.readVal tags m dw.stBid 2912 (.int .i32) = some (.int .i32 lmc) ∧
    Sem.readVal tags m dw.stBid 2936 (.int .i32) = some (.int .i32 dmc) ∧
    Sem.readVal tags m dw.stBid 2960 (.int .i32) = some (.int .i32 blmc) ∧
    readIntField? tags m s "internal_state" "heap_len" = some heapLen ∧
    readIntField? tags m s "internal_state" "heap_max" = some heapMax ∧
    0 ≤ heapLen ∧ heapLen ≤ 572 ∧ 0 ≤ heapMax ∧ heapMax ≤ 573) ∧
  (∀ i < 573, ∃ fc dl : BitVec 16,
    Sem.readVal tags m dw.stBid (Int64.ofNat (212 + 4 * i)) (.int .u16) = some (.int .u16 fc) ∧
    Sem.readVal tags m dw.stBid (Int64.ofNat (212 + 4 * i + 2)) (.int .u16) = some (.int .u16 dl)) ∧
  (∀ i < 61, ∃ fc dl : BitVec 16,
    Sem.readVal tags m dw.stBid (Int64.ofNat (2504 + 4 * i)) (.int .u16) = some (.int .u16 fc) ∧
    Sem.readVal tags m dw.stBid (Int64.ofNat (2504 + 4 * i + 2)) (.int .u16) = some (.int .u16 dl)) ∧
  (∀ i < 39, ∃ fc dl : BitVec 16,
    Sem.readVal tags m dw.stBid (Int64.ofNat (2748 + 4 * i)) (.int .u16) = some (.int .u16 fc) ∧
    Sem.readVal tags m dw.stBid (Int64.ofNat (2748 + 4 * i + 2)) (.int .u16) = some (.int .u16 dl)) ∧
  (∀ i < 16, ∃ bv : BitVec 16,
    Sem.readVal tags m dw.stBid (Int64.ofNat (2976 + 2 * i)) (.int .u16) = some (.int .u16 bv)) ∧
  (∀ i < 573, ∃ bv : BitVec 8,
    Sem.readVal tags m dw.stBid (Int64.ofNat (5308 + i)) (.int .u8) = some (.int .u8 bv)) ∧
  (∀ level matches_ blockStart wsize hsize strstart,
    readIntField? tags m s "internal_state" "level" = some level →
    readNatField? tags m s "internal_state" "matches" = some matches_ →
    readIntField? tags m s "internal_state" "block_start" = some blockStart →
    readNatField? tags m s "internal_state" "w_size" = some wsize →
    readNatField? tags m s "internal_state" "hash_size" = some hsize →
    readNatField? tags m s "internal_state" "strstart" = some strstart →
    (level ≠ 0 → matches_ = 0) ∧
    (level = 0 → 0 ≤ blockStart) ∧
    ((level ≠ 0 ∨ matches_ = 0) →
      ValidPrevChain tags m dw.headBid dw.prevBid hsize wsize strstart) ∧
    (level = 0 ∧ matches_ = 1 →
      ∃ hBound, hBound ≤ strstart + wsize ∧ hBound < 2 * wsize ∧
        ValidPrevChain tags m dw.headBid dw.prevBid hsize wsize hBound))

/-- Client-mutable scalar fields on `z_stream_s` initialized by `inflate` (`total_in`, `total_out`,
`data_type`, and `adler` whenever `wrap ≠ 0`). -/
def InflateAccumulatorsInit (tags : TypeEnv) (m : Mem) (strmPtr : Val) (wrap : Int) : Prop :=
  (∃ tin, readNatField? tags m strmPtr "z_stream_s" "total_in" = some tin) ∧
  (∃ tout, readNatField? tags m strmPtr "z_stream_s" "total_out" = some tout) ∧
  (wrap = 0 ∨ ∃ ad, readNatField? tags m strmPtr "z_stream_s" "adler" = some ad) ∧
  (∃ dt, readIntField? tags m strmPtr "z_stream_s" "data_type" = some dt)

theorem InflateAccumulatorsInit.congr_block {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId}
    {off : Int64} {wrap : Int} (heq : m2.blocks b = m1.blocks b)
    (h : InflateAccumulatorsInit tags m1 (.ptr b off) wrap) :
    InflateAccumulatorsInit tags m2 (.ptr b off) wrap := by
  rcases h with ⟨⟨a, ha⟩, ⟨b', hb'⟩, h3, ⟨d, hd⟩⟩
  refine ⟨⟨a, by rw [readNatField?_congr_block tags heq]; exact ha⟩,
    ⟨b', by rw [readNatField?_congr_block tags heq]; exact hb'⟩,
    h3.elim Or.inl (fun ⟨c, hc⟩ => Or.inr ⟨c, by rw [readNatField?_congr_block tags heq]; exact hc⟩),
    ⟨d, by rw [readIntField?_congr_block tags heq]; exact hd⟩⟩

/-- Client-mutable scalar accumulator fields on `z_stream_s` (`total_in`, `total_out`,
`adler`, `data_type`) required initialized on internal/owned stream calls (`compress`,
`uncompress`, `gzread`, `gzwrite`, `_tr_flush_block`). -/
def StreamAccumulatorsInit (tags : TypeEnv) (m : Mem) (strmPtr : Val) : Prop :=
  (∃ tin, readNatField? tags m strmPtr "z_stream_s" "total_in" = some tin) ∧
  (∃ tout, readNatField? tags m strmPtr "z_stream_s" "total_out" = some tout) ∧
  (∃ ad, readNatField? tags m strmPtr "z_stream_s" "adler" = some ad) ∧
  (∃ dt, readIntField? tags m strmPtr "z_stream_s" "data_type" = some dt)

theorem StreamAccumulatorsInit.to_inflateAccumulators {tags : TypeEnv} {m : Mem} {strmPtr : Val}
    (wrap : Int) (h : StreamAccumulatorsInit tags m strmPtr) :
    InflateAccumulatorsInit tags m strmPtr wrap :=
  ⟨h.1, h.2.1, Or.inr h.2.2.1, h.2.2.2⟩

theorem StreamAccumulatorsInit.congr_block {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    (heq : m2.blocks b = m1.blocks b) (h : StreamAccumulatorsInit tags m1 (.ptr b off)) :
    StreamAccumulatorsInit tags m2 (.ptr b off) := by
  rcases h with ⟨⟨a, ha⟩, ⟨b', hb'⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
  exact ⟨⟨a, by rw [readNatField?_congr_block tags heq]; exact ha⟩,
    ⟨b', by rw [readNatField?_congr_block tags heq]; exact hb'⟩,
    ⟨c, by rw [readNatField?_congr_block tags heq]; exact hc⟩,
    ⟨d, by rw [readIntField?_congr_block tags heq]; exact hd⟩⟩

private theorem readNatField?_some_blk {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {st fld : String} {n : Nat} (h : readNatField? tags m (.ptr b off) st fld = some n) :
    ∃ blk, m.blocks b = some blk := by
  by_cases hnone : m.blocks b = none
  · exfalso
    unfold readNatField? readField? at h
    dsimp only [bind, Option.bind] at h
    cases hfl : fieldLayout? tags (.structTy st) fld with
    | none => rw [hfl] at h; cases h
    | some p =>
      rw [hfl] at h
      dsimp only at h
      unfold Sem.readVal Mem.readBytes at h
      rw [hnone] at h
      dsimp only [bind, Option.bind] at h
      cases hty : p.snd.unqual <;> simp [hty, CTy.intKind?, CTy.unqual] at h
  · cases hb : m.blocks b with
    | none => contradiction
    | some blk => exact ⟨blk, rfl⟩

theorem StreamAccumulatorsInit.roExt {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    (hro : C99.Proof.ROExt m1 m2) (h : StreamAccumulatorsInit tags m1 (.ptr b off)) :
    StreamAccumulatorsInit tags m2 (.ptr b off) := by
  rcases h with ⟨⟨tin, htin⟩, ⟨tout, htout⟩, ⟨ad, had⟩, ⟨dt, hdt⟩⟩
  obtain ⟨blk, hb⟩ := readNatField?_some_blk htin
  exact StreamAccumulatorsInit.congr_block (hro.2.1 b (mem_lt_nextBlock hb)) ⟨⟨tin, htin⟩, ⟨tout, htout⟩, ⟨ad, had⟩, ⟨dt, hdt⟩⟩

theorem InflateStateInv.congr_blocks {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {strmPtr : Val} {iw : InflateWitness} {sb : BlockId} {soff : Int64}
    (hptr : strmPtr = .ptr sb soff)
    (hpres : ∀ b, b ∈ iw.ownedList → m2.blocks b = m1.blocks b)
    (hsa : readField? tags m2 strmPtr "z_stream_s" "state" = readField? tags m1 strmPtr "z_stream_s" "state" ∧
           readField? tags m2 strmPtr "z_stream_s" "zalloc" = readField? tags m1 strmPtr "z_stream_s" "zalloc" ∧
           readField? tags m2 strmPtr "z_stream_s" "zfree" = readField? tags m1 strmPtr "z_stream_s" "zfree" ∧
           readField? tags m2 strmPtr "z_stream_s" "opaque" = readField? tags m1 strmPtr "z_stream_s" "opaque")
    (hroG : ∀ b blk, m1.blocks b = some blk → blk.kind = .global → blk.perm = .ro → m2.blocks b = m1.blocks b)
    (h : InflateStateInv tags gEnv m1 strmPtr iw) :
    InflateStateInv tags gEnv m2 strmPtr iw := by
  subst hptr
  have hst : m2.blocks iw.stBid = m1.blocks iw.stBid := hpres iw.stBid (by simp [InflateWitness.ownedList])
  rcases h with ⟨hh, hdisj, hs_st, hs_za, hs_zf, hs_op, hstrm, hmode, hlast, hwrap, hreqw,
    hhd, hfl, hdm, hck, htot, hhead, hwin, hsc, hnext, hcodes, hmodes⟩
  refine ⟨hh.congr_blocks hst, hdisj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsa.1]; exact hs_st
  · rw [hsa.2.1]; exact hs_za
  · rw [hsa.2.2.1]; exact hs_zf
  · rw [hsa.2.2.2]; exact hs_op
  · rw [readField?_congr_block tags hst]; exact hstrm
  · simpa [readNatField?_congr_block tags hst] using hmode
  · simpa [readIntField?_congr_block tags hst] using hlast
  · simpa [readIntField?_congr_block tags hst] using hwrap
  · simpa [readIntField?_congr_block tags hst] using hreqw
  · simpa [readIntField?_congr_block tags hst] using hhd
  · simpa [readIntField?_congr_block tags hst] using hfl
  · simpa [readNatField?_congr_block tags hst] using hdm
  · simpa [readNatField?_congr_block tags hst] using hck
  · simpa [readNatField?_congr_block tags hst] using htot
  · simpa [readField?_congr_block tags hst] using hhead
  · rcases hwin with ⟨rb, wb, ws, wh, wn, wr, rwr, md,
      hrb, hwb, hws, hwh, hwn, hwr, hrwr, hmd, hrb_b, hwb_b, hrw_b, hw_b, hm_b, hmatch⟩
    refine ⟨rb, wb, ws, wh, wn, wr, rwr, md,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrb_b, hwb_b, hrw_b, hw_b, hm_b, ?_⟩
    · rw [readNatField?_congr_block tags hst]; exact hrb
    · rw [readNatField?_congr_block tags hst]; exact hwb
    · rw [readNatField?_congr_block tags hst]; exact hws
    · rw [readNatField?_congr_block tags hst]; exact hwh
    · rw [readNatField?_congr_block tags hst]; exact hwn
    · rw [readIntField?_congr_block tags hst]; exact hwr
    · rw [readIntField?_congr_block tags hst]; exact hrwr
    · rw [readNatField?_congr_block tags hst]; exact hmd
    · cases hw_eq : iw.win? with
      | none =>
        rw [hw_eq] at hmatch
        simpa [hw_eq, readField?_congr_block tags hst] using hmatch
      | some winb =>
        rw [hw_eq] at hmatch
        have hwin_blk : m2.blocks winb = m1.blocks winb :=
          hpres winb (by simp [InflateWitness.ownedList, hw_eq])
        rcases hmatch with ⟨h1, h2, hwf, wblk, hmb, rest⟩
        refine ⟨h1, h2, ?_, wblk, hwin_blk ▸ hmb, rest⟩
        rw [readField?_congr_block tags hst]; exact hwf
  · rcases hsc with ⟨ho, bi, le, off, ex, lb, db, nc, nl, nd, hv, sn, bk, ws,
      h1, h2, h2b, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h12b, h13, h13b, h13c, h14⟩
    refine ⟨ho, bi, le, off, ex, lb, db, nc, nl, nd, hv, sn, bk, ws, ?_⟩
    simp only [readNatField?_congr_block tags hst, readIntField?_congr_block tags hst]
    exact ⟨h1, h2, h2b, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h12b, h13, h13b, h13c, h14⟩
  · simpa [readField?_congr_block tags hst] using hnext
  · rcases hcodes with ⟨lc, dc, hlc, hdc, hcds⟩
    refine ⟨lc, dc, ?_, ?_, ?_⟩
    · rw [readField?_congr_block tags hst]; exact hlc
    · rw [readField?_congr_block tags hst]; exact hdc
    · rcases hcds with ⟨rfl, doff, rfl, hdoff⟩ |
        ⟨b_lf, blk_lf, b_df, blk_df, hlu_lf, hm_lf, hk_lf, hp_lf, rfl, hlu_df, hm_df, hk_df, hp_df, rfl⟩
      · exact Or.inl ⟨rfl, doff, rfl, hdoff⟩
      · exact Or.inr ⟨b_lf, blk_lf, b_df, blk_df, hlu_lf,
          (hroG b_lf blk_lf hm_lf hk_lf hp_lf).symm ▸ hm_lf, hk_lf, hp_lf, rfl, hlu_df,
          (hroG b_df blk_df hm_df hk_df hp_df).symm ▸ hm_df, hk_df, hp_df, rfl⟩
  · intro mode hmd
    rw [readNatField?_congr_block tags hst] at hmd
    obtain ⟨hm1, hm2, hm3⟩ := hmodes mode hmd
    refine ⟨?_, ?_, ?_⟩
    · intro hm
      rcases hm1 hm with ⟨nc, nl, nd, hv, h1, h2, h3, h4, b1, b2, b3, b4, b5, b6, hord⟩
      refine ⟨nc, nl, nd, hv, ?_, ?_, ?_, ?_, b1, b2, b3, b4, b5, b6, ?_⟩
      · rw [readNatField?_congr_block tags hst]; exact h1
      · rw [readNatField?_congr_block tags hst]; exact h2
      · rw [readNatField?_congr_block tags hst]; exact h3
      · rw [readNatField?_congr_block tags hst]; exact h4
      · intro j hj
        rcases hord j hj with ⟨v, hrv, hvle⟩
        exact ⟨v, by rw [readVal_eq_of_blocks_eq tags hst]; exact hrv, hvle⟩
    · intro hm
      rcases hm2 hm with ⟨nl, nd, hv, lb, cnt, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, htab, hcnt, hlens⟩
      refine ⟨nl, nd, hv, lb, cnt, ?_, ?_, ?_, ?_, h5, h6, h7, h8, h9, h10, ?_, hcnt, ?_⟩
      · rw [readNatField?_congr_block tags hst]; exact h1
      · rw [readNatField?_congr_block tags hst]; exact h2
      · rw [readNatField?_congr_block tags hst]; exact h3
      · rw [readNatField?_congr_block tags hst]; exact h4
      · exact htab.congr_block rfl hst
      · intro i hi
        rcases hlens i hi with ⟨v, hrv, hle⟩
        exact ⟨v, by rw [readVal_eq_of_blocks_eq tags hst]; exact hrv, hle⟩
    · intro hm
      rcases hm3 hm with ⟨lc, dc, lb, db, len_, off_, ex, ws,
        h1, h2, h3, h4, h5, h6, h7, h8, hlb, hdb, ⟨lcnt, hlct, hlptr⟩, ⟨dcnt, hdct⟩, pm1, pm2, pm3, pm4⟩
      refine ⟨lc, dc, lb, db, len_, off_, ex, ws,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlb, hdb, ?_, ?_, pm1, pm2, pm3, pm4⟩
      · rw [readField?_congr_block tags hst]; exact h1
      · rw [readField?_congr_block tags hst]; exact h2
      · rw [readNatField?_congr_block tags hst]; exact h3
      · rw [readNatField?_congr_block tags hst]; exact h4
      · rw [readNatField?_congr_block tags hst]; exact h5
      · rw [readNatField?_congr_block tags hst]; exact h6
      · rw [readNatField?_congr_block tags hst]; exact h7
      · rw [readNatField?_congr_block tags hst]; exact h8
      · refine ⟨lcnt, ?_, hlptr⟩
        rcases hcodes with ⟨lc', _, hlc', _, hcds⟩
        rw [hlc'] at h1; cases h1
        rcases hcds with ⟨rfl, _⟩ | ⟨b_lf, blk_lf, _, _, _, hm_lf, hk_lf, hp_lf, rfl, _⟩
        · exact hlct.congr_block rfl hst
        · exact hlct.congr_block rfl (hroG b_lf blk_lf hm_lf hk_lf hp_lf)
      · refine ⟨dcnt, ?_⟩
        rcases hcodes with ⟨_, dc', _, hdc', hcds⟩
        rw [hdc'] at h2; cases h2
        rcases hcds with ⟨_, doff, rfl, _⟩ | ⟨_, _, b_df, blk_df, _, _, _, _, _, _, hm_df, hk_df, hp_df, rfl⟩
        · exact hdct.congr_block rfl hst
        · exact hdct.congr_block rfl (hroG b_df blk_df hm_df hk_df hp_df)

theorem InflateStateInv.roExt {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {strmPtr : Val} {iw : InflateWitness} {sb : BlockId} {soff : Int64}
    (hptr : strmPtr = .ptr sb soff)
    (hsblk : (m1.blocks sb).isSome = true)
    (hro : C99.Proof.ROExt m1 m2)
    (h : InflateStateInv tags gEnv m1 strmPtr iw) :
    InflateStateInv tags gEnv m2 strmPtr iw := by
  subst hptr
  rcases Option.isSome_iff_exists.mp hsblk with ⟨sblk, hsblk'⟩
  have hsb_eq : m2.blocks sb = m1.blocks sb := hro.2.1 sb (mem_lt_nextBlock hsblk')
  refine InflateStateInv.congr_blocks rfl ?_ ?_ ?_ h
  · intro b hb
    simp only [InflateWitness.ownedList, List.mem_cons] at hb
    rcases hb with rfl | hmem
    · rcases h.1 with ⟨stblk, hstb, _⟩
      exact hro.2.1 iw.stBid (mem_lt_nextBlock hstb)
    · cases hw : iw.win? with
      | none => simp [hw] at hmem
      | some wb =>
        rw [hw] at hmem
        simp only [Option.toList_some, List.mem_singleton] at hmem
        subst hmem
        rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwin, _⟩
        rcases hwin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmatch⟩
        rw [hw] at hmatch
        rcases hmatch with ⟨_, _, _, wblk, hmwb, _⟩
        exact hro.2.1 b (mem_lt_nextBlock hmwb)
  · exact ⟨readField?_congr_block tags hsb_eq, readField?_congr_block tags hsb_eq,
      readField?_congr_block tags hsb_eq, readField?_congr_block tags hsb_eq⟩
  · intro b blk hmb _ _; exact hro.2.1 b (mem_lt_nextBlock hmb)

theorem InflateBackInv.congr_blocks {tags : TypeEnv}
    {m1 m2 : Mem} {strmPtr : Val} {ibw : InflateBackWitness}
    (hst : m2.blocks ibw.stBid = m1.blocks ibw.stBid)
    (hwin : Writable m2 (.ptr ibw.winBid ibw.winOff) (2 ^ ibw.wbits))
    (hsa : readField? tags m2 strmPtr "z_stream_s" "state" = readField? tags m1 strmPtr "z_stream_s" "state" ∧
           readField? tags m2 strmPtr "z_stream_s" "zalloc" = readField? tags m1 strmPtr "z_stream_s" "zalloc" ∧
           readField? tags m2 strmPtr "z_stream_s" "zfree" = readField? tags m1 strmPtr "z_stream_s" "zfree" ∧
           readField? tags m2 strmPtr "z_stream_s" "opaque" = readField? tags m1 strmPtr "z_stream_s" "opaque")
    (h : InflateBackInv tags m1 strmPtr ibw) :
    InflateBackInv tags m2 strmPtr ibw := by
  rcases h with ⟨hh, hne1, hne2, hwb1, hwb2, _, hs1, hs2, hs3, hs4, hw, hwb, hws, hwn, ⟨wh, hwh, hwhle⟩, hsn, hdm⟩
  refine ⟨hh.congr_blocks hst, hne1, hne2, hwb1, hwb2, hwin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨wh, ?_, hwhle⟩, ?_, ?_⟩
  · rw [hsa.1]; exact hs1
  · rw [hsa.2.1]; exact hs2
  · rw [hsa.2.2.1]; exact hs3
  · rw [hsa.2.2.2]; exact hs4
  · rw [readField?_congr_block tags hst]; exact hw
  · rw [readNatField?_congr_block tags hst]; exact hwb
  · rw [readNatField?_congr_block tags hst]; exact hws
  · rw [readNatField?_congr_block tags hst]; exact hwn
  · rw [readNatField?_congr_block tags hst]; exact hwh
  · rw [readNatField?_congr_block tags hst]; exact hsn
  · rw [readNatField?_congr_block tags hst]; exact hdm

theorem InflateBackInv.roExt {tags : TypeEnv}
    {m1 m2 : Mem} {strmPtr : Val} {ibw : InflateBackWitness} {sb : BlockId} {soff : Int64}
    (hptr : strmPtr = .ptr sb soff) (hsblk : (m1.blocks sb).isSome = true)
    (hro : C99.Proof.ROExt m1 m2) (h : InflateBackInv tags m1 strmPtr ibw) :
    InflateBackInv tags m2 strmPtr ibw := by
  subst hptr
  rcases Option.isSome_iff_exists.mp hsblk with ⟨sblk, hsblk'⟩
  have hsb_eq : m2.blocks sb = m1.blocks sb := hro.2.1 sb (mem_lt_nextBlock hsblk')
  rcases h.1 with ⟨stblk, hstb, _⟩
  exact InflateBackInv.congr_blocks (hro.2.1 ibw.stBid (mem_lt_nextBlock hstb))
    (writable_roExt hro h.2.2.2.2.2.1)
    ⟨readField?_congr_block tags hsb_eq, readField?_congr_block tags hsb_eq,
      readField?_congr_block tags hsb_eq, readField?_congr_block tags hsb_eq⟩ h

theorem DeflateStateInv.congr_blocks {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {strmPtr : Val} {dw : DeflateWitness}
    (hpres : ∀ b, b ∈ dw.ownedList → m2.blocks b = m1.blocks b)
    (hsa : readField? tags m2 strmPtr "z_stream_s" "state" = readField? tags m1 strmPtr "z_stream_s" "state" ∧
           readField? tags m2 strmPtr "z_stream_s" "zalloc" = readField? tags m1 strmPtr "z_stream_s" "zalloc" ∧
           readField? tags m2 strmPtr "z_stream_s" "zfree" = readField? tags m1 strmPtr "z_stream_s" "zfree" ∧
           readField? tags m2 strmPtr "z_stream_s" "opaque" = readField? tags m1 strmPtr "z_stream_s" "opaque" ∧
           readField? tags m2 strmPtr "z_stream_s" "adler" = readField? tags m1 strmPtr "z_stream_s" "adler")
    (h : DeflateStateInv tags gEnv m1 strmPtr dw) :
    DeflateStateInv tags gEnv m2 strmPtr dw := by
  have hst : m2.blocks dw.stBid = m1.blocks dw.stBid := hpres dw.stBid (by simp [DeflateWitness.ownedList])
  have hwin : m2.blocks dw.winBid = m1.blocks dw.winBid := hpres dw.winBid (by simp [DeflateWitness.ownedList])
  have hprv : m2.blocks dw.prevBid = m1.blocks dw.prevBid := hpres dw.prevBid (by simp [DeflateWitness.ownedList])
  have hhd : m2.blocks dw.headBid = m1.blocks dw.headBid := hpres dw.headBid (by simp [DeflateWitness.ownedList])
  have hpbf : m2.blocks dw.pbufBid = m1.blocks dw.pbufBid := hpres dw.pbufBid (by simp [DeflateWitness.ownedList])
  rcases h with ⟨hnodup, hh, hs_st, hs_za, hs_zf, hs_op, ⟨ad, had⟩, hstrm, hstatus, hwrap, hgzhd, hsc,
    hwinf, hpbuf, hdescs, htrees, hlt, hdt, hblt, hblc, hdep, hchain⟩
  refine ⟨hnodup, hh.congr_blocks hst, ?_, ?_, ?_, ?_, ⟨ad, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsa.1]; exact hs_st
  · rw [hsa.2.1]; exact hs_za
  · rw [hsa.2.2.1]; exact hs_zf
  · rw [hsa.2.2.2.1]; exact hs_op
  · unfold readNatField? at had ⊢; rw [hsa.2.2.2.2]; exact had
  · rw [readField?_congr_block tags hst]; exact hstrm
  · simpa [readIntField?_congr_block tags hst] using hstatus
  · simpa [readIntField?_congr_block tags hst] using hwrap
  · simpa [readField?_congr_block tags hst] using hgzhd
  · rcases hsc with ⟨a1, a2, a3, a4, a5, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩
    refine ⟨a1, a2, a3, a4, a5, ?_, ?_, r3, ?_, ?_, r6, r7, ?_, r9⟩ <;>
      simp only [readNatField?_congr_block tags hst, readIntField?_congr_block tags hst] <;>
      assumption
  · rcases hwinf with ⟨wb, ws, wm, wz, h1, h2, h3, h4, b1, b2, b3, b4, b5, hw_ptr, hw_blk, hp_ptr, hp_blk, hhash, hpos⟩
    refine ⟨wb, ws, wm, wz, ?_, ?_, ?_, ?_, b1, b2, b3, b4, b5, ?_, hw_blk.congr_blocks hwin,
      ?_, hp_blk.congr_blocks hprv, ?_, ?_⟩
    · rw [readNatField?_congr_block tags hst]; exact h1
    · rw [readNatField?_congr_block tags hst]; exact h2
    · rw [readNatField?_congr_block tags hst]; exact h3
    · rw [readNatField?_congr_block tags hst]; exact h4
    · rw [readField?_congr_block tags hst]; exact hw_ptr
    · rw [readField?_congr_block tags hst]; exact hp_ptr
    · rcases hhash with ⟨ih, hb, hs, hm, hsh, hbl, f1, f2, f3, f4, f5, g1, g2, g3, g4, g5, g6, g7, f13, f14, f15, f16, f17, f18, f19⟩
      refine ⟨ih, hb, hs, hm, hsh, hbl, ?_, ?_, ?_, ?_, ?_, g1, g2, g3, g4, g5, g6, g7, ?_, hhd ▸ f14, f15, f16, f17, f18, ?_⟩
      · rw [readNatField?_congr_block tags hst]; exact f1
      · rw [readNatField?_congr_block tags hst]; exact f2
      · rw [readNatField?_congr_block tags hst]; exact f3
      · rw [readNatField?_congr_block tags hst]; exact f4
      · rw [readNatField?_congr_block tags hst]; exact f5
      · rw [readField?_congr_block tags hst]; exact f13
      · intro i hi
        rcases f19 i hi with ⟨hv, hrv⟩
        exact ⟨hv, by rw [readVal_eq_of_blocks_eq tags hhd]; exact hrv⟩
    · rcases hpos with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, wbl,
        q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15,
        c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, qblk, qbytes⟩
      refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, wbl,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, hwin ▸ qblk, qbytes⟩ <;>
        simp only [readNatField?_congr_block tags hst, readIntField?_congr_block tags hst] <;>
        assumption
  · rcases hpbuf with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14,
      c1, c2, c3, c4, c5, c6, c7, c8, qblk, qkind, qperm, qsz, qal, qb1, qb2⟩
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      c1, c2, c3, c4, c5, c6, c7, c8, hpbf ▸ qblk, qkind, qperm, qsz, qal, qb1, qb2⟩ <;>
      simp only [readField?_congr_block tags hst, readNatField?_congr_block tags hst, readIntField?_congr_block tags hst] <;>
      assumption
  · rcases hdescs with ⟨b1, b2, b3, l1, l2, l3, r1, r2, r3, r4, r5, r6⟩
    refine ⟨b1, b2, b3, l1, l2, l3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [readVal_eq_of_blocks_eq tags hst] <;>
      assumption
  · rcases htrees with ⟨a1, a2, a3, a4, a5, r1, r2, r3, r4, r5, c1, c2, c3, c4⟩
    refine ⟨a1, a2, a3, a4, a5, ?_, ?_, ?_, ?_, ?_, c1, c2, c3, c4⟩ <;>
      simp only [readVal_eq_of_blocks_eq tags hst, readIntField?_congr_block tags hst] <;>
      assumption
  · intro i hi; rcases hlt i hi with ⟨fc, dl, h1, h2⟩
    exact ⟨fc, dl, by rw [readVal_eq_of_blocks_eq tags hst]; exact h1, by rw [readVal_eq_of_blocks_eq tags hst]; exact h2⟩
  · intro i hi; rcases hdt i hi with ⟨fc, dl, h1, h2⟩
    exact ⟨fc, dl, by rw [readVal_eq_of_blocks_eq tags hst]; exact h1, by rw [readVal_eq_of_blocks_eq tags hst]; exact h2⟩
  · intro i hi; rcases hblt i hi with ⟨fc, dl, h1, h2⟩
    exact ⟨fc, dl, by rw [readVal_eq_of_blocks_eq tags hst]; exact h1, by rw [readVal_eq_of_blocks_eq tags hst]; exact h2⟩
  · intro i hi; rcases hblc i hi with ⟨bv, h1⟩
    exact ⟨bv, by rw [readVal_eq_of_blocks_eq tags hst]; exact h1⟩
  · intro i hi; rcases hdep i hi with ⟨bv, h1⟩
    exact ⟨bv, by rw [readVal_eq_of_blocks_eq tags hst]; exact h1⟩
  · intro lvl mt bks ws hs str h1 h2 h3 h4 h5 h6
    simp only [readIntField?_congr_block tags hst, readNatField?_congr_block tags hst] at h1 h2 h3 h4 h5 h6
    obtain ⟨hc1, hc2, hc3, hc4⟩ := hchain lvl mt bks ws hs str h1 h2 h3 h4 h5 h6
    refine ⟨hc1, hc2, fun ho => (hc3 ho).congr_blocks hhd hprv, fun ha => ?_⟩
    obtain ⟨hbnd, hb1, hb2, hvc⟩ := hc4 ha
    exact ⟨hbnd, hb1, hb2, hvc.congr_blocks hhd hprv⟩

theorem DeflateStateInv.roExt {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {strmPtr : Val} {dw : DeflateWitness} {sb : BlockId} {soff : Int64}
    (hptr : strmPtr = .ptr sb soff) (hsblk : (m1.blocks sb).isSome = true)
    (hro : C99.Proof.ROExt m1 m2) (h : DeflateStateInv tags gEnv m1 strmPtr dw) :
    DeflateStateInv tags gEnv m2 strmPtr dw := by
  subst hptr
  rcases Option.isSome_iff_exists.mp hsblk with ⟨sblk, hsblk'⟩
  have hsb_eq : m2.blocks sb = m1.blocks sb := hro.2.1 sb (mem_lt_nextBlock hsblk')
  refine DeflateStateInv.congr_blocks ?_ ?_ h
  · intro b hb
    rcases h with ⟨_, hst, _, _, _, _, _, _, _, _, _, _, hwinf, hpbuf, _⟩
    simp only [DeflateWitness.ownedList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · rcases hst with ⟨blk, hmb, _⟩; exact hro.2.1 dw.stBid (mem_lt_nextBlock hmb)
    · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwblk, _⟩
      rcases hwblk with ⟨blk, hmb, _⟩; exact hro.2.1 dw.winBid (mem_lt_nextBlock hmb)
    · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpblk, _⟩
      rcases hpblk with ⟨blk, hmb, _⟩; exact hro.2.1 dw.prevBid (mem_lt_nextBlock hmb)
    · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hblk, _⟩, _⟩
      exact hro.2.1 dw.headBid (mem_lt_nextBlock hblk)
    · rcases hpbuf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpblk, _⟩
      exact hro.2.1 dw.pbufBid (mem_lt_nextBlock hpblk)
  · exact ⟨readField?_congr_block tags hsb_eq, readField?_congr_block tags hsb_eq,
      readField?_congr_block tags hsb_eq, readField?_congr_block tags hsb_eq,
      readField?_congr_block tags hsb_eq⟩

/-! ## 3. Gzip File Handle Witness & Invariant (`GzWitness`, `GzStateInv`) -/

/-- Owned heap block IDs of one live `gz_state` handle (`GZ_READ` or `GZ_WRITE`). -/
structure GzWitness where
  gzBid : BlockId
  pathBid : BlockId
  msg? : Option BlockId
  in? : Option BlockId
  out? : Option BlockId
  stream? : Option (Sum InflateWitness DeflateWitness)
  deriving DecidableEq, Repr

def GzWitness.streamOwnedList : Option (Sum InflateWitness DeflateWitness) → List BlockId
  | none => []
  | some (.inl iw) => iw.ownedList
  | some (.inr dw) => dw.ownedList

def GzWitness.ownedList (gw : GzWitness) : List BlockId :=
  gw.gzBid :: gw.pathBid :: gw.msg?.toList ++ gw.in?.toList ++ gw.out?.toList ++
    GzWitness.streamOwnedList gw.stream?

/-- Full memory invariant for a live `gz_state` handle at `(.ptr gw.gzBid 0)`.
Parameterizing by `checkReadX` and `checkWriteIn` lets internal stream helpers temporarily
point `x.next` at caller output (`gz_decomp` called from `gz_read`) or `strm.next_in` at
caller input (`gz_comp` called from `gz_write`) while keeping all other invariants live. -/
def GzStateInvCore (checkReadX checkWriteIn : Bool)
    (tags : TypeEnv) (gEnv : Env) (m : Mem) (gw : GzWitness) : Prop :=
  gw.ownedList.Nodup ∧
  HeapRwBlock m gw.gzBid 248 8 ∧
  (∃ plen, HeapRwBlock m gw.pathBid (plen + 1) 1 ∧ m.strlenAt gw.pathBid 0 = some plen ∧
    readField? tags m (.ptr gw.gzBid 0) "gz_state" "path" = some (.ptr gw.pathBid 0)) ∧
  (match gw.msg? with
   | none => readField? tags m (.ptr gw.gzBid 0) "gz_state" "msg" = some .null
   | some mb => ∃ mlen, HeapRwBlock m mb (mlen + 1) 1 ∧ m.strlenAt mb 0 = some mlen ∧
     readField? tags m (.ptr gw.gzBid 0) "gz_state" "msg" = some (.ptr mb 0)) ∧
  let g : Val := .ptr gw.gzBid 0
  let strmPtr : Val := .ptr gw.gzBid 136
  (∃ mode fd size want direct junk how again start eof past level strategy reset_ skip err xHave xPos,
    readIntField? tags m g "gz_state" "mode" = some mode ∧
    readIntField? tags m g "gz_state" "fd" = some fd ∧
    readNatField? tags m g "gz_state" "size" = some size ∧
    readNatField? tags m g "gz_state" "want" = some want ∧
    readIntField? tags m g "gz_state" "direct" = some direct ∧
    readIntField? tags m g "gz_state" "junk" = some junk ∧
    readIntField? tags m g "gz_state" "how" = some how ∧
    readIntField? tags m g "gz_state" "again" = some again ∧
    readIntField? tags m g "gz_state" "start" = some start ∧
    readIntField? tags m g "gz_state" "eof" = some eof ∧
    readIntField? tags m g "gz_state" "past" = some past ∧
    readIntField? tags m g "gz_state" "level" = some level ∧
    readIntField? tags m g "gz_state" "strategy" = some strategy ∧
    readIntField? tags m g "gz_state" "reset" = some reset_ ∧
    readIntField? tags m g "gz_state" "skip" = some skip ∧
    readIntField? tags m g "gz_state" "err" = some err ∧
    readNatField? tags m g "gzFile_s" "have" = some xHave ∧
    readIntField? tags m g "gzFile_s" "pos" = some xPos ∧
    (mode = 7247 ∨ mode = 31153) ∧
    8 ≤ want ∧ want < 2 ^ 31 ∧ (size = 0 ∨ size = want) ∧
    0 ≤ start ∧ 0 ≤ skip ∧ 0 ≤ xPos + (xHave : Int) ∧
    (mode = 31153 → 0 ≤ xPos) ∧
    (size = 0 →
      gw.in? = none ∧ gw.out? = none ∧ gw.stream? = none ∧ xHave = 0 ∧
      (mode = 7247 → how = 0 ∧ (-1 ≤ direct ∧ direct ≤ 1) ∧ (-1 ≤ junk ∧ junk ≤ 1)) ∧
      (mode = 31153 → direct = 0 ∨ direct = 1)) ∧
    (0 < size ∧ mode = 7247 →
      (-1 ≤ direct ∧ direct ≤ 1) ∧ (-1 ≤ junk ∧ junk ≤ 1) ∧ (how = 0 ∨ how = 1 ∨ how = 2) ∧
      ∃ inBid outBid iw inBlk outBlk,
        gw.in? = some inBid ∧ gw.out? = some outBid ∧ gw.stream? = some (.inl iw) ∧
        m.blocks inBid = some inBlk ∧ inBlk.kind = .heap ∧ inBlk.perm = .rw ∧
        size ≤ inBlk.size ∧ 1 ≤ inBlk.align ∧
        readField? tags m g "gz_state" "in" = some (.ptr inBid 0) ∧
        m.blocks outBid = some outBlk ∧ outBlk.kind = .heap ∧ outBlk.perm = .rw ∧
        2 * size ≤ outBlk.size ∧ 1 ≤ outBlk.align ∧
        readField? tags m g "gz_state" "out" = some (.ptr outBid 0) ∧
        InflateStateInv tags gEnv m strmPtr iw ∧
        StreamAccumulatorsInit tags m strmPtr ∧
        readField? tags m (.ptr iw.stBid 0) "inflate_state" "head" = some .null ∧
        (∃ smsg, readField? tags m strmPtr "z_stream_s" "msg" = some smsg ∧
          (smsg = .null ∨ ∃ mb mblk, smsg = .ptr mb 0 ∧ m.blocks mb = some mblk ∧
            mblk.kind = .global ∧ mblk.perm = .ro ∧ ∃ mlen, m.strlenAt mb 0 = some mlen)) ∧
        (∃ nextIn availIn,
          readField? tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
          readNatField? tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
          ((availIn = 0 ∧ (nextIn = .null ∨ ∃ o ≤ size, nextIn = .ptr inBid (Int64.ofNat o))) ∨
           (∃ o : Nat, nextIn = .ptr inBid (Int64.ofNat o) ∧ o + availIn ≤ size ∧
             ∀ j < availIn, ∃ u : UInt8, inBlk.bytes (o + j) = .byte u))) ∧
        (checkReadX = true →
          xHave ≤ 2 * size ∧
          (xHave = 0 ∨ ∃ xOff : Nat,
            readField? tags m g "gzFile_s" "next" = some (.ptr outBid (Int64.ofNat xOff)) ∧
            xOff + xHave ≤ 2 * size ∧
            ∀ j < xHave, ∃ u : UInt8, outBlk.bytes (xOff + j) = .byte u))) ∧
    (0 < size ∧ mode = 31153 →
      (direct = 0 ∨ direct = 1) ∧ xHave = 0 ∧
      ∃ inBid inBlk,
        gw.in? = some inBid ∧
        m.blocks inBid = some inBlk ∧ inBlk.kind = .heap ∧ inBlk.perm = .rw ∧
        2 * size ≤ inBlk.size ∧ 1 ≤ inBlk.align ∧
        readField? tags m g "gz_state" "in" = some (.ptr inBid 0) ∧
        (checkWriteIn = true →
          ∃ nextIn availIn,
            readField? tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
            readNatField? tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
            ((availIn = 0 ∧ (nextIn = .null ∨ ∃ o ≤ 2 * size, nextIn = .ptr inBid (Int64.ofNat o))) ∨
             (∃ o : Nat, nextIn = .ptr inBid (Int64.ofNat o) ∧ o + availIn ≤ 2 * size ∧
               ∀ j < availIn, ∃ u : UInt8, inBlk.bytes (o + j) = .byte u))) ∧
        (direct = 1 → gw.out? = none ∧ gw.stream? = none) ∧
        (direct = 0 →
          ∃ outBid dw outBlk xOff outOff avOut,
            gw.out? = some outBid ∧ gw.stream? = some (.inr dw) ∧
            m.blocks outBid = some outBlk ∧ outBlk.kind = .heap ∧ outBlk.perm = .rw ∧
            size ≤ outBlk.size ∧ 1 ≤ outBlk.align ∧
            readField? tags m g "gz_state" "out" = some (.ptr outBid 0) ∧
            DeflateStateInv tags gEnv m strmPtr dw ∧
            StreamAccumulatorsInit tags m strmPtr ∧
            readField? tags m g "gzFile_s" "next" = some (.ptr outBid (Int64.ofNat xOff)) ∧
            readField? tags m strmPtr "z_stream_s" "next_out" = some (.ptr outBid (Int64.ofNat outOff)) ∧
            readNatField? tags m strmPtr "z_stream_s" "avail_out" = some avOut ∧
            xOff ≤ outOff ∧ outOff + avOut = size ∧
            ∀ j < outOff - xOff, ∃ u : UInt8, outBlk.bytes (xOff + j) = .byte u)))

abbrev GzStateInv (tags : TypeEnv) (gEnv : Env) (m : Mem) (gw : GzWitness) : Prop :=
  GzStateInvCore true true tags gEnv m gw

theorem GzStateInvCore.weaken {cX1 cI1 cX2 cI2 : Bool}
    (hX : cX2 = true → cX1 = true) (hI : cI2 = true → cI1 = true)
    {tags : TypeEnv} {gEnv : Env} {m : Mem} {gw : GzWitness}
    (h : GzStateInvCore cX1 cI1 tags gEnv m gw) :
    GzStateInvCore cX2 cI2 tags gEnv m gw := by
  rcases h with ⟨hnd, hgz, hpath, hmsg, mode, fd, size, want, direct, junk, how, again, start,
    eof, past, level, strategy, reset_, skip, err, xHave, xPos,
    f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    b1, b2, b3, b4, b5, b6, b7, b8, hsz0, hread, hwrite⟩
  refine ⟨hnd, hgz, hpath, hmsg, mode, fd, size, want, direct, junk, how, again, start,
    eof, past, level, strategy, reset_, skip, err, xHave, xPos,
    f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    b1, b2, b3, b4, b5, b6, b7, b8, hsz0, ?_, ?_⟩
  · intro hr
    rcases hread hr with ⟨d1, d2, d3, inBid, outBid, iw, inBlk, outBlk,
      hinw, houtw, hstrw, hb1, hb2, hb3, hb4, hb5, hb6, ob1, ob2, ob3, ob4, ob5, ob6,
      hinf, hacc, hhd, hmsg', hnin, hrx⟩
    exact ⟨d1, d2, d3, inBid, outBid, iw, inBlk, outBlk,
      hinw, houtw, hstrw, hb1, hb2, hb3, hb4, hb5, hb6, ob1, ob2, ob3, ob4, ob5, ob6,
      hinf, hacc, hhd, hmsg', hnin, fun hx => hrx (hX hx)⟩
  · intro hw
    rcases hwrite hw with ⟨hd1, hxh, inBid, inBlk, hinw, hb1, hb2, hb3, hb4, hb5, hb6, hwin, hd_1, hd_0⟩
    exact ⟨hd1, hxh, inBid, inBlk, hinw, hb1, hb2, hb3, hb4, hb5, hb6, fun hi => hwin (hI hi), hd_1, hd_0⟩

private theorem InflateWitness.mem_ownedList_of_streamOwned {iw : InflateWitness}
    (b : BlockId) (hb : b ∈ iw.ownedList) :
    b ∈ GzWitness.streamOwnedList (some (.inl iw)) := hb

private theorem DeflateWitness.mem_ownedList_of_streamOwned {dw : DeflateWitness}
    (b : BlockId) (hb : b ∈ dw.ownedList) :
    b ∈ GzWitness.streamOwnedList (some (.inr dw)) := hb

theorem GzStateInvCore.congr_blocks {cX cI : Bool} {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {gw : GzWitness}
    (hpres : ∀ b, b ∈ gw.ownedList → m2.blocks b = m1.blocks b)
    (hroG : ∀ b blk, m1.blocks b = some blk → blk.kind = .global → blk.perm = .ro → m2.blocks b = m1.blocks b)
    (h : GzStateInvCore cX cI tags gEnv m1 gw) :
    GzStateInvCore cX cI tags gEnv m2 gw := by
  have hgz : m2.blocks gw.gzBid = m1.blocks gw.gzBid :=
    hpres gw.gzBid (by simp [GzWitness.ownedList])
  have hpa : m2.blocks gw.pathBid = m1.blocks gw.pathBid :=
    hpres gw.pathBid (by simp [GzWitness.ownedList])
  rcases h with ⟨hnodup, hgz_blk, ⟨plen, hp_blk, hp_str, hp_fld⟩, hmsg, hrest⟩
  refine ⟨hnodup, hgz_blk.congr_blocks hgz, ⟨plen, hp_blk.congr_blocks hpa, strlenAt_congr_block hpa hp_str, ?_⟩, ?_, ?_⟩
  · rw [readField?_congr_block tags hgz]; exact hp_fld
  · cases hmw : gw.msg? with
    | none =>
      rw [hmw] at hmsg
      rw [readField?_congr_block tags hgz]; exact hmsg
    | some mb =>
      rw [hmw] at hmsg
      have hmb : m2.blocks mb = m1.blocks mb := hpres mb (by simp [GzWitness.ownedList, hmw])
      rcases hmsg with ⟨mlen, hm_blk, hm_str, hm_fld⟩
      exact ⟨mlen, hm_blk.congr_blocks hmb, strlenAt_congr_block hmb hm_str,
        by rw [readField?_congr_block tags hgz]; exact hm_fld⟩
  · rcases hrest with ⟨mode, fd, size, want, direct, junk, how, again, start, eof, past, level,
      strategy, reset_, skip, err, xHave, xPos,
      f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
      b1, b2, b3, b4, b5, b6, b7, b8, hsz0, hread, hwrite⟩
    refine ⟨mode, fd, size, want, direct, junk, how, again, start, eof, past, level,
      strategy, reset_, skip, err, xHave, xPos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      b1, b2, b3, b4, b5, b6, b7, b8, hsz0, ?_, ?_⟩ <;>
      try (simp only [readIntField?_congr_block tags hgz, readNatField?_congr_block tags hgz]; assumption)
    · intro hr
      rcases hread hr with ⟨d1, d2, d3, inBid, outBid, iw, inBlk, outBlk,
        hinw, houtw, hstrw, hin_b, hin_k, hin_p, hin_sz, hin_al, hin_f,
        hout_b, hout_k, hout_p, hout_sz, hout_al, hout_f, hinf, hacc, hhd, hsm, hnin, hrx⟩
      have hin_eq : m2.blocks inBid = m1.blocks inBid :=
        hpres inBid (by simp [GzWitness.ownedList, hinw])
      have hout_eq : m2.blocks outBid = m1.blocks outBid :=
        hpres outBid (by simp [GzWitness.ownedList, houtw])
      have hst_eq : m2.blocks iw.stBid = m1.blocks iw.stBid := by
        apply hpres
        simp only [GzWitness.ownedList, hstrw, List.mem_append]
        exact Or.inr (InflateWitness.mem_ownedList_of_streamOwned iw.stBid
          (by simp [InflateWitness.ownedList]))
      refine ⟨d1, d2, d3, inBid, outBid, iw, inBlk, outBlk, hinw, houtw, hstrw,
        hin_eq ▸ hin_b, hin_k, hin_p, hin_sz, hin_al, ?_,
        hout_eq ▸ hout_b, hout_k, hout_p, hout_sz, hout_al, ?_, ?_, hacc.congr_block hgz, ?_, ?_, ?_, ?_⟩
      · rw [readField?_congr_block tags hgz]; exact hin_f
      · rw [readField?_congr_block tags hgz]; exact hout_f
      · refine hinf.congr_blocks rfl ?_ ?_ hroG
        · intro b hb
          apply hpres
          simp only [GzWitness.ownedList, hstrw, List.mem_append]
          exact Or.inr hb
        · exact ⟨readField?_congr_block tags hgz, readField?_congr_block tags hgz,
            readField?_congr_block tags hgz, readField?_congr_block tags hgz⟩
      · rw [readField?_congr_block tags hst_eq]; exact hhd
      · rcases hsm with ⟨smsg, hsmsg, hsmsg_p⟩
        refine ⟨smsg, by rw [readField?_congr_block tags hgz]; exact hsmsg, ?_⟩
        rcases hsmsg_p with rfl | ⟨mb, mblk, rfl, hm_mb, hmk, hmp, mlen, hml⟩
        · exact Or.inl rfl
        · have heqm := hroG mb mblk hm_mb hmk hmp
          exact Or.inr ⟨mb, mblk, rfl, heqm.symm ▸ hm_mb, hmk, hmp, mlen,
            strlenAt_congr_block heqm hml⟩
      · rcases hnin with ⟨ni, avi, hni, havi, hc⟩
        refine ⟨ni, avi, ?_, ?_, hc⟩
        · rw [readField?_congr_block tags hgz]; exact hni
        · rw [readNatField?_congr_block tags hgz]; exact havi
      · intro hx
        rcases hrx hx with ⟨hxh1, hxh2⟩
        refine ⟨hxh1, ?_⟩
        rcases hxh2 with rfl | ⟨xo, hxn, hxo1, hxo2⟩
        · exact Or.inl rfl
        · refine Or.inr ⟨xo, ?_, hxo1, hxo2⟩
          rw [readField?_congr_block tags hgz]; exact hxn
    · intro hw
      rcases hwrite hw with ⟨hd1, hxh, inBid, inBlk, hinw, hin_b, hin_k, hin_p, hin_sz, hin_al, hin_f, hnin, hd_1, hd_0⟩
      have hin_eq : m2.blocks inBid = m1.blocks inBid :=
        hpres inBid (by simp [GzWitness.ownedList, hinw])
      refine ⟨hd1, hxh, inBid, inBlk, hinw, hin_eq ▸ hin_b, hin_k, hin_p, hin_sz, hin_al, ?_, ?_, hd_1, ?_⟩
      · rw [readField?_congr_block tags hgz]; exact hin_f
      · intro hi
        rcases hnin hi with ⟨ni, avi, hni, havi, hc⟩
        refine ⟨ni, avi, ?_, ?_, hc⟩
        · rw [readField?_congr_block tags hgz]; exact hni
        · rw [readNatField?_congr_block tags hgz]; exact havi
      · intro hd0
        rcases hd_0 hd0 with ⟨outBid, dw, outBlk, xOff, outOff, avOut,
          houtw, hstrw, hout_b, hout_k, hout_p, hout_sz, hout_al, hout_f,
          hdef, hacc, hxn, hno, havo, hle, heqsz, hbytes⟩
        have hout_eq : m2.blocks outBid = m1.blocks outBid :=
          hpres outBid (by simp [GzWitness.ownedList, houtw])
        refine ⟨outBid, dw, outBlk, xOff, outOff, avOut, houtw, hstrw,
          hout_eq ▸ hout_b, hout_k, hout_p, hout_sz, hout_al, ?_, ?_, hacc.congr_block hgz, ?_, ?_, ?_, hle, heqsz, hbytes⟩
        · rw [readField?_congr_block tags hgz]; exact hout_f
        · refine hdef.congr_blocks ?_ ?_
          · intro b hb
            apply hpres
            simp only [GzWitness.ownedList, hstrw, List.mem_append]
            exact Or.inr hb
          · exact ⟨readField?_congr_block tags hgz, readField?_congr_block tags hgz,
              readField?_congr_block tags hgz, readField?_congr_block tags hgz,
              readField?_congr_block tags hgz⟩
        · rw [readField?_congr_block tags hgz]; exact hxn
        · rw [readField?_congr_block tags hgz]; exact hno
        · rw [readNatField?_congr_block tags hgz]; exact havo

theorem GzStateInv.congr_blocks {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {gw : GzWitness}
    (hpres : ∀ b, b ∈ gw.ownedList → m2.blocks b = m1.blocks b)
    (hroG : ∀ b blk, m1.blocks b = some blk → blk.kind = .global → blk.perm = .ro → m2.blocks b = m1.blocks b)
    (h : GzStateInv tags gEnv m1 gw) :
    GzStateInv tags gEnv m2 gw :=
  GzStateInvCore.congr_blocks hpres hroG h

theorem GzStateInvCore.roExt {cX cI : Bool} {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {gw : GzWitness} (hro : C99.Proof.ROExt m1 m2)
    (h : GzStateInvCore cX cI tags gEnv m1 gw) :
    GzStateInvCore cX cI tags gEnv m2 gw := by
  refine GzStateInvCore.congr_blocks ?_ (fun b blk hmb _ _ => hro.2.1 b (mem_lt_nextBlock hmb)) h
  intro b hb
  rcases h with ⟨_, ⟨gzb, hgzb, _⟩, ⟨_, ⟨pb, hpb, _⟩, _⟩, hmsg, hrest⟩
  simp only [GzWitness.ownedList, List.mem_cons, List.mem_append, or_assoc] at hb
  rcases hb with rfl | rfl | hm | hin | hout | hstrm
  · exact hro.2.1 gw.gzBid (mem_lt_nextBlock hgzb)
  · exact hro.2.1 gw.pathBid (mem_lt_nextBlock hpb)
  · cases hm_eq : gw.msg? with
    | none => simp [hm_eq] at hm
    | some mb =>
      rw [hm_eq] at hm hmsg
      simp only [Option.toList_some, List.mem_singleton] at hm
      subst hm
      rcases hmsg with ⟨_, ⟨mblk, hmblk, _⟩, _⟩
      exact hro.2.1 b (mem_lt_nextBlock hmblk)
  · cases hin_eq : gw.in? with
    | none => simp [hin_eq] at hin
    | some ib =>
      rw [hin_eq] at hin
      simp only [Option.toList_some, List.mem_singleton] at hin
      subst hin
      rcases hrest with ⟨mode, fd, size, want, direct, junk, how, again, start, eof, past, level,
        strategy, reset_, skip, err, xHave, xPos,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
      by_cases hsz : size = 0
      · obtain ⟨hin0, _⟩ := hsz0 hsz
        rw [hin0] at hin_eq; cases hin_eq
      · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
        rcases hmd with rfl | rfl
        · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, inBid, outBid, iw, inBlk, _, hinw, _, _, hin_b, _⟩
          rw [hinw] at hin_eq; cases hin_eq
          exact hro.2.1 b (mem_lt_nextBlock hin_b)
        · rcases hwrite ⟨hpos, rfl⟩ with ⟨_, _, inBid, inBlk, hinw, hin_b, _⟩
          rw [hinw] at hin_eq; cases hin_eq
          exact hro.2.1 b (mem_lt_nextBlock hin_b)
  · cases hout_eq : gw.out? with
    | none => simp [hout_eq] at hout
    | some ob =>
      rw [hout_eq] at hout
      simp only [Option.toList_some, List.mem_singleton] at hout
      subst hout
      rcases hrest with ⟨mode, fd, size, want, direct, junk, how, again, start, eof, past, level,
        strategy, reset_, skip, err, xHave, xPos,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
      by_cases hsz : size = 0
      · obtain ⟨_, hout0, _⟩ := hsz0 hsz
        rw [hout0] at hout_eq; cases hout_eq
      · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
        rcases hmd with rfl | rfl
        · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, _, outBid, _, _, outBlk, _, houtw, _, _, _, _, _, _, _, hout_b, _⟩
          rw [houtw] at hout_eq; cases hout_eq
          exact hro.2.1 b (mem_lt_nextBlock hout_b)
        · rcases hwrite ⟨hpos, rfl⟩ with ⟨hd, _, _, _, _, _, _, _, _, _, _, _, hd1, hd0⟩
          rcases hd with rfl | rfl
          · rcases hd0 rfl with ⟨outBid, _, outBlk, _, _, _, houtw, _, hout_b, _⟩
            rw [houtw] at hout_eq; cases hout_eq
            exact hro.2.1 b (mem_lt_nextBlock hout_b)
          · rw [((hd1 rfl).1)] at hout_eq; cases hout_eq
  · cases hs_eq : gw.stream? with
    | none => simp [hs_eq, GzWitness.streamOwnedList] at hstrm
    | some s =>
      rw [hs_eq] at hstrm
      cases s with
      | inl iw =>
        rcases hrest with ⟨mode, fd, size, want, direct, junk, how, again, start, eof, past, level,
          strategy, reset_, skip, err, xHave, xPos,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
        by_cases hsz : size = 0
        · obtain ⟨_, _, hs0, _⟩ := hsz0 hsz; rw [hs0] at hs_eq; cases hs_eq
        · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
          rcases hmd with rfl | rfl
          · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, _, _, iw', _, _, _, _, hstrw,
              _, _, _, _, _, _, _, _, _, _, _, _, hinf, _⟩
            rw [hstrw] at hs_eq; cases hs_eq
            simp only [GzWitness.streamOwnedList, InflateWitness.ownedList, List.mem_cons] at hstrm
            rcases hstrm with rfl | hwm
            · rcases hinf.1 with ⟨blk, hmb, _⟩; exact hro.2.1 iw.stBid (mem_lt_nextBlock hmb)
            · cases hw' : iw.win? with
              | none => simp [hw'] at hwm
              | some wb =>
                rw [hw'] at hwm
                simp only [Option.toList_some, List.mem_singleton] at hwm
                subst hwm
                rcases hinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwin, _⟩
                rcases hwin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmatch⟩
                rw [hw'] at hmatch
                rcases hmatch with ⟨_, _, _, wblk, hmb, _⟩
                exact hro.2.1 b (mem_lt_nextBlock hmb)
          · rcases hwrite ⟨hpos, rfl⟩ with ⟨hd, _, _, _, _, _, _, _, _, _, _, _, hd1, hd0⟩
            rcases hd with rfl | rfl
            · rcases hd0 rfl with ⟨_, dw', _, _, _, _, _, hstrw, _⟩
              rw [hstrw] at hs_eq; cases hs_eq
            · rw [(hd1 rfl).2] at hs_eq; cases hs_eq
      | inr dw =>
        rcases hrest with ⟨mode, fd, size, want, direct, junk, how, again, start, eof, past, level,
          strategy, reset_, skip, err, xHave, xPos,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
        by_cases hsz : size = 0
        · obtain ⟨_, _, hs0, _⟩ := hsz0 hsz; rw [hs0] at hs_eq; cases hs_eq
        · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
          rcases hmd with rfl | rfl
          · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, _, _, iw', _, _, _, _, hstrw, _⟩
            rw [hstrw] at hs_eq; cases hs_eq
          · rcases hwrite ⟨hpos, rfl⟩ with ⟨hd, _, _, _, _, _, _, _, _, _, _, _, hd1, hd0⟩
            rcases hd with rfl | rfl
            · rcases hd0 rfl with ⟨_, dw', _, _, _, _, _, hstrw, _, _, _, _, _, _, hdef, _⟩
              rw [hstrw] at hs_eq; cases hs_eq
              simp only [GzWitness.streamOwnedList, DeflateWitness.ownedList, List.mem_cons,
                List.not_mem_nil, or_false] at hstrm
              rcases hdef with ⟨_, hst, _, _, _, _, _, _, _, _, _, _, hwinf, hpbuf, _⟩
              rcases hstrm with rfl | rfl | rfl | rfl | rfl
              · rcases hst with ⟨blk, hmb, _⟩; exact hro.2.1 dw.stBid (mem_lt_nextBlock hmb)
              · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hwblk, _⟩
                rcases hwblk with ⟨blk, hmb, _⟩; exact hro.2.1 dw.winBid (mem_lt_nextBlock hmb)
              · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpblk, _⟩
                rcases hpblk with ⟨blk, hmb, _⟩; exact hro.2.1 dw.prevBid (mem_lt_nextBlock hmb)
              · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hblk, _⟩, _⟩
                exact hro.2.1 dw.headBid (mem_lt_nextBlock hblk)
              · rcases hpbuf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpblk, _⟩
                exact hro.2.1 dw.pbufBid (mem_lt_nextBlock hpblk)
            · rw [(hd1 rfl).2] at hs_eq; cases hs_eq

theorem GzStateInv.roExt {tags : TypeEnv} {gEnv : Env}
    {m1 m2 : Mem} {gw : GzWitness} (hro : C99.Proof.ROExt m1 m2)
    (h : GzStateInv tags gEnv m1 gw) :
    GzStateInv tags gEnv m2 gw :=
  GzStateInvCore.roExt hro h

/-! ## 4. Unified Library Invariant (`ZlibInv`) & Ownership Partition -/

/-- Witness carrying the owned heap blocks of an external `z_stream` handle. -/
inductive StreamWit where
  | deflate (dw : DeflateWitness)
  | inflate (iw : InflateWitness)
  | inflateBack (ibw : InflateBackWitness)
  deriving DecidableEq, Repr

def StreamWit.kind : StreamWit → StreamKind
  | .deflate _ => .deflate
  | .inflate _ => .inflate
  | .inflateBack _ => .inflateBack

def StreamWit.ownedList : StreamWit → List BlockId
  | .deflate dw => dw.ownedList
  | .inflate iw => iw.ownedList
  | .inflateBack ibw => ibw.ownedList

def StreamWit.stBid : StreamWit → BlockId
  | .deflate dw => dw.stBid
  | .inflate iw => iw.stBid
  | .inflateBack ibw => ibw.stBid

theorem StreamWit.stBid_mem_ownedList (sw : StreamWit) : sw.stBid ∈ sw.ownedList := by
  cases sw with
  | deflate dw => simp [StreamWit.stBid, StreamWit.ownedList, DeflateWitness.ownedList]
  | inflate iw => simp [StreamWit.stBid, StreamWit.ownedList, InflateWitness.ownedList]
  | inflateBack ibw => simp [StreamWit.stBid, StreamWit.ownedList, InflateBackWitness.ownedList]

/-- Memory invariant for an external live stream handle `(b, k)` at `(.ptr b 0)`. -/
def StreamStateInv (tags : TypeEnv) (gEnv : Env) (m : Mem) (b : BlockId) :
    StreamKind → StreamWit → Prop
  | .deflate, .deflate dw => DeflateStateInv tags gEnv m (.ptr b 0) dw
  | .inflate, .inflate iw => InflateStateInv tags gEnv m (.ptr b 0) iw
  | .inflateBack, .inflateBack ibw => InflateBackInv tags m (.ptr b 0) ibw
  | _, _ => False

/-- Combined list of all library-owned heap blocks across all live streams and `gzFile`s. -/
def allOwnedList (streamWits : List (BlockId × StreamWit)) (gzWits : List GzWitness) : List BlockId :=
  streamWits.flatMap (fun p => p.2.ownedList) ++ gzWits.flatMap GzWitness.ownedList

theorem mem_allOwnedList_of_stream {streamWits : List (BlockId × StreamWit)} {gzWits : List GzWitness}
    {p : BlockId × StreamWit} (hp : p ∈ streamWits) {b : BlockId} (hb : b ∈ p.2.ownedList) :
    b ∈ allOwnedList streamWits gzWits :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hp, hb⟩)

theorem mem_allOwnedList_of_gz {streamWits : List (BlockId × StreamWit)} {gzWits : List GzWitness}
    {gw : GzWitness} (hg : gw ∈ gzWits) {b : BlockId} (hb : b ∈ gw.ownedList) :
    b ∈ allOwnedList streamWits gzWits :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨gw, hg, hb⟩)

private theorem readVal_ptr_ne_some_blk {tags : TypeEnv} {m : Mem} {b pb : BlockId}
    {off poff : Int64} {ty : CTy} (hne : b ≠ pb)
    (h : Sem.readVal tags m b off ty = some (.ptr pb poff)) :
    ∃ blk, m.blocks b = some blk := by
  by_cases hnone : m.blocks b = none
  · exfalso
    unfold Sem.readVal at h
    dsimp only [bind, Option.bind, pure, Pure.pure] at h
    match hty : ty.unqual with
    | .void | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ | .const_ _ | .typedef _ _ =>
      rw [hty] at h; cases h
    | .array _ _ =>
      rw [hty] at h
      dsimp only at h
      cases h
      exact hne rfl
    | .int k =>
      rw [hty] at h
      dsimp only [CTy.intKind?] at h
      rw [hnone] at h
      cases h
    | .enumTy _ _ =>
      rw [hty] at h
      dsimp only [CTy.intKind?] at h
      rw [hnone] at h
      cases h
    | .ptr _ =>
      rw [hty] at h
      dsimp only at h
      rw [hnone] at h
      cases h
    | .fnPtr _ _ _ =>
      rw [hty] at h
      dsimp only at h
      rw [hnone] at h
      cases h
    | .vaList =>
      rw [hty] at h
      dsimp only [Mem.readBytes] at h
      rw [hnone] at h
      cases h
  · cases hb : m.blocks b with
    | none => contradiction
    | some blk => exact ⟨blk, rfl⟩

private theorem readField?_ptr_ne_some_blk {tags : TypeEnv} {m : Mem} {b pb : BlockId}
    {off poff : Int64} {st fld : String} (hne : b ≠ pb)
    (h : readField? tags m (.ptr b off) st fld = some (.ptr pb poff)) :
    ∃ blk, m.blocks b = some blk := by
  unfold readField? at h
  dsimp only [bind, Option.bind] at h
  cases hfl : fieldLayout? tags (.structTy st) fld with
  | none => rw [hfl] at h; cases h
  | some p =>
    rw [hfl] at h
    dsimp only at h
    exact readVal_ptr_ne_some_blk hne h

theorem StreamStateInv.state_eq {tags : TypeEnv} {gEnv : Env} {m : Mem} {b : BlockId}
    {k : StreamKind} {sw : StreamWit} (h : StreamStateInv tags gEnv m b k sw) :
    readField? tags m (.ptr b 0) "z_stream_s" "state" = some (.ptr sw.stBid 0) := by
  match k, sw with
  | .deflate, .deflate dw => exact h.2.2.1
  | .inflate, .inflate iw => exact h.2.2.1
  | .inflateBack, .inflateBack ibw =>
    rcases h with ⟨_, _, _, _, _, _, hst, _⟩
    exact hst

theorem DeflateStateInv.owned_heap {tags : TypeEnv} {gEnv : Env} {m : Mem}
    {strmPtr : Val} {dw : DeflateWitness} (h : DeflateStateInv tags gEnv m strmPtr dw) :
    ∀ x ∈ dw.ownedList, ∃ blk, m.blocks x = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw := by
  rcases h with ⟨_, ⟨stblk, hst, hstk, hstp, _⟩, _, _, _, _, _, _, _, _, _, _, hwinf, hpbuf, _⟩
  intro x hx
  simp only [DeflateWitness.ownedList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨stblk, hst, hstk, hstp⟩
  · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨wblk, hw, hwk, hwp, _⟩, _⟩
    exact ⟨wblk, hw, hwk, hwp⟩
  · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨pblk, hp, hpk, hpp, _⟩, _⟩
    exact ⟨pblk, hp, hpk, hpp⟩
  · rcases hwinf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm_h, hhk, hhp, _⟩, _⟩
    exact ⟨_, hm_h, hhk, hhp⟩
  · rcases hpbuf with ⟨_, _, _, _, _, _, _, _, _, _, _, _, pblk,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, hpk, hpp, _⟩
    exact ⟨pblk, hp, hpk, hpp⟩

theorem InflateStateInv.owned_heap {tags : TypeEnv} {gEnv : Env} {m : Mem}
    {strmPtr : Val} {iw : InflateWitness} (h : InflateStateInv tags gEnv m strmPtr iw) :
    ∀ x ∈ iw.ownedList, ∃ blk, m.blocks x = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw := by
  rcases h with ⟨⟨stblk, hst, hstk, hstp, _⟩, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwin, _⟩
  intro x hx
  simp only [InflateWitness.ownedList, List.mem_cons] at hx
  rcases hx with rfl | hwm
  · exact ⟨stblk, hst, hstk, hstp⟩
  · cases hw' : iw.win? with
    | none => simp [hw'] at hwm
    | some wb =>
      rw [hw'] at hwm
      simp only [Option.toList_some, List.mem_singleton] at hwm
      subst hwm
      rcases hwin with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmatch⟩
      rw [hw'] at hmatch
      rcases hmatch with ⟨_, _, _, wblk, hmwb, hwk, hwp, _⟩
      exact ⟨wblk, hmwb, hwk, hwp⟩

theorem InflateBackInv.owned_heap {tags : TypeEnv} {m : Mem}
    {strmPtr : Val} {ibw : InflateBackWitness} (h : InflateBackInv tags m strmPtr ibw) :
    ∀ x ∈ ibw.ownedList, ∃ blk, m.blocks x = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw := by
  rcases h with ⟨⟨stblk, hst, hstk, hstp, _⟩, _⟩
  intro x hx
  simp only [InflateBackWitness.ownedList, List.mem_singleton] at hx
  subst hx
  exact ⟨stblk, hst, hstk, hstp⟩

theorem StreamStateInv.owned_heap {tags : TypeEnv} {gEnv : Env} {m : Mem} {b : BlockId}
    {k : StreamKind} {sw : StreamWit} (h : StreamStateInv tags gEnv m b k sw) :
    ∀ x ∈ sw.ownedList, ∃ blk, m.blocks x = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw := by
  match k, sw with
  | .deflate, .deflate dw => exact DeflateStateInv.owned_heap h
  | .inflate, .inflate iw => exact InflateStateInv.owned_heap h
  | .inflateBack, .inflateBack ibw => exact InflateBackInv.owned_heap h

theorem GzStateInvCore.owned_heap {cX cI : Bool} {tags : TypeEnv} {gEnv : Env} {m : Mem}
    {gw : GzWitness} (h : GzStateInvCore cX cI tags gEnv m gw) :
    ∀ x ∈ gw.ownedList, ∃ blk, m.blocks x = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw := by
  intro x hx
  rcases h with ⟨_, ⟨gzb, hgzb, hgzk, hgzp, _⟩, ⟨_, ⟨pb, hpb, hpk, hpp, _⟩, _⟩, hmsg, hrest⟩
  simp only [GzWitness.ownedList, List.mem_cons, List.mem_append, or_assoc] at hx
  rcases hx with rfl | rfl | hm | hin | hout | hstrm
  · exact ⟨gzb, hgzb, hgzk, hgzp⟩
  · exact ⟨pb, hpb, hpk, hpp⟩
  · cases hm_eq : gw.msg? with
    | none => simp [hm_eq] at hm
    | some mb =>
      rw [hm_eq] at hm hmsg
      simp only [Option.toList_some, List.mem_singleton] at hm
      subst hm
      rcases hmsg with ⟨_, ⟨mblk, hmblk, hmk, hmp, _⟩, _⟩
      exact ⟨mblk, hmblk, hmk, hmp⟩
  · cases hin_eq : gw.in? with
    | none => simp [hin_eq] at hin
    | some ib =>
      rw [hin_eq] at hin
      simp only [Option.toList_some, List.mem_singleton] at hin
      subst hin
      rcases hrest with ⟨mode, _, size, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
      by_cases hsz : size = 0
      · obtain ⟨hin0, _⟩ := hsz0 hsz; rw [hin0] at hin_eq; cases hin_eq
      · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
        rcases hmd with rfl | rfl
        · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, inBid, _, _, inBlk, _, hinw, _, _, hin_b, hin_k, hin_p, _⟩
          rw [hinw] at hin_eq; cases hin_eq
          exact ⟨inBlk, hin_b, hin_k, hin_p⟩
        · rcases hwrite ⟨hpos, rfl⟩ with ⟨_, _, inBid, inBlk, hinw, hin_b, hin_k, hin_p, _⟩
          rw [hinw] at hin_eq; cases hin_eq
          exact ⟨inBlk, hin_b, hin_k, hin_p⟩
  · cases hout_eq : gw.out? with
    | none => simp [hout_eq] at hout
    | some ob =>
      rw [hout_eq] at hout
      simp only [Option.toList_some, List.mem_singleton] at hout
      subst hout
      rcases hrest with ⟨mode, _, size, _, direct, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
      by_cases hsz : size = 0
      · obtain ⟨_, hout0, _⟩ := hsz0 hsz; rw [hout0] at hout_eq; cases hout_eq
      · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
        rcases hmd with rfl | rfl
        · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, _, outBid, _, _, outBlk, _, houtw, _, _, _, _, _, _, _, hout_b, hout_k, hout_p, _⟩
          rw [houtw] at hout_eq; cases hout_eq
          exact ⟨outBlk, hout_b, hout_k, hout_p⟩
        · rcases hwrite ⟨hpos, rfl⟩ with ⟨hd, _, _, _, _, _, _, _, _, _, _, _, hd1, hd0⟩
          rcases hd with rfl | rfl
          · rcases hd0 rfl with ⟨outBid, _, outBlk, _, _, _, houtw, _, hout_b, hout_k, hout_p, _⟩
            rw [houtw] at hout_eq; cases hout_eq
            exact ⟨outBlk, hout_b, hout_k, hout_p⟩
          · rw [(hd1 rfl).1] at hout_eq; cases hout_eq
  · cases hs_eq : gw.stream? with
    | none => simp [hs_eq, GzWitness.streamOwnedList] at hstrm
    | some s =>
      rw [hs_eq] at hstrm
      cases s with
      | inl iw =>
        rcases hrest with ⟨mode, _, size, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
        by_cases hsz : size = 0
        · obtain ⟨_, _, hs0, _⟩ := hsz0 hsz; rw [hs0] at hs_eq; cases hs_eq
        · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
          rcases hmd with rfl | rfl
          · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, _, _, iw', _, _, _, _, hstrw,
              _, _, _, _, _, _, _, _, _, _, _, _, hinf, _⟩
            rw [hstrw] at hs_eq; cases hs_eq
            exact InflateStateInv.owned_heap hinf x hstrm
          · rcases hwrite ⟨hpos, rfl⟩ with ⟨hd, _, _, _, _, _, _, _, _, _, _, _, hd1, hd0⟩
            rcases hd with rfl | rfl
            · rcases hd0 rfl with ⟨_, _, _, _, _, _, _, hstrw, _⟩; rw [hstrw] at hs_eq; cases hs_eq
            · rw [(hd1 rfl).2] at hs_eq; cases hs_eq
      | inr dw =>
        rcases hrest with ⟨mode, _, size, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hmd, _, _, _, _, _, _, _, hsz0, hread, hwrite⟩
        by_cases hsz : size = 0
        · obtain ⟨_, _, hs0, _⟩ := hsz0 hsz; rw [hs0] at hs_eq; cases hs_eq
        · have hpos : 0 < size := Nat.pos_of_ne_zero hsz
          rcases hmd with rfl | rfl
          · rcases hread ⟨hpos, rfl⟩ with ⟨_, _, _, _, _, iw', _, _, _, _, hstrw, _⟩; rw [hstrw] at hs_eq; cases hs_eq
          · rcases hwrite ⟨hpos, rfl⟩ with ⟨hd, _, _, _, _, _, _, _, _, _, _, _, hd1, hd0⟩
            rcases hd with rfl | rfl
            · rcases hd0 rfl with ⟨_, dw', _, _, _, _, _, hstrw, _, _, _, _, _, _, hdef, _⟩
              rw [hstrw] at hs_eq; cases hs_eq
              exact DeflateStateInv.owned_heap hdef x hstrm
            · rw [(hd1 rfl).2] at hs_eq; cases hs_eq

theorem GzStateInv.owned_heap {tags : TypeEnv} {gEnv : Env} {m : Mem} {gw : GzWitness}
    (h : GzStateInv tags gEnv m gw) :
    ∀ x ∈ gw.ownedList, ∃ blk, m.blocks x = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw :=
  GzStateInvCore.owned_heap h

private theorem nodup_append_disjoint {α : Type _} {l₁ l₂ : List α}
    (h : (l₁ ++ l₂).Nodup) : l₁.Nodup ∧ l₂.Nodup ∧ ∀ x, x ∈ l₁ → x ∉ l₂ := by
  induction l₁ with
  | nil => simp_all
  | cons a t ih =>
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or] at h
    rcases h with ⟨⟨hna1, hna2⟩, htail⟩
    obtain ⟨ht1, ht2, hdisj⟩ := ih htail
    refine ⟨List.nodup_cons.mpr ⟨hna1, ht1⟩, ht2, fun x hx => ?_⟩
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · exact hna2
    · exact hdisj x hxt

private theorem nodup_flatMap_distinct {α β : Type _} [DecidableEq α]
    {f : α → List β} {l : List α} (hl : l.Nodup) (hfm : (l.flatMap f).Nodup)
    {a₁ a₂ : α} (h1 : a₁ ∈ l) (h2 : a₂ ∈ l) (hne : a₁ ≠ a₂) :
    ∀ x, x ∈ f a₁ → x ∉ f a₂ := by
  induction l with
  | nil => cases h1
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons] at hfm
    obtain ⟨hfa, hft, hdisj⟩ := nodup_append_disjoint hfm
    simp only [List.mem_cons] at h1 h2
    rcases h1 with rfl | h1t <;> rcases h2 with rfl | h2t
    · exact absurd rfl hne
    · intro x hx
      have hin := hdisj x hx
      intro hx2
      exact hin (List.mem_flatMap.mpr ⟨a₂, h2t, hx2⟩)
    · intro x hx hx2
      have hin := hdisj x hx2
      exact hin (List.mem_flatMap.mpr ⟨a₁, h1t, hx⟩)
    · exact ih hl.2 hft h1t h2t

/-- Unified whole-library safety invariant across all 15 TUs.
Maintains `BaseInv`, static `InitLibzAllProps`, global `z_errmsg` / non-errno RO-global facts,
an exact bijection between `v.streams` / `v.gzFiles` and live owned heap witnesses whose
concatenated block list is duplicate-free (`Nodup`) and coincides with `owned`. -/
def ZlibInv (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (v : ClientView) (owned : BlockSet) (m : Mem) (os : OSState) : Prop :=
  BaseInv m0 os0 v owned m os ∧
  InitLibzAllProps prog gEnv m0 os0 ∧
  NonErrnoROGlobal os0.errnoBlk m0 ∧
  ZErrmsgReady prog.tags gEnv m0 ∧
  ∃ (streamWits : List (BlockId × StreamWit)) (gzWits : List GzWitness),
    streamWits.map (fun p => (p.1, p.2.kind)) = v.streams ∧
    gzWits.map GzWitness.gzBid = v.gzFiles ∧
    (v.streams.map Prod.fst).Nodup ∧
    (allOwnedList streamWits gzWits).Nodup ∧
    (∀ b, owned b ↔ b ∈ allOwnedList streamWits gzWits) ∧
    (∀ p ∈ streamWits, StreamStateInv prog.tags gEnv m p.1 p.2.kind p.2 ∧ ¬ owned p.1) ∧
    (∀ gw ∈ gzWits, GzStateInv prog.tags gEnv m gw) ∧
    (∀ b, os.strerrorBlk = some b →
      ¬ owned b ∧ (m0.blocks b).isNone = true ∧ b ≠ os.errnoBlk ∧
      ∃ blk, m.blocks b = some blk ∧ blk.kind = .global ∧ blk.perm = .ro)

theorem ZlibInv.toBaseInv {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) :
    BaseInv m0 os0 v owned m os := h.1

theorem ZlibInv.toAllProps {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) :
    InitLibzAllProps prog gEnv m0 os0 := h.2.1

theorem ZlibInv.toInitProps {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) :
    InitLibzProps prog gEnv m0 os0 := h.2.1.base

theorem ZlibInv.empty_owned {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) (hv : v.isEmpty) :
    ∀ b, ¬ owned b :=
  h.1.emptyNoOwned hv

theorem ZlibInv.zErrmsgReady {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) :
    ZErrmsgReady prog.tags gEnv m := by
  rcases h.2.2.2.1 with ⟨b, blk, hlu, hm0b, hperm, hkind, hsz, hal, hptrs⟩
  have hm_b : m.blocks b = some blk :=
    BaseInv.global_block_eq_of_m0_size_ne h.2.1.base h.1 hm0b (by rw [hsz]; decide)
  refine ⟨b, blk, hlu, hm_b, hperm, hkind, hsz, hal, fun i hi => ?_⟩
  rcases hptrs i hi with ⟨sb, sblk, len, hrd, hm0sb, hsperm, hskind, hstr⟩
  have hne : sb ≠ os0.errnoBlk := by
    intro heq
    subst heq
    rcases h.2.1.base.errno_blk with ⟨eblk, heblk, _, _, heperm, _⟩
    rw [hm0sb] at heblk; cases heblk
    rw [hsperm] at heperm; cases heperm
  have hm_sb : m.blocks sb = some sblk := by
    rw [h.1.roGlobals sb (by simp [hm0sb]) hne, hm0sb]
  refine ⟨sb, sblk, len, ?_, hm_sb, hsperm, hskind, strlenAt_congr_block (hm_sb.trans hm0sb.symm) hstr⟩
  rw [readVal_eq_of_blocks_eq prog.tags (hm_b.trans hm0b.symm)]
  exact hrd

theorem ZlibInv.owned_heap_not_m0 {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) {b : BlockId} (hb : owned b) :
    (∃ blk, m.blocks b = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw) ∧
    (m0.blocks b).isNone = true ∧ b ≠ os0.errnoBlk := by
  rcases h with ⟨hbase, hall, hnon, _, streamWits, gzWits, _, _, _, _, hown, hst, hgz, _⟩
  have hin : b ∈ allOwnedList streamWits gzWits := (hown b).mp hb
  have hheap : ∃ blk, m.blocks b = some blk ∧ blk.kind = .heap ∧ blk.perm = .rw := by
    simp only [allOwnedList, List.mem_append, List.mem_flatMap] at hin
    rcases hin with ⟨p, hp, hbp⟩ | ⟨gw, hg, hbg⟩
    · exact StreamStateInv.owned_heap (hst p hp).1 b hbp
    · exact GzStateInv.owned_heap (hgz gw hg) b hbg
  rcases hheap with ⟨blk, hm_b, hk, hp⟩
  have hne_err : b ≠ os0.errnoBlk := by
    intro heq
    subst heq
    rcases hbase.errnoValid with ⟨eblk, heblk, _, _, _, hek⟩
    rw [hbase.errnoBlkEq] at heblk
    rw [hm_b] at heblk; cases heblk
    rw [hk] at hek; cases hek
  have hm0_none : (m0.blocks b).isNone = true := by
    cases hm0 : m0.blocks b with
    | none => rfl
    | some m0blk =>
      exfalso
      obtain ⟨_, hm0k⟩ := hnon b m0blk hm0 hne_err
      have hsame := hbase.roGlobals b (by simp [hm0]) hne_err
      rw [hm0, hm_b] at hsame; cases hsame
      rw [hk] at hm0k; cases hm0k
  exact ⟨⟨blk, hm_b, hk, hp⟩, hm0_none, hne_err⟩

private theorem nodup_of_map_nodup {α β : Type _} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    exact List.nodup_cons.mpr ⟨fun hat => h.1 ⟨a, hat, rfl⟩, nodup_of_map_nodup f h.2⟩

private theorem gzBid_map_nodup_of_owned :
    ∀ {l : List GzWitness}, (l.flatMap GzWitness.ownedList).Nodup → (l.map GzWitness.gzBid).Nodup
  | [], _ => List.nodup_nil
  | g :: t, h => by
    rw [List.flatMap_cons] at h
    obtain ⟨_, htflat, hdisj_gt⟩ := nodup_append_disjoint h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, gzBid_map_nodup_of_owned htflat⟩
    rintro ⟨g', hg't, hbid⟩
    have hmem1 : g.gzBid ∈ g.ownedList := by simp [GzWitness.ownedList]
    have hmem2 : g'.gzBid ∈ t.flatMap GzWitness.ownedList :=
      List.mem_flatMap.mpr ⟨g', hg't, by simp [GzWitness.ownedList]⟩
    rw [hbid] at hmem2
    exact hdisj_gt g.gzBid hmem1 hmem2

theorem ZlibInv.stream_gz_nodup_disjoint {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) :
    ∃ (streamWits : List (BlockId × StreamWit)) (gzWits : List GzWitness),
      streamWits.map (fun p => (p.1, p.2.kind)) = v.streams ∧
      gzWits.map GzWitness.gzBid = v.gzFiles ∧
      streamWits.Nodup ∧
      gzWits.Nodup ∧
      (∀ p₁ ∈ streamWits, ∀ p₂ ∈ streamWits, p₁ ≠ p₂ →
        ∀ x, x ∈ p₁.2.ownedList → x ∉ p₂.2.ownedList) ∧
      (∀ gw₁ ∈ gzWits, ∀ gw₂ ∈ gzWits, gw₁ ≠ gw₂ →
        ∀ x, x ∈ gw₁.ownedList → x ∉ gw₂.ownedList) ∧
      (∀ p ∈ streamWits, ∀ gw ∈ gzWits, ∀ x, x ∈ p.2.ownedList → x ∉ gw.ownedList) := by
  rcases h with ⟨_, _, _, _, streamWits, gzWits, hms, hmg, hnd_v, hnd_all, _, _, _⟩
  obtain ⟨hnd_sflat, hnd_gflat, hdisj_sg⟩ := nodup_append_disjoint hnd_all
  have hnd_sfst : (streamWits.map Prod.fst).Nodup := by
    have heq : streamWits.map Prod.fst = v.streams.map Prod.fst := by
      rw [← hms, List.map_map]; rfl
    rw [heq]; exact hnd_v
  have hnd_sw : streamWits.Nodup := nodup_of_map_nodup Prod.fst hnd_sfst
  have hnd_gw : gzWits.Nodup := nodup_of_map_nodup GzWitness.gzBid (gzBid_map_nodup_of_owned hnd_gflat)
  refine ⟨streamWits, gzWits, hms, hmg, hnd_sw, hnd_gw, ?_, ?_, ?_⟩
  · exact fun p₁ hp₁ p₂ hp₂ hne => nodup_flatMap_distinct hnd_sw hnd_sflat hp₁ hp₂ hne
  · exact fun gw₁ hg₁ gw₂ hg₂ hne => nodup_flatMap_distinct hnd_gw hnd_gflat hg₁ hg₂ hne
  · exact fun p hp gw hg x hx1 hx2 =>
      hdisj_sg x (List.mem_flatMap.mpr ⟨p, hp, hx1⟩) (List.mem_flatMap.mpr ⟨gw, hg, hx2⟩)

theorem ZlibInv.init {globBase staticBase strBase : Nat → UInt64} {errnoBase : UInt64}
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (hinit : initLibz globBase staticBase strBase errnoBase = some (prog, gEnv, m0, os0)) :
    ZlibInv prog gEnv m0 os0 ClientView.empty (fun _ => False) m0 os0 := by
  have hall := initLibz_allProps hinit
  refine ⟨BaseInv.init hall.base, hall, initLibz_nonErrnoROGlobal hinit,
    zErrmsgReady_of_initLibz hinit, [], [], rfl, rfl, List.nodup_nil, ?_,
    ?_, (fun _ hmem => by cases hmem), (fun _ hmem => by cases hmem),
    (fun _ hb => by rw [hall.base.strerror_none] at hb; cases hb)⟩
  · simp [allOwnedList]
  · intro b
    simp [allOwnedList]

theorem ZlibInv.clientFrame {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m m' : Mem} {os os' : OSState}
    (hinv : ZlibInv prog gEnv m0 os0 v owned m os)
    (hcf : ClientFrame prog.tags m0 v owned m m' os os') :
    ZlibInv prog gEnv m0 os0 v owned m' os' := by
  rcases hinv with ⟨hbase, hall, hnon, hze0, streamWits, gzWits,
    hms, hmg, hnd_v, hnd_all, hown, hst, hgz, hstr⟩
  have hroG : ∀ b blk, m.blocks b = some blk → blk.kind = .global → blk.perm = .ro →
      m'.blocks b = m.blocks b := by
    intro b blk hmb hbk hbp
    exact hcf.2.2.1 b (Or.inr (Or.inr (Or.inr (Or.inr ⟨blk, hmb, hbk, hbp⟩))))
  refine ⟨BaseInv.clientFrame hbase hcf, hall, hnon, hze0, streamWits, gzWits,
    hms, hmg, hnd_v, hnd_all, hown, ?_, ?_, ?_⟩
  · intro p hp
    rcases hst p hp with ⟨hss, hnotown⟩
    refine ⟨?_, hnotown⟩
    have hvmem : (p.1, p.2.kind) ∈ v.streams := by
      rw [← hms]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hcf_s := hcf.2.2.2 p.1 p.2.kind hvmem
    have hsa : readField? prog.tags m' (.ptr p.1 0) "z_stream_s" "state" =
                 readField? prog.tags m (.ptr p.1 0) "z_stream_s" "state" ∧
               readField? prog.tags m' (.ptr p.1 0) "z_stream_s" "zalloc" =
                 readField? prog.tags m (.ptr p.1 0) "z_stream_s" "zalloc" ∧
               readField? prog.tags m' (.ptr p.1 0) "z_stream_s" "zfree" =
                 readField? prog.tags m (.ptr p.1 0) "z_stream_s" "zfree" ∧
               readField? prog.tags m' (.ptr p.1 0) "z_stream_s" "opaque" =
                 readField? prog.tags m (.ptr p.1 0) "z_stream_s" "opaque" :=
      ⟨hcf_s.1 "state" (by simp), hcf_s.1 "zalloc" (by simp),
       hcf_s.1 "zfree" (by simp), hcf_s.1 "opaque" (by simp)⟩
    have hpres : ∀ b, b ∈ p.2.ownedList → m'.blocks b = m.blocks b := by
      intro b hb
      exact hcf.2.2.1 b (Or.inl ((hown b).mpr (mem_allOwnedList_of_stream hp hb)))
    rcases p with ⟨sb, sw⟩
    cases sw with
    | deflate dw =>
      exact DeflateStateInv.congr_blocks hpres
        ⟨hsa.1, hsa.2.1, hsa.2.2.1, hsa.2.2.2, hcf_s.1 "adler" (by simp)⟩ hss
    | inflate iw =>
      exact InflateStateInv.congr_blocks rfl hpres hsa hroG hss
    | inflateBack ibw =>
      dsimp only [StreamStateInv] at hss ⊢
      have hwin' : Writable m' (.ptr ibw.winBid ibw.winOff) (2 ^ ibw.wbits) := by
        have hw := hcf_s.2 rfl
        rcases hss with ⟨_, _, _, _, _, _, hst_f, _, _, _, hwin_f, _, hws_f, _⟩
        dsimp only at hw
        rw [hst_f, Option.getD_some, hwin_f, Option.getD_some, hws_f, Option.getD_some] at hw
        exact hw
      exact InflateBackInv.congr_blocks
        (hpres ibw.stBid (by simp [StreamWit.ownedList, InflateBackWitness.ownedList])) hwin' hsa hss
  · intro gw hg
    refine GzStateInv.congr_blocks ?_ hroG (hgz gw hg)
    intro b hb
    exact hcf.2.2.1 b (Or.inl ((hown b).mpr (mem_allOwnedList_of_gz hg hb)))
  · intro b hb
    rw [hcf.2.1] at hb
    obtain ⟨hno, hm0b, hne, blk, hblk, hgk, hgp⟩ := hstr b hb
    refine ⟨hno, hm0b, by rw [hcf.1]; exact hne, blk, ?_, hgk, hgp⟩
    rw [hcf.2.2.1 b (Or.inr (Or.inr (Or.inl hb)))]
    exact hblk

theorem ZlibInv.roExt {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m m' : Mem} {os : OSState}
    (hinv : ZlibInv prog gEnv m0 os0 v owned m os)
    (hro : C99.Proof.ROExt m m') :
    ZlibInv prog gEnv m0 os0 v owned m' os := by
  rcases hinv with ⟨hbase, hall, hnon, hze0, streamWits, gzWits,
    hms, hmg, hnd_v, hnd_all, hown, hst, hgz, hstr⟩
  refine ⟨BaseInv.roExt hbase hro, hall, hnon, hze0, streamWits, gzWits,
    hms, hmg, hnd_v, hnd_all, hown, ?_, ?_, ?_⟩
  · intro p hp
    rcases hst p hp with ⟨hss, hnotown⟩
    refine ⟨?_, hnotown⟩
    have hst_mem : p.2.stBid ∈ p.2.ownedList := p.2.stBid_mem_ownedList
    have hown_st : owned p.2.stBid := (hown _).mpr (mem_allOwnedList_of_stream hp hst_mem)
    have hne : p.1 ≠ p.2.stBid := fun heq => hnotown (heq ▸ hown_st)
    have hsb_blk : (m.blocks p.1).isSome = true := by
      rcases readField?_ptr_ne_some_blk hne hss.state_eq with ⟨blk, hblk⟩
      simp [hblk]
    rcases p with ⟨sb, sw⟩
    cases sw with
    | deflate dw => exact DeflateStateInv.roExt rfl hsb_blk hro hss
    | inflate iw => exact InflateStateInv.roExt rfl hsb_blk hro hss
    | inflateBack ibw => exact InflateBackInv.roExt rfl hsb_blk hro hss
  · intro gw hg
    exact GzStateInv.roExt hro (hgz gw hg)
  · intro b hb
    obtain ⟨hno, hm0b, hne, blk, hblk, hgk, hgp⟩ := hstr b hb
    refine ⟨hno, hm0b, hne, blk, ?_, hgk, hgp⟩
    rw [hro.2.1 b (mem_lt_nextBlock hblk)]
    exact hblk

theorem ZlibInv.strerrorValid {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (hinv : ZlibInv prog gEnv m0 os0 v owned m os)
    {b : BlockId} (hb : os.strerrorBlk = some b) :
    ¬ owned b ∧ (m0.blocks b).isNone = true ∧ b ≠ os.errnoBlk ∧
    ∃ blk, m.blocks b = some blk ∧ blk.kind = .global ∧ blk.perm = .ro :=
  hinv.2.2.2.2.choose_spec.choose_spec.2.2.2.2.2.2.2 b hb

/-! ## 5. Conditional-Termination `WPSafe`, `ZlibInv_to_ContractSafe`, & Lifted Wave 1 Proofs -/

def readBudgetIsSome : Sem.RunState → Prop
  | .running _ _ _ _ os _ => os.readBudget.isSome = true
  | .returned _ _ os => os.readBudget.isSome = true
  | .ub => False

theorem star_destr {α : Type} {R : α → α → Prop} {x z : α}
    (h : Sem.Star R x z) : x = z ∨ ∃ y, R x y ∧ Sem.Star R y z := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hxy hyz ih =>
    rcases ih with rfl | ⟨w, hxw, hwy⟩
    · exact Or.inr ⟨_, hyz, .refl _⟩
    · exact Or.inr ⟨w, hxw, .tail hwy hyz⟩

theorem safe_of_step {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {s : Sem.RunState} (hnub : ¬ s.isUB)
    (hnext : ∀ s', Sem.Step prog cfg ext s s' → Sem.Safe prog cfg ext s') :
    Sem.Safe prog cfg ext s := by
  intro s' hstar
  rcases star_destr hstar with rfl | ⟨s1, hstep, htail⟩
  · exact hnub
  · exact hnext s1 hstep s' htail

/-- Safety and postcondition invariance for arbitrary (possibly unbounded when
`os.readBudget = none`) C executions, strengthening to terminating `WPTerm` whenever
`os.readBudget.isSome = true`. -/
def WPSafe (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (s : Sem.RunState) : Prop :=
  Sem.Safe prog cfg ext s ∧
  (readBudgetIsSome s → C99.Proof.WPTerm prog cfg ext Q s) ∧
  (∀ ret m' os', Sem.Star (Sem.Step prog cfg ext) s (.returned ret m' os') → Q ret m' os')

theorem WPSafe.safe {prog cfg ext Q s} (h : WPSafe prog cfg ext Q s) :
    Sem.Safe prog cfg ext s := h.1

theorem WPSafe.terminatesSafely {prog cfg ext Q s} (h : WPSafe prog cfg ext Q s)
    (hb : readBudgetIsSome s) : Sem.TerminatesSafely prog cfg ext s :=
  (h.2.1 hb).terminatesSafely

theorem WPSafe.post {prog cfg ext Q s ret m' os'} (h : WPSafe prog cfg ext Q s)
    (hstar : Sem.Star (Sem.Step prog cfg ext) s (.returned ret m' os')) :
    Q ret m' os' :=
  h.2.2 ret m' os' hstar

theorem WPSafe.of_wpTerm {prog cfg ext Q s} (hw : C99.Proof.WPTerm prog cfg ext Q s) :
    WPSafe prog cfg ext Q s :=
  ⟨hw.safe, fun _ => hw, fun _ _ _ h => hw.post h⟩

theorem WPSafe.returned {prog cfg ext Q ret m os} (hq : Q ret m os) :
    WPSafe prog cfg ext Q (.returned ret m os) :=
  WPSafe.of_wpTerm (C99.Proof.WPTerm.returned hq)

theorem WPSafe.mono {prog cfg ext Q1 Q2 s}
    (hm : ∀ v m os, Q1 v m os → Q2 v m os) (hw : WPSafe prog cfg ext Q1 s) :
    WPSafe prog cfg ext Q2 s :=
  ⟨hw.1, fun hb => (hw.2.1 hb).mono hm, fun v m os hst => hm v m os (hw.2.2 v m os hst)⟩

private def detStepBudget : Sem.DetStep → Prop
  | .next s' => readBudgetIsSome s'
  | .allocStr _ _ _ _ _ _ _ os' _ => os'.readBudget.isSome = true
  | .allocLocal _ _ _ _ _ _ os' _ => os'.readBudget.isSome = true
  | .callFn _ _ _ _ _ _ _ _ os' _ => os'.readBudget.isSome = true

private theorem stepDet_preserves_budget {prog : Prog} {cfg : PointerConfig}
    {s : Sem.RunState} {d : Sem.DetStep}
    (hd : Sem.stepDet prog cfg s = some d) (hb : readBudgetIsSome s) :
    detStepBudget d := by
  cases s with
  | ub => cases hd
  | returned _ _ _ => cases hd
  | running ctrl env blks m os k =>
    dsimp only [readBudgetIsSome] at hb
    unfold Sem.stepDet at hd
    cases ctrl with
    | expr es ctx mods =>
      cases es with
      | eval w e fs =>
        cases w with
        | lval =>
          dsimp only at hd
          rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩
          exact hb
        | rval =>
          cases e <;> dsimp only at hd
          all_goals
            first
            | (cases hd; exact hb)
            | (rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb)
      | ret rv fs =>
        cases rv with
        | lval _ _ _ | structVal _ _ =>
          cases fs with
          | nil =>
            dsimp only at hd
            cases ctx <;> dsimp only [bind, Option.bind] at hd <;> try cases hd
            · exact hb
            · exact hb
            · split <;> exact hb
          | cons f rest =>
            cases f <;> dsimp only at hd <;>
              (rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb)
        | rval v ty =>
          cases v with
          | fnPtr sym =>
            cases fs with
            | nil =>
              dsimp only at hd
              cases ctx <;> dsimp only [bind, Option.bind] at hd
              · cases hd; exact hb
              · split at hd
                · cases hd; cases Sem.unwindReturn m blks k <;> exact hb
                · cases hcv : Sem.castVal m k.topRetTy (.fnPtr sym) <;>
                    simp only [hcv, Option.map_none, Option.map_some, Option.some.injEq] at hd
                  · cases hd
                  · subst hd; cases Sem.unwindReturn m blks k <;> exact hb
              · cases hd; exact hb
              · cases hit : Sem.isTruthy (.fnPtr sym) <;>
                  simp only [hit, Option.map_none, Option.map_some, Option.some.injEq] at hd
                · cases hd
                · subst hd; exact hb
              · cases hit : Sem.isTruthy (.fnPtr sym) <;>
                  simp only [hit, Option.map_none, Option.map_some, Option.some.injEq] at hd
                · cases hd
                · subst hd; split <;> exact hb
              · cases hit : Sem.isTruthy (.fnPtr sym) <;>
                  simp only [hit, Option.map_none, Option.map_some, Option.some.injEq] at hd
                · cases hd
                · subst hd; split <;> exact hb
              · cases hit : Sem.isTruthy (.fnPtr sym) <;>
                  simp only [hit, Option.map_none, Option.map_some, Option.some.injEq] at hd
                · cases hd
                · subst hd; split <;> exact hb
              · cases hd; split <;> exact hb
              · cases hvi : Sem.valAsInt? (.fnPtr sym) <;>
                  simp only [hvi, Option.map_none, Option.map_some, Option.some.injEq] at hd
                · cases hd
                · subst hd; split <;> exact hb
            | cons f rest =>
              cases f with
              | callFnF args =>
                cases args with
                | nil => dsimp only at hd; cases hd; exact hb
                | cons _ _ =>
                  dsimp only at hd
                  rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb
              | callArgF _ _ _ todo =>
                cases todo with
                | nil => dsimp only at hd; cases hd; exact hb
                | cons _ _ =>
                  dsimp only at hd
                  rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb
              | _ =>
                dsimp only at hd
                rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb
          | _ =>
            cases fs with
            | nil =>
              dsimp only at hd
              cases ctx <;> dsimp only [bind, Option.bind] at hd
              · cases hd; exact hb
              · split at hd
                · cases hd; cases Sem.unwindReturn m blks k <;> exact hb
                · rcases Option.map_eq_some_iff.mp hd with ⟨cv, _, rfl⟩
                  cases Sem.unwindReturn m blks k <;> exact hb
              · cases hd; exact hb
              · rcases Option.map_eq_some_iff.mp hd with ⟨b, _, rfl⟩; exact hb
              · rcases Option.map_eq_some_iff.mp hd with ⟨b, _, rfl⟩; split <;> exact hb
              · rcases Option.map_eq_some_iff.mp hd with ⟨b, _, rfl⟩; split <;> exact hb
              · rcases Option.map_eq_some_iff.mp hd with ⟨b, _, rfl⟩; split <;> exact hb
              · cases hd; split <;> exact hb
              · rcases Option.map_eq_some_iff.mp hd with ⟨_, _, rfl⟩; split <;> exact hb
            | cons f rest =>
              cases f with
              | callArgF _ _ _ todo =>
                cases todo with
                | nil => dsimp only at hd; cases hd; exact hb
                | cons _ _ =>
                  dsimp only at hd
                  rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb
              | _ =>
                dsimp only at hd
                rcases Option.map_eq_some_iff.mp hd with ⟨⟨_, _, _⟩, _, rfl⟩; exact hb
    | stmt st =>
      cases st with
      | nop =>
        cases k with
        | stmts ss _ => cases ss <;> cases hd <;> exact hb
        | blockEnd _ _ _ | switchCont _ | callFrame _ _ _ _ _ _ _ => cases hd; exact hb
        | loop c? stp? body isDo rest =>
          cases hd
          dsimp only [detStepBudget]
          unfold Sem.loopNext
          split <;> exact hb
        | stop rt =>
          cases hd; exact hb
      | expr _ | decl _ => cases hd; exact hb
      | decls ds =>
        cases ds with
        | nil => cases hd; exact hb
        | cons d rest =>
          dsimp only at hd
          split at hd
          · cases hd; exact hb
          · split at hd
            · cases hd; exact hb
            · cases hd; exact hb
            · cases hd
      | block ss => cases ss <;> cases hd <;> exact hb
      | ifStmt _ _ _ | whileStmt _ _ | doWhileStmt _ _
      | switchStmt _ _ | caseStmt _ _ | defaultStmt _ | labelStmt _ _ => cases hd; exact hb
      | forStmt init? c? stp? body =>
        cases init? with
        | some _ => cases hd; exact hb
        | none => cases c? <;> cases hd <;> exact hb
      | breakStmt =>
        dsimp only at hd
        rcases Option.map_eq_some_iff.mp hd with ⟨p, _, rfl⟩; exact hb
      | continueStmt =>
        dsimp only at hd
        rcases Option.map_eq_some_iff.mp hd with ⟨p, _, rfl⟩
        dsimp only [detStepBudget]
        unfold Sem.loopNext
        split <;> exact hb
      | gotoStmt _ =>
        dsimp only at hd
        rcases Option.map_eq_some_iff.mp hd with ⟨p, _, rfl⟩; exact hb
      | returnStmt e? =>
        cases e? with
        | some _ => cases hd; exact hb
        | none =>
          dsimp only at hd
          split at hd
          · cases hd; cases Sem.unwindReturn m blks k <;> exact hb
          · cases hd

private theorem stepDet_next_readBudget {prog : Prog} {cfg : PointerConfig}
    {s s' : Sem.RunState} (hd : Sem.stepDet prog cfg s = some (.next s')) :
    readBudgetIsSome s → readBudgetIsSome s' :=
  stepDet_preserves_budget hd

theorem WPSafe.of_det_state {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s s' : Sem.RunState}
    (hd : Sem.stepDet prog cfg s = some (.next s'))
    (hw : WPSafe prog cfg ext Q s') :
    WPSafe prog cfg ext Q s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  have hstepInv : ∀ s1, Sem.Step prog cfg ext s s1 → s1 = s' := by
    intro s1 hs1
    cases hs1 with
    | det hd' => rw [hd] at hd'; cases hd'; rfl
    | det_ub hd' => rw [hd] at hd'; cases hd'
    | strLit hd' | localDecl hd' | localDecl_ub hd'
    | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
      rw [hd] at hd'; cases hd'
  refine ⟨safe_of_step hnub (fun s1 hs1 => (hstepInv s1 hs1) ▸ hw.1), ?_, ?_⟩
  · intro hb
    exact C99.Proof.WPTerm.of_det_state hd (hw.2.1 (stepDet_next_readBudget hd hb))
  · intro ret m' os' hstar
    rcases star_destr hstar with rfl | ⟨s1, hs1, htail⟩
    · cases hd
    · rw [hstepInv s1 hs1] at htail
      exact hw.2.2 ret m' os' htail

theorem WPSafe.of_det {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ctrl : Sem.Control} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {s' : Sem.RunState}
    (hd : Sem.stepDet prog cfg (.running ctrl env blks m os k) = some (.next s'))
    (hw : WPSafe prog cfg ext Q s') :
    WPSafe prog cfg ext Q (.running ctrl env blks m os k) :=
  WPSafe.of_det_state hd hw

theorem WPSafe.of_exprPure {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {es es' : Sem.ExprState} {ctx : Sem.ExprCtx} {mods mods' : ModSet}
    {env : Env} {blks : List BlockId} {m m' : Mem} {os : OSState} {k : Sem.Cont}
    (h : Sem.stepExprPure prog cfg env m mods es = some (es', m', mods'))
    (hw : WPSafe prog cfg ext Q (.running (.expr es' ctx mods') env blks m' os k)) :
    WPSafe prog cfg ext Q (.running (.expr es ctx mods) env blks m os k) :=
  WPSafe.of_det (C99.Proof.stepDet_exprPure h) hw

theorem WPSafe.of_strLit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : Sem.RunState}
    {str : String} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocStr str fs ctx mods env blks m os k))
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (hw : ∀ (base : UInt64) (bid : BlockId) (m' : Mem),
      m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') →
      WPSafe prog cfg ext Q
        (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods)
          env blks m' os k)) :
    WPSafe prog cfg ext Q s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  have hstep : ∀ s', Sem.Step prog cfg ext s s' → WPSafe prog cfg ext Q s' := by
    intro s' hs'
    cases hs' with
    | strLit hd' _ halloc' => rw [hd] at hd'; cases hd'; exact hw _ _ _ halloc'
    | det hd' | det_ub hd' | localDecl hd' | localDecl_ub hd'
    | call_internal hd' | call_internal_ub hd' | call_ext hd' | call_ext_ub hd' =>
      rw [hd] at hd'; cases hd'
  refine ⟨safe_of_step hnub (fun s' hs' => (hstep s' hs').1), ?_, ?_⟩
  · intro hb
    have hbud : os.readBudget.isSome = true := stepDet_preserves_budget hd hb
    exact C99.Proof.WPTerm.of_strLit hd hsz (fun base bid m' halloc => (hw base bid m' halloc).2.1 hbud)
  · intro ret m' os' hstar
    rcases star_destr hstar with rfl | ⟨s1, hs1, htail⟩
    · cases hd
    · exact (hstep s1 hs1).2.2 ret m' os' htail

theorem WPSafe.of_call_internal {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : Sem.RunState}
    {sym : String} {fnTy : CTy} {fn : FnDef} {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Sem.Cont}
    (hd : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
    (hwit : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv0, callBlks0, m0'))
    (hw : ∀ base callEnv callBlks m',
      Sem.pushCallParams prog.tags m base 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv, callBlks, m') →
      os.readBudget = os.readBudget →
      WPSafe prog cfg ext Q
        (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k)))
    (hos_bud : readBudgetIsSome s → os.readBudget.isSome = true) :
    WPSafe prog cfg ext Q s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  obtain ⟨callEnv0, callBlks0, m0', hpush0⟩ := hwit
  have hstep : ∀ s', Sem.Step prog cfg ext s s' → WPSafe prog cfg ext Q s' := by
    intro s' hs'
    cases hs' with
    | call_internal hd' hfn' hcoerce' hpush' =>
      rw [hd] at hd'; cases hd'
      rw [hfn] at hfn'; cases hfn'
      rw [hcoerce] at hcoerce'; cases hcoerce'
      exact hw _ _ _ _ hpush' rfl
    | call_internal_ub hd' hfn' hbad =>
      rw [hd] at hd'; cases hd'
      rw [hfn] at hfn'; cases hfn'
      exact False.elim (hbad coerced (fun _ => 0) callEnv0 callBlks0 m0' hcoerce hpush0)
    | call_ext hd' hnfn' | call_ext_ub hd' hnfn' =>
      rw [hd] at hd'; cases hd'; rw [hfn] at hnfn'; cases hnfn'
    | det hd' | det_ub hd' | strLit hd' | localDecl hd' | localDecl_ub hd' =>
      rw [hd] at hd'; cases hd'
  refine ⟨safe_of_step hnub (fun s' hs' => (hstep s' hs').1), ?_, ?_⟩
  · intro hb
    exact C99.Proof.WPTerm.of_call_internal hd hfn hcoerce ⟨callEnv0, callBlks0, m0', hpush0⟩
      (fun base ce cb m' hp => (hw base ce cb m' hp rfl).2.1 (hos_bud hb))
  · intro ret m' os' hstar
    rcases star_destr hstar with rfl | ⟨s1, hs1, htail⟩
    · cases hd
    · exact (hstep s1 hs1).2.2 ret m' os' htail

theorem WPSafe.of_call_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {s : Sem.RunState}
    {sym : String} {fnTy retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Sem.Cont}
    (hd : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hnfn : prog.fns sym = none)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hnoub : ¬ ext sym coerced m os .ub)
    (hw : ∀ ret m' os', ext sym coerced m os (.ok ret m' os') →
      WPSafe prog cfg ext Q (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k))
    (hterm : readBudgetIsSome s →
      (∃ ret m' os', ext sym coerced m os (.ok ret m' os')) ∧
      ∀ ret m' os', ext sym coerced m os (.ok ret m' os') →
        C99.Proof.WPTerm prog cfg ext Q
          (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    WPSafe prog cfg ext Q s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  have hstep : ∀ s', Sem.Step prog cfg ext s s' → WPSafe prog cfg ext Q s' := by
    intro s' hs'
    cases hs' with
    | call_ext hd' hnfn' hsig' hcoerce' hext =>
      rw [hd] at hd'; cases hd'
      rw [hsig] at hsig'; cases hsig'
      rw [hcoerce] at hcoerce'; cases hcoerce'
      rename_i out'
      cases out' with
      | ub => exact False.elim (hnoub hext)
      | ok ret m' os' => exact hw ret m' os' hext
    | call_ext_ub hd' _ hbad =>
      rw [hd] at hd'; cases hd'
      exact False.elim (hbad ⟨retTy, paramTys, variadic, coerced, hsig, hcoerce⟩)
    | call_internal hd' hfn' | call_internal_ub hd' hfn' =>
      rw [hd] at hd'; cases hd'; rw [hnfn] at hfn'; cases hfn'
    | det hd' | det_ub hd' | strLit hd' | localDecl hd' | localDecl_ub hd' =>
      rw [hd] at hd'; cases hd'
  refine ⟨safe_of_step hnub (fun s' hs' => (hstep s' hs').1), ?_, ?_⟩
  · intro hb
    obtain ⟨hex, ht⟩ := hterm hb
    exact C99.Proof.WPTerm.of_call_ext hd hnfn hsig hcoerce hex hnoub ht
  · intro ret m' os' hstar
    rcases star_destr hstar with rfl | ⟨s1, hs1, htail⟩
    · cases hd
    · exact (hstep s1 hs1).2.2 ret m' os' htail

theorem WPSafe.of_inv {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {I : Sem.RunState → Prop} {s0 : Sem.RunState}
    (h0 : I s0)
    (hsafe : ∀ s, I s → ¬ s.isUB ∧
      (∀ ret m os, s = .returned ret m os → Q ret m os) ∧
      (∀ s', Sem.Step prog cfg ext s s' →
        I s' ∨ (Sem.Safe prog cfg ext s' ∧
          ∀ ret m os, Sem.Star (Sem.Step prog cfg ext) s' (.returned ret m os) → Q ret m os)))
    (hterm : readBudgetIsSome s0 → C99.Proof.WPTerm prog cfg ext Q s0) :
    WPSafe prog cfg ext Q s0 := by
  let TailOK : Sem.RunState → Prop := fun s =>
    Sem.Safe prog cfg ext s ∧
    ∀ ret m os, Sem.Star (Sem.Step prog cfg ext) s (.returned ret m os) → Q ret m os
  have hstarInv : ∀ s', Sem.Star (Sem.Step prog cfg ext) s0 s' → I s' ∨ TailOK s' := by
    intro s' hstar
    induction hstar with
    | refl => exact Or.inl h0
    | tail _ hstep ih =>
      rcases ih with hi | hok
      · exact (hsafe _ hi).2.2 _ hstep
      · refine Or.inr ⟨fun s'' hst'' => hok.1 s'' (C99.Proof.star_head hstep hst''),
          fun ret m os hst'' => hok.2 ret m os (C99.Proof.star_head hstep hst'')⟩
  refine ⟨fun s' hstar => ?_, hterm, fun ret m' os' hstar => ?_⟩
  · rcases hstarInv s' hstar with hi | hok
    · exact (hsafe s' hi).1
    · exact hok.1 s' (.refl s')
  · rcases hstarInv (.returned ret m' os') hstar with hi | hok
    · exact (hsafe _ hi).2.1 ret m' os' rfl
    · exact hok.2 ret m' os' (.refl _)

private theorem simple_cast_ok {ty : CTy} (h : IsSimpleParamTy ty) :
    match ty.unqual with
    | .void | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ | .vaList => True
    | _ => False := by
  rcases isSimpleParamTy_iff.mp h with ⟨k, hk⟩ | ⟨el, hel⟩
  · simp [hk]
  · simp [hel]

private theorem map_unqual_len {a b : List CTy}
    (h : a.map CTy.unqual = b.map CTy.unqual) : a.length = b.length := by
  have := congrArg List.length h
  simpa using this

private theorem args_map_void_rev (args : List Val) :
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

private theorem callState_stepDet_callFn
    {prog : Prog} {gEnv : Env} {m : Mem} {os : OSState} {fnName : String}
    {args : List Val} {s0 : Sem.RunState}
    {protoRetTy : CTy} {protoParamTys : List CTy} {variadic : Bool}
    (hproto : prog.fnProtos fnName = some (protoRetTy, protoParamTys, variadic))
    (hcs : Zlib.Spec.callState prog gEnv m os fnName args = some s0) :
    Sem.stepDet prog Zlib.Spec.zlibPointerConfig s0 =
      some (.callFn fnName (CTy.fnPtr protoRetTy protoParamTys variadic)
        (args.map (fun v => (v, CTy.void))) [] .returnVal gEnv [] m os (.stop protoRetTy)) := by
  unfold Zlib.Spec.callState at hcs
  simp only [hproto, bind, Option.bind, pure, Pure.pure] at hcs
  have hm := args_map_void_rev args
  cases hr : args.reverse with
  | nil =>
    simp only [hr] at hcs hm
    cases hcs
    rw [hm]
    rfl
  | cons last revInit =>
    simp only [hr] at hcs hm
    cases hcs
    rw [← hm]
    unfold Sem.stepDet
    simp only []

private theorem callState_readBudgetIsSome_iff
    {prog : Prog} {gEnv : Env} {m : Mem} {os : OSState} {fnName : String}
    {args : List Val} {s0 : Sem.RunState}
    {protoRetTy : CTy} {protoParamTys : List CTy} {variadic : Bool}
    (hproto : prog.fnProtos fnName = some (protoRetTy, protoParamTys, variadic))
    (hcs : Zlib.Spec.callState prog gEnv m os fnName args = some s0) :
    readBudgetIsSome s0 ↔ os.readBudget.isSome = true := by
  unfold Zlib.Spec.callState at hcs
  simp only [hproto, bind, Option.bind, pure, Pure.pure] at hcs
  cases hr : args.reverse with
  | nil => simp only [hr] at hcs; cases hcs; rfl
  | cons _ _ => simp only [hr] at hcs; cases hcs; rfl

theorem coerceCallArgs_variadic_of_argsWellTyped
    {m : Mem} {ptys cParamTys : List CTy} {args : List Val}
    (hmap : ptys.map CTy.unqual = cParamTys.map CTy.unqual)
    (hawt : ArgsHaveCTy cParamTys true args)
    (htys : ∀ p ∈ ptys, match p.unqual with
      | .void | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ | .vaList => True
      | _ => False) :
    ∃ coerced,
      Sem.coerceCallArgs m ptys true (args.map (fun v => (v, .void))) = some coerced ∧
      coerced.take ptys.length = args.take ptys.length := by
  rcases hawt with ⟨hlen, hval⟩
  simp only [↓reduceIte] at hlen
  have hplen : ptys.length = cParamTys.length := map_unqual_len hmap
  have hawt_fixed : ArgsHaveCTy cParamTys false (args.take ptys.length) := by
    refine ⟨?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_take]
      omega
    · intro i hi
      have hv := hval i hi
      have hlt : i < ptys.length := by omega
      rw [List.getElem?_take]
      simp [hlt]
      exact hv
  have hnonvar := coerceCallArgs_of_argsWellTyped (m := m) hmap hawt_fixed htys
  unfold Sem.coerceCallArgs at hnonvar
  simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind, List.length_map,
    List.length_take] at hnonvar
  rw [Nat.min_eq_left (by omega : ptys.length ≤ args.length), beq_self_eq_true] at hnonvar
  simp only [guard, ↓reduceIte, pure, Pure.pure] at hnonvar
  have htake_map : (args.map (fun v => (v, CTy.void))).take ptys.length =
      (args.take ptys.length).map (fun v => (v, CTy.void)) :=
    List.map_take.symm
  refine ⟨args.take ptys.length ++
      ((args.map (fun v => (v, CTy.void))).drop ptys.length).map
        (fun x => Sem.promoteVariadicArg x.1), ?_, ?_⟩
  · unfold Sem.coerceCallArgs
    have hle : ptys.length ≤ args.length := by omega
    simp only [↓reduceIte, bind, Option.bind, List.length_map, guard, hle, htake_map, hnonvar,
      pure, Pure.pure]
  · exact List.take_left' (by simp [show ptys.length ≤ args.length by omega])

/-- Universal non-variadic `ContractSafe` builder against `ZlibInv` supporting heap and
OS state modifications (`WPSafe`). -/
theorem ZlibInv_to_ContractSafe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView} {fn : FnDef}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hnonvar : c.variadic = false ∧ fn.variadic = false)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, false))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hbody : ∀ v owned m os args base callEnv callBlks m1,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      Sem.pushCallParams prog.tags m base 0 (fn.params.zip args)
          (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv, callBlks, m1) →
      WPSafe prog Zlib.Spec.zlibPointerConfig ext
        (fun ret m' os' => ∃ owned' v',
          c.post prog.tags owned v m args ret m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))
        (.running (.stmt fn.body) callEnv callBlks m1 os
          (.callFrame gEnv [] fn.retTy fn.body [] .returnVal (.stop protoRetTy)))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c := by
  intro v owned m os args s0 hInv hpre hawt hargDisj hcs
  have hawt' : Zlib.Spec.ArgsWellTyped prog c.paramTys false args := by simpa [hnonvar.1] using hawt
  have hmapTy : (fn.params.map (·.ty)).map CTy.unqual = c.paramTys.map CTy.unqual := by
    simpa [List.map_map, Function.comp_def] using hptys
  have hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false
      (args.map (fun x => (x, .void))) = some args :=
    coerceCallArgs_of_argsWellTyped hmapTy (argsWellTyped_to_haveCTy hawt') (fun p hp => by
      simp only [List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      exact simple_cast_ok (hsimple q hq))
  have htake : args.take fn.params.length = args := by
    have hlen1 := hawt'.1
    simp only [Bool.false_eq_true, ↓reduceIte] at hlen1
    have hlen2 : fn.params.length = c.paramTys.length := by simpa using map_unqual_len hmapTy
    exact List.take_of_length_le (by omega)
  have hawtFn : ArgsHaveCTy (fn.params.map (·.ty)) false args := by
    refine ⟨?_, ?_⟩
    · have h1 := hawt'.1; simp only [Bool.false_eq_true, ↓reduceIte] at h1
      have h2 : fn.params.length = c.paramTys.length := by simpa using map_unqual_len hmapTy
      simp [h1, h2]
    · intro i hi
      simp only [List.length_map] at hi
      have h2 : fn.params.length = c.paramTys.length := by simpa using map_unqual_len hmapTy
      have hv := hawt'.2.1 i (by omega)
      cases hg : args[i]? with
      | none => simp [hg] at hv
      | some av =>
        simp only [hg] at hv ⊢
        simp only [List.getElem_map]
        have hith := congrArg (·[i]?) hptys
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem (by omega : i < c.paramTys.length),
          Option.map_some, Option.some.injEq] at hith
        rw [valHasCTy_unqual, hith, ← valHasCTy_unqual]
        exact hv
  have hex0 : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip args)
        (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') :=
    pushCallParams_exists_base0 prog.tags hsimple hawtFn
  have hstep := callState_stepDet_callFn hproto hcs
  have hwpSafe : WPSafe prog Zlib.Spec.zlibPointerConfig ext
      (fun ret m' os' => ∃ owned' v',
        c.post prog.tags owned v m args ret m' v' ∧
        ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
        FramePreserved m m' (fun b =>
          owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
          userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
        NoHeapLeak m m' owned' ∧
        (v'.isEmpty → ∀ b, ¬ owned' b)) s0 := by
    refine WPSafe.of_call_internal hstep hfn (by simpa [hnonvar.2] using hcoerce)
      (by simpa [htake, hname] using hex0) ?_
      (fun hb => (callState_readBudgetIsSome_iff hproto hcs).mp hb)
    intro base callEnv callBlks m1 hpush _
    rw [htake, ← hname] at hpush
    exact hbody v owned m os args base callEnv callBlks m1 hInv hpre hawt' hargDisj hpush
  exact ⟨hwpSafe.safe,
    fun hb => hwpSafe.terminatesSafely ((callState_readBudgetIsSome_iff hproto hcs).mpr hb),
    hwpSafe.2.2⟩

/-- Universal variadic `ContractSafe` builder against `ZlibInv` (used for `gzprintf`). -/
theorem ZlibInv_to_ContractSafe_variadic
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView} {fn : FnDef}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hvar : c.variadic = true ∧ fn.variadic = true)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, true))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hbody : ∀ v owned m os args base callEnv callBlks m1,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      Sem.pushCallParams prog.tags m base 0 (fn.params.zip (args.take fn.params.length))
          (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv, callBlks, m1) →
      WPSafe prog Zlib.Spec.zlibPointerConfig ext
        (fun ret m' os' => ∃ owned' v',
          c.post prog.tags owned v m args ret m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))
        (.running (.stmt fn.body) callEnv callBlks m1 os
          (.callFrame gEnv [] fn.retTy fn.body [] .returnVal (.stop protoRetTy)))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c := by
  intro v owned m os args s0 hInv hpre hawt hargDisj hcs
  have hawt' : Zlib.Spec.ArgsWellTyped prog c.paramTys true args := by simpa [hvar.1] using hawt
  have hmapTy : (fn.params.map (·.ty)).map CTy.unqual = c.paramTys.map CTy.unqual := by
    simpa [List.map_map, Function.comp_def] using hptys
  obtain ⟨coerced, hcoerce, htake⟩ := coerceCallArgs_variadic_of_argsWellTyped hmapTy
      (argsWellTyped_to_haveCTy hawt') (fun p hp => by
    simp only [List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact simple_cast_ok (hsimple q hq))
  simp only [List.length_map] at htake
  have hawtFn : ArgsHaveCTy (fn.params.map (·.ty)) false (args.take fn.params.length) := by
    have h1 := hawt'.1; simp only [↓reduceIte] at h1
    have h2 : fn.params.length = c.paramTys.length := by simpa using map_unqual_len hmapTy
    refine ⟨by simp [List.length_take, h1, h2], ?_⟩
    intro i hi
    simp only [List.length_map] at hi
    have hv := hawt'.2.1 i (by omega)
    rw [List.getElem?_take]
    simp only [hi, ↓reduceIte]
    cases hg : args[i]? with
    | none => simp [hg] at hv
    | some av =>
      simp only [hg] at hv ⊢
      simp only [List.getElem_map]
      have hith := congrArg (·[i]?) hptys
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by omega : i < c.paramTys.length),
        Option.map_some, Option.some.injEq] at hith
      rw [valHasCTy_unqual, hith, ← valHasCTy_unqual]
      exact hv
  have hex0 : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip (args.take fn.params.length))
        (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') :=
    pushCallParams_exists_base0 prog.tags hsimple hawtFn
  have hstep := callState_stepDet_callFn hproto hcs
  have hwpSafe : WPSafe prog Zlib.Spec.zlibPointerConfig ext
      (fun ret m' os' => ∃ owned' v',
        c.post prog.tags owned v m args ret m' v' ∧
        ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
        FramePreserved m m' (fun b =>
          owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
          userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
        NoHeapLeak m m' owned' ∧
        (v'.isEmpty → ∀ b, ¬ owned' b)) s0 := by
    refine WPSafe.of_call_internal hstep hfn (by simpa [hvar.2] using hcoerce)
      (by simpa [htake, hname] using hex0) ?_
      (fun hb => (callState_readBudgetIsSome_iff hproto hcs).mp hb)
    intro base callEnv callBlks m1 hpush _
    rw [htake, ← hname] at hpush
    exact hbody v owned m os args base callEnv callBlks m1 hInv hpre hawt' hargDisj hpush
  exact ⟨hwpSafe.safe,
    fun hb => hwpSafe.terminatesSafely ((callState_readBudgetIsSome_iff hproto hcs).mpr hb),
    hwpSafe.2.2⟩

theorem FuncBodySpec.to_zlibInv_contractSafe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView} {fn : FnDef}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hnonvar : c.variadic = false ∧ fn.variadic = false)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, false))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hbody : FuncBodySpec prog Zlib.Spec.zlibPointerConfig ext fn Pre Post)
    (hpreImp : ∀ v owned m os args,
      BaseInv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      Pre m args)
    (hpostImp : ∀ v owned m args ret m',
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      C99.Proof.ROExt m m' →
      Post m args ret m' →
      (if protoRetTy.isVoid = true then
        c.post prog.tags owned v m args .void m' v
      else
        ∃ cv, Sem.castVal m' protoRetTy ret = some cv ∧
          c.post prog.tags owned v m args cv m' v)) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c :=
  FuncBodySpec.to_contractSafe
    (fun _ _ _ _ h => h.toBaseInv)
    (fun _ _ _ _ _ h hro => h.roExt hro)
    hfn hname hnonvar hproto hptys hsimple hbody hpreImp hpostImp

/-- Internal `zError` WP spec supplied directly by `ZlibInv.zErrmsgReady`. -/
theorem zError_zlibInv_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} {ext : ExtHandler}
    {v : ClientView} {owned : BlockSet} {os : OSState} :
    FuncBodySpec prog Zlib.Spec.zlibPointerConfig ext Zlib.Zutil.zutilTU_fn_zError
      (fun m' args => ZlibInv prog gEnv m0 os0 v owned m' os ∧ ∃ err : BitVec 32, args = [.int .i32 err])
      (fun _ _ ret m' => Zlib.Spec.CString m' ret ∧
        ∃ sb sblk, ret = .ptr sb 0 ∧ m'.blocks sb = some sblk ∧ sblk.perm = .ro ∧ sblk.kind = .global) := by
  intro args env blks m' m1 os' base callEnv callBlks fs ctx k Q ⟨hinv', herr⟩ hlen hpush hcont
  refine zError_spec hinv'.toInitProps args env blks m' m1 os' base callEnv callBlks fs ctx k Q
    ⟨?_, herr⟩ hlen hpush hcont
  rw [hinv'.toInitProps.globalEnv_eq]
  exact hinv'.zErrmsgReady

/-! ### Lifted Wave 1 `ContractSafe` Theorems against `ZlibInv prog gEnv m0 os0` -/

section Wave1Lifted

variable {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
  {userExt : ExtHandler} {userWrite : BlockSet}

theorem zlibVersion_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Zutil.zlibVersion_contract :=
  zlibVersion_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem zlibCompileFlags_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Zutil.zlibCompileFlags_contract :=
  zlibCompileFlags_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem compressBound_z_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Compress.compressBound_z_contract :=
  compressBound_z_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem compressBound_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Compress.compressBound_contract :=
  compressBound_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem adler32_z_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Adler32.adler32_z_contract :=
  adler32_z_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem adler32_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Adler32.adler32_contract :=
  adler32_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem adler32_combine_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Adler32.adler32_combine_contract :=
  adler32_combine_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem adler32_combine64_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Adler32.adler32_combine64_contract :=
  adler32_combine64_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_z_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_z_contract :=
  crc32_z_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_contract :=
  crc32_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_combine_gen64_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_combine_gen64_contract :=
  crc32_combine_gen64_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_combine_gen_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_combine_gen_contract :=
  crc32_combine_gen_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_combine_op_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_combine_op_contract :=
  crc32_combine_op_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_combine64_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_combine64_contract :=
  crc32_combine64_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

theorem crc32_combine_zlibInv_safe (hlib : InitLibzProps prog gEnv m0 os0) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Crc32.crc32_combine_contract :=
  crc32_combine_safe hlib (fun _ _ _ _ h => h.toBaseInv) (fun _ _ _ _ _ h hro => h.roExt hro)

end Wave1Lifted

/-! ## 6. Call Simulation (`CallWPTermSpec`, `CallSafeSpec`), `ZALLOC`/`ZFREE`, & User Callbacks -/

def CallWPTermSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (fn : FnDef)
    (Pre : Mem → OSState → List Val → Prop)
    (Post : Mem → OSState → List Val → Val → Mem → OSState → Prop) : Prop :=
  ∀ (args : List Val) (env : Env) (blks : List BlockId)
    (m m1 : Mem) (os : OSState)
    (base : Nat → UInt64) (callEnv : Env) (callBlks : List BlockId)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont)
    (Q : Val → Mem → OSState → Prop),
    Pre m os args →
    args.length = fn.params.length →
    Sem.pushCallParams prog.tags m base 0 (fn.params.zip args)
        (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv, callBlks, m1) →
    (∀ ret m' os', Post m os args ret m' os' →
      C99.Proof.WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os' k)) →
    C99.Proof.WPTerm prog cfg ext Q
      (.running (.stmt fn.body) callEnv callBlks m1 os
        (.callFrame env blks fn.retTy fn.body fs ctx k))

def CallSafeSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (fn : FnDef)
    (Pre : Mem → OSState → List Val → Prop)
    (Post : Mem → OSState → List Val → Val → Mem → OSState → Prop) : Prop :=
  ∀ (args : List Val) (env : Env) (blks : List BlockId)
    (m m1 : Mem) (os : OSState)
    (base : Nat → UInt64) (callEnv : Env) (callBlks : List BlockId)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont)
    (Q : Val → Mem → OSState → Prop),
    Pre m os args →
    args.length = fn.params.length →
    Sem.pushCallParams prog.tags m base 0 (fn.params.zip args)
        (prog.fnStatics fn.name ++ prog.globalEnv) [] = some (callEnv, callBlks, m1) →
    (∀ ret m' os', Post m os args ret m' os' →
      WPSafe prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os' k)) →
    WPSafe prog cfg ext Q
      (.running (.stmt fn.body) callEnv callBlks m1 os
        (.callFrame env blks fn.retTy fn.body fs ctx k))

theorem CallWPTermSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler} {fn : FnDef}
    {Pre1 Pre2 : Mem → OSState → List Val → Prop}
    {Post1 Post2 : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hpre : ∀ m os args, Pre2 m os args → Pre1 m os args)
    (hpost : ∀ m os args ret m' os', Pre2 m os args → Post1 m os args ret m' os' →
      Post2 m os args ret m' os')
    (hspec : CallWPTermSpec prog cfg ext fn Pre1 Post1) :
    CallWPTermSpec prog cfg ext fn Pre2 Post2 := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hp hlen hpush hcont
  exact hspec args env blks m m1 os base callEnv callBlks fs ctx k Q (hpre m os args hp)
    hlen hpush (fun ret m' os' hpo => hcont ret m' os' (hpost m os args ret m' os' hp hpo))

theorem CallSafeSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler} {fn : FnDef}
    {Pre1 Pre2 : Mem → OSState → List Val → Prop}
    {Post1 Post2 : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hpre : ∀ m os args, Pre2 m os args → Pre1 m os args)
    (hpost : ∀ m os args ret m' os', Pre2 m os args → Post1 m os args ret m' os' →
      Post2 m os args ret m' os')
    (hspec : CallSafeSpec prog cfg ext fn Pre1 Post1) :
    CallSafeSpec prog cfg ext fn Pre2 Post2 := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hp hlen hpush hcont
  exact hspec args env blks m m1 os base callEnv callBlks fs ctx k Q (hpre m os args hp)
    hlen hpush (fun ret m' os' hpo => hcont ret m' os' (hpost m os args ret m' os' hp hpo))

theorem HeapBodySpec.to_callWPTermSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (h : HeapBodySpec prog cfg ext fn Pre Post) :
    CallWPTermSpec prog cfg ext fn
      (fun m _ args => Pre m args)
      (fun m os args ret m' os' => os' = os ∧ Post m args ret m') := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush hcont
  exact h args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush
    (fun ret m' hp => hcont ret m' os ⟨rfl, hp⟩)

theorem FuncBodySpec.to_callWPTermSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → List Val → Prop} {Post : Mem → List Val → Val → Mem → Prop}
    (h : FuncBodySpec prog cfg ext fn Pre Post) :
    CallWPTermSpec prog cfg ext fn
      (fun m _ args => Pre m args)
      (fun m os args ret m' os' => os' = os ∧ C99.Proof.ROExt m m' ∧ Post m args ret m') := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush hcont
  exact h args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush
    (fun ret m' hro hp => hcont ret m' os ⟨rfl, hro, hp⟩)

theorem CallWPTermSpec.call
    {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hspec : CallWPTermSpec prog cfg ext fn Pre Post)
    {s : Sem.RunState} {sym : String} {fnTy : CTy} {argVals : List (Val × CTy)}
    {coerced : List Val} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    (hstep : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false argVals = some coerced)
    (hpre : Pre m os coerced)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hcont : ∀ ret m' os', Post m os coerced ret m' os' →
      C99.Proof.WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os' k)) :
    C99.Proof.WPTerm prog cfg ext Q s := by
  have ⟨hlenC, _⟩ := coerceCallArgs_length hcoerce
  simp only [List.length_map] at hlenC
  have htake : List.take fn.params.length coerced = coerced :=
    List.take_of_length_le (by omega)
  have hawt : ArgsHaveCTy (fn.params.map (·.ty)) false coerced :=
    coerceCallArgs_produces_argsWellTyped hcoerce
  have hex0 : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip coerced)
        (prog.fnStatics sym ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') := by
    rw [← hsym]
    exact pushCallParams_exists_base0 prog.tags hsimp hawt
  apply C99.Proof.WPTerm.of_call_internal hstep hfn (by simpa [hnonvar] using hcoerce)
    (by simpa [htake] using hex0)
  intro base callEnv callBlks m1 hpush
  rw [htake, ← hsym] at hpush
  exact hspec coerced env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlenC hpush hcont

theorem CallSafeSpec.call
    {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hspec : CallSafeSpec prog cfg ext fn Pre Post)
    {s : Sem.RunState} {sym : String} {fnTy : CTy} {argVals : List (Val × CTy)}
    {coerced : List Val} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    (hstep : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false argVals = some coerced)
    (hpre : Pre m os coerced)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hcont : ∀ ret m' os', Post m os coerced ret m' os' →
      WPSafe prog cfg ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os' k)) :
    WPSafe prog cfg ext Q s := by
  have ⟨hlenC, _⟩ := coerceCallArgs_length hcoerce
  simp only [List.length_map] at hlenC
  have htake : List.take fn.params.length coerced = coerced :=
    List.take_of_length_le (by omega)
  have hawt : ArgsHaveCTy (fn.params.map (·.ty)) false coerced :=
    coerceCallArgs_produces_argsWellTyped hcoerce
  have hex0 : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip coerced)
        (prog.fnStatics sym ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') := by
    rw [← hsym]
    exact pushCallParams_exists_base0 prog.tags hsimp hawt
  have hos_bud : readBudgetIsSome s → os.readBudget.isSome = true := by
    intro hb
    exact stepDet_preserves_budget hstep hb
  apply WPSafe.of_call_internal hstep hfn (by simpa [hnonvar] using hcoerce)
    (by simpa [htake] using hex0) _ hos_bud
  intro base callEnv callBlks m1 hpush _
  rw [htake, ← hsym] at hpush
  exact hspec coerced env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlenC hpush hcont

/-! ### Continuation Lifting & `CallWPTermSpec.to_callSafeSpec` -/

inductive ContLift (env : Env) (blks : List BlockId) (rt : CTy) (fnBody : CStmt)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont) :
    Sem.Cont → Sem.Cont → Prop where
  | base :
      ContLift env blks rt fnBody fs ctx k
        (.callFrame [] [] rt fnBody [] .returnVal (.stop rt))
        (.callFrame env blks rt fnBody fs ctx k)
  | stmts {ss rest1 rest2} :
      ContLift env blks rt fnBody fs ctx k rest1 rest2 →
      ContLift env blks rt fnBody fs ctx k (.stmts ss rest1) (.stmts ss rest2)
  | blockEnd {se sb rest1 rest2} :
      ContLift env blks rt fnBody fs ctx k rest1 rest2 →
      ContLift env blks rt fnBody fs ctx k (.blockEnd se sb rest1) (.blockEnd se sb rest2)
  | loop {c? stp? b isDo rest1 rest2} :
      ContLift env blks rt fnBody fs ctx k rest1 rest2 →
      ContLift env blks rt fnBody fs ctx k (.loop c? stp? b isDo rest1) (.loop c? stp? b isDo rest2)
  | switchCont {rest1 rest2} :
      ContLift env blks rt fnBody fs ctx k rest1 rest2 →
      ContLift env blks rt fnBody fs ctx k (.switchCont rest1) (.switchCont rest2)
  | callFrame {re rb rt' b' fs' ctx' rest1 rest2} :
      ContLift env blks rt fnBody fs ctx k rest1 rest2 →
      ContLift env blks rt fnBody fs ctx k
        (.callFrame re rb rt' b' fs' ctx' rest1)
        (.callFrame re rb rt' b' fs' ctx' rest2)

def hasBottomFrame (env : Env) (blks : List BlockId) (rt : CTy) (fnBody : CStmt)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont) (k1 : Sem.Cont) : Prop :=
  ∃ k2, ContLift env blks rt fnBody fs ctx k k1 k2

def liftCont (env : Env) (blks : List BlockId) (rt : CTy) (fnBody : CStmt)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont) : Sem.Cont → Sem.Cont
  | .callFrame _ _ _ _ _ _ (.stop _) => .callFrame env blks rt fnBody fs ctx k
  | .stmts ss rest => .stmts ss (liftCont env blks rt fnBody fs ctx k rest)
  | .blockEnd se sb rest => .blockEnd se sb (liftCont env blks rt fnBody fs ctx k rest)
  | .loop c? stp? b isDo rest => .loop c? stp? b isDo (liftCont env blks rt fnBody fs ctx k rest)
  | .switchCont rest => .switchCont (liftCont env blks rt fnBody fs ctx k rest)
  | .callFrame re rb rt' b' fs' ctx' rest =>
      .callFrame re rb rt' b' fs' ctx' (liftCont env blks rt fnBody fs ctx k rest)
  | c@(.stop _) => c

private theorem contLift_stop_not_left {env blks rt fnBody fs ctx k} {rt' : CTy} {k2 : Sem.Cont}
    (h : ContLift env blks rt fnBody fs ctx k (.stop rt') k2) : False := by
  cases h

theorem ContLift.liftCont_eq {env blks rt fnBody fs ctx k k1 k2}
    (h : ContLift env blks rt fnBody fs ctx k k1 k2) :
    liftCont env blks rt fnBody fs ctx k k1 = k2 := by
  induction h with
  | base => rfl
  | stmts _ ih => simp [liftCont, ih]
  | blockEnd _ ih => simp [liftCont, ih]
  | loop _ ih => simp [liftCont, ih]
  | switchCont _ ih => simp [liftCont, ih]
  | @callFrame re rb rt' b' fs' ctx' rest1 rest2 hrest ih =>
    cases rest1 with
    | stop _ => exact False.elim (contLift_stop_not_left hrest)
    | _ => exact congrArg (fun x => Sem.Cont.callFrame re rb rt' b' fs' ctx' x) ih

theorem ContLift.topRetTy {env blks rt fnBody fs ctx k k1 k2}
    (h : ContLift env blks rt fnBody fs ctx k k1 k2) :
    k1.topRetTy = k2.topRetTy := by
  induction h <;> simp [Sem.Cont.topRetTy, *]

private theorem findInStmt_ifStmt (lbl : String) (e : Env) (b : List BlockId)
    (c : CExpr) (t : CStmt) (f? : Option CStmt) (k : Sem.Cont) :
    Sem.findInStmt lbl e b (.ifStmt c t f?) k =
      match Sem.findInStmt lbl e b t k with
      | some res => some res
      | none => match f? with | some f => Sem.findInStmt lbl e b f k | none => none := by
  delta Sem.findInStmt CStmt.brecOn CStmt.brecOn.go Sem.findInStmt._f
  dsimp only
  cases f? <;> rfl

mutual
private theorem findInStmts_contLift {env blks rt fnBody fs ctx k}
    (lbl : String) (e : Env) (b : List BlockId) {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) (ss : List CStmt) :
    (Sem.findInStmts lbl e b k1 ss = none ∧ Sem.findInStmts lbl e b k2 ss = none) ∨
    (∃ s' e' b' k1' k2',
      ContLift env blks rt fnBody fs ctx k k1' k2' ∧
      Sem.findInStmts lbl e b k1 ss = some (s', e', b', k1') ∧
      Sem.findInStmts lbl e b k2 ss = some (s', e', b', k2')) := by
  cases ss with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons hd tl =>
    dsimp only [Sem.findInStmts]
    have hk' : ContLift env blks rt fnBody fs ctx k
        (if tl.isEmpty then k1 else .stmts tl k1)
        (if tl.isEmpty then k2 else .stmts tl k2) := by
      cases tl with
      | nil => exact hk
      | cons _ _ => exact ContLift.stmts hk
    rcases findInStmt_contLift lbl e b hk' hd with ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hkl, hs1, hs2⟩
    · rw [hn1, hn2]
      exact findInStmts_contLift lbl e b hk tl
    · rw [hs1, hs2]
      exact Or.inr ⟨s', e', b', k1', k2', hkl, rfl, rfl⟩

private theorem findInStmt_contLift {env blks rt fnBody fs ctx k}
    (lbl : String) (e : Env) (b : List BlockId) {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) (st : CStmt) :
    (Sem.findInStmt lbl e b st k1 = none ∧ Sem.findInStmt lbl e b st k2 = none) ∨
    (∃ s' e' b' k1' k2',
      ContLift env blks rt fnBody fs ctx k k1' k2' ∧
      Sem.findInStmt lbl e b st k1 = some (s', e', b', k1') ∧
      Sem.findInStmt lbl e b st k2 = some (s', e', b', k2')) := by
  cases st with
  | labelStmt l body =>
    dsimp only [Sem.findInStmt]
    by_cases heq : (l == lbl) = true
    · simp only [heq, ↓reduceIte]
      exact Or.inr ⟨body, e, b, k1, k2, hk, rfl, rfl⟩
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      exact findInStmt_contLift lbl e b hk body
  | block ss =>
    dsimp only [Sem.findInStmt]
    exact findInStmts_contLift lbl e [] (ContLift.blockEnd hk) ss
  | ifStmt c t f? =>
    rw [findInStmt_ifStmt, findInStmt_ifStmt]
    rcases findInStmt_contLift lbl e b hk t with ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hkl, hs1, hs2⟩
    · rw [hn1, hn2]
      cases f? with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some f => exact findInStmt_contLift lbl e b hk f
    · rw [hs1, hs2]
      exact Or.inr ⟨s', e', b', k1', k2', hkl, rfl, rfl⟩
  | whileStmt c body =>
    dsimp only [Sem.findInStmt]
    exact findInStmt_contLift lbl e b (ContLift.loop hk) body
  | doWhileStmt body c =>
    dsimp only [Sem.findInStmt]
    exact findInStmt_contLift lbl e b (ContLift.loop hk) body
  | forStmt _ c? stp? body =>
    dsimp only [Sem.findInStmt]
    exact findInStmt_contLift lbl e b (ContLift.loop hk) body
  | switchStmt _ body =>
    dsimp only [Sem.findInStmt]
    exact findInStmt_contLift lbl e b (ContLift.switchCont hk) body
  | caseStmt _ body =>
    dsimp only [Sem.findInStmt]
    exact findInStmt_contLift lbl e b hk body
  | defaultStmt body =>
    dsimp only [Sem.findInStmt]
    exact findInStmt_contLift lbl e b hk body
  | nop | expr _ | decl _ | decls _ | breakStmt | continueStmt | gotoStmt _ | returnStmt _ =>
    exact Or.inl ⟨rfl, rfl⟩
end

theorem ContLift.gotoInCont {env blks rt fnBody fs ctx k}
    (lbl : String) (m : Mem) (e : Env) (b : List BlockId) {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) :
    (Sem.gotoInCont lbl m e b k1 = none ∧ Sem.gotoInCont lbl m e b k2 = none) ∨
    (∃ s' e' b' m' k1' k2',
      ContLift env blks rt fnBody fs ctx k k1' k2' ∧
      Sem.gotoInCont lbl m e b k1 = some (s', e', b', m', k1') ∧
      Sem.gotoInCont lbl m e b k2 = some (s', e', b', m', k2')) := by
  induction hk generalizing m e b with
  | base =>
    dsimp only [Sem.gotoInCont]
    rcases findInStmt_contLift lbl e b ContLift.base fnBody with
      ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hkl, hs1, hs2⟩
    · rw [hn1, hn2]; exact Or.inl ⟨rfl, rfl⟩
    · rw [hs1, hs2]; exact Or.inr ⟨s', e', b', m, k1', k2', hkl, rfl, rfl⟩
  | stmts hrest ih =>
    rename_i ss _ _
    dsimp only [Sem.gotoInCont]
    rcases findInStmts_contLift lbl e b hrest ss with
      ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hkl, hs1, hs2⟩
    · rw [hn1, hn2]; exact ih m e b
    · rw [hs1, hs2]; exact Or.inr ⟨s', e', b', m, k1', k2', hkl, rfl, rfl⟩
  | blockEnd _ ih =>
    dsimp only [Sem.gotoInCont]
    exact ih (m.freeStack b) _ _
  | loop hrest ih =>
    rename_i c? stp? body isDo _ _
    dsimp only [Sem.gotoInCont]
    rcases findInStmt_contLift lbl e b (ContLift.loop hrest) body with
      ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hkl, hs1, hs2⟩
    · rw [hn1, hn2]; exact ih m e b
    · rw [hs1, hs2]; exact Or.inr ⟨s', e', b', m, k1', k2', hkl, rfl, rfl⟩
  | switchCont _ ih =>
    dsimp only [Sem.gotoInCont]
    exact ih m e b
  | @callFrame re rb rt' b' fs' ctx' r1 r2 hrest _ =>
    dsimp only [Sem.gotoInCont]
    rcases findInStmt_contLift lbl e b (ContLift.callFrame hrest) b' with
      ⟨hn1, hn2⟩ | ⟨s', e', b', k1', k2', hkl, hs1, hs2⟩
    · rw [hn1, hn2]; exact Or.inl ⟨rfl, rfl⟩
    · rw [hs1, hs2]; exact Or.inr ⟨s', e', b', m, k1', k2', hkl, rfl, rfl⟩

theorem ContLift.unwindBreak {env blks rt fnBody fs ctx k}
    (m : Mem) (e : Env) (b : List BlockId) {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) :
    (Sem.unwindBreak m e b k1 = none ∧ Sem.unwindBreak m e b k2 = none) ∨
    (∃ e' b' m' k1' k2',
      ContLift env blks rt fnBody fs ctx k k1' k2' ∧
      Sem.unwindBreak m e b k1 = some (e', b', m', k1') ∧
      Sem.unwindBreak m e b k2 = some (e', b', m', k2')) := by
  induction hk generalizing m e b with
  | base | callFrame _ => exact Or.inl ⟨rfl, rfl⟩
  | stmts _ ih =>
    dsimp only [Sem.unwindBreak]
    exact ih m e b
  | blockEnd _ ih =>
    dsimp only [Sem.unwindBreak]
    exact ih (m.freeStack b) _ _
  | loop hrest _ | switchCont hrest _ => exact Or.inr ⟨e, b, m, _, _, hrest, rfl, rfl⟩

theorem ContLift.unwindContinue {env blks rt fnBody fs ctx k}
    (m : Mem) (e : Env) (b : List BlockId) {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) :
    (Sem.unwindContinue m e b k1 = none ∧ Sem.unwindContinue m e b k2 = none) ∨
    (∃ c? stp? body isDo e' b' m' k1' k2',
      ContLift env blks rt fnBody fs ctx k k1' k2' ∧
      Sem.unwindContinue m e b k1 = some (c?, stp?, body, isDo, e', b', m', k1') ∧
      Sem.unwindContinue m e b k2 = some (c?, stp?, body, isDo, e', b', m', k2')) := by
  induction hk generalizing m e b with
  | base | callFrame _ => exact Or.inl ⟨rfl, rfl⟩
  | stmts _ ih | switchCont _ ih =>
    dsimp only [Sem.unwindContinue]
    exact ih m e b
  | blockEnd _ ih =>
    dsimp only [Sem.unwindContinue]
    exact ih (m.freeStack b) _ _
  | loop hrest _ => exact Or.inr ⟨_, _, _, _, e, b, m, _, _, hrest, rfl, rfl⟩

theorem ContLift.unwindReturn {env blks rt fnBody fs ctx k}
    (m : Mem) (b : List BlockId) {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) :
    (∃ m', Sem.unwindReturn m b k1 = some ([], [], rt, m', [], .returnVal, .stop rt) ∧
           Sem.unwindReturn m b k2 = some (env, blks, rt, m', fs, ctx, k) ∧
           k1.topRetTy = rt ∧ k2.topRetTy = rt) ∨
    (∃ re rb rt' m' fs' ctx' k1' k2',
      ContLift env blks rt fnBody fs ctx k k1' k2' ∧
      Sem.unwindReturn m b k1 = some (re, rb, rt', m', fs', ctx', k1') ∧
      Sem.unwindReturn m b k2 = some (re, rb, rt', m', fs', ctx', k2')) := by
  induction hk generalizing m b with
  | base =>
    exact Or.inl ⟨m.freeStack b, rfl, rfl, rfl, rfl⟩
  | stmts _ ih | loop _ ih | switchCont _ ih =>
    dsimp only [Sem.unwindReturn, Sem.Cont.topRetTy]
    exact ih m b
  | blockEnd _ ih =>
    dsimp only [Sem.unwindReturn, Sem.Cont.topRetTy]
    exact ih (m.freeStack b) _
  | callFrame hrest _ =>
    exact Or.inr ⟨_, _, _, m.freeStack b, _, _, _, _, hrest, rfl, rfl⟩

private theorem castVal_idem_anyMem {m1 m2 : Mem} {ty : CTy} {v cv : Val}
    (h : Sem.castVal m1 ty v = some cv) : Sem.castVal m2 ty cv = some cv := by
  unfold Sem.castVal at h ⊢
  dsimp only at h ⊢
  by_cases hvoid : ty.unqual.isVoid = true
  · simp only [hvoid, ↓reduceIte, Option.some.injEq] at h ⊢
    exact h
  · simp only [hvoid, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hki : ty.unqual.intKind? with
    | some k =>
      simp only [hki] at h ⊢
      cases v with
      | «int» k1 bv =>
        simp only [Option.some.injEq] at h
        subst h
        dsimp only [Sem.ofIntCast]
        congr 2
        split
        · exact BitVec.ofInt_toInt
        · rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      | null =>
        simp only [Option.some.injEq] at h
        subst h
        dsimp only [Sem.ofIntCast]
        congr 2
        split <;> simp
      | ptr pb poff =>
        rcases Option.map_eq_some_iff.mp h with ⟨a, _, rfl⟩
        dsimp only [Sem.ofIntCast]
        congr 2
        split
        · exact BitVec.ofInt_toInt
        · rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      | fnPtr _ | vaList _ | «void» | undef => cases h
    | none =>
      simp only [hki] at h ⊢
      cases hut : ty.unqual with
      | ptr _ =>
        simp only [hut] at h ⊢
        cases v with
        | null => cases h; rfl
        | ptr _ _ => cases h; rfl
        | «int» _ bv =>
          by_cases hz : (bv.toNat == 0) = true
          · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h; rfl
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h; cases h
        | _ => cases h
      | fnPtr _ _ _ =>
        simp only [hut] at h ⊢
        cases v with
        | null => cases h; rfl
        | fnPtr _ => cases h; rfl
        | «int» _ bv =>
          by_cases hz : (bv.toNat == 0) = true
          · simp only [hz, ↓reduceIte, Option.some.injEq] at h; subst h; rfl
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h; cases h
        | _ => cases h
      | vaList =>
        simp only [hut] at h ⊢
        cases v with
        | vaList flag =>
          cases flag
          · cases h
          · cases h; rfl
        | _ => cases h
      | _ => simp only [hut] at h; cases h

private theorem castVal_undef_none {m : Mem} {ty : CTy} (hnot : ty.isVoid = false) :
    Sem.castVal m ty .undef = none := by
  unfold Sem.castVal
  dsimp only
  have hnot' : ty.unqual.isVoid = false := by
    simpa [CTy.isVoid, cty_unqual_idem] using hnot
  simp only [hnot', Bool.false_eq_true, ↓reduceIte]
  cases ty.unqual.intKind? with
  | some k => rfl
  | none => cases ty.unqual <;> rfl

inductive RunStateLift (env : Env) (blks : List BlockId) (rt : CTy) (fnBody : CStmt)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont) :
    Sem.RunState → Sem.RunState → Prop where
  | inside {ctrl e b m os k1 k2} :
      ContLift env blks rt fnBody fs ctx k k1 k2 →
      RunStateLift env blks rt fnBody fs ctx k (.running ctrl e b m os k1) (.running ctrl e b m os k2)
  | exitedVoid {m' os' rty} :
      rt.isVoid = true → (rty = .void ∨ rty = rt) →
      RunStateLift env blks rt fnBody fs ctx k
        (.running (.expr (.ret (.rval .void rty) []) .returnVal []) [] [] m' os' (.stop rt))
        (.running (.expr (.ret (.rval .void rty) fs) ctx []) env blks m' os' k)
  | exitedVal {v m' os'} :
      rt.isVoid = false → Sem.castVal m' rt v = some v →
      RunStateLift env blks rt fnBody fs ctx k
        (.running (.expr (.ret (.rval v rt) []) .returnVal []) [] [] m' os' (.stop rt))
        (.running (.expr (.ret (.rval v rt) fs) ctx []) env blks m' os' k)
  | exitedUndef {m' os'} :
      rt.isVoid = false →
      RunStateLift env blks rt fnBody fs ctx k
        (.running (.expr (.ret (.rval .undef rt) []) .returnVal []) [] [] m' os' (.stop rt))
        (.running (.expr (.ret (.rval .undef rt) fs) ctx []) env blks m' os' k)

private def DetStepLift (env : Env) (blks : List BlockId) (rt : CTy) (fnBody : CStmt)
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (k : Sem.Cont)
    (d1 d2 : Option Sem.DetStep) : Prop :=
  match d1 with
  | none => d2 = none
  | some (.next s1') =>
      ∃ s2', d2 = some (.next s2') ∧ RunStateLift env blks rt fnBody fs ctx k s1' s2'
  | some (.allocStr str fs' ctx' mods' e' b' m' os' k1') =>
      ∃ k2', ContLift env blks rt fnBody fs ctx k k1' k2' ∧
        d2 = some (.allocStr str fs' ctx' mods' e' b' m' os' k2')
  | some (.allocLocal d i? rest e' b' m' os' k1') =>
      ∃ k2', ContLift env blks rt fnBody fs ctx k k1' k2' ∧
        d2 = some (.allocLocal d i? rest e' b' m' os' k2')
  | some (.callFn sym fty args fs' ctx' e' b' m' os' k1') =>
      ∃ k2', ContLift env blks rt fnBody fs ctx k k1' k2' ∧
        d2 = some (.callFn sym fty args fs' ctx' e' b' m' os' k2')

private theorem stepExprPure_lift {env blks rt fnBody fs ctx k}
    {ect : Sem.ExprCtx} {e : Env} {b : List BlockId} {os : OSState} {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2)
    {d1 d2 : Option Sem.DetStep}
    (opt : Option (Sem.ExprState × Mem × ModSet))
    (h1 : d1 = opt.map (fun (es', m', mods') => Sem.DetStep.next (.running (.expr es' ect mods') e b m' os k1)))
    (h2 : d2 = opt.map (fun (es', m', mods') => Sem.DetStep.next (.running (.expr es' ect mods') e b m' os k2))) :
    DetStepLift env blks rt fnBody fs ctx k d1 d2 := by
  subst h1; subst h2
  cases opt with
  | none => rfl
  | some p => exact ⟨_, rfl, RunStateLift.inside hk⟩

private theorem stepDet_ret_rval_nil (prog : Prog) (cfg : PointerConfig)
    (v : Val) (ty : CTy) (ctx : Sem.ExprCtx) (mods : ModSet)
    (e : Env) (b : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval v ty) []) ctx mods) e b m os k) =
      match ctx with
      | .discard => some (.next (.running (.stmt .nop) e b m os k))
      | .returnVal =>
        let rt := k.topRetTy
        if rt.isVoid then
          some (.next (match Sem.unwindReturn m b k with
            | some (re, rb, _, m', fs, rctx, rk) =>
                .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' os rk
            | none => .returned .void (m.freeStack b) os))
        else
          (Sem.castVal m rt v).map (fun cv =>
            .next (match Sem.unwindReturn m b k with
              | some (re, rb, _, m', fs, rctx, rk) =>
                  .running (.expr (.ret (.rval cv rt) fs) rctx []) re rb m' os rk
              | none => .returned cv (m.freeStack b) os))
      | .varInit d rest => some (.allocLocal d (some (.rval v ty)) rest e b m os k)
      | .branch t f => (Sem.isTruthy v).map fun bv =>
          .next (.running (.stmt (if bv then t else f)) e b m os k)
      | .whileCond c body => (Sem.isTruthy v).map fun bv =>
          .next (if bv then .running (.stmt body) e b m os (.loop (some c) none body false k)
                 else .running (.stmt .nop) e b m os k)
      | .doWhileCond body c => (Sem.isTruthy v).map fun bv =>
          .next (if bv then .running (.stmt body) e b m os (.loop (some c) none body true k)
                 else .running (.stmt .nop) e b m os k)
      | .forCond c stp? body => (Sem.isTruthy v).map fun bv =>
          .next (if bv then .running (.stmt body) e b m os (.loop (some c) stp? body false k)
                 else .running (.stmt .nop) e b m os k)
      | .forStep c? stp? body =>
          some (.next (match c? with
            | some c => .running (.expr (.eval .rval c []) (.forCond c stp? body) []) e b m os k
            | none => .running (.stmt body) e b m os (.loop none stp? body false k)))
      | .switchScrut body => (Sem.valAsInt? v).map fun (_, iv) =>
          .next (match Sem.findSwitchTarget iv body with
            | some tgt => .running (.stmt tgt) e b m os (.switchCont k)
            | none => .running (.stmt .nop) e b m os k) := by
  cases v <;> rfl

private theorem stepDet_ret_rval_callArgF_nil (prog : Prog) (cfg : PointerConfig)
    (v : Val) (ty : CTy) (sym : String) (fnTy : CTy) (done : List (Val × CTy))
    (fs : List Sem.ExprFrame) (ctx : Sem.ExprCtx) (mods : ModSet)
    (e : Env) (b : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval v ty) (.callArgF sym fnTy done [] :: fs)) ctx mods) e b m os k) =
      some (.callFn sym fnTy (done ++ [(v, ty)]) fs ctx e b m os k) := by
  cases v <;> rfl

private theorem stepDet_ret_rval_cons_fallback (prog : Prog) (cfg : PointerConfig)
    (v : Val) (ty : CTy) (f0 : Sem.ExprFrame) (fs : List Sem.ExprFrame)
    (ctx : Sem.ExprCtx) (mods : ModSet)
    (e : Env) (b : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont)
    (h1 : ∀ ds, f0 = .callFnF ds → ds ≠ [])
    (h2 : ∀ sym fnTy done rest, f0 = .callArgF sym fnTy done rest → rest ≠ []) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval v ty) (f0 :: fs)) ctx mods) e b m os k) =
      (Sem.stepExprPure prog cfg e m mods (.ret (.rval v ty) (f0 :: fs))).map
        (fun (es', m', mods') => .next (.running (.expr es' ctx mods') e b m' os k)) := by
  cases f0 with
  | callFnF ds =>
    cases ds with
    | nil => exact False.elim (h1 [] rfl rfl)
    | cons _ _ => cases v <;> rfl
  | callArgF sym fnTy done rest =>
    cases rest with
    | nil => exact False.elim (h2 sym fnTy done [] rfl rfl)
    | cons _ _ => cases v <;> rfl
  | _ => cases v <;> rfl

private theorem stepDet_decls_cons (prog : Prog) (cfg : PointerConfig)
    (d : VarDecl) (rest : List VarDecl)
    (e : Env) (b : List BlockId) (m : Mem) (os : OSState) (k : Sem.Cont) :
    Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) e b m os k) =
      if d.isStatic = true then
        some (.next (.running (.stmt (.decls rest)) e b m os k))
      else
        match d.init? with
        | none => some (.allocLocal d none rest e b m os k)
        | some (.expr ex) =>
            some (.next (.running (.expr (.eval .rval ex []) (.varInit d rest) []) e b m os k))
        | some _ => none := by
  cases d with
  | mk _ _ isSt init? =>
    cases isSt with
    | true => rfl
    | false =>
      cases init? with
      | none => rfl
      | some iv => cases iv <;> rfl

private theorem stepDet_contLift {prog : Prog} {cfg : PointerConfig}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    {ctrl : Sem.Control} {e : Env} {b : List BlockId} {m : Mem} {os : OSState} {k1 k2 : Sem.Cont}
    (hk : ContLift env blks rt fnBody fs ctx k k1 k2) :
    DetStepLift env blks rt fnBody fs ctx k
      (Sem.stepDet prog cfg (.running ctrl e b m os k1))
      (Sem.stepDet prog cfg (.running ctrl e b m os k2)) := by
  have ht := hk.topRetTy
  unfold Sem.stepDet
  cases ctrl with
  | expr es ect mods =>
    cases es with
    | eval w ex fs' =>
      cases w with
      | lval => exact stepExprPure_lift hk _ rfl rfl
      | rval =>
        cases ex with
        | strLit str => exact ⟨k2, hk, rfl⟩
        | _ => exact stepExprPure_lift hk _ rfl rfl
    | ret rv fs' =>
      cases rv with
      | lval _ _ _ | structVal _ _ =>
        cases fs' with
        | nil =>
          cases ect with
          | discard => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | varInit d rest => exact ⟨k2, hk, rfl⟩
          | forStep c? stp? body =>
            dsimp only [DetStepLift]
            cases c? with
            | some _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
            | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
          | returnVal | branch _ _ | whileCond _ _ | doWhileCond _ _ | forCond _ _ _ | switchScrut _ =>
            rfl
        | cons _ _ =>
          exact stepExprPure_lift hk _ rfl rfl
      | rval v ty =>
        cases fs' with
        | cons f0 frest =>
          cases f0 with
          | callFnF ds =>
            cases ds with
            | nil =>
              cases v with
              | fnPtr _ => exact ⟨k2, hk, rfl⟩
              | _ => exact stepExprPure_lift hk _ rfl rfl
            | cons a ds' =>
              exact stepExprPure_lift hk _
                (stepDet_ret_rval_cons_fallback prog cfg v ty (.callFnF (a :: ds')) frest ect mods e b m os k1
                  (fun _ h hnil => by cases h; cases hnil) (fun _ _ _ _ h => by cases h))
                (stepDet_ret_rval_cons_fallback prog cfg v ty (.callFnF (a :: ds')) frest ect mods e b m os k2
                  (fun _ h hnil => by cases h; cases hnil) (fun _ _ _ _ h => by cases h))
          | callArgF sym fnTy' done restArgs =>
            cases restArgs with
            | nil =>
              show DetStepLift env blks rt fnBody fs ctx k
                (Sem.stepDet prog cfg (.running (.expr (.ret (.rval v ty) (.callArgF sym fnTy' done [] :: frest)) ect mods) e b m os k1))
                (Sem.stepDet prog cfg (.running (.expr (.ret (.rval v ty) (.callArgF sym fnTy' done [] :: frest)) ect mods) e b m os k2))
              rw [stepDet_ret_rval_callArgF_nil, stepDet_ret_rval_callArgF_nil]
              exact ⟨k2, hk, rfl⟩
            | cons a rest' =>
              exact stepExprPure_lift hk _
                (stepDet_ret_rval_cons_fallback prog cfg v ty (.callArgF sym fnTy' done (a :: rest')) frest ect mods e b m os k1
                  (fun _ h => by cases h) (fun _ _ _ _ h hnil => by cases h; cases hnil))
                (stepDet_ret_rval_cons_fallback prog cfg v ty (.callArgF sym fnTy' done (a :: rest')) frest ect mods e b m os k2
                  (fun _ h => by cases h) (fun _ _ _ _ h hnil => by cases h; cases hnil))
          | _ =>
            exact stepExprPure_lift hk _
              (stepDet_ret_rval_cons_fallback prog cfg v ty _ frest ect mods e b m os k1
                (fun _ h => by cases h) (fun _ _ _ _ h => by cases h))
              (stepDet_ret_rval_cons_fallback prog cfg v ty _ frest ect mods e b m os k2
                (fun _ h => by cases h) (fun _ _ _ _ h => by cases h))
        | nil =>
          change DetStepLift env blks rt fnBody fs ctx k
            (Sem.stepDet prog cfg (.running (.expr (.ret (.rval v ty) []) ect mods) e b m os k1))
            (Sem.stepDet prog cfg (.running (.expr (.ret (.rval v ty) []) ect mods) e b m os k2))
          rw [stepDet_ret_rval_nil, stepDet_ret_rval_nil]
          cases ect with
          | discard => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | varInit d rest => exact ⟨k2, hk, rfl⟩
          | forStep c? stp? body =>
            dsimp only [DetStepLift]
            cases c? with
            | some _ => exact ⟨_, rfl, RunStateLift.inside hk⟩
            | none => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
          | branch t f =>
            dsimp only [DetStepLift]
            cases Sem.isTruthy v with
            | none => rfl
            | some bv => exact ⟨_, rfl, RunStateLift.inside hk⟩
          | whileCond c body | doWhileCond body c | forCond c _ body =>
            dsimp only [DetStepLift]
            cases Sem.isTruthy v with
            | none => rfl
            | some bv =>
              cases bv with
              | false => exact ⟨_, rfl, RunStateLift.inside hk⟩
              | true => exact ⟨_, rfl, RunStateLift.inside (ContLift.loop hk)⟩
          | switchScrut body =>
            dsimp only [DetStepLift]
            cases Sem.valAsInt? v with
            | none => rfl
            | some p =>
              dsimp only [Option.map]
              cases Sem.findSwitchTarget p.2 body with
              | none => exact ⟨_, rfl, RunStateLift.inside hk⟩
              | some tgt => exact ⟨_, rfl, RunStateLift.inside (ContLift.switchCont hk)⟩
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
              | none => simp [Option.map]
              | some cv =>
                simp only [Option.map_some]
                rcases ContLift.unwindReturn m b hk with
                  ⟨m', hu1, hu2, hrt1, hrt2⟩ | ⟨re, rb, rt', m', fs', ctx', k1', k2', hkl, hu1, hu2⟩
                · rw [hu1, hu2]
                  have hrtv : rt.isVoid = false :=
                    Bool.eq_false_iff.mpr (by rw [← hrt2]; exact hvoid)
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
      dsimp only [DetStepLift]
      rcases ContLift.unwindBreak m e b hk with
        ⟨hn1, hn2⟩ | ⟨e', b', m', k1', k2', hkl, hb1, hb2⟩
      · rw [hn1, hn2]; rfl
      · rw [hb1, hb2]; exact ⟨_, rfl, RunStateLift.inside hkl⟩
    | continueStmt =>
      dsimp only [DetStepLift]
      rcases ContLift.unwindContinue m e b hk with
        ⟨hn1, hn2⟩ | ⟨c?, stp?, body, isDo, e', b', m', k1', k2', hkl, hc1, hc2⟩
      · rw [hn1, hn2]; rfl
      · rw [hc1, hc2]
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

private theorem stepDet_ret_stop_void_any (prog : Prog) (cfg : PointerConfig)
    (env : Env) (v : Val) (rty rt : CTy) (m : Mem) (os : OSState) (hv : rt.isVoid = true) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval v rty) []) .returnVal []) env [] m os (.stop rt)) =
      some (.next (.returned .void m os)) := by
  rw [stepDet_ret_rval_nil]
  dsimp only
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

private theorem stepDet_ret_stop_undef (prog : Prog) (cfg : PointerConfig)
    (rt : CTy) (m : Mem) (os : OSState) (hnot : rt.isVoid = false) :
    Sem.stepDet prog cfg (.running (.expr (.ret (.rval .undef rt) []) .returnVal []) [] [] m os (.stop rt)) =
      none := by
  unfold Sem.stepDet
  dsimp only [bind, Option.bind]
  simp only [Sem.Cont.topRetTy, hnot, Bool.false_eq_true, ↓reduceIte, castVal_undef_none hnot,
    Option.map_none]

theorem wpTerm_runStateLift_safe {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    (hvoid : rt.isVoid = true → rt = .void)
    {Q_bot : Val → Mem → OSState → Prop} {Q_real : Val → Mem → OSState → Prop}
    {s1 s2 : Sem.RunState}
    (ht : C99.Proof.WPTerm prog cfg ext Q_bot s1)
    (hlift : RunStateLift env blks rt fnBody fs ctx k s1 s2)
    (hdone : ∀ ret m' os', Q_bot ret m' os' →
      Sem.Safe prog cfg ext (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k) ∧
      (∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext)
        (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k) (.returned r m'' os'') →
        Q_real r m'' os'')) :
    Sem.Safe prog cfg ext s2 ∧
    (∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext) s2 (.returned r m'' os'') → Q_real r m'' os'') := by
  induction ht generalizing s2 with
  | returned hq => cases hlift
  | @step s1 hnub1 hex1 hnext1 ih =>
    cases hlift with
    | @exitedVoid m' os' rty hrt hrty =>
      have hrt_eq : rt = .void := hvoid hrt
      subst hrt_eq
      rcases hrty with rfl | rfl <;>
        exact hdone .void m' os' ((hnext1 _ (.det (stepDet_ret_stop_void prog cfg [] _ .void m' os' hrt))).post (.refl _))
    | @exitedVal v m' os' hnot hcast =>
      exact hdone v m' os' ((hnext1 _ (.det (stepDet_ret_stop_val prog cfg [] rt rt v v m' os' hnot hcast))).post (.refl _))
    | @exitedUndef m' os' hnot =>
      exact False.elim ((hnext1 Sem.RunState.ub (.det_ub (stepDet_ret_stop_undef prog cfg rt m' os' hnot))).safe _ (.refl Sem.RunState.ub) rfl)
    | @inside ctrl e b m os k1 k2 hk =>
      have hnub2 : ¬ Sem.RunState.isUB (.running ctrl e b m os k2) := Bool.false_ne_true
      have hstep2 : ∀ s2', Sem.Step prog cfg ext (.running ctrl e b m os k2) s2' →
          Sem.Safe prog cfg ext s2' ∧
          (∀ r m'' os'', Sem.Star (Sem.Step prog cfg ext) s2' (.returned r m'' os'') → Q_real r m'' os'') := by
        intro s2' hs2'
        have hd := stepDet_contLift (prog := prog) (cfg := cfg) (ctrl := ctrl)
          (e := e) (b := b) (m := m) (os := os) hk
        cases hd1 : Sem.stepDet prog cfg (.running ctrl e b m os k1) with
        | none =>
          rw [hd1] at hd
          dsimp only [DetStepLift] at hd
          have hs1_ub : Sem.Step prog cfg ext (.running ctrl e b m os k1) Sem.RunState.ub := .det_ub hd1
          exact False.elim ((hnext1 Sem.RunState.ub hs1_ub).safe _ (.refl Sem.RunState.ub) rfl)
        | some d1 =>
          rw [hd1] at hd
          dsimp only [DetStepLift] at hd
          cases d1 with
          | next s1' =>
            obtain ⟨s2_det, hd2, hlift'⟩ := hd
            cases hs2' with
            | det hd2' =>
              rw [hd2] at hd2'; cases hd2'
              exact ih s1' (.det hd1) hlift'
            | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | allocStr str fs' ctx' mods' e' b' m' os' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | strLit hd2' hsz halloc =>
              rw [hd2] at hd2'; cases hd2'
              exact ih _ (.strLit hd1 hsz halloc) (RunStateLift.inside hk')
            | det hd2' | det_ub hd2' | localDecl hd2' | localDecl_ub hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | allocLocal d i? rest e' b' m' os' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | localDecl hd2' hsz hal hba halloc hwr =>
              rw [hd2] at hd2'; cases hd2'
              exact ih _ (.localDecl hd1 hsz hal hba halloc hwr) (RunStateLift.inside hk')
            | localDecl_ub hd2' hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim ((hnext1 Sem.RunState.ub (.localDecl_ub hd1 hbad)).safe _ (.refl Sem.RunState.ub) rfl)
            | det hd2' | det_ub hd2' | strLit hd2'
            | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
          | callFn sym fty args fs' ctx' e' b' m' os' k1' =>
            obtain ⟨k2', hk', hd2⟩ := hd
            cases hs2' with
            | call_internal hd2' hfn hcoerce hpush =>
              rw [hd2] at hd2'; cases hd2'
              exact ih _ (.call_internal hd1 hfn hcoerce hpush)
                (RunStateLift.inside (ContLift.callFrame hk'))
            | call_internal_ub hd2' hfn hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim ((hnext1 Sem.RunState.ub (.call_internal_ub hd1 hfn hbad)).safe _ (.refl Sem.RunState.ub) rfl)
            | call_ext hd2' hnfn hsig hcoerce hext =>
              rw [hd2] at hd2'; cases hd2'
              rename_i out'
              cases out' with
              | ub =>
                exact False.elim ((hnext1 Sem.RunState.ub (.call_ext hd1 hnfn hsig hcoerce hext)).safe _ (.refl Sem.RunState.ub) rfl)
              | ok ret m' os' =>
                exact ih _ (.call_ext hd1 hnfn hsig hcoerce hext) (RunStateLift.inside hk')
            | call_ext_ub hd2' hnfn hbad =>
              rw [hd2] at hd2'; cases hd2'
              exact False.elim ((hnext1 Sem.RunState.ub (.call_ext_ub hd1 hnfn hbad)).safe _ (.refl Sem.RunState.ub) rfl)
            | det hd2' | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2' =>
              rw [hd2] at hd2'; cases hd2'
      refine ⟨safe_of_step hnub2 (fun s2' h => (hstep2 s2' h).1), ?_⟩
      intro r m'' os'' hstar
      rcases star_destr hstar with hEq | ⟨s2', hs2', htail⟩
      · cases hEq
      · exact (hstep2 s2' hs2').2 r m'' os'' htail

theorem CallWPTermSpec.to_callSafeSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hspec : CallWPTermSpec prog cfg ext fn Pre Post)
    (hvoid : fn.retTy.isVoid = true → fn.retTy = .void)
    (hret : ∀ m os args ret m' os', Pre m os args → Post m os args ret m' os' →
      if fn.retTy.isVoid then ret = .void else Sem.castVal m' fn.retTy ret = some ret)
    (hbud : ∀ m os args ret m' os',
      Pre m os args → os.readBudget.isSome = true →
      Post m os args ret m' os' → os'.readBudget.isSome = true) :
    CallSafeSpec prog cfg ext fn Pre Post := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush hcont
  have ht_bot : C99.Proof.WPTerm prog cfg ext (fun ret m' os' => Post m os args ret m' os')
      (.running (.stmt fn.body) callEnv callBlks m1 os
        (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) := by
    refine hspec args [] [] m m1 os base callEnv callBlks [] .returnVal (.stop fn.retTy)
      (fun ret m' os' => Post m os args ret m' os') hpre hlen hpush ?_
    intro ret m' os' hpo
    have hrm := hret m os args ret m' os' hpre hpo
    by_cases hv : fn.retTy.isVoid = true
    · simp only [hv, ↓reduceIte] at hrm
      subst hrm
      exact C99.Proof.WPTerm.of_det (stepDet_ret_stop_void prog cfg [] fn.retTy fn.retTy m' os' hv) (.returned hpo)
    · have hnv : fn.retTy.isVoid = false := Bool.eq_false_iff.mpr hv
      simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hrm
      exact C99.Proof.WPTerm.of_det (stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy ret ret m' os' hnv hrm) (.returned hpo)
  have hsp := wpTerm_runStateLift_safe (env := env) (blks := blks) (rt := fn.retTy)
    (fnBody := fn.body) (fs := fs) (ctx := ctx) (k := k) hvoid
    (Q_bot := fun ret m' os' => Post m os args ret m' os') (Q_real := Q)
    ht_bot (RunStateLift.inside ContLift.base)
    (fun ret m' os' hpo => ⟨(hcont ret m' os' hpo).safe, fun r m'' os'' hst => (hcont ret m' os' hpo).post hst⟩)
  refine ⟨hsp.1, ?_, hsp.2⟩
  intro hb
  dsimp only [readBudgetIsSome] at hb
  refine hspec args env blks m m1 os base callEnv callBlks fs ctx k Q hpre hlen hpush ?_
  intro ret m' os' hpo
  exact (hcont ret m' os' hpo).2.1 (hbud m os args ret m' os' hpre hb hpo)

theorem CallSafeSpec.to_contractSafe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView} {fn : FnDef}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hnonvar : c.variadic = false ∧ fn.variadic = false)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, false))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hspec : CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext fn Pre Post)
    (hpreImp : ∀ v owned m os args,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      Pre m os args)
    (hpostImp : ∀ v owned m os args ret m' os',
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys false args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      Post m os args ret m' os' →
      ∃ cv,
        (if protoRetTy.isVoid = true then cv = .void
         else Sem.castVal m' protoRetTy ret = some cv) ∧
        (∃ owned' v',
          c.post prog.tags owned v m args cv m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c := by
  refine ZlibInv_to_ContractSafe hfn hname hnonvar hproto hptys hsimple ?_
  intro v owned m os args base callEnv callBlks m1 hInv hpre hawt hargDisj hpush
  have hlen : args.length = fn.params.length := by
    have h1 := hawt.1; simp only [Bool.false_eq_true, ↓reduceIte] at h1
    have h2 : fn.params.length = c.paramTys.length := by
      simpa using congrArg List.length hptys
    omega
  refine hspec args gEnv [] m m1 os base callEnv callBlks [] .returnVal (.stop protoRetTy) _
    (hpreImp v owned m os args hInv hpre hawt hargDisj) hlen hpush ?_
  intro ret m' os' hpo
  obtain ⟨cv, hcv, hres⟩ := hpostImp v owned m os args ret m' os' hInv hpre hawt hargDisj hpo
  by_cases hv : protoRetTy.isVoid = true
  · simp only [hv, ↓reduceIte] at hcv
    subst hcv
    exact WPSafe.of_det (stepDet_ret_stop_void_any prog Zlib.Spec.zlibPointerConfig gEnv ret fn.retTy protoRetTy m' os' hv)
      (WPSafe.returned hres)
  · have hnv : protoRetTy.isVoid = false := Bool.eq_false_iff.mpr hv
    simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hcv
    exact WPSafe.of_det (stepDet_ret_stop_val prog Zlib.Spec.zlibPointerConfig gEnv fn.retTy protoRetTy ret cv m' os' hnv hcv)
      (WPSafe.returned hres)

theorem CallSafeSpec.to_contractSafe_variadic
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {ext : ExtHandler} {userWrite : BlockSet}
    {c : FnContract Zlib.Spec.ClientView} {fn : FnDef}
    {protoRetTy : CTy} {protoParamTys : List CTy}
    {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hfn : prog.fns c.fnName = some fn)
    (hname : fn.name = c.fnName)
    (hvar : c.variadic = true ∧ fn.variadic = true)
    (hproto : prog.fnProtos c.fnName = some (protoRetTy, protoParamTys, true))
    (hptys : List.map (fun p => p.ty.unqual) fn.params = List.map CTy.unqual c.paramTys)
    (hsimple : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hspec : CallSafeSpec prog Zlib.Spec.zlibPointerConfig ext fn Pre Post)
    (hpreImp : ∀ v owned m os args,
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      Pre m os (args.take fn.params.length))
    (hpostImp : ∀ v owned m os args ret m' os',
      ZlibInv prog gEnv m0 os0 v owned m os →
      c.pre prog.tags owned v m args →
      Zlib.Spec.ArgsWellTyped prog c.paramTys true args →
      (∀ a ∈ args, Zlib.Spec.DisjointFrom a (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b)) →
      Post m os (args.take fn.params.length) ret m' os' →
      ∃ cv,
        (if protoRetTy.isVoid = true then cv = .void
         else Sem.castVal m' protoRetTy ret = some cv) ∧
        (∃ owned' v',
          c.post prog.tags owned v m args cv m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ c.modSet prog.tags owned v m args b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))) :
    Zlib.Spec.ContractSafe prog gEnv ext (ZlibInv prog gEnv m0 os0) userWrite c := by
  refine ZlibInv_to_ContractSafe_variadic hfn hname hvar hproto hptys hsimple ?_
  intro v owned m os args base callEnv callBlks m1 hInv hpre hawt hargDisj hpush
  have hlen : (args.take fn.params.length).length = fn.params.length := by
    have h1 := hawt.1; simp only [↓reduceIte] at h1
    have h2 : fn.params.length = c.paramTys.length := by
      simpa using congrArg List.length hptys
    simp only [List.length_take]; omega
  refine hspec (args.take fn.params.length) gEnv [] m m1 os base callEnv callBlks []
    .returnVal (.stop protoRetTy) _
    (hpreImp v owned m os args hInv hpre hawt hargDisj) hlen hpush ?_
  intro ret m' os' hpo
  obtain ⟨cv, hcv, hres⟩ := hpostImp v owned m os args ret m' os' hInv hpre hawt hargDisj hpo
  by_cases hv : protoRetTy.isVoid = true
  · simp only [hv, ↓reduceIte] at hcv
    subst hcv
    exact WPSafe.of_det (stepDet_ret_stop_void_any prog Zlib.Spec.zlibPointerConfig gEnv ret fn.retTy protoRetTy m' os' hv)
      (WPSafe.returned hres)
  · have hnv : protoRetTy.isVoid = false := Bool.eq_false_iff.mpr hv
    simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hcv
    exact WPSafe.of_det (stepDet_ret_stop_val prog Zlib.Spec.zlibPointerConfig gEnv fn.retTy protoRetTy ret cv m' os' hnv hcv)
      (WPSafe.returned hres)

/-! ### Finite-Reachability Loop Combinator (`Reach`) for `WPSafe` -/

inductive Reach (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (R : Sem.RunState → Prop) : Sem.RunState → Prop where
  | done {s} : R s → Reach prog cfg ext R s
  | step {s} :
      ¬ s.isUB →
      (∃ s', Sem.Step prog cfg ext s s') →
      (∀ s', Sem.Step prog cfg ext s s' → Reach prog cfg ext R s') →
      Reach prog cfg ext R s

def Reach1 (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (R : Sem.RunState → Prop) (s : Sem.RunState) : Prop :=
  ¬ s.isUB ∧ (∃ s', Sem.Step prog cfg ext s s') ∧ (∀ s', Sem.Step prog cfg ext s s' → Reach prog cfg ext R s')

theorem Reach.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {R1 R2 : Sem.RunState → Prop} {s : Sem.RunState}
    (hm : ∀ s', R1 s' → R2 s') (hr : Reach prog cfg ext R1 s) :
    Reach prog cfg ext R2 s := by
  induction hr with
  | done h => exact .done (hm _ h)
  | step hnub hex _ ih => exact .step hnub hex ih

theorem Reach.of_det {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {R : Sem.RunState → Prop} {s s' : Sem.RunState}
    (hd : Sem.stepDet prog cfg s = some (.next s'))
    (hr : Reach prog cfg ext R s') :
    Reach prog cfg ext R s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  refine .step hnub ⟨s', .det hd⟩ ?_
  intro s1 hs1
  cases hs1 with
  | det hd1 => rw [hd] at hd1; cases hd1; exact hr
  | det_ub hd1 | strLit hd1 | localDecl hd1 | localDecl_ub hd1
  | call_internal hd1 | call_internal_ub hd1 | call_ext hd1 | call_ext_ub hd1 =>
    rw [hd] at hd1; cases hd1

theorem Reach.of_exprPure {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {R : Sem.RunState → Prop}
    {es es' : Sem.ExprState} {ctx : Sem.ExprCtx} {mods mods' : ModSet}
    {env : Env} {blks : List BlockId} {m m' : Mem} {os : OSState} {k : Sem.Cont}
    (hp : Sem.stepExprPure prog cfg env m mods es = some (es', m', mods'))
    (hd : Sem.stepDet prog cfg (.running (.expr es ctx mods) env blks m os k) =
      some (.next (.running (.expr es' ctx mods') env blks m' os k)))
    (hr : Reach prog cfg ext R (.running (.expr es' ctx mods') env blks m' os k)) :
    Reach prog cfg ext R (.running (.expr es ctx mods) env blks m os k) :=
  let _ := hp
  Reach.of_det hd hr

theorem Reach.of_strLit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {R : Sem.RunState → Prop} {s : Sem.RunState}
    {str : String} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    (hd : Sem.stepDet prog cfg s = some (.allocStr str fs ctx mods env blks m os k))
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (hw : ∀ base bid m',
      m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') →
      Reach prog cfg ext R
        (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods) env blks m' os k)) :
    Reach prog cfg ext R s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  let p := m.alloc (str.utf8ByteSize + 1) 1 .ro .global 0
    (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)
  refine .step hnub ⟨_, .strLit hd hsz (base := 0) (bid := p.1) (m' := p.2) rfl⟩ ?_
  intro s1 hs1
  cases hs1 with
  | strLit hd1 _ halloc => rw [hd] at hd1; cases hd1; exact hw _ _ _ halloc
  | det hd1 | det_ub hd1 | localDecl hd1 | localDecl_ub hd1
  | call_internal hd1 | call_internal_ub hd1 | call_ext hd1 | call_ext_ub hd1 =>
    rw [hd] at hd1; cases hd1

theorem Reach.of_call_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {R : Sem.RunState → Prop} {s : Sem.RunState}
    {sym : String} {fnTy retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {k : Sem.Cont}
    (hd : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hnfn : prog.fns sym = none)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hex : ∃ ret m' os', ext sym coerced m os (.ok ret m' os'))
    (hnoub : ¬ ext sym coerced m os .ub)
    (hw : ∀ ret m' os', ext sym coerced m os (.ok ret m' os') →
      Reach prog cfg ext R (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    Reach prog cfg ext R s := by
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hd | returned _ _ _ => cases hd | running _ _ _ _ _ _ => exact Bool.false_ne_true
  obtain ⟨ret0, m0', os0', he0⟩ := hex
  refine .step hnub ⟨_, .call_ext hd hnfn hsig hcoerce he0⟩ ?_
  intro s1 hs1
  cases hs1 with
  | call_ext hd1 hnfn1 hsig1 hcoerce1 he1 =>
    rw [hd] at hd1; cases hd1
    rw [hsig] at hsig1; cases hsig1
    rw [hcoerce] at hcoerce1; cases hcoerce1
    rename_i out'
    cases out' with
    | ub => exact False.elim (hnoub he1)
    | ok ret m' os' => exact hw ret m' os' he1
  | call_ext_ub hd1 _ hbad =>
    rw [hd] at hd1; cases hd1
    exact False.elim (hbad ⟨retTy, paramTys, variadic, coerced, hsig, hcoerce⟩)
  | call_internal hd1 hfn | call_internal_ub hd1 hfn =>
    rw [hd] at hd1; cases hd1; rw [hnfn] at hfn; cases hfn
  | det hd1 | det_ub hd1 | strLit hd1 | localDecl hd1 | localDecl_ub hd1 =>
    rw [hd] at hd1; cases hd1

theorem wpTerm_runStateLift_reach {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {env : Env} {blks : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {k : Sem.Cont}
    (hvoid : rt.isVoid = true → rt = .void)
    {Q_bot : Val → Mem → OSState → Prop} {R : Sem.RunState → Prop}
    {s1 s2 : Sem.RunState}
    (ht : C99.Proof.WPTerm prog cfg ext Q_bot s1)
    (hlift : RunStateLift env blks rt fnBody fs ctx k s1 s2)
    (hdone : ∀ ret m' os', Q_bot ret m' os' →
      Reach prog cfg ext R (.running (.expr (.ret (.rval ret rt) fs) ctx []) env blks m' os' k)) :
    Reach prog cfg ext R s2 := by
  induction ht generalizing s2 with
  | returned _ => cases hlift
  | @step s1 hnub1 hex1 hnext1 ih =>
    cases hlift with
    | @exitedVoid m' os' rty hrt hrty =>
      have hrt_eq : rt = .void := hvoid hrt
      subst hrt_eq
      rcases hrty with rfl | rfl <;>
        exact hdone .void m' os' ((hnext1 _ (.det (stepDet_ret_stop_void prog cfg [] _ .void m' os' hrt))).post (.refl _))
    | @exitedVal v m' os' hnot hcast =>
      exact hdone v m' os' ((hnext1 _ (.det (stepDet_ret_stop_val prog cfg [] rt rt v v m' os' hnot hcast))).post (.refl _))
    | @exitedUndef m' os' hnot =>
      exact False.elim ((hnext1 Sem.RunState.ub (.det_ub (stepDet_ret_stop_undef prog cfg rt m' os' hnot))).safe _ (.refl Sem.RunState.ub) rfl)
    | @inside ctrl e b m os k1 k2 hk =>
      have hnub2 : ¬ Sem.RunState.isUB (.running ctrl e b m os k2) := Bool.false_ne_true
      have hd := stepDet_contLift (prog := prog) (cfg := cfg) (ctrl := ctrl)
        (e := e) (b := b) (m := m) (os := os) hk
      have hex2 : ∃ s2', Sem.Step prog cfg ext (.running ctrl e b m os k2) s2' := by
        obtain ⟨s1', hs1'⟩ := hex1
        cases hs1' with
        | det hd1 =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd; obtain ⟨s2', hd2, _⟩ := hd
          exact ⟨s2', .det hd2⟩
        | det_ub hd1 =>
          exact False.elim ((hnext1 Sem.RunState.ub (.det_ub hd1)).safe _ (.refl Sem.RunState.ub) rfl)
        | strLit hd1 hsz halloc =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd; obtain ⟨k2', _, hd2⟩ := hd
          exact ⟨_, .strLit hd2 hsz halloc⟩
        | localDecl hd1 hsz hal hba halloc hwr =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd; obtain ⟨k2', _, hd2⟩ := hd
          exact ⟨_, .localDecl hd2 hsz hal hba halloc hwr⟩
        | localDecl_ub hd1 hbad =>
          exact False.elim ((hnext1 Sem.RunState.ub (.localDecl_ub hd1 hbad)).safe _ (.refl Sem.RunState.ub) rfl)
        | call_internal hd1 hfn hcoerce hpush =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd; obtain ⟨k2', _, hd2⟩ := hd
          exact ⟨_, .call_internal hd2 hfn hcoerce hpush⟩
        | call_internal_ub hd1 hfn hbad =>
          exact False.elim ((hnext1 Sem.RunState.ub (.call_internal_ub hd1 hfn hbad)).safe _ (.refl Sem.RunState.ub) rfl)
        | call_ext hd1 hnfn hsig hcoerce hext =>
          rw [hd1] at hd; dsimp only [DetStepLift] at hd; obtain ⟨k2', _, hd2⟩ := hd
          exact ⟨_, .call_ext hd2 hnfn hsig hcoerce hext⟩
        | call_ext_ub hd1 hnfn hbad =>
          exact False.elim ((hnext1 Sem.RunState.ub (.call_ext_ub hd1 hnfn hbad)).safe _ (.refl Sem.RunState.ub) rfl)
      refine .step hnub2 hex2 ?_
      intro s2' hs2'
      cases hd1 : Sem.stepDet prog cfg (.running ctrl e b m os k1) with
      | none =>
        exact False.elim ((hnext1 Sem.RunState.ub (.det_ub hd1)).safe _ (.refl Sem.RunState.ub) rfl)
      | some d1 =>
        rw [hd1] at hd
        dsimp only [DetStepLift] at hd
        cases d1 with
        | next s1' =>
          obtain ⟨s2_det, hd2, hlift'⟩ := hd
          cases hs2' with
          | det hd2' => rw [hd2] at hd2'; cases hd2'; exact ih s1' (.det hd1) hlift'
          | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2'
          | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
            rw [hd2] at hd2'; cases hd2'
        | allocStr str fs' ctx' mods' e' b' m' os' k1' =>
          obtain ⟨k2', hk', hd2⟩ := hd
          cases hs2' with
          | strLit hd2' hsz halloc =>
            rw [hd2] at hd2'; cases hd2'
            exact ih _ (.strLit hd1 hsz halloc) (RunStateLift.inside hk')
          | det hd2' | det_ub hd2' | localDecl hd2' | localDecl_ub hd2'
          | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
            rw [hd2] at hd2'; cases hd2'
        | allocLocal d i? rest e' b' m' os' k1' =>
          obtain ⟨k2', hk', hd2⟩ := hd
          cases hs2' with
          | localDecl hd2' hsz hal hba halloc hwr =>
            rw [hd2] at hd2'; cases hd2'
            exact ih _ (.localDecl hd1 hsz hal hba halloc hwr) (RunStateLift.inside hk')
          | localDecl_ub hd2' hbad =>
            rw [hd2] at hd2'; cases hd2'
            exact False.elim ((hnext1 Sem.RunState.ub (.localDecl_ub hd1 hbad)).safe _ (.refl Sem.RunState.ub) rfl)
          | det hd2' | det_ub hd2' | strLit hd2'
          | call_internal hd2' | call_internal_ub hd2' | call_ext hd2' | call_ext_ub hd2' =>
            rw [hd2] at hd2'; cases hd2'
        | callFn sym fty args fs' ctx' e' b' m' os' k1' =>
          obtain ⟨k2', hk', hd2⟩ := hd
          cases hs2' with
          | call_internal hd2' hfn hcoerce hpush =>
            rw [hd2] at hd2'; cases hd2'
            exact ih _ (.call_internal hd1 hfn hcoerce hpush)
              (RunStateLift.inside (ContLift.callFrame hk'))
          | call_internal_ub hd2' hfn hbad =>
            rw [hd2] at hd2'; cases hd2'
            exact False.elim ((hnext1 Sem.RunState.ub (.call_internal_ub hd1 hfn hbad)).safe _ (.refl Sem.RunState.ub) rfl)
          | call_ext hd2' hnfn hsig hcoerce hext =>
            rw [hd2] at hd2'; cases hd2'
            rename_i out'
            cases out' with
            | ub =>
              exact False.elim ((hnext1 Sem.RunState.ub (.call_ext hd1 hnfn hsig hcoerce hext)).safe _ (.refl Sem.RunState.ub) rfl)
            | ok ret m' os' =>
              exact ih _ (.call_ext hd1 hnfn hsig hcoerce hext) (RunStateLift.inside hk')
          | call_ext_ub hd2' hnfn hbad =>
            rw [hd2] at hd2'; cases hd2'
            exact False.elim ((hnext1 Sem.RunState.ub (.call_ext_ub hd1 hnfn hbad)).safe _ (.refl Sem.RunState.ub) rfl)
          | det hd2' | det_ub hd2' | strLit hd2' | localDecl hd2' | localDecl_ub hd2' =>
            rw [hd2] at hd2'; cases hd2'

theorem CallWPTermSpec.call_reach
    {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {fn : FnDef} {Pre : Mem → OSState → List Val → Prop}
    {Post : Mem → OSState → List Val → Val → Mem → OSState → Prop}
    (hspec : CallWPTermSpec prog cfg ext fn Pre Post)
    (hvoid : fn.retTy.isVoid = true → fn.retTy = .void)
    (hret : ∀ m os args ret m' os', Pre m os args → Post m os args ret m' os' →
      if fn.retTy.isVoid then ret = .void else Sem.castVal m' fn.retTy ret = some ret)
    {R : Sem.RunState → Prop} {s : Sem.RunState} {sym : String} {fnTy : CTy}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    (hstep : Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false argVals = some coerced)
    (hpre : Pre m os coerced)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (hcont : ∀ ret m' os', Post m os coerced ret m' os' →
      Reach prog cfg ext R
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os' k)) :
    Reach prog cfg ext R s := by
  have ⟨hlenC, _⟩ := coerceCallArgs_length hcoerce
  simp only [List.length_map] at hlenC
  have htake : List.take fn.params.length coerced = coerced :=
    List.take_of_length_le (by omega)
  have hawt : ArgsHaveCTy (fn.params.map (·.ty)) false coerced :=
    coerceCallArgs_produces_argsWellTyped hcoerce
  have hex0 : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0 (fn.params.zip coerced)
        (prog.fnStatics sym ++ prog.globalEnv) [] = some (callEnv0, callBlks0, m0') := by
    rw [← hsym]
    exact pushCallParams_exists_base0 prog.tags hsimp hawt
  obtain ⟨callEnv0, callBlks0, m0', hpush0⟩ := hex0
  have hnub : ¬ s.isUB := by
    cases s with | ub => cases hstep | returned _ _ _ => cases hstep | running _ _ _ _ _ _ => exact Bool.false_ne_true
  have hcoerceV : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced := by
    simpa [hnonvar] using hcoerce
  refine .step hnub ⟨_, .call_internal hstep hfn hcoerceV (by simpa [htake] using hpush0)⟩ ?_
  intro s1 hs1
  cases hs1 with
  | call_internal hd1 hfn1 hcoerce1 hpush1 =>
    rw [hstep] at hd1; cases hd1
    rw [hfn] at hfn1; cases hfn1
    rw [hcoerceV] at hcoerce1; cases hcoerce1
    rw [htake, ← hsym] at hpush1
    rename_i callEnv1 callBlks1 base1 m1'
    have ht_bot : C99.Proof.WPTerm prog cfg ext (fun ret m' os' => Post m os coerced ret m' os')
        (.running (.stmt fn.body) callEnv1 callBlks1 m1' os
          (.callFrame [] [] fn.retTy fn.body [] .returnVal (.stop fn.retTy))) := by
      refine hspec coerced [] [] m m1' os base1 callEnv1 callBlks1 [] .returnVal (.stop fn.retTy) _
        hpre hlenC hpush1 ?_
      intro ret m' os' hpo
      have hrm := hret m os coerced ret m' os' hpre hpo
      by_cases hv : fn.retTy.isVoid = true
      · simp only [hv, ↓reduceIte] at hrm; subst hrm
        exact C99.Proof.WPTerm.of_det (stepDet_ret_stop_void prog cfg [] fn.retTy fn.retTy m' os' hv) (.returned hpo)
      · have hnv : fn.retTy.isVoid = false := Bool.eq_false_iff.mpr hv
        simp only [hnv, Bool.false_eq_true, ↓reduceIte] at hrm
        exact C99.Proof.WPTerm.of_det (stepDet_ret_stop_val prog cfg [] fn.retTy fn.retTy ret ret m' os' hnv hrm) (.returned hpo)
    exact wpTerm_runStateLift_reach hvoid ht_bot (RunStateLift.inside ContLift.base) hcont
  | call_internal_ub hd1 hfn1 hbad =>
    rw [hstep] at hd1; cases hd1; rw [hfn] at hfn1; cases hfn1
    exact False.elim (hbad coerced (fun _ => 0) callEnv0 callBlks0 m0'
      (by simpa [hnonvar] using hcoerce) (by simpa [htake] using hpush0))
  | call_ext hd1 hnfn1 | call_ext_ub hd1 hnfn1 =>
    rw [hstep] at hd1; cases hd1; rw [hfn] at hnfn1; cases hnfn1
  | det hd1 | det_ub hd1 | strLit hd1 | localDecl hd1 | localDecl_ub hd1 =>
    rw [hstep] at hd1; cases hd1

theorem WPSafe.of_reach_loop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {LoopState : Sem.RunState → Prop} {s0 : Sem.RunState}
    (h0 : LoopState s0)
    (hloop : ∀ s, LoopState s →
      Reach1 prog cfg ext (fun s' => LoopState s' ∨ WPSafe prog cfg ext Q s') s)
    (hterm : readBudgetIsSome s0 → C99.Proof.WPTerm prog cfg ext Q s0) :
    WPSafe prog cfg ext Q s0 := by
  let Inv : Sem.RunState → Prop :=
    Reach prog cfg ext (fun s' => LoopState s' ∨ WPSafe prog cfg ext Q s')
  refine WPSafe.of_inv
    (@Reach.done prog cfg ext (fun s' => LoopState s' ∨ WPSafe prog cfg ext Q s') s0 (Or.inl h0))
    ?_ hterm
  intro s hs
  cases hs with
  | done hbranch =>
    rcases hbranch with hl | hwp
    · obtain ⟨hnub, hex, hnext⟩ := hloop s hl
      refine ⟨hnub, ?_, fun s' hstep => Or.inl (hnext s' hstep)⟩
      intro ret m os heq
      subst heq
      obtain ⟨s', hst⟩ := hex
      exact False.elim (C99.Proof.step_not_returned hst)
    · refine ⟨hwp.safe _ (.refl s), fun ret m os heq => ?_, fun s' hstep => ?_⟩
      · subst heq; exact hwp.post (.refl _)
      · exact Or.inr ⟨fun s'' hst => hwp.safe _ (C99.Proof.star_head hstep hst),
          fun ret m os hst => hwp.post (C99.Proof.star_head hstep hst)⟩
  | step hnub hex hnext =>
    refine ⟨hnub, ?_, fun s' hstep => Or.inl (hnext s' hstep)⟩
    intro ret m os heq
    subst heq
    obtain ⟨s', hst⟩ := hex
    exact False.elim (C99.Proof.step_not_returned hst)

/-! ### Internal `ZALLOC` / `ZFREE` & `SafeUserCallbacks` Combinators -/

theorem zcalloc_internal_call
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} {userExt : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0)
    {s : Sem.RunState} {fnTy : CTy} {argVals : List (Val × CTy)}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    {op : Val} {items size : BitVec 32}
    (hstep : Sem.stepDet prog Zlib.Spec.zlibPointerConfig s =
      some (.callFn "zcalloc" fnTy argVals fs ctx env blks m os k))
    (hcoerce : Sem.coerceCallArgs m (Zlib.Zutil.zutilTU_fn_zcalloc.params.map (·.ty)) false argVals =
      some [op, .int .u32 items, .int .u32 size])
    (hop : op = .null ∨ ∃ b off, op = .ptr b off)
    (hcont : ∀ ret m', ZcallocPost m items size ret m' →
      C99.Proof.WPTerm prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q
        (.running (.expr (.ret (.rval ret Zlib.Zutil.zutilTU_fn_zcalloc.retTy) fs) ctx [])
          env blks m' os k)) :
    C99.Proof.WPTerm prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q s :=
  (zcalloc_spec hlib).call hstep (prog_fns_zcalloc hlib) rfl rfl hcoerce
    ⟨op, items, size, rfl, hop⟩ zcalloc_params_simple hcont

theorem zcalloc_internal_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} {userExt : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0)
    {s : Sem.RunState} {fnTy : CTy} {argVals : List (Val × CTy)}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    {op : Val} {items size : BitVec 32}
    (hstep : Sem.stepDet prog Zlib.Spec.zlibPointerConfig s =
      some (.callFn "zcalloc" fnTy argVals fs ctx env blks m os k))
    (hcoerce : Sem.coerceCallArgs m (Zlib.Zutil.zutilTU_fn_zcalloc.params.map (·.ty)) false argVals =
      some [op, .int .u32 items, .int .u32 size])
    (hop : op = .null ∨ ∃ b off, op = .ptr b off)
    (hcont : ∀ ret m', ZcallocPost m items size ret m' →
      WPSafe prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q
        (.running (.expr (.ret (.rval ret Zlib.Zutil.zutilTU_fn_zcalloc.retTy) fs) ctx [])
          env blks m' os k)) :
    WPSafe prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q s := by
  have hcw : CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Zutil.zutilTU_fn_zcalloc
      (fun _ _ args => ∃ op items size,
        args = [op, .int .u32 items, .int .u32 size] ∧ (op = .null ∨ ∃ b off, op = .ptr b off))
      (fun m os args ret m' os' => os' = os ∧ match args with
        | [_, .int .u32 items, .int .u32 size] => ZcallocPost m items size ret m'
        | _ => False) :=
    (zcalloc_spec hlib).to_callWPTermSpec
  have hcs := hcw.to_callSafeSpec (by simp [Zlib.Zutil.zutilTU_fn_zcalloc, CTy.isVoid, CTy.unqual])
    (by
      intro m_ os_ args_ ret_ m'_ os'_ hpre hpo
      rcases hpre with ⟨op', items', size', rfl, _⟩
      rcases hpo with ⟨rfl, hzc⟩
      simp only [Zlib.Zutil.zutilTU_fn_zcalloc, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte]
      rcases hzc with ⟨rfl, _⟩ | ⟨bid, _, rfl, _⟩ <;> rfl)
    (fun _ _ _ _ _ _ _ hbud ⟨rfl, _⟩ => hbud)
  exact hcs.call hstep (prog_fns_zcalloc hlib) rfl rfl hcoerce
    ⟨op, items, size, rfl, hop⟩ zcalloc_params_simple
    (fun ret m' os' ⟨hos, hzc⟩ => hos ▸ hcont ret m' hzc)

theorem zcfree_internal_call
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} {userExt : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0)
    {s : Sem.RunState} {fnTy : CTy} {argVals : List (Val × CTy)}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    {op ptr : Val}
    (hstep : Sem.stepDet prog Zlib.Spec.zlibPointerConfig s =
      some (.callFn "zcfree" fnTy argVals fs ctx env blks m os k))
    (hcoerce : Sem.coerceCallArgs m (Zlib.Zutil.zutilTU_fn_zcfree.params.map (·.ty)) false argVals =
      some [op, ptr])
    (hop : op = .null ∨ ∃ b off, op = .ptr b off)
    (hfree : FreePre m ptr)
    (hcont : ∀ ret m', ZcfreePost m ptr ret m' →
      C99.Proof.WPTerm prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q
        (.running (.expr (.ret (.rval ret Zlib.Zutil.zutilTU_fn_zcfree.retTy) fs) ctx [])
          env blks m' os k)) :
    C99.Proof.WPTerm prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q s :=
  (zcfree_spec hlib).call hstep (prog_fns_zcfree hlib) rfl rfl hcoerce
    ⟨op, ptr, rfl, hop, hfree⟩ zcfree_params_simple hcont

theorem zcfree_internal_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState} {userExt : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0)
    {s : Sem.RunState} {fnTy : CTy} {argVals : List (Val × CTy)}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    {op ptr : Val}
    (hstep : Sem.stepDet prog Zlib.Spec.zlibPointerConfig s =
      some (.callFn "zcfree" fnTy argVals fs ctx env blks m os k))
    (hcoerce : Sem.coerceCallArgs m (Zlib.Zutil.zutilTU_fn_zcfree.params.map (·.ty)) false argVals =
      some [op, ptr])
    (hop : op = .null ∨ ∃ b off, op = .ptr b off)
    (hfree : FreePre m ptr)
    (hcont : ∀ ret m', ZcfreePost m ptr ret m' →
      WPSafe prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q
        (.running (.expr (.ret (.rval ret Zlib.Zutil.zutilTU_fn_zcfree.retTy) fs) ctx [])
          env blks m' os k)) :
    WPSafe prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q s := by
  have hcw : CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Zutil.zutilTU_fn_zcfree
      (fun m _ args => ∃ op ptr,
        args = [op, ptr] ∧ (op = .null ∨ ∃ b off, op = .ptr b off) ∧ FreePre m ptr)
      (fun m os args ret m' os' => os' = os ∧ match args with
        | [_, ptr] => ZcfreePost m ptr ret m'
        | _ => False) :=
    (zcfree_spec hlib).to_callWPTermSpec
  have hcs := hcw.to_callSafeSpec (by simp [Zlib.Zutil.zutilTU_fn_zcfree, CTy.isVoid])
    (by
      intro m_ os_ args_ ret_ m'_ os'_ hpre hpo
      rcases hpre with ⟨op', ptr', rfl, _⟩
      rcases hpo with ⟨rfl, hzc⟩
      simp only [Zlib.Zutil.zutilTU_fn_zcfree, CTy.isVoid, CTy.unqual, ↓reduceIte]
      exact hzc.1)
    (fun _ _ _ _ _ _ _ hbud ⟨rfl, _⟩ => hbud)
  exact hcs.call hstep (prog_fns_zcfree hlib) rfl rfl hcoerce
    ⟨op, ptr, rfl, hop, hfree⟩ zcfree_params_simple
    (fun ret m' os' ⟨hos, hzc⟩ => hos ▸ hcont ret m' hzc)

theorem ZcallocPost.fresh_not_owned
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m m' : Mem} {os : OSState}
    {items size : BitVec 32} {bid : BlockId}
    (hinv : ZlibInv prog gEnv m0 os0 v owned m os)
    (hp : ZcallocPost m items size (.ptr bid 0) m') :
    ¬ owned bid ∧ (m0.blocks bid).isNone = true ∧ bid ≠ os.errnoBlk ∧ os.strerrorBlk ≠ some bid := by
  rcases hp with ⟨hc, _⟩ | ⟨bid', _, hinj, hnone, _⟩
  · cases hc
  · cases hinj
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ho
      have hact := hinv.toBaseInv.ownedActive bid ho
      rw [hnone] at hact
      cases hact
    · cases hm0 : m0.blocks bid with
      | none => rfl
      | some gblk =>
        exfalso
        by_cases herr : bid = os0.errnoBlk
        · subst herr
          rcases hinv.toBaseInv.errnoValid with ⟨eblk, heblk, _⟩
          rw [hinv.toBaseInv.errnoBlkEq, hnone] at heblk
          cases heblk
        · have hro := hinv.toBaseInv.roGlobals bid (by simp [hm0]) herr
          rw [hro, hm0] at hnone
          cases hnone
    · rcases hinv.toBaseInv.errnoValid with ⟨eblk, heblk, _⟩
      intro heq
      rw [← heq, hnone] at heblk
      cases heblk
    · intro hstr
      obtain ⟨_, _, _, _, hblk, _⟩ := hinv.strerrorValid hstr
      rw [hnone] at hblk
      cases hblk

theorem zlibExt_userExt {userExt : ExtHandler} {sym : String}
    (hnl : sym ≠ "LSEEK") (hnstd : Zlib.Spec.isStdLibcSym sym = false) :
    Zlib.Spec.zlibExt userExt sym = userExt sym := by
  funext args m os out
  simp [Zlib.Spec.zlibExt, hnl, hnstd]

theorem safeUserCallbacks_framePreserved {tags : TypeEnv} {m0 : Mem} {v : ClientView}
    {owned userWrite : BlockSet} {userExt : ExtHandler}
    {sym : String} {args : List Val} {m m' : Mem} {os os' : OSState} {ret : Val}
    (hsafe : Zlib.Spec.SafeUserCallbacks tags m0 v owned userWrite userExt)
    (hext : userExt sym args m os (.ok ret m' os')) :
    os'.errnoBlk = os.errnoBlk ∧
    os'.strerrorBlk = os.strerrorBlk ∧
    Zlib.Spec.FramePreserved m m' (fun b =>
      ¬ Zlib.Spec.LibProtected m0 owned os m b ∧ (∀ k, (b, k) ∉ v.streams) ∧
      (∀ sb, (sb, .inflateBack) ∈ v.streams →
        Zlib.Spec.PtrBlock ((Zlib.Spec.readField? tags m ((Zlib.Spec.readField? tags m (.ptr sb 0) "z_stream_s" "state").getD .null)
          "inflate_state" "window").getD .null) ≠ some b) ∧
      (userWrite b ∨ (m.blocks b).isNone ∨
        (∃ op noff, args = [op, .ptr b noff]))) ∧
    Zlib.Spec.NoHeapLeak m m' owned :=
  let h := (hsafe.2 sym args m os (.ok ret m' os') hext).2 ret m' os' rfl
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem safeUserCallbacks_inFunc {tags : TypeEnv} {m0 : Mem} {v : ClientView}
    {owned userWrite : BlockSet} {userExt : ExtHandler}
    {sym : String} {op : Val} {nb : BlockId} {noff : Int64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (hsafe : Zlib.Spec.SafeUserCallbacks tags m0 v owned userWrite userExt)
    (hext : userExt sym [op, .ptr nb noff] m os (.ok ret m' os')) :
    ∃ avail : BitVec 32, ret = .int .u32 avail ∧
      (avail.toNat = 0 ∨ ∃ bs pb po, m'.readBytes nb noff 8 = some bs ∧
        Mem.decodePtr bs = some (.ptr pb po) ∧ Readable m' (.ptr pb po) avail.toNat ∧
        ¬ Zlib.Spec.LibProtected m0 owned os m' pb ∧ (∀ k, (pb, k) ∉ v.streams) ∧
        (∀ sb, (sb, .inflateBack) ∈ v.streams →
          Zlib.Spec.PtrBlock ((Zlib.Spec.readField? tags m' ((Zlib.Spec.readField? tags m' (.ptr sb 0) "z_stream_s" "state").getD .null)
            "inflate_state" "window").getD .null) ≠ some pb) ∧
        (∀ blk, m'.blocks pb = some blk → blk.kind ≠ .stack)) ∧
      (∀ k, os.readBudget = some k → ∃ k', os'.readBudget = some k' ∧ (avail.toNat > 0 → k' < k)) :=
  (hsafe.2 sym [op, .ptr nb noff] m os (.ok ret m' os') hext).2 ret m' os' rfl |>.2.2.2.2.1 op nb noff rfl

theorem safeUserCallbacks_outFunc {tags : TypeEnv} {m0 : Mem} {v : ClientView}
    {owned userWrite : BlockSet} {userExt : ExtHandler}
    {sym : String} {op buf len : Val}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (hsafe : Zlib.Spec.SafeUserCallbacks tags m0 v owned userWrite userExt)
    (hext : userExt sym [op, buf, len] m os (.ok ret m' os')) :
    (∃ r : BitVec 32, ret = .int .i32 r) ∧ os'.readBudget = os.readBudget :=
  (hsafe.2 sym [op, buf, len] m os (.ok ret m' os') hext).2 ret m' os' rfl |>.2.2.2.2.2 op buf len rfl

theorem user_callback_wpTerm
    {prog : Prog} {m0 : Mem} {v : ClientView} {owned userWrite : BlockSet} {userExt : ExtHandler}
    (hsafe : Zlib.Spec.SafeUserCallbacks prog.tags m0 v owned userWrite userExt)
    {s : Sem.RunState} {sym : String} {fnTy retTy : CTy}
    {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    (hstep : Sem.stepDet prog Zlib.Spec.zlibPointerConfig s =
      some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hnfn : prog.fns sym = none)
    (hnl : sym ≠ "LSEEK")
    (hnstd : Zlib.Spec.isStdLibcSym sym = false)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hex : ∃ ret m' os', userExt sym coerced m os (.ok ret m' os'))
    (hcont : ∀ ret m' os', userExt sym coerced m os (.ok ret m' os') →
      C99.Proof.WPTerm prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q
        (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    C99.Proof.WPTerm prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q s := by
  have hze : Zlib.Spec.zlibExt userExt sym = userExt sym := zlibExt_userExt hnl hnstd
  have hnoub : ¬ Zlib.Spec.zlibExt userExt sym coerced m os .ub := by
    rw [hze]
    intro hub
    exact (hsafe.2 sym coerced m os .ub hub).1 rfl
  refine C99.Proof.WPTerm.of_call_ext hstep hnfn hsig hcoerce ?_ hnoub ?_
  · rcases hex with ⟨ret, m', os', he⟩
    exact ⟨ret, m', os', by rw [hze]; exact he⟩
  · intro ret m' os' he
    rw [hze] at he
    exact hcont ret m' os' he

theorem user_callback_wpSafe
    {prog : Prog} {m0 : Mem} {v : ClientView} {owned userWrite : BlockSet} {userExt : ExtHandler}
    (hsafe : Zlib.Spec.SafeUserCallbacks prog.tags m0 v owned userWrite userExt)
    {s : Sem.RunState} {sym : String} {fnTy retTy : CTy}
    {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {Q : Val → Mem → OSState → Prop}
    (hstep : Sem.stepDet prog Zlib.Spec.zlibPointerConfig s =
      some (.callFn sym fnTy argVals fs ctx env blks m os k))
    (hnfn : prog.fns sym = none)
    (hnl : sym ≠ "LSEEK")
    (hnstd : Zlib.Spec.isStdLibcSym sym = false)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hterm : readBudgetIsSome s →
      (∃ ret m' os', userExt sym coerced m os (.ok ret m' os')) ∧
      ∀ ret m' os', userExt sym coerced m os (.ok ret m' os') →
        os'.readBudget.isSome = true)
    (hcont : ∀ ret m' os', userExt sym coerced m os (.ok ret m' os') →
      WPSafe prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q
        (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    WPSafe prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt) Q s := by
  have hze : Zlib.Spec.zlibExt userExt sym = userExt sym := zlibExt_userExt hnl hnstd
  have hnoub : ¬ Zlib.Spec.zlibExt userExt sym coerced m os .ub := by
    rw [hze]
    intro hub
    exact (hsafe.2 sym coerced m os .ub hub).1 rfl
  refine WPSafe.of_call_ext hstep hnfn hsig hcoerce hnoub ?_ ?_
  · intro ret m' os' he
    rw [hze] at he
    exact hcont ret m' os' he
  · intro hb
    obtain ⟨hex, hbud⟩ := hterm hb
    refine ⟨?_, ?_⟩
    · rcases hex with ⟨ret, m', os', he⟩
      exact ⟨ret, m', os', by rw [hze]; exact he⟩
    · intro ret m' os' he
      rw [hze] at he
      exact (hcont ret m' os' he).2.1 (hbud ret m' os' he)

/-! ## 7. Decoupled Cross-Module Spec Records (`structure *Specs`) -/

/-- Minimal global/OS environment invariant sufficient for all internal Wave 2–4 helpers
(independent of any external `ClientView` or `owned` partition, so stack-local
`uncompress2`/`compress2` streams and embedded `gz_state.strm` reuse the exact same specs). -/
def LibGlobalsOk (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) : Prop :=
  InitLibzAllProps prog gEnv m0 os0 ∧
  NonErrnoROGlobal os0.errnoBlk m0 ∧
  BaseInv m0 os0 Zlib.Spec.ClientView.empty (fun _ => False) m os

theorem ZlibInv.toLibGlobalsOk {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {v : ClientView} {owned : BlockSet} {m : Mem} {os : OSState}
    (h : ZlibInv prog gEnv m0 os0 v owned m os) :
    LibGlobalsOk prog gEnv m0 os0 m os := by
  have hb := h.toBaseInv
  refine ⟨h.toAllProps, h.2.2.1,
    hb.roGlobals, hb.errnoBlkEq, hb.errnoValid, (fun _ hf => False.elim hf),
    (fun _ _ hf => False.elim hf)⟩

theorem LibGlobalsOk.roExt {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {m m' : Mem} {os : OSState}
    (h : LibGlobalsOk prog gEnv m0 os0 m os) (hro : C99.Proof.ROExt m m') :
    LibGlobalsOk prog gEnv m0 os0 m' os :=
  ⟨h.1, h.2.1, BaseInv.roExt h.2.2 hro⟩

theorem LibGlobalsOk.of_framePreserved {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {m m' : Mem} {os os' : OSState} {modSet : BlockSet}
    (h : LibGlobalsOk prog gEnv m0 os0 m os)
    (hfp : FramePreserved m m' modSet)
    (hnom0 : ∀ b, (m0.blocks b).isSome = true → b ≠ os0.errnoBlk → ¬ modSet b)
    (herrEq : os'.errnoBlk = os.errnoBlk)
    (herrOk : ∃ blk, m'.blocks os'.errnoBlk = some blk ∧
      blk.size = 4 ∧ blk.align = 4 ∧ blk.perm = .rw ∧ blk.kind = .global) :
    LibGlobalsOk prog gEnv m0 os0 m' os' := by
  refine ⟨h.1, h.2.1, ?_, herrEq.trans h.2.2.errnoBlkEq, herrOk, (fun _ hf => False.elim hf),
    (fun _ _ hf => False.elim hf)⟩
  intro b hm0 hne
  have hm_old : (m.blocks b).isSome = true := by
    rw [h.2.2.roGlobals b hm0 hne]
    exact hm0
  exact (hfp.1 b hm_old (hnom0 b hm0 hne)).trans (h.2.2.roGlobals b hm0 hne)

/-- Two byte ranges `(b1, off1, len1)` and `(b2, off2, len2)` do not overlap in memory. -/
def DisjointByteRanges (b1 : BlockId) (off1 : Int64) (len1 : Nat)
    (b2 : BlockId) (off2 : Int64) (len2 : Nat) : Prop :=
  b1 ≠ b2 ∨ off1.toInt + len1 ≤ off2.toInt ∨ off2.toInt + len2 ≤ off1.toInt

/-- Helper predicate: block set `bs` is pairwise distinct from `(m0.blocks ·).isSome` and `errnoBlk`. -/
def HeapBlocksFreshFromLib (m0 : Mem) (os0 : OSState) (bs : List BlockId) : Prop :=
  ∀ b ∈ bs, (m0.blocks b).isNone = true ∧ b ≠ os0.errnoBlk

/-- Canonical C `struct` type of a compiled Huffman `code` entry (`inftrees.h`). -/
def huffCodeCTy : CTy :=
  .anonStruct [("op", .int .u8), ("bits", .int .u8), ("val", .int .u16)]

/-- Minimum capacity in `code` entries required by `inflate_table` for each `codetype`. -/
def inflateTableMinCap : Nat → Nat
  | 0 => 592
  | 1 => 852
  | _ => 592

/-- Precondition for `inflate_table(type, lens, codes, table, bits, work)`. -/
def InflateTablePre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  ∃ (typeCode : BitVec 32) (lensPtr : Val) (codesVal : BitVec 32)
    (tablePtr bitsPtr workPtr : Val)
    (lb tpb bpb tb wb : BlockId) (loff tpo bpo toff woff : Int64)
    (tblk wblk : Block) (cap root0 : Nat),
    args = [.int .u32 typeCode, lensPtr, .int .u32 codesVal, tablePtr, bitsPtr, workPtr] ∧
    typeCode.toNat ≤ 2 ∧
    let codes := codesVal.toNat
    (typeCode.toNat = 0 → 1 ≤ codes ∧ codes ≤ 19) ∧
    (typeCode.toNat = 1 → 1 ≤ codes ∧ codes ≤ 286) ∧
    (typeCode.toNat = 2 → 1 ≤ codes ∧ codes ≤ 32) ∧
    (typeCode.toNat = 0 → 4 ≤ root0) ∧
    (typeCode.toNat = 1 → 8 ≤ root0) ∧
    (typeCode.toNat = 2 → 5 ≤ root0) ∧
    lensPtr = .ptr lb loff ∧ Readable m lensPtr (2 * codes) ∧
    (∃ blk_l, m.blocks lb = some blk_l ∧ Mem.isAligned blk_l loff 2 = true) ∧
    (∀ i < codes, ∃ v : BitVec 16,
      Sem.readVal prog.tags m lb (Int64.ofInt (loff.toInt + 2 * i)) (.int .u16) =
        some (.int .u16 v) ∧ v.toNat ≤ 15) ∧
    tablePtr = .ptr tpb tpo ∧ TypedCell prog.tags m tablePtr huffCodeCTy.ptr ∧
    Sem.readVal prog.tags m tpb tpo huffCodeCTy.ptr = some (.ptr tb toff) ∧
    m.blocks tb = some tblk ∧ tblk.perm = .rw ∧
    inflateTableMinCap typeCode.toNat ≤ cap ∧
    Mem.inBounds tblk toff (4 * cap) = true ∧ Mem.isAligned tblk toff 2 = true ∧
    bitsPtr = .ptr bpb bpo ∧ TypedCell prog.tags m bitsPtr (.int .u32) ∧
    Sem.readVal prog.tags m bpb bpo (.int .u32) = some (.int .u32 (BitVec.ofNat 32 root0)) ∧
    1 ≤ root0 ∧ root0 ≤ 15 ∧
    workPtr = .ptr wb woff ∧ Writable m workPtr (2 * 288) ∧
    m.blocks wb = some wblk ∧ Mem.isAligned wblk woff 2 = true ∧
    DisjointByteRanges tpb tpo 8 bpb bpo 4 ∧
    DisjointByteRanges tpb tpo 8 tb toff (4 * cap) ∧
    DisjointByteRanges tpb tpo 8 wb woff (2 * 288) ∧
    DisjointByteRanges bpb bpo 4 tb toff (4 * cap) ∧
    DisjointByteRanges bpb bpo 4 wb woff (2 * 288) ∧
    DisjointByteRanges tb toff (4 * cap) wb woff (2 * 288) ∧
    DisjointByteRanges lb loff (2 * codes) tpb tpo 8 ∧
    DisjointByteRanges lb loff (2 * codes) bpb bpo 4 ∧
    DisjointByteRanges lb loff (2 * codes) tb toff (4 * cap) ∧
    DisjointByteRanges lb loff (2 * codes) wb woff (2 * 288)

/-- Postcondition for `inflate_table`. -/
def InflateTablePost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  (∃ r : BitVec 32, ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1 ∨ r.toInt = 1) ∧
    (∃ (typeCode codesVal : BitVec 32)
      (lensPtr tablePtr bitsPtr workPtr : Val)
      (lb tpb bpb tb wb : BlockId) (loff tpo bpo toff woff : Int64) (cap root0 : Nat),
      args = [.int .u32 typeCode, lensPtr, .int .u32 codesVal, tablePtr, bitsPtr, workPtr] ∧
      lensPtr = .ptr lb loff ∧
      tablePtr = .ptr tpb tpo ∧ bitsPtr = .ptr bpb bpo ∧
      Sem.readVal prog.tags m tpb tpo huffCodeCTy.ptr = some (.ptr tb toff) ∧
      Sem.readVal prog.tags m bpb bpo (.int .u32) = some (.int .u32 (BitVec.ofNat 32 root0)) ∧
      workPtr = .ptr wb woff ∧
      FramePreserved m m' (fun b => b = tpb ∨ b = bpb ∨ b = tb ∨ b = wb) ∧
      (∀ b ∈ [tpb, bpb, tb, wb], ∀ (off : Nat) (v : UInt8),
        ((b = tpb → (off : Int) < tpo.toInt ∨ tpo.toInt + 8 ≤ (off : Int)) ∧
         (b = bpb → (off : Int) < bpo.toInt ∨ bpo.toInt + 4 ≤ (off : Int)) ∧
         (b = tb → (off : Int) < toff.toInt ∨ toff.toInt + 4 * cap ≤ (off : Int)) ∧
         (b = wb → (off : Int) < woff.toInt ∨ woff.toInt + 2 * 288 ≤ (off : Int))) →
        (∃ blk, m.blocks b = some blk ∧ blk.bytes off = .byte v) →
        ∃ blk', m'.blocks b = some blk' ∧ blk'.bytes off = .byte v) ∧
      (r.toInt ≠ 0 →
        Sem.readVal prog.tags m' tpb tpo huffCodeCTy.ptr =
          Sem.readVal prog.tags m tpb tpo huffCodeCTy.ptr ∧
        Sem.readVal prog.tags m' bpb bpo (.int .u32) =
          Sem.readVal prog.tags m bpb bpo (.int .u32)) ∧
      (r.toInt = 0 →
        ∃ (newOff : Int64) (root' used : Nat),
          Sem.readVal prog.tags m' tpb tpo huffCodeCTy.ptr = some (.ptr tb newOff) ∧
          Sem.readVal prog.tags m' bpb bpo (.int .u32) = some (.int .u32 (BitVec.ofNat 32 root')) ∧
          newOff.toInt = toff.toInt + 4 * used ∧
          1 ≤ root' ∧ root' ≤ root0 ∧ root' ≤ 15 ∧ 2 ^ root' ≤ used ∧ used ≤ cap ∧
          (typeCode.toNat = 0 →
            (∀ i < codesVal.toNat, ∃ v : BitVec 16,
              Sem.readVal prog.tags m lb (Int64.ofInt (loff.toInt + 2 * i)) (.int .u16) =
                some (.int .u16 v) ∧ v.toNat ≤ 7) →
            root0 ≤ 7 → used ≤ 128) ∧
          (typeCode.toNat = 1 → used ≤ 852) ∧
          (typeCode.toNat = 2 → used ≤ 592) ∧
          CodeTableValid prog.tags m' (.ptr tb toff) root' used (decide (typeCode.toNat = 2)))))

/-- Precondition for `inflate_fast(strm, start)` supporting both heap-window `InflateStateInv`
and caller-window `InflateBackInv`. -/
def InflateFastPre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  ∃ (strmPtr : Val) (start : BitVec 32)
    (nextIn nextOut begPtr stPtr : Val)
    (availIn availOut bits : Nat) (stBid : BlockId),
    args = [strmPtr, .int .u32 start] ∧
    TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
    readField? prog.tags m strmPtr "z_stream_s" "state" = some stPtr ∧
    stPtr = .ptr stBid 0 ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
    6 ≤ availIn ∧ Readable m nextIn availIn ∧
    258 ≤ availOut ∧ Writable m nextOut availOut ∧
    availOut ≤ start.toNat ∧
    (∃ ob ooff, nextOut = .ptr ob ooff ∧
      begPtr = .ptr ob (Int64.ofInt (ooff.toInt - (start.toNat - availOut))) ∧
      Readable m begPtr (start.toNat - availOut) ∧
      Writable m begPtr start.toNat ∧
      ob ≠ stBid ∧ (∀ sb, PtrBlock strmPtr = some sb → ob ≠ sb)) ∧
    DisjointFrom nextIn (fun b => b = stBid ∨ PtrBlock strmPtr = some b) ∧
    readNatField? prog.tags m stPtr "inflate_state" "mode" = some 16200 ∧
    readNatField? prog.tags m stPtr "inflate_state" "bits" = some bits ∧
    bits ≤ 31 ∧
    ((∃ iw : InflateWitness,
        InflateStateInv prog.tags gEnv m strmPtr iw ∧
        iw.stBid = stBid ∧
        bits < 8 ∧
        DisjointFrom nextIn (fun b => b ∈ iw.ownedList) ∧
        DisjointFrom nextOut (fun b => b ∈ iw.ownedList)) ∨
     (∃ (ibw : InflateBackWitness) (lc dc : Val) (lb db lcnt dcnt : Nat),
        InflateBackInv prog.tags m strmPtr ibw ∧
        ibw.stBid = stBid ∧
        PtrBlock nextOut = some ibw.winBid ∧
        nextOut = .ptr ibw.winBid
          (Int64.ofInt (ibw.winOff.toInt + (2 ^ ibw.wbits - availOut))) ∧
        start.toNat = 2 ^ ibw.wbits ∧
        DisjointFrom nextIn (fun b => b = ibw.winBid) ∧
        readField? prog.tags m stPtr "inflate_state" "lencode" = some lc ∧
        readField? prog.tags m stPtr "inflate_state" "distcode" = some dc ∧
        readNatField? prog.tags m stPtr "inflate_state" "lenbits" = some lb ∧
        readNatField? prog.tags m stPtr "inflate_state" "distbits" = some db ∧
        CodeTableValid prog.tags m lc lb lcnt false ∧
        CodeTableValid prog.tags m dc db dcnt true))

/-- Postcondition for `inflate_fast`. -/
def InflateFastPost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  ∃ (strmPtr : Val) (start : BitVec 32)
    (nextIn nextIn' nextOut nextOut' stPtr : Val)
    (availIn availIn' availOut availOut' bits bits' mode' : Nat)
    (stBid sb ob : BlockId) (inOff outOff soff : Int64),
    args = [strmPtr, .int .u32 start] ∧
    strmPtr = .ptr sb soff ∧
    readField? prog.tags m strmPtr "z_stream_s" "state" = some stPtr ∧
    stPtr = .ptr stBid 0 ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
    readNatField? prog.tags m stPtr "inflate_state" "bits" = some bits ∧
    PtrBlock nextIn = PtrBlock nextIn' ∧
    (∃ ib, nextIn = .ptr ib inOff ∧
      nextIn' = .ptr ib (Int64.ofInt (inOff.toInt + (availIn - availIn')))) ∧
    readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
    readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
    availIn' ≤ availIn ∧ (availIn' = 0 ∨ Readable m' nextIn' availIn') ∧
    nextOut = .ptr ob outOff ∧
    nextOut' = .ptr ob (Int64.ofInt (outOff.toInt + (availOut - availOut'))) ∧
    readField? prog.tags m' strmPtr "z_stream_s" "next_out" = some nextOut' ∧
    readNatField? prog.tags m' strmPtr "z_stream_s" "avail_out" = some availOut' ∧
    availOut' ≤ availOut ∧ Writable m' nextOut' availOut' ∧
    Writable m' (.ptr ob (Int64.ofInt (outOff.toInt - (start.toNat - availOut)))) start.toNat ∧
    Readable m' (.ptr ob (Int64.ofInt (outOff.toInt - (start.toNat - availOut))))
      (start.toNat - availOut') ∧
    readNatField? prog.tags m' stPtr "inflate_state" "bits" = some bits' ∧
    bits' < 8 ∧
    readNatField? prog.tags m' stPtr "inflate_state" "mode" = some mode' ∧
    (mode' = 16200 ∨ mode' = 16191 ∨ mode' = 16209) ∧
    (mode' = 16200 ∨ mode' = 16191 → 8 * availIn' + bits' < 8 * availIn + bits) ∧
    (mode' = 16209 →
      ∃ msg, readField? prog.tags m' strmPtr "z_stream_s" "msg" = some msg ∧
        (msg = .null ∨ CString m' msg)) ∧
    readField? prog.tags m' stPtr "inflate_state" "lencode" =
      readField? prog.tags m stPtr "inflate_state" "lencode" ∧
    readField? prog.tags m' stPtr "inflate_state" "distcode" =
      readField? prog.tags m stPtr "inflate_state" "distcode" ∧
    readField? prog.tags m' stPtr "inflate_state" "lenbits" =
      readField? prog.tags m stPtr "inflate_state" "lenbits" ∧
    readField? prog.tags m' stPtr "inflate_state" "distbits" =
      readField? prog.tags m stPtr "inflate_state" "distbits" ∧
    readField? prog.tags m' stPtr "inflate_state" "last" =
      readField? prog.tags m stPtr "inflate_state" "last" ∧
    (∀ j < 1732,
      Sem.readVal prog.tags m' stBid (Int64.ofNat (1384 + 4 * j)) (.int .u8) =
        Sem.readVal prog.tags m stBid (Int64.ofNat (1384 + 4 * j)) (.int .u8) ∧
      Sem.readVal prog.tags m' stBid (Int64.ofNat (1384 + 4 * j + 1)) (.int .u8) =
        Sem.readVal prog.tags m stBid (Int64.ofNat (1384 + 4 * j + 1)) (.int .u8) ∧
      Sem.readVal prog.tags m' stBid (Int64.ofNat (1384 + 4 * j + 2)) (.int .u16) =
        Sem.readVal prog.tags m stBid (Int64.ofNat (1384 + 4 * j + 2)) (.int .u16)) ∧
    PreservesOutsideRange m m' sb soff 112 ∧
    PreservesOutsideRange m m' ob outOff (availOut - availOut') ∧
    FramePreserved m m' (fun b => b = stBid ∨ b = ob ∨ b = sb) ∧
    (∀ iw : InflateWitness, InflateStateInv prog.tags gEnv m strmPtr iw →
      InflateStateInv prog.tags gEnv m' strmPtr iw) ∧
    (∀ ibw : InflateBackWitness, InflateBackInv prog.tags m strmPtr ibw →
      InflateBackInv prog.tags m' strmPtr ibw)

/-- Strict rank of `deflate_state.status` / `wrap` along forward compression transitions. -/
def deflatePhaseRank (status wrap : Int) : Nat :=
  match status with
  | 42 => 9
  | 57 => 8
  | 69 => 7
  | 73 => 6
  | 91 => 5
  | 103 => 4
  | 113 => 3
  | 666 => if wrap > 0 then 2 else 1
  | _ => 0

/-- Five-component termination measure for `deflate` when header is absent (`gzhead = NULL`). -/
def deflateEmitTuple (tags : TypeEnv) (m : Mem) (dw : DeflateWitness)
    (availIn : Nat) (flush : Int) : Nat × Nat × Nat × Nat × Nat :=
  let st := Val.ptr dw.stBid 0
  let look := (readNatField? tags m st "internal_state" "lookahead").getD 0
  let mav := (readNatField? tags m st "internal_state" "match_available").getD 0
  let lvl := (readIntField? tags m st "internal_state" "level").getD 0
  let strs := (readNatField? tags m st "internal_state" "strstart").getD 0
  let bks := (readIntField? tags m st "internal_state" "block_start").getD 0
  let storedPend := if lvl == 0 && 0 ≤ bks then strs - bks.toNat else 0
  let symNext := (readNatField? tags m st "internal_state" "sym_next").getD 0
  let status := (readIntField? tags m st "internal_state" "status").getD 0
  let wrap := (readIntField? tags m st "internal_state" "wrap").getD 0
  let pend := (readNatField? tags m st "internal_state" "pending").getD 0
  let lastFl := (readIntField? tags m st "internal_state" "last_flush").getD (-2)
  (availIn + look + mav + storedPend, symNext, deflatePhaseRank status wrap, pend,
    if lastFl == flush then 0 else 1)

/-- Strict lexicographic ordering on 5-tuples of `Nat`. -/
def Tuple5Lt (a b : Nat × Nat × Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ (a.2.2.1 < b.2.2.1 ∨
    (a.2.2.1 = b.2.2.1 ∧ (a.2.2.2.1 < b.2.2.2.1 ∨
      (a.2.2.2.1 = b.2.2.2.1 ∧ a.2.2.2.2 < b.2.2.2.2)))))))

/-- Non-strict lexicographic ordering on 5-tuples of `Nat`. -/
def Tuple5Le (a b : Nat × Nat × Nat × Nat × Nat) : Prop :=
  a = b ∨ Tuple5Lt a b

/-! ### Spec Records for Wave 2–4 Modules -/

/-- Decoupled verification interface for `Zlib.Inftrees` (`inflate_table`, `inflate_fixed`). -/
structure InftreesSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userExt : ExtHandler) : Prop where
  inflate_table_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inftrees.inftreesTU_fn_inflate_table
      (InflateTablePre prog gEnv m0 os0)
      (InflateTablePost prog gEnv m0 os0)
  inflate_fixed_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inftrees.inftreesTU_fn_inflate_fixed
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ statePtr stBid stOff, args = [statePtr] ∧
          statePtr = .ptr stBid stOff ∧
          TypedCell prog.tags m statePtr (.structTy "inflate_state"))
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ statePtr stBid stOff,
          args = [statePtr] ∧ statePtr = .ptr stBid stOff ∧
          FramePreserved m m' (fun b => b = stBid) ∧
          (∀ fld, fld ∉ (["lencode", "lenbits", "distcode", "distbits"] : List String) →
            readField? prog.tags m' statePtr "inflate_state" fld =
              readField? prog.tags m statePtr "inflate_state" fld) ∧
          (∃ lfb lfty lblk, gEnv.lookup "lenfix" = some (lfb, lfty) ∧ m'.blocks lfb = some lblk ∧
            readField? prog.tags m' statePtr "inflate_state" "lencode" = some (.ptr lfb 0)) ∧
          (∃ dfb dfty dblk, gEnv.lookup "distfix" = some (dfb, dfty) ∧ m'.blocks dfb = some dblk ∧
            readField? prog.tags m' statePtr "inflate_state" "distcode" = some (.ptr dfb 0)) ∧
          readNatField? prog.tags m' statePtr "inflate_state" "lenbits" = some 9 ∧
          readNatField? prog.tags m' statePtr "inflate_state" "distbits" = some 5)

/-- Decoupled verification interface for `Zlib.Inffast` (`inflate_fast`). -/
structure InffastSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userExt : ExtHandler) : Prop where
  inflate_fast_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inffast.inffastTU_fn_inflate_fast
      (InflateFastPre prog gEnv m0 os0)
      (InflateFastPost prog gEnv m0 os0)

/-- Decoupled verification interface for `Zlib.Inflate` helpers and non-`inflate` public APIs. -/
structure InflateCoreSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  inflateReset_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateReset_contract
  inflateReset2_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateReset2_contract
  inflateInit2__safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateInit2__contract
  inflateInit__safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateInit__contract
  inflatePrime_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflatePrime_contract
  inflateEnd_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateEnd_contract
  inflateGetDictionary_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateGetDictionary_contract
  inflateSetDictionary_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateSetDictionary_contract
  inflateGetHeader_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateGetHeader_contract
  inflateSync_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateSync_contract
  inflateCopy_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateCopy_contract
  inflateMark_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflateMark_contract
  inflateStateCheck_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateStateCheck
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr, args = [strmPtr] ∧
          (strmPtr = .null ∨ ∃ iw, InflateStateInv prog.tags gEnv m strmPtr iw))
      (fun m os args ret m' os' =>
        MemBlocksUnchanged m m' ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr, args = [strmPtr] ∧
          ((strmPtr = .null ∧ ret = .int .i32 1) ∨
           ((∃ iw, InflateStateInv prog.tags gEnv m strmPtr iw) ∧ ret = .int .i32 0)))
  inflateResetKeep_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateResetKeep
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff iw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          sb ∉ iw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 iw.ownedList)
      (fun m os args ret m' os' =>
        ret = .int .i32 0 ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff iw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          InflateStateInv prog.tags gEnv m' strmPtr iw ∧
          (∀ wrap, readIntField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "wrap" = some wrap →
            InflateAccumulatorsInit prog.tags m' strmPtr wrap) ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          readNatField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "mode" = some 16180 ∧
          readField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "head" = some .null ∧
          readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b = iw.stBid) ∧
          NoHeapLeak m m' (fun _ => False))
  inflateReset_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateReset
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff iw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          sb ∉ iw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 iw.ownedList)
      (fun m os args ret m' os' =>
        ret = .int .i32 0 ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff iw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          InflateStateInv prog.tags gEnv m' strmPtr iw ∧
          (∀ wrap, readIntField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "wrap" = some wrap →
            InflateAccumulatorsInit prog.tags m' strmPtr wrap) ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          readNatField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "mode" = some 16180 ∧
          readNatField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "wsize" = some 0 ∧
          readNatField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "whave" = some 0 ∧
          readNatField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "wnext" = some 0 ∧
          readField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "head" = some .null ∧
          readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b = iw.stBid) ∧
          NoHeapLeak m m' (fun _ => False))
  inflateReset2_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateReset2
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff wb iw,
          args = [strmPtr, .int .i32 wb] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          sb ∉ iw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 iw.ownedList)
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff wb iw r,
          args = [strmPtr, .int .i32 wb] ∧ strmPtr = .ptr sb soff ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          ret = .int .i32 r ∧
          ((r.toInt = 0 ∧ ∃ iw',
              iw'.stBid = iw.stBid ∧
              (iw'.win? = iw.win? ∨ (iw'.win? = none ∧ ∀ w, iw.win? = some w → m'.blocks w = none)) ∧
              InflateStateInv prog.tags gEnv m' strmPtr iw' ∧
              (∀ wrap, readIntField? prog.tags m' (.ptr iw'.stBid 0) "inflate_state" "wrap" = some wrap →
                InflateAccumulatorsInit prog.tags m' strmPtr wrap) ∧
              (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
                readField? prog.tags m' strmPtr "z_stream_s" fld =
                  readField? prog.tags m strmPtr "z_stream_s" fld) ∧
              readField? prog.tags m' (.ptr iw'.stBid 0) "inflate_state" "head" = some .null ∧
              readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b => b = sb ∨ b ∈ iw.ownedList) ∧
              NoHeapLeak m m' (fun b => b ∈ iw'.ownedList)) ∨
           (r.toInt = -2 ∧ MemBlocksUnchanged m m')))
  inflateInit2__spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateInit2_
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr wb streamSz verPtr,
          args = [strmPtr, .int .i32 wb, verPtr, .int .i32 streamSz] ∧
          OptCString m verPtr ∧
          (strmPtr = .null ∨
            ∃ sb soff, strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              (∃ za, readField? prog.tags m strmPtr "z_stream_s" "zalloc" = some za ∧
                (za = .null ∨ za = .fnPtr "zcalloc")) ∧
              (∃ zf, readField? prog.tags m strmPtr "z_stream_s" "zfree" = some zf ∧
                (zf = .null ∨ zf = .fnPtr "zcfree"))))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr wb streamSz verPtr r,
          args = [strmPtr, .int .i32 wb, verPtr, .int .i32 streamSz] ∧
          ret = .int .i32 r ∧
          ((r.toInt = 0 ∧ ∃ sb soff iw,
              strmPtr = .ptr sb soff ∧ iw.win? = none ∧
              (m.blocks iw.stBid).isNone = true ∧ iw.stBid ≠ sb ∧
              (m0.blocks iw.stBid).isNone = true ∧ iw.stBid ≠ os0.errnoBlk ∧
              InflateStateInv prog.tags gEnv m' strmPtr iw ∧
              (∀ wrap, readIntField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "wrap" = some wrap →
                InflateAccumulatorsInit prog.tags m' strmPtr wrap) ∧
              (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
                readField? prog.tags m' strmPtr "z_stream_s" fld =
                  readField? prog.tags m strmPtr "z_stream_s" fld) ∧
              readField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "head" = some .null ∧
              readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b => b = sb ∨ b = iw.stBid) ∧
              NoHeapLeak m m' (fun b => b = iw.stBid)) ∨
           (r.toInt ≠ 0 ∧
              (∀ sb soff, strmPtr = .ptr sb soff → PreservesOutsideRange m m' sb soff 112) ∧
              FramePreserved m m' (fun b => PtrBlock strmPtr = some b) ∧
              NoHeapLeak m m' (fun _ => False))))
  inflateInit__spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateInit_
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr verPtr streamSz,
          args = [strmPtr, verPtr, .int .i32 streamSz] ∧
          OptCString m verPtr ∧
          (strmPtr = .null ∨
            ∃ sb soff, strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              (∃ za, readField? prog.tags m strmPtr "z_stream_s" "zalloc" = some za ∧
                (za = .null ∨ za = .fnPtr "zcalloc")) ∧
              (∃ zf, readField? prog.tags m strmPtr "z_stream_s" "zfree" = some zf ∧
                (zf = .null ∨ zf = .fnPtr "zcfree"))))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr verPtr streamSz r,
          args = [strmPtr, verPtr, .int .i32 streamSz] ∧
          ret = .int .i32 r ∧
          ((r.toInt = 0 ∧ ∃ sb soff iw,
              strmPtr = .ptr sb soff ∧ iw.win? = none ∧
              (m.blocks iw.stBid).isNone = true ∧ iw.stBid ≠ sb ∧
              (m0.blocks iw.stBid).isNone = true ∧ iw.stBid ≠ os0.errnoBlk ∧
              InflateStateInv prog.tags gEnv m' strmPtr iw ∧
              (∀ wrap, readIntField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "wrap" = some wrap →
                InflateAccumulatorsInit prog.tags m' strmPtr wrap) ∧
              (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
                readField? prog.tags m' strmPtr "z_stream_s" fld =
                  readField? prog.tags m strmPtr "z_stream_s" fld) ∧
              readField? prog.tags m' (.ptr iw.stBid 0) "inflate_state" "head" = some .null ∧
              readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b => b = sb ∨ b = iw.stBid) ∧
              NoHeapLeak m m' (fun b => b = iw.stBid)) ∨
           (r.toInt ≠ 0 ∧
              (∀ sb soff, strmPtr = .ptr sb soff → PreservesOutsideRange m m' sb soff 112) ∧
              FramePreserved m m' (fun b => PtrBlock strmPtr = some b) ∧
              NoHeapLeak m m' (fun _ => False))))
  inflateEnd_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflateEnd
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff iw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          sb ∉ iw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 iw.ownedList)
      (fun m os args ret m' os' =>
        ret = .int .i32 0 ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff iw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          (∀ b ∈ iw.ownedList, m'.blocks b = none) ∧
          readField? prog.tags m' strmPtr "z_stream_s" "state" = some .null ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b ∈ iw.ownedList) ∧
          NoHeapLeak m m' (fun _ => False))
  updatewindow_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_updatewindow
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff endPtr copy iw,
          args = [strmPtr, endPtr, .int .u32 copy] ∧ strmPtr = .ptr sb soff ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          sb ∉ iw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 iw.ownedList ∧
          ∃ eb eoff, endPtr = .ptr eb eoff ∧
            copy.toNat ≤ eoff.toInt ∧
            Readable m (.ptr eb (Int64.ofInt (eoff.toInt - copy.toNat))) copy.toNat ∧
            eb ∉ iw.ownedList ∧ (copy.toNat = 0 ∨ eb ≠ sb))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff endPtr copy iw r,
          args = [strmPtr, endPtr, .int .u32 copy] ∧ strmPtr = .ptr sb soff ∧
          InflateStateInv prog.tags gEnv m strmPtr iw ∧
          ret = .int .i32 r ∧
          ((r.toInt = 0 ∧ ∃ iw',
              iw'.stBid = iw.stBid ∧
              (iw'.win? = iw.win? ∨
                (iw.win? = none ∧ ∃ wb, iw'.win? = some wb ∧
                  (m.blocks wb).isNone = true ∧ wb ≠ sb ∧
                  (m0.blocks wb).isNone = true ∧ wb ≠ os0.errnoBlk ∧ wb ∉ iw.ownedList)) ∧
              InflateStateInv prog.tags gEnv m' strmPtr iw' ∧
              FramePreserved m m' (fun b => b ∈ iw'.ownedList) ∧
              NoHeapLeak m m' (fun b => b ∈ iw'.ownedList)) ∨
           (r.toInt = 1 ∧
              FramePreserved m m' (fun b => b ∈ iw.ownedList) ∧
              NoHeapLeak m m' (fun b => b ∈ iw.ownedList))))
  syncsearch_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_syncsearch
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ havePtr bufPtr len have0,
          args = [havePtr, bufPtr, .int .u32 len] ∧
          TypedCell prog.tags m havePtr (.int .u32) ∧
          (∃ hb hoff, havePtr = .ptr hb hoff ∧
            Sem.readVal prog.tags m hb hoff (.int .u32) = some (.int .u32 have0)) ∧
          (len.toNat = 0 ∨ (Readable m bufPtr len.toNat ∧ PtrBlock bufPtr ≠ PtrBlock havePtr)))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ havePtr bufPtr len hb hoff have' r,
          args = [havePtr, bufPtr, .int .u32 len] ∧
          havePtr = .ptr hb hoff ∧
          ret = .int .u32 r ∧ r.toNat ≤ len.toNat ∧
          Sem.readVal prog.tags m' hb hoff (.int .u32) = some (.int .u32 have') ∧
          have'.toNat ≤ 4 ∧
          FramePreserved m m' (fun b => b = hb) ∧
          NoHeapLeak m m' (fun _ => False))

/-- Decoupled verification interface for `Zlib.Inflate.inflate` (public contract +
internal progress-tracked spec for `uncompress2_z` and `gzread`). -/
structure InflateMainSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  inflate_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Inflate.inflate_contract
  inflate_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Inflate.inflateTU_fn_inflate
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr flush, args = [strmPtr, .int .i32 flush] ∧
          (strmPtr = .null ∨
            ∃ sb soff iw nextIn nextOut availIn availOut,
              strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              InflateStateInv prog.tags gEnv m strmPtr iw ∧
              (∃ ti, readNatField? prog.tags m strmPtr "z_stream_s" "total_in" = some ti) ∧
              (∃ to_, readNatField? prog.tags m strmPtr "z_stream_s" "total_out" = some to_) ∧
              sb ∉ iw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 iw.ownedList ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
              (availIn = 0 ∨ (Readable m nextIn availIn ∧
                DisjointFrom nextIn (fun b => b ∈ iw.ownedList ∨ b = sb))) ∧
              (availOut = 0 ∨ (Writable m nextOut availOut ∧
                DisjointFrom nextOut (fun b => b ∈ iw.ownedList ∨ b = sb))) ∧
              (availIn = 0 ∨ availOut = 0 ∨ PtrBlock nextIn ≠ PtrBlock nextOut) ∧
              (availOut = 0 → ∀ ws,
                readNatField? prog.tags m (.ptr iw.stBid 0) "inflate_state" "wsize" = some ws →
                ws = 0 ∨ Readable m nextOut 0) ∧
              (∀ hd, readField? prog.tags m (.ptr iw.stBid 0) "inflate_state" "head" = some hd →
                hd = .null)))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr flush r,
          args = [strmPtr, .int .i32 flush] ∧ ret = .int .i32 r ∧
          ((strmPtr = .null ∧ r.toInt = -2 ∧ MemBlocksUnchanged m m') ∨
           (∃ sb soff iw iw' nextIn nextIn' nextOut nextOut' availIn availIn' availOut availOut',
              strmPtr = .ptr sb soff ∧
              InflateStateInv prog.tags gEnv m strmPtr iw ∧
              InflateStateInv prog.tags gEnv m' strmPtr iw' ∧
              (∀ wrap, readIntField? prog.tags m' (.ptr iw'.stBid 0) "inflate_state" "wrap" = some wrap →
                InflateAccumulatorsInit prog.tags m' strmPtr wrap) ∧
              (StreamAccumulatorsInit prog.tags m strmPtr →
                StreamAccumulatorsInit prog.tags m' strmPtr) ∧
              readField? prog.tags m' (.ptr iw'.stBid 0) "inflate_state" "head" = some .null ∧
              iw'.stBid = iw.stBid ∧
              (iw'.win? = iw.win? ∨
                (iw.win? = none ∧ ∃ wb, iw'.win? = some wb ∧
                  (m.blocks wb).isNone = true ∧ wb ≠ sb ∧
                  (m0.blocks wb).isNone = true ∧ wb ≠ os0.errnoBlk ∧ wb ∉ iw.ownedList)) ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
              readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
              readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
              readField? prog.tags m' strmPtr "z_stream_s" "next_out" = some nextOut' ∧
              readNatField? prog.tags m' strmPtr "z_stream_s" "avail_out" = some availOut' ∧
              availIn' ≤ availIn ∧ availOut' ≤ availOut ∧
              (availIn' = availIn → nextIn' = nextIn) ∧
              (availIn' < availIn → ∃ ib ioff, nextIn = .ptr ib ioff ∧
                nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + (availIn - availIn'))) ∧
                (availIn' = 0 ∨ Readable m' nextIn' availIn')) ∧
              (availOut' = availOut → nextOut' = nextOut) ∧
              (availOut' < availOut → ∃ ob ooff, nextOut = .ptr ob ooff ∧
                nextOut' = .ptr ob (Int64.ofInt (ooff.toInt + (availOut - availOut'))) ∧
                Readable m' nextOut (availOut - availOut') ∧
                PreservesOutsideRange m m' ob ooff availOut ∧
                (availOut' = 0 ∨ Writable m' nextOut' availOut')) ∧
              (r.toInt = 0 → availIn' < availIn ∨ availOut' < availOut) ∧
              (∀ msg0, readField? prog.tags m strmPtr "z_stream_s" "msg" = some msg0 →
                (msg0 = .null ∨ ∃ mb0 mblk0, msg0 = .ptr mb0 0 ∧ m.blocks mb0 = some mblk0 ∧
                  mblk0.kind = .global ∧ mblk0.perm = .ro ∧ CString m msg0) →
                ∃ msg', readField? prog.tags m' strmPtr "z_stream_s" "msg" = some msg' ∧
                  (msg' = .null ∨ ∃ mb' mblk', msg' = .ptr mb' 0 ∧ m'.blocks mb' = some mblk' ∧
                    mblk'.kind = .global ∧ mblk'.perm = .ro ∧ CString m' msg')) ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b =>
                b = sb ∨ b ∈ iw'.ownedList ∨ (availOut' < availOut ∧ PtrBlock nextOut = some b)) ∧
              NoHeapLeak m m' (fun b => b ∈ iw'.ownedList))))

/-- Decoupled verification interface for `Zlib.Infback` (`inflateBackInit_`, `inflateBack`,
`inflateBackEnd`). -/
structure InfbackSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  inflateBackInit__safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Infback.inflateBackInit__contract
  inflateBack_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Infback.inflateBack_contract
  inflateBackEnd_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Infback.inflateBackEnd_contract

/-- Decoupled verification interface for `Zlib.Trees` (`_tr_init`, `_tr_stored_block`,
`_tr_flush_bits`, `_tr_align`, `_tr_flush_block`, `_tr_tally`). -/
structure TreesSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userExt : ExtHandler) : Prop where
  _tr_init_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Trees.treesTU_fn__tr_init
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr stBid, args = [sPtr] ∧ sPtr = .ptr stBid 0 ∧
          HeapRwBlock m stBid 5968 8)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr stBid, args = [sPtr] ∧ sPtr = .ptr stBid 0 ∧
          FramePreserved m m' (fun b => b = stBid) ∧
          NoHeapLeak m m' (fun _ => False) ∧
          (∀ fld, fld ∈ (["w_size", "w_bits", "w_mask", "window", "window_size",
              "prev", "head", "ins_h", "hash_size", "hash_bits", "hash_mask", "hash_shift",
              "pending_buf", "pending_buf_size", "pending_out", "pending", "strm",
              "status", "wrap", "gzhead", "gzindex", "method", "last_flush",
              "sym_buf", "lit_bufsize", "sym_end"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          readNatField? prog.tags m' sPtr "internal_state" "bi_buf" = some 0 ∧
          readNatField? prog.tags m' sPtr "internal_state" "bi_valid" = some 0 ∧
          readNatField? prog.tags m' sPtr "internal_state" "sym_next" = some 0 ∧
          readNatField? prog.tags m' sPtr "internal_state" "opt_len" = some 0 ∧
          readNatField? prog.tags m' sPtr "internal_state" "static_len" = some 0 ∧
          readNatField? prog.tags m' sPtr "internal_state" "matches" = some 0)
  _tr_stored_block_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Trees.treesTU_fn__tr_stored_block
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr bufPtr storedLen last strmPtr sb soff dw pend bv pbsz,
          args = [sPtr, bufPtr, .int .u64 storedLen, .int .i32 last] ∧
          sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          sb ∉ dw.ownedList ∧
          readField? prog.tags m sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
          readNatField? prog.tags m sPtr "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m sPtr "internal_state" "bi_valid" = some bv ∧
          readNatField? prog.tags m sPtr "internal_state" "pending_buf_size" = some pbsz ∧
          pend + (bv + 7) / 8 + 4 + storedLen.toNat ≤ pbsz ∧
          (storedLen.toNat = 0 ∨
            (Readable m bufPtr storedLen.toNat ∧
              DisjointFrom bufPtr (fun b => b = dw.stBid ∨ b = dw.pbufBid ∨ b = sb))))
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr bufPtr storedLen last strmPtr dw pend',
          args = [sPtr, bufPtr, .int .u64 storedLen, .int .i32 last] ∧
          sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          readNatField? prog.tags m' sPtr "internal_state" "pending" = some pend' ∧
          4 + storedLen.toNat ≤ pend' ∧
          (∀ fld, fld ∉ (["bi_buf", "bi_valid", "pending"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.pbufBid) ∧
          NoHeapLeak m m' (fun _ => False))
  _tr_flush_bits_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Trees.treesTU_fn__tr_flush_bits
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr strmPtr sb soff dw pend pbsz,
          args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧ sb ∉ dw.ownedList ∧
          readField? prog.tags m sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
          readNatField? prog.tags m sPtr "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m sPtr "internal_state" "pending_buf_size" = some pbsz ∧
          pend + 2 ≤ pbsz)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr strmPtr dw, args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (∀ fld, fld ∉ (["bi_buf", "bi_valid", "pending"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.pbufBid) ∧
          NoHeapLeak m m' (fun _ => False))
  _tr_align_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Trees.treesTU_fn__tr_align
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr strmPtr sb soff dw pend pbsz,
          args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧ sb ∉ dw.ownedList ∧
          readField? prog.tags m sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
          readNatField? prog.tags m sPtr "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m sPtr "internal_state" "pending_buf_size" = some pbsz ∧
          pend + 10 ≤ pbsz)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr strmPtr dw, args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (∀ fld, fld ∉ (["bi_buf", "bi_valid", "pending"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.pbufBid) ∧
          NoHeapLeak m m' (fun _ => False))
  _tr_flush_block_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Trees.treesTU_fn__tr_flush_block
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr bufPtr storedLen last strmPtr sb soff dw pend bv pbsz,
          args = [sPtr, bufPtr, .int .u64 storedLen, .int .i32 last] ∧
          sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          ((∃ level, readIntField? prog.tags m sPtr "internal_state" "level" = some level ∧ level ≤ 0) ∨
            ∃ dt, readIntField? prog.tags m strmPtr "z_stream_s" "data_type" = some dt) ∧
          sb ∉ dw.ownedList ∧
          readField? prog.tags m sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
          readNatField? prog.tags m sPtr "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m sPtr "internal_state" "bi_valid" = some bv ∧
          readNatField? prog.tags m sPtr "internal_state" "pending_buf_size" = some pbsz ∧
          pend + (bv + 7) / 8 + 4 + storedLen.toNat ≤ pbsz ∧
          (storedLen.toNat = 0 ∨
            (Readable m bufPtr storedLen.toNat ∧
              DisjointFrom bufPtr (fun b => b = dw.stBid ∨ b = dw.pbufBid ∨ b = sb))))
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr bufPtr storedLen last strmPtr sb soff dw,
          args = [sPtr, bufPtr, .int .u64 storedLen, .int .i32 last] ∧
          sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
          readNatField? prog.tags m' sPtr "internal_state" "sym_next" = some 0 ∧
          (∀ fld, fld ∈ (["level", "strategy", "wrap", "status", "gzhead", "gzindex", "method",
              "last_flush", "w_size", "w_bits", "w_mask", "window", "window_size", "strstart",
              "block_start", "lookahead", "match_available", "match_length", "prev_length",
              "match_start", "prev_match", "insert", "slid", "high_water", "pending_out",
              "pending_buf", "pending_buf_size", "sym_buf", "lit_bufsize", "sym_end",
              "strm", "bi_used"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "total_in", "next_out", "avail_out",
              "total_out", "adler"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b = dw.stBid ∨ b = dw.pbufBid) ∧
          NoHeapLeak m m' (fun _ => False))
  _tr_tally_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Trees.treesTU_fn__tr_tally
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr dist lc strmPtr sb soff dw symNext symEnd,
          args = [sPtr, .int .u32 dist, .int .u32 lc] ∧
          sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧ sb ∉ dw.ownedList ∧
          readNatField? prog.tags m sPtr "internal_state" "sym_next" = some symNext ∧
          readNatField? prog.tags m sPtr "internal_state" "sym_end" = some symEnd ∧
          symNext + 3 ≤ symEnd ∧ lc.toNat < 256 ∧ dist.toNat ≤ 32768)
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr dist lc strmPtr dw symNext r,
          args = [sPtr, .int .u32 dist, .int .u32 lc] ∧
          sPtr = .ptr dw.stBid 0 ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = 1) ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          readNatField? prog.tags m sPtr "internal_state" "sym_next" = some symNext ∧
          readNatField? prog.tags m' sPtr "internal_state" "sym_next" = some (symNext + 3) ∧
          (∀ fld, fld ∉ (["sym_buf", "sym_next", "opt_len", "static_len", "matches",
              "dyn_ltree", "dyn_dtree"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.pbufBid) ∧
          NoHeapLeak m m' (fun _ => False))

/-- Decoupled verification interface for `Zlib.Deflate` core helpers and non-`deflate`
non-`deflateParams` public APIs. -/
structure DeflateCoreSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  deflateInit__safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateInit__contract
  deflateInit2__safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateInit2__contract
  deflateSetDictionary_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateSetDictionary_contract
  deflateGetDictionary_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateGetDictionary_contract
  deflateReset_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateReset_contract
  deflateSetHeader_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateSetHeader_contract
  deflatePending_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflatePending_contract
  deflateUsed_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateUsed_contract
  deflatePrime_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflatePrime_contract
  deflateTune_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateTune_contract
  deflateBound_z_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateBound_z_contract
  deflateBound_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateBound_contract
  deflateEnd_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateEnd_contract
  deflateCopy_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateCopy_contract
  deflateStateCheck_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateStateCheck
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr, args = [strmPtr] ∧
          (strmPtr = .null ∨ ∃ dw, DeflateStateInv prog.tags gEnv m strmPtr dw))
      (fun m os args ret m' os' =>
        MemBlocksUnchanged m m' ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr, args = [strmPtr] ∧
          ((strmPtr = .null ∧ ret = .int .i32 1) ∨
           ((∃ dw, DeflateStateInv prog.tags gEnv m strmPtr dw) ∧ ret = .int .i32 0)))
  deflateResetKeep_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateResetKeep
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff dw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          sb ∉ dw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 dw.ownedList)
      (fun m os args ret m' os' =>
        ret = .int .i32 0 ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff dw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          StreamAccumulatorsInit prog.tags m' strmPtr ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b ∈ dw.ownedList) ∧
          NoHeapLeak m m' (fun _ => False))
  lm_init_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_lm_init
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr strmPtr sb soff dw, args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧
          strmPtr = .ptr sb soff ∧ DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          sb ∉ dw.ownedList)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr strmPtr dw, args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (∀ fld, fld ∈ (["level", "strategy", "wrap", "status", "gzhead", "gzindex",
              "method", "last_flush", "w_size", "w_bits", "w_mask", "window", "window_size",
              "pending_buf", "pending_buf_size", "pending_out", "pending", "sym_buf",
              "lit_bufsize", "sym_next", "sym_end", "bi_buf", "bi_valid", "bi_used",
              "strm"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.headBid) ∧
          NoHeapLeak m m' (fun _ => False))
  deflateReset_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateReset
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff dw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          sb ∉ dw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 dw.ownedList)
      (fun m os args ret m' os' =>
        ret = .int .i32 0 ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff dw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          StreamAccumulatorsInit prog.tags m' strmPtr ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b ∈ dw.ownedList) ∧
          NoHeapLeak m m' (fun _ => False))
  deflateInit2__spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateInit2_
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr level method wb ml strat streamSz verPtr,
          args = [strmPtr, .int .i32 level, .int .i32 method, .int .i32 wb,
            .int .i32 ml, .int .i32 strat, verPtr, .int .i32 streamSz] ∧
          OptCString m verPtr ∧
          (strmPtr = .null ∨
            ∃ sb soff, strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              (∃ za, readField? prog.tags m strmPtr "z_stream_s" "zalloc" = some za ∧
                (za = .null ∨ za = .fnPtr "zcalloc")) ∧
              (∃ zf, readField? prog.tags m strmPtr "z_stream_s" "zfree" = some zf ∧
                (zf = .null ∨ zf = .fnPtr "zcfree"))))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr level method wb ml strat streamSz verPtr r,
          args = [strmPtr, .int .i32 level, .int .i32 method, .int .i32 wb,
            .int .i32 ml, .int .i32 strat, verPtr, .int .i32 streamSz] ∧
          ret = .int .i32 r ∧
          ((r.toInt = 0 ∧ ∃ sb soff dw,
              strmPtr = .ptr sb soff ∧
              sb ∉ dw.ownedList ∧
              (∀ b ∈ dw.ownedList, (m.blocks b).isNone = true) ∧
              HeapBlocksFreshFromLib m0 os0 dw.ownedList ∧
              DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
              StreamAccumulatorsInit prog.tags m' strmPtr ∧
              (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
                readField? prog.tags m' strmPtr "z_stream_s" fld =
                  readField? prog.tags m strmPtr "z_stream_s" fld) ∧
              readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b => b = sb ∨ b ∈ dw.ownedList) ∧
              NoHeapLeak m m' (fun b => b ∈ dw.ownedList)) ∨
           (r.toInt ≠ 0 ∧
              (∀ sb soff, strmPtr = .ptr sb soff → PreservesOutsideRange m m' sb soff 112) ∧
              FramePreserved m m' (fun b => PtrBlock strmPtr = some b) ∧
              NoHeapLeak m m' (fun _ => False))))
  deflateInit__spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateInit_
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr level streamSz verPtr,
          args = [strmPtr, .int .i32 level, verPtr, .int .i32 streamSz] ∧
          OptCString m verPtr ∧
          (strmPtr = .null ∨
            ∃ sb soff, strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              (∃ za, readField? prog.tags m strmPtr "z_stream_s" "zalloc" = some za ∧
                (za = .null ∨ za = .fnPtr "zcalloc")) ∧
              (∃ zf, readField? prog.tags m strmPtr "z_stream_s" "zfree" = some zf ∧
                (zf = .null ∨ zf = .fnPtr "zcfree"))))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr level streamSz verPtr r,
          args = [strmPtr, .int .i32 level, verPtr, .int .i32 streamSz] ∧
          ret = .int .i32 r ∧
          ((r.toInt = 0 ∧ ∃ sb soff dw,
              strmPtr = .ptr sb soff ∧
              sb ∉ dw.ownedList ∧
              (∀ b ∈ dw.ownedList, (m.blocks b).isNone = true) ∧
              HeapBlocksFreshFromLib m0 os0 dw.ownedList ∧
              DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
              StreamAccumulatorsInit prog.tags m' strmPtr ∧
              (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
                readField? prog.tags m' strmPtr "z_stream_s" fld =
                  readField? prog.tags m strmPtr "z_stream_s" fld) ∧
              readField? prog.tags m' strmPtr "z_stream_s" "msg" = some .null ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b => b = sb ∨ b ∈ dw.ownedList) ∧
              NoHeapLeak m m' (fun b => b ∈ dw.ownedList)) ∨
           (r.toInt ≠ 0 ∧
              (∀ sb soff, strmPtr = .ptr sb soff → PreservesOutsideRange m m' sb soff 112) ∧
              FramePreserved m m' (fun b => PtrBlock strmPtr = some b) ∧
              NoHeapLeak m m' (fun _ => False))))
  deflateEnd_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateEnd
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff dw, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          sb ∉ dw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 dw.ownedList)
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff dw r, args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = 1) ∧
          (∀ b ∈ dw.ownedList, m'.blocks b = none) ∧
          readField? prog.tags m' strmPtr "z_stream_s" "state" = some .null ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b => b = sb ∨ b ∈ dw.ownedList) ∧
          NoHeapLeak m m' (fun _ => False))
  putShortMSB_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_putShortMSB
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr bval strmPtr sb soff dw pend pbsz,
          args = [sPtr, .int .u32 bval] ∧ sPtr = .ptr dw.stBid 0 ∧
          strmPtr = .ptr sb soff ∧ DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          sb ∉ dw.ownedList ∧
          readField? prog.tags m sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
          readNatField? prog.tags m sPtr "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m sPtr "internal_state" "pending_buf_size" = some pbsz ∧
          pend + 2 ≤ pbsz)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr bval strmPtr dw pend,
          args = [sPtr, .int .u32 bval] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          readNatField? prog.tags m sPtr "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m' sPtr "internal_state" "pending" = some (pend + 2) ∧
          (∀ fld, fld ≠ "pending" →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.pbufBid) ∧
          NoHeapLeak m m' (fun _ => False))
  flush_pending_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_flush_pending
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr sb soff dw nextOut availOut,
          args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          (∃ to_, readNatField? prog.tags m strmPtr "z_stream_s" "total_out" = some to_) ∧
          sb ∉ dw.ownedList ∧
          readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
          readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
          (availOut = 0 ∨ (Writable m nextOut availOut ∧
            DisjointFrom nextOut (fun b => b ∈ dw.ownedList ∨ b = sb))))
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr sb soff dw nextOut nextOut' availOut availOut' pend pend',
          args = [strmPtr] ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "total_in", "data_type", "msg"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          (∀ fld, fld ∉ (["pending", "pending_out"] : List String) →
            readField? prog.tags m' (.ptr dw.stBid 0) "internal_state" fld =
              readField? prog.tags m (.ptr dw.stBid 0) "internal_state" fld) ∧
          readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
          readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
          readField? prog.tags m' strmPtr "z_stream_s" "next_out" = some nextOut' ∧
          readNatField? prog.tags m' strmPtr "z_stream_s" "avail_out" = some availOut' ∧
          readNatField? prog.tags m (.ptr dw.stBid 0) "internal_state" "pending" = some pend ∧
          readNatField? prog.tags m' (.ptr dw.stBid 0) "internal_state" "pending" = some pend' ∧
          let len := min pend availOut
          availOut' = availOut - len ∧ pend' = pend - len ∧
          (len = 0 → nextOut' = nextOut) ∧
          (len > 0 → ∃ ob ooff, nextOut = .ptr ob ooff ∧
            nextOut' = .ptr ob (Int64.ofInt (ooff.toInt + len)) ∧
            Readable m' nextOut len ∧
            PreservesOutsideRange m m' ob ooff availOut ∧
            (availOut' = 0 ∨ Writable m' nextOut' availOut')) ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b =>
            b = sb ∨ b = dw.stBid ∨ (len > 0 ∧ PtrBlock nextOut = some b)) ∧
          NoHeapLeak m m' (fun _ => False))
  read_buf_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_read_buf
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr bufPtr size sb soff dw nextIn availIn,
          args = [strmPtr, bufPtr, .int .u32 size] ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          (∃ ti, readNatField? prog.tags m strmPtr "z_stream_s" "total_in" = some ti) ∧
          sb ∉ dw.ownedList ∧
          readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
          readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
          (availIn = 0 ∨ (Readable m nextIn availIn ∧
            DisjointFrom nextIn (fun b => b = sb ∨ b ∈ dw.ownedList))) ∧
          (size.toNat = 0 ∨ availIn = 0 ∨
            (Writable m bufPtr (min availIn size.toNat) ∧
              DisjointFrom bufPtr (fun b => b = sb ∨ b = dw.stBid) ∧
              PtrBlock nextIn ≠ PtrBlock bufPtr)))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr bufPtr size sb soff dw nextIn nextIn' availIn availIn' r,
          args = [strmPtr, bufPtr, .int .u32 size] ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
          (∀ fld, fld ∈ (["next_out", "avail_out", "total_out", "data_type", "msg"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          (∀ fld, readField? prog.tags m' (.ptr dw.stBid 0) "internal_state" fld =
            readField? prog.tags m (.ptr dw.stBid 0) "internal_state" fld) ∧
          readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
          readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
          readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
          readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
          ret = .int .u32 r ∧ r.toNat = min availIn size.toNat ∧
          availIn' = availIn - r.toNat ∧
          (r.toNat = 0 → nextIn' = nextIn) ∧
          (r.toNat > 0 → ∃ ib ioff bb boff, nextIn = .ptr ib ioff ∧ bufPtr = .ptr bb boff ∧
            nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + r.toNat)) ∧
            (availIn' = 0 ∨ Readable m' nextIn' availIn') ∧
            Readable m' bufPtr r.toNat ∧
            PreservesOutsideRange m m' bb boff r.toNat) ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b =>
            b = sb ∨ (r.toNat > 0 ∧ PtrBlock bufPtr = some b)) ∧
          NoHeapLeak m m' (fun _ => False))
  fill_window_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_fill_window
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr strmPtr sb soff dw nextIn availIn look,
          args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          (∃ ti, readNatField? prog.tags m strmPtr "z_stream_s" "total_in" = some ti) ∧
          sb ∉ dw.ownedList ∧
          readNatField? prog.tags m sPtr "internal_state" "lookahead" = some look ∧
          look < 262 ∧
          readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
          readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
          (availIn = 0 ∨ (Readable m nextIn availIn ∧
            DisjointFrom nextIn (fun b => b = sb ∨ b ∈ dw.ownedList))))
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr strmPtr sb soff dw nextIn nextIn' availIn availIn' look look',
          args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
          readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
          readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
          readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
          readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
          readNatField? prog.tags m sPtr "internal_state" "lookahead" = some look ∧
          readNatField? prog.tags m' sPtr "internal_state" "lookahead" = some look' ∧
          availIn' ≤ availIn ∧
          availIn' + look' = availIn + look ∧
          (availIn' = availIn → nextIn' = nextIn) ∧
          (availIn' < availIn → ∃ ib ioff, nextIn = .ptr ib ioff ∧
            nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + (availIn - availIn'))) ∧
            (availIn' = 0 ∨ Readable m' nextIn' availIn')) ∧
          (∀ fld, fld ∈ (["next_out", "avail_out", "total_out", "data_type", "msg"] : List String) →
            readField? prog.tags m' strmPtr "z_stream_s" fld =
              readField? prog.tags m strmPtr "z_stream_s" fld) ∧
          (∀ fld, fld ∈ (["sym_next", "status", "wrap", "pending", "pending_out", "pending_buf",
              "pending_buf_size", "last_flush", "match_available", "level", "strategy",
              "gzhead", "gzindex", "method", "w_size", "w_bits", "w_mask", "bi_buf",
              "bi_valid", "bi_used"] : List String) →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          (∀ str0 bks0,
            readNatField? prog.tags m sPtr "internal_state" "strstart" = some str0 →
            readIntField? prog.tags m sPtr "internal_state" "block_start" = some bks0 →
            ∃ str1 bks1,
              readNatField? prog.tags m' sPtr "internal_state" "strstart" = some str1 ∧
              readIntField? prog.tags m' sPtr "internal_state" "block_start" = some bks1 ∧
              (str1 : Int) - bks1 = (str0 : Int) - bks0) ∧
          PreservesOutsideRange m m' sb soff 112 ∧
          FramePreserved m m' (fun b =>
            b = sb ∨ b = dw.stBid ∨ b = dw.winBid ∨ b = dw.prevBid ∨ b = dw.headBid) ∧
          NoHeapLeak m m' (fun _ => False))
  slide_hash_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_slide_hash
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr strmPtr dw, args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr strmPtr dw, args = [sPtr] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          (∀ fld, fld ≠ "slid" →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid ∨ b = dw.prevBid ∨ b = dw.headBid) ∧
          NoHeapLeak m m' (fun _ => False))

/-- Shared precondition for the 5 block compressors (`deflate_stored`, `deflate_fast`,
`deflate_slow`, `deflate_rle`, `deflate_huff`). -/
def DeflateBlockPre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  ∃ sPtr flush strmPtr sb soff dw nextIn nextOut availIn availOut,
    args = [sPtr, .int .i32 flush] ∧ sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
    0 ≤ flush.toInt ∧ flush.toInt ≤ 5 ∧
    TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
    DeflateStateInv prog.tags gEnv m strmPtr dw ∧
    (∃ ti, readNatField? prog.tags m strmPtr "z_stream_s" "total_in" = some ti) ∧
    (∃ to_, readNatField? prog.tags m strmPtr "z_stream_s" "total_out" = some to_) ∧
    ((∃ lvl, readIntField? prog.tags m sPtr "internal_state" "level" = some lvl ∧ lvl ≤ 0) ∨
      ∃ dt, readIntField? prog.tags m strmPtr "z_stream_s" "data_type" = some dt) ∧
    readField? prog.tags m sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
    readNatField? prog.tags m sPtr "internal_state" "pending" = some 0 ∧
    sb ∉ dw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 dw.ownedList ∧
    (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
    availOut > 0 ∧ Writable m nextOut availOut ∧
    DisjointFrom nextOut (fun b => b ∈ dw.ownedList ∨ b = sb) ∧
    (availIn = 0 ∨ (Readable m nextIn availIn ∧
      DisjointFrom nextIn (fun b => b ∈ dw.ownedList ∨ b = sb) ∧
      PtrBlock nextIn ≠ PtrBlock nextOut))

/-- Shared postcondition for the 5 block compressors. -/
def DeflateBlockPost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  ∃ sPtr flush strmPtr sb soff dw nextIn nextIn' nextOut nextOut'
    availIn availIn' availOut availOut' look' mav' pend' r,
    args = [sPtr, .int .i32 flush] ∧ sPtr = .ptr dw.stBid 0 ∧ strmPtr = .ptr sb soff ∧
    ret = .int .u32 r ∧ (r.toInt = 0 ∨ r.toInt = 1 ∨ r.toInt = 2 ∨ r.toInt = 3) ∧
    DeflateStateInv prog.tags gEnv m strmPtr dw ∧
    DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
    (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
    readField? prog.tags m' strmPtr "z_stream_s" "msg" =
      readField? prog.tags m strmPtr "z_stream_s" "msg" ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
    readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
    readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
    readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
    readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
    readField? prog.tags m' strmPtr "z_stream_s" "next_out" = some nextOut' ∧
    readNatField? prog.tags m' strmPtr "z_stream_s" "avail_out" = some availOut' ∧
    readNatField? prog.tags m' sPtr "internal_state" "lookahead" = some look' ∧
    readNatField? prog.tags m' sPtr "internal_state" "match_available" = some mav' ∧
    readNatField? prog.tags m' sPtr "internal_state" "pending" = some pend' ∧
    availIn' ≤ availIn ∧ availOut' ≤ availOut ∧
    (availIn' = availIn → nextIn' = nextIn) ∧
    (availIn' < availIn → ∃ ib ioff, nextIn = .ptr ib ioff ∧
      nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + (availIn - availIn'))) ∧
      (availIn' = 0 ∨ Readable m' nextIn' availIn')) ∧
    (availOut' = availOut → nextOut' = nextOut) ∧
    (availOut' < availOut → ∃ ob ooff, nextOut = .ptr ob ooff ∧
      nextOut' = .ptr ob (Int64.ofInt (ooff.toInt + (availOut - availOut'))) ∧
      Readable m' nextOut (availOut - availOut') ∧
      PreservesOutsideRange m m' ob ooff availOut ∧
      (availOut' = 0 ∨ Writable m' nextOut' availOut')) ∧
    (r.toInt = 1 ∨ r.toInt = 3 →
      pend' = 0 ∧
      readField? prog.tags m' sPtr "internal_state" "pending_out" = some (.ptr dw.pbufBid 0) ∧
      availIn' = 0 ∧ look' = 0 ∧ mav' = 0) ∧
    (r.toInt = 1 → flush.toInt ≠ 0) ∧
    (r.toInt = 2 → availOut' = 0) ∧
    (r.toInt = 3 → flush.toInt = 4) ∧
    (r.toInt = 0 → availOut' = 0 ∨ (availIn' = 0 ∧ flush.toInt = 0)) ∧
    (0 ≤ flush.toInt → flush.toInt ≤ 4 →
      Tuple5Le (deflateEmitTuple prog.tags m' dw availIn' flush.toInt)
        (deflateEmitTuple prog.tags m dw availIn flush.toInt) ∧
      (availOut' < availOut → availOut' = 0 → availOut ≥ 8 →
        Tuple5Lt (deflateEmitTuple prog.tags m' dw availIn' flush.toInt)
          (deflateEmitTuple prog.tags m dw availIn flush.toInt))) ∧
    (∀ fld, fld ∈ (["level", "strategy", "wrap", "status", "gzhead", "gzindex", "method",
        "last_flush"] : List String) →
      readField? prog.tags m' sPtr "internal_state" fld =
        readField? prog.tags m sPtr "internal_state" fld) ∧
    PreservesOutsideRange m m' sb soff 112 ∧
    FramePreserved m m' (fun b =>
      b = sb ∨ b ∈ dw.ownedList ∨ (availOut' < availOut ∧ PtrBlock nextOut = some b)) ∧
    NoHeapLeak m m' (fun _ => False)

/-- Decoupled verification interface for `Zlib.Deflate` block-compression subroutines
(`longest_match`, `deflate_stored`, `deflate_fast`, `deflate_slow`, `deflate_rle`, `deflate_huff`). -/
structure DeflateBlocksSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userExt : ExtHandler) : Prop where
  longest_match_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_longest_match
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ sPtr curMatch strmPtr dw lvl wsize strstart lookahead prevLen highWater,
          args = [sPtr, .int .u32 curMatch] ∧ sPtr = .ptr dw.stBid 0 ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          readIntField? prog.tags m sPtr "internal_state" "level" = some lvl ∧ lvl ≠ 0 ∧
          readNatField? prog.tags m sPtr "internal_state" "w_size" = some wsize ∧
          readNatField? prog.tags m sPtr "internal_state" "strstart" = some strstart ∧
          readNatField? prog.tags m sPtr "internal_state" "lookahead" = some lookahead ∧
          readNatField? prog.tags m sPtr "internal_state" "prev_length" = some prevLen ∧
          readNatField? prog.tags m sPtr "internal_state" "high_water" = some highWater ∧
          0 < curMatch.toNat ∧ curMatch.toNat < strstart ∧
          strstart - curMatch.toNat ≤ wsize - 262 ∧
          3 ≤ lookahead ∧ 2 ≤ prevLen ∧ prevLen ≤ 257 ∧
          strstart + 258 ≤ highWater)
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ sPtr curMatch strmPtr dw wsize strstart lookahead prevLen matchStart' r,
          args = [sPtr, .int .u32 curMatch] ∧ sPtr = .ptr dw.stBid 0 ∧
          ret = .int .u32 r ∧
          DeflateStateInv prog.tags gEnv m strmPtr dw ∧
          DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
          readNatField? prog.tags m sPtr "internal_state" "w_size" = some wsize ∧
          readNatField? prog.tags m sPtr "internal_state" "strstart" = some strstart ∧
          readNatField? prog.tags m sPtr "internal_state" "lookahead" = some lookahead ∧
          readNatField? prog.tags m sPtr "internal_state" "prev_length" = some prevLen ∧
          readNatField? prog.tags m' sPtr "internal_state" "match_start" = some matchStart' ∧
          r.toNat ≤ lookahead ∧ r.toNat ≤ 258 ∧
          (prevLen < r.toNat →
            1 ≤ strstart - matchStart' ∧ strstart - matchStart' ≤ wsize - 262) ∧
          (∀ fld, fld ≠ "match_start" →
            readField? prog.tags m' sPtr "internal_state" fld =
              readField? prog.tags m sPtr "internal_state" fld) ∧
          FramePreserved m m' (fun b => b = dw.stBid) ∧
          NoHeapLeak m m' (fun _ => False))
  deflate_stored_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflate_stored
      (fun m os args =>
        DeflateBlockPre prog gEnv m0 os0 m os args ∧
        ∃ sPtr flush, args = [sPtr, .int .i32 flush] ∧
          readIntField? prog.tags m sPtr "internal_state" "level" = some 0)
      (DeflateBlockPost prog gEnv m0 os0)
  deflate_fast_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflate_fast
      (fun m os args =>
        DeflateBlockPre prog gEnv m0 os0 m os args ∧
        ∃ sPtr flush lvl, args = [sPtr, .int .i32 flush] ∧
          readIntField? prog.tags m sPtr "internal_state" "level" = some lvl ∧ 0 < lvl ∧
          readIntField? prog.tags m sPtr "internal_state" "match_available" = some 0)
      (DeflateBlockPost prog gEnv m0 os0)
  deflate_slow_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflate_slow
      (fun m os args =>
        DeflateBlockPre prog gEnv m0 os0 m os args ∧
        ∃ sPtr flush lvl, args = [sPtr, .int .i32 flush] ∧
          readIntField? prog.tags m sPtr "internal_state" "level" = some lvl ∧ 0 < lvl)
      (DeflateBlockPost prog gEnv m0 os0)
  deflate_rle_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflate_rle
      (fun m os args =>
        DeflateBlockPre prog gEnv m0 os0 m os args ∧
        ∃ sPtr flush lvl, args = [sPtr, .int .i32 flush] ∧
          readIntField? prog.tags m sPtr "internal_state" "level" = some lvl ∧ 0 < lvl)
      (DeflateBlockPost prog gEnv m0 os0)
  deflate_huff_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflate_huff
      (fun m os args =>
        DeflateBlockPre prog gEnv m0 os0 m os args ∧
        ∃ sPtr flush lvl, args = [sPtr, .int .i32 flush] ∧
          readIntField? prog.tags m sPtr "internal_state" "level" = some lvl ∧ 0 < lvl)
      (DeflateBlockPost prog gEnv m0 os0)

/-- Decoupled verification interface for `Zlib.Deflate.{deflate, deflateParams}` (public contracts +
internal progress-tracked specs for `compress2_z`, `gz_comp`, and `gzsetparams`). -/
structure DeflateMainSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  deflate_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflate_contract
  deflateParams_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Deflate.deflateParams_contract
  deflateParams_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflateParams
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr level strat, args = [strmPtr, .int .i32 level, .int .i32 strat] ∧
          (strmPtr = .null ∨
            ∃ sb soff dw nextIn nextOut availIn availOut owned hd,
              strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              DeflateStateInv prog.tags gEnv m strmPtr dw ∧
              (∃ ti, readNatField? prog.tags m strmPtr "z_stream_s" "total_in" = some ti) ∧
              (∃ to_, readNatField? prog.tags m strmPtr "z_stream_s" "total_out" = some to_) ∧
              (∀ b ∈ dw.ownedList, owned b) ∧
              readField? prog.tags m (.ptr dw.stBid 0) "internal_state" "gzhead" = some hd ∧
              Zlib.Spec.DeflateHeaderReady prog.tags owned m hd ∧
              sb ∉ dw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 dw.ownedList ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
              (availIn = 0 ∨ (Readable m nextIn availIn ∧
                DisjointFrom nextIn (fun b => b ∈ dw.ownedList ∨ b = sb))) ∧
              (availOut = 0 ∨ (Writable m nextOut availOut ∧
                DisjointFrom nextOut (fun b => b ∈ dw.ownedList ∨ b = sb))) ∧
              (availIn = 0 ∨ availOut = 0 ∨ PtrBlock nextIn ≠ PtrBlock nextOut)))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr level strat r,
          args = [strmPtr, .int .i32 level, .int .i32 strat] ∧
          ret = .int .i32 r ∧
          ((strmPtr = .null ∧ r.toInt = -2 ∧ MemBlocksUnchanged m m') ∨
           (∃ sb soff dw nextIn nextIn' nextOut nextOut' availIn availIn' availOut availOut',
              strmPtr = .ptr sb soff ∧
              DeflateStateInv prog.tags gEnv m strmPtr dw ∧
              DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
              (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
              readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
              readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
              readField? prog.tags m' strmPtr "z_stream_s" "next_out" = some nextOut' ∧
              readNatField? prog.tags m' strmPtr "z_stream_s" "avail_out" = some availOut' ∧
              availIn' ≤ availIn ∧ availOut' ≤ availOut ∧
              (availIn' = availIn → nextIn' = nextIn) ∧
              (availIn' < availIn → ∃ ib ioff, nextIn = .ptr ib ioff ∧
                nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + (availIn - availIn'))) ∧
                (availIn' = 0 ∨ Readable m' nextIn' availIn')) ∧
              (availOut' = availOut → nextOut' = nextOut) ∧
              (availOut' < availOut → ∃ ob ooff, nextOut = .ptr ob ooff ∧
                nextOut' = .ptr ob (Int64.ofInt (ooff.toInt + (availOut - availOut'))) ∧
                Readable m' nextOut (availOut - availOut') ∧
                PreservesOutsideRange m m' ob ooff availOut ∧
                (availOut' = 0 ∨ Writable m' nextOut' availOut')) ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b =>
                b = sb ∨ b ∈ dw.ownedList ∨ (availOut' < availOut ∧ PtrBlock nextOut = some b)) ∧
              NoHeapLeak m m' (fun b => b ∈ dw.ownedList))))
  deflate_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Deflate.deflateTU_fn_deflate
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ strmPtr flush, args = [strmPtr, .int .i32 flush] ∧
          (strmPtr = .null ∨
            ∃ sb soff dw nextIn nextOut availIn availOut owned hd,
              strmPtr = .ptr sb soff ∧
              TypedCell prog.tags m strmPtr (.structTy "z_stream_s") ∧
              DeflateStateInv prog.tags gEnv m strmPtr dw ∧
              (∃ ti, readNatField? prog.tags m strmPtr "z_stream_s" "total_in" = some ti) ∧
              (∃ to_, readNatField? prog.tags m strmPtr "z_stream_s" "total_out" = some to_) ∧
              (∀ b ∈ dw.ownedList, owned b) ∧
              readField? prog.tags m (.ptr dw.stBid 0) "internal_state" "gzhead" = some hd ∧
              Zlib.Spec.DeflateHeaderReady prog.tags owned m hd ∧
              sb ∉ dw.ownedList ∧ HeapBlocksFreshFromLib m0 os0 dw.ownedList ∧
              (m0.blocks sb).isNone = true ∧ sb ≠ os0.errnoBlk ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
              (availIn = 0 ∨ (Readable m nextIn availIn ∧
                DisjointFrom nextIn (fun b => b ∈ dw.ownedList ∨ b = sb))) ∧
              (availOut = 0 ∨ (Writable m nextOut availOut ∧
                DisjointFrom nextOut (fun b => b ∈ dw.ownedList ∨ b = sb))) ∧
              (availIn = 0 ∨ availOut = 0 ∨ PtrBlock nextIn ≠ PtrBlock nextOut)))
      (fun m os args ret m' os' =>
        os' = os ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        ∃ strmPtr flush r,
          args = [strmPtr, .int .i32 flush] ∧ ret = .int .i32 r ∧
          ((strmPtr = .null ∧ r.toInt = -2 ∧ MemBlocksUnchanged m m') ∨
           (∃ sb soff dw nextIn nextIn' nextOut nextOut' availIn availIn' availOut availOut'
              wrap0 hd0,
              strmPtr = .ptr sb soff ∧
              DeflateStateInv prog.tags gEnv m strmPtr dw ∧
              DeflateStateInv prog.tags gEnv m' strmPtr dw ∧
              (StreamAccumulatorsInit prog.tags m strmPtr → StreamAccumulatorsInit prog.tags m' strmPtr) ∧
              readIntField? prog.tags m (.ptr dw.stBid 0) "internal_state" "wrap" = some wrap0 ∧
              readField? prog.tags m (.ptr dw.stBid 0) "internal_state" "gzhead" = some hd0 ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_in" = some nextIn ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_in" = some availIn ∧
              readField? prog.tags m strmPtr "z_stream_s" "next_out" = some nextOut ∧
              readNatField? prog.tags m strmPtr "z_stream_s" "avail_out" = some availOut ∧
              readField? prog.tags m' strmPtr "z_stream_s" "next_in" = some nextIn' ∧
              readNatField? prog.tags m' strmPtr "z_stream_s" "avail_in" = some availIn' ∧
              readField? prog.tags m' strmPtr "z_stream_s" "next_out" = some nextOut' ∧
              readNatField? prog.tags m' strmPtr "z_stream_s" "avail_out" = some availOut' ∧
              availIn' ≤ availIn ∧ availOut' ≤ availOut ∧
              (availIn' = availIn → nextIn' = nextIn) ∧
              (availIn' < availIn → ∃ ib ioff, nextIn = .ptr ib ioff ∧
                nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + (availIn - availIn'))) ∧
                (availIn' = 0 ∨ Readable m' nextIn' availIn')) ∧
              (availOut' = availOut → nextOut' = nextOut) ∧
              (availOut' < availOut → ∃ ob ooff, nextOut = .ptr ob ooff ∧
                nextOut' = .ptr ob (Int64.ofInt (ooff.toInt + (availOut - availOut'))) ∧
                Readable m' nextOut (availOut - availOut') ∧
                PreservesOutsideRange m m' ob ooff availOut ∧
                (availOut' = 0 ∨ Writable m' nextOut' availOut')) ∧
              (availOut = 0 → r.toInt ≠ 0 ∧ r.toInt ≠ 1) ∧
              (wrap0 ≠ 0 → hd0 = .null → 0 ≤ flush.toInt → flush.toInt ≤ 4 →
                r.toInt = 0 → availIn' < availIn ∨ availOut' < availOut) ∧
              (hd0 = .null → 0 ≤ flush.toInt → flush.toInt ≤ 4 →
                availOut' < availOut →
                (availOut' > 0 →
                  Tuple5Le (deflateEmitTuple prog.tags m' dw availIn' flush.toInt)
                    (deflateEmitTuple prog.tags m dw availIn flush.toInt)) ∧
                (availOut' = 0 → availOut ≥ 8 →
                  Tuple5Lt (deflateEmitTuple prog.tags m' dw availIn' flush.toInt)
                    (deflateEmitTuple prog.tags m dw availIn flush.toInt))) ∧
              (∀ msg0, readField? prog.tags m strmPtr "z_stream_s" "msg" = some msg0 →
                (msg0 = .null ∨ ∃ mb0 mblk0, msg0 = .ptr mb0 0 ∧ m.blocks mb0 = some mblk0 ∧
                  mblk0.kind = .global ∧ mblk0.perm = .ro ∧ CString m msg0) →
                ∃ msg', readField? prog.tags m' strmPtr "z_stream_s" "msg" = some msg' ∧
                  (msg' = .null ∨ ∃ mb' mblk', msg' = .ptr mb' 0 ∧ m'.blocks mb' = some mblk' ∧
                    mblk'.kind = .global ∧ mblk'.perm = .ro ∧ CString m' msg')) ∧
              PreservesOutsideRange m m' sb soff 112 ∧
              FramePreserved m m' (fun b =>
                b = sb ∨ b ∈ dw.ownedList ∨ (availOut' < availOut ∧ PtrBlock nextOut = some b)) ∧
              NoHeapLeak m m' (fun b => b ∈ dw.ownedList))))

/-- Precondition for `gz_error(state, err, msg)` requiring only `gz_state` + `path` + `msg?`. -/
def GzErrorPre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  ∃ (statePtr : Val) (errVal : BitVec 32) (msgArg : Val)
    (gzBid pathBid : BlockId) (msgBid? : Option BlockId),
    args = [statePtr, .int .i32 errVal, msgArg] ∧
    statePtr = .ptr gzBid 0 ∧
    HeapRwBlock m gzBid 248 8 ∧
    HeapBlocksFreshFromLib m0 os0 (gzBid :: pathBid :: msgBid?.toList) ∧
    readField? prog.tags m statePtr "gz_state" "path" = some (.ptr pathBid 0) ∧
    (∃ pblk, m.blocks pathBid = some pblk ∧ pblk.kind = .heap ∧ pblk.perm = .rw ∧
      ∃ plen, m.strlenAt pathBid 0 = some plen) ∧
    (∃ curErr : Int, readIntField? prog.tags m statePtr "gz_state" "err" = some curErr ∧
      match msgBid? with
      | none => readField? prog.tags m statePtr "gz_state" "msg" = some .null ∨
          (curErr = -4 ∧ ∃ mp, readField? prog.tags m statePtr "gz_state" "msg" = some mp ∧ CString m mp)
      | some mb => curErr ≠ -4 ∧ readField? prog.tags m statePtr "gz_state" "msg" = some (.ptr mb 0) ∧
          ∃ mblk, m.blocks mb = some mblk ∧ mblk.kind = .heap ∧ mblk.perm = .rw ∧
            ∃ mlen, m.strlenAt mb 0 = some mlen) ∧
    pathBid ≠ gzBid ∧
    (∀ mb, msgBid? = some mb → mb ≠ gzBid ∧ mb ≠ pathBid) ∧
    OptCString m msgArg ∧
    DisjointFrom msgArg (fun b => b = gzBid ∨ b = pathBid ∨ msgBid? = some b ∨
      b = os.errnoBlk ∨ os.strerrorBlk = some b)

/-- Postcondition for `gz_error` preserving all non-`(err, msg)` fields of `gz_state`. -/
def GzErrorPost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .void ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  os'.errnoBlk = os.errnoBlk ∧ os'.strerrorBlk = os.strerrorBlk ∧
  ∃ (statePtr : Val) (errVal : BitVec 32) (msgArg : Val) (gzBid pathBid : BlockId)
    (msgBid? msgBid'? : Option BlockId),
    args = [statePtr, .int .i32 errVal, msgArg] ∧
    statePtr = .ptr gzBid 0 ∧
    readField? prog.tags m statePtr "gz_state" "path" = some (.ptr pathBid 0) ∧
    (∀ mb, msgBid? = some mb → m'.blocks mb = none) ∧
    (match msgBid'? with
     | none => True
     | some mb' =>
       (m.blocks mb').isNone = true ∧ (m0.blocks mb').isNone = true ∧
       mb' ≠ os0.errnoBlk ∧ mb' ≠ gzBid ∧ mb' ≠ pathBid ∧
       (∀ mb, msgBid? = some mb → mb' ≠ mb) ∧
       ∃ mblk', m'.blocks mb' = some mblk' ∧ mblk'.kind = .heap ∧ mblk'.perm = .rw ∧
         ∃ mlen', m'.strlenAt mb' 0 = some mlen') ∧
    (∃ e' : Int, readIntField? prog.tags m' statePtr "gz_state" "err" = some e' ∧
      (msgBid'?.isSome = true → e' = errVal.toInt ∧ e' ≠ -4) ∧
      (msgBid'? = none → e' = errVal.toInt ∨ e' = -4) ∧
      match msgBid'? with
      | none => readField? prog.tags m' statePtr "gz_state" "msg" = some .null
      | some mb' => readField? prog.tags m' statePtr "gz_state" "msg" = some (.ptr mb' 0)) ∧
    (∀ fld, fld ∉ (["err", "msg"] : List String) →
      readField? prog.tags m' statePtr "gz_state" fld =
        readField? prog.tags m statePtr "gz_state" fld) ∧
    readField? prog.tags m' statePtr "gz_state" "x" =
      readField? prog.tags m statePtr "gz_state" "x" ∧
    (∀ (off : Int) ty, off ≥ 136 →
      Sem.readVal prog.tags m' gzBid (Int64.ofInt off) ty =
        Sem.readVal prog.tags m gzBid (Int64.ofInt off) ty) ∧
    FramePreserved m m' (fun b => b = gzBid ∨ msgBid? = some b ∨ msgBid'? = some b ∨ b = os.errnoBlk) ∧
    NoHeapLeak m m' (fun b => msgBid'? = some b)

/-- Precondition for `gz_reset(state)` (satisfied both by `GzStateInv` and `gz_open` post-init). -/
def GzResetPre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  ∃ (statePtr : Val) (gw : GzWitness),
    args = [statePtr] ∧ statePtr = .ptr gw.gzBid 0 ∧
    HeapRwBlock m gw.gzBid 248 8 ∧
    gw.ownedList.Nodup ∧
    HeapBlocksFreshFromLib m0 os0 gw.ownedList ∧
    (∃ mode, readIntField? prog.tags m statePtr "gz_state" "mode" = some mode ∧
      (mode = 7247 ∨ mode = 31153)) ∧
    (∃ size, readNatField? prog.tags m statePtr "gz_state" "size" = some size ∧
      (size = 0 ∨ size ≥ 8)) ∧
    (∃ want, readNatField? prog.tags m statePtr "gz_state" "want" = some want ∧ want ≥ 8) ∧
    (∃ fd, readIntField? prog.tags m statePtr "gz_state" "fd" = some fd) ∧
    (∃ direct, readIntField? prog.tags m statePtr "gz_state" "direct" = some direct ∧
      (direct = 0 ∨ direct = 1)) ∧
    (∃ level, readIntField? prog.tags m statePtr "gz_state" "level" = some level) ∧
    (∃ strat, readIntField? prog.tags m statePtr "gz_state" "strategy" = some strat) ∧
    (∃ start, readIntField? prog.tags m statePtr "gz_state" "start" = some start) ∧
    readField? prog.tags m statePtr "gz_state" "path" = some (.ptr gw.pathBid 0) ∧
    (∃ pblk, m.blocks gw.pathBid = some pblk ∧ pblk.kind = .heap ∧ pblk.perm = .rw ∧
      ∃ plen, m.strlenAt gw.pathBid 0 = some plen) ∧
    (∃ curErr : Int, readIntField? prog.tags m statePtr "gz_state" "err" = some curErr ∧
      match gw.msg? with
      | none => readField? prog.tags m statePtr "gz_state" "msg" = some .null ∨
          (curErr = -4 ∧ ∃ mp, readField? prog.tags m statePtr "gz_state" "msg" = some mp ∧ CString m mp)
      | some mb => curErr ≠ -4 ∧ readField? prog.tags m statePtr "gz_state" "msg" = some (.ptr mb 0) ∧
          ∃ mblk, m.blocks mb = some mblk ∧ mblk.kind = .heap ∧ mblk.perm = .rw ∧
            ∃ mlen, m.strlenAt mb 0 = some mlen) ∧
    (readNatField? prog.tags m statePtr "gz_state" "size" = some 0 →
      gw.in? = none ∧ gw.out? = none ∧ gw.stream? = none ∧
      readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "next_in" = some .null ∧
      readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "zalloc" = some .null ∧
      readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "zfree" = some .null ∧
      readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "opaque" = some .null ∧
      readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "state" = some .null) ∧
    (∀ sz, readNatField? prog.tags m statePtr "gz_state" "size" = some sz → sz > 0 →
      ∃ md, readIntField? prog.tags m statePtr "gz_state" "mode" = some md ∧
        (md = 7247 →
          ∃ inBid outBid iw inBlk outBlk,
            gw.in? = some inBid ∧ gw.out? = some outBid ∧ gw.stream? = some (.inl iw) ∧
            readField? prog.tags m statePtr "gz_state" "in" = some (.ptr inBid 0) ∧
            readField? prog.tags m statePtr "gz_state" "out" = some (.ptr outBid 0) ∧
            m.blocks inBid = some inBlk ∧ inBlk.kind = .heap ∧ inBlk.perm = .rw ∧ inBlk.size ≥ sz ∧
            m.blocks outBid = some outBlk ∧ outBlk.kind = .heap ∧ outBlk.perm = .rw ∧ outBlk.size ≥ 2 * sz ∧
            InflateStateInv prog.tags gEnv m (.ptr gw.gzBid 136) iw ∧
            readField? prog.tags m (.ptr iw.stBid 0) "inflate_state" "head" = some .null ∧
            (∃ smsg, readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "msg" = some smsg ∧
              (smsg = .null ∨ ∃ mb mblk, smsg = .ptr mb 0 ∧ m.blocks mb = some mblk ∧
                mblk.kind = .global ∧ mblk.perm = .ro ∧ ∃ mlen, m.strlenAt mb 0 = some mlen))) ∧
        (md = 31153 →
          ∃ inBid inBlk,
            gw.in? = some inBid ∧
            readField? prog.tags m statePtr "gz_state" "in" = some (.ptr inBid 0) ∧
            m.blocks inBid = some inBlk ∧ inBlk.kind = .heap ∧ inBlk.perm = .rw ∧ inBlk.size ≥ sz ∧
            ∃ dir, readIntField? prog.tags m statePtr "gz_state" "direct" = some dir ∧
              (dir = 1 → gw.out? = none ∧ gw.stream? = none) ∧
              (dir = 0 →
                ∃ outBid outBlk dw,
                  gw.out? = some outBid ∧ gw.stream? = some (.inr dw) ∧
                  readField? prog.tags m statePtr "gz_state" "out" = some (.ptr outBid 0) ∧
                  m.blocks outBid = some outBlk ∧ outBlk.kind = .heap ∧ outBlk.perm = .rw ∧ outBlk.size ≥ sz ∧
                  DeflateStateInv prog.tags gEnv m (.ptr gw.gzBid 136) dw)))

/-- Postcondition for `gz_reset`: establishes full `GzStateInv` with `msg? := none`. -/
def GzResetPost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (args : List Val) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .void ∧ LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  os'.errnoBlk = os.errnoBlk ∧ os'.strerrorBlk = os.strerrorBlk ∧
  ∃ (statePtr : Val) (gw : GzWitness),
    args = [statePtr] ∧ statePtr = .ptr gw.gzBid 0 ∧
    let gw' := { gw with msg? := none }
    (∀ mb, gw.msg? = some mb → m'.blocks mb = none) ∧
    GzStateInv prog.tags gEnv m' gw' ∧
    FramePreserved m m' (fun b => b = gw.gzBid ∨ gw.msg? = some b) ∧
    NoHeapLeak m m' (fun _ => False)

/-- Decoupled verification interface for `Zlib.Gzlib` (14 public contracts + 4 helpers). -/
structure GzlibSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  gzopen_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzopen_contract
  gzopen64_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzopen64_contract
  gzdopen_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzdopen_contract
  gzbuffer_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzbuffer_contract
  gzrewind_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzrewind_contract
  gzseek64_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzseek64_contract
  gzseek_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzseek_contract
  gztell64_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gztell64_contract
  gztell_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gztell_contract
  gzoffset64_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzoffset64_contract
  gzoffset_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzoffset_contract
  gzeof_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzeof_contract
  gzerror_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzerror_contract
  gzclearerr_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzlib.gzclearerr_contract
  gz_open_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzlib.gzlibTU_fn_gz_open
      (fun m os args =>
        LibGlobalsOk prog gEnv m0 os0 m os ∧
        ∃ pathPtr fd modePtr,
          args = [pathPtr, .int .i32 fd, modePtr] ∧
          OptCString m pathPtr ∧ OptCString m modePtr ∧
          DisjointFrom pathPtr (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b) ∧
          DisjointFrom modePtr (fun b => b = os.errnoBlk ∨ os.strerrorBlk = some b))
      (fun m os _ ret m' os' =>
        LibGlobalsOk prog gEnv m0 os0 m' os' ∧
        os'.errnoBlk = os.errnoBlk ∧ os'.strerrorBlk = os.strerrorBlk ∧
        ((ret = .null ∧ FramePreserved m m' (fun b => b = os.errnoBlk) ∧ NoHeapLeak m m' (fun _ => False)) ∨
         (∃ gw : GzWitness, ret = .ptr gw.gzBid 0 ∧
            gw.in? = none ∧ gw.out? = none ∧ gw.msg? = none ∧ gw.stream? = none ∧
            (∀ b ∈ gw.ownedList, (m.blocks b).isNone = true) ∧
            HeapBlocksFreshFromLib m0 os0 gw.ownedList ∧
            GzStateInv prog.tags gEnv m' gw ∧
            FramePreserved m m' (fun b => b ∈ gw.ownedList ∨ b = os.errnoBlk) ∧
            NoHeapLeak m m' (fun b => b ∈ gw.ownedList))))
  gz_reset_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzlib.gzlibTU_fn_gz_reset
      (GzResetPre prog gEnv m0 os0)
      (GzResetPost prog gEnv m0 os0)
  gz_error_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzlib.gzlibTU_fn_gz_error
      (GzErrorPre prog gEnv m0 os0)
      (GzErrorPost prog gEnv m0 os0)
  gz_intmax_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzlib.gzlibTU_fn_gz_intmax
      (fun _ _ args => args = [])
      (fun m os _ ret m' os' =>
        MemBlocksUnchanged m m' ∧ os' = os ∧ ∃ u : BitVec 32, ret = .int .u32 u ∧ u.toNat > 0)

/-- Common `GZ_READ` step invariant for internal `Gzread` helpers operating on a live `gw`. -/
def GzReadStepPre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  GzStateInv prog.tags gEnv m gw ∧
  readIntField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "mode" = some 7247 ∧
  HeapBlocksFreshFromLib m0 os0 gw.ownedList

/-- Parameterized `GZ_READ` step postcondition preserving `GzStateInvCore checkReadX true`
with exact heap/frame accounting. -/
def GzReadStepPostCore (checkReadX : Bool) (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) (extraMod : BlockSet)
    (m' : Mem) (os' : OSState) (gw' : GzWitness) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  os'.errnoBlk = os.errnoBlk ∧
  gw'.gzBid = gw.gzBid ∧ gw'.pathBid = gw.pathBid ∧
  GzStateInvCore checkReadX true prog.tags gEnv m' gw' ∧
  readIntField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "mode" = some 7247 ∧
  HeapBlocksFreshFromLib m0 os0 gw'.ownedList ∧
  (∀ b ∈ gw'.ownedList, b ∉ gw.ownedList → (m.blocks b).isNone = true) ∧
  FramePreserved m m' (fun b =>
    b ∈ gw.ownedList ∨ b ∈ gw'.ownedList ∨ extraMod b ∨
    b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
  NoHeapLeak m m' (fun b => b ∈ gw'.ownedList)

/-- Standard `GZ_READ` step postcondition (`checkReadX = true`). -/
abbrev GzReadStepPost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) (extraMod : BlockSet)
    (m' : Mem) (os' : OSState) (gw' : GzWitness) : Prop :=
  GzReadStepPostCore true prog gEnv m0 os0 m os gw extraMod m' os' gw'

/-- Decoupled verification interface for `Zlib.Gzread` (8 public contracts + internal helpers
including `gzclose_r_spec` for `Zlib.Gzclose`). -/
structure GzreadSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  gzread_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzread_contract
  gzfread_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzfread_contract
  gzgetc_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzgetc_contract
  gzgetc__safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzgetc__contract
  gzungetc_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzungetc_contract
  gzgets_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzgets_contract
  gzdirect_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzdirect_contract
  gzclose_r_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzread.gzclose_r_contract
  gzclose_r_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gzclose_r
      (fun m os args => ∃ v owned file,
        args = [file] ∧ ZlibInv prog gEnv m0 os0 v owned m os ∧ GzReady v file)
      (fun m os args ret m' os' => ∀ v owned file,
        args = [file] → ZlibInv prog gEnv m0 os0 v owned m os → GzReady v file →
        ∃ owned' v',
          Zlib.Gzread.gzclose_r_contract.post prog.tags owned v m [file] ret m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ Zlib.Gzread.gzclose_r_contract.modSet prog.tags owned v m [file] b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))
  gz_load_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_load
      (fun m os args =>
        ∃ gw bufPtr len havePtr hb hoff,
          args = [.ptr gw.gzBid 0, bufPtr, .int .u32 len, havePtr] ∧
          GzReadStepPre prog gEnv m0 os0 m os gw ∧
          havePtr = .ptr hb hoff ∧ TypedCell prog.tags m havePtr (.int .u32) ∧
          hb ≠ gw.pathBid ∧ (∀ mb, gw.msg? = some mb → hb ≠ mb) ∧
          hb ≠ os.errnoBlk ∧ (∀ b ∈ GzWitness.streamOwnedList gw.stream?, hb ≠ b) ∧
          (∀ b, gw.in? = some b → hb ≠ b) ∧ (∀ b, gw.out? = some b → hb ≠ b) ∧
          (hb = gw.gzBid → hoff = 0) ∧
          (len.toNat = 0 ∨ Writable m bufPtr len.toNat) ∧
          DisjointFrom bufPtr (fun b =>
            b = gw.gzBid ∨ b = gw.pathBid ∨ gw.msg? = some b ∨
            b ∈ GzWitness.streamOwnedList gw.stream? ∨ b = os.errnoBlk) ∧
          (∀ b, PtrBlock bufPtr = some b → gw.in? = some b →
            ∀ nIn avIn o,
              readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "next_in" = some nIn →
              readNatField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "avail_in" = some avIn →
              avIn = 0 ∨ (nIn = .ptr b (Int64.ofNat o) → ∃ boff, bufPtr = .ptr b boff ∧
                DisjointByteRanges b (Int64.ofNat o) avIn b boff len.toNat)) ∧
          (hb = gw.gzBid →
            ∃ sz ob,
              readNatField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "size" = some sz ∧
              gw.out? = some ob ∧ bufPtr = .ptr ob 0 ∧ len.toNat ≤ 2 * sz ∧
              readField? prog.tags m (.ptr gw.gzBid 0) "gzFile_s" "next" = some (.ptr ob 0)) ∧
          (∀ bb boff, bufPtr = .ptr bb boff → hb = bb →
            DisjointByteRanges hb hoff 4 bb boff len.toNat))
      (fun m os args ret m' os' =>
        ∃ gw bufPtr len havePtr hb hoff r have' gw',
          args = [.ptr gw.gzBid 0, bufPtr, .int .u32 len, havePtr] ∧
          havePtr = .ptr hb hoff ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          Sem.readVal prog.tags m' hb hoff (.int .u32) = some (.int .u32 have') ∧
          have'.toNat ≤ len.toNat ∧
          (have'.toNat = 0 ∨ Readable m' bufPtr have'.toNat) ∧
          (∀ bb boff, bufPtr = .ptr bb boff → PreservesOutsideRange m m' bb boff len.toNat) ∧
          (∀ fld, fld ∈ (["mode", "size", "want", "fd", "direct", "junk", "how", "start",
              "past", "level", "strategy", "reset", "skip", "in", "out", "path"] : List String) →
            readField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" fld =
              readField? prog.tags m (.ptr gw.gzBid 0) "gz_state" fld) ∧
          (∀ fld, fld ∈ (["next_in", "avail_in", "next_out", "avail_out"] : List String) →
            readField? prog.tags m' (.ptr gw'.gzBid 136) "z_stream_s" fld =
              readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" fld) ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPost prog gEnv m0 os0 m os gw
            (fun b => (hb ≠ gw.gzBid ∧ b = hb) ∨ (len.toNat > 0 ∧ PtrBlock bufPtr = some b))
            m' os' gw')
  gz_avail_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_avail
      (fun m os args =>
        ∃ gw sz, args = [.ptr gw.gzBid 0] ∧
          GzReadStepPre prog gEnv m0 os0 m os gw ∧
          readNatField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "size" = some sz ∧ sz > 0)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPost prog gEnv m0 os0 m os gw (fun _ => False) m' os' gw')
  gz_room_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_room
      (fun m os args =>
        ∃ gw max, args = [.ptr gw.gzBid 0, .int .u32 max] ∧
          GzReadStepPre prog gEnv m0 os0 m os gw ∧ max.toNat ≥ 1)
      (fun m os args ret m' os' =>
        MemBlocksUnchanged m m' ∧ os' = os ∧
        ∃ max r,
          args.tail = [.int .u32 max] ∧ ret = .int .u32 r ∧
          r.toNat ≤ max.toNat)
  gz_look_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_look
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzReadStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPost prog gEnv m0 os0 m os gw (fun _ => False) m' os' gw' ∧
          (r.toInt = 0 →
            ∃ sz, readNatField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "size" = some sz ∧ sz ≥ 8))
  gz_decomp_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_decomp
      (fun m os args =>
        ∃ gw sz availOut nextOut, args = [.ptr gw.gzBid 0] ∧
          GzReadStepPre prog gEnv m0 os0 m os gw ∧
          readNatField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "size" = some sz ∧ sz ≥ 8 ∧
          readIntField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "how" = some 2 ∧
          readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "next_out" = some nextOut ∧
          readNatField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "avail_out" = some availOut ∧
          availOut > 0 ∧ Writable m nextOut availOut ∧
          DisjointFrom nextOut (fun b =>
            b = gw.gzBid ∨ b = gw.pathBid ∨ gw.msg? = some b ∨ b = os.errnoBlk ∨
            gw.in? = some b ∨ b ∈ GzWitness.streamOwnedList gw.stream?))
      (fun m os args ret m' os' =>
        ∃ gw r gw' nextOut availOut xHave' availOut', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "next_out" = some nextOut ∧
          readNatField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "avail_out" = some availOut ∧
          readNatField? prog.tags m' (.ptr gw'.gzBid 0) "gzFile_s" "have" = some xHave' ∧
          readNatField? prog.tags m' (.ptr gw'.gzBid 136) "z_stream_s" "avail_out" = some availOut' ∧
          availOut' ≤ availOut ∧ xHave' = availOut - availOut' ∧
          readField? prog.tags m' (.ptr gw'.gzBid 0) "gzFile_s" "next" = some nextOut ∧
          (xHave' = 0 ∨ Readable m' nextOut xHave') ∧
          (∀ ob ooff, nextOut = .ptr ob ooff → PreservesOutsideRange m m' ob ooff availOut) ∧
          readIntField? prog.tags m' (.ptr gw'.gzBid 0) "gzFile_s" "pos" =
            readIntField? prog.tags m (.ptr gw.gzBid 0) "gzFile_s" "pos" ∧
          gw'.out? = gw.out? ∧ gw'.in? = gw.in? ∧
          readNatField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "size" =
            readNatField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "size" ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPostCore false prog gEnv m0 os0 m os gw
            (fun b => PtrBlock nextOut = some b) m' os' gw')
  gz_fetch_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_fetch
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzReadStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPost prog gEnv m0 os0 m os gw (fun _ => False) m' os' gw')
  gz_skip_have_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_skip_have
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzReadStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ret = .void ∧ os' = os ∧
        ∃ gw, args = [.ptr gw.gzBid 0] ∧
          GzReadStepPost prog gEnv m0 os0 m os gw (fun _ => False) m' os' gw)
  gz_skip_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_skip
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzReadStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPost prog gEnv m0 os0 m os gw (fun _ => False) m' os' gw')
  gz_read_spec :
    CallSafeSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzread.gzreadTU_fn_gz_read
      (fun m os args =>
        ∃ gw bufPtr len, args = [.ptr gw.gzBid 0, bufPtr, .int .u64 len] ∧
          GzReadStepPre prog gEnv m0 os0 m os gw ∧
          (len.toNat = 0 ∨ Writable m bufPtr len.toNat) ∧
          DisjointFrom bufPtr (fun b => b ∈ gw.ownedList ∨ b = os.errnoBlk))
      (fun m os args ret m' os' =>
        ∃ gw bufPtr len r gw',
          args = [.ptr gw.gzBid 0, bufPtr, .int .u64 len] ∧
          ret = .int .u64 r ∧ r.toNat ≤ len.toNat ∧
          (os.readBudget.isSome = true → os'.readBudget.isSome = true) ∧
          GzReadStepPost prog gEnv m0 os0 m os gw
            (fun b => len.toNat > 0 ∧ PtrBlock bufPtr = some b)
            m' os' gw')

/-- Parameterized `GZ_WRITE` step invariant operating on a live `gw`. -/
def GzWriteStepPreCore (checkWriteIn : Bool) (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m os ∧
  GzStateInvCore true checkWriteIn prog.tags gEnv m gw ∧
  readIntField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "mode" = some 31153 ∧
  HeapBlocksFreshFromLib m0 os0 gw.ownedList

/-- Standard `GZ_WRITE` step invariant (`checkWriteIn = true`). -/
abbrev GzWriteStepPre (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) : Prop :=
  GzWriteStepPreCore true prog gEnv m0 os0 m os gw

/-- Parameterized `GZ_WRITE` step postcondition preserving `GzStateInvCore true checkWriteIn`
with exact heap/frame accounting. -/
def GzWriteStepPostCore (checkWriteIn : Bool) (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) (m' : Mem) (os' : OSState) (gw' : GzWitness) : Prop :=
  LibGlobalsOk prog gEnv m0 os0 m' os' ∧
  os'.errnoBlk = os.errnoBlk ∧
  gw'.gzBid = gw.gzBid ∧ gw'.pathBid = gw.pathBid ∧
  GzStateInvCore true checkWriteIn prog.tags gEnv m' gw' ∧
  readIntField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "mode" = some 31153 ∧
  HeapBlocksFreshFromLib m0 os0 gw'.ownedList ∧
  (∀ b ∈ gw'.ownedList, b ∉ gw.ownedList → (m.blocks b).isNone = true) ∧
  FramePreserved m m' (fun b =>
    b ∈ gw.ownedList ∨ b ∈ gw'.ownedList ∨
    b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
  NoHeapLeak m m' (fun b => b ∈ gw'.ownedList)

/-- Standard `GZ_WRITE` step postcondition (`checkWriteIn = true`). -/
abbrev GzWriteStepPost (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (m : Mem) (os : OSState) (gw : GzWitness) (m' : Mem) (os' : OSState) (gw' : GzWitness) : Prop :=
  GzWriteStepPostCore true prog gEnv m0 os0 m os gw m' os' gw'

/-- Decoupled verification interface for `Zlib.Gzwrite` (8 public contracts + internal helpers
including `gzclose_w_spec` for `Zlib.Gzclose`). -/
structure GzwriteSpecs (prog : Prog) (gEnv : Env) (m0 : Mem) (os0 : OSState)
    (userWrite : BlockSet) (userExt : ExtHandler) : Prop where
  gzwrite_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzwrite_contract
  gzfwrite_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzfwrite_contract
  gzputc_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzputc_contract
  gzputs_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzputs_contract
  gzprintf_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzprintf_contract
  gzflush_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzflush_contract
  gzsetparams_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzsetparams_contract
  gzclose_w_safe :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) (ZlibInv prog gEnv m0 os0) userWrite
      Zlib.Gzwrite.gzclose_w_contract
  gzclose_w_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gzclose_w
      (fun m os args => ∃ v owned file,
        args = [file] ∧ ZlibInv prog gEnv m0 os0 v owned m os ∧ GzReady v file)
      (fun m os args ret m' os' => ∀ v owned file,
        args = [file] → ZlibInv prog gEnv m0 os0 v owned m os → GzReady v file →
        ∃ owned' v',
          Zlib.Gzwrite.gzclose_w_contract.post prog.tags owned v m [file] ret m' v' ∧
          ZlibInv prog gEnv m0 os0 v' owned' m' os' ∧
          FramePreserved m m' (fun b =>
            owned b ∨ owned' b ∨ Zlib.Gzwrite.gzclose_w_contract.modSet prog.tags owned v m [file] b ∨
            userWrite b ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
          NoHeapLeak m m' owned' ∧
          (v'.isEmpty → ∀ b, ¬ owned' b))
  gz_init_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gz_init
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzWriteStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          GzWriteStepPost prog gEnv m0 os0 m os gw m' os' gw' ∧
          (r.toInt = 0 →
            ∃ sz, readNatField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "size" = some sz ∧ sz ≥ 8))
  gz_comp_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gz_comp
      (fun m os args =>
        ∃ gw flush nextIn availIn,
          args = [.ptr gw.gzBid 0, .int .i32 flush] ∧
          GzWriteStepPreCore false prog gEnv m0 os0 m os gw ∧
          0 ≤ flush.toInt ∧ flush.toInt ≤ 4 ∧
          readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "next_in" = some nextIn ∧
          readNatField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "avail_in" = some availIn ∧
          (availIn = 0 ∨ Readable m nextIn availIn) ∧
          DisjointFrom nextIn (fun b =>
            b = gw.gzBid ∨ b = gw.pathBid ∨ gw.msg? = some b ∨ b = os.errnoBlk ∨
            gw.out? = some b ∨ b ∈ GzWitness.streamOwnedList gw.stream?))
      (fun m os args ret m' os' =>
        ∃ gw flush nextIn nextIn' availIn availIn' r gw',
          args = [.ptr gw.gzBid 0, .int .i32 flush] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          readField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "next_in" = some nextIn ∧
          readNatField? prog.tags m (.ptr gw.gzBid 136) "z_stream_s" "avail_in" = some availIn ∧
          readField? prog.tags m' (.ptr gw'.gzBid 136) "z_stream_s" "next_in" = some nextIn' ∧
          readNatField? prog.tags m' (.ptr gw'.gzBid 136) "z_stream_s" "avail_in" = some availIn' ∧
          availIn' ≤ availIn ∧
          (availIn' = availIn → nextIn' = nextIn) ∧
          (availIn' < availIn → ∃ ib ioff, nextIn = .ptr ib ioff ∧
            nextIn' = .ptr ib (Int64.ofInt (ioff.toInt + (availIn - availIn'))) ∧
            (availIn' = 0 ∨ Readable m' nextIn' availIn')) ∧
          readIntField? prog.tags m' (.ptr gw'.gzBid 0) "gzFile_s" "pos" =
            readIntField? prog.tags m (.ptr gw.gzBid 0) "gzFile_s" "pos" ∧
          (∀ sz, readNatField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "size" = some sz → sz > 0 →
            gw'.in? = gw.in?) ∧
          GzWriteStepPostCore false prog gEnv m0 os0 m os gw m' os' gw' ∧
          (r.toInt = 0 → availIn' = 0))
  gz_zero_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gz_zero
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzWriteStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = -1) ∧
          GzWriteStepPost prog gEnv m0 os0 m os gw m' os' gw' ∧
          (r.toInt = 0 →
            readIntField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "skip" = some 0))
  gz_write_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gz_write
      (fun m os args =>
        ∃ gw bufPtr len, args = [.ptr gw.gzBid 0, bufPtr, .int .u64 len] ∧
          GzWriteStepPre prog gEnv m0 os0 m os gw ∧
          (len.toNat = 0 ∨ Readable m bufPtr len.toNat) ∧
          DisjointFrom bufPtr (fun b => b ∈ gw.ownedList ∨ b = os.errnoBlk))
      (fun m os args ret m' os' =>
        ∃ gw bufPtr len r gw',
          args = [.ptr gw.gzBid 0, bufPtr, .int .u64 len] ∧
          ret = .int .u64 r ∧ r.toNat ≤ len.toNat ∧
          GzWriteStepPost prog gEnv m0 os0 m os gw m' os' gw')
  gz_vacate_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gz_vacate
      (fun m os args =>
        ∃ gw, args = [.ptr gw.gzBid 0] ∧ GzWriteStepPre prog gEnv m0 os0 m os gw)
      (fun m os args ret m' os' =>
        ∃ gw r gw', args = [.ptr gw.gzBid 0] ∧
          ret = .int .i32 r ∧ (r.toInt = 0 ∨ r.toInt = 1) ∧
          GzWriteStepPost prog gEnv m0 os0 m os gw m' os' gw' ∧
          (∀ sz, readNatField? prog.tags m (.ptr gw.gzBid 0) "gz_state" "size" = some sz → sz > 0 →
            gw'.in? = gw.in?) ∧
          (r.toInt = 0 →
            ∀ sz', readNatField? prog.tags m' (.ptr gw'.gzBid 0) "gz_state" "size" = some sz' → sz' > 0 →
            ∃ nextIn' availIn',
              readField? prog.tags m' (.ptr gw'.gzBid 136) "z_stream_s" "next_in" = some nextIn' ∧
              readNatField? prog.tags m' (.ptr gw'.gzBid 136) "z_stream_s" "avail_in" = some availIn' ∧
              ((nextIn' = .null ∧ availIn' = 0) ∨
               (∃ o' ib', gw'.in? = some ib' ∧
                  nextIn' = .ptr ib' (Int64.ofNat o') ∧ o' + availIn' ≤ sz'))))
  gzvprintf_spec :
    CallWPTermSpec prog Zlib.Spec.zlibPointerConfig (Zlib.Spec.zlibExt userExt)
      Zlib.Gzwrite.gzwriteTU_fn_gzvprintf
      (fun m os args =>
        ∃ file fmtPtr, args = [file, fmtPtr, .vaList true] ∧
          (file = .null ∨
            (∃ gw : GzWitness, file = .ptr gw.gzBid 0 ∧
              LibGlobalsOk prog gEnv m0 os0 m os ∧ GzStateInv prog.tags gEnv m gw ∧
              HeapBlocksFreshFromLib m0 os0 gw.ownedList ∧
              SafeFmtString m fmtPtr ∧
              DisjointFrom fmtPtr (fun b =>
                b ∈ gw.ownedList ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b))))
      (fun m os args ret m' os' =>
        ∃ file fmtPtr r, args = [file, fmtPtr, .vaList true] ∧
          ret = .int .i32 r ∧
          ((file = .null ∧ r.toInt = -2 ∧ MemBlocksUnchanged m m' ∧ os' = os) ∨
           (∃ gw gw' : GzWitness, file = .ptr gw.gzBid 0 ∧
              LibGlobalsOk prog gEnv m0 os0 m' os' ∧
              os'.errnoBlk = os.errnoBlk ∧
              gw'.gzBid = gw.gzBid ∧ gw'.pathBid = gw.pathBid ∧
              GzStateInv prog.tags gEnv m' gw' ∧
              HeapBlocksFreshFromLib m0 os0 gw'.ownedList ∧
              (∀ b ∈ gw'.ownedList, b ∉ gw.ownedList → (m.blocks b).isNone = true) ∧
              FramePreserved m m' (fun b =>
                b ∈ gw.ownedList ∨ b ∈ gw'.ownedList ∨ b = os.errnoBlk ∨ os.strerrorBlk = some b ∨ os'.strerrorBlk = some b) ∧
              NoHeapLeak m m' (fun b => b ∈ gw'.ownedList))))

end Zlib.Proof
