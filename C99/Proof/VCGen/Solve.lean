import C99.Proof.VCGen.VCGen

/-!
# Functional VCGen Simplification & SMT-Style Leaf Tactics (`C99.Proof.VCGen.Solve`)

Provides constructive byte-slice lookup (`BufSlice.read_byte_fn`), `ROExt` framing
combinators, and Verus-style VC unfolding + SMT-style leaf tactics (`vc_unfold`,
`vc_leaf`). Strictly 100% zlib-agnostic.
-/

namespace C99.Proof.VCGen

open C99 C99.Sem C99.Proof

@[simp] theorem string_beq_eq_decide (a b : String) : (a == b) = decide (a = b) := by
  cases h : (a == b) <;> simp_all

/-! ## Constructive Byte-Slice Lookup (`BufSlice.read_byte_fn`) -/

/-- Byte value at offset `off + k` inside memory block `blk`, defaulting to `0` if uninitialized. -/
def blockByteAt (blk : Block) (off : Int64) (k : Nat) : BitVec 8 :=
  match blk.bytes (off.toInt.toNat + k) with
  | .byte b => b.toBitVec
  | _ => 0

/-- Deterministic pointer-arithmetic and byte-read elimination for valid `BufSlice` buffers. -/
theorem BufSlice.read_byte_fn {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {len : Nat} {el : CTy}
    (hb : BufSlice m b off len) (hel : el.unqual = .int .u8) :
    ∃ blk, m.blocks b = some blk ∧
      ∀ k : Nat, k < len →
        Sem.evalPtrAdd cfg tags m (.ptr b off) el k = some (.ptr b (Int64.ofInt (off.toInt + k))) ∧
        Sem.readVal tags m b (Int64.ofInt (off.toInt + k)) el = some (.int .u8 (blockByteAt blk off k)) := by
  rcases hb with ⟨blk, hblk, hin, hconcr⟩
  refine ⟨blk, hblk, fun k hk => ?_⟩
  obtain ⟨u, hadd, hrd⟩ :=
    BufSlice.read_byte_at (cfg := cfg) (tags := tags) ⟨blk, hblk, hin, hconcr⟩ hk hel
  refine ⟨hadd, ?_⟩
  obtain ⟨byte, hbyte⟩ := hconcr k hk
  obtain ⟨h0, hlen⟩ := inBounds_iff.mp hin
  have hlt63 : off.toInt + (k : Int) < 2 ^ 63 := by
    have := blk.sizeLt; rw [ptrDiffLimit_val] at this; omega
  have hin1 : Mem.inBounds blk (Int64.ofInt (off.toInt + k)) 1 = true :=
    inBounds_add hin (by omega)
  have hoff : (Int64.ofInt (off.toInt + k)).toInt.toNat = off.toInt.toNat + k := by
    rw [int64_ofInt_toInt (by omega) hlt63]; omega
  have hrbytes : m.readBytes b (Int64.ofInt (off.toInt + k)) 1 = some [.byte byte] := by
    rw [readBytes_of_bounds hblk hin1, hoff]
    apply congrArg some
    change [blk.bytes (off.toInt.toNat + k + 0)] = [.byte byte]
    rw [Nat.add_zero, hbyte]
  have hdec : Mem.decodeInt .u8 [.byte byte] = some byte.toBitVec := by
    have hgd : (([MemByte.byte byte].length == IntKind.u8.bytes) = true) := rfl
    simp only [Mem.decodeInt, Mem.decodeInt.go, hgd, guard_true,
      Nat.shiftLeft_zero, Nat.zero_or, bind, Option.bind, pure, Pure.pure]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, UInt8.toNat_toBitVec, IntKind.bits]
    exact Nat.mod_eq_of_lt byte.toBitVec.isLt
  have hrd_byte : Sem.readVal tags m b (Int64.ofInt (off.toInt + k)) el = some (.int .u8 byte.toBitVec) := by
    unfold Sem.readVal
    rw [← cty_unqual_idem el, hel]
    have hal1 : Mem.isAligned blk (Int64.ofInt (off.toInt + k)) 1 = true := by
      apply isAligned_one
      rw [int64_ofInt_toInt (by omega) hlt63]; omega
    change (do let blk ← m.blocks b
               let _ ← guard (Mem.isAligned blk (Int64.ofInt (off.toInt + (k : Int))) 1 = true)
               let bs ← m.readBytes b (Int64.ofInt (off.toInt + (k : Int))) 1
               let v ← Mem.decodeInt .u8 bs
               pure (Val.int .u8 v)) = _
    simp only [hblk, hal1, guard_true, hrbytes, hdec, bind, Option.bind, pure, Pure.pure]
  unfold blockByteAt
  rw [hbyte]
  exact hrd_byte

/-! ## Generic Read-Only / Stack Frame Helpers -/

theorem roExt_of_blocks_eq_next {m m' : Mem}
    (hle : m.nextBlock ≤ m'.nextBlock) (heq : ∀ b, m'.blocks b = m.blocks b) :
    ROExt m m' := by
  refine ⟨hle, fun b _ => heq b, fun b _ hge hbm' => ?_⟩
  have hf := m.fresh b hge
  rw [heq b, hf] at hbm'
  cases hbm'

theorem roExt_dropBlks_blocks_eq {m_clean m m_after : Mem} {bs : List BlockId}
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (heq : ∀ b, m_after.blocks b = m.blocks b) :
    ∀ b, (dropBlks m_after bs).blocks b = m_clean.blocks b := by
  intro b
  by_cases hbs : b ∈ bs
  · rw [dropBlks_blocks_mem _ _ hbs, habs b hbs]
  · rw [dropBlks_blocks_not_mem _ _ hbs, heq b, hagree b hbs]

theorem blocks_eq_dropBlks_id {m_clean m m_after : Mem} {bs : List BlockId}
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (heq : ∀ b, m_after.blocks b = m.blocks b) :
    (∀ b, (dropBlks m_after bs).blocks b = m_clean.blocks b) ∧
    (m.nextBlock ≤ m_after.nextBlock → m_clean.nextBlock ≤ m.nextBlock →
      m_clean.nextBlock ≤ (dropBlks m_after bs).nextBlock) :=
  ⟨roExt_dropBlks_blocks_eq habs hagree heq, fun h1 h2 => by
    rw [dropBlks_nextBlock]; exact Nat.le_trans h2 h1⟩

theorem post_stack_of_blocks_eq {m m' : Mem}
    (hle : m.nextBlock ≤ m'.nextBlock) (heq : ∀ b, m'.blocks b = m.blocks b) :
    m.nextBlock ≤ m'.nextBlock ∧ ∀ b blk, m.blocks b = some blk → blk.kind = .stack → m'.blocks b = some blk :=
  ⟨hle, fun b _ hb _ => (heq b).trans hb⟩

/-- Read-only state-preservation witness across a call (no heap/globals allocated/modified). -/
def MemUnchanged (m0 m1 : Mem) : Prop :=
  m0.nextBlock ≤ m1.nextBlock ∧ ∀ b, m1.blocks b = m0.blocks b

theorem MemUnchanged.refl (m : Mem) : MemUnchanged m m :=
  ⟨Nat.le_refl _, fun _ => rfl⟩

theorem MemUnchanged.trans {m0 m1 m2 : Mem} (h1 : MemUnchanged m0 m1) (h2 : MemUnchanged m1 m2) :
    MemUnchanged m0 m2 :=
  ⟨Nat.le_trans h1.1 h2.1, fun b => (h2.2 b).trans (h1.2 b)⟩

theorem MemUnchanged.roExt {m0 m1 : Mem} (h : MemUnchanged m0 m1) : ROExt m0 m1 :=
  roExt_of_blocks_eq_next h.1 h.2

theorem MemUnchanged.post_stack {m0 m1 : Mem} (h : MemUnchanged m0 m1) :
    m0.nextBlock ≤ m1.nextBlock ∧ ∀ b blk, m0.blocks b = some blk → blk.kind = .stack → m1.blocks b = some blk :=
  post_stack_of_blocks_eq h.1 h.2

theorem MemUnchanged.post_drop {m_clean m m_after : Mem} {bs : List BlockId}
    (hle : m_clean.nextBlock ≤ m.nextBlock)
    (habs : ∀ b ∈ bs, m_clean.blocks b = none)
    (hagree : ∀ b, b ∉ bs → m.blocks b = m_clean.blocks b)
    (h : MemUnchanged m m_after) :
    MemUnchanged m_clean (dropBlks m_after bs) :=
  ⟨by rw [dropBlks_nextBlock]; exact Nat.le_trans hle h.1,
   roExt_dropBlks_blocks_eq habs hagree h.2⟩

theorem BufSlice.read_byte_0 {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {len : Nat} {el : CTy} (hb : BufSlice m b off len) (hlen : 0 < len) (hel : el.unqual = .int .u8) :
    ∃ blk, m.blocks b = some blk ∧
      Sem.readVal tags m b off el = some (.int .u8 (blockByteAt blk off 0)) := by
  obtain ⟨blk, hblk, hfn⟩ := BufSlice.read_byte_fn (cfg := {}) (tags := tags) hb hel
  have h0 := (hfn 0 hlen).2
  have hoff : Int64.ofInt (off.toInt + (0 : Nat)) = off := by
    rw [Int.ofNat_zero, Int.add_zero, int64_ofInt_toInt_self]
  rw [hoff] at h0
  exact ⟨blk, hblk, h0⟩

theorem BufSlice.applyBinary_add_nat {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {len k : Nat} {pty el : CTy}
    (hb : BufSlice m b off len) (hk : k ≤ len)
    (hptr : pty.unqual = .ptr el) (hel : el.unqual = .int .u8) (hk31 : k < 2 ^ 31) :
    Sem.applyBinary cfg tags m .add (.ptr b off) pty (.int .i32 (BitVec.ofInt IntKind.i32.bits k)) (.int .i32) =
      some (.ptr b (Int64.ofInt (off.toInt + k)), pty.unqual) := by
  have hadv := (BufSlice.advance (cfg := cfg) (tags := tags) hb hk hel).1
  have hptr_b : pty.isPtr = true := by unfold CTy.isPtr; rw [hptr]
  have hi2 : Sem.valAsInt? (.int .i32 (BitVec.ofInt IntKind.i32.bits k)) = some (IntKind.i32, (k : Int)) := by
    change some (IntKind.i32, (BitVec.ofInt 32 (k : Int)).toInt) = some (IntKind.i32, (k : Int))
    congr 2
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  unfold Sem.applyBinary
  simp only [hptr_b, Bool.true_or, ↓reduceIte, hptr, hi2, hadv, Option.map_some]

theorem coerceCallArgs_singleton_scalar {m : Mem} {ty rty : CTy} {v : Val}
    (hv : ValScalarTyped ty v) :
    Sem.coerceCallArgs m [ty] false [(v, rty)] = some [v] := by
  unfold Sem.coerceCallArgs
  simp [hv.castVal_self]

/-! ## Kernel-Reducible Tag Env, Enum, and Type Layout Helpers -/

theorem collectTagEnv_append (a b : List TopItem) :
    collectTagEnv (a ++ b) = collectTagEnv a ++ collectTagEnv b := by
  simp [collectTagEnv, List.filterMap_append]

theorem list_lookup_append {α β : Type} [BEq α] (xs ys : List (α × β)) (k : α) :
    (xs ++ ys).lookup k = (xs.lookup k).or (ys.lookup k) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.cons_append, List.lookup]
    cases (k == a)
    · exact ih
    · rfl

def enumScanEval (name : String) : Int → List (String × Option Int) → Option Int
  | _, [] => none
  | nextVal, (k, v?) :: tl =>
    let v := v?.getD nextVal
    if k == name then some v else enumScanEval name (v + 1) tl

def enumConstEval : TypeEnv → String → Option Int
  | [], _ => none
  | (_, .enumDef items _) :: rest, name =>
    match enumScanEval name 0 items with
    | some v => some v
    | none => enumConstEval rest name
  | _ :: rest, name => enumConstEval rest name

private theorem enumConst?_scan_eq (rest : TypeEnv) (name : String) (n : Int)
    (items : List (String × Option Int)) (hrest : Sem.enumConst? rest name = enumConstEval rest name) :
    Sem.enumConst?.scan rest name n items =
      (enumScanEval name n items).or (enumConstEval rest name) := by
  induction items generalizing n with
  | nil => simp [Sem.enumConst?.scan, enumScanEval, hrest]
  | cons hd tl ih =>
    rcases hd with ⟨k, v?⟩
    simp only [Sem.enumConst?.scan, enumScanEval]
    by_cases hk : (k == name) = true
    · simp [hk]
    · have hkf : (k == name) = false := Bool.eq_false_iff.mpr hk
      simp only [hkf, Bool.false_eq_true, ↓reduceIte]
      exact ih _

theorem enumConst?_eq_eval (tags : TypeEnv) (name : String) :
    Sem.enumConst? tags name = enumConstEval tags name := by
  induction tags with
  | nil => simp [Sem.enumConst?, enumConstEval]
  | cons hd tl ih =>
    rcases hd with ⟨k, td⟩
    cases td with
    | structDef _ => simp only [Sem.enumConst?, enumConstEval, ih]
    | unionDef _ => simp only [Sem.enumConst?, enumConstEval, ih]
    | enumDef items u =>
      simp only [Sem.enumConst?, enumConstEval]
      rw [enumConst?_scan_eq tl name 0 items ih]
      cases enumScanEval name 0 items <;> rfl

theorem enumConst?_append (a b : TypeEnv) (name : String) :
    Sem.enumConst? (a ++ b) name = (Sem.enumConst? a name).or (Sem.enumConst? b name) := by
  induction a with
  | nil => simp [Sem.enumConst?]
  | cons hd tl ih =>
    rcases hd with ⟨k, td⟩
    cases td with
    | structDef _ => simp only [List.cons_append, Sem.enumConst?, ih]
    | unionDef _ => simp only [List.cons_append, Sem.enumConst?, ih]
    | enumDef items u =>
      simp only [List.cons_append, Sem.enumConst?]
      suffices ∀ n xs,
          Sem.enumConst?.scan (tl ++ b) name n xs =
          (Sem.enumConst?.scan tl name n xs).or (Sem.enumConst? b name) from this 0 items
      intro n xs
      induction xs generalizing n with
      | nil => simp [Sem.enumConst?.scan, ih]
      | cons x rest ihr =>
        rcases x with ⟨kn, v?⟩
        simp only [Sem.enumConst?.scan]
        by_cases hkn : (kn == name) = true
        · simp [hkn]
        · have hknf : (kn == name) = false := Bool.eq_false_iff.mpr hkn
          simp only [hknf, Bool.false_eq_true, ↓reduceIte]
          exact ihr _

def alignofFlatAux : Nat → CTy → Option Nat
  | 0, _ => none
  | _, .void => some 1
  | _, .int k => some k.align
  | n + 1, .const_ t => alignofFlatAux n t
  | _, .ptr _ => some 8
  | n + 1, .array elem _ => alignofFlatAux n elem
  | _, .enumTy _ _ => some 4
  | _, .fnPtr _ _ _ => some 8
  | _, .vaList => some 8
  | n + 1, .typedef _ t => alignofFlatAux n t
  | _, _ => none

def sizeofFlatAux : Nat → CTy → Option Nat
  | 0, _ => none
  | _, .void => some 0
  | _, .int k => some k.bytes
  | n + 1, .const_ t => sizeofFlatAux n t
  | _, .ptr _ => some 8
  | n + 1, .array elem (some cnt) => (sizeofFlatAux n elem).map (cnt * ·)
  | _, .array _ none => some 0
  | _, .enumTy _ _ => some 4
  | _, .fnPtr _ _ _ => some 8
  | _, .vaList => some 24
  | n + 1, .typedef _ t => sizeofFlatAux n t
  | _, _ => none

theorem alignofFlatAux_eq {f : Nat} {ty : CTy} {n : Nat}
    (h : alignofFlatAux f ty = some n) (env : TypeEnv) :
    ∀ fuel, alignofAux env fuel ty = n := by
  induction f generalizing ty n with
  | zero => cases h
  | succ f ih =>
    intro fuel
    cases ty with
    | void => cases h; cases fuel <;> simp [alignofAux]
    | int k => cases h; cases fuel <;> simp [alignofAux]
    | const_ t => cases fuel <;> simp [alignofAux, ih h]
    | ptr _ => cases h; cases fuel <;> simp [alignofAux]
    | array elem _ => cases fuel <;> simp [alignofAux, ih h]
    | enumTy _ _ => cases h; cases fuel <;> simp [alignofAux]
    | fnPtr _ _ _ => cases h; cases fuel <;> simp [alignofAux]
    | vaList => cases h; cases fuel <;> simp [alignofAux]
    | typedef _ t => cases fuel <;> simp [alignofAux, ih h]
    | anonStruct _ | anonUnion _ | structTy _ | unionTy _ => cases h

theorem sizeofFlatAux_eq {f : Nat} {ty : CTy} {n : Nat}
    (h : sizeofFlatAux f ty = some n) (env : TypeEnv) :
    ∀ fuel, sizeofAux env fuel ty = n := by
  induction f generalizing ty n with
  | zero => cases h
  | succ f ih =>
    intro fuel
    cases ty with
    | void => cases h; cases fuel <;> simp [sizeofAux]
    | int k => cases h; cases fuel <;> simp [sizeofAux]
    | const_ t => cases fuel <;> simp [sizeofAux, ih h]
    | ptr _ => cases h; cases fuel <;> simp [sizeofAux]
    | array elem cnt? =>
      cases cnt? with
      | none => cases h; cases fuel <;> simp [sizeofAux]
      | some cnt =>
        simp only [sizeofFlatAux] at h
        cases hs : sizeofFlatAux f elem with
        | none => rw [hs] at h; cases h
        | some s =>
          rw [hs] at h
          cases h
          cases fuel <;> simp [sizeofAux, ih hs]
    | enumTy _ _ => cases h; cases fuel <;> simp [sizeofAux]
    | fnPtr _ _ _ => cases h; cases fuel <;> simp [sizeofAux]
    | vaList => cases h; cases fuel <;> simp [sizeofAux]
    | typedef _ t => cases fuel <;> simp [sizeofAux, ih h]
    | anonStruct _ | anonUnion _ | structTy _ | unionTy _ => cases h

theorem alignofFlat_ty_eq {ty : CTy} {n : Nat} (h : alignofFlatAux 16 ty = some n) (env : TypeEnv) :
    alignofTy env ty = n := alignofFlatAux_eq h env _

theorem sizeofFlat_ty_eq {ty : CTy} {n : Nat} (h : sizeofFlatAux 16 ty = some n) (env : TypeEnv) :
    sizeofTy env ty = n := sizeofFlatAux_eq h env _

@[simp] theorem alignofAux_void (tags : TypeEnv) (f : Nat) : alignofAux tags f .void = 1 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_int (tags : TypeEnv) (f : Nat) (k : IntKind) :
    alignofAux tags f (.int k) = k.align := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_const (tags : TypeEnv) (f : Nat) (t : CTy) :
    alignofAux tags f (.const_ t) = alignofAux tags f t := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_ptr (tags : TypeEnv) (f : Nat) (t : CTy) :
    alignofAux tags f (.ptr t) = 8 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_array (tags : TypeEnv) (f : Nat) (el : CTy) (n? : Option Nat) :
    alignofAux tags f (.array el n?) = alignofAux tags f el := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_enumTy (tags : TypeEnv) (f : Nat) (tag : String) (isU : Bool) :
    alignofAux tags f (.enumTy tag isU) = 4 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_fnPtr (tags : TypeEnv) (f : Nat) (r : CTy) (ps : List CTy) (v : Bool) :
    alignofAux tags f (.fnPtr r ps v) = 8 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_vaList (tags : TypeEnv) (f : Nat) :
    alignofAux tags f .vaList = 8 := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_typedef (tags : TypeEnv) (f : Nat) (n : String) (t : CTy) :
    alignofAux tags f (.typedef n t) = alignofAux tags f t := by
  cases f <;> simp [alignofAux]
@[simp] theorem alignofAux_anonStruct (tags : TypeEnv) (f : Nat) (flds : List (String × CTy)) :
    alignofAux tags f (.anonStruct flds) = alignofFields tags f flds 1 := by
  cases f <;> simp [alignofAux]

@[simp] theorem sizeofAux_void (tags : TypeEnv) (f : Nat) : sizeofAux tags f .void = 0 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_int (tags : TypeEnv) (f : Nat) (k : IntKind) :
    sizeofAux tags f (.int k) = k.bytes := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_const (tags : TypeEnv) (f : Nat) (t : CTy) :
    sizeofAux tags f (.const_ t) = sizeofAux tags f t := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_ptr (tags : TypeEnv) (f : Nat) (t : CTy) :
    sizeofAux tags f (.ptr t) = 8 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_array_some (tags : TypeEnv) (f : Nat) (el : CTy) (n : Nat) :
    sizeofAux tags f (.array el (some n)) = n * sizeofAux tags f el := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_array_none (tags : TypeEnv) (f : Nat) (el : CTy) :
    sizeofAux tags f (.array el none) = 0 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_enumTy (tags : TypeEnv) (f : Nat) (tag : String) (isU : Bool) :
    sizeofAux tags f (.enumTy tag isU) = 4 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_fnPtr (tags : TypeEnv) (f : Nat) (r : CTy) (ps : List CTy) (v : Bool) :
    sizeofAux tags f (.fnPtr r ps v) = 8 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_vaList (tags : TypeEnv) (f : Nat) :
    sizeofAux tags f .vaList = 24 := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_typedef (tags : TypeEnv) (f : Nat) (n : String) (t : CTy) :
    sizeofAux tags f (.typedef n t) = sizeofAux tags f t := by
  cases f <;> simp [sizeofAux]
@[simp] theorem sizeofAux_anonStruct (tags : TypeEnv) (f : Nat) (flds : List (String × CTy)) :
    sizeofAux tags f (.anonStruct flds) = sizeofStructFields tags f 0 1 flds := by
  cases f <;> simp [sizeofAux]

theorem alignofFields_cons (tags : TypeEnv) (fuel : Nat) (nm : String) (fty : CTy)
    (rest : List (String × CTy)) (acc : Nat) :
    alignofFields tags fuel ((nm, fty) :: rest) acc =
      alignofFields tags fuel rest (max acc (alignofAux tags fuel fty)) := by
  cases fuel <;> simp [alignofFields]

theorem alignofFields_nil (tags : TypeEnv) (fuel : Nat) (acc : Nat) :
    alignofFields tags fuel [] acc = acc := by
  cases fuel <;> simp [alignofFields]

theorem sizeofStructFields_cons (tags : TypeEnv) (fuel sz al : Nat) (nm : String)
    (fty : CTy) (rest : List (String × CTy)) :
    sizeofStructFields tags fuel sz al ((nm, fty) :: rest) =
      let fa := max 1 (alignofAux tags fuel fty)
      let off := alignUp sz fa
      sizeofStructFields tags fuel (off + sizeofAux tags fuel fty) (max al fa) rest := by
  cases fuel <;> simp [sizeofStructFields]

theorem sizeofStructFields_nil (tags : TypeEnv) (fuel sz al : Nat) :
    sizeofStructFields tags fuel sz al [] = alignUp sz al := by
  cases fuel <;> simp [sizeofStructFields]

/-! ## Concrete-Head Equational Algebra & VC Tactics (`vc_unfold`, `vc_leaf`) -/

@[simp] theorem dite_true_prop {α : Sort _} {t : True → α} {e : ¬ True → α} :
    (dite True t e) = t trivial := rfl

@[simp] theorem val_int_ne_undef {k : IntKind} {bv : BitVec k.bits} :
    (Val.int k bv ≠ .undef) = True := by simp
@[simp] theorem val_ptr_ne_undef {b : BlockId} {off : Int64} :
    (Val.ptr b off ≠ .undef) = True := by simp
@[simp] theorem val_null_ne_undef :
    (Val.null ≠ .undef) = True := by simp
@[simp] theorem val_fnPtr_ne_undef {s : String} :
    (Val.fnPtr s ≠ .undef) = True := by simp

theorem vcBranch_int (k : IntKind) (bv : BitVec k.bits) (Kt Kf : Prop) :
    vcBranch (.int k bv) Kt Kf = ((bv ≠ 0 → Kt) ∧ (¬ (bv ≠ 0) → Kf)) := rfl
theorem vcBranch_ptr (b : BlockId) (off : Int64) (Kt Kf : Prop) :
    vcBranch (.ptr b off) Kt Kf = ((True → Kt) ∧ (¬ True → Kf)) := rfl
theorem vcBranch_null (Kt Kf : Prop) :
    vcBranch .null Kt Kf = ((False → Kt) ∧ (¬ False → Kf)) := rfl
theorem vcBranch_fnPtr (s : String) (Kt Kf : Prop) :
    vcBranch (.fnPtr s) Kt Kf = ((True → Kt) ∧ (¬ True → Kf)) := rfl

theorem vcBindVal_int (k : IntKind) (bv : BitVec k.bits) (K : Val → Prop) :
    vcBindVal (.int k bv) K = (∀ bv' : BitVec k.bits, bv' = bv → K (.int k bv')) := rfl
theorem vcBindVal_ptr (b : BlockId) (off : Int64) (K : Val → Prop) :
    vcBindVal (.ptr b off) K = (∀ off' : Int64, off' = off → K (.ptr b off')) := rfl
theorem vcBindVal_null (K : Val → Prop) : vcBindVal .null K = K .null := rfl
theorem vcBindVal_fnPtr (s : String) (K : Val → Prop) : vcBindVal (.fnPtr s) K = K (.fnPtr s) := rfl

def vcUnBody (op : UnOp) (lk : IntKind) (iv : Int) (isZero : Bool) : Prop × Val × CTy :=
  match op with
  | .plus => (lk.signed = true → lk.inRange iv = true, .int lk (BitVec.ofInt lk.bits iv), .int lk)
  | .neg => (lk.signed = true → lk.inRange (-iv) = true, .int lk (BitVec.ofInt lk.bits (-iv)), .int lk)
  | .bitNot => (True, .int lk (~~~BitVec.ofInt lk.bits iv), .int lk)
  | .logNot => (True, .int .i32 (if isZero then 1 else 0), .int .i32)

theorem vcUnary_int_mk (op : UnOp) (k : IntKind) (bv : BitVec k.bits) (K : Val → CTy → Prop) :
    vcUnary op (.int k bv) K =
      let u := vcUnBody op k.promote (valIntNum k bv) (bv == 0)
      u.1 ∧ K u.2.1 u.2.2 := by
  unfold vcUnary vcIntUnOp
  cases op <;> rfl

theorem vcUnary_ptr_logNot (b : BlockId) (off : Int64) (K : Val → CTy → Prop) :
    vcUnary .logNot (.ptr b off) K = K (.int .i32 0) (.int .i32) := rfl
theorem vcUnary_null_logNot (K : Val → CTy → Prop) :
    vcUnary .logNot .null K = K (.int .i32 1) (.int .i32) := rfl
theorem vcUnary_fnPtr_logNot (s : String) (K : Val → CTy → Prop) :
    vcUnary .logNot (.fnPtr s) K = K (.int .i32 0) (.int .i32) := rfl

theorem vcCast_int (m : Mem) (target : CTy) (k : IntKind) (bv : BitVec k.bits) (K : Val → CTy → Prop) :
    vcCast m target (.int k bv) K =
      match vcPureCast? target (.int k bv) with
      | some rv => K rv target
      | none => match Sem.castVal m target (.int k bv) with | some rv => K rv target | none => False := rfl

theorem vcCast_null (m : Mem) (target : CTy) (K : Val → CTy → Prop) :
    vcCast m target .null K =
      match vcPureCast? target .null with
      | some rv => K rv target
      | none => match Sem.castVal m target .null with | some rv => K rv target | none => False := rfl

theorem vcCast_ptr (m : Mem) (target : CTy) (b : BlockId) (off : Int64) (K : Val → CTy → Prop) :
    vcCast m target (.ptr b off) K =
      match vcPureCast? target (.ptr b off) with
      | some rv => K rv target
      | none => match Sem.castVal m target (.ptr b off) with | some rv => K rv target | none => False := rfl

theorem vcCast_fnPtr (m : Mem) (target : CTy) (s : String) (K : Val → CTy → Prop) :
    vcCast m target (.fnPtr s) K =
      match vcPureCast? target (.fnPtr s) with
      | some rv => K rv target
      | none => match Sem.castVal m target (.fnPtr s) with | some rv => K rv target | none => False := rfl

def vcArithBody (op : BinOp) (ck : IntKind) (i1 i2 : Int) : Prop × Val × CTy :=
  let c1 := BitVec.ofInt ck.bits i1
  let c2 := BitVec.ofInt ck.bits i2
  let n1 := valIntNum ck c1
  let n2 := valIntNum ck c2
  match op with
  | .add => (ck.signed = true → ck.inRange (n1 + n2) = true, .int ck (c1 + c2), .int ck)
  | .sub => (ck.signed = true → ck.inRange (n1 - n2) = true, .int ck (c1 - c2), .int ck)
  | .mul => (ck.signed = true → ck.inRange (n1 * n2) = true, .int ck (c1 * c2), .int ck)
  | .div => (n2 ≠ 0 ∧ (ck.signed = true → ck.inRange (Int.tdiv n1 n2) = true),
             .int ck (BitVec.ofInt ck.bits (Int.tdiv n1 n2)), .int ck)
  | .mod => (n2 ≠ 0 ∧ (ck.signed = true → ck.inRange (Int.tmod n1 n2) = true),
             .int ck (BitVec.ofInt ck.bits (Int.tmod n1 n2)), .int ck)
  | .bitAnd => (True, .int ck (c1 &&& c2), .int ck)
  | .bitOr => (True, .int ck (c1 ||| c2), .int ck)
  | .bitXor => (True, .int ck (c1 ^^^ c2), .int ck)
  | .eq | .ne | .lt | .le | .gt | .ge =>
    (True, .int .i32 (if Sem.cmpOrd op n1 n2 then 1 else 0), .int .i32)
  | .shl | .shr => (True, .int ck c1, .int ck)

def vcShiftBody (isShl : Bool) (lk : IntKind) (i1 i2 : Int) : Prop × Val × CTy :=
  let sh := i2.toNat
  if lk.signed then
    let raw := if isShl then i1 * (2 ^ sh : Int) else i1 / (2 ^ sh : Int)
    (0 ≤ i2 ∧ i2 < (lk.bits : Int) ∧ 0 ≤ i1 ∧ lk.inRange raw = true,
     .int lk (BitVec.ofInt lk.bits raw), .int lk)
  else
    (0 ≤ i2 ∧ i2 < (lk.bits : Int),
     .int lk (if isShl then BitVec.ofInt lk.bits i1 <<< sh else BitVec.ofInt lk.bits i1 >>> sh), .int lk)

theorem vcUnBody_i32 (op : UnOp) (iv : Int) (z : Bool) :
    vcUnBody op .i32 iv z =
      match op with
      | .plus => (IntKind.i32.inRange iv = true, .int .i32 (BitVec.ofInt IntKind.i32.bits iv), .int .i32)
      | .neg => (IntKind.i32.inRange (-iv) = true, .int .i32 (BitVec.ofInt IntKind.i32.bits (-iv)), .int .i32)
      | .bitNot => (True, .int .i32 (~~~BitVec.ofInt IntKind.i32.bits iv), .int .i32)
      | .logNot => (True, .int .i32 (if z then 1 else 0), .int .i32) := by
  cases op <;> simp [vcUnBody, IntKind.signed]

theorem vcUnBody_u32 (op : UnOp) (iv : Int) (z : Bool) :
    vcUnBody op .u32 iv z =
      match op with
      | .plus => (True, .int .u32 (BitVec.ofInt IntKind.u32.bits iv), .int .u32)
      | .neg => (True, .int .u32 (BitVec.ofInt IntKind.u32.bits (-iv)), .int .u32)
      | .bitNot => (True, .int .u32 (~~~BitVec.ofInt IntKind.u32.bits iv), .int .u32)
      | .logNot => (True, .int .i32 (if z then 1 else 0), .int .i32) := by
  cases op <;> simp [vcUnBody, IntKind.signed]

theorem vcUnBody_i64 (op : UnOp) (iv : Int) (z : Bool) :
    vcUnBody op .i64 iv z =
      match op with
      | .plus => (IntKind.i64.inRange iv = true, .int .i64 (BitVec.ofInt IntKind.i64.bits iv), .int .i64)
      | .neg => (IntKind.i64.inRange (-iv) = true, .int .i64 (BitVec.ofInt IntKind.i64.bits (-iv)), .int .i64)
      | .bitNot => (True, .int .i64 (~~~BitVec.ofInt IntKind.i64.bits iv), .int .i64)
      | .logNot => (True, .int .i32 (if z then 1 else 0), .int .i32) := by
  cases op <;> simp [vcUnBody, IntKind.signed]

theorem vcUnBody_u64 (op : UnOp) (iv : Int) (z : Bool) :
    vcUnBody op .u64 iv z =
      match op with
      | .plus => (True, .int .u64 (BitVec.ofInt IntKind.u64.bits iv), .int .u64)
      | .neg => (True, .int .u64 (BitVec.ofInt IntKind.u64.bits (-iv)), .int .u64)
      | .bitNot => (True, .int .u64 (~~~BitVec.ofInt IntKind.u64.bits iv), .int .u64)
      | .logNot => (True, .int .i32 (if z then 1 else 0), .int .i32) := by
  cases op <;> simp [vcUnBody, IntKind.signed]

theorem vcArithBody_i32 (op : BinOp) (i1 i2 : Int) :
    vcArithBody op .i32 i1 i2 =
      (let c1 := BitVec.ofInt IntKind.i32.bits i1
       let c2 := BitVec.ofInt IntKind.i32.bits i2
       let n1 := c1.toInt
       let n2 := c2.toInt
       match op with
       | .add => (IntKind.i32.inRange (n1 + n2) = true, .int .i32 (c1 + c2), .int .i32)
       | .sub => (IntKind.i32.inRange (n1 - n2) = true, .int .i32 (c1 - c2), .int .i32)
       | .mul => (IntKind.i32.inRange (n1 * n2) = true, .int .i32 (c1 * c2), .int .i32)
       | .div => (n2 ≠ 0 ∧ IntKind.i32.inRange (Int.tdiv n1 n2) = true,
                  .int .i32 (BitVec.ofInt IntKind.i32.bits (Int.tdiv n1 n2)), .int .i32)
       | .mod => (n2 ≠ 0 ∧ IntKind.i32.inRange (Int.tmod n1 n2) = true,
                  .int .i32 (BitVec.ofInt IntKind.i32.bits (Int.tmod n1 n2)), .int .i32)
       | .bitAnd => (True, .int .i32 (c1 &&& c2), .int .i32)
       | .bitOr => (True, .int .i32 (c1 ||| c2), .int .i32)
       | .bitXor => (True, .int .i32 (c1 ^^^ c2), .int .i32)
       | .eq | .ne | .lt | .le | .gt | .ge =>
         (True, .int .i32 (if Sem.cmpOrd op n1 n2 then 1 else 0), .int .i32)
       | .shl | .shr => (True, .int .i32 c1, .int .i32)) := by
  cases op <;> simp [vcArithBody, valIntNum, IntKind.signed]

theorem vcArithBody_u32 (op : BinOp) (i1 i2 : Int) :
    vcArithBody op .u32 i1 i2 =
      (let c1 := BitVec.ofInt IntKind.u32.bits i1
       let c2 := BitVec.ofInt IntKind.u32.bits i2
       let n1 : Int := c1.toNat
       let n2 : Int := c2.toNat
       match op with
       | .add => (True, .int .u32 (c1 + c2), .int .u32)
       | .sub => (True, .int .u32 (c1 - c2), .int .u32)
       | .mul => (True, .int .u32 (c1 * c2), .int .u32)
       | .div => (n2 ≠ 0, .int .u32 (BitVec.ofInt IntKind.u32.bits (Int.tdiv n1 n2)), .int .u32)
       | .mod => (n2 ≠ 0, .int .u32 (BitVec.ofInt IntKind.u32.bits (Int.tmod n1 n2)), .int .u32)
       | .bitAnd => (True, .int .u32 (c1 &&& c2), .int .u32)
       | .bitOr => (True, .int .u32 (c1 ||| c2), .int .u32)
       | .bitXor => (True, .int .u32 (c1 ^^^ c2), .int .u32)
       | .eq | .ne | .lt | .le | .gt | .ge =>
         (True, .int .i32 (if Sem.cmpOrd op n1 n2 then 1 else 0), .int .i32)
       | .shl | .shr => (True, .int .u32 c1, .int .u32)) := by
  cases op <;> simp [vcArithBody, valIntNum, IntKind.signed]

theorem vcArithBody_i64 (op : BinOp) (i1 i2 : Int) :
    vcArithBody op .i64 i1 i2 =
      (let c1 := BitVec.ofInt IntKind.i64.bits i1
       let c2 := BitVec.ofInt IntKind.i64.bits i2
       let n1 := c1.toInt
       let n2 := c2.toInt
       match op with
       | .add => (IntKind.i64.inRange (n1 + n2) = true, .int .i64 (c1 + c2), .int .i64)
       | .sub => (IntKind.i64.inRange (n1 - n2) = true, .int .i64 (c1 - c2), .int .i64)
       | .mul => (IntKind.i64.inRange (n1 * n2) = true, .int .i64 (c1 * c2), .int .i64)
       | .div => (n2 ≠ 0 ∧ IntKind.i64.inRange (Int.tdiv n1 n2) = true,
                  .int .i64 (BitVec.ofInt IntKind.i64.bits (Int.tdiv n1 n2)), .int .i64)
       | .mod => (n2 ≠ 0 ∧ IntKind.i64.inRange (Int.tmod n1 n2) = true,
                  .int .i64 (BitVec.ofInt IntKind.i64.bits (Int.tmod n1 n2)), .int .i64)
       | .bitAnd => (True, .int .i64 (c1 &&& c2), .int .i64)
       | .bitOr => (True, .int .i64 (c1 ||| c2), .int .i64)
       | .bitXor => (True, .int .i64 (c1 ^^^ c2), .int .i64)
       | .eq | .ne | .lt | .le | .gt | .ge =>
         (True, .int .i32 (if Sem.cmpOrd op n1 n2 then 1 else 0), .int .i32)
       | .shl | .shr => (True, .int .i64 c1, .int .i64)) := by
  cases op <;> simp [vcArithBody, valIntNum, IntKind.signed]

theorem vcArithBody_u64 (op : BinOp) (i1 i2 : Int) :
    vcArithBody op .u64 i1 i2 =
      (let c1 := BitVec.ofInt IntKind.u64.bits i1
       let c2 := BitVec.ofInt IntKind.u64.bits i2
       let n1 : Int := c1.toNat
       let n2 : Int := c2.toNat
       match op with
       | .add => (True, .int .u64 (c1 + c2), .int .u64)
       | .sub => (True, .int .u64 (c1 - c2), .int .u64)
       | .mul => (True, .int .u64 (c1 * c2), .int .u64)
       | .div => (n2 ≠ 0, .int .u64 (BitVec.ofInt IntKind.u64.bits (Int.tdiv n1 n2)), .int .u64)
       | .mod => (n2 ≠ 0, .int .u64 (BitVec.ofInt IntKind.u64.bits (Int.tmod n1 n2)), .int .u64)
       | .bitAnd => (True, .int .u64 (c1 &&& c2), .int .u64)
       | .bitOr => (True, .int .u64 (c1 ||| c2), .int .u64)
       | .bitXor => (True, .int .u64 (c1 ^^^ c2), .int .u64)
       | .eq | .ne | .lt | .le | .gt | .ge =>
         (True, .int .i32 (if Sem.cmpOrd op n1 n2 then 1 else 0), .int .i32)
       | .shl | .shr => (True, .int .u64 c1, .int .u64)) := by
  cases op <;> simp [vcArithBody, valIntNum, IntKind.signed]

theorem vcShiftBody_i32 (isShl : Bool) (i1 i2 : Int) :
    vcShiftBody isShl .i32 i1 i2 =
      (let raw := if isShl then i1 * (2 ^ i2.toNat : Int) else i1 / (2 ^ i2.toNat : Int)
       (0 ≤ i2 ∧ i2 < 32 ∧ 0 ≤ i1 ∧ IntKind.i32.inRange raw = true,
        .int .i32 (BitVec.ofInt IntKind.i32.bits raw), .int .i32)) := rfl

theorem vcShiftBody_u32 (isShl : Bool) (i1 i2 : Int) :
    vcShiftBody isShl .u32 i1 i2 =
      (0 ≤ i2 ∧ i2 < 32,
       .int .u32 (if isShl then BitVec.ofInt IntKind.u32.bits i1 <<< i2.toNat
                  else BitVec.ofInt IntKind.u32.bits i1 >>> i2.toNat), .int .u32) := rfl

theorem vcShiftBody_i64 (isShl : Bool) (i1 i2 : Int) :
    vcShiftBody isShl .i64 i1 i2 =
      (let raw := if isShl then i1 * (2 ^ i2.toNat : Int) else i1 / (2 ^ i2.toNat : Int)
       (0 ≤ i2 ∧ i2 < 64 ∧ 0 ≤ i1 ∧ IntKind.i64.inRange raw = true,
        .int .i64 (BitVec.ofInt IntKind.i64.bits raw), .int .i64)) := rfl

theorem vcShiftBody_u64 (isShl : Bool) (i1 i2 : Int) :
    vcShiftBody isShl .u64 i1 i2 =
      (0 ≤ i2 ∧ i2 < 64,
       .int .u64 (if isShl then BitVec.ofInt IntKind.u64.bits i1 <<< i2.toNat
                  else BitVec.ofInt IntKind.u64.bits i1 >>> i2.toNat), .int .u64) := rfl

theorem bv_toInt_zero (k : IntKind) : (0 : BitVec k.bits).toInt = 0 := by simp

theorem bv_ofInt_valIntNum (k : IntKind) (v : BitVec k.bits) :
    BitVec.ofInt k.bits (valIntNum k v) = v := by
  cases hs : k.signed <;> simp [valIntNum, hs]

theorem intKind_beq_eq_decide (a b : IntKind) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

def vcBinaryIntCont (op : BinOp) (k1 : IntKind) (bv1 : BitVec k1.bits)
    (k2 : IntKind) (bv2 : BitVec k2.bits) (K : Val → CTy → Prop) (fallback : Prop) :
    Option IntKind → Option IntKind → Prop
  | some k1', some k2' =>
    if k1 == k1' && k2 == k2' then
      let b :=
        if op == .shl || op == .shr then
          vcShiftBody (op == .shl) k1.promote (valIntNum k1 bv1) (valIntNum k2 bv2)
        else
          vcArithBody op (IntKind.usualArith k1 k2) (valIntNum k1 bv1) (valIntNum k2 bv2)
      b.1 ∧ K b.2.1 b.2.2
    else False
  | _, _ => fallback

theorem vcBinaryIntCont_some (op k1 bv1 k2 bv2 K fallback k1' k2') :
    vcBinaryIntCont op k1 bv1 k2 bv2 K fallback (some k1') (some k2') =
      (if k1 == k1' && k2 == k2' then
        let b :=
          if op == .shl || op == .shr then
            vcShiftBody (op == .shl) k1.promote (valIntNum k1 bv1) (valIntNum k2 bv2)
          else
            vcArithBody op (IntKind.usualArith k1 k2) (valIntNum k1 bv1) (valIntNum k2 bv2)
        b.1 ∧ K b.2.1 b.2.2
      else False) := rfl

theorem vcBinary_int_mk {cfg tags m op k1 k2} {bv1 : BitVec k1.bits} {t1 : CTy}
    {bv2 : BitVec k2.bits} {t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m op (.int k1 bv1) t1 (.int k2 bv2) t2 K =
      vcBinaryIntCont op k1 bv1 k2 bv2 K
        (if (t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) && (op == .eq || op == .ne) then
          match vcPtrEqBool? (.int k1 bv1) (.int k2 bv2) with
          | some eq =>
            K (.int .i32 (if (if op == .eq then eq else !eq) then 1 else 0)) (.int .i32)
          | none => False
        else
          match Sem.applyBinary cfg tags m op (.int k1 bv1) t1 (.int k2 bv2) t2 with
          | some (rv, rt) => K rv rt
          | none => False)
        t1.intKind? t2.intKind? := by
  unfold vcBinary vcBinaryIntCont
  cases t1.intKind? with
  | none => rfl
  | some k1' =>
    cases t2.intKind? with
    | none => rfl
    | some k2' =>
      dsimp only
      by_cases hkk : k1 = k1' ∧ k2 = k2'
      · rcases hkk with ⟨rfl, rfl⟩
        have hkb : (k1 == k1 && k2 == k2) = true := by simp
        simp only [hkb, ↓reduceIte]
        cases op <;> (unfold vcIntBinOp vcShiftBody vcArithBody; rfl)
      · have hkf : (k1 == k1' && k2 == k2') = false := by
          cases k1 <;> cases k1' <;> cases k2 <;> cases k2' <;>
            simp_all [intKind_beq_eq_decide]
        simp only [hkk, ↓reduceDIte, hkf, Bool.false_eq_true, ↓reduceIte]

private theorem vcBinary_ptrCmp_aux {cfg tags m} (op : BinOp) (v1 v2 : Val)
    {t1 t2 : CTy} {K : Val → CTy → Prop} {res : Bool}
    (hv1 : match v1 with | .ptr _ _ | .null | .fnPtr _ => True | _ => False)
    (hop : (op == .eq || op == .ne) = true)
    (hptr : vcPtrEqBool? v1 v2 = some res) :
    vcBinary cfg tags m op v1 t1 v2 t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then
        K (.int .i32 (if (if op == .eq then res else !res) then 1 else 0)) (.int .i32)
      else False := by
  have hint : Sem.evalIntBinary op v1 v2 = none := by
    cases v1 with
    | ptr _ _ | null | fnPtr _ => rfl
    | _ => simp at hv1
  have hsplit : vcBinary cfg tags m op v1 t1 v2 t2 K =
      (if (t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) && (op == .eq || op == .ne) then
        match vcPtrEqBool? v1 v2 with
        | some eq => K (.int .i32 (if (if op == .eq then eq else !eq) then 1 else 0)) (.int .i32)
        | none => False
      else
        match Sem.applyBinary cfg tags m op v1 t1 v2 t2 with
        | some (rv, rt) => K rv rt
        | none => False) := by
    unfold vcBinary
    cases v1 with
    | ptr _ _ | null | fnPtr _ =>
      cases v2 <;> cases t1.intKind? <;> cases t2.intKind? <;> rfl
    | _ => simp at hv1
  rw [hsplit]
  by_cases hpt : (t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) = true
  · simp only [hpt, hop, Bool.and_self, ↓reduceIte, hptr]
  · have hptf : (t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2) = false := Bool.eq_false_iff.mpr hpt
    have h1f : t1.isPtr = false := by revert hptf; cases t1.isPtr <;> simp
    have h2f : t2.isPtr = false := by revert hptf; cases t2.isPtr <;> simp
    have hf1 : isFnCTy t1 = false := by revert hptf; cases isFnCTy t1 <;> simp
    have hf2 : isFnCTy t2 = false := by revert hptf; cases isFnCTy t2 <;> simp
    dsimp only [isFnCTy] at hf1 hf2
    simp only [hptf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    unfold Sem.applyBinary
    simp only [h1f, h2f, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    cases hq1 : t1.unqual <;>
      first | (rw [hq1] at hf1; contradiction) |
        (cases hq2 : t2.unqual <;> first | (rw [hq2] at hf2; contradiction) |
          (dsimp only; simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, hint]))

theorem vcBinary_ptr_ptr_eq {cfg tags m b1 o1 b2 o2} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq (.ptr b1 o1) t1 (.ptr b2 o2) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then
        K (.int .i32 (if (b1 == b2 && o1 == o2) then 1 else 0)) (.int .i32)
      else False :=
  vcBinary_ptrCmp_aux .eq (.ptr b1 o1) (.ptr b2 o2) trivial rfl rfl

theorem vcBinary_ptr_ptr_ne {cfg tags m b1 o1 b2 o2} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne (.ptr b1 o1) t1 (.ptr b2 o2) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then
        K (.int .i32 (if !(b1 == b2 && o1 == o2) then 1 else 0)) (.int .i32)
      else False :=
  vcBinary_ptrCmp_aux .ne (.ptr b1 o1) (.ptr b2 o2) trivial rfl rfl

theorem vcBinary_ptr_null_eq {cfg tags m b1 o1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq (.ptr b1 o1) t1 .null t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq (.ptr b1 o1) .null trivial rfl rfl

theorem vcBinary_ptr_null_ne {cfg tags m b1 o1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne (.ptr b1 o1) t1 .null t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne (.ptr b1 o1) .null trivial rfl rfl

theorem vcBinary_null_ptr_eq {cfg tags m b2 o2} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq .null t1 (.ptr b2 o2) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq .null (.ptr b2 o2) trivial rfl rfl

theorem vcBinary_null_ptr_ne {cfg tags m b2 o2} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne .null t1 (.ptr b2 o2) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne .null (.ptr b2 o2) trivial rfl rfl

theorem vcBinary_fnPtr_null_eq {cfg tags m s1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq (.fnPtr s1) t1 .null t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq (.fnPtr s1) .null trivial rfl rfl

theorem vcBinary_fnPtr_null_ne {cfg tags m s1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne (.fnPtr s1) t1 .null t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne (.fnPtr s1) .null trivial rfl rfl

theorem vcBinary_null_null_eq {cfg tags m} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq .null t1 .null t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq .null .null trivial rfl rfl

theorem vcBinary_null_null_ne {cfg tags m} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne .null t1 .null t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne .null .null trivial rfl rfl

theorem bv_ofInt_zero (k : IntKind) : BitVec.ofInt k.bits 0 = 0 := by simp
theorem bv_toNat_zero (k : IntKind) : (0 : BitVec k.bits).toNat = 0 := by simp

theorem vcBinary_ptr_zero_eq {cfg tags m b1 o1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq (.ptr b1 o1) t1 (.int .i32 0) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq (.ptr b1 o1) (.int .i32 0) trivial rfl rfl

theorem vcBinary_ptr_zero_ne {cfg tags m b1 o1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne (.ptr b1 o1) t1 (.int .i32 0) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne (.ptr b1 o1) (.int .i32 0) trivial rfl rfl

theorem vcBinary_null_zero_eq {cfg tags m} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq .null t1 (.int .i32 0) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq .null (.int .i32 0) trivial rfl rfl

theorem vcBinary_null_zero_ne {cfg tags m} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne .null t1 (.int .i32 0) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne .null (.int .i32 0) trivial rfl rfl

theorem vcBinary_fnPtr_zero_eq {cfg tags m s1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .eq (.fnPtr s1) t1 (.int .i32 0) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 0) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .eq (.fnPtr s1) (.int .i32 0) trivial rfl rfl

theorem vcBinary_fnPtr_zero_ne {cfg tags m s1} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .ne (.fnPtr s1) t1 (.int .i32 0) t2 K =
      if t1.isPtr || t2.isPtr || isFnCTy t1 || isFnCTy t2 then K (.int .i32 1) (.int .i32) else False :=
  vcBinary_ptrCmp_aux .ne (.fnPtr s1) (.int .i32 0) trivial rfl rfl

theorem vcBinary_ptr_add_int {cfg tags m b o k2 bv2} {t1 t2 : CTy} {K : Val → CTy → Prop} :
    vcBinary cfg tags m .add (.ptr b o) t1 (.int k2 bv2) t2 K =
      match Sem.applyBinary cfg tags m .add (.ptr b o) t1 (.int k2 bv2) t2 with
      | some (rv, rt) => K rv rt
      | none => False := by
  unfold vcBinary
  have hne : (BinOp.add == .eq || BinOp.add == .ne) = false := rfl
  cases t1.intKind? <;> cases t2.intKind? <;> simp only [hne, Bool.and_false] <;> rfl

theorem vcFn_nonVoid {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt} {pre post}
    {ty : CTy} (hva : fn.variadic = false) (hret : fn.retTy = ty) (hvoid : ty.isVoid = false) :
    vcFn prog cfg specs fn annBody pre post =
      ∀ m os args,
        (∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2) →
        args.length = fn.params.length →
        pre m os args →
        vcStmt prog cfg specs (prog.fnStatics fn.name ++ prog.globalEnv) ty
          { normal := fun s' => post m os args .undef s'.exitFn s'.os
            onBreak := fun _ => False
            onContinue := fun _ => False
            onReturn := fun rv m' os' => post m os args rv m' os'
            onGoto := fun _ _ => False }
          { regs := (fn.params.zip args).reverse.map (fun (p, v) => (p.name, v, p.ty))
            stack := []
            mem := m
            os := os }
          annBody := by
  unfold vcFn fnEntryPost fnEntryState
  rw [hva, hret]
  simp only [hvoid, Bool.false_eq_true, ↓reduceIte]
  apply propext
  constructor
  · intro h m os args hvt hlen hpre
    have hvt' : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2 := by
      rwa [List.take_of_length_le (Nat.le_of_eq hlen)]
    have hvc := h m os args hvt' hlen hpre
    rwa [List.take_of_length_le (Nat.le_of_eq hlen)] at hvc
  · intro h m os args hvt hlen hpre
    rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hvt ⊢
    exact h m os args hvt hlen hpre

theorem vcFn_void {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt} {pre post}
    (hva : fn.variadic = false) (hret : fn.retTy = .void) :
    vcFn prog cfg specs fn annBody pre post =
      ∀ m os args,
        (∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2) →
        args.length = fn.params.length →
        pre m os args →
        vcStmt prog cfg specs (prog.fnStatics fn.name ++ prog.globalEnv) .void
          { normal := fun s' => post m os args .void s'.exitFn s'.os
            onBreak := fun _ => False
            onContinue := fun _ => False
            onReturn := fun rv m' os' => post m os args rv m' os'
            onGoto := fun _ _ => False }
          { regs := (fn.params.zip args).reverse.map (fun (p, v) => (p.name, v, p.ty))
            stack := []
            mem := m
            os := os }
          annBody := by
  unfold vcFn fnEntryPost fnEntryState
  rw [hva, hret]
  simp only [CTy.isVoid, CTy.unqual, ↓reduceIte]
  apply propext
  constructor
  · intro h m os args hvt hlen hpre
    have hvt' : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2 := by
      rwa [List.take_of_length_le (Nat.le_of_eq hlen)]
    have hvc := h m os args hvt' hlen hpre
    rwa [List.take_of_length_le (Nat.le_of_eq hlen)] at hvc
  · intro h m os args hvt hlen hpre
    rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hvt ⊢
    exact h m os args hvt hlen hpre

theorem vcFnSafe_nonVoid {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt} {pre post}
    {ty : CTy} (hva : fn.variadic = false) (hret : fn.retTy = ty) (hvoid : ty.isVoid = false) :
    vcFnSafe prog cfg specs fn annBody pre post =
      ∀ m os args,
        (∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2) →
        args.length = fn.params.length →
        pre m os args →
        let kp : ContPost :=
          { normal := fun s' => post m os args .undef s'.exitFn s'.os
            onBreak := fun _ => False
            onContinue := fun _ => False
            onReturn := fun rv m' os' => post m os args rv m' os'
            onGoto := fun _ _ => False }
        let s0 : SymState :=
          { regs := (fn.params.zip args).reverse.map (fun (p, v) => (p.name, v, p.ty))
            stack := []
            mem := m
            os := os }
        (os.readBudget.isSome = false →
          vcStmtSafe prog cfg specs (prog.fnStatics fn.name ++ prog.globalEnv) ty kp s0 annBody) ∧
        (os.readBudget.isSome = true →
          vcStmt prog cfg specs.toTermSpecs (prog.fnStatics fn.name ++ prog.globalEnv) ty kp s0 annBody) := by
  unfold vcFnSafe vcFnSafeSplit fnEntryPost fnEntryState
  rw [hva, hret]
  simp only [hvoid, Bool.false_eq_true, ↓reduceIte]
  apply propext
  constructor
  · intro h m os args hvt hlen hpre
    have hvt' : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2 := by
      rwa [List.take_of_length_le (Nat.le_of_eq hlen)]
    have hvc := h m os args hvt' hlen hpre
    rwa [List.take_of_length_le (Nat.le_of_eq hlen)] at hvc
  · intro h m os args hvt hlen hpre
    rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hvt ⊢
    exact h m os args hvt hlen hpre

theorem vcFnSafe_void {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {fn : FnDef} {annBody : AnnStmt} {pre post}
    (hva : fn.variadic = false) (hret : fn.retTy = .void) :
    vcFnSafe prog cfg specs fn annBody pre post =
      ∀ m os args,
        (∀ pv ∈ fn.params.zip args, ValScalarTyped pv.1.ty pv.2) →
        args.length = fn.params.length →
        pre m os args →
        let kp : ContPost :=
          { normal := fun s' => post m os args .void s'.exitFn s'.os
            onBreak := fun _ => False
            onContinue := fun _ => False
            onReturn := fun rv m' os' => post m os args rv m' os'
            onGoto := fun _ _ => False }
        let s0 : SymState :=
          { regs := (fn.params.zip args).reverse.map (fun (p, v) => (p.name, v, p.ty))
            stack := []
            mem := m
            os := os }
        (os.readBudget.isSome = false →
          vcStmtSafe prog cfg specs (prog.fnStatics fn.name ++ prog.globalEnv) .void kp s0 annBody) ∧
        (os.readBudget.isSome = true →
          vcStmt prog cfg specs.toTermSpecs (prog.fnStatics fn.name ++ prog.globalEnv) .void kp s0 annBody) := by
  unfold vcFnSafe vcFnSafeSplit fnEntryPost fnEntryState
  rw [hva, hret]
  simp only [CTy.isVoid, CTy.unqual, ↓reduceIte]
  apply propext
  constructor
  · intro h m os args hvt hlen hpre
    have hvt' : ∀ pv ∈ fn.params.zip (args.take fn.params.length), ValScalarTyped pv.1.ty pv.2 := by
      rwa [List.take_of_length_le (Nat.le_of_eq hlen)]
    have hvc := h m os args hvt' hlen hpre
    rwa [List.take_of_length_le (Nat.le_of_eq hlen)] at hvc
  · intro h m os args hvt hlen hpre
    rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hvt ⊢
    exact h m os args hvt hlen hpre

theorem binOp_beq_shl (op : BinOp) :
    (op == BinOp.shl) = match op with | .shl => true | _ => false := by cases op <;> rfl
theorem binOp_beq_shr (op : BinOp) :
    (op == BinOp.shr) = match op with | .shr => true | _ => false := by cases op <;> rfl
theorem binOp_beq_eq (op : BinOp) :
    (op == BinOp.eq) = match op with | .eq => true | _ => false := by cases op <;> rfl
theorem binOp_beq_ne (op : BinOp) :
    (op == BinOp.ne) = match op with | .ne => true | _ => false := by cases op <;> rfl

theorem bv64_ofNat_toNat (n : Nat) (h : n < 18446744073709551616) :
    (BitVec.ofNat IntKind.u64.bits n).toNat = n := by
  change n % 2 ^ 64 = n
  exact Nat.mod_eq_of_lt h

theorem regEnv_set_nil (x : String) (v : Val) (ty : CTy) :
    RegEnv.set [] x v ty = [] := rfl

theorem list_lookup_nil {α : Type _} (x : String) :
    ([] : List (String × α)).lookup x = none := rfl

theorem list_lookup_cons {α : Type _} (k : String) (v : α) (rest : List (String × α)) (x : String) :
    ((k, v) :: rest).lookup x = if x == k then some v else rest.lookup x := by
  cases h : (x == k) <;> simp [List.lookup, h]

theorem ofIntCast_valIntNum (k : IntKind) (v : BitVec k.bits) :
    Sem.ofIntCast k (valIntNum k v) = .int k v := by
  unfold Sem.ofIntCast
  rw [bv_ofInt_valIntNum]

theorem symState_regs_mk (r : RegEnv) (stk : Env) (m : Mem) (os : OSState) :
    ({ regs := r, stack := stk, mem := m, os := os } : SymState).regs = r := rfl
theorem symState_stack_mk (r : RegEnv) (stk : Env) (m : Mem) (os : OSState) :
    ({ regs := r, stack := stk, mem := m, os := os } : SymState).stack = stk := rfl
theorem symState_mem_mk (r : RegEnv) (stk : Env) (m : Mem) (os : OSState) :
    ({ regs := r, stack := stk, mem := m, os := os } : SymState).mem = m := rfl
theorem symState_os_mk (r : RegEnv) (stk : Env) (m : Mem) (os : OSState) :
    ({ regs := r, stack := stk, mem := m, os := os } : SymState).os = os := rfl
theorem symState_exitBlock_mk (r : RegEnv) (stk : Env) (m : Mem) (os : OSState) (reg0 stk0 : Nat) :
    ({ regs := r, stack := stk, mem := m, os := os } : SymState).exitBlock reg0 stk0 =
      { regs := r.drop (r.length - reg0)
        stack := stk.drop (stk.length - stk0)
        mem := m.freeStack ((stk.take (stk.length - stk0)).map (·.2.1))
        os := os } := rfl

theorem contPost_normal_mk (kn kb kc : SymState → Prop) (kr : Val → Mem → OSState → Prop)
    (kg : String → SymState → Prop) :
    ({ normal := kn, onBreak := kb, onContinue := kc, onReturn := kr, onGoto := kg } : ContPost).normal = kn := rfl
theorem contPost_onBreak_mk (kn kb kc : SymState → Prop) (kr : Val → Mem → OSState → Prop)
    (kg : String → SymState → Prop) :
    ({ normal := kn, onBreak := kb, onContinue := kc, onReturn := kr, onGoto := kg } : ContPost).onBreak = kb := rfl
theorem contPost_onContinue_mk (kn kb kc : SymState → Prop) (kr : Val → Mem → OSState → Prop)
    (kg : String → SymState → Prop) :
    ({ normal := kn, onBreak := kb, onContinue := kc, onReturn := kr, onGoto := kg } : ContPost).onContinue = kc := rfl
theorem contPost_onReturn_mk (kn kb kc : SymState → Prop) (kr : Val → Mem → OSState → Prop)
    (kg : String → SymState → Prop) :
    ({ normal := kn, onBreak := kb, onContinue := kc, onReturn := kr, onGoto := kg } : ContPost).onReturn = kr := rfl
theorem contPost_onGoto_mk (kn kb kc : SymState → Prop) (kr : Val → Mem → OSState → Prop)
    (kg : String → SymState → Prop) :
    ({ normal := kn, onBreak := kb, onContinue := kc, onReturn := kr, onGoto := kg } : ContPost).onGoto = kg := rfl

section ConcreteVC

theorem vcStmt_eq_vcStmtGen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {s : SymState} {stmt : AnnStmt} :
    vcStmt prog cfg specs baseEnv retTy k s stmt =
      vcStmtGen true prog cfg specs.toContracts baseEnv retTy k s stmt := rfl

theorem vcStmtList_eq_vcStmtListGen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SpecEnv prog cfg ext} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {s : SymState} {ss : List AnnStmt} :
    vcStmtList prog cfg specs baseEnv retTy k s ss =
      vcStmtListGen true prog cfg specs.toContracts baseEnv retTy k s ss := rfl

theorem vcStmtSafe_eq_vcStmtGen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {s : SymState} {stmt : AnnStmt} :
    vcStmtSafe prog cfg specs baseEnv retTy k s stmt =
      vcStmtGen false prog cfg specs.toContracts baseEnv retTy k s stmt := rfl

theorem vcStmtSafeList_eq_vcStmtListGen {ext : ExtHandler} {prog : Prog} {cfg : PointerConfig}
    {specs : SafeSpecEnv prog cfg ext} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {s : SymState} {ss : List AnnStmt} :
    vcStmtSafeList prog cfg specs baseEnv retTy k s ss =
      vcStmtListGen false prog cfg specs.toContracts baseEnv retTy k s ss := rfl

theorem vcDeclList_nil_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcDeclList prog cfg contracts baseEnv k [] { regs := r, stack := stk, mem := m, os := os } =
      k.normal { regs := r, stack := stk, mem := m, os := os } := rfl

theorem vcDeclList_static_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {k : ContPost}
    {nm : String} {ty : CTy} {init? : Option InitVal} {isStk : Bool}
    {rest : List (VarDecl × Bool)} {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcDeclList prog cfg contracts baseEnv k
        (({ name := nm, ty := ty, isStatic := true, init? := init? }, isStk) :: rest)
        { regs := r, stack := stk, mem := m, os := os } =
      vcDeclList prog cfg contracts baseEnv k rest { regs := r, stack := stk, mem := m, os := os } := rfl

theorem vcDeclList_reg_none_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {k : ContPost}
    {nm : String} {ty : CTy} {rest : List (VarDecl × Bool)}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcDeclList prog cfg contracts baseEnv k
        (({ name := nm, ty := ty, isStatic := false, init? := none }, false) :: rest)
        { regs := r, stack := stk, mem := m, os := os } =
      (max 1 (sizeofTy prog.tags ty) < ptrDiffLimit ∧
       0 < max 1 (alignofTy prog.tags ty) ∧
       stk.lookup nm = none ∧
       vcDeclList prog cfg contracts baseEnv k rest
         { regs := (nm, .undef, ty) :: r, stack := stk, mem := m, os := os }) := rfl

theorem vcDeclList_reg_expr_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {k : ContPost}
    {nm : String} {ty : CTy} {e : CExpr} {rest : List (VarDecl × Bool)}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcDeclList prog cfg contracts baseEnv k
        (({ name := nm, ty := ty, isStatic := false, init? := some (.expr e) }, false) :: rest)
        { regs := r, stack := stk, mem := m, os := os } =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] e fun rv _ s1 _ _ =>
        vcCast s1.mem ty.stripConst rv fun cv _ =>
          max 1 (sizeofTy prog.tags ty) < ptrDiffLimit ∧
          0 < max 1 (alignofTy prog.tags ty) ∧
          s1.stack.lookup nm = none ∧
          ValScalarTyped ty cv ∧
          vcBindVal cv fun v0 =>
            vcDeclList prog cfg contracts baseEnv k rest
              { regs := (nm, v0, ty) :: s1.regs, stack := s1.stack, mem := s1.mem, os := s1.os } := rfl

theorem vcDeclList_stk_none_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {k : ContPost}
    {nm : String} {ty : CTy} {rest : List (VarDecl × Bool)}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcDeclList prog cfg contracts baseEnv k
        (({ name := nm, ty := ty, isStatic := false, init? := none }, true) :: rest)
        { regs := r, stack := stk, mem := m, os := os } =
      (∃ (hsz : max 1 (sizeofTy prog.tags ty) < ptrDiffLimit)
         (hal : 0 < max 1 (alignofTy prog.tags ty)),
         r.lookup nm = none ∧
         ∀ (bid : BlockId) (hle : m.nextBlock ≤ bid) (base : UInt64)
           (hba : base.toNat % max 1 (alignofTy prog.tags ty) = 0),
           let m' := allocAt m bid hle (max 1 (sizeofTy prog.tags ty))
             (max 1 (alignofTy prog.tags ty)) .rw .stack base (fun _ => .undef) hsz hal hba
           vcDeclList prog cfg contracts baseEnv k rest
             { regs := r, stack := (nm, bid, ty) :: stk, mem := m', os := os }) := rfl

theorem vcDeclList_stk_expr_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {k : ContPost}
    {nm : String} {ty : CTy} {e : CExpr} {rest : List (VarDecl × Bool)}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcDeclList prog cfg contracts baseEnv k
        (({ name := nm, ty := ty, isStatic := false, init? := some (.expr e) }, true) :: rest)
        { regs := r, stack := stk, mem := m, os := os } =
      (if isAggTy ty then
         vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] e fun bs _ s1 _ _ =>
           ∃ (hsz : max 1 (sizeofTy prog.tags ty) < ptrDiffLimit)
             (hal : 0 < max 1 (alignofTy prog.tags ty)),
             bs.length = sizeofTy prog.tags ty ∧
             s1.regs.lookup nm = none ∧
             ∀ (bid : BlockId) (hle : s1.mem.nextBlock ≤ bid) (base : UInt64)
               (hba : base.toNat % max 1 (alignofTy prog.tags ty) = 0),
               let m1 := allocAt s1.mem bid hle (max 1 (sizeofTy prog.tags ty))
                 (max 1 (alignofTy prog.tags ty)) .rw .stack base (fun _ => .undef) hsz hal hba
               match m1.writeBytes bid 0 bs with
               | none => False
               | some m2 =>
                 vcDeclList prog cfg contracts baseEnv k rest
                   { regs := s1.regs, stack := (nm, bid, ty) :: s1.stack, mem := m2, os := s1.os }
       else
         vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] e fun rv _ s1 _ _ =>
           vcCast s1.mem ty.stripConst rv fun cv _ =>
             ∃ (hsz : max 1 (sizeofTy prog.tags ty) < ptrDiffLimit)
               (hal : 0 < max 1 (alignofTy prog.tags ty)),
               ValScalarTyped ty cv ∧
               s1.regs.lookup nm = none ∧
               ∀ (bid : BlockId) (hle : s1.mem.nextBlock ≤ bid) (base : UInt64)
                 (hba : base.toNat % max 1 (alignofTy prog.tags ty) = 0),
                 let m1 := allocAt s1.mem bid hle (max 1 (sizeofTy prog.tags ty))
                   (max 1 (alignofTy prog.tags ty)) .rw .stack base (fun _ => .undef) hsz hal hba
                 match Sem.writeVal m1 bid 0 ty.stripConst cv with
                 | none => False
                 | some m2 =>
                   vcDeclList prog cfg contracts baseEnv k rest
                     { regs := s1.regs, stack := (nm, bid, ty) :: s1.stack, mem := m2, os := s1.os }) := rfl

theorem vcStmtListGen_nil_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcStmtListGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } [] =
      k.normal { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtListGen

theorem vcStmtListGen_singleton_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {hd : AnnStmt} :
    vcStmtListGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } [hd] =
      vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } hd := by
  conv => lhs; unfold vcStmtListGen

theorem vcStmtListGen_cons_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {hd hd2 : AnnStmt} {tl : List AnnStmt} :
    vcStmtListGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (hd :: hd2 :: tl) =
      vcStmtGen strict prog cfg contracts baseEnv retTy
        { k with
          normal := fun s1 => vcStmtListGen strict prog cfg contracts baseEnv retTy k s1 (hd2 :: tl)
          onGoto := fun lbl s1 =>
            match hgt : AnnStmt.findGotoAnnList lbl (hd2 :: tl) with
            | some (tgt, fs) =>
              have _hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf (hd2 :: tl) :=
                AnnStmt.findGotoAnnList_sizeOf_lt hgt
              vcStmtGen strict prog cfg contracts baseEnv retTy
                (vcFramesCont strict prog cfg contracts baseEnv retTy k s1 fs) s1 tgt
            | none =>
              AnnStmt.annHasLabelList lbl (hd2 :: tl) = false ∧ k.onGoto lbl s1 }
        { regs := r, stack := stk, mem := m, os := os } hd := by
  conv => lhs; unfold vcStmtListGen
  rfl

theorem vcStmtGen_nop_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } .nop =
      k.normal { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_expr_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {e : CExpr} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.expr e) =
      vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] e
        fun s1 _ _ => k.normal s1 := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_decl_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {d : VarDecl} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.decl d) =
      vcDeclList prog cfg contracts baseEnv k [(d, false)]
        { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_decls_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {ds : List VarDecl} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.decls ds) =
      vcDeclList prog cfg contracts baseEnv k (ds.map (·, false))
        { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_stackDecl_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {d : VarDecl} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.stackDecl d) =
      vcDeclList prog cfg contracts baseEnv k [(d, true)]
        { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_stackDecls_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {ds : List VarDecl} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.stackDecls ds) =
      vcDeclList prog cfg contracts baseEnv k (ds.map (·, true))
        { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_mixedDecls_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {ds : List (VarDecl × Bool)} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.mixedDecls ds) =
      vcDeclList prog cfg contracts baseEnv k ds
        { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_block_nil_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.block []) =
      k.normal { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_block_cons_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {hd : AnnStmt} {tl : List AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.block (hd :: tl)) =
      vcStmtListGen strict prog cfg contracts baseEnv retTy
        { normal := fun s' => k.normal (s'.exitBlock r.length stk.length)
          onBreak := fun s' => k.onBreak (s'.exitBlock r.length stk.length)
          onContinue := fun s' => k.onContinue (s'.exitBlock r.length stk.length)
          onReturn := k.onReturn
          onGoto := fun lbl s' => k.onGoto lbl (s'.exitBlock r.length stk.length) }
        { regs := r, stack := stk, mem := m, os := os } (hd :: tl) := by
  conv =>
    lhs
    unfold vcStmtGen
    simp only [symState_regs_mk, symState_stack_mk]

theorem vcStmtGen_ifStmt_none_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {c : CExpr} {t : AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.ifStmt c t none) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] c
        fun vc _ s1 _ _ =>
          vcBranch vc (vcStmtGen strict prog cfg contracts baseEnv retTy k s1 t) (k.normal s1) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_ifStmt_some_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {c : CExpr} {t f : AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.ifStmt c t (some f)) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] c
        fun vc _ s1 _ _ =>
          vcBranch vc
            (vcStmtGen strict prog cfg contracts baseEnv retTy k s1 t)
            (vcStmtGen strict prog cfg contracts baseEnv retTy k s1 f) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_ifJoin_none_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {c : CExpr} {t : AnnStmt} {J : SymState → Prop} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.ifJoin c t none J) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] c
        fun vc _ s1 _ _ =>
          vcBranch vc (vcStmtGen strict prog cfg contracts baseEnv retTy { k with normal := J } s1 t) (J s1) ∧
          (∀ s2, J s2 → k.normal s2) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_ifJoin_some_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {c : CExpr} {t f : AnnStmt} {J : SymState → Prop} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.ifJoin c t (some f) J) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] c
        fun vc _ s1 _ _ =>
          let kJoin : ContPost := { k with normal := J }
          vcBranch vc
            (vcStmtGen strict prog cfg contracts baseEnv retTy kJoin s1 t)
            (vcStmtGen strict prog cfg contracts baseEnv retTy kJoin s1 f) ∧
          (∀ s2, J s2 → k.normal s2) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_whileLoop_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {c : CExpr} {body : AnnStmt}
    {Inv : SymState → Nat → SymState → Prop} {meas : SymState → Nat} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.whileLoop c body Inv meas) =
      ((if strict then
          Inv { regs := r, stack := stk, mem := m, os := os }
            (meas { regs := r, stack := stk, mem := m, os := os })
            { regs := r, stack := stk, mem := m, os := os }
        else
          Inv { regs := r, stack := stk, mem := m, os := os } 0
            { regs := r, stack := stk, mem := m, os := os }) ∧
       ∀ n s1,
         (if strict then Inv { regs := r, stack := stk, mem := m, os := os } n s1
          else n = 0 ∧ Inv { regs := r, stack := stk, mem := m, os := os } 0 s1) →
         vcExprR prog cfg contracts baseEnv s1 [] [] c fun vc _ s2 _ _ =>
           vcBranch vc
             (vcStmtGen strict prog cfg contracts baseEnv retTy
               { normal := fun s3 =>
                   if strict then meas s3 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                   else Inv { regs := r, stack := stk, mem := m, os := os } 0 s3
                 onBreak := k.normal
                 onContinue := fun s3 =>
                   if strict then meas s3 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                   else Inv { regs := r, stack := stk, mem := m, os := os } 0 s3
                 onReturn := k.onReturn
                 onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
               s2 body)
             (k.normal s2)) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_doWhileLoop_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {body : AnnStmt} {c : CExpr}
    {Inv : SymState → Nat → SymState → Prop} {meas : SymState → Nat} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.doWhileLoop body c Inv meas) =
      ((if strict then
          Inv { regs := r, stack := stk, mem := m, os := os }
            (meas { regs := r, stack := stk, mem := m, os := os })
            { regs := r, stack := stk, mem := m, os := os }
        else
          Inv { regs := r, stack := stk, mem := m, os := os } 0
            { regs := r, stack := stk, mem := m, os := os }) ∧
       ∀ n s1,
         (if strict then Inv { regs := r, stack := stk, mem := m, os := os } n s1
          else n = 0 ∧ Inv { regs := r, stack := stk, mem := m, os := os } 0 s1) →
         let afterBody := fun s2 =>
           vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
             vcBranch vc
               (if strict then meas s3 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                else Inv { regs := r, stack := stk, mem := m, os := os } 0 s3)
               (k.normal s3)
         vcStmtGen strict prog cfg contracts baseEnv retTy
           { normal := afterBody
             onBreak := k.normal
             onContinue := afterBody
             onReturn := k.onReturn
             onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
           s1 body) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_doWhileGotos_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {body : AnnStmt} {c : CExpr}
    {Inv : SymState → Nat → SymState → Prop}
    {gotoSpecs : List (String × (SymState → Nat → SymState → Prop))}
    {meas : SymState → Nat} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.doWhileGotos body c Inv gotoSpecs meas) =
      ((if strict then
          Inv { regs := r, stack := stk, mem := m, os := os }
            (meas { regs := r, stack := stk, mem := m, os := os })
            { regs := r, stack := stk, mem := m, os := os }
        else
          Inv { regs := r, stack := stk, mem := m, os := os } 0
            { regs := r, stack := stk, mem := m, os := os }) ∧
       (∀ n s1,
         (if strict then Inv { regs := r, stack := stk, mem := m, os := os } n s1
          else n = 0 ∧ Inv { regs := r, stack := stk, mem := m, os := os } 0 s1) →
         let afterBody := fun s2 =>
           vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
             vcBranch vc
               (if strict then meas s3 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                else Inv { regs := r, stack := stk, mem := m, os := os } 0 s3)
               (k.normal s3)
         vcStmtGen strict prog cfg contracts baseEnv retTy
           { normal := afterBody
             onBreak := k.normal
             onContinue := afterBody
             onReturn := k.onReturn
             onGoto := fun lbl s3 =>
               match gotoSpecs.lookup lbl with
               | some GSpec =>
                 if strict then meas s3 < n ∧ GSpec { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                 else GSpec { regs := r, stack := stk, mem := m, os := os } 0 s3
               | none => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
           s1 body) ∧
       (∀ p ∈ gotoSpecs,
         match hgt : AnnStmt.findGotoAnn p.1 body with
         | none => False
         | some (tgt, fs) =>
           have _hlt : sizeOf tgt + AnnStmt.framesSize fs < sizeOf body :=
             AnnStmt.findGotoAnn_sizeOf_lt hgt
           ∀ n sG,
             (if strict then p.2 { regs := r, stack := stk, mem := m, os := os } n sG
              else n = 0 ∧ p.2 { regs := r, stack := stk, mem := m, os := os } 0 sG) →
             let afterBody := fun s2 =>
               vcExprR prog cfg contracts baseEnv s2 [] [] c fun vc _ s3 _ _ =>
                 vcBranch vc
                   (if strict then meas s3 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                    else Inv { regs := r, stack := stk, mem := m, os := os } 0 s3)
                   (k.normal s3)
             let kLoop : ContPost :=
               { normal := afterBody
                 onBreak := k.normal
                 onContinue := afterBody
                 onReturn := k.onReturn
                 onGoto := fun lbl s3 =>
                   match gotoSpecs.lookup lbl with
                   | some GSpec =>
                     if strict then meas s3 < n ∧ GSpec { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
                     else GSpec { regs := r, stack := stk, mem := m, os := os } 0 s3
                   | none => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
             vcStmtGen strict prog cfg contracts baseEnv retTy
               (vcFramesCont strict prog cfg contracts baseEnv retTy kLoop sG fs) sG tgt)) := by
  conv => lhs; unfold vcStmtGen
  rfl

theorem vcStmtGen_forLoop_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState}
    {init? c? stp? : Option CExpr} {body : AnnStmt}
    {Inv : SymState → Nat → SymState → Prop} {meas : SymState → Nat} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.forLoop init? c? stp? body Inv meas) =
      ((match init? with
        | none =>
          if strict then
            Inv { regs := r, stack := stk, mem := m, os := os }
              (meas { regs := r, stack := stk, mem := m, os := os })
              { regs := r, stack := stk, mem := m, os := os }
          else
            Inv { regs := r, stack := stk, mem := m, os := os } 0
              { regs := r, stack := stk, mem := m, os := os }
        | some init =>
          vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] init
            fun s0 _ _ =>
              if strict then Inv { regs := r, stack := stk, mem := m, os := os } (meas s0) s0
              else Inv { regs := r, stack := stk, mem := m, os := os } 0 s0) ∧
       ∀ n s1,
         (if strict then Inv { regs := r, stack := stk, mem := m, os := os } n s1
          else n = 0 ∧ Inv { regs := r, stack := stk, mem := m, os := os } 0 s1) →
         let afterBody := fun s2 =>
           match stp? with
           | none =>
             if strict then meas s2 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s2) s2
             else Inv { regs := r, stack := stk, mem := m, os := os } 0 s2
           | some stp =>
             vcExprDiscard prog cfg contracts baseEnv s2 [] [] stp fun s3 _ _ =>
               if strict then meas s3 < n ∧ Inv { regs := r, stack := stk, mem := m, os := os } (meas s3) s3
               else Inv { regs := r, stack := stk, mem := m, os := os } 0 s3
         let kLoop : ContPost :=
           { normal := afterBody
             onBreak := k.normal
             onContinue := afterBody
             onReturn := k.onReturn
             onGoto := fun lbl s3 => AnnStmt.annHasLabel lbl body = false ∧ k.onGoto lbl s3 }
         match c? with
         | some c =>
           vcExprR prog cfg contracts baseEnv s1 [] [] c fun vc _ s2 _ _ =>
             vcBranch vc (vcStmtGen strict prog cfg contracts baseEnv retTy kLoop s2 body) (k.normal s2)
         | none => vcStmtGen strict prog cfg contracts baseEnv retTy kLoop s1 body) := by
  conv => lhs; unfold vcStmtGen
  rfl

def vcSwitchCont (strict : Bool) (prog : Prog) (cfg : PointerConfig)
    (contracts : ContractEnv) (baseEnv : Env) (retTy : CTy)
    (k : ContPost) (s1 : SymState) (iv : Int) (body : AnnStmt) :
    Option AnnStmt → Prop
  | none => Sem.findSwitchTarget iv body.erase = none ∧ k.normal s1
  | some tgt =>
    Sem.findSwitchTarget iv body.erase = some tgt.erase ∧
    vcStmtGen strict prog cfg contracts baseEnv retTy { k with onBreak := k.normal } s1 tgt

theorem vcStmtGen_switchStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {scrut : CExpr} {body : AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.switchStmt scrut body) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] scrut
        fun v _ s1 _ _ =>
          ∃ k_int iv, Sem.valAsInt? v = some (k_int, iv) ∧
            vcSwitchCont strict prog cfg contracts baseEnv retTy k s1 iv body
              (AnnStmt.findSwitchAnnTarget iv body) := by
  conv => lhs; unfold vcStmtGen
  congr 1; funext v _ s1 _ _
  apply propext
  apply exists_congr; intro k_int
  apply exists_congr; intro iv
  apply and_congr_right; intro _
  split
  · rename_i hnone; (conv => rhs; rw [hnone]); rfl
  · rename_i tgt hsome; (conv => rhs; rw [hsome]); rfl

theorem vcStmtGen_caseStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {v : Int} {body : AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.caseStmt v body) =
      vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } body := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_defaultStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {body : AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.defaultStmt body) =
      vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } body := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_labelStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {lbl : String} {body : AnnStmt} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.labelStmt lbl body) =
      vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } body := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_gotoStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {lbl : String} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.gotoStmt lbl) =
      k.onGoto lbl { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_breakStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } .breakStmt =
      k.onBreak { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_continueStmt_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } .continueStmt =
      k.onContinue { regs := r, stack := stk, mem := m, os := os } := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_returnStmt_none_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.returnStmt none) =
      (retTy.isVoid = true ∧
       k.onReturn .void ({ regs := r, stack := stk, mem := m, os := os } : SymState).exitFn os) := by
  conv => lhs; unfold vcStmtGen

theorem vcStmtGen_returnStmt_some_mk {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {e : CExpr} :
    vcStmtGen strict prog cfg contracts baseEnv retTy k
        { regs := r, stack := stk, mem := m, os := os } (.returnStmt (some e)) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } [] [] e
        fun rv _ s1 _ _ =>
          if retTy.isVoid then k.onReturn .void s1.exitFn s1.os
          else vcCast s1.mem retTy rv fun cv _ => k.onReturn cv s1.exitFn s1.os := by
  conv => lhs; unfold vcStmtGen

theorem vcExprL_paren_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.paren e) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e K := by
  conv => lhs; unfold vcExprL

theorem vcExprL_var_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {x : String} {K} :
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x) K =
      (r.lookup x = none ∧
       match stk.lookup x with
       | some (b, ty) => K b 0 ty { regs := r, stack := stk, mem := m, os := os } mv mh
       | none =>
         match baseEnv.lookup x with
         | some (b, ty) => K b 0 ty { regs := r, stack := stk, mem := m, os := os } mv mh
         | none => False) := by
  conv => lhs; unfold vcExprL
  rfl

theorem vcExprL_deref_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr el, .ptr b off => K b off el s1 mv1 mh1
          | _, _ => False := by
  conv => lhs; unfold vcExprL
  rfl

theorem vcExprL_index_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base idx : CExpr} {K} :
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index base idx) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
            match pty.unqual, Sem.valAsInt? iv with
            | .ptr el, some (_, idxInt) =>
              match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
              | some (.ptr b off) => K b off el s2 mv2 mh2
              | _ => False
            | _, _ => False := by
  conv => lhs; unfold vcExprL
  rfl

theorem vcExprL_member_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base : CExpr} {fld : String} {K} :
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member base fld) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun b off sty s1 mv1 mh1 =>
          match fieldLayout? prog.tags sty fld with
          | some (foff, fty) => K b (Int64.ofInt (off.toInt + foff)) fty s1 mv1 mh1
          | none => False := by
  conv => lhs; unfold vcExprL
  rfl

theorem vcExprL_arrow_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base : CExpr} {fld : String} {K} :
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow base fld) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr sty, .ptr b off =>
            match fieldLayout? prog.tags sty fld with
            | some (foff, fty) => K b (Int64.ofInt (off.toInt + foff)) fty s1 mv1 mh1
            | none => False
          | _, _ => False := by
  conv => lhs; unfold vcExprL
  rfl

theorem vcExprR_paren_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.paren e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_lit_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {val : Int} {k : IntKind} {suf : LitSuffix} {rad : LitRadix} {sym? : Option String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.lit val k suf rad sym?) K =
      K (Sem.ofIntCast k val) (.int k) { regs := r, stack := stk, mem := m, os := os } mv mh := by
  conv => lhs; unfold vcExprR

theorem vcExprR_strLit_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {str : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.strLit str) K =
      vcStrLit { regs := r, stack := stk, mem := m, os := os } mv mh str K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_sizeOfTy_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {ty : CTy} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.sizeOfTy ty) K =
      K (.int .u64 (BitVec.ofNat IntKind.u64.bits (sizeofTy prog.tags ty))) (.int .u64)
        { regs := r, stack := stk, mem := m, os := os } mv mh := by
  conv => lhs; unfold vcExprR

theorem vcExprR_sizeOfExpr_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.sizeOfExpr e) K =
      match Sem.exprType? prog.tags
          (({ regs := r, stack := stk, mem := m, os := os } : SymState).typeEnv baseEnv) prog.fnProtos e with
      | some ty =>
        K (.int .u64 (BitVec.ofNat IntKind.u64.bits (sizeofTy prog.tags ty))) (.int .u64)
          { regs := r, stack := stk, mem := m, os := os } mv mh
      | none => False := by
  conv => lhs; unfold vcExprR
  rfl

def vcVarCont (prog : Prog) (baseEnv : Env) (r : RegEnv) (stk : Env) (m : Mem) (os : OSState)
    (mv : List String) (mh : List (BlockId × Int64 × Nat)) (x : String)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | some (v, ty) =>
    isScalarPlaceTy ty ∧ x ∉ mv ∧ v ≠ .undef ∧
    K v ty.decay { regs := r, stack := stk, mem := m, os := os } mv mh
  | none =>
    let s := ({ regs := r, stack := stk, mem := m, os := os } : SymState)
    match stk.lookup x with
    | some (b, ty) => vcReadHeapPlace prog s mv mh b 0 ty K
    | none =>
      match baseEnv.lookup x with
      | some (b, ty) => vcReadHeapPlace prog s mv mh b 0 ty K
      | none =>
        match Sem.enumConst? prog.tags x with
        | some ev => K (Sem.ofIntCast .i32 ev) (.int .i32) s mv mh
        | none =>
          match prog.fnProtos x with
          | some (ret, ps, va) => K (.fnPtr x) (.fnPtr ret ps va) s mv mh
          | none => False

theorem vcVarCont_some {prog baseEnv r stk m os mv mh x K v ty} :
    vcVarCont prog baseEnv r stk m os mv mh x K (some (v, ty)) =
      (isScalarPlaceTy ty ∧ x ∉ mv ∧ v ≠ .undef ∧
       K v ty.decay { regs := r, stack := stk, mem := m, os := os } mv mh) := rfl

theorem vcVarCont_none {prog baseEnv r stk m os mv mh x K} :
    let s := ({ regs := r, stack := stk, mem := m, os := os } : SymState)
    vcVarCont prog baseEnv r stk m os mv mh x K none =
      (match stk.lookup x with
       | some (b, ty) => vcReadHeapPlace prog s mv mh b 0 ty K
       | none =>
         match baseEnv.lookup x with
         | some (b, ty) => vcReadHeapPlace prog s mv mh b 0 ty K
         | none =>
           match Sem.enumConst? prog.tags x with
           | some ev => K (Sem.ofIntCast .i32 ev) (.int .i32) s mv mh
           | none =>
             match prog.fnProtos x with
             | some (ret, ps, va) => K (.fnPtr x) (.fnPtr ret ps va) s mv mh
             | none => False) := rfl

theorem vcExprR_var_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {x : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x) K =
      vcVarCont prog baseEnv r stk m os mv mh x K (r.lookup x) := by
  conv =>
    lhs
    unfold vcExprR
    simp only [symState_regs_mk, symState_stack_mk]
  cases r.lookup x <;> rfl

theorem vcExprR_unary_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : UnOp} {e : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.unary op e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e
        fun v _ s1 mv1 mh1 => vcUnary op v fun rv rt => K rv rt s1 mv1 mh1 := by
  conv => lhs; unfold vcExprR

theorem vcExprR_cast_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {target : CTy} {e : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.cast target e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e
        fun v _ s1 mv1 mh1 => vcCast s1.mem target v fun cv _ => K cv target s1 mv1 mh1 := by
  conv => lhs; unfold vcExprR

theorem vcExprR_binary_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : BinOp} {l rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.binary op l rhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun v1 t1 s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun v2 t2 s2 mv2 mh2 =>
            vcBinary cfg prog.tags s2.mem op v1 t1 v2 t2 fun rv rt => K rv rt s2 mv2 mh2 := by
  conv => lhs; unfold vcExprR

theorem vcExprR_logAnd_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {l rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.logAnd l rhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun v1 _ s1 mv1 mh1 =>
          vcBranch v1
            (vcExprR prog cfg contracts baseEnv s1 [] [] rhs fun v2 _ s2 mv2 mh2 =>
              vcBranch v2 (K (.int .i32 1) (.int .i32) s2 mv2 mh2) (K (.int .i32 0) (.int .i32) s2 mv2 mh2))
            (K (.int .i32 0) (.int .i32) s1 mv1 mh1) := by
  conv => lhs; unfold vcExprR

theorem vcExprR_logOr_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {l rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.logOr l rhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun v1 _ s1 mv1 mh1 =>
          vcBranch v1
            (K (.int .i32 1) (.int .i32) s1 mv1 mh1)
            (vcExprR prog cfg contracts baseEnv s1 [] [] rhs fun v2 _ s2 mv2 mh2 =>
              vcBranch v2 (K (.int .i32 1) (.int .i32) s2 mv2 mh2) (K (.int .i32 0) (.int .i32) s2 mv2 mh2)) := by
  conv => lhs; unfold vcExprR

theorem vcExprR_cond_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {c t f : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.cond c t f) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh c
        fun vc _ s1 _ _ =>
          vcBranch vc (vcExprR prog cfg contracts baseEnv s1 [] [] t K)
            (vcExprR prog cfg contracts baseEnv s1 [] [] f K) := by
  conv => lhs; unfold vcExprR

theorem vcExprR_comma_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {l rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.comma l rhs) K =
      vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun s1 _ _ => vcExprR prog cfg contracts baseEnv s1 [] [] rhs K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_addrOf_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {l : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.addrOf l) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun b off ty s1 mv1 mh1 => K (.ptr b off) (.ptr ty) s1 mv1 mh1 := by
  conv => lhs; unfold vcExprR

theorem vcExprR_deref_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr el, .ptr b off => vcReadHeapPlace prog s1 mv1 mh1 b off el K
          | .fnPtr rt ps va, .fnPtr sym => K (.fnPtr sym) (.fnPtr rt ps va) s1 mv1 mh1
          | _, _ => False := by
  conv => lhs; unfold vcExprR
  rfl

theorem vcExprR_index_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base idx : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index base idx) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
            match pty.unqual, Sem.valAsInt? iv with
            | .ptr el, some (_, idxInt) =>
              match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
              | some (.ptr b off) => vcReadHeapPlace prog s2 mv2 mh2 b off el K
              | _ => False
            | _, _ => False := by
  conv => lhs; unfold vcExprR
  rfl

theorem vcExprR_member_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base : CExpr} {fld : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member base fld) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun b off sty s1 mv1 mh1 =>
          match fieldLayout? prog.tags sty fld with
          | some (foff, fty) => vcReadHeapPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
          | none => False := by
  conv => lhs; unfold vcExprR
  rfl

theorem vcExprR_arrow_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base : CExpr} {fld : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow base fld) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr sty, .ptr b off =>
            match fieldLayout? prog.tags sty fld with
            | some (foff, fty) =>
              vcReadHeapPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
            | none => False
          | _, _ => False := by
  conv => lhs; unfold vcExprR
  rfl

def vcIncDecVarCont (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv) (baseEnv : Env)
    (r : RegEnv) (stk : Env) (m : Mem) (os : OSState)
    (mv : List String) (mh : List (BlockId × Int64 × Nat)) (op : IncDecOp) (x : String)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | some (oldV, lty) =>
    let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
    x ∉ mv ∧ oldV ≠ .undef ∧ lty.isConst = false ∧
    vcBinary cfg prog.tags m .add oldV lty (.int .i32 (BitVec.ofInt IntKind.i32.bits d)) (.int .i32) fun newV _ =>
      vcCast m lty newV fun cv _ =>
        ValScalarTyped lty cv ∧
        vcBindVal cv fun nv =>
          let retV := match op with | .preInc | .preDec => newV | _ => oldV
          K retV lty { regs := r.set x nv lty, stack := stk, mem := m, os := os } (x :: mv) mh
  | none =>
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x)
      fun b off lty s1 mv1 mh1 =>
        vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 b off lty K

theorem vcIncDecVarCont_some {prog cfg contracts baseEnv r stk m os mv mh op x K oldV lty} :
    vcIncDecVarCont prog cfg contracts baseEnv r stk m os mv mh op x K (some (oldV, lty)) =
      (let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
       x ∉ mv ∧ oldV ≠ .undef ∧ lty.isConst = false ∧
       vcBinary cfg prog.tags m .add oldV lty (.int .i32 (BitVec.ofInt IntKind.i32.bits d)) (.int .i32) fun newV _ =>
         vcCast m lty newV fun cv _ =>
           ValScalarTyped lty cv ∧
           vcBindVal cv fun nv =>
             let retV := match op with | .preInc | .preDec => newV | _ => oldV
             K retV lty { regs := r.set x nv lty, stack := stk, mem := m, os := os } (x :: mv) mh) := rfl

theorem vcIncDecVarCont_none {prog cfg contracts baseEnv r stk m os mv mh op x K} :
    vcIncDecVarCont prog cfg contracts baseEnv r stk m os mv mh op x K none =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x)
        fun b off lty s1 mv1 mh1 =>
          vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 b off lty K := rfl

theorem vcExprR_incDec_var_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : IncDecOp} {x : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op (.var x)) K =
      vcIncDecVarCont prog cfg contracts baseEnv r stk m os mv mh op x K (r.lookup x) := by
  conv =>
    lhs
    unfold vcExprR
    simp only [symState_regs_mk, symState_stack_mk, symState_mem_mk, symState_os_mk]
  cases r.lookup x <;> rfl

theorem vcExprR_incDec_deref_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : IncDecOp} {e : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op (.deref e)) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e)
        fun b off lty s1 mv1 mh1 => vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 b off lty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_incDec_index_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : IncDecOp} {b idx : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op (.index b idx)) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index b idx)
        fun blk off lty s1 mv1 mh1 => vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 blk off lty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_incDec_member_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : IncDecOp} {b : CExpr} {fld : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op (.member b fld)) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member b fld)
        fun blk off lty s1 mv1 mh1 => vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 blk off lty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_incDec_arrow_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {op : IncDecOp} {b : CExpr} {fld : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op (.arrow b fld)) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow b fld)
        fun blk off lty s1 mv1 mh1 => vcIncDecPlaceFinish prog cfg op s1 mv1 mh1 blk off lty K := by
  conv => lhs; unfold vcExprR

def vcAssignStepCont (prog : Prog) (cfg : PointerConfig) (op : AssignOp) (x : String)
    (mv1 : List String) (mh1 : List (BlockId × Int64 × Nat)) (s1 : SymState)
    (lty : CTy) (rval : Val) (rty : CTy)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | none => False
  | some (oldV, lty1) =>
    lty1 = lty ∧
    match Sem.assignOpToBin? op with
    | none =>
      vcCast s1.mem lty rval fun cv _ =>
        ValScalarTyped lty cv ∧
        vcBindVal cv fun nv =>
          K nv lty { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os } (x :: mv1) mh1
    | some bop =>
      oldV ≠ .undef ∧
      vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
        vcCast s1.mem lty rawV fun cv _ =>
          ValScalarTyped lty cv ∧
          vcBindVal cv fun nv =>
            K nv lty { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os } (x :: mv1) mh1

theorem vcAssignStepCont_some {prog cfg op x mv1 mh1 s1 lty rval rty K oldV lty1} :
    vcAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K (some (oldV, lty1)) =
      (lty1 = lty ∧
       match Sem.assignOpToBin? op with
       | none =>
         vcCast s1.mem lty rval fun cv _ =>
           ValScalarTyped lty cv ∧
           vcBindVal cv fun nv =>
             K nv lty { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os } (x :: mv1) mh1
       | some bop =>
         oldV ≠ .undef ∧
         vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
           vcCast s1.mem lty rawV fun cv _ =>
             ValScalarTyped lty cv ∧
             vcBindVal cv fun nv =>
               K nv lty { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os }
                 (x :: mv1) mh1) := rfl

theorem vcAssignStepCont_none {prog cfg op x mv1 mh1 s1 lty rval rty K} :
    vcAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K none = False := rfl

def vcAssignVarCont (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (r : RegEnv) (stk : Env) (m : Mem) (os : OSState)
    (mv : List String) (mh : List (BlockId × Int64 × Nat)) (op : AssignOp) (x : String) (rhs : CExpr)
    (K : Val → CTy → SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | none =>
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x)
      fun b off lty s1 mv1 mh1 =>
        vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
          vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K
  | some (_, lty) =>
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh rhs
      fun rval rty s1 mv1 mh1 =>
        x ∉ mv1 ∧ lty.isConst = false ∧
        vcAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K (s1.regs.lookup x)

theorem vcAssignVarCont_some {prog cfg contracts baseEnv r stk m os mv mh op x rhs K oldV0 lty} :
    vcAssignVarCont prog cfg contracts baseEnv r stk m os mv mh op x rhs K (some (oldV0, lty)) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh rhs
        fun rval rty s1 mv1 mh1 =>
          x ∉ mv1 ∧ lty.isConst = false ∧
          vcAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K (s1.regs.lookup x) := rfl

theorem vcAssignVarCont_none {prog cfg contracts baseEnv r stk m os mv mh op x rhs K} :
    vcAssignVarCont prog cfg contracts baseEnv r stk m os mv mh op x rhs K none =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x)
        fun b off lty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K := rfl

theorem vcExprR_assign_var_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {x : String} {rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.var x) rhs) K =
      vcAssignVarCont prog cfg contracts baseEnv r stk m os mv mh op x rhs K (r.lookup x) := by
  conv =>
    lhs
    unfold vcExprR
    simp only [symState_regs_mk]
  cases hl : r.lookup x with
  | none => rfl
  | some p =>
    rcases p with ⟨oldV0, lty⟩
    rfl

theorem vcExprR_assign_deref_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {e rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.deref e) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e)
        fun b off lty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_assign_index_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {base idx rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.index base idx) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index base idx)
        fun b off lty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_assign_member_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {base : CExpr} {fld : String} {rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.member base fld) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member base fld)
        fun b off lty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_assign_arrow_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {base : CExpr} {fld : String} {rhs : CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.arrow base fld) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow base fld)
        fun b off lty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty K := by
  conv => lhs; unfold vcExprR

theorem vcExprR_call_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {fn : CExpr} {args : List CExpr} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.call fn args) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh fn
        fun fnV fnTy sFn mvFn mhFn =>
          match fnV, fnTy.unqual with
          | .fnPtr sym, .fnPtr rt ptys va =>
            match contracts sym with
            | none => False
            | some spec =>
              spec.sym = sym ∧
              rt = spec.retTy ∧
              ptys.map CTy.unqual = spec.paramTys.map CTy.unqual ∧
              va = spec.variadic ∧
              vcCallArgs prog cfg contracts baseEnv sFn mvFn mhFn args [] fun sArgs argVals =>
                match Sem.coerceCallArgs sArgs.mem spec.paramTys spec.variadic argVals with
                | some coerced =>
                  spec.pre sArgs.mem sArgs.os coerced ∧
                  ∀ rv m' os', spec.post sArgs.mem sArgs.os coerced rv m' os' →
                    K rv spec.retTy { sArgs with mem := m', os := os' } [] []
                | none => False
          | _, _ => False := by
  conv => lhs; unfold vcExprR
  rfl

theorem vcExprR_vaStart_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {ap lastParam : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.vaStart ap lastParam) K =
      (r.lookup ap = none ∧
       match stk.lookup ap with
       | some (b, ty) =>
         ty.isVaList = true ∧
         match m.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) (.byte 1)) with
         | some m' => K .void .void { regs := r, stack := stk, mem := m', os := os } mv mh
         | none => False
       | none =>
         match baseEnv.lookup ap with
         | some (b, ty) =>
           ty.isVaList = true ∧
           match m.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) (.byte 1)) with
           | some m' => K .void .void { regs := r, stack := stk, mem := m', os := os } mv mh
           | none => False
         | none => False) := by
  conv => lhs; unfold vcExprR
  rfl

theorem vcExprR_vaEnd_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {ap : String} {K} :
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.vaEnd ap) K =
      (r.lookup ap = none ∧
       match stk.lookup ap with
       | some (b, ty) =>
         ty.isVaList = true ∧
         match m.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) .undef) with
         | some m' => K .void .void { regs := r, stack := stk, mem := m', os := os } mv mh
         | none => False
       | none =>
         match baseEnv.lookup ap with
         | some (b, ty) =>
           ty.isVaList = true ∧
           match m.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) .undef) with
           | some m' => K .void .void { regs := r, stack := stk, mem := m', os := os } mv mh
           | none => False
         | none => False) := by
  conv => lhs; unfold vcExprR
  rfl

theorem vcCallArgs_nil_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh done K} :
    vcCallArgs prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh [] done K =
      K { regs := r, stack := stk, mem := m, os := os } done := by
  conv => lhs; unfold vcCallArgs

theorem vcCallArgs_cons_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {arg : CExpr} {rest : List CExpr} {done K} :
    vcCallArgs prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (arg :: rest) done K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh arg
        fun v ty s1 mv1 mh1 =>
          vcCallArgs prog cfg contracts baseEnv s1 mv1 mh1 rest (done ++ [(v, ty)]) K := by
  conv => lhs; unfold vcCallArgs

theorem vcExprDiscard_paren_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.paren e) K =
      vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e K := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_comma_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {l rhs : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.comma l rhs) K =
      vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun s1 _ _ => vcExprDiscard prog cfg contracts baseEnv s1 [] [] rhs K := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_cond_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {c t f : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.cond c t f) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh c
        fun vc _ s1 _ _ =>
          vcBranch vc (vcExprDiscard prog cfg contracts baseEnv s1 [] [] t K)
            (vcExprDiscard prog cfg contracts baseEnv s1 [] [] f K) := by
  conv => lhs; unfold vcExprDiscard

def vcDiscardVarCont (prog : Prog) (baseEnv : Env) (r : RegEnv) (stk : Env) (m : Mem) (os : OSState)
    (mv : List String) (mh : List (BlockId × Int64 × Nat)) (x : String)
    (K : SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | some (v, ty) =>
    isScalarPlaceTy ty ∧ x ∉ mv ∧ v ≠ .undef ∧
    K { regs := r, stack := stk, mem := m, os := os } mv mh
  | none =>
    let s := ({ regs := r, stack := stk, mem := m, os := os } : SymState)
    match stk.lookup x with
    | some (b, ty) => vcReadDiscardPlace prog s mv mh b 0 ty K
    | none =>
      match baseEnv.lookup x with
      | some (b, ty) => vcReadDiscardPlace prog s mv mh b 0 ty K
      | none =>
        match Sem.enumConst? prog.tags x with
        | some _ => K s mv mh
        | none =>
          match prog.fnProtos x with
          | some _ => K s mv mh
          | none => False

theorem vcDiscardVarCont_some {prog baseEnv r stk m os mv mh x K v ty} :
    vcDiscardVarCont prog baseEnv r stk m os mv mh x K (some (v, ty)) =
      (isScalarPlaceTy ty ∧ x ∉ mv ∧ v ≠ .undef ∧
       K { regs := r, stack := stk, mem := m, os := os } mv mh) := rfl

theorem vcDiscardVarCont_none {prog baseEnv r stk m os mv mh x K} :
    let s := ({ regs := r, stack := stk, mem := m, os := os } : SymState)
    vcDiscardVarCont prog baseEnv r stk m os mv mh x K none =
      (match stk.lookup x with
       | some (b, ty) => vcReadDiscardPlace prog s mv mh b 0 ty K
       | none =>
         match baseEnv.lookup x with
         | some (b, ty) => vcReadDiscardPlace prog s mv mh b 0 ty K
         | none =>
           match Sem.enumConst? prog.tags x with
           | some _ => K s mv mh
           | none =>
             match prog.fnProtos x with
             | some _ => K s mv mh
             | none => False) := rfl

theorem vcExprDiscard_var_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {x : String} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x) K =
      vcDiscardVarCont prog baseEnv r stk m os mv mh x K (r.lookup x) := by
  conv =>
    lhs
    unfold vcExprDiscard
    simp only [symState_regs_mk, symState_stack_mk]
  cases r.lookup x <;> rfl

theorem vcExprDiscard_deref_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {e : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr el, .ptr b off => vcReadDiscardPlace prog s1 mv1 mh1 b off el K
          | .fnPtr _ _ _, .fnPtr _ => K s1 mv1 mh1
          | _, _ => False := by
  conv => lhs; unfold vcExprDiscard
  rfl

theorem vcExprDiscard_index_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base idx : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index base idx) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
            match pty.unqual, Sem.valAsInt? iv with
            | .ptr el, some (_, idxInt) =>
              match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
              | some (.ptr b off) => vcReadDiscardPlace prog s2 mv2 mh2 b off el K
              | _ => False
            | _, _ => False := by
  conv => lhs; unfold vcExprDiscard
  rfl

theorem vcExprDiscard_member_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base : CExpr} {fld : String} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member base fld) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun b off sty s1 mv1 mh1 =>
          match fieldLayout? prog.tags sty fld with
          | some (foff, fty) => vcReadDiscardPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
          | none => False := by
  conv => lhs; unfold vcExprDiscard
  rfl

theorem vcExprDiscard_arrow_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh} {base : CExpr} {fld : String} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow base fld) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr sty, .ptr b off =>
            match fieldLayout? prog.tags sty fld with
            | some (foff, fty) => vcReadDiscardPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
            | none => False
          | _, _ => False := by
  conv => lhs; unfold vcExprDiscard
  rfl

def vcDiscardAssignStepCont (prog : Prog) (cfg : PointerConfig) (op : AssignOp) (x : String)
    (mv1 : List String) (mh1 : List (BlockId × Int64 × Nat)) (s1 : SymState)
    (lty : CTy) (rval : Val) (rty : CTy)
    (K : SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | none => False
  | some (oldV, lty1) =>
    lty1 = lty ∧
    match Sem.assignOpToBin? op with
    | none =>
      vcCast s1.mem lty rval fun cv _ =>
        ValScalarTyped lty cv ∧
        vcBindVal cv fun nv =>
          K { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os } (x :: mv1) mh1
    | some bop =>
      oldV ≠ .undef ∧
      vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
        vcCast s1.mem lty rawV fun cv _ =>
          ValScalarTyped lty cv ∧
          vcBindVal cv fun nv =>
            K { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os } (x :: mv1) mh1

theorem vcDiscardAssignStepCont_some {prog cfg op x mv1 mh1 s1 lty rval rty K oldV lty1} :
    vcDiscardAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K (some (oldV, lty1)) =
      (lty1 = lty ∧
       match Sem.assignOpToBin? op with
       | none =>
         vcCast s1.mem lty rval fun cv _ =>
           ValScalarTyped lty cv ∧
           vcBindVal cv fun nv =>
             K { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os } (x :: mv1) mh1
       | some bop =>
         oldV ≠ .undef ∧
         vcBinary cfg prog.tags s1.mem bop oldV lty rval rty fun rawV _ =>
           vcCast s1.mem lty rawV fun cv _ =>
             ValScalarTyped lty cv ∧
             vcBindVal cv fun nv =>
               K { regs := s1.regs.set x nv lty, stack := s1.stack, mem := s1.mem, os := s1.os }
                 (x :: mv1) mh1) := rfl

theorem vcDiscardAssignStepCont_none {prog cfg op x mv1 mh1 s1 lty rval rty K} :
    vcDiscardAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K none = False := rfl

def vcDiscardAssignVarCont (prog : Prog) (cfg : PointerConfig) (contracts : ContractEnv)
    (baseEnv : Env) (r : RegEnv) (stk : Env) (m : Mem) (os : OSState)
    (mv : List String) (mh : List (BlockId × Int64 × Nat)) (op : AssignOp) (x : String) (rhs : CExpr)
    (K : SymState → List String → List (BlockId × Int64 × Nat) → Prop) :
    Option (Val × CTy) → Prop
  | none =>
    vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x)
      fun b off lty s1 mv1 mh1 =>
        if isAggTy lty then
          op = .eq ∧
          vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
            vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
        else
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
            vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
  | some (_, lty) =>
    vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh rhs
      fun rval rty s1 mv1 mh1 =>
        x ∉ mv1 ∧ lty.isConst = false ∧
        vcDiscardAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K (s1.regs.lookup x)

theorem vcDiscardAssignVarCont_some {prog cfg contracts baseEnv r stk m os mv mh op x rhs K oldV0 lty} :
    vcDiscardAssignVarCont prog cfg contracts baseEnv r stk m os mv mh op x rhs K (some (oldV0, lty)) =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh rhs
        fun rval rty s1 mv1 mh1 =>
          x ∉ mv1 ∧ lty.isConst = false ∧
          vcDiscardAssignStepCont prog cfg op x mv1 mh1 s1 lty rval rty K (s1.regs.lookup x) := rfl

theorem vcDiscardAssignVarCont_none {prog cfg contracts baseEnv r stk m os mv mh op x rhs K} :
    vcDiscardAssignVarCont prog cfg contracts baseEnv r stk m os mv mh op x rhs K none =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x)
        fun b off lty s1 mv1 mh1 =>
          if isAggTy lty then
            op = .eq ∧
            vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
              vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
          else
            vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
              vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3 := rfl

theorem vcExprDiscard_assign_var_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {x : String} {rhs : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.var x) rhs) K =
      vcDiscardAssignVarCont prog cfg contracts baseEnv r stk m os mv mh op x rhs K (r.lookup x) := by
  conv =>
    lhs
    unfold vcExprDiscard
    simp only [symState_regs_mk]
  cases hl : r.lookup x with
  | none => rfl
  | some p => rcases p with ⟨_, _⟩; rfl

theorem vcExprDiscard_assign_deref_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {e rhs : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.deref e) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e)
        fun b off lty s1 mv1 mh1 =>
          if isAggTy lty then
            op = .eq ∧
            vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
              vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
          else
            vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
              vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_assign_index_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {base idx rhs : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.index base idx) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index base idx)
        fun b off lty s1 mv1 mh1 =>
          if isAggTy lty then
            op = .eq ∧
            vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
              vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
          else
            vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
              vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_assign_member_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {base : CExpr} {fld : String} {rhs : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.member base fld) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member base fld)
        fun b off lty s1 mv1 mh1 =>
          if isAggTy lty then
            op = .eq ∧
            vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
              vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
          else
            vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
              vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_assign_arrow_mk {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env}
    {r : RegEnv} {stk : Env} {m : Mem} {os : OSState} {mv mh}
    {op : AssignOp} {base : CExpr} {fld : String} {rhs : CExpr} {K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op (.arrow base fld) rhs) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow base fld)
        fun b off lty s1 mv1 mh1 =>
          if isAggTy lty then
            op = .eq ∧
            vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
              vcWriteAggPlace prog s2 mv2 mh2 b off lty bs fun _ _ s3 mv3 mh3 => K s3 mv3 mh3
          else
            vcExprR prog cfg contracts baseEnv s1 mv1 mh1 rhs fun rval rty s2 mv2 mh2 =>
              vcAssignPlaceFinish prog cfg op s2 mv2 mh2 b off lty rval rty fun _ _ s3 mv3 mh3 => K s3 mv3 mh3 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_lit_mk {prog cfg contracts baseEnv r stk m os mv mh val lk suf rad sym? K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.lit val lk suf rad sym?) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.lit val lk suf rad sym?) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_strLit_mk {prog cfg contracts baseEnv r stk m os mv mh str K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.strLit str) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.strLit str) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_sizeOfTy_mk {prog cfg contracts baseEnv r stk m os mv mh ty K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.sizeOfTy ty) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.sizeOfTy ty) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_sizeOfExpr_mk {prog cfg contracts baseEnv r stk m os mv mh e K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.sizeOfExpr e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.sizeOfExpr e) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_unary_mk {prog cfg contracts baseEnv r stk m os mv mh op e K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.unary op e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.unary op e) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_binary_mk {prog cfg contracts baseEnv r stk m os mv mh op l rhs K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.binary op l rhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.binary op l rhs) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_logAnd_mk {prog cfg contracts baseEnv r stk m os mv mh l rhs K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.logAnd l rhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.logAnd l rhs) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_logOr_mk {prog cfg contracts baseEnv r stk m os mv mh l rhs K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.logOr l rhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.logOr l rhs) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_cast_mk {prog cfg contracts baseEnv r stk m os mv mh target e K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.cast target e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.cast target e) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_addrOf_mk {prog cfg contracts baseEnv r stk m os mv mh l K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.addrOf l) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.addrOf l) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_incDec_mk {prog cfg contracts baseEnv r stk m os mv mh op lhs K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op lhs) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.incDec op lhs) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_call_mk {prog cfg contracts baseEnv r stk m os mv mh fn args K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.call fn args) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.call fn args) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_vaStart_mk {prog cfg contracts baseEnv r stk m os mv mh ap lp K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.vaStart ap lp) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.vaStart ap lp) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprDiscard_vaEnd_mk {prog cfg contracts baseEnv r stk m os mv mh ap K} :
    vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.vaEnd ap) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.vaEnd ap) fun _ _ s1 mv1 mh1 => K s1 mv1 mh1 := by
  conv => lhs; unfold vcExprDiscard

theorem vcExprAgg_paren_mk {prog cfg contracts baseEnv r stk m os mv mh e K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.paren e) K =
      vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e K := by
  conv => lhs; unfold vcExprAgg

theorem vcExprAgg_var_mk {prog cfg contracts baseEnv r stk m os mv mh x K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.var x) K =
      (r.lookup x = none ∧
       match stk.lookup x with
       | some (b, ty) => vcReadAggPlace prog { regs := r, stack := stk, mem := m, os := os } mv mh b 0 ty K
       | none =>
         match baseEnv.lookup x with
         | some (b, ty) => vcReadAggPlace prog { regs := r, stack := stk, mem := m, os := os } mv mh b 0 ty K
         | none => False) := by
  conv => lhs; unfold vcExprAgg
  rfl

theorem vcExprAgg_deref_mk {prog cfg contracts baseEnv r stk m os mv mh e K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.deref e) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh e
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr el, .ptr b off => vcReadAggPlace prog s1 mv1 mh1 b off el K
          | _, _ => False := by
  conv => lhs; unfold vcExprAgg
  rfl

theorem vcExprAgg_index_mk {prog cfg contracts baseEnv r stk m os mv mh base idx K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.index base idx) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          vcExprR prog cfg contracts baseEnv s1 mv1 mh1 idx fun iv _ s2 mv2 mh2 =>
            match pty.unqual, Sem.valAsInt? iv with
            | .ptr el, some (_, idxInt) =>
              match Sem.evalPtrAdd cfg prog.tags s2.mem p el idxInt with
              | some (.ptr b off) => vcReadAggPlace prog s2 mv2 mh2 b off el K
              | _ => False
            | _, _ => False := by
  conv => lhs; unfold vcExprAgg
  rfl

theorem vcExprAgg_member_mk {prog cfg contracts baseEnv r stk m os mv mh base fld K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.member base fld) K =
      vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun b off sty s1 mv1 mh1 =>
          match fieldLayout? prog.tags sty fld with
          | some (foff, fty) => vcReadAggPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
          | none => False := by
  conv => lhs; unfold vcExprAgg
  rfl

theorem vcExprAgg_arrow_mk {prog cfg contracts baseEnv r stk m os mv mh base fld K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.arrow base fld) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh base
        fun p pty s1 mv1 mh1 =>
          match pty.unqual, p with
          | .ptr sty, .ptr b off =>
            match fieldLayout? prog.tags sty fld with
            | some (foff, fty) => vcReadAggPlace prog s1 mv1 mh1 b (Int64.ofInt (off.toInt + foff)) fty K
            | none => False
          | _, _ => False := by
  conv => lhs; unfold vcExprAgg
  rfl

theorem vcExprAgg_cond_mk {prog cfg contracts baseEnv r stk m os mv mh c t f K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.cond c t f) K =
      vcExprR prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh c
        fun vc _ s1 _ _ =>
          vcBranch vc (vcExprAgg prog cfg contracts baseEnv s1 [] [] t K)
            (vcExprAgg prog cfg contracts baseEnv s1 [] [] f K) := by
  conv => lhs; unfold vcExprAgg

theorem vcExprAgg_comma_mk {prog cfg contracts baseEnv r stk m os mv mh l rhs K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh (.comma l rhs) K =
      vcExprDiscard prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh l
        fun s1 _ _ => vcExprAgg prog cfg contracts baseEnv s1 [] [] rhs K := by
  conv => lhs; unfold vcExprAgg

theorem vcExprAgg_assign_mk {prog cfg contracts baseEnv r stk m os mv mh op lhs rhs K} :
    vcExprAgg prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh
        (.assign op lhs rhs) K =
      if op == .eq then
        vcExprL prog cfg contracts baseEnv { regs := r, stack := stk, mem := m, os := os } mv mh lhs
          fun b off lty s1 mv1 mh1 =>
            vcExprAgg prog cfg contracts baseEnv s1 mv1 mh1 rhs fun bs _ s2 mv2 mh2 =>
              vcWriteAggPlace prog s2 mv2 mh2 b off lty bs K
      else False := by
  conv => lhs; unfold vcExprAgg

theorem vcSwitch_target_some {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {s1 : SymState} {iv : Int} {body tgt : AnnStmt}
    (htgt : AnnStmt.findSwitchAnnTarget iv body = some tgt)
    (herase : Sem.findSwitchTarget iv body.erase = some tgt.erase)
    (hbody : vcStmtGen strict prog cfg contracts baseEnv retTy { k with onBreak := k.normal } s1 tgt) :
    vcSwitchCont strict prog cfg contracts baseEnv retTy k s1 iv body
      (AnnStmt.findSwitchAnnTarget iv body) := by
  rw [htgt]; exact ⟨herase, hbody⟩

theorem vcSwitch_target_none {strict : Bool} {prog : Prog} {cfg : PointerConfig}
    {contracts : ContractEnv} {baseEnv : Env} {retTy : CTy} {k : ContPost}
    {s1 : SymState} {iv : Int} {body : AnnStmt}
    (htgt : AnnStmt.findSwitchAnnTarget iv body = none)
    (herase : Sem.findSwitchTarget iv body.erase = none)
    (hnorm : k.normal s1) :
    vcSwitchCont strict prog cfg contracts baseEnv retTy k s1 iv body
      (AnnStmt.findSwitchAnnTarget iv body) := by
  rw [htgt]; exact ⟨herase, hnorm⟩

theorem usualArith_u64_l (b : IntKind) : IntKind.usualArith .u64 b = .u64 := by cases b <;> rfl
theorem usualArith_u64_r (a : IntKind) : IntKind.usualArith a .u64 = .u64 := by cases a <;> rfl
theorem usualArith_i64_i64 : IntKind.usualArith .i64 .i64 = .i64 := rfl
theorem usualArith_i64_i32 : IntKind.usualArith .i64 .i32 = .i64 := rfl
theorem usualArith_i32_i64 : IntKind.usualArith .i32 .i64 = .i64 := rfl
theorem usualArith_i64_u32 : IntKind.usualArith .i64 .u32 = .i64 := rfl
theorem usualArith_u32_i64 : IntKind.usualArith .u32 .i64 = .i64 := rfl
theorem usualArith_u32_u32 : IntKind.usualArith .u32 .u32 = .u32 := rfl
theorem usualArith_u32_i32 : IntKind.usualArith .u32 .i32 = .u32 := rfl
theorem usualArith_i32_u32 : IntKind.usualArith .i32 .u32 = .u32 := rfl
theorem usualArith_i32_i32 : IntKind.usualArith .i32 .i32 = .i32 := rfl
theorem usualArith_i8_l (b : IntKind) : IntKind.usualArith .i8 b = IntKind.usualArith .i32 b := by cases b <;> rfl
theorem usualArith_i8_r (a : IntKind) : IntKind.usualArith a .i8 = IntKind.usualArith a .i32 := by cases a <;> rfl
theorem usualArith_u8_l (b : IntKind) : IntKind.usualArith .u8 b = IntKind.usualArith .i32 b := by cases b <;> rfl
theorem usualArith_u8_r (a : IntKind) : IntKind.usualArith a .u8 = IntKind.usualArith a .i32 := by cases a <;> rfl
theorem usualArith_i16_l (b : IntKind) : IntKind.usualArith .i16 b = IntKind.usualArith .i32 b := by cases b <;> rfl
theorem usualArith_i16_r (a : IntKind) : IntKind.usualArith a .i16 = IntKind.usualArith a .i32 := by cases a <;> rfl
theorem usualArith_u16_l (b : IntKind) : IntKind.usualArith .u16 b = IntKind.usualArith .i32 b := by cases b <;> rfl
theorem usualArith_u16_r (a : IntKind) : IntKind.usualArith a .u16 = IntKind.usualArith a .i32 := by cases a <;> rfl

theorem intKind?_int (k : IntKind) : CTy.intKind? (.int k) = some k := rfl
theorem intKind?_typedef (n : String) (t : CTy) : CTy.intKind? (.typedef n t) = t.intKind? := rfl
theorem intKind?_const (t : CTy) : CTy.intKind? (.const_ t) = t.intKind? := rfl
theorem intKind?_enum (tag : String) (isU : Bool) :
    CTy.intKind? (.enumTy tag isU) = some (if isU then .u32 else .i32) := rfl
theorem intKind?_ptr (t : CTy) : CTy.intKind? (.ptr t) = none := rfl
theorem intKind?_fnPtr (r : CTy) (ps : List CTy) (va : Bool) : CTy.intKind? (.fnPtr r ps va) = none := rfl
theorem intKind?_void : CTy.intKind? .void = none := rfl

theorem isVoid_void : CTy.isVoid .void = true := rfl
theorem isVoid_int (k : IntKind) : CTy.isVoid (.int k) = false := rfl
theorem isVoid_typedef (n : String) (t : CTy) : CTy.isVoid (.typedef n t) = t.isVoid := rfl
theorem isVoid_const (t : CTy) : CTy.isVoid (.const_ t) = t.isVoid := rfl
theorem isVoid_ptr (t : CTy) : CTy.isVoid (.ptr t) = false := rfl
theorem isVoid_enum (tag : String) (isU : Bool) : CTy.isVoid (.enumTy tag isU) = false := rfl
theorem isVoid_fnPtr (r : CTy) (ps : List CTy) (va : Bool) : CTy.isVoid (.fnPtr r ps va) = false := rfl

theorem isPtr_ptr (t : CTy) : CTy.isPtr (.ptr t) = true := rfl
theorem isPtr_typedef (n : String) (t : CTy) : CTy.isPtr (.typedef n t) = t.isPtr := rfl
theorem isPtr_const (t : CTy) : CTy.isPtr (.const_ t) = t.isPtr := rfl
theorem isPtr_int (k : IntKind) : CTy.isPtr (.int k) = false := rfl
theorem isPtr_enum (tag : String) (isU : Bool) : CTy.isPtr (.enumTy tag isU) = false := rfl
theorem isPtr_fnPtr (r : CTy) (ps : List CTy) (va : Bool) : CTy.isPtr (.fnPtr r ps va) = false := rfl
theorem isPtr_void : CTy.isPtr .void = false := rfl

theorem isFnCTy_fnPtr (r : CTy) (ps : List CTy) (va : Bool) : isFnCTy (.fnPtr r ps va) = true := rfl
theorem isFnCTy_typedef (n : String) (t : CTy) : isFnCTy (.typedef n t) = isFnCTy t := rfl
theorem isFnCTy_const (t : CTy) : isFnCTy (.const_ t) = isFnCTy t := rfl
theorem isFnCTy_ptr (t : CTy) : isFnCTy (.ptr t) = false := rfl
theorem isFnCTy_int (k : IntKind) : isFnCTy (.int k) = false := rfl
theorem isFnCTy_enum (tag : String) (isU : Bool) : isFnCTy (.enumTy tag isU) = false := rfl
theorem isFnCTy_void : isFnCTy .void = false := rfl

theorem isScalarPlaceTy_int (k : IntKind) : isScalarPlaceTy (.int k) = true := rfl
theorem isScalarPlaceTy_typedef (n : String) (t : CTy) : isScalarPlaceTy (.typedef n t) = isScalarPlaceTy t := rfl
theorem isScalarPlaceTy_const (t : CTy) : isScalarPlaceTy (.const_ t) = isScalarPlaceTy t := rfl
theorem isScalarPlaceTy_ptr (t : CTy) : isScalarPlaceTy (.ptr t) = true := rfl
theorem isScalarPlaceTy_enum (tag : String) (isU : Bool) : isScalarPlaceTy (.enumTy tag isU) = true := rfl
theorem isScalarPlaceTy_fnPtr (r : CTy) (ps : List CTy) (va : Bool) :
    isScalarPlaceTy (.fnPtr r ps va) = true := rfl
theorem isScalarPlaceTy_vaList : isScalarPlaceTy .vaList = true := rfl

end ConcreteVC

macro "vc_unfold" : tactic => `(tactic| (
  try dsimp only [List.zip, List.zipWith, List.reverse, List.reverseAux, List.map]
  try simp only [
    SpecEnv.toContracts_apply, SafeSpecEnv.toContracts_apply, SafeSpecEnv.toTermSpecs_apply,
    vcStmt_eq_vcStmtGen, vcStmtList_eq_vcStmtListGen,
    vcStmtSafe_eq_vcStmtGen, vcStmtSafeList_eq_vcStmtListGen,
    symState_regs_mk, symState_stack_mk, symState_mem_mk, symState_os_mk, symState_exitBlock_mk,
    SymState.exitFn_of_stack_nil, freeStack_nil,
    contPost_normal_mk, contPost_onBreak_mk, contPost_onContinue_mk, contPost_onReturn_mk, contPost_onGoto_mk,
    vcDeclList_nil_mk, vcDeclList_static_mk, vcDeclList_reg_none_mk, vcDeclList_reg_expr_mk,
    vcDeclList_stk_none_mk, vcDeclList_stk_expr_mk,
    vcStmtListGen_nil_mk, vcStmtListGen_singleton_mk, vcStmtListGen_cons_mk,
    vcStmtGen_nop_mk, vcStmtGen_expr_mk,
    vcStmtGen_decl_mk, vcStmtGen_decls_mk, vcStmtGen_stackDecl_mk, vcStmtGen_stackDecls_mk, vcStmtGen_mixedDecls_mk,
    vcStmtGen_block_nil_mk, vcStmtGen_block_cons_mk,
    vcStmtGen_ifStmt_none_mk, vcStmtGen_ifStmt_some_mk,
    vcStmtGen_ifJoin_none_mk, vcStmtGen_ifJoin_some_mk,
    vcStmtGen_whileLoop_mk, vcStmtGen_doWhileLoop_mk, vcStmtGen_doWhileGotos_mk, vcStmtGen_forLoop_mk,
    vcStmtGen_switchStmt_mk, vcStmtGen_caseStmt_mk, vcStmtGen_defaultStmt_mk,
    vcStmtGen_labelStmt_mk, vcStmtGen_gotoStmt_mk,
    vcStmtGen_breakStmt_mk, vcStmtGen_continueStmt_mk,
    vcStmtGen_returnStmt_none_mk, vcStmtGen_returnStmt_some_mk
  ]
  try simp only [
    vcExprL_paren_mk, vcExprL_var_mk, vcExprL_deref_mk, vcExprL_index_mk, vcExprL_member_mk, vcExprL_arrow_mk,
    vcExprR_paren_mk, vcExprR_lit_mk, vcExprR_strLit_mk, vcExprR_sizeOfTy_mk, vcExprR_sizeOfExpr_mk,
    vcExprR_var_mk, vcVarCont_some, vcVarCont_none,
    vcExprR_unary_mk, vcExprR_cast_mk, vcExprR_binary_mk,
    vcExprR_logAnd_mk, vcExprR_logOr_mk, vcExprR_cond_mk, vcExprR_comma_mk,
    vcExprR_addrOf_mk, vcExprR_deref_mk, vcExprR_index_mk, vcExprR_member_mk, vcExprR_arrow_mk,
    vcExprR_incDec_var_mk, vcIncDecVarCont_some, vcIncDecVarCont_none,
    vcExprR_incDec_deref_mk, vcExprR_incDec_index_mk, vcExprR_incDec_member_mk, vcExprR_incDec_arrow_mk,
    vcExprR_assign_var_mk, vcAssignVarCont_some, vcAssignVarCont_none,
    vcAssignStepCont_some, vcAssignStepCont_none,
    vcExprR_assign_deref_mk, vcExprR_assign_index_mk, vcExprR_assign_member_mk, vcExprR_assign_arrow_mk,
    vcExprR_call_mk, vcExprR_vaStart_mk, vcExprR_vaEnd_mk,
    vcCallArgs_nil_mk, vcCallArgs_cons_mk,
    vcExprDiscard_paren_mk, vcExprDiscard_comma_mk, vcExprDiscard_cond_mk,
    vcExprDiscard_var_mk, vcDiscardVarCont_some, vcDiscardVarCont_none,
    vcExprDiscard_deref_mk, vcExprDiscard_index_mk, vcExprDiscard_member_mk, vcExprDiscard_arrow_mk,
    vcExprDiscard_assign_var_mk, vcDiscardAssignVarCont_some, vcDiscardAssignVarCont_none,
    vcDiscardAssignStepCont_some, vcDiscardAssignStepCont_none,
    vcExprDiscard_assign_deref_mk, vcExprDiscard_assign_index_mk,
    vcExprDiscard_assign_member_mk, vcExprDiscard_assign_arrow_mk,
    vcExprDiscard_lit_mk, vcExprDiscard_strLit_mk, vcExprDiscard_sizeOfTy_mk, vcExprDiscard_sizeOfExpr_mk,
    vcExprDiscard_unary_mk, vcExprDiscard_binary_mk, vcExprDiscard_logAnd_mk, vcExprDiscard_logOr_mk,
    vcExprDiscard_cast_mk, vcExprDiscard_addrOf_mk, vcExprDiscard_incDec_mk,
    vcExprDiscard_call_mk, vcExprDiscard_vaStart_mk, vcExprDiscard_vaEnd_mk,
    vcExprAgg_paren_mk, vcExprAgg_var_mk, vcExprAgg_deref_mk, vcExprAgg_index_mk,
    vcExprAgg_member_mk, vcExprAgg_arrow_mk, vcExprAgg_cond_mk, vcExprAgg_comma_mk, vcExprAgg_assign_mk
  ]
  try simp only [
    AnnStmt.ofCStmt, AnnStmt.ofCStmtList, AnnStmt.annHasLabel, AnnStmt.annHasLabelList,
    vcBranch_int, vcBranch_ptr, vcBranch_null, vcBranch_fnPtr,
    vcUnary_int_mk, vcUnary_ptr_logNot, vcUnary_null_logNot, vcUnary_fnPtr_logNot,
    vcUnBody_i32, vcUnBody_u32, vcUnBody_i64, vcUnBody_u64,
    vcCast_int, vcCast_null, vcCast_ptr, vcCast_fnPtr, vcPureCast?,
    vcBinary_int_mk, vcBinaryIntCont_some, intKind_beq_eq_decide, bv_ofInt_valIntNum,
    vcArithBody_i32, vcArithBody_u32, vcArithBody_i64, vcArithBody_u64,
    vcShiftBody_i32, vcShiftBody_u32, vcShiftBody_i64, vcShiftBody_u64,
    binOp_beq_shl, binOp_beq_shr, binOp_beq_eq, binOp_beq_ne,
    vcBinary_ptr_ptr_eq, vcBinary_ptr_ptr_ne, vcBinary_ptr_null_eq, vcBinary_ptr_null_ne,
    vcBinary_null_ptr_eq, vcBinary_null_ptr_ne, vcBinary_fnPtr_null_eq, vcBinary_fnPtr_null_ne,
    vcBinary_null_null_eq, vcBinary_null_null_ne, vcBinary_ptr_add_int,
    vcBinary_ptr_zero_eq, vcBinary_ptr_zero_ne, vcBinary_null_zero_eq, vcBinary_null_zero_ne,
    vcBinary_fnPtr_zero_eq, vcBinary_fnPtr_zero_ne, bv_ofInt_zero, bv_toNat_zero,
    vcBindVal_int, vcBindVal_ptr, vcBindVal_null, vcBindVal_fnPtr,
    vcReadHeapPlace, vcReadDiscardPlace, vcReadAggPlace,
    vcAssignPlaceFinish, vcWriteAggPlace, vcIncDecPlaceFinish,
    isAggTy, isNonAggRvalTy,
    isScalarPlaceTy_int, isScalarPlaceTy_typedef, isScalarPlaceTy_const,
    isScalarPlaceTy_ptr, isScalarPlaceTy_enum, isScalarPlaceTy_fnPtr, isScalarPlaceTy_vaList,
    isFnCTy_fnPtr, isFnCTy_typedef, isFnCTy_const, isFnCTy_ptr, isFnCTy_int, isFnCTy_enum, isFnCTy_void,
    promote_i8, promote_u8, promote_i16, promote_u16, promote_i32, promote_u32, promote_i64, promote_u64,
    usualArith_u64_l, usualArith_u64_r, usualArith_i64_i64, usualArith_i64_i32, usualArith_i32_i64,
    usualArith_i64_u32, usualArith_u32_i64, usualArith_u32_u32, usualArith_u32_i32, usualArith_i32_u32,
    usualArith_i32_i32, usualArith_i8_l, usualArith_i8_r, usualArith_u8_l, usualArith_u8_r,
    usualArith_i16_l, usualArith_i16_r, usualArith_u16_l, usualArith_u16_r,
    intKind?_int, intKind?_typedef, intKind?_const, intKind?_enum, intKind?_ptr, intKind?_fnPtr, intKind?_void,
    isVoid_void, isVoid_int, isVoid_typedef, isVoid_const, isVoid_ptr, isVoid_enum, isVoid_fnPtr,
    isPtr_ptr, isPtr_typedef, isPtr_const, isPtr_int, isPtr_enum, isPtr_fnPtr, isPtr_void,
    ofIntCast_valIntNum, valIntNum, Sem.valAsInt?, Sem.ofIntCast, Sem.assignOpToBin?, Sem.cmpOrd,
    CTy.decay, CTy.unqual, CTy.stripConst, CTy.isConst, CTy.isVaList,
    IntKind.bytes, IntKind.align, IntKind.signed, IntKind.inRange,
    RegEnv.lookup_nil, RegEnv.lookup_cons, RegEnv.set_cons, regEnv_set_nil,
    list_lookup_nil, list_lookup_cons,
    string_beq_eq_decide, String.reduceEq,
    decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false,
    Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true,
    Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
    Bool.not_true, Bool.not_false, ↓reduceIte, beq_self_eq_true, and_true, true_and
  ]
  try simp only [
    val_int_ne_undef, val_ptr_ne_undef, val_null_ne_undef, val_fnPtr_ne_undef,
    List.length_nil, List.length_cons, List.drop_zero, List.drop_succ_cons,
    List.take_zero, List.take_nil,
    List.not_mem_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    not_false_eq_true, false_implies, true_implies, implies_true, forall_const,
    ite_one_zero_ne_zero, bv32_ne_zero_iff, bitVec_ofInt_toNat, bitVec_ofInt_toInt, bv64_ofNat_toNat, bv_toInt_zero,
    decide_true, decide_false, exists_eq',
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceLT, Nat.sub_zero,
    Int.reduceAdd, Int.reduceSub, Int.reduceMul, Int.reduceMod, Int.reduceNeg,
    Int.reduceLT, Int.reduceLE,
    Bool.and_eq_true, Bool.or_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true,
    Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
    Bool.not_true, Bool.not_false,
    ↓reduceIte, beq_self_eq_true, and_true, true_and,
    Option.map_some, Option.map_none
  ]))

macro "vc_leaf" : tactic => `(tactic|
  first | trivial | rfl | decide | omega | bv_omega | grind)

end C99.Proof.VCGen
