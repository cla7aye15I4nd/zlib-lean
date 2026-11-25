import Lean
import C99.Proof.Mem
import C99.Proof.WP

/-!
# Automated Symbolic Stepper, Pure Evaluator, and Auto-Framing (`C99.Proof.AutoWP`)

Zero-kernel-extension tactic and lemma library over `C99.Proof.WP`:
- Safety-abstracted predicates (`AnyInt`, `IntRange`, `PtrValid`, `PtrWritable`, `Slot`, `Field`,
  `FrameBlocks`)
- Fast `simp only` / `BitVec.eq_of_toNat_eq` / `BitVec.ofInt_toInt` scalar and expression lemmas
- Preservation/framing lemmas across `writeVal`, `writeBytes`, `writePlace`, `alloc`, `freeStack`,
  `ROExt`, and `FrameBlocks`
- Deterministic single-step (`c_step`), pure expression (`c_eval`), context framing (`c_frame`),
  and bounded straight-line execution (`c_run`) tactics
- Built-in smoke tests (`private theorem`) verifying safety and termination of synthetic C ASTs
-/

namespace C99.Proof

open C99 C99.Sem

/-! ## 1. Safety-Abstracted Predicates & Uniform Memory/Slot Representation -/

/-- Mathematical integer denoted by a C runtime `BitVec k.bits` under `IntKind` signedness. -/
def intToInt (k : IntKind) (bv : BitVec k.bits) : Int :=
  if k.signed then bv.toInt else (bv.toNat : Int)

/-- Value holds any integer of `IntKind` `k`. -/
def AnyInt (k : IntKind) (v : Val) : Prop :=
  ∃ bv : BitVec k.bits, v = .int k bv

/-- Value holds an integer of `IntKind` `k` whose mathematical value lies in `[lo, hi]`. -/
def IntRange (k : IntKind) (lo hi : Int) (v : Val) : Prop :=
  ∃ bv : BitVec k.bits, v = .int k bv ∧ lo ≤ intToInt k bv ∧ intToInt k bv ≤ hi

/-- Pointer `p` points within an allocated block in `m` with at least `len` readable bytes. -/
def PtrValid (m : Mem) (p : Val) (len : Nat) : Prop :=
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ Mem.inBounds blk off len = true

/-- Pointer `p` points within an allocated `.rw` block in `m` with at least `len` writable bytes. -/
def PtrWritable (m : Mem) (p : Val) (len : Nat) : Prop :=
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.inBounds blk off len = true

/-- Pointer `p` is aligned to `al` bytes in `m`. -/
def PtrAligned (m : Mem) (p : Val) (al : Nat) : Prop :=
  ∃ b off blk, p = .ptr b off ∧ m.blocks b = some blk ∧ Mem.isAligned blk off al = true

/-- Set of block identifiers permitted to be modified or stack-allocated across a frame. -/
def AutoBlockSet : Type := BlockId → Prop

namespace AutoBlockSet

instance : Membership BlockId AutoBlockSet where
  mem s b := s b

def empty : AutoBlockSet := fun _ => False
def singleton (b : BlockId) : AutoBlockSet := fun x => x = b
def insert (b : BlockId) (s : AutoBlockSet) : AutoBlockSet := fun x => x = b ∨ s x
def union (s1 s2 : AutoBlockSet) : AutoBlockSet := fun x => s1 x ∨ s2 x
def ofList (bs : List BlockId) : AutoBlockSet := fun x => x ∈ bs

instance : EmptyCollection AutoBlockSet := ⟨empty⟩
instance : Singleton BlockId AutoBlockSet := ⟨singleton⟩
instance : Insert BlockId AutoBlockSet := ⟨insert⟩
instance : Union AutoBlockSet := ⟨union⟩

@[simp] theorem mem_empty (b : BlockId) : b ∈ (∅ : AutoBlockSet) ↔ False := Iff.rfl
@[simp] theorem mem_singleton (a b : BlockId) : b ∈ ({a} : AutoBlockSet) ↔ b = a := Iff.rfl
@[simp] theorem mem_singleton_fn (a b : BlockId) : b ∈ singleton a ↔ b = a := Iff.rfl
@[simp] theorem mem_insert (a b : BlockId) (s : AutoBlockSet) : b ∈ insert a s ↔ b = a ∨ b ∈ s := Iff.rfl
@[simp] theorem mem_union (b : BlockId) (s1 s2 : AutoBlockSet) : b ∈ s1 ∪ s2 ↔ b ∈ s1 ∨ b ∈ s2 := Iff.rfl
@[simp] theorem mem_ofList (b : BlockId) (bs : List BlockId) : b ∈ ofList bs ↔ b ∈ bs := Iff.rfl

theorem union_self (s : AutoBlockSet) : s ∪ s = s := by
  funext x
  exact propext or_self_iff

end AutoBlockSet

/-- Frame invariant across a memory transition `m ↦ m'`:
`m.nextBlock ≤ m'.nextBlock`, pre-existing blocks outside `allowed` are byte-identical,
and newly allocated blocks outside `allowed` are read-only globals (e.g. string literals). -/
def FrameBlocks (m m' : Mem) (allowed : AutoBlockSet) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧
  (∀ b, b < m.nextBlock → b ∉ allowed → m'.blocks b = m.blocks b) ∧
  (∀ b blk, m.nextBlock ≤ b → b ∉ allowed → m'.blocks b = some blk →
    blk.kind = .global ∧ blk.perm = .ro)

/-- Scalar byte size and alignment independent of `TypeEnv`. -/
def scalarSizeAlign (ty : CTy) : Nat × Nat :=
  match ty.unqual with
  | .int k => (k.bytes, k.align)
  | .enumTy _ isU => let k := if isU then IntKind.u32 else IntKind.i32; (k.bytes, k.align)
  | .ptr _ | .fnPtr _ _ _ => (8, 8)
  | .vaList => (24, 8)
  | _ => (1, 1)

/-- Local variable slot in `env` and `m` at block `b` of type `ty`, holding either an
initialized value satisfying `P` or `.undef` when `P .undef` holds. -/
def Slot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty : CTy) (P : Val → Prop) : Prop :=
  env.lookup name = some (b, ty) ∧
  ∃ blk, m.blocks b = some blk ∧
    (ty.isConst = false → blk.perm = .rw) ∧
    Mem.inBounds blk 0 (scalarSizeAlign ty).1 = true ∧
    Mem.isAligned blk 0 (scalarSizeAlign ty).2 = true ∧
    ((∃ v, Sem.readVal [] m b 0 ty = some v ∧ P v) ∨ P .undef)

abbrev Slot.int_any (env : Env) (m : Mem) (name : String) (b : BlockId) (k : IntKind) : Prop :=
  Slot env m name b (.int k) (AnyInt k)

abbrev Slot.int_eq (env : Env) (m : Mem) (name : String) (b : BlockId) (k : IntKind)
    (bv : BitVec k.bits) : Prop :=
  Slot env m name b (.int k) (· = .int k bv)

abbrev Slot.int_range (env : Env) (m : Mem) (name : String) (b : BlockId) (k : IntKind)
    (lo hi : Int) : Prop :=
  Slot env m name b (.int k) (IntRange k lo hi)

abbrev Slot.ptr (env : Env) (m : Mem) (name : String) (b : BlockId) (to : CTy)
    (P : Val → Prop) : Prop :=
  Slot env m name b (.ptr to) P

abbrev Slot.ptr_eq (env : Env) (m : Mem) (name : String) (b : BlockId) (to : CTy)
    (p : Val) : Prop :=
  Slot env m name b (.ptr to) (· = p)

abbrev Slot.ptr_valid (env : Env) (m : Mem) (name : String) (b : BlockId) (to : CTy)
    (len : Nat) : Prop :=
  Slot env m name b (.ptr to) (PtrValid m · len)

abbrev Slot.ptr_writable (env : Env) (m : Mem) (name : String) (b : BlockId) (to : CTy)
    (len : Nat) : Prop :=
  Slot env m name b (.ptr to) (PtrWritable m · len)

abbrev Slot.uninit (env : Env) (m : Mem) (name : String) (b : BlockId) (ty : CTy) : Prop :=
  Slot env m name b ty (· = .undef)

/-- Struct field at `b` + `off` + `fieldLayout? tags (.structTy structTag) fld` holding a value
satisfying `P` (or `.undef` when `P .undef` holds). -/
def Field (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (fty : CTy) (P : Val → Prop) : Prop :=
  ∃ foff blk,
    fieldLayout? tags (.structTy structTag) fld = some (foff, fty) ∧
    m.blocks b = some blk ∧
    (fty.isConst = false → blk.perm = .rw) ∧
    0 ≤ off.toInt ∧ off.toInt + foff + sizeofTy tags fty ≤ blk.size ∧
    Mem.isAligned blk (Int64.ofInt (off.toInt + foff)) (max 1 (alignofTy tags fty)) = true ∧
    ((∃ v, Sem.readVal tags m b (Int64.ofInt (off.toInt + foff)) fty = some v ∧ P v) ∨ P .undef)

abbrev Field.int_any (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (k : IntKind) : Prop :=
  Field tags m b off structTag fld (.int k) (AnyInt k)

abbrev Field.int_eq (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (k : IntKind) (bv : BitVec k.bits) : Prop :=
  Field tags m b off structTag fld (.int k) (· = .int k bv)

abbrev Field.int_range (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (k : IntKind) (lo hi : Int) : Prop :=
  Field tags m b off structTag fld (.int k) (IntRange k lo hi)

abbrev Field.ptr (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (to : CTy) (P : Val → Prop) : Prop :=
  Field tags m b off structTag fld (.ptr to) P

abbrev Field.uninit (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (fty : CTy) : Prop :=
  Field tags m b off structTag fld fty (· = .undef)

/-! ## 2. Basic Predicate & Scalar Arithmetic Lemmas -/

@[simp] theorem cty_unqual_idem : ∀ ty : CTy, ty.unqual.unqual = ty.unqual
  | .const_ t => cty_unqual_idem t
  | .typedef _ t => cty_unqual_idem t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .enumTy _ _ | .anonStruct _ | .anonUnion _ | .fnPtr _ _ _ | .vaList => rfl

theorem intKind?_unqual_cases {ty : CTy} {ik : IntKind} (h : ty.intKind? = some ik) :
    ty.unqual = .int ik ∨ ∃ tag isU, ty.unqual = .enumTy tag isU ∧ (if isU then IntKind.u32 else .i32) = ik := by
  unfold CTy.intKind? at h
  cases hu : ty.unqual <;> rw [hu] at h <;> cases h
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl, rfl⟩

@[simp] theorem intToInt_zero (k : IntKind) : intToInt k 0 = 0 := by
  cases k <;> rfl

@[simp] theorem intToInt_ofInt_zero (k : IntKind) :
    intToInt k (BitVec.ofInt k.bits 0) = 0 := by
  cases k <;> rfl

@[simp] theorem intToInt_ofInt_zero_u8  : intToInt .u8  (BitVec.ofInt 8  0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_i8  : intToInt .i8  (BitVec.ofInt 8  0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_u16 : intToInt .u16 (BitVec.ofInt 16 0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_i16 : intToInt .i16 (BitVec.ofInt 16 0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_u32 : intToInt .u32 (BitVec.ofInt 32 0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_i32 : intToInt .i32 (BitVec.ofInt 32 0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_u64 : intToInt .u64 (BitVec.ofInt 64 0) = 0 := rfl
@[simp] theorem intToInt_ofInt_zero_i64 : intToInt .i64 (BitVec.ofInt 64 0) = 0 := rfl

@[simp] theorem alignUp_zero (a : Nat) : alignUp 0 a = 0 := by
  unfold alignUp
  split
  · rfl
  · simp [Nat.div_eq_of_lt (by omega : a - 1 < a)]

theorem intToInt_bounds (k : IntKind) (bv : BitVec k.bits) :
    k.minVal ≤ intToInt k bv ∧ intToInt k bv ≤ k.maxVal := by
  cases k <;> simp only [intToInt, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
    Bool.false_eq_true, ↓reduceIte]
  · have h1 := BitVec.le_toInt (x := bv); have h2 := BitVec.toInt_lt (x := bv)
    simp only [IntKind.bits] at h1 h2; omega
  · have hlt : bv.toNat < 2 ^ 8 := bv.isLt; omega
  · have h1 := BitVec.le_toInt (x := bv); have h2 := BitVec.toInt_lt (x := bv)
    simp only [IntKind.bits] at h1 h2; omega
  · have hlt : bv.toNat < 2 ^ 16 := bv.isLt; omega
  · have h1 := BitVec.le_toInt (x := bv); have h2 := BitVec.toInt_lt (x := bv)
    simp only [IntKind.bits] at h1 h2; omega
  · have hlt : bv.toNat < 2 ^ 32 := bv.isLt; omega
  · have h1 := BitVec.le_toInt (x := bv); have h2 := BitVec.toInt_lt (x := bv)
    simp only [IntKind.bits] at h1 h2; omega
  · have hlt : bv.toNat < 2 ^ 64 := bv.isLt; omega

theorem intToInt_ofInt_eq {k : IntKind} {x : Int}
    (hlo : k.minVal ≤ x) (hhi : x ≤ k.maxVal) :
    intToInt k (BitVec.ofInt k.bits x) = x := by
  cases k <;> simp only [intToInt, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
    Bool.false_eq_true, ↓reduceIte] at *
  · rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  · rw [BitVec.toNat_ofInt]
    have hmod : x % (2 ^ 8 : Nat) = x := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]; omega
  · rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  · rw [BitVec.toNat_ofInt]
    have hmod : x % (2 ^ 16 : Nat) = x := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]; omega
  · rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  · rw [BitVec.toNat_ofInt]
    have hmod : x % (2 ^ 32 : Nat) = x := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]; omega
  · rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  · rw [BitVec.toNat_ofInt]
    have hmod : x % (2 ^ 64 : Nat) = x := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod]; omega

theorem ofInt_intToInt (k : IntKind) (bv : BitVec k.bits) :
    BitVec.ofInt k.bits (intToInt k bv) = bv := by
  unfold intToInt
  cases hs : k.signed
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    have hlt := bv.isLt
    have hmod : (bv.toNat : Int) % (2 ^ k.bits : Nat) = (bv.toNat : Int) :=
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlt)
    rw [hmod]
    rfl
  · simp only [↓reduceIte, BitVec.ofInt_toInt]

theorem eq_of_intToInt_eq {k : IntKind} {bv1 bv2 : BitVec k.bits}
    (h : intToInt k bv1 = intToInt k bv2) : bv1 = bv2 := by
  have h1 := ofInt_intToInt k bv1
  have h2 := ofInt_intToInt k bv2
  rw [← h1, ← h2, h]

theorem intToInt_eq_zero_iff {k : IntKind} {bv : BitVec k.bits} :
    intToInt k bv = 0 ↔ bv = 0 := by
  constructor
  · intro h
    apply eq_of_intToInt_eq
    rw [intToInt_zero]
    exact h
  · rintro rfl
    exact intToInt_zero k

@[simp] theorem not_AnyInt_undef (k : IntKind) : ¬ AnyInt k .undef := by
  rintro ⟨_, h⟩; cases h

@[simp] theorem not_IntRange_undef (k : IntKind) (lo hi : Int) : ¬ IntRange k lo hi .undef := by
  rintro ⟨_, h, _⟩; cases h

@[simp] theorem not_PtrValid_undef (m : Mem) (len : Nat) : ¬ PtrValid m .undef len := by
  rintro ⟨_, _, _, h, _⟩; cases h

@[simp] theorem not_PtrWritable_undef (m : Mem) (len : Nat) : ¬ PtrWritable m .undef len := by
  rintro ⟨_, _, _, h, _⟩; cases h

@[simp] theorem not_PtrAligned_undef (m : Mem) (al : Nat) : ¬ PtrAligned m .undef al := by
  rintro ⟨_, _, _, h, _⟩; cases h

@[simp] theorem not_eq_int_undef (k : IntKind) (bv : BitVec k.bits) :
    ¬ (Val.undef = .int k bv) := by intro h; cases h

@[simp] theorem not_eq_ptr_undef (b : BlockId) (off : Int64) :
    ¬ (Val.undef = .ptr b off) := by intro h; cases h

@[simp] theorem not_eq_null_undef : ¬ (Val.undef = .null) := by intro h; cases h

@[simp] theorem not_eq_fnPtr_undef (s : SymId) : ¬ (Val.undef = .fnPtr s) := by intro h; cases h

theorem AnyInt.of_int (k : IntKind) (bv : BitVec k.bits) : AnyInt k (.int k bv) := ⟨bv, rfl⟩

theorem IntRange.of_int {k : IntKind} {lo hi : Int} (bv : BitVec k.bits)
    (hlo : lo ≤ intToInt k bv) (hhi : intToInt k bv ≤ hi) :
    IntRange k lo hi (.int k bv) := ⟨bv, rfl, hlo, hhi⟩

theorem IntRange.mono {k : IntKind} {lo lo' hi hi' : Int} {v : Val}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hr : IntRange k lo hi v) :
    IntRange k lo' hi' v := by
  rcases hr with ⟨bv, rfl, hl, hh⟩
  exact ⟨bv, rfl, Int.le_trans hlo hl, Int.le_trans hh hhi⟩

theorem IntRange.toAnyInt {k : IntKind} {lo hi : Int} {v : Val}
    (hr : IntRange k lo hi v) : AnyInt k v := by
  rcases hr with ⟨bv, rfl, _⟩
  exact ⟨bv, rfl⟩

theorem AnyInt.toIntRange {k : IntKind} {v : Val} (ha : AnyInt k v) :
    IntRange k k.minVal k.maxVal v := by
  rcases ha with ⟨bv, rfl⟩
  have hb := intToInt_bounds k bv
  exact ⟨bv, rfl, hb.1, hb.2⟩

theorem PtrWritable.toValid {m : Mem} {p : Val} {len : Nat}
    (hw : PtrWritable m p len) : PtrValid m p len := by
  rcases hw with ⟨b, off, blk, rfl, hb, _, hin⟩
  exact ⟨b, off, blk, rfl, hb, hin⟩

theorem PtrValid.mono {m : Mem} {p : Val} {len len' : Nat}
    (hle : len' ≤ len) (hv : PtrValid m p len) : PtrValid m p len' := by
  rcases hv with ⟨b, off, blk, rfl, hb, hin⟩
  exact ⟨b, off, blk, rfl, hb, inBounds_mono hin hle⟩

theorem PtrWritable.mono {m : Mem} {p : Val} {len len' : Nat}
    (hle : len' ≤ len) (hw : PtrWritable m p len) : PtrWritable m p len' := by
  rcases hw with ⟨b, off, blk, rfl, hb, hp, hin⟩
  exact ⟨b, off, blk, rfl, hb, hp, inBounds_mono hin hle⟩

theorem PtrValid.of_add {m : Mem} {b : BlockId} {off : Int64} {len k len' : Nat}
    (hv : PtrValid m (.ptr b off) len) (hle : k + len' ≤ len) :
    PtrValid m (.ptr b (Int64.ofInt (off.toInt + k))) len' := by
  rcases hv with ⟨b0, off0, blk, hpeq, hb, hin⟩
  cases hpeq
  exact ⟨b, Int64.ofInt (off.toInt + k), blk, rfl, hb, inBounds_add hin hle⟩

theorem PtrWritable.of_add {m : Mem} {b : BlockId} {off : Int64} {len k len' : Nat}
    (hw : PtrWritable m (.ptr b off) len) (hle : k + len' ≤ len) :
    PtrWritable m (.ptr b (Int64.ofInt (off.toInt + k))) len' := by
  rcases hw with ⟨b0, off0, blk, hpeq, hb, hp, hin⟩
  cases hpeq
  exact ⟨b, Int64.ofInt (off.toInt + k), blk, rfl, hb, hp, inBounds_add hin hle⟩

theorem Slot.mono {env : Env} {m : Mem} {name : String} {b : BlockId} {ty : CTy}
    {P P' : Val → Prop} (hm : ∀ v, P v → P' v) (hs : Slot env m name b ty P) :
    Slot env m name b ty P' := by
  rcases hs with ⟨hl, blk, hb, hp, hin, hal, hval⟩
  refine ⟨hl, blk, hb, hp, hin, hal, ?_⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · exact Or.inl ⟨v, hrd, hm v hpv⟩
  · exact Or.inr (hm .undef hundef)

theorem Slot.to_int_any {env : Env} {m : Mem} {name : String} {b : BlockId} {ty : CTy}
    {k : IntKind} {P : Val → Prop} (hm : ∀ v, P v → AnyInt k v)
    (hs : Slot env m name b ty P) : Slot env m name b ty (AnyInt k) :=
  hs.mono hm

theorem Slot.to_int_range {env : Env} {m : Mem} {name : String} {b : BlockId} {ty : CTy}
    {k : IntKind} {lo hi : Int} {bv : BitVec k.bits}
    (hs : Slot env m name b ty (· = .int k bv))
    (hlo : lo ≤ intToInt k bv) (hhi : intToInt k bv ≤ hi) :
    Slot env m name b ty (IntRange k lo hi) :=
  hs.mono (fun _ heq => by subst heq; exact IntRange.of_int bv hlo hhi)

theorem Field.mono {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {P P' : Val → Prop}
    (hm : ∀ v, P v → P' v) (hf : Field tags m b off structTag fld fty P) :
    Field tags m b off structTag fld fty P' := by
  rcases hf with ⟨foff, blk, hfl, hb, hp, h0, hsz, hal, hval⟩
  refine ⟨foff, blk, hfl, hb, hp, h0, hsz, hal, ?_⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · exact Or.inl ⟨v, hrd, hm v hpv⟩
  · exact Or.inr (hm .undef hundef)

theorem Field.to_int_any {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {k : IntKind} {P : Val → Prop}
    (hm : ∀ v, P v → AnyInt k v) (hf : Field tags m b off structTag fld fty P) :
    Field tags m b off structTag fld fty (AnyInt k) :=
  hf.mono hm

theorem Field.to_int_range {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {k : IntKind} {lo hi : Int} {bv : BitVec k.bits}
    (hf : Field tags m b off structTag fld fty (· = .int k bv))
    (hlo : lo ≤ intToInt k bv) (hhi : intToInt k bv ≤ hi) :
    Field tags m b off structTag fld fty (IntRange k lo hi) :=
  hf.mono (fun _ heq => by subst heq; exact IntRange.of_int bv hlo hhi)

/-! ## 3. Fast Scalar, Cast, Unary, Binary, and Read/Write Lemmas -/

@[simp] theorem modSet_conflicts_nil_auto (b : BlockId) (off : Int64) (sz : Nat) :
    ModSet.conflicts [] b off sz = false := rfl

@[simp] theorem modSet_conflicts_cons (e : ModEntry) (ms : ModSet) (b : BlockId) (off : Int64)
    (sz : Nat) :
    ModSet.conflicts (e :: ms) b off sz =
      ((e.bid == b && !(e.off.toInt + e.len ≤ off.toInt || off.toInt + sz ≤ e.off.toInt)) ||
       ModSet.conflicts ms b off sz) := rfl

@[simp] theorem freeStack_nil_auto (m : Mem) : m.freeStack [] = m := by
  cases m
  rfl

@[simp] theorem isTruthy_int_iff (k : IntKind) (bv : BitVec k.bits) :
    isTruthy (.int k bv) = some (decide (intToInt k bv ≠ 0)) := by
  unfold isTruthy
  by_cases hz : bv = 0
  · subst hz
    have hz0 : intToInt k (0 : BitVec k.bits) = 0 := intToInt_zero k
    have hnat0 : (0 : BitVec k.bits).toNat = 0 := rfl
    change some ((0 : BitVec k.bits).toNat != 0) = some (decide (intToInt k (0 : BitVec k.bits) ≠ 0))
    rw [hz0, hnat0]
    rfl
  · have hnat : bv.toNat ≠ 0 := fun h0 => hz (BitVec.eq_of_toNat_eq (by simpa using h0))
    have hi : intToInt k bv ≠ 0 := fun h0 => hz (intToInt_eq_zero_iff.mp h0)
    simp [hnat, hi]

@[simp] theorem isTruthy_u8 (bv : BitVec 8) :
    isTruthy (.int .u8 bv) = some (decide (intToInt .u8 bv ≠ 0)) := isTruthy_int_iff .u8 bv

@[simp] theorem isTruthy_i8 (bv : BitVec 8) :
    isTruthy (.int .i8 bv) = some (decide (intToInt .i8 bv ≠ 0)) := isTruthy_int_iff .i8 bv

@[simp] theorem isTruthy_u16 (bv : BitVec 16) :
    isTruthy (.int .u16 bv) = some (decide (intToInt .u16 bv ≠ 0)) := isTruthy_int_iff .u16 bv

@[simp] theorem isTruthy_i16 (bv : BitVec 16) :
    isTruthy (.int .i16 bv) = some (decide (intToInt .i16 bv ≠ 0)) := isTruthy_int_iff .i16 bv

@[simp] theorem isTruthy_u32 (bv : BitVec 32) :
    isTruthy (.int .u32 bv) = some (decide (intToInt .u32 bv ≠ 0)) := isTruthy_int_iff .u32 bv

@[simp] theorem isTruthy_i32 (bv : BitVec 32) :
    isTruthy (.int .i32 bv) = some (decide (intToInt .i32 bv ≠ 0)) := isTruthy_int_iff .i32 bv

@[simp] theorem isTruthy_u64 (bv : BitVec 64) :
    isTruthy (.int .u64 bv) = some (decide (intToInt .u64 bv ≠ 0)) := isTruthy_int_iff .u64 bv

@[simp] theorem isTruthy_i64 (bv : BitVec 64) :
    isTruthy (.int .i64 bv) = some (decide (intToInt .i64 bv ≠ 0)) := isTruthy_int_iff .i64 bv

@[simp] theorem isTruthy_bool_int (b : Bool) :
    isTruthy (.int .i32 (if b then 1 else 0)) = some b := by
  cases b <;> rfl

@[simp] theorem isTruthy_ptr_auto (b : BlockId) (off : Int64) :
    isTruthy (.ptr b off) = some true := rfl

@[simp] theorem isTruthy_null_auto : isTruthy .null = some false := rfl

@[simp] theorem isTruthy_fnPtr_auto (s : SymId) : isTruthy (.fnPtr s) = some true := rfl

theorem valAsInt?_int_toInt (k : IntKind) (bv : BitVec k.bits) :
    valAsInt? (.int k bv) = some (k, intToInt k bv) := rfl

theorem ofIntCast_eq (k : IntKind) (v : Int) :
    ofIntCast k v = .int k (BitVec.ofInt k.bits v) := rfl

theorem ofIntExact_signed_bounds {k : IntKind} (hk : k.signed = true) {v : Int}
    (hlo : k.minVal ≤ v) (hhi : v ≤ k.maxVal) :
    ofIntExact k v = some (.int k (BitVec.ofInt k.bits v)) := by
  have hr : k.inRange v = true := by
    simp only [IntKind.inRange, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlo, hhi⟩
  exact ofIntExact_signed hk hr

/-- Decidable check whether every value of `k1` fits losslessly in `k2`. -/
def fitsIn (k1 k2 : IntKind) : Bool :=
  decide (k2.minVal ≤ k1.minVal ∧ k1.maxVal ≤ k2.maxVal)

theorem fitsIn_bounds {k1 k2 : IntKind} (hf : fitsIn k1 k2 = true) (bv : BitVec k1.bits) :
    k2.minVal ≤ intToInt k1 bv ∧ intToInt k1 bv ≤ k2.maxVal := by
  simp only [fitsIn, decide_eq_true_eq] at hf
  have hb := intToInt_bounds k1 bv
  omega

@[simp] theorem castVal_const (m : Mem) (ty : CTy) (v : Val) :
    castVal m (.const_ ty) v = castVal m ty v := by
  simp [castVal, CTy.unqual]

@[simp] theorem castVal_typedef (m : Mem) (name : String) (ty : CTy) (v : Val) :
    castVal m (.typedef name ty) v = castVal m ty v := by
  simp [castVal, CTy.unqual]

@[simp] theorem castVal_int_toInt (m : Mem) (k k1 : IntKind) (bv : BitVec k1.bits) :
    castVal m (.int k) (.int k1 bv) = some (.int k (BitVec.ofInt k.bits (intToInt k1 bv))) := by
  simp [castVal_int, ofIntCast, intToInt]

@[simp] theorem castVal_ptr_zero (m : Mem) (to : CTy) (k : IntKind) :
    castVal m (.ptr to) (.int k 0) = some .null := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?]

@[simp] theorem castVal_enum_int (m : Mem) (tag : String) (isU : Bool)
    (k1 : IntKind) (bv : BitVec k1.bits) :
    castVal m (.enumTy tag isU) (.int k1 bv) =
      some (.int (if isU then .u32 else .i32)
        (BitVec.ofInt (if isU then IntKind.u32 else .i32).bits (intToInt k1 bv))) := by
  simp [castVal, CTy.unqual, CTy.isVoid, CTy.intKind?, ofIntCast, intToInt]

@[simp] theorem evalUnary_logNot_int_auto (k : IntKind) (bv : BitVec k.bits) :
    evalUnary .logNot (.int k bv) =
      some (.int .i32 (if intToInt k bv != 0 then 0 else 1), .int .i32) := by
  simp [evalUnary, isTruthy_int_iff, bind, Option.bind, pure, Pure.pure]

@[simp] theorem evalUnary_logNot_ptr_auto (b : BlockId) (off : Int64) :
    evalUnary .logNot (.ptr b off) = some (.int .i32 0, .int .i32) := rfl

@[simp] theorem evalUnary_logNot_null_auto :
    evalUnary .logNot .null = some (.int .i32 1, .int .i32) := rfl

@[simp] theorem evalUnary_bitNot_int (k : IntKind) (bv : BitVec k.bits) :
    evalUnary .bitNot (.int k bv) =
      some (.int k.promote (~~~(BitVec.ofInt k.promote.bits (intToInt k bv))), .int k.promote) := rfl

theorem evalUnary_plus_int {k : IntKind} (bv : BitVec k.bits)
    (hlo : k.promote.minVal ≤ intToInt k bv) (hhi : intToInt k bv ≤ k.promote.maxVal) :
    evalUnary .plus (.int k bv) =
      some (.int k.promote (BitVec.ofInt k.promote.bits (intToInt k bv)), .int k.promote) := by
  unfold evalUnary
  simp only [valAsInt?_int_toInt, bind, Option.bind, pure, Pure.pure]
  cases hs : k.promote.signed
  · rw [ofIntExact_unsigned hs]
  · rw [ofIntExact_signed_bounds hs hlo hhi]

theorem evalUnary_neg_int {k : IntKind} (bv : BitVec k.bits)
    (hlo : k.promote.minVal ≤ -intToInt k bv) (hhi : -intToInt k bv ≤ k.promote.maxVal) :
    evalUnary .neg (.int k bv) =
      some (.int k.promote (BitVec.ofInt k.promote.bits (-intToInt k bv)), .int k.promote) := by
  unfold evalUnary
  simp only [valAsInt?_int_toInt, bind, Option.bind, pure, Pure.pure]
  cases hs : k.promote.signed
  · rw [ofIntExact_unsigned hs]
  · rw [ofIntExact_signed_bounds hs hlo hhi]

theorem evalIntBinary_cmp {op : BinOp}
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (k1 k2 : IntKind) (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits) :
    let ck := IntKind.usualArith k1 k2
    let n1 := intToInt ck (BitVec.ofInt ck.bits (intToInt k1 bv1))
    let n2 := intToInt ck (BitVec.ofInt ck.bits (intToInt k2 bv2))
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) =
      some (.int .i32 (if cmpOrd op n1 n2 then 1 else 0), .int .i32) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [evalIntBinary, intToInt, bind, Option.bind, pure, Pure.pure]

theorem evalIntBinary_cmp_inRange {op : BinOp}
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {k1 k2 : IntKind} (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits)
    (h1 : (IntKind.usualArith k1 k2).minVal ≤ intToInt k1 bv1 ∧
          intToInt k1 bv1 ≤ (IntKind.usualArith k1 k2).maxVal)
    (h2 : (IntKind.usualArith k1 k2).minVal ≤ intToInt k2 bv2 ∧
          intToInt k2 bv2 ≤ (IntKind.usualArith k1 k2).maxVal) :
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) =
      some (.int .i32 (if cmpOrd op (intToInt k1 bv1) (intToInt k2 bv2) then 1 else 0), .int .i32) := by
  rw [evalIntBinary_cmp hop]
  simp only [intToInt_ofInt_eq h1.1 h1.2, intToInt_ofInt_eq h2.1 h2.2]

theorem evalIntBinary_bitwise {op : BinOp}
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (k1 k2 : IntKind) (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits) :
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (intToInt k1 bv1)
    let c2 := BitVec.ofInt ck.bits (intToInt k2 bv2)
    let res := match op with | .bitAnd => c1 &&& c2 | .bitOr => c1 ||| c2 | _ => c1 ^^^ c2
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) = some (.int ck res, .int ck) := by
  rcases hop with rfl | rfl | rfl <;>
    simp [evalIntBinary, intToInt, bind, Option.bind, pure, Pure.pure]

theorem evalIntBinary_arith_signed {op : BinOp}
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    {k1 k2 : IntKind} (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits)
    (hs : (IntKind.usualArith k1 k2).signed = true)
    (h1 : (IntKind.usualArith k1 k2).minVal ≤ intToInt k1 bv1 ∧
          intToInt k1 bv1 ≤ (IntKind.usualArith k1 k2).maxVal)
    (h2 : (IntKind.usualArith k1 k2).minVal ≤ intToInt k2 bv2 ∧
          intToInt k2 bv2 ≤ (IntKind.usualArith k1 k2).maxVal)
    (hd : (op = .div ∨ op = .mod) → intToInt k2 bv2 ≠ 0)
    (raw : Int)
    (hraw : raw = match op with
      | .add => intToInt k1 bv1 + intToInt k2 bv2
      | .sub => intToInt k1 bv1 - intToInt k2 bv2
      | .mul => intToInt k1 bv1 * intToInt k2 bv2
      | .div => Int.tdiv (intToInt k1 bv1) (intToInt k2 bv2)
      | _ => Int.tmod (intToInt k1 bv1) (intToInt k2 bv2))
    (hlo : (IntKind.usualArith k1 k2).minVal ≤ raw)
    (hhi : raw ≤ (IntKind.usualArith k1 k2).maxVal) :
    let ck := IntKind.usualArith k1 k2
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) =
      some (.int ck (BitVec.ofInt ck.bits raw), .int ck) := by
  subst hraw
  have hn1 : intToInt (IntKind.usualArith k1 k2)
      (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)) = intToInt k1 bv1 :=
    intToInt_ofInt_eq h1.1 h1.2
  have hn2 : intToInt (IntKind.usualArith k1 k2)
      (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)) = intToInt k2 bv2 :=
    intToInt_ofInt_eq h2.1 h2.2
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hx1 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toNat) = intToInt k1 bv1 := hn1
    have hx2 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) = intToInt k2 bv2 := hn2
    rw [hx1, hx2, ofIntExact_signed_bounds hs hlo hhi]
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hx1 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toNat) = intToInt k1 bv1 := hn1
    have hx2 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) = intToInt k2 bv2 := hn2
    rw [hx1, hx2, ofIntExact_signed_bounds hs hlo hhi]
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hx1 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toNat) = intToInt k1 bv1 := hn1
    have hx2 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) = intToInt k2 bv2 := hn2
    rw [hx1, hx2, ofIntExact_signed_bounds hs hlo hhi]
  · have hnz : intToInt k2 bv2 ≠ 0 := hd (Or.inl rfl)
    have hbeq : (intToInt k2 bv2 == 0) = false := beq_false_of_ne hnz
    unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hx1 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toNat) = intToInt k1 bv1 := hn1
    have hx2 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) = intToInt k2 bv2 := hn2
    rw [hx1, hx2, hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, ofIntExact_signed_bounds hs hlo hhi]
  · have hnz : intToInt k2 bv2 ≠ 0 := hd (Or.inr rfl)
    have hbeq : (intToInt k2 bv2 == 0) = false := beq_false_of_ne hnz
    unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hx1 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k1 bv1)).toNat) = intToInt k1 bv1 := hn1
    have hx2 : (if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) = intToInt k2 bv2 := hn2
    rw [hx1, hx2, hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, ofIntExact_signed_bounds hs hlo hhi]

theorem evalIntBinary_arith_unsigned {op : BinOp}
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    {k1 k2 : IntKind} (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits)
    (hu : (IntKind.usualArith k1 k2).signed = false)
    (hd : (op = .div ∨ op = .mod) →
      intToInt (IntKind.usualArith k1 k2) (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)) ≠ 0) :
    let ck := IntKind.usualArith k1 k2
    let n1 := intToInt ck (BitVec.ofInt ck.bits (intToInt k1 bv1))
    let n2 := intToInt ck (BitVec.ofInt ck.bits (intToInt k2 bv2))
    let raw := match op with
      | .add => n1 + n2 | .sub => n1 - n2 | .mul => n1 * n2
      | .div => Int.tdiv n1 n2 | _ => Int.tmod n1 n2
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) =
      some (.int ck (BitVec.ofInt ck.bits raw), .int ck) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    rw [ofIntExact_unsigned hu]; rfl
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    rw [ofIntExact_unsigned hu]; rfl
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    rw [ofIntExact_unsigned hu]; rfl
  · have hnz := hd (Or.inl rfl)
    have hbeq : (intToInt (IntKind.usualArith k1 k2)
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)) == 0) = false :=
      beq_false_of_ne hnz
    unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hbeq' : ((if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) == 0) = false := hbeq
    rw [hbeq']
    simp only [Bool.false_eq_true, ↓reduceIte, ofIntExact_unsigned hu]; rfl
  · have hnz := hd (Or.inr rfl)
    have hbeq : (intToInt (IntKind.usualArith k1 k2)
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)) == 0) = false :=
      beq_false_of_ne hnz
    unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hbeq' : ((if (IntKind.usualArith k1 k2).signed = true then
        (BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toInt else
        ↑(BitVec.ofInt (IntKind.usualArith k1 k2).bits (intToInt k2 bv2)).toNat) == 0) = false := hbeq
    rw [hbeq']
    simp only [Bool.false_eq_true, ↓reduceIte, ofIntExact_unsigned hu]; rfl

theorem evalIntBinary_shift_unsigned {op : BinOp} (hop : op = .shl ∨ op = .shr)
    {k1 k2 : IntKind} (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits)
    (hu : k1.promote.signed = false)
    (hlo : 0 ≤ intToInt k2 bv2) (hhi : intToInt k2 bv2 < k1.promote.bits) :
    let lk := k1.promote
    let bv := BitVec.ofInt lk.bits (intToInt k1 bv1)
    let sh := (intToInt k2 bv2).toNat
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) =
      some (.int lk (if op == .shl then bv <<< sh else bv >>> sh), .int lk) := by
  have hg : (decide (0 ≤ intToInt k2 bv2) && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlo, hhi⟩
  rcases hop with rfl | rfl
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    change Option.bind (guard ((0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true)) _ = _
    have hbool : (0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true := hg
    rw [hbool]
    simp only [guard, Pure.pure, ↓reduceIte, hu, Bool.false_eq_true, Option.bind]
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hbool : (0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true := hg
    change Option.bind (guard ((0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true)) _ = _
    rw [hbool]
    simp only [guard, Pure.pure, ↓reduceIte, hu, Bool.false_eq_true, Option.bind]

theorem evalIntBinary_shift_signed {op : BinOp} (hop : op = .shl ∨ op = .shr)
    {k1 k2 : IntKind} (bv1 : BitVec k1.bits) (bv2 : BitVec k2.bits)
    (hs : k1.promote.signed = true)
    (h1 : 0 ≤ intToInt k1 bv1)
    (h2lo : 0 ≤ intToInt k2 bv2) (h2hi : intToInt k2 bv2 < k1.promote.bits)
    (raw : Int)
    (hraw : raw = if op == .shl then intToInt k1 bv1 * (2 ^ (intToInt k2 bv2).toNat : Int)
                  else intToInt k1 bv1 / (2 ^ (intToInt k2 bv2).toNat : Int))
    (hlo : k1.promote.minVal ≤ raw) (hhi : raw ≤ k1.promote.maxVal) :
    evalIntBinary op (.int k1 bv1) (.int k2 bv2) =
      some (.int k1.promote (BitVec.ofInt k1.promote.bits raw), .int k1.promote) := by
  subst hraw
  have hg : (0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h2lo, h2hi⟩
  rcases hop with rfl | rfl
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    change Option.bind (guard ((0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true)) _ = _
    rw [hg]
    simp only [guard, Pure.pure, ↓reduceIte, hs, Option.bind]
    change Option.bind (if (0 ≤ intToInt k1 bv1) then some () else none) _ = _
    simp only [h1, ↓reduceIte, Option.bind, ofIntExact_signed_bounds hs hlo hhi]
  · unfold evalIntBinary
    rw [valAsInt?_int_toInt, valAsInt?_int_toInt]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    change Option.bind (guard ((0 ≤ intToInt k2 bv2 && decide (intToInt k2 bv2 < (k1.promote.bits : Int))) = true)) _ = _
    rw [hg]
    simp only [guard, Pure.pure, ↓reduceIte, hs, Option.bind]
    change Option.bind (if (0 ≤ intToInt k1 bv1) then some () else none) _ = _
    simp only [h1, ↓reduceIte, Option.bind, ofIntExact_signed_bounds hs hlo hhi]

theorem applyBinary_int {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {op : BinOp} {v1 v2 : Val} {t1 t2 : CTy}
    (ht1 : t1.isPtr = false) (ht2 : t2.isPtr = false)
    (hf1 : match t1.unqual with | .fnPtr .. => false | _ => true)
    (hf2 : match t2.unqual with | .fnPtr .. => false | _ => true) :
    applyBinary cfg tags m op v1 t1 v2 t2 = evalIntBinary op v1 v2 := by
  unfold applyBinary
  cases hu1 : t1.unqual <;> simp [hu1] at hf1 <;>
  cases hu2 : t2.unqual <;> simp [hu2] at hf2 <;>
  simp only [ht1, ht2, hu1, hu2, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

theorem applyBinary_int_of_intKind {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {op : BinOp} {v1 v2 : Val} {t1 t2 : CTy} {k1 k2 : IntKind}
    (hk1 : t1.intKind? = some k1) (hk2 : t2.intKind? = some k2) :
    applyBinary cfg tags m op v1 t1 v2 t2 = evalIntBinary op v1 v2 := by
  apply applyBinary_int
  · unfold CTy.isPtr; unfold CTy.intKind? at hk1; cases hu : t1.unqual <;> simp [hu] at hk1 <;> rfl
  · unfold CTy.isPtr; unfold CTy.intKind? at hk2; cases hu : t2.unqual <;> simp [hu] at hk2 <;> rfl
  · unfold CTy.intKind? at hk1; cases hu : t1.unqual <;> simp [hu] at hk1 <;> rfl
  · unfold CTy.intKind? at hk2; cases hu : t2.unqual <;> simp [hu] at hk2 <;> rfl

theorem readVal_tags_irrel (tags1 tags2 : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (ty : CTy) : Sem.readVal tags1 m b off ty = Sem.readVal tags2 m b off ty := by
  unfold Sem.readVal
  cases ty.unqual <;> simp [sizeofTy, sizeofAux]

theorem CTy.isPtr_of_unqual_ptr {ty el : CTy} (h : ty.unqual = .ptr el) : ty.isPtr = true := by
  simp [CTy.isPtr, h]

theorem CTy.intKind?_eq_some_of_unqual_int {ty : CTy} {k : IntKind} (h : ty.unqual = .int k) :
    ty.intKind? = some k := by
  simp [CTy.intKind?, h]

theorem sizeofTy_eq_scalar (tags : TypeEnv) {ty : CTy} {k : IntKind}
    (hk : ty.intKind? = some k) : sizeofTy tags ty = k.bytes := by
  rw [← sizeofTy_unqual]
  unfold CTy.intKind? at hk
  cases hu : ty.unqual <;> simp [hu] at hk
  · subst hk; simp [sizeofTy, sizeofAux]
  · cases hk; simp [sizeofTy, sizeofAux]; cases ‹Bool› <;> rfl

theorem alignofTy_eq_scalar (tags : TypeEnv) {ty : CTy} {k : IntKind}
    (hk : ty.intKind? = some k) : alignofTy tags ty = k.align := by
  rw [← alignofTy_unqual]
  unfold CTy.intKind? at hk
  cases hu : ty.unqual <;> simp [hu] at hk
  · subst hk; simp [alignofTy, alignofAux]
  · cases hk; simp [alignofTy, alignofAux]; cases ‹Bool› <;> rfl

private theorem sizeofTy_eq_ptr_auto (tags : TypeEnv) {ty el : CTy}
    (hptr : ty.unqual = .ptr el) : sizeofTy tags ty = 8 := by
  rw [← sizeofTy_unqual, hptr]; simp

private theorem alignofTy_eq_ptr_auto (tags : TypeEnv) {ty el : CTy}
    (hptr : ty.unqual = .ptr el) : alignofTy tags ty = 8 := by
  rw [← alignofTy_unqual, hptr]; simp

theorem writeVal_writeBytes_len (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (h : Sem.writeVal m b off ty v = some m') :
    ∃ bs, m.writeBytes b off bs = some m' ∧ bs.length = sizeofTy tags ty := by
  unfold Sem.writeVal at h
  by_cases hc : ty.isConst
  · simp [hc, bind, Option.bind, guard] at h
  · simp only [hc, Bool.not_false, guard_true, bind, Option.bind] at h
    cases hblk : m.blocks b with
    | none => simp [hblk] at h
    | some blk =>
      simp only [hblk] at h
      cases hty : ty.unqual with
      | int k =>
        simp only [hty, CTy.unqual, CTy.intKind?] at h
        cases ha : Mem.isAligned blk off k.align with
        | false => dsimp only [guard, bind, Option.bind] at h; rw [ha] at h; cases h
        | true =>
          simp only [ha, guard_true] at h
          cases hvi : valAsInt? v with
          | none => simp [hvi] at h
          | some p =>
            simp only [hvi] at h
            refine ⟨_, h, ?_⟩
            rw [encodeInt_length, ← sizeofTy_unqual, hty]; simp
      | enumTy tag isU =>
        cases isU
        · simp only [hty, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte] at h
          cases ha : Mem.isAligned blk off IntKind.i32.align with
          | false => simp only [guard, Pure.pure] at h; rw [ha] at h; cases h
          | true =>
            simp only [ha, guard_true] at h
            cases hvi : valAsInt? v with
            | none => simp [hvi] at h
            | some p =>
              simp only [hvi] at h
              refine ⟨_, h, ?_⟩
              rw [encodeInt_length, ← sizeofTy_unqual, hty]; simp [sizeofTy, sizeofAux, IntKind.bytes]; decide
        · simp only [hty, CTy.unqual, CTy.intKind?, ↓reduceIte] at h
          cases ha : Mem.isAligned blk off IntKind.u32.align with
          | false => simp only [guard, Pure.pure] at h; rw [ha] at h; cases h
          | true =>
            simp only [ha, guard_true] at h
            cases hvi : valAsInt? v with
            | none => simp [hvi] at h
            | some p =>
              simp only [hvi] at h
              refine ⟨_, h, ?_⟩
              rw [encodeInt_length, ← sizeofTy_unqual, hty]; simp [sizeofTy, sizeofAux, IntKind.bytes]; decide
      | ptr _ =>
        simp only [hty] at h
        cases ha : Mem.isAligned blk off 8 with
        | false => rw [ha] at h; cases h
        | true =>
          simp only [ha, guard_true] at h
          have hsz8 : sizeofTy tags ty = 8 := by rw [← sizeofTy_unqual, hty]; simp
          cases v with
          | null => exact ⟨_, h, by simp [hsz8]⟩
          | ptr pb poff => exact ⟨_, h, by simp [hsz8]⟩
          | int _ bv =>
            by_cases hz : bv.toNat == 0
            · simp only [hz, ↓reduceIte] at h; exact ⟨_, h, by simp [hsz8]⟩
            · simp [hz] at h
          | _ => cases h
      | fnPtr _ _ _ =>
        simp only [hty] at h
        cases ha : Mem.isAligned blk off 8 with
        | false => rw [ha] at h; cases h
        | true =>
          simp only [ha, guard_true] at h
          have hsz8 : sizeofTy tags ty = 8 := by
            rw [← sizeofTy_unqual, hty]; simp [sizeofTy, sizeofAux]
          cases v with
          | null => exact ⟨_, h, by simp [hsz8]⟩
          | fnPtr s => exact ⟨_, h, by simp [hsz8]⟩
          | int _ bv =>
            by_cases hz : bv.toNat == 0
            · simp only [hz, ↓reduceIte] at h; exact ⟨_, h, by simp [hsz8]⟩
            · simp [hz] at h
          | _ => cases h
      | vaList =>
        simp only [hty] at h
        have hsz24 : sizeofTy tags ty = 24 := by
          rw [← sizeofTy_unqual, hty]; simp [sizeofTy, sizeofAux]
        cases v with
        | vaList valid =>
          cases valid with
          | false => cases h
          | true => exact ⟨_, h, by simp [hsz24]⟩
        | _ => cases h
      | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
        simp [hty] at h

theorem writePlace_writeBytes_len {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {rv : ExprRes} {res : ExprRes}
    (h : writePlace tags m b off ty rv = some (res, m')) :
    ∃ bs, m.writeBytes b off bs = some m' ∧ bs.length = sizeofTy tags ty := by
  cases rv with
  | lval _ _ _ => cases h
  | structVal bs _ =>
    unfold writePlace at h
    dsimp only at h
    by_cases hlen : bs.length == sizeofTy tags ty
    · simp only [hlen, ↓reduceIte, Option.map] at h
      cases hm : m.writeBytes b off bs with
      | none => simp [hm] at h
      | some m1 => simp only [hm] at h; cases h; exact ⟨bs, hm, beq_iff_eq.mp hlen⟩
    · simp [hlen] at h
  | rval v _ =>
    unfold writePlace at h
    dsimp only [bind, Option.bind, pure, Pure.pure] at h
    cases hty : ty.unqual <;> simp only [hty] at h
    all_goals
      first
      | (cases hc : castVal m ty v with
         | none => simp [hc] at h
         | some cv =>
           simp only [hc] at h
           cases hw : writeVal m b off ty cv with
           | none => simp [hw] at h
           | some m1 => simp only [hw] at h; cases h; exact writeVal_writeBytes_len tags hw)
      | (cases hw : writeVal m b off ty v with
         | none => simp [hw] at h
         | some m1 => simp only [hw] at h; cases h; exact writeVal_writeBytes_len tags hw)

theorem readVal_writeVal_same_int' (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {tyw tyr : CTy} {k : IntKind} {v : BitVec k.bits}
    (huq : tyr.unqual = tyw.unqual) (hk : tyw.intKind? = some k)
    (hb : m.blocks b = some blk)
    (hwr : Sem.writeVal m b off tyw (.int k v) = some m') :
    Sem.readVal tags m' b off tyr = some (.int k v) := by
  unfold Sem.writeVal at hwr
  by_cases hc : tyw.isConst
  · simp [hc, bind, Option.bind, guard] at hwr
  · simp only [hc, Bool.not_false, guard_true, hb, bind, Option.bind] at hwr
    have hcases : tyw.unqual = .int k ∨ ∃ tag isU, tyw.unqual = .enumTy tag isU ∧
        k = (if isU then .u32 else .i32) := by
      unfold CTy.intKind? at hk
      cases hu : tyw.unqual <;> simp [hu] at hk
      · exact Or.inl (hk ▸ rfl)
      · exact Or.inr ⟨_, _, rfl, hk.symm⟩
    have hwb : Mem.isAligned blk off k.align = true ∧
        m.writeBytes b off (Mem.encodeInt k v) = some m' := by
      have heq : BitVec.ofInt k.bits (if k.signed then v.toInt else (v.toNat : Int)) = v := by
        by_cases hs : k.signed <;> simp [hs]
      rcases hcases with hu | ⟨tag, isU, hu, hkeq⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, valAsInt?, heq] at hwr
        cases hal : Mem.isAligned blk off k.align
        · simp only [guard, Pure.pure] at hwr; rw [hal] at hwr; cases hwr
        · simp only [hal, guard_true] at hwr; exact ⟨rfl, hwr⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, valAsInt?] at hwr
        rw [← hkeq] at hwr
        simp only [heq] at hwr
        cases hal : Mem.isAligned blk off k.align
        · simp only [guard, Pure.pure] at hwr; rw [hal] at hwr; cases hwr
        · simp only [hal, guard_true] at hwr; exact ⟨rfl, hwr⟩
    have hrd := readBytes_writeBytes_same hb hwb.2
    have hblk' := writeBytes_blocks_eq hb hwb.2
    have hal' : Mem.isAligned { blk with bytes := (fun i =>
        if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + (Mem.encodeInt k v).length then
          (Mem.encodeInt k v)[i - off.toInt.toNat]?.getD .undef
        else blk.bytes i) } off k.align = true := by
      simpa [Mem.isAligned] using hwb.1
    unfold Sem.readVal
    rcases hcases with hu | ⟨tag, isU, hu, hkeq⟩
    · simp only [huq, hu, CTy.unqual, CTy.intKind?, hblk', hal', guard_true, bind, Option.bind]
      rw [← encodeInt_length k v, hrd]
      dsimp [pure]
      rw [decodeInt_encodeInt]
    · simp only [huq, hu, CTy.unqual, CTy.intKind?, ← hkeq, hblk', hal', guard_true, bind, Option.bind]
      rw [← encodeInt_length k v, hrd]
      dsimp [pure]
      rw [decodeInt_encodeInt]

theorem readVal_writeVal_same_ptr' (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {tyw tyr elw elr : CTy} {v : Val}
    (hwptr : tyw.unqual = .ptr elw) (hrptr : tyr.unqual = .ptr elr)
    (hb : m.blocks b = some blk)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hwr : Sem.writeVal m b off tyw v = some m') :
    Sem.readVal tags m' b off tyr = some v := by
  unfold Sem.writeVal at hwr
  by_cases hc : tyw.isConst
  · simp [hc, bind, Option.bind, guard] at hwr
  · simp only [hc, Bool.not_false, guard_true, hb, hwptr, bind, Option.bind] at hwr
    have hal : Mem.isAligned blk off 8 = true := by
      cases hg : Mem.isAligned blk off 8
      · simp [hg, guard] at hwr
      · rfl
    simp only [hal, guard_true] at hwr
    rcases hv with rfl | ⟨pb, poff, rfl⟩
    · have hrd := readBytes_writeBytes_same hb hwr
      have hblk' := writeBytes_blocks_eq hb hwr
      have hal' : Mem.isAligned { blk with bytes := (fun i =>
          if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + Mem.encodeNull.length then
            Mem.encodeNull[i - off.toInt.toNat]?.getD .undef
          else blk.bytes i) } off 8 = true := by
        simpa [Mem.isAligned] using hal
      unfold Sem.readVal
      simp only [hrptr, hblk', hal', guard_true, bind, Option.bind]
      rw [← encodeNull_length, hrd]
      dsimp [pure]
      rw [decodePtr_encodeNull]
    · have hrd := readBytes_writeBytes_same hb hwr
      have hblk' := writeBytes_blocks_eq hb hwr
      have hal' : Mem.isAligned { blk with bytes := (fun i =>
          if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + (Mem.encodePtr pb poff).length then
            (Mem.encodePtr pb poff)[i - off.toInt.toNat]?.getD .undef
          else blk.bytes i) } off 8 = true := by
        simpa [Mem.isAligned] using hal
      unfold Sem.readVal
      simp only [hrptr, hblk', hal', guard_true, bind, Option.bind]
      rw [← encodePtr_length pb poff, hrd]
      dsimp [pure]
      rw [decodePtr_encodePtr]

theorem writeVal_int_some' {m : Mem} {b : BlockId} {off : Int64} {blk : Block} {ty : CTy}
    {k : IntKind} {v : Val} {iv : Int}
    (hnc : ty.isConst = false) (hk : ty.intKind? = some k)
    (hb : m.blocks b = some blk) (hrw : blk.perm = .rw)
    (hal : Mem.isAligned blk off k.align = true)
    (hin : Mem.inBounds blk off k.bytes = true)
    (hvi : valAsInt? v = some (k, iv)) :
    ∃ m', Sem.writeVal m b off ty v = some m' := by
  have hin2 : Mem.inBounds blk off (Mem.encodeInt k (BitVec.ofInt k.bits iv)).length = true := by
    simpa [encodeInt_length] using hin
  obtain ⟨m', hm'⟩ := writeBytes_eq_some hb hrw hin2
  refine ⟨m', ?_⟩
  unfold CTy.intKind? at hk
  cases hu : ty.unqual <;> simp [hu] at hk
  · subst hk
    unfold Sem.writeVal
    simp [hnc, hb, hu, CTy.unqual, CTy.intKind?, hal, hvi, hm', bind, Option.bind]
  · rename_i tag isU
    cases isU <;> simp at hk <;> subst hk <;>
    · unfold Sem.writeVal
      simp [hnc, hb, hu, CTy.unqual, CTy.intKind?, hal, hvi, hm', bind, Option.bind]

/-! ## 4. Framing & Preservation Lemmas (`FrameBlocks`, `Slot`, `Field`, `PtrValid`, `PtrWritable`) -/

theorem FrameBlocks.refl (m : Mem) (allowed : AutoBlockSet) : FrameBlocks m m allowed :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl, fun b _ hle _ hs => by
    rw [m.fresh b hle] at hs; cases hs⟩

theorem FrameBlocks.mono {m m' : Mem} {s1 s2 : AutoBlockSet}
    (hsub : ∀ b, b ∈ s1 → b ∈ s2) (hf : FrameBlocks m m' s1) : FrameBlocks m m' s2 :=
  ⟨hf.1, fun b hlt hnot => hf.2.1 b hlt (fun h1 => hnot (hsub b h1)),
   fun b blk hle hnot hs => hf.2.2 b blk hle (fun h1 => hnot (hsub b h1)) hs⟩

theorem FrameBlocks.trans {m1 m2 m3 : Mem} {s1 s2 : AutoBlockSet}
    (h12 : FrameBlocks m1 m2 s1) (h23 : FrameBlocks m2 m3 s2) :
    FrameBlocks m1 m3 (s1 ∪ s2) := by
  refine ⟨Nat.le_trans h12.1 h23.1, ?_, ?_⟩
  · intro b hb hnot
    have hnot1 : b ∉ s1 := fun h => hnot (Or.inl h)
    have hnot2 : b ∉ s2 := fun h => hnot (Or.inr h)
    rw [h23.2.1 b (Nat.lt_of_lt_of_le hb h12.1) hnot2, h12.2.1 b hb hnot1]
  · intro b blk hle hnot hs
    have hnot1 : b ∉ s1 := fun h => hnot (Or.inl h)
    have hnot2 : b ∉ s2 := fun h => hnot (Or.inr h)
    by_cases hm2 : b < m2.nextBlock
    · rw [h23.2.1 b hm2 hnot2] at hs
      exact h12.2.2 b blk hle hnot1 hs
    · exact h23.2.2 b blk (Nat.le_of_not_lt hm2) hnot2 hs

theorem FrameBlocks.trans_same {m1 m2 m3 : Mem} {s : AutoBlockSet}
    (h12 : FrameBlocks m1 m2 s) (h23 : FrameBlocks m2 m3 s) :
    FrameBlocks m1 m3 s := by
  simpa [AutoBlockSet.union_self] using FrameBlocks.trans h12 h23

theorem FrameBlocks.of_roExt {m m' : Mem} (allowed : AutoBlockSet) (hro : ROExt m m') :
    FrameBlocks m m' allowed :=
  ⟨hro.1, fun b hb _ => hro.2.1 b hb, fun b blk hle _ hs => hro.2.2 b blk hle hs⟩

theorem FrameBlocks.of_writeBytes {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    (h : m.writeBytes b off bs = some m') : FrameBlocks m m' {b} := by
  refine ⟨by rw [writeBytes_nextBlock h]; exact Nat.le_refl _, ?_, ?_⟩
  · intro x _ hnot
    exact writeBytes_blocks_ne h (by simpa [AutoBlockSet.mem_singleton] using hnot)
  · intro x blk hle hnot hs
    have hne : x ≠ b := by simpa [AutoBlockSet.mem_singleton] using hnot
    rw [writeBytes_blocks_ne h hne, m.fresh x hle] at hs
    cases hs

theorem FrameBlocks.of_writeVal {m m' : Mem} {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (h : Sem.writeVal m b off ty v = some m') : FrameBlocks m m' {b} := by
  obtain ⟨_, hm⟩ := writeVal_writeBytes h
  exact FrameBlocks.of_writeBytes hm

theorem FrameBlocks.of_writePlace {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {rv res : ExprRes} (h : writePlace tags m b off ty rv = some (res, m')) :
    FrameBlocks m m' {b} := by
  obtain ⟨_, hm⟩ := writePlace_writeBytes h
  exact FrameBlocks.of_writeBytes hm

theorem FrameBlocks.of_alloc {m m' : Mem} {sz al : Nat} {p : Perm} {k : AllocKind}
    {ba : UInt64} {init : Nat → MemByte} {h1 : sz < ptrDiffLimit} {h2 : 0 < al}
    {h3 : ba.toNat % al = 0} {bid : BlockId}
    (ha : m.alloc sz al p k ba init h1 h2 h3 = (bid, m')) :
    FrameBlocks m m' {bid} := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm' : m' = (m.alloc sz al p k ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  subst hbid hm'
  refine ⟨Nat.le_succ _, ?_, ?_⟩
  · intro b hb _
    exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt hb)
  · intro b blk hle hnot hs
    have hne : b ≠ m.nextBlock := by simpa [AutoBlockSet.mem_singleton] using hnot
    rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, m.fresh b hle] at hs
    cases hs

theorem FrameBlocks.of_alloc_strLit {m m' : Mem} {bid : BlockId} {base : UInt64} {str : String}
    (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
    (halloc : m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m')) :
    FrameBlocks m m' ∅ :=
  FrameBlocks.of_roExt ∅ (ROExt.of_strLit hsz halloc)

theorem FrameBlocks.of_freeStack (m : Mem) (blks : List BlockId) :
    FrameBlocks m (m.freeStack blks) (AutoBlockSet.ofList blks) := by
  refine ⟨Nat.le_refl _, ?_, ?_⟩
  · intro b _ hnot
    exact freeStack_blocks_not_mem m blks (by simpa using hnot)
  · intro b blk hle hnot hs
    rw [freeStack_blocks_not_mem m blks (by simpa using hnot), m.fresh b hle] at hs
    cases hs

theorem FrameBlocks.of_localFrameMem {m0 m : Mem} {blks : List BlockId}
    (hf : LocalFrameMem m0 m blks) : FrameBlocks m0 m (AutoBlockSet.ofList blks) := by
  refine ⟨hf.1, fun b hb _ => hf.2.1 b hb, ?_⟩
  intro b blk hle hnot hs
  rcases hf.2.2.2.2 b blk hle hs with ⟨_, hmem⟩ | hro
  · exact False.elim (hnot hmem)
  · exact hro

theorem FrameBlocks.freeStack_above {m0 m : Mem} {allowed : AutoBlockSet} {blks : List BlockId}
    (hf : FrameBlocks m0 m (allowed ∪ AutoBlockSet.ofList blks))
    (hge : ∀ b ∈ blks, m0.nextBlock ≤ b)
    (hstack : ∀ b ∈ blks, ∀ blk, m.blocks b = some blk → blk.kind = .stack) :
    FrameBlocks m0 (m.freeStack blks) allowed := by
  refine ⟨by simpa using hf.1, ?_, ?_⟩
  · intro b hb hnot
    have hnotBlks : b ∉ blks := fun hmem => Nat.not_lt_of_le (hge b hmem) hb
    rw [freeStack_blocks_not_mem m blks hnotBlks]
    exact hf.2.1 b hb (fun hor => by rcases hor with ha | hb2; exact hnot ha; exact hnotBlks hb2)
  · intro b blk hle hnot hs
    by_cases hmem : b ∈ blks
    · cases hmb : m.blocks b with
      | none =>
        rw [Mem.freeStack] at hs
        simp [hmem, hmb] at hs
      | some blk0 =>
        have hk0 := hstack b hmem blk0 hmb
        rw [freeStack_blocks_mem_stack m blks hmem hmb hk0] at hs
        cases hs
    · rw [freeStack_blocks_not_mem m blks hmem] at hs
      exact hf.2.2 b blk hle (fun hor => by rcases hor with ha | hb2; exact hnot ha; exact hmem hb2) hs

theorem FrameBlocks.blocks_eq {m m' : Mem} {allowed : AutoBlockSet} {b : BlockId} {blk : Block}
    (hf : FrameBlocks m m' allowed) (hb : m.blocks b = some blk) (hnot : b ∉ allowed) :
    m'.blocks b = some blk := by
  rw [hf.2.1 b (lt_nextBlock_of_some hb) hnot, hb]

theorem blocks_preserve_writeBytes {m m' : Mem} {b b' : BlockId} {off : Int64} {bs : List MemByte}
    {blk : Block} (hwr : m.writeBytes b' off bs = some m') (hb : m.blocks b = some blk)
    (hne : b ≠ b') : m'.blocks b = some blk := by
  rw [writeBytes_blocks_ne hwr hne, hb]

theorem blocks_preserve_writeVal {m m' : Mem} {b b' : BlockId} {off : Int64} {ty : CTy} {v : Val}
    {blk : Block} (hwr : Sem.writeVal m b' off ty v = some m') (hb : m.blocks b = some blk)
    (hne : b ≠ b') : m'.blocks b = some blk := by
  rw [writeVal_blocks_ne hwr hne, hb]

theorem blocks_preserve_writePlace {tags : TypeEnv} {m m' : Mem} {b b' : BlockId} {off : Int64}
    {ty : CTy} {rv res : ExprRes} {blk : Block}
    (hwr : writePlace tags m b' off ty rv = some (res, m')) (hb : m.blocks b = some blk)
    (hne : b ≠ b') : m'.blocks b = some blk := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes hwr
  exact blocks_preserve_writeBytes hwb hb hne

theorem blocks_preserve_alloc {m m' : Mem} {sz al : Nat} {p : Perm} {k : AllocKind}
    {ba : UInt64} {init : Nat → MemByte} {h1 : sz < ptrDiffLimit} {h2 : 0 < al}
    {h3 : ba.toNat % al = 0} {bid b : BlockId} {blk : Block}
    (ha : m.alloc sz al p k ba init h1 h2 h3 = (bid, m')) (hb : m.blocks b = some blk) :
    m'.blocks b = some blk := by
  have hm' : m' = (m.alloc sz al p k ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  subst hm'
  rw [alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt (lt_nextBlock_of_some hb)), hb]

theorem blocks_preserve_freeStack {m : Mem} {blks : List BlockId} {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) (hnot : b ∉ blks) :
    (m.freeStack blks).blocks b = some blk := by
  rw [freeStack_blocks_not_mem m blks hnot, hb]

theorem blocks_preserve_roExt {m m' : Mem} {b : BlockId} {blk : Block}
    (hro : ROExt m m') (hb : m.blocks b = some blk) : m'.blocks b = some blk := by
  rw [hro.2.1 b (lt_nextBlock_of_some hb), hb]

theorem blocks_preserve_frameBlocks {m m' : Mem} {allowed : AutoBlockSet} {b : BlockId} {blk : Block}
    (hf : FrameBlocks m m' allowed) (hb : m.blocks b = some blk) (hnot : b ∉ allowed) :
    m'.blocks b = some blk :=
  hf.blocks_eq hb hnot

/-! ### `PtrValid` & `PtrWritable` Preservation -/

theorem PtrValid.preserve_writeBytes {m m' : Mem} {p : Val} {len : Nat}
    {b' : BlockId} {off' : Int64} {bs : List MemByte}
    (hv : PtrValid m p len) (hwr : m.writeBytes b' off' bs = some m') : PtrValid m' p len := by
  rcases hv with ⟨b, off, blk, rfl, hb, hin⟩
  by_cases heq : b = b'
  · subst heq
    refine ⟨b, off, _, rfl, writeBytes_blocks_eq hb hwr, ?_⟩
    simpa [Mem.inBounds] using hin
  · exact ⟨b, off, blk, rfl, blocks_preserve_writeBytes hwr hb heq, hin⟩

theorem PtrValid.preserve_writeVal {m m' : Mem} {p : Val} {len : Nat}
    {b' : BlockId} {off' : Int64} {ty : CTy} {v : Val}
    (hv : PtrValid m p len) (hwr : Sem.writeVal m b' off' ty v = some m') : PtrValid m' p len := by
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  exact hv.preserve_writeBytes hwb

theorem PtrValid.preserve_writePlace {tags : TypeEnv} {m m' : Mem} {p : Val} {len : Nat}
    {b' : BlockId} {off' : Int64} {ty : CTy} {rv res : ExprRes}
    (hv : PtrValid m p len) (hwr : writePlace tags m b' off' ty rv = some (res, m')) :
    PtrValid m' p len := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes hwr
  exact hv.preserve_writeBytes hwb

theorem PtrValid.preserve_alloc {m m' : Mem} {p : Val} {len : Nat}
    {sz al : Nat} {perm : Perm} {k : AllocKind} {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0} {bid : BlockId}
    (hv : PtrValid m p len) (ha : m.alloc sz al perm k ba init h1 h2 h3 = (bid, m')) :
    PtrValid m' p len := by
  rcases hv with ⟨b, off, blk, rfl, hb, hin⟩
  exact ⟨b, off, blk, rfl, blocks_preserve_alloc ha hb, hin⟩

theorem PtrValid.preserve_freeStack {m : Mem} {p : Val} {len : Nat} {blks : List BlockId}
    (hv : PtrValid m p len) (hnot : ∀ b off, p = .ptr b off → b ∉ blks) :
    PtrValid (m.freeStack blks) p len := by
  rcases hv with ⟨b, off, blk, rfl, hb, hin⟩
  exact ⟨b, off, blk, rfl, blocks_preserve_freeStack hb (hnot b off rfl), hin⟩

theorem PtrValid.preserve_roExt {m m' : Mem} {p : Val} {len : Nat}
    (hv : PtrValid m p len) (hro : ROExt m m') : PtrValid m' p len := by
  rcases hv with ⟨b, off, blk, rfl, hb, hin⟩
  exact ⟨b, off, blk, rfl, blocks_preserve_roExt hro hb, hin⟩

theorem PtrValid.preserve_frameBlocks {m m' : Mem} {p : Val} {len : Nat} {allowed : AutoBlockSet}
    (hv : PtrValid m p len) (hf : FrameBlocks m m' allowed)
    (hnot : ∀ b off, p = .ptr b off → b ∉ allowed) : PtrValid m' p len := by
  rcases hv with ⟨b, off, blk, rfl, hb, hin⟩
  exact ⟨b, off, blk, rfl, hf.blocks_eq hb (hnot b off rfl), hin⟩

theorem PtrWritable.preserve_writeBytes {m m' : Mem} {p : Val} {len : Nat}
    {b' : BlockId} {off' : Int64} {bs : List MemByte}
    (hw : PtrWritable m p len) (hwr : m.writeBytes b' off' bs = some m') : PtrWritable m' p len := by
  rcases hw with ⟨b, off, blk, rfl, hb, hp, hin⟩
  by_cases heq : b = b'
  · subst heq
    refine ⟨b, off, _, rfl, writeBytes_blocks_eq hb hwr, hp, ?_⟩
    simpa [Mem.inBounds] using hin
  · exact ⟨b, off, blk, rfl, blocks_preserve_writeBytes hwr hb heq, hp, hin⟩

theorem PtrWritable.preserve_writeVal {m m' : Mem} {p : Val} {len : Nat}
    {b' : BlockId} {off' : Int64} {ty : CTy} {v : Val}
    (hw : PtrWritable m p len) (hwr : Sem.writeVal m b' off' ty v = some m') :
    PtrWritable m' p len := by
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  exact hw.preserve_writeBytes hwb

theorem PtrWritable.preserve_writePlace {tags : TypeEnv} {m m' : Mem} {p : Val} {len : Nat}
    {b' : BlockId} {off' : Int64} {ty : CTy} {rv res : ExprRes}
    (hw : PtrWritable m p len) (hwr : writePlace tags m b' off' ty rv = some (res, m')) :
    PtrWritable m' p len := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes hwr
  exact hw.preserve_writeBytes hwb

theorem PtrWritable.preserve_alloc {m m' : Mem} {p : Val} {len : Nat}
    {sz al : Nat} {perm : Perm} {k : AllocKind} {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0} {bid : BlockId}
    (hw : PtrWritable m p len) (ha : m.alloc sz al perm k ba init h1 h2 h3 = (bid, m')) :
    PtrWritable m' p len := by
  rcases hw with ⟨b, off, blk, rfl, hb, hp, hin⟩
  exact ⟨b, off, blk, rfl, blocks_preserve_alloc ha hb, hp, hin⟩

theorem PtrWritable.preserve_freeStack {m : Mem} {p : Val} {len : Nat} {blks : List BlockId}
    (hw : PtrWritable m p len) (hnot : ∀ b off, p = .ptr b off → b ∉ blks) :
    PtrWritable (m.freeStack blks) p len := by
  rcases hw with ⟨b, off, blk, rfl, hb, hp, hin⟩
  exact ⟨b, off, blk, rfl, blocks_preserve_freeStack hb (hnot b off rfl), hp, hin⟩

theorem PtrWritable.preserve_roExt {m m' : Mem} {p : Val} {len : Nat}
    (hw : PtrWritable m p len) (hro : ROExt m m') : PtrWritable m' p len := by
  rcases hw with ⟨b, off, blk, rfl, hb, hp, hin⟩
  exact ⟨b, off, blk, rfl, blocks_preserve_roExt hro hb, hp, hin⟩

theorem PtrWritable.preserve_frameBlocks {m m' : Mem} {p : Val} {len : Nat} {allowed : AutoBlockSet}
    (hw : PtrWritable m p len) (hf : FrameBlocks m m' allowed)
    (hnot : ∀ b off, p = .ptr b off → b ∉ allowed) : PtrWritable m' p len := by
  rcases hw with ⟨b, off, blk, rfl, hb, hp, hin⟩
  exact ⟨b, off, blk, rfl, hf.blocks_eq hb (hnot b off rfl), hp, hin⟩

theorem LocalFrameMem.writeVal_stack {m0 m m' : Mem} {blks : List BlockId}
    {b : BlockId} {off : Int64} {ty : CTy} {v : Val} {blk : Block}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hb : m.blocks b = some blk) (hwr : Sem.writeVal m b off ty v = some m') :
    LocalFrameMem m0 m' blks := by
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  exact hf.write_stack hmem hb hwb

theorem LocalFrameMem.writePlace_stack {tags : TypeEnv} {m0 m m' : Mem} {blks : List BlockId}
    {b : BlockId} {off : Int64} {ty : CTy} {rv res : ExprRes} {blk : Block}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hb : m.blocks b = some blk) (hwr : writePlace tags m b off ty rv = some (res, m')) :
    LocalFrameMem m0 m' blks := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes hwr
  exact hf.write_stack hmem hb hwb

/-! ### `Slot` Preservation -/

private theorem readVal_congr_block {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {blk : Block} (h1 : m1.blocks b = some blk) (h2 : m2.blocks b = some blk) :
    Sem.readVal tags m2 b off ty = Sem.readVal tags m1 b off ty := by
  unfold Sem.readVal
  cases ty.unqual <;> simp only [h1, h2, Mem.readBytes, bind, Option.bind]

private theorem readVal_writeBytes_disjoint (tags : TypeEnv) {m m' : Mem} {b : BlockId}
    {off woff : Int64} {bs : List MemByte} {ty : CTy} {blk : Block}
    (hb : m.blocks b = some blk) (hwr : m.writeBytes b woff bs = some m')
    (h0_off : 0 ≤ off.toInt) (h0_woff : 0 ≤ woff.toInt)
    (hdis : off.toInt + sizeofTy tags ty ≤ woff.toInt ∨
            woff.toInt + bs.length ≤ off.toInt) :
    Sem.readVal tags m' b off ty = Sem.readVal tags m b off ty := by
  have hblk' := writeBytes_blocks_eq hb hwr
  let blk' : Block := { blk with bytes := (fun i =>
    if woff.toInt.toNat ≤ i ∧ i < woff.toInt.toNat + bs.length then
      bs[i - woff.toInt.toNat]?.getD .undef
    else blk.bytes i) }
  have hblk'_eq : m'.blocks b = some blk' := hblk'
  have hsz_eq : ∀ len : Nat, len ≤ sizeofTy tags ty →
      m'.readBytes b off len = m.readBytes b off len := by
    intro len hlen
    unfold Mem.readBytes
    rw [hb, hblk'_eq]
    dsimp only [bind, Option.bind, pure, Pure.pure]
    have hin_eq : Mem.inBounds blk' off len = Mem.inBounds blk off len := rfl
    rw [hin_eq]
    cases hin : Mem.inBounds blk off len
    · exact Eq.trans (rfl : _ = (none : Option (List MemByte))) rfl
    · simp only [guard_true, Option.some.injEq]
      apply List.map_congr_left
      intro i hi
      have hil : i < len := List.mem_range.mp hi
      have hnot : ¬ (woff.toInt.toNat ≤ off.toInt.toNat + i ∧
          off.toInt.toNat + i < woff.toInt.toNat + bs.length) := by
        omega
      dsimp only [blk']
      by_cases hcond : woff.toInt.toNat ≤ off.toInt.toNat + i ∧
          off.toInt.toNat + i < woff.toInt.toNat + bs.length
      · exact False.elim (hnot hcond)
      · simp only [eq_false hcond, ↓reduceIte]
  unfold Sem.readVal
  cases hu : ty.unqual with
  | array _ _ => rfl
  | int k =>
    have hlen : k.bytes ≤ sizeofTy tags ty := by
      rw [← sizeofTy_unqual, hu]; simp [sizeofTy, sizeofAux]
    have hrb := hsz_eq k.bytes hlen
    have hal : Mem.isAligned blk' off k.align = Mem.isAligned blk off k.align := rfl
    simp only [CTy.unqual, CTy.intKind?, hb, hblk'_eq, hal, hrb, bind, Option.bind]
  | enumTy _ isU =>
    have hlen : (if isU then IntKind.u32 else .i32).bytes ≤ sizeofTy tags ty := by
      rw [← sizeofTy_unqual, hu]; cases isU <;> simp [sizeofTy, sizeofAux, IntKind.bytes] <;> decide
    have hrb := hsz_eq (if isU then IntKind.u32 else .i32).bytes hlen
    have hal : Mem.isAligned blk' off (if isU then IntKind.u32 else .i32).align =
        Mem.isAligned blk off (if isU then IntKind.u32 else .i32).align := rfl
    simp only [CTy.unqual, CTy.intKind?, hb, hblk'_eq, hal, hrb, bind, Option.bind]
  | ptr _ =>
    have hlen : 8 ≤ sizeofTy tags ty := by rw [← sizeofTy_unqual, hu]; simp [sizeofTy, sizeofAux]
    have hrb := hsz_eq 8 hlen
    have hal : Mem.isAligned blk' off 8 = Mem.isAligned blk off 8 := rfl
    simp only [hb, hblk'_eq, hal, hrb, bind, Option.bind]
  | fnPtr _ _ _ =>
    have hlen : 8 ≤ sizeofTy tags ty := by
      rw [← sizeofTy_unqual, hu]; simp [sizeofTy, sizeofAux]
    have hrb := hsz_eq 8 hlen
    have hal : Mem.isAligned blk' off 8 = Mem.isAligned blk off 8 := rfl
    simp only [hb, hblk'_eq, hal, hrb, bind, Option.bind]
  | vaList =>
    have hlen : sizeofTy tags .vaList ≤ sizeofTy tags ty := by
      have hsub : sizeofTy tags .vaList = sizeofTy tags ty.unqual := by rw [hu]
      rw [hsub, sizeofTy_unqual]
      exact Nat.le_refl _
    have hrb := hsz_eq (sizeofTy tags .vaList) hlen
    simp only [sizeofTy, sizeofAux, bind, Option.bind] at hrb ⊢
    rw [hrb]
  | _ => rfl

theorem Slot.preserve_env_cons {env : Env} {m : Mem} {name dname : String}
    {b db : BlockId} {ty dty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hne : name ≠ dname) :
    Slot ((dname, db, dty) :: env) m name b ty P := by
  rcases hs with ⟨hl, rest⟩
  refine ⟨?_, rest⟩
  have hbeq : (name == dname) = false := beq_false_of_ne hne
  unfold List.lookup
  simp [hbeq]
  exact hl

theorem Slot.unpush_env {env : Env} {m : Mem} {name dname : String}
    {b db : BlockId} {ty dty : CTy} {P : Val → Prop}
    (hs : Slot ((dname, db, dty) :: env) m name b ty P) (hne : name ≠ dname) :
    Slot env m name b ty P := by
  rcases hs with ⟨hl, rest⟩
  refine ⟨?_, rest⟩
  have hbeq : (name == dname) = false := beq_false_of_ne hne
  unfold List.lookup at hl
  simp [hbeq] at hl
  exact hl

theorem Slot.preserve_mem_eq_block {env : Env} {m m' : Mem} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hblk : m'.blocks b = m.blocks b) :
    Slot env m' name b ty P := by
  rcases hs with ⟨hl, blk, hb, hp, hin, hal, hval⟩
  have hb' : m'.blocks b = some blk := hblk.trans hb
  refine ⟨hl, blk, hb', hp, hin, hal, ?_⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · exact Or.inl ⟨v, by rw [readVal_congr_block hb hb']; exact hrd, hpv⟩
  · exact Or.inr hundef

theorem Slot.preserve_writeBytes {env : Env} {m m' : Mem} {name : String}
    {b b' : BlockId} {off' : Int64} {bs : List MemByte} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hwr : m.writeBytes b' off' bs = some m') (hne : b ≠ b') :
    Slot env m' name b ty P :=
  hs.preserve_mem_eq_block (writeBytes_blocks_ne hwr hne)

theorem Slot.preserve_writeVal {env : Env} {m m' : Mem} {name : String}
    {b b' : BlockId} {off' : Int64} {tyw ty : CTy} {v : Val} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hwr : Sem.writeVal m b' off' tyw v = some m') (hne : b ≠ b') :
    Slot env m' name b ty P :=
  hs.preserve_mem_eq_block (writeVal_blocks_ne hwr hne)

theorem Slot.preserve_writePlace {tags : TypeEnv} {env : Env} {m m' : Mem} {name : String}
    {b b' : BlockId} {off' : Int64} {tyw ty : CTy} {rv res : ExprRes} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hwr : writePlace tags m b' off' tyw rv = some (res, m'))
    (hne : b ≠ b') : Slot env m' name b ty P := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes hwr
  exact hs.preserve_writeBytes hwb hne

theorem Slot.preserve_alloc {env : Env} {m m' : Mem} {name : String}
    {b bid : BlockId} {ty : CTy} {P : Val → Prop}
    {sz al : Nat} {perm : Perm} {k : AllocKind} {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0}
    (hs : Slot env m name b ty P) (ha : m.alloc sz al perm k ba init h1 h2 h3 = (bid, m')) :
    Slot env m' name b ty P := by
  rcases hs with ⟨hl, blk, hb, hp, hin, hal, hval⟩
  have hm' : m' = (m.alloc sz al perm k ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hb)
  have heq : m'.blocks b = m.blocks b := by
    rw [hm']; exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne
  refine ⟨hl, blk, heq.trans hb, hp, hin, hal, ?_⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · exact Or.inl ⟨v, by rw [readVal_congr_block hb (heq.trans hb)]; exact hrd, hpv⟩
  · exact Or.inr hundef

theorem Slot.preserve_freeStack {env : Env} {m : Mem} {blks : List BlockId} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hnot : b ∉ blks) :
    Slot env (m.freeStack blks) name b ty P :=
  hs.preserve_mem_eq_block (freeStack_blocks_not_mem m blks hnot)

theorem Slot.preserve_roExt {env : Env} {m m' : Mem} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hro : ROExt m m') :
    Slot env m' name b ty P := by
  have ⟨_, _, hb, _⟩ := hs
  exact hs.preserve_mem_eq_block (hro.2.1 b (lt_nextBlock_of_some hb))

theorem Slot.preserve_frameBlocks {env : Env} {m m' : Mem} {allowed : AutoBlockSet} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hf : FrameBlocks m m' allowed) (hnot : b ∉ allowed) :
    Slot env m' name b ty P := by
  have ⟨_, _, hb, _⟩ := hs
  exact hs.preserve_mem_eq_block (hf.2.1 b (lt_nextBlock_of_some hb) hnot)

theorem Slot.preserve_localDecl_none {env : Env} {m m' : Mem} {name : String}
    {b bid : BlockId} {ty : CTy} {P : Val → Prop}
    {d : VarDecl} {sz al : Nat} {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0}
    (hs : Slot env m name b ty P) (hne : name ≠ d.name)
    (ha : m.alloc sz al .rw .stack ba init h1 h2 h3 = (bid, m')) :
    Slot ((d.name, bid, d.ty) :: env) m' name b ty P :=
  (hs.preserve_alloc ha).preserve_env_cons hne

/-! ### `Field` Preservation -/

theorem Field.preserve_mem_eq_block {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) (hblk : m'.blocks b = m.blocks b) :
    Field tags m' b off structTag fld fty P := by
  rcases hf with ⟨foff, blk, hfl, hb, hp, h0, hsz, hal, hval⟩
  have hb' : m'.blocks b = some blk := hblk.trans hb
  refine ⟨foff, blk, hfl, hb', hp, h0, hsz, hal, ?_⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · exact Or.inl ⟨v, by rw [readVal_congr_block hb hb']; exact hrd, hpv⟩
  · exact Or.inr hundef

theorem Field.preserve_writeBytes_ne {tags : TypeEnv} {m m' : Mem} {b b' : BlockId}
    {off woff : Int64} {bs : List MemByte} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P)
    (hwr : m.writeBytes b' woff bs = some m') (hne : b ≠ b') :
    Field tags m' b off structTag fld fty P :=
  hf.preserve_mem_eq_block (writeBytes_blocks_ne hwr hne)

theorem Field.preserve_writeVal_ne {tags : TypeEnv} {m m' : Mem} {b b' : BlockId}
    {off woff : Int64} {tyw : CTy} {v : Val} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P)
    (hwr : Sem.writeVal m b' woff tyw v = some m') (hne : b ≠ b') :
    Field tags m' b off structTag fld fty P :=
  hf.preserve_mem_eq_block (writeVal_blocks_ne hwr hne)

theorem Field.preserve_writePlace_ne {tags : TypeEnv} {m m' : Mem} {b b' : BlockId}
    {off woff : Int64} {tyw : CTy} {rv res : ExprRes}
    {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P)
    (hwr : writePlace tags m b' woff tyw rv = some (res, m')) (hne : b ≠ b') :
    Field tags m' b off structTag fld fty P := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes hwr
  exact hf.preserve_writeBytes_ne hwb hne

theorem Field.preserve_writeBytes_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {off woff : Int64} {bs : List MemByte} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    {foff : Nat}
    (hf : Field tags m b off structTag fld fty P)
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hwr : m.writeBytes b woff bs = some m')
    (hw0 : 0 ≤ woff.toInt)
    (hdis : off.toInt + foff + sizeofTy tags fty ≤ woff.toInt ∨
            woff.toInt + bs.length ≤ off.toInt + foff) :
    Field tags m' b off structTag fld fty P := by
  rcases hf with ⟨foff0, blk, hfl0, hb, hp, h0, hsz, hal, hval⟩
  rw [hfl] at hfl0
  cases hfl0
  have hlt : off.toInt + foff < ptrDiffLimit := by
    have := blk.sizeLt; omega
  have hfld_off : (Int64.ofInt (off.toInt + foff)).toInt = off.toInt + foff :=
    int64_ofInt_toInt (by omega) hlt
  have hblk' := writeBytes_blocks_eq hb hwr
  refine ⟨foff, _, hfl, hblk', hp, h0, hsz, by simpa [Mem.isAligned] using hal, ?_⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · refine Or.inl ⟨v, ?_, hpv⟩
    rw [readVal_writeBytes_disjoint tags hb hwr (by omega) hw0]
    · exact hrd
    · rw [hfld_off]; exact hdis
  · exact Or.inr hundef

theorem Field.preserve_writeVal_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {off woff : Int64} {tyw : CTy} {wv : Val}
    {structTag fld : String} {fty : CTy} {P : Val → Prop} {foff : Nat}
    (hf : Field tags m b off structTag fld fty P)
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hwr : Sem.writeVal m b woff tyw wv = some m')
    (hw0 : 0 ≤ woff.toInt)
    (hdis : off.toInt + foff + sizeofTy tags fty ≤ woff.toInt ∨
            woff.toInt + sizeofTy tags tyw ≤ off.toInt + foff) :
    Field tags m' b off structTag fld fty P := by
  obtain ⟨bs, hwb, hlen⟩ := writeVal_writeBytes_len tags hwr
  rw [← hlen] at hdis
  exact hf.preserve_writeBytes_disjoint hfl hwb hw0 hdis

theorem Field.preserve_writePlace_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {off woff : Int64} {tyw : CTy} {rv res : ExprRes}
    {structTag fld : String} {fty : CTy} {P : Val → Prop} {foff : Nat}
    (hf : Field tags m b off structTag fld fty P)
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hwr : writePlace tags m b woff tyw rv = some (res, m'))
    (hw0 : 0 ≤ woff.toInt)
    (hdis : off.toInt + foff + sizeofTy tags fty ≤ woff.toInt ∨
            woff.toInt + sizeofTy tags tyw ≤ off.toInt + foff) :
    Field tags m' b off structTag fld fty P := by
  obtain ⟨bs, hwb, hlen⟩ := writePlace_writeBytes_len hwr
  rw [← hlen] at hdis
  exact hf.preserve_writeBytes_disjoint hfl hwb hw0 hdis

theorem Field.preserve_alloc {tags : TypeEnv} {m m' : Mem} {b bid : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {P : Val → Prop}
    {sz al : Nat} {perm : Perm} {k : AllocKind} {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0}
    (hf : Field tags m b off structTag fld fty P)
    (ha : m.alloc sz al perm k ba init h1 h2 h3 = (bid, m')) :
    Field tags m' b off structTag fld fty P := by
  have ⟨_, _, _, hb, _⟩ := hf
  exact hf.preserve_mem_eq_block (by
    have hm' : m' = (m.alloc sz al perm k ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
    rw [hm']
    exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ (Nat.ne_of_lt (lt_nextBlock_of_some hb)))

theorem Field.preserve_freeStack {tags : TypeEnv} {m : Mem} {blks : List BlockId}
    {b : BlockId} {off : Int64} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) (hnot : b ∉ blks) :
    Field tags (m.freeStack blks) b off structTag fld fty P :=
  hf.preserve_mem_eq_block (freeStack_blocks_not_mem m blks hnot)

theorem Field.preserve_roExt {tags : TypeEnv} {m m' : Mem}
    {b : BlockId} {off : Int64} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) (hro : ROExt m m') :
    Field tags m' b off structTag fld fty P := by
  have ⟨_, _, _, hb, _⟩ := hf
  exact hf.preserve_mem_eq_block (hro.2.1 b (lt_nextBlock_of_some hb))

theorem Field.preserve_frameBlocks {tags : TypeEnv} {m m' : Mem} {allowed : AutoBlockSet}
    {b : BlockId} {off : Int64} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P)
    (hfr : FrameBlocks m m' allowed) (hnot : b ∉ allowed) :
    Field tags m' b off structTag fld fty P := by
  have ⟨_, _, _, hb, _⟩ := hf
  exact hf.preserve_mem_eq_block (hfr.2.1 b (lt_nextBlock_of_some hb) hnot)

/-! ### `Field` Constructors -/

theorem Field.mk_uninit {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {foff : Nat} {blk : Block}
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hb : m.blocks b = some blk) (hrw : fty.isConst = false → blk.perm = .rw)
    (h0 : 0 ≤ off.toInt) (hsz : off.toInt + foff + sizeofTy tags fty ≤ blk.size)
    (hal : Mem.isAligned blk (Int64.ofInt (off.toInt + foff)) (max 1 (alignofTy tags fty)) = true) :
    Field tags m b off structTag fld fty (· = .undef) :=
  ⟨foff, blk, hfl, hb, hrw, h0, hsz, hal, Or.inr rfl⟩

theorem Field.mk_val {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {P : Val → Prop} {foff : Nat} {blk : Block} {v : Val}
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hb : m.blocks b = some blk) (hrw : fty.isConst = false → blk.perm = .rw)
    (h0 : 0 ≤ off.toInt) (hsz : off.toInt + foff + sizeofTy tags fty ≤ blk.size)
    (hal : Mem.isAligned blk (Int64.ofInt (off.toInt + foff)) (max 1 (alignofTy tags fty)) = true)
    (hrd : Sem.readVal tags m b (Int64.ofInt (off.toInt + foff)) fty = some v) (hp : P v) :
    Field tags m b off structTag fld fty P :=
  ⟨foff, blk, hfl, hb, hrw, h0, hsz, hal, Or.inl ⟨v, hrd, hp⟩⟩

/-! ## 5. Verified `WPTerm` Statement & Expression Stepping Lemmas -/

/-! ### Statements and Continuations -/

theorem wp_block_nil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.block [])) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_block_cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {hd : CStmt} {tl : List CStmt}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.stmt hd) env [] m os
        (if tl.isEmpty then .blockEnd env blks k else .stmts tl (.blockEnd env blks k)))) :
    WPTerm prog cfg ext Q (.running (.stmt (.block (hd :: tl))) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_stmts_cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {s : CStmt} {ss : List CStmt}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt s) env blks m os (.stmts ss k))) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.stmts (s :: ss) k)) :=
  WPTerm.of_det rfl hw

theorem wp_stmts_nil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.stmts [] k)) :=
  WPTerm.of_det rfl hw

theorem wp_blockEnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env savedEnv : Env} {blks savedBlks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) savedEnv savedBlks (m.freeStack blks) os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.blockEnd savedEnv savedBlks k)) :=
  WPTerm.of_det rfl hw

theorem wp_nop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {rt : CTy}
    (hq : Q (if rt.isVoid then .void else .undef) (m.freeStack blks) os) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.stop rt)) :=
  WPTerm.of_det rfl (.returned hq)

theorem wp_nop_switchCont {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.switchCont k)) :=
  WPTerm.of_det rfl hw

theorem wp_nop_loop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c? stp? : Option CExpr} {body : CStmt} {isDo : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (loopNext c? stp? body isDo env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.loop c? stp? body isDo k)) :=
  WPTerm.of_det rfl hw

theorem wp_nop_callFrame {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env re : Env} {blks rb : List BlockId} {rt : CTy} {fnBody : CStmt}
    {fs : List ExprFrame} {ctx : ExprCtx} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) ctx [])
        re rb (m.freeStack blks) os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.callFrame re rb rt fnBody fs ctx k)) :=
  WPTerm.of_det rfl hw

theorem wp_expr_stmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {e : CExpr} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval e []) .discard []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr e)) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_expr_discard {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {rv : ExprRes} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret rv []) .discard mods) env blks m os k) :=
  WPTerm.of_det (by cases rv with | rval v _ => cases v <;> rfl | _ => rfl) hw

theorem wp_decl {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt (.decls [d])) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decl d)) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_decls_nil {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls [])) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_decls_static {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rest : List VarDecl}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = true)
    (hw : WPTerm prog cfg ext Q (.running (.stmt (.decls rest)) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [hst]) hw

theorem wp_decls_cons_init {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {e : CExpr} {rest : List VarDecl}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = false) (hinit : d.init? = some (.expr e))
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval e []) (.varInit d rest) []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [hst, hinit]) hw

private theorem scalarSizeAlign_le_max1 (tags : TypeEnv) (ty : CTy) :
    (scalarSizeAlign ty).1 ≤ max 1 (sizeofTy tags ty) := by
  unfold scalarSizeAlign
  cases hu : ty.unqual
  · exact Nat.le_max_left _ _
  · rw [← sizeofTy_unqual, hu]; simp [IntKind.bytes]; cases ‹IntKind› <;> decide
  · exact Nat.le_max_left _ _
  · rw [← sizeofTy_unqual, hu]; simp
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _
  · rw [← sizeofTy_unqual, hu]; simp [sizeofTy, sizeofAux, IntKind.bytes]; cases ‹Bool› <;> decide
  · rw [← sizeofTy_unqual, hu]; simp [sizeofTy, sizeofAux]
  · rw [← sizeofTy_unqual, hu]; simp [sizeofTy, sizeofAux]
  · exact Nat.le_max_left _ _

private theorem scalarSizeAlign_dvd_max1 (tags : TypeEnv) (ty : CTy) :
    (scalarSizeAlign ty).2 ∣ max 1 (alignofTy tags ty) := by
  unfold scalarSizeAlign
  cases hu : ty.unqual
  · exact Nat.one_dvd _
  · rw [← alignofTy_unqual, hu]; simp [IntKind.align, IntKind.bytes]; cases ‹IntKind› <;> decide
  · exact Nat.one_dvd _
  · rw [← alignofTy_unqual, hu]; simp
  · exact Nat.one_dvd _
  · exact Nat.one_dvd _
  · exact Nat.one_dvd _
  · exact Nat.one_dvd _
  · exact Nat.one_dvd _
  · rw [← alignofTy_unqual, hu]; simp [alignofTy, alignofAux, IntKind.align, IntKind.bytes]; cases ‹Bool› <;> decide
  · rw [← alignofTy_unqual, hu]; simp [alignofTy, alignofAux]
  · rw [← alignofTy_unqual, hu]; simp [alignofTy, alignofAux]
  · exact Nat.one_dvd _

private theorem slot_alloc_uninit {tags : TypeEnv} {m m1 : Mem} {d : VarDecl}
    {env : Env} {base : UInt64}
    {hsz : max 1 (sizeofTy tags d.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags d.ty)}
    {hba : base.toNat % max 1 (alignofTy tags d.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (m.nextBlock, m1)) :
    Slot ((d.name, m.nextBlock, d.ty) :: env) m1 d.name m.nextBlock d.ty (· = .undef) := by
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hblk : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy tags d.ty),
      max 1 (alignofTy tags d.ty), .rw, .stack, base, fun _ => .undef, hsz, hal, hba⟩ := by
    rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  refine ⟨by simp [List.lookup], _, hblk, fun _ => rfl, ?_, ?_, Or.inr rfl⟩
  · rw [inBounds_iff]
    exact ⟨Int.le_refl _, by simpa [Int64.toInt_zero] using scalarSizeAlign_le_max1 tags d.ty⟩
  · rw [isAligned_iff]
    refine ⟨Int.le_refl _, ?_, ?_⟩
    · cases hu : d.ty.unqual <;> simp only [scalarSizeAlign, hu]
      · decide
      · cases ‹IntKind› <;> decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · decide
      · cases ‹Bool› <;> decide
      · decide
      · decide
      · decide
    · rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (scalarSizeAlign_dvd_max1 tags d.ty) (Nat.dvd_of_mod_eq_zero hba))

theorem wp_localDecl_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rest : List VarDecl}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = false) (hinit : d.init? = none)
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (m.nextBlock, m1) →
      Slot ((d.name, m.nextBlock, d.ty) :: env) m1 d.name m.nextBlock d.ty (· = .undef) →
      FrameBlocks m m1 {m.nextBlock} →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m1 os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) := by
  refine WPTerm.of_localDecl_none (rest := rest) (env := env) (blks := blks) (m := m) (os := os) (k := k)
    (by unfold stepDet; dsimp only; rw [hst, hinit]; rfl) hsz hal ?_
  intro base bid m1 hba ha
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  subst hbid
  exact hw base m1 hba ha (slot_alloc_uninit ha) (FrameBlocks.of_alloc ha)

theorem wp_localDecl_int_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rest : List VarDecl} {ik : IntKind}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = false) (hinit : d.init? = none) (hik : d.ty.intKind? = some ik)
    (hw : ∀ (base : UInt64) (m1 : Mem)
      (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
      (hal : 0 < max 1 (alignofTy prog.tags d.ty))
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (m.nextBlock, m1) →
      Slot.uninit ((d.name, m.nextBlock, d.ty) :: env) m1 d.name m.nextBlock d.ty →
      FrameBlocks m m1 {m.nextBlock} →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m1 os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_scalar prog.tags hik]; cases ik <;> decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_scalar prog.tags hik]; cases ik <;> decide
  exact wp_localDecl_none hst hinit hsz hal (fun base m1 hba ha hs hf =>
    hw base m1 hsz hal hba ha hs hf)

theorem wp_localDecl_ptr_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rest : List VarDecl} {el : CTy}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = false) (hinit : d.init? = none) (hptr : d.ty.unqual = .ptr el)
    (hw : ∀ (base : UInt64) (m1 : Mem)
      (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
      (hal : 0 < max 1 (alignofTy prog.tags d.ty))
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (m.nextBlock, m1) →
      Slot.uninit ((d.name, m.nextBlock, d.ty) :: env) m1 d.name m.nextBlock d.ty →
      FrameBlocks m m1 {m.nextBlock} →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m1 os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_ptr_auto prog.tags hptr]; decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_ptr_auto prog.tags hptr]; decide
  exact wp_localDecl_none hst hinit hsz hal (fun base m1 hba ha hs hf =>
    hw base m1 hsz hal hba ha hs hf)

theorem wp_localDecl_init {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rv : ExprRes} {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (alignofTy prog.tags d.ty))
    (hw : ∀ (base : UInt64) (m1 : Mem)
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (m.nextBlock, m1) →
      ∃ r m2, writePlace prog.tags m1 m.nextBlock 0 d.ty.stripConst rv = some (r, m2) ∧
        WPTerm prog cfg ext Q
          (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret rv []) (.varInit d rest) mods) env blks m os k) := by
  refine WPTerm.of_localDecl_some (rv := rv) (rest := rest) (env := env) (blks := blks) (m := m) (os := os) (k := k)
    (by cases rv with | rval v _ => cases v <;> rfl | _ => rfl) hsz hal ?_
  intro base bid m1 hba ha
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  subst hbid
  exact hw base m1 hba ha

private theorem writePlace_int_slot {tags : TypeEnv} {m m1 m2 : Mem} {d : VarDecl}
    {env : Env} {ik k1 : IntKind} {bv : BitVec k1.bits} {vty : CTy}
    {base : UInt64}
    {hsz : max 1 (sizeofTy tags d.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags d.ty)}
    {hba : base.toNat % max 1 (alignofTy tags d.ty) = 0}
    (hik : d.ty.intKind? = some ik)
    (ha : m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba = (m.nextBlock, m1))
    (hwr : Sem.writeVal m1 m.nextBlock 0 d.ty.stripConst
      (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) = some m2) :
    writePlace tags m1 m.nextBlock 0 d.ty.stripConst (.rval (.int k1 bv) vty) =
      some (.rval (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) d.ty.stripConst, m2) ∧
    Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty
      (· = .int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) ∧
    FrameBlocks m m2 {m.nextBlock} := by
  have hu_int : d.ty.stripConst.unqual = .int ik ∨ ∃ tag isU, d.ty.stripConst.unqual = .enumTy tag isU := by
    unfold CTy.intKind? at hik
    rw [← stripConst_unqual] at hik
    cases hu : d.ty.stripConst.unqual <;> simp [hu] at hik
    · exact Or.inl (hik ▸ rfl)
    · exact Or.inr ⟨_, _, rfl⟩
  have hcast : castVal m1 d.ty.stripConst (.int k1 bv) =
      some (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) := by
    unfold castVal
    rcases hu_int with hu | ⟨tag, isU, hu⟩
    · simp only [hu, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte,
        ofIntCast, intToInt]
    · unfold CTy.intKind? at hik
      rw [← stripConst_unqual, hu] at hik
      have hki : (if isU then IntKind.u32 else .i32) = ik := Option.some.inj hik
      simp only [hu, CTy.isVoid, CTy.unqual, CTy.intKind?, hki, Bool.false_eq_true, ↓reduceIte,
        ofIntCast, intToInt]
  have hwp : writePlace tags m1 m.nextBlock 0 d.ty.stripConst (.rval (.int k1 bv) vty) =
      some (.rval (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) d.ty.stripConst, m2) := by
    unfold writePlace
    rcases hu_int with hu | ⟨tag, isU, hu⟩
    · simp [hu, hcast, hwr, bind, Option.bind, pure, Pure.pure]
    · simp [hu, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy tags d.ty),
      max 1 (alignofTy tags d.ty), .rw, .stack, base, fun _ => .undef, hsz, hal, hba⟩ := by
    rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hik_strip : d.ty.stripConst.intKind? = some ik := by
    unfold CTy.intKind? at hik ⊢
    rw [stripConst_unqual]
    exact hik
  have hrd : Sem.readVal [] m2 m.nextBlock 0 d.ty =
      some (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) :=
    readVal_writeVal_same_int' [] (by rw [stripConst_unqual]) hik_strip hblk1 hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk2 := writeBytes_blocks_eq hblk1 hwb
  have hslot : Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty
      (· = .int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) := by
    refine ⟨by simp [List.lookup], _, hblk2, fun _ => rfl, ?_, ?_, Or.inl ⟨_, hrd, rfl⟩⟩
    · rw [inBounds_iff]
      exact ⟨Int.le_refl _, by simpa [Int64.toInt_zero] using scalarSizeAlign_le_max1 tags d.ty⟩
    · rw [isAligned_iff]
      dsimp only
      refine ⟨Int.le_refl _, ?_, ?_⟩
      · cases hu : d.ty.unqual <;> simp only [scalarSizeAlign, hu]
        · decide
        · cases ‹IntKind› <;> decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · cases ‹Bool› <;> decide
        · decide
        · decide
        · decide
      · rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (scalarSizeAlign_dvd_max1 tags d.ty) (Nat.dvd_of_mod_eq_zero hba))
  have hfr : FrameBlocks m m2 {m.nextBlock} :=
    FrameBlocks.trans_same (FrameBlocks.of_alloc ha) (FrameBlocks.of_writeVal hwr)
  exact ⟨hwp, hslot, hfr⟩

theorem wp_localDecl_init_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {ik k1 : IntKind} {bv : BitVec k1.bits} {vty : CTy}
    {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : d.ty.intKind? = some ik)
    (hw : ∀ (m2 : Mem) (newBv : BitVec ik.bits),
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)) →
      Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = .int ik newBv) →
      FrameBlocks m m2 {m.nextBlock} →
      (∀ b, b ≠ m.nextBlock → m2.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k1 bv) vty) []) (.varInit d rest) mods) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_scalar prog.tags hik]; cases ik <;> decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_scalar prog.tags hik]; cases ik <;> decide
  refine wp_localDecl_init hsz hal ?_
  intro base m1 hba ha
  have hsz' : max 1 (sizeofTy prog.tags d.ty.stripConst) < ptrDiffLimit := by
    rw [← sizeofTy_unqual, stripConst_unqual, sizeofTy_unqual]; exact hsz
  have hal' : 0 < max 1 (alignofTy prog.tags d.ty.stripConst) := by
    rw [← alignofTy_unqual, stripConst_unqual, alignofTy_unqual]; exact hal
  have hba' : base.toNat % max 1 (alignofTy prog.tags d.ty.stripConst) = 0 := by
    rw [← alignofTy_unqual, stripConst_unqual, alignofTy_unqual]; exact hba
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy prog.tags d.ty),
      max 1 (alignofTy prog.tags d.ty), .rw, .stack, base, fun _ => .undef, hsz, hal, hba⟩ := by
    rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_le : ik.bytes ≤ max 1 (sizeofTy prog.tags d.ty) := by
    rw [sizeofTy_eq_scalar prog.tags hik]; exact Nat.le_max_right _ _
  have hal_eq : ik.align = max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_scalar prog.tags hik]; cases ik <;> rfl
  obtain ⟨m2, hwr⟩ := writeVal_int_some' (stripConst_isConst d.ty)
    (by simpa [CTy.intKind?, stripConst_unqual] using hik) hblk1 rfl
    (by rw [isAligned_iff]
        exact ⟨Int.le_refl _, by cases ik <;> decide,
          by rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero, hal_eq]; exact hba⟩)
    (by rw [inBounds_iff]; exact ⟨Int.le_refl _, by simpa [Int64.toInt_zero] using hsz_le⟩)
    (valAsInt?_int_toInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)))
  obtain ⟨hwp, hslot, hfr⟩ := writePlace_int_slot hik ha hwr
  refine ⟨_, m2, hwp, hw m2 _ rfl hslot hfr ?_⟩
  intro b hne
  rw [writeVal_blocks_ne hwr hne, hm1]
  exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne

theorem wp_localDecl_init_int_same {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {ik : IntKind} {bv : BitVec ik.bits} {vty : CTy}
    {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : d.ty.intKind? = some ik)
    (hw : ∀ (m2 : Mem),
      Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = .int ik bv) →
      FrameBlocks m m2 {m.nextBlock} →
      (∀ b, b ≠ m.nextBlock → m2.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) []) (.varInit d rest) mods) env blks m os k) := by
  refine wp_localDecl_init_int hik ?_
  intro m2 newBv heq hslot hfr hblks
  have hbv : newBv = bv := eq_of_intToInt_eq (by simpa [ofInt_intToInt] using heq)
  subst hbv
  exact hw m2 hslot hfr hblks

theorem wp_localDecl_init_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {el : CTy} {v : Val} {vty : CTy}
    {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hptr : d.ty.unqual = .ptr el)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hw : ∀ (m2 : Mem),
      Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = v) →
      FrameBlocks m m2 {m.nextBlock} →
      (∀ b, b ≠ m.nextBlock → m2.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) []) (.varInit d rest) mods) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_ptr_auto prog.tags hptr]; decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_ptr_auto prog.tags hptr]; decide
  refine wp_localDecl_init hsz hal ?_
  intro base m1 hba ha
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy prog.tags d.ty),
      max 1 (alignofTy prog.tags d.ty), .rw, .stack, base, fun _ => .undef, hsz, hal, hba⟩ := by
    rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz8 : sizeofTy prog.tags d.ty = 8 := sizeofTy_eq_ptr_auto prog.tags hptr
  have hal8 : alignofTy prog.tags d.ty = 8 := alignofTy_eq_ptr_auto prog.tags hptr
  obtain ⟨m2, hwr⟩ := writeVal_ptr_some (stripConst_isConst d.ty)
    (by rw [stripConst_unqual, hptr]) hblk1 rfl
    (by rw [isAligned_iff]
        exact ⟨Int.le_refl _, by decide, by rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]; simpa [hal8] using hba⟩)
    (by rw [inBounds_iff]; exact ⟨Int.le_refl _, by simp [Int64.toInt_zero, hsz8]⟩)
    hv
  have hcast : castVal m1 d.ty.stripConst v = some v := by
    unfold castVal
    rcases hv with rfl | ⟨pb, poff, rfl⟩
    · simp only [stripConst_unqual, hptr, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]
    · simp only [stripConst_unqual, hptr, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]
  have hwp : writePlace prog.tags m1 m.nextBlock 0 d.ty.stripConst (.rval v vty) =
      some (.rval v d.ty.stripConst, m2) := by
    unfold writePlace
    simp [stripConst_unqual, hptr, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hrd : Sem.readVal [] m2 m.nextBlock 0 d.ty = some v :=
    readVal_writeVal_same_ptr' [] (by rw [stripConst_unqual, hptr]) hptr hblk1 hv hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk2 := writeBytes_blocks_eq hblk1 hwb
  have hslot : Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = v) := by
    refine ⟨by simp [List.lookup], _, hblk2, fun _ => rfl, ?_, ?_, Or.inl ⟨_, hrd, rfl⟩⟩
    · rw [inBounds_iff]
      exact ⟨Int.le_refl _, by simpa [Int64.toInt_zero] using scalarSizeAlign_le_max1 prog.tags d.ty⟩
    · rw [isAligned_iff]
      dsimp only
      refine ⟨Int.le_refl _, ?_, ?_⟩
      · unfold scalarSizeAlign; simp [hptr]
      · rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (scalarSizeAlign_dvd_max1 prog.tags d.ty) (Nat.dvd_of_mod_eq_zero hba))
  have hfr : FrameBlocks m m2 {m.nextBlock} :=
    FrameBlocks.trans_same (FrameBlocks.of_alloc ha) (FrameBlocks.of_writeVal hwr)
  refine ⟨_, m2, hwp, hw m2 hslot hfr ?_⟩
  intro b hne
  rw [writeVal_blocks_ne hwr hne, hm1]
  exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne

theorem wp_if {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c : CExpr} {t : CStmt} {f? : Option CStmt}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval c []) (.branch t (f?.getD .nop)) []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.ifStmt c t f?)) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_if_bool {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {t f : CStmt} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q (.running (.stmt (if b then t else f)) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.branch t f) mods) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [ht]) hw

theorem wp_branch_true {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {t f : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some true)
    (hw : WPTerm prog cfg ext Q (.running (.stmt t) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.branch t f) mods) env blks m os k) :=
  wp_if_bool ht hw

theorem wp_branch_false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {t f : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : isTruthy v = some false)
    (hw : WPTerm prog cfg ext Q (.running (.stmt f) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.branch t f) mods) env blks m os k) :=
  wp_if_bool hf hw

theorem wp_whileCond_bool {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {c : CExpr} {body : CStmt} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q
      (if b then .running (.stmt body) env blks m os (.loop (some c) none body false k)
       else .running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.whileCond c body) mods) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [ht]) hw

theorem wp_whileCond_true {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {c : CExpr} {body : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some true)
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os (.loop (some c) none body false k))) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.whileCond c body) mods) env blks m os k) :=
  wp_whileCond_bool ht hw

theorem wp_whileCond_false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {c : CExpr} {body : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : isTruthy v = some false)
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.whileCond c body) mods) env blks m os k) :=
  wp_whileCond_bool hf hw

theorem wp_whileCond_bool_ite {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c : CExpr} {body : CStmt} {ty : CTy} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (if b then .running (.stmt body) env blks m os (.loop (some c) none body false k)
       else .running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if b then 1 else 0)) ty) []) (.whileCond c body) mods) env blks m os k) :=
  wp_whileCond_bool (isTruthy_bool_int b) hw

theorem wp_forCond_bool {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {c : CExpr} {stp? : Option CExpr} {body : CStmt} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q
      (if b then .running (.stmt body) env blks m os (.loop (some c) stp? body false k)
       else .running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.forCond c stp? body) mods) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [ht]) hw

theorem wp_forCond_true {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {c : CExpr} {stp? : Option CExpr} {body : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some true)
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os (.loop (some c) stp? body false k))) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.forCond c stp? body) mods) env blks m os k) :=
  wp_forCond_bool ht hw

theorem wp_forCond_false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {c : CExpr} {stp? : Option CExpr} {body : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : isTruthy v = some false)
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.forCond c stp? body) mods) env blks m os k) :=
  wp_forCond_bool hf hw

theorem wp_forCond_bool_ite {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c : CExpr} {stp? : Option CExpr} {body : CStmt} {ty : CTy} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (if b then .running (.stmt body) env blks m os (.loop (some c) stp? body false k)
       else .running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if b then 1 else 0)) ty) []) (.forCond c stp? body) mods) env blks m os k) :=
  wp_forCond_bool (isTruthy_bool_int b) hw

theorem wp_doWhileCond_bool {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {body : CStmt} {c : CExpr} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q
      (if b then .running (.stmt body) env blks m os (.loop (some c) none body true k)
       else .running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.doWhileCond body c) mods) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [ht]) hw

theorem wp_doWhileCond_true {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {body : CStmt} {c : CExpr} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some true)
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os (.loop (some c) none body true k))) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.doWhileCond body c) mods) env blks m os k) :=
  wp_doWhileCond_bool ht hw

theorem wp_doWhileCond_false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {body : CStmt} {c : CExpr} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : isTruthy v = some false)
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) (.doWhileCond body c) mods) env blks m os k) :=
  wp_doWhileCond_bool hf hw

theorem wp_doWhileCond_bool_ite {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {body : CStmt} {c : CExpr} {ty : CTy} {mods : ModSet} {b : Bool}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (if b then .running (.stmt body) env blks m os (.loop (some c) none body true k)
       else .running (.stmt .nop) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if b then 1 else 0)) ty) []) (.doWhileCond body c) mods) env blks m os k) :=
  wp_doWhileCond_bool (isTruthy_bool_int b) hw

theorem wp_forStep {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {rv : ExprRes} {c? stp? : Option CExpr} {body : CStmt} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (match c? with
      | some c => .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k
      | none => .running (.stmt body) env blks m os (.loop none stp? body false k))) :
    WPTerm prog cfg ext Q (.running (.expr (.ret rv []) (.forStep c? stp? body) mods) env blks m os k) :=
  WPTerm.of_det (by cases rv with | lval _ _ _ | structVal _ _ => rfl | rval v _ => cases v <;> rfl) hw

theorem wp_return_expr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {e : CExpr} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval e []) .returnVal []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.returnStmt (some e))) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_return_void {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hvoid : k.topRetTy.isVoid = true)
    (hw : WPTerm prog cfg ext Q (match unwindReturn m blks k with
      | some (re, rb, _, m', fs, rctx, rk) =>
        .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' os rk
      | none => .returned .void (m.freeStack blks) os)) :
    WPTerm prog cfg ext Q (.running (.stmt (.returnStmt none)) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp only [hvoid, ↓reduceIte]; cases unwindReturn m blks k <;> rfl) hw

theorem wp_return_void_stop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hvoid : k.topRetTy.isVoid = true) (huw : unwindReturn m blks k = none)
    (hq : Q .void (m.freeStack blks) os) :
    WPTerm prog cfg ext Q (.running (.stmt (.returnStmt none)) env blks m os k) :=
  wp_return_void hvoid (by rw [huw]; exact .returned hq)

theorem wp_return_val {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v cv : Val} {ty : CTy} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hnv : k.topRetTy.isVoid = false) (hcast : castVal m k.topRetTy v = some cv)
    (hw : WPTerm prog cfg ext Q (match unwindReturn m blks k with
      | some (re, rb, _, m', fs, rctx, rk) =>
        .running (.expr (.ret (.rval cv k.topRetTy) fs) rctx []) re rb m' os rk
      | none => .returned cv (m.freeStack blks) os)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) .returnVal mods) env blks m os k) := by
  refine WPTerm.of_det ?_ hw
  unfold stepDet
  simp only [hnv, Bool.false_eq_true, ↓reduceIte, Option.bind, hcast, Option.map]
  rcases unwindReturn m blks k with _ | ⟨re, rb, rr, m', fs, rctx, rk⟩ <;> rfl

theorem wp_return_val_stop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v cv : Val} {ty : CTy} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hnv : k.topRetTy.isVoid = false) (hcast : castVal m k.topRetTy v = some cv)
    (huw : unwindReturn m blks k = none) (hq : Q cv (m.freeStack blks) os) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) .returnVal mods) env blks m os k) :=
  wp_return_val hnv hcast (by rw [huw]; exact .returned hq)

theorem wp_return_val_void {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty : CTy} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hvoid : k.topRetTy.isVoid = true)
    (hw : WPTerm prog cfg ext Q (match unwindReturn m blks k with
      | some (re, rb, _, m', fs, rctx, rk) =>
        .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' os rk
      | none => .returned .void (m.freeStack blks) os)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) .returnVal mods) env blks m os k) :=
  WPTerm.of_det (by
    unfold stepDet
    cases v <;> simp only [hvoid, ↓reduceIte] <;> cases unwindReturn m blks k <;> rfl) hw

theorem wp_break {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {env e' : Env} {blks b' : List BlockId} {m m' : Mem} {os : OSState} {k k' : Cont}
    (huw : unwindBreak m env blks k = some (e', b', m', k'))
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) e' b' m' os k')) :
    WPTerm prog cfg ext Q (.running (.stmt .breakStmt) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [huw]) hw

theorem wp_continue {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c? stp? : Option CExpr} {body : CStmt} {isDo : Bool}
    {env e' : Env} {blks b' : List BlockId} {m m' : Mem} {os : OSState} {k k' : Cont}
    (huw : unwindContinue m env blks k = some (c?, stp?, body, isDo, e', b', m', k'))
    (hw : WPTerm prog cfg ext Q (loopNext c? stp? body isDo e' b' m' os k')) :
    WPTerm prog cfg ext Q (.running (.stmt .continueStmt) env blks m os k) :=
  WPTerm.of_det (by unfold stepDet; simp [huw]) hw

theorem wp_case {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Int} {body : CStmt} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.caseStmt v body)) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_default {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {body : CStmt} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.defaultStmt body)) env blks m os k) :=
  WPTerm.of_det rfl hw

theorem wp_label {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {lbl : String} {body : CStmt} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.labelStmt lbl body)) env blks m os k) :=
  WPTerm.of_det rfl hw

/-! ### Pure & Effectful Expression Stepping Lemmas -/

theorem wp_paren {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {e : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval w e fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval w (.paren e) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_lit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Int} {ik : IntKind} {suf : LitSuffix} {rad : LitRadix} {sym? : Option String}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik (BitVec.ofInt ik.bits v)) (.int ik)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.lit v ik suf rad sym?) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_sizeOfTy {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ty : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .u64 (BitVec.ofNat 64 (sizeofTy prog.tags ty))) (.int .u64)) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.sizeOfTy ty) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_var_lval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {b : BlockId} {ty : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hl : env.lookup x = some (b, ty))
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.lval b 0 ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .lval (.var x) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hl]) hw

theorem wp_var_lval_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {b : BlockId} {ty : CTy} {P : Val → Prop}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m x b ty P)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.lval b 0 ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .lval (.var x) fs) ctx mods) env blks m os k) :=
  wp_var_lval hs.1 hw

private theorem readPlace_of_slot {tags : TypeEnv} {env : Env} {m : Mem} {mods : ModSet}
    {x : String} {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m x b ty P) (hnu : ¬ P .undef)
    (hnc : mods.conflicts b 0 (sizeofTy tags ty) = false) :
    ∃ v, readPlace tags m mods .rval b 0 ty = some (.rval v ty.decay) ∧ P v := by
  rcases hs with ⟨_, _, _, _, _, _, hval⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · refine ⟨v, ?_, hpv⟩
    have hrd' : Sem.readVal tags m b 0 ty = some v := by
      rw [readVal_tags_irrel tags []]; exact hrd
    unfold readPlace
    unfold Sem.readVal at hrd
    cases hu : ty.unqual <;> rw [hu] at hrd <;> dsimp only
    · cases hrd
    · simp only [hnc, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · cases hrd
    · simp only [hnc, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · cases hrd
      rfl
    · cases hrd
    · cases hrd
    · cases hrd
    · cases hrd
    · simp only [hnc, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · simp only [hnc, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · simp only [hnc, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · cases hrd
  · exact False.elim (hnu hundef)

theorem wp_var_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {b : BlockId} {ty : CTy} {P : Val → Prop}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m x b ty P) (hnu : ¬ P .undef)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags ty) = false)
    (hw : ∀ v, P v → WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v ty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) := by
  obtain ⟨v, hrp, hpv⟩ := readPlace_of_slot hs hnu hnc
  exact WPTerm.of_exprPure (by unfold stepExprPure; simp [hs.1, hrp]) (hw v hpv)

theorem wp_var_slot_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {b : BlockId} {ty : CTy} {w : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m x b ty (· = w)) (hnu : ¬ (Val.undef = w))
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags ty) = false)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval w ty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) :=
  wp_var_slot hs hnu hnc (fun _ heq => by subst heq; exact hw)

theorem wp_var_slot_anyInt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {b : BlockId} {ty : CTy} {ik : IntKind}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m x b ty (AnyInt ik))
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags ty) = false)
    (hw : ∀ bv : BitVec ik.bits, WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) ty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) :=
  wp_var_slot hs (not_AnyInt_undef ik) hnc (fun _ ⟨bv, heq⟩ => heq ▸ hw bv)

theorem wp_var_slot_intRange {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {b : BlockId} {ty : CTy} {ik : IntKind} {lo hi : Int}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m x b ty (IntRange ik lo hi))
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags ty) = false)
    (hw : ∀ bv : BitVec ik.bits, lo ≤ intToInt ik bv → intToInt ik bv ≤ hi →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik bv) ty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) :=
  wp_var_slot hs (not_IntRange_undef ik lo hi) hnc (fun _ ⟨bv, heq, h1, h2⟩ => heq ▸ hw bv h1 h2)

theorem wp_var_enum {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {ev : Int} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hne : env.lookup x = none) (he : enumConst? prog.tags x = some ev)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (BitVec.ofInt 32 ev)) (.int .i32)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; dsimp only; rw [hne]; dsimp only; rw [he]; rfl) hw

theorem wp_var_fnProto {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {x : String} {rt : CTy} {ps : List CTy} {variadic : Bool}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hne : env.lookup x = none) (henum : enumConst? prog.tags x = none)
    (hp : prog.fnProtos x = some (rt, ps, variadic))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.fnPtr x) (.fnPtr rt ps variadic)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.var x) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hne, henum, hp]) hw

theorem wp_cast {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ty : CTy} {e : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval e (.castF ty :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.cast ty e) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_cast_ret {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v cv : Val} {vty ty : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hc : castVal m ty v = some cv)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval cv ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v vty) (.castF ty :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hc]) hw

theorem wp_cast_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {k1 ik : IntKind} {bv : BitVec k1.bits} {vty ty : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : ty.intKind? = some ik) (hnv : ty.unqual.isVoid = false)
    (hw : ∀ newBv : BitVec ik.bits,
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)) →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik newBv) ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k1 bv) vty) (.castF ty :: fs)) ctx mods) env blks m os k) := by
  have hc : castVal m ty (.int k1 bv) =
      some (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) := by
    unfold castVal
    have hki : ty.unqual.intKind? = some ik := by
      unfold CTy.intKind? at hik ⊢
      rw [cty_unqual_idem]
      exact hik
    simp only [hnv, hki, Bool.false_eq_true, ↓reduceIte, ofIntCast, intToInt]
  exact wp_cast_ret hc (hw _ rfl)

theorem wp_unary {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : UnOp} {e : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval e (.unaryF op :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.unary op e) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_unary_ret {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : UnOp} {v rv : Val} {vty rt : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (he : evalUnary op v = some (rv, rt))
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v vty) (.unaryF op :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [he]) hw

theorem wp_unary_neg_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ik : IntKind} {bv : BitVec ik.bits} {vty : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hlo : ik.promote.minVal ≤ -intToInt ik bv)
    (hhi : -intToInt ik bv ≤ ik.promote.maxVal)
    (hw : ∀ newBv : BitVec ik.promote.bits,
      intToInt ik.promote newBv = -intToInt ik bv →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik.promote newBv) (.int ik.promote)) fs) ctx mods)
          env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) (.unaryF .neg :: fs)) ctx mods) env blks m os k) :=
  wp_unary_ret (evalUnary_neg_int bv hlo hhi)
    (hw _ (intToInt_ofInt_eq hlo hhi))

theorem wp_binary {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} {l r : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval l (.binLhsF op r :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.binary op l r) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_binLhs {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} {v1 : Val} {t1 : CTy} {r : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval r (.binRhsF op v1 t1 :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v1 t1) (.binLhsF op r :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_binRhs_ret {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} {v1 v2 rv : Val} {t1 t2 rt : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hb : applyBinary cfg prog.tags m op v1 t1 v2 t2 = some (rv, rt))
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v2 t2) (.binRhsF op v1 t1 :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hb]) hw

theorem wp_binRhs_int_cmp {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {k1 k2 : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (h1 : (IntKind.usualArith k1 k2).minVal ≤ intToInt k1 bv1 ∧
          intToInt k1 bv1 ≤ (IntKind.usualArith k1 k2).maxVal)
    (h2 : (IntKind.usualArith k1 k2).minVal ≤ intToInt k2 bv2 ∧
          intToInt k2 bv2 ≤ (IntKind.usualArith k1 k2).maxVal)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if cmpOrd op (intToInt k1 bv1) (intToInt k2 bv2) then 1 else 0)) (.int .i32)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  refine wp_binRhs_ret ?_ hw
  rw [applyBinary_int_of_intKind ht1 ht2]
  exact evalIntBinary_cmp_inRange hop bv1 bv2 h1 h2

theorem wp_binRhs_int_cmp_fit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {k1 k2 : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hf1 : fitsIn k1 (IntKind.usualArith k1 k2) = true)
    (hf2 : fitsIn k2 (IntKind.usualArith k1 k2) = true)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if cmpOrd op (intToInt k1 bv1) (intToInt k2 bv2) then 1 else 0)) (.int .i32)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) :=
  wp_binRhs_int_cmp hop ht1 ht2 (fitsIn_bounds hf1 bv1) (fitsIn_bounds hf2 bv2) hw

@[reducible] def evalArithRaw (op : BinOp) (x y : Int) : Int :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .div => Int.tdiv x y
  | _ => Int.tmod x y

theorem wp_binRhs_int_arith_signed {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    {k1 k2 ck : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hck : IntKind.usualArith k1 k2 = ck)
    (hs : ck.signed = true)
    (h1 : ck.minVal ≤ intToInt k1 bv1 ∧ intToInt k1 bv1 ≤ ck.maxVal)
    (h2 : ck.minVal ≤ intToInt k2 bv2 ∧ intToInt k2 bv2 ≤ ck.maxVal)
    (hd : (op = .div ∨ op = .mod) → intToInt k2 bv2 ≠ 0)
    (raw : Int)
    (hraw : raw = evalArithRaw op (intToInt k1 bv1) (intToInt k2 bv2))
    (hlo : ck.minVal ≤ raw)
    (hhi : raw ≤ ck.maxVal)
    (hw : ∀ newBv : BitVec ck.bits,
      intToInt ck newBv = raw →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ck newBv) (.int ck)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  subst hck
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    refine wp_binRhs_ret (by
      rw [applyBinary_int_of_intKind ht1 ht2]
      exact evalIntBinary_arith_signed (by simp) bv1 bv2 hs h1 h2 hd raw
        (by rw [hraw]) hlo hhi)
      (hw _ (intToInt_ofInt_eq hlo hhi))

theorem wp_binRhs_int_arith_unsigned {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod)
    {k1 k2 ck : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hck : IntKind.usualArith k1 k2 = ck)
    (hu : ck.signed = false)
    (hd : (op = .div ∨ op = .mod) →
      intToInt ck (BitVec.ofInt ck.bits (intToInt k2 bv2)) ≠ 0)
    (hw : ∀ newBv : BitVec ck.bits,
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ck newBv) (.int ck)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  subst hck
  exact wp_binRhs_ret (by
    rw [applyBinary_int_of_intKind ht1 ht2]
    exact evalIntBinary_arith_unsigned hop bv1 bv2 hu hd) (hw _)

theorem wp_binRhs_int_bitwise {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    {k1 k2 : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hw : ∀ newBv : BitVec (IntKind.usualArith k1 k2).bits,
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int (IntKind.usualArith k1 k2) newBv)
            (.int (IntKind.usualArith k1 k2))) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  exact wp_binRhs_ret (by
    rw [applyBinary_int_of_intKind ht1 ht2]
    exact evalIntBinary_bitwise hop k1 k2 bv1 bv2) (hw _)

theorem wp_binRhs_int_shift_unsigned {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .shl ∨ op = .shr)
    {k1 k2 : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hu : k1.promote.signed = false)
    (hlo : 0 ≤ intToInt k2 bv2) (hhi : intToInt k2 bv2 < k1.promote.bits)
    (hw : ∀ newBv : BitVec k1.promote.bits,
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int k1.promote newBv) (.int k1.promote)) fs) ctx mods)
          env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  exact wp_binRhs_ret (by
    rw [applyBinary_int_of_intKind ht1 ht2]
    exact evalIntBinary_shift_unsigned hop bv1 bv2 hu hlo hhi) (hw _)

theorem wp_binRhs_int_shift_signed {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .shl ∨ op = .shr)
    {k1 k2 : IntKind} {bv1 : BitVec k1.bits} {bv2 : BitVec k2.bits} {t1 t2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hs : k1.promote.signed = true)
    (h1 : 0 ≤ intToInt k1 bv1)
    (h2lo : 0 ≤ intToInt k2 bv2) (h2hi : intToInt k2 bv2 < k1.promote.bits)
    (raw : Int)
    (hraw : raw = if op == .shl then intToInt k1 bv1 * (2 ^ (intToInt k2 bv2).toNat : Int)
                  else intToInt k1 bv1 / (2 ^ (intToInt k2 bv2).toNat : Int))
    (hlo : k1.promote.minVal ≤ raw) (hhi : raw ≤ k1.promote.maxVal)
    (hw : ∀ newBv : BitVec k1.promote.bits,
      intToInt k1.promote newBv = raw →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int k1.promote newBv) (.int k1.promote)) fs) ctx mods)
          env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k2 bv2) t2) (.binRhsF op (.int k1 bv1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  refine wp_binRhs_ret ?_ (hw _ (intToInt_ofInt_eq hlo hhi))
  rw [applyBinary_int_of_intKind ht1 ht2]
  exact evalIntBinary_shift_signed hop bv1 bv2 hs h1 h2lo h2hi raw hraw hlo hhi

theorem wp_binRhs_ptrAdd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {blk : Block} {el : CTy} {t1 t2 : CTy}
    {ik : IntKind} {bv : BitVec ik.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.unqual = .ptr el)
    (_ht2 : t2.intKind? = some ik)
    (hb : m.blocks b = some blk)
    (h0 : 0 ≤ off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int))
    (hle : off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int) ≤ (blk.size : Int))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b (Int64.ofInt (off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int)))) (.ptr el)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) t2) (.binRhsF .add (.ptr b off) t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp1 : t1.isPtr = true := CTy.isPtr_of_unqual_ptr ht1
  have hap : applyBinary cfg prog.tags m .add (.ptr b off) t1 (.int ik bv) t2 =
      some (.ptr b (Int64.ofInt (off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int))), .ptr el) := by
    unfold applyBinary
    simp only [hp1, Bool.true_or, ↓reduceIte, ht1, valAsInt?_int_toInt, evalPtrAdd, hb,
      bind, Option.bind, pure, Pure.pure]
    have hg : (0 ≤ off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int) &&
        off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int) ≤ (blk.size : Int)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h0, hle⟩
    cases hz : intToInt ik bv == 0 && cfg.allowAddZeroAny
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hg]
      simp only [guard, Pure.pure, ↓reduceIte, Option.map]
    · have hiz : intToInt ik bv = 0 := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hz).1
      have hoff : Int64.ofInt (off.toInt + 0 * (max 1 (sizeofTy prog.tags el) : Int)) = off := by
        rw [Int.zero_mul, Int.add_zero, Int64.ofInt_toInt]
      rw [hiz, hoff]
      simp only [↓reduceIte, Option.map]
  exact wp_binRhs_ret hap hw

theorem wp_addrOf {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {e : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .lval e (.addrOfF :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.addrOf e) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_addrOf_ret {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {ty : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.ptr b off) (.ptr ty)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.lval b off ty) (.addrOfF :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_deref {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {e : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval e (.derefF w :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval w (.deref e) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_deref_lval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty el : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.lval b off el) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.derefF .lval :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hp, readPlace, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_deref_rval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty el : CTy} {res : ExprRes}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el)
    (hr : readPlace prog.tags m mods .rval b off el = some res)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret res fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hp, hr, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_index {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {base idx : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval base (.indexBaseF w idx :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval w (.index base idx) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_indexBase {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {p : Val} {pty : CTy} {idx : CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval idx (.indexIdxF w p pty :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval p pty) (.indexBaseF w idx :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_indexIdx {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {p : Val} {pty el : CTy} {iv : Val} {ity : CTy} {ik : IntKind} {idx : Int}
    {b : BlockId} {off : Int64} {res : ExprRes}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el) (hiv : valAsInt? iv = some (ik, idx))
    (hadd : evalPtrAdd cfg prog.tags m p el idx = some (.ptr b off))
    (hr : readPlace prog.tags m mods w b off el = some res)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret res fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval iv ity) (.indexIdxF w p pty :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hp, hiv, hadd, hr, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_member {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {b : CExpr} {fld : String} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .lval b (.memberF w fld :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval w (.member b fld) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_member_lval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {ty fty : CTy} {fld : String} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hfl : fieldLayout? prog.tags ty fld = some (foff, fty))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b (Int64.ofInt (off.toInt + foff)) fty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b off ty) (.memberF .lval fld :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hfl, readPlace, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_arrow {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {w : Want} {b : CExpr} {fld : String} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval b (.arrowF w fld :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval w (.arrow b fld) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_arrow_lval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty sty fty : CTy} {fld : String} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr sty)
    (hfl : fieldLayout? prog.tags sty fld = some (foff, fty))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b (Int64.ofInt (off.toInt + foff)) fty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.arrowF .lval fld :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hp, hfl, readPlace, bind, Option.bind, pure, Pure.pure]) hw

private theorem readPlace_of_field {tags : TypeEnv} {m : Mem} {mods : ModSet}
    {b : BlockId} {off : Int64} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) (hnu : ¬ P .undef)
    (hnc : ∀ foff, fieldLayout? tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy tags fty) = false) :
    ∃ foff v, fieldLayout? tags (.structTy structTag) fld = some (foff, fty) ∧
      readPlace tags m mods .rval b (Int64.ofInt (off.toInt + foff)) fty = some (.rval v fty.decay) ∧
      P v := by
  rcases hf with ⟨foff, blk, hfl, _, _, _, _, _, hval⟩
  rcases hval with ⟨v, hrd, hpv⟩ | hundef
  · refine ⟨foff, v, hfl, ?_, hpv⟩
    have hncf := hnc foff hfl
    have hrd' := hrd
    unfold readPlace
    unfold Sem.readVal at hrd
    cases hu : fty.unqual <;> rw [hu] at hrd <;> dsimp only
    · cases hrd
    · simp only [hncf, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · cases hrd
    · simp only [hncf, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · cases hrd
      rfl
    · cases hrd
    · cases hrd
    · cases hrd
    · cases hrd
    · simp only [hncf, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · simp only [hncf, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · simp only [hncf, Bool.not_false, guard_true, hrd', bind, Option.bind, Option.map]
    · cases hrd
  · exact False.elim (hnu hundef)

theorem wp_arrow_field {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty sty fty : CTy} {structTag fld : String} {P : Val → Prop}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr sty) (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty P) (hnu : ¬ P .undef)
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : ∀ v, P v → WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) ctx mods) env blks m os k) := by
  obtain ⟨foff, v, hfl, hrp, hpv⟩ := readPlace_of_field hf hnu hnc
  have hfl' : fieldLayout? prog.tags sty fld = some (foff, fty) := by
    unfold fieldLayout? at hfl ⊢
    rw [hsty]
    exact hfl
  exact WPTerm.of_exprPure (by
    unfold stepExprPure
    simp only [hp, hfl', hrp, bind, Option.bind, pure, Pure.pure]) (hw v hpv)

theorem wp_arrow_field_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty sty fty : CTy} {structTag fld : String} {w : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr sty) (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty (· = w)) (hnu : ¬ (Val.undef = w))
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval w fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) ctx mods) env blks m os k) :=
  wp_arrow_field hp hsty hf hnu hnc (fun _ heq => heq ▸ hw)

theorem wp_arrow_field_anyInt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty sty fty : CTy} {structTag fld : String} {ik : IntKind}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr sty) (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty (AnyInt ik))
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : ∀ bv : BitVec ik.bits, WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) ctx mods) env blks m os k) :=
  wp_arrow_field hp hsty hf (not_AnyInt_undef ik) hnc (fun _ ⟨bv, heq⟩ => heq ▸ hw bv)

theorem wp_arrow_field_intRange {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty sty fty : CTy} {structTag fld : String}
    {ik : IntKind} {lo hi : Int}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr sty) (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty (IntRange ik lo hi))
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : ∀ bv : BitVec ik.bits, lo ≤ intToInt ik bv → intToInt ik bv ≤ hi →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik bv) fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) ctx mods) env blks m os k) :=
  wp_arrow_field hp hsty hf (not_IntRange_undef ik lo hi) hnc (fun _ ⟨bv, heq, h1, h2⟩ => heq ▸ hw bv h1 h2)

theorem wp_member_field {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {sty fty : CTy} {structTag fld : String} {P : Val → Prop}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty P) (hnu : ¬ P .undef)
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : ∀ v, P v → WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b off sty) (.memberF .rval fld :: fs)) ctx mods) env blks m os k) := by
  obtain ⟨foff, v, hfl, hrp, hpv⟩ := readPlace_of_field hf hnu hnc
  have hfl' : fieldLayout? prog.tags sty fld = some (foff, fty) := by
    unfold fieldLayout? at hfl ⊢; rw [hsty]; exact hfl
  exact WPTerm.of_exprPure (by
    unfold stepExprPure
    simp only [hfl', hrp, bind, Option.bind, pure, Pure.pure]) (hw v hpv)

theorem wp_member_field_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {sty fty : CTy} {structTag fld : String} {w : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty (· = w)) (hnu : ¬ (Val.undef = w))
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval w fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b off sty) (.memberF .rval fld :: fs)) ctx mods) env blks m os k) :=
  wp_member_field hsty hf hnu hnc (fun _ heq => heq ▸ hw)

theorem wp_member_field_anyInt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {sty fty : CTy} {structTag fld : String} {ik : IntKind}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty (AnyInt ik))
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : ∀ bv : BitVec ik.bits, WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b off sty) (.memberF .rval fld :: fs)) ctx mods) env blks m os k) :=
  wp_member_field hsty hf (not_AnyInt_undef ik) hnc (fun _ ⟨bv, heq⟩ => heq ▸ hw bv)

theorem wp_member_field_intRange {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {sty fty : CTy} {structTag fld : String}
    {ik : IntKind} {lo hi : Int}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hsty : sty.unqual = .structTy structTag)
    (hf : Field prog.tags m b off structTag fld fty (IntRange ik lo hi))
    (hnc : ∀ foff, fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty) →
      mods.conflicts b (Int64.ofInt (off.toInt + foff)) (sizeofTy prog.tags fty) = false)
    (hw : ∀ bv : BitVec ik.bits, lo ≤ intToInt ik bv → intToInt ik bv ≤ hi →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik bv) fty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b off sty) (.memberF .rval fld :: fs)) ctx mods) env blks m os k) :=
  wp_member_field hsty hf (not_IntRange_undef ik lo hi) hnc (fun _ ⟨bv, heq, h1, h2⟩ => heq ▸ hw bv h1 h2)

theorem wp_cond {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c t f : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval c (.condF t f :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.cond c t f) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_cond_bool {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {t f : CExpr} {b : Bool}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (if b then t else f) fs) ctx []) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.condF t f :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [ht, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_logAnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {l r : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval l (.logAndF r :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.logAnd l r) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_logAnd_false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {r : CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : isTruthy v = some false)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.int .i32 0) (.int .i32)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.logAndF r :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hf, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_logAnd_true {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {r : CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some true)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval r (.logAndEndF :: fs)) ctx []) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.logAndF r :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [ht, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_logAndEnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {b : Bool}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if b then 1 else 0)) (.int .i32)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.logAndEndF :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [ht, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_logOr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {l r : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval l (.logOrF r :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.logOr l r) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_logOr_true {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {r : CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some true)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.int .i32 1) (.int .i32)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.logOrF r :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [ht, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_logOr_false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {r : CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : isTruthy v = some false)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval r (.logOrEndF :: fs)) ctx []) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.logOrF r :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [hf, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_logOrEnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {vty : CTy} {b : Bool}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht : isTruthy v = some b)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if b then 1 else 0)) (.int .i32)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.logOrEndF :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by unfold stepExprPure; simp [ht, bind, Option.bind, pure, Pure.pure]) hw

theorem wp_comma {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {l r : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval l (.commaF r :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.comma l r) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_comma_ret {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {rv : ExprRes} {r : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval r fs) ctx []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret rv (.commaF r :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by cases rv <;> rfl) hw

theorem wp_call_push {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {fn : CExpr} {args : List CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval fn (.callFnF args :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.call fn args) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_call_arg0 {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {sym : String} {fnTy : CTy} {arg : CExpr} {rest : List CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval arg (.callArgF sym fnTy [] rest :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.fnPtr sym) fnTy) (.callFnF (arg :: rest) :: fs)) ctx mods)
        env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_call_arg_next {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {sym : String} {fnTy : CTy} {done : List (Val × CTy)} {v : Val} {ty : CTy}
    {arg : CExpr} {rest : List CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval arg (.callArgF sym fnTy (done ++ [(v, ty)]) rest :: fs)) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v ty) (.callArgF sym fnTy done (arg :: rest) :: fs)) ctx mods)
        env blks m os k) :=
  WPTerm.of_exprPure rfl hw

/-! ### Assignments (`assign_slot`, `assign_field`, `assignOp`) and `incDec` -/

theorem wp_assign {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : AssignOp} {lhs rhs : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .lval lhs (.assignLhsF op rhs :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.assign op lhs rhs) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_assign_rhs {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : AssignOp} {b : BlockId} {off : Int64} {lty : CTy} {rhs : CExpr}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval rhs (.assignRhsF op b off lty :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b off lty) (.assignLhsF op rhs :: fs)) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

theorem wp_assign_slot_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {name : String} {b : BlockId} {lty vty : CTy} {P : Val → Prop}
    {ik k1 : IntKind} {bv : BitVec k1.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hw : ∀ (m' : Mem) (newBv : BitVec ik.bits),
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)) →
      Sem.writeVal m b 0 lty (.int ik newBv) = some m' →
      Slot env m' name b lty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik newBv) lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k1 bv) vty) (.assignRhsF .eq b 0 lty :: fs)) ctx mods)
        env blks m os k) := by
  rcases hs with ⟨hl, blk, hb, hp, hin, hal, _⟩
  have hrw : blk.perm = .rw := hp hnc_ty
  have hal_eq : (scalarSizeAlign lty).2 = ik.align := by
    unfold scalarSizeAlign
    unfold CTy.intKind? at hik
    cases hu : lty.unqual <;> simp [hu] at hik
    · subst hik; rfl
    · cases hik; rfl
  have hin_eq : (scalarSizeAlign lty).1 = ik.bytes := by
    unfold scalarSizeAlign
    unfold CTy.intKind? at hik
    cases hu : lty.unqual <;> simp [hu] at hik
    · subst hik; rfl
    · cases hik; rfl
  have hal' : Mem.isAligned blk 0 ik.align = true := hal_eq ▸ hal
  have hin' : Mem.inBounds blk 0 ik.bytes = true := hin_eq ▸ hin
  let cv : BitVec ik.bits := BitVec.ofInt ik.bits (intToInt k1 bv)
  obtain ⟨m', hwr⟩ := writeVal_int_some' hnc_ty hik hb hrw hal' hin' (valAsInt?_int_toInt ik cv)
  have hcast : castVal m lty (.int k1 bv) = some (.int ik cv) := by
    unfold castVal
    have hnv : lty.unqual.isVoid = false := by
      unfold CTy.intKind? at hik
      cases hu : lty.unqual <;> simp [hu] at hik <;> rfl
    have hki : lty.unqual.intKind? = some ik := by
      unfold CTy.intKind? at hik ⊢
      rw [cty_unqual_idem]
      exact hik
    simp only [hnv, hki, Bool.false_eq_true, ↓reduceIte, ofIntCast, intToInt, cv]
  have hu_int : lty.unqual = .int ik ∨ ∃ tag isU, lty.unqual = .enumTy tag isU := by
    unfold CTy.intKind? at hik
    cases hu : lty.unqual <;> simp [hu] at hik
    · subst hik; exact Or.inl rfl
    · exact Or.inr ⟨_, _, rfl⟩
  have hwp : writePlace prog.tags m b 0 lty (.rval (.int k1 bv) vty) =
      some (.rval (.int ik cv) lty, m') := by
    unfold writePlace
    rcases hu_int with hu | ⟨tag, isU, hu⟩ <;> simp [hu, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hrd : Sem.readVal [] m' b 0 lty = some (.int ik cv) :=
    readVal_writeVal_same_int' [] rfl hik hb hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk' := writeBytes_blocks_eq hb hwb
  have hs' : Slot env m' name b lty (· = .int ik cv) :=
    ⟨hl, _, hblk', hp, by simpa [Mem.inBounds] using hin, by simpa [Mem.isAligned] using hal, Or.inl ⟨_, hrd, rfl⟩⟩
  refine WPTerm.of_exprPure ?_ (hw m' cv rfl hwr hs' (FrameBlocks.of_writeVal hwr))
  unfold stepExprPure
  simp [hnc, assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_assign_slot_int_same {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {name : String} {b : BlockId} {lty vty : CTy} {P : Val → Prop}
    {ik : IntKind} {bv : BitVec ik.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hw : ∀ (m' : Mem),
      Sem.writeVal m b 0 lty (.int ik bv) = some m' →
      Slot env m' name b lty (· = .int ik bv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik bv) lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) (.assignRhsF .eq b 0 lty :: fs)) ctx mods)
        env blks m os k) := by
  refine wp_assign_slot_int hs hnc_ty hik hnc (fun m' newBv heq hwr hs' hfr => ?_)
  have hbv : newBv = bv := eq_of_intToInt_eq (by simpa [ofInt_intToInt] using heq)
  subst hbv
  exact hw m' hwr hs' hfr

theorem wp_assign_slot_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {name : String} {b : BlockId} {lty el vty : CTy} {P : Val → Prop} {v : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnc_ty : lty.isConst = false) (hptr : lty.unqual = .ptr el)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hw : ∀ (m' : Mem),
      Sem.writeVal m b 0 lty v = some m' →
      Slot env m' name b lty (· = v) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval v lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.assignRhsF .eq b 0 lty :: fs)) ctx mods)
        env blks m os k) := by
  rcases hs with ⟨hl, blk, hb, hp, hin, hal, _⟩
  have hrw : blk.perm = .rw := hp hnc_ty
  have hal8 : Mem.isAligned blk 0 8 = true := by
    unfold scalarSizeAlign at hal; simp [hptr] at hal; exact hal
  have hin8 : Mem.inBounds blk 0 8 = true := by
    unfold scalarSizeAlign at hin; simp [hptr] at hin; exact hin
  obtain ⟨m', hwr⟩ := writeVal_ptr_some hnc_ty hptr hb hrw hal8 hin8 hv
  have hcast : castVal m lty v = some v := by
    unfold castVal
    rcases hv with rfl | ⟨pb, poff, rfl⟩ <;>
      simp only [hptr, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]
  have hwp : writePlace prog.tags m b 0 lty (.rval v vty) = some (.rval v lty, m') := by
    unfold writePlace; simp [hptr, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hrd : Sem.readVal [] m' b 0 lty = some v :=
    readVal_writeVal_same_ptr' [] hptr hptr hb hv hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk' := writeBytes_blocks_eq hb hwb
  have hs' : Slot env m' name b lty (· = v) :=
    ⟨hl, _, hblk', hp, by simpa [Mem.inBounds] using hin, by simpa [Mem.isAligned] using hal, Or.inl ⟨_, hrd, rfl⟩⟩
  refine WPTerm.of_exprPure ?_ (hw m' hwr hs' (FrameBlocks.of_writeVal hwr))
  unfold stepExprPure
  simp [hnc, assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_assign_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {name : String} {b : BlockId} {lty vty : CTy} {P : Val → Prop} {v : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hres : ∃ cv m', writePlace prog.tags m b 0 lty (.rval v vty) = some (.rval cv lty, m') ∧
      Slot env m' name b lty (· = cv) ∧
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval cv lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.assignRhsF .eq b 0 lty :: fs)) ctx mods)
        env blks m os k) := by
  let _ := hs
  obtain ⟨cv, m', hwp, _, hw⟩ := hres
  refine WPTerm.of_exprPure ?_ hw
  unfold stepExprPure
  simp [hnc, assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_assign_field_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty vty : CTy} {P : Val → Prop}
    {ik k1 : IntKind} {bv : BitVec k1.bits} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hw : ∀ (m' : Mem) (newBv : BitVec ik.bits),
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)) →
      Sem.writeVal m b fldOff fty (.int ik newBv) = some m' →
      Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik newBv) fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k1 bv) vty) (.assignRhsF .eq b fldOff fty :: fs)) ctx mods)
        env blks m os k) := by
  subst hoff
  rcases hf with ⟨foff0, blk, hfl0, hb, hp, h0, hsz, hal, _⟩
  rw [hfl] at hfl0
  cases hfl0
  have hrw : blk.perm = .rw := hp hnc_ty
  have hsz_eq : sizeofTy prog.tags fty = ik.bytes := sizeofTy_eq_scalar prog.tags hik
  have hal_eq : alignofTy prog.tags fty = ik.align := alignofTy_eq_scalar prog.tags hik
  have hal_pos : max 1 (alignofTy prog.tags fty) = ik.align := by
    rw [hal_eq]; cases ik <;> rfl
  have hlt : soff.toInt + foff < ptrDiffLimit := by have := blk.sizeLt; omega
  have hfld_int : (Int64.ofInt (soff.toInt + foff)).toInt = soff.toInt + foff :=
    int64_ofInt_toInt (by omega) hlt
  have hal' : Mem.isAligned blk (Int64.ofInt (soff.toInt + foff)) ik.align = true :=
    hal_pos ▸ hal
  have hin' : Mem.inBounds blk (Int64.ofInt (soff.toInt + foff)) ik.bytes = true := by
    rw [inBounds_iff, hfld_int, ← hsz_eq]
    exact ⟨by omega, by omega⟩
  let cv : BitVec ik.bits := BitVec.ofInt ik.bits (intToInt k1 bv)
  obtain ⟨m', hwr⟩ := writeVal_int_some' hnc_ty hik hb hrw hal' hin' (valAsInt?_int_toInt ik cv)
  have hcast : castVal m fty (.int k1 bv) = some (.int ik cv) := by
    unfold castVal
    have hnv : fty.unqual.isVoid = false := by
      unfold CTy.intKind? at hik
      cases hu : fty.unqual <;> simp [hu] at hik <;> rfl
    have hki : fty.unqual.intKind? = some ik := by
      unfold CTy.intKind? at hik ⊢
      rw [cty_unqual_idem]
      exact hik
    simp only [hnv, hki, Bool.false_eq_true, ↓reduceIte, ofIntCast, intToInt, cv]
  have hu_int : fty.unqual = .int ik ∨ ∃ tag isU, fty.unqual = .enumTy tag isU := by
    unfold CTy.intKind? at hik
    cases hu : fty.unqual <;> simp [hu] at hik
    · subst hik; exact Or.inl rfl
    · exact Or.inr ⟨_, _, rfl⟩
  have hwp : writePlace prog.tags m b (Int64.ofInt (soff.toInt + foff)) fty (.rval (.int k1 bv) vty) =
      some (.rval (.int ik cv) fty, m') := by
    unfold writePlace
    rcases hu_int with hu | ⟨tag, isU, hu⟩ <;> simp only [hu, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hrd : Sem.readVal prog.tags m' b (Int64.ofInt (soff.toInt + foff)) fty = some (.int ik cv) :=
    readVal_writeVal_same_int' prog.tags rfl hik hb hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk' := writeBytes_blocks_eq hb hwb
  have hf' : Field prog.tags m' b soff structTag fld fty (· = .int ik cv) :=
    ⟨foff, _, hfl, hblk', hp, h0, hsz, by simpa [Mem.isAligned] using hal, Or.inl ⟨_, hrd, rfl⟩⟩
  refine WPTerm.of_exprPure ?_ (hw m' cv rfl hwr hf' (FrameBlocks.of_writeVal hwr))
  unfold stepExprPure
  simp only [hnc, Bool.not_false, guard_true, assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_assign_field_int_same {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty vty : CTy} {P : Val → Prop}
    {ik : IntKind} {bv : BitVec ik.bits} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hw : ∀ (m' : Mem),
      Sem.writeVal m b fldOff fty (.int ik bv) = some m' →
      Field prog.tags m' b soff structTag fld fty (· = .int ik bv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik bv) fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) (.assignRhsF .eq b fldOff fty :: fs)) ctx mods)
        env blks m os k) := by
  refine wp_assign_field_int hf hfl hoff hnc_ty hik hnc (fun m' newBv heq hwr hf' hfr => ?_)
  have hbv : newBv = bv := eq_of_intToInt_eq (by simpa [ofInt_intToInt] using heq)
  subst hbv
  exact hw m' hwr hf' hfr

theorem wp_assign_field_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty el vty : CTy} {P : Val → Prop}
    {v : Val} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnc_ty : fty.isConst = false) (hptr : fty.unqual = .ptr el)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hw : ∀ (m' : Mem),
      Sem.writeVal m b fldOff fty v = some m' →
      Field prog.tags m' b soff structTag fld fty (· = v) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval v fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.assignRhsF .eq b fldOff fty :: fs)) ctx mods)
        env blks m os k) := by
  subst hoff
  rcases hf with ⟨foff0, blk, hfl0, hb, hp, h0, hsz, hal, _⟩
  rw [hfl] at hfl0
  cases hfl0
  have hrw : blk.perm = .rw := hp hnc_ty
  have hsz8 : sizeofTy prog.tags fty = 8 := sizeofTy_eq_ptr_auto prog.tags hptr
  have hal8 : alignofTy prog.tags fty = 8 := alignofTy_eq_ptr_auto prog.tags hptr
  have hlt : soff.toInt + foff < ptrDiffLimit := by have := blk.sizeLt; omega
  have hfld_int : (Int64.ofInt (soff.toInt + foff)).toInt = soff.toInt + foff :=
    int64_ofInt_toInt (by omega) hlt
  have hal' : Mem.isAligned blk (Int64.ofInt (soff.toInt + foff)) 8 = true := by
    rw [hal8] at hal; exact hal
  have hin' : Mem.inBounds blk (Int64.ofInt (soff.toInt + foff)) 8 = true := by
    rw [inBounds_iff, hfld_int, ← hsz8]; exact ⟨by omega, by omega⟩
  obtain ⟨m', hwr⟩ := writeVal_ptr_some hnc_ty hptr hb hrw hal' hin' hv
  have hcast : castVal m fty v = some v := by
    unfold castVal
    rcases hv with rfl | ⟨pb, poff, rfl⟩ <;>
      simp only [hptr, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]
  have hwp : writePlace prog.tags m b (Int64.ofInt (soff.toInt + foff)) fty (.rval v vty) =
      some (.rval v fty, m') := by
    unfold writePlace; simp only [hptr, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hrd : Sem.readVal prog.tags m' b (Int64.ofInt (soff.toInt + foff)) fty = some v :=
    readVal_writeVal_same_ptr' prog.tags hptr hptr hb hv hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk' := writeBytes_blocks_eq hb hwb
  have hf' : Field prog.tags m' b soff structTag fld fty (· = v) :=
    ⟨foff, _, hfl, hblk', hp, h0, hsz, by simpa [Mem.isAligned] using hal, Or.inl ⟨_, hrd, rfl⟩⟩
  refine WPTerm.of_exprPure ?_ (hw m' hwr hf' (FrameBlocks.of_writeVal hwr))
  unfold stepExprPure
  simp only [hnc, Bool.not_false, guard_true, assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_assign_field {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty vty : CTy} {P : Val → Prop}
    {v : Val} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hres : ∃ cv m', writePlace prog.tags m b fldOff fty (.rval v vty) = some (.rval cv fty, m') ∧
      Field prog.tags m' b soff structTag fld fty (· = cv) ∧
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval cv fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.assignRhsF .eq b fldOff fty :: fs)) ctx mods)
        env blks m os k) := by
  let _ := hf; let _ := hfl; let _ := hoff
  obtain ⟨cv, m', hwp, _, hw⟩ := hres
  refine WPTerm.of_exprPure ?_ hw
  unfold stepExprPure
  simp [hnc, assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_assignOp {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : AssignOp} {bop : BinOp} {b : BlockId} {off : Int64} {lty vty : CTy} {v : Val}
    {oldV nv cv : Val} {nt : CTy} {m' : Mem}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hop : assignOpToBin? op = some bop)
    (hnc : mods.conflicts b off (sizeofTy prog.tags lty) = false)
    (hrd : Sem.readVal prog.tags m b off lty = some oldV)
    (hbin : applyBinary cfg prog.tags m bop oldV lty v vty = some (nv, nt))
    (hwp : writePlace prog.tags m b off lty (.rval nv lty) = some (.rval cv lty, m'))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval cv lty) fs) ctx (⟨b, off, sizeofTy prog.tags lty⟩ :: mods))
        env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) (.assignRhsF op b off lty :: fs)) ctx mods)
        env blks m os k) := by
  refine WPTerm.of_exprPure ?_ hw
  unfold stepExprPure
  simp [hnc, hop, hrd, hbin, hwp, bind, Option.bind, pure, Pure.pure]

theorem wp_incDec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} {lhs : CExpr} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .lval lhs (.incDecF op :: fs)) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval (.incDec op lhs) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure rfl hw

@[reducible] def incDecDelta (op : IncDecOp) : Int :=
  match op with
  | .preInc | .postInc => 1
  | .preDec | .postDec => -1

private theorem intToInt_incDec_delta (op : IncDecOp) :
    intToInt .i32 (BitVec.ofInt 32 (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1)) =
      match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1 := by
  cases op <;> decide

private theorem incDec_delta_range (op : IncDecOp) :
    -1 ≤ (match op with | .preInc | .postInc => (1 : Int) | .preDec | .postDec => -1) ∧
    (match op with | .preInc | .postInc => (1 : Int) | .preDec | .postDec => -1) ≤ 1 := by
  cases op <;> decide

private theorem usualArith_minMax_one (ik : IntKind) (hs : (IntKind.usualArith ik .i32).signed = true) :
    (IntKind.usualArith ik .i32).minVal ≤ -1 ∧ 1 ≤ (IntKind.usualArith ik .i32).maxVal := by
  cases ik <;> simp only [IntKind.usualArith, IntKind.signed] at hs <;> (try contradiction) <;> decide

private theorem minMax_le_usualArith_of_fitsIn {k : IntKind} (hf : fitsIn k (IntKind.usualArith k .i32) = true) :
    (IntKind.usualArith k .i32).minVal ≤ k.minVal ∧ k.maxVal ≤ (IntKind.usualArith k .i32).maxVal := by
  cases k <;> simp only [fitsIn, IntKind.usualArith] at hf <;> (try contradiction) <;> decide

private theorem ofInt_add_unsigned {k : IntKind} (hs : k.signed = false) (x y : Int) :
    BitVec.ofInt k.bits (intToInt k (BitVec.ofInt k.bits x) + intToInt k (BitVec.ofInt k.bits y)) =
      BitVec.ofInt k.bits (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [intToInt, hs, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofInt]
  have hpos : (0 : Int) < ((2 ^ k.bits : Nat) : Int) := Int.natCast_pos.mpr (Nat.pow_pos (by decide))
  apply Int.ofNat.inj
  change (((((x % ((2 ^ k.bits : Nat) : Int)).toNat : Int) +
      ((y % ((2 ^ k.bits : Nat) : Int)).toNat : Int)) % ((2 ^ k.bits : Nat) : Int)).toNat : Int) =
    (((x + y) % ((2 ^ k.bits : Nat) : Int)).toNat : Int)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg x (Int.ne_of_gt hpos)),
      Int.toNat_of_nonneg (Int.emod_nonneg y (Int.ne_of_gt hpos)),
      Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hpos)),
      Int.toNat_of_nonneg (Int.emod_nonneg (x + y) (Int.ne_of_gt hpos)),
      ← Int.add_emod]

theorem wp_incDec_slot_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} {name : String} {b : BlockId} {lty : CTy} {P : Val → Prop}
    {ik : IntKind}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnu : ¬ P .undef)
    (hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      let ck := IntKind.usualArith ik .i32
      let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
      ck.minVal ≤ intToInt ik oldBv ∧ intToInt ik oldBv ≤ ck.maxVal ∧
      (ck.signed = true → ck.minVal ≤ intToInt ik oldBv + d ∧ intToInt ik oldBv + d ≤ ck.maxVal))
    (hw : ∀ (m' : Mem) (oldBv newBv : BitVec ik.bits)
      (midBv : BitVec (IntKind.usualArith ik .i32).bits),
      P (.int ik oldBv) →
      intToInt (IntKind.usualArith ik .i32) midBv =
        intToInt (IntKind.usualArith ik .i32)
          (BitVec.ofInt (IntKind.usualArith ik .i32).bits
            (intToInt ik oldBv + (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1))) →
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt (IntKind.usualArith ik .i32) midBv)) →
      Sem.writeVal m b 0 lty (.int ik newBv) = some m' →
      Slot env m' name b lty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      let retV : Val := match op with
        | .preInc | .preDec => .int (IntKind.usualArith ik .i32) midBv
        | .postInc | .postDec => .int ik oldBv
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval retV lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b 0 lty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  rcases hs with ⟨hl, blk, hb, hp, hin, hal, hval⟩
  rcases hval with ⟨oldV, hrd, hpv⟩ | hundef
  · have hrw : blk.perm = .rw := hp hnc_ty
    have hcases : ∃ oldBv : BitVec ik.bits, oldV = .int ik oldBv := by
      have hrd' := hrd
      unfold Sem.readVal at hrd'
      rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk 0 ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b 0 ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hki, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk 0 ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b 0 ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
    rcases hcases with ⟨oldBv, rfl⟩
    let ck := IntKind.usualArith ik .i32
    have hck_bounds := hok oldBv hpv
    have hal_eq : (scalarSizeAlign lty).2 = ik.align := by
      unfold scalarSizeAlign
      rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩ <;> simp [hu]
      rw [hki]
    have hin_eq : (scalarSizeAlign lty).1 = ik.bytes := by
      unfold scalarSizeAlign
      rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩ <;> simp [hu]
      rw [hki]
    have hbin_one : ∀ (d : Int) (hd : d = 1 ∨ d = -1)
        (hd_val : intToInt .i32 (BitVec.ofInt 32 d) = d)
        (hsr_fn : ck.signed = true → ck.minVal ≤ intToInt ik oldBv + d ∧ intToInt ik oldBv + d ≤ ck.maxVal),
        applyBinary cfg prog.tags m .add (.int ik oldBv) lty
          (.int .i32 (BitVec.ofInt 32 d)) (.int .i32) =
          some (.int ck (BitVec.ofInt ck.bits (intToInt ik oldBv + d)), .int ck) := by
      intro d hd hd_val hsr_fn
      rw [applyBinary_int_of_intKind hik (by rfl : (CTy.int .i32).intKind? = some .i32)]
      cases hs_ck : ck.signed
      · have hev := evalIntBinary_arith_unsigned (k2 := .i32) (Or.inl rfl) oldBv (BitVec.ofInt 32 d) hs_ck
          (fun h => by rcases h with h | h <;> cases h)
        dsimp only at hev
        rw [hd_val, ofInt_add_unsigned hs_ck (intToInt ik oldBv) d] at hev
        exact hev
      · have hsr := hsr_fn hs_ck
        have h2_bounds : ck.minVal ≤ intToInt .i32 (BitVec.ofInt 32 d) ∧
            intToInt .i32 (BitVec.ofInt 32 d) ≤ ck.maxVal := by
          rw [hd_val]
          have hck_range := usualArith_minMax_one ik hs_ck
          dsimp only [ck] at hck_range ⊢
          rcases hd with rfl | rfl <;> omega
        exact evalIntBinary_arith_signed (k2 := .i32) (Or.inl rfl) oldBv
          (bv2 := (BitVec.ofInt 32 d : BitVec IntKind.i32.bits)) hs_ck
          ⟨hck_bounds.1, hck_bounds.2.1⟩ h2_bounds (fun h => by rcases h with h | h <;> cases h)
          (intToInt ik oldBv + d) (by dsimp only; rw [hd_val]) hsr.1 hsr.2
    have hrd_tags : Sem.readVal prog.tags m b 0 lty = some (.int ik oldBv) := by
      rw [readVal_tags_irrel prog.tags []]; exact hrd
    have hrun : ∀ (d : Int),
        ∃ (m' : Mem) (midBv : BitVec ck.bits) (newBv : BitVec ik.bits),
          midBv = BitVec.ofInt ck.bits (intToInt ik oldBv + d) ∧
          newBv = BitVec.ofInt ik.bits (intToInt ck midBv) ∧
          Sem.writeVal m b 0 lty (.int ik newBv) = some m' ∧
          Sem.writeVal m b 0 lty (.int ck midBv) = some m' ∧
          Slot env m' name b lty (· = .int ik newBv) ∧
          FrameBlocks m m' {b} := by
      intro d
      let midBv := BitVec.ofInt ck.bits (intToInt ik oldBv + d)
      let newBv := BitVec.ofInt ik.bits (intToInt ck midBv)
      obtain ⟨m', hwr_new⟩ := writeVal_int_some' hnc_ty hik hb hrw (hal_eq ▸ hal) (hin_eq ▸ hin)
        (valAsInt?_int_toInt ik newBv)
      have heq_bv : BitVec.ofInt ik.bits (intToInt ck midBv) = BitVec.ofInt ik.bits (intToInt ik newBv) :=
        (ofInt_intToInt ik newBv).symm
      have hwr_eq : Sem.writeVal m b 0 lty (.int ck midBv) = Sem.writeVal m b 0 lty (.int ik newBv) := by
        unfold Sem.writeVal
        rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩
        · simp only [hnc_ty, Bool.not_false, guard_true, hb, hu, CTy.unqual, CTy.intKind?,
            valAsInt?_int_toInt, bind, Option.bind, heq_bv]
        · simp only [hnc_ty, Bool.not_false, guard_true, hb, hu, CTy.unqual, CTy.intKind?,
            hki, valAsInt?_int_toInt, bind, Option.bind, heq_bv]
      have hwr_mid : Sem.writeVal m b 0 lty (.int ck midBv) = some m' := hwr_eq.trans hwr_new
      have hrd_new : Sem.readVal [] m' b 0 lty = some (.int ik newBv) :=
        readVal_writeVal_same_int' [] rfl hik hb hwr_new
      obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr_new
      have hblk' := writeBytes_blocks_eq hb hwb
      have hs' : Slot env m' name b lty (· = .int ik newBv) :=
        ⟨hl, _, hblk', hp, by simpa [Mem.inBounds] using hin, by simpa [Mem.isAligned] using hal, Or.inl ⟨_, hrd_new, rfl⟩⟩
      exact ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hs', FrameBlocks.of_writeVal hwr_new⟩
    cases op
    · have hbin := hbin_one 1 (Or.inl rfl) (intToInt_incDec_delta .preInc) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hs', hfr⟩ := hrun 1
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b 0 lty) (.incDecF .preInc :: fs)) =
          some (.ret (.rval (.int ck (BitVec.ofInt ck.bits (intToInt ik oldBv + 1))) lty) fs,
                m', ⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd_tags, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hs' hfr)
    · have hbin := hbin_one (-1) (Or.inr rfl) (intToInt_incDec_delta .preDec) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hs', hfr⟩ := hrun (-1)
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b 0 lty) (.incDecF .preDec :: fs)) =
          some (.ret (.rval (.int ck (BitVec.ofInt ck.bits (intToInt ik oldBv + -1))) lty) fs,
                m', ⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd_tags, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hs' hfr)
    · have hbin := hbin_one 1 (Or.inl rfl) (intToInt_incDec_delta .postInc) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hs', hfr⟩ := hrun 1
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b 0 lty) (.incDecF .postInc :: fs)) =
          some (.ret (.rval (.int ik oldBv) lty) fs,
                m', ⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd_tags, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hs' hfr)
    · have hbin := hbin_one (-1) (Or.inr rfl) (intToInt_incDec_delta .postDec) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hs', hfr⟩ := hrun (-1)
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b 0 lty) (.incDecF .postDec :: fs)) =
          some (.ret (.rval (.int ik oldBv) lty) fs,
                m', ⟨b, 0, sizeofTy prog.tags lty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd_tags, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hs' hfr)
  · exact False.elim (hnu hundef)

theorem wp_incDec_slot_post_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} (hop : op = .postInc ∨ op = .postDec)
    {name : String} {b : BlockId} {lty : CTy} {P : Val → Prop} {ik : IntKind}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnu : ¬ P .undef)
    (hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hfit : fitsIn ik (IntKind.usualArith ik .i32) = true)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      ((IntKind.usualArith ik .i32).signed = true →
        (IntKind.usualArith ik .i32).minVal ≤ intToInt ik oldBv + incDecDelta op ∧
        intToInt ik oldBv + incDecDelta op ≤ (IntKind.usualArith ik .i32).maxVal) ∧
      (ik.minVal ≤ intToInt ik oldBv + incDecDelta op ∧ intToInt ik oldBv + incDecDelta op ≤ ik.maxVal))
    (hw : ∀ (m' : Mem) (oldBv newBv : BitVec ik.bits),
      P (.int ik oldBv) →
      intToInt ik newBv = intToInt ik oldBv + incDecDelta op →
      Sem.writeVal m b 0 lty (.int ik newBv) = some m' →
      Slot env m' name b lty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik oldBv) lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b 0 lty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  refine wp_incDec_slot_int hs hnu hnc_ty hik hnc ?_ ?_
  · intro oldBv hpv
    have hfb := fitsIn_bounds hfit oldBv
    have hok' := hok oldBv hpv
    dsimp only [incDecDelta] at hok'
    refine ⟨hfb.1, hfb.2, fun hs_ck => ?_⟩
    rcases hop with rfl | rfl <;> exact hok'.1 hs_ck
  · intro m' oldBv newBv midBv hpv hmid hnew hwr hs' hfr
    have hok' := hok oldBv hpv
    dsimp only [incDecDelta] at hok'
    have hmid_val : intToInt (IntKind.usualArith ik .i32) midBv =
        intToInt ik oldBv + (match op with | .postInc => 1 | _ => -1) := by
      rw [hmid]
      have hmm := minMax_le_usualArith_of_fitsIn hfit
      have h2 := hok'.2
      rcases hop with rfl | rfl <;> dsimp only at h2 ⊢ <;> exact intToInt_ofInt_eq (by omega) (by omega)
    have hnew_eq : intToInt ik newBv =
        intToInt ik oldBv + (match op with | .postInc => 1 | _ => -1) := by
      rw [hnew, hmid_val]
      rcases hop with rfl | rfl <;> exact intToInt_ofInt_eq hok'.2.1 hok'.2.2
    rcases hop with rfl | rfl <;> exact hw m' oldBv newBv hpv hnew_eq hwr hs' hfr

theorem wp_incDec_slot_post_int_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} (hop : op = .postInc ∨ op = .postDec)
    {name : String} {b : BlockId} {lty : CTy} {ik : IntKind} {oldBv : BitVec ik.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty (· = .int ik oldBv))
    (hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hfit : fitsIn ik (IntKind.usualArith ik .i32) = true)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hs_lo : (IntKind.usualArith ik .i32).signed = true →
      (IntKind.usualArith ik .i32).minVal ≤ intToInt ik oldBv + incDecDelta op)
    (hs_hi : (IntKind.usualArith ik .i32).signed = true →
      intToInt ik oldBv + incDecDelta op ≤ (IntKind.usualArith ik .i32).maxVal)
    (hlo : ik.minVal ≤ intToInt ik oldBv + incDecDelta op)
    (hhi : intToInt ik oldBv + incDecDelta op ≤ ik.maxVal)
    (hw : ∀ (m' : Mem) (newBv : BitVec ik.bits),
      intToInt ik newBv = intToInt ik oldBv + incDecDelta op →
      Sem.writeVal m b 0 lty (.int ik newBv) = some m' →
      Slot env m' name b lty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik oldBv) lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b 0 lty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  refine wp_incDec_slot_post_int hop hs (fun h => by cases h) hnc_ty hik hfit hnc
    (fun _ h => by cases h; exact ⟨fun hs_ck => ⟨hs_lo hs_ck, hs_hi hs_ck⟩, hlo, hhi⟩) ?_
  intro m' oldBv' newBv h heq hwr hs' hfr
  cases h
  exact hw m' newBv heq hwr hs' hfr

private theorem intToInt_cast_eq {k1 k2 : IntKind} (h : k1 = k2) (bv : BitVec k1.bits) :
    intToInt k2 (h ▸ bv) = intToInt k1 bv := by
  subst h; rfl

private theorem val_int_cast_eq {k1 k2 : IntKind} (h : k1 = k2) (bv : BitVec k1.bits) :
    Val.int k2 (h ▸ bv) = Val.int k1 bv := by
  subst h; rfl

private theorem intToInt_ofInt_cast {k1 k2 : IntKind} (h : k1 = k2) (x : Int) :
    intToInt k1 (BitVec.ofInt k1.bits x) = intToInt k2 (BitVec.ofInt k2.bits x) := by
  subst h; rfl

private theorem eq_of_intToInt_cast {k1 k2 : IntKind} (h : k1 = k2) (x : BitVec k2.bits) (y : BitVec k1.bits)
    (heq : intToInt k2 x = intToInt k2 (BitVec.ofInt k2.bits (intToInt k1 y))) :
    x = h ▸ y := by
  subst h; rw [ofInt_intToInt] at heq; exact eq_of_intToInt_eq heq

theorem wp_incDec_slot_pre_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} (hop : op = .preInc ∨ op = .preDec)
    {name : String} {b : BlockId} {lty : CTy} {P : Val → Prop} {ik : IntKind}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnu : ¬ P .undef)
    (hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hck : IntKind.usualArith ik .i32 = ik)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      ik.signed = true → ik.minVal ≤ intToInt ik oldBv + incDecDelta op ∧ intToInt ik oldBv + incDecDelta op ≤ ik.maxVal)
    (hw : ∀ (m' : Mem) (oldBv newBv : BitVec ik.bits),
      P (.int ik oldBv) →
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt ik oldBv + incDecDelta op)) →
      Sem.writeVal m b 0 lty (.int ik newBv) = some m' →
      Slot env m' name b lty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik newBv) lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b 0 lty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  refine wp_incDec_slot_int hs hnu hnc_ty hik hnc ?_ ?_
  · intro oldBv hpv
    have hb := intToInt_bounds ik oldBv
    rw [hck]
    refine ⟨hb.1, hb.2, fun hs_ck => ?_⟩
    rcases hop with rfl | rfl <;> exact hok oldBv hpv hs_ck
  · intro m' oldBv newBv midBv hpv hmid hnew hwr hs' hfr
    have heq_new : newBv = hck ▸ midBv := eq_of_intToInt_cast hck newBv midBv hnew
    have hnew' : intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits
        (intToInt ik oldBv + (match op with | .preInc => 1 | _ => -1))) := by
      rw [heq_new, intToInt_cast_eq hck midBv, hmid]
      rcases hop with rfl | rfl <;> exact intToInt_ofInt_cast hck _
    have hret : Val.int (IntKind.usualArith ik .i32) midBv = Val.int ik newBv := by
      rw [heq_new, val_int_cast_eq hck midBv]
    rcases hop with rfl | rfl
    · simpa [hret] using hw m' oldBv newBv hpv hnew' hwr hs' hfr
    · simpa [hret] using hw m' oldBv newBv hpv hnew' hwr hs' hfr

/-! ### Additional Unary, Cast, Deref, Index, Pointer Binary, Field `incDec` & `assignOp` Lemmas -/

theorem wp_unary_plus_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ik : IntKind} {bv : BitVec ik.bits} {vty : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hlo : ik.promote.minVal ≤ intToInt ik bv)
    (hhi : intToInt ik bv ≤ ik.promote.maxVal)
    (hw : ∀ newBv : BitVec ik.promote.bits,
      intToInt ik.promote newBv = intToInt ik bv →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik.promote newBv) (.int ik.promote)) fs) ctx mods)
          env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) (.unaryF .plus :: fs)) ctx mods) env blks m os k) :=
  wp_unary_ret (evalUnary_plus_int bv hlo hhi) (hw _ (intToInt_ofInt_eq hlo hhi))

theorem wp_unary_bitNot_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ik : IntKind} {bv : BitVec ik.bits} {vty : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik.promote (~~~(BitVec.ofInt ik.promote.bits (intToInt ik bv))))
        (.int ik.promote)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) (.unaryF .bitNot :: fs)) ctx mods) env blks m os k) :=
  wp_unary_ret (evalUnary_bitNot_int ik bv) hw

theorem wp_unary_logNot_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ik : IntKind} {bv : BitVec ik.bits} {vty : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if intToInt ik bv != 0 then 0 else 1)) (.int .i32)) fs) ctx mods)
        env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) (.unaryF .logNot :: fs)) ctx mods) env blks m os k) :=
  wp_unary_ret (evalUnary_logNot_int_auto ik bv) hw

theorem wp_unary_logNot_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {vty : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 0) (.int .i32)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) vty) (.unaryF .logNot :: fs)) ctx mods) env blks m os k) :=
  wp_unary_ret (evalUnary_logNot_ptr_auto b off) hw

theorem wp_unary_logNot_null {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {vty : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 1) (.int .i32)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval .null vty) (.unaryF .logNot :: fs)) ctx mods) env blks m os k) :=
  wp_unary_ret evalUnary_logNot_null_auto hw

theorem wp_cast_ptr_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {vty ty el : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : ty.unqual = .ptr el)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.ptr b off) ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) vty) (.castF ty :: fs)) ctx mods) env blks m os k) :=
  wp_cast_ret (by simp [castVal, hp, CTy.isVoid, CTy.unqual, CTy.intKind?]) hw

theorem wp_cast_ptr_null {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {vty ty el : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : ty.unqual = .ptr el)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval .null ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval .null vty) (.castF ty :: fs)) ctx mods) env blks m os k) :=
  wp_cast_ret (by simp [castVal, hp, CTy.isVoid, CTy.unqual, CTy.intKind?]) hw

theorem wp_cast_ptr_zero {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ik : IntKind} {vty ty el : CTy} {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : ty.unqual = .ptr el)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval .null ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik 0) vty) (.castF ty :: fs)) ctx mods) env blks m os k) :=
  wp_cast_ret (by simp [castVal, hp, CTy.isVoid, CTy.unqual, CTy.intKind?]) hw

theorem wp_deref_rval_scalar {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty el : CTy} {v : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el)
    (hscalar : match el.unqual with
      | .array _ _ | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ => false
      | _ => true)
    (hnc : mods.conflicts b off (sizeofTy prog.tags el) = false)
    (hrd : Sem.readVal prog.tags m b off el = some v)
    (hw : WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v el.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) ctx mods) env blks m os k) := by
  refine wp_deref_rval hp ?_ hw
  unfold readPlace
  cases hu : el.unqual <;> simp only [hu] at hscalar <;> (try cases hscalar) <;>
    simp only [hnc, Bool.not_false, guard_true, hrd, bind, Option.bind, Option.map]

theorem wp_deref_rval_array {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {pty el elem : CTy} {len? : Option Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el) (har : el.unqual = .array elem len?)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) el.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b off) pty) (.derefF .rval :: fs)) ctx mods) env blks m os k) :=
  wp_deref_rval hp (by unfold readPlace; rw [har]) hw

private theorem evalPtrAdd_int_bounds {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {blk : Block} {el : CTy} {idx : Int}
    (hb : m.blocks b = some blk)
    (h0 : 0 ≤ off.toInt + idx * (max 1 (sizeofTy tags el) : Int))
    (hle : off.toInt + idx * (max 1 (sizeofTy tags el) : Int) ≤ (blk.size : Int)) :
    evalPtrAdd cfg tags m (.ptr b off) el idx =
      some (.ptr b (Int64.ofInt (off.toInt + idx * (max 1 (sizeofTy tags el) : Int)))) := by
  unfold evalPtrAdd
  have hg : (0 ≤ off.toInt + idx * (max 1 (sizeofTy tags el) : Int) &&
      off.toInt + idx * (max 1 (sizeofTy tags el) : Int) ≤ (blk.size : Int)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h0, hle⟩
  cases hz : idx == 0 && cfg.allowAddZeroAny
  · simp only [Bool.false_eq_true, ↓reduceIte, hb, bind, Option.bind, pure, Pure.pure]
    rw [hg]
    simp only [guard, Pure.pure, ↓reduceIte]
  · have hiz : idx = 0 := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hz).1
    have hoff : Int64.ofInt (off.toInt + 0 * (max 1 (sizeofTy tags el) : Int)) = off := by
      rw [Int.zero_mul, Int.add_zero, Int64.ofInt_toInt]
    rw [hiz, hoff]
    simp only [↓reduceIte]

theorem wp_indexIdx_lval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {blk : Block} {pty el ity : CTy}
    {ik : IntKind} {bv : BitVec ik.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el) (hb : m.blocks b = some blk)
    (h0 : 0 ≤ off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int))
    (hle : off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int) ≤ (blk.size : Int))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b (Int64.ofInt (off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int))) el) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) ity) (.indexIdxF .lval (.ptr b off) pty :: fs)) ctx mods)
        env blks m os k) :=
  wp_indexIdx hp (valAsInt?_int_toInt ik bv) (evalPtrAdd_int_bounds hb h0 hle) rfl hw

theorem wp_indexIdx_rval_scalar {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {blk : Block} {pty el ity : CTy}
    {ik : IntKind} {bv : BitVec ik.bits} {v : Val}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : pty.unqual = .ptr el) (hb : m.blocks b = some blk)
    (hscalar : match el.unqual with
      | .array _ _ | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ => false
      | _ => true)
    (h0 : 0 ≤ off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int))
    (hle : off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int) ≤ (blk.size : Int))
    (hnc : mods.conflicts b (Int64.ofInt (off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int)))
      (sizeofTy prog.tags el) = false)
    (hrd : Sem.readVal prog.tags m b
      (Int64.ofInt (off.toInt + intToInt ik bv * (max 1 (sizeofTy prog.tags el) : Int))) el = some v)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v el.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) ity) (.indexIdxF .rval (.ptr b off) pty :: fs)) ctx mods)
        env blks m os k) := by
  refine wp_indexIdx hp (valAsInt?_int_toInt ik bv) (evalPtrAdd_int_bounds hb h0 hle) ?_ hw
  unfold readPlace
  cases hu : el.unqual <;> simp only [hu] at hscalar <;> (try cases hscalar) <;>
    simp only [hnc, Bool.not_false, guard_true, hrd, bind, Option.bind, Option.map]

theorem wp_binRhs_ptrSub_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {off : Int64} {blk : Block} {el : CTy} {t1 t2 : CTy}
    {ik : IntKind} {bv : BitVec ik.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.unqual = .ptr el) (ht2 : t2.isPtr = false)
    (hb : m.blocks b = some blk)
    (h0 : 0 ≤ off.toInt + (-intToInt ik bv) * (max 1 (sizeofTy prog.tags el) : Int))
    (hle : off.toInt + (-intToInt ik bv) * (max 1 (sizeofTy prog.tags el) : Int) ≤ (blk.size : Int))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b (Int64.ofInt (off.toInt + (-intToInt ik bv) * (max 1 (sizeofTy prog.tags el) : Int)))) (.ptr el)) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) t2) (.binRhsF .sub (.ptr b off) t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp1 : t1.isPtr = true := CTy.isPtr_of_unqual_ptr ht1
  have hap : applyBinary cfg prog.tags m .sub (.ptr b off) t1 (.int ik bv) t2 =
      some (.ptr b (Int64.ofInt (off.toInt + (-intToInt ik bv) * (max 1 (sizeofTy prog.tags el) : Int))), .ptr el) := by
    unfold applyBinary
    simp only [hp1, ht2, Bool.true_or, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ht1,
      valAsInt?_int_toInt, evalPtrAdd_int_bounds hb h0 hle, Option.map]
  exact wp_binRhs_ret hap hw

theorem wp_binRhs_ptrCmp_eq_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .eq ∨ op = .ne)
    {b1 b2 : BlockId} {o1 o2 : Int64} {t1 t2 el1 el2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.unqual = .ptr el1) (ht2 : t2.unqual = .ptr el2)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if (if op == .eq then (b1 == b2 && o1 == o2) else !(b1 == b2 && o1 == o2)) then 1 else 0)) (.int .i32)) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b2 o2) t2) (.binRhsF op (.ptr b1 o1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp1 : t1.isPtr = true := CTy.isPtr_of_unqual_ptr ht1
  have hp2 : t2.isPtr = true := CTy.isPtr_of_unqual_ptr ht2
  have hap : applyBinary cfg prog.tags m op (.ptr b1 o1) t1 (.ptr b2 o2) t2 =
      some (.int .i32 (if (if op == .eq then (b1 == b2 && o1 == o2) else !(b1 == b2 && o1 == o2)) then 1 else 0), .int .i32) := by
    rcases hop with rfl | rfl
    · simp [applyBinary, hp1, hp2, evalPtrCmp]
    · simp only [applyBinary, hp1, hp2, Bool.true_or, ↓reduceIte, evalPtrCmp, Option.map,
        Bool.not_and]
  exact wp_binRhs_ret hap hw

theorem wp_binRhs_ptrCmp_eq_null {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .eq ∨ op = .ne)
    {b1 : BlockId} {o1 : Int64} {t1 t2 el1 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.unqual = .ptr el1)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if (if op == .eq then false else true) then 1 else 0)) (.int .i32)) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval .null t2) (.binRhsF op (.ptr b1 o1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp1 : t1.isPtr = true := CTy.isPtr_of_unqual_ptr ht1
  have hap : applyBinary cfg prog.tags m op (.ptr b1 o1) t1 .null t2 =
      some (.int .i32 (if (if op == .eq then false else true) then 1 else 0), .int .i32) := by
    rcases hop with rfl | rfl <;> simp [applyBinary, hp1, evalPtrCmp]
  exact wp_binRhs_ret hap hw

theorem wp_binRhs_ptrCmp_null_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .eq ∨ op = .ne)
    {b2 : BlockId} {o2 : Int64} {t1 t2 el2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht2 : t2.unqual = .ptr el2)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if (if op == .eq then false else true) then 1 else 0)) (.int .i32)) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b2 o2) t2) (.binRhsF op .null t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp2 : t2.isPtr = true := CTy.isPtr_of_unqual_ptr ht2
  have hap : applyBinary cfg prog.tags m op .null t1 (.ptr b2 o2) t2 =
      some (.int .i32 (if (if op == .eq then false else true) then 1 else 0), .int .i32) := by
    rcases hop with rfl | rfl <;> simp [applyBinary, hp2, evalPtrCmp]
  exact wp_binRhs_ret hap hw

theorem wp_binRhs_ptrCmp_rel {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : BinOp} (hop : op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {b : BlockId} {o1 o2 : Int64} {blk : Block} {t1 t2 el1 el2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.unqual = .ptr el1) (ht2 : t2.unqual = .ptr el2)
    (hb : m.blocks b = some blk)
    (h10 : 0 ≤ o1.toInt) (h1s : o1.toInt ≤ blk.size)
    (h20 : 0 ≤ o2.toInt) (h2s : o2.toInt ≤ blk.size)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int .i32 (if cmpOrd op o1.toInt o2.toInt then 1 else 0)) (.int .i32)) fs)
        ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b o2) t2) (.binRhsF op (.ptr b o1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp1 : t1.isPtr = true := CTy.isPtr_of_unqual_ptr ht1
  have hp2 : t2.isPtr = true := CTy.isPtr_of_unqual_ptr ht2
  have hg : (0 ≤ o1.toInt && o1.toInt ≤ (blk.size : Int) && 0 ≤ o2.toInt && o2.toInt ≤ (blk.size : Int)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨⟨h10, h1s⟩, h20⟩, h2s⟩
  have hap : applyBinary cfg prog.tags m op (.ptr b o1) t1 (.ptr b o2) t2 =
      some (.int .i32 (if cmpOrd op o1.toInt o2.toInt then 1 else 0), .int .i32) := by
    rcases hop with rfl | rfl | rfl | rfl <;>
      simp only [applyBinary, hp1, hp2, Bool.true_or, ↓reduceIte, evalPtrCmp, beq_self_eq_true,
        hb, hg, guard_true, Option.map, bind, Option.bind, pure, Pure.pure]
  exact wp_binRhs_ret hap hw

theorem wp_binRhs_ptrDiff {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {b : BlockId} {o1 o2 : Int64} {blk : Block} {t1 t2 el1 el2 : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (ht1 : t1.unqual = .ptr el1) (ht2 : t2.unqual = .ptr el2)
    (hb : m.blocks b = some blk)
    (h10 : 0 ≤ o1.toInt) (h1s : o1.toInt ≤ blk.size)
    (h20 : 0 ≤ o2.toInt) (h2s : o2.toInt ≤ blk.size)
    (hdvd : ((o1.toInt - o2.toInt) % (max 1 (sizeofTy prog.tags el1) : Int) == 0) = true)
    (hlo : IntKind.i64.minVal ≤ (o1.toInt - o2.toInt) / (max 1 (sizeofTy prog.tags el1) : Int))
    (hhi : (o1.toInt - o2.toInt) / (max 1 (sizeofTy prog.tags el1) : Int) ≤ IntKind.i64.maxVal)
    (hw : ∀ newBv : BitVec 64,
      intToInt .i64 newBv = (o1.toInt - o2.toInt) / (max 1 (sizeofTy prog.tags el1) : Int) →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int .i64 newBv) (.int .i64)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.ptr b o2) t2) (.binRhsF .sub (.ptr b o1) t1 :: fs)) ctx mods)
        env blks m os k) := by
  have hp1 : t1.isPtr = true := CTy.isPtr_of_unqual_ptr ht1
  have hp2 : t2.isPtr = true := CTy.isPtr_of_unqual_ptr ht2
  have hg : (0 ≤ o1.toInt && o1.toInt ≤ (blk.size : Int) && 0 ≤ o2.toInt && o2.toInt ≤ (blk.size : Int)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨⟨h10, h1s⟩, h20⟩, h2s⟩
  have hex := ofIntExact_signed_bounds (k := .i64) rfl hlo hhi
  have hap : applyBinary cfg prog.tags m .sub (.ptr b o1) t1 (.ptr b o2) t2 =
      some (.int .i64 (BitVec.ofInt 64 ((o1.toInt - o2.toInt) / (max 1 (sizeofTy prog.tags el1) : Int))), .int .i64) := by
    unfold applyBinary
    simp only [hp1, hp2, Bool.true_or, Bool.and_self, ↓reduceIte, ht1, evalPtrDiff, beq_self_eq_true,
      guard_true, hb, hg, hdvd, hex, Option.map, bind, Option.bind]
    rfl
  exact wp_binRhs_ret hap (hw _ (intToInt_ofInt_eq hlo hhi))

/-! ### Field `incDec` and Slot/Field `assignOp` Lemmas -/

theorem wp_incDec_field_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty : CTy}
    {P : Val → Prop} {ik : IntKind} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnu : ¬ P .undef) (hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      let ck := IntKind.usualArith ik .i32
      let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
      ck.minVal ≤ intToInt ik oldBv ∧ intToInt ik oldBv ≤ ck.maxVal ∧
      (ck.signed = true → ck.minVal ≤ intToInt ik oldBv + d ∧ intToInt ik oldBv + d ≤ ck.maxVal))
    (hw : ∀ (m' : Mem) (oldBv newBv : BitVec ik.bits)
      (midBv : BitVec (IntKind.usualArith ik .i32).bits),
      P (.int ik oldBv) →
      intToInt (IntKind.usualArith ik .i32) midBv =
        intToInt (IntKind.usualArith ik .i32)
          (BitVec.ofInt (IntKind.usualArith ik .i32).bits
            (intToInt ik oldBv + (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1))) →
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt (IntKind.usualArith ik .i32) midBv)) →
      Sem.writeVal m b fldOff fty (.int ik newBv) = some m' →
      Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      let retV : Val := match op with
        | .preInc | .preDec => .int (IntKind.usualArith ik .i32) midBv
        | .postInc | .postDec => .int ik oldBv
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval retV fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b fldOff fty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  subst hoff
  rcases hf with ⟨foff0, blk, hfl0, hb, hp, h0, hsz, hal, hval⟩
  rw [hfl] at hfl0
  cases hfl0
  rcases hval with ⟨oldV, hrd, hpv⟩ | hundef
  · have hrw : blk.perm = .rw := hp hnc_ty
    have hcases : ∃ oldBv : BitVec ik.bits, oldV = .int ik oldBv := by
      have hrd' := hrd
      unfold Sem.readVal at hrd'
      rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk (Int64.ofInt (soff.toInt + ↑foff)) ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b (Int64.ofInt (soff.toInt + ↑foff)) ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hki, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk (Int64.ofInt (soff.toInt + ↑foff)) ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b (Int64.ofInt (soff.toInt + ↑foff)) ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
    rcases hcases with ⟨oldBv, rfl⟩
    let ck := IntKind.usualArith ik .i32
    have hck_bounds := hok oldBv hpv
    have hsz_eq : sizeofTy prog.tags fty = ik.bytes := sizeofTy_eq_scalar prog.tags hik
    have hal_eq : alignofTy prog.tags fty = ik.align := alignofTy_eq_scalar prog.tags hik
    have hal_pos : max 1 (alignofTy prog.tags fty) = ik.align := by
      rw [hal_eq]; cases ik <;> rfl
    have hlt : soff.toInt + foff < ptrDiffLimit := by have := blk.sizeLt; omega
    have hfld_int : (Int64.ofInt (soff.toInt + foff)).toInt = soff.toInt + foff :=
      int64_ofInt_toInt (by omega) hlt
    have hal' : Mem.isAligned blk (Int64.ofInt (soff.toInt + foff)) ik.align = true := hal_pos ▸ hal
    have hin' : Mem.inBounds blk (Int64.ofInt (soff.toInt + foff)) ik.bytes = true := by
      rw [inBounds_iff, hfld_int, ← hsz_eq]; exact ⟨by omega, by omega⟩
    have hbin_one : ∀ (d : Int) (hd : d = 1 ∨ d = -1)
        (hd_val : intToInt .i32 (BitVec.ofInt 32 d) = d)
        (hsr_fn : ck.signed = true → ck.minVal ≤ intToInt ik oldBv + d ∧ intToInt ik oldBv + d ≤ ck.maxVal),
        applyBinary cfg prog.tags m .add (.int ik oldBv) fty
          (.int .i32 (BitVec.ofInt 32 d)) (.int .i32) =
          some (.int ck (BitVec.ofInt ck.bits (intToInt ik oldBv + d)), .int ck) := by
      intro d hd hd_val hsr_fn
      rw [applyBinary_int_of_intKind hik (by rfl : (CTy.int .i32).intKind? = some .i32)]
      cases hs_ck : ck.signed
      · have hev := evalIntBinary_arith_unsigned (k2 := .i32) (Or.inl rfl) oldBv (BitVec.ofInt 32 d) hs_ck
          (fun h => by rcases h with h | h <;> cases h)
        dsimp only at hev
        rw [hd_val, ofInt_add_unsigned hs_ck (intToInt ik oldBv) d] at hev
        exact hev
      · have hsr := hsr_fn hs_ck
        have h2_bounds : ck.minVal ≤ intToInt .i32 (BitVec.ofInt 32 d) ∧
            intToInt .i32 (BitVec.ofInt 32 d) ≤ ck.maxVal := by
          rw [hd_val]
          have hck_range := usualArith_minMax_one ik hs_ck
          dsimp only [ck] at hck_range ⊢
          rcases hd with rfl | rfl <;> omega
        exact evalIntBinary_arith_signed (k2 := .i32) (Or.inl rfl) oldBv
          (bv2 := (BitVec.ofInt 32 d : BitVec IntKind.i32.bits)) hs_ck
          ⟨hck_bounds.1, hck_bounds.2.1⟩ h2_bounds (fun h => by rcases h with h | h <;> cases h)
          (intToInt ik oldBv + d) (by dsimp only; rw [hd_val]) hsr.1 hsr.2
    have hrun : ∀ (d : Int),
        ∃ (m' : Mem) (midBv : BitVec ck.bits) (newBv : BitVec ik.bits),
          midBv = BitVec.ofInt ck.bits (intToInt ik oldBv + d) ∧
          newBv = BitVec.ofInt ik.bits (intToInt ck midBv) ∧
          Sem.writeVal m b (Int64.ofInt (soff.toInt + foff)) fty (.int ik newBv) = some m' ∧
          Sem.writeVal m b (Int64.ofInt (soff.toInt + foff)) fty (.int ck midBv) = some m' ∧
          Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) ∧
          FrameBlocks m m' {b} := by
      intro d
      let midBv := BitVec.ofInt ck.bits (intToInt ik oldBv + d)
      let newBv := BitVec.ofInt ik.bits (intToInt ck midBv)
      obtain ⟨m', hwr_new⟩ := writeVal_int_some' hnc_ty hik hb hrw hal' hin'
        (valAsInt?_int_toInt ik newBv)
      have heq_bv : BitVec.ofInt ik.bits (intToInt ck midBv) = BitVec.ofInt ik.bits (intToInt ik newBv) :=
        (ofInt_intToInt ik newBv).symm
      have hwr_eq : Sem.writeVal m b (Int64.ofInt (soff.toInt + foff)) fty (.int ck midBv) =
          Sem.writeVal m b (Int64.ofInt (soff.toInt + foff)) fty (.int ik newBv) := by
        unfold Sem.writeVal
        rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩
        · simp only [hnc_ty, Bool.not_false, guard_true, hb, hu, CTy.unqual, CTy.intKind?,
            valAsInt?_int_toInt, bind, Option.bind, heq_bv]
        · simp only [hnc_ty, Bool.not_false, guard_true, hb, hu, CTy.unqual, CTy.intKind?,
            hki, valAsInt?_int_toInt, bind, Option.bind, heq_bv]
      have hwr_mid : Sem.writeVal m b (Int64.ofInt (soff.toInt + foff)) fty (.int ck midBv) = some m' :=
        hwr_eq.trans hwr_new
      have hrd_new : Sem.readVal prog.tags m' b (Int64.ofInt (soff.toInt + foff)) fty = some (.int ik newBv) :=
        readVal_writeVal_same_int' prog.tags rfl hik hb hwr_new
      obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr_new
      have hblk' := writeBytes_blocks_eq hb hwb
      have hf' : Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) :=
        ⟨foff, _, hfl, hblk', hp, h0, hsz, by simpa [Mem.isAligned] using hal, Or.inl ⟨_, hrd_new, rfl⟩⟩
      exact ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hf', FrameBlocks.of_writeVal hwr_new⟩
    cases op
    · have hbin := hbin_one 1 (Or.inl rfl) (intToInt_incDec_delta .preInc) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hf', hfr⟩ := hrun 1
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b (Int64.ofInt (soff.toInt + foff)) fty) (.incDecF .preInc :: fs)) =
          some (.ret (.rval (.int ck (BitVec.ofInt ck.bits (intToInt ik oldBv + 1))) fty) fs,
                m', ⟨b, Int64.ofInt (soff.toInt + foff), sizeofTy prog.tags fty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hf' hfr)
    · have hbin := hbin_one (-1) (Or.inr rfl) (intToInt_incDec_delta .preDec) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hf', hfr⟩ := hrun (-1)
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b (Int64.ofInt (soff.toInt + foff)) fty) (.incDecF .preDec :: fs)) =
          some (.ret (.rval (.int ck (BitVec.ofInt ck.bits (intToInt ik oldBv + -1))) fty) fs,
                m', ⟨b, Int64.ofInt (soff.toInt + foff), sizeofTy prog.tags fty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hf' hfr)
    · have hbin := hbin_one 1 (Or.inl rfl) (intToInt_incDec_delta .postInc) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hf', hfr⟩ := hrun 1
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b (Int64.ofInt (soff.toInt + foff)) fty) (.incDecF .postInc :: fs)) =
          some (.ret (.rval (.int ik oldBv) fty) fs,
                m', ⟨b, Int64.ofInt (soff.toInt + foff), sizeofTy prog.tags fty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hf' hfr)
    · have hbin := hbin_one (-1) (Or.inr rfl) (intToInt_incDec_delta .postDec) (fun hs => by simpa using hck_bounds.2.2 hs)
      obtain ⟨m', midBv, newBv, rfl, rfl, hwr_new, hwr_mid, hf', hfr⟩ := hrun (-1)
      have hstep : stepExprPure prog cfg env m mods (.ret (.lval b (Int64.ofInt (soff.toInt + foff)) fty) (.incDecF .postDec :: fs)) =
          some (.ret (.rval (.int ik oldBv) fty) fs,
                m', ⟨b, Int64.ofInt (soff.toInt + foff), sizeofTy prog.tags fty⟩ :: mods) := by
        unfold stepExprPure
        simp only [hnc, Bool.not_false, guard_true, hrd, hbin, hwr_mid, bind, Option.bind, pure, Pure.pure]
      exact WPTerm.of_exprPure hstep (by simpa using hw m' oldBv _ _ hpv rfl rfl hwr_new hf' hfr)
  · exact False.elim (hnu hundef)

theorem wp_incDec_field_post_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} (hop : op = .postInc ∨ op = .postDec)
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty : CTy}
    {P : Val → Prop} {ik : IntKind} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnu : ¬ P .undef) (hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hfit : fitsIn ik (IntKind.usualArith ik .i32) = true)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      ((IntKind.usualArith ik .i32).signed = true →
        (IntKind.usualArith ik .i32).minVal ≤ intToInt ik oldBv + incDecDelta op ∧
        intToInt ik oldBv + incDecDelta op ≤ (IntKind.usualArith ik .i32).maxVal) ∧
      (ik.minVal ≤ intToInt ik oldBv + incDecDelta op ∧ intToInt ik oldBv + incDecDelta op ≤ ik.maxVal))
    (hw : ∀ (m' : Mem) (oldBv newBv : BitVec ik.bits),
      P (.int ik oldBv) →
      intToInt ik newBv = intToInt ik oldBv + incDecDelta op →
      Sem.writeVal m b fldOff fty (.int ik newBv) = some m' →
      Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik oldBv) fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b fldOff fty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  refine wp_incDec_field_int hf hfl hoff hnu hnc_ty hik hnc ?_ ?_
  · intro oldBv hpv
    have hfb := fitsIn_bounds hfit oldBv
    have hok' := hok oldBv hpv
    dsimp only [incDecDelta] at hok'
    refine ⟨hfb.1, hfb.2, fun hs_ck => ?_⟩
    rcases hop with rfl | rfl <;> exact hok'.1 hs_ck
  · intro m' oldBv newBv midBv hpv hmid hnew hwr hf' hfr
    have hok' := hok oldBv hpv
    dsimp only [incDecDelta] at hok'
    have hmid_val : intToInt (IntKind.usualArith ik .i32) midBv =
        intToInt ik oldBv + (match op with | .postInc => 1 | _ => -1) := by
      rw [hmid]
      have hmm := minMax_le_usualArith_of_fitsIn hfit
      have h2 := hok'.2
      rcases hop with rfl | rfl <;> dsimp only at h2 ⊢ <;> exact intToInt_ofInt_eq (by omega) (by omega)
    have hnew_eq : intToInt ik newBv =
        intToInt ik oldBv + (match op with | .postInc => 1 | _ => -1) := by
      rw [hnew, hmid_val]
      rcases hop with rfl | rfl <;> exact intToInt_ofInt_eq hok'.2.1 hok'.2.2
    rcases hop with rfl | rfl <;> exact hw m' oldBv newBv hpv hnew_eq hwr hf' hfr

theorem wp_incDec_field_post_int_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} (hop : op = .postInc ∨ op = .postDec)
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty : CTy}
    {ik : IntKind} {oldBv : BitVec ik.bits} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty (· = .int ik oldBv))
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hfit : fitsIn ik (IntKind.usualArith ik .i32) = true)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hs_lo : (IntKind.usualArith ik .i32).signed = true →
      (IntKind.usualArith ik .i32).minVal ≤ intToInt ik oldBv + incDecDelta op)
    (hs_hi : (IntKind.usualArith ik .i32).signed = true →
      intToInt ik oldBv + incDecDelta op ≤ (IntKind.usualArith ik .i32).maxVal)
    (hlo : ik.minVal ≤ intToInt ik oldBv + incDecDelta op)
    (hhi : intToInt ik oldBv + incDecDelta op ≤ ik.maxVal)
    (hw : ∀ (m' : Mem) (newBv : BitVec ik.bits),
      intToInt ik newBv = intToInt ik oldBv + incDecDelta op →
      Sem.writeVal m b fldOff fty (.int ik newBv) = some m' →
      Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik oldBv) fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b fldOff fty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  refine wp_incDec_field_post_int hop hf hfl hoff (fun h => by cases h) hnc_ty hik hfit hnc
    (fun _ h => by cases h; exact ⟨fun hs_ck => ⟨hs_lo hs_ck, hs_hi hs_ck⟩, hlo, hhi⟩) ?_
  intro m' oldBv' newBv h heq hwr hf' hfr
  cases h
  exact hw m' newBv heq hwr hf' hfr

theorem wp_incDec_field_pre_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : IncDecOp} (hop : op = .preInc ∨ op = .preDec)
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty : CTy}
    {P : Val → Prop} {ik : IntKind} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnu : ¬ P .undef) (hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hck : IntKind.usualArith ik .i32 = ik)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      ik.signed = true → ik.minVal ≤ intToInt ik oldBv + incDecDelta op ∧ intToInt ik oldBv + incDecDelta op ≤ ik.maxVal)
    (hw : ∀ (m' : Mem) (oldBv newBv : BitVec ik.bits),
      P (.int ik oldBv) →
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt ik oldBv + incDecDelta op)) →
      Sem.writeVal m b fldOff fty (.int ik newBv) = some m' →
      Field prog.tags m' b soff structTag fld fty (· = .int ik newBv) →
      FrameBlocks m m' {b} →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (.int ik newBv) fty) fs) ctx
            (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
          env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b fldOff fty) (.incDecF op :: fs)) ctx mods) env blks m os k) := by
  refine wp_incDec_field_int hf hfl hoff hnu hnc_ty hik hnc ?_ ?_
  · intro oldBv hpv
    have hb := intToInt_bounds ik oldBv
    rw [hck]
    refine ⟨hb.1, hb.2, fun hs_ck => ?_⟩
    rcases hop with rfl | rfl <;> exact hok oldBv hpv hs_ck
  · intro m' oldBv newBv midBv hpv hmid hnew hwr hf' hfr
    have heq_new : newBv = hck ▸ midBv := eq_of_intToInt_cast hck newBv midBv hnew
    have hnew' : intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits
        (intToInt ik oldBv + (match op with | .preInc => 1 | _ => -1))) := by
      rw [heq_new, intToInt_cast_eq hck midBv, hmid]
      rcases hop with rfl | rfl <;> exact intToInt_ofInt_cast hck _
    have hret : Val.int (IntKind.usualArith ik .i32) midBv = Val.int ik newBv := by
      rw [heq_new, val_int_cast_eq hck midBv]
    rcases hop with rfl | rfl
    · simpa [hret] using hw m' oldBv newBv hpv hnew' hwr hf' hfr
    · simpa [hret] using hw m' oldBv newBv hpv hnew' hwr hf' hfr

theorem wp_assignOp_slot_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : AssignOp} {bop : BinOp} (hop : assignOpToBin? op = some bop)
    {name : String} {b : BlockId} {lty rty : CTy} {P : Val → Prop}
    {ik rk : IntKind} {rbv : BitVec rk.bits}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hs : Slot env m name b lty P) (hnu : ¬ P .undef)
    (_hnc_ty : lty.isConst = false) (hik : lty.intKind? = some ik)
    (hrk : rty.intKind? = some rk)
    (hnc : mods.conflicts b 0 (sizeofTy prog.tags lty) = false)
    (hbin_ok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      ∃ nv nt, applyBinary cfg prog.tags m bop (.int ik oldBv) lty (.int rk rbv) rty = some (nv, nt) ∧
        ∃ cv m', writePlace prog.tags m b 0 lty (.rval nv lty) = some (.rval cv lty, m') ∧
          Slot env m' name b lty (· = cv) ∧
          FrameBlocks m m' {b} ∧
          WPTerm prog cfg ext Q
            (.running (.expr (.ret (.rval cv lty) fs) ctx (⟨b, 0, sizeofTy prog.tags lty⟩ :: mods))
              env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int rk rbv) rty) (.assignRhsF op b 0 lty :: fs)) ctx mods)
        env blks m os k) := by
  let _ := hrk
  rcases hs with ⟨_, blk, hb, _, _, _, hval⟩
  rcases hval with ⟨oldV, hrd, hpv⟩ | hundef
  · have hcases : ∃ oldBv : BitVec ik.bits, oldV = .int ik oldBv := by
      have hrd' := hrd
      unfold Sem.readVal at hrd'
      rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk 0 ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b 0 ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hki, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk 0 ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b 0 ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
    rcases hcases with ⟨oldBv, rfl⟩
    obtain ⟨nv, nt, hbin, cv, m', hwp, _, _, hw⟩ := hbin_ok oldBv hpv
    have hrd_tags : Sem.readVal prog.tags m b 0 lty = some (.int ik oldBv) := by
      rw [readVal_tags_irrel prog.tags []]; exact hrd
    exact wp_assignOp hop hnc hrd_tags hbin hwp hw
  · exact False.elim (hnu hundef)

theorem wp_assignOp_field_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {op : AssignOp} {bop : BinOp} (hop : assignOpToBin? op = some bop)
    {b : BlockId} {soff fldOff : Int64} {structTag fld : String} {fty rty : CTy} {P : Val → Prop}
    {ik rk : IntKind} {rbv : BitVec rk.bits} {foff : Nat}
    {fs : List ExprFrame} {ctx : ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hf : Field prog.tags m b soff structTag fld fty P)
    (hfl : fieldLayout? prog.tags (.structTy structTag) fld = some (foff, fty))
    (hoff : fldOff = Int64.ofInt (soff.toInt + foff))
    (hnu : ¬ P .undef) (_hnc_ty : fty.isConst = false) (hik : fty.intKind? = some ik)
    (hrk : rty.intKind? = some rk)
    (hnc : mods.conflicts b fldOff (sizeofTy prog.tags fty) = false)
    (hbin_ok : ∀ oldBv : BitVec ik.bits, P (.int ik oldBv) →
      ∃ nv nt, applyBinary cfg prog.tags m bop (.int ik oldBv) fty (.int rk rbv) rty = some (nv, nt) ∧
        ∃ cv m', writePlace prog.tags m b fldOff fty (.rval nv fty) = some (.rval cv fty, m') ∧
          Field prog.tags m' b soff structTag fld fty (· = cv) ∧
          FrameBlocks m m' {b} ∧
          WPTerm prog cfg ext Q
            (.running (.expr (.ret (.rval cv fty) fs) ctx
                (⟨b, fldOff, sizeofTy prog.tags fty⟩ :: mods))
              env blks m' os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int rk rbv) rty) (.assignRhsF op b fldOff fty :: fs)) ctx mods)
        env blks m os k) := by
  let _ := hrk
  subst hoff
  rcases hf with ⟨foff0, blk, hfl0, hb, _, _, _, _, hval⟩
  rw [hfl] at hfl0
  cases hfl0
  rcases hval with ⟨oldV, hrd, hpv⟩ | hundef
  · have hcases : ∃ oldBv : BitVec ik.bits, oldV = .int ik oldBv := by
      have hrd' := hrd
      unfold Sem.readVal at hrd'
      rcases intKind?_unqual_cases hik with hu | ⟨tag, isU, hu, hki⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk (Int64.ofInt (soff.toInt + ↑foff)) ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b (Int64.ofInt (soff.toInt + ↑foff)) ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
      · simp only [hu, CTy.unqual, CTy.intKind?, hki, hb, bind, Option.bind] at hrd'
        cases hrb : Mem.isAligned blk (Int64.ofInt (soff.toInt + ↑foff)) ik.align
        · simp only [hrb, guard, Pure.pure, Bool.false_eq_true, ↓reduceIte] at hrd'
          have hfail : (failure : Option Unit) = none := rfl
          simp only [hfail] at hrd'; cases hrd'
        · simp only [hrb, guard_true] at hrd'
          cases hrb2 : m.readBytes b (Int64.ofInt (soff.toInt + ↑foff)) ik.bytes with
          | none => simp only [hrb2] at hrd'; cases hrd'
          | some bs =>
            simp only [hrb2] at hrd'
            cases hdec : Mem.decodeInt ik bs with
            | none => simp only [hdec] at hrd'; cases hrd'
            | some bv => simp only [hdec, pure, Pure.pure, Option.some.injEq] at hrd'; exact ⟨bv, hrd'.symm⟩
    rcases hcases with ⟨oldBv, rfl⟩
    obtain ⟨nv, nt, hbin, cv, m', hwp, _, _, hw⟩ := hbin_ok oldBv hpv
    exact wp_assignOp hop hnc hrd hbin hwp hw
  · exact False.elim (hnu hundef)

/-! ### Framing/NextBlock Helpers & Short Aliases -/

theorem Slot.lt_nextBlock {env : Env} {m : Mem} {name : String} {b : BlockId}
    {ty : CTy} {P : Val → Prop} (hs : Slot env m name b ty P) : b < m.nextBlock := by
  rcases hs with ⟨_, blk, hb, _⟩
  exact lt_nextBlock_of_some hb

theorem Field.lt_nextBlock {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) : b < m.nextBlock := by
  rcases hf with ⟨_, blk, _, hb, _⟩
  exact lt_nextBlock_of_some hb

theorem PtrValid.lt_nextBlock_ptr {m : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (hp : PtrValid m (.ptr b off) len) : b < m.nextBlock := by
  rcases hp with ⟨b', off', blk, heq, hb, _⟩
  cases heq
  exact lt_nextBlock_of_some hb

theorem PtrWritable.lt_nextBlock_ptr {m : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (hp : PtrWritable m (.ptr b off) len) : b < m.nextBlock := by
  rcases hp with ⟨b', off', blk, heq, hb, _⟩
  cases heq
  exact lt_nextBlock_of_some hb

theorem alloc_nextBlock_eq {m m' : Mem} {sz al : Nat} {perm : Perm} {k : AllocKind}
    {ba : UInt64} {init : Nat → MemByte}
    {h1 : sz < ptrDiffLimit} {h2 : 0 < al} {h3 : ba.toNat % al = 0} {bid : BlockId}
    (ha : m.alloc sz al perm k ba init h1 h2 h3 = (bid, m')) :
    m'.nextBlock = m.nextBlock + 1 := by
  have hm' : m' = (m.alloc sz al perm k ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  rw [hm']; rfl

theorem writePlace_nextBlock {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {rv res : ExprRes} (h : writePlace tags m b off ty rv = some (res, m')) :
    m'.nextBlock = m.nextBlock := by
  obtain ⟨_, hwb⟩ := writePlace_writeBytes h
  exact writeBytes_nextBlock hwb

theorem Slot.preserve_frameBlocks_next {env : Env} {m m' : Mem} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (hfr : FrameBlocks m m' {m.nextBlock}) :
    Slot env m' name b ty P :=
  hs.preserve_frameBlocks hfr (fun hm =>
    Nat.ne_of_lt hs.lt_nextBlock (by simpa [AutoBlockSet.mem_singleton] using hm))

theorem Field.preserve_frameBlocks_next {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) (hfr : FrameBlocks m m' {m.nextBlock}) :
    Field tags m' b off structTag fld fty P :=
  hf.preserve_frameBlocks hfr (fun hm =>
    Nat.ne_of_lt hf.lt_nextBlock (by simpa [AutoBlockSet.mem_singleton] using hm))

theorem blocks_preserve_frameBlocks_next {m m' : Mem} {b : BlockId} {blk : Block}
    (hfr : FrameBlocks m m' {m.nextBlock}) (hb : m.blocks b = some blk) :
    m'.blocks b = some blk :=
  blocks_preserve_frameBlocks hfr hb (fun hm =>
    Nat.ne_of_lt (lt_nextBlock_of_some hb) (by simpa [AutoBlockSet.mem_singleton] using hm))

theorem Field.preserve_writeVal_disjoint_fld {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {soff : Int64} {wfoff : Nat} {wty : CTy} {wv : Val}
    {structTag fld wfld : String} {fty : CTy} {P Pw : Val → Prop} {foff : Nat}
    (hf : Field tags m b soff structTag fld fty P)
    (hfw : Field tags m b soff structTag wfld wty Pw)
    (hwr : Sem.writeVal m b (Int64.ofInt (soff.toInt + wfoff)) wty wv = some m')
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hflw : fieldLayout? tags (.structTy structTag) wfld = some (wfoff, wty))
    (hdis : foff + sizeofTy tags fty ≤ wfoff ∨ wfoff + sizeofTy tags wty ≤ foff) :
    Field tags m' b soff structTag fld fty P := by
  rcases hfw with ⟨wfoff0, wblk, hflw0, _, _, h0w, hszw, _⟩
  rw [hflw] at hflw0
  cases hflw0
  have hltw : soff.toInt + wfoff < ptrDiffLimit := by have := wblk.sizeLt; omega
  have hw_int : (Int64.ofInt (soff.toInt + wfoff)).toInt = soff.toInt + wfoff :=
    int64_ofInt_toInt (by omega) hltw
  refine hf.preserve_writeVal_disjoint hfl hwr (by omega) ?_
  rw [hw_int]
  omega

theorem Field.preserve_writePlace_disjoint_fld {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {soff : Int64} {wfoff : Nat} {wty : CTy} {rv res : ExprRes}
    {structTag fld wfld : String} {fty : CTy} {P Pw : Val → Prop} {foff : Nat}
    (hf : Field tags m b soff structTag fld fty P)
    (hfw : Field tags m b soff structTag wfld wty Pw)
    (hwr : writePlace tags m b (Int64.ofInt (soff.toInt + wfoff)) wty rv = some (res, m'))
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hflw : fieldLayout? tags (.structTy structTag) wfld = some (wfoff, wty))
    (hdis : foff + sizeofTy tags fty ≤ wfoff ∨ wfoff + sizeofTy tags wty ≤ foff) :
    Field tags m' b soff structTag fld fty P := by
  obtain ⟨bs, hwb, hlen⟩ := writePlace_writeBytes_len hwr
  rcases hfw with ⟨wfoff0, wblk, hflw0, _, _, h0w, hszw, _⟩
  rw [hflw] at hflw0
  cases hflw0
  have hltw : soff.toInt + wfoff < ptrDiffLimit := by have := wblk.sizeLt; omega
  have hw_int : (Int64.ofInt (soff.toInt + wfoff)).toInt = soff.toInt + wfoff :=
    int64_ofInt_toInt (by omega) hltw
  refine hf.preserve_writeBytes_disjoint hfl hwb (by omega) ?_
  rw [hw_int, hlen]
  omega

private theorem slot_freeStack_at {env : Env} {m : Mem} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (blks : List BlockId) (hnot : b ∉ blks) :
    Slot env (m.freeStack blks) name b ty P :=
  hs.preserve_freeStack hnot

private theorem field_freeStack_at {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {structTag fld : String} {fty : CTy} {P : Val → Prop}
    (hf : Field tags m b off structTag fld fty P) (blks : List BlockId) (hnot : b ∉ blks) :
    Field tags (m.freeStack blks) b off structTag fld fty P :=
  hf.preserve_freeStack hnot

private theorem blocks_freeStack_at {m : Mem} {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) (blks : List BlockId) (hnot : b ∉ blks) :
    (m.freeStack blks).blocks b = some blk :=
  blocks_preserve_freeStack hb hnot

private theorem ptrValid_freeStack_at {m : Mem} {p : Val} {len : Nat}
    (hv : PtrValid m p len) (blks : List BlockId)
    (hnot : ∀ b off, p = .ptr b off → b ∉ blks) :
    PtrValid (m.freeStack blks) p len :=
  hv.preserve_freeStack hnot

private theorem ptrWritable_freeStack_at {m : Mem} {p : Val} {len : Nat}
    (hw : PtrWritable m p len) (blks : List BlockId)
    (hnot : ∀ b off, p = .ptr b off → b ∉ blks) :
    PtrWritable (m.freeStack blks) p len :=
  hw.preserve_freeStack hnot

private theorem slot_env_cons_at {env : Env} {m : Mem} {name : String}
    {b : BlockId} {ty : CTy} {P : Val → Prop}
    (hs : Slot env m name b ty P) (dname : String) (db : BlockId) (dty : CTy)
    (hne : name ≠ dname) :
    Slot ((dname, db, dty) :: env) m name b ty P :=
  hs.preserve_env_cons hne

theorem wp_localDecl_init_int_fresh {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {ik k1 : IntKind} {bv : BitVec k1.bits} {vty : CTy}
    {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : d.ty.intKind? = some ik)
    (hw : ∀ (m2 : Mem) (newBv : BitVec ik.bits),
      intToInt ik newBv = intToInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)) →
      Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = .int ik newBv) →
      FrameBlocks m m2 {m.nextBlock} →
      m2.nextBlock = m.nextBlock + 1 →
      (∀ b, b ≠ m.nextBlock → m2.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int k1 bv) vty) []) (.varInit d rest) mods) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_scalar prog.tags hik]; cases ik <;> decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_scalar prog.tags hik]; cases ik <;> decide
  refine wp_localDecl_init hsz hal ?_
  intro base m1 hba ha
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy prog.tags d.ty),
      max 1 (alignofTy prog.tags d.ty), .rw, .stack, base, fun _ => .undef, hsz, hal, hba⟩ := by
    rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_le : ik.bytes ≤ max 1 (sizeofTy prog.tags d.ty) := by
    rw [sizeofTy_eq_scalar prog.tags hik]; exact Nat.le_max_right _ _
  have hal_eq : ik.align = max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_scalar prog.tags hik]; cases ik <;> rfl
  obtain ⟨m2, hwr⟩ := writeVal_int_some' (stripConst_isConst d.ty)
    (by simpa [CTy.intKind?, stripConst_unqual] using hik) hblk1 rfl
    (by rw [isAligned_iff]
        exact ⟨Int.le_refl _, by cases ik <;> decide,
          by rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero, hal_eq]; exact hba⟩)
    (by rw [inBounds_iff]; exact ⟨Int.le_refl _, by simpa [Int64.toInt_zero] using hsz_le⟩)
    (valAsInt?_int_toInt ik (BitVec.ofInt ik.bits (intToInt k1 bv)))
  obtain ⟨hwp, hslot, hfr⟩ := writePlace_int_slot hik ha hwr
  have hnb : m2.nextBlock = m.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr]; exact alloc_nextBlock_eq ha
  refine ⟨_, m2, hwp, hw m2 _ rfl hslot hfr hnb ?_⟩
  intro b hne
  rw [writeVal_blocks_ne hwr hne, hm1]
  exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne

theorem wp_localDecl_init_int_same_fresh {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {ik : IntKind} {bv : BitVec ik.bits} {vty : CTy}
    {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : d.ty.intKind? = some ik)
    (hw : ∀ (m2 : Mem),
      Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = .int ik bv) →
      FrameBlocks m m2 {m.nextBlock} →
      m2.nextBlock = m.nextBlock + 1 →
      (∀ b, b ≠ m.nextBlock → m2.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik bv) vty) []) (.varInit d rest) mods) env blks m os k) := by
  refine wp_localDecl_init_int_fresh hik ?_
  intro m2 newBv heq hslot hfr hnb hblks
  have hbv : newBv = bv := eq_of_intToInt_eq (by simpa [ofInt_intToInt] using heq)
  subst hbv
  exact hw m2 hslot hfr hnb hblks

theorem wp_localDecl_init_ptr_fresh {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {el : CTy} {v : Val} {vty : CTy}
    {rest : List VarDecl} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hptr : d.ty.unqual = .ptr el)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (hw : ∀ (m2 : Mem),
      Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = v) →
      FrameBlocks m m2 {m.nextBlock} →
      m2.nextBlock = m.nextBlock + 1 →
      (∀ b, b ≠ m.nextBlock → m2.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m2 os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval v vty) []) (.varInit d rest) mods) env blks m os k) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_ptr_auto prog.tags hptr]; decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) := by
    rw [alignofTy_eq_ptr_auto prog.tags hptr]; decide
  refine wp_localDecl_init hsz hal ?_
  intro base m1 hba ha
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
      .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hblk1 : m1.blocks m.nextBlock = some ⟨max 1 (sizeofTy prog.tags d.ty),
      max 1 (alignofTy prog.tags d.ty), .rw, .stack, base, fun _ => .undef, hsz, hal, hba⟩ := by
    rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz8 : sizeofTy prog.tags d.ty = 8 := sizeofTy_eq_ptr_auto prog.tags hptr
  have hal8 : alignofTy prog.tags d.ty = 8 := alignofTy_eq_ptr_auto prog.tags hptr
  obtain ⟨m2, hwr⟩ := writeVal_ptr_some (stripConst_isConst d.ty)
    (by rw [stripConst_unqual, hptr]) hblk1 rfl
    (by rw [isAligned_iff]
        exact ⟨Int.le_refl _, by decide, by rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]; simpa [hal8] using hba⟩)
    (by rw [inBounds_iff]; exact ⟨Int.le_refl _, by simp [Int64.toInt_zero, hsz8]⟩)
    hv
  have hcast : castVal m1 d.ty.stripConst v = some v := by
    unfold castVal
    rcases hv with rfl | ⟨pb, poff, rfl⟩ <;>
      simp only [stripConst_unqual, hptr, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]
  have hwp : writePlace prog.tags m1 m.nextBlock 0 d.ty.stripConst (.rval v vty) =
      some (.rval v d.ty.stripConst, m2) := by
    unfold writePlace; simp [stripConst_unqual, hptr, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hrd : Sem.readVal [] m2 m.nextBlock 0 d.ty = some v :=
    readVal_writeVal_same_ptr' [] (by rw [stripConst_unqual, hptr]) hptr hblk1 hv hwr
  obtain ⟨_, hwb⟩ := writeVal_writeBytes hwr
  have hblk2 := writeBytes_blocks_eq hblk1 hwb
  have hslot : Slot ((d.name, m.nextBlock, d.ty) :: env) m2 d.name m.nextBlock d.ty (· = v) := by
    refine ⟨by simp [List.lookup], _, hblk2, fun _ => rfl, ?_, ?_, Or.inl ⟨_, hrd, rfl⟩⟩
    · rw [inBounds_iff]
      exact ⟨Int.le_refl _, by simpa [Int64.toInt_zero] using scalarSizeAlign_le_max1 prog.tags d.ty⟩
    · rw [isAligned_iff]
      dsimp only
      refine ⟨Int.le_refl _, ?_, ?_⟩
      · cases hu : d.ty.unqual <;> simp only [scalarSizeAlign, hu]
        · decide
        · cases ‹IntKind› <;> decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · cases ‹Bool› <;> decide
        · decide
        · decide
        · decide
      · rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (scalarSizeAlign_dvd_max1 prog.tags d.ty) (Nat.dvd_of_mod_eq_zero hba))
  have hfr : FrameBlocks m m2 {m.nextBlock} :=
    FrameBlocks.trans_same (FrameBlocks.of_alloc ha) (FrameBlocks.of_writeVal hwr)
  have hnb : m2.nextBlock = m.nextBlock + 1 := by
    rw [writeVal_nextBlock hwr]; exact alloc_nextBlock_eq ha
  refine ⟨_, m2, hwp, hw m2 hslot hfr hnb ?_⟩
  intro b hne
  rw [writeVal_blocks_ne hwr hne, hm1]
  exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne

theorem wp_localDecl_int_none_fresh {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rest : List VarDecl} {ik : IntKind}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = false) (hinit : d.init? = none) (hik : d.ty.intKind? = some ik)
    (hw : ∀ (_base : UInt64) (m1 : Mem),
      Slot.uninit ((d.name, m.nextBlock, d.ty) :: env) m1 d.name m.nextBlock d.ty →
      FrameBlocks m m1 {m.nextBlock} →
      m1.nextBlock = m.nextBlock + 1 →
      (∀ b, b ≠ m.nextBlock → m1.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m1 os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) := by
  refine wp_localDecl_int_none hst hinit hik (fun base m1 hsz hal hba ha hs hfr => ?_)
  exact hw base m1 hs hfr (alloc_nextBlock_eq ha) (fun b hne => by
    have hm1 : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
    rw [hm1]; exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne)

theorem wp_localDecl_ptr_none_fresh {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {d : VarDecl} {rest : List VarDecl} {el : CTy}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hst : d.isStatic = false) (hinit : d.init? = none) (hptr : d.ty.unqual = .ptr el)
    (hw : ∀ (_base : UInt64) (m1 : Mem),
      Slot.uninit ((d.name, m.nextBlock, d.ty) :: env) m1 d.name m.nextBlock d.ty →
      FrameBlocks m m1 {m.nextBlock} →
      m1.nextBlock = m.nextBlock + 1 →
      (∀ b, b ≠ m.nextBlock → m1.blocks b = m.blocks b) →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, m.nextBlock, d.ty) :: env) (m.nextBlock :: blks) m1 os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decls (d :: rest))) env blks m os k) := by
  refine wp_localDecl_ptr_none hst hinit hptr (fun base m1 hsz hal hba ha hs hfr => ?_)
  exact hw base m1 hs hfr (alloc_nextBlock_eq ha) (fun b hne => by
    have hm1 : m1 = (m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
    rw [hm1]; exact alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne)

theorem FrameBlocks.freeStack_local {m0 m1 : Mem} {allowed localAllowed : AutoBlockSet}
    {blks : List BlockId}
    (hfr : FrameBlocks m0 m1 (allowed ∪ localAllowed))
    (hge : ∀ b, b ∈ blks → m0.nextBlock ≤ b)
    (hcov : ∀ b, b ∈ localAllowed → b ∈ blks)
    (hstack : ∀ b blk, b ∈ blks → m1.blocks b = some blk → blk.kind = .stack) :
    FrameBlocks m0 (m1.freeStack blks) allowed := by
  refine ⟨by rw [freeStack_nextBlock]; exact hfr.1, ?_, ?_⟩
  · intro b hlt hnot
    have hnb : b ∉ blks := fun hm => Nat.not_le_of_gt hlt (hge b hm)
    have hnl : b ∉ localAllowed := fun hm => hnb (hcov b hm)
    rw [freeStack_blocks_not_mem m1 blks hnb]
    exact hfr.2.1 b hlt (fun h => h.elim hnot hnl)
  · intro b blk hle hnot hs
    by_cases hm : b ∈ blks
    · cases hb1 : m1.blocks b with
      | none =>
        have : (m1.freeStack blks).blocks b = none := by simp [Mem.freeStack, hm, hb1]
        rw [this] at hs; cases hs
      | some blk1 =>
        rw [freeStack_blocks_mem_stack m1 blks hm hb1 (hstack b blk1 hm hb1)] at hs
        cases hs
    · have hnl : b ∉ localAllowed := fun hl => hm (hcov b hl)
      rw [freeStack_blocks_not_mem m1 blks hm] at hs
      exact hfr.2.2 b blk hle (fun h => h.elim hnot hnl) hs

theorem wp_return_val_stop_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {k1 ik : IntKind} {bv : BitVec k1.bits} {ty : CTy} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : k.topRetTy.intKind? = some ik) (hnv : k.topRetTy.unqual.isVoid = false)
    (huw : unwindReturn m blks k = none)
    (hq : Q (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) (m.freeStack blks) os) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.int k1 bv) ty) []) .returnVal mods) env blks m os k) := by
  have hnv' : k.topRetTy.isVoid = false := by
    unfold CTy.isVoid at hnv ⊢; rw [cty_unqual_idem] at hnv; exact hnv
  have hcast : castVal m k.topRetTy (.int k1 bv) = some (.int ik (BitVec.ofInt ik.bits (intToInt k1 bv))) := by
    unfold castVal
    have hki : k.topRetTy.unqual.intKind? = some ik := by
      unfold CTy.intKind? at hik ⊢; rw [cty_unqual_idem]; exact hik
    simp only [hnv, hki, Bool.false_eq_true, ↓reduceIte, ofIntCast, intToInt]
  exact wp_return_val_stop hnv' hcast huw hq

theorem wp_return_val_stop_int_same {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {ik : IntKind} {bv : BitVec ik.bits} {ty : CTy} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hik : k.topRetTy.intKind? = some ik) (hnv : k.topRetTy.unqual.isVoid = false)
    (huw : unwindReturn m blks k = none)
    (hq : Q (.int ik bv) (m.freeStack blks) os) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.int ik bv) ty) []) .returnVal mods) env blks m os k) := by
  refine wp_return_val_stop_int hik hnv huw ?_
  simpa only [ofInt_intToInt] using hq

theorem wp_return_val_stop_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {v : Val} {ty el : CTy} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hp : k.topRetTy.unqual = .ptr el)
    (hv : v = .null ∨ ∃ pb poff, v = .ptr pb poff)
    (huw : unwindReturn m blks k = none)
    (hq : Q v (m.freeStack blks) os) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) []) .returnVal mods) env blks m os k) := by
  have hnv' : k.topRetTy.isVoid = false := by
    unfold CTy.isVoid; rw [hp]
  have hcast : castVal m k.topRetTy v = some v := by
    unfold castVal
    rcases hv with rfl | ⟨pb, poff, rfl⟩ <;>
      simp only [hp, CTy.isVoid, CTy.unqual, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]
  exact wp_return_val_stop hnv' hcast huw hq

theorem FrameBlocks.freeStack_preserve_ge {m0 m1 : Mem} {allowed : AutoBlockSet} {blks : List BlockId}
    (hf : FrameBlocks m0 m1 allowed) (hge : ∀ b, b ∈ blks → m0.nextBlock ≤ b) :
    FrameBlocks m0 (m1.freeStack blks) (fun b => allowed b ∨ m0.nextBlock ≤ b) := by
  refine ⟨by simpa only [freeStack_nextBlock] using hf.1, ?_, ?_⟩
  · intro b hb hnot
    have hnb : b ∉ blks := fun hm => Nat.not_lt_of_le (hge b hm) hb
    rw [freeStack_blocks_not_mem m1 blks hnb]
    exact hf.2.1 b hb (fun ha => hnot (Or.inl ha))
  · intro b _ hle hnot _
    exact False.elim (hnot (Or.inr hle))

theorem FrameBlocks.trans_sub {m0 m1 m2 : Mem} {a b : AutoBlockSet}
    (h1 : FrameBlocks m0 m1 a) (h2 : FrameBlocks m1 m2 b)
    (hsub : ∀ x, x ∈ b → x ∈ a) :
    FrameBlocks m0 m2 a :=
  FrameBlocks.trans_same h1 (h2.mono hsub)

theorem FrameBlocks.freeStack_allowed_ge {m0 m1 : Mem} {allowed : AutoBlockSet} {blks : List BlockId}
    (hf : FrameBlocks m0 m1 (fun b => allowed b ∨ m0.nextBlock ≤ b))
    (hge : ∀ b, b ∈ blks → m0.nextBlock ≤ b) :
    FrameBlocks m0 (m1.freeStack blks) (fun b => allowed b ∨ m0.nextBlock ≤ b) :=
  (hf.freeStack_preserve_ge hge).mono (fun _ h => h.elim id Or.inr)

theorem FrameBlocks.trans_next_ge {m0 m1 m2 : Mem} {allowed : AutoBlockSet}
    (hf1 : FrameBlocks m0 m1 (fun b => allowed b ∨ m0.nextBlock ≤ b))
    (hf2 : FrameBlocks m1 m2 {m1.nextBlock}) :
    FrameBlocks m0 m2 (fun b => allowed b ∨ m0.nextBlock ≤ b) :=
  hf1.trans_sub hf2 (fun _ h => by
    rw [AutoBlockSet.mem_singleton] at h; subst h; exact Or.inr hf1.1)

theorem wp_loop_next_while {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {c : CExpr} {body : CStmt} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Cont}
    (hw : WPTerm prog cfg ext Q (.running (.expr (.eval .rval c []) (.forCond c none body) []) env blks m os k)) :
    WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os (.loop (some c) none body false k)) :=
  WPTerm.of_det rfl hw

/-! ## 6. Automated Tactics (`c_frame`, `c_eval`, `c_step`, `c_run`) -/

section Tactics

open Lean Meta Elab Tactic

private def mkConstFresh (nm : Name) : MetaM Expr := do
  let info ← getConstInfo nm
  let us ← mkFreshLevelMVarsFor info
  return mkConst nm us

private def isWPTermTarget (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some ``C99.Proof.WPTerm

private def extractWPRunning (goal : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr)) := do
  let g ← whnfR goal
  let fn := g.getAppFn
  let args := g.getAppArgs
  if fn.constName? == some ``C99.Proof.WPTerm then
    if let (some a0, some a1, some a2, some a3, some a4) :=
        (args[0]?, args[1]?, args[2]?, args[3]?, args[4]?) then
      if args.size == 5 then
        let st ← whnf a4
        let sfn := st.getAppFn
        let sargs := st.getAppArgs
        if sfn.constName? == some ``C99.Sem.RunState.running && sargs.size == 6 then
          if let (some s0, some s1, some s2, some s3, some s4, some s5) :=
              (sargs[0]?, sargs[1]?, sargs[2]?, sargs[3]?, sargs[4]?, sargs[5]?) then
            return some (a0, a1, a2, a3, s0, s1, s2, s3, s4, s5)
  return none

private def fastCompatHyp (t1 t2 : Expr) : MetaM Bool := do
  let fn1 := t1.getAppFn.constName?
  let fn2 := t2.getAppFn.constName?
  if fn1 != fn2 then return false
  let a1 := t1.getAppArgs
  let a2 := t2.getAppArgs
  if fn1 == some ``C99.Proof.Slot && a1.size == 6 && a2.size == 6 then
    if let (some m1, some m2, some n1, some n2, some b1, some b2) :=
        (a1[1]?, a2[1]?, a1[2]?, a2[2]?, a1[3]?, a2[3]?) then
      if !(← withReducible (isDefEq m1 m2)) then return false
      if !(← withReducible (isDefEq n1 n2)) then return false
      if !(← withReducible (isDefEq b1 b2)) then return false
      return true
  if fn1 == some ``C99.Proof.Field && a1.size == 8 && a2.size == 8 then
    if let (some m1, some m2, some b1, some b2, some f1, some f2) :=
        (a1[1]?, a2[1]?, a1[2]?, a2[2]?, a1[5]?, a2[5]?) then
      if !(← withReducible (isDefEq m1 m2)) then return false
      if !(← withReducible (isDefEq b1 b2)) then return false
      if !(← withReducible (isDefEq f1 f2)) then return false
      return true
  if (fn1 == some ``C99.Proof.PtrValid || fn1 == some ``C99.Proof.PtrWritable) &&
      a1.size == 3 && a2.size == 3 then
    if let (some m1, some m2) := (a1[0]?, a2[0]?) then
      if !(← withReducible (isDefEq m1 m2)) then return false
      return true
  return true

private def existsHypOfType (tgt : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  for ldecl in lctx do
    if !ldecl.isImplementationDetail then
      if ← fastCompatHyp ldecl.type tgt then
        if ← isDefEq ldecl.type tgt then
          return true
  return false

private def existsHypOfTypeReducible (tgt : Expr) : MetaM Bool := do
  let tgtHead := tgt.getAppFn.constName?
  let lctx ← getLCtx
  for ldecl in lctx do
    if !ldecl.isImplementationDetail then
      if ldecl.type.getAppFn.constName? == tgtHead then
        if ← withReducible (isDefEq ldecl.type tgt) then
          return true
  return false

private def tryEval (stx : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    evalTactic stx
    if (← getGoals).isEmpty then
      return true
    else
      restoreState s
      return false
  catch _ =>
    restoreState s
    return false

private def noteFromGoal (nameHint : Name) (mkPrf : MetaM Expr) : TacticM Unit := do
  let mvarId ← getMainGoal
  let added ← mvarId.withContext do
    let prf ← mkPrf
    let ty ← inferType prf
    if ← existsHypOfTypeReducible ty then
      return none
    else
      let (_, mvarId') ← mvarId.note nameHint prf
      return some mvarId'
  if let some m' := added then
    replaceMainGoal [m']

private def injectNextBlockBounds : TacticM Unit := do
  let mvarId ← getMainGoal
  let fvarInfos ← mvarId.withContext do
    let lctx ← getLCtx
    let mut infos : List (Expr × Expr) := []
    for ldecl in lctx do
      if !ldecl.isImplementationDetail then
        let ty ← whnfR ldecl.type
        let fvar := ldecl.toExpr
        infos := (fvar, ty) :: infos
    return infos
  for (fvar, ty) in fvarInfos do
    let fn := ty.getAppFn.constName?
    let args := ty.getAppArgs
    if fn == some ``C99.Proof.Slot && args.size == 6 then
      try noteFromGoal `_hnb (mkAppM ``C99.Proof.Slot.lt_nextBlock #[fvar]) catch _ => pure ()
    else if fn == some ``C99.Proof.Field && args.size == 8 then
      try noteFromGoal `_hnb (mkAppM ``C99.Proof.Field.lt_nextBlock #[fvar]) catch _ => pure ()
      try
        noteFromGoal `_hf0 do
          mkAppM ``And.left #[← mkAppM ``And.right #[← mkAppM ``And.right #[← mkAppM ``And.right #[← mkAppM ``And.right #[fvar]]]]]
      catch _ => pure ()
    else if fn == some ``C99.Proof.PtrValid && args.size == 3 then
      try noteFromGoal `_hnb (mkAppM ``C99.Proof.PtrValid.lt_nextBlock_ptr #[fvar]) catch _ => pure ()
    else if fn == some ``C99.Proof.PtrWritable && args.size == 3 then
      try noteFromGoal `_hnb (mkAppM ``C99.Proof.PtrWritable.lt_nextBlock_ptr #[fvar]) catch _ => pure ()
    else if fn == some ``C99.Proof.FrameBlocks && args.size == 3 then
      try noteFromGoal `_hfr_nb (mkAppM ``And.left #[fvar]) catch _ => pure ()
    else if fn == some ``Eq && args.size == 3 then
      if let some lhs := args[1]? then
        let lfn := lhs.getAppFn.constName?
        if lfn == some ``C99.Mem.blocks then
          try noteFromGoal `_hnb (mkAppM ``C99.Proof.lt_nextBlock_of_some #[fvar]) catch _ => pure ()
        else if lfn == some ``C99.Mem.alloc then
          try noteFromGoal `_hnb (mkAppM ``C99.Proof.alloc_nextBlock_eq #[fvar]) catch _ => pure ()
        else if lfn == some ``C99.Sem.writeVal then
          try noteFromGoal `_hnb (mkAppM ``C99.Proof.writeVal_nextBlock #[fvar]) catch _ => pure ()
        else if lfn == some ``C99.Mem.writeBytes then
          try noteFromGoal `_hnb (mkAppM ``C99.Proof.writeBytes_nextBlock #[fvar]) catch _ => pure ()
        else if lfn == some ``C99.Sem.writePlace then
          try noteFromGoal `_hnb (mkAppM ``C99.Proof.writePlace_nextBlock #[fvar]) catch _ => pure ()

private partial def listMemReducible (e listExpr : Expr) : MetaM Bool := do
  let lw ← whnfR listExpr
  if lw.getAppFn.constName? == some ``List.cons && lw.getAppArgs.size == 3 then
    if let (some hd, some tl) := (lw.getAppArgs[1]?, lw.getAppArgs[2]?) then
      if ← withReducible (isDefEq e hd) then return true
      return ← listMemReducible e tl
  if lw.getAppFn.constName? == some ``C99.Proof.AutoBlockSet.singleton && lw.getAppArgs.size == 1 then
    if let some a := lw.getAppArgs[0]? then
      return ← withReducible (isDefEq e a)
  return false

private def isTriviallyFalseGoal (tRaw : Expr) : MetaM Bool := do
  let fn := tRaw.getAppFn.constName?
  let args := tRaw.getAppArgs
  if fn == some ``Ne && args.size == 3 then
    if let (some a, some b) := (args[1]?, args[2]?) then
      return ← withReducible (isDefEq a b)
  if fn == some ``Not && args.size == 1 then
    if let some inner := args[0]? then
      let innerW ← whnfR inner
      if innerW.getAppFn.constName? == some ``Membership.mem && innerW.getAppArgs.size == 5 then
        if let (some xs, some x) := (innerW.getAppArgs[3]?, innerW.getAppArgs[4]?) then
          return ← listMemReducible x xs
  return false

private def unfoldBlockIdAndArithInGoal : TacticM Unit := do
  let mut g ← getMainGoal
  let t ← g.withContext do instantiateMVars (← g.getType)
  let t1 := t.replace fun sub => if sub.isConstOf ``C99.BlockId then some (mkConst ``Nat) else none
  if t != t1 then
    g ← g.replaceTargetDefEq t1
  let fvarUpdates ← g.withContext do
    let lctx ← getLCtx
    let mut upd : Array (FVarId × Expr) := #[]
    for ld in lctx do
      if !ld.isImplementationDetail then
        let h := ld.type.getAppFn.constName?
        if h == some ``Eq || h == some ``Ne || h == some ``Not ||
           h == some ``LT.lt || h == some ``LE.le || h == some ``GT.gt || h == some ``GE.ge then
          let ty ← instantiateMVars ld.type
          let hasB := (ty.find? fun s => s.isConstOf ``C99.BlockId).isSome
          let hasA := (ty.find? fun s => s.isConstOf ``C99.Proof.evalArithRaw || s.isConstOf ``C99.Proof.incDecDelta).isSome
          let mut ty' := if hasB then
            ty.replace fun sub => if sub.isConstOf ``C99.BlockId then some (mkConst ``Nat) else none
            else ty
          if hasA then
            ty' ← Meta.transform ty' fun sub => do
              if sub.getAppFn.isConstOf ``C99.Proof.evalArithRaw ||
                 sub.getAppFn.isConstOf ``C99.Proof.incDecDelta then
                if let some u ← Meta.unfoldDefinition? sub then
                  return .visit (← whnfCore u)
              return .continue
          if ty' != ty then
            upd := upd.push (ld.fvarId, ty')
    return upd
  for (fv, ty') in fvarUpdates do
    g ← g.replaceLocalDeclDefEq fv ty'
  replaceMainGoal [g]

private def closedC99Arity? (n : Name) : Option Nat :=
  if n == ``C99.IntKind.usualArith || n == ``C99.Proof.fitsIn || n == ``C99.Proof.intToInt then some 2
  else if n == ``C99.IntKind.promote || n == ``C99.IntKind.rank ||
      n == ``C99.IntKind.minVal || n == ``C99.IntKind.maxVal ||
      n == ``C99.IntKind.signed ||
      n == ``C99.IntKind.bytes || n == ``C99.IntKind.align ||
      n == ``C99.CTy.unqual || n == ``C99.CTy.decay ||
      n == ``C99.CTy.isVoid || n == ``C99.CTy.isPtr ||
      n == ``C99.CTy.isConst || n == ``C99.CTy.intKind? ||
      n == ``C99.Proof.incDecDelta then some 1
  else if n == ``C99.Proof.evalArithRaw then some 3
  else none

private def reifyReduced (e : Expr) : Expr :=
  match e with
  | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => toExpr (n : Int)
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => toExpr (-(n + 1 : Int))
  | _ => e

private def reduceClosedC99 (e : Expr) : MetaM Expr :=
  Meta.transform e (skipConstInApp := true) fun sub => do
    if !sub.hasFVar && !sub.hasMVar && !sub.hasLooseBVars then
      if let some fn := sub.getAppFn.constName? then
        if closedC99Arity? fn == some sub.getAppNumArgs then
          return .done (reifyReduced (← Meta.reduce sub))
    return .continue

private def closeSideGoal (mvarId : MVarId) : TacticM Bool := do
  let origGoals ← getGoals
  let s ← saveState
  if ← mvarId.isAssigned then
    return true
  let isP ← mvarId.withContext do isProp (← mvarId.getType)
  if !isP then
    return false
  setGoals [mvarId]
  -- 1. Try assumption first
  if ← tryEval (← `(tactic| assumption)) then
    setGoals origGoals; return true
  -- Pre-reduce closed C99 scalar/type calls via kernel defeq (before `rfl` so out-params normalize)
  let mvarId ← try
    mvarId.withContext do
      let t ← instantiateMVars (← mvarId.getType)
      let t' ← reduceClosedC99 t
      if t == t' then pure mvarId else mvarId.replaceTargetDefEq t'
  catch _ => pure mvarId
  setGoals [mvarId]
  if ← tryEval (← `(tactic| rfl)) then
    setGoals origGoals; return true
  if ← tryEval (← `(tactic| (dsimp only [C99.Proof.evalArithRaw]; rfl))) then
    setGoals origGoals; return true
  -- 2. Concrete type/layout/modset evaluation + decide / undef inequality
  if ← tryEval (← `(tactic|
    ((try simp only [C99.CTy.unqual, C99.CTy.decay, C99.CTy.isVoid, C99.CTy.isPtr, C99.CTy.isConst,
        C99.CTy.intKind?, C99.ModSet.conflicts, C99.fieldLayout?, List.lookup,
        C99.Sem.unwindReturn, C99.Sem.Cont.topRetTy,
        C99.IntKind.signed, C99.IntKind.bits, C99.IntKind.bytes, C99.IntKind.align,
        C99.Proof.fitsIn, BEq.beq, Bool.not_false, Bool.not_true, Bool.and_true, Bool.true_and,
        Bool.or_false, Bool.false_or, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        decide_eq_true_eq, Option.some.injEq, List.mem_cons, List.not_mem_nil, List.any_nil,
        C99.Proof.AutoBlockSet.mem_singleton, C99.Proof.AutoBlockSet.mem_insert,
        C99.Proof.AutoBlockSet.mem_empty, C99.Proof.AutoBlockSet.mem_union, C99.Proof.AutoBlockSet.mem_ofList]);
     first | rfl | decide | (intro _h; rcases _h with _h | _h <;> (cases _h; done))))) then
    setGoals origGoals; return true
  let curTgt ← mvarId.withContext do instantiateMVars (← mvarId.getType)
  let hasUndef := (curTgt.find? (·.isConstOf ``C99.Val.undef)).isSome
  if hasUndef then
    if ← tryEval (← `(tactic| first | exact C99.Proof.not_IntRange_undef _ _ _ | exact C99.Proof.not_AnyInt_undef _)) then
      setGoals origGoals; return true
  -- 3. Truthiness goals (`isTruthy v = some true`/`false`)
  let hasTruthy := (curTgt.find? (·.isConstOf ``C99.Sem.isTruthy)).isSome
  if hasTruthy then
    let s3 ← saveState
    let b3Ok ← (do
      try
        evalTactic (← `(tactic|
          ((try simp only [C99.Proof.isTruthy_bool_int, C99.Proof.isTruthy_ptr_auto,
              C99.Proof.isTruthy_null_auto, C99.Proof.isTruthy_fnPtr_auto]);
           (try simp only [C99.Proof.isTruthy_u8, C99.Proof.isTruthy_i8,
              C99.Proof.isTruthy_u16, C99.Proof.isTruthy_i16, C99.Proof.isTruthy_u32,
              C99.Proof.isTruthy_i32, C99.Proof.isTruthy_u64, C99.Proof.isTruthy_i64,
              C99.Proof.isTruthy_int_iff]);
           (try simp only [Option.some.injEq, C99.Sem.cmpOrd,
              C99.Proof.intToInt_ofInt_zero, C99.Proof.intToInt_ofInt_zero_u8, C99.Proof.intToInt_ofInt_zero_i8,
              C99.Proof.intToInt_ofInt_zero_u16, C99.Proof.intToInt_ofInt_zero_i16, C99.Proof.intToInt_ofInt_zero_u32,
              C99.Proof.intToInt_ofInt_zero_i32, C99.Proof.intToInt_ofInt_zero_u64, C99.Proof.intToInt_ofInt_zero_i64,
              C99.Proof.evalArithRaw, C99.Proof.incDecDelta, Bool.not_false, Bool.false_eq_true, ↓reduceIte]);
           (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not, eq_self]))))
        if !(← getGoals).isEmpty then
          unfoldBlockIdAndArithInGoal
          evalTactic (← `(tactic| (first | rfl | decide | omega)))
        pure (← getGoals).isEmpty
      catch _ =>
        restoreState s3
        pure false)
    if b3Ok then
      setGoals origGoals; return true
    restoreState s3
  -- 3b. Single-premise arrow (`true = true → lo ≤ ... ≤ hi` or `false = true → ...`)
  let isArrow1 := curTgt.isForall
  if isArrow1 then
    if ← tryEval (← `(tactic| (intro _h; (try dsimp only [C99.Proof.incDecDelta]); first | (cases _h; done) | omega))) then
      setGoals origGoals; return true
  -- 4. Div/mod guard or `fieldLayout? → ModSet.conflicts` or `hok : ∀ oldBv, P _ → ...`
  let isArrow2 := match curTgt with
    | .forallE _ _ b _ => b.isForall
    | _ => false
  if isArrow2 then
    let s4 ← saveState
    let b4Ok ← (do
      try
        evalTactic (← `(tactic|
          (intro _a _b;
           (try dsimp only);
           (try dsimp only [C99.Proof.evalArithRaw, C99.Proof.incDecDelta]);
           (try dsimp only at _b);
           (first
             | (rcases _a with _a | _a <;> cases _a; done)
             | ((try simp only [C99.ModSet.conflicts, List.any_nil]); all_goals (first | rfl | decide); done)
             | (simp only [C99.fieldLayout?, List.lookup, BEq.beq, Bool.false_eq_true, ↓reduceIte] at _b;
                cases _b;
                (try simp only [C99.ModSet.conflicts, C99.sizeofTy, C99.sizeofAux, C99.IntKind.bytes,
                  C99.Proof.int64_ofInt_toInt, Int64.toInt_zero, Int.toNat_zero, Int.add_zero, Int.zero_add,
                  List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_false_iff, Bool.not_eq_true',
                  beq_iff_eq, decide_eq_true_eq]);
                all_goals (first | rfl | decide | omega))
             | (try (first
                 | (rcases _b with ⟨_bv, _heq, _hlo, _hhi⟩; cases _heq)
                 | (rcases _b with ⟨_bv, _heq⟩; cases _heq)
                 | cases _b));
               (try simp only [eq_self, Bool.false_eq_true, true_implies, false_implies]);
               omega))))
        pure (← getGoals).isEmpty
      catch _ =>
        restoreState s4
        pure false)
    if b4Ok then
      setGoals origGoals; return true
    restoreState s4
  -- 5. Numeric / pointer / block inequality bounds via `injectNextBlockBounds` + `omega`
  let (isForallTgt, tgtHead?) ← mvarId.withContext do
    let tRaw ← mvarId.getType
    let tW ← whnfR tRaw
    pure (tRaw.isForall, tW.getAppFn.constName?)
  let runBranch5 := !isForallTgt && tgtHead? != some ``And && tgtHead? != some ``Exists &&
    tgtHead? != some ``C99.Proof.WPTerm && tgtHead? != some ``C99.Proof.Slot &&
    tgtHead? != some ``C99.Proof.Field && tgtHead? != some ``C99.Proof.FrameBlocks
  let closed5 ← (if !runBranch5 then pure false else do
    if ← mvarId.withContext (isTriviallyFalseGoal (← mvarId.getType)) then
      pure false
    else
    let s5 ← saveState
    try
      injectNextBlockBounds
      unfoldBlockIdAndArithInGoal
      evalTactic (← `(tactic|
        ((try simp only [C99.CTy.unqual, C99.CTy.intKind?, C99.ModSet.conflicts, C99.fieldLayout?,
            List.lookup, C99.sizeofTy, C99.sizeofAux, C99.alignofTy, C99.alignofAux,
            C99.Proof.sizeofTy_int, C99.Proof.alignofTy_int, C99.Proof.sizeofTy_ptr, C99.Proof.alignofTy_ptr,
            C99.Proof.alignUp_zero, C99.alignUp, Nat.max_def,
            C99.Proof.scalarSizeAlign, C99.Proof.evalArithRaw, C99.Proof.incDecDelta,
            C99.IntKind.signed, C99.IntKind.bits, C99.IntKind.bytes, C99.IntKind.align,
            Int64.toInt_zero, Int.toNat_zero, Nat.add_zero, Int.add_zero, Int.zero_add,
            Int.zero_mul, Int.mul_zero, List.any_cons, List.any_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or, C99.Proof.AutoBlockSet.mem_singleton,
            C99.Proof.AutoBlockSet.mem_insert, C99.Proof.AutoBlockSet.mem_union, C99.Proof.AutoBlockSet.mem_ofList,
            Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_true', beq_iff_eq,
            decide_eq_true_eq, ne_eq]);
         (try repeat' apply And.intro);
         all_goals (first | rfl | decide | omega | (left; omega) | (right; omega)))))
      return (← getGoals).isEmpty
    catch _ =>
      restoreState s5
      return false)
  if closed5 then
    setGoals origGoals; return true
  -- 6. Try `fitsIn_bounds (by decide) _` for promotion bounds on abstract BitVecs
  if (curTgt.find? (·.isConstOf ``LE.le)).isSome then
    if ← tryEval (← `(tactic| exact C99.Proof.fitsIn_bounds (by decide) _)) then
      setGoals origGoals; return true
    if ← tryEval (← `(tactic| exact C99.Proof.intToInt_bounds _ _)) then
      setGoals origGoals; return true
  restoreState s
  return false

private def applyWPLemma (thm : Name) (introCont : Bool := true) (terminalGoal : Bool := false)
    (hintFVar? : Option Expr := none) : TacticM Bool := do
  let s ← saveState
  try
    let g ← getMainGoal
    let c ← g.withContext do mkConstFresh thm
    let subgoals ← g.apply c
    let mut contGoals : List MVarId := []
    let mut sideGoals : List MVarId := []
    for m in subgoals do
      let isCont ← m.withContext do
        forallTelescopeReducing (← m.getType) fun _ body => pure (isWPTermTarget body)
      if isCont then
        contGoals := contGoals ++ [m]
      else
        sideGoals := sideGoals ++ [m]
    if let some hfv := hintFVar? then
      let mut matched := false
      for sg in sideGoals do
        let isFld ← sg.withContext do
          let st ← whnfR (← sg.getType)
          pure (st.getAppFn.constName? == some ``C99.Proof.Field)
        if isFld then
          let ok ← sg.withContext do
            if ← isDefEq (← inferType hfv) (← sg.getType) then
              sg.assign hfv
              pure true
            else pure false
          if ok then
            matched := true
            break
      if !matched then
        restoreState s
        return false
    -- When `terminalGoal = true` and `contGoals` is empty, the final side goal is the postcondition `Q`.
    let mut postGoals : List MVarId := []
    if terminalGoal && contGoals.isEmpty then
      if let some lastSg := sideGoals.getLast? then
        postGoals := [lastSg]
        sideGoals := sideGoals.dropLast
    -- Two-pass side-goal discharge so metavars unified later allow earlier side goals to close
    let mut rem : List MVarId := sideGoals
    for _ in [0, 1] do
      let mut nextRem : List MVarId := []
      for sg in rem do
        if !(← closeSideGoal sg) then
          nextRem := nextRem ++ [sg]
      rem := nextRem
    let mut anyUnassigned := false
    for sg in rem do
      if !(← sg.isAssigned) then
        anyUnassigned := true
    if anyUnassigned then
      restoreState s
      return false
    let mut finalConts : List MVarId := []
    for cg in contGoals do
      if !(← cg.isAssigned) then
        let mut cur := cg
        if introCont then
          for _ in List.range 16 do
            let ty ← cur.withContext do whnfR (← cur.getType)
            if ty.isForall then
              let (_, cur') ← cur.intro1P
              cur := cur'
            else
              break
        setGoals [cur]
        try
          evalTactic (← `(tactic| dsimp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]))
        catch _ => pure ()
        finalConts := finalConts ++ (← getGoals)
    for pg in postGoals do
      if !(← pg.isAssigned) then
        setGoals [pg]
        try evalTactic (← `(tactic| simp only [C99.Proof.freeStack_nil_auto])) catch _ => pure ()
        let curPgs ← getGoals
        if !(← tryEval (← `(tactic| first | assumption | rfl))) then
          finalConts := finalConts ++ curPgs
    setGoals finalConts
    return true
  catch _ =>
    restoreState s
    return false

private def tryApplyList (thms : List Name) (introCont : Bool := true) (terminalGoal : Bool := false) : TacticM Bool := do
  for thm in thms do
    if ← applyWPLemma thm introCont terminalGoal then
      return true
  return false

private def tryApplyFieldList (thms : List Name) (mGoal blkGoal : Expr) : TacticM Bool := do
  let g ← getMainGoal
  let cands ← g.withContext do
    let lctx ← getLCtx
    let mut out : Array Expr := #[]
    for ld in lctx do
      if !ld.isImplementationDetail then
        let ty ← whnfR ld.type
        if ty.getAppFn.constName? == some ``C99.Proof.Field && ty.getAppArgs.size == 8 then
          if let (some hm, some hb) := (ty.getAppArgs[1]?, ty.getAppArgs[2]?) then
            if (← withReducible (isDefEq hm mGoal)) && (← withReducible (isDefEq hb blkGoal)) then
              out := out.push ld.toExpr
    return out
  if cands.isEmpty then
    return false
  for thm in thms do
    for hfv in cands do
      if ← applyWPLemma thm true false (some hfv) then
        return true
  return false

private def tryDeriveHyp (thm : Name) (args : Array Expr) (nameHint : Name)
    (reducibleDup : Bool := true) : TacticM Bool := do
  let s ← saveState
  try
    let g ← getMainGoal
    let (prf, mvars, ty) ← g.withContext do
      let c ← mkConstFresh thm
      let cTy ← whnfR (← inferType c)
      let (allMvs, bis, resTy) ← forallMetaTelescopeReducing cTy
      let mut argIdx := 0
      for i in [:allMvs.size] do
        if let some bi := bis[i]? then
          if bi == .default then
            if hlt : argIdx < args.size then
              let mv := allMvs[i]!
              let arg := args[argIdx]
              if !(← isDefEq (← inferType mv) (← inferType arg)) then
                throwError "tryDeriveHyp arg type mismatch"
              if !(← isDefEq mv arg) then
                throwError "tryDeriveHyp arg unify mismatch"
              argIdx := argIdx + 1
      if argIdx < args.size then
        throwError "tryDeriveHyp too many args"
      let prf := mkAppN c allMvs
      pure (prf, allMvs.toList, ← instantiateMVars resTy)
    let dup1 ← g.withContext (if reducibleDup then existsHypOfTypeReducible ty else existsHypOfType ty)
    if dup1 then
      restoreState s
      return false
    let mut rem := mvars.map (·.mvarId!)
    for _ in [0, 1] do
      let mut nextRem : List MVarId := []
      for mvid in rem do
        if !(← mvid.isAssigned) then
          if !(← closeSideGoal mvid) then
            nextRem := nextRem ++ [mvid]
      rem := nextRem
    let mut anyUnassigned := false
    for mvid in rem do
      if !(← mvid.isAssigned) then
        anyUnassigned := true
    if anyUnassigned then
      restoreState s
      return false
    let tyFin ← g.withContext do instantiateMVars ty
    let dup2 ← g.withContext (if reducibleDup then existsHypOfTypeReducible tyFin else existsHypOfType tyFin)
    if dup2 then
      restoreState s
      return false
    let prfFin ← g.withContext do instantiateMVars prf
    let (_, g') ← g.note nameHint prfFin
    replaceMainGoal [g']
    return true
  catch _ =>
    restoreState s
    return false

private def hypMem? (hty : Expr) : Option Expr :=
  let hfn := hty.getAppFn.constName?
  let args := hty.getAppArgs
  if hfn == some ``C99.Proof.Slot then args[1]?
  else if hfn == some ``C99.Proof.Field then args[1]?
  else if hfn == some ``C99.Proof.PtrValid || hfn == some ``C99.Proof.PtrWritable then args[0]?
  else if hfn == some ``Eq then
    match args[1]? with
    | some lhs =>
      if lhs.getAppFn.constName? == some ``C99.Mem.blocks then lhs.getAppArgs[0]?
      else none
    | none => none
  else none

private def sameMemReducible (e1 e2 : Expr) : MetaM Bool := do
  if e1 == e2 then return true
  if e1.isFVar && e2.isFVar then
    let d1 ← e1.fvarId!.getDecl
    let d2 ← e2.fvarId!.getDecl
    if !d1.isLet && !d2.isLet then
      return false
  if let (.lit l1, .lit l2) := (e1, e2) then
    return l1 == l2
  withReducible (isDefEq e1 e2)

private def transDestMem? (tty : Expr) : MetaM (Option Expr) := do
  let tfn := tty.getAppFn.constName?
  let targs := tty.getAppArgs
  if tfn == some ``C99.Proof.ROExt || tfn == some ``C99.Proof.FrameBlocks then
    return targs[1]?
  if tfn == some ``Eq then
    if let (some lhs, some rhs) := (targs[1]?, targs[2]?) then
      let lfn := lhs.getAppFn.constName?
      if lfn == some ``C99.Sem.writeVal || lfn == some ``C99.Mem.writeBytes then
        let rw ← whnfR rhs
        if rw.getAppFn.constName? == some ``Option.some then
          return rw.getAppArgs[1]?
      else if lfn == some ``C99.Sem.writePlace then
        let rw ← whnfR rhs
        if rw.getAppFn.constName? == some ``Option.some then
          if let some pr := rw.getAppArgs[1]? then
            let pw ← whnfR pr
            if pw.getAppFn.constName? == some ``Prod.mk then
              return pw.getAppArgs[3]?
      else if lfn == some ``C99.Mem.alloc then
        let rw ← whnfR rhs
        if rw.getAppFn.constName? == some ``Prod.mk then
          return rw.getAppArgs[3]?
  return none

private def alreadyAtDest (fvars : List (Expr × Expr)) (mDest : Expr) (hty : Expr) : MetaM Bool := do
  let hfn := hty.getAppFn.constName?
  let hargs := hty.getAppArgs
  for (_, cty) in fvars do
    if cty.getAppFn.constName? != hfn then continue
    let cargs := cty.getAppArgs
    if hfn == some ``C99.Proof.Slot then
      if let (some he, some hn, some hb, some cm, some ce, some cn, some cb) :=
          (hargs[0]?, hargs[2]?, hargs[3]?, cargs[1]?, cargs[0]?, cargs[2]?, cargs[3]?) then
        if (← sameMemReducible cm mDest) && (← sameMemReducible hb cb) &&
           (← sameMemReducible hn cn) && (← sameMemReducible he ce) then
          return true
    else if hfn == some ``C99.Proof.Field then
      if let (some hb, some hf, some cm, some cb, some cf) :=
          (hargs[2]?, hargs[5]?, cargs[1]?, cargs[2]?, cargs[5]?) then
        if (← sameMemReducible cm mDest) && (← sameMemReducible hb cb) &&
           (← sameMemReducible hf cf) then
          return true
    else if hfn == some ``Eq then
      if let (some hLhs, some cLhs) := (hargs[1]?, cargs[1]?) then
        if hLhs.getAppFn.constName? == some ``C99.Mem.blocks &&
           cLhs.getAppFn.constName? == some ``C99.Mem.blocks then
          if let (some hb, some cm, some cb) := (hLhs.getAppArgs[1]?, cLhs.getAppArgs[0]?, cLhs.getAppArgs[1]?) then
            if (← sameMemReducible cm mDest) && (← sameMemReducible hb cb) then
              return true
  return false

/-- Automatically transports `Slot`, `Field`, `m.blocks`, `PtrValid`, `PtrWritable`, and
`LocalFrameMem` hypotheses across `writeVal`, `writeBytes`, `writePlace`, `alloc`, `ROExt`,
`FrameBlocks`, `freeStack`, and `(x, b, ty) :: env` transitions. -/
def runCFrame : TacticM Unit := do
  for _ in List.range 8 do
    let mut progress := false
    let g ← getMainGoal
    let wpInfo? ← g.withContext do extractWPRunning (← g.getType)
    let fvars ← g.withContext do
      let lctx ← getLCtx
      let mut out : List (Expr × Expr) := []
      for ld in lctx do
        if !ld.isImplementationDetail then
          let ty0 ← whnfR ld.type
          let ty1 ← if ty0.getAppFn.constName? == some ``C99.Proof.Slot.uninit then whnf ty0 else pure ty0
          out := out ++ [(ld.toExpr, ty1)]
      return out
    -- Rule A: transport across transition hypotheses in context
    for (tfv, tty) in fvars do
      let tfn := tty.getAppFn.constName?
      let targs := tty.getAppArgs
      let mDest? ← (← getMainGoal).withContext (transDestMem? tty)
      if tfn == some ``Eq then
        if let some lhs := targs[1]? then
          let lfn := lhs.getAppFn.constName?
          let largs := lhs.getAppArgs
          let mSrc? : Option Expr :=
            if lfn == some ``C99.Sem.writeVal then largs[0]?
            else if lfn == some ``C99.Mem.writeBytes then largs[0]?
            else if lfn == some ``C99.Sem.writePlace then largs[1]?
            else if lfn == some ``C99.Mem.alloc then largs[0]?
            else none
          let blkW? : Option Expr :=
            if lfn == some ``C99.Sem.writeVal || lfn == some ``C99.Mem.writeBytes then largs[1]?
            else if lfn == some ``C99.Sem.writePlace then largs[2]?
            else none
          if let some mSrc := mSrc? then
            for (hfv, hty) in fvars do
              let matchMem ← match hypMem? hty with
                | some hm => (← getMainGoal).withContext (sameMemReducible hm mSrc)
                | none => pure false
              if !matchMem then continue
              if let some md := mDest? then
                if ← (← getMainGoal).withContext (alreadyAtDest fvars md hty) then continue
              let hfn := hty.getAppFn.constName?
              if hfn == some ``C99.Proof.Slot then
                let sameBlk ← match hty.getAppArgs[3]?, blkW? with
                  | some hb, some bw => (← getMainGoal).withContext (sameMemReducible hb bw)
                  | _, _ => pure false
                if sameBlk then continue
                let thm :=
                  if lfn == some ``C99.Sem.writeVal then ``C99.Proof.Slot.preserve_writeVal
                  else if lfn == some ``C99.Mem.writeBytes then ``C99.Proof.Slot.preserve_writeBytes
                  else if lfn == some ``C99.Sem.writePlace then ``C99.Proof.Slot.preserve_writePlace
                  else ``C99.Proof.Slot.preserve_alloc
                if ← tryDeriveHyp thm #[hfv, tfv] `hs_fr then progress := true
              else if hfn == some ``C99.Proof.Field then
                if lfn == some ``C99.Mem.alloc then
                  if ← tryDeriveHyp ``C99.Proof.Field.preserve_alloc #[hfv, tfv] `hf_fr then progress := true
                else
                  let sameBlk ← match hty.getAppArgs[2]?, blkW? with
                    | some hb, some bw => (← getMainGoal).withContext (sameMemReducible hb bw)
                    | _, _ => pure false
                  let neOk ← if sameBlk then pure false else do
                    let thmNe :=
                      if lfn == some ``C99.Sem.writeVal then ``C99.Proof.Field.preserve_writeVal_ne
                      else if lfn == some ``C99.Mem.writeBytes then ``C99.Proof.Field.preserve_writeBytes_ne
                      else ``C99.Proof.Field.preserve_writePlace_ne
                    tryDeriveHyp thmNe #[hfv, tfv] `hf_fr
                  if neOk then
                    progress := true
                  else if sameBlk && (lfn == some ``C99.Sem.writeVal || lfn == some ``C99.Sem.writePlace) then
                    for (wfv, wty) in fvars do
                      if wty.getAppFn.constName? == some ``C99.Proof.Field then
                        if let (some wm, some wb, some wfld) := (wty.getAppArgs[1]?, wty.getAppArgs[2]?, wty.getAppArgs[5]?) then
                          let wmOk ← (← getMainGoal).withContext (sameMemReducible wm mSrc)
                          let wbOk ← match blkW? with
                            | some bw => (← getMainGoal).withContext (sameMemReducible wb bw)
                            | none => pure true
                          let diffFld ← match hty.getAppArgs[5]? with
                            | some hfld => pure !(← (← getMainGoal).withContext (sameMemReducible hfld wfld))
                            | none => pure true
                          if wmOk && wbOk && diffFld then
                            let thmDisj :=
                              if lfn == some ``C99.Sem.writeVal then ``C99.Proof.Field.preserve_writeVal_disjoint_fld
                              else ``C99.Proof.Field.preserve_writePlace_disjoint_fld
                            if ← tryDeriveHyp thmDisj #[hfv, wfv, tfv] `hf_disj then
                              progress := true
                              break
              else if hfn == some ``Eq then
                if let some hLhs := hty.getAppArgs[1]? then
                  if hLhs.getAppFn.constName? == some ``C99.Mem.blocks then
                    let thm :=
                      if lfn == some ``C99.Sem.writeVal then ``C99.Proof.blocks_preserve_writeVal
                      else if lfn == some ``C99.Mem.writeBytes then ``C99.Proof.blocks_preserve_writeBytes
                      else if lfn == some ``C99.Sem.writePlace then ``C99.Proof.blocks_preserve_writePlace
                      else ``C99.Proof.blocks_preserve_alloc
                    if ← tryDeriveHyp thm #[tfv, hfv] `hb_fr then progress := true
              else if hfn == some ``C99.Proof.PtrValid then
                let thm :=
                  if lfn == some ``C99.Sem.writeVal then ``C99.Proof.PtrValid.preserve_writeVal
                  else if lfn == some ``C99.Mem.writeBytes then ``C99.Proof.PtrValid.preserve_writeBytes
                  else if lfn == some ``C99.Sem.writePlace then ``C99.Proof.PtrValid.preserve_writePlace
                  else ``C99.Proof.PtrValid.preserve_alloc
                if ← tryDeriveHyp thm #[hfv, tfv] `hpv_fr then progress := true
              else if hfn == some ``C99.Proof.PtrWritable then
                if lfn == some ``C99.Sem.writeVal then
                  if ← tryDeriveHyp ``C99.Proof.PtrWritable.preserve_writeVal #[hfv, tfv] `hpw_fr then progress := true
                else if lfn == some ``C99.Mem.writeBytes then
                  if ← tryDeriveHyp ``C99.Proof.PtrWritable.preserve_writeBytes #[hfv, tfv] `hpw_fr then progress := true
                else if lfn == some ``C99.Sem.writePlace then
                  if ← tryDeriveHyp ``C99.Proof.PtrWritable.preserve_writePlace #[hfv, tfv] `hpw_fr then progress := true
                else
                  if ← tryDeriveHyp ``C99.Proof.PtrWritable.preserve_alloc #[hfv, tfv] `hpw_fr then progress := true
      else if tfn == some ``C99.Proof.ROExt then
        if let some mSrc := targs[0]? then
          for (hfv, hty) in fvars do
            let matchMem ← match hypMem? hty with
              | some hm => (← getMainGoal).withContext (sameMemReducible hm mSrc)
              | none => pure false
            if !matchMem then continue
            if let some md := mDest? then
              if ← (← getMainGoal).withContext (alreadyAtDest fvars md hty) then continue
            let hfn := hty.getAppFn.constName?
            if hfn == some ``C99.Proof.Slot then
              if ← tryDeriveHyp ``C99.Proof.Slot.preserve_roExt #[hfv, tfv] `hs_ro then progress := true
            else if hfn == some ``C99.Proof.Field then
              if ← tryDeriveHyp ``C99.Proof.Field.preserve_roExt #[hfv, tfv] `hf_ro then progress := true
            else if hfn == some ``Eq then
              if let some hLhs := hty.getAppArgs[1]? then
                if hLhs.getAppFn.constName? == some ``C99.Mem.blocks then
                  if ← tryDeriveHyp ``C99.Proof.blocks_preserve_roExt #[tfv, hfv] `hb_ro then progress := true
            else if hfn == some ``C99.Proof.PtrValid then
              if ← tryDeriveHyp ``C99.Proof.PtrValid.preserve_roExt #[hfv, tfv] `hpv_ro then progress := true
            else if hfn == some ``C99.Proof.PtrWritable then
              if ← tryDeriveHyp ``C99.Proof.PtrWritable.preserve_roExt #[hfv, tfv] `hpw_ro then progress := true
      else if tfn == some ``C99.Proof.FrameBlocks then
        if let (some mSrc, some allowed) := (targs[0]?, targs[2]?) then
          for (hfv, hty) in fvars do
            let matchMem ← match hypMem? hty with
              | some hm => (← getMainGoal).withContext (sameMemReducible hm mSrc)
              | none => pure false
            if !matchMem then continue
            if let some md := mDest? then
              if ← (← getMainGoal).withContext (alreadyAtDest fvars md hty) then continue
            let hfn := hty.getAppFn.constName?
            let hb? : Option Expr :=
              if hfn == some ``C99.Proof.Slot then hty.getAppArgs[3]?
              else if hfn == some ``C99.Proof.Field then hty.getAppArgs[2]?
              else if hfn == some ``Eq then hty.getAppArgs[1]?.bind fun l => l.getAppArgs[1]?
              else none
            let inAllowed ← match hb? with
              | some hb => (← getMainGoal).withContext (listMemReducible hb allowed)
              | none => pure false
            if inAllowed then continue
            if hfn == some ``C99.Proof.Slot then
              if ← (do
                if ← tryDeriveHyp ``C99.Proof.Slot.preserve_frameBlocks #[hfv, tfv] `hs_fr then return true
                tryDeriveHyp ``C99.Proof.Slot.preserve_frameBlocks_next #[hfv, tfv] `hs_fr) then progress := true
            else if hfn == some ``C99.Proof.Field then
              if ← (do
                if ← tryDeriveHyp ``C99.Proof.Field.preserve_frameBlocks #[hfv, tfv] `hf_fr then return true
                tryDeriveHyp ``C99.Proof.Field.preserve_frameBlocks_next #[hfv, tfv] `hf_fr) then progress := true
            else if hfn == some ``Eq then
              if let some hLhs := hty.getAppArgs[1]? then
                if hLhs.getAppFn.constName? == some ``C99.Mem.blocks then
                  if ← (do
                    if ← tryDeriveHyp ``C99.Proof.blocks_preserve_frameBlocks #[tfv, hfv] `hb_fr then return true
                    tryDeriveHyp ``C99.Proof.blocks_preserve_frameBlocks_next #[tfv, hfv] `hb_fr) then progress := true
            else if hfn == some ``C99.Proof.PtrValid then
              if ← tryDeriveHyp ``C99.Proof.PtrValid.preserve_frameBlocks #[hfv, tfv] `hpv_fr then progress := true
            else if hfn == some ``C99.Proof.PtrWritable then
              if ← tryDeriveHyp ``C99.Proof.PtrWritable.preserve_frameBlocks #[hfv, tfv] `hpw_fr then progress := true
    -- Rule B & C: transport into goal's `freeStack` and pushed `env`
    let freeStackBlks? ← (← getMainGoal).withContext do
      if let some (_, _, _, _, _, _, _, mTgt, _, _) := wpInfo? then
        let mTgtW ← whnfR mTgt
        if mTgtW.getAppFn.constName? == some ``C99.Mem.freeStack then
          if let (some m0, some b0) := (mTgtW.getAppArgs[0]?, mTgtW.getAppArgs[1]?) then
            return some (m0, b0)
      let tgt ← instantiateMVars (← (← getMainGoal).getType)
      let found? := tgt.find? fun sub =>
        sub.getAppFn.constName? == some ``C99.Mem.freeStack && sub.getAppArgs.size == 2
      return found?.bind fun sub =>
        match sub.getAppArgs[0]?, sub.getAppArgs[1]? with
        | some m0, some b0 => some (m0, b0)
        | _, _ => none
    if let some (fsMem, blksArg) := freeStackBlks? then
      for (hfv, hty) in fvars do
        let matchMem ← match hypMem? hty with
          | some hm => (← getMainGoal).withContext (sameMemReducible hm fsMem)
          | none => pure false
        if !matchMem then continue
        let hfn := hty.getAppFn.constName?
        if hfn == some ``C99.Proof.Slot then
          if ← tryDeriveHyp ``C99.Proof.slot_freeStack_at #[hfv, blksArg] `hs_fs then
            progress := true
        else if hfn == some ``C99.Proof.Field then
          if ← tryDeriveHyp ``C99.Proof.field_freeStack_at #[hfv, blksArg] `hf_fs then
            progress := true
        else if hfn == some ``Eq then
          if let some hLhs := hty.getAppArgs[1]? then
            if hLhs.getAppFn.constName? == some ``C99.Mem.blocks then
              if ← tryDeriveHyp ``C99.Proof.blocks_freeStack_at #[hfv, blksArg] `hb_fs then
                progress := true
        else if hfn == some ``C99.Proof.PtrValid then
          if ← tryDeriveHyp ``C99.Proof.ptrValid_freeStack_at #[hfv, blksArg] `hpv_fs then
            progress := true
        else if hfn == some ``C99.Proof.PtrWritable then
          if ← tryDeriveHyp ``C99.Proof.ptrWritable_freeStack_at #[hfv, blksArg] `hpw_fs then
            progress := true
    if let some (_, _, _, _, _, envTgt, _, mTgt, _, _) := wpInfo? then
      let envTgtW ← (← getMainGoal).withContext do whnf envTgt
      if envTgtW.getAppFn.constName? == some ``List.cons then
        if let (some hdRaw, some envRest) := (envTgtW.getAppArgs[1]?, envTgtW.getAppArgs[2]?) then
          let hdW ← (← getMainGoal).withContext do whnf hdRaw
          if hdW.getAppFn.constName? == some ``Prod.mk then
            if let (some dname, some sndRaw) := (hdW.getAppArgs[2]?, hdW.getAppArgs[3]?) then
              let sndW ← (← getMainGoal).withContext do whnf sndRaw
              if sndW.getAppFn.constName? == some ``Prod.mk then
                if let (some db, some dty) := (sndW.getAppArgs[2]?, sndW.getAppArgs[3]?) then
                  for (hfv, hty) in fvars do
                    if hty.getAppFn.constName? == some ``C99.Proof.Slot then
                      if let (some hEnv, some hm) := (hty.getAppArgs[0]?, hty.getAppArgs[1]?) then
                        if ← (← getMainGoal).withContext (sameMemReducible hm mTgt) then
                          if ← (← getMainGoal).withContext (isDefEq hEnv envRest) then
                            if ← tryDeriveHyp ``C99.Proof.slot_env_cons_at #[hfv, dname, db, dty] `hs_env false then
                              progress := true
    if !progress then
      break

/-- Advances a single pure expression evaluation step inside `WPTerm` (`c_eval` inner step). -/
def runCEvalStep : TacticM Bool := do
  let g ← getMainGoal
  let some (_, _, _, _, ctrl, _, _, _, _, _) ← g.withContext do extractWPRunning (← g.getType)
    | return false
  let ctrlW ← g.withContext do whnf ctrl
  if ctrlW.getAppFn.constName? != some ``C99.Sem.Control.expr then
    return false
  let some esRaw := ctrlW.getAppArgs[0]? | return false
  let es ← g.withContext do whnf esRaw
  let esFn := es.getAppFn.constName?
  let esArgs := es.getAppArgs
  if esFn == some ``C99.Sem.ExprState.eval && esArgs.size == 3 then
    let (some wRaw, some eRaw) := (esArgs[0]?, esArgs[1]?) | return false
    let want ← g.withContext do whnf wRaw
    let e ← g.withContext do whnf eRaw
    let isRval := want.getAppFn.constName? == some ``C99.Sem.Want.rval
    let eFn := e.getAppFn.constName?
    if eFn == some ``C99.CExpr.paren then return ← applyWPLemma ``C99.Proof.wp_paren
    if eFn == some ``C99.CExpr.lit && isRval then return ← applyWPLemma ``C99.Proof.wp_lit
    if eFn == some ``C99.CExpr.sizeOfTy && isRval then return ← applyWPLemma ``C99.Proof.wp_sizeOfTy
    if eFn == some ``C99.CExpr.var then
      if isRval then
        return ← tryApplyList [``C99.Proof.wp_var_slot_eq, ``C99.Proof.wp_var_slot_intRange,
          ``C99.Proof.wp_var_slot_anyInt, ``C99.Proof.wp_var_enum, ``C99.Proof.wp_var_fnProto]
      else
        return ← tryApplyList [``C99.Proof.wp_var_lval_slot, ``C99.Proof.wp_var_lval]
    if eFn == some ``C99.CExpr.cast then return ← applyWPLemma ``C99.Proof.wp_cast
    if eFn == some ``C99.CExpr.unary then return ← applyWPLemma ``C99.Proof.wp_unary
    if eFn == some ``C99.CExpr.binary then return ← applyWPLemma ``C99.Proof.wp_binary
    if eFn == some ``C99.CExpr.addrOf then return ← applyWPLemma ``C99.Proof.wp_addrOf
    if eFn == some ``C99.CExpr.deref then return ← applyWPLemma ``C99.Proof.wp_deref
    if eFn == some ``C99.CExpr.index then return ← applyWPLemma ``C99.Proof.wp_index
    if eFn == some ``C99.CExpr.member then return ← applyWPLemma ``C99.Proof.wp_member
    if eFn == some ``C99.CExpr.arrow then return ← applyWPLemma ``C99.Proof.wp_arrow
    if eFn == some ``C99.CExpr.cond then return ← applyWPLemma ``C99.Proof.wp_cond
    if eFn == some ``C99.CExpr.logAnd then return ← applyWPLemma ``C99.Proof.wp_logAnd
    if eFn == some ``C99.CExpr.logOr then return ← applyWPLemma ``C99.Proof.wp_logOr
    if eFn == some ``C99.CExpr.comma then return ← applyWPLemma ``C99.Proof.wp_comma
    return false
  else if esFn == some ``C99.Sem.ExprState.ret && esArgs.size == 2 then
    let some fsRaw := esArgs[1]? | return false
    let fs ← g.withContext do whnf fsRaw
    if fs.getAppFn.constName? != some ``List.cons then
      return false
    let some fRaw := fs.getAppArgs[1]? | return false
    let f ← g.withContext do whnf fRaw
    let fFn := f.getAppFn.constName?
    if fFn == some ``C99.Sem.ExprFrame.binLhsF then return ← applyWPLemma ``C99.Proof.wp_binLhs
    if fFn == some ``C99.Sem.ExprFrame.indexBaseF then return ← applyWPLemma ``C99.Proof.wp_indexBase
    if fFn == some ``C99.Sem.ExprFrame.commaF then return ← applyWPLemma ``C99.Proof.wp_comma_ret
    if fFn == some ``C99.Sem.ExprFrame.addrOfF then return ← applyWPLemma ``C99.Proof.wp_addrOf_ret
    if fFn == some ``C99.Sem.ExprFrame.castF then
      return ← tryApplyList [``C99.Proof.wp_cast_int, ``C99.Proof.wp_cast_ptr_ptr,
        ``C99.Proof.wp_cast_ptr_null, ``C99.Proof.wp_cast_ptr_zero, ``C99.Proof.wp_cast_ret]
    if fFn == some ``C99.Sem.ExprFrame.unaryF then
      return ← tryApplyList [``C99.Proof.wp_unary_neg_int, ``C99.Proof.wp_unary_plus_int,
        ``C99.Proof.wp_unary_bitNot_int, ``C99.Proof.wp_unary_logNot_int,
        ``C99.Proof.wp_unary_logNot_ptr, ``C99.Proof.wp_unary_logNot_null, ``C99.Proof.wp_unary_ret]
    if fFn == some ``C99.Sem.ExprFrame.binRhsF then
      return ← tryApplyList [``C99.Proof.wp_binRhs_int_cmp_fit, ``C99.Proof.wp_binRhs_int_cmp,
        ``C99.Proof.wp_binRhs_int_arith_signed, ``C99.Proof.wp_binRhs_int_arith_unsigned,
        ``C99.Proof.wp_binRhs_int_bitwise, ``C99.Proof.wp_binRhs_int_shift_unsigned,
        ``C99.Proof.wp_binRhs_int_shift_signed, ``C99.Proof.wp_binRhs_ptrAdd,
        ``C99.Proof.wp_binRhs_ptrSub_int, ``C99.Proof.wp_binRhs_ptrCmp_eq_ptr,
        ``C99.Proof.wp_binRhs_ptrCmp_eq_null, ``C99.Proof.wp_binRhs_ptrCmp_null_eq,
        ``C99.Proof.wp_binRhs_ptrCmp_rel, ``C99.Proof.wp_binRhs_ptrDiff, ``C99.Proof.wp_binRhs_ret]
    if fFn == some ``C99.Sem.ExprFrame.derefF then
      return ← tryApplyList [``C99.Proof.wp_deref_lval, ``C99.Proof.wp_deref_rval_array,
        ``C99.Proof.wp_deref_rval_scalar, ``C99.Proof.wp_deref_rval]
    if fFn == some ``C99.Sem.ExprFrame.indexIdxF then
      return ← tryApplyList [``C99.Proof.wp_indexIdx_lval, ``C99.Proof.wp_indexIdx_rval_scalar,
        ``C99.Proof.wp_indexIdx]
    if fFn == some ``C99.Sem.ExprFrame.memberF then
      return ← tryApplyList [``C99.Proof.wp_member_lval, ``C99.Proof.wp_member_field_eq,
        ``C99.Proof.wp_member_field_intRange, ``C99.Proof.wp_member_field_anyInt]
    if fFn == some ``C99.Sem.ExprFrame.arrowF then
      return ← tryApplyList [``C99.Proof.wp_arrow_lval, ``C99.Proof.wp_arrow_field_eq,
        ``C99.Proof.wp_arrow_field_intRange, ``C99.Proof.wp_arrow_field_anyInt]
    if fFn == some ``C99.Sem.ExprFrame.condF then
      return ← applyWPLemma ``C99.Proof.wp_cond_bool
    if fFn == some ``C99.Sem.ExprFrame.logAndF then
      return ← tryApplyList [``C99.Proof.wp_logAnd_false, ``C99.Proof.wp_logAnd_true]
    if fFn == some ``C99.Sem.ExprFrame.logAndEndF then
      return ← applyWPLemma ``C99.Proof.wp_logAndEnd
    if fFn == some ``C99.Sem.ExprFrame.logOrF then
      return ← tryApplyList [``C99.Proof.wp_logOr_true, ``C99.Proof.wp_logOr_false]
    if fFn == some ``C99.Sem.ExprFrame.logOrEndF then
      return ← applyWPLemma ``C99.Proof.wp_logOrEnd
    return false
  return false

/-- Evaluates pure C subexpressions inside a `WPTerm` goal up to `128` steps. -/
def runCEval : TacticM Unit := do
  for _ in List.range 128 do
    if !(← runCEvalStep) then
      break

/-- Advances one deterministic `WPTerm` step (statement, control, declaration, assignment,
incDec, or expression step) and automatically transports framed facts via `c_frame`. -/
def runCStep : TacticM Bool := do
  let g ← getMainGoal
  let some (_, _, _, _, ctrl, _, _, mGoal, _, k) ← g.withContext do extractWPRunning (← g.getType)
    | return false
  let ctrlW ← g.withContext do whnf ctrl
  let ctrlFn := ctrlW.getAppFn.constName?
  if ctrlFn == some ``C99.Sem.Control.stmt then
    let some stRaw := ctrlW.getAppArgs[0]? | return false
    let st ← g.withContext do whnf stRaw
    let stFn := st.getAppFn.constName?
    if stFn == some ``C99.CStmt.block then
      return ← tryApplyList [``C99.Proof.wp_block_nil, ``C99.Proof.wp_block_cons]
    if stFn == some ``C99.CStmt.nop then
      let kW ← g.withContext do whnf k
      let kFn := kW.getAppFn.constName?
      if kFn == some ``C99.Sem.Cont.stmts then
        return ← tryApplyList [``C99.Proof.wp_stmts_nil, ``C99.Proof.wp_stmts_cons]
      if kFn == some ``C99.Sem.Cont.blockEnd then
        if ← applyWPLemma ``C99.Proof.wp_blockEnd then
          runCFrame
          return true
        return false
      if kFn == some ``C99.Sem.Cont.stop then
        if ← applyWPLemma ``C99.Proof.wp_nop false true then
          if !(← getGoals).isEmpty then runCFrame
          return true
        return false
      if kFn == some ``C99.Sem.Cont.switchCont then
        return ← applyWPLemma ``C99.Proof.wp_nop_switchCont
      if kFn == some ``C99.Sem.Cont.callFrame then
        if ← applyWPLemma ``C99.Proof.wp_nop_callFrame then
          runCFrame
          return true
        return false
      return false
    if stFn == some ``C99.CStmt.expr then return ← applyWPLemma ``C99.Proof.wp_expr_stmt
    if stFn == some ``C99.CStmt.decl then return ← applyWPLemma ``C99.Proof.wp_decl
    if stFn == some ``C99.CStmt.decls then
      let ok ← tryApplyList [``C99.Proof.wp_decls_nil, ``C99.Proof.wp_decls_static,
        ``C99.Proof.wp_localDecl_int_none_fresh, ``C99.Proof.wp_localDecl_ptr_none_fresh,
        ``C99.Proof.wp_localDecl_none, ``C99.Proof.wp_decls_cons_init]
      if ok then
        runCFrame
        return true
      return false
    if stFn == some ``C99.CStmt.ifStmt then return ← applyWPLemma ``C99.Proof.wp_if
    if stFn == some ``C99.CStmt.returnStmt then
      let some optRaw := st.getAppArgs[0]? | return false
      let opt ← g.withContext do whnf optRaw
      if opt.getAppFn.constName? == some ``Option.some then
        return ← applyWPLemma ``C99.Proof.wp_return_expr
      else
        if ← applyWPLemma ``C99.Proof.wp_return_void_stop false true then
          if !(← getGoals).isEmpty then runCFrame
          return true
        if ← applyWPLemma ``C99.Proof.wp_return_void false false then
          if !(← getGoals).isEmpty then runCFrame
          return true
        return false
    if stFn == some ``C99.CStmt.breakStmt then
      if ← applyWPLemma ``C99.Proof.wp_break then
        runCFrame
        return true
      return false
    if stFn == some ``C99.CStmt.continueStmt then
      if ← applyWPLemma ``C99.Proof.wp_continue then
        runCFrame
        return true
      return false
    if stFn == some ``C99.CStmt.caseStmt then return ← applyWPLemma ``C99.Proof.wp_case
    if stFn == some ``C99.CStmt.defaultStmt then return ← applyWPLemma ``C99.Proof.wp_default
    if stFn == some ``C99.CStmt.labelStmt then return ← applyWPLemma ``C99.Proof.wp_label
    return false
  else if ctrlFn == some ``C99.Sem.Control.expr then
    let (some esRaw, some ctxRaw) := (ctrlW.getAppArgs[0]?, ctrlW.getAppArgs[1]?) | return false
    let es ← g.withContext do whnf esRaw
    let ctx ← g.withContext do whnf ctxRaw
    let esFn := es.getAppFn.constName?
    let esArgs := es.getAppArgs
    if esFn == some ``C99.Sem.ExprState.ret && esArgs.size == 2 then
      let some fsRaw := esArgs[1]? | return false
      let fs ← g.withContext do whnf fsRaw
      if fs.getAppFn.constName? == some ``List.nil then
        let ctxFn := ctx.getAppFn.constName?
        if ctxFn == some ``C99.Sem.ExprCtx.discard then return ← applyWPLemma ``C99.Proof.wp_expr_discard
        if ctxFn == some ``C99.Sem.ExprCtx.returnVal then
          if ← tryApplyList [``C99.Proof.wp_return_val_stop_int_same,
              ``C99.Proof.wp_return_val_stop_int, ``C99.Proof.wp_return_val_stop_ptr,
              ``C99.Proof.wp_return_val_stop] false true then
            if !(← getGoals).isEmpty then runCFrame
            return true
          if ← tryApplyList [``C99.Proof.wp_return_val_void, ``C99.Proof.wp_return_val] false false then
            if !(← getGoals).isEmpty then runCFrame
            return true
          return false
        if ctxFn == some ``C99.Sem.ExprCtx.varInit then
          let ok ← tryApplyList [``C99.Proof.wp_localDecl_init_int_same_fresh,
            ``C99.Proof.wp_localDecl_init_int_fresh, ``C99.Proof.wp_localDecl_init_ptr_fresh]
          if ok then
            runCFrame
            return true
          return false
        if ctxFn == some ``C99.Sem.ExprCtx.branch then
          return ← tryApplyList [``C99.Proof.wp_branch_true, ``C99.Proof.wp_branch_false]
        if ctxFn == some ``C99.Sem.ExprCtx.whileCond then
          return ← tryApplyList [``C99.Proof.wp_whileCond_true, ``C99.Proof.wp_whileCond_false,
            ``C99.Proof.wp_whileCond_bool_ite]
        if ctxFn == some ``C99.Sem.ExprCtx.forCond then
          return ← tryApplyList [``C99.Proof.wp_forCond_true, ``C99.Proof.wp_forCond_false,
            ``C99.Proof.wp_forCond_bool_ite]
        if ctxFn == some ``C99.Sem.ExprCtx.doWhileCond then
          return ← tryApplyList [``C99.Proof.wp_doWhileCond_true, ``C99.Proof.wp_doWhileCond_false,
            ``C99.Proof.wp_doWhileCond_bool_ite]
        if ctxFn == some ``C99.Sem.ExprCtx.forStep then
          return ← applyWPLemma ``C99.Proof.wp_forStep
        return false
      else if fs.getAppFn.constName? == some ``List.cons then
        let some fRaw := fs.getAppArgs[1]? | return false
        let f ← g.withContext do whnf fRaw
        let fFn := f.getAppFn.constName?
        if fFn == some ``C99.Sem.ExprFrame.assignLhsF then
          return ← applyWPLemma ``C99.Proof.wp_assign_rhs
        if fFn == some ``C99.Sem.ExprFrame.assignRhsF then
          let fieldOk ← match f.getAppArgs[1]? with
            | some blkGoal => tryApplyFieldList [``C99.Proof.wp_assign_field_int_same,
                ``C99.Proof.wp_assign_field_int, ``C99.Proof.wp_assign_field_ptr,
                ``C99.Proof.wp_assignOp_field_int] mGoal blkGoal
            | none => pure false
          let ok ← if fieldOk then pure true else
            tryApplyList [``C99.Proof.wp_assign_slot_int_same, ``C99.Proof.wp_assign_slot_int,
              ``C99.Proof.wp_assign_slot_ptr, ``C99.Proof.wp_assignOp_slot_int]
          if ok then
            runCFrame
            return true
          return false
        if fFn == some ``C99.Sem.ExprFrame.incDecF then
          let some opRaw := f.getAppArgs[0]? | return false
          let opW ← g.withContext do whnf opRaw
          let opFn := opW.getAppFn.constName?
          let (fieldThms, slotThms) :=
            if opFn == some ``C99.IncDecOp.postInc || opFn == some ``C99.IncDecOp.postDec then
              ([``C99.Proof.wp_incDec_field_post_int_eq, ``C99.Proof.wp_incDec_field_post_int,
                ``C99.Proof.wp_incDec_field_int],
               [``C99.Proof.wp_incDec_slot_post_int_eq, ``C99.Proof.wp_incDec_slot_post_int,
                ``C99.Proof.wp_incDec_slot_int])
            else
              ([``C99.Proof.wp_incDec_field_pre_int, ``C99.Proof.wp_incDec_field_int],
               [``C99.Proof.wp_incDec_slot_pre_int, ``C99.Proof.wp_incDec_slot_int])
          let blkGoal? ← match esArgs[0]? with
            | some resRaw => do
              let resW ← g.withContext do whnf resRaw
              pure (if resW.getAppFn.constName? == some ``C99.Sem.ExprRes.lval then resW.getAppArgs[0]? else none)
            | none => pure none
          let fieldOk ← match blkGoal? with
            | some blkGoal => tryApplyFieldList fieldThms mGoal blkGoal
            | none => pure false
          let ok ← if fieldOk then pure true else tryApplyList slotThms
          if ok then
            runCFrame
            return true
          return false
        if fFn == some ``C99.Sem.ExprFrame.callFnF then
          let some argsRaw := f.getAppArgs[0]? | return false
          let argsW ← g.withContext do whnf argsRaw
          if argsW.getAppFn.constName? == some ``List.cons then
            return ← applyWPLemma ``C99.Proof.wp_call_arg0
          return false
        if fFn == some ``C99.Sem.ExprFrame.callArgF then
          let some restRaw := f.getAppArgs[3]? | return false
          let restW ← g.withContext do whnf restRaw
          if restW.getAppFn.constName? == some ``List.cons then
            return ← applyWPLemma ``C99.Proof.wp_call_arg_next
          return false
        return ← runCEvalStep
    else if esFn == some ``C99.Sem.ExprState.eval && esArgs.size == 3 then
      let some eRaw := esArgs[1]? | return false
      let e ← g.withContext do whnf eRaw
      let eFn := e.getAppFn.constName?
      if eFn == some ``C99.CExpr.assign then return ← applyWPLemma ``C99.Proof.wp_assign
      if eFn == some ``C99.CExpr.incDec then return ← applyWPLemma ``C99.Proof.wp_incDec
      if eFn == some ``C99.CExpr.call then return ← applyWPLemma ``C99.Proof.wp_call_push
      return ← runCEvalStep
  return false

/-- Iterates `c_step` + `c_frame` across straight-line sequences up to `fuel` steps,
stopping cleanly at loops, switches, gotos, unknown branches, function calls, or non-`WPTerm` goals. -/
def runCRun (fuel : Nat := 256) : TacticM Unit := do
  runCFrame
  for _ in List.range fuel do
    if (← getGoals).isEmpty then
      break
    let g ← getMainGoal
    let isWP ← g.withContext do
      let ty ← whnfR (← g.getType)
      pure (isWPTermTarget ty)
    if !isWP then
      break
    if !(← runCStep) then
      break

end Tactics

open Lean Elab Tactic in
/-- Automatically transports `Slot`, `Field`, `m.blocks`, `PtrValid`, and `PtrWritable`
hypotheses across memory transitions (`writeVal`, `writeBytes`, `writePlace`, `alloc`, `ROExt`,
`FrameBlocks`, `freeStack`) and pushed `env` bindings. -/
elab "c_frame" : tactic => runCFrame

open Lean Elab Tactic in
/-- Evaluates pure C subexpressions inside a `WPTerm` goal in one call. -/
elab "c_eval" : tactic => runCEval

open Lean Elab Tactic in
/-- Advances a single deterministic `WPTerm` step (statement, declaration, assignment, incDec,
control transfer, or expression evaluation) and auto-frames context hypotheses. -/
elab "c_step" : tactic => do
  let ok ← runCStep
  if !ok then
    throwError "c_step: no deterministic step applies at the current goal"

open Lean Elab Tactic in
/-- Iterates `c_step` / `c_frame` safely across straight-line C sequences (stopping cleanly at
loops, switches, gotos, unknown branches, calls ready to invoke, or finished postconditions). -/
syntax "c_run" (num)? : tactic

elab_rules : tactic
  | `(tactic| c_run) => runCRun 256
  | `(tactic| c_run $n:num) => runCRun n.getNat

/-! ## 7. Built-In Smoke Tests (`smoke_fn1`, `smoke_fn2`) -/

private def smokeFn1Body : CStmt :=
  .block [
    .decls [
      { name := "v0", ty := .int .i32, isStatic := false, init? := some (.expr (.lit 1)) },
      { name := "v1", ty := .int .i32, isStatic := false, init? := some (.expr (.lit 2)) },
      { name := "v2", ty := .int .i32, isStatic := false, init? := some (.expr (.binary .add (.var "v0") (.var "v1"))) },
      { name := "v3", ty := .int .i32, isStatic := false, init? := none }
    ],
    .expr (.assign .eq (.var "v3") (.binary .add (.var "a") (.var "v2"))),
    .expr (.assign .eq (.arrow (.var "s") "x") (.binary .add (.arrow (.var "s") "x") (.var "v3"))),
    .ifStmt (.binary .gt (.arrow (.var "s") "x") (.lit 0))
      (.returnStmt (some (.arrow (.var "s") "x")))
      (some (.returnStmt (some (.arrow (.var "s") "y"))))
  ]

private theorem smoke_fn1 (cfg : PointerConfig) (ext : ExtHandler)
    (m0 : Mem) (os0 : OSState)
    (bs ba bstruct : BlockId) (offs : Int64) (abv : BitVec 32)
    (_hne_sa : bs ≠ ba) (hne_xs : bstruct ≠ bs) (hne_xa : bstruct ≠ ba)
    (ha_range : -100 ≤ intToInt .i32 abv ∧ intToInt .i32 abv ≤ 1000)
    (hs_s : Slot [("s", bs, .ptr (.structTy "Pair")), ("a", ba, .int .i32)]
      m0 "s" bs (.ptr (.structTy "Pair")) (· = .ptr bstruct offs))
    (hs_a : Slot [("s", bs, .ptr (.structTy "Pair")), ("a", ba, .int .i32)]
      m0 "a" ba (.int .i32) (· = .int .i32 abv))
    (hf_x : Field [("Pair", .structDef [("x", .int .i32), ("y", .int .i32)])]
      m0 bstruct offs "Pair" "x" (.int .i32) (IntRange .i32 0 1000))
    (hf_y : Field [("Pair", .structDef [("x", .int .i32), ("y", .int .i32)])]
      m0 bstruct offs "Pair" "y" (.int .i32) (IntRange .i32 (-100) 100)) :
    let prog : Prog := {
      tags := [("Pair", .structDef [("x", .int .i32), ("y", .int .i32)])],
      globals := [], fns := fun _ => none, fnProtos := fun _ => none, fnStatics := fun _ => [] }
    let env0 : Env := [("s", bs, .ptr (.structTy "Pair")), ("a", ba, .int .i32)]
    let Q : Val → Mem → OSState → Prop := fun rv m' _ =>
      (∃ bv : BitVec 32, rv = .int .i32 bv ∧ -100 ≤ intToInt .i32 bv ∧ intToInt .i32 bv ≤ 3000) ∧
      Field prog.tags m' bstruct offs "Pair" "y" (.int .i32) (IntRange .i32 (-100) 100) ∧
      FrameBlocks m0 m' (fun b => b = bstruct ∨ m0.nextBlock ≤ b)
    WPTerm prog cfg ext Q (.running (.stmt smokeFn1Body) env0 [] m0 os0 (.stop (.int .i32))) := by
  intro prog env0 Q
  c_run
  have hfr0 : FrameBlocks m0 _ (fun b => b = bstruct ∨ m0.nextBlock ≤ b) :=
    ‹FrameBlocks m0 _ {m0.nextBlock}›.mono (fun _ h => by rw [AutoBlockSet.mem_singleton] at h; subst h; exact Or.inr (Nat.le_refl _))
  have hfr1 := hfr0.trans_next_ge ‹FrameBlocks _ _ _›
  have hfr2 := hfr1.trans_next_ge ‹FrameBlocks _ _ _›
  have hfr3 := (hfr2.trans_next_ge ‹FrameBlocks _ _ _›).trans_sub ‹FrameBlocks _ _ {m2.nextBlock}›
    (fun _ h => by rw [AutoBlockSet.mem_singleton] at h; subst h; exact Or.inr hfr2.1)
  have hfr4 := hfr3.trans_sub ‹FrameBlocks _ _ {bstruct}›
    (fun _ h => by rw [AutoBlockSet.mem_singleton] at h; subst h; exact Or.inl rfl)
  have hfr_done : ∀ {blks : List BlockId}, (∀ b ∈ blks, m0.nextBlock ≤ b) →
      FrameBlocks m0 (m'.freeStack blks) (fun b => b = bstruct ∨ m0.nextBlock ≤ b) :=
    fun h => hfr4.freeStack_allowed_ge h
  by_cases hgt : 0 < intToInt .i32 ‹_›
  · c_run; dsimp only [evalArithRaw] at *
    exact ⟨⟨_, rfl, by omega, by omega⟩, by assumption, hfr_done (fun _ hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> first | exact hfr2.1 | exact hfr1.1 | exact hfr0.1 | exact Nat.le_refl _)⟩
  · c_run
    exact ⟨⟨_, rfl, by omega, by omega⟩, by assumption, hfr_done (fun _ hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> first | exact hfr2.1 | exact hfr1.1 | exact hfr0.1 | exact Nat.le_refl _)⟩

private def smokeFn2Body : CStmt :=
  .whileStmt (.incDec .postDec (.var "n"))
    (.expr (.incDec .postInc (.arrow (.var "p") "count")))

private theorem smoke_fn2 (cfg : PointerConfig) (ext : ExtHandler)
    (m0 : Mem) (os0 : OSState)
    (bp bn bc : BlockId) (offc : Int64) (n0 : Nat) (nbv0 : BitVec 32)
    (hne_pn : bp ≠ bn) (hne_pc : bp ≠ bc) (hne_nc : bn ≠ bc)
    (hn0_eq : intToInt .i32 nbv0 = (n0 : Int)) (hn0_le : n0 ≤ 100)
    (hs_p : Slot [("p", bp, .ptr (.structTy "Counter")), ("n", bn, .int .i32)]
      m0 "p" bp (.ptr (.structTy "Counter")) (· = .ptr bc offc))
    (hs_n : Slot [("p", bp, .ptr (.structTy "Counter")), ("n", bn, .int .i32)]
      m0 "n" bn (.int .i32) (· = .int .i32 nbv0))
    (hf_cnt : Field [("Counter", .structDef [("count", .int .i32)])]
      m0 bc offc "Counter" "count" (.int .i32) (IntRange .i32 0 1000)) :
    let prog : Prog := {
      tags := [("Counter", .structDef [("count", .int .i32)])],
      globals := [], fns := fun _ => none, fnProtos := fun _ => none, fnStatics := fun _ => [] }
    let env0 : Env := [("p", bp, .ptr (.structTy "Counter")), ("n", bn, .int .i32)]
    let Q : Val → Mem → OSState → Prop := fun rv m' _ =>
      rv = .void ∧
      Field prog.tags m' bc offc "Counter" "count" (.int .i32) (IntRange .i32 0 1100) ∧
      FrameBlocks m0 m' {bn, bc}
    WPTerm prog cfg ext Q (.running (.stmt smokeFn2Body) env0 [] m0 os0 (.stop .void)) := by
  intro prog env0 Q
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun k env blks m _ =>
    env = env0 ∧ blks = [] ∧ k ≤ 100 ∧
    (∃ nbv : BitVec 32, intToInt .i32 nbv = (k : Int) ∧ Slot env0 m "n" bn (.int .i32) (· = .int .i32 nbv)) ∧
    Slot env0 m "p" bp (.ptr (.structTy "Counter")) (· = .ptr bc offc) ∧
    Field prog.tags m bc offc "Counter" "count" (.int .i32) (IntRange .i32 0 (1100 - k)) ∧
    FrameBlocks m0 m {bn, bc}
  refine WPTerm.while_wf Inv (n0 := n0) ⟨rfl, rfl, hn0_le, ⟨nbv0, hn0_eq, hs_n⟩, hs_p,
    hf_cnt.mono (fun _ ⟨bv, hbv, h1, h2⟩ => ⟨bv, hbv, h1, by omega⟩), FrameBlocks.refl m0 _⟩ ?_
  intro k env blks m os hinv ih
  rcases hinv with ⟨rfl, rfl, hk_le, ⟨nbv, hnbv, hs_nk⟩, hs_pk, hf_ck, hfr_k⟩
  c_step; c_eval; c_frame; c_run
  by_cases hk0 : k = 0
  · subst hk0; c_run
    refine ⟨rfl, Field.mono (fun _ ⟨bv, hbv, h1, h2⟩ => ⟨bv, hbv, h1, by omega⟩)
      ‹Field prog.tags _ bc offc "Counter" "count" (.int .i32) (IntRange .i32 0 (1100 - ↑0))›,
      hfr_k.trans_sub ‹FrameBlocks m _ {bn}› (fun _ h => by simp only [AutoBlockSet.mem_singleton] at h; exact Or.inl h)⟩
  · c_run; apply wp_loop_next_while
    refine ih (k - 1) env0 [] _ os (by omega) ⟨rfl, rfl, by omega, ?_, by assumption, ?_, ?_⟩
    · refine ⟨_, ?_, by assumption⟩; dsimp only [incDecDelta] at *; omega
    · apply Field.mono; rotate_left 1; assumption
      obtain ⟨_, heq, _, _⟩ := ‹IntRange .i32 0 (1100 - ↑k) _›; cases heq
      intro _ h; subst h; exact ⟨_, rfl, by dsimp only [incDecDelta] at *; omega, by dsimp only [incDecDelta] at *; omega⟩
    · exact hfr_k.trans_sub (FrameBlocks.trans (s1 := {bn}) (s2 := {bc}) (by assumption) (by assumption))
        (fun _ h => by simp only [AutoBlockSet.mem_union, AutoBlockSet.mem_singleton] at h; rcases h with h | h <;> first | exact Or.inl h | exact Or.inr h)

end C99.Proof

