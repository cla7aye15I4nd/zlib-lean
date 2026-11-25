import C99.Proof.Mem
import C99.Proof.WP

/-!
# Composable Symbolic WP & Hoare Logic for `C99.Sem` (`C99.Proof.Hoare`)

Domain-agnostic symbolic verification infrastructure built directly over
`C99.Proof.Mem` and `C99.Proof.WP`:
1. Fast `simp only` scalar, cast, truthiness, unary, binary, and pointer combinators.
2. Block-level framing (`FrameMod`), local slots, struct `FieldCell`, and typed `ArraySlice`.
3. Continuation-polymorphic `ExprSpec`, `PureExprSpec`, `LvalSpec`, `PureLvalSpec`, `ExprListSpec`.
4. Continuation-polymorphic `StmtSpec` and multi-exit `StmtSpecEx` (`Norm`, `Brk`, `Cont`, `Ret`).
5. `ExtLibc` specifications and `WPTerm` combinators matching `C99.Libc.ExtStep` / `ExtOk`.
-/

namespace C99.Proof

open C99 C99.Sem

/-! ## 1. Fast `simp only` Scalar, Type, Cast, Truthiness & Pointer Combinators -/

/-! ### 1.1 Basic Type, Memory, and Lookup Helpers -/

theorem cty_unqual_idemp (ty : CTy) : ty.unqual.unqual = ty.unqual := by
  match ty with
  | .const_ t => simp only [CTy.unqual]; exact cty_unqual_idemp t
  | .typedef _ t => simp only [CTy.unqual]; exact cty_unqual_idemp t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

theorem cty_decay_of_int : ∀ (ty : CTy) {k : IntKind},
    ty.unqual = .int k → ty.decay.unqual = .int k
  | .const_ t, _, hk => cty_decay_of_int t hk
  | .typedef _ t, _, hk => cty_decay_of_int t hk
  | .int _, _, hk => hk
  | .void, _, hk | .ptr _, _, hk | .array _ _, _, hk | .structTy _, _, hk | .unionTy _, _, hk
  | .anonStruct _, _, hk | .anonUnion _, _, hk | .enumTy _ _, _, hk | .fnPtr _ _ _, _, hk
  | .vaList, _, hk => by cases hk

theorem cty_decay_of_ptr : ∀ (ty : CTy) {el : CTy},
    ty.unqual = .ptr el → ty.decay.unqual = .ptr el
  | .const_ t, _, hp => cty_decay_of_ptr t hp
  | .typedef _ t, _, hp => cty_decay_of_ptr t hp
  | .ptr _, _, hp => hp
  | .void, _, hp | .int _, _, hp | .array _ _, _, hp | .structTy _, _, hp | .unionTy _, _, hp
  | .anonStruct _, _, hp | .anonUnion _, _, hp | .enumTy _ _, _, hp | .fnPtr _ _ _, _, hp
  | .vaList, _, hp => by cases hp

theorem cty_decay_of_fnPtr : ∀ (ty : CTy) {rty : CTy} {ptys : List CTy} {va : Bool},
    ty.unqual = .fnPtr rty ptys va → ty.decay.unqual = .fnPtr rty ptys va
  | .const_ t, _, _, _, hf => cty_decay_of_fnPtr t hf
  | .typedef _ t, _, _, _, hf => cty_decay_of_fnPtr t hf
  | .fnPtr _ _ _, _, _, _, hf => hf
  | .void, _, _, _, hf | .int _, _, _, _, hf | .ptr _, _, _, _, hf | .array _ _, _, _, _, hf
  | .structTy _, _, _, _, hf | .unionTy _, _, _, _, hf | .anonStruct _, _, _, _, hf
  | .anonUnion _, _, _, _, hf | .enumTy _ _, _, _, _, hf | .vaList, _, _, _, hf => by cases hf

theorem cty_decay_of_array : ∀ (ty : CTy) {el : CTy} {n : Option Nat},
    ty.unqual = .array el n → ty.decay.unqual = .ptr el
  | .const_ t, _, _, ha => cty_decay_of_array t ha
  | .typedef _ t, _, _, ha => cty_decay_of_array t ha
  | .array _ _, _, _, ha => by cases ha; rfl
  | .void, _, _, ha | .int _, _, _, ha | .ptr _, _, _, ha | .structTy _, _, _, ha
  | .unionTy _, _, _, ha | .anonStruct _, _, _, ha | .anonUnion _, _, _, ha
  | .enumTy _ _, _, _, ha | .fnPtr _ _ _, _, _, ha | .vaList, _, _, ha => by cases ha

theorem cty_isPtr_of_ptr {ty el : CTy} (hp : ty.unqual = .ptr el) : ty.isPtr = true := by
  simp only [CTy.isPtr, hp]

theorem cty_isPtr_false_of_int {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    ty.isPtr = false := by
  simp only [CTy.isPtr, hk]

theorem cty_isPtr_false_of_enum {ty : CTy} {tag : String} {isU : Bool}
    (he : ty.unqual = .enumTy tag isU) : ty.isPtr = false := by
  simp only [CTy.isPtr, he]

theorem sizeofTy_eq_bytes {tags : TypeEnv} {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    sizeofTy tags ty = k.bytes := by
  rw [← sizeofTy_unqual, hk]; exact sizeofTy_int tags k

theorem alignofTy_eq_align {tags : TypeEnv} {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    alignofTy tags ty = k.align := by
  rw [← alignofTy_unqual, hk]; exact alignofTy_int tags k

theorem sizeofTy_eq_ptr {tags : TypeEnv} {ty el : CTy} (hp : ty.unqual = .ptr el) :
    sizeofTy tags ty = 8 := by
  rw [← sizeofTy_unqual, hp]; exact sizeofTy_ptr tags el

theorem alignofTy_eq_ptr {tags : TypeEnv} {ty el : CTy} (hp : ty.unqual = .ptr el) :
    alignofTy tags ty = 8 := by
  rw [← alignofTy_unqual, hp]; exact alignofTy_ptr tags el

theorem sizeofTy_eq_fnPtr {tags : TypeEnv} {ty rty : CTy} {ptys : List CTy} {va : Bool}
    (hf : ty.unqual = .fnPtr rty ptys va) : sizeofTy tags ty = 8 := by
  rw [← sizeofTy_unqual, hf]; unfold sizeofTy sizeofAux; rfl

theorem alignofTy_eq_fnPtr {tags : TypeEnv} {ty rty : CTy} {ptys : List CTy} {va : Bool}
    (hf : ty.unqual = .fnPtr rty ptys va) : alignofTy tags ty = 8 := by
  rw [← alignofTy_unqual, hf]; unfold alignofTy alignofAux; rfl

private theorem opt_bind_some {α β : Type} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

theorem freeStack_nil_eq (m : Mem) : m.freeStack [] = m := by
  cases m
  unfold Mem.freeStack
  have h : ∀ b : BlockId, ([] : List BlockId).contains b = false := fun _ => rfl
  simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem readBytes_congr_blocks {m1 m2 : Mem} {b : BlockId}
    (hb : m1.blocks b = m2.blocks b) (off : Int64) (len : Nat) :
    m1.readBytes b off len = m2.readBytes b off len := by
  unfold Mem.readBytes; rw [hb]

theorem readVal_congr_blocks (tags : TypeEnv) {m1 m2 : Mem} {b : BlockId}
    (hb : m1.blocks b = m2.blocks b) (off : Int64) (ty : CTy) :
    Sem.readVal tags m1 b off ty = Sem.readVal tags m2 b off ty := by
  unfold Sem.readVal Mem.readBytes; rw [hb]

theorem strlenAt_congr_blocks {m1 m2 : Mem} {b : BlockId}
    (hb : m1.blocks b = m2.blocks b) (off : Int64) :
    m1.strlenAt b off = m2.strlenAt b off := by
  unfold Mem.strlenAt; rw [hb]

theorem modSet_conflicts_nil (b : BlockId) (o : Int64) (n : Nat) :
    ModSet.conflicts [] b o n = false := rfl

theorem modSet_conflicts_cons_ne {b b' : BlockId} {o o' : Int64} {n n' : Nat} {ms : ModSet}
    (hne : b' ≠ b) (hrest : ms.conflicts b o n = false) :
    ModSet.conflicts (⟨b', o', n'⟩ :: ms) b o n = false := by
  unfold ModSet.conflicts at hrest ⊢
  simp only [List.any_cons, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
  exact ⟨Or.inl (beq_false_of_ne hne), hrest⟩

theorem modSet_conflicts_cons_disjoint {b : BlockId} {o o' : Int64} {n n' : Nat} {ms : ModSet}
    (hdisj : o'.toInt + n' ≤ o.toInt ∨ o.toInt + n ≤ o'.toInt)
    (hrest : ms.conflicts b o n = false) :
    ModSet.conflicts (⟨b, o', n'⟩ :: ms) b o n = false := by
  unfold ModSet.conflicts at hrest ⊢
  simp only [List.any_cons, Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false']
  refine ⟨Or.inr ?_, hrest⟩
  exact decide_eq_true hdisj

/-! ### 1.2 `BitVec` and `Int64` Arithmetic Helpers -/

theorem bitVec_ofInt_toInt {w : Nat} (bv : BitVec w) : BitVec.ofInt w bv.toInt = bv :=
  BitVec.ofInt_toInt

theorem bitVec_ofInt_toInt_of_range {w : Nat} (hw : 0 < w) {x : Int}
    (hlo : -(2 ^ (w - 1) : Int) ≤ x) (hhi : x < (2 ^ (w - 1) : Int)) :
    (BitVec.ofInt w x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  have hpow : ((2 ^ w : Nat) : Int) = 2 * (2 ^ (w - 1) : Int) := by
    rw [Int.natCast_pow, ← Nat.sub_add_cancel hw, Int.pow_succ, Int.mul_comm]
    norm_cast
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem bitVec_ofInt_toNat {w : Nat} {x : Int} (hlo : 0 ≤ x) (hhi : x < (2 ^ w : Int)) :
    (BitVec.ofInt w x).toNat = x.toNat := by
  rw [BitVec.toNat_ofInt]
  have hhi' : x < ((2 ^ w : Nat) : Int) := by rw [Int.natCast_pow]; exact hhi
  rw [Int.emod_eq_of_lt hlo hhi']

theorem bitVec_ofInt_natCast_toNat {w : Nat} {n : Nat} (hlt : n < 2 ^ w) :
    (BitVec.ofInt w (n : Int)).toNat = n := by
  rw [bitVec_ofInt_toNat (Int.natCast_nonneg n) (by exact_mod_cast hlt), Int.toNat_natCast]

theorem bitVec_ofInt_toNat_self {w : Nat} (bv : BitVec w) :
    BitVec.ofInt w (bv.toNat : Int) = bv := by
  apply BitVec.eq_of_toNat_eq
  exact bitVec_ofInt_natCast_toNat bv.isLt

theorem int64_ofNat_toInt {n : Nat} (hlt : (n : Int) < 2 ^ 63) :
    (Int64.ofNat n).toInt = (n : Int) := by
  have heq : (Int64.ofNat n).toBitVec = BitVec.ofInt 64 (n : Int) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 n).toNat = (BitVec.ofInt 64 (n : Int)).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    rw [bitVec_ofInt_natCast_toNat (by omega)]
  change (Int64.ofNat n).toBitVec.toInt = (n : Int)
  rw [heq]
  exact bitVec_ofInt_toInt_of_range (by decide) (by omega) hlt

theorem bitVec_ofNat_eq_ofInt {w : Nat} (n : Nat) :
    BitVec.ofNat w n = BitVec.ofInt w (n : Int) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have h1 : (n : Int) % ((2 ^ w : Nat) : Int) = ((n % 2 ^ w : Nat) : Int) := by omega
  rw [h1, Int.toNat_natCast]

/-! ### 1.3 Truthiness Lemmas -/

@[simp] theorem isTruthy_int (k : IntKind) (v : BitVec k.bits) :
    isTruthy (.int k v) = some (v.toNat != 0) := rfl

theorem isTruthy_int_true {k : IntKind} {v : BitVec k.bits} (h : v.toNat ≠ 0) :
    isTruthy (.int k v) = some true := by
  simp only [isTruthy_int, bne, beq_false_of_ne h, Bool.not_false]

theorem isTruthy_int_false {k : IntKind} {v : BitVec k.bits} (h : v.toNat = 0) :
    isTruthy (.int k v) = some false := by
  simp only [isTruthy_int, h, bne_self_eq_false]

@[simp] theorem isTruthy_ptr (b : BlockId) (off : Int64) :
    isTruthy (.ptr b off) = some true := rfl

@[simp] theorem isTruthy_fnPtr (sym : SymId) :
    isTruthy (.fnPtr sym) = some true := rfl

@[simp] theorem isTruthy_null :
    isTruthy .null = some false := rfl

/-! ### 1.4 `castVal` Lemmas -/

theorem castVal_unqual_eq (m : Mem) (ty : CTy) (v : Val) :
    castVal m ty v = castVal m ty.unqual v := by
  unfold castVal
  simp only [cty_unqual_idemp]

theorem castVal_void_eq {m : Mem} {ty : CTy} (hv : ty.unqual = .void) (v : Val) :
    castVal m ty v = some .void := by
  unfold castVal
  simp only [hv, CTy.isVoid, CTy.unqual, ↓reduceIte]

theorem castVal_int_eq {m : Mem} {ty : CTy} {k1 k2 : IntKind}
    (hk2 : ty.unqual = .int k2) (bv : BitVec k1.bits) :
    castVal m ty (.int k1 bv) =
      some (.int k2 (BitVec.ofInt k2.bits (if k1.signed then bv.toInt else (bv.toNat : Int)))) := by
  unfold castVal
  simp only [hk2, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?, ofIntCast]

theorem castVal_int_self_eq {m : Mem} {ty : CTy} {k : IntKind}
    (hk : ty.unqual = .int k) (bv : BitVec k.bits) :
    castVal m ty (.int k bv) = some (.int k bv) := by
  rw [castVal_int_eq hk]
  by_cases hs : k.signed
  · simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self]

theorem castVal_int_null_eq {m : Mem} {ty : CTy} {k2 : IntKind}
    (hk2 : ty.unqual = .int k2) :
    castVal m ty .null = some (.int k2 0) := by
  unfold castVal
  simp only [hk2, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?]

theorem castVal_int_ptr_eq {m : Mem} {ty : CTy} {k2 : IntKind} {b : BlockId} {off : Int64}
    {addr : UInt64} (hk2 : ty.unqual = .int k2) (ha : m.addrOf b off = some addr) :
    castVal m ty (.ptr b off) = some (.int k2 (BitVec.ofNat k2.bits addr.toNat)) := by
  unfold castVal
  simp only [hk2, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?, ha,
    Option.map_some]

theorem castVal_enum_int_eq {m : Mem} {ty : CTy} {tag : String} {isU : Bool} {k1 : IntKind}
    (he : ty.unqual = .enumTy tag isU) (bv : BitVec k1.bits) :
    castVal m ty (.int k1 bv) =
      some (.int (if isU then .u32 else .i32)
        (BitVec.ofInt (if isU then IntKind.u32 else IntKind.i32).bits
          (if k1.signed then bv.toInt else (bv.toNat : Int)))) := by
  unfold castVal
  simp only [he, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?, ofIntCast]

theorem castVal_ptr_eq {m : Mem} {ty el : CTy}
    (hp : ty.unqual = .ptr el) (b : BlockId) (off : Int64) :
    castVal m ty (.ptr b off) = some (.ptr b off) := by
  unfold castVal
  simp only [hp, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?]

theorem castVal_null_eq {m : Mem} {ty el : CTy}
    (hp : ty.unqual = .ptr el) :
    castVal m ty .null = some .null := by
  unfold castVal
  simp only [hp, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?]

theorem castVal_ptr_zero_eq {m : Mem} {ty el : CTy} {k : IntKind}
    (hp : ty.unqual = .ptr el) {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    castVal m ty (.int k bv) = some .null := by
  unfold castVal
  simp only [hp, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?, hz,
    beq_self_eq_true]

theorem castVal_fnPtr_eq {m : Mem} {ty rty : CTy} {ptys : List CTy} {va : Bool}
    (hf : ty.unqual = .fnPtr rty ptys va) (sym : SymId) :
    castVal m ty (.fnPtr sym) = some (.fnPtr sym) := by
  unfold castVal
  simp only [hf, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?]

theorem castVal_fnPtr_null_eq {m : Mem} {ty rty : CTy} {ptys : List CTy} {va : Bool}
    (hf : ty.unqual = .fnPtr rty ptys va) :
    castVal m ty .null = some .null := by
  unfold castVal
  simp only [hf, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?]

theorem castVal_vaList_eq {m : Mem} {ty : CTy} (hv : ty.unqual = .vaList) :
    castVal m ty (.vaList true) = some (.vaList true) := by
  unfold castVal
  simp only [hv, CTy.isVoid, CTy.unqual, Bool.false_eq_true, ↓reduceIte, CTy.intKind?]

/-! ### 1.5 `evalUnary` Lemmas (`evalUnary` / `evalIntUnary`) -/

theorem evalUnary_plus_gen {k : IntKind} (v : BitVec k.bits)
    (hr : k.promote.inRange (if k.signed then v.toInt else (v.toNat : Int)) = true) :
    evalUnary .plus (.int k v) =
      some (.int k.promote (BitVec.ofInt k.promote.bits (if k.signed then v.toInt else (v.toNat : Int))),
        .int k.promote) := by
  unfold evalUnary
  simp only [valAsInt?_int, bind, opt_bind_some, pure, Pure.pure]
  by_cases hs : k.promote.signed
  · simp only [ofIntExact_signed hs hr, opt_bind_some]
  · have hsf : k.promote.signed = false := Bool.eq_false_iff.mpr hs
    simp only [ofIntExact_unsigned hsf, opt_bind_some]

private theorem some_val_int_i32 {a : BitVec IntKind.i32.bits} {b : BitVec 32}
    (h : (a : BitVec 32) = b) :
    some (Val.int .i32 a, CTy.int .i32) = some (Val.int .i32 b, CTy.int .i32) := by
  have ha : a = b := h
  exact congrArg (fun x => some (Val.int .i32 x, CTy.int .i32)) ha

private theorem some_val_int_u32 {a : BitVec IntKind.u32.bits} {b : BitVec 32}
    (h : (a : BitVec 32) = b) :
    some (Val.int .u32 a, CTy.int .u32) = some (Val.int .u32 b, CTy.int .u32) := by
  have ha : a = b := h
  exact congrArg (fun x => some (Val.int .u32 x, CTy.int .u32)) ha

private theorem some_val_int_i64 {a : BitVec IntKind.i64.bits} {b : BitVec 64}
    (h : (a : BitVec 64) = b) :
    some (Val.int .i64 a, CTy.int .i64) = some (Val.int .i64 b, CTy.int .i64) := by
  have ha : a = b := h
  exact congrArg (fun x => some (Val.int .i64 x, CTy.int .i64)) ha

private theorem some_val_int_u64 {a : BitVec IntKind.u64.bits} {b : BitVec 64}
    (h : (a : BitVec 64) = b) :
    some (Val.int .u64 a, CTy.int .u64) = some (Val.int .u64 b, CTy.int .u64) := by
  have ha : a = b := h
  exact congrArg (fun x => some (Val.int .u64 x, CTy.int .u64)) ha

theorem evalUnary_plus_signed_exact {k : IntKind} (hk : k.promote = k) (hs : k.signed = true)
    (v : BitVec k.bits) (hr : k.inRange v.toInt = true) :
    evalUnary .plus (.int k v) = some (.int k v, .int k) := by
  cases k <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hk hs
  all_goals try cases hk
  all_goals try cases hs
  · have h := evalUnary_plus_gen (k := .i32) v hr
    simp only [promote_i32, IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt] at h
    exact h
  · have h := evalUnary_plus_gen (k := .i64) v hr
    simp only [promote_i64, IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt] at h
    exact h

theorem evalUnary_plus_unsigned {k : IntKind} (hk : k.promote.signed = false)
    (hprom : k.promote = k) (v : BitVec k.bits) :
    evalUnary .plus (.int k v) = some (.int k v, .int k) := by
  cases k <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hk hprom
  all_goals
    try cases hk
    try cases hprom
  · unfold evalUnary
    simp only [valAsInt?_int, promote_u32, IntKind.signed, Bool.false_eq_true, ↓reduceIte,
      ofIntExact_unsigned (k := .u32) rfl, bind, opt_bind_some, pure, Pure.pure,
      bitVec_ofInt_toNat_self]
  · unfold evalUnary
    simp only [valAsInt?_int, promote_u64, IntKind.signed, Bool.false_eq_true, ↓reduceIte,
      ofIntExact_unsigned (k := .u64) rfl, bind, opt_bind_some, pure, Pure.pure,
      bitVec_ofInt_toNat_self]

theorem evalUnary_plus_i32 (v : BitVec 32) :
    evalUnary .plus (.int .i32 v) = some (.int .i32 v, .int .i32) := by
  have hlo : -(2 ^ 31 : Int) ≤ v.toInt := BitVec.le_toInt v
  have hhi : v.toInt < (2 ^ 31 : Int) := BitVec.toInt_lt
  have hr : IntKind.i32.inRange v.toInt = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalUnary_plus_signed_exact (k := .i32) rfl rfl v hr

theorem evalUnary_plus_u32 (v : BitVec 32) :
    evalUnary .plus (.int .u32 v) = some (.int .u32 v, .int .u32) :=
  evalUnary_plus_unsigned (k := .u32) rfl rfl v

theorem evalUnary_plus_i64 (v : BitVec 64) :
    evalUnary .plus (.int .i64 v) = some (.int .i64 v, .int .i64) := by
  have hlo : -(2 ^ 63 : Int) ≤ v.toInt := BitVec.le_toInt v
  have hhi : v.toInt < (2 ^ 63 : Int) := BitVec.toInt_lt
  have hr : IntKind.i64.inRange v.toInt = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalUnary_plus_signed_exact (k := .i64) rfl rfl v hr

theorem evalUnary_plus_u64 (v : BitVec 64) :
    evalUnary .plus (.int .u64 v) = some (.int .u64 v, .int .u64) :=
  evalUnary_plus_unsigned (k := .u64) rfl rfl v

theorem evalUnary_neg_unsigned {k : IntKind} (hk : k.promote.signed = false)
    (hprom : k.promote = k) (v : BitVec k.bits) :
    evalUnary .neg (.int k v) = some (.int k (-v), .int k) := by
  cases k <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hk hprom
  all_goals
    try cases hk
    try cases hprom
  · unfold evalUnary
    simp only [valAsInt?_int, promote_u32, IntKind.signed, Bool.false_eq_true, ↓reduceIte,
      ofIntExact_unsigned (k := .u32) rfl, bind, opt_bind_some, pure, Pure.pure,
      BitVec.ofInt_neg, bitVec_ofInt_toNat_self]
  · unfold evalUnary
    simp only [valAsInt?_int, promote_u64, IntKind.signed, Bool.false_eq_true, ↓reduceIte,
      ofIntExact_unsigned (k := .u64) rfl, bind, opt_bind_some, pure, Pure.pure,
      BitVec.ofInt_neg, bitVec_ofInt_toNat_self]

theorem evalUnary_neg_u32 (v : BitVec 32) :
    evalUnary .neg (.int .u32 v) = some (.int .u32 (-v), .int .u32) :=
  evalUnary_neg_unsigned (k := .u32) rfl rfl v

theorem evalUnary_neg_u64 (v : BitVec 64) :
    evalUnary .neg (.int .u64 v) = some (.int .u64 (-v), .int .u64) :=
  evalUnary_neg_unsigned (k := .u64) rfl rfl v

theorem evalUnary_neg_signed {k : IntKind} (hk : k.promote.signed = true) (v : BitVec k.bits)
    (hr : k.promote.inRange (-(if k.signed then v.toInt else (v.toNat : Int))) = true) :
    evalUnary .neg (.int k v) =
      some (.int k.promote (BitVec.ofInt k.promote.bits (-(if k.signed then v.toInt else (v.toNat : Int)))),
        .int k.promote) := by
  unfold evalUnary
  simp only [valAsInt?_int, bind, opt_bind_some, pure, Pure.pure, ofIntExact_signed hk hr]

theorem evalUnary_neg_signed_exact {k : IntKind} (hk : k.promote = k) (hs : k.signed = true)
    (v : BitVec k.bits) (hr : k.inRange (-v.toInt) = true) :
    evalUnary .neg (.int k v) = some (.int k (-v), .int k) := by
  cases k <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hk hs
  all_goals try cases hk
  all_goals try cases hs
  · have h := evalUnary_neg_signed (k := .i32) rfl v hr
    simp only [promote_i32, IntKind.signed, ↓reduceIte, BitVec.ofInt_neg, bitVec_ofInt_toInt] at h
    exact h
  · have h := evalUnary_neg_signed (k := .i64) rfl v hr
    simp only [promote_i64, IntKind.signed, ↓reduceIte, BitVec.ofInt_neg, bitVec_ofInt_toInt] at h
    exact h

theorem evalUnary_neg_i32 {v : BitVec 32} (hno : v.toInt ≠ -(2 ^ 31 : Int)) :
    evalUnary .neg (.int .i32 v) = some (.int .i32 (-v), .int .i32) := by
  have hlo : -(2 ^ 31 : Int) ≤ v.toInt := BitVec.le_toInt v
  have hhi : v.toInt < (2 ^ 31 : Int) := BitVec.toInt_lt
  have hr : IntKind.i32.inRange (-v.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalUnary_neg_signed_exact (k := .i32) rfl rfl v hr

theorem evalUnary_neg_i64 {v : BitVec 64} (hno : v.toInt ≠ -(2 ^ 63 : Int)) :
    evalUnary .neg (.int .i64 v) = some (.int .i64 (-v), .int .i64) := by
  have hlo : -(2 ^ 63 : Int) ≤ v.toInt := BitVec.le_toInt v
  have hhi : v.toInt < (2 ^ 63 : Int) := BitVec.toInt_lt
  have hr : IntKind.i64.inRange (-v.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalUnary_neg_signed_exact (k := .i64) rfl rfl v hr

theorem evalUnary_neg_u8 (v : BitVec 8) :
    evalUnary .neg (.int .u8 v) = some (.int .i32 (BitVec.ofInt 32 (-(v.toNat : Int))), .int .i32) := by
  have hv : v.toNat < 2 ^ 8 := v.isLt
  have hr : IntKind.i32.inRange (-(v.toNat : Int)) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalUnary_neg_signed (k := .u8) rfl v hr

theorem evalUnary_neg_u16 (v : BitVec 16) :
    evalUnary .neg (.int .u16 v) = some (.int .i32 (BitVec.ofInt 32 (-(v.toNat : Int))), .int .i32) := by
  have hv : v.toNat < 2 ^ 16 := v.isLt
  have hr : IntKind.i32.inRange (-(v.toNat : Int)) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalUnary_neg_signed (k := .u16) rfl v hr

theorem evalUnary_bitNot_gen {k : IntKind} (v : BitVec k.bits) :
    evalUnary .bitNot (.int k v) =
      some (.int k.promote (~~~(BitVec.ofInt k.promote.bits (if k.signed then v.toInt else (v.toNat : Int)))),
        .int k.promote) := rfl

theorem evalUnary_bitNot_exact {k : IntKind} (hprom : k.promote = k) (v : BitVec k.bits) :
    evalUnary .bitNot (.int k v) = some (.int k (~~~v), .int k) := by
  cases k <;> simp only [IntKind.promote, IntKind.rank] at hprom
  all_goals try cases hprom
  · unfold evalUnary; simp only [promote_i32, IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt]; rfl
  · unfold evalUnary; simp only [promote_u32, IntKind.signed, Bool.false_eq_true, ↓reduceIte,
      bitVec_ofInt_toNat_self]; rfl
  · unfold evalUnary; simp only [promote_i64, IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt]; rfl
  · unfold evalUnary; simp only [promote_u64, IntKind.signed, Bool.false_eq_true, ↓reduceIte,
      bitVec_ofInt_toNat_self]; rfl

theorem evalUnary_bitNot_i32 (v : BitVec 32) :
    evalUnary .bitNot (.int .i32 v) = some (.int .i32 (~~~v), .int .i32) :=
  evalUnary_bitNot_exact (k := .i32) rfl v

theorem evalUnary_bitNot_u32 (v : BitVec 32) :
    evalUnary .bitNot (.int .u32 v) = some (.int .u32 (~~~v), .int .u32) :=
  evalUnary_bitNot_exact (k := .u32) rfl v

theorem evalUnary_bitNot_i64 (v : BitVec 64) :
    evalUnary .bitNot (.int .i64 v) = some (.int .i64 (~~~v), .int .i64) :=
  evalUnary_bitNot_exact (k := .i64) rfl v

theorem evalUnary_bitNot_u64 (v : BitVec 64) :
    evalUnary .bitNot (.int .u64 v) = some (.int .u64 (~~~v), .int .u64) :=
  evalUnary_bitNot_exact (k := .u64) rfl v

theorem evalUnary_logNot_int (k : IntKind) (v : BitVec k.bits) :
    evalUnary .logNot (.int k v) =
      some (.int .i32 (if v.toNat != 0 then 0 else 1), .int .i32) := rfl

theorem evalUnary_logNot_i32 (v : BitVec 32) :
    evalUnary .logNot (.int .i32 v) = some (.int .i32 (if v.toNat != 0 then 0 else 1), .int .i32) := rfl

theorem evalUnary_logNot_u32 (v : BitVec 32) :
    evalUnary .logNot (.int .u32 v) = some (.int .i32 (if v.toNat != 0 then 0 else 1), .int .i32) := rfl

theorem evalUnary_logNot_i64 (v : BitVec 64) :
    evalUnary .logNot (.int .i64 v) = some (.int .i32 (if v.toNat != 0 then 0 else 1), .int .i32) := rfl

theorem evalUnary_logNot_u64 (v : BitVec 64) :
    evalUnary .logNot (.int .u64 v) = some (.int .i32 (if v.toNat != 0 then 0 else 1), .int .i32) := rfl

@[simp] theorem evalUnary_logNot_ptr (b : BlockId) (off : Int64) :
    evalUnary .logNot (.ptr b off) = some (.int .i32 0, .int .i32) := rfl

@[simp] theorem evalUnary_logNot_fnPtr (sym : SymId) :
    evalUnary .logNot (.fnPtr sym) = some (.int .i32 0, .int .i32) := rfl

@[simp] theorem evalUnary_logNot_null :
    evalUnary .logNot .null = some (.int .i32 1, .int .i32) := rfl

/-! ### 1.6 Fast `simp only` `evalIntBinary` Combinators -/

private theorem bitVec_ofInt_add_eq {w : Nat} (a b : Int) :
    BitVec.ofInt w (a + b) = BitVec.ofInt w a + BitVec.ofInt w b := by
  simp only [BitVec.ofInt_add]

private theorem bitVec_ofInt_sub_eq {w : Nat} (a b : Int) :
    BitVec.ofInt w (a - b) = BitVec.ofInt w a - BitVec.ofInt w b := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ← BitVec.sub_eq_add_neg]

private theorem bitVec_ofInt_mul_eq {w : Nat} (a b : Int) :
    BitVec.ofInt w (a * b) = BitVec.ofInt w a * BitVec.ofInt w b := by
  simp only [BitVec.ofInt_mul]

private theorem bitVec_ofInt_tdiv_unsigned {w : Nat} (a b : BitVec w) :
    BitVec.ofInt w (Int.tdiv (a.toNat : Int) (b.toNat : Int)) = a / b := by
  have ht : Int.tdiv (a.toNat : Int) (b.toNat : Int) = ((a.toNat / b.toNat : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _), Int.natCast_ediv]
  rw [ht]
  apply BitVec.eq_of_toNat_eq
  rw [bitVec_ofInt_natCast_toNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)]
  rfl

private theorem bitVec_ofInt_tmod_unsigned {w : Nat} (a b : BitVec w) :
    BitVec.ofInt w (Int.tmod (a.toNat : Int) (b.toNat : Int)) = a % b := by
  have ht : Int.tmod (a.toNat : Int) (b.toNat : Int) = ((a.toNat % b.toNat : Nat) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _), Int.natCast_emod]
  rw [ht]
  apply BitVec.eq_of_toNat_eq
  have hlt : a.toNat % b.toNat < 2 ^ w := by
    by_cases hb : b.toNat = 0
    · simp only [hb, Nat.mod_zero]; exact a.isLt
    · exact Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) b.isLt
  rw [bitVec_ofInt_natCast_toNat hlt]
  rfl

theorem evalIntBinary_cmp_gen (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (k1 k2 : IntKind) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    let n1 := if ck.signed then c1.toInt else (c1.toNat : Int)
    let n2 := if ck.signed then c2.toInt else (c2.toNat : Int)
    evalIntBinary op (.int k1 v1) (.int k2 v2) =
      some (.int .i32 (if cmpOrd op n1 n2 then 1 else 0), .int .i32) := by
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, opt_bind_some, pure, Pure.pure]
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem evalIntBinary_cmp_same (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {k : IntKind} (hck : IntKind.usualArith k k = k) (v1 v2 : BitVec k.bits) :
    let n1 := if k.signed then v1.toInt else (v1.toNat : Int)
    let n2 := if k.signed then v2.toInt else (v2.toNat : Int)
    evalIntBinary op (.int k v1) (.int k v2) =
      some (.int .i32 (if cmpOrd op n1 n2 then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_gen op hop k k v1 v2
  dsimp only at h
  rw [hck] at h
  by_cases hs : k.signed
  · simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h ⊢; exact h
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h ⊢; exact h

theorem evalIntBinary_unsigned_add {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .add (.int k1 v1) (.int k2 v2) = some (.int ck (c1 + c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, ofIntExact_unsigned hs,
    bind, opt_bind_some, pure, Pure.pure]
  rw [bitVec_ofInt_add_eq, bitVec_ofInt_toNat_self, bitVec_ofInt_toNat_self]

theorem evalIntBinary_unsigned_sub {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .sub (.int k1 v1) (.int k2 v2) = some (.int ck (c1 - c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, ofIntExact_unsigned hs,
    bind, opt_bind_some, pure, Pure.pure]
  rw [bitVec_ofInt_sub_eq, bitVec_ofInt_toNat_self, bitVec_ofInt_toNat_self]

theorem evalIntBinary_unsigned_mul {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .mul (.int k1 v1) (.int k2 v2) = some (.int ck (c1 * c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, ofIntExact_unsigned hs,
    bind, opt_bind_some, pure, Pure.pure]
  rw [bitVec_ofInt_mul_eq, bitVec_ofInt_toNat_self, bitVec_ofInt_toNat_self]

theorem evalIntBinary_unsigned_div {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hnz : (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toNat ≠ 0) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .div (.int k1 v1) (.int k2 v2) = some (.int ck (c1 / c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  have hne : (((BitVec.ofInt (k1.usualArith k2).bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toNat : Int) == 0) = false :=
    beq_false_of_ne (by omega)
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, hne, ofIntExact_unsigned hs,
    bind, opt_bind_some, pure, Pure.pure, bitVec_ofInt_tdiv_unsigned]

theorem evalIntBinary_unsigned_mod {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = false)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hnz : (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toNat ≠ 0) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .mod (.int k1 v1) (.int k2 v2) = some (.int ck (c1 % c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  have hne : (((BitVec.ofInt (k1.usualArith k2).bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toNat : Int) == 0) = false :=
    beq_false_of_ne (by omega)
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, hne, ofIntExact_unsigned hs,
    bind, opt_bind_some, pure, Pure.pure, bitVec_ofInt_tmod_unsigned]

theorem evalIntBinary_bitAnd_gen {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .bitAnd (.int k1 v1) (.int k2 v2) = some (.int ck (c1 &&& c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_bitOr_gen {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .bitOr (.int k1 v1) (.int k2 v2) = some (.int ck (c1 ||| c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_bitXor_gen {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .bitXor (.int k1 v1) (.int k2 v2) = some (.int ck (c1 ^^^ c2), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_signed_add {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hr : ck.inRange
      ((BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))).toInt +
       (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt) = true) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .add (.int k1 v1) (.int k2 v2) =
      some (.int ck (BitVec.ofInt ck.bits (c1.toInt + c2.toInt)), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, hs, ↓reduceIte, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_signed_sub {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hr : ck.inRange
      ((BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))).toInt -
       (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt) = true) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .sub (.int k1 v1) (.int k2 v2) =
      some (.int ck (BitVec.ofInt ck.bits (c1.toInt - c2.toInt)), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, hs, ↓reduceIte, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_signed_mul {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hr : ck.inRange
      ((BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))).toInt *
       (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt) = true) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .mul (.int k1 v1) (.int k2 v2) =
      some (.int ck (BitVec.ofInt ck.bits (c1.toInt * c2.toInt)), .int ck) := by
  subst hck
  unfold evalIntBinary
  simp only [valAsInt?_int, hs, ↓reduceIte, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_signed_div {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hnz : (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt ≠ 0)
    (hr : ck.inRange
      (Int.tdiv
        (BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))).toInt
        (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt) = true) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .div (.int k1 v1) (.int k2 v2) =
      some (.int ck (BitVec.ofInt ck.bits (Int.tdiv c1.toInt c2.toInt)), .int ck) := by
  subst hck
  unfold evalIntBinary
  have hne : ((BitVec.ofInt (k1.usualArith k2).bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt == 0) = false :=
    beq_false_of_ne hnz
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, hne, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_signed_mod {k1 k2 ck : IntKind}
    (hck : IntKind.usualArith k1 k2 = ck) (hs : ck.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hnz : (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt ≠ 0)
    (hr : ck.inRange
      (Int.tmod
        (BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))).toInt
        (BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt) = true) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    evalIntBinary .mod (.int k1 v1) (.int k2 v2) =
      some (.int ck (BitVec.ofInt ck.bits (Int.tmod c1.toInt c2.toInt)), .int ck) := by
  subst hck
  unfold evalIntBinary
  have hne : ((BitVec.ofInt (k1.usualArith k2).bits (if k2.signed then v2.toInt else (v2.toNat : Int))).toInt == 0) = false :=
    beq_false_of_ne hnz
  simp only [valAsInt?_int, hs, Bool.false_eq_true, ↓reduceIte, hne, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_unsigned_shift (op : BinOp) (hop : op = .shl ∨ op = .shr)
    {k1 k2 : IntKind} (hs : k1.promote.signed = false) (hprom : k1.promote = k1)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < (k1.bits : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary op (.int k1 v1) (.int k2 v2) =
      some (.int k1 (if op == .shl then v1 <<< sh else v1 >>> sh), .int k1) := by
  cases k1 <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hs hprom
  all_goals try cases hs
  all_goals try cases hprom
  · unfold evalIntBinary
    have hs32 : IntKind.u32.signed = false := rfl
    rcases hop with rfl | rfl <;>
      (simp only [valAsInt?_int, promote_u32, hs32, Bool.false_eq_true, ↓reduceIte,
        guard, Bool.and_eq_true, decide_eq_true_eq, hlo, hhi, and_self,
        bind, opt_bind_some, pure, Pure.pure, bitVec_ofInt_toNat_self]; rfl)
  · unfold evalIntBinary
    have hs64 : IntKind.u64.signed = false := rfl
    rcases hop with rfl | rfl <;>
      (simp only [valAsInt?_int, promote_u64, hs64, Bool.false_eq_true, ↓reduceIte,
        guard, Bool.and_eq_true, decide_eq_true_eq, hlo, hhi, and_self,
        bind, opt_bind_some, pure, Pure.pure, bitVec_ofInt_toNat_self]; rfl)

theorem evalIntBinary_signed_shl {k1 k2 : IntKind} (hs : k1.promote.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ (if k1.signed then v1.toInt else (v1.toNat : Int)))
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < (k1.promote.bits : Int))
    (hr : k1.promote.inRange
      ((if k1.signed then v1.toInt else (v1.toNat : Int)) *
       (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true) :
    let i1 := if k1.signed then v1.toInt else (v1.toNat : Int)
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int k1 v1) (.int k2 v2) =
      some (.int k1.promote (BitVec.ofInt k1.promote.bits (i1 * (2 ^ sh : Int))), .int k1.promote) := by
  unfold evalIntBinary
  simp only [valAsInt?_int, guard, Bool.and_eq_true, decide_eq_true_eq, hlo, hhi, and_self,
    ↓reduceIte, hs, h1, beq_self_eq_true, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_signed_shr {k1 k2 : IntKind} (hs : k1.promote.signed = true)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ (if k1.signed then v1.toInt else (v1.toNat : Int)))
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < (k1.promote.bits : Int))
    (hr : k1.promote.inRange
      ((if k1.signed then v1.toInt else (v1.toNat : Int)) /
       (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true) :
    let i1 := if k1.signed then v1.toInt else (v1.toNat : Int)
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int k1 v1) (.int k2 v2) =
      some (.int k1.promote (BitVec.ofInt k1.promote.bits (i1 / (2 ^ sh : Int))), .int k1.promote) := by
  unfold evalIntBinary
  have hne : (BinOp.shr == BinOp.shl) = false := rfl
  simp only [valAsInt?_int, guard, Bool.and_eq_true, decide_eq_true_eq, hlo, hhi, and_self,
    ↓reduceIte, hs, h1, hne, Bool.false_eq_true, ofIntExact_signed hs hr,
    bind, opt_bind_some, pure, Pure.pure]

theorem evalIntBinary_cmp_exact (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {k1 k2 ck : IntKind} (hck : IntKind.usualArith k1 k2 = ck)
    (v1 : BitVec k1.bits) (v2 : BitVec k2.bits) :
    let c1 := BitVec.ofInt ck.bits (if k1.signed then v1.toInt else (v1.toNat : Int))
    let c2 := BitVec.ofInt ck.bits (if k2.signed then v2.toInt else (v2.toNat : Int))
    let n1 := if ck.signed then c1.toInt else (c1.toNat : Int)
    let n2 := if ck.signed then c2.toInt else (c2.toNat : Int)
    evalIntBinary op (.int k1 v1) (.int k2 v2) =
      some (.int .i32 (if cmpOrd op n1 n2 then 1 else 0), .int .i32) := by
  subst hck
  exact evalIntBinary_cmp_gen op hop k1 k2 v1 v2

private theorem evalIntBinary_cmp_same_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {k : IntKind} (hck : IntKind.usualArith k k = k) (v1 v2 : BitVec k.bits) :
    evalIntBinary op (.int k v1) (.int k v2) =
      some (.int .i32 (if cmpOrd op
        (if k.signed then v1.toInt else (v1.toNat : Int))
        (if k.signed then v2.toInt else (v2.toNat : Int)) then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop hck v1 v2
  by_cases hs : k.signed
  · simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h ⊢; exact h
  · have hsf : k.signed = false := Bool.eq_false_iff.mpr hs
    simp only [hsf, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h ⊢; exact h

private theorem evalIntBinary_unsigned_same_arith (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    {k : IntKind} (hck : IntKind.usualArith k k = k) (hs : k.signed = false)
    (v1 v2 : BitVec k.bits) :
    evalIntBinary op (.int k v1) (.int k v2) =
      some (.int k (match op with
        | .add => v1 + v2 | .sub => v1 - v2 | .mul => v1 * v2
        | .bitAnd => v1 &&& v2 | .bitOr => v1 ||| v2 | _ => v1 ^^^ v2), .int k) := by
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · have h := evalIntBinary_unsigned_add hck hs v1 v2
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_sub hck hs v1 v2
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_mul hck hs v1 v2
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitAnd_gen hck v1 v2
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitOr_gen hck v1 v2
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitXor_gen hck v1 v2
    simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h

private theorem evalIntBinary_unsigned_same_div {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = false)
    (v1 v2 : BitVec k.bits) (hnz : v2.toNat ≠ 0) :
    evalIntBinary .div (.int k v1) (.int k v2) = some (.int k (v1 / v2), .int k) := by
  have h := evalIntBinary_unsigned_div hck hs v1 v2
    (by simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self]; exact hnz)
  simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h
  exact h

private theorem evalIntBinary_unsigned_same_mod {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = false)
    (v1 v2 : BitVec k.bits) (hnz : v2.toNat ≠ 0) :
    evalIntBinary .mod (.int k v1) (.int k v2) = some (.int k (v1 % v2), .int k) := by
  have h := evalIntBinary_unsigned_mod hck hs v1 v2
    (by simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self]; exact hnz)
  simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h
  exact h

private theorem evalIntBinary_signed_same_add {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = true)
    (v1 v2 : BitVec k.bits) (hr : k.inRange (v1.toInt + v2.toInt) = true) :
    evalIntBinary .add (.int k v1) (.int k v2) = some (.int k (v1 + v2), .int k) := by
  have h := evalIntBinary_signed_add hck hs v1 v2
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [hs, ↓reduceIte, bitVec_ofInt_toInt, bitVec_ofInt_add_eq] at h
  exact h

private theorem evalIntBinary_signed_same_sub {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = true)
    (v1 v2 : BitVec k.bits) (hr : k.inRange (v1.toInt - v2.toInt) = true) :
    evalIntBinary .sub (.int k v1) (.int k v2) = some (.int k (v1 - v2), .int k) := by
  have h := evalIntBinary_signed_sub hck hs v1 v2
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [hs, ↓reduceIte, bitVec_ofInt_toInt, bitVec_ofInt_sub_eq] at h
  exact h

private theorem evalIntBinary_signed_same_mul {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = true)
    (v1 v2 : BitVec k.bits) (hr : k.inRange (v1.toInt * v2.toInt) = true) :
    evalIntBinary .mul (.int k v1) (.int k v2) = some (.int k (v1 * v2), .int k) := by
  have h := evalIntBinary_signed_mul hck hs v1 v2
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [hs, ↓reduceIte, bitVec_ofInt_toInt, bitVec_ofInt_mul_eq] at h
  exact h

private theorem evalIntBinary_signed_same_div {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = true)
    (v1 v2 : BitVec k.bits) (hnz : v2.toInt ≠ 0) (hr : k.inRange (Int.tdiv v1.toInt v2.toInt) = true) :
    evalIntBinary .div (.int k v1) (.int k v2) =
      some (.int k (BitVec.ofInt k.bits (Int.tdiv v1.toInt v2.toInt)), .int k) := by
  have h := evalIntBinary_signed_div hck hs v1 v2
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hnz)
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h
  exact h

private theorem evalIntBinary_signed_same_mod {k : IntKind}
    (hck : IntKind.usualArith k k = k) (hs : k.signed = true)
    (v1 v2 : BitVec k.bits) (hnz : v2.toInt ≠ 0) (hr : k.inRange (Int.tmod v1.toInt v2.toInt) = true) :
    evalIntBinary .mod (.int k v1) (.int k v2) =
      some (.int k (BitVec.ofInt k.bits (Int.tmod v1.toInt v2.toInt)), .int k) := by
  have h := evalIntBinary_signed_mod hck hs v1 v2
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hnz)
    (by simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h
  exact h

private theorem evalIntBinary_signed_same_bitop (op : BinOp)
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    {k : IntKind} (hck : IntKind.usualArith k k = k) (hs : k.signed = true)
    (v1 v2 : BitVec k.bits) :
    evalIntBinary op (.int k v1) (.int k v2) =
      some (.int k (match op with | .bitAnd => v1 &&& v2 | .bitOr => v1 ||| v2 | _ => v1 ^^^ v2), .int k) := by
  rcases hop with rfl | rfl | rfl
  · have h := evalIntBinary_bitAnd_gen hck v1 v2
    simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h; exact h
  · have h := evalIntBinary_bitOr_gen hck v1 v2
    simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h; exact h
  · have h := evalIntBinary_bitXor_gen hck v1 v2
    simp only [hs, ↓reduceIte, bitVec_ofInt_toInt] at h; exact h

private theorem evalIntBinary_shl_signed_same {k1 k2 : IntKind} (hprom : k1.promote = k1)
    (hs : k1.signed = true) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ v1.toInt) (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < (k1.bits : Int))
    (hr : k1.inRange (v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int k1 v1) (.int k2 v2) =
      some (.int k1 (BitVec.ofInt k1.bits (v1.toInt * (2 ^ sh : Int))), .int k1) := by
  cases k1 <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hprom hs
  all_goals try cases hprom
  all_goals try cases hs
  · have h := evalIntBinary_signed_shl (k1 := .i32) (k2 := k2) rfl v1 v2 h1 hlo hhi hr
    simp only [promote_i32] at h; exact h
  · have h := evalIntBinary_signed_shl (k1 := .i64) (k2 := k2) rfl v1 v2 h1 hlo hhi hr
    simp only [promote_i64] at h; exact h

private theorem evalIntBinary_shr_signed_same {k1 k2 : IntKind} (hprom : k1.promote = k1)
    (hs : k1.signed = true) (v1 : BitVec k1.bits) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ v1.toInt) (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < (k1.bits : Int))
    (hr : k1.inRange (v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int k1 v1) (.int k2 v2) =
      some (.int k1 (BitVec.ofInt k1.bits (v1.toInt / (2 ^ sh : Int))), .int k1) := by
  cases k1 <;> simp only [IntKind.promote, IntKind.rank, IntKind.signed] at hprom hs
  all_goals try cases hprom
  all_goals try cases hs
  · have h := evalIntBinary_signed_shr (k1 := .i32) (k2 := k2) rfl v1 v2 h1 hlo hhi hr
    simp only [promote_i32] at h; exact h
  · have h := evalIntBinary_signed_shr (k1 := .i64) (k2 := k2) rfl v1 v2 h1 hlo hhi hr
    simp only [promote_i64] at h; exact h

private theorem i32_inRange_iff (x : Int) :
    IntKind.i32.inRange x = true ↔ -(2 ^ 31 : Int) ≤ x ∧ x < (2 ^ 31 : Int) := by
  have hmin : IntKind.i32.minVal = -(2 ^ 31 : Int) := rfl
  have hmax : IntKind.i32.maxVal = (2 ^ 31 : Int) - 1 := rfl
  simp only [IntKind.inRange, hmin, hmax, Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem i64_inRange_iff (x : Int) :
    IntKind.i64.inRange x = true ↔ -(2 ^ 63 : Int) ≤ x ∧ x < (2 ^ 63 : Int) := by
  have hmin : IntKind.i64.minVal = -(2 ^ 63 : Int) := rfl
  have hmax : IntKind.i64.maxVal = (2 ^ 63 : Int) - 1 := rfl
  simp only [IntKind.inRange, hmin, hmax, Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem u8_bits_lt (v : BitVec IntKind.u8.bits) : v.toNat < 256 := v.isLt
private theorem u16_bits_lt (v : BitVec IntKind.u16.bits) : v.toNat < 65536 := v.isLt

private theorem bv_ofInt_i32_eq_of_range {x : Int}
    (hlo : -(2 ^ 31 : Int) ≤ x) (hhi : x < (2 ^ 31 : Int)) :
    (BitVec.ofInt IntKind.i32.bits x).toInt = x :=
  bitVec_ofInt_toInt_of_range (by decide)
    (by change -(2 ^ 31 : Int) ≤ x; exact hlo)
    (by change x < (2 ^ 31 : Int); exact hhi)

private theorem bv_ofInt_i64_eq_of_range {x : Int}
    (hlo : -(2 ^ 63 : Int) ≤ x) (hhi : x < (2 ^ 63 : Int)) :
    (BitVec.ofInt IntKind.i64.bits x).toInt = x :=
  bitVec_ofInt_toInt_of_range (by decide)
    (by change -(2 ^ 63 : Int) ≤ x; exact hlo)
    (by change x < (2 ^ 63 : Int); exact hhi)

/-! #### Fast Specialized `evalIntBinary` Lemmas for Common Kinds & Mixed Literal Cases -/

theorem evalIntBinary_cmp_i32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 32) :
    evalIntBinary op (.int .i32 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op v1.toInt v2.toInt then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_same_bits op hop (k := .i32) rfl v1 v2
  simp only [IntKind.signed, ↓reduceIte] at h
  exact h

theorem evalIntBinary_cmp_u32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 32) :
    evalIntBinary op (.int .u32 v1) (.int .u32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) (v2.toNat : Int) then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_same_bits op hop (k := .u32) rfl v1 v2
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
  exact h

theorem evalIntBinary_cmp_i64 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 64) :
    evalIntBinary op (.int .i64 v1) (.int .i64 v2) =
      some (.int .i32 (if cmpOrd op v1.toInt v2.toInt then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_same_bits op hop (k := .i64) rfl v1 v2
  simp only [IntKind.signed, ↓reduceIte] at h
  exact h

theorem evalIntBinary_cmp_u64 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 64) :
    evalIntBinary op (.int .u64 v1) (.int .u64 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) (v2.toNat : Int) then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_same_bits op hop (k := .u64) rfl v1 v2
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
  exact h

theorem evalIntBinary_add_u32 (v1 v2 : BitVec 32) :
    evalIntBinary .add (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 + v2), .int .u32) :=
  evalIntBinary_unsigned_same_arith .add (Or.inl rfl) (k := .u32) rfl rfl v1 v2

theorem evalIntBinary_sub_u32 (v1 v2 : BitVec 32) :
    evalIntBinary .sub (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 - v2), .int .u32) :=
  evalIntBinary_unsigned_same_arith .sub (Or.inr (Or.inl rfl)) (k := .u32) rfl rfl v1 v2

theorem evalIntBinary_mul_u32 (v1 v2 : BitVec 32) :
    evalIntBinary .mul (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 * v2), .int .u32) :=
  evalIntBinary_unsigned_same_arith .mul (Or.inr (Or.inr (Or.inl rfl))) (k := .u32) rfl rfl v1 v2

theorem evalIntBinary_div_u32 (v1 v2 : BitVec 32) (hnz : v2.toNat ≠ 0) :
    evalIntBinary .div (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 / v2), .int .u32) :=
  evalIntBinary_unsigned_same_div (k := .u32) rfl rfl v1 v2 hnz

theorem evalIntBinary_mod_u32 (v1 v2 : BitVec 32) (hnz : v2.toNat ≠ 0) :
    evalIntBinary .mod (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 % v2), .int .u32) :=
  evalIntBinary_unsigned_same_mod (k := .u32) rfl rfl v1 v2 hnz

theorem evalIntBinary_bitAnd_u32 (v1 v2 : BitVec 32) :
    evalIntBinary .bitAnd (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 &&& v2), .int .u32) :=
  evalIntBinary_unsigned_same_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (k := .u32) rfl rfl v1 v2

theorem evalIntBinary_bitOr_u32 (v1 v2 : BitVec 32) :
    evalIntBinary .bitOr (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 ||| v2), .int .u32) :=
  evalIntBinary_unsigned_same_arith .bitOr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (k := .u32) rfl rfl v1 v2

theorem evalIntBinary_bitXor_u32 (v1 v2 : BitVec 32) :
    evalIntBinary .bitXor (.int .u32 v1) (.int .u32 v2) = some (.int .u32 (v1 ^^^ v2), .int .u32) :=
  evalIntBinary_unsigned_same_arith .bitXor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (k := .u32) rfl rfl v1 v2

theorem evalIntBinary_add_u64 (v1 v2 : BitVec 64) :
    evalIntBinary .add (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 + v2), .int .u64) :=
  evalIntBinary_unsigned_same_arith .add (Or.inl rfl) (k := .u64) rfl rfl v1 v2

theorem evalIntBinary_sub_u64 (v1 v2 : BitVec 64) :
    evalIntBinary .sub (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 - v2), .int .u64) :=
  evalIntBinary_unsigned_same_arith .sub (Or.inr (Or.inl rfl)) (k := .u64) rfl rfl v1 v2

theorem evalIntBinary_mul_u64 (v1 v2 : BitVec 64) :
    evalIntBinary .mul (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 * v2), .int .u64) :=
  evalIntBinary_unsigned_same_arith .mul (Or.inr (Or.inr (Or.inl rfl))) (k := .u64) rfl rfl v1 v2

theorem evalIntBinary_div_u64 (v1 v2 : BitVec 64) (hnz : v2.toNat ≠ 0) :
    evalIntBinary .div (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 / v2), .int .u64) :=
  evalIntBinary_unsigned_same_div (k := .u64) rfl rfl v1 v2 hnz

theorem evalIntBinary_mod_u64 (v1 v2 : BitVec 64) (hnz : v2.toNat ≠ 0) :
    evalIntBinary .mod (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 % v2), .int .u64) :=
  evalIntBinary_unsigned_same_mod (k := .u64) rfl rfl v1 v2 hnz

theorem evalIntBinary_bitAnd_u64 (v1 v2 : BitVec 64) :
    evalIntBinary .bitAnd (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 &&& v2), .int .u64) :=
  evalIntBinary_unsigned_same_arith .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (k := .u64) rfl rfl v1 v2

theorem evalIntBinary_bitOr_u64 (v1 v2 : BitVec 64) :
    evalIntBinary .bitOr (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 ||| v2), .int .u64) :=
  evalIntBinary_unsigned_same_arith .bitOr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (k := .u64) rfl rfl v1 v2

theorem evalIntBinary_bitXor_u64 (v1 v2 : BitVec 64) :
    evalIntBinary .bitXor (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 ^^^ v2), .int .u64) :=
  evalIntBinary_unsigned_same_arith .bitXor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (k := .u64) rfl rfl v1 v2

theorem evalIntBinary_add_i32 (v1 v2 : BitVec 32)
    (hlo : -(2 ^ 31 : Int) ≤ v1.toInt + v2.toInt) (hhi : v1.toInt + v2.toInt < (2 ^ 31 : Int)) :
    evalIntBinary .add (.int .i32 v1) (.int .i32 v2) = some (.int .i32 (v1 + v2), .int .i32) := by
  have hr : IntKind.i32.inRange (v1.toInt + v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalIntBinary_signed_same_add (k := .i32) rfl rfl v1 v2 hr

theorem evalIntBinary_sub_i32 (v1 v2 : BitVec 32)
    (hlo : -(2 ^ 31 : Int) ≤ v1.toInt - v2.toInt) (hhi : v1.toInt - v2.toInt < (2 ^ 31 : Int)) :
    evalIntBinary .sub (.int .i32 v1) (.int .i32 v2) = some (.int .i32 (v1 - v2), .int .i32) := by
  have hr : IntKind.i32.inRange (v1.toInt - v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalIntBinary_signed_same_sub (k := .i32) rfl rfl v1 v2 hr

theorem evalIntBinary_mul_i32 (v1 v2 : BitVec 32)
    (hlo : -(2 ^ 31 : Int) ≤ v1.toInt * v2.toInt) (hhi : v1.toInt * v2.toInt < (2 ^ 31 : Int)) :
    evalIntBinary .mul (.int .i32 v1) (.int .i32 v2) = some (.int .i32 (v1 * v2), .int .i32) := by
  have hr : IntKind.i32.inRange (v1.toInt * v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalIntBinary_signed_same_mul (k := .i32) rfl rfl v1 v2 hr

theorem evalIntBinary_div_i32 (v1 v2 : BitVec 32) (hnz : v2.toInt ≠ 0)
    (hno : ¬ (v1.toInt = -(2 ^ 31 : Int) ∧ v2.toInt = -1)) :
    evalIntBinary .div (.int .i32 v1) (.int .i32 v2) =
      some (.int .i32 (BitVec.ofInt 32 (Int.tdiv v1.toInt v2.toInt)), .int .i32) := by
  have h1lo : -(2 ^ 31 : Int) ≤ v1.toInt := BitVec.le_toInt v1
  have h1hi : v1.toInt ≤ (2 ^ 31 : Int) - 1 := by have := BitVec.toInt_lt (x := v1); omega
  have hbound : -(2 ^ 31 : Int) ≤ Int.tdiv v1.toInt v2.toInt ∧
      Int.tdiv v1.toInt v2.toInt ≤ (2 ^ 31 : Int) - 1 := by
    by_cases h1 : v2.toInt = 1
    · rw [h1, Int.tdiv_one]; exact ⟨h1lo, h1hi⟩
    · by_cases hm1 : v2.toInt = -1
      · rw [hm1, Int.tdiv_neg, Int.tdiv_one]; omega
      · have h2ge : 2 ≤ v2.toInt.natAbs := by omega
        have hlt : (Int.tdiv v1.toInt v2.toInt).natAbs ≤ v1.toInt.natAbs / 2 := by
          rw [Int.natAbs_tdiv]; exact Nat.div_le_div_left h2ge (by decide)
        have h1abs : v1.toInt.natAbs ≤ 2 ^ 31 := by omega
        have hhalf : (Int.tdiv v1.toInt v2.toInt).natAbs ≤ 2 ^ 30 := by omega
        omega
  have hr : IntKind.i32.inRange (Int.tdiv v1.toInt v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    exact hbound
  rw [evalIntBinary_signed_same_div (k := .i32) rfl rfl v1 v2 hnz hr]
  exact some_val_int_i32 rfl

theorem evalIntBinary_mod_i32 (v1 v2 : BitVec 32) (hnz : v2.toInt ≠ 0) :
    evalIntBinary .mod (.int .i32 v1) (.int .i32 v2) =
      some (.int .i32 (BitVec.ofInt 32 (Int.tmod v1.toInt v2.toInt)), .int .i32) := by
  have h2lo : -(2 ^ 31 : Int) ≤ v2.toInt := BitVec.le_toInt v2
  have h2hi : v2.toInt ≤ (2 ^ 31 : Int) - 1 := by have := BitVec.toInt_lt (x := v2); omega
  have hbound : -(2 ^ 31 : Int) ≤ Int.tmod v1.toInt v2.toInt ∧
      Int.tmod v1.toInt v2.toInt ≤ (2 ^ 31 : Int) - 1 := by
    by_cases hm1 : v2.toInt = -1
    · rw [hm1, Int.tmod_neg, Int.tmod_one]; omega
    · have habs : (Int.tmod v1.toInt v2.toInt).natAbs < v2.toInt.natAbs := by
        rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hnz)
      have hv2abs : v2.toInt.natAbs ≤ 2 ^ 31 := by omega
      omega
  have hr : IntKind.i32.inRange (Int.tmod v1.toInt v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    exact hbound
  rw [evalIntBinary_signed_same_mod (k := .i32) rfl rfl v1 v2 hnz hr]
  exact some_val_int_i32 rfl

theorem evalIntBinary_bitAnd_i32 (v1 v2 : BitVec 32) :
    evalIntBinary .bitAnd (.int .i32 v1) (.int .i32 v2) = some (.int .i32 (v1 &&& v2), .int .i32) :=
  evalIntBinary_signed_same_bitop .bitAnd (Or.inl rfl) (k := .i32) rfl rfl v1 v2

theorem evalIntBinary_bitOr_i32 (v1 v2 : BitVec 32) :
    evalIntBinary .bitOr (.int .i32 v1) (.int .i32 v2) = some (.int .i32 (v1 ||| v2), .int .i32) :=
  evalIntBinary_signed_same_bitop .bitOr (Or.inr (Or.inl rfl)) (k := .i32) rfl rfl v1 v2

theorem evalIntBinary_bitXor_i32 (v1 v2 : BitVec 32) :
    evalIntBinary .bitXor (.int .i32 v1) (.int .i32 v2) = some (.int .i32 (v1 ^^^ v2), .int .i32) :=
  evalIntBinary_signed_same_bitop .bitXor (Or.inr (Or.inr rfl)) (k := .i32) rfl rfl v1 v2

theorem evalIntBinary_add_i64 (v1 v2 : BitVec 64)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt + v2.toInt) (hhi : v1.toInt + v2.toInt < (2 ^ 63 : Int)) :
    evalIntBinary .add (.int .i64 v1) (.int .i64 v2) = some (.int .i64 (v1 + v2), .int .i64) := by
  have hr : IntKind.i64.inRange (v1.toInt + v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalIntBinary_signed_same_add (k := .i64) rfl rfl v1 v2 hr

theorem evalIntBinary_sub_i64 (v1 v2 : BitVec 64)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt - v2.toInt) (hhi : v1.toInt - v2.toInt < (2 ^ 63 : Int)) :
    evalIntBinary .sub (.int .i64 v1) (.int .i64 v2) = some (.int .i64 (v1 - v2), .int .i64) := by
  have hr : IntKind.i64.inRange (v1.toInt - v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalIntBinary_signed_same_sub (k := .i64) rfl rfl v1 v2 hr

theorem evalIntBinary_mul_i64 (v1 v2 : BitVec 64)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt * v2.toInt) (hhi : v1.toInt * v2.toInt < (2 ^ 63 : Int)) :
    evalIntBinary .mul (.int .i64 v1) (.int .i64 v2) = some (.int .i64 (v1 * v2), .int .i64) := by
  have hr : IntKind.i64.inRange (v1.toInt * v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  exact evalIntBinary_signed_same_mul (k := .i64) rfl rfl v1 v2 hr

theorem evalIntBinary_div_i64 (v1 v2 : BitVec 64) (hnz : v2.toInt ≠ 0)
    (hno : ¬ (v1.toInt = -(2 ^ 63 : Int) ∧ v2.toInt = -1)) :
    evalIntBinary .div (.int .i64 v1) (.int .i64 v2) =
      some (.int .i64 (BitVec.ofInt 64 (Int.tdiv v1.toInt v2.toInt)), .int .i64) := by
  have h1lo : -(2 ^ 63 : Int) ≤ v1.toInt := BitVec.le_toInt v1
  have h1hi : v1.toInt ≤ (2 ^ 63 : Int) - 1 := by have := BitVec.toInt_lt (x := v1); omega
  have hbound : -(2 ^ 63 : Int) ≤ Int.tdiv v1.toInt v2.toInt ∧
      Int.tdiv v1.toInt v2.toInt ≤ (2 ^ 63 : Int) - 1 := by
    by_cases h1 : v2.toInt = 1
    · rw [h1, Int.tdiv_one]; exact ⟨h1lo, h1hi⟩
    · by_cases hm1 : v2.toInt = -1
      · rw [hm1, Int.tdiv_neg, Int.tdiv_one]; omega
      · have h2ge : 2 ≤ v2.toInt.natAbs := by omega
        have hlt : (Int.tdiv v1.toInt v2.toInt).natAbs ≤ v1.toInt.natAbs / 2 := by
          rw [Int.natAbs_tdiv]; exact Nat.div_le_div_left h2ge (by decide)
        have h1abs : v1.toInt.natAbs ≤ 2 ^ 63 := by omega
        have hhalf : (Int.tdiv v1.toInt v2.toInt).natAbs ≤ 2 ^ 62 := by omega
        omega
  have hr : IntKind.i64.inRange (Int.tdiv v1.toInt v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    exact hbound
  rw [evalIntBinary_signed_same_div (k := .i64) rfl rfl v1 v2 hnz hr]
  exact some_val_int_i64 rfl

theorem evalIntBinary_mod_i64 (v1 v2 : BitVec 64) (hnz : v2.toInt ≠ 0) :
    evalIntBinary .mod (.int .i64 v1) (.int .i64 v2) =
      some (.int .i64 (BitVec.ofInt 64 (Int.tmod v1.toInt v2.toInt)), .int .i64) := by
  have h2lo : -(2 ^ 63 : Int) ≤ v2.toInt := BitVec.le_toInt v2
  have h2hi : v2.toInt ≤ (2 ^ 63 : Int) - 1 := by have := BitVec.toInt_lt (x := v2); omega
  have hbound : -(2 ^ 63 : Int) ≤ Int.tmod v1.toInt v2.toInt ∧
      Int.tmod v1.toInt v2.toInt ≤ (2 ^ 63 : Int) - 1 := by
    by_cases hm1 : v2.toInt = -1
    · rw [hm1, Int.tmod_neg, Int.tmod_one]; omega
    · have habs : (Int.tmod v1.toInt v2.toInt).natAbs < v2.toInt.natAbs := by
        rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hnz)
      have hv2abs : v2.toInt.natAbs ≤ 2 ^ 63 := by omega
      omega
  have hr : IntKind.i64.inRange (Int.tmod v1.toInt v2.toInt) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    exact hbound
  rw [evalIntBinary_signed_same_mod (k := .i64) rfl rfl v1 v2 hnz hr]
  exact some_val_int_i64 rfl

theorem evalIntBinary_bitAnd_i64 (v1 v2 : BitVec 64) :
    evalIntBinary .bitAnd (.int .i64 v1) (.int .i64 v2) = some (.int .i64 (v1 &&& v2), .int .i64) :=
  evalIntBinary_signed_same_bitop .bitAnd (Or.inl rfl) (k := .i64) rfl rfl v1 v2

theorem evalIntBinary_bitOr_i64 (v1 v2 : BitVec 64) :
    evalIntBinary .bitOr (.int .i64 v1) (.int .i64 v2) = some (.int .i64 (v1 ||| v2), .int .i64) :=
  evalIntBinary_signed_same_bitop .bitOr (Or.inr (Or.inl rfl)) (k := .i64) rfl rfl v1 v2

theorem evalIntBinary_bitXor_i64 (v1 v2 : BitVec 64) :
    evalIntBinary .bitXor (.int .i64 v1) (.int .i64 v2) = some (.int .i64 (v1 ^^^ v2), .int .i64) :=
  evalIntBinary_signed_same_bitop .bitXor (Or.inr (Or.inr rfl)) (k := .i64) rfl rfl v1 v2

theorem evalIntBinary_shl_u32 {k2 : IntKind} (v1 : BitVec 32) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .u32 v1) (.int k2 v2) = some (.int .u32 (v1 <<< sh), .int .u32) := by
  have h := evalIntBinary_unsigned_shift .shl (Or.inl rfl) (k1 := .u32) (k2 := k2) rfl rfl v1 v2 hlo hhi
  simp only [beq_self_eq_true, ↓reduceIte] at h
  rw [h]; exact some_val_int_u32 rfl

theorem evalIntBinary_shr_u32 {k2 : IntKind} (v1 : BitVec 32) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .u32 v1) (.int k2 v2) = some (.int .u32 (v1 >>> sh), .int .u32) := by
  have h := evalIntBinary_unsigned_shift .shr (Or.inr rfl) (k1 := .u32) (k2 := k2) rfl rfl v1 v2 hlo hhi
  have hne : (BinOp.shr == BinOp.shl) = false := rfl
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  rw [h]; exact some_val_int_u32 rfl

theorem evalIntBinary_shl_u64 {k2 : IntKind} (v1 : BitVec 64) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 64) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .u64 v1) (.int k2 v2) = some (.int .u64 (v1 <<< sh), .int .u64) := by
  have h := evalIntBinary_unsigned_shift .shl (Or.inl rfl) (k1 := .u64) (k2 := k2) rfl rfl v1 v2 hlo hhi
  simp only [beq_self_eq_true, ↓reduceIte] at h
  rw [h]; exact some_val_int_u64 rfl

theorem evalIntBinary_shr_u64 {k2 : IntKind} (v1 : BitVec 64) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 64) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .u64 v1) (.int k2 v2) = some (.int .u64 (v1 >>> sh), .int .u64) := by
  have h := evalIntBinary_unsigned_shift .shr (Or.inr rfl) (k1 := .u64) (k2 := k2) rfl rfl v1 v2 hlo hhi
  have hne : (BinOp.shr == BinOp.shl) = false := rfl
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  rw [h]; exact some_val_int_u64 rfl

theorem evalIntBinary_shl_i32 {k2 : IntKind} (v1 : BitVec 32) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ v1.toInt)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32)
    (hr : v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) < (2 ^ 31 : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .i32 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 (v1.toInt * (2 ^ sh : Int))), .int .i32) := by
  have hp : (0 : Int) ≤ 2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat :=
    Int.pow_nonneg (by decide)
  have hm : 0 ≤ v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) :=
    Int.mul_nonneg h1 hp
  have hrange : IntKind.i32.inRange
      (v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i32_inRange_iff _).mpr ⟨by omega, hr⟩
  rw [evalIntBinary_shl_signed_same (k1 := .i32) (k2 := k2) rfl rfl v1 v2 h1 hlo hhi hrange]
  exact some_val_int_i32 rfl

theorem evalIntBinary_shr_i32 {k2 : IntKind} (v1 : BitVec 32) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ v1.toInt)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .i32 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 (v1.toInt / (2 ^ sh : Int))), .int .i32) := by
  have h1hi : v1.toInt < (2 ^ 31 : Int) := BitVec.toInt_lt
  have hdiv : 0 ≤ v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ∧
      v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ≤ v1.toInt :=
    ⟨Int.ediv_nonneg h1 (Int.pow_nonneg (by decide)), Int.ediv_le_self _ h1⟩
  have hrange : IntKind.i32.inRange
      (v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  rw [evalIntBinary_shr_signed_same (k1 := .i32) (k2 := k2) rfl rfl v1 v2 h1 hlo hhi hrange]
  exact some_val_int_i32 rfl

theorem evalIntBinary_shl_i64 {k2 : IntKind} (v1 : BitVec 64) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ v1.toInt)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 64)
    (hr : v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) < (2 ^ 63 : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .i64 v1) (.int k2 v2) =
      some (.int .i64 (BitVec.ofInt 64 (v1.toInt * (2 ^ sh : Int))), .int .i64) := by
  have hp : (0 : Int) ≤ 2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat :=
    Int.pow_nonneg (by decide)
  have hm : 0 ≤ v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) :=
    Int.mul_nonneg h1 hp
  have hrange : IntKind.i64.inRange
      (v1.toInt * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i64_inRange_iff _).mpr ⟨by omega, hr⟩
  rw [evalIntBinary_shl_signed_same (k1 := .i64) (k2 := k2) rfl rfl v1 v2 h1 hlo hhi hrange]
  exact some_val_int_i64 rfl

theorem evalIntBinary_shr_i64 {k2 : IntKind} (v1 : BitVec 64) (v2 : BitVec k2.bits)
    (h1 : 0 ≤ v1.toInt)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 64) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .i64 v1) (.int k2 v2) =
      some (.int .i64 (BitVec.ofInt 64 (v1.toInt / (2 ^ sh : Int))), .int .i64) := by
  have h1hi : v1.toInt < (2 ^ 63 : Int) := BitVec.toInt_lt
  have hdiv : 0 ≤ v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ∧
      v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ≤ v1.toInt :=
    ⟨Int.ediv_nonneg h1 (Int.pow_nonneg (by decide)), Int.ediv_le_self _ h1⟩
  have hrange : IntKind.i64.inRange
      (v1.toInt / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i64_inRange_iff _).mpr (by omega)
  rw [evalIntBinary_shr_signed_same (k1 := .i64) (k2 := k2) rfl rfl v1 v2 h1 hlo hhi hrange]
  exact some_val_int_i64 rfl

private theorem evalIntBinary_shl_u8_bits {k2 : IntKind} (v1 : BitVec IntKind.u8.bits) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32)
    (hr : (v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) < (2 ^ 31 : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .u8 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) * (2 ^ sh : Int))), .int .i32) := by
  have h1 : (0 : Int) ≤ v1.toNat := Int.natCast_nonneg _
  have hp : (0 : Int) ≤ 2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat :=
    Int.pow_nonneg (by decide)
  have hm : 0 ≤ (v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) :=
    Int.mul_nonneg h1 hp
  have hrange : IntKind.i32.inRange
      ((v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i32_inRange_iff _).mpr ⟨by omega, hr⟩
  have h := evalIntBinary_signed_shl (k1 := .u8) (k2 := k2) rfl v1 v2 h1 hlo hhi hrange
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_shl_u8 {k2 : IntKind} (v1 : BitVec 8) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32)
    (hr : (v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) < (2 ^ 31 : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .u8 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) * (2 ^ sh : Int))), .int .i32) :=
  evalIntBinary_shl_u8_bits v1 v2 hlo hhi hr

private theorem evalIntBinary_shr_u8_bits {k2 : IntKind} (v1 : BitVec IntKind.u8.bits) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .u8 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) / (2 ^ sh : Int))), .int .i32) := by
  have h1 : (0 : Int) ≤ v1.toNat := Int.natCast_nonneg _
  have h1hi : (v1.toNat : Int) < 256 := Int.ofNat_lt.mpr (u8_bits_lt v1)
  have hdiv : 0 ≤ (v1.toNat : Int) / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ∧
      (v1.toNat : Int) / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ≤ v1.toNat :=
    ⟨Int.ediv_nonneg h1 (Int.pow_nonneg (by decide)), Int.ediv_le_self _ h1⟩
  have hrange : IntKind.i32.inRange
      ((v1.toNat : Int) / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_shr (k1 := .u8) (k2 := k2) rfl v1 v2 h1 hlo hhi hrange
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_shr_u8 {k2 : IntKind} (v1 : BitVec 8) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .u8 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) / (2 ^ sh : Int))), .int .i32) :=
  evalIntBinary_shr_u8_bits v1 v2 hlo hhi

private theorem evalIntBinary_shl_u16_bits {k2 : IntKind} (v1 : BitVec IntKind.u16.bits) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32)
    (hr : (v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) < (2 ^ 31 : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .u16 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) * (2 ^ sh : Int))), .int .i32) := by
  have h1 : (0 : Int) ≤ v1.toNat := Int.natCast_nonneg _
  have hp : (0 : Int) ≤ 2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat :=
    Int.pow_nonneg (by decide)
  have hm : 0 ≤ (v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) :=
    Int.mul_nonneg h1 hp
  have hrange : IntKind.i32.inRange
      ((v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i32_inRange_iff _).mpr ⟨by omega, hr⟩
  have h := evalIntBinary_signed_shl (k1 := .u16) (k2 := k2) rfl v1 v2 h1 hlo hhi hrange
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_shl_u16 {k2 : IntKind} (v1 : BitVec 16) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32)
    (hr : (v1.toNat : Int) * (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) < (2 ^ 31 : Int)) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shl (.int .u16 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) * (2 ^ sh : Int))), .int .i32) :=
  evalIntBinary_shl_u16_bits v1 v2 hlo hhi hr

private theorem evalIntBinary_shr_u16_bits {k2 : IntKind} (v1 : BitVec IntKind.u16.bits) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .u16 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) / (2 ^ sh : Int))), .int .i32) := by
  have h1 : (0 : Int) ≤ v1.toNat := Int.natCast_nonneg _
  have h1hi : (v1.toNat : Int) < 65536 := Int.ofNat_lt.mpr (u16_bits_lt v1)
  have hdiv : 0 ≤ (v1.toNat : Int) / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ∧
      (v1.toNat : Int) / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int) ≤ v1.toNat :=
    ⟨Int.ediv_nonneg h1 (Int.pow_nonneg (by decide)), Int.ediv_le_self _ h1⟩
  have hrange : IntKind.i32.inRange
      ((v1.toNat : Int) / (2 ^ (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_shr (k1 := .u16) (k2 := k2) rfl v1 v2 h1 hlo hhi hrange
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_shr_u16 {k2 : IntKind} (v1 : BitVec 16) (v2 : BitVec k2.bits)
    (hlo : 0 ≤ (if k2.signed then v2.toInt else (v2.toNat : Int)))
    (hhi : (if k2.signed then v2.toInt else (v2.toNat : Int)) < 32) :
    let sh := (if k2.signed then v2.toInt else (v2.toNat : Int)).toNat
    evalIntBinary .shr (.int .u16 v1) (.int k2 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) / (2 ^ sh : Int))), .int .i32) :=
  evalIntBinary_shr_u16_bits v1 v2 hlo hhi

/-! #### Mixed-Width `evalIntBinary` Lemmas (`u64`/`u32`/`i64` with `i32`, `u8`/`u16` with `u8`/`u16`/`i32`) -/

private theorem evalIntBinary_cmp_u64_i32_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec IntKind.u64.bits) (v2 : BitVec IntKind.i32.bits) :
    let n2 := ((BitVec.ofInt 64 v2.toInt).toNat : Int)
    evalIntBinary op (.int .u64 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) n2 then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .u64) (k2 := .i32) (ck := .u64) rfl v1 v2
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h
  exact h

theorem evalIntBinary_cmp_u64_i32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec 64) (v2 : BitVec 32) :
    let n2 := ((BitVec.ofInt 64 v2.toInt).toNat : Int)
    evalIntBinary op (.int .u64 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) n2 then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_u64_i32_bits op hop v1 v2

private theorem evalIntBinary_cmp_u32_i32_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec IntKind.u32.bits) (v2 : BitVec IntKind.i32.bits) :
    let n2 := ((BitVec.ofInt 32 v2.toInt).toNat : Int)
    evalIntBinary op (.int .u32 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) n2 then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .u32) (k2 := .i32) (ck := .u32) rfl v1 v2
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h
  exact h

theorem evalIntBinary_cmp_u32_i32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 32) :
    let n2 := ((BitVec.ofInt 32 v2.toInt).toNat : Int)
    evalIntBinary op (.int .u32 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) n2 then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_u32_i32_bits op hop v1 v2

private theorem evalIntBinary_cmp_i64_i32_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec IntKind.i64.bits) (v2 : BitVec IntKind.i32.bits) :
    evalIntBinary op (.int .i64 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op v1.toInt (BitVec.ofInt 64 v2.toInt).toInt then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .i64) (k2 := .i32) (ck := .i64) rfl v1 v2
  simp only [IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt] at h
  exact h

theorem evalIntBinary_cmp_i64_i32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec 64) (v2 : BitVec 32) :
    evalIntBinary op (.int .i64 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op v1.toInt (BitVec.ofInt 64 v2.toInt).toInt then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_i64_i32_bits op hop v1 v2

private theorem evalIntBinary_cmp_u8_i32_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec IntKind.u8.bits) (v2 : BitVec IntKind.i32.bits) :
    evalIntBinary op (.int .u8 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) v2.toInt then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .u8) (k2 := .i32) (ck := .i32) rfl v1 v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by have := u8_bits_lt v1; omega)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, bitVec_ofInt_toInt] at h
  exact h

theorem evalIntBinary_cmp_u8_i32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec 8) (v2 : BitVec 32) :
    evalIntBinary op (.int .u8 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) v2.toInt then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_u8_i32_bits op hop v1 v2

private theorem evalIntBinary_cmp_u16_i32_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec IntKind.u16.bits) (v2 : BitVec IntKind.i32.bits) :
    evalIntBinary op (.int .u16 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) v2.toInt then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .u16) (k2 := .i32) (ck := .i32) rfl v1 v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by have := u16_bits_lt v1; omega)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, bitVec_ofInt_toInt] at h
  exact h

theorem evalIntBinary_cmp_u16_i32 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 : BitVec 16) (v2 : BitVec 32) :
    evalIntBinary op (.int .u16 v1) (.int .i32 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) v2.toInt then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_u16_i32_bits op hop v1 v2

private theorem evalIntBinary_cmp_u8_u8_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec IntKind.u8.bits) :
    evalIntBinary op (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) (v2.toNat : Int) then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .u8) (k2 := .u8) (ck := .i32) rfl v1 v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by have := u8_bits_lt v1; omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by have := u8_bits_lt v2; omega)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  exact h

theorem evalIntBinary_cmp_u8_u8 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 8) :
    evalIntBinary op (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) (v2.toNat : Int) then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_u8_u8_bits op hop v1 v2

private theorem evalIntBinary_cmp_u16_u16_bits (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec IntKind.u16.bits) :
    evalIntBinary op (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) (v2.toNat : Int) then 1 else 0), .int .i32) := by
  have h := evalIntBinary_cmp_exact op hop (k1 := .u16) (k2 := .u16) (ck := .i32) rfl v1 v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by have := u16_bits_lt v1; omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by have := u16_bits_lt v2; omega)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  exact h

theorem evalIntBinary_cmp_u16_u16 (op : BinOp)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (v1 v2 : BitVec 16) :
    evalIntBinary op (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (if cmpOrd op (v1.toNat : Int) (v2.toNat : Int) then 1 else 0), .int .i32) :=
  evalIntBinary_cmp_u16_u16_bits op hop v1 v2

private theorem evalIntBinary_u64_i32_arith_bits (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 : BitVec IntKind.u64.bits) (v2 : BitVec IntKind.i32.bits) :
    let v2' : BitVec IntKind.u64.bits := BitVec.ofInt IntKind.u64.bits v2.toInt
    evalIntBinary op (.int .u64 v1) (.int .i32 v2) =
      some (.int .u64 (match op with
        | .add => v1 + v2' | .sub => v1 - v2' | .mul => v1 * v2'
        | .bitAnd => v1 &&& v2' | .bitOr => v1 ||| v2' | _ => v1 ^^^ v2'), .int .u64) := by
  have hck : IntKind.usualArith .u64 .i32 = .u64 := rfl
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · have h := evalIntBinary_unsigned_add hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_sub hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_mul hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitAnd_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitOr_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitXor_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h

theorem evalIntBinary_u64_i32_arith (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 : BitVec 64) (v2 : BitVec 32) :
    let v2' := BitVec.ofInt 64 v2.toInt
    evalIntBinary op (.int .u64 v1) (.int .i32 v2) =
      some (.int .u64 (match op with
        | .add => v1 + v2' | .sub => v1 - v2' | .mul => v1 * v2'
        | .bitAnd => v1 &&& v2' | .bitOr => v1 ||| v2' | _ => v1 ^^^ v2'), .int .u64) :=
  evalIntBinary_u64_i32_arith_bits op hop v1 v2

private theorem evalIntBinary_u32_i32_arith_bits (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 : BitVec IntKind.u32.bits) (v2 : BitVec IntKind.i32.bits) :
    let v2' : BitVec IntKind.u32.bits := BitVec.ofInt IntKind.u32.bits v2.toInt
    evalIntBinary op (.int .u32 v1) (.int .i32 v2) =
      some (.int .u32 (match op with
        | .add => v1 + v2' | .sub => v1 - v2' | .mul => v1 * v2'
        | .bitAnd => v1 &&& v2' | .bitOr => v1 ||| v2' | _ => v1 ^^^ v2'), .int .u32) := by
  have hck : IntKind.usualArith .u32 .i32 = .u32 := rfl
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · have h := evalIntBinary_unsigned_add hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_sub hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_mul hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitAnd_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitOr_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitXor_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h

theorem evalIntBinary_u32_i32_arith (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 v2 : BitVec 32) :
    evalIntBinary op (.int .u32 v1) (.int .i32 v2) =
      some (.int .u32 (match op with
        | .add => v1 + v2 | .sub => v1 - v2 | .mul => v1 * v2
        | .bitAnd => v1 &&& v2 | .bitOr => v1 ||| v2 | _ => v1 ^^^ v2), .int .u32) := by
  have hv2 : (BitVec.ofInt IntKind.u32.bits (@BitVec.toInt IntKind.i32.bits v2) : BitVec 32) = v2 :=
    BitVec.ofInt_toInt
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [evalIntBinary_u32_i32_arith_bits .add (Or.inl rfl) v1 v2]
    exact some_val_int_u32 (congrArg (v1 + ·) hv2)
  · rw [evalIntBinary_u32_i32_arith_bits .sub (Or.inr (Or.inl rfl)) v1 v2]
    exact some_val_int_u32 (congrArg (v1 - ·) hv2)
  · rw [evalIntBinary_u32_i32_arith_bits .mul (Or.inr (Or.inr (Or.inl rfl))) v1 v2]
    exact some_val_int_u32 (congrArg (v1 * ·) hv2)
  · rw [evalIntBinary_u32_i32_arith_bits .bitAnd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) v1 v2]
    exact some_val_int_u32 (congrArg (v1 &&& ·) hv2)
  · rw [evalIntBinary_u32_i32_arith_bits .bitOr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) v1 v2]
    exact some_val_int_u32 (congrArg (v1 ||| ·) hv2)
  · rw [evalIntBinary_u32_i32_arith_bits .bitXor (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) v1 v2]
    exact some_val_int_u32 (congrArg (v1 ^^^ ·) hv2)

private theorem evalIntBinary_u64_u32_arith_bits (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 : BitVec IntKind.u64.bits) (v2 : BitVec IntKind.u32.bits) :
    let v2' : BitVec IntKind.u64.bits := BitVec.ofInt IntKind.u64.bits (v2.toNat : Int)
    evalIntBinary op (.int .u64 v1) (.int .u32 v2) =
      some (.int .u64 (match op with
        | .add => v1 + v2' | .sub => v1 - v2' | .mul => v1 * v2'
        | .bitAnd => v1 &&& v2' | .bitOr => v1 ||| v2' | _ => v1 ^^^ v2'), .int .u64) := by
  have hck : IntKind.usualArith .u64 .u32 = .u64 := rfl
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · have h := evalIntBinary_unsigned_add hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_sub hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_unsigned_mul hck rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitAnd_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitOr_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h
  · have h := evalIntBinary_bitXor_gen hck v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self] at h; exact h

theorem evalIntBinary_u64_u32_arith (op : BinOp)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 : BitVec 64) (v2 : BitVec 32) :
    let v2' := BitVec.ofInt 64 (v2.toNat : Int)
    evalIntBinary op (.int .u64 v1) (.int .u32 v2) =
      some (.int .u64 (match op with
        | .add => v1 + v2' | .sub => v1 - v2' | .mul => v1 * v2'
        | .bitAnd => v1 &&& v2' | .bitOr => v1 ||| v2' | _ => v1 ^^^ v2'), .int .u64) :=
  evalIntBinary_u64_u32_arith_bits op hop v1 v2

private theorem evalIntBinary_u8_u8_add_bits (v1 v2 : BitVec IntKind.u8.bits) :
    evalIntBinary .add (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) + (v2.toNat : Int))), .int .i32) := by
  have h1 := u8_bits_lt v1; have h2 := u8_bits_lt v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hr : IntKind.i32.inRange ((v1.toNat : Int) + (v2.toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_add (k1 := .u8) (k2 := .u8) (ck := .i32) rfl rfl v1 v2
    (by simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2]; exact hr)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u8_u8_add (v1 v2 : BitVec 8) :
    evalIntBinary .add (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) + (v2.toNat : Int))), .int .i32) :=
  evalIntBinary_u8_u8_add_bits v1 v2

private theorem evalIntBinary_u8_u8_sub_bits (v1 v2 : BitVec IntKind.u8.bits) :
    evalIntBinary .sub (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) - (v2.toNat : Int))), .int .i32) := by
  have h1 := u8_bits_lt v1; have h2 := u8_bits_lt v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hr : IntKind.i32.inRange ((v1.toNat : Int) - (v2.toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_sub (k1 := .u8) (k2 := .u8) (ck := .i32) rfl rfl v1 v2
    (by simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2]; exact hr)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u8_u8_sub (v1 v2 : BitVec 8) :
    evalIntBinary .sub (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) - (v2.toNat : Int))), .int .i32) :=
  evalIntBinary_u8_u8_sub_bits v1 v2

private theorem evalIntBinary_u8_u8_mul_bits (v1 v2 : BitVec IntKind.u8.bits) :
    evalIntBinary .mul (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) * (v2.toNat : Int))), .int .i32) := by
  have h1 := u8_bits_lt v1; have h2 := u8_bits_lt v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hm : v1.toNat * v2.toNat ≤ 255 * 255 := Nat.mul_le_mul (Nat.le_of_lt_succ h1) (Nat.le_of_lt_succ h2)
  have hm_int : (v1.toNat : Int) * (v2.toNat : Int) ≤ 255 * 255 := by
    rw [← Int.natCast_mul]
    exact Int.ofNat_le.mpr hm
  have h0 : (0 : Int) ≤ (v1.toNat : Int) * (v2.toNat : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hr : IntKind.i32.inRange ((v1.toNat : Int) * (v2.toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_mul (k1 := .u8) (k2 := .u8) (ck := .i32) rfl rfl v1 v2
    (by simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2]; exact hr)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u8_u8_mul (v1 v2 : BitVec 8) :
    evalIntBinary .mul (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) * (v2.toNat : Int))), .int .i32) :=
  evalIntBinary_u8_u8_mul_bits v1 v2

private theorem evalIntBinary_u8_u8_bitop_bits (op : BinOp)
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 v2 : BitVec IntKind.u8.bits) :
    let c1 := BitVec.ofInt 32 (v1.toNat : Int)
    let c2 := BitVec.ofInt 32 (v2.toNat : Int)
    evalIntBinary op (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (match op with | .bitAnd => c1 &&& c2 | .bitOr => c1 ||| c2 | _ => c1 ^^^ c2), .int .i32) := by
  rcases hop with rfl | rfl | rfl
  · have h := evalIntBinary_bitAnd_gen (k1 := .u8) (k2 := .u8) (ck := .i32) rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
    rw [h]; exact some_val_int_i32 rfl
  · have h := evalIntBinary_bitOr_gen (k1 := .u8) (k2 := .u8) (ck := .i32) rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
    rw [h]; exact some_val_int_i32 rfl
  · have h := evalIntBinary_bitXor_gen (k1 := .u8) (k2 := .u8) (ck := .i32) rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
    rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u8_u8_bitop (op : BinOp) (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 v2 : BitVec 8) :
    let c1 := BitVec.ofInt 32 (v1.toNat : Int)
    let c2 := BitVec.ofInt 32 (v2.toNat : Int)
    evalIntBinary op (.int .u8 v1) (.int .u8 v2) =
      some (.int .i32 (match op with | .bitAnd => c1 &&& c2 | .bitOr => c1 ||| c2 | _ => c1 ^^^ c2), .int .i32) :=
  evalIntBinary_u8_u8_bitop_bits op hop v1 v2

private theorem evalIntBinary_u16_u16_add_bits (v1 v2 : BitVec IntKind.u16.bits) :
    evalIntBinary .add (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) + (v2.toNat : Int))), .int .i32) := by
  have h1 := u16_bits_lt v1; have h2 := u16_bits_lt v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hr : IntKind.i32.inRange ((v1.toNat : Int) + (v2.toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_add (k1 := .u16) (k2 := .u16) (ck := .i32) rfl rfl v1 v2
    (by simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2]; exact hr)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u16_u16_add (v1 v2 : BitVec 16) :
    evalIntBinary .add (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) + (v2.toNat : Int))), .int .i32) :=
  evalIntBinary_u16_u16_add_bits v1 v2

private theorem evalIntBinary_u16_u16_sub_bits (v1 v2 : BitVec IntKind.u16.bits) :
    evalIntBinary .sub (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) - (v2.toNat : Int))), .int .i32) := by
  have h1 := u16_bits_lt v1; have h2 := u16_bits_lt v2
  have hv1 : (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int)).toInt = (v1.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hv2 : (BitVec.ofInt IntKind.i32.bits (v2.toNat : Int)).toInt = (v2.toNat : Int) :=
    bv_ofInt_i32_eq_of_range (by omega) (by omega)
  have hr : IntKind.i32.inRange ((v1.toNat : Int) - (v2.toNat : Int)) = true :=
    (i32_inRange_iff _).mpr (by omega)
  have h := evalIntBinary_signed_sub (k1 := .u16) (k2 := .u16) (ck := .i32) rfl rfl v1 v2
    (by simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2]; exact hr)
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, hv1, hv2] at h
  rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u16_u16_sub (v1 v2 : BitVec 16) :
    evalIntBinary .sub (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (BitVec.ofInt 32 ((v1.toNat : Int) - (v2.toNat : Int))), .int .i32) :=
  evalIntBinary_u16_u16_sub_bits v1 v2

private theorem evalIntBinary_u16_u16_bitop_bits (op : BinOp)
    (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 v2 : BitVec IntKind.u16.bits) :
    let c1 := BitVec.ofInt 32 (v1.toNat : Int)
    let c2 := BitVec.ofInt 32 (v2.toNat : Int)
    evalIntBinary op (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (match op with | .bitAnd => c1 &&& c2 | .bitOr => c1 ||| c2 | _ => c1 ^^^ c2), .int .i32) := by
  rcases hop with rfl | rfl | rfl
  · have h := evalIntBinary_bitAnd_gen (k1 := .u16) (k2 := .u16) (ck := .i32) rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
    rw [h]; exact some_val_int_i32 rfl
  · have h := evalIntBinary_bitOr_gen (k1 := .u16) (k2 := .u16) (ck := .i32) rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
    rw [h]; exact some_val_int_i32 rfl
  · have h := evalIntBinary_bitXor_gen (k1 := .u16) (k2 := .u16) (ck := .i32) rfl v1 v2
    simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
    rw [h]; exact some_val_int_i32 rfl

theorem evalIntBinary_u16_u16_bitop (op : BinOp) (hop : op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor)
    (v1 v2 : BitVec 16) :
    let c1 := BitVec.ofInt 32 (v1.toNat : Int)
    let c2 := BitVec.ofInt 32 (v2.toNat : Int)
    evalIntBinary op (.int .u16 v1) (.int .u16 v2) =
      some (.int .i32 (match op with | .bitAnd => c1 &&& c2 | .bitOr => c1 ||| c2 | _ => c1 ^^^ c2), .int .i32) :=
  evalIntBinary_u16_u16_bitop_bits op hop v1 v2

private theorem evalIntBinary_u8_i32_bitAnd_bits
    (v1 : BitVec IntKind.u8.bits) (v2 : BitVec IntKind.i32.bits) :
    evalIntBinary .bitAnd (.int .u8 v1) (.int .i32 v2) =
      some (.int .i32 (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int) &&& v2), .int .i32) := by
  have h := evalIntBinary_bitAnd_gen (k1 := .u8) (k2 := .i32) (ck := .i32) rfl v1 v2
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toInt] at h
  exact h

theorem evalIntBinary_u8_i32_bitAnd (v1 : BitVec 8) (v2 : BitVec 32) :
    evalIntBinary .bitAnd (.int .u8 v1) (.int .i32 v2) =
      some (.int .i32 (BitVec.ofInt 32 (v1.toNat : Int) &&& v2), .int .i32) := by
  rw [evalIntBinary_u8_i32_bitAnd_bits v1 v2]
  exact some_val_int_i32 rfl

private theorem evalIntBinary_u16_i32_bitAnd_bits
    (v1 : BitVec IntKind.u16.bits) (v2 : BitVec IntKind.i32.bits) :
    evalIntBinary .bitAnd (.int .u16 v1) (.int .i32 v2) =
      some (.int .i32 (BitVec.ofInt IntKind.i32.bits (v1.toNat : Int) &&& v2), .int .i32) := by
  have h := evalIntBinary_bitAnd_gen (k1 := .u16) (k2 := .i32) (ck := .i32) rfl v1 v2
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toInt] at h
  exact h

theorem evalIntBinary_u16_i32_bitAnd (v1 : BitVec 16) (v2 : BitVec 32) :
    evalIntBinary .bitAnd (.int .u16 v1) (.int .i32 v2) =
      some (.int .i32 (BitVec.ofInt 32 (v1.toNat : Int) &&& v2), .int .i32) := by
  rw [evalIntBinary_u16_i32_bitAnd_bits v1 v2]
  exact some_val_int_i32 rfl

private theorem evalIntBinary_i64_i32_add_bits
    (v1 : BitVec IntKind.i64.bits) (v2 : BitVec IntKind.i32.bits)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt + v2.toInt) (hhi : v1.toInt + v2.toInt < (2 ^ 63 : Int)) :
    let v2' : BitVec IntKind.i64.bits := BitVec.ofInt IntKind.i64.bits v2.toInt
    evalIntBinary .add (.int .i64 v1) (.int .i32 v2) = some (.int .i64 (v1 + v2'), .int .i64) := by
  have h2lo : -(2 ^ 31 : Int) ≤ v2.toInt := BitVec.le_toInt v2
  have h2hi : v2.toInt < (2 ^ 31 : Int) := BitVec.toInt_lt
  have hv2 : (BitVec.ofInt IntKind.i64.bits v2.toInt).toInt = v2.toInt :=
    bv_ofInt_i64_eq_of_range (by omega) (by omega)
  have hr : IntKind.i64.inRange (v1.toInt + (BitVec.ofInt IntKind.i64.bits v2.toInt).toInt) = true :=
    (i64_inRange_iff _).mpr (by rw [hv2]; exact ⟨hlo, hhi⟩)
  have h := evalIntBinary_signed_add (k1 := .i64) (k2 := .i32) (ck := .i64) rfl rfl v1 v2
    (by simp only [IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt, bitVec_ofInt_add_eq] at h
  exact h

theorem evalIntBinary_i64_i32_add (v1 : BitVec 64) (v2 : BitVec 32)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt + v2.toInt) (hhi : v1.toInt + v2.toInt < (2 ^ 63 : Int)) :
    let v2' := BitVec.ofInt 64 v2.toInt
    evalIntBinary .add (.int .i64 v1) (.int .i32 v2) = some (.int .i64 (v1 + v2'), .int .i64) :=
  evalIntBinary_i64_i32_add_bits v1 v2 hlo hhi

private theorem evalIntBinary_i64_i32_sub_bits
    (v1 : BitVec IntKind.i64.bits) (v2 : BitVec IntKind.i32.bits)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt - v2.toInt) (hhi : v1.toInt - v2.toInt < (2 ^ 63 : Int)) :
    let v2' : BitVec IntKind.i64.bits := BitVec.ofInt IntKind.i64.bits v2.toInt
    evalIntBinary .sub (.int .i64 v1) (.int .i32 v2) = some (.int .i64 (v1 - v2'), .int .i64) := by
  have h2lo : -(2 ^ 31 : Int) ≤ v2.toInt := BitVec.le_toInt v2
  have h2hi : v2.toInt < (2 ^ 31 : Int) := BitVec.toInt_lt
  have hv2 : (BitVec.ofInt IntKind.i64.bits v2.toInt).toInt = v2.toInt :=
    bv_ofInt_i64_eq_of_range (by omega) (by omega)
  have hr : IntKind.i64.inRange (v1.toInt - (BitVec.ofInt IntKind.i64.bits v2.toInt).toInt) = true :=
    (i64_inRange_iff _).mpr (by rw [hv2]; exact ⟨hlo, hhi⟩)
  have h := evalIntBinary_signed_sub (k1 := .i64) (k2 := .i32) (ck := .i64) rfl rfl v1 v2
    (by simp only [IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt]; exact hr)
  simp only [IntKind.signed, ↓reduceIte, bitVec_ofInt_toInt, bitVec_ofInt_sub_eq] at h
  exact h

theorem evalIntBinary_i64_i32_sub (v1 : BitVec 64) (v2 : BitVec 32)
    (hlo : -(2 ^ 63 : Int) ≤ v1.toInt - v2.toInt) (hhi : v1.toInt - v2.toInt < (2 ^ 63 : Int)) :
    let v2' := BitVec.ofInt 64 v2.toInt
    evalIntBinary .sub (.int .i64 v1) (.int .i32 v2) = some (.int .i64 (v1 - v2'), .int .i64) :=
  evalIntBinary_i64_i32_sub_bits v1 v2 hlo hhi

/-! ### 1.7 Pointer Arithmetic & Comparison Combinators -/

theorem evalPtrAdd_zero_of_allow {cfg : PointerConfig} (hallow : cfg.allowAddZeroAny = true)
    (tags : TypeEnv) (m : Mem) {p : Val} (hp : p = .null ∨ ∃ b off, p = .ptr b off) (el : CTy) :
    evalPtrAdd cfg tags m p el 0 = some p := by
  unfold evalPtrAdd
  simp only [beq_self_eq_true, hallow, Bool.and_self, ↓reduceIte]
  rcases hp with rfl | ⟨b, off, rfl⟩ <;> rfl

theorem evalPtrAdd_some {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {blk : Block} {el : CTy} {idx : Int}
    (hb : m.blocks b = some blk)
    (hlo : 0 ≤ off.toInt + idx * (max 1 (sizeofTy tags el) : Int))
    (hhi : off.toInt + idx * (max 1 (sizeofTy tags el) : Int) ≤ (blk.size : Int)) :
    evalPtrAdd cfg tags m (.ptr b off) el idx =
      some (.ptr b (Int64.ofInt (off.toInt + idx * (max 1 (sizeofTy tags el) : Int)))) := by
  unfold evalPtrAdd
  by_cases h0 : (idx == 0 && cfg.allowAddZeroAny) = true
  · have hidx : idx = 0 := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp h0).1
    subst hidx
    simp only [h0, ↓reduceIte, Int.zero_mul, Int.add_zero]
    cases off with
    | ofUInt64 u =>
      cases u with
      | ofBitVec bv =>
        have h : (⟨⟨bv⟩⟩ : Int64) = Int64.ofInt (⟨⟨bv⟩⟩ : Int64).toInt :=
          congrArg (fun x : BitVec 64 => (⟨⟨x⟩⟩ : Int64)) BitVec.ofInt_toInt.symm
        exact congrArg (fun y => some (Val.ptr b y)) h
  · have h0f : (idx == 0 && cfg.allowAddZeroAny) = false := Bool.eq_false_iff.mpr h0
    have hguard : (0 ≤ off.toInt + idx * (max 1 (sizeofTy tags el) : Int) &&
        decide (off.toInt + idx * (max 1 (sizeofTy tags el) : Int) ≤ (blk.size : Int))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hlo, hhi⟩
    simp only [h0f, Bool.false_eq_true, ↓reduceIte, hb, hguard, guard_true, bind, opt_bind_some,
      pure, Pure.pure]

theorem evalPtrSub_some {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {blk : Block} {el : CTy} {idx : Int}
    (hb : m.blocks b = some blk)
    (hlo : 0 ≤ off.toInt + (-idx) * (max 1 (sizeofTy tags el) : Int))
    (hhi : off.toInt + (-idx) * (max 1 (sizeofTy tags el) : Int) ≤ (blk.size : Int)) :
    evalPtrAdd cfg tags m (.ptr b off) el (-idx) =
      some (.ptr b (Int64.ofInt (off.toInt - idx * (max 1 (sizeofTy tags el) : Int)))) := by
  have heq : off.toInt + (-idx) * (max 1 (sizeofTy tags el) : Int) =
      off.toInt - idx * (max 1 (sizeofTy tags el) : Int) := by
    simp only [Int.neg_mul, ← Int.sub_eq_add_neg]
  rw [← heq]
  exact evalPtrAdd_some hb hlo hhi

theorem evalPtrDiff_null_some {cfg : PointerConfig} (hallow : cfg.allowNullDiffNull = true)
    (tags : TypeEnv) (m : Mem) (el : CTy) :
    evalPtrDiff cfg tags m .null .null el = some (.int .i64 0) := by
  unfold evalPtrDiff
  simp only [hallow, ↓reduceIte]

theorem evalPtrDiff_some {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {o1 o2 : Int64} {blk : Block} {el : CTy}
    (hb : m.blocks b = some blk)
    (h1lo : 0 ≤ o1.toInt) (h1hi : o1.toInt ≤ (blk.size : Int))
    (h2lo : 0 ≤ o2.toInt) (h2hi : o2.toInt ≤ (blk.size : Int))
    (hdiv : (o1.toInt - o2.toInt) % (max 1 (sizeofTy tags el) : Int) = 0) :
    evalPtrDiff cfg tags m (.ptr b o1) (.ptr b o2) el =
      some (.int .i64 (BitVec.ofInt 64 ((o1.toInt - o2.toInt) / (max 1 (sizeofTy tags el) : Int)))) := by
  unfold evalPtrDiff
  have h12 : (0 ≤ o1.toInt && decide (o1.toInt ≤ (blk.size : Int)) &&
      0 ≤ o2.toInt && decide (o2.toInt ≤ (blk.size : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h1lo, h1hi⟩, h2lo⟩, h2hi⟩
  have hmod : ((o1.toInt - o2.toInt) % (max 1 (sizeofTy tags el) : Int) == 0) = true :=
    beq_iff_eq.mpr hdiv
  have hsz : (blk.size : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    exact_mod_cast this
  have hdiff_lo : -(2 ^ 63 : Int) < o1.toInt - o2.toInt := by omega
  have hdiff_hi : o1.toInt - o2.toInt < (2 ^ 63 : Int) := by omega
  have hd1 : (1 : Int) ≤ max 1 (sizeofTy tags el) := by omega
  have hq_le : (o1.toInt - o2.toInt) / (max 1 (sizeofTy tags el) : Int) ≤ (2 ^ 63 : Int) - 1 := by
    apply Int.ediv_le_of_le_mul (by omega)
    have := Int.mul_le_mul_of_nonneg_left hd1 (by decide : (0 : Int) ≤ (2 ^ 63 : Int) - 1)
    omega
  have hq_ge : -(2 ^ 63 : Int) ≤ (o1.toInt - o2.toInt) / (max 1 (sizeofTy tags el) : Int) := by
    apply Int.le_ediv_of_mul_le (by omega)
    have := Int.mul_le_mul_of_nonpos_left (by decide : -(2 ^ 63 : Int) ≤ 0) hd1
    omega
  have hr : IntKind.i64.inRange ((o1.toInt - o2.toInt) / (max 1 (sizeofTy tags el) : Int)) = true :=
    (i64_inRange_iff _).mpr ⟨hq_ge, by omega⟩
  simp only [beq_self_eq_true, guard_true, hb, h12, hmod, ofIntExact_signed rfl hr,
    bind, opt_bind_some]
  rfl

theorem evalPtrCmp_eq_ptr_ptr (m : Mem) (b1 b2 : BlockId) (o1 o2 : Int64) :
    evalPtrCmp m .eq (.ptr b1 o1) (.ptr b2 o2) =
      some (.int .i32 (if b1 == b2 && o1 == o2 then 1 else 0)) := rfl

theorem evalPtrCmp_ne_ptr_ptr (m : Mem) (b1 b2 : BlockId) (o1 o2 : Int64) :
    evalPtrCmp m .ne (.ptr b1 o1) (.ptr b2 o2) =
      some (.int .i32 (if !(b1 == b2 && o1 == o2) then 1 else 0)) := rfl

theorem evalPtrCmp_eq_ptr_null (m : Mem) (b : BlockId) (off : Int64) :
    evalPtrCmp m .eq (.ptr b off) .null = some (.int .i32 0) := rfl

theorem evalPtrCmp_ne_ptr_null (m : Mem) (b : BlockId) (off : Int64) :
    evalPtrCmp m .ne (.ptr b off) .null = some (.int .i32 1) := rfl

theorem evalPtrCmp_eq_null_ptr (m : Mem) (b : BlockId) (off : Int64) :
    evalPtrCmp m .eq .null (.ptr b off) = some (.int .i32 0) := rfl

theorem evalPtrCmp_ne_null_ptr (m : Mem) (b : BlockId) (off : Int64) :
    evalPtrCmp m .ne .null (.ptr b off) = some (.int .i32 1) := rfl

theorem evalPtrCmp_eq_null_null (m : Mem) :
    evalPtrCmp m .eq .null .null = some (.int .i32 1) := rfl

theorem evalPtrCmp_ne_null_null (m : Mem) :
    evalPtrCmp m .ne .null .null = some (.int .i32 0) := rfl

theorem evalPtrCmp_eq_ptr_zero (m : Mem) (b : BlockId) (off : Int64)
    {k : IntKind} {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    evalPtrCmp m .eq (.ptr b off) (.int k bv) = some (.int .i32 0) := by
  unfold evalPtrCmp
  simp only [hz, beq_self_eq_true, ↓reduceIte, Option.map_some]
  rfl

theorem evalPtrCmp_ne_ptr_zero (m : Mem) (b : BlockId) (off : Int64)
    {k : IntKind} {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    evalPtrCmp m .ne (.ptr b off) (.int k bv) = some (.int .i32 1) := by
  unfold evalPtrCmp
  simp only [hz, beq_self_eq_true, ↓reduceIte, Option.map_some]
  rfl

theorem evalPtrCmp_eq_zero_ptr (m : Mem) (b : BlockId) (off : Int64)
    {k : IntKind} {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    evalPtrCmp m .eq (.int k bv) (.ptr b off) = some (.int .i32 0) := by
  unfold evalPtrCmp
  simp only [hz, beq_self_eq_true, ↓reduceIte, Option.map_some]
  rfl

theorem evalPtrCmp_ne_zero_ptr (m : Mem) (b : BlockId) (off : Int64)
    {k : IntKind} {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    evalPtrCmp m .ne (.int k bv) (.ptr b off) = some (.int .i32 1) := by
  unfold evalPtrCmp
  simp only [hz, beq_self_eq_true, ↓reduceIte, Option.map_some]
  rfl

theorem evalPtrCmp_eq_null_zero (m : Mem) {k : IntKind} {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    evalPtrCmp m .eq .null (.int k bv) = some (.int .i32 1) := by
  unfold evalPtrCmp
  simp only [hz, beq_self_eq_true, Bool.and_self, ↓reduceIte, Option.map_some]

theorem evalPtrCmp_ne_null_zero (m : Mem) {k : IntKind} {bv : BitVec k.bits} (hz : bv.toNat = 0) :
    evalPtrCmp m .ne .null (.int k bv) = some (.int .i32 0) := by
  unfold evalPtrCmp
  simp only [hz, beq_self_eq_true, Bool.and_self, ↓reduceIte, Option.map_some]
  rfl

theorem evalPtrCmp_eq_fnPtr_fnPtr (m : Mem) (s1 s2 : SymId) :
    evalPtrCmp m .eq (.fnPtr s1) (.fnPtr s2) =
      some (.int .i32 (if s1 == s2 then 1 else 0)) := rfl

theorem evalPtrCmp_ne_fnPtr_fnPtr (m : Mem) (s1 s2 : SymId) :
    evalPtrCmp m .ne (.fnPtr s1) (.fnPtr s2) =
      some (.int .i32 (if !(s1 == s2) then 1 else 0)) := rfl

theorem evalPtrCmp_eq_fnPtr_null (m : Mem) (s : SymId) :
    evalPtrCmp m .eq (.fnPtr s) .null = some (.int .i32 0) := rfl

theorem evalPtrCmp_ne_fnPtr_null (m : Mem) (s : SymId) :
    evalPtrCmp m .ne (.fnPtr s) .null = some (.int .i32 1) := rfl

theorem evalPtrCmp_ord_some {m : Mem} {op : BinOp}
    (hop : op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {b : BlockId} {o1 o2 : Int64} {blk : Block}
    (hb : m.blocks b = some blk)
    (h1lo : 0 ≤ o1.toInt) (h1hi : o1.toInt ≤ (blk.size : Int))
    (h2lo : 0 ≤ o2.toInt) (h2hi : o2.toInt ≤ (blk.size : Int)) :
    evalPtrCmp m op (.ptr b o1) (.ptr b o2) =
      some (.int .i32 (if cmpOrd op o1.toInt o2.toInt then 1 else 0)) := by
  unfold evalPtrCmp
  have h12 : (0 ≤ o1.toInt && decide (o1.toInt ≤ (blk.size : Int)) &&
      0 ≤ o2.toInt && decide (o2.toInt ≤ (blk.size : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h1lo, h1hi⟩, h2lo⟩, h2hi⟩
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [beq_self_eq_true, guard_true, hb, h12, bind, opt_bind_some, pure, Pure.pure]

theorem evalPtrCmp_some {m : Mem} {op : BinOp} {p q : Val}
    (h : (op = .eq ∨ op = .ne) ∧
      ((∃ b1 o1 b2 o2, p = .ptr b1 o1 ∧ q = .ptr b2 o2) ∨
       (∃ s1 s2, p = .fnPtr s1 ∧ q = .fnPtr s2) ∨
       ((∃ b o, p = .ptr b o) ∧ q = .null) ∨
       (p = .null ∧ (∃ b o, q = .ptr b o)) ∨
       (p = .null ∧ q = .null)) ∨
      ((op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) ∧
        ∃ b o1 o2 blk, p = .ptr b o1 ∧ q = .ptr b o2 ∧ m.blocks b = some blk ∧
          0 ≤ o1.toInt ∧ o1.toInt ≤ (blk.size : Int) ∧
          0 ≤ o2.toInt ∧ o2.toInt ≤ (blk.size : Int))) :
    ∃ r, evalPtrCmp m op p q = some (.int .i32 r) := by
  rcases h with ⟨hop, hpq⟩ | ⟨hop, b, o1, o2, blk, rfl, rfl, hb, h1lo, h1hi, h2lo, h2hi⟩
  · rcases hop with rfl | rfl
    · rcases hpq with ⟨b1, o1, b2, o2, rfl, rfl⟩ | ⟨s1, s2, rfl, rfl⟩ |
        ⟨⟨b, o, rfl⟩, rfl⟩ | ⟨rfl, ⟨b, o, rfl⟩⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, evalPtrCmp_eq_ptr_ptr m b1 b2 o1 o2⟩
      · exact ⟨_, evalPtrCmp_eq_fnPtr_fnPtr m s1 s2⟩
      · exact ⟨_, evalPtrCmp_eq_ptr_null m b o⟩
      · exact ⟨_, evalPtrCmp_eq_null_ptr m b o⟩
      · exact ⟨_, evalPtrCmp_eq_null_null m⟩
    · rcases hpq with ⟨b1, o1, b2, o2, rfl, rfl⟩ | ⟨s1, s2, rfl, rfl⟩ |
        ⟨⟨b, o, rfl⟩, rfl⟩ | ⟨rfl, ⟨b, o, rfl⟩⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, evalPtrCmp_ne_ptr_ptr m b1 b2 o1 o2⟩
      · exact ⟨_, evalPtrCmp_ne_fnPtr_fnPtr m s1 s2⟩
      · exact ⟨_, evalPtrCmp_ne_ptr_null m b o⟩
      · exact ⟨_, evalPtrCmp_ne_null_ptr m b o⟩
      · exact ⟨_, evalPtrCmp_ne_null_null m⟩
  · exact ⟨_, evalPtrCmp_ord_some hop hb h1lo h1hi h2lo h2hi⟩

theorem applyBinary_int_eq {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {op : BinOp} {v1 v2 : Val} {t1 t2 : CTy} {k1 k2 : IntKind}
    (ht1 : t1.unqual = .int k1) (ht2 : t2.unqual = .int k2) :
    applyBinary cfg tags m op v1 t1 v2 t2 = evalIntBinary op v1 v2 := by
  unfold applyBinary
  simp only [CTy.isPtr, ht1, ht2, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

theorem applyBinary_ptrAdd_r {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {p : Val} {pt el : CTy} (hpt : pt.unqual = .ptr el)
    {k : IntKind} {iv : BitVec k.bits} {it : CTy} {res : Val}
    (hadd : evalPtrAdd cfg tags m p el (if k.signed then iv.toInt else (iv.toNat : Int)) = some res) :
    applyBinary cfg tags m .add p pt (.int k iv) it = some (res, .ptr el) := by
  unfold applyBinary
  simp only [CTy.isPtr, hpt, Bool.true_or, ↓reduceIte, valAsInt?_int, hadd, Option.map_some]

theorem applyBinary_ptrAdd_l {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {k : IntKind} {iv : BitVec k.bits} {it : CTy} (hit : it.unqual = .int k)
    {p : Val} {pt el : CTy} (hpt : pt.unqual = .ptr el) {res : Val}
    (hadd : evalPtrAdd cfg tags m p el (if k.signed then iv.toInt else (iv.toNat : Int)) = some res) :
    applyBinary cfg tags m .add (.int k iv) it p pt = some (res, .ptr el) := by
  unfold applyBinary
  simp only [CTy.isPtr, hit, hpt, Bool.false_or, Bool.true_or, ↓reduceIte, valAsInt?_int,
    Bool.false_eq_true, hadd, Option.map_some]

theorem applyBinary_ptrSub {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {p : Val} {pt el : CTy} (hpt : pt.unqual = .ptr el)
    {k : IntKind} {iv : BitVec k.bits} {it : CTy} (hit : it.unqual = .int k) {res : Val}
    (hsub : evalPtrAdd cfg tags m p el (-(if k.signed then iv.toInt else (iv.toNat : Int))) = some res) :
    applyBinary cfg tags m .sub p pt (.int k iv) it = some (res, .ptr el) := by
  unfold applyBinary
  simp only [CTy.isPtr, hpt, hit, Bool.true_or, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    valAsInt?_int, hsub, Option.map_some]

theorem applyBinary_ptrDiff {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {p1 p2 : Val} {pt1 pt2 el1 el2 : CTy}
    (hp1 : pt1.unqual = .ptr el1) (hp2 : pt2.unqual = .ptr el2) {res : Val}
    (hdiff : evalPtrDiff cfg tags m p1 p2 el1 = some res) :
    applyBinary cfg tags m .sub p1 pt1 p2 pt2 = some (res, .int .i64) := by
  unfold applyBinary
  simp only [CTy.isPtr, hp1, hp2, Bool.true_or, Bool.and_self, ↓reduceIte, hdiff, Option.map_some]

theorem applyBinary_ptrCmp {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {op : BinOp} (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {p1 p2 : Val} {t1 t2 : CTy}
    (hptr : t1.isPtr = true ∨ t2.isPtr = true ∨
      (∃ r ps va, t1.unqual = .fnPtr r ps va) ∨
      (∃ r ps va, t2.unqual = .fnPtr r ps va))
    {res : Val} (hcmp : evalPtrCmp m op p1 p2 = some res) :
    applyBinary cfg tags m op p1 t1 p2 t2 = some (res, .int .i32) := by
  unfold applyBinary
  rcases hptr with h | h | ⟨r, ps, va, h⟩ | ⟨r, ps, va, h⟩ <;>
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [h, Bool.true_or, Bool.or_true, ↓reduceIte, hcmp, Option.map_some]

/-! ## 2. Block-Level Framing (`FrameMod`), Local Slots, Struct `FieldCell` & `ArraySlice` -/

/-! ### 2.1 `FrameMod` (Block-Level Framing Predicate & Combinators) -/

/-- Memory framing predicate: `m'` preserves `m.nextBlock ≤ m'.nextBlock`, keeps every pre-existing
    block `< m.nextBlock` outside `allowed` identical, and ensures any newly allocated block
    `≥ m.nextBlock` is either in `allowed` or is a read-only global (e.g. string literal). -/
def FrameMod (m m' : Mem) (allowed : BlockId → Prop) : Prop :=
  m.nextBlock ≤ m'.nextBlock ∧
  (∀ b, b < m.nextBlock → ¬ allowed b → m'.blocks b = m.blocks b) ∧
  (∀ b blk, m.nextBlock ≤ b → m'.blocks b = some blk →
    allowed b ∨ (blk.kind = .global ∧ blk.perm = .ro))

theorem FrameMod.refl (m : Mem) (allowed : BlockId → Prop) : FrameMod m m allowed :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl, fun _ _ hle hsome =>
    False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))⟩

theorem FrameMod.mono {m m' : Mem} {a1 a2 : BlockId → Prop}
    (hsub : ∀ b, a1 b → a2 b) (h : FrameMod m m' a1) : FrameMod m m' a2 :=
  ⟨h.1, fun b hlt hn2 => h.2.1 b hlt (fun ha1 => hn2 (hsub b ha1)),
    fun b blk hle hsome => match h.2.2 b blk hle hsome with
      | Or.inl ha1 => Or.inl (hsub b ha1)
      | Or.inr hro => Or.inr hro⟩

theorem FrameMod.trans {m1 m2 m3 : Mem} {a1 a2 : BlockId → Prop}
    (h12 : FrameMod m1 m2 a1) (h23 : FrameMod m2 m3 a2) :
    FrameMod m1 m3 (fun b => a1 b ∨ a2 b) := by
  refine ⟨Nat.le_trans h12.1 h23.1, ?_, ?_⟩
  · intro b hlt hn
    have hlt2 : b < m2.nextBlock := Nat.lt_of_lt_of_le hlt h12.1
    rw [h23.2.1 b hlt2 (fun ha2 => hn (Or.inr ha2)),
      h12.2.1 b hlt (fun ha1 => hn (Or.inl ha1))]
  · intro b blk hle1 hsome3
    by_cases hle2 : m2.nextBlock ≤ b
    · exact match h23.2.2 b blk hle2 hsome3 with
        | Or.inl ha2 => Or.inl (Or.inr ha2)
        | Or.inr hro => Or.inr hro
    · have hlt2 : b < m2.nextBlock := Nat.lt_of_not_le hle2
      by_cases ha2 : a2 b
      · exact Or.inl (Or.inr ha2)
      · have hsome2 : m2.blocks b = some blk := by
          rw [← h23.2.1 b hlt2 ha2]; exact hsome3
        exact match h12.2.2 b blk hle1 hsome2 with
          | Or.inl ha1 => Or.inl (Or.inl ha1)
          | Or.inr hro => Or.inr hro

theorem FrameMod.trans_same {m1 m2 m3 : Mem} {allowed : BlockId → Prop}
    (h12 : FrameMod m1 m2 allowed) (h23 : FrameMod m2 m3 allowed) :
    FrameMod m1 m3 allowed :=
  (h12.trans h23).mono (fun _ h => h.elim id id)

theorem FrameMod.of_roExt {m m' : Mem} (hro : ROExt m m') (allowed : BlockId → Prop) :
    FrameMod m m' allowed :=
  ⟨hro.1, fun b hlt _ => hro.2.1 b hlt, fun b blk hle hsome => Or.inr (hro.2.2 b blk hle hsome)⟩

theorem FrameMod.trans_roExt {m1 m2 m3 : Mem} {allowed : BlockId → Prop}
    (h12 : FrameMod m1 m2 allowed) (hro : ROExt m2 m3) :
    FrameMod m1 m3 allowed :=
  (h12.trans (FrameMod.of_roExt hro (fun _ => False))).mono (fun _ h => h.elim id False.elim)

theorem FrameMod.roExt_trans {m1 m2 m3 : Mem} {allowed : BlockId → Prop}
    (hro : ROExt m1 m2) (h23 : FrameMod m2 m3 allowed) :
    FrameMod m1 m3 allowed :=
  ((FrameMod.of_roExt hro (fun _ => False)).trans h23).mono (fun _ h => h.elim False.elim id)

theorem FrameMod.to_roExt_of_empty {m m' : Mem}
    (h : FrameMod m m' (fun _ => False)) : ROExt m m' :=
  ⟨h.1, fun b hlt => h.2.1 b hlt False.elim, fun b blk hle hsome =>
    match h.2.2 b blk hle hsome with
    | Or.inl hf => False.elim hf
    | Or.inr hro => hro⟩

theorem FrameMod.blocks_eq_of_notin {m m' : Mem} {allowed : BlockId → Prop}
    (h : FrameMod m m' allowed) {b : BlockId} (hlt : b < m.nextBlock) (hn : ¬ allowed b) :
    m'.blocks b = m.blocks b :=
  h.2.1 b hlt hn

theorem FrameMod.blocks_some_of_notin {m m' : Mem} {allowed : BlockId → Prop}
    (h : FrameMod m m' allowed) {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) (hn : ¬ allowed b) :
    m'.blocks b = some blk := by
  rw [h.blocks_eq_of_notin (lt_nextBlock_of_some hb) hn, hb]

theorem FrameMod.addrOf_of_notin {m m' : Mem} {allowed : BlockId → Prop}
    (h : FrameMod m m' allowed) {b : BlockId} (hlt : b < m.nextBlock) (hn : ¬ allowed b)
    (off : Int64) :
    m'.addrOf b off = m.addrOf b off := by
  unfold Mem.addrOf
  rw [h.blocks_eq_of_notin hlt hn]

theorem FrameMod.readBytes_of_notin {m m' : Mem} {allowed : BlockId → Prop}
    (h : FrameMod m m' allowed) {b : BlockId} (hlt : b < m.nextBlock) (hn : ¬ allowed b)
    (off : Int64) (len : Nat) :
    m'.readBytes b off len = m.readBytes b off len :=
  readBytes_congr_blocks (h.blocks_eq_of_notin hlt hn) off len

theorem FrameMod.readVal_of_notin (tags : TypeEnv) {m m' : Mem} {allowed : BlockId → Prop}
    (h : FrameMod m m' allowed) {b : BlockId} (hlt : b < m.nextBlock) (hn : ¬ allowed b)
    (off : Int64) (ty : CTy) :
    Sem.readVal tags m' b off ty = Sem.readVal tags m b off ty :=
  readVal_congr_blocks tags (h.blocks_eq_of_notin hlt hn) off ty

theorem FrameMod.strlenAt_of_notin {m m' : Mem} {allowed : BlockId → Prop}
    (h : FrameMod m m' allowed) {b : BlockId} (hlt : b < m.nextBlock) (hn : ¬ allowed b)
    (off : Int64) :
    m'.strlenAt b off = m.strlenAt b off :=
  strlenAt_congr_blocks (h.blocks_eq_of_notin hlt hn) off

theorem FrameMod.of_writeBytes {m m' : Mem} {b : BlockId} {off : Int64} {bytes : List MemByte}
    (hw : m.writeBytes b off bytes = some m') :
    FrameMod m m' (· = b) := by
  refine ⟨Nat.le_of_eq (writeBytes_nextBlock hw).symm, ?_, ?_⟩
  · intro b' _ hne
    exact writeBytes_blocks_ne hw hne
  · intro b' _ hle hsome
    by_cases heq : b' = b
    · exact Or.inl heq
    · rw [writeBytes_blocks_ne hw heq] at hsome
      exact False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))

theorem FrameMod.of_writeVal {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (hw : Sem.writeVal m b off ty v = some m') :
    FrameMod m m' (· = b) := by
  obtain ⟨bs, hbs⟩ := writeVal_writeBytes hw
  exact FrameMod.of_writeBytes hbs

theorem FrameMod.of_writePlace (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {rv res : ExprRes} (hw : Sem.writePlace tags m b off ty rv = some (res, m')) :
    FrameMod m m' (· = b) := by
  obtain ⟨bs, hbs⟩ := writePlace_writeBytes hw
  exact FrameMod.of_writeBytes hbs

theorem FrameMod.of_alloc {m m' : Mem} {sz al : Nat} {perm : Perm} {kind : AllocKind}
    {ba : UInt64} {init : Nat → MemByte} {hsz : sz < ptrDiffLimit} {hal : 0 < al}
    {hba : ba.toNat % al = 0} {b : BlockId}
    (ha : m.alloc sz al perm kind ba init hsz hal hba = (b, m')) :
    FrameMod m m' (· = b) := by
  unfold Mem.alloc at ha
  cases ha
  refine ⟨Nat.le_succ _, ?_, ?_⟩
  · intro b' hlt hne
    have hbeq : (b' == m.nextBlock) = false := beq_false_of_ne hne
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  · intro b' _ hle hsome
    by_cases heq : b' = m.nextBlock
    · exact Or.inl heq
    · have hbeq : (b' == m.nextBlock) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hsome
      exact False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))

theorem FrameMod.of_free {m m' : Mem} {b : BlockId} (hf : m.free b = some m') :
    FrameMod m m' (· = b) := by
  unfold Mem.free at hf
  cases hblk : m.blocks b with
  | none => simp only [hblk] at hf; cases hf
  | some blk =>
    simp only [hblk] at hf
    by_cases hk : (blk.kind == .heap) = true
    · simp only [hk, ↓reduceIte] at hf
      cases hf
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      · intro b' _ hne
        have hbeq : (b' == b) = false := beq_false_of_ne hne
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      · intro b' _ hle hsome
        by_cases heq : b' = b
        · exact Or.inl heq
        · have hbeq : (b' == b) = false := beq_false_of_ne heq
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hsome
          exact False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))
    · have hkf : (blk.kind == .heap) = false := Bool.eq_false_iff.mpr hk
      simp only [hkf, Bool.false_eq_true, ↓reduceIte] at hf
      cases hf

theorem FrameMod.of_freeStack (m : Mem) (bs : List BlockId) :
    FrameMod m (m.freeStack bs) (fun b => bs.contains b = true) := by
  unfold Mem.freeStack
  refine ⟨Nat.le_refl _, ?_, ?_⟩
  · intro b' _ hnin
    have hcf : bs.contains b' = false := Bool.eq_false_iff.mpr hnin
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
  · intro b' _ hle hsome
    by_cases hmem : bs.contains b' = true
    · exact Or.inl hmem
    · have hcf : bs.contains b' = false := Bool.eq_false_iff.mpr hmem
      simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hsome
      exact False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))

theorem FrameMod.of_dropBlock (m : Mem) (b : BlockId) :
    FrameMod m (m.dropBlock b) (· = b) := by
  unfold Mem.dropBlock
  refine ⟨Nat.le_refl _, ?_, ?_⟩
  · intro b' _ hne
    have hbeq : (b' == b) = false := beq_false_of_ne hne
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  · intro b' _ hle hsome
    by_cases heq : b' = b
    · exact Or.inl heq
    · have hbeq : (b' == b) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hsome
      exact False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))

theorem FrameMod.of_localFrameMem {base m : Mem} {blks : List BlockId}
    (hlf : LocalFrameMem base m blks) :
    FrameMod base m (fun b => b ∈ blks) :=
  ⟨hlf.1, fun b hlt _ => hlf.2.1 b hlt, fun b blk hle hsome =>
    match hlf.2.2.2.2 b blk hle hsome with
    | Or.inl ⟨_, hmem⟩ => Or.inl hmem
    | Or.inr hro => Or.inr hro⟩

theorem FrameMod.of_localFrameMem_ge {base m : Mem} {blks : List BlockId}
    (hlf : LocalFrameMem base m blks) :
    FrameMod base m (fun b => base.nextBlock ≤ b) :=
  ⟨hlf.1, fun b hlt _ => hlf.2.1 b hlt, fun _ _ hle _ => Or.inl hle⟩

/-! ### 2.2 Same-Block Disjoint Byte-Range Preservation -/

theorem writeBytes_preserves_perm {m m' : Mem} {b : BlockId} {off : Int64} {bytes : List MemByte}
    (hw : m.writeBytes b off bytes = some m') {blk : Block} (hb : m.blocks b = some blk) :
    ∃ blk', m'.blocks b = some blk' ∧ blk'.kind = blk.kind ∧ blk'.perm = blk.perm ∧
      blk'.size = blk.size ∧ blk'.align = blk.align ∧ blk'.baseAddr = blk.baseAddr ∧
      (∀ i, blk'.bytes i =
        if off.toInt.toNat ≤ i ∧ i < off.toInt.toNat + bytes.length
        then bytes[i - off.toInt.toNat]?.getD .undef
        else blk.bytes i) := by
  exact ⟨_, writeBytes_blocks_eq hb hw, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem writeBytes_inBounds_true {m m' : Mem} {b : BlockId} {off : Int64} {bytes : List MemByte}
    (hw : m.writeBytes b off bytes = some m') {blk : Block} (hb : m.blocks b = some blk) :
    blk.perm = .rw ∧ Mem.inBounds blk off bytes.length = true := by
  unfold Mem.writeBytes at hw
  split at hw
  · rename_i hblk
    rw [hb] at hblk; cases hblk
  · rename_i blk0 hblk
    rw [hb] at hblk; cases hblk
    split at hw
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond
    · cases hw

private theorem opt_pure_some {α : Type} (a : α) : (Pure.pure a : Option α) = some a := rfl

private theorem opt_bind_none {α β : Type} (f : α → Option β) : (none : Option α).bind f = none := rfl

private theorem env_lookup_cons_eq (x : String) (v : BlockId × CTy) (env : Env) :
    ((x, v) :: env).lookup x = some v := by
  simp only [List.lookup, beq_self_eq_true]

theorem readBytes_writeBytes_disjoint {m m' : Mem} {b : BlockId} {off : Int64}
    {bytes : List MemByte} (hw : m.writeBytes b off bytes = some m')
    {off' : Int64} {len' : Nat}
    (hdisj : off.toInt + bytes.length ≤ off'.toInt ∨ off'.toInt + len' ≤ off.toInt) :
    m'.readBytes b off' len' = m.readBytes b off' len' := by
  cases hb : m.blocks b with
  | none =>
    unfold Mem.writeBytes at hw
    split at hw
    · cases hw
    · rename_i blk0 hblk; rw [hb] at hblk; cases hblk
  | some blk =>
    obtain ⟨_, hwb⟩ := writeBytes_inBounds_true hw hb
    have hw_bounds : 0 ≤ off.toInt := (inBounds_iff.mp hwb).1
    obtain ⟨blk', hb', _, _, hsz', _, _, hbytes⟩ := writeBytes_preserves_perm hw hb
    have hin_eq : Mem.inBounds blk' off' len' = Mem.inBounds blk off' len' := by
      unfold Mem.inBounds; rw [hsz']
    by_cases hin : Mem.inBounds blk off' len' = true
    · have hin' : Mem.inBounds blk' off' len' = true := by rw [hin_eq]; exact hin
      have h0' : 0 ≤ off'.toInt := (inBounds_iff.mp hin).1
      rw [readBytes_of_bounds hb' hin', readBytes_of_bounds hb hin]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilen : i < len' := List.mem_range.mp hi
      rw [hbytes]
      have hnot : ¬ (off.toInt.toNat ≤ off'.toInt.toNat + i ∧
          off'.toInt.toNat + i < off.toInt.toNat + bytes.length) := by
        omega
      simp only [hnot, ↓reduceIte]
    · have hinf : Mem.inBounds blk off' len' = false := Bool.eq_false_iff.mpr hin
      have hinf' : Mem.inBounds blk' off' len' = false := by rw [hin_eq]; exact hinf
      unfold Mem.readBytes
      simp only [hb, hb', hinf, hinf', guard, Bool.false_eq_true, ↓reduceIte, bind, opt_bind_some]
      rfl

private theorem sizeofTy_enum (tags : TypeEnv) {ty : CTy} {tag : String} {isU : Bool}
    (he : ty.unqual = .enumTy tag isU) : sizeofTy tags ty = 4 := by
  rw [← sizeofTy_unqual, he]; unfold sizeofTy sizeofAux; rfl

theorem readVal_writeBytes_disjoint (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {bytes : List MemByte} (hw : m.writeBytes b off bytes = some m')
    {off' : Int64} {ty' : CTy}
    (hdisj : off.toInt + bytes.length ≤ off'.toInt ∨
      off'.toInt + (max 1 (sizeofTy tags ty') : Int) ≤ off.toInt) :
    Sem.readVal tags m' b off' ty' = Sem.readVal tags m b off' ty' := by
  cases hb : m.blocks b with
  | none =>
    unfold Mem.writeBytes at hw
    split at hw
    · cases hw
    · rename_i blk0 hblk; rw [hb] at hblk; cases hblk
  | some blk =>
    obtain ⟨blk', hb', _, _, _, _, hba', _⟩ := writeBytes_preserves_perm hw hb
    have hal_eq : ∀ al, Mem.isAligned blk' off' al = Mem.isAligned blk off' al := by
      intro al; unfold Mem.isAligned; rw [hba']
    have hr_eq : ∀ len : Nat, (len : Int) ≤ (max 1 (sizeofTy tags ty') : Int) →
        m'.readBytes b off' len = m.readBytes b off' len := by
      intro len hle
      exact readBytes_writeBytes_disjoint hw (by
        rcases hdisj with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by omega))
    unfold Sem.readVal
    dsimp only
    cases hq : ty'.unqual with
    | array _ _ => rfl
    | void | structTy _ | unionTy _ | anonStruct _ | anonUnion _
    | const_ _ | typedef _ _ => rfl
    | int k =>
      have hsz := sizeofTy_eq_bytes (tags := tags) hq
      simp only [CTy.intKind?, CTy.unqual, hb, hb', hal_eq, bind, opt_bind_some]
      by_cases ha : Mem.isAligned blk off' k.align = true
      · simp only [ha, guard_true, opt_bind_some, hr_eq k.bytes (by omega)]
      · have haf : Mem.isAligned blk off' k.align = false := Bool.eq_false_iff.mpr ha
        simp only [haf, guard, Bool.false_eq_true, ↓reduceIte]; rfl
    | enumTy tag isU =>
      have hsz := sizeofTy_enum tags hq
      have hkb : (if isU = true then IntKind.u32 else IntKind.i32).bytes = 4 := by
        cases isU <;> rfl
      simp only [CTy.intKind?, CTy.unqual, hb, hb', hal_eq, bind, opt_bind_some]
      by_cases ha : Mem.isAligned blk off' (if isU = true then IntKind.u32 else IntKind.i32).align = true
      · simp only [ha, guard_true, opt_bind_some,
          hr_eq (if isU = true then IntKind.u32 else IntKind.i32).bytes (by rw [hkb]; omega)]
      · have haf : Mem.isAligned blk off' (if isU = true then IntKind.u32 else IntKind.i32).align = false :=
          Bool.eq_false_iff.mpr ha
        simp only [haf, guard, Bool.false_eq_true, ↓reduceIte]; rfl
    | ptr el =>
      have hsz := sizeofTy_eq_ptr (tags := tags) hq
      simp only [hb, hb', hal_eq, bind, opt_bind_some]
      by_cases ha : Mem.isAligned blk off' 8 = true
      · simp only [ha, guard_true, opt_bind_some, hr_eq 8 (by omega)]
      · have haf : Mem.isAligned blk off' 8 = false := Bool.eq_false_iff.mpr ha
        simp only [haf, guard, Bool.false_eq_true, ↓reduceIte]; rfl
    | fnPtr r ps va =>
      have hsz := sizeofTy_eq_fnPtr (tags := tags) hq
      simp only [hb, hb', hal_eq, bind, opt_bind_some]
      by_cases ha : Mem.isAligned blk off' 8 = true
      · simp only [ha, guard_true, opt_bind_some, hr_eq 8 (by omega)]
      · have haf : Mem.isAligned blk off' 8 = false := Bool.eq_false_iff.mpr ha
        simp only [haf, guard, Bool.false_eq_true, ↓reduceIte]; rfl
    | vaList =>
      have hsz : sizeofTy tags (.vaList) = sizeofTy tags ty' := by rw [← hq, sizeofTy_unqual]
      simp only [bind, hr_eq (sizeofTy tags .vaList) (by omega)]

private theorem sizeofTy_vaList (tags : TypeEnv) {ty : CTy} (hv : ty.unqual = .vaList) :
    sizeofTy tags ty = 24 := by
  rw [← sizeofTy_unqual, hv]
  unfold sizeofTy sizeofAux
  rfl

theorem writeVal_writeBytes_exact (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (hw : Sem.writeVal m b off ty v = some m') :
    ∃ bs, bs.length = sizeofTy tags ty ∧ m.writeBytes b off bs = some m' := by
  unfold Sem.writeVal at hw
  cases hnc : ty.isConst
  · simp only [hnc, Bool.not_false, guard_true, bind, opt_bind_some] at hw
    cases hb : m.blocks b with
    | none => simp only [hb] at hw; cases hw
    | some blk =>
      simp only [hb, opt_bind_some] at hw
      obtain ⟨ut, hq⟩ : ∃ ut, ty.unqual = ut := ⟨_, rfl⟩
      rw [hq] at hw
      cases ut with
      | void | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _
      | const_ _ | typedef _ _ => cases hw
      | int k =>
        dsimp only at hw
        simp only [CTy.intKind?, CTy.unqual, opt_bind_some] at hw
        by_cases ha : Mem.isAligned blk off k.align = true
        · simp only [ha, guard_true, opt_bind_some] at hw
          cases hv : valAsInt? v with
          | none => simp only [hv] at hw; cases hw
          | some pair =>
            simp only [hv] at hw
            exact ⟨_, by rw [encodeInt_length, sizeofTy_eq_bytes hq], hw⟩
        · have haf : Mem.isAligned blk off k.align = false := Bool.eq_false_iff.mpr ha
          rw [haf] at hw
          cases hw
      | enumTy tag isU =>
        dsimp only at hw
        simp only [CTy.intKind?, CTy.unqual, opt_bind_some] at hw
        by_cases ha : Mem.isAligned blk off (if isU = true then IntKind.u32 else IntKind.i32).align = true
        · simp only [ha, guard_true, opt_bind_some] at hw
          cases hv : valAsInt? v with
          | none => simp only [hv] at hw; cases hw
          | some pair =>
            simp only [hv] at hw
            have hkb : (if isU = true then IntKind.u32 else IntKind.i32).bytes = 4 := by
              cases isU <;> rfl
            exact ⟨_, by rw [encodeInt_length, hkb, sizeofTy_enum tags hq], hw⟩
        · have haf : Mem.isAligned blk off (if isU = true then IntKind.u32 else IntKind.i32).align = false :=
            Bool.eq_false_iff.mpr ha
          rw [haf] at hw
          cases hw
      | ptr el =>
        dsimp only at hw
        by_cases ha : Mem.isAligned blk off 8 = true
        · simp only [ha, guard_true, opt_bind_some] at hw
          cases v with
          | null => exact ⟨_, by rw [encodeNull_length, sizeofTy_eq_ptr hq], hw⟩
          | ptr pb po => exact ⟨_, by rw [encodePtr_length, sizeofTy_eq_ptr hq], hw⟩
          | int _ bv =>
            by_cases hz : (bv.toNat == 0) = true
            · simp only [hz, ↓reduceIte] at hw
              exact ⟨_, by rw [encodeNull_length, sizeofTy_eq_ptr hq], hw⟩
            · have hzf : (bv.toNat == 0) = false := Bool.eq_false_iff.mpr hz
              simp only [hzf, Bool.false_eq_true, ↓reduceIte] at hw; cases hw
          | _ => cases hw
        · have haf : Mem.isAligned blk off 8 = false := Bool.eq_false_iff.mpr ha
          rw [haf] at hw
          cases hw
      | fnPtr r ps va =>
        dsimp only at hw
        by_cases ha : Mem.isAligned blk off 8 = true
        · simp only [ha, guard_true, opt_bind_some] at hw
          cases v with
          | null => exact ⟨_, by rw [encodeNull_length, sizeofTy_eq_fnPtr hq], hw⟩
          | fnPtr s => exact ⟨_, by rw [encodeFnPtr_length, sizeofTy_eq_fnPtr hq], hw⟩
          | int _ bv =>
            by_cases hz : (bv.toNat == 0) = true
            · simp only [hz, ↓reduceIte] at hw
              exact ⟨_, by rw [encodeNull_length, sizeofTy_eq_fnPtr hq], hw⟩
            · have hzf : (bv.toNat == 0) = false := Bool.eq_false_iff.mpr hz
              simp only [hzf, Bool.false_eq_true, ↓reduceIte] at hw; cases hw
          | _ => cases hw
        · have haf : Mem.isAligned blk off 8 = false := Bool.eq_false_iff.mpr ha
          rw [haf] at hw
          cases hw
      | vaList =>
        dsimp only at hw
        cases v with
        | vaList valid =>
          cases valid with
          | false => cases hw
          | true => exact ⟨_, by rw [List.length_replicate, sizeofTy_vaList tags hq], hw⟩
        | _ => cases hw
  · simp only [hnc, Bool.not_true, guard, Bool.false_eq_true, ↓reduceIte] at hw
    cases hw

theorem readVal_writeVal_disjoint (tags : TypeEnv) {m m' : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (hw : Sem.writeVal m b off ty v = some m')
    {off' : Int64} {ty' : CTy}
    (hdisj : off.toInt + (sizeofTy tags ty : Int) ≤ off'.toInt ∨
      off'.toInt + (max 1 (sizeofTy tags ty') : Int) ≤ off.toInt) :
    Sem.readVal tags m' b off' ty' = Sem.readVal tags m b off' ty' := by
  obtain ⟨bs, hlen, hbs⟩ := writeVal_writeBytes_exact tags hw
  exact readVal_writeBytes_disjoint tags hbs (by rw [hlen]; exact hdisj)

/-! ### 2.3 Local Stack Slots (`LocalIntSlot`, `LocalPtrSlot`, `LocalFnPtrSlot`) -/

theorem cty_decay_eq_int : ∀ (ty : CTy) {k : IntKind},
    ty.unqual = .int k → ty.decay = .int k
  | .const_ t, _, h => cty_decay_eq_int t h
  | .typedef _ t, _, h => cty_decay_eq_int t h
  | .int _, _, h => h
  | .void, _, h | .ptr _, _, h | .array _ _, _, h | .structTy _, _, h | .unionTy _, _, h
  | .anonStruct _, _, h | .anonUnion _, _, h | .enumTy _ _, _, h | .fnPtr _ _ _, _, h
  | .vaList, _, h => by cases h

theorem cty_decay_eq_ptr : ∀ (ty : CTy) {el : CTy},
    ty.unqual = .ptr el → ty.decay = .ptr el
  | .const_ t, _, h => cty_decay_eq_ptr t h
  | .typedef _ t, _, h => cty_decay_eq_ptr t h
  | .ptr _, _, h => h
  | .void, _, h | .int _, _, h | .array _ _, _, h | .structTy _, _, h | .unionTy _, _, h
  | .anonStruct _, _, h | .anonUnion _, _, h | .enumTy _ _, _, h | .fnPtr _ _ _, _, h
  | .vaList, _, h => by cases h

theorem cty_decay_eq_fnPtr : ∀ (ty : CTy) {rty : CTy} {ptys : List CTy} {va : Bool},
    ty.unqual = .fnPtr rty ptys va → ty.decay = .fnPtr rty ptys va
  | .const_ t, _, _, _, h => cty_decay_eq_fnPtr t h
  | .typedef _ t, _, _, _, h => cty_decay_eq_fnPtr t h
  | .fnPtr _ _ _, _, _, _, h => h
  | .void, _, _, _, h | .int _, _, _, _, h | .ptr _, _, _, _, h | .array _ _, _, _, _, h
  | .structTy _, _, _, _, h | .unionTy _, _, _, _, h | .anonStruct _, _, _, _, h
  | .anonUnion _, _, _, _, h | .enumTy _ _, _, _, _, h | .vaList, _, _, _, h => by cases h

theorem cty_decay_eq_array : ∀ (ty : CTy) {el : CTy} {n : Option Nat},
    ty.unqual = .array el n → ty.decay = .ptr el
  | .const_ t, _, _, h => cty_decay_eq_array t h
  | .typedef _ t, _, _, h => cty_decay_eq_array t h
  | .array _ _, _, _, h => by cases h; rfl
  | .void, _, _, h | .int _, _, _, h | .ptr _, _, _, h | .structTy _, _, _, h
  | .unionTy _, _, _, h | .anonStruct _, _, _, h | .anonUnion _, _, _, h
  | .enumTy _ _, _, _, h | .fnPtr _ _ _, _, _, h | .vaList, _, _, h => by cases h

theorem cty_stripConst_isConst : ∀ (ty : CTy), ty.stripConst.isConst = false
  | .const_ t => cty_stripConst_isConst t
  | .typedef _ t => cty_stripConst_isConst t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

theorem cty_stripConst_unqual : ∀ (ty : CTy), ty.stripConst.unqual = ty.unqual
  | .const_ t => cty_stripConst_unqual t
  | .typedef _ t => cty_stripConst_unqual t
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

private theorem k_align_pos (k : IntKind) : 0 < k.align := by
  cases k <;> decide

private theorem k_bytes_pos (k : IntKind) : 0 < k.bytes := by
  cases k <;> decide

private theorem isAligned_zero_of_eq {blk : Block} {al : Nat} (hpos : 0 < al)
    (hal : blk.align = al) : Mem.isAligned blk 0 al = true := by
  unfold Mem.isAligned
  rw [Int64.toInt_zero]
  simp only [Int.le_refl, Int.toNat_zero, Nat.add_zero, hpos, decide_true, Bool.true_and]
  exact beq_iff_eq.mpr (show blk.baseAddr.toNat % al = 0 from by rw [← hal]; exact blk.baseAligned)

private theorem inBounds_zero_of_le {blk : Block} {len : Nat} (hle : len ≤ blk.size) :
    Mem.inBounds blk 0 len = true := by
  unfold Mem.inBounds
  rw [Int64.toInt_zero]
  simp only [Int.le_refl, Int.toNat_zero, Nat.zero_add, decide_true, Bool.true_and, decide_eq_true_eq]
  exact hle

/-- An uninitialized writable local integer variable slot in `env` and `m`. -/
def UninitLocalIntSlot (env : Env) (m : Mem) (x : String) (ty : CTy) (k : IntKind) : Prop :=
  ∃ b blk, env.lookup x = some (b, ty) ∧ ty.isConst = false ∧ ty.unqual = .int k ∧
    m.blocks b = some blk ∧ blk.perm = .rw ∧ k.bytes ≤ blk.size ∧
    Mem.isAligned blk 0 k.align = true

/-- A readable local integer variable slot holding `v`. -/
def LocalIntSlot (env : Env) (m : Mem) (x : String) (ty : CTy) (k : IntKind)
    (v : BitVec k.bits) : Prop :=
  ∃ b blk, env.lookup x = some (b, ty) ∧ ty.unqual = .int k ∧
    m.blocks b = some blk ∧ blk.perm = .rw ∧ k.bytes ≤ blk.size ∧
    Mem.isAligned blk 0 k.align = true ∧
    m.readBytes b 0 k.bytes = some (Mem.encodeInt k v)

/-- An uninitialized writable local pointer variable slot in `env` and `m`. -/
def UninitLocalPtrSlot (env : Env) (m : Mem) (x : String) (ty el : CTy) : Prop :=
  ∃ b blk, env.lookup x = some (b, ty) ∧ ty.isConst = false ∧ ty.unqual = .ptr el ∧
    m.blocks b = some blk ∧ blk.perm = .rw ∧ 8 ≤ blk.size ∧
    Mem.isAligned blk 0 8 = true

/-- A readable local pointer variable slot holding `v` (`.null` or `.ptr bp op`). -/
def LocalPtrSlot (env : Env) (m : Mem) (x : String) (ty el : CTy) (v : Val) : Prop :=
  ∃ b blk, env.lookup x = some (b, ty) ∧ ty.unqual = .ptr el ∧
    m.blocks b = some blk ∧ blk.perm = .rw ∧ 8 ≤ blk.size ∧
    Mem.isAligned blk 0 8 = true ∧
    ((v = .null ∧ m.readBytes b 0 8 = some Mem.encodeNull) ∨
     (∃ bp op, v = .ptr bp op ∧ m.readBytes b 0 8 = some (Mem.encodePtr bp op)))

/-- A readable local function-pointer variable slot holding `v` (`.null` or `.fnPtr sym`). -/
def LocalFnPtrSlot (env : Env) (m : Mem) (x : String) (ty rty : CTy) (ptys : List CTy)
    (va : Bool) (v : Val) : Prop :=
  ∃ b blk, env.lookup x = some (b, ty) ∧ ty.unqual = .fnPtr rty ptys va ∧
    m.blocks b = some blk ∧ blk.perm = .rw ∧ 8 ≤ blk.size ∧
    Mem.isAligned blk 0 8 = true ∧
    ((v = .null ∧ m.readBytes b 0 8 = some Mem.encodeNull) ∨
     (∃ sym, v = .fnPtr sym ∧ m.readBytes b 0 8 = some (Mem.encodeFnPtr sym)))

theorem LocalIntSlot.to_uninit {env : Env} {m : Mem} {x : String} {ty : CTy} {k : IntKind}
    {v : BitVec k.bits} (hnc : ty.isConst = false) (h : LocalIntSlot env m x ty k v) :
    UninitLocalIntSlot env m x ty k := by
  rcases h with ⟨b, blk, hl, hty, hb, hp, hsz, hal, _⟩
  exact ⟨b, blk, hl, hnc, hty, hb, hp, hsz, hal⟩

theorem LocalPtrSlot.to_uninit {env : Env} {m : Mem} {x : String} {ty el : CTy} {v : Val}
    (hnc : ty.isConst = false) (h : LocalPtrSlot env m x ty el v) :
    UninitLocalPtrSlot env m x ty el := by
  rcases h with ⟨b, blk, hl, hty, hb, hp, hsz, hal, _⟩
  exact ⟨b, blk, hl, hnc, hty, hb, hp, hsz, hal⟩

theorem UninitLocalIntSlot.preserve_frameMod {env : Env} {m m' : Mem} {allowed : BlockId → Prop}
    {x : String} {ty : CTy} {k : IntKind}
    (h : UninitLocalIntSlot env m x ty k) (hfr : FrameMod m m' allowed)
    (hnotin : ∀ b blk, env.lookup x = some (b, ty) → m.blocks b = some blk → ¬ allowed b) :
    UninitLocalIntSlot env m' x ty k := by
  rcases h with ⟨b, blk, hl, hnc, hty, hb, hp, hsz, hal⟩
  exact ⟨b, blk, hl, hnc, hty, hfr.blocks_some_of_notin hb (hnotin b blk hl hb), hp, hsz, hal⟩

theorem LocalIntSlot.preserve_frameMod {env : Env} {m m' : Mem} {allowed : BlockId → Prop}
    {x : String} {ty : CTy} {k : IntKind} {v : BitVec k.bits}
    (h : LocalIntSlot env m x ty k v) (hfr : FrameMod m m' allowed)
    (hnotin : ∀ b blk, env.lookup x = some (b, ty) → m.blocks b = some blk → ¬ allowed b) :
    LocalIntSlot env m' x ty k v := by
  rcases h with ⟨b, blk, hl, hty, hb, hp, hsz, hal, hrb⟩
  have hn := hnotin b blk hl hb
  have hlt := lt_nextBlock_of_some hb
  refine ⟨b, blk, hl, hty, hfr.blocks_some_of_notin hb hn, hp, hsz, hal, ?_⟩
  rw [hfr.readBytes_of_notin hlt hn, hrb]

theorem UninitLocalPtrSlot.preserve_frameMod {env : Env} {m m' : Mem} {allowed : BlockId → Prop}
    {x : String} {ty el : CTy}
    (h : UninitLocalPtrSlot env m x ty el) (hfr : FrameMod m m' allowed)
    (hnotin : ∀ b blk, env.lookup x = some (b, ty) → m.blocks b = some blk → ¬ allowed b) :
    UninitLocalPtrSlot env m' x ty el := by
  rcases h with ⟨b, blk, hl, hnc, hty, hb, hp, hsz, hal⟩
  exact ⟨b, blk, hl, hnc, hty, hfr.blocks_some_of_notin hb (hnotin b blk hl hb), hp, hsz, hal⟩

theorem LocalPtrSlot.preserve_frameMod {env : Env} {m m' : Mem} {allowed : BlockId → Prop}
    {x : String} {ty el : CTy} {v : Val}
    (h : LocalPtrSlot env m x ty el v) (hfr : FrameMod m m' allowed)
    (hnotin : ∀ b blk, env.lookup x = some (b, ty) → m.blocks b = some blk → ¬ allowed b) :
    LocalPtrSlot env m' x ty el v := by
  rcases h with ⟨b, blk, hl, hty, hb, hp, hsz, hal, hrb⟩
  have hn := hnotin b blk hl hb
  have hlt := lt_nextBlock_of_some hb
  refine ⟨b, blk, hl, hty, hfr.blocks_some_of_notin hb hn, hp, hsz, hal, ?_⟩
  rcases hrb with ⟨rfl, hr⟩ | ⟨bp, op, rfl, hr⟩
  · left; exact ⟨rfl, by rw [hfr.readBytes_of_notin hlt hn, hr]⟩
  · right; exact ⟨bp, op, rfl, by rw [hfr.readBytes_of_notin hlt hn, hr]⟩

theorem LocalFnPtrSlot.preserve_frameMod {env : Env} {m m' : Mem} {allowed : BlockId → Prop}
    {x : String} {ty rty : CTy} {ptys : List CTy} {va : Bool} {v : Val}
    (h : LocalFnPtrSlot env m x ty rty ptys va v) (hfr : FrameMod m m' allowed)
    (hnotin : ∀ b blk, env.lookup x = some (b, ty) → m.blocks b = some blk → ¬ allowed b) :
    LocalFnPtrSlot env m' x ty rty ptys va v := by
  rcases h with ⟨b, blk, hl, hty, hb, hp, hsz, hal, hrb⟩
  have hn := hnotin b blk hl hb
  have hlt := lt_nextBlock_of_some hb
  refine ⟨b, blk, hl, hty, hfr.blocks_some_of_notin hb hn, hp, hsz, hal, ?_⟩
  rcases hrb with ⟨rfl, hr⟩ | ⟨sym, rfl, hr⟩
  · left; exact ⟨rfl, by rw [hfr.readBytes_of_notin hlt hn, hr]⟩
  · right; exact ⟨sym, rfl, by rw [hfr.readBytes_of_notin hlt hn, hr]⟩

theorem UninitLocalIntSlot.preserve_roExt {env : Env} {m m' : Mem} {x : String} {ty : CTy}
    {k : IntKind} (h : UninitLocalIntSlot env m x ty k) (hro : ROExt m m') :
    UninitLocalIntSlot env m' x ty k :=
  h.preserve_frameMod (FrameMod.of_roExt hro (fun _ => False)) (fun _ _ _ _ h => h)

theorem LocalIntSlot.preserve_roExt {env : Env} {m m' : Mem} {x : String} {ty : CTy}
    {k : IntKind} {v : BitVec k.bits} (h : LocalIntSlot env m x ty k v) (hro : ROExt m m') :
    LocalIntSlot env m' x ty k v :=
  h.preserve_frameMod (FrameMod.of_roExt hro (fun _ => False)) (fun _ _ _ _ h => h)

theorem UninitLocalPtrSlot.preserve_roExt {env : Env} {m m' : Mem} {x : String} {ty el : CTy}
    (h : UninitLocalPtrSlot env m x ty el) (hro : ROExt m m') :
    UninitLocalPtrSlot env m' x ty el :=
  h.preserve_frameMod (FrameMod.of_roExt hro (fun _ => False)) (fun _ _ _ _ h => h)

theorem LocalPtrSlot.preserve_roExt {env : Env} {m m' : Mem} {x : String} {ty el : CTy} {v : Val}
    (h : LocalPtrSlot env m x ty el v) (hro : ROExt m m') :
    LocalPtrSlot env m' x ty el v :=
  h.preserve_frameMod (FrameMod.of_roExt hro (fun _ => False)) (fun _ _ _ _ h => h)

theorem LocalFnPtrSlot.preserve_roExt {env : Env} {m m' : Mem} {x : String} {ty rty : CTy}
    {ptys : List CTy} {va : Bool} {v : Val}
    (h : LocalFnPtrSlot env m x ty rty ptys va v) (hro : ROExt m m') :
    LocalFnPtrSlot env m' x ty rty ptys va v :=
  h.preserve_frameMod (FrameMod.of_roExt hro (fun _ => False)) (fun _ _ _ _ h => h)

theorem UninitLocalIntSlot.of_alloc (tags : TypeEnv) {env : Env} {m m' : Mem}
    {x : String} {ty : CTy} {k : IntKind}
    {base : UInt64} {bid : BlockId} {init : Nat → MemByte}
    {hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags ty)}
    {hba : base.toNat % max 1 (alignofTy tags ty) = 0}
    (hnc : ty.isConst = false) (hty : ty.unqual = .int k)
    (ha : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base init hsz hal hba = (bid, m')) :
    UninitLocalIntSlot ((x, bid, ty) :: env) m' x ty k := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm' : m' = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base init hsz hal hba).2 := (congrArg Prod.snd ha).symm
  subst hbid hm'
  let blk : Block := ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, base,
    init, hsz, hal, hba⟩
  have hb : (m.alloc _ _ .rw .stack base init hsz hal hba).2.blocks m.nextBlock = some blk :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_eq : max 1 (sizeofTy tags ty) = k.bytes := by
    rw [sizeofTy_eq_bytes hty]; exact Nat.max_eq_right (k_bytes_pos k)
  have hal_eq : max 1 (alignofTy tags ty) = k.align := by
    rw [alignofTy_eq_align hty]; exact Nat.max_eq_right (k_align_pos k)
  refine ⟨m.nextBlock, blk, ?_, hnc, hty, hb, rfl, ?_, ?_⟩
  · exact env_lookup_cons_eq x (m.nextBlock, ty) env
  · change k.bytes ≤ max 1 (sizeofTy tags ty)
    rw [hsz_eq]
    exact Nat.le_refl _
  · exact isAligned_zero_of_eq (k_align_pos k) hal_eq

theorem UninitLocalPtrSlot.of_alloc (tags : TypeEnv) {env : Env} {m m' : Mem}
    {x : String} {ty el : CTy}
    {base : UInt64} {bid : BlockId} {init : Nat → MemByte}
    {hsz : max 1 (sizeofTy tags ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags ty)}
    {hba : base.toNat % max 1 (alignofTy tags ty) = 0}
    (hnc : ty.isConst = false) (hty : ty.unqual = .ptr el)
    (ha : m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base init hsz hal hba = (bid, m')) :
    UninitLocalPtrSlot ((x, bid, ty) :: env) m' x ty el := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm' : m' = (m.alloc (max 1 (sizeofTy tags ty)) (max 1 (alignofTy tags ty))
      .rw .stack base init hsz hal hba).2 := (congrArg Prod.snd ha).symm
  subst hbid hm'
  let blk : Block := ⟨max 1 (sizeofTy tags ty), max 1 (alignofTy tags ty), .rw, .stack, base,
    init, hsz, hal, hba⟩
  have hb : (m.alloc _ _ .rw .stack base init hsz hal hba).2.blocks m.nextBlock = some blk :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_eq : max 1 (sizeofTy tags ty) = 8 := by
    rw [sizeofTy_eq_ptr hty]; decide
  have hal_eq : max 1 (alignofTy tags ty) = 8 := by
    rw [alignofTy_eq_ptr hty]; decide
  refine ⟨m.nextBlock, blk, ?_, hnc, hty, hb, rfl, ?_, ?_⟩
  · exact env_lookup_cons_eq x (m.nextBlock, ty) env
  · change 8 ≤ max 1 (sizeofTy tags ty)
    rw [hsz_eq]
    exact Nat.le_refl _
  · exact isAligned_zero_of_eq (by decide) hal_eq

private theorem readVal_int_of_readBytes (tags : TypeEnv) {m : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {ty : CTy} {k : IntKind} {v : BitVec k.bits}
    (hty : ty.unqual = .int k) (hb : m.blocks b = some blk)
    (hal : Mem.isAligned blk off k.align = true)
    (hrb : m.readBytes b off k.bytes = some (Mem.encodeInt k v)) :
    Sem.readVal tags m b off ty = some (.int k v) := by
  unfold Sem.readVal
  dsimp only
  rw [hty]
  simp only [CTy.intKind?, CTy.unqual, hb, hal, guard_true, hrb, decodeInt_encodeInt,
    bind, opt_bind_some, opt_pure_some]

private theorem readVal_ptr_of_readBytes (tags : TypeEnv) {m : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {ty el : CTy} (hty : ty.unqual = .ptr el) (hb : m.blocks b = some blk)
    (hal : Mem.isAligned blk off 8 = true) {v : Val}
    (hrb : (v = .null ∧ m.readBytes b off 8 = some Mem.encodeNull) ∨
      (∃ bp op, v = .ptr bp op ∧ m.readBytes b off 8 = some (Mem.encodePtr bp op))) :
    Sem.readVal tags m b off ty = some v := by
  unfold Sem.readVal
  dsimp only
  rw [hty]
  simp only [hb, hal, guard_true, bind, opt_bind_some]
  rcases hrb with ⟨rfl, hr⟩ | ⟨bp, op, rfl, hr⟩
  · simp only [hr, decodePtr_encodeNull, opt_bind_some, opt_pure_some]
  · simp only [hr, decodePtr_encodePtr, opt_bind_some, opt_pure_some]

private theorem readVal_fnPtr_of_readBytes (tags : TypeEnv) {m : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {ty rty : CTy} {ptys : List CTy} {va : Bool}
    (hty : ty.unqual = .fnPtr rty ptys va) (hb : m.blocks b = some blk)
    (hal : Mem.isAligned blk off 8 = true) {v : Val}
    (hrb : (v = .null ∧ m.readBytes b off 8 = some Mem.encodeNull) ∨
      (∃ sym, v = .fnPtr sym ∧ m.readBytes b off 8 = some (Mem.encodeFnPtr sym))) :
    Sem.readVal tags m b off ty = some v := by
  unfold Sem.readVal
  dsimp only
  rw [hty]
  simp only [hb, hal, guard_true, bind, opt_bind_some]
  rcases hrb with ⟨rfl, hr⟩ | ⟨sym, rfl, hr⟩
  · simp only [hr, decodePtr_encodeNull, opt_bind_some, opt_pure_some]
  · simp only [hr, decodePtr_encodeFnPtr, opt_bind_some, opt_pure_some]

theorem LocalIntSlot.readPlace_some (tags : TypeEnv) {env : Env} {m : Mem} {mods : ModSet}
    {x : String} {ty : CTy} {k : IntKind} {v : BitVec k.bits}
    (h : LocalIntSlot env m x ty k v)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 k.bytes = false) :
    ∃ b, env.lookup x = some (b, ty) ∧
      Sem.readPlace tags m mods .rval b 0 ty = some (.rval (.int k v) (.int k)) := by
  rcases h with ⟨b, blk, hl, hty, hb, _, _, hal, hrb⟩
  refine ⟨b, hl, ?_⟩
  have hnc : mods.conflicts b 0 (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_bytes hty]; exact hmod b hl
  have hrv : Sem.readVal tags m b 0 ty = some (.int k v) :=
    readVal_int_of_readBytes tags hty hb hal hrb
  have hdec : ty.decay = .int k := cty_decay_eq_int ty hty
  unfold Sem.readPlace
  dsimp only
  rw [hty]
  simp only [hnc, Bool.not_false, guard_true, hrv, Option.map_some, hdec, bind, opt_bind_some]

theorem LocalIntSlot.readPlace_nil_some (tags : TypeEnv) {env : Env} {m : Mem}
    {x : String} {ty : CTy} {k : IntKind} {v : BitVec k.bits}
    (h : LocalIntSlot env m x ty k v) :
    ∃ b, env.lookup x = some (b, ty) ∧
      Sem.readPlace tags m [] .rval b 0 ty = some (.rval (.int k v) (.int k)) :=
  h.readPlace_some tags (fun _ _ => modSet_conflicts_nil _ _ _)

theorem LocalPtrSlot.readPlace_some (tags : TypeEnv) {env : Env} {m : Mem} {mods : ModSet}
    {x : String} {ty el : CTy} {v : Val}
    (h : LocalPtrSlot env m x ty el v)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 8 = false) :
    ∃ b, env.lookup x = some (b, ty) ∧
      Sem.readPlace tags m mods .rval b 0 ty = some (.rval v (.ptr el)) := by
  rcases h with ⟨b, blk, hl, hty, hb, _, _, hal, hrb⟩
  refine ⟨b, hl, ?_⟩
  have hnc : mods.conflicts b 0 (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_ptr hty]; exact hmod b hl
  have hrv : Sem.readVal tags m b 0 ty = some v :=
    readVal_ptr_of_readBytes tags hty hb hal hrb
  have hdec : ty.decay = .ptr el := cty_decay_eq_ptr ty hty
  unfold Sem.readPlace
  dsimp only
  rw [hty]
  simp only [hnc, Bool.not_false, guard_true, hrv, Option.map_some, hdec, bind, opt_bind_some]

theorem LocalPtrSlot.readPlace_nil_some (tags : TypeEnv) {env : Env} {m : Mem}
    {x : String} {ty el : CTy} {v : Val}
    (h : LocalPtrSlot env m x ty el v) :
    ∃ b, env.lookup x = some (b, ty) ∧
      Sem.readPlace tags m [] .rval b 0 ty = some (.rval v (.ptr el)) :=
  h.readPlace_some tags (fun _ _ => modSet_conflicts_nil _ _ _)

theorem LocalFnPtrSlot.readPlace_some (tags : TypeEnv) {env : Env} {m : Mem} {mods : ModSet}
    {x : String} {ty rty : CTy} {ptys : List CTy} {va : Bool} {v : Val}
    (h : LocalFnPtrSlot env m x ty rty ptys va v)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 8 = false) :
    ∃ b, env.lookup x = some (b, ty) ∧
      Sem.readPlace tags m mods .rval b 0 ty = some (.rval v (.fnPtr rty ptys va)) := by
  rcases h with ⟨b, blk, hl, hty, hb, _, _, hal, hrb⟩
  refine ⟨b, hl, ?_⟩
  have hnc : mods.conflicts b 0 (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_fnPtr hty]; exact hmod b hl
  have hrv : Sem.readVal tags m b 0 ty = some v :=
    readVal_fnPtr_of_readBytes tags hty hb hal hrb
  have hdec : ty.decay = .fnPtr rty ptys va := cty_decay_eq_fnPtr ty hty
  unfold Sem.readPlace
  dsimp only
  rw [hty]
  simp only [hnc, Bool.not_false, guard_true, hrv, Option.map_some, hdec, bind, opt_bind_some]

theorem UninitLocalIntSlot.writeVal_int_some {env : Env} {m : Mem} {x : String} {ty : CTy}
    {k : IntKind} (h : UninitLocalIntSlot env m x ty k) (v : BitVec k.bits) :
    ∃ b m', env.lookup x = some (b, ty) ∧
      Sem.writeVal m b 0 ty (.int k v) = some m' ∧
      LocalIntSlot env m' x ty k v ∧ FrameMod m m' (· = b) := by
  rcases h with ⟨b, blk, hl, hnc, hty, hb, hp, hsz, hal⟩
  have hin : Mem.inBounds blk 0 k.bytes = true := inBounds_zero_of_le hsz
  have hvi : valAsInt? (.int k v) = some (k, if k.signed then v.toInt else (v.toNat : Int)) := rfl
  obtain ⟨m', hm'⟩ := C99.Proof.writeVal_int_some hnc hty hb hp hal hin hvi
  have hw_eq : Sem.writeVal m b 0 ty (.int k v) = m.writeBytes b 0 (Mem.encodeInt k v) := by
    unfold Sem.writeVal
    dsimp only
    rw [hty]
    simp only [hnc, Bool.not_false, guard_true, hb, CTy.intKind?, CTy.unqual, hal, hvi,
      bind, opt_bind_some]
    by_cases hs : k.signed
    · simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self]
  have hwb : m.writeBytes b 0 (Mem.encodeInt k v) = some m' := by rw [← hw_eq]; exact hm'
  obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hwb hb
  have hrb' : m'.readBytes b 0 k.bytes = some (Mem.encodeInt k v) := by
    have := readBytes_writeBytes_same hb hwb
    rw [encodeInt_length] at this
    exact this
  have hal'' : Mem.isAligned blk' 0 k.align = true := by
    unfold Mem.isAligned at hal ⊢
    rw [hba']; exact hal
  have hperm' : blk'.perm = .rw := by rw [hp', hp]
  have hsz'' : k.bytes ≤ blk'.size := by rw [hsz']; exact hsz
  exact ⟨b, m', hl, hm', ⟨b, blk', hl, hty, hb', hperm', hsz'', hal'', hrb'⟩,
    FrameMod.of_writeBytes hwb⟩

theorem UninitLocalIntSlot.writePlace_int_some (tags : TypeEnv) {env : Env} {m : Mem}
    {x : String} {ty : CTy} {k : IntKind} (h : UninitLocalIntSlot env m x ty k)
    {v : Val} {t' : CTy} {iv : BitVec k.bits}
    (hc : castVal m ty v = some (.int k iv)) :
    ∃ b m', env.lookup x = some (b, ty) ∧
      Sem.writePlace tags m b 0 ty (.rval v t') = some (.rval (.int k iv) ty, m') ∧
      LocalIntSlot env m' x ty k iv ∧ FrameMod m m' (· = b) := by
  have hty : ty.unqual = .int k := by rcases h with ⟨_, _, _, _, hty, _⟩; exact hty
  obtain ⟨b, m', hl, hwv, hslot, hfr⟩ := h.writeVal_int_some iv
  refine ⟨b, m', hl, ?_, hslot, hfr⟩
  unfold Sem.writePlace
  dsimp only
  rw [hty]
  simp only [hc, hwv, bind, opt_bind_some, opt_pure_some]

theorem LocalIntSlot.writePlace_int_some (tags : TypeEnv) {env : Env} {m : Mem}
    {x : String} {ty : CTy} {k : IntKind} {old : BitVec k.bits}
    (hnc : ty.isConst = false) (h : LocalIntSlot env m x ty k old)
    {v : Val} {t' : CTy} {iv : BitVec k.bits}
    (hc : castVal m ty v = some (.int k iv)) :
    ∃ b m', env.lookup x = some (b, ty) ∧
      Sem.writePlace tags m b 0 ty (.rval v t') = some (.rval (.int k iv) ty, m') ∧
      LocalIntSlot env m' x ty k iv ∧ FrameMod m m' (· = b) :=
  (h.to_uninit hnc).writePlace_int_some tags hc

theorem UninitLocalPtrSlot.writeVal_ptr_some {env : Env} {m : Mem} {x : String} {ty el : CTy}
    (h : UninitLocalPtrSlot env m x ty el) {v : Val}
    (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ b m', env.lookup x = some (b, ty) ∧
      Sem.writeVal m b 0 ty v = some m' ∧
      LocalPtrSlot env m' x ty el v ∧ FrameMod m m' (· = b) := by
  rcases h with ⟨b, blk, hl, hnc, hty, hb, hp, hsz, hal⟩
  have hin : Mem.inBounds blk 0 8 = true := inBounds_zero_of_le hsz
  obtain ⟨m', hm'⟩ := C99.Proof.writeVal_ptr_some hnc hty hb hp hal hin hv
  have hwb : (v = .null ∧ m.writeBytes b 0 Mem.encodeNull = some m') ∨
      (∃ bp op, v = .ptr bp op ∧ m.writeBytes b 0 (Mem.encodePtr bp op) = some m') := by
    unfold Sem.writeVal at hm'
    dsimp only at hm'
    rw [hty] at hm'
    simp only [hnc, Bool.not_false, guard_true, hb, hal, bind, opt_bind_some] at hm'
    rcases hv with rfl | ⟨bp, op, rfl⟩
    · exact Or.inl ⟨rfl, hm'⟩
    · exact Or.inr ⟨bp, op, rfl, hm'⟩
  rcases hwb with ⟨rfl, hwb0⟩ | ⟨bp, op, rfl, hwb0⟩
  · obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hwb0 hb
    have hrb' : m'.readBytes b 0 8 = some Mem.encodeNull := by
      have := readBytes_writeBytes_same hb hwb0
      rw [encodeNull_length] at this
      exact this
    have hal'' : Mem.isAligned blk' 0 8 = true := by
      unfold Mem.isAligned at hal ⊢; rw [hba']; exact hal
    exact ⟨b, m', hl, hm',
      ⟨b, blk', hl, hty, hb', by rw [hp', hp], by rw [hsz']; exact hsz, hal'', Or.inl ⟨rfl, hrb'⟩⟩,
      FrameMod.of_writeBytes hwb0⟩
  · obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hwb0 hb
    have hrb' : m'.readBytes b 0 8 = some (Mem.encodePtr bp op) := by
      have := readBytes_writeBytes_same hb hwb0
      rw [encodePtr_length] at this
      exact this
    have hal'' : Mem.isAligned blk' 0 8 = true := by
      unfold Mem.isAligned at hal ⊢; rw [hba']; exact hal
    exact ⟨b, m', hl, hm',
      ⟨b, blk', hl, hty, hb', by rw [hp', hp], by rw [hsz']; exact hsz, hal'',
        Or.inr ⟨bp, op, rfl, hrb'⟩⟩,
      FrameMod.of_writeBytes hwb0⟩

theorem UninitLocalPtrSlot.writePlace_ptr_some (tags : TypeEnv) {env : Env} {m : Mem}
    {x : String} {ty el : CTy} (h : UninitLocalPtrSlot env m x ty el)
    {v : Val} {t' : CTy} (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ b m', env.lookup x = some (b, ty) ∧
      Sem.writePlace tags m b 0 ty (.rval v t') = some (.rval v ty, m') ∧
      LocalPtrSlot env m' x ty el v ∧ FrameMod m m' (· = b) := by
  have hty : ty.unqual = .ptr el := by rcases h with ⟨_, _, _, _, hty, _⟩; exact hty
  have hc : castVal m ty v = some v := by
    rcases hv with rfl | ⟨bp, op, rfl⟩
    · exact castVal_null_eq hty
    · exact castVal_ptr_eq hty bp op
  obtain ⟨b, m', hl, hwv, hslot, hfr⟩ := h.writeVal_ptr_some hv
  refine ⟨b, m', hl, ?_, hslot, hfr⟩
  unfold Sem.writePlace
  dsimp only
  rw [hty]
  simp only [hc, hwv, bind, opt_bind_some, opt_pure_some]

theorem LocalPtrSlot.writePlace_ptr_some (tags : TypeEnv) {env : Env} {m : Mem}
    {x : String} {ty el : CTy} {old : Val}
    (hnc : ty.isConst = false) (h : LocalPtrSlot env m x ty el old)
    {v : Val} {t' : CTy} (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ b m', env.lookup x = some (b, ty) ∧
      Sem.writePlace tags m b 0 ty (.rval v t') = some (.rval v ty, m') ∧
      LocalPtrSlot env m' x ty el v ∧ FrameMod m m' (· = b) :=
  (h.to_uninit hnc).writePlace_ptr_some tags hv

/-! ### 2.4 Heap / Struct `FieldCell`, Typed `ArraySlice`, and `ByteSlice` -/

/-- A readable, aligned, in-bounds field/memory cell at `(b, off)` of type `ty` holding `v`. -/
def FieldCell (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) (v : Val) : Prop :=
  ∃ blk, m.blocks b = some blk ∧
    Mem.isAligned blk off (max 1 (alignofTy tags ty)) = true ∧
    Mem.inBounds blk off (sizeofTy tags ty) = true ∧
    Sem.readVal tags m b off ty = some v

/-- A mutable, readable, aligned, in-bounds field/memory cell at `(b, off)` holding `v`. -/
def FieldMutCell (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) (v : Val) : Prop :=
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧ ty.isConst = false ∧
    Mem.isAligned blk off (max 1 (alignofTy tags ty)) = true ∧
    Mem.inBounds blk off (sizeofTy tags ty) = true ∧
    Sem.readVal tags m b off ty = some v

/-- An uninitialized writable, aligned, in-bounds field/memory cell at `(b, off)` of type `ty`. -/
def FieldUninit (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) : Prop :=
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧ ty.isConst = false ∧
    Mem.isAligned blk off (max 1 (alignofTy tags ty)) = true ∧
    Mem.inBounds blk off (sizeofTy tags ty) = true

theorem FieldMutCell.to_cell {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (h : FieldMutCell tags m b off ty v) :
    FieldCell tags m b off ty v := by
  rcases h with ⟨blk, hb, _, _, hal, hin, hr⟩
  exact ⟨blk, hb, hal, hin, hr⟩

theorem FieldMutCell.to_uninit {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (h : FieldMutCell tags m b off ty v) :
    FieldUninit tags m b off ty := by
  rcases h with ⟨blk, hb, hp, hnc, hal, hin, _⟩
  exact ⟨blk, hb, hp, hnc, hal, hin⟩

theorem FieldCell.readVal_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v : Val} (h : FieldCell tags m b off ty v) :
    Sem.readVal tags m b off ty = some v := by
  rcases h with ⟨_, _, _, _, hr⟩; exact hr

theorem FieldCell.readPlace_int_some {tags : TypeEnv} {m : Mem} {mods : ModSet}
    {b : BlockId} {off : Int64} {ty : CTy} {k : IntKind} {v : Val}
    (hty : ty.unqual = .int k) (h : FieldCell tags m b off ty v)
    (hmod : mods.conflicts b off k.bytes = false) :
    Sem.readPlace tags m mods .rval b off ty = some (.rval v (.int k)) := by
  have hr := h.readVal_some
  have hnc : mods.conflicts b off (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_bytes hty]; exact hmod
  have hdec : ty.decay = .int k := cty_decay_eq_int ty hty
  unfold Sem.readPlace
  dsimp only
  rw [hty]
  simp only [hnc, Bool.not_false, guard_true, hr, Option.map_some, hdec, bind, opt_bind_some]

theorem FieldCell.readPlace_ptr_some {tags : TypeEnv} {m : Mem} {mods : ModSet}
    {b : BlockId} {off : Int64} {ty el : CTy} {v : Val}
    (hty : ty.unqual = .ptr el) (h : FieldCell tags m b off ty v)
    (hmod : mods.conflicts b off 8 = false) :
    Sem.readPlace tags m mods .rval b off ty = some (.rval v (.ptr el)) := by
  have hr := h.readVal_some
  have hnc : mods.conflicts b off (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_ptr hty]; exact hmod
  have hdec : ty.decay = .ptr el := cty_decay_eq_ptr ty hty
  unfold Sem.readPlace
  dsimp only
  rw [hty]
  simp only [hnc, Bool.not_false, guard_true, hr, Option.map_some, hdec, bind, opt_bind_some]

theorem FieldCell.readPlace_fnPtr_some {tags : TypeEnv} {m : Mem} {mods : ModSet}
    {b : BlockId} {off : Int64} {ty rty : CTy} {ptys : List CTy} {va : Bool} {v : Val}
    (hty : ty.unqual = .fnPtr rty ptys va) (h : FieldCell tags m b off ty v)
    (hmod : mods.conflicts b off 8 = false) :
    Sem.readPlace tags m mods .rval b off ty = some (.rval v (.fnPtr rty ptys va)) := by
  have hr := h.readVal_some
  have hnc : mods.conflicts b off (sizeofTy tags ty) = false := by
    rw [sizeofTy_eq_fnPtr hty]; exact hmod
  have hdec : ty.decay = .fnPtr rty ptys va := cty_decay_eq_fnPtr ty hty
  unfold Sem.readPlace
  dsimp only
  rw [hty]
  simp only [hnc, Bool.not_false, guard_true, hr, Option.map_some, hdec, bind, opt_bind_some]

theorem FieldCell.preserve_frameMod {tags : TypeEnv} {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (h : FieldCell tags m b off ty v) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    FieldCell tags m' b off ty v := by
  rcases h with ⟨blk, hb, hal, hin, hr⟩
  have hlt := lt_nextBlock_of_some hb
  exact ⟨blk, hfr.blocks_some_of_notin hb hnotin, hal, hin,
    by rw [hfr.readVal_of_notin tags hlt hnotin]; exact hr⟩

theorem FieldMutCell.preserve_frameMod {tags : TypeEnv} {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {off : Int64} {ty : CTy} {v : Val}
    (h : FieldMutCell tags m b off ty v) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    FieldMutCell tags m' b off ty v := by
  rcases h with ⟨blk, hb, hp, hnc, hal, hin, hr⟩
  have hlt := lt_nextBlock_of_some hb
  exact ⟨blk, hfr.blocks_some_of_notin hb hnotin, hp, hnc, hal, hin,
    by rw [hfr.readVal_of_notin tags hlt hnotin]; exact hr⟩

theorem FieldUninit.preserve_frameMod {tags : TypeEnv} {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {off : Int64} {ty : CTy}
    (h : FieldUninit tags m b off ty) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    FieldUninit tags m' b off ty := by
  rcases h with ⟨blk, hb, hp, hnc, hal, hin⟩
  exact ⟨blk, hfr.blocks_some_of_notin hb hnotin, hp, hnc, hal, hin⟩

theorem FieldCell.preserve_writeVal_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {off woff : Int64} {ty wty : CTy} {v wv : Val}
    (h : FieldCell tags m b off ty v) (hw : Sem.writeVal m b woff wty wv = some m')
    (hdisj : woff.toInt + (sizeofTy tags wty : Int) ≤ off.toInt ∨
      off.toInt + (max 1 (sizeofTy tags ty) : Int) ≤ woff.toInt) :
    FieldCell tags m' b off ty v := by
  rcases h with ⟨blk, hb, hal, hin, hr⟩
  obtain ⟨bs, _, hbs⟩ := writeVal_writeBytes_exact tags hw
  obtain ⟨blk', hb', _, _, hsz', _, hba', _⟩ := writeBytes_preserves_perm hbs hb
  have hal'' : Mem.isAligned blk' off (max 1 (alignofTy tags ty)) = true := by
    unfold Mem.isAligned at hal ⊢; rw [hba']; exact hal
  have hin'' : Mem.inBounds blk' off (sizeofTy tags ty) = true := by
    unfold Mem.inBounds at hin ⊢; rw [hsz']; exact hin
  exact ⟨blk', hb', hal'', hin'', by rw [readVal_writeVal_disjoint tags hw hdisj]; exact hr⟩

theorem FieldMutCell.preserve_writeVal_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId}
    {off woff : Int64} {ty wty : CTy} {v wv : Val}
    (h : FieldMutCell tags m b off ty v) (hw : Sem.writeVal m b woff wty wv = some m')
    (hdisj : woff.toInt + (sizeofTy tags wty : Int) ≤ off.toInt ∨
      off.toInt + (max 1 (sizeofTy tags ty) : Int) ≤ woff.toInt) :
    FieldMutCell tags m' b off ty v := by
  rcases h with ⟨blk, hb, hp, hnc, hal, hin, hr⟩
  obtain ⟨bs, _, hbs⟩ := writeVal_writeBytes_exact tags hw
  obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hbs hb
  have hal'' : Mem.isAligned blk' off (max 1 (alignofTy tags ty)) = true := by
    unfold Mem.isAligned at hal ⊢; rw [hba']; exact hal
  have hin'' : Mem.inBounds blk' off (sizeofTy tags ty) = true := by
    unfold Mem.inBounds at hin ⊢; rw [hsz']; exact hin
  exact ⟨blk', hb', by rw [hp', hp], hnc, hal'', hin'',
    by rw [readVal_writeVal_disjoint tags hw hdisj]; exact hr⟩

theorem FieldUninit.writeVal_int_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {k : IntKind} (hty : ty.unqual = .int k)
    (h : FieldUninit tags m b off ty) (v : BitVec k.bits) :
    ∃ m', Sem.writeVal m b off ty (.int k v) = some m' ∧
      FieldMutCell tags m' b off ty (.int k v) ∧ FrameMod m m' (· = b) := by
  rcases h with ⟨blk, hb, hp, hnc, hal, hin⟩
  have hal_eq : max 1 (alignofTy tags ty) = k.align := by
    rw [alignofTy_eq_align hty]; exact Nat.max_eq_right (k_align_pos k)
  have hsz_eq : sizeofTy tags ty = k.bytes := sizeofTy_eq_bytes hty
  have halk : Mem.isAligned blk off k.align = true := by rw [← hal_eq]; exact hal
  have hink : Mem.inBounds blk off k.bytes = true := by rw [← hsz_eq]; exact hin
  have hvi : valAsInt? (.int k v) = some (k, if k.signed then v.toInt else (v.toNat : Int)) := rfl
  obtain ⟨m', hm'⟩ := C99.Proof.writeVal_int_some hnc hty hb hp halk hink hvi
  have hw_eq : Sem.writeVal m b off ty (.int k v) = m.writeBytes b off (Mem.encodeInt k v) := by
    unfold Sem.writeVal
    dsimp only
    rw [hty]
    simp only [hnc, Bool.not_false, guard_true, hb, CTy.intKind?, CTy.unqual, halk, hvi,
      bind, opt_bind_some]
    by_cases hs : k.signed
    · simp only [hs, ↓reduceIte, bitVec_ofInt_toInt]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat_self]
  have hwb : m.writeBytes b off (Mem.encodeInt k v) = some m' := by rw [← hw_eq]; exact hm'
  obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hwb hb
  have halk' : Mem.isAligned blk' off k.align = true := by
    unfold Mem.isAligned at halk ⊢; rw [hba']; exact halk
  have hal' : Mem.isAligned blk' off (max 1 (alignofTy tags ty)) = true := by
    rw [hal_eq]; exact halk'
  have hin' : Mem.inBounds blk' off (sizeofTy tags ty) = true := by
    unfold Mem.inBounds at hin ⊢; rw [hsz']; exact hin
  have hrb' : m'.readBytes b off k.bytes = some (Mem.encodeInt k v) := by
    have := readBytes_writeBytes_same hb hwb
    rw [encodeInt_length] at this
    exact this
  have hr' : Sem.readVal tags m' b off ty = some (.int k v) :=
    readVal_int_of_readBytes tags hty hb' halk' hrb'
  exact ⟨m', hm', ⟨blk', hb', by rw [hp', hp], hnc, hal', hin', hr'⟩,
    FrameMod.of_writeBytes hwb⟩

theorem FieldUninit.writePlace_int_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {k : IntKind} (hty : ty.unqual = .int k)
    (h : FieldUninit tags m b off ty) {v : Val} {t' : CTy} {iv : BitVec k.bits}
    (hc : castVal m ty v = some (.int k iv)) :
    ∃ m', Sem.writePlace tags m b off ty (.rval v t') = some (.rval (.int k iv) ty, m') ∧
      FieldMutCell tags m' b off ty (.int k iv) ∧ FrameMod m m' (· = b) := by
  obtain ⟨m', hwv, hcell, hfr⟩ := h.writeVal_int_some hty iv
  refine ⟨m', ?_, hcell, hfr⟩
  unfold Sem.writePlace
  dsimp only
  rw [hty]
  simp only [hc, hwv, bind, opt_bind_some, opt_pure_some]

theorem FieldMutCell.writePlace_int_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {k : IntKind} {old : Val} (hty : ty.unqual = .int k)
    (h : FieldMutCell tags m b off ty old) {v : Val} {t' : CTy} {iv : BitVec k.bits}
    (hc : castVal m ty v = some (.int k iv)) :
    ∃ m', Sem.writePlace tags m b off ty (.rval v t') = some (.rval (.int k iv) ty, m') ∧
      FieldMutCell tags m' b off ty (.int k iv) ∧ FrameMod m m' (· = b) :=
  h.to_uninit.writePlace_int_some hty hc

theorem FieldUninit.writeVal_ptr_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty el : CTy} (hty : ty.unqual = .ptr el)
    (h : FieldUninit tags m b off ty) {v : Val} (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ m', Sem.writeVal m b off ty v = some m' ∧
      FieldMutCell tags m' b off ty v ∧ FrameMod m m' (· = b) := by
  rcases h with ⟨blk, hb, hp, hnc, hal, hin⟩
  have hal_eq : max 1 (alignofTy tags ty) = 8 := by
    rw [alignofTy_eq_ptr hty]; decide
  have hsz_eq : sizeofTy tags ty = 8 := sizeofTy_eq_ptr hty
  have hal8 : Mem.isAligned blk off 8 = true := by rw [← hal_eq]; exact hal
  have hin8 : Mem.inBounds blk off 8 = true := by rw [← hsz_eq]; exact hin
  obtain ⟨m', hm'⟩ := C99.Proof.writeVal_ptr_some hnc hty hb hp hal8 hin8 hv
  have hwb : (v = .null ∧ m.writeBytes b off Mem.encodeNull = some m') ∨
      (∃ bp op, v = .ptr bp op ∧ m.writeBytes b off (Mem.encodePtr bp op) = some m') := by
    unfold Sem.writeVal at hm'
    dsimp only at hm'
    rw [hty] at hm'
    simp only [hnc, Bool.not_false, guard_true, hb, hal8, bind, opt_bind_some] at hm'
    rcases hv with rfl | ⟨bp, op, rfl⟩
    · exact Or.inl ⟨rfl, hm'⟩
    · exact Or.inr ⟨bp, op, rfl, hm'⟩
  rcases hwb with ⟨rfl, hwb0⟩ | ⟨bp, op, rfl, hwb0⟩
  · obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hwb0 hb
    have hal8' : Mem.isAligned blk' off 8 = true := by
      unfold Mem.isAligned at hal8 ⊢; rw [hba']; exact hal8
    have hal' : Mem.isAligned blk' off (max 1 (alignofTy tags ty)) = true := by
      rw [hal_eq]; exact hal8'
    have hin' : Mem.inBounds blk' off (sizeofTy tags ty) = true := by
      unfold Mem.inBounds at hin ⊢; rw [hsz']; exact hin
    have hrb' : m'.readBytes b off 8 = some Mem.encodeNull := by
      have := readBytes_writeBytes_same hb hwb0
      rw [encodeNull_length] at this
      exact this
    have hr' : Sem.readVal tags m' b off ty = some .null :=
      readVal_ptr_of_readBytes tags hty hb' hal8' (Or.inl ⟨rfl, hrb'⟩)
    exact ⟨m', hm', ⟨blk', hb', by rw [hp', hp], hnc, hal', hin', hr'⟩,
      FrameMod.of_writeBytes hwb0⟩
  · obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hwb0 hb
    have hal8' : Mem.isAligned blk' off 8 = true := by
      unfold Mem.isAligned at hal8 ⊢; rw [hba']; exact hal8
    have hal' : Mem.isAligned blk' off (max 1 (alignofTy tags ty)) = true := by
      rw [hal_eq]; exact hal8'
    have hin' : Mem.inBounds blk' off (sizeofTy tags ty) = true := by
      unfold Mem.inBounds at hin ⊢; rw [hsz']; exact hin
    have hrb' : m'.readBytes b off 8 = some (Mem.encodePtr bp op) := by
      have := readBytes_writeBytes_same hb hwb0
      rw [encodePtr_length] at this
      exact this
    have hr' : Sem.readVal tags m' b off ty = some (.ptr bp op) :=
      readVal_ptr_of_readBytes tags hty hb' hal8' (Or.inr ⟨bp, op, rfl, hrb'⟩)
    exact ⟨m', hm', ⟨blk', hb', by rw [hp', hp], hnc, hal', hin', hr'⟩,
      FrameMod.of_writeBytes hwb0⟩

theorem FieldUninit.writePlace_ptr_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty el : CTy} (hty : ty.unqual = .ptr el)
    (h : FieldUninit tags m b off ty) {v : Val} {t' : CTy}
    (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ m', Sem.writePlace tags m b off ty (.rval v t') = some (.rval v ty, m') ∧
      FieldMutCell tags m' b off ty v ∧ FrameMod m m' (· = b) := by
  have hc : castVal m ty v = some v := by
    rcases hv with rfl | ⟨bp, op, rfl⟩
    · exact castVal_null_eq hty
    · exact castVal_ptr_eq hty bp op
  obtain ⟨m', hwv, hcell, hfr⟩ := h.writeVal_ptr_some hty hv
  refine ⟨m', ?_, hcell, hfr⟩
  unfold Sem.writePlace
  dsimp only
  rw [hty]
  simp only [hc, hwv, bind, opt_bind_some, opt_pure_some]

theorem FieldMutCell.writePlace_ptr_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {ty el : CTy} {old : Val} (hty : ty.unqual = .ptr el)
    (h : FieldMutCell tags m b off ty old) {v : Val} {t' : CTy}
    (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ m', Sem.writePlace tags m b off ty (.rval v t') = some (.rval v ty, m') ∧
      FieldMutCell tags m' b off ty v ∧ FrameMod m m' (· = b) :=
  h.to_uninit.writePlace_ptr_some hty hv

/-- A readable typed array slice `[b + baseOff .. b + baseOff + elems.length * sizeof(el))`. -/
def ArraySlice (tags : TypeEnv) (m : Mem) (b : BlockId) (baseOff : Int64) (el : CTy)
    (elems : List Val) : Prop :=
  0 < sizeofTy tags el ∧
  ∃ blk, m.blocks b = some blk ∧
    0 ≤ baseOff.toInt ∧
    baseOff.toInt + (elems.length * sizeofTy tags el : Int) ≤ (blk.size : Int) ∧
    (∀ i, i < elems.length →
      Mem.isAligned blk (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int)))
        (max 1 (alignofTy tags el)) = true) ∧
    ∀ (i : Nat) (hi : i < elems.length),
      Sem.readVal tags m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el =
        some elems[i]

/-- A mutable, readable typed array slice `[b + baseOff .. b + baseOff + elems.length * sizeof(el))`. -/
def MutArraySlice (tags : TypeEnv) (m : Mem) (b : BlockId) (baseOff : Int64) (el : CTy)
    (elems : List Val) : Prop :=
  0 < sizeofTy tags el ∧ el.isConst = false ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    0 ≤ baseOff.toInt ∧
    baseOff.toInt + (elems.length * sizeofTy tags el : Int) ≤ (blk.size : Int) ∧
    (∀ i, i < elems.length →
      Mem.isAligned blk (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int)))
        (max 1 (alignofTy tags el)) = true) ∧
    ∀ (i : Nat) (hi : i < elems.length),
      Sem.readVal tags m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el =
        some elems[i]

theorem MutArraySlice.to_slice {tags : TypeEnv} {m : Mem} {b : BlockId} {baseOff : Int64}
    {el : CTy} {elems : List Val} (h : MutArraySlice tags m b baseOff el elems) :
    ArraySlice tags m b baseOff el elems := by
  rcases h with ⟨hpos, _, blk, hb, _, hlo, hhi, hal, hread⟩
  exact ⟨hpos, blk, hb, hlo, hhi, hal, hread⟩

private theorem int64_ofInt_toInt_of_lt {x : Int} (hlo : 0 ≤ x) (hhi : x < 2 ^ 63) :
    (Int64.ofInt x).toInt = x := by
  change (BitVec.ofInt 64 x).toInt = x
  exact bitVec_ofInt_toInt_of_range (by decide) (by omega) hhi

private theorem mul_add_le_mul_of_lt {i n s : Nat} (hi : i < n) :
    (i : Int) * (s : Int) + (s : Int) ≤ (n : Int) * (s : Int) := by
  have h1 : (i + 1) * s ≤ n * s := Nat.mul_le_mul_right s hi
  rw [Nat.add_mul, Nat.one_mul] at h1
  have h2 : ((i * s + s : Nat) : Int) ≤ (n * s : Int) := Int.ofNat_le.mpr h1
  rw [Int.natCast_add, Int.natCast_mul] at h2
  exact h2

theorem ArraySlice.elemCell {tags : TypeEnv} {m : Mem} {b : BlockId} {baseOff : Int64}
    {el : CTy} {elems : List Val} (h : ArraySlice tags m b baseOff el elems)
    (i : Nat) (hi : i < elems.length) :
    FieldCell tags m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el elems[i] := by
  rcases h with ⟨_, blk, hb, hlo, hhi, hal, hread⟩
  have hblk_sz : (blk.size : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    exact_mod_cast this
  have hmul_nonneg : 0 ≤ (i : Int) * (sizeofTy tags el : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hmul_le := mul_add_le_mul_of_lt (s := sizeofTy tags el) hi
  have hsum_hi : baseOff.toInt + (i : Int) * (sizeofTy tags el : Int) + (sizeofTy tags el : Int) ≤ (blk.size : Int) := by
    omega
  have hoff_nonneg : 0 ≤ baseOff.toInt + (i * sizeofTy tags el : Int) := by omega
  have hoff_lt : baseOff.toInt + (i * sizeofTy tags el : Int) < 2 ^ 63 := by omega
  have hoff_toInt : (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt =
      baseOff.toInt + (i * sizeofTy tags el : Int) := int64_ofInt_toInt_of_lt hoff_nonneg hoff_lt
  have hin : Mem.inBounds blk (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) (sizeofTy tags el) = true := by
    unfold Mem.inBounds
    simp only [hoff_toInt, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hoff_nonneg, by omega⟩
  exact ⟨blk, hb, hal i hi, hin, hread i hi⟩

theorem MutArraySlice.elemMutCell {tags : TypeEnv} {m : Mem} {b : BlockId} {baseOff : Int64}
    {el : CTy} {elems : List Val} (h : MutArraySlice tags m b baseOff el elems)
    (i : Nat) (hi : i < elems.length) :
    FieldMutCell tags m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el elems[i] := by
  obtain ⟨blk0, hb0, hal0, hin0, hr0⟩ := h.to_slice.elemCell i hi
  rcases h with ⟨_, hnc, blk, hb, hp, _⟩
  rw [hb0] at hb
  cases hb
  exact ⟨blk0, hb0, hp, hnc, hal0, hin0, hr0⟩

theorem ArraySlice.readVal_elem {tags : TypeEnv} {m : Mem} {b : BlockId} {baseOff : Int64}
    {el : CTy} {elems : List Val} (h : ArraySlice tags m b baseOff el elems)
    (i : Nat) (hi : i < elems.length) :
    Sem.readVal tags m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el =
      some elems[i] :=
  (h.elemCell i hi).readVal_some

theorem ArraySlice.preserve_frameMod {tags : TypeEnv} {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {baseOff : Int64} {el : CTy} {elems : List Val}
    (h : ArraySlice tags m b baseOff el elems) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    ArraySlice tags m' b baseOff el elems := by
  rcases h with ⟨hpos, blk, hb, hlo, hhi, hal, hread⟩
  have hlt := lt_nextBlock_of_some hb
  refine ⟨hpos, blk, hfr.blocks_some_of_notin hb hnotin, hlo, hhi, hal, fun i hi => ?_⟩
  rw [hfr.readVal_of_notin tags hlt hnotin]
  exact hread i hi

theorem MutArraySlice.preserve_frameMod {tags : TypeEnv} {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {baseOff : Int64} {el : CTy} {elems : List Val}
    (h : MutArraySlice tags m b baseOff el elems) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    MutArraySlice tags m' b baseOff el elems := by
  rcases h with ⟨hpos, hnc, blk, hb, hp, hlo, hhi, hal, hread⟩
  have hlt := lt_nextBlock_of_some hb
  refine ⟨hpos, hnc, blk, hfr.blocks_some_of_notin hb hnotin, hp, hlo, hhi, hal, fun i hi => ?_⟩
  rw [hfr.readVal_of_notin tags hlt hnotin]
  exact hread i hi

theorem MutArraySlice.writeElemVal_int {tags : TypeEnv} {m : Mem} {b : BlockId} {baseOff : Int64}
    {el : CTy} {k : IntKind} (hel : el.unqual = .int k) {elems : List Val}
    (h : MutArraySlice tags m b baseOff el elems) (i : Nat) (hi : i < elems.length)
    (v : BitVec k.bits) :
    ∃ m', Sem.writeVal m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el (.int k v) = some m' ∧
      MutArraySlice tags m' b baseOff el (elems.set i (.int k v)) ∧
      FrameMod m m' (· = b) := by
  have hcell := h.elemMutCell i hi
  obtain ⟨m', hw, hcell', hfr⟩ := hcell.to_uninit.writeVal_int_some hel v
  rcases h with ⟨hpos, hnc, blk, hb, hp, hlo, hhi, hal, hread⟩
  obtain ⟨bs, hlen, hbs⟩ := writeVal_writeBytes_exact tags hw
  obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hbs hb
  have hal_eq : ∀ off al, Mem.isAligned blk' off al = Mem.isAligned blk off al := by
    intro off al; unfold Mem.isAligned; rw [hba']
  have hblk_sz : (blk.size : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    exact_mod_cast this
  have hi_mul_nonneg : 0 ≤ (i : Int) * (sizeofTy tags el : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hi_mul_le := mul_add_le_mul_of_lt (s := sizeofTy tags el) hi
  have hi_off_nonneg : 0 ≤ baseOff.toInt + (i * sizeofTy tags el : Int) := by omega
  have hi_off_lt : baseOff.toInt + (i * sizeofTy tags el : Int) < 2 ^ 63 := by omega
  have hi_off_toInt : (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt =
      baseOff.toInt + (i * sizeofTy tags el : Int) := int64_ofInt_toInt_of_lt hi_off_nonneg hi_off_lt
  refine ⟨m', hw, ⟨hpos, hnc, blk', hb', by rw [hp', hp], hlo, ?_, ?_, ?_⟩, hfr⟩
  · rw [hsz', List.length_set]; exact hhi
  · intro j hj
    rw [List.length_set] at hj
    rw [hal_eq]
    exact hal j hj
  · intro j hj
    have hj' : j < elems.length := by rw [List.length_set] at hj; exact hj
    by_cases heq : j = i
    · subst heq
      rw [List.getElem_set_self]
      exact hcell'.to_cell.readVal_some
    · rw [List.getElem_set_ne (Ne.symm heq)]
      have hj_mul_nonneg : 0 ≤ (j : Int) * (sizeofTy tags el : Int) :=
        Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      have hj_mul_le := mul_add_le_mul_of_lt (s := sizeofTy tags el) hj'
      have hj_off_nonneg : 0 ≤ baseOff.toInt + (j * sizeofTy tags el : Int) := by omega
      have hj_off_lt : baseOff.toInt + (j * sizeofTy tags el : Int) < 2 ^ 63 := by omega
      have hj_off_toInt : (Int64.ofInt (baseOff.toInt + (j * sizeofTy tags el : Int))).toInt =
          baseOff.toInt + (j * sizeofTy tags el : Int) := int64_ofInt_toInt_of_lt hj_off_nonneg hj_off_lt
      have hmax : max (1 : Int) (sizeofTy tags el : Int) = (sizeofTy tags el : Int) := by omega
      have hdisj : (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt + (sizeofTy tags el : Int) ≤
            (Int64.ofInt (baseOff.toInt + (j * sizeofTy tags el : Int))).toInt ∨
          (Int64.ofInt (baseOff.toInt + (j * sizeofTy tags el : Int))).toInt + (max 1 (sizeofTy tags el) : Int) ≤
            (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt := by
        rw [hi_off_toInt, hj_off_toInt, hmax]
        rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · right
          have hmul := mul_add_le_mul_of_lt (s := sizeofTy tags el) hlt
          omega
        · left
          have hmul := mul_add_le_mul_of_lt (s := sizeofTy tags el) hgt
          omega
      rw [readVal_writeVal_disjoint tags hw hdisj]
      exact hread j hj'

theorem MutArraySlice.writeElemVal_ptr {tags : TypeEnv} {m : Mem} {b : BlockId} {baseOff : Int64}
    {el elemTy : CTy} (hel : el.unqual = .ptr elemTy) {elems : List Val}
    (h : MutArraySlice tags m b baseOff el elems) (i : Nat) (hi : i < elems.length)
    {v : Val} (hv : v = .null ∨ ∃ bp op, v = .ptr bp op) :
    ∃ m', Sem.writeVal m b (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))) el v = some m' ∧
      MutArraySlice tags m' b baseOff el (elems.set i v) ∧
      FrameMod m m' (· = b) := by
  have hcell := h.elemMutCell i hi
  obtain ⟨m', hw, hcell', hfr⟩ := hcell.to_uninit.writeVal_ptr_some hel hv
  rcases h with ⟨hpos, hnc, blk, hb, hp, hlo, hhi, hal, hread⟩
  obtain ⟨bs, hlen, hbs⟩ := writeVal_writeBytes_exact tags hw
  obtain ⟨blk', hb', _, hp', hsz', _, hba', _⟩ := writeBytes_preserves_perm hbs hb
  have hal_eq : ∀ off al, Mem.isAligned blk' off al = Mem.isAligned blk off al := by
    intro off al; unfold Mem.isAligned; rw [hba']
  have hblk_sz : (blk.size : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    exact_mod_cast this
  have hi_mul_nonneg : 0 ≤ (i : Int) * (sizeofTy tags el : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hi_mul_le := mul_add_le_mul_of_lt (s := sizeofTy tags el) hi
  have hi_off_nonneg : 0 ≤ baseOff.toInt + (i * sizeofTy tags el : Int) := by omega
  have hi_off_lt : baseOff.toInt + (i * sizeofTy tags el : Int) < 2 ^ 63 := by omega
  have hi_off_toInt : (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt =
      baseOff.toInt + (i * sizeofTy tags el : Int) := int64_ofInt_toInt_of_lt hi_off_nonneg hi_off_lt
  refine ⟨m', hw, ⟨hpos, hnc, blk', hb', by rw [hp', hp], hlo, ?_, ?_, ?_⟩, hfr⟩
  · rw [hsz', List.length_set]; exact hhi
  · intro j hj
    rw [List.length_set] at hj
    rw [hal_eq]
    exact hal j hj
  · intro j hj
    have hj' : j < elems.length := by rw [List.length_set] at hj; exact hj
    by_cases heq : j = i
    · subst heq
      rw [List.getElem_set_self]
      exact hcell'.to_cell.readVal_some
    · rw [List.getElem_set_ne (Ne.symm heq)]
      have hj_mul_nonneg : 0 ≤ (j : Int) * (sizeofTy tags el : Int) :=
        Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      have hj_mul_le := mul_add_le_mul_of_lt (s := sizeofTy tags el) hj'
      have hj_off_nonneg : 0 ≤ baseOff.toInt + (j * sizeofTy tags el : Int) := by omega
      have hj_off_lt : baseOff.toInt + (j * sizeofTy tags el : Int) < 2 ^ 63 := by omega
      have hj_off_toInt : (Int64.ofInt (baseOff.toInt + (j * sizeofTy tags el : Int))).toInt =
          baseOff.toInt + (j * sizeofTy tags el : Int) := int64_ofInt_toInt_of_lt hj_off_nonneg hj_off_lt
      have hmax : max (1 : Int) (sizeofTy tags el : Int) = (sizeofTy tags el : Int) := by omega
      have hdisj : (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt + (sizeofTy tags el : Int) ≤
            (Int64.ofInt (baseOff.toInt + (j * sizeofTy tags el : Int))).toInt ∨
          (Int64.ofInt (baseOff.toInt + (j * sizeofTy tags el : Int))).toInt + (max 1 (sizeofTy tags el) : Int) ≤
            (Int64.ofInt (baseOff.toInt + (i * sizeofTy tags el : Int))).toInt := by
        rw [hi_off_toInt, hj_off_toInt, hmax]
        rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
        · right
          have hmul := mul_add_le_mul_of_lt (s := sizeofTy tags el) hlt
          omega
        · left
          have hmul := mul_add_le_mul_of_lt (s := sizeofTy tags el) hgt
          omega
      rw [readVal_writeVal_disjoint tags hw hdisj]
      exact hread j hj'

private theorem allConcreteBytes_map_byte (bs : List UInt8) :
    Libc.allConcreteBytes (bs.map MemByte.byte) = some bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, Libc.allConcreteBytes, ih, bind, opt_bind_some, opt_pure_some]

/-- A readable concrete byte slice `[b + baseOff .. b + baseOff + bytes.length)` in memory. -/
def ByteSlice (m : Mem) (b : BlockId) (baseOff : Int64) (bytes : List UInt8) : Prop :=
  ∃ blk, m.blocks b = some blk ∧
    0 ≤ baseOff.toInt ∧
    baseOff.toInt + (bytes.length : Int) ≤ (blk.size : Int) ∧
    m.readBytes b baseOff bytes.length = some (bytes.map MemByte.byte)

/-- A mutable, in-bounds byte slice `[b + baseOff .. b + baseOff + len)` in memory. -/
def MutByteSlice (m : Mem) (b : BlockId) (baseOff : Int64) (len : Nat) : Prop :=
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    0 ≤ baseOff.toInt ∧
    baseOff.toInt + (len : Int) ≤ (blk.size : Int)

theorem ByteSlice.to_mut {m : Mem} {b : BlockId} {baseOff : Int64} {bytes : List UInt8}
    (hp : ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw)
    (h : ByteSlice m b baseOff bytes) :
    MutByteSlice m b baseOff bytes.length := by
  rcases h with ⟨blk, hb, hlo, hhi, _⟩
  rcases hp with ⟨blk0, hb0, hp0⟩
  rw [hb] at hb0
  cases hb0
  exact ⟨blk, hb, hp0, hlo, hhi⟩

theorem ByteSlice.validReadableRange {m : Mem} {b : BlockId} {baseOff : Int64}
    {bytes : List UInt8} (h : ByteSlice m b baseOff bytes) :
    Libc.validReadableRange m b baseOff bytes.length = true := by
  rcases h with ⟨blk, hb, hlo, hhi, _⟩
  unfold Libc.validReadableRange Mem.inBounds
  simp only [hb, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlo, by omega⟩

theorem ByteSlice.allConcreteBytes {m : Mem} {b : BlockId} {baseOff : Int64}
    {bytes : List UInt8} (h : ByteSlice m b baseOff bytes) :
    ∃ mbs, m.readBytes b baseOff bytes.length = some mbs ∧
      Libc.allConcreteBytes mbs = some bytes := by
  rcases h with ⟨_, _, _, _, hr⟩
  exact ⟨bytes.map MemByte.byte, hr, allConcreteBytes_map_byte bytes⟩

theorem MutByteSlice.validWritableRange {m : Mem} {b : BlockId} {baseOff : Int64} {len : Nat}
    (h : MutByteSlice m b baseOff len) :
    Libc.validWritableRange m b baseOff len = true := by
  rcases h with ⟨blk, hb, hp, hlo, hhi⟩
  unfold Libc.validWritableRange Mem.inBounds
  simp only [hb, hp, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlo, by omega⟩

theorem ByteSlice.preserve_frameMod {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {baseOff : Int64} {bytes : List UInt8}
    (h : ByteSlice m b baseOff bytes) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    ByteSlice m' b baseOff bytes := by
  rcases h with ⟨blk, hb, hlo, hhi, hr⟩
  have hlt := lt_nextBlock_of_some hb
  exact ⟨blk, hfr.blocks_some_of_notin hb hnotin, hlo, hhi,
    by rw [hfr.readBytes_of_notin hlt hnotin]; exact hr⟩

theorem MutByteSlice.preserve_frameMod {m m' : Mem} {allowed : BlockId → Prop}
    {b : BlockId} {baseOff : Int64} {len : Nat}
    (h : MutByteSlice m b baseOff len) (hfr : FrameMod m m' allowed) (hnotin : ¬ allowed b) :
    MutByteSlice m' b baseOff len := by
  rcases h with ⟨blk, hb, hp, hlo, hhi⟩
  exact ⟨blk, hfr.blocks_some_of_notin hb hnotin, hp, hlo, hhi⟩

theorem MutByteSlice.writeBytes_some {m : Mem} {b : BlockId} {baseOff : Int64} {bytes : List UInt8}
    (h : MutByteSlice m b baseOff bytes.length) :
    ∃ m', m.writeBytes b baseOff (bytes.map MemByte.byte) = some m' ∧
      ByteSlice m' b baseOff bytes ∧ FrameMod m m' (· = b) := by
  rcases h with ⟨blk, hb, hp, hlo, hhi⟩
  have hin : Mem.inBounds blk baseOff (bytes.map MemByte.byte).length = true := by
    unfold Mem.inBounds
    simp only [List.length_map, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlo, by omega⟩
  obtain ⟨m', hm'⟩ := writeBytes_eq_some hb hp hin
  obtain ⟨blk', hb', _, _, hsz', _, _, _⟩ := writeBytes_preserves_perm hm' hb
  have hrb' : m'.readBytes b baseOff bytes.length = some (bytes.map MemByte.byte) := by
    have := readBytes_writeBytes_same hb hm'
    rw [List.length_map] at this
    exact this
  exact ⟨m', hm', ⟨blk', hb', hlo, by rw [hsz']; exact hhi, hrb'⟩, FrameMod.of_writeBytes hm'⟩

/-! ## 3. Continuation-Polymorphic `ExprSpec`, `LvalSpec` & `ExprListSpec` -/

/-- Continuation-polymorphic weakest precondition specification for evaluating rvalue `e`
    starting from `(env, blks, m, os, mods)`. -/
def ExprSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet) (e : CExpr)
    (Post : Val → CTy → Mem → OSState → ModSet → Prop) : Prop :=
  ∀ fs ctx k,
    (∀ v ty m' os' mods', Post v ty m' os' mods' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) fs) ctx mods') env blks m' os' k)) →
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m os k)

/-- Pure expression specification: leaves memory, OS state, and `ModSet` unchanged. -/
def PureExprSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet) (e : CExpr)
    (Post : Val → CTy → Prop) : Prop :=
  ExprSpec prog cfg ext Q env blks m os mods e
    (fun v ty m' os' mods' => Post v ty ∧ m' = m ∧ os' = os ∧ mods' = mods)

/-- Continuation-polymorphic weakest precondition specification for evaluating lvalue `e`
    to `(b, off, ty)` starting from `(env, blks, m, os, mods)`. -/
def LvalSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet) (e : CExpr)
    (Post : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop) : Prop :=
  ∀ fs ctx k,
    (∀ b off ty m' os' mods', Post b off ty m' os' mods' →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.lval b off ty) fs) ctx mods') env blks m' os' k)) →
    WPTerm prog cfg ext Q (.running (.expr (.eval .lval e fs) ctx mods) env blks m os k)

/-- Pure lvalue specification: leaves memory, OS state, and `ModSet` unchanged. -/
def PureLvalSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet) (e : CExpr)
    (Post : BlockId → Int64 → CTy → Prop) : Prop :=
  LvalSpec prog cfg ext Q env blks m os mods e
    (fun b off ty m' os' mods' => Post b off ty ∧ m' = m ∧ os' = os ∧ mods' = mods)

/-- Dispatch WP at a function call site `(sym, fnTy, argVals)`. -/
def CallDispatchWP (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (sym : String) (fnTy : CTy) (argVals : List (Val × CTy))
    (m : Mem) (os : OSState) (fs : List ExprFrame) (ctx : ExprCtx) (k : Cont) : Prop :=
  ∀ s, Sem.stepDet prog cfg s = some (.callFn sym fnTy argVals fs ctx env blks m os k) →
    WPTerm prog cfg ext Q s

/-- Specification for evaluating a non-empty tail `args` of a function argument list,
    given `done` arguments already evaluated. -/
def ExprListSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet) (done : List (Val × CTy))
    (args : List CExpr) (Post : List (Val × CTy) → Mem → OSState → Prop) : Prop :=
  ∀ sym fnTy fs ctx k,
    (∀ vs m' os', Post vs m' os' →
      CallDispatchWP prog cfg ext Q env blks sym fnTy (done ++ vs) m' os' fs ctx k) →
    match args with
    | [] => CallDispatchWP prog cfg ext Q env blks sym fnTy done m os fs ctx k
    | arg :: rest =>
      WPTerm prog cfg ext Q
        (.running (.expr (.eval .rval arg (.callArgF sym fnTy done rest :: fs)) ctx mods)
          env blks m os k)

theorem ExprSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P1 P2 : Val → CTy → Mem → OSState → ModSet → Prop}
    (h : ExprSpec prog cfg ext Q env blks m os mods e P1)
    (himp : ∀ v ty m' os' mods', P1 v ty m' os' mods' → P2 v ty m' os' mods') :
    ExprSpec prog cfg ext Q env blks m os mods e P2 :=
  fun fs ctx k hcont => h fs ctx k (fun v ty m' os' mods' hp => hcont v ty m' os' mods' (himp v ty m' os' mods' hp))

theorem PureExprSpec.to_expr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr} {P : Val → CTy → Prop}
    (h : PureExprSpec prog cfg ext Q env blks m os mods e P) :
    ExprSpec prog cfg ext Q env blks m os mods e
      (fun v ty m' os' mods' => P v ty ∧ m' = m ∧ os' = os ∧ mods' = mods) := h

theorem PureExprSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr} {P1 P2 : Val → CTy → Prop}
    (h : PureExprSpec prog cfg ext Q env blks m os mods e P1)
    (himp : ∀ v ty, P1 v ty → P2 v ty) :
    PureExprSpec prog cfg ext Q env blks m os mods e P2 :=
  ExprSpec.mono h (fun v ty _ _ _ ⟨hp, hm, hos, hmd⟩ => ⟨himp v ty hp, hm, hos, hmd⟩)

theorem LvalSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P1 P2 : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    (h : LvalSpec prog cfg ext Q env blks m os mods e P1)
    (himp : ∀ b off ty m' os' mods', P1 b off ty m' os' mods' → P2 b off ty m' os' mods') :
    LvalSpec prog cfg ext Q env blks m os mods e P2 :=
  fun fs ctx k hcont => h fs ctx k (fun b off ty m' os' mods' hp => hcont b off ty m' os' mods' (himp b off ty m' os' mods' hp))

theorem PureLvalSpec.to_lval {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr} {P : BlockId → Int64 → CTy → Prop}
    (h : PureLvalSpec prog cfg ext Q env blks m os mods e P) :
    LvalSpec prog cfg ext Q env blks m os mods e
      (fun b off ty m' os' mods' => P b off ty ∧ m' = m ∧ os' = os ∧ mods' = mods) := h

/-! ### 3.1 Literals, Variables, String Literals, `paren`, `sizeof` -/

theorem PureExprSpec.lit (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet)
    (v : Int) (k : IntKind) (suf : LitSuffix) (rad : LitRadix) (sym? : Option String) :
    PureExprSpec prog cfg ext Q env blks m os mods (.lit v k suf rad sym?)
      (fun rv rty => rv = ofIntCast k v ∧ rty = .int k) := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure (es' := .ret (.rval (ofIntCast k v) (.int k)) fs)
    (mods' := mods) (m' := m) rfl ?_
  exact hcont _ _ m os mods ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem PureExprSpec.var_readPlace {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {b : BlockId} {ty : CTy}
    {rv : Val} {rty : CTy}
    (hl : env.lookup x = some (b, ty))
    (hrp : Sem.readPlace prog.tags m mods .rval b 0 ty = some (.rval rv rty)) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun v t => v = rv ∧ t = rty) := by
  intro fs ctx cont hcont
  have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
      some (.ret (.rval rv rty) fs, m, mods) := by
    unfold Sem.stepExprPure
    simp only [hl, hrp, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont rv rty m os mods ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem PureExprSpec.var_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {ty : CTy} {k : IntKind}
    {v : BitVec k.bits}
    (h : LocalIntSlot env m x ty k v)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 k.bytes = false) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun rv rty => rv = .int k v ∧ rty = .int k) := by
  obtain ⟨b, hl, hrp⟩ := h.readPlace_some prog.tags hmod
  exact PureExprSpec.var_readPlace hl hrp

theorem PureExprSpec.var_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {ty el : CTy} {v : Val}
    (h : LocalPtrSlot env m x ty el v)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 8 = false) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun rv rty => rv = v ∧ rty = .ptr el) := by
  obtain ⟨b, hl, hrp⟩ := h.readPlace_some prog.tags hmod
  exact PureExprSpec.var_readPlace hl hrp

theorem PureExprSpec.var_fnPtr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {ty rty : CTy}
    {ptys : List CTy} {va : Bool} {v : Val}
    (h : LocalFnPtrSlot env m x ty rty ptys va v)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 8 = false) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun rv rt => rv = v ∧ rt = .fnPtr rty ptys va) := by
  obtain ⟨b, hl, hrp⟩ := h.readPlace_some prog.tags hmod
  exact PureExprSpec.var_readPlace hl hrp

theorem PureExprSpec.var_array {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {b : BlockId}
    {ty el : CTy} {n : Option Nat}
    (hl : env.lookup x = some (b, ty)) (ha : ty.unqual = .array el n) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun rv rty => rv = .ptr b 0 ∧ rty = .ptr el) := by
  have hrp : Sem.readPlace prog.tags m mods .rval b 0 ty = some (.rval (.ptr b 0) (.ptr el)) := by
    unfold Sem.readPlace
    dsimp only
    rw [ha]
    simp only [cty_decay_eq_array ty ha]
  exact PureExprSpec.var_readPlace hl hrp

theorem PureExprSpec.var_enum {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {ev : Int}
    (hn : env.lookup x = none) (he : Sem.enumConst? prog.tags x = some ev) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun rv rty => rv = ofIntCast .i32 ev ∧ rty = .int .i32) := by
  intro fs ctx cont hcont
  have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
      some (.ret (.rval (ofIntCast .i32 ev) (.int .i32)) fs, m, mods) := by
    unfold Sem.stepExprPure
    simp only [hn, he]
  exact WPTerm.of_exprPure hstep (hcont _ _ m os mods ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem PureExprSpec.var_fnProto {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {rty : CTy}
    {ptys : List CTy} {va : Bool}
    (hn : env.lookup x = none) (he : Sem.enumConst? prog.tags x = none)
    (hp : prog.fnProtos x = some (rty, ptys, va)) :
    PureExprSpec prog cfg ext Q env blks m os mods (.var x)
      (fun rv rt => rv = .fnPtr x ∧ rt = .fnPtr rty ptys va) := by
  intro fs ctx cont hcont
  have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.var x) fs) =
      some (.ret (.rval (.fnPtr x) (.fnPtr rty ptys va)) fs, m, mods) := by
    unfold Sem.stepExprPure
    simp only [hn, he, hp, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont _ _ m os mods ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem PureLvalSpec.var {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {b : BlockId} {ty : CTy}
    (hl : env.lookup x = some (b, ty)) :
    PureLvalSpec prog cfg ext Q env blks m os mods (.var x)
      (fun b' off' ty' => b' = b ∧ off' = 0 ∧ ty' = ty) := by
  intro fs ctx cont hcont
  have hstep : Sem.stepExprPure prog cfg env m mods (.eval .lval (.var x) fs) =
      some (.ret (.lval b 0 ty) fs, m, mods) := by
    unfold Sem.stepExprPure
    simp only [hl, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont b 0 ty m os mods ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem ExprSpec.strLit {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {s : String}
    (hsz : s.utf8ByteSize + 1 < ptrDiffLimit) :
    ExprSpec prog cfg ext Q env blks m os mods (.strLit s)
      (fun rv rty m' os' mods' =>
        ∃ bid, rv = .ptr bid 0 ∧ rty = .ptr (.const_ (.int .i8)) ∧
          ROExt m m' ∧ os' = os ∧ mods' = mods ∧
          m'.blocks bid ≠ none ∧
          (∃ blk, m'.blocks bid = some blk ∧ blk.kind = .global ∧ blk.perm = .ro ∧
            blk.size = s.utf8ByteSize + 1 ∧
            ∀ i, blk.bytes i = .byte ((s.toUTF8[i]?).getD 0))) := by
  intro fs ctx cont hcont
  refine WPTerm.of_strLit (by unfold Sem.stepDet; rfl) hsz ?_
  intro base bid m' halloc
  have hro : ROExt m m' := ROExt.of_strLit hsz halloc
  have hbid : bid = m.nextBlock := (congrArg Prod.fst halloc).symm
  have hm' : m' = (m.alloc (s.utf8ByteSize + 1) 1 .ro .global base
      (fun i => .byte ((s.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _)).2 :=
    (congrArg Prod.snd halloc).symm
  let blk : Block := ⟨s.utf8ByteSize + 1, 1, .ro, .global, base,
    fun i => .byte ((s.toUTF8[i]?).getD 0), hsz, by decide, Nat.mod_one _⟩
  have hb : m'.blocks bid = some blk := by
    rw [hm', hbid]
    exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hne : m'.blocks bid ≠ none := by rw [hb]; intro h; cases h
  exact hcont _ _ m' os mods ⟨bid, rfl, rfl, hro, rfl, rfl, hne,
    ⟨blk, hb, rfl, rfl, rfl, fun _ => rfl⟩⟩

theorem ExprSpec.paren {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    (h : ExprSpec prog cfg ext Q env blks m os mods e P) :
    ExprSpec prog cfg ext Q env blks m os mods (.paren e) P := by
  intro fs ctx cont hcont
  exact WPTerm.of_exprPure rfl (h fs ctx cont hcont)

theorem PureExprSpec.paren {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr} {P : Val → CTy → Prop}
    (h : PureExprSpec prog cfg ext Q env blks m os mods e P) :
    PureExprSpec prog cfg ext Q env blks m os mods (.paren e) P :=
  ExprSpec.paren h

theorem LvalSpec.paren {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    (h : LvalSpec prog cfg ext Q env blks m os mods e P) :
    LvalSpec prog cfg ext Q env blks m os mods (.paren e) P := by
  intro fs ctx cont hcont
  exact WPTerm.of_exprPure rfl (h fs ctx cont hcont)

theorem PureExprSpec.sizeofTy (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (mods : ModSet) (ty : CTy) :
    PureExprSpec prog cfg ext Q env blks m os mods (.sizeOfTy ty)
      (fun rv rty => rv = .int .u64 (BitVec.ofNat 64 (C99.sizeofTy prog.tags ty)) ∧ rty = .int .u64) := by
  intro fs ctx cont hcont
  exact WPTerm.of_exprPure rfl (hcont _ _ m os mods ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩)

theorem PureExprSpec.sizeofExpr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr} {ty : CTy}
    (ht : Sem.exprType? prog.tags env prog.fnProtos e = some ty) :
    PureExprSpec prog cfg ext Q env blks m os mods (.sizeOfExpr e)
      (fun rv rty => rv = .int .u64 (BitVec.ofNat 64 (C99.sizeofTy prog.tags ty)) ∧ rty = .int .u64) := by
  intro fs ctx cont hcont
  have hstep : Sem.stepExprPure prog cfg env m mods (.eval .rval (.sizeOfExpr e) fs) =
      some (.ret (.rval (.int .u64 (BitVec.ofNat 64 (C99.sizeofTy prog.tags ty))) (.int .u64)) fs, m, mods) := by
    unfold Sem.stepExprPure
    simp only [ht, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont _ _ m os mods ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩)

/-! ### 3.2 Cast, Unary, Binary, Pointer Arithmetic, Short-Circuit Logic, Ternary & Comma -/

theorem ExprSpec.cast {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {ty : CTy} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os mods e P)
    (hc : ∀ v t m' os' mods', P v t m' os' mods' →
      ∃ cv, Sem.castVal m' ty v = some cv ∧ Post cv ty m' os' mods') :
    ExprSpec prog cfg ext Q env blks m os mods (.cast ty e) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine he (.castF ty :: fs) ctx cont ?_
  intro v t m' os' mods' hp
  obtain ⟨cv, hcv, hpost⟩ := hc v t m' os' mods' hp
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.rval v t) (.castF ty :: fs)) =
      some (.ret (.rval cv ty) fs, m', mods') := by
    unfold Sem.stepExprPure
    simp only [hcv, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont cv ty m' os' mods' hpost)

theorem PureExprSpec.cast {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {ty : CTy} {e : CExpr}
    {P Post : Val → CTy → Prop}
    (he : PureExprSpec prog cfg ext Q env blks m os mods e P)
    (hc : ∀ v t, P v t → ∃ cv, Sem.castVal m ty v = some cv ∧ Post cv ty) :
    PureExprSpec prog cfg ext Q env blks m os mods (.cast ty e) Post := by
  refine ExprSpec.cast he ?_
  intro v t m' os' mods' ⟨hp, rfl, rfl, rfl⟩
  obtain ⟨cv, hcv, hpost⟩ := hc v t hp
  exact ⟨cv, hcv, hpost, rfl, rfl, rfl⟩

theorem ExprSpec.unary {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : UnOp} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os mods e P)
    (hu : ∀ v t m' os' mods', P v t m' os' mods' →
      ∃ rv rt, Sem.evalUnary op v = some (rv, rt) ∧ Post rv rt m' os' mods') :
    ExprSpec prog cfg ext Q env blks m os mods (.unary op e) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine he (.unaryF op :: fs) ctx cont ?_
  intro v t m' os' mods' hp
  obtain ⟨rv, rt, hrv, hpost⟩ := hu v t m' os' mods' hp
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.rval v t) (.unaryF op :: fs)) =
      some (.ret (.rval rv rt) fs, m', mods') := by
    unfold Sem.stepExprPure
    simp only [hrv, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont rv rt m' os' mods' hpost)

theorem PureExprSpec.unary {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : UnOp} {e : CExpr}
    {P Post : Val → CTy → Prop}
    (he : PureExprSpec prog cfg ext Q env blks m os mods e P)
    (hu : ∀ v t, P v t → ∃ rv rt, Sem.evalUnary op v = some (rv, rt) ∧ Post rv rt) :
    PureExprSpec prog cfg ext Q env blks m os mods (.unary op e) Post := by
  refine ExprSpec.unary he ?_
  intro v t m' os' mods' ⟨hp, rfl, rfl, rfl⟩
  obtain ⟨rv, rt, hrv, hpost⟩ := hu v t hp
  exact ⟨rv, rt, hrv, hpost, rfl, rfl, rfl⟩

theorem ExprSpec.binary {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : BinOp} {l r : CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : ExprSpec prog cfg ext Q env blks m os mods l P1)
    (hr : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 r
        (fun v2 t2 m2 os2 mods2 =>
          ∃ rv rt, Sem.applyBinary cfg prog.tags m2 op v1 t1 v2 t2 = some (rv, rt) ∧
            Post rv rt m2 os2 mods2)) :
    ExprSpec prog cfg ext Q env blks m os mods (.binary op l r) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.binLhsF op r :: fs) ctx cont ?_
  intro v1 t1 m1 os1 mods1 hp1
  refine WPTerm.of_exprPure rfl ?_
  refine (hr v1 t1 m1 os1 mods1 hp1) (.binRhsF op v1 t1 :: fs) ctx cont ?_
  intro v2 t2 m2 os2 mods2 ⟨rv, rt, hab, hpost⟩
  have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.binRhsF op v1 t1 :: fs)) =
      some (.ret (.rval rv rt) fs, m2, mods2) := by
    unfold Sem.stepExprPure
    simp only [hab, Option.map_some]
  exact WPTerm.of_exprPure hstep (hcont rv rt m2 os2 mods2 hpost)

theorem PureExprSpec.binary {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : BinOp} {l r : CExpr}
    {P1 P2 Post : Val → CTy → Prop}
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l P1)
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r P2)
    (hb : ∀ v1 t1 v2 t2, P1 v1 t1 → P2 v2 t2 →
      ∃ rv rt, Sem.applyBinary cfg prog.tags m op v1 t1 v2 t2 = some (rv, rt) ∧ Post rv rt) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary op l r) Post := by
  refine ExprSpec.binary hl ?_
  intro v1 t1 m1 os1 mods1 ⟨hp1, rfl, rfl, rfl⟩
  refine ExprSpec.mono hr ?_
  intro v2 t2 m2 os2 mods2 ⟨hp2, rfl, rfl, rfl⟩
  obtain ⟨rv, rt, hab, hpost⟩ := hb v1 t1 v2 t2 hp1 hp2
  exact ⟨rv, rt, hab, hpost, rfl, rfl, rfl⟩

theorem PureExprSpec.binary_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : BinOp} {l r : CExpr}
    {k1 k2 : IntKind} {v1 : BitVec k1.bits} {v2 : BitVec k2.bits}
    {rv : Val} {rt : CTy}
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l (fun x t => x = .int k1 v1 ∧ t = .int k1))
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r (fun x t => x = .int k2 v2 ∧ t = .int k2))
    (heval : Sem.evalIntBinary op (.int k1 v1) (.int k2 v2) = some (rv, rt)) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary op l r) (fun x t => x = rv ∧ t = rt) := by
  refine PureExprSpec.binary hl hr ?_
  rintro x1 t1 x2 t2 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  refine ⟨rv, rt, ?_, rfl, rfl⟩
  rw [applyBinary_int_eq (k1 := k1) (k2 := k2) rfl rfl]
  exact heval

theorem PureExprSpec.binary_ptrAdd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {p : Val} {pty el : CTy} {k : IntKind} {idxBv : BitVec k.bits} {res : Val}
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l (fun x t => x = p ∧ t = pty))
    (hptr : pty.unqual = .ptr el)
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r (fun x _ => x = .int k idxBv))
    (heval : Sem.evalPtrAdd cfg prog.tags m p el (if k.signed then idxBv.toInt else (idxBv.toNat : Int)) = some res) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary .add l r)
      (fun x t => x = res ∧ t = .ptr el) := by
  refine PureExprSpec.binary hl hr ?_
  rintro x1 t1 x2 t2 ⟨rfl, rfl⟩ rfl
  exact ⟨res, .ptr el, applyBinary_ptrAdd_r hptr heval, rfl, rfl⟩

theorem PureExprSpec.binary_ptrAdd_l {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {k : IntKind} {idxBv : BitVec k.bits} {p : Val → CTy → Prop}
    {pty el : CTy} {pv : Val} {res : Val}
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l
      (fun x t => x = .int k idxBv ∧ ∃ ti, t = ti ∧ ti.unqual = .int k))
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r (fun x t => x = pv ∧ t = pty ∧ p x t))
    (hptr : pty.unqual = .ptr el)
    (heval : Sem.evalPtrAdd cfg prog.tags m pv el (if k.signed then idxBv.toInt else (idxBv.toNat : Int)) = some res) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary .add l r)
      (fun x t => x = res ∧ t = .ptr el) := by
  refine PureExprSpec.binary hl hr ?_
  rintro x1 t1 x2 t2 ⟨rfl, ti, rfl, hit⟩ ⟨rfl, rfl, _⟩
  exact ⟨res, .ptr el, applyBinary_ptrAdd_l hit hptr heval, rfl, rfl⟩

theorem PureExprSpec.binary_ptrSub {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {p : Val} {pty el : CTy} {k : IntKind} {idxBv : BitVec k.bits} {res : Val}
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l (fun x t => x = p ∧ t = pty))
    (hptr : pty.unqual = .ptr el)
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r (fun x t => x = .int k idxBv ∧ t.unqual = .int k))
    (heval : Sem.evalPtrAdd cfg prog.tags m p el (-(if k.signed then idxBv.toInt else (idxBv.toNat : Int))) = some res) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary .sub l r)
      (fun x t => x = res ∧ t = .ptr el) := by
  refine PureExprSpec.binary hl hr ?_
  rintro x1 t1 x2 t2 ⟨rfl, rfl⟩ ⟨rfl, hit⟩
  exact ⟨res, .ptr el, applyBinary_ptrSub hptr hit heval, rfl, rfl⟩

theorem PureExprSpec.binary_ptrDiff {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {p1 p2 : Val} {pt1 pt2 el1 el2 : CTy} {res : Val}
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l (fun x t => x = p1 ∧ t = pt1))
    (hp1 : pt1.unqual = .ptr el1)
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r (fun x t => x = p2 ∧ t = pt2))
    (hp2 : pt2.unqual = .ptr el2)
    (heval : Sem.evalPtrDiff cfg prog.tags m p1 p2 el1 = some res) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary .sub l r)
      (fun x t => x = res ∧ t = .int .i64) := by
  refine PureExprSpec.binary hl hr ?_
  rintro x1 t1 x2 t2 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact ⟨res, .int .i64, applyBinary_ptrDiff hp1 hp2 heval, rfl, rfl⟩

theorem PureExprSpec.binary_ptrCmp {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : BinOp} {l r : CExpr}
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    {p1 p2 : Val} {t1 t2 : CTy} {res : Val}
    (hptr : t1.isPtr = true ∨ t2.isPtr = true ∨
      (∃ r ps va, t1.unqual = .fnPtr r ps va) ∨
      (∃ r ps va, t2.unqual = .fnPtr r ps va))
    (hl : PureExprSpec prog cfg ext Q env blks m os mods l (fun x t => x = p1 ∧ t = t1))
    (hr : PureExprSpec prog cfg ext Q env blks m os mods r (fun x t => x = p2 ∧ t = t2))
    (hcmp : Sem.evalPtrCmp m op p1 p2 = some res) :
    PureExprSpec prog cfg ext Q env blks m os mods (.binary op l r)
      (fun x t => x = res ∧ t = .int .i32) := by
  refine PureExprSpec.binary hl hr ?_
  rintro x1 s1 x2 s2 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  exact ⟨res, .int .i32, applyBinary_ptrCmp hop hptr hcmp, rfl, rfl⟩

theorem ExprSpec.logAnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : ExprSpec prog cfg ext Q env blks m os mods l P1)
    (hfalse : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 →
      Sem.isTruthy v1 = some false → Post (.int .i32 0) (.int .i32) m1 os1 mods1)
    (htrue : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 →
      Sem.isTruthy v1 = some true →
      ExprSpec prog cfg ext Q env blks m1 os1 [] r
        (fun v2 _ m2 os2 mods2 => ∃ b2 : Bool, Sem.isTruthy v2 = some b2 ∧
          Post (.int .i32 (if b2 then 1 else 0)) (.int .i32) m2 os2 mods2))
    (htruthy1 : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 → ∃ b1 : Bool, Sem.isTruthy v1 = some b1) :
    ExprSpec prog cfg ext Q env blks m os mods (.logAnd l r) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.logAndF r :: fs) ctx cont ?_
  intro v1 t1 m1 os1 mods1 hp1
  obtain ⟨b1, hb1⟩ := htruthy1 v1 t1 m1 os1 mods1 hp1
  cases b1 with
  | false =>
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logAndF r :: fs)) =
        some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m1, mods1) := by
      unfold Sem.stepExprPure
      simp only [hb1, Bool.not_false, ↓reduceIte, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep (hcont (.int .i32 0) (.int .i32) m1 os1 mods1 (hfalse v1 t1 m1 os1 mods1 hp1 hb1))
  | true =>
    have hstep1 : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logAndF r :: fs)) =
        some (.eval .rval r (.logAndEndF :: fs), m1, []) := by
      unfold Sem.stepExprPure
      simp only [hb1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, opt_bind_some, opt_pure_some]
    refine WPTerm.of_exprPure hstep1 ?_
    refine (htrue v1 t1 m1 os1 mods1 hp1 hb1) (.logAndEndF :: fs) ctx cont ?_
    intro v2 t2 m2 os2 mods2 ⟨b2, hb2, hpost⟩
    have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logAndEndF :: fs)) =
        some (.ret (.rval (.int .i32 (if b2 then 1 else 0)) (.int .i32)) fs, m2, mods2) := by
      unfold Sem.stepExprPure
      simp only [hb2, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep2 (hcont _ _ m2 os2 mods2 hpost)

theorem ExprSpec.logOr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : ExprSpec prog cfg ext Q env blks m os mods l P1)
    (htrue : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 →
      Sem.isTruthy v1 = some true → Post (.int .i32 1) (.int .i32) m1 os1 mods1)
    (hfalse : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 →
      Sem.isTruthy v1 = some false →
      ExprSpec prog cfg ext Q env blks m1 os1 [] r
        (fun v2 _ m2 os2 mods2 => ∃ b2 : Bool, Sem.isTruthy v2 = some b2 ∧
          Post (.int .i32 (if b2 then 1 else 0)) (.int .i32) m2 os2 mods2))
    (htruthy1 : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 → ∃ b1 : Bool, Sem.isTruthy v1 = some b1) :
    ExprSpec prog cfg ext Q env blks m os mods (.logOr l r) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.logOrF r :: fs) ctx cont ?_
  intro v1 t1 m1 os1 mods1 hp1
  obtain ⟨b1, hb1⟩ := htruthy1 v1 t1 m1 os1 mods1 hp1
  cases b1 with
  | true =>
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logOrF r :: fs)) =
        some (.ret (.rval (.int .i32 1) (.int .i32)) fs, m1, mods1) := by
      unfold Sem.stepExprPure
      simp only [hb1, ↓reduceIte, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep (hcont (.int .i32 1) (.int .i32) m1 os1 mods1 (htrue v1 t1 m1 os1 mods1 hp1 hb1))
  | false =>
    have hstep1 : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.rval v1 t1) (.logOrF r :: fs)) =
        some (.eval .rval r (.logOrEndF :: fs), m1, []) := by
      unfold Sem.stepExprPure
      simp only [hb1, Bool.false_eq_true, ↓reduceIte, bind, opt_bind_some, opt_pure_some]
    refine WPTerm.of_exprPure hstep1 ?_
    refine (hfalse v1 t1 m1 os1 mods1 hp1 hb1) (.logOrEndF :: fs) ctx cont ?_
    intro v2 t2 m2 os2 mods2 ⟨b2, hb2, hpost⟩
    have hstep2 : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval v2 t2) (.logOrEndF :: fs)) =
        some (.ret (.rval (.int .i32 (if b2 then 1 else 0)) (.int .i32)) fs, m2, mods2) := by
      unfold Sem.stepExprPure
      simp only [hb2, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep2 (hcont _ _ m2 os2 mods2 hpost)

theorem ExprSpec.cond {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {c t f : CExpr}
    {Pc : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hc : ExprSpec prog cfg ext Q env blks m os mods c Pc)
    (htruthy : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc)
    (ht : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc →
      Sem.isTruthy vc = some true → ExprSpec prog cfg ext Q env blks mc osc [] t Post)
    (hf : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc →
      Sem.isTruthy vc = some false → ExprSpec prog cfg ext Q env blks mc osc [] f Post) :
    ExprSpec prog cfg ext Q env blks m os mods (.cond c t f) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hc (.condF t f :: fs) ctx cont ?_
  intro vc tc mc osc modsc hpc
  obtain ⟨bc, hbc⟩ := htruthy vc tc mc osc modsc hpc
  have hstep : Sem.stepExprPure prog cfg env mc modsc (.ret (.rval vc tc) (.condF t f :: fs)) =
      some (.eval .rval (if bc then t else f) fs, mc, []) := by
    unfold Sem.stepExprPure
    simp only [hbc, bind, opt_bind_some, opt_pure_some]
  refine WPTerm.of_exprPure hstep ?_
  cases bc with
  | true => exact (ht vc tc mc osc modsc hpc hbc) fs ctx cont hcont
  | false => exact (hf vc tc mc osc modsc hpc hbc) fs ctx cont hcont

theorem ExprSpec.comma {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : ExprSpec prog cfg ext Q env blks m os mods l P1)
    (hr : ∀ v1 t1 m1 os1 mods1, P1 v1 t1 m1 os1 mods1 →
      ExprSpec prog cfg ext Q env blks m1 os1 [] r Post) :
    ExprSpec prog cfg ext Q env blks m os mods (.comma l r) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.commaF r :: fs) ctx cont ?_
  intro v1 t1 m1 os1 mods1 hp1
  exact WPTerm.of_exprPure rfl ((hr v1 t1 m1 os1 mods1 hp1) fs ctx cont hcont)

/-! ### 3.3 Address-Of, Dereference, Indexing, Member/Arrow, Assignments & Inc/Dec -/

theorem ExprSpec.addrOf {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    (hl : LvalSpec prog cfg ext Q env blks m os mods e P) :
    ExprSpec prog cfg ext Q env blks m os mods (.addrOf e)
      (fun v ty m' os' mods' => ∃ b off lty, v = .ptr b off ∧ ty = .ptr lty ∧ P b off lty m' os' mods') := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.addrOfF :: fs) ctx cont ?_
  intro b off lty m' os' mods' hp
  exact WPTerm.of_exprPure rfl (hcont (.ptr b off) (.ptr lty) m' os' mods' ⟨b, off, lty, rfl, rfl, hp⟩)

theorem LvalSpec.deref {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os mods e P)
    (hp : ∀ v t m' os' mods', P v t m' os' mods' →
      ∃ b off el, v = .ptr b off ∧ t.unqual = .ptr el) :
    LvalSpec prog cfg ext Q env blks m os mods (.deref e)
      (fun b off el m' os' mods' => ∃ t, t.unqual = .ptr el ∧ P (.ptr b off) t m' os' mods') := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine he (.derefF .lval :: fs) ctx cont ?_
  intro v t m' os' mods' hpe
  obtain ⟨b, off, el, rfl, hptr⟩ := hp v t m' os' mods' hpe
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.rval (.ptr b off) t) (.derefF .lval :: fs)) =
      some (.ret (.lval b off el) fs, m', mods') := by
    unfold Sem.stepExprPure Sem.readPlace
    dsimp only
    rw [hptr]
    rfl
  exact WPTerm.of_exprPure hstep (hcont b off el m' os' mods' ⟨t, hptr, hpe⟩)

theorem ExprSpec.deref {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os mods e P)
    (hr : ∀ v t m' os' mods', P v t m' os' mods' →
      ∃ b off el rv rty, v = .ptr b off ∧ t.unqual = .ptr el ∧
        Sem.readPlace prog.tags m' mods' .rval b off el = some (.rval rv rty) ∧
        Post rv rty m' os' mods') :
    ExprSpec prog cfg ext Q env blks m os mods (.deref e) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine he (.derefF .rval :: fs) ctx cont ?_
  intro v t m' os' mods' hpe
  obtain ⟨b, off, el, rv, rty, rfl, hptr, hrp, hpost⟩ := hr v t m' os' mods' hpe
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.rval (.ptr b off) t) (.derefF .rval :: fs)) =
      some (.ret (.rval rv rty) fs, m', mods') := by
    unfold Sem.stepExprPure
    dsimp only
    rw [hptr]
    simp only [hrp, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont rv rty m' os' mods' hpost)

theorem LvalSpec.index {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base idx : CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    (hb : ExprSpec prog cfg ext Q env blks m os mods base P1)
    (hi : ∀ vp tp m1 os1 mods1, P1 vp tp m1 os1 mods1 →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 idx
        (fun vi _ m2 os2 mods2 =>
          ∃ el k iv b' off', tp.unqual = .ptr el ∧ valAsInt? vi = some (k, iv) ∧
            Sem.evalPtrAdd cfg prog.tags m2 vp el iv = some (.ptr b' off') ∧
            Post b' off' el m2 os2 mods2)) :
    LvalSpec prog cfg ext Q env blks m os mods (.index base idx) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hb (.indexBaseF .lval idx :: fs) ctx cont ?_
  intro vp tp m1 os1 mods1 hp1
  refine WPTerm.of_exprPure rfl ?_
  refine (hi vp tp m1 os1 mods1 hp1) (.indexIdxF .lval vp tp :: fs) ctx cont ?_
  intro vi ti m2 os2 mods2 ⟨el, k, iv, b', off', hptr, hvi, hadd, hpost⟩
  have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval vi ti) (.indexIdxF .lval vp tp :: fs)) =
      some (.ret (.lval b' off' el) fs, m2, mods2) := by
    unfold Sem.stepExprPure Sem.readPlace
    dsimp only
    rw [hptr]
    simp only [hvi, hadd, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont b' off' el m2 os2 mods2 hpost)

theorem ExprSpec.index {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base idx : CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hb : ExprSpec prog cfg ext Q env blks m os mods base P1)
    (hi : ∀ vp tp m1 os1 mods1, P1 vp tp m1 os1 mods1 →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 idx
        (fun vi _ m2 os2 mods2 =>
          ∃ el k iv b' off' rv rty, tp.unqual = .ptr el ∧ valAsInt? vi = some (k, iv) ∧
            Sem.evalPtrAdd cfg prog.tags m2 vp el iv = some (.ptr b' off') ∧
            Sem.readPlace prog.tags m2 mods2 .rval b' off' el = some (.rval rv rty) ∧
            Post rv rty m2 os2 mods2)) :
    ExprSpec prog cfg ext Q env blks m os mods (.index base idx) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hb (.indexBaseF .rval idx :: fs) ctx cont ?_
  intro vp tp m1 os1 mods1 hp1
  refine WPTerm.of_exprPure rfl ?_
  refine (hi vp tp m1 os1 mods1 hp1) (.indexIdxF .rval vp tp :: fs) ctx cont ?_
  intro vi ti m2 os2 mods2 ⟨el, k, iv, b', off', rv, rty, hptr, hvi, hadd, hrp, hpost⟩
  have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval vi ti) (.indexIdxF .rval vp tp :: fs)) =
      some (.ret (.rval rv rty) fs, m2, mods2) := by
    unfold Sem.stepExprPure
    dsimp only
    rw [hptr]
    simp only [hvi, hadd, hrp, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont rv rty m2 os2 mods2 hpost)

theorem LvalSpec.member {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base : CExpr} {fld : String}
    {P : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    {Post : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    (hb : LvalSpec prog cfg ext Q env blks m os mods base P)
    (hf : ∀ b off sty m' os' mods', P b off sty m' os' mods' →
      ∃ foff fty, fieldLayout? prog.tags sty fld = some (foff, fty) ∧
        Post b (Int64.ofInt (off.toInt + foff)) fty m' os' mods') :
    LvalSpec prog cfg ext Q env blks m os mods (.member base fld) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hb (.memberF .lval fld :: fs) ctx cont ?_
  intro b off sty m' os' mods' hp
  obtain ⟨foff, fty, hfl, hpost⟩ := hf b off sty m' os' mods' hp
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.lval b off sty) (.memberF .lval fld :: fs)) =
      some (.ret (.lval b (Int64.ofInt (off.toInt + foff)) fty) fs, m', mods') := by
    unfold Sem.stepExprPure Sem.readPlace
    simp only [hfl, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont b (Int64.ofInt (off.toInt + foff)) fty m' os' mods' hpost)

theorem ExprSpec.member {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base : CExpr} {fld : String}
    {P : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hb : LvalSpec prog cfg ext Q env blks m os mods base P)
    (hf : ∀ b off sty m' os' mods', P b off sty m' os' mods' →
      ∃ foff fty rv rty, fieldLayout? prog.tags sty fld = some (foff, fty) ∧
        Sem.readPlace prog.tags m' mods' .rval b (Int64.ofInt (off.toInt + foff)) fty = some (.rval rv rty) ∧
        Post rv rty m' os' mods') :
    ExprSpec prog cfg ext Q env blks m os mods (.member base fld) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hb (.memberF .rval fld :: fs) ctx cont ?_
  intro b off sty m' os' mods' hp
  obtain ⟨foff, fty, rv, rty, hfl, hrp, hpost⟩ := hf b off sty m' os' mods' hp
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.lval b off sty) (.memberF .rval fld :: fs)) =
      some (.ret (.rval rv rty) fs, m', mods') := by
    unfold Sem.stepExprPure
    simp only [hfl, hrp, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont rv rty m' os' mods' hpost)

theorem LvalSpec.arrow {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base : CExpr} {fld : String}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    (hb : ExprSpec prog cfg ext Q env blks m os mods base P)
    (hf : ∀ vp pty m' os' mods', P vp pty m' os' mods' →
      ∃ b off sty foff fty, vp = .ptr b off ∧ pty.unqual = .ptr sty ∧
        fieldLayout? prog.tags sty fld = some (foff, fty) ∧
        Post b (Int64.ofInt (off.toInt + foff)) fty m' os' mods') :
    LvalSpec prog cfg ext Q env blks m os mods (.arrow base fld) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hb (.arrowF .lval fld :: fs) ctx cont ?_
  intro vp pty m' os' mods' hp
  obtain ⟨b, off, sty, foff, fty, rfl, hptr, hfl, hpost⟩ := hf vp pty m' os' mods' hp
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.rval (.ptr b off) pty) (.arrowF .lval fld :: fs)) =
      some (.ret (.lval b (Int64.ofInt (off.toInt + foff)) fty) fs, m', mods') := by
    unfold Sem.stepExprPure Sem.readPlace
    dsimp only
    rw [hptr]
    simp only [hfl, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont b (Int64.ofInt (off.toInt + foff)) fty m' os' mods' hpost)

theorem ExprSpec.arrow {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base : CExpr} {fld : String}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hb : ExprSpec prog cfg ext Q env blks m os mods base P)
    (hf : ∀ vp pty m' os' mods', P vp pty m' os' mods' →
      ∃ b off sty foff fty rv rty, vp = .ptr b off ∧ pty.unqual = .ptr sty ∧
        fieldLayout? prog.tags sty fld = some (foff, fty) ∧
        Sem.readPlace prog.tags m' mods' .rval b (Int64.ofInt (off.toInt + foff)) fty = some (.rval rv rty) ∧
        Post rv rty m' os' mods') :
    ExprSpec prog cfg ext Q env blks m os mods (.arrow base fld) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hb (.arrowF .rval fld :: fs) ctx cont ?_
  intro vp pty m' os' mods' hp
  obtain ⟨b, off, sty, foff, fty, rv, rty, rfl, hptr, hfl, hrp, hpost⟩ := hf vp pty m' os' mods' hp
  have hstep : Sem.stepExprPure prog cfg env m' mods' (.ret (.rval (.ptr b off) pty) (.arrowF .rval fld :: fs)) =
      some (.ret (.rval rv rty) fs, m', mods') := by
    unfold Sem.stepExprPure
    dsimp only
    rw [hptr]
    simp only [hfl, hrp, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont rv rty m' os' mods' hpost)

theorem ExprSpec.assign_eq {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {l r : CExpr}
    {Pl : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : LvalSpec prog cfg ext Q env blks m os mods l Pl)
    (hr : ∀ b off lty m1 os1 mods1, Pl b off lty m1 os1 mods1 →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 r
        (fun rv rty m2 os2 mods2 =>
          mods2.conflicts b off (C99.sizeofTy prog.tags lty) = false ∧
          ∃ resV m3,
            Sem.writePlace prog.tags m2 b off lty (.rval rv rty) = some (.rval resV lty, m3) ∧
            Post resV lty m3 os2 (⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods2))) :
    ExprSpec prog cfg ext Q env blks m os mods (.assign .eq l r) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.assignLhsF .eq r :: fs) ctx cont ?_
  intro b off lty m1 os1 mods1 hpl
  refine WPTerm.of_exprPure rfl ?_
  refine (hr b off lty m1 os1 mods1 hpl) (.assignRhsF .eq b off lty :: fs) ctx cont ?_
  intro rv rty m2 os2 mods2 ⟨hnc, resV, m3, hwp, hpost⟩
  have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval rv rty) (.assignRhsF .eq b off lty :: fs)) =
      some (.ret (.rval resV lty) fs, m3, ⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods2) := by
    unfold Sem.stepExprPure Sem.assignOpToBin?
    simp only [hnc, Bool.not_false, guard_true, hwp, bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont resV lty m3 os2 _ hpost)

theorem ExprSpec.assign_op {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : AssignOp} {bop : BinOp} {l r : CExpr}
    (hop : Sem.assignOpToBin? op = some bop)
    {Pl : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : LvalSpec prog cfg ext Q env blks m os mods l Pl)
    (hr : ∀ b off lty m1 os1 mods1, Pl b off lty m1 os1 mods1 →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 r
        (fun rv rty m2 os2 mods2 =>
          mods2.conflicts b off (C99.sizeofTy prog.tags lty) = false ∧
          ∃ oldV nv nt resV m3,
            Sem.readVal prog.tags m2 b off lty = some oldV ∧
            Sem.applyBinary cfg prog.tags m2 bop oldV lty rv rty = some (nv, nt) ∧
            Sem.writePlace prog.tags m2 b off lty (.rval nv lty) = some (.rval resV lty, m3) ∧
            Post resV lty m3 os2 (⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods2))) :
    ExprSpec prog cfg ext Q env blks m os mods (.assign op l r) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.assignLhsF op r :: fs) ctx cont ?_
  intro b off lty m1 os1 mods1 hpl
  refine WPTerm.of_exprPure rfl ?_
  refine (hr b off lty m1 os1 mods1 hpl) (.assignRhsF op b off lty :: fs) ctx cont ?_
  intro rv rty m2 os2 mods2 ⟨hnc, oldV, nv, nt, resV, m3, hrv, hab, hwp, hpost⟩
  have hstep : Sem.stepExprPure prog cfg env m2 mods2 (.ret (.rval rv rty) (.assignRhsF op b off lty :: fs)) =
      some (.ret (.rval resV lty) fs, m3, ⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods2) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, hop, hrv, hab, hwp,
      bind, opt_bind_some, opt_pure_some]
  exact WPTerm.of_exprPure hstep (hcont resV lty m3 os2 _ hpost)

theorem ExprSpec.incDec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : IncDecOp} {l : CExpr}
    {Pl : BlockId → Int64 → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hl : LvalSpec prog cfg ext Q env blks m os mods l Pl)
    (hi : ∀ b off lty m1 os1 mods1, Pl b off lty m1 os1 mods1 →
      mods1.conflicts b off (C99.sizeofTy prog.tags lty) = false ∧
      ∃ oldV newV nt m2,
        Sem.readVal prog.tags m1 b off lty = some oldV ∧
        Sem.applyBinary cfg prog.tags m1 .add oldV lty
          (.int .i32 (BitVec.ofInt 32 (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1)))
          (.int .i32) = some (newV, nt) ∧
        Sem.writeVal m1 b off lty newV = some m2 ∧
        Post (match op with | .preInc | .preDec => newV | _ => oldV) lty m2 os1
          (⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods1)) :
    ExprSpec prog cfg ext Q env blks m os mods (.incDec op l) Post := by
  intro fs ctx cont hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hl (.incDecF op :: fs) ctx cont ?_
  intro b off lty m1 os1 mods1 hpl
  obtain ⟨hnc, oldV, newV, nt, m2, hrv, hab, hwv, hpost⟩ := hi b off lty m1 os1 mods1 hpl
  cases op with
  | preInc =>
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off lty) (.incDecF .preInc :: fs)) =
        some (.ret (.rval newV lty) fs, m2, ⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods1) := by
      unfold Sem.stepExprPure
      simp only [hnc, Bool.not_false, guard_true, hrv, hab, hwv, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep (hcont newV lty m2 os1 _ hpost)
  | preDec =>
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off lty) (.incDecF .preDec :: fs)) =
        some (.ret (.rval newV lty) fs, m2, ⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods1) := by
      unfold Sem.stepExprPure
      simp only [hnc, Bool.not_false, guard_true, hrv, hab, hwv, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep (hcont newV lty m2 os1 _ hpost)
  | postInc =>
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off lty) (.incDecF .postInc :: fs)) =
        some (.ret (.rval oldV lty) fs, m2, ⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods1) := by
      unfold Sem.stepExprPure
      simp only [hnc, Bool.not_false, guard_true, hrv, hab, hwv, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep (hcont oldV lty m2 os1 _ hpost)
  | postDec =>
    have hstep : Sem.stepExprPure prog cfg env m1 mods1 (.ret (.lval b off lty) (.incDecF .postDec :: fs)) =
        some (.ret (.rval oldV lty) fs, m2, ⟨b, off, C99.sizeofTy prog.tags lty⟩ :: mods1) := by
      unfold Sem.stepExprPure
      simp only [hnc, Bool.not_false, guard_true, hrv, hab, hwv, bind, opt_bind_some, opt_pure_some]
    exact WPTerm.of_exprPure hstep (hcont oldV lty m2 os1 _ hpost)

/-! ### 3.4 Function Call Combinators (`CallDispatchWP`, `ExprListSpec`, `call`) -/

theorem CallDispatchWP.internal {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {sym : String} {fnTy : CTy} {fn : FnDef} {argVals : List (Val × CTy)} {coerced : List Val}
    {m : Mem} {os : OSState} {fs : List ExprFrame} {ctx : ExprCtx} {k : Cont}
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
      WPTerm prog cfg ext Q
        (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k))) :
    CallDispatchWP prog cfg ext Q env blks sym fnTy argVals m os fs ctx k :=
  fun _ hd => WPTerm.of_call_internal hd hfn hcoerce hwit hw

theorem CallDispatchWP.ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {sym : String} {fnTy retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    {argVals : List (Val × CTy)} {coerced : List Val}
    {m : Mem} {os : OSState} {fs : List ExprFrame} {ctx : ExprCtx} {k : Cont}
    (hnfn : prog.fns sym = none)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hex : ∃ ret m' os', ext sym coerced m os (.ok ret m' os'))
    (hnoub : ¬ ext sym coerced m os .ub)
    (hw : ∀ ret m' os', ext sym coerced m os (.ok ret m' os') →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    CallDispatchWP prog cfg ext Q env blks sym fnTy argVals m os fs ctx k :=
  fun _ hd => WPTerm.of_call_ext hd hnfn hsig hcoerce hex hnoub hw

theorem ExprListSpec.singleton {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {done : List (Val × CTy)} {arg : CExpr}
    {Post : List (Val × CTy) → Mem → OSState → Prop}
    (ha : ExprSpec prog cfg ext Q env blks m os mods arg
      (fun v ty m' os' _ => Post [(v, ty)] m' os')) :
    ExprListSpec prog cfg ext Q env blks m os mods done [arg] Post := by
  intro sym fnTy fs ctx k hcont
  refine ha (.callArgF sym fnTy done [] :: fs) ctx k ?_
  intro v ty m' os' mods' hp
  exact hcont [(v, ty)] m' os' hp
    (.running (.expr (.ret (.rval v ty) (.callArgF sym fnTy done [] :: fs)) ctx mods') env blks m' os' k)
    (by unfold Sem.stepDet; cases v <;> rfl)

theorem ExprListSpec.cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {done : List (Val × CTy)}
    {arg a2 : CExpr} {rest : List CExpr}
    {P1 : Val → CTy → Mem → OSState → ModSet → Prop}
    {Post : List (Val × CTy) → Mem → OSState → Prop}
    (ha : ExprSpec prog cfg ext Q env blks m os mods arg P1)
    (htail : ∀ v ty m1 os1 mods1, P1 v ty m1 os1 mods1 →
      ExprListSpec prog cfg ext Q env blks m1 os1 mods1 (done ++ [(v, ty)]) (a2 :: rest)
        (fun vs m2 os2 => Post ((v, ty) :: vs) m2 os2)) :
    ExprListSpec prog cfg ext Q env blks m os mods done (arg :: a2 :: rest) Post := by
  intro sym fnTy fs ctx k hcont
  refine ha (.callArgF sym fnTy done (a2 :: rest) :: fs) ctx k ?_
  intro v ty m1 os1 mods1 hp1
  refine WPTerm.of_exprPure rfl ?_
  refine (htail v ty m1 os1 mods1 hp1) sym fnTy fs ctx k ?_
  intro vs m2 os2 hpost
  have heq : (done ++ [(v, ty)]) ++ vs = done ++ ((v, ty) :: vs) := by simp [List.append_assoc]
  rw [heq]
  exact hcont ((v, ty) :: vs) m2 os2 hpost

theorem ExprSpec.call_zero {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {fn : CExpr}
    {Pfn : String → CTy → Mem → OSState → ModSet → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hfn : ExprSpec prog cfg ext Q env blks m os mods fn
      (fun v ty m1 os1 mods1 => ∃ sym, v = .fnPtr sym ∧ Pfn sym ty m1 os1 mods1))
    (hcall : ∀ sym fnTy m1 os1 mods1 fs ctx k, Pfn sym fnTy m1 os1 mods1 →
      (∀ rv rt m' os', Post rv rt m' os' [] →
        WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx []) env blks m' os' k)) →
      CallDispatchWP prog cfg ext Q env blks sym fnTy [] m1 os1 fs ctx k) :
    ExprSpec prog cfg ext Q env blks m os mods (.call fn []) Post := by
  intro fs ctx k hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hfn (.callFnF [] :: fs) ctx k ?_
  intro fnVal fnTy m1 os1 mods1 ⟨sym, hfnEq, hp⟩
  subst hfnEq
  exact hcall sym fnTy m1 os1 mods1 fs ctx k hp
    (fun rv rt m' os' hpost => hcont rv rt m' os' [] hpost)
    (.running (.expr (.ret (.rval (.fnPtr sym) fnTy) (.callFnF [] :: fs)) ctx mods1) env blks m1 os1 k)
    (by unfold Sem.stepDet; rfl)

theorem ExprListSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {done : List (Val × CTy)} {args : List CExpr}
    {P1 P2 : List (Val × CTy) → Mem → OSState → Prop}
    (h : ExprListSpec prog cfg ext Q env blks m os mods done args P1)
    (himp : ∀ vs m' os', P1 vs m' os' → P2 vs m' os') :
    ExprListSpec prog cfg ext Q env blks m os mods done args P2 :=
  fun sym fnTy fs ctx k hcont =>
    h sym fnTy fs ctx k (fun vs m' os' hp1 => hcont vs m' os' (himp vs m' os' hp1))

theorem ExprSpec.call_args {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {fn arg : CExpr} {rest : List CExpr}
    {Pfn : String → CTy → Mem → OSState → ModSet → Prop}
    {Pargs : String → CTy → List (Val × CTy) → Mem → OSState → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hfn : ExprSpec prog cfg ext Q env blks m os mods fn
      (fun v ty m1 os1 mods1 => ∃ sym, v = .fnPtr sym ∧ Pfn sym ty m1 os1 mods1))
    (hargs : ∀ sym fnTy m1 os1 mods1, Pfn sym fnTy m1 os1 mods1 →
      ExprListSpec prog cfg ext Q env blks m1 os1 mods1 [] (arg :: rest)
        (fun vs m2 os2 => Pargs sym fnTy vs m2 os2))
    (hcall : ∀ sym fnTy vs m2 os2 fs ctx k, Pargs sym fnTy vs m2 os2 →
      (∀ rv rt m' os', Post rv rt m' os' [] →
        WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx []) env blks m' os' k)) →
      CallDispatchWP prog cfg ext Q env blks sym fnTy vs m2 os2 fs ctx k) :
    ExprSpec prog cfg ext Q env blks m os mods (.call fn (arg :: rest)) Post := by
  intro fs ctx k hcont
  refine WPTerm.of_exprPure rfl ?_
  refine hfn (.callFnF (arg :: rest) :: fs) ctx k ?_
  intro _ fnTy m1 os1 mods1 ⟨sym, hfnEq, hp⟩
  subst hfnEq
  refine WPTerm.of_exprPure rfl ?_
  refine (hargs sym fnTy m1 os1 mods1 hp) sym fnTy fs ctx k ?_
  intro vs m2 os2 hpargs
  rw [List.nil_append]
  exact hcall sym fnTy vs m2 os2 fs ctx k hpargs
    (fun rv rt m' os' hpost => hcont rv rt m' os' [] hpost)

/-! ### 3.5 Specialized Slot, Field, Array & Direct Call Helpers -/

theorem ExprSpec.assign_int_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {r : CExpr}
    {ty : CTy} {k : IntKind}
    (hslot : UninitLocalIntSlot env m x ty k)
    (hr : ExprSpec prog cfg ext Q env blks m os mods r
      (fun rv _ m2 _ mods2 =>
        (∀ b, env.lookup x = some (b, ty) → mods2.conflicts b 0 k.bytes = false) ∧
        ∃ iv, Sem.castVal m2 ty rv = some (.int k iv) ∧
          UninitLocalIntSlot env m2 x ty k))
    (hpost_fn : Mem → OSState → ModSet → BlockId → BitVec k.bits → Prop)
    (hbuild : ∀ b m2 os2 mods2 iv m3,
      env.lookup x = some (b, ty) →
      LocalIntSlot env m3 x ty k iv →
      FrameMod m2 m3 (· = b) →
      hpost_fn m3 os2 (⟨b, 0, k.bytes⟩ :: mods2) b iv) :
    ExprSpec prog cfg ext Q env blks m os mods (.assign .eq (.var x) r)
      (fun resV resTy m' os' mods' =>
        ∃ b iv, resV = .int k iv ∧ resTy = ty ∧ hpost_fn m' os' mods' b iv) := by
  have ⟨b0, _, hl0, _⟩ := hslot
  refine ExprSpec.assign_eq (PureLvalSpec.var hl0).to_lval ?_
  intro b off lty m1 os1 mods1 ⟨⟨hb, hoff, hty⟩, hm1, hos1, hmods1⟩
  subst hb hoff hty hm1 hos1 hmods1
  refine ExprSpec.mono hr ?_
  intro rv rty m2 os2 mods2 ⟨hmod, iv, hc, hslot2⟩
  obtain ⟨b', m3, hl', hwp, hloc', hfr⟩ := hslot2.writePlace_int_some prog.tags (t' := rty) hc
  rw [hl0] at hl'
  cases hl'
  have hty_int : lty.unqual = .int k := by rcases hslot2 with ⟨_, _, _, _, hty, _⟩; exact hty
  have hsz_eq : C99.sizeofTy prog.tags lty = k.bytes := sizeofTy_eq_bytes hty_int
  refine ⟨by rw [hsz_eq]; exact hmod b hl0, .int k iv, m3, hwp, ?_⟩
  rw [hsz_eq]
  exact ⟨b, iv, rfl, rfl, hbuild b m2 os2 mods2 iv m3 hl0 hloc' hfr⟩

theorem ExprSpec.assign_ptr_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {x : String} {r : CExpr}
    {ty el : CTy}
    (hslot : UninitLocalPtrSlot env m x ty el)
    (hr : ExprSpec prog cfg ext Q env blks m os mods r
      (fun rv _ m2 _ mods2 =>
        (∀ b, env.lookup x = some (b, ty) → mods2.conflicts b 0 8 = false) ∧
        (rv = .null ∨ ∃ bp op, rv = .ptr bp op) ∧
        UninitLocalPtrSlot env m2 x ty el))
    (hpost_fn : Mem → OSState → ModSet → BlockId → Val → Prop)
    (hbuild : ∀ b m2 os2 mods2 v m3,
      env.lookup x = some (b, ty) →
      LocalPtrSlot env m3 x ty el v →
      FrameMod m2 m3 (· = b) →
      hpost_fn m3 os2 (⟨b, 0, 8⟩ :: mods2) b v) :
    ExprSpec prog cfg ext Q env blks m os mods (.assign .eq (.var x) r)
      (fun resV resTy m' os' mods' =>
        ∃ b, resTy = ty ∧ hpost_fn m' os' mods' b resV) := by
  have ⟨b0, _, hl0, _⟩ := hslot
  refine ExprSpec.assign_eq (PureLvalSpec.var hl0).to_lval ?_
  intro b off lty m1 os1 mods1 ⟨⟨hb, hoff, hty⟩, hm1, hos1, hmods1⟩
  subst hb hoff hty hm1 hos1 hmods1
  refine ExprSpec.mono hr ?_
  intro rv rty m2 os2 mods2 ⟨hmod, hv, hslot2⟩
  obtain ⟨b', m3, hl', hwp, hloc', hfr⟩ := hslot2.writePlace_ptr_some prog.tags (t' := rty) hv
  rw [hl0] at hl'
  cases hl'
  have hty_ptr : lty.unqual = .ptr el := by rcases hslot2 with ⟨_, _, _, _, hty, _⟩; exact hty
  have hsz_eq : C99.sizeofTy prog.tags lty = 8 := sizeofTy_eq_ptr hty_ptr
  refine ⟨by rw [hsz_eq]; exact hmod b hl0, rv, m3, hwp, ?_⟩
  rw [hsz_eq]
  exact ⟨b, rfl, hbuild b m2 os2 mods2 rv m3 hl0 hloc' hfr⟩

theorem ExprSpec.call_ext_0 {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {sym : String}
    {retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    (hnenv : env.lookup sym = none)
    (henum : Sem.enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (retTy, paramTys, variadic))
    (hnfn : prog.fns sym = none)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic [] = some [])
    (hex : ∃ ret m' os', ext sym [] m os (.ok ret m' os'))
    (hnoub : ¬ ext sym [] m os .ub)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ ret m' os', ext sym [] m os (.ok ret m' os') → Post ret retTy m' os' []) :
    ExprSpec prog cfg ext Q env blks m os mods (.call (.var sym) []) Post := by
  refine ExprSpec.call_zero
    (Pfn := fun sym' fnTy' m1 os1 mods1 =>
      sym' = sym ∧ fnTy' = .fnPtr retTy paramTys variadic ∧ m1 = m ∧ os1 = os ∧ mods1 = mods)
    (hfn := ExprSpec.mono (PureExprSpec.var_fnProto hnenv henum hproto).to_expr
      (fun _ _ _ _ _ ⟨⟨hv, hty⟩, hm, hos, hmd⟩ => ⟨sym, hv, rfl, hty, hm, hos, hmd⟩)) ?_
  intro sym' fnTy m1 os1 mods1 fs ctx k ⟨hsym, hty, hm, hos, _⟩ hcont
  subst hsym hty hm hos
  exact CallDispatchWP.ext hnfn rfl hcoerce hex hnoub
    (fun ret m' os' hok => hcont ret retTy m' os' (hpost ret m' os' hok))

theorem ExprSpec.call_ext {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {sym : String} {arg : CExpr} {rest : List CExpr}
    {retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    (hnenv : env.lookup sym = none)
    (henum : Sem.enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (retTy, paramTys, variadic))
    (hnfn : prog.fns sym = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg ext Q env blks m os mods [] (arg :: rest) Pargs)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hext : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ coerced,
        Sem.coerceCallArgs m2 paramTys variadic vs = some coerced ∧
        (∃ ret m' os', ext sym coerced m2 os2 (.ok ret m' os')) ∧
        (¬ ext sym coerced m2 os2 .ub) ∧
        (∀ ret m' os', ext sym coerced m2 os2 (.ok ret m' os') →
          Post ret retTy m' os' [])) :
    ExprSpec prog cfg ext Q env blks m os mods (.call (.var sym) (arg :: rest)) Post := by
  refine ExprSpec.call_args
    (Pfn := fun sym' fnTy' m1 os1 mods1 =>
      sym' = sym ∧ fnTy' = .fnPtr retTy paramTys variadic ∧ m1 = m ∧ os1 = os ∧ mods1 = mods)
    (Pargs := fun sym' fnTy' vs m2 os2 =>
      sym' = sym ∧ fnTy' = .fnPtr retTy paramTys variadic ∧ Pargs vs m2 os2)
    (hfn := ExprSpec.mono (PureExprSpec.var_fnProto hnenv henum hproto).to_expr
      (fun _ _ _ _ _ ⟨⟨hv, hty⟩, hm, hos, hmd⟩ => ⟨sym, hv, rfl, hty, hm, hos, hmd⟩))
    (hargs := fun sym' fnTy' m1 os1 mods1 ⟨hsym, hty, hm, hos, hmd⟩ => by
      subst hsym hty hm hos hmd
      exact hargs.mono (fun vs m2 os2 hp => ⟨rfl, rfl, hp⟩)) ?_
  intro sym' fnTy vs m2 os2 fs ctx k ⟨hsym, hty, hpargs⟩ hcont
  subst hsym hty
  obtain ⟨coerced, hcoerce, hex, hnoub, hpost⟩ := hext vs m2 os2 hpargs
  exact CallDispatchWP.ext hnfn rfl hcoerce hex hnoub
    (fun ret m' os' hok => hcont ret retTy m' os' (hpost ret m' os' hok))

theorem ExprSpec.call_internal_0 {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {sym : String} {fn : FnDef}
    {retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    (hnenv : env.lookup sym = none)
    (henum : Sem.enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (retTy, paramTys, variadic))
    (hfn : prog.fns sym = some fn)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) fn.variadic [] = some [])
    (hwit : ∃ callEnv0 callBlks0 m0',
      Sem.pushCallParams prog.tags m (fun _ => 0) 0
        (fn.params.zip (([] : List Val).take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv0, callBlks0, m0'))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hw : ∀ base callEnv callBlks m' fs ctx k,
      Sem.pushCallParams prog.tags m base 0
        (fn.params.zip (([] : List Val).take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv, callBlks, m') →
      (∀ rv rt m'' os'', Post rv rt m'' os'' [] →
        WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx []) env blks m'' os'' k)) →
      WPTerm prog cfg ext Q
        (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k))) :
    ExprSpec prog cfg ext Q env blks m os mods (.call (.var sym) []) Post := by
  refine ExprSpec.call_zero
    (Pfn := fun sym' fnTy' m1 os1 mods1 =>
      sym' = sym ∧ fnTy' = .fnPtr retTy paramTys variadic ∧ m1 = m ∧ os1 = os ∧ mods1 = mods)
    (hfn := ExprSpec.mono (PureExprSpec.var_fnProto hnenv henum hproto).to_expr
      (fun _ _ _ _ _ ⟨⟨hv, hty⟩, hm, hos, hmd⟩ => ⟨sym, hv, rfl, hty, hm, hos, hmd⟩)) ?_
  intro sym' fnTy m1 os1 mods1 fs ctx k ⟨hsym, hty, hm, hos, _⟩ hcont
  subst hsym hty hm hos
  exact CallDispatchWP.internal hfn hcoerce hwit
    (fun base callEnv callBlks m' hpush => hw base callEnv callBlks m' fs ctx k hpush hcont)

theorem ExprSpec.call_internal {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {sym : String} {fn : FnDef}
    {arg : CExpr} {rest : List CExpr}
    {retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    (hnenv : env.lookup sym = none)
    (henum : Sem.enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (retTy, paramTys, variadic))
    (hfn : prog.fns sym = some fn)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg ext Q env blks m os mods [] (arg :: rest) Pargs)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hint : ∀ vs m2 os2 fs ctx k, Pargs vs m2 os2 →
      (∀ rv rt m'' os'', Post rv rt m'' os'' [] →
        WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx []) env blks m'' os'' k)) →
      ∃ coerced,
        Sem.coerceCallArgs m2 (fn.params.map (·.ty)) fn.variadic vs = some coerced ∧
        (∃ callEnv0 callBlks0 m0',
          Sem.pushCallParams prog.tags m2 (fun _ => 0) 0
            (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
              some (callEnv0, callBlks0, m0')) ∧
        (∀ base callEnv callBlks m',
          Sem.pushCallParams prog.tags m2 base 0
            (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
              some (callEnv, callBlks, m') →
          WPTerm prog cfg ext Q
            (.running (.stmt fn.body) callEnv callBlks m' os2 (.callFrame env blks fn.retTy fn.body fs ctx k)))) :
    ExprSpec prog cfg ext Q env blks m os mods (.call (.var sym) (arg :: rest)) Post := by
  refine ExprSpec.call_args
    (Pfn := fun sym' fnTy' m1 os1 mods1 =>
      sym' = sym ∧ fnTy' = .fnPtr retTy paramTys variadic ∧ m1 = m ∧ os1 = os ∧ mods1 = mods)
    (Pargs := fun sym' fnTy' vs m2 os2 =>
      sym' = sym ∧ fnTy' = .fnPtr retTy paramTys variadic ∧ Pargs vs m2 os2)
    (hfn := ExprSpec.mono (PureExprSpec.var_fnProto hnenv henum hproto).to_expr
      (fun _ _ _ _ _ ⟨⟨hv, hty⟩, hm, hos, hmd⟩ => ⟨sym, hv, rfl, hty, hm, hos, hmd⟩))
    (hargs := fun sym' fnTy' m1 os1 mods1 ⟨hsym, hty, hm, hos, hmd⟩ => by
      subst hsym hty hm hos hmd
      exact hargs.mono (fun vs m2 os2 hp => ⟨rfl, rfl, hp⟩)) ?_
  intro sym' fnTy vs m2 os2 fs ctx k ⟨hsym, hty, hpargs⟩ hcont
  subst hsym hty
  obtain ⟨coerced, hcoerce, hwit, hw⟩ := hint vs m2 os2 fs ctx k hpargs hcont
  exact CallDispatchWP.internal hfn hcoerce hwit hw

theorem ExprSpec.call_fnPtr_args {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {fn arg : CExpr} {rest : List CExpr}
    {Pfn : String → CTy → Mem → OSState → ModSet → Prop}
    {Pargs : String → CTy → List (Val × CTy) → Mem → OSState → Prop}
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hfn : ExprSpec prog cfg ext Q env blks m os mods fn
      (fun v ty m1 os1 mods1 => ∃ sym, v = .fnPtr sym ∧ Pfn sym ty m1 os1 mods1))
    (hargs : ∀ sym fnTy m1 os1 mods1, Pfn sym fnTy m1 os1 mods1 →
      ExprListSpec prog cfg ext Q env blks m1 os1 mods1 [] (arg :: rest)
        (fun vs m2 os2 => Pargs sym fnTy vs m2 os2))
    (hcall : ∀ sym fnTy vs m2 os2 fs ctx k, Pargs sym fnTy vs m2 os2 →
      (∀ rv rt m' os', Post rv rt m' os' [] →
        WPTerm prog cfg ext Q (.running (.expr (.ret (.rval rv rt) fs) ctx []) env blks m' os' k)) →
      CallDispatchWP prog cfg ext Q env blks sym fnTy vs m2 os2 fs ctx k) :
    ExprSpec prog cfg ext Q env blks m os mods (.call fn (arg :: rest)) Post :=
  ExprSpec.call_args hfn hargs hcall

theorem PureExprSpec.arrow_cell_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base : CExpr} {fld : String}
    {b : BlockId} {off : Int64} {pty sty : CTy} {foff : Nat} {fty : CTy} {fk : IntKind} {fv : Val}
    (hb : PureExprSpec prog cfg ext Q env blks m os mods base (fun x t => x = .ptr b off ∧ t = pty))
    (hp : pty.unqual = .ptr sty)
    (hfl : fieldLayout? prog.tags sty fld = some (foff, fty))
    (hfint : fty.unqual = .int fk)
    (hcell : FieldCell prog.tags m b (Int64.ofInt (off.toInt + foff)) fty fv)
    (hmod : mods.conflicts b (Int64.ofInt (off.toInt + foff)) fk.bytes = false) :
    PureExprSpec prog cfg ext Q env blks m os mods (.arrow base fld)
      (fun rv rty => rv = fv ∧ rty = .int fk) := by
  refine ExprSpec.arrow hb.to_expr ?_
  intro vp pty' m' os' mods' ⟨⟨hvp, hpty'⟩, hm', hos', hmods'⟩
  subst hvp hpty' hm' hos' hmods'
  exact ⟨b, off, sty, foff, fty, fv, .int fk, rfl, hp, hfl,
    hcell.readPlace_int_some hfint hmod, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem PureExprSpec.arrow_cell_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base : CExpr} {fld : String}
    {b : BlockId} {off : Int64} {pty sty : CTy} {foff : Nat} {fty fel : CTy} {fv : Val}
    (hb : PureExprSpec prog cfg ext Q env blks m os mods base (fun x t => x = .ptr b off ∧ t = pty))
    (hp : pty.unqual = .ptr sty)
    (hfl : fieldLayout? prog.tags sty fld = some (foff, fty))
    (hfptr : fty.unqual = .ptr fel)
    (hcell : FieldCell prog.tags m b (Int64.ofInt (off.toInt + foff)) fty fv)
    (hmod : mods.conflicts b (Int64.ofInt (off.toInt + foff)) 8 = false) :
    PureExprSpec prog cfg ext Q env blks m os mods (.arrow base fld)
      (fun rv rty => rv = fv ∧ rty = .ptr fel) := by
  refine ExprSpec.arrow hb.to_expr ?_
  intro vp pty' m' os' mods' ⟨⟨hvp, hpty'⟩, hm', hos', hmods'⟩
  subst hvp hpty' hm' hos' hmods'
  exact ⟨b, off, sty, foff, fty, fv, .ptr fel, rfl, hp, hfl,
    hcell.readPlace_ptr_some hfptr hmod, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem PureExprSpec.index_slice_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base idx : CExpr}
    {b : BlockId} {baseOff : Int64} {pty el : CTy} {elems : List Val}
    {ik : IntKind} {iv : BitVec ik.bits} {ek : IntKind} {i : Nat}
    (hb : PureExprSpec prog cfg ext Q env blks m os mods base
      (fun x t => x = .ptr b baseOff ∧ t = pty))
    (hp : pty.unqual = .ptr el)
    (hel : el.unqual = .int ek)
    (hslice : ArraySlice prog.tags m b baseOff el elems)
    (hidx : PureExprSpec prog cfg ext Q env blks m os mods idx (fun x _ => x = .int ik iv))
    (hi_val : (if ik.signed then iv.toInt else (iv.toNat : Int)) = (i : Int))
    (hi_lt : i < elems.length)
    (hmod : mods.conflicts b (Int64.ofInt (baseOff.toInt + (i * C99.sizeofTy prog.tags el : Int))) ek.bytes = false) :
    PureExprSpec prog cfg ext Q env blks m os mods (.index base idx)
      (fun rv rty => rv = elems[i] ∧ rty = .int ek) := by
  have hcell := hslice.elemCell i hi_lt
  rcases hslice with ⟨hpos, blk, hblk, hlo, hhi, _, _⟩
  have hblk_sz : (blk.size : Int) < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    exact_mod_cast this
  have hmax : (max 1 (C99.sizeofTy prog.tags el) : Int) = (C99.sizeofTy prog.tags el : Int) := by omega
  have hmul_nonneg : 0 ≤ (i : Int) * (C99.sizeofTy prog.tags el : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hmul_le := mul_add_le_mul_of_lt (s := C99.sizeofTy prog.tags el) hi_lt
  have hadd : Sem.evalPtrAdd cfg prog.tags m (.ptr b baseOff) el (i : Int) =
      some (.ptr b (Int64.ofInt (baseOff.toInt + (i * C99.sizeofTy prog.tags el : Int)))) := by
    have h1 := evalPtrAdd_some (cfg := cfg) (tags := prog.tags) (off := baseOff) (el := el)
      (idx := (i : Int)) hblk (by rw [hmax]; omega) (by rw [hmax]; omega)
    rw [hmax] at h1
    exact h1
  refine ExprSpec.index hb.to_expr ?_
  intro vp tp m1 os1 mods1 ⟨⟨hvp, htp⟩, hm1, hos1, hmods1⟩
  subst hvp htp hm1 hos1 hmods1
  refine ExprSpec.mono hidx.to_expr ?_
  intro vi ti m2 os2 mods2 ⟨hvi_eq, hm2, hos2, hmods2⟩
  subst hvi_eq hm2 hos2 hmods2
  have hvi : valAsInt? (.int ik iv) = some (ik, (i : Int)) := by change some _ = _; rw [hi_val]
  exact ⟨el, ik, (i : Int), b, Int64.ofInt (baseOff.toInt + (i * C99.sizeofTy prog.tags el : Int)),
    elems[i], .int ek, hp, hvi, hadd, hcell.readPlace_int_some hel hmod,
    ⟨rfl, rfl⟩, rfl, rfl, rfl⟩

theorem ExprSpec.incDec_int_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : IncDecOp} {x : String}
    {ty : CTy} {k : IntKind} {old : BitVec k.bits}
    (hnc : ty.isConst = false)
    (hslot : LocalIntSlot env m x ty k old)
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 k.bytes = false)
    {newV : BitVec k.bits}
    (hadd : Sem.evalIntBinary .add (.int k old)
      (.int .i32 (BitVec.ofInt 32 (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1))) =
      some (.int k newV, .int k)) :
    ExprSpec prog cfg ext Q env blks m os mods (.incDec op (.var x))
      (fun rv rt m' os' mods' =>
        ∃ b, env.lookup x = some (b, ty) ∧
          rv = .int k (match op with | .preInc | .preDec => newV | _ => old) ∧
          rt = ty ∧ LocalIntSlot env m' x ty k newV ∧ FrameMod m m' (· = b) ∧
          os' = os ∧ mods' = ⟨b, 0, k.bytes⟩ :: mods) := by
  rcases hslot with ⟨b0, blk0, hl0, hty0, hb0, hp0, hsz0, hal0, hrb0⟩
  cases op with
  | preInc | postInc =>
    refine ExprSpec.incDec (PureLvalSpec.var hl0).to_lval ?_
    intro b off lty m1 os1 mods1 ⟨⟨hb, hoff, hty⟩, hm1, hos1, hmods1⟩
    subst hb hoff hty hm1 hos1 hmods1
    have hslot0 : LocalIntSlot env m1 x lty k old := ⟨b, blk0, hl0, hty0, hb0, hp0, hsz0, hal0, hrb0⟩
    have hsz_eq : C99.sizeofTy prog.tags lty = k.bytes := sizeofTy_eq_bytes hty0
    have hrv : Sem.readVal prog.tags m1 b 0 lty = some (.int k old) :=
      readVal_int_of_readBytes prog.tags hty0 hb0 hal0 hrb0
    have hab : Sem.applyBinary cfg prog.tags m1 .add (.int k old) lty
        (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) = some (.int k newV, .int k) := by
      rw [applyBinary_int_eq (k1 := k) (k2 := .i32) hty0 rfl]; exact hadd
    obtain ⟨b', m2, hl', hwv, hslot', hfr⟩ := (hslot0.to_uninit hnc).writeVal_int_some newV
    rw [hl0] at hl'; cases hl'
    exact ⟨by rw [hsz_eq]; exact hmod b hl0, .int k old, .int k newV, .int k, m2, hrv, hab, hwv,
      b, hl0, rfl, rfl, hslot', hfr, rfl, by rw [hsz_eq]⟩
  | preDec | postDec =>
    refine ExprSpec.incDec (PureLvalSpec.var hl0).to_lval ?_
    intro b off lty m1 os1 mods1 ⟨⟨hb, hoff, hty⟩, hm1, hos1, hmods1⟩
    subst hb hoff hty hm1 hos1 hmods1
    have hslot0 : LocalIntSlot env m1 x lty k old := ⟨b, blk0, hl0, hty0, hb0, hp0, hsz0, hal0, hrb0⟩
    have hsz_eq : C99.sizeofTy prog.tags lty = k.bytes := sizeofTy_eq_bytes hty0
    have hrv : Sem.readVal prog.tags m1 b 0 lty = some (.int k old) :=
      readVal_int_of_readBytes prog.tags hty0 hb0 hal0 hrb0
    have hab : Sem.applyBinary cfg prog.tags m1 .add (.int k old) lty
        (.int .i32 (BitVec.ofInt 32 (-1))) (.int .i32) = some (.int k newV, .int k) := by
      rw [applyBinary_int_eq (k1 := k) (k2 := .i32) hty0 rfl]; exact hadd
    obtain ⟨b', m2, hl', hwv, hslot', hfr⟩ := (hslot0.to_uninit hnc).writeVal_int_some newV
    rw [hl0] at hl'; cases hl'
    exact ⟨by rw [hsz_eq]; exact hmod b hl0, .int k old, .int k newV, .int k, m2, hrv, hab, hwv,
      b, hl0, rfl, rfl, hslot', hfr, rfl, by rw [hsz_eq]⟩

theorem ExprSpec.incDec_ptr_slot {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {op : IncDecOp} {x : String}
    {ty el : CTy} {pb : BlockId} {poff newOff : Int64}
    (hnc : ty.isConst = false)
    (hslot : LocalPtrSlot env m x ty el (.ptr pb poff))
    (hmod : ∀ b, env.lookup x = some (b, ty) → mods.conflicts b 0 8 = false)
    (hadd : Sem.evalPtrAdd cfg prog.tags m (.ptr pb poff) el
      (match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1) = some (.ptr pb newOff)) :
    ExprSpec prog cfg ext Q env blks m os mods (.incDec op (.var x))
      (fun rv rt m' os' mods' =>
        ∃ b, env.lookup x = some (b, ty) ∧
          rv = .ptr pb (match op with | .preInc | .preDec => newOff | _ => poff) ∧
          rt = ty ∧ LocalPtrSlot env m' x ty el (.ptr pb newOff) ∧ FrameMod m m' (· = b) ∧
          os' = os ∧ mods' = ⟨b, 0, 8⟩ :: mods) := by
  rcases hslot with ⟨b0, blk0, hl0, hty0, hb0, hp0, hsz0, hal0, hrb0⟩
  cases op with
  | preInc | postInc =>
    refine ExprSpec.incDec (PureLvalSpec.var hl0).to_lval ?_
    intro b off lty m1 os1 mods1 ⟨⟨hb, hoff, hty⟩, hm1, hos1, hmods1⟩
    subst hb hoff hty hm1 hos1 hmods1
    have hslot0 : LocalPtrSlot env m1 x lty el (.ptr pb poff) :=
      ⟨b, blk0, hl0, hty0, hb0, hp0, hsz0, hal0, hrb0⟩
    have hsz_eq : C99.sizeofTy prog.tags lty = 8 := sizeofTy_eq_ptr hty0
    have hrv : Sem.readVal prog.tags m1 b 0 lty = some (.ptr pb poff) :=
      readVal_ptr_of_readBytes prog.tags hty0 hb0 hal0 (by
        rcases hrb0 with ⟨hnull, _⟩ | ⟨bp, op0, hp_eq, hr⟩
        · cases hnull
        · cases hp_eq; exact Or.inr ⟨pb, poff, rfl, hr⟩)
    have h32 : (BitVec.ofInt 32 1).toInt = 1 := by decide
    have hadd' : Sem.evalPtrAdd cfg prog.tags m1 (.ptr pb poff) el (BitVec.ofInt 32 1).toInt =
        some (.ptr pb newOff) := by rw [h32]; exact hadd
    have hab : Sem.applyBinary cfg prog.tags m1 .add (.ptr pb poff) lty
        (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) = some (.ptr pb newOff, .ptr el) :=
      applyBinary_ptrAdd_r hty0 hadd'
    obtain ⟨b', m2, hl', hwv, hslot', hfr⟩ := (hslot0.to_uninit hnc).writeVal_ptr_some (Or.inr ⟨pb, newOff, rfl⟩)
    rw [hl0] at hl'; cases hl'
    exact ⟨by rw [hsz_eq]; exact hmod b hl0, .ptr pb poff, .ptr pb newOff, .ptr el, m2, hrv, hab, hwv,
      b, hl0, rfl, rfl, hslot', hfr, rfl, by rw [hsz_eq]⟩
  | preDec | postDec =>
    refine ExprSpec.incDec (PureLvalSpec.var hl0).to_lval ?_
    intro b off lty m1 os1 mods1 ⟨⟨hb, hoff, hty⟩, hm1, hos1, hmods1⟩
    subst hb hoff hty hm1 hos1 hmods1
    have hslot0 : LocalPtrSlot env m1 x lty el (.ptr pb poff) :=
      ⟨b, blk0, hl0, hty0, hb0, hp0, hsz0, hal0, hrb0⟩
    have hsz_eq : C99.sizeofTy prog.tags lty = 8 := sizeofTy_eq_ptr hty0
    have hrv : Sem.readVal prog.tags m1 b 0 lty = some (.ptr pb poff) :=
      readVal_ptr_of_readBytes prog.tags hty0 hb0 hal0 (by
        rcases hrb0 with ⟨hnull, _⟩ | ⟨bp, op0, hp_eq, hr⟩
        · cases hnull
        · cases hp_eq; exact Or.inr ⟨pb, poff, rfl, hr⟩)
    have h32 : (BitVec.ofInt 32 (-1)).toInt = -1 := by decide
    have hadd' : Sem.evalPtrAdd cfg prog.tags m1 (.ptr pb poff) el (BitVec.ofInt 32 (-1)).toInt =
        some (.ptr pb newOff) := by rw [h32]; exact hadd
    have hab : Sem.applyBinary cfg prog.tags m1 .add (.ptr pb poff) lty
        (.int .i32 (BitVec.ofInt 32 (-1))) (.int .i32) = some (.ptr pb newOff, .ptr el) :=
      applyBinary_ptrAdd_r hty0 hadd'
    obtain ⟨b', m2, hl', hwv, hslot', hfr⟩ := (hslot0.to_uninit hnc).writeVal_ptr_some (Or.inr ⟨pb, newOff, rfl⟩)
    rw [hl0] at hl'; cases hl'
    exact ⟨by rw [hsz_eq]; exact hmod b hl0, .ptr pb poff, .ptr pb newOff, .ptr el, m2, hrv, hab, hwv,
      b, hl0, rfl, rfl, hslot', hfr, rfl, by rw [hsz_eq]⟩

theorem ExprSpec.assign_int_field {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base rhs : CExpr} {fld : String}
    {b : BlockId} {off : Int64} {pty sty : CTy} {foff : Nat} {fty : CTy} {fk : IntKind}
    (hb : ExprSpec prog cfg ext Q env blks m os mods base
      (fun vp pt m1 _ _ => vp = .ptr b off ∧ pt = pty ∧
        FieldUninit prog.tags m1 b (Int64.ofInt (off.toInt + foff)) fty))
    (hptr : pty.unqual = .ptr sty)
    (hfl : fieldLayout? prog.tags sty fld = some (foff, fty))
    (hfk : fty.unqual = .int fk)
    (hr : ∀ m1 os1 mods1,
      FieldUninit prog.tags m1 b (Int64.ofInt (off.toInt + foff)) fty →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 rhs
        (fun rv _ m2 _ mods2 =>
          mods2.conflicts b (Int64.ofInt (off.toInt + foff)) fk.bytes = false ∧
          ∃ iv, Sem.castVal m2 fty rv = some (.int fk iv) ∧
            FieldUninit prog.tags m2 b (Int64.ofInt (off.toInt + foff)) fty))
    (hpost_fn : Mem → OSState → ModSet → BitVec fk.bits → Prop)
    (hbuild : ∀ m2 os2 mods2 iv m3,
      FieldMutCell prog.tags m3 b (Int64.ofInt (off.toInt + foff)) fty (.int fk iv) →
      FrameMod m2 m3 (· = b) →
      hpost_fn m3 os2 (⟨b, Int64.ofInt (off.toInt + foff), fk.bytes⟩ :: mods2) iv) :
    ExprSpec prog cfg ext Q env blks m os mods (.assign .eq (.arrow base fld) rhs)
      (fun resV resTy m' os' mods' =>
        ∃ iv, resV = .int fk iv ∧ resTy = fty ∧ hpost_fn m' os' mods' iv) := by
  refine ExprSpec.assign_eq (LvalSpec.arrow hb
    (Post := fun b' off' fty' m1 _ _ =>
      b' = b ∧ off' = Int64.ofInt (off.toInt + foff) ∧ fty' = fty ∧
      FieldUninit prog.tags m1 b (Int64.ofInt (off.toInt + foff)) fty)
    (fun vp pt m1 _ _ ⟨hvp, hpt, hfu⟩ =>
      ⟨b, off, sty, foff, fty, hvp, by rw [hpt]; exact hptr, hfl, rfl, rfl, rfl, hfu⟩)) ?_
  intro b' off' fty' m1 os1 mods1 ⟨hb', hoff', hfty', hfu1⟩
  subst hb' hoff' hfty'
  refine ExprSpec.mono (hr m1 os1 mods1 hfu1) ?_
  intro rv rty m2 os2 mods2 ⟨hmod, iv, hc, hfu2⟩
  obtain ⟨m3, hwp, hcell', hfr⟩ := hfu2.writePlace_int_some hfk (t' := rty) hc
  have hsz_eq : C99.sizeofTy prog.tags fty' = fk.bytes := sizeofTy_eq_bytes hfk
  refine ⟨by rw [hsz_eq]; exact hmod, .int fk iv, m3, hwp, ?_⟩
  rw [hsz_eq]
  exact ⟨iv, rfl, rfl, hbuild m2 os2 mods2 iv m3 hcell' hfr⟩

theorem ExprSpec.assign_ptr_field {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {base rhs : CExpr} {fld : String}
    {b : BlockId} {off : Int64} {pty sty : CTy} {foff : Nat} {fty fel : CTy}
    (hb : ExprSpec prog cfg ext Q env blks m os mods base
      (fun vp pt m1 _ _ => vp = .ptr b off ∧ pt = pty ∧
        FieldUninit prog.tags m1 b (Int64.ofInt (off.toInt + foff)) fty))
    (hptr : pty.unqual = .ptr sty)
    (hfl : fieldLayout? prog.tags sty fld = some (foff, fty))
    (hfel : fty.unqual = .ptr fel)
    (hr : ∀ m1 os1 mods1,
      FieldUninit prog.tags m1 b (Int64.ofInt (off.toInt + foff)) fty →
      ExprSpec prog cfg ext Q env blks m1 os1 mods1 rhs
        (fun rv _ m2 _ mods2 =>
          mods2.conflicts b (Int64.ofInt (off.toInt + foff)) 8 = false ∧
          (rv = .null ∨ ∃ bp op, rv = .ptr bp op) ∧
          FieldUninit prog.tags m2 b (Int64.ofInt (off.toInt + foff)) fty))
    (hpost_fn : Mem → OSState → ModSet → Val → Prop)
    (hbuild : ∀ m2 os2 mods2 v m3,
      FieldMutCell prog.tags m3 b (Int64.ofInt (off.toInt + foff)) fty v →
      FrameMod m2 m3 (· = b) →
      hpost_fn m3 os2 (⟨b, Int64.ofInt (off.toInt + foff), 8⟩ :: mods2) v) :
    ExprSpec prog cfg ext Q env blks m os mods (.assign .eq (.arrow base fld) rhs)
      (fun resV resTy m' os' mods' =>
        resTy = fty ∧ hpost_fn m' os' mods' resV) := by
  refine ExprSpec.assign_eq (LvalSpec.arrow hb
    (Post := fun b' off' fty' m1 _ _ =>
      b' = b ∧ off' = Int64.ofInt (off.toInt + foff) ∧ fty' = fty ∧
      FieldUninit prog.tags m1 b (Int64.ofInt (off.toInt + foff)) fty)
    (fun vp pt m1 _ _ ⟨hvp, hpt, hfu⟩ =>
      ⟨b, off, sty, foff, fty, hvp, by rw [hpt]; exact hptr, hfl, rfl, rfl, rfl, hfu⟩)) ?_
  intro b' off' fty' m1 os1 mods1 ⟨hb', hoff', hfty', hfu1⟩
  subst hb' hoff' hfty'
  refine ExprSpec.mono (hr m1 os1 mods1 hfu1) ?_
  intro rv rty m2 os2 mods2 ⟨hmod, hv, hfu2⟩
  obtain ⟨m3, hwp, hcell', hfr⟩ := hfu2.writePlace_ptr_some hfel (t' := rty) hv
  have hsz_eq : C99.sizeofTy prog.tags fty' = 8 := sizeofTy_eq_ptr hfel
  refine ⟨by rw [hsz_eq]; exact hmod, rv, m3, hwp, ?_⟩
  rw [hsz_eq]
  exact ⟨rfl, hbuild m2 os2 mods2 rv m3 hcell' hfr⟩

/-! ## 4. Continuation-Polymorphic `StmtSpec` & Multi-Exit `StmtSpecEx` -/

/-- Whether continuation `k` contains an enclosing `.callFrame`. -/
def contHasCallFrame : Cont → Bool
  | .stop _ => false
  | .callFrame .. => true
  | .stmts _ k | .blockEnd _ _ k | .loop _ _ _ _ k | .switchCont k => contHasCallFrame k

/-- Continuation `k` accepts any `break` exit satisfying `PBrk`. -/
def BreakContOK (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop)
    (PBrk : Env → List BlockId → Mem → OSState → Prop) (k : Cont) : Prop :=
  ∀ env' blks' m' os', PBrk env' blks' m' os' →
    ∃ e2 b2 m2 k2, Sem.unwindBreak m' env' blks' k = some (e2, b2, m2, k2) ∧
      WPTerm prog cfg ext Q (.running (.stmt .nop) e2 b2 m2 os' k2)

/-- Continuation `k` accepts any `continue` exit satisfying `PCont`. -/
def ContContOK (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop)
    (PCont : Env → List BlockId → Mem → OSState → Prop) (k : Cont) : Prop :=
  ∀ env' blks' m' os', PCont env' blks' m' os' →
    ∃ c? stp? body isDo e2 b2 m2 k2,
      Sem.unwindContinue m' env' blks' k = some (c?, stp?, body, isDo, e2, b2, m2, k2) ∧
      WPTerm prog cfg ext Q (Sem.loopNext c? stp? body isDo e2 b2 m2 os' k2)

/-- Continuation `k` accepts any cast `return` exit satisfying `PRet` at return type `rt`. -/
def RetContOK (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (rt : CTy)
    (PRet : Val → List BlockId → Mem → OSState → Prop) (k : Cont) : Prop :=
  k.topRetTy = rt ∧
  ∀ cv blks' m' os', (rt.isVoid = true → cv = .void) → PRet cv blks' m' os' →
    contHasCallFrame k = true ∧
    ∃ re rb rt' m2 fs rctx rk,
      Sem.unwindReturn m' blks' k = some (re, rb, rt', m2, fs, rctx, rk) ∧
      let rtOut := if rt.isVoid then .void else rt
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval cv rtOut) fs) rctx []) re rb m2 os' rk)

/-- Normal-exit statement specification over `WPTerm`. -/
def StmtSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (s : CStmt)
    (PostNorm : Env → List BlockId → Mem → OSState → Prop) : Prop :=
  ∀ k,
    (∀ env' blks' m' os', PostNorm env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k)) →
    WPTerm prog cfg ext Q (.running (.stmt s) env blks m os k)

/-- Normal-exit statement-list specification over `WPTerm`. -/
def StmtsSpec (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (ss : List CStmt)
    (PostNorm : Env → List BlockId → Mem → OSState → Prop) : Prop :=
  ∀ k,
    (∀ env' blks' m' os', PostNorm env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k)) →
    match ss with
    | [] => WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)
    | hd :: tl => WPTerm prog cfg ext Q (.running (.stmt hd) env blks m os (.stmts tl k))

/-- Multi-exit statement specification tracking normal exit, `break`, `continue`, and `return`. -/
def StmtSpecEx (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) (s : CStmt)
    (PostNorm PostBrk PostCont : Env → List BlockId → Mem → OSState → Prop)
    (PostRet : Val → List BlockId → Mem → OSState → Prop) : Prop :=
  ∀ k,
    (∀ env' blks' m' os', PostNorm env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k)) →
    BreakContOK prog cfg ext Q PostBrk k →
    ContContOK prog cfg ext Q PostCont k →
    RetContOK prog cfg ext Q rt PostRet k →
    WPTerm prog cfg ext Q (.running (.stmt s) env blks m os k)

/-- Multi-exit statement-list specification tracking normal exit, `break`, `continue`, and `return`. -/
def StmtsSpecEx (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) (ss : List CStmt)
    (PostNorm PostBrk PostCont : Env → List BlockId → Mem → OSState → Prop)
    (PostRet : Val → List BlockId → Mem → OSState → Prop) : Prop :=
  ∀ k,
    (∀ env' blks' m' os', PostNorm env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k)) →
    BreakContOK prog cfg ext Q PostBrk k →
    ContContOK prog cfg ext Q PostCont k →
    RetContOK prog cfg ext Q rt PostRet k →
    match ss with
    | [] => WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os k)
    | hd :: tl => WPTerm prog cfg ext Q (.running (.stmt hd) env blks m os (.stmts tl k))

/-! ### 4.1 Continuation Exit Helpers (`BreakContOK`, `ContContOK`, `RetContOK`) -/

theorem BreakContOK.false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} (k : Cont) :
    BreakContOK prog cfg ext Q (fun _ _ _ _ => False) k :=
  fun _ _ _ _ h => False.elim h

theorem ContContOK.false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} (k : Cont) :
    ContContOK prog cfg ext Q (fun _ _ _ _ => False) k :=
  fun _ _ _ _ h => False.elim h

theorem RetContOK.false {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {k : Cont} :
    RetContOK prog cfg ext Q k.topRetTy (fun _ _ _ _ => False) k :=
  ⟨rfl, fun _ _ _ _ _ h => False.elim h⟩

theorem BreakContOK.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P1 P2 : Env → List BlockId → Mem → OSState → Prop} {k : Cont}
    (h : BreakContOK prog cfg ext Q P2 k) (himp : ∀ e b m o, P1 e b m o → P2 e b m o) :
    BreakContOK prog cfg ext Q P1 k :=
  fun e b m o hp => h e b m o (himp e b m o hp)

theorem ContContOK.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P1 P2 : Env → List BlockId → Mem → OSState → Prop} {k : Cont}
    (h : ContContOK prog cfg ext Q P2 k) (himp : ∀ e b m o, P1 e b m o → P2 e b m o) :
    ContContOK prog cfg ext Q P1 k :=
  fun e b m o hp => h e b m o (himp e b m o hp)

theorem RetContOK.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {rt : CTy}
    {P1 P2 : Val → List BlockId → Mem → OSState → Prop} {k : Cont}
    (h : RetContOK prog cfg ext Q rt P2 k) (himp : ∀ v b m o, P1 v b m o → P2 v b m o) :
    RetContOK prog cfg ext Q rt P1 k :=
  ⟨h.1, fun v b m o hv hp => h.2 v b m o hv (himp v b m o hp)⟩

theorem BreakContOK.stmts {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop}
    {ss : List CStmt} {k : Cont} (h : BreakContOK prog cfg ext Q P k) :
    BreakContOK prog cfg ext Q P (.stmts ss k) := h

theorem ContContOK.stmts {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop}
    {ss : List CStmt} {k : Cont} (h : ContContOK prog cfg ext Q P k) :
    ContContOK prog cfg ext Q P (.stmts ss k) := h

theorem RetContOK.stmts {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {rt : CTy}
    {P : Val → List BlockId → Mem → OSState → Prop} {ss : List CStmt} {k : Cont}
    (h : RetContOK prog cfg ext Q rt P k) :
    RetContOK prog cfg ext Q rt P (.stmts ss k) := h

theorem BreakContOK.blockEnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop}
    {savedEnv : Env} {savedBlks : List BlockId} {k : Cont}
    (h : BreakContOK prog cfg ext Q
      (fun e b m o => e = savedEnv ∧ b = savedBlks ∧ ∃ e0 b0 m0, m = m0.freeStack b0 ∧ P e0 b0 m0 o) k) :
    BreakContOK prog cfg ext Q P (.blockEnd savedEnv savedBlks k) :=
  fun env' blks' m' os' hp =>
    h savedEnv savedBlks (m'.freeStack blks') os' ⟨rfl, rfl, env', blks', m', rfl, hp⟩

theorem ContContOK.blockEnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop}
    {savedEnv : Env} {savedBlks : List BlockId} {k : Cont}
    (h : ContContOK prog cfg ext Q
      (fun e b m o => e = savedEnv ∧ b = savedBlks ∧ ∃ e0 b0 m0, m = m0.freeStack b0 ∧ P e0 b0 m0 o) k) :
    ContContOK prog cfg ext Q P (.blockEnd savedEnv savedBlks k) :=
  fun env' blks' m' os' hp =>
    h savedEnv savedBlks (m'.freeStack blks') os' ⟨rfl, rfl, env', blks', m', rfl, hp⟩

theorem RetContOK.blockEnd {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {rt : CTy}
    {P : Val → List BlockId → Mem → OSState → Prop}
    {savedEnv : Env} {savedBlks : List BlockId} {k : Cont}
    (h : RetContOK prog cfg ext Q rt
      (fun v b m o => b = savedBlks ∧ ∃ b0 m0, m = m0.freeStack b0 ∧ P v b0 m0 o) k) :
    RetContOK prog cfg ext Q rt P (.blockEnd savedEnv savedBlks k) :=
  ⟨h.1, fun cv blks' m' os' hv hp => h.2 cv savedBlks (m'.freeStack blks') os' hv ⟨rfl, blks', m', rfl, hp⟩⟩

theorem BreakContOK.switchCont {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop} {k : Cont}
    (h : ∀ env' blks' m' os', P env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k)) :
    BreakContOK prog cfg ext Q P (.switchCont k) :=
  fun env' blks' m' os' hp => ⟨env', blks', m', k, rfl, h env' blks' m' os' hp⟩

theorem ContContOK.switchCont {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop} {k : Cont}
    (h : ContContOK prog cfg ext Q P k) :
    ContContOK prog cfg ext Q P (.switchCont k) := h

theorem RetContOK.switchCont {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {rt : CTy}
    {P : Val → List BlockId → Mem → OSState → Prop} {k : Cont}
    (h : RetContOK prog cfg ext Q rt P k) :
    RetContOK prog cfg ext Q rt P (.switchCont k) := h

theorem BreakContOK.loop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop}
    {c? stp? : Option CExpr} {body : CStmt} {isDo : Bool} {k : Cont}
    (h : ∀ env' blks' m' os', P env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k)) :
    BreakContOK prog cfg ext Q P (.loop c? stp? body isDo k) :=
  fun env' blks' m' os' hp => ⟨env', blks', m', k, rfl, h env' blks' m' os' hp⟩

theorem ContContOK.loop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {P : Env → List BlockId → Mem → OSState → Prop}
    {c? stp? : Option CExpr} {body : CStmt} {isDo : Bool} {k : Cont}
    (h : ∀ env' blks' m' os', P env' blks' m' os' →
      WPTerm prog cfg ext Q (Sem.loopNext c? stp? body isDo env' blks' m' os' k)) :
    ContContOK prog cfg ext Q P (.loop c? stp? body isDo k) :=
  fun env' blks' m' os' hp => ⟨c?, stp?, body, isDo, env', blks', m', k, rfl, h env' blks' m' os' hp⟩

theorem RetContOK.loop {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {rt : CTy}
    {P : Val → List BlockId → Mem → OSState → Prop}
    {c? stp? : Option CExpr} {body : CStmt} {isDo : Bool} {k : Cont}
    (h : RetContOK prog cfg ext Q rt P k) :
    RetContOK prog cfg ext Q rt P (.loop c? stp? body isDo k) := h

theorem RetContOK.callFrame {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {re : Env} {rb : List BlockId} {rt : CTy}
    {fnBody : CStmt} {fs : List ExprFrame} {ctx : ExprCtx} {k : Cont}
    {PRet : Val → List BlockId → Mem → OSState → Prop}
    (h : ∀ cv blks' m' os', (rt.isVoid = true → cv = .void) → PRet cv blks' m' os' →
      let rtOut := if rt.isVoid then .void else rt
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval cv rtOut) fs) ctx []) re rb (m'.freeStack blks') os' k)) :
    RetContOK prog cfg ext Q rt PRet (.callFrame re rb rt fnBody fs ctx k) :=
  ⟨rfl, fun cv blks' m' os' hv hp =>
    ⟨rfl, re, rb, rt, m'.freeStack blks', fs, ctx, k, rfl, h cv blks' m' os' hv hp⟩⟩

/-! ### 4.2 Structural, Framing & Top-Level / CallFrame Eliminators -/

theorem StmtSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {s : CStmt}
    {P1 P2 : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpec prog cfg ext Q env blks m os s P1)
    (himp : ∀ e b m' o, P1 e b m' o → P2 e b m' o) :
    StmtSpec prog cfg ext Q env blks m os s P2 :=
  fun k hcont => h k (fun e b m' o hp => hcont e b m' o (himp e b m' o hp))

theorem StmtsSpec.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {ss : List CStmt}
    {P1 P2 : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtsSpec prog cfg ext Q env blks m os ss P1)
    (himp : ∀ e b m' o, P1 e b m' o → P2 e b m' o) :
    StmtsSpec prog cfg ext Q env blks m os ss P2 :=
  fun k hcont => h k (fun e b m' o hp => hcont e b m' o (himp e b m' o hp))

theorem StmtSpecEx.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {s : CStmt}
    {N1 N2 B1 B2 C1 C2 : Env → List BlockId → Mem → OSState → Prop}
    {R1 R2 : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt s N1 B1 C1 R1)
    (hn : ∀ e b m' o, N1 e b m' o → N2 e b m' o)
    (hb : ∀ e b m' o, B1 e b m' o → B2 e b m' o)
    (hc : ∀ e b m' o, C1 e b m' o → C2 e b m' o)
    (hr : ∀ v b m' o, R1 v b m' o → R2 v b m' o) :
    StmtSpecEx prog cfg ext Q env blks m os rt s N2 B2 C2 R2 :=
  fun k hk hbrk hcnt hret =>
    h k (fun e b m' o hp => hk e b m' o (hn e b m' o hp))
      (hbrk.mono hb) (hcnt.mono hc) (hret.mono hr)

theorem StmtsSpecEx.mono {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {ss : List CStmt}
    {N1 N2 B1 B2 C1 C2 : Env → List BlockId → Mem → OSState → Prop}
    {R1 R2 : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtsSpecEx prog cfg ext Q env blks m os rt ss N1 B1 C1 R1)
    (hn : ∀ e b m' o, N1 e b m' o → N2 e b m' o)
    (hb : ∀ e b m' o, B1 e b m' o → B2 e b m' o)
    (hc : ∀ e b m' o, C1 e b m' o → C2 e b m' o)
    (hr : ∀ v b m' o, R1 v b m' o → R2 v b m' o) :
    StmtsSpecEx prog cfg ext Q env blks m os rt ss N2 B2 C2 R2 :=
  fun k hk hbrk hcnt hret =>
    h k (fun e b m' o hp => hk e b m' o (hn e b m' o hp))
      (hbrk.mono hb) (hcnt.mono hc) (hret.mono hr)

theorem StmtSpecEx.to_stmtSpec {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {s : CStmt}
    {PostNorm : Env → List BlockId → Mem → OSState → Prop}
    (h : ∀ rt, StmtSpecEx prog cfg ext Q env blks m os rt s PostNorm
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False)) :
    StmtSpec prog cfg ext Q env blks m os s PostNorm :=
  fun k hk => h k.topRetTy k hk (BreakContOK.false k) (ContContOK.false k) RetContOK.false

theorem StmtSpec.to_ex {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} (rt : CTy) {s : CStmt}
    {PostNorm : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpec prog cfg ext Q env blks m os s PostNorm) :
    StmtSpecEx prog cfg ext Q env blks m os rt s PostNorm
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) :=
  fun k hk _ _ _ => h k hk

theorem StmtSpecEx.to_topLevel_noRet {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {s : CStmt} {rt : CTy}
    {PostNorm : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt s PostNorm
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False))
    (hnorm : ∀ env' blks' m' os', PostNorm env' blks' m' os' →
      Q (if rt.isVoid then .void else .undef) (m'.freeStack blks') os') :
    WPTerm prog cfg ext Q (.running (.stmt s) env blks m os (.stop rt)) :=
  h (.stop rt)
    (fun env' blks' m' os' hn => WPTerm.of_det rfl (WPTerm.returned (hnorm env' blks' m' os' hn)))
    (BreakContOK.false _) (ContContOK.false _) RetContOK.false

theorem StmtSpecEx.to_callFrame {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env re : Env} {blks rb : List BlockId}
    {m : Mem} {os : OSState} {s fnBody : CStmt} {rt : CTy}
    {fs : List ExprFrame} {ctx : ExprCtx} {k : Cont}
    {PostNorm : Env → List BlockId → Mem → OSState → Prop}
    {PostRet : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt s PostNorm
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) PostRet)
    (hnorm : ∀ env' blks' m' os', PostNorm env' blks' m' os' →
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval (if rt.isVoid then .void else .undef) rt) fs) ctx [])
          re rb (m'.freeStack blks') os' k))
    (hret : ∀ cv blks' m' os', (rt.isVoid = true → cv = .void) → PostRet cv blks' m' os' →
      let rtOut := if rt.isVoid then .void else rt
      WPTerm prog cfg ext Q
        (.running (.expr (.ret (.rval cv rtOut) fs) ctx []) re rb (m'.freeStack blks') os' k)) :
    WPTerm prog cfg ext Q (.running (.stmt s) env blks m os (.callFrame re rb rt fnBody fs ctx k)) :=
  h (.callFrame re rb rt fnBody fs ctx k)
    (fun env' blks' m' os' hn => WPTerm.of_det rfl (hnorm env' blks' m' os' hn))
    (BreakContOK.false _)
    (ContContOK.false _)
    (RetContOK.callFrame hret)

/-! ### 4.3 `nop`, `expr`, Sequential Composition (`stmts`), `block`, and Local `decls` -/

theorem StmtSpecEx.nop (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) :
    StmtSpecEx prog cfg ext Q env blks m os rt .nop
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os)
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) :=
  fun _ hk _ _ _ => hk env blks m os ⟨rfl, rfl, rfl, rfl⟩

theorem StmtSpec.nop (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) :
    StmtSpec prog cfg ext Q env blks m os .nop
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os) :=
  fun _ hk => hk env blks m os ⟨rfl, rfl, rfl, rfl⟩

theorem StmtSpecEx.expr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os [] e P) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.expr e)
      (fun e' b' m' os' => e' = env ∧ b' = blks ∧ ∃ v ty mods', P v ty m' os' mods')
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) := by
  intro k hk _ _ _
  refine WPTerm.of_det rfl ?_
  refine he [] .discard k ?_
  intro v ty m' os' mods' hp
  have hd : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval v ty) []) .discard mods') env blks m' os' k) =
      some (.next (.running (.stmt .nop) env blks m' os' k)) := by
    unfold Sem.stepDet; cases v <;> rfl
  exact WPTerm.of_det hd (hk env blks m' os' ⟨rfl, rfl, v, ty, mods', hp⟩)

theorem StmtSpec.expr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {e : CExpr}
    {P : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os [] e P) :
    StmtSpec prog cfg ext Q env blks m os (.expr e)
      (fun e' b' m' os' => e' = env ∧ b' = blks ∧ ∃ v ty mods', P v ty m' os' mods') :=
  StmtSpecEx.to_stmtSpec (fun _ => StmtSpecEx.expr he)

theorem StmtsSpecEx.nil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) :
    StmtsSpecEx prog cfg ext Q env blks m os rt []
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os)
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) :=
  fun _ hk _ _ _ => hk env blks m os ⟨rfl, rfl, rfl, rfl⟩

theorem StmtsSpecEx.singleton {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {s : CStmt}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hs : StmtSpecEx prog cfg ext Q env blks m os rt s PN PB PC PR) :
    StmtsSpecEx prog cfg ext Q env blks m os rt [s] PN PB PC PR := by
  intro k hk hbrk hcnt hret
  refine hs (.stmts [] k) ?_ hbrk.stmts hcnt.stmts hret.stmts
  intro e' b' m' o' hp
  exact WPTerm.of_det rfl (hk e' b' m' o' hp)

theorem StmtsSpecEx.cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {hd hd2 : CStmt} {tl : List CStmt}
    {P1 PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hs : StmtSpecEx prog cfg ext Q env blks m os rt hd P1 PB PC PR)
    (hrest : ∀ e' b' m' o', P1 e' b' m' o' →
      StmtsSpecEx prog cfg ext Q e' b' m' o' rt (hd2 :: tl) PN PB PC PR) :
    StmtsSpecEx prog cfg ext Q env blks m os rt (hd :: hd2 :: tl) PN PB PC PR := by
  intro k hk hbrk hcnt hret
  refine hs (.stmts (hd2 :: tl) k) ?_ hbrk.stmts hcnt.stmts hret.stmts
  intro e' b' m' o' hp1
  refine WPTerm.of_det rfl ?_
  exact (hrest e' b' m' o' hp1) k hk hbrk hcnt hret

theorem StmtsSpec.nil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) :
    StmtsSpec prog cfg ext Q env blks m os []
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os) :=
  fun _ hk => hk env blks m os ⟨rfl, rfl, rfl, rfl⟩

theorem StmtsSpec.singleton {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {s : CStmt}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hs : StmtSpec prog cfg ext Q env blks m os s PN) :
    StmtsSpec prog cfg ext Q env blks m os [s] PN := by
  intro k hk
  refine hs (.stmts [] k) ?_
  intro e' b' m' o' hp
  exact WPTerm.of_det rfl (hk e' b' m' o' hp)

theorem StmtsSpec.cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {hd hd2 : CStmt} {tl : List CStmt}
    {P1 PN : Env → List BlockId → Mem → OSState → Prop}
    (hs : StmtSpec prog cfg ext Q env blks m os hd P1)
    (hrest : ∀ e' b' m' o', P1 e' b' m' o' →
      StmtsSpec prog cfg ext Q e' b' m' o' (hd2 :: tl) PN) :
    StmtsSpec prog cfg ext Q env blks m os (hd :: hd2 :: tl) PN := by
  intro k hk
  refine hs (.stmts (hd2 :: tl) k) ?_
  intro e' b' m' o' hp1
  refine WPTerm.of_det rfl ?_
  exact (hrest e' b' m' o' hp1) k hk

theorem StmtSpecEx.block_nil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.block [])
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os)
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) :=
  fun _ hk _ _ _ => WPTerm.of_det rfl (hk env blks m os ⟨rfl, rfl, rfl, rfl⟩)

theorem StmtSpec.block_nil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) :
    StmtSpec prog cfg ext Q env blks m os (.block [])
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os) :=
  StmtSpecEx.to_stmtSpec (fun _ => StmtSpecEx.block_nil prog cfg ext Q env blks m os _)

theorem StmtSpecEx.block_cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {hd hd2 : CStmt} {tl : List CStmt}
    {PNi PBi PCi : Env → List BlockId → Mem → OSState → Prop}
    {PRi : Val → List BlockId → Mem → OSState → Prop}
    (hbody : StmtsSpecEx prog cfg ext Q env [] m os rt (hd :: hd2 :: tl) PNi PBi PCi PRi) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.block (hd :: hd2 :: tl))
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PNi e0 b0 m0 o)
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PBi e0 b0 m0 o)
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PCi e0 b0 m0 o)
      (fun v b m' o => b = blks ∧ ∃ b0 m0, m' = m0.freeStack b0 ∧ PRi v b0 m0 o) := by
  intro k hk hbrk hcnt hret
  refine WPTerm.of_det rfl ?_
  let kBlk := Cont.blockEnd env blks k
  exact hbody kBlk
    (fun e0 b0 m0 o0 hpn => WPTerm.of_det rfl (hk env blks (m0.freeStack b0) o0 ⟨rfl, rfl, e0, b0, m0, rfl, hpn⟩))
    (BreakContOK.blockEnd hbrk) (ContContOK.blockEnd hcnt) (RetContOK.blockEnd hret)

theorem StmtSpecEx.block_singleton {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {s : CStmt}
    {PNi PBi PCi : Env → List BlockId → Mem → OSState → Prop}
    {PRi : Val → List BlockId → Mem → OSState → Prop}
    (hs : StmtSpecEx prog cfg ext Q env [] m os rt s PNi PBi PCi PRi) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.block [s])
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PNi e0 b0 m0 o)
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PBi e0 b0 m0 o)
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PCi e0 b0 m0 o)
      (fun v b m' o => b = blks ∧ ∃ b0 m0, m' = m0.freeStack b0 ∧ PRi v b0 m0 o) := by
  intro k hk hbrk hcnt hret
  refine WPTerm.of_det rfl ?_
  exact hs (.blockEnd env blks k)
    (fun e0 b0 m0 o0 hpn => WPTerm.of_det rfl (hk env blks (m0.freeStack b0) o0 ⟨rfl, rfl, e0, b0, m0, rfl, hpn⟩))
    (BreakContOK.blockEnd hbrk) (ContContOK.blockEnd hcnt) (RetContOK.blockEnd hret)

theorem StmtSpec.block_cons {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {hd hd2 : CStmt} {tl : List CStmt}
    {PNi : Env → List BlockId → Mem → OSState → Prop}
    (hbody : StmtsSpec prog cfg ext Q env [] m os (hd :: hd2 :: tl) PNi) :
    StmtSpec prog cfg ext Q env blks m os (.block (hd :: hd2 :: tl))
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PNi e0 b0 m0 o) := by
  intro k hk
  refine WPTerm.of_det rfl ?_
  exact hbody (.blockEnd env blks k)
    (fun e0 b0 m0 o0 hpn => WPTerm.of_det rfl (hk env blks (m0.freeStack b0) o0 ⟨rfl, rfl, e0, b0, m0, rfl, hpn⟩))

theorem StmtSpec.block_singleton {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {s : CStmt}
    {PNi : Env → List BlockId → Mem → OSState → Prop}
    (hs : StmtSpec prog cfg ext Q env [] m os s PNi) :
    StmtSpec prog cfg ext Q env blks m os (.block [s])
      (fun e b m' o => e = env ∧ b = blks ∧ ∃ e0 b0 m0, m' = m0.freeStack b0 ∧ PNi e0 b0 m0 o) := by
  intro k hk
  refine WPTerm.of_det rfl ?_
  exact hs (.blockEnd env blks k)
    (fun e0 b0 m0 o0 hpn => WPTerm.of_det rfl (hk env blks (m0.freeStack b0) o0 ⟨rfl, rfl, e0, b0, m0, rfl, hpn⟩))

theorem StmtSpecEx.decls_nil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.decls [])
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os)
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) :=
  fun _ hk _ _ _ => WPTerm.of_det rfl (hk env blks m os ⟨rfl, rfl, rfl, rfl⟩)

theorem StmtSpec.decls_nil (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) :
    StmtSpec prog cfg ext Q env blks m os (.decls [])
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os) :=
  StmtSpecEx.to_stmtSpec (fun _ => StmtSpecEx.decls_nil prog cfg ext Q env blks m os _)

theorem StmtSpecEx.decls_static {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {d : VarDecl} {rest : List VarDecl}
    (hst : d.isStatic = true)
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hrest : StmtSpecEx prog cfg ext Q env blks m os rt (.decls rest) PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.decls (d :: rest)) PN PB PC PR := by
  intro k hk hbrk hcnt hret
  have hd : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env blks m os k) =
      some (.next (.running (.stmt (.decls rest)) env blks m os k)) := by
    unfold Sem.stepDet
    simp only [hst, ↓reduceIte]
  exact WPTerm.of_det hd (hrest k hk hbrk hcnt hret)

theorem StmtSpecEx.decls_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {d : VarDecl} {rest : List VarDecl}
    (hst : d.isStatic = false) (hinit : d.init? = none)
    (hsz : max 1 (C99.sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (C99.alignofTy prog.tags d.ty))
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hrest : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (C99.alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (C99.sizeofTy prog.tags d.ty)) (max 1 (C99.alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      StmtSpecEx prog cfg ext Q ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os rt (.decls rest)
        PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.decls (d :: rest)) PN PB PC PR := by
  intro k hk hbrk hcnt hret
  have hd : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env blks m os k) =
      some (.allocLocal d none rest env blks m os k) := by
    unfold Sem.stepDet
    simp only [hst, Bool.false_eq_true, ↓reduceIte, hinit]
  refine WPTerm.of_localDecl_none hd hsz hal ?_
  intro base bid m1 hba halloc
  exact hrest base bid m1 hba halloc k hk hbrk hcnt hret

theorem StmtSpecEx.decls_some {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {d : VarDecl} {e : CExpr} {rest : List VarDecl}
    (hst : d.isStatic = false) (hinit : d.init? = some (.expr e))
    (hsz : max 1 (C99.sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (C99.alignofTy prog.tags d.ty))
    {Pe : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os [] e Pe)
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hrest : ∀ v ty m' os' mods', Pe v ty m' os' mods' →
      ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
        (hba : base.toNat % max 1 (C99.alignofTy prog.tags d.ty) = 0),
        m'.alloc (max 1 (C99.sizeofTy prog.tags d.ty)) (max 1 (C99.alignofTy prog.tags d.ty))
          .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
        ∃ r m2, Sem.writePlace prog.tags m1 bid 0 d.ty.stripConst (.rval v ty) = some (r, m2) ∧
          StmtSpecEx prog cfg ext Q ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os' rt (.decls rest)
            PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.decls (d :: rest)) PN PB PC PR := by
  intro k hk hbrk hcnt hret
  have hd : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env blks m os k) =
      some (.next (.running (.expr (.eval .rval e []) (.varInit d rest) []) env blks m os k)) := by
    unfold Sem.stepDet
    simp only [hst, Bool.false_eq_true, ↓reduceIte, hinit]
  refine WPTerm.of_det hd ?_
  refine he [] (.varInit d rest) k ?_
  intro v ty m' os' mods' hpe
  have hd2 : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval v ty) []) (.varInit d rest) mods') env blks m' os' k) =
      some (.allocLocal d (some (.rval v ty)) rest env blks m' os' k) := by
    unfold Sem.stepDet; cases v <;> rfl
  refine WPTerm.of_localDecl_some hd2 hsz hal ?_
  intro base bid m1 hba halloc
  obtain ⟨r, m2, hwr, hs⟩ := hrest v ty m' os' mods' hpe base bid m1 hba halloc
  exact ⟨r, m2, hwr, hs k hk hbrk hcnt hret⟩

theorem StmtSpecEx.decl {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {d : VarDecl}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt (.decls [d]) PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.decl d) PN PB PC PR :=
  fun k hk hbrk hcnt hret => WPTerm.of_det rfl (h k hk hbrk hcnt hret)

/-! ### 4.4 Branch (`ifStmt`, `ifElseStmt`, `switchStmt`), Loops (`while`, `doWhile`, `for`), Jumps -/

theorem StmtSpecEx.ifElseStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {c : CExpr} {t f : CStmt}
    {Pc : Val → CTy → Mem → OSState → ModSet → Prop}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hc : ExprSpec prog cfg ext Q env blks m os [] c Pc)
    (htruthy : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc)
    (ht : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
      StmtSpecEx prog cfg ext Q env blks mc osc rt t PN PB PC PR)
    (hf : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
      StmtSpecEx prog cfg ext Q env blks mc osc rt f PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.ifStmt c t (some f)) PN PB PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.of_det rfl ?_
  refine hc [] (.branch t f) k ?_
  intro vc tc mc osc modsc hpc
  obtain ⟨bc, hbc⟩ := htruthy vc tc mc osc modsc hpc
  have hd : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval vc tc) []) (.branch t f) modsc) env blks mc osc k) =
      some (.next (.running (.stmt (if bc then t else f)) env blks mc osc k)) := by
    unfold Sem.stepDet
    cases vc <;> simp only [Option.bind, hbc, Option.map_some]
  refine WPTerm.of_det hd ?_
  cases bc with
  | true => exact (ht vc tc mc osc modsc hpc hbc) k hk hbrk hcnt hret
  | false => exact (hf vc tc mc osc modsc hpc hbc) k hk hbrk hcnt hret

theorem StmtSpecEx.ifStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {c : CExpr} {t : CStmt}
    {Pc : Val → CTy → Mem → OSState → ModSet → Prop}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hc : ExprSpec prog cfg ext Q env blks m os [] c Pc)
    (htruthy : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc)
    (ht : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
      StmtSpecEx prog cfg ext Q env blks mc osc rt t PN PB PC PR)
    (hf : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
      PN env blks mc osc) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.ifStmt c t none) PN PB PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.of_det rfl ?_
  refine hc [] (.branch t .nop) k ?_
  intro vc tc mc osc modsc hpc
  obtain ⟨bc, hbc⟩ := htruthy vc tc mc osc modsc hpc
  have hd : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval vc tc) []) (.branch t .nop) modsc) env blks mc osc k) =
      some (.next (.running (.stmt (if bc then t else .nop)) env blks mc osc k)) := by
    unfold Sem.stepDet
    cases vc <;> simp only [Option.bind, hbc, Option.map_some]
  refine WPTerm.of_det hd ?_
  cases bc with
  | true => exact (ht vc tc mc osc modsc hpc hbc) k hk hbrk hcnt hret
  | false => exact hk env blks mc osc (hf vc tc mc osc modsc hpc hbc)

theorem StmtSpec.ifElseStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {c : CExpr} {t f : CStmt}
    {Pc : Val → CTy → Mem → OSState → ModSet → Prop}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hc : ExprSpec prog cfg ext Q env blks m os [] c Pc)
    (htruthy : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc)
    (ht : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
      StmtSpec prog cfg ext Q env blks mc osc t PN)
    (hf : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
      StmtSpec prog cfg ext Q env blks mc osc f PN) :
    StmtSpec prog cfg ext Q env blks m os (.ifStmt c t (some f)) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.ifElseStmt hc htruthy (fun vc tc mc osc modsc hp ht1 => (ht vc tc mc osc modsc hp ht1).to_ex rt)
      (fun vc tc mc osc modsc hp hf1 => (hf vc tc mc osc modsc hp hf1).to_ex rt))

theorem StmtSpec.ifStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {c : CExpr} {t : CStmt}
    {Pc : Val → CTy → Mem → OSState → ModSet → Prop}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hc : ExprSpec prog cfg ext Q env blks m os [] c Pc)
    (htruthy : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc)
    (ht : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
      StmtSpec prog cfg ext Q env blks mc osc t PN)
    (hf : ∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
      PN env blks mc osc) :
    StmtSpec prog cfg ext Q env blks m os (.ifStmt c t none) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.ifStmt hc htruthy (fun vc tc mc osc modsc hp ht1 => (ht vc tc mc osc modsc hp ht1).to_ex rt) hf)

theorem StmtSpecEx.caseStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {v : Int} {body : CStmt}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt body PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.caseStmt v body) PN PB PC PR :=
  fun k hk hbrk hcnt hret => WPTerm.of_det rfl (h k hk hbrk hcnt hret)

theorem StmtSpecEx.defaultStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {body : CStmt}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt body PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.defaultStmt body) PN PB PC PR :=
  fun k hk hbrk hcnt hret => WPTerm.of_det rfl (h k hk hbrk hcnt hret)

theorem StmtSpecEx.labelStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {lbl : String} {body : CStmt}
    {PN PB PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (h : StmtSpecEx prog cfg ext Q env blks m os rt body PN PB PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.labelStmt lbl body) PN PB PC PR :=
  fun k hk hbrk hcnt hret => WPTerm.of_det rfl (h k hk hbrk hcnt hret)

theorem StmtSpecEx.switchStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {scrut : CExpr} {body : CStmt}
    {Pscr : Val → CTy → Mem → OSState → ModSet → Prop}
    {PN PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hs : ExprSpec prog cfg ext Q env blks m os [] scrut Pscr)
    (hint : ∀ sv st ms oss modss, Pscr sv st ms oss modss →
      ∃ ik iv, valAsInt? sv = some (ik, iv))
    (hnone : ∀ sv st ms oss modss ik iv, Pscr sv st ms oss modss →
      valAsInt? sv = some (ik, iv) → Sem.findSwitchTarget iv body = none → PN env blks ms oss)
    (hsome : ∀ sv st ms oss modss ik iv tgt, Pscr sv st ms oss modss →
      valAsInt? sv = some (ik, iv) → Sem.findSwitchTarget iv body = some tgt →
      StmtSpecEx prog cfg ext Q env blks ms oss rt tgt PN PN PC PR) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.switchStmt scrut body) PN
      (fun _ _ _ _ => False) PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.of_det rfl ?_
  refine hs [] (.switchScrut body) k ?_
  intro sv st ms oss modss hps
  obtain ⟨ik, iv, hvi⟩ := hint sv st ms oss modss hps
  cases hft : Sem.findSwitchTarget iv body with
  | none =>
    have hd : Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval sv st) []) (.switchScrut body) modss) env blks ms oss k) =
        some (.next (.running (.stmt .nop) env blks ms oss k)) := by
      unfold Sem.stepDet
      cases sv <;> simp only [Option.bind, hvi, hft, Option.map_some]
    exact WPTerm.of_det hd (hk env blks ms oss (hnone sv st ms oss modss ik iv hps hvi hft))
  | some tgt =>
    have hd : Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval sv st) []) (.switchScrut body) modss) env blks ms oss k) =
        some (.next (.running (.stmt tgt) env blks ms oss (.switchCont k))) := by
      unfold Sem.stepDet
      cases sv <;> simp only [Option.bind, hvi, hft, Option.map_some]
    refine WPTerm.of_det hd ?_
    exact (hsome sv st ms oss modss ik iv tgt hps hvi hft) (.switchCont k)
      (fun e' b' m' o' hn => WPTerm.of_det rfl (hk e' b' m' o' hn))
      (BreakContOK.switchCont hk) hcnt.switchCont hret.switchCont

theorem StmtSpecEx.whileStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {rt : CTy} {c : CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
        ExprSpec prog cfg ext Q env blks m os [] c Pc ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
          PN env blks mc osc) ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
          ∃ PNb PCb,
            StmtSpecEx prog cfg ext Q env blks mc osc rt body PNb PN PCb PR ∧
            (∀ e' b' m' o', PNb e' b' m' o' → ∃ n', n' < n ∧ Inv n' e' b' m' o') ∧
            (∀ e' b' m' o', PCb e' b' m' o' → ∃ n', n' < n ∧ Inv n' e' b' m' o'))) :
    StmtSpecEx prog cfg ext Q env0 blks0 m0 os0 rt (.whileStmt c body) PN
      (fun _ _ _ _ => False) PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.while_wf Inv hinit ?_
  intro n env blks m os hinv ih
  obtain ⟨Pc, hc, htruthy, hfalse, htrue⟩ := hstep n env blks m os hinv
  refine hc [] (.forCond c none body) k ?_
  intro vc tc mc osc modsc hpc
  obtain ⟨bc, hbc⟩ := htruthy vc tc mc osc modsc hpc
  cases bc with
  | false =>
    have hd : Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval vc tc) []) (.forCond c none body) modsc) env blks mc osc k) =
        some (.next (.running (.stmt .nop) env blks mc osc k)) := by
      unfold Sem.stepDet
      cases vc <;> simp only [Option.bind, hbc, Option.map_some, Bool.false_eq_true, ↓reduceIte]
    exact WPTerm.of_det hd (hk env blks mc osc (hfalse vc tc mc osc modsc hpc hbc))
  | true =>
    have hd : Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval vc tc) []) (.forCond c none body) modsc) env blks mc osc k) =
        some (.next (.running (.stmt body) env blks mc osc (.loop (some c) none body false k))) := by
      unfold Sem.stepDet
      cases vc <;> simp only [Option.bind, hbc, Option.map_some, ↓reduceIte]
    refine WPTerm.of_det hd ?_
    obtain ⟨PNb, PCb, hbody, hnb_dec, hcb_dec⟩ := htrue vc tc mc osc modsc hpc hbc
    refine hbody (.loop (some c) none body false k) ?_ (BreakContOK.loop hk) (ContContOK.loop ?_) hret.loop
    · intro e' b' m' o' hpn
      obtain ⟨n', hlt, hinv'⟩ := hnb_dec e' b' m' o' hpn
      exact WPTerm.of_det rfl (ih n' e' b' m' o' hlt hinv')
    · intro e' b' m' o' hpc_b
      obtain ⟨n', hlt, hinv'⟩ := hcb_dec e' b' m' o' hpc_b
      exact ih n' e' b' m' o' hlt hinv'

theorem StmtSpecEx.doWhileStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {rt : CTy} {body : CStmt} {c : CExpr} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      ∃ PNb PCb,
        StmtSpecEx prog cfg ext Q env blks m os rt body PNb PN PCb PR ∧
        (∀ e1 b1 m1 o1, (PNb e1 b1 m1 o1 ∨ PCb e1 b1 m1 o1) →
          ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
            ExprSpec prog cfg ext Q e1 b1 m1 o1 [] c Pc ∧
            (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
            (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
              PN e1 b1 mc osc) ∧
            (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
              ∃ n', n' < n ∧ Inv n' e1 b1 mc osc))) :
    StmtSpecEx prog cfg ext Q env0 blks0 m0 os0 rt (.doWhileStmt body c) PN
      (fun _ _ _ _ => False) PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.doWhile_wf Inv hinit ?_
  intro n env blks m os hinv ih
  obtain ⟨PNb, PCb, hbody, hcond⟩ := hstep n env blks m os hinv
  have hcond_wp : ∀ e1 b1 m1 o1, (PNb e1 b1 m1 o1 ∨ PCb e1 b1 m1 o1) →
      WPTerm prog cfg ext Q (.running (.expr (.eval .rval c []) (.doWhileCond body c) []) e1 b1 m1 o1 k) := by
    intro e1 b1 m1 o1 hpre
    obtain ⟨Pc, hc, htruthy, hfalse, htrue⟩ := hcond e1 b1 m1 o1 hpre
    refine hc [] (.doWhileCond body c) k ?_
    intro vc tc mc osc modsc hpc
    obtain ⟨bc, hbc⟩ := htruthy vc tc mc osc modsc hpc
    cases bc with
    | false =>
      have hd : Sem.stepDet prog cfg
          (.running (.expr (.ret (.rval vc tc) []) (.doWhileCond body c) modsc) e1 b1 mc osc k) =
          some (.next (.running (.stmt .nop) e1 b1 mc osc k)) := by
        unfold Sem.stepDet
        cases vc <;> simp only [Option.bind, hbc, Option.map_some, Bool.false_eq_true, ↓reduceIte]
      exact WPTerm.of_det hd (hk e1 b1 mc osc (hfalse vc tc mc osc modsc hpc hbc))
    | true =>
      have hd : Sem.stepDet prog cfg
          (.running (.expr (.ret (.rval vc tc) []) (.doWhileCond body c) modsc) e1 b1 mc osc k) =
          some (.next (.running (.stmt body) e1 b1 mc osc (.loop (some c) none body true k))) := by
        unfold Sem.stepDet
        cases vc <;> simp only [Option.bind, hbc, Option.map_some, ↓reduceIte]
      obtain ⟨n', hlt, hinv'⟩ := htrue vc tc mc osc modsc hpc hbc
      exact WPTerm.of_det hd (ih n' e1 b1 mc osc hlt hinv')
  refine hbody (.loop (some c) none body true k) ?_ (BreakContOK.loop hk) (ContContOK.loop ?_) hret.loop
  · intro e1 b1 m1 o1 hpn
    exact WPTerm.of_det rfl (hcond_wp e1 b1 m1 o1 (Or.inl hpn))
  · intro e1 b1 m1 o1 hpc_b
    exact hcond_wp e1 b1 m1 o1 (Or.inr hpc_b)

/-- Loop post-body step condition for `for (init?; c?; stp?) body`. -/
def ForStepNext (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    (n : Nat) (stp? : Option CExpr) (e1 : Env) (b1 : List BlockId) (m1 : Mem) (o1 : OSState) : Prop :=
  match stp? with
  | none => ∃ n', n' < n ∧ Inv n' e1 b1 m1 o1
  | some stp =>
    ∃ Ps : Val → CTy → Mem → OSState → ModSet → Prop,
      ExprSpec prog cfg ext Q e1 b1 m1 o1 [] stp Ps ∧
      (∀ vs ts ms oss modss, Ps vs ts ms oss modss → ∃ n', n' < n ∧ Inv n' e1 b1 ms oss)

/-- Loop-step hypothesis for `for (init?; c?; stp?) body`. -/
def ForStepHyp (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    (rt : CTy) (c? stp? : Option CExpr) (body : CStmt)
    (PN : Env → List BlockId → Mem → OSState → Prop)
    (PR : Val → List BlockId → Mem → OSState → Prop) : Prop :=
  ∀ n env blks m os, Inv n env blks m os →
    match c? with
    | none =>
      ∃ PNb PCb,
        StmtSpecEx prog cfg ext Q env blks m os rt body PNb PN PCb PR ∧
        (∀ e1 b1 m1 o1, (PNb e1 b1 m1 o1 ∨ PCb e1 b1 m1 o1) →
          ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1)
    | some c =>
      ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
        ExprSpec prog cfg ext Q env blks m os [] c Pc ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
          PN env blks mc osc) ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
          ∃ PNb PCb,
            StmtSpecEx prog cfg ext Q env blks mc osc rt body PNb PN PCb PR ∧
            (∀ e1 b1 m1 o1, (PNb e1 b1 m1 o1 ∨ PCb e1 b1 m1 o1) →
              ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1))

private theorem forAfterBody {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {Inv : Nat → Env → List BlockId → Mem → OSState → Prop}
    {c? stp? : Option CExpr} {body : CStmt} {k : Cont} {n : Nat}
    (ih : ∀ n' env' blks' m' os', n' < n → Inv n' env' blks' m' os' →
      WPTerm prog cfg ext Q (forLoopEntry c? stp? body env' blks' m' os' k))
    (PNb PCb : Env → List BlockId → Mem → OSState → Prop)
    (hm : ∀ e1 b1 m1 o1, (PNb e1 b1 m1 o1 ∨ PCb e1 b1 m1 o1) →
      ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1)
    (e1 : Env) (b1 : List BlockId) (m1 : Mem) (o1 : OSState)
    (hpre : PNb e1 b1 m1 o1 ∨ PCb e1 b1 m1 o1) :
    WPTerm prog cfg ext Q (Sem.loopNext c? stp? body false e1 b1 m1 o1 k) := by
  cases stp? with
  | none =>
    obtain ⟨n', hlt, hinv'⟩ := hm e1 b1 m1 o1 hpre
    cases c? <;> exact ih n' e1 b1 m1 o1 hlt hinv'
  | some stp =>
    obtain ⟨Ps, hstp, hnext⟩ := hm e1 b1 m1 o1 hpre
    refine hstp [] (.forStep c? (some stp) body) k ?_
    intro vs ts ms oss modss hps
    obtain ⟨n', hlt, hinv'⟩ := hnext vs ts ms oss modss hps
    have hd : Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval vs ts) []) (.forStep c? (some stp) body) modss) e1 b1 ms oss k) =
        some (.next (forLoopEntry c? (some stp) body e1 b1 ms oss k)) := by
      unfold Sem.stepDet forLoopEntry
      cases c? <;> cases vs <;> rfl
    exact WPTerm.of_det hd (ih n' e1 b1 ms oss hlt hinv')

private theorem forLoopEntry_of_step {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {Inv : Nat → Env → List BlockId → Mem → OSState → Prop}
    {rt : CTy} {c? stp? : Option CExpr} {body : CStmt}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    {k : Cont}
    (hk : ∀ env' blks' m' os', PN env' blks' m' os' →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env' blks' m' os' k))
    (hret : RetContOK prog cfg ext Q rt PR k)
    (hstep : ForStepHyp prog cfg ext Q Inv rt c? stp? body PN PR)
    {n : Nat} {env : Env} {blks : List BlockId} {m : Mem} {os : OSState}
    (hinv : Inv n env blks m os)
    (ih : ∀ n' env' blks' m' os', n' < n → Inv n' env' blks' m' os' →
      WPTerm prog cfg ext Q (forLoopEntry c? stp? body env' blks' m' os' k)) :
    WPTerm prog cfg ext Q (forLoopEntry c? stp? body env blks m os k) := by
  cases c? with
  | none =>
    obtain ⟨PNb, PCb, hbody, hm⟩ := hstep n env blks m os hinv
    refine hbody (.loop none stp? body false k) ?_ (BreakContOK.loop hk) (ContContOK.loop ?_) hret.loop
    · intro e1 b1 m1 o1 hpn
      exact WPTerm.of_det rfl (forAfterBody ih PNb PCb hm e1 b1 m1 o1 (Or.inl hpn))
    · intro e1 b1 m1 o1 hpc_b
      exact forAfterBody ih PNb PCb hm e1 b1 m1 o1 (Or.inr hpc_b)
  | some c =>
    obtain ⟨Pc, hc, htruthy, hfalse, htrue⟩ := hstep n env blks m os hinv
    refine hc [] (.forCond c stp? body) k ?_
    intro vc tc mc osc modsc hpc
    obtain ⟨bc, hbc⟩ := htruthy vc tc mc osc modsc hpc
    cases bc with
    | false =>
      have hd : Sem.stepDet prog cfg
          (.running (.expr (.ret (.rval vc tc) []) (.forCond c stp? body) modsc) env blks mc osc k) =
          some (.next (.running (.stmt .nop) env blks mc osc k)) := by
        unfold Sem.stepDet
        cases vc <;> simp only [Option.bind, hbc, Option.map_some, Bool.false_eq_true, ↓reduceIte]
      exact WPTerm.of_det hd (hk env blks mc osc (hfalse vc tc mc osc modsc hpc hbc))
    | true =>
      have hd : Sem.stepDet prog cfg
          (.running (.expr (.ret (.rval vc tc) []) (.forCond c stp? body) modsc) env blks mc osc k) =
          some (.next (.running (.stmt body) env blks mc osc (.loop (some c) stp? body false k))) := by
        unfold Sem.stepDet
        cases vc <;> simp only [Option.bind, hbc, Option.map_some, ↓reduceIte]
      refine WPTerm.of_det hd ?_
      obtain ⟨PNb, PCb, hbody, hm⟩ := htrue vc tc mc osc modsc hpc hbc
      refine hbody (.loop (some c) stp? body false k) ?_ (BreakContOK.loop hk) (ContContOK.loop ?_) hret.loop
      · intro e1 b1 m1 o1 hpn
        exact WPTerm.of_det rfl (forAfterBody ih PNb PCb hm e1 b1 m1 o1 (Or.inl hpn))
      · intro e1 b1 m1 o1 hpc_b
        exact forAfterBody ih PNb PCb hm e1 b1 m1 o1 (Or.inr hpc_b)

theorem StmtSpecEx.forNoneStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {rt : CTy} {c? stp? : Option CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ForStepHyp prog cfg ext Q Inv rt c? stp? body PN PR) :
    StmtSpecEx prog cfg ext Q env0 blks0 m0 os0 rt (.forStmt none c? stp? body) PN
      (fun _ _ _ _ => False) PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.for_none_wf Inv hinit ?_
  intro n env blks m os hinv ih
  exact forLoopEntry_of_step hk hret hstep hinv ih

theorem StmtSpecEx.forStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {rt : CTy} {init : CExpr} {c? stp? : Option CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN PC : Env → List BlockId → Mem → OSState → Prop}
    {PR : Val → List BlockId → Mem → OSState → Prop}
    {Pi : Val → CTy → Mem → OSState → ModSet → Prop}
    (hinit_expr : ExprSpec prog cfg ext Q env0 blks0 m0 os0 [] init Pi)
    (hinv0 : ∀ vi ti m1 os1 modsi, Pi vi ti m1 os1 modsi → Inv n0 env0 blks0 m1 os1)
    (hstep : ForStepHyp prog cfg ext Q Inv rt c? stp? body PN PR) :
    StmtSpecEx prog cfg ext Q env0 blks0 m0 os0 rt (.forStmt (some init) c? stp? body) PN
      (fun _ _ _ _ => False) PC PR := by
  intro k hk hbrk hcnt hret
  refine WPTerm.for_wf Inv (n0 := n0) ?_ ?_
  · intro hentry
    refine hinit_expr [] (.forStep c? stp? body) k ?_
    intro vi ti m1 os1 modsi hpi
    have hd : Sem.stepDet prog cfg
        (.running (.expr (.ret (.rval vi ti) []) (.forStep c? stp? body) modsi) env0 blks0 m1 os1 k) =
        some (.next (forLoopEntry c? stp? body env0 blks0 m1 os1 k)) := by
      unfold Sem.stepDet forLoopEntry
      cases c? <;> cases vi <;> rfl
    exact WPTerm.of_det hd (hentry env0 blks0 m1 os1 (hinv0 vi ti m1 os1 modsi hpi))
  · intro n env blks m os hinv ih
    exact forLoopEntry_of_step hk hret hstep hinv ih

theorem StmtSpecEx.breakStmt (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) :
    StmtSpecEx prog cfg ext Q env blks m os rt .breakStmt
      (fun _ _ _ _ => False)
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os)
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) := by
  intro k _ hbrk _ _
  obtain ⟨e2, b2, m2, k2, hu, hw⟩ := hbrk env blks m os ⟨rfl, rfl, rfl, rfl⟩
  have hd : Sem.stepDet prog cfg (.running (.stmt .breakStmt) env blks m os k) =
      some (.next (.running (.stmt .nop) e2 b2 m2 os k2)) := by
    unfold Sem.stepDet
    simp only [hu, Option.map_some]
  exact WPTerm.of_det hd hw

theorem StmtSpecEx.continueStmt (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler)
    (Q : Val → Mem → OSState → Prop) (env : Env) (blks : List BlockId)
    (m : Mem) (os : OSState) (rt : CTy) :
    StmtSpecEx prog cfg ext Q env blks m os rt .continueStmt
      (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun e b m' o => e = env ∧ b = blks ∧ m' = m ∧ o = os)
      (fun _ _ _ _ => False) := by
  intro k _ _ hcnt _
  obtain ⟨c?, stp?, body, isDo, e2, b2, m2, k2, hu, hw⟩ := hcnt env blks m os ⟨rfl, rfl, rfl, rfl⟩
  have hd : Sem.stepDet prog cfg (.running (.stmt .continueStmt) env blks m os k) =
      some (.next (Sem.loopNext c? stp? body isDo e2 b2 m2 os k2)) := by
    unfold Sem.stepDet
    simp only [hu, Option.map_some]
  exact WPTerm.of_det hd hw

theorem StmtSpecEx.returnStmt_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} (hvoid : rt.isVoid = true) :
    StmtSpecEx prog cfg ext Q env blks m os rt (.returnStmt none)
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun cv blks' m' os' => cv = .void ∧ blks' = blks ∧ m' = m ∧ os' = os) := by
  intro k _ _ _ ⟨hkrt, hret⟩
  obtain ⟨_, re, rb, rt', m2, fs, rctx, rk, hu, hw⟩ :=
    hret .void blks m os (fun _ => rfl) ⟨rfl, rfl, rfl, rfl⟩
  have hkv : k.topRetTy.isVoid = true := by rw [hkrt]; exact hvoid
  have hd : Sem.stepDet prog cfg (.running (.stmt (.returnStmt none)) env blks m os k) =
      some (.next (.running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m2 os rk)) := by
    unfold Sem.stepDet
    simp only [hkv, ↓reduceIte, hu]
  have hrtOut : (if rt.isVoid = true then CTy.void else rt) = .void := by
    simp only [hvoid, ↓reduceIte]
  rw [hrtOut] at hw
  exact WPTerm.of_det hd hw

theorem StmtSpecEx.returnStmt_some {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {e : CExpr} (hnv : rt.isVoid = false)
    {Pe : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os [] e Pe)
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hcast : ∀ v ty m' os' mods', Pe v ty m' os' mods' →
      ∃ cv, Sem.castVal m' rt v = some cv ∧ PR cv blks m' os') :
    StmtSpecEx prog cfg ext Q env blks m os rt (.returnStmt (some e))
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) PR := by
  intro k _ _ _ ⟨hkrt, hret⟩
  refine WPTerm.of_det rfl ?_
  refine he [] .returnVal k ?_
  intro v ty m' os' mods' hpe
  obtain ⟨cv, hcv, hpr⟩ := hcast v ty m' os' mods' hpe
  obtain ⟨_, re, rb, rt', m2, fs, rctx, rk, hu, hw⟩ :=
    hret cv blks m' os' (fun hv => by rw [hnv] at hv; cases hv) hpr
  have hd : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval v ty) []) .returnVal mods') env blks m' os' k) =
      some (.next (.running (.expr (.ret (.rval cv rt) fs) rctx []) re rb m2 os' rk)) := by
    unfold Sem.stepDet
    cases v <;> simp only [Option.bind_some, hkrt, hnv, Bool.false_eq_true, ↓reduceIte, hcv,
      Option.map_some, hu]
  have hrtOut : (if rt.isVoid = true then CTy.void else rt) = rt := by
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
  rw [hrtOut] at hw
  exact WPTerm.of_det hd hw

theorem StmtSpecEx.returnStmt_some_void {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {rt : CTy} {e : CExpr} (hvoid : rt.isVoid = true)
    {Pe : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os [] e Pe)
    {PR : Val → List BlockId → Mem → OSState → Prop}
    (hpost : ∀ v ty m' os' mods', Pe v ty m' os' mods' → PR .void blks m' os') :
    StmtSpecEx prog cfg ext Q env blks m os rt (.returnStmt (some e))
      (fun _ _ _ _ => False) (fun _ _ _ _ => False) (fun _ _ _ _ => False) PR := by
  intro k _ _ _ ⟨hkrt, hret⟩
  refine WPTerm.of_det rfl ?_
  refine he [] .returnVal k ?_
  intro v ty m' os' mods' hpe
  obtain ⟨_, re, rb, rt', m2, fs, rctx, rk, hu, hw⟩ :=
    hret .void blks m' os' (fun _ => rfl) (hpost v ty m' os' mods' hpe)
  have hd : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval v ty) []) .returnVal mods') env blks m' os' k) =
      some (.next (.running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m2 os' rk)) := by
    unfold Sem.stepDet
    cases v <;> simp only [Option.bind_some, hkrt, hvoid, ↓reduceIte, hu]
  have hrtOut : (if rt.isVoid = true then CTy.void else rt) = .void := by
    simp only [hvoid, ↓reduceIte]
  rw [hrtOut] at hw
  exact WPTerm.of_det hd hw

theorem StmtSpec.decls_static {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {d : VarDecl} {rest : List VarDecl}
    (hst : d.isStatic = true) {PN : Env → List BlockId → Mem → OSState → Prop}
    (hrest : StmtSpec prog cfg ext Q env blks m os (.decls rest) PN) :
    StmtSpec prog cfg ext Q env blks m os (.decls (d :: rest)) PN :=
  StmtSpecEx.to_stmtSpec (fun rt => StmtSpecEx.decls_static hst (hrest.to_ex rt))

theorem StmtSpec.decls_none {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {d : VarDecl} {rest : List VarDecl}
    (hst : d.isStatic = false) (hinit : d.init? = none)
    (hsz : max 1 (C99.sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (C99.alignofTy prog.tags d.ty))
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hrest : ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
      (hba : base.toNat % max 1 (C99.alignofTy prog.tags d.ty) = 0),
      m.alloc (max 1 (C99.sizeofTy prog.tags d.ty)) (max 1 (C99.alignofTy prog.tags d.ty))
        .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
      StmtSpec prog cfg ext Q ((d.name, bid, d.ty) :: env) (bid :: blks) m1 os (.decls rest) PN) :
    StmtSpec prog cfg ext Q env blks m os (.decls (d :: rest)) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.decls_none hst hinit hsz hal (fun base bid m1 hba ha => (hrest base bid m1 hba ha).to_ex rt))

theorem StmtSpec.decls_some {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {d : VarDecl} {e : CExpr} {rest : List VarDecl}
    (hst : d.isStatic = false) (hinit : d.init? = some (.expr e))
    (hsz : max 1 (C99.sizeofTy prog.tags d.ty) < ptrDiffLimit)
    (hal : 0 < max 1 (C99.alignofTy prog.tags d.ty))
    {Pe : Val → CTy → Mem → OSState → ModSet → Prop}
    (he : ExprSpec prog cfg ext Q env blks m os [] e Pe)
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hrest : ∀ v ty m' os' mods', Pe v ty m' os' mods' →
      ∀ (base : UInt64) (bid : BlockId) (m1 : Mem)
        (hba : base.toNat % max 1 (C99.alignofTy prog.tags d.ty) = 0),
        m'.alloc (max 1 (C99.sizeofTy prog.tags d.ty)) (max 1 (C99.alignofTy prog.tags d.ty))
          .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1) →
        ∃ r m2, Sem.writePlace prog.tags m1 bid 0 d.ty.stripConst (.rval v ty) = some (r, m2) ∧
          StmtSpec prog cfg ext Q ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os' (.decls rest) PN) :
    StmtSpec prog cfg ext Q env blks m os (.decls (d :: rest)) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.decls_some hst hinit hsz hal he fun v ty m' os' mods' hp base bid m1 hba ha =>
      let ⟨r, m2, hwr, hs⟩ := hrest v ty m' os' mods' hp base bid m1 hba ha
      ⟨r, m2, hwr, hs.to_ex rt⟩)

theorem StmtSpec.decl {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {d : VarDecl}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpec prog cfg ext Q env blks m os (.decls [d]) PN) :
    StmtSpec prog cfg ext Q env blks m os (.decl d) PN :=
  StmtSpecEx.to_stmtSpec (fun rt => StmtSpecEx.decl (h.to_ex rt))

theorem StmtSpec.caseStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {v : Int} {body : CStmt}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpec prog cfg ext Q env blks m os body PN) :
    StmtSpec prog cfg ext Q env blks m os (.caseStmt v body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt => StmtSpecEx.caseStmt (h.to_ex rt))

theorem StmtSpec.defaultStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {body : CStmt}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpec prog cfg ext Q env blks m os body PN) :
    StmtSpec prog cfg ext Q env blks m os (.defaultStmt body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt => StmtSpecEx.defaultStmt (h.to_ex rt))

theorem StmtSpec.labelStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {lbl : String} {body : CStmt}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (h : StmtSpec prog cfg ext Q env blks m os body PN) :
    StmtSpec prog cfg ext Q env blks m os (.labelStmt lbl body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt => StmtSpecEx.labelStmt (h.to_ex rt))

theorem StmtSpec.switchStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {scrut : CExpr} {body : CStmt}
    {Pscr : Val → CTy → Mem → OSState → ModSet → Prop}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hs : ExprSpec prog cfg ext Q env blks m os [] scrut Pscr)
    (hint : ∀ sv st ms oss modss, Pscr sv st ms oss modss →
      ∃ ik iv, valAsInt? sv = some (ik, iv))
    (hnone : ∀ sv st ms oss modss ik iv, Pscr sv st ms oss modss →
      valAsInt? sv = some (ik, iv) → Sem.findSwitchTarget iv body = none → PN env blks ms oss)
    (hsome : ∀ sv st ms oss modss ik iv tgt, Pscr sv st ms oss modss →
      valAsInt? sv = some (ik, iv) → Sem.findSwitchTarget iv body = some tgt →
      ∃ PNb, StmtSpec prog cfg ext Q env blks ms oss tgt PNb ∧
        (∀ e1 b1 m1 o1, PNb e1 b1 m1 o1 → PN e1 b1 m1 o1)) :
    StmtSpec prog cfg ext Q env blks m os (.switchStmt scrut body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.switchStmt hs hint hnone fun sv st ms oss modss ik iv tgt hp hvi hft =>
      let ⟨_, hb, himp⟩ := hsome sv st ms oss modss ik iv tgt hp hvi hft
      (hb.to_ex rt).mono himp (fun _ _ _ _ h => False.elim h)
        (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h))

theorem StmtSpec.whileStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {c : CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
        ExprSpec prog cfg ext Q env blks m os [] c Pc ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
          PN env blks mc osc) ∧
        (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
          ∃ PNb, StmtSpec prog cfg ext Q env blks mc osc body PNb ∧
            (∀ e' b' m' o', PNb e' b' m' o' → ∃ n', n' < n ∧ Inv n' e' b' m' o'))) :
    StmtSpec prog cfg ext Q env0 blks0 m0 os0 (.whileStmt c body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.whileStmt Inv hinit fun n env blks m os hi =>
      let ⟨Pc, hc, htr, hfa, htrb⟩ := hstep n env blks m os hi
      ⟨Pc, hc, htr, hfa, fun vc tc mc osc modsc hp ht1 =>
        let ⟨PNb, hb, hdec⟩ := htrb vc tc mc osc modsc hp ht1
        ⟨PNb, fun _ _ _ _ => False,
          (hb.to_ex rt).mono (fun _ _ _ _ => id) (fun _ _ _ _ h => False.elim h)
            (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h),
          hdec, fun _ _ _ _ h => False.elim h⟩⟩)

theorem StmtSpec.doWhileStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {body : CStmt} {c : CExpr} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      ∃ PNb, StmtSpec prog cfg ext Q env blks m os body PNb ∧
        (∀ e1 b1 m1 o1, PNb e1 b1 m1 o1 →
          ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
            ExprSpec prog cfg ext Q e1 b1 m1 o1 [] c Pc ∧
            (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
            (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
              PN e1 b1 mc osc) ∧
            (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
              ∃ n', n' < n ∧ Inv n' e1 b1 mc osc))) :
    StmtSpec prog cfg ext Q env0 blks0 m0 os0 (.doWhileStmt body c) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.doWhileStmt Inv hinit fun n env blks m os hi =>
      let ⟨PNb, hb, hcond⟩ := hstep n env blks m os hi
      ⟨PNb, fun _ _ _ _ => False,
        (hb.to_ex rt).mono (fun _ _ _ _ => id) (fun _ _ _ _ h => False.elim h)
          (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h),
        fun e1 b1 m1 o1 hp => hcond e1 b1 m1 o1 (hp.elim id False.elim)⟩)

theorem StmtSpec.forNoneStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {c? stp? : Option CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    (hinit : Inv n0 env0 blks0 m0 os0)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      match c? with
      | none =>
        ∃ PNb, StmtSpec prog cfg ext Q env blks m os body PNb ∧
          (∀ e1 b1 m1 o1, PNb e1 b1 m1 o1 → ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1)
      | some c =>
        ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
          ExprSpec prog cfg ext Q env blks m os [] c Pc ∧
          (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
          (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
            PN env blks mc osc) ∧
          (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
            ∃ PNb, StmtSpec prog cfg ext Q env blks mc osc body PNb ∧
              (∀ e1 b1 m1 o1, PNb e1 b1 m1 o1 → ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1))) :
    StmtSpec prog cfg ext Q env0 blks0 m0 os0 (.forStmt none c? stp? body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.forNoneStmt Inv hinit fun n env blks m os hi => by
      cases c? with
      | none =>
        obtain ⟨PNb, hb, hm⟩ := hstep n env blks m os hi
        exact ⟨PNb, fun _ _ _ _ => False,
          (hb.to_ex rt).mono (fun _ _ _ _ => id) (fun _ _ _ _ h => False.elim h)
            (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h),
          fun e1 b1 m1 o1 hp => hm e1 b1 m1 o1 (hp.elim id False.elim)⟩
      | some c =>
        obtain ⟨Pc, hc, htr, hfa, htrb⟩ := hstep n env blks m os hi
        refine ⟨Pc, hc, htr, hfa, fun vc tc mc osc modsc hp ht1 => ?_⟩
        obtain ⟨PNb, hb, hm⟩ := htrb vc tc mc osc modsc hp ht1
        exact ⟨PNb, fun _ _ _ _ => False,
          (hb.to_ex rt).mono (fun _ _ _ _ => id) (fun _ _ _ _ h => False.elim h)
            (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h),
          fun e1 b1 m1 o1 hp => hm e1 b1 m1 o1 (hp.elim id False.elim)⟩)

theorem StmtSpec.forStmt {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    (Inv : Nat → Env → List BlockId → Mem → OSState → Prop)
    {init : CExpr} {c? stp? : Option CExpr} {body : CStmt} {n0 : Nat}
    {env0 : Env} {blks0 : List BlockId} {m0 : Mem} {os0 : OSState}
    {PN : Env → List BlockId → Mem → OSState → Prop}
    {Pi : Val → CTy → Mem → OSState → ModSet → Prop}
    (hinit_expr : ExprSpec prog cfg ext Q env0 blks0 m0 os0 [] init Pi)
    (hinv0 : ∀ vi ti m1 os1 modsi, Pi vi ti m1 os1 modsi → Inv n0 env0 blks0 m1 os1)
    (hstep : ∀ n env blks m os, Inv n env blks m os →
      match c? with
      | none =>
        ∃ PNb, StmtSpec prog cfg ext Q env blks m os body PNb ∧
          (∀ e1 b1 m1 o1, PNb e1 b1 m1 o1 → ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1)
      | some c =>
        ∃ Pc : Val → CTy → Mem → OSState → ModSet → Prop,
          ExprSpec prog cfg ext Q env blks m os [] c Pc ∧
          (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → ∃ bc : Bool, Sem.isTruthy vc = some bc) ∧
          (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some false →
            PN env blks mc osc) ∧
          (∀ vc tc mc osc modsc, Pc vc tc mc osc modsc → Sem.isTruthy vc = some true →
            ∃ PNb, StmtSpec prog cfg ext Q env blks mc osc body PNb ∧
              (∀ e1 b1 m1 o1, PNb e1 b1 m1 o1 → ForStepNext prog cfg ext Q Inv n stp? e1 b1 m1 o1))) :
    StmtSpec prog cfg ext Q env0 blks0 m0 os0 (.forStmt (some init) c? stp? body) PN :=
  StmtSpecEx.to_stmtSpec (fun rt =>
    StmtSpecEx.forStmt Inv hinit_expr hinv0 fun n env blks m os hi => by
      cases c? with
      | none =>
        obtain ⟨PNb, hb, hm⟩ := hstep n env blks m os hi
        exact ⟨PNb, fun _ _ _ _ => False,
          (hb.to_ex rt).mono (fun _ _ _ _ => id) (fun _ _ _ _ h => False.elim h)
            (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h),
          fun e1 b1 m1 o1 hp => hm e1 b1 m1 o1 (hp.elim id False.elim)⟩
      | some c =>
        obtain ⟨Pc, hc, htr, hfa, htrb⟩ := hstep n env blks m os hi
        refine ⟨Pc, hc, htr, hfa, fun vc tc mc osc modsc hp ht1 => ?_⟩
        obtain ⟨PNb, hb, hm⟩ := htrb vc tc mc osc modsc hp ht1
        exact ⟨PNb, fun _ _ _ _ => False,
          (hb.to_ex rt).mono (fun _ _ _ _ => id) (fun _ _ _ _ h => False.elim h)
            (fun _ _ _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h),
          fun e1 b1 m1 o1 hp => hm e1 b1 m1 o1 (hp.elim id False.elim)⟩)

/-! ## 5. External Libc / POSIX Framing & Call Combinators (`ExtLibc`) -/

namespace ExtLibc

/-! ### 5.1 General `ExtStep` / `ExtOk`, `writeErrno`, Ranges & Byte Helpers -/

theorem ok_iff {fn : String} {args : List Val} {m m' : Mem} {os os' : OSState} {ret : Val} :
    Libc.ExtStep fn args m os (.ok ret m' os') ↔ Libc.ExtOk fn args m os ret m' os' :=
  Iff.rfl

theorem not_ub_of_ok {fn : String} {args : List Val} {m : Mem} {os : OSState}
    (h : ∃ ret m' os', Libc.ExtOk fn args m os ret m' os') :
    ¬ Libc.ExtStep fn args m os .ub :=
  fun hub => hub h

theorem callDispatch_extOk {prog : Prog} {cfg : PointerConfig} {Q : Val → Mem → OSState → Prop}
    {env : Env} {blks : List BlockId} {sym : String} {fnTy : CTy} {argVals : List (Val × CTy)}
    {m : Mem} {os : OSState} {fs : List ExprFrame} {ctx : ExprCtx} {k : Cont}
    {retTy : CTy} {paramTys : List CTy} {variadic : Bool} {coerced : List Val}
    (hnfn : prog.fns sym = none)
    (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
    (hcoerce : Sem.coerceCallArgs m paramTys variadic argVals = some coerced)
    (hex : ∃ ret m' os', Libc.ExtOk sym coerced m os ret m' os')
    (hpost : ∀ ret m' os', Libc.ExtOk sym coerced m os ret m' os' →
      WPTerm prog cfg Libc.ExtStep Q (.running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k)) :
    CallDispatchWP prog cfg Libc.ExtStep Q env blks sym fnTy argVals m os fs ctx k :=
  CallDispatchWP.ext hnfn hsig hcoerce hex (not_ub_of_ok hex) hpost

theorem exprSpec_call_extOk {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {sym : String} {arg : CExpr} {rest : List CExpr}
    {retTy : CTy} {paramTys : List CTy} {variadic : Bool}
    (hnenv : env.lookup sym = none)
    (henum : Sem.enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (retTy, paramTys, variadic))
    (hnfn : prog.fns sym = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] (arg :: rest) Pargs)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hext : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ coerced,
        Sem.coerceCallArgs m2 paramTys variadic vs = some coerced ∧
        (∃ ret m' os', Libc.ExtOk sym coerced m2 os2 ret m' os') ∧
        (∀ ret m' os', Libc.ExtOk sym coerced m2 os2 ret m' os' →
          Post ret retTy m' os' [])) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var sym) (arg :: rest)) Post :=
  ExprSpec.call_ext hnenv henum hproto hnfn hargs fun vs m2 os2 hp =>
    let ⟨coerced, hco, hex, hpost⟩ := hext vs m2 os2 hp
    ⟨coerced, hco, hex, not_ub_of_ok hex, hpost⟩

theorem writeErrno_eq_some {m : Mem} {os : OSState} {blk : Block} (e : Int32)
    (hb : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ m', Libc.writeErrno m os e = some m' := by
  have hlen : (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length = 4 := by
    simp only [Mem.encodeInt, IntKind.bytes, List.length_map, List.length_range]
    rfl
  have hin : Mem.inBounds blk 0 (Mem.encodeInt .i32 (BitVec.ofInt 32 e.toInt)).length = true := by
    rw [hlen]
    exact inBounds_zero_of_le hsz
  exact writeBytes_eq_some hb hrw hin

theorem frameMod_of_writeErrno {m m' : Mem} {os : OSState} {e : Int32}
    (h : Libc.writeErrno m os e = some m') :
    FrameMod m m' (· = os.errnoBlk) :=
  FrameMod.of_writeBytes h

theorem writeErrno_nextBlock {m m' : Mem} {os : OSState} {e : Int32}
    (h : Libc.writeErrno m os e = some m') :
    m'.nextBlock = m.nextBlock :=
  writeBytes_nextBlock h

theorem writeErrno_preserves_perm {m m' : Mem} {os : OSState} {e : Int32}
    (h : Libc.writeErrno m os e = some m') {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) :
    ∃ blk', m'.blocks b = some blk' ∧ blk'.size = blk.size ∧ blk'.perm = blk.perm ∧ blk'.kind = blk.kind := by
  by_cases heq : b = os.errnoBlk
  · subst heq
    obtain ⟨blk', hb', hkind, hperm, hsz, _, _, _⟩ := writeBytes_preserves_perm h hb
    exact ⟨blk', hb', hsz, hperm, hkind⟩
  · have hblk' := writeBytes_blocks_ne h heq
    rw [hb] at hblk'
    exact ⟨blk, hblk', rfl, rfl, rfl⟩

theorem ptrDisjointOrEq_of_ne {b1 b2 : BlockId} (hne : b1 ≠ b2) (o1 o2 : Int64) (n : Nat) :
    Libc.ptrDisjointOrEq b1 o1 b2 o2 n = true := by
  unfold Libc.ptrDisjointOrEq
  have hbeq : (b1 != b2) = true := bne_iff_ne.mpr hne
  simp only [hbeq, Bool.true_or]

theorem ptrDisjointOrEq_of_zero (b1 b2 : BlockId) (o1 o2 : Int64) :
    Libc.ptrDisjointOrEq b1 o1 b2 o2 0 = true := by
  unfold Libc.ptrDisjointOrEq
  rcases Int.le_total o1.toInt o2.toInt with h | h
  · have h1 : decide (o1.toInt + ↑(0 : Nat) ≤ o2.toInt) = true := decide_eq_true (by omega)
    simp only [h1, Bool.or_true, Bool.true_or]
  · have h2 : decide (o2.toInt + ↑(0 : Nat) ≤ o1.toInt) = true := decide_eq_true (by omega)
    simp only [h2, Bool.or_true]

theorem ptrDisjointOrEq_of_le_left (b1 b2 : BlockId) {o1 o2 : Int64} {n : Nat}
    (hle : o1.toInt + n ≤ o2.toInt) :
    Libc.ptrDisjointOrEq b1 o1 b2 o2 n = true := by
  unfold Libc.ptrDisjointOrEq
  have h1 : decide (o1.toInt + ↑n ≤ o2.toInt) = true := decide_eq_true hle
  simp only [h1, Bool.or_true, Bool.true_or]

theorem ptrDisjointOrEq_of_le_right (b1 b2 : BlockId) {o1 o2 : Int64} {n : Nat}
    (hle : o2.toInt + n ≤ o1.toInt) :
    Libc.ptrDisjointOrEq b1 o1 b2 o2 n = true := by
  unfold Libc.ptrDisjointOrEq
  have h2 : decide (o2.toInt + ↑n ≤ o1.toInt) = true := decide_eq_true hle
  simp only [h2, Bool.or_true]

theorem validWritableRange_iff {m : Mem} {b : BlockId} {off : Int64} {n : Nat} :
    Libc.validWritableRange m b off n = true ↔
      ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧ Mem.inBounds blk off n = true := by
  unfold Libc.validWritableRange
  cases hb : m.blocks b with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro _ h _; cases h
  | some blk =>
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro ⟨hp, hin⟩; exact ⟨blk, rfl, hp, hin⟩
    · intro ⟨blk', heq, hp, hin⟩; cases heq; exact ⟨hp, hin⟩

theorem validReadableRange_iff {m : Mem} {b : BlockId} {off : Int64} {n : Nat} :
    Libc.validReadableRange m b off n = true ↔
      ∃ blk, m.blocks b = some blk ∧ Mem.inBounds blk off n = true := by
  unfold Libc.validReadableRange
  cases hb : m.blocks b with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro _ h _; cases h
  | some blk =>
    constructor
    · intro hin; exact ⟨blk, rfl, hin⟩
    · intro ⟨blk', heq, hin⟩; cases heq; exact hin

theorem validReadableRange_of_validWritableRange {m : Mem} {b : BlockId} {off : Int64} {n : Nat}
    (h : Libc.validWritableRange m b off n = true) :
    Libc.validReadableRange m b off n = true := by
  obtain ⟨blk, hb, _, hin⟩ := validWritableRange_iff.mp h
  exact validReadableRange_iff.mpr ⟨blk, hb, hin⟩

theorem allConcreteBytes_map_byte (bs : List UInt8) :
    Libc.allConcreteBytes (bs.map MemByte.byte) = some bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    simp only [List.map_cons, Libc.allConcreteBytes, ih, bind, Option.bind_some, pure]

theorem allConcreteBytes_replicate_byte (n : Nat) (b : UInt8) :
    Libc.allConcreteBytes (List.replicate n (.byte b)) = some (List.replicate n b) := by
  have heq : List.replicate n (MemByte.byte b) = (List.replicate n b).map MemByte.byte := by
    induction n with
    | zero => rfl
    | succ k ih => simp only [List.replicate_succ, List.map_cons, ih]
  rw [heq]
  exact allConcreteBytes_map_byte _

theorem hasNul_eq_true_of_mem {bs : List MemByte} (h : MemByte.byte 0 ∈ bs) :
    Libc.hasNul bs = true := by
  induction bs with
  | nil => cases h
  | cons hd tl ih =>
    rcases List.mem_cons.mp h with rfl | htl
    · rfl
    · cases hd with
      | undef | ptrFrag _ _ _ | fnFrag _ _ => exact ih htl
      | byte _ =>
        unfold Libc.hasNul
        split
        · next he => cases he
        · rfl
        · next _ _ he => cases he; exact ih htl

private theorem memchrStep_go_inv (b : BlockId) (off : Int64) (target : UInt8) (n : Nat)
    (blk : Block) (start : Nat) (hstart : start = off.toInt.toNat) :
    ∀ k i ret, n - i = k →
      Libc.memchrStep.go b off target n blk start i = some ret →
      ret = .null ∨
        ∃ j < n, i ≤ j ∧ ret = .ptr b (Int64.ofInt (off.toInt + j)) ∧
          blk.bytes (off.toInt.toNat + j) = .byte target := by
  intro k
  induction k with
  | zero =>
    intro i ret hni hgo
    rw [Libc.memchrStep.go] at hgo
    have hnlt : ¬ i < n := by omega
    simp only [hnlt, ↓reduceDIte, Option.some.injEq] at hgo
    exact Or.inl hgo.symm
  | succ k' ih =>
    intro i ret hni hgo
    rw [Libc.memchrStep.go] at hgo
    have hlt : i < n := by omega
    simp only [hlt, ↓reduceDIte] at hgo
    cases hby : blk.bytes (start + i) with
    | undef | ptrFrag _ _ _ | fnFrag _ _ => simp only [hby] at hgo; cases hgo
    | byte byte =>
      simp only [hby] at hgo
      by_cases heq : byte = target
      · have hbeq : (byte == target) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, Option.some.injEq] at hgo
        rw [← hgo]
        refine Or.inr ⟨i, hlt, Nat.le_refl _, rfl, ?_⟩
        rw [← hstart, hby, heq]
      · have hbf : (byte == target) = false := beq_false_of_ne heq
        simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hgo
        rcases ih (i + 1) ret (by omega) hgo with rfl | ⟨j, hjn, hij, hr, hb⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨j, hjn, by omega, hr, hb⟩

theorem memchrStep_inv {m : Mem} {b : BlockId} {off : Int64} {target : UInt8} {n : Nat} {ret : Val}
    (h : Libc.memchrStep m b off target n = some ret) :
    ∃ blk, m.blocks b = some blk ∧ Mem.inBounds blk off n = true ∧
      (ret = .null ∨
        ∃ i < n, ret = .ptr b (Int64.ofInt (off.toInt + i)) ∧
          blk.bytes (off.toInt.toNat + i) = .byte target) := by
  unfold Libc.memchrStep at h
  cases hb : m.blocks b with
  | none => simp only [hb, bind, Option.bind] at h; cases h
  | some blk =>
    simp only [hb, bind, Option.bind] at h
    by_cases hin : (0 ≤ off.toInt && off.toInt.toNat + n ≤ blk.size) = true
    · simp only [hin, guard, pure, ↓reduceIte] at h
      have hinB : Mem.inBounds blk off n = true := hin
      refine ⟨blk, rfl, hinB, ?_⟩
      rcases memchrStep_go_inv b off target n blk off.toInt.toNat rfl n 0 ret (Nat.sub_zero n) h with
        rfl | ⟨i, hlt, _, hr, hby⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨i, hlt, hr, hby⟩
    · have hinf : (0 ≤ off.toInt && off.toInt.toNat + n ≤ blk.size) = false := Bool.eq_false_iff.mpr hin
      simp only [hinf, guard, Bool.false_eq_true, ↓reduceIte] at h
      cases h

private theorem memchrStep_go_concrete (b : BlockId) (off : Int64) (target : UInt8) (n : Nat)
    (blk : Block) (start : Nat) (hstart : start = off.toInt.toNat)
    (hconc : ∀ i < n, ∃ byte, blk.bytes (off.toInt.toNat + i) = .byte byte) :
    ∀ k i, n - i = k → ∃ ret, Libc.memchrStep.go b off target n blk start i = some ret := by
  intro k
  induction k with
  | zero =>
    intro i hni
    rw [Libc.memchrStep.go]
    have hnlt : ¬ i < n := by omega
    simp only [hnlt, ↓reduceDIte]
    exact ⟨.null, rfl⟩
  | succ k' ih =>
    intro i hni
    rw [Libc.memchrStep.go]
    have hlt : i < n := by omega
    simp only [hlt, ↓reduceDIte]
    obtain ⟨byte, hby⟩ := hconc i hlt
    have hby' : blk.bytes (start + i) = .byte byte := by rw [hstart]; exact hby
    rw [hby']
    by_cases heq : byte = target
    · have hbeq : (byte == target) = true := beq_iff_eq.mpr heq
      simp only [hbeq, ↓reduceIte]
      exact ⟨_, rfl⟩
    · have hbf : (byte == target) = false := beq_false_of_ne heq
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      exact ih (i + 1) (by omega)

theorem memchrStep_eq_some_of_concrete {m : Mem} {b : BlockId} {off : Int64} {target : UInt8} {n : Nat}
    {blk : Block} (hb : m.blocks b = some blk) (hin : Mem.inBounds blk off n = true)
    (hconc : ∀ i < n, ∃ byte, blk.bytes (off.toInt.toNat + i) = .byte byte) :
    ∃ ret, Libc.memchrStep m b off target n = some ret := by
  unfold Libc.memchrStep
  have hinB : (0 ≤ off.toInt && off.toInt.toNat + n ≤ blk.size) = true := hin
  simp only [hb, bind, Option.bind, hinB, guard, pure, ↓reduceIte]
  exact memchrStep_go_concrete b off target n blk off.toInt.toNat rfl hconc n 0 (Nat.sub_zero n)

private theorem strlenAt_go_bytes (blk : Block) (n : Nat) (bs : List UInt8)
    (hsz : blk.size = n + 1) (hlen : bs.length = n) (hnonnul : (0 : UInt8) ∉ bs)
    (hbytes : ∀ i, blk.bytes i = .byte (if i < n then bs[i]?.getD 0 else 0)) :
    ∀ k, k ≤ n → Mem.strlenAt.go blk 0 (n - k) = some n := by
  intro k hk
  induction k with
  | zero =>
    rw [Nat.sub_zero, Mem.strlenAt.go]
    have hlt : n < blk.size := by omega
    simp only [hlt, ↓reduceDIte, hbytes, Nat.lt_irrefl, ↓reduceIte, Nat.sub_zero]
  | succ k' ih =>
    have hlt : n - (k' + 1) < n := by omega
    have hltbs : n - (k' + 1) < bs.length := by rw [hlen]; exact hlt
    have hlt1 : n - (k' + 1) < blk.size := by omega
    have hnz : bs[n - (k' + 1)]?.getD 0 ≠ 0 := by
      rw [List.getElem?_eq_getElem hltbs, Option.getD_some]
      have hmem : bs[n - (k' + 1)] ∈ bs := List.getElem_mem hltbs
      intro heq
      rw [heq] at hmem
      exact hnonnul hmem
    rw [Mem.strlenAt.go]
    simp only [hlt1, ↓reduceDIte, hbytes, hlt, ↓reduceIte]
    cases hbv : bs[n - (k' + 1)]?.getD 0 with
    | ofBitVec v =>
      match hv : v.toNat with
      | 0 =>
        exfalso; apply hnz
        rw [hbv]; apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; exact hv
      | _ + 1 =>
        have hsub : n - (k' + 1) + 1 = n - k' := by omega
        rw [hsub]
        exact ih (by omega)

theorem strlenAt_alloc_zero_terminated {m m' : Mem} {n : Nat} {bs : List UInt8} {base : UInt64}
    {hsz : n + 1 < ptrDiffLimit} {bid : BlockId}
    (hlen : bs.length = n) (hnonnul : (0 : UInt8) ∉ bs)
    (halloc : m.alloc (n + 1) 1 .ro .global base
      (fun i => .byte (if i < n then bs[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _) = (bid, m')) :
    m'.strlenAt bid 0 = some n := by
  unfold Mem.alloc at halloc
  cases halloc
  unfold Mem.strlenAt
  simp only [BEq.refl, ↓reduceIte, bind, Option.bind_some, Int64.toInt_zero, Int.le_refl,
    Int.toNat_zero, Nat.zero_le, Bool.and_self, guard, decide_true, pure]
  let blk0 : Block :=
    { size := n + 1, align := 1, perm := .ro, kind := .global, baseAddr := base,
      bytes := fun i => .byte (if i < n then bs[i]?.getD 0 else 0),
      sizeLt := hsz, alignPos := by decide, baseAligned := Nat.mod_one _ }
  have h := strlenAt_go_bytes blk0 n bs rfl hlen hnonnul (fun _ => rfl) n (Nat.le_refl n)
  rw [Nat.sub_self] at h
  exact h

/-! ### 5.2 Fast `coerceCallArgs` Lemmas -/

private theorem guard_option_pos (p : Prop) [Decidable p] (h : p) :
    (guard p : Option Unit) = some () := by
  unfold guard
  simp only [h, ↓reduceIte, pure]

theorem coerceCallArgs_0 (m : Mem) :
    Sem.coerceCallArgs m [] false [] = some [] := rfl

theorem coerceCallArgs_1 {m : Mem} {p1 : CTy} {v1 c1 : Val} {t1 : CTy}
    (hc1 : Sem.castVal m p1 v1 = some c1) :
    Sem.coerceCallArgs m [p1] false [(v1, t1)] = some [c1] := by
  unfold Sem.coerceCallArgs
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil, BEq.refl,
    guard, pure, List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    bind, Option.bind, hc1]

theorem coerceCallArgs_2 {m : Mem} {p1 p2 : CTy} {v1 v2 c1 c2 : Val} {t1 t2 : CTy}
    (hc1 : Sem.castVal m p1 v1 = some c1) (hc2 : Sem.castVal m p2 v2 = some c2) :
    Sem.coerceCallArgs m [p1, p2] false [(v1, t1), (v2, t2)] = some [c1, c2] := by
  unfold Sem.coerceCallArgs
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil, BEq.refl,
    guard, pure, List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    bind, Option.bind, hc1, hc2]

theorem coerceCallArgs_3 {m : Mem} {p1 p2 p3 : CTy} {v1 v2 v3 c1 c2 c3 : Val} {t1 t2 t3 : CTy}
    (hc1 : Sem.castVal m p1 v1 = some c1) (hc2 : Sem.castVal m p2 v2 = some c2)
    (hc3 : Sem.castVal m p3 v3 = some c3) :
    Sem.coerceCallArgs m [p1, p2, p3] false [(v1, t1), (v2, t2), (v3, t3)] = some [c1, c2, c3] := by
  unfold Sem.coerceCallArgs
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil, BEq.refl,
    guard, pure, List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    bind, Option.bind, hc1, hc2, hc3]

theorem coerceCallArgs_4 {m : Mem} {p1 p2 p3 p4 : CTy} {v1 v2 v3 v4 c1 c2 c3 c4 : Val}
    {t1 t2 t3 t4 : CTy}
    (hc1 : Sem.castVal m p1 v1 = some c1) (hc2 : Sem.castVal m p2 v2 = some c2)
    (hc3 : Sem.castVal m p3 v3 = some c3) (hc4 : Sem.castVal m p4 v4 = some c4) :
    Sem.coerceCallArgs m [p1, p2, p3, p4] false [(v1, t1), (v2, t2), (v3, t3), (v4, t4)] =
      some [c1, c2, c3, c4] := by
  unfold Sem.coerceCallArgs
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil, BEq.refl,
    guard, pure, List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    bind, Option.bind, hc1, hc2, hc3, hc4]

theorem coerceCallArgs_variadic_2 {m : Mem} {p1 p2 : CTy} {v1 v2 c1 c2 : Val} {t1 t2 : CTy}
    {rest : List (Val × CTy)}
    (hc1 : Sem.castVal m p1 v1 = some c1) (hc2 : Sem.castVal m p2 v2 = some c2) :
    Sem.coerceCallArgs m [p1, p2] true ((v1, t1) :: (v2, t2) :: rest) =
      some (c1 :: c2 :: rest.map (fun (v, _) => Sem.promoteVariadicArg v)) := by
  unfold Sem.coerceCallArgs
  have hg : (guard ([p1, p2].length ≤ ((v1, t1) :: (v2, t2) :: rest).length) : Option Unit) = some () :=
    guard_option_pos _ (by simp only [List.length_cons, List.length_nil]; omega)
  simp only [↓reduceIte]
  rw [hg]
  simp only [pure, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    bind, Option.bind, hc1, hc2, List.cons_append, List.nil_append]

theorem coerceCallArgs_variadic_3 {m : Mem} {p1 p2 p3 : CTy} {v1 v2 v3 c1 c2 c3 : Val}
    {t1 t2 t3 : CTy} {rest : List (Val × CTy)}
    (hc1 : Sem.castVal m p1 v1 = some c1) (hc2 : Sem.castVal m p2 v2 = some c2)
    (hc3 : Sem.castVal m p3 v3 = some c3) :
    Sem.coerceCallArgs m [p1, p2, p3] true ((v1, t1) :: (v2, t2) :: (v3, t3) :: rest) =
      some (c1 :: c2 :: c3 :: rest.map (fun (v, _) => Sem.promoteVariadicArg v)) := by
  unfold Sem.coerceCallArgs
  have hg : (guard ([p1, p2, p3].length ≤ ((v1, t1) :: (v2, t2) :: (v3, t3) :: rest).length) : Option Unit) =
      some () :=
    guard_option_pos _ (by simp only [List.length_cons, List.length_nil]; omega)
  simp only [↓reduceIte]
  rw [hg]
  simp only [pure, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    List.zip_cons_cons, List.zip_nil_right, List.mapM_cons, List.mapM_nil,
    bind, Option.bind, hc1, hc2, hc3, List.cons_append, List.nil_append]

/-! ### 5.3 Typed Outcome Specs, Witnesses, Elimination & `ExprSpec` Combinators (All 19 Libc/POSIX Functions) -/

private theorem bitVec_ofNat_toNat_self {w : Nat} (bv : BitVec w) :
    BitVec.ofNat w bv.toNat = bv :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bv.isLt])

private theorem nat_eq_of_bitVec64_eq_lt {n : Nat} {bv : BitVec 64}
    (heq : BitVec.ofNat 64 n = bv) (hlt : n < ptrDiffLimit) : n = bv.toNat := by
  have h := congrArg BitVec.toNat heq
  have hlim : ptrDiffLimit = 2 ^ 63 := rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

private theorem readBytes_length {m : Mem} {b : BlockId} {off : Int64} {len : Nat} {bs : List MemByte}
    (h : m.readBytes b off len = some bs) : bs.length = len := by
  unfold Mem.readBytes at h
  cases hb : m.blocks b with
  | none => simp only [hb, bind, Option.bind] at h; cases h
  | some blk =>
    simp only [hb, bind, Option.bind] at h
    by_cases hin : Mem.inBounds blk off len = true
    · simp only [hin, guard, pure, ↓reduceIte, Option.some.injEq] at h
      rw [← h, List.length_map, List.length_range]
    · have hinf : Mem.inBounds blk off len = false := Bool.eq_false_iff.mpr hin
      simp only [hinf, guard, Bool.false_eq_true, ↓reduceIte] at h
      cases h

private theorem inBounds_lt_ptrDiffLimit {blk : Block} {off : Int64} {n : Nat}
    (hin : Mem.inBounds blk off n = true) : n < ptrDiffLimit := by
  unfold Mem.inBounds at hin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  have hsz := blk.sizeLt
  omega

private theorem frameMod_of_alloc_ro {m m' : Mem} {sz al : Nat} {ba : UInt64} {init : Nat → MemByte}
    {hsz : sz < ptrDiffLimit} {hal : 0 < al} {hba : ba.toNat % al = 0} {bid : BlockId}
    (ha : m.alloc sz al .ro .global ba init hsz hal hba = (bid, m')) :
    FrameMod m m' (fun _ => False) := by
  unfold Mem.alloc at ha
  cases ha
  refine ⟨Nat.le_succ _, ?_, ?_⟩
  · intro b' hlt _
    have hne : b' ≠ m.nextBlock := Nat.ne_of_lt hlt
    have hbeq : (b' == m.nextBlock) = false := beq_false_of_ne hne
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  · intro b' blk' hle hsome
    by_cases heq : b' = m.nextBlock
    · have hbeq : (b' == m.nextBlock) = true := beq_iff_eq.mpr heq
      simp only [hbeq, ↓reduceIte, Option.some.injEq] at hsome
      rw [← hsome]
      exact Or.inr ⟨rfl, rfl⟩
    · have hbeq : (b' == m.nextBlock) = false := beq_false_of_ne heq
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hsome
      exact False.elim (Nat.not_lt_of_ge hle (lt_nextBlock_of_some hsome))

private theorem alloc_blocks_self {m m' : Mem} {sz al : Nat} {perm : Perm} {kind : AllocKind}
    {ba : UInt64} {init : Nat → MemByte} {hsz : sz < ptrDiffLimit} {hal : 0 < al}
    {hba : ba.toNat % al = 0} {bid : BlockId}
    (ha : m.alloc sz al perm kind ba init hsz hal hba = (bid, m')) :
    bid = m.nextBlock ∧ m'.nextBlock = m.nextBlock + 1 ∧
      ∃ blk, m'.blocks bid = some blk ∧ blk.size = sz ∧ blk.align = al ∧
        blk.perm = perm ∧ blk.kind = kind ∧ (∀ i, blk.bytes i = init i) := by
  unfold Mem.alloc at ha
  cases ha
  let blk : Block :=
    { size := sz, align := al, perm := perm, kind := kind, baseAddr := ba, bytes := init,
      sizeLt := hsz, alignPos := hal, baseAligned := hba }
  refine ⟨rfl, rfl, blk, ?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  simp only [BEq.refl, ↓reduceIte]
  rfl

private theorem readBytes_len_lt {m : Mem} {b : BlockId} {off : Int64} {n : Nat} {bs : List MemByte}
    (h : m.readBytes b off n = some bs) : n < ptrDiffLimit := by
  unfold Mem.readBytes at h
  cases hb : m.blocks b with
  | none => simp only [hb, bind, Option.bind] at h; cases h
  | some blk =>
    simp only [hb, bind, Option.bind] at h
    by_cases hin : Mem.inBounds blk off n = true
    · exact inBounds_lt_ptrDiffLimit hin
    · have hinf : Mem.inBounds blk off n = false := Bool.eq_false_iff.mpr hin
      simp only [hinf, guard, Bool.false_eq_true, ↓reduceIte] at h
      cases h

private theorem writeBytes_len_lt {m m' : Mem} {b : BlockId} {off : Int64} {bs : List MemByte}
    (h : m.writeBytes b off bs = some m') : bs.length < ptrDiffLimit := by
  unfold Mem.writeBytes at h
  split at h
  · cases h
  · next blk _ =>
    split at h
    · next hp =>
      simp only [Bool.and_eq_true] at hp
      exact inBounds_lt_ptrDiffLimit hp.2
    · cases h

private theorem val_int_eq {k : IntKind} {v1 v2 : BitVec k.bits}
    (h : Val.int k v1 = Val.int k v2) : v1 = v2 := by
  cases h; rfl

private theorem val_ptr_eq {b1 b2 : BlockId} {o1 o2 : Int64}
    (h : Val.ptr b1 o1 = Val.ptr b2 o2) : b1 = b2 ∧ o1 = o2 := by
  cases h; exact ⟨rfl, rfl⟩

private theorem ne_or_elim {s fn a b : String} (heq : s = fn) (hor : fn = a ∨ fn = b)
    (hne1 : s ≠ a) (hne2 : s ≠ b) : False := by
  rw [← heq] at hor
  exact hor.elim hne1 hne2

private theorem ne_or_or_elim {fn s1 s2 a b : String}
    (h1 : fn = s1 ∨ fn = s2) (h2 : fn = a ∨ fn = b)
    (hne11 : s1 ≠ a) (hne12 : s1 ≠ b) (hne21 : s2 ≠ a) (hne22 : s2 ≠ b) : False :=
  h1.elim (fun ha => h2.elim (fun hb => hne11 (ha.symm.trans hb)) (fun hb => hne12 (ha.symm.trans hb)))
          (fun ha => h2.elim (fun hb => hne21 (ha.symm.trans hb)) (fun hb => hne22 (ha.symm.trans hb)))

/-! #### 5.3.1 `malloc` -/

def MallocPost (n : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  ((ret = .null ∧ m' = m) ∨
    ∃ bid blk,
      ret = .ptr bid 0 ∧ bid = m.nextBlock ∧ m'.nextBlock = m.nextBlock + 1 ∧
      m'.blocks bid = some blk ∧ blk.size = n.toNat ∧ blk.align = 16 ∧
      blk.perm = .rw ∧ blk.kind = .heap ∧
      FrameMod m m' (· = bid) ∧
      (∀ b < m.nextBlock, m'.blocks b = m.blocks b))

theorem malloc_ok_elim {n : BitVec 64} {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "malloc" [.int .u64 n] m os ret m' os') :
    MallocPost n m os ret m' os' := by
  generalize hfn : ("malloc" : String) = fn at h
  generalize hargs : ([Val.int .u64 n] : List Val) = args at h
  cases h with
  | malloc_null => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | malloc_ok n_nat hsz base hba _ _ bid _ halloc =>
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hargs).1).symm
    have hn : n_nat = n.toNat := nat_eq_of_bitVec64_eq_lt heq hsz
    obtain ⟨hbid, hnb, blk, hblk, hszb, halb, hpb, hkb, _⟩ := alloc_blocks_self halloc
    have hfr := FrameMod.of_alloc halloc
    refine ⟨rfl, Or.inr ⟨bid, blk, rfl, hbid, hnb, hblk, hn ▸ hszb, halb, hpb, hkb, hfr, ?_⟩⟩
    intro b hlt
    exact hfr.blocks_eq_of_notin hlt (fun heqb => by rw [heqb, hbid] at hlt; exact Nat.lt_irrefl _ hlt)
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem malloc_ok_exists (n : BitVec 64) (m : Mem) (os : OSState) :
    ∃ ret m' os', Libc.ExtOk "malloc" [.int .u64 n] m os ret m' os' :=
  ⟨.null, m, os, by simpa only [bitVec_ofNat_toNat_self] using Libc.ExtOk.malloc_null n.toNat m os⟩

theorem call_malloc {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {arg : CExpr}
    (hnenv : env.lookup "malloc" = none)
    (henum : Sem.enumConst? prog.tags "malloc" = none)
    (hproto : prog.fnProtos "malloc" = some (.ptr .void, [.int .u64], false))
    (hnfn : prog.fns "malloc" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [arg] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ vn tn n, vs = [(vn, tn)] ∧ Sem.castVal m2 (.int .u64) vn = some (.int .u64 n))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 n ret m' os', Pargs vs m2 os2 →
      (∃ vn tn, vs = [(vn, tn)] ∧ Sem.castVal m2 (.int .u64) vn = some (.int .u64 n)) →
      MallocPost n m2 os2 ret m' os' →
      Post ret (.ptr .void) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "malloc") [arg]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨vn, tn, n, rfl, hcn⟩ := hpre vs m2 os2 hp
  refine ⟨[.int .u64 n], coerceCallArgs_1 hcn, malloc_ok_exists n m2 os2, ?_⟩
  intro ret m' os' hok
  exact hpost [(vn, tn)] m2 os2 n ret m' os' hp ⟨vn, tn, rfl, hcn⟩ (malloc_ok_elim hok)

/-! #### 5.3.2 `calloc` -/

def CallocPost (k n : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  ((ret = .null ∧ m' = m) ∨
    ∃ bid blk,
      ret = .ptr bid 0 ∧ bid = m.nextBlock ∧ m'.nextBlock = m.nextBlock + 1 ∧
      m'.blocks bid = some blk ∧ blk.size = k.toNat * n.toNat ∧ blk.align = 16 ∧
      blk.perm = .rw ∧ blk.kind = .heap ∧
      (∀ i, blk.bytes i = .byte 0) ∧
      FrameMod m m' (· = bid) ∧
      (∀ b < m.nextBlock, m'.blocks b = m.blocks b))

theorem calloc_ok_elim {k n : BitVec 64} {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "calloc" [.int .u64 k, .int .u64 n] m os ret m' os') :
    CallocPost k n m os ret m' os' := by
  generalize hfn : ("calloc" : String) = fn at h
  generalize hargs : ([Val.int .u64 k, Val.int .u64 n] : List Val) = args at h
  cases h with
  | calloc_null => exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | calloc_ok k_nat n_nat hsz base hba _ _ bid _ halloc =>
    rcases List.cons.inj hargs with ⟨harg1, hrest1⟩
    have hk : BitVec.ofNat 64 k_nat = k := (val_int_eq harg1).symm
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hrest1).1).symm
    have hkn : k_nat * n_nat = k.toNat * n.toNat := by
      have hk1 := congrArg BitVec.toNat hk
      have hn1 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat] at hk1 hn1
      have hlim : ptrDiffLimit = 2 ^ 63 := rfl
      by_cases hklt : k_nat < 2 ^ 64
      · by_cases hnlt : n_nat < 2 ^ 64
        · rw [Nat.mod_eq_of_lt hklt] at hk1
          rw [Nat.mod_eq_of_lt hnlt] at hn1
          rw [hk1, hn1]
        · have hge : 2 ^ 64 ≤ n_nat := Nat.le_of_not_lt hnlt
          have hk0 : k_nat = 0 := by
            by_cases hkz : k_nat = 0
            · exact hkz
            · have hpos : 0 < k_nat := Nat.pos_of_ne_zero hkz
              have hm : 2 ^ 64 ≤ k_nat * n_nat := by
                calc 2 ^ 64 ≤ 1 * n_nat := by omega
                  _ ≤ k_nat * n_nat := Nat.mul_le_mul_right n_nat hpos
              omega
          rw [hk0] at hk1 ⊢
          have hk0' : k.toNat = 0 := by simpa using hk1.symm
          simp only [hk0', Nat.zero_mul]
      · have hge : 2 ^ 64 ≤ k_nat := Nat.le_of_not_lt hklt
        have hn0 : n_nat = 0 := by
          by_cases hnz : n_nat = 0
          · exact hnz
          · have hpos : 0 < n_nat := Nat.pos_of_ne_zero hnz
            have hm : 2 ^ 64 ≤ k_nat * n_nat := by
              calc 2 ^ 64 ≤ k_nat * 1 := by omega
                _ ≤ k_nat * n_nat := Nat.mul_le_mul_left k_nat hpos
            omega
        rw [hn0] at hn1 ⊢
        have hn0' : n.toNat = 0 := by simpa using hn1.symm
        simp only [hn0', Nat.mul_zero]
    obtain ⟨hbid, hnb, blk, hblk, hszb, halb, hpb, hkb, hbytes⟩ := alloc_blocks_self halloc
    have hfr := FrameMod.of_alloc halloc
    refine ⟨rfl, Or.inr ⟨bid, blk, rfl, hbid, hnb, hblk, hkn ▸ hszb, halb, hpb, hkb, hbytes, hfr, ?_⟩⟩
    intro b hlt
    exact hfr.blocks_eq_of_notin hlt (fun heqb => by rw [heqb, hbid] at hlt; exact Nat.lt_irrefl _ hlt)
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem calloc_ok_exists (k n : BitVec 64) (m : Mem) (os : OSState) :
    ∃ ret m' os', Libc.ExtOk "calloc" [.int .u64 k, .int .u64 n] m os ret m' os' :=
  ⟨.null, m, os, by
    simpa only [bitVec_ofNat_toNat_self] using Libc.ExtOk.calloc_null k.toNat n.toNat m os⟩

theorem call_calloc {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 : CExpr}
    (hnenv : env.lookup "calloc" = none)
    (henum : Sem.enumConst? prog.tags "calloc" = none)
    (hproto : prog.fnProtos "calloc" = some (.ptr .void, [.int .u64, .int .u64], false))
    (hnfn : prog.fns "calloc" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 k n, vs = [(v1, t1), (v2, t2)] ∧
        Sem.castVal m2 (.int .u64) v1 = some (.int .u64 k) ∧
        Sem.castVal m2 (.int .u64) v2 = some (.int .u64 n))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 k n ret m' os', Pargs vs m2 os2 →
      (∃ v1 t1 v2 t2, vs = [(v1, t1), (v2, t2)] ∧
        Sem.castVal m2 (.int .u64) v1 = some (.int .u64 k) ∧
        Sem.castVal m2 (.int .u64) v2 = some (.int .u64 n)) →
      CallocPost k n m2 os2 ret m' os' →
      Post ret (.ptr .void) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "calloc") [a1, a2]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, v2, t2, k, n, rfl, hc1, hc2⟩ := hpre vs m2 os2 hp
  refine ⟨[.int .u64 k, .int .u64 n], coerceCallArgs_2 hc1 hc2, calloc_ok_exists k n m2 os2, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1), (v2, t2)] m2 os2 k n ret m' os' hp ⟨v1, t1, v2, t2, rfl, hc1, hc2⟩
    (calloc_ok_elim hok)

/-! #### 5.3.3 `free` -/

def FreePost (ptr : Val) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .void ∧ os' = os ∧
  ((ptr = .null ∧ m' = m ∧ FrameMod m m' (fun _ => False)) ∨
    ∃ b, ptr = .ptr b 0 ∧ m.free b = some m' ∧ m'.blocks b = none ∧ FrameMod m m' (· = b))

theorem free_ok_elim {ptr : Val} {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "free" [ptr] m os ret m' os') :
    FreePost ptr m os ret m' os' := by
  generalize hfn : ("free" : String) = fn at h
  generalize hargs : ([ptr] : List Val) = args at h
  cases h with
  | free_null =>
    have hp : ptr = .null := (List.cons.inj hargs).1
    exact ⟨rfl, rfl, Or.inl ⟨hp, rfl, FrameMod.refl m _⟩⟩
  | free_ok b _ _ _ hfree =>
    have hp : ptr = .ptr b 0 := (List.cons.inj hargs).1
    have hnone : m'.blocks b = none := by
      unfold Mem.free at hfree
      cases hb : m.blocks b with
      | none => simp only [hb] at hfree; cases hfree
      | some blk =>
        simp only [hb] at hfree
        by_cases hk : (blk.kind == .heap) = true
        · simp only [hk, ↓reduceIte, Option.some.injEq] at hfree
          rw [← hfree]
          simp only [BEq.refl, ↓reduceIte]
        · have hkf : (blk.kind == .heap) = false := Bool.eq_false_iff.mpr hk
          simp only [hkf, Bool.false_eq_true, ↓reduceIte] at hfree
          cases hfree
    exact ⟨rfl, rfl, Or.inr ⟨b, hp, hfree, hnone, FrameMod.of_free hfree⟩⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem free_null_exists (m : Mem) (os : OSState) :
    ∃ ret m' os', Libc.ExtOk "free" [.null] m os ret m' os' :=
  ⟨.void, m, os, Libc.ExtOk.free_null m os⟩

theorem free_eq_some {m : Mem} {b : BlockId} {blk : Block}
    (hb : m.blocks b = some blk) (hheap : blk.kind = .heap) :
    ∃ m', m.free b = some m' := by
  unfold Mem.free
  have hk : (blk.kind == .heap) = true := beq_iff_eq.mpr hheap
  simp only [hb, hk, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem free_ok_exists {ptr : Val} {m : Mem} (os : OSState)
    (h : ptr = .null ∨ ∃ b, ptr = .ptr b 0 ∧ ∃ blk, m.blocks b = some blk ∧ blk.kind = .heap) :
    ∃ ret m' os', Libc.ExtOk "free" [ptr] m os ret m' os' := by
  rcases h with rfl | ⟨b, rfl, blk, hb, hh⟩
  · exact free_null_exists m os
  · obtain ⟨m', hf⟩ := free_eq_some hb hh
    exact ⟨.void, m', os, Libc.ExtOk.free_ok b m m' os hf⟩

theorem call_free {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {arg : CExpr}
    (hnenv : env.lookup "free" = none)
    (henum : Sem.enumConst? prog.tags "free" = none)
    (hproto : prog.fnProtos "free" = some (.void, [.ptr .void], false))
    (hnfn : prog.fns "free" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [arg] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ vp tp, vs = [(vp, tp)] ∧
        (vp = .null ∨ ∃ b, vp = .ptr b 0 ∧ ∃ blk, m2.blocks b = some blk ∧ blk.kind = .heap))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 vp ret m' os', Pargs vs m2 os2 →
      (∃ tp, vs = [(vp, tp)]) →
      FreePost vp m2 os2 ret m' os' →
      Post ret .void m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "free") [arg]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨vp, tp, rfl, hokp⟩ := hpre vs m2 os2 hp
  have hcast : Sem.castVal m2 (.ptr .void) vp = some vp := by
    rcases hokp with rfl | ⟨b, rfl, _⟩
    · exact castVal_null_eq rfl
    · exact castVal_ptr_eq rfl b 0
  refine ⟨[vp], coerceCallArgs_1 hcast, free_ok_exists os2 hokp, ?_⟩
  intro ret m' os' he
  exact hpost [(vp, tp)] m2 os2 vp ret m' os' hp ⟨tp, rfl⟩ (free_ok_elim he)

/-! #### 5.3.4 `memcpy` -/

def MemcpyPost (bd bs : BlockId) (od os_ : Int64) (n : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .ptr bd od ∧ os' = os ∧
  Libc.ptrDisjointOrEq bd od bs os_ n.toNat = true ∧
  (∃ bytes, m.readBytes bs os_ n.toNat = some bytes ∧ bytes.length = n.toNat ∧
    m.writeBytes bd od bytes = some m') ∧
  FrameMod m m' (· = bd)

theorem memcpy_ok_elim {bd bs : BlockId} {od os_ : Int64} {n : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "memcpy" [.ptr bd od, .ptr bs os_, .int .u64 n] m os ret m' os') :
    MemcpyPost bd bs od os_ n m os ret m' os' := by
  generalize hfn : ("memcpy" : String) = fn at h
  generalize hargs : ([Val.ptr bd od, Val.ptr bs os_, Val.int .u64 n] : List Val) = args at h
  cases h with
  | memcpy_ok bd' bs' od' os_' n_nat bytes _ _ _ hdis hrd hwr =>
    rcases List.cons.inj hargs with ⟨hp1, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hp2, hrest2⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp1
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp2
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hrest2).1).symm
    have hlen : bytes.length = n_nat := readBytes_length hrd
    have hlt : n_nat < ptrDiffLimit := readBytes_len_lt hrd
    have hn : n_nat = n.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hn] at hdis hrd hlen
    exact ⟨rfl, rfl, hdis, ⟨bytes, hrd, hlen, hwr⟩, FrameMod.of_writeBytes hwr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem memcpy_ok_exists {bd bs : BlockId} {od os_ : Int64} {n : BitVec 64}
    {m : Mem} (os : OSState)
    (hdis : Libc.ptrDisjointOrEq bd od bs os_ n.toNat = true)
    (hsrc : ∃ bytes, m.readBytes bs os_ n.toNat = some bytes)
    (hdest : Libc.validWritableRange m bd od n.toNat = true) :
    ∃ ret m' os', Libc.ExtOk "memcpy" [.ptr bd od, .ptr bs os_, .int .u64 n] m os ret m' os' := by
  obtain ⟨bytes, hrd⟩ := hsrc
  obtain ⟨blk, hb, hrw, hin⟩ := validWritableRange_iff.mp hdest
  have hin' : Mem.inBounds blk od bytes.length = true := by rw [readBytes_length hrd]; exact hin
  obtain ⟨m', hwr⟩ := writeBytes_eq_some hb hrw hin'
  exact ⟨.ptr bd od, m', os, by
    simpa only [bitVec_ofNat_toNat_self] using
      Libc.ExtOk.memcpy_ok bd bs od os_ n.toNat bytes m m' os hdis hrd hwr⟩

theorem call_memcpy {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "memcpy" = none)
    (henum : Sem.enumConst? prog.tags "memcpy" = none)
    (hproto : prog.fnProtos "memcpy" = some (.ptr .void, [.ptr .void, .ptr (.const_ .void), .int .u64], false))
    (hnfn : prog.fns "memcpy" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ bd od t1 bs os_ t2 v3 t3 n, vs = [(.ptr bd od, t1), (.ptr bs os_, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n) ∧
        Libc.ptrDisjointOrEq bd od bs os_ n.toNat = true ∧
        (∃ bytes, m2.readBytes bs os_ n.toNat = some bytes) ∧
        Libc.validWritableRange m2 bd od n.toNat = true)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 bd od bs os_ n ret m' os', Pargs vs m2 os2 →
      (∃ t1 t2 v3 t3, vs = [(.ptr bd od, t1), (.ptr bs os_, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n)) →
      MemcpyPost bd bs od os_ n m2 os2 ret m' os' →
      Post ret (.ptr .void) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "memcpy") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨bd, od, t1, bs, os_, t2, v3, t3, n, rfl, hc3, hdis, hsrc, hdst⟩ := hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr .void) (.ptr bd od) = some (.ptr bd od) := castVal_ptr_eq rfl bd od
  have hc2 : Sem.castVal m2 (.ptr (.const_ .void)) (.ptr bs os_) = some (.ptr bs os_) := castVal_ptr_eq rfl bs os_
  refine ⟨[.ptr bd od, .ptr bs os_, .int .u64 n], coerceCallArgs_3 hc1 hc2 hc3,
    memcpy_ok_exists os2 hdis hsrc hdst, ?_⟩
  intro ret m' os' hok
  exact hpost [(.ptr bd od, t1), (.ptr bs os_, t2), (v3, t3)] m2 os2 bd od bs os_ n ret m' os'
    hp ⟨t1, t2, v3, t3, rfl, hc3⟩ (memcpy_ok_elim hok)

/-! #### 5.3.5 `memmove` -/

def MemmovePost (bd bs : BlockId) (od os_ : Int64) (n : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .ptr bd od ∧ os' = os ∧
  (∃ bytes, m.readBytes bs os_ n.toNat = some bytes ∧ bytes.length = n.toNat ∧
    m.writeBytes bd od bytes = some m') ∧
  FrameMod m m' (· = bd)

theorem memmove_ok_elim {bd bs : BlockId} {od os_ : Int64} {n : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "memmove" [.ptr bd od, .ptr bs os_, .int .u64 n] m os ret m' os') :
    MemmovePost bd bs od os_ n m os ret m' os' := by
  generalize hfn : ("memmove" : String) = fn at h
  generalize hargs : ([Val.ptr bd od, Val.ptr bs os_, Val.int .u64 n] : List Val) = args at h
  cases h with
  | memmove_ok bd' bs' od' os_' n_nat bytes _ _ _ hrd hwr =>
    rcases List.cons.inj hargs with ⟨hp1, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hp2, hrest2⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp1
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp2
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hrest2).1).symm
    have hlen : bytes.length = n_nat := readBytes_length hrd
    have hlt : n_nat < ptrDiffLimit := readBytes_len_lt hrd
    have hn : n_nat = n.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hn] at hrd hlen
    exact ⟨rfl, rfl, ⟨bytes, hrd, hlen, hwr⟩, FrameMod.of_writeBytes hwr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem memmove_ok_exists {bd bs : BlockId} {od os_ : Int64} {n : BitVec 64}
    {m : Mem} (os : OSState)
    (hsrc : ∃ bytes, m.readBytes bs os_ n.toNat = some bytes)
    (hdest : Libc.validWritableRange m bd od n.toNat = true) :
    ∃ ret m' os', Libc.ExtOk "memmove" [.ptr bd od, .ptr bs os_, .int .u64 n] m os ret m' os' := by
  obtain ⟨bytes, hrd⟩ := hsrc
  obtain ⟨blk, hb, hrw, hin⟩ := validWritableRange_iff.mp hdest
  have hin' : Mem.inBounds blk od bytes.length = true := by rw [readBytes_length hrd]; exact hin
  obtain ⟨m', hwr⟩ := writeBytes_eq_some hb hrw hin'
  exact ⟨.ptr bd od, m', os, by
    simpa only [bitVec_ofNat_toNat_self] using
      Libc.ExtOk.memmove_ok bd bs od os_ n.toNat bytes m m' os hrd hwr⟩

theorem call_memmove {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "memmove" = none)
    (henum : Sem.enumConst? prog.tags "memmove" = none)
    (hproto : prog.fnProtos "memmove" = some (.ptr .void, [.ptr .void, .ptr (.const_ .void), .int .u64], false))
    (hnfn : prog.fns "memmove" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ bd od t1 bs os_ t2 v3 t3 n, vs = [(.ptr bd od, t1), (.ptr bs os_, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n) ∧
        (∃ bytes, m2.readBytes bs os_ n.toNat = some bytes) ∧
        Libc.validWritableRange m2 bd od n.toNat = true)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 bd od bs os_ n ret m' os', Pargs vs m2 os2 →
      (∃ t1 t2 v3 t3, vs = [(.ptr bd od, t1), (.ptr bs os_, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n)) →
      MemmovePost bd bs od os_ n m2 os2 ret m' os' →
      Post ret (.ptr .void) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "memmove") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨bd, od, t1, bs, os_, t2, v3, t3, n, rfl, hc3, hsrc, hdst⟩ := hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr .void) (.ptr bd od) = some (.ptr bd od) := castVal_ptr_eq rfl bd od
  have hc2 : Sem.castVal m2 (.ptr (.const_ .void)) (.ptr bs os_) = some (.ptr bs os_) := castVal_ptr_eq rfl bs os_
  refine ⟨[.ptr bd od, .ptr bs os_, .int .u64 n], coerceCallArgs_3 hc1 hc2 hc3,
    memmove_ok_exists os2 hsrc hdst, ?_⟩
  intro ret m' os' hok
  exact hpost [(.ptr bd od, t1), (.ptr bs os_, t2), (v3, t3)] m2 os2 bd od bs os_ n ret m' os'
    hp ⟨t1, t2, v3, t3, rfl, hc3⟩ (memmove_ok_elim hok)

/-! #### 5.3.6 `memset` -/

def MemsetPost (bd : BlockId) (od : Int64) (c : BitVec 32) (n : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ret = .ptr bd od ∧ os' = os ∧
  m.writeBytes bd od (List.replicate n.toNat (.byte (UInt8.ofNat (c.toNat % 256)))) = some m' ∧
  FrameMod m m' (· = bd)

theorem memset_ok_elim {bd : BlockId} {od : Int64} {c : BitVec 32} {n : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "memset" [.ptr bd od, .int .i32 c, .int .u64 n] m os ret m' os') :
    MemsetPost bd od c n m os ret m' os' := by
  generalize hfn : ("memset" : String) = fn at h
  generalize hargs : ([Val.ptr bd od, Val.int .i32 c, Val.int .u64 n] : List Val) = args at h
  cases h with
  | memset_ok bd' od' c' n_nat _ _ _ hwr =>
    rcases List.cons.inj hargs with ⟨hp1, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hc2, hrest2⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp1
    have hce : c = c' := val_int_eq hc2
    subst hce
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hrest2).1).symm
    have hlt : n_nat < ptrDiffLimit := by
      have hbl := writeBytes_len_lt hwr
      rw [List.length_replicate] at hbl
      exact hbl
    have hn : n_nat = n.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hn] at hwr
    exact ⟨rfl, rfl, hwr, FrameMod.of_writeBytes hwr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem memset_ok_exists {bd : BlockId} {od : Int64} (c : BitVec 32) {n : BitVec 64}
    {m : Mem} (os : OSState)
    (hdest : Libc.validWritableRange m bd od n.toNat = true) :
    ∃ ret m' os', Libc.ExtOk "memset" [.ptr bd od, .int .i32 c, .int .u64 n] m os ret m' os' := by
  obtain ⟨blk, hb, hrw, hin⟩ := validWritableRange_iff.mp hdest
  let bs := List.replicate n.toNat (MemByte.byte (UInt8.ofNat (c.toNat % 256)))
  have hin' : Mem.inBounds blk od bs.length = true := by
    simp only [bs, List.length_replicate]
    exact hin
  obtain ⟨m', hwr⟩ := writeBytes_eq_some hb hrw hin'
  exact ⟨.ptr bd od, m', os, by
    simpa only [bitVec_ofNat_toNat_self] using Libc.ExtOk.memset_ok bd od c n.toNat m m' os hwr⟩

theorem call_memset {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "memset" = none)
    (henum : Sem.enumConst? prog.tags "memset" = none)
    (hproto : prog.fnProtos "memset" = some (.ptr .void, [.ptr .void, .int .i32, .int .u64], false))
    (hnfn : prog.fns "memset" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ bd od t1 v2 t2 c v3 t3 n, vs = [(.ptr bd od, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v2 = some (.int .i32 c) ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n) ∧
        Libc.validWritableRange m2 bd od n.toNat = true)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 bd od c n ret m' os', Pargs vs m2 os2 →
      (∃ t1 v2 t2 v3 t3, vs = [(.ptr bd od, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v2 = some (.int .i32 c) ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n)) →
      MemsetPost bd od c n m2 os2 ret m' os' →
      Post ret (.ptr .void) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "memset") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨bd, od, t1, v2, t2, c, v3, t3, n, rfl, hc2, hc3, hdst⟩ := hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr .void) (.ptr bd od) = some (.ptr bd od) := castVal_ptr_eq rfl bd od
  refine ⟨[.ptr bd od, .int .i32 c, .int .u64 n], coerceCallArgs_3 hc1 hc2 hc3,
    memset_ok_exists c os2 hdst, ?_⟩
  intro ret m' os' hok
  exact hpost [(.ptr bd od, t1), (v2, t2), (v3, t3)] m2 os2 bd od c n ret m' os'
    hp ⟨t1, v2, t2, v3, t3, rfl, hc2, hc3⟩ (memset_ok_elim hok)

/-! #### 5.3.7 `memcmp` -/

def MemcmpPost (b1 b2 : BlockId) (o1 o2 : Int64) (n : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  m' = m ∧ os' = os ∧
  ∃ raw1 raw2 bs1 bs2,
    m.readBytes b1 o1 n.toNat = some raw1 ∧ Libc.allConcreteBytes raw1 = some bs1 ∧
    m.readBytes b2 o2 n.toNat = some raw2 ∧ Libc.allConcreteBytes raw2 = some bs2 ∧
    ret = .int .i32 (BitVec.ofInt 32 (Libc.memcmpBytes bs1 bs2).toInt)

theorem memcmp_ok_elim {b1 b2 : BlockId} {o1 o2 : Int64} {n : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "memcmp" [.ptr b1 o1, .ptr b2 o2, .int .u64 n] m os ret m' os') :
    MemcmpPost b1 b2 o1 o2 n m os ret m' os' := by
  generalize hfn : ("memcmp" : String) = fn at h
  generalize hargs : ([Val.ptr b1 o1, Val.ptr b2 o2, Val.int .u64 n] : List Val) = args at h
  cases h with
  | memcmp_ok b1' b2' o1' o2' n_nat raw1 raw2 bs1 bs2 _ _ hr1 hc1 hr2 hc2 =>
    rcases List.cons.inj hargs with ⟨hp1, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hp2, hrest2⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp1
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp2
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hrest2).1).symm
    have hlt : n_nat < ptrDiffLimit := readBytes_len_lt hr1
    have hn : n_nat = n.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hn] at hr1 hr2
    exact ⟨rfl, rfl, raw1, raw2, bs1, bs2, hr1, hc1, hr2, hc2, rfl⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem memcmp_ok_exists {b1 b2 : BlockId} {o1 o2 : Int64} {n : BitVec 64}
    {m : Mem} (os : OSState)
    {raw1 raw2 : List MemByte} {bs1 bs2 : List UInt8}
    (hr1 : m.readBytes b1 o1 n.toNat = some raw1) (hc1 : Libc.allConcreteBytes raw1 = some bs1)
    (hr2 : m.readBytes b2 o2 n.toNat = some raw2) (hc2 : Libc.allConcreteBytes raw2 = some bs2) :
    ∃ ret m' os', Libc.ExtOk "memcmp" [.ptr b1 o1, .ptr b2 o2, .int .u64 n] m os ret m' os' :=
  ⟨.int .i32 (BitVec.ofInt 32 (Libc.memcmpBytes bs1 bs2).toInt), m, os, by
    simpa only [bitVec_ofNat_toNat_self] using
      Libc.ExtOk.memcmp_ok b1 b2 o1 o2 n.toNat raw1 raw2 bs1 bs2 m os hr1 hc1 hr2 hc2⟩

theorem call_memcmp {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "memcmp" = none)
    (henum : Sem.enumConst? prog.tags "memcmp" = none)
    (hproto : prog.fnProtos "memcmp" = some (.int .i32, [.ptr (.const_ .void), .ptr (.const_ .void), .int .u64], false))
    (hnfn : prog.fns "memcmp" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ b1 o1 t1 b2 o2 t2 v3 t3 n raw1 raw2 bs1 bs2,
        vs = [(.ptr b1 o1, t1), (.ptr b2 o2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n) ∧
        m2.readBytes b1 o1 n.toNat = some raw1 ∧ Libc.allConcreteBytes raw1 = some bs1 ∧
        m2.readBytes b2 o2 n.toNat = some raw2 ∧ Libc.allConcreteBytes raw2 = some bs2)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 b1 o1 b2 o2 n ret m' os', Pargs vs m2 os2 →
      (∃ t1 t2 v3 t3, vs = [(.ptr b1 o1, t1), (.ptr b2 o2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n)) →
      MemcmpPost b1 b2 o1 o2 n m2 os2 ret m' os' →
      Post ret (.int .i32) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "memcmp") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨b1, o1, t1, b2, o2, t2, v3, t3, n, raw1, raw2, bs1, bs2, rfl, hc3, hr1, hcc1, hr2, hcc2⟩ :=
    hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr (.const_ .void)) (.ptr b1 o1) = some (.ptr b1 o1) := castVal_ptr_eq rfl b1 o1
  have hc2 : Sem.castVal m2 (.ptr (.const_ .void)) (.ptr b2 o2) = some (.ptr b2 o2) := castVal_ptr_eq rfl b2 o2
  refine ⟨[.ptr b1 o1, .ptr b2 o2, .int .u64 n], coerceCallArgs_3 hc1 hc2 hc3,
    memcmp_ok_exists os2 hr1 hcc1 hr2 hcc2, ?_⟩
  intro ret m' os' hok
  exact hpost [(.ptr b1 o1, t1), (.ptr b2 o2, t2), (v3, t3)] m2 os2 b1 o1 b2 o2 n ret m' os'
    hp ⟨t1, t2, v3, t3, rfl, hc3⟩ (memcmp_ok_elim hok)

/-! #### 5.3.8 `strlen` -/

def StrlenPost (b : BlockId) (off : Int64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  m' = m ∧ os' = os ∧ ∃ len, m.strlenAt b off = some len ∧ ret = .int .u64 (BitVec.ofNat 64 len)

theorem strlen_ok_elim {b : BlockId} {off : Int64} {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "strlen" [.ptr b off] m os ret m' os') :
    StrlenPost b off m os ret m' os' := by
  generalize hfn : ("strlen" : String) = fn at h
  generalize hargs : ([Val.ptr b off] : List Val) = args at h
  cases h with
  | strlen_ok _ _ len _ _ hlen =>
    obtain ⟨rfl, rfl⟩ := val_ptr_eq (List.cons.inj hargs).1
    exact ⟨rfl, rfl, len, hlen, rfl⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem strlen_ok_exists {b : BlockId} {off : Int64} {m : Mem} (os : OSState) {len : Nat}
    (hlen : m.strlenAt b off = some len) :
    ∃ ret m' os', Libc.ExtOk "strlen" [.ptr b off] m os ret m' os' :=
  ⟨.int .u64 (BitVec.ofNat 64 len), m, os, Libc.ExtOk.strlen_ok b off len m os hlen⟩

theorem call_strlen {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {arg : CExpr}
    (hnenv : env.lookup "strlen" = none)
    (henum : Sem.enumConst? prog.tags "strlen" = none)
    (hproto : prog.fnProtos "strlen" = some (.int .u64, [.ptr (.const_ (.int .i8))], false))
    (hnfn : prog.fns "strlen" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [arg] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ b off t1 len, vs = [(.ptr b off, t1)] ∧ m2.strlenAt b off = some len)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 b off ret m' os', Pargs vs m2 os2 →
      (∃ t1, vs = [(.ptr b off, t1)]) →
      StrlenPost b off m2 os2 ret m' os' →
      Post ret (.int .u64) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "strlen") [arg]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨b, off, t1, len, rfl, hlen⟩ := hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr (.const_ (.int .i8))) (.ptr b off) = some (.ptr b off) :=
    castVal_ptr_eq rfl b off
  refine ⟨[.ptr b off], coerceCallArgs_1 hc1, strlen_ok_exists os2 hlen, ?_⟩
  intro ret m' os' hok
  exact hpost [(.ptr b off, t1)] m2 os2 b off ret m' os' hp ⟨t1, rfl⟩ (strlen_ok_elim hok)

/-! #### 5.3.9 `memchr` -/

def MemchrPost (b : BlockId) (off : Int64) (c : BitVec 32) (n : BitVec 64)
    (m : Mem) (os : OSState) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  m' = m ∧ os' = os ∧
  Libc.memchrStep m b off (UInt8.ofNat (c.toNat % 256)) n.toNat = some ret ∧
  (ret = .null ∨ ∃ i < n.toNat, ret = .ptr b (Int64.ofInt (off.toInt + i)))

theorem memchr_ok_elim {b : BlockId} {off : Int64} {c : BitVec 32} {n : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "memchr" [.ptr b off, .int .i32 c, .int .u64 n] m os ret m' os') :
    MemchrPost b off c n m os ret m' os' := by
  generalize hfn : ("memchr" : String) = fn at h
  generalize hargs : ([Val.ptr b off, Val.int .i32 c, Val.int .u64 n] : List Val) = args at h
  cases h with
  | memchr_ok _ _ c' n_nat _ _ _ hres =>
    rcases List.cons.inj hargs with ⟨hp1, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hc2, hrest2⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp1
    have hce : c = c' := val_int_eq hc2
    subst hce
    have heq : BitVec.ofNat 64 n_nat = n := (val_int_eq (List.cons.inj hrest2).1).symm
    obtain ⟨blk, _, hin, hcases⟩ := memchrStep_inv hres
    have hlt : n_nat < ptrDiffLimit := inBounds_lt_ptrDiffLimit hin
    have hn : n_nat = n.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hn] at hres hcases
    refine ⟨rfl, rfl, hres, ?_⟩
    rcases hcases with rfl | ⟨i, hlti, hr, _⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hlti, hr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem memchr_ok_exists {b : BlockId} {off : Int64} {c : BitVec 32} {n : BitVec 64}
    {m : Mem} (os : OSState) {ret0 : Val}
    (hres : Libc.memchrStep m b off (UInt8.ofNat (c.toNat % 256)) n.toNat = some ret0) :
    ∃ ret m' os', Libc.ExtOk "memchr" [.ptr b off, .int .i32 c, .int .u64 n] m os ret m' os' :=
  ⟨ret0, m, os, by
    simpa only [bitVec_ofNat_toNat_self] using Libc.ExtOk.memchr_ok b off c n.toNat ret0 m os hres⟩

theorem call_memchr {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "memchr" = none)
    (henum : Sem.enumConst? prog.tags "memchr" = none)
    (hproto : prog.fnProtos "memchr" = some (.ptr .void, [.ptr (.const_ .void), .int .i32, .int .u64], false))
    (hnfn : prog.fns "memchr" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ b off t1 v2 t2 c v3 t3 n ret0, vs = [(.ptr b off, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v2 = some (.int .i32 c) ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n) ∧
        Libc.memchrStep m2 b off (UInt8.ofNat (c.toNat % 256)) n.toNat = some ret0)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 b off c n ret m' os', Pargs vs m2 os2 →
      (∃ t1 v2 t2 v3 t3, vs = [(.ptr b off, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v2 = some (.int .i32 c) ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 n)) →
      MemchrPost b off c n m2 os2 ret m' os' →
      Post ret (.ptr .void) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "memchr") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨b, off, t1, v2, t2, c, v3, t3, n, ret0, rfl, hc2, hc3, hres⟩ := hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr (.const_ .void)) (.ptr b off) = some (.ptr b off) := castVal_ptr_eq rfl b off
  refine ⟨[.ptr b off, .int .i32 c, .int .u64 n], coerceCallArgs_3 hc1 hc2 hc3,
    memchr_ok_exists os2 hres, ?_⟩
  intro ret m' os' hok
  exact hpost [(.ptr b off, t1), (v2, t2), (v3, t3)] m2 os2 b off c n ret m' os'
    hp ⟨t1, v2, t2, v3, t3, rfl, hc2, hc3⟩ (memchr_ok_elim hok)

/-! #### 5.3.10 `open` -/

def OpenPost (b : BlockId) (off : Int64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  (∃ plen, m.strlenAt b off = some plen) ∧
  (∃ (fd e : Int32), -1 ≤ fd.toInt ∧ Libc.writeErrno m os e = some m' ∧
    ret = .int .i32 (BitVec.ofInt 32 fd.toInt)) ∧
  FrameMod m m' (· = os.errnoBlk)

theorem open_ok_elim {b : BlockId} {off : Int64} {flags : BitVec 32} {rest : List Val}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "open" (.ptr b off :: .int .i32 flags :: rest) m os ret m' os') :
    OpenPost b off m os ret m' os' := by
  generalize hfn : ("open" : String) = fn at h
  generalize hargs : (Val.ptr b off :: Val.int .i32 flags :: rest) = args at h
  cases h with
  | open_ok _ _ plen _ _ fd e _ _ _ hpath hfd herr =>
    obtain ⟨rfl, rfl⟩ := val_ptr_eq (List.cons.inj hargs).1
    exact ⟨rfl, ⟨plen, hpath⟩, ⟨fd, e, hfd, herr, rfl⟩, frameMod_of_writeErrno herr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem open_ok_exists {b : BlockId} {off : Int64} (flags : BitVec 32) (rest : List Val)
    {m : Mem} (os : OSState) {plen : Nat}
    (hpath : m.strlenAt b off = some plen)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "open" (.ptr b off :: .int .i32 flags :: rest) m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i32 (BitVec.ofInt 32 (-1 : Int32).toInt), m', os,
    Libc.ExtOk.open_ok b off plen flags rest (-1) 0 m m' os hpath (by decide) herr⟩

theorem call_open {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 : CExpr} {restArgs : List CExpr}
    (hnenv : env.lookup "open" = none)
    (henum : Sem.enumConst? prog.tags "open" = none)
    (hproto : prog.fnProtos "open" = some (.int .i32, [.ptr (.const_ (.int .i8)), .int .i32], true))
    (hnfn : prog.fns "open" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] (a1 :: a2 :: restArgs) Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ b off t1 v2 t2 flags rest plen blk, vs = (.ptr b off, t1) :: (v2, t2) :: rest ∧
        Sem.castVal m2 (.int .i32) v2 = some (.int .i32 flags) ∧
        m2.strlenAt b off = some plen ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 b off ret m' os', Pargs vs m2 os2 →
      (∃ t1 v2 t2 rest, vs = (.ptr b off, t1) :: (v2, t2) :: rest) →
      OpenPost b off m2 os2 ret m' os' →
      Post ret (.int .i32) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "open") (a1 :: a2 :: restArgs)) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨b, off, t1, v2, t2, flags, rest, plen, blk, rfl, hc2, hpath, herrBlk, hrw, hsz⟩ :=
    hpre vs m2 os2 hp
  have hc1 : Sem.castVal m2 (.ptr (.const_ (.int .i8))) (.ptr b off) = some (.ptr b off) :=
    castVal_ptr_eq rfl b off
  refine ⟨.ptr b off :: .int .i32 flags :: rest.map (fun (v, _) => Sem.promoteVariadicArg v),
    coerceCallArgs_variadic_2 hc1 hc2, open_ok_exists flags _ os2 hpath herrBlk hrw hsz, ?_⟩
  intro ret m' os' hok
  exact hpost ((.ptr b off, t1) :: (v2, t2) :: rest) m2 os2 b off ret m' os' hp
    ⟨t1, v2, t2, rest, rfl⟩ (open_ok_elim hok)

/-! #### 5.3.11 `close` -/

def ClosePost (m : Mem) (os : OSState) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  (∃ (r e : Int32), (r = 0 ∨ r = -1) ∧ Libc.writeErrno m os e = some m' ∧
    ret = .int .i32 (BitVec.ofInt 32 r.toInt)) ∧
  FrameMod m m' (· = os.errnoBlk)

theorem close_ok_elim {fd : BitVec 32} {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "close" [.int .i32 fd] m os ret m' os') :
    ClosePost m os ret m' os' := by
  generalize hfn : ("close" : String) = fn at h
  generalize hargs : ([Val.int .i32 fd] : List Val) = args at h
  cases h with
  | close_ok _ r e _ _ _ hret herr =>
    exact ⟨rfl, ⟨r, e, hret, herr, rfl⟩, frameMod_of_writeErrno herr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem close_ok_exists (fd : BitVec 32) {m : Mem} (os : OSState)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "close" [.int .i32 fd] m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m', os,
    Libc.ExtOk.close_ok fd 0 0 m m' os (Or.inl rfl) herr⟩

theorem call_close {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {arg : CExpr}
    (hnenv : env.lookup "close" = none)
    (henum : Sem.enumConst? prog.tags "close" = none)
    (hproto : prog.fnProtos "close" = some (.int .i32, [.int .i32], false))
    (hnfn : prog.fns "close" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [arg] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 fd blk, vs = [(v1, t1)] ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 ret m' os', Pargs vs m2 os2 →
      ClosePost m2 os2 ret m' os' →
      Post ret (.int .i32) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "close") [arg]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, fd, blk, rfl, hc1, herrBlk, hrw, hsz⟩ := hpre vs m2 os2 hp
  refine ⟨[.int .i32 fd], coerceCallArgs_1 hc1, close_ok_exists fd os2 herrBlk hrw hsz, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1)] m2 os2 ret m' os' hp (close_ok_elim hok)

/-! #### 5.3.12 `fcntl` -/

def FcntlPost (m : Mem) (os : OSState) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  (∃ (r e : Int32), Libc.writeErrno m os e = some m' ∧
    ret = .int .i32 (BitVec.ofInt 32 r.toInt)) ∧
  FrameMod m m' (· = os.errnoBlk)

theorem fcntl_ok_elim {fd cmd : BitVec 32} {rest : List Val}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "fcntl" (.int .i32 fd :: .int .i32 cmd :: rest) m os ret m' os') :
    FcntlPost m os ret m' os' := by
  generalize hfn : ("fcntl" : String) = fn at h
  generalize hargs : (Val.int .i32 fd :: Val.int .i32 cmd :: rest) = args at h
  cases h with
  | fcntl_ok _ _ _ r e _ _ _ herr =>
    exact ⟨rfl, ⟨r, e, herr, rfl⟩, frameMod_of_writeErrno herr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem fcntl_ok_exists (fd cmd : BitVec 32) (rest : List Val) {m : Mem} (os : OSState)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "fcntl" (.int .i32 fd :: .int .i32 cmd :: rest) m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m', os,
    Libc.ExtOk.fcntl_ok fd cmd rest 0 0 m m' os herr⟩

theorem call_fcntl {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 : CExpr} {restArgs : List CExpr}
    (hnenv : env.lookup "fcntl" = none)
    (henum : Sem.enumConst? prog.tags "fcntl" = none)
    (hproto : prog.fnProtos "fcntl" = some (.int .i32, [.int .i32, .int .i32], true))
    (hnfn : prog.fns "fcntl" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] (a1 :: a2 :: restArgs) Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 fd cmd rest blk, vs = (v1, t1) :: (v2, t2) :: rest ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        Sem.castVal m2 (.int .i32) v2 = some (.int .i32 cmd) ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 ret m' os', Pargs vs m2 os2 →
      FcntlPost m2 os2 ret m' os' →
      Post ret (.int .i32) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "fcntl") (a1 :: a2 :: restArgs)) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, v2, t2, fd, cmd, rest, blk, rfl, hc1, hc2, herrBlk, hrw, hsz⟩ := hpre vs m2 os2 hp
  refine ⟨.int .i32 fd :: .int .i32 cmd :: rest.map (fun (v, _) => Sem.promoteVariadicArg v),
    coerceCallArgs_variadic_2 hc1 hc2, fcntl_ok_exists fd cmd _ os2 herrBlk hrw hsz, ?_⟩
  intro ret m' os' hok
  exact hpost ((v1, t1) :: (v2, t2) :: rest) m2 os2 ret m' os' hp (fcntl_ok_elim hok)

/-! #### 5.3.13 & 5.3.14 `lseek` & `lseek64` -/

def LseekPost (m : Mem) (os : OSState) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  (∃ (r : Int64) (e : Int32), Libc.writeErrno m os e = some m' ∧
    ret = .int .i64 (BitVec.ofInt 64 r.toInt)) ∧
  FrameMod m m' (· = os.errnoBlk)

theorem lseek_family_ok_elim {fn : String} (hfn : fn = "lseek" ∨ fn = "lseek64")
    {fd : BitVec 32} {off : BitVec 64} {whence : BitVec 32}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk fn [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os') :
    LseekPost m os ret m' os' := by
  generalize hargs : ([Val.int .i32 fd, Val.int .i64 off, Val.int .i32 whence] : List Val) = args at h
  cases h with
  | lseek_ok _ _ _ _ _ r e _ _ _ herr =>
    exact ⟨rfl, ⟨r, e, herr, rfl⟩, frameMod_of_writeErrno herr⟩
  | printf_zero _ hp _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact False.elim (ne_or_or_elim hfn hp (by decide) (by decide) (by decide) (by decide))
  | printf_ok _ hp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact False.elim (ne_or_or_elim hfn hp (by decide) (by decide) (by decide) (by decide))
  | _ => rcases hfn with h1 | h1 <;> exact absurd h1 (by decide)

theorem lseek_ok_elim {fd : BitVec 32} {off : BitVec 64} {whence : BitVec 32}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "lseek" [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os') :
    LseekPost m os ret m' os' :=
  lseek_family_ok_elim (Or.inl rfl) h

theorem lseek64_ok_elim {fd : BitVec 32} {off : BitVec 64} {whence : BitVec 32}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "lseek64" [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os') :
    LseekPost m os ret m' os' :=
  lseek_family_ok_elim (Or.inr rfl) h

theorem lseek_family_ok_exists {fn : String} (hfn : fn = "lseek" ∨ fn = "lseek64")
    (fd : BitVec 32) (off : BitVec 64) (whence : BitVec 32) {m : Mem} (os : OSState)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk fn [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i64 (BitVec.ofInt 64 (0 : Int64).toInt), m', os,
    Libc.ExtOk.lseek_ok fn hfn fd off whence 0 0 m m' os herr⟩

theorem lseek_ok_exists (fd : BitVec 32) (off : BitVec 64) (whence : BitVec 32) {m : Mem} (os : OSState)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "lseek" [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os' :=
  lseek_family_ok_exists (Or.inl rfl) fd off whence os herrBlk hrw hsz

theorem lseek64_ok_exists (fd : BitVec 32) (off : BitVec 64) (whence : BitVec 32) {m : Mem} (os : OSState)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "lseek64" [.int .i32 fd, .int .i64 off, .int .i32 whence] m os ret m' os' :=
  lseek_family_ok_exists (Or.inr rfl) fd off whence os herrBlk hrw hsz

private theorem call_lseek_family {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {fn : String} (hfn : fn = "lseek" ∨ fn = "lseek64")
    {a1 a2 a3 : CExpr}
    (hnenv : env.lookup fn = none)
    (henum : Sem.enumConst? prog.tags fn = none)
    (hproto : prog.fnProtos fn = some (.int .i64, [.int .i32, .int .i64, .int .i32], false))
    (hnfn : prog.fns fn = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 v3 t3 fd off whence blk, vs = [(v1, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        Sem.castVal m2 (.int .i64) v2 = some (.int .i64 off) ∧
        Sem.castVal m2 (.int .i32) v3 = some (.int .i32 whence) ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 ret m' os', Pargs vs m2 os2 →
      LseekPost m2 os2 ret m' os' →
      Post ret (.int .i64) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var fn) [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, v2, t2, v3, t3, fd, off, whence, blk, rfl, hc1, hc2, hc3, herrBlk, hrw, hsz⟩ :=
    hpre vs m2 os2 hp
  refine ⟨[.int .i32 fd, .int .i64 off, .int .i32 whence], coerceCallArgs_3 hc1 hc2 hc3,
    lseek_family_ok_exists hfn fd off whence os2 herrBlk hrw hsz, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1), (v2, t2), (v3, t3)] m2 os2 ret m' os' hp (lseek_family_ok_elim hfn hok)

theorem call_lseek {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "lseek" = none)
    (henum : Sem.enumConst? prog.tags "lseek" = none)
    (hproto : prog.fnProtos "lseek" = some (.int .i64, [.int .i32, .int .i64, .int .i32], false))
    (hnfn : prog.fns "lseek" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 v3 t3 fd off whence blk, vs = [(v1, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        Sem.castVal m2 (.int .i64) v2 = some (.int .i64 off) ∧
        Sem.castVal m2 (.int .i32) v3 = some (.int .i32 whence) ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 ret m' os', Pargs vs m2 os2 →
      LseekPost m2 os2 ret m' os' →
      Post ret (.int .i64) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "lseek") [a1, a2, a3]) Post :=
  call_lseek_family (Or.inl rfl) hnenv henum hproto hnfn hargs hpre hpost

theorem call_lseek64 {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "lseek64" = none)
    (henum : Sem.enumConst? prog.tags "lseek64" = none)
    (hproto : prog.fnProtos "lseek64" = some (.int .i64, [.int .i32, .int .i64, .int .i32], false))
    (hnfn : prog.fns "lseek64" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 v3 t3 fd off whence blk, vs = [(v1, t1), (v2, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        Sem.castVal m2 (.int .i64) v2 = some (.int .i64 off) ∧
        Sem.castVal m2 (.int .i32) v3 = some (.int .i32 whence) ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 ret m' os', Pargs vs m2 os2 →
      LseekPost m2 os2 ret m' os' →
      Post ret (.int .i64) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "lseek64") [a1, a2, a3]) Post :=
  call_lseek_family (Or.inr rfl) hnenv henum hproto hnfn hargs hpre hpost

/-! #### 5.3.15 `read` -/

def ReadPost (b : BlockId) (off : Int64) (cnt : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os'.errnoBlk = os.errnoBlk ∧
  os'.strerrorBlk = os.strerrorBlk ∧
  FrameMod m m' (fun x => x = b ∨ x = os.errnoBlk) ∧
  ((ret = .int .i64 (BitVec.ofInt 64 (-1)) ∧ os' = os ∧
      (∃ e, Libc.writeErrno m os e = some m') ∧
      FrameMod m m' (· = os.errnoBlk)) ∨
    (∃ (k : Nat) (bs : List UInt8) (e : Int32) (m1 : Mem),
      k ≤ min cnt.toNat (2 ^ 63 - 1) ∧ bs.length = k ∧
      (match os.readBudget with | some rem => k ≤ rem | none => true) ∧
      m.writeBytes b off (bs.map MemByte.byte) = some m1 ∧
      Libc.writeErrno m1 os e = some m' ∧
      ret = .int .i64 (BitVec.ofNat 64 k) ∧
      os' = { os with readBudget := os.readBudget.map (· - k) }))

theorem read_ok_elim {fd : BitVec 32} {b : BlockId} {off : Int64} {cnt : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "read" [.int .i32 fd, .ptr b off, .int .u64 cnt] m os ret m' os') :
    ReadPost b off cnt m os ret m' os' := by
  generalize hfn : ("read" : String) = fn at h
  generalize hargs : ([Val.int .i32 fd, Val.ptr b off, Val.int .u64 cnt] : List Val) = args at h
  cases h with
  | read_fail _ _ _ _ e _ _ _ _ herr =>
    have hfr := frameMod_of_writeErrno herr
    exact ⟨rfl, rfl, hfr.mono (fun _ hx => Or.inr hx), Or.inl ⟨rfl, rfl, ⟨e, herr⟩, hfr⟩⟩
  | read_ok _ _ _ cnt_nat k bs e _ m1 _ _ hbuf hk hlen hbud hwr herr =>
    rcases List.cons.inj hargs with ⟨_, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hp2, hrest2⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp2
    have heq : BitVec.ofNat 64 cnt_nat = cnt := (val_int_eq (List.cons.inj hrest2).1).symm
    obtain ⟨blk, _, _, hin⟩ := validWritableRange_iff.mp hbuf
    have hlt : cnt_nat < ptrDiffLimit := inBounds_lt_ptrDiffLimit hin
    have hcnt : cnt_nat = cnt.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hcnt] at hk
    have hfr1 := FrameMod.of_writeBytes hwr
    have hfr2 := frameMod_of_writeErrno herr
    have hfr := (hfr1.trans hfr2).mono (fun x hx => hx)
    refine ⟨rfl, rfl, hfr, Or.inr ⟨k, bs, e, m1, hk, hlen, hbud, hwr, herr, rfl, rfl⟩⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem read_ok_exists (fd : BitVec 32) {b : BlockId} {off : Int64} {cnt : BitVec 64}
    {m : Mem} (os : OSState)
    (hbuf : Libc.validWritableRange m b off cnt.toNat = true)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "read" [.int .i32 fd, .ptr b off, .int .u64 cnt] m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i64 (BitVec.ofInt 64 (-1)), m', os, by
    simpa only [bitVec_ofNat_toNat_self] using Libc.ExtOk.read_fail fd b off cnt.toNat 0 m m' os hbuf herr⟩

theorem call_read {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "read" = none)
    (henum : Sem.enumConst? prog.tags "read" = none)
    (hproto : prog.fnProtos "read" = some (.int .i64, [.int .i32, .ptr .void, .int .u64], false))
    (hnfn : prog.fns "read" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 b off t2 v3 t3 fd cnt blk, vs = [(v1, t1), (.ptr b off, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 cnt) ∧
        Libc.validWritableRange m2 b off cnt.toNat = true ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 b off cnt ret m' os', Pargs vs m2 os2 →
      (∃ v1 t1 t2 v3 t3, vs = [(v1, t1), (.ptr b off, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 cnt)) →
      ReadPost b off cnt m2 os2 ret m' os' →
      Post ret (.int .i64) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "read") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, b, off, t2, v3, t3, fd, cnt, blk, rfl, hc1, hc3, hbuf, herrBlk, hrw, hsz⟩ :=
    hpre vs m2 os2 hp
  have hc2 : Sem.castVal m2 (.ptr .void) (.ptr b off) = some (.ptr b off) := castVal_ptr_eq rfl b off
  refine ⟨[.int .i32 fd, .ptr b off, .int .u64 cnt], coerceCallArgs_3 hc1 hc2 hc3,
    read_ok_exists fd os2 hbuf herrBlk hrw hsz, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1), (.ptr b off, t2), (v3, t3)] m2 os2 b off cnt ret m' os' hp
    ⟨v1, t1, t2, v3, t3, rfl, hc3⟩ (read_ok_elim hok)

/-! #### 5.3.16 `write` -/

def WritePost (cnt : BitVec 64) (m : Mem) (os : OSState)
    (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  (∃ e, Libc.writeErrno m os e = some m') ∧
  FrameMod m m' (· = os.errnoBlk) ∧
  (ret = .int .i64 (BitVec.ofInt 64 (-1)) ∨
    ∃ k : Nat, (cnt.toNat = 0 → k = 0) ∧
      (cnt.toNat > 0 → 1 ≤ k ∧ k ≤ min cnt.toNat (2 ^ 63 - 1)) ∧
      ret = .int .i64 (BitVec.ofNat 64 k))

theorem write_ok_elim {fd : BitVec 32} {b : BlockId} {off : Int64} {cnt : BitVec 64}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "write" [.int .i32 fd, .ptr b off, .int .u64 cnt] m os ret m' os') :
    WritePost cnt m os ret m' os' := by
  generalize hfn : ("write" : String) = fn at h
  generalize hargs : ([Val.int .i32 fd, Val.ptr b off, Val.int .u64 cnt] : List Val) = args at h
  cases h with
  | write_fail _ _ _ _ e _ _ _ _ herr =>
    exact ⟨rfl, ⟨e, herr⟩, frameMod_of_writeErrno herr, Or.inl rfl⟩
  | write_ok _ _ _ cnt_nat k e _ _ _ hbuf hk herr =>
    rcases List.cons.inj hargs with ⟨_, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨_, hrest2⟩
    have heq : BitVec.ofNat 64 cnt_nat = cnt := (val_int_eq (List.cons.inj hrest2).1).symm
    obtain ⟨blk, _, hin⟩ := validReadableRange_iff.mp hbuf
    have hlt : cnt_nat < ptrDiffLimit := inBounds_lt_ptrDiffLimit hin
    have hcnt : cnt_nat = cnt.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hcnt] at hk
    exact ⟨rfl, ⟨e, herr⟩, frameMod_of_writeErrno herr, Or.inr ⟨k, hk.1, hk.2, rfl⟩⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem write_ok_exists (fd : BitVec 32) {b : BlockId} {off : Int64} {cnt : BitVec 64}
    {m : Mem} (os : OSState)
    (hbuf : Libc.validReadableRange m b off cnt.toNat = true)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk "write" [.int .i32 fd, .ptr b off, .int .u64 cnt] m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i64 (BitVec.ofInt 64 (-1)), m', os, by
    simpa only [bitVec_ofNat_toNat_self] using Libc.ExtOk.write_fail fd b off cnt.toNat 0 m m' os hbuf herr⟩

theorem call_write {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr}
    (hnenv : env.lookup "write" = none)
    (henum : Sem.enumConst? prog.tags "write" = none)
    (hproto : prog.fnProtos "write" = some (.int .i64, [.int .i32, .ptr (.const_ .void), .int .u64], false))
    (hnfn : prog.fns "write" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 b off t2 v3 t3 fd cnt blk, vs = [(v1, t1), (.ptr b off, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .i32) v1 = some (.int .i32 fd) ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 cnt) ∧
        Libc.validReadableRange m2 b off cnt.toNat = true ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size)
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 cnt ret m' os', Pargs vs m2 os2 →
      (∃ v1 t1 b off t2 v3 t3, vs = [(v1, t1), (.ptr b off, t2), (v3, t3)] ∧
        Sem.castVal m2 (.int .u64) v3 = some (.int .u64 cnt)) →
      WritePost cnt m2 os2 ret m' os' →
      Post ret (.int .i64) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "write") [a1, a2, a3]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, b, off, t2, v3, t3, fd, cnt, blk, rfl, hc1, hc3, hbuf, herrBlk, hrw, hsz⟩ :=
    hpre vs m2 os2 hp
  have hc2 : Sem.castVal m2 (.ptr (.const_ .void)) (.ptr b off) = some (.ptr b off) := castVal_ptr_eq rfl b off
  refine ⟨[.int .i32 fd, .ptr b off, .int .u64 cnt], coerceCallArgs_3 hc1 hc2 hc3,
    write_ok_exists fd os2 hbuf herrBlk hrw hsz, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1), (.ptr b off, t2), (v3, t3)] m2 os2 cnt ret m' os' hp
    ⟨v1, t1, b, off, t2, v3, t3, rfl, hc3⟩ (write_ok_elim hok)

/-! #### 5.3.17 `strerror` -/

def StrerrorPost (m : Mem) (os : OSState) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  ∃ bid n blk,
    ret = .ptr bid 0 ∧
    os' = { os with strerrorBlk := some bid } ∧
    m'.blocks bid = some blk ∧
    blk.size = n + 1 ∧ blk.perm = .ro ∧ blk.kind = .global ∧
    m'.strlenAt bid 0 = some n ∧
    FrameMod m m' (fun b => os.strerrorBlk = some b)

theorem strerror_ok_elim {ev : BitVec 32} {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk "strerror" [.int .i32 ev] m os ret m' os') :
    StrerrorPost m os ret m' os' := by
  generalize hfn : ("strerror" : String) = fn at h
  generalize hargs : ([Val.int .i32 ev] : List Val) = args at h
  cases h with
  | strerror_ok _ n bs base hsz _ _ bid _ hlen hnonnul halloc =>
    let m0 := match os.strerrorBlk with | some old => m.dropBlock old | none => m
    have halloc' : m0.alloc (n + 1) 1 .ro .global base
        (fun i => .byte (if i < n then bs[i]?.getD 0 else 0)) hsz (by decide) (Nat.mod_one _) = (bid, m') :=
      halloc
    have hfr0 : FrameMod m m0 (fun b => os.strerrorBlk = some b) := by
      cases hsb : os.strerrorBlk with
      | none =>
        simp only [m0, hsb]
        exact FrameMod.refl m _
      | some old =>
        simp only [m0, hsb]
        exact (FrameMod.of_dropBlock m old).mono (fun b heq => by rw [heq])
    have hfr1 : FrameMod m0 m' (fun _ => False) := frameMod_of_alloc_ro halloc'
    have hfr : FrameMod m m' (fun b => os.strerrorBlk = some b) :=
      (hfr0.trans hfr1).mono (fun _ hx => hx.elim id False.elim)
    obtain ⟨_, _, blk, hblk, hszb, _, hpb, hkb, _⟩ := alloc_blocks_self halloc'
    have hstr := strlenAt_alloc_zero_terminated hlen hnonnul halloc'
    exact ⟨bid, n, blk, rfl, rfl, hblk, hszb, hpb, hkb, hstr, hfr⟩
  | _ =>
    first
    | exact absurd hfn (by decide)
    | exact False.elim (ne_or_elim hfn (by assumption) (by decide) (by decide))

theorem strerror_ok_exists (ev : BitVec 32) (m : Mem) (os : OSState) :
    ∃ ret m' os', Libc.ExtOk "strerror" [.int .i32 ev] m os ret m' os' := by
  let m0 := match os.strerrorBlk with | some old => m.dropBlock old | none => m
  have hsz : 0 + 1 < ptrDiffLimit := by unfold ptrDiffLimit; omega
  let res := m0.alloc (0 + 1) 1 .ro .global 0
    (fun i => .byte (if i < 0 then ([] : List UInt8)[i]?.getD 0 else 0))
    hsz (by decide) (Nat.mod_one _)
  exact ⟨.ptr res.1 0, res.2, { os with strerrorBlk := some res.1 },
    Libc.ExtOk.strerror_ok ev 0 [] 0 hsz m res.2 res.1 os rfl (by simp) rfl⟩

theorem call_strerror {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {arg : CExpr}
    (hnenv : env.lookup "strerror" = none)
    (henum : Sem.enumConst? prog.tags "strerror" = none)
    (hproto : prog.fnProtos "strerror" = some (.ptr (.int .i8), [.int .i32], false))
    (hnfn : prog.fns "strerror" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [arg] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 ev, vs = [(v1, t1)] ∧ Sem.castVal m2 (.int .i32) v1 = some (.int .i32 ev))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 ret m' os', Pargs vs m2 os2 →
      StrerrorPost m2 os2 ret m' os' →
      Post ret (.ptr (.int .i8)) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "strerror") [arg]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, ev, rfl, hc1⟩ := hpre vs m2 os2 hp
  refine ⟨[.int .i32 ev], coerceCallArgs_1 hc1, strerror_ok_exists ev m2 os2, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1)] m2 os2 ret m' os' hp (strerror_ok_elim hok)

/-! #### 5.3.18 & 5.3.19 `snprintf` & `vsnprintf` -/

def PrintfPost (buf : Val) (sz : BitVec 64) (bf : BlockId) (of_ : Int64)
    (m : Mem) (os : OSState) (ret : Val) (m' : Mem) (os' : OSState) : Prop :=
  os' = os ∧
  Libc.printfFmtOk m bf of_ ∧
  (∃ r : Int32, ret = .int .i32 (BitVec.ofInt 32 r.toInt)) ∧
  ((sz = 0 ∧ (∃ e, Libc.writeErrno m os e = some m') ∧ FrameMod m m' (· = os.errnoBlk)) ∨
    (∃ bb ob outBytes m1 e,
      buf = .ptr bb ob ∧ sz.toNat > 0 ∧
      Libc.validWritableRange m bb ob sz.toNat = true ∧
      outBytes.length = sz.toNat ∧ Libc.hasNul outBytes = true ∧
      m.writeBytes bb ob outBytes = some m1 ∧
      Libc.writeErrno m1 os e = some m' ∧
      FrameMod m m' (fun x => x = bb ∨ x = os.errnoBlk)))

theorem printf_family_ok_elim {fn : String} (hfn : fn = "snprintf" ∨ fn = "vsnprintf")
    {buf : Val} {sz : BitVec 64} {bf : BlockId} {of_ : Int64} {rest : List Val}
    {m m' : Mem} {os os' : OSState} {ret : Val}
    (h : Libc.ExtOk fn (buf :: .int .u64 sz :: .ptr bf of_ :: rest) m os ret m' os') :
    PrintfPost buf sz bf of_ m os ret m' os' := by
  generalize hargs : (buf :: Val.int .u64 sz :: Val.ptr bf of_ :: rest) = args at h
  cases h with
  | printf_zero _ _ _ _ _ _ r e _ _ _ _ hfmt herr =>
    rcases List.cons.inj hargs with ⟨_, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hsz0, hrest2⟩
    rcases List.cons.inj hrest2 with ⟨hp3, _⟩
    have hszEq : sz = 0 := val_int_eq hsz0
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp3
    exact ⟨rfl, hfmt, ⟨r, rfl⟩, Or.inl ⟨hszEq, ⟨e, herr⟩, frameMod_of_writeErrno herr⟩⟩
  | printf_ok _ _ bb ob sz_nat _ _ _ outBytes r e _ m1 _ _ _ hszp hfmt hbuf hlen hnul hwr herr =>
    rcases List.cons.inj hargs with ⟨hbufEq, hrest1⟩
    rcases List.cons.inj hrest1 with ⟨hszEqV, hrest2⟩
    rcases List.cons.inj hrest2 with ⟨hp3, _⟩
    obtain ⟨rfl, rfl⟩ := val_ptr_eq hp3
    have heq : BitVec.ofNat 64 sz_nat = sz := (val_int_eq hszEqV).symm
    obtain ⟨blk, _, _, hin⟩ := validWritableRange_iff.mp hbuf
    have hlt : sz_nat < ptrDiffLimit := inBounds_lt_ptrDiffLimit hin
    have hszEq : sz_nat = sz.toNat := nat_eq_of_bitVec64_eq_lt heq hlt
    rw [hszEq] at hszp hbuf hlen
    have hfr := (FrameMod.of_writeBytes hwr).trans (frameMod_of_writeErrno herr)
    exact ⟨rfl, hfmt, ⟨r, rfl⟩,
      Or.inr ⟨bb, ob, outBytes, m1, e, hbufEq, hszp, hbuf, hlen, hnul, hwr, herr, hfr⟩⟩
  | lseek_ok _ hl _ _ _ _ _ _ _ _ _ =>
    exact False.elim (ne_or_or_elim hfn hl (by decide) (by decide) (by decide) (by decide))
  | _ => rcases hfn with h1 | h1 <;> exact absurd h1 (by decide)

theorem printf_zero_exists {fn : String} (hfn : fn = "snprintf" ∨ fn = "vsnprintf")
    (buf : Val) {bf : BlockId} {of_ : Int64} (rest : List Val)
    (hva : fn = "vsnprintf" → ∃ rest', rest = .vaList true :: rest')
    {m : Mem} (os : OSState)
    (hfmt : Libc.printfFmtOk m bf of_)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk fn (buf :: .int .u64 0 :: .ptr bf of_ :: rest) m os ret m' os' := by
  obtain ⟨m', herr⟩ := writeErrno_eq_some 0 herrBlk hrw hsz
  exact ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m', os,
    Libc.ExtOk.printf_zero fn hfn buf bf of_ rest 0 0 m m' os hva hfmt herr⟩

theorem printf_ok_exists {fn : String} (hfn : fn = "snprintf" ∨ fn = "vsnprintf")
    {bb : BlockId} {ob : Int64} {sz : BitVec 64} {bf : BlockId} {of_ : Int64} (rest : List Val)
    (hva : fn = "vsnprintf" → ∃ rest', rest = .vaList true :: rest')
    (hszp : sz.toNat > 0)
    {m : Mem} (os : OSState)
    (hfmt : Libc.printfFmtOk m bf of_)
    (hbuf : Libc.validWritableRange m bb ob sz.toNat = true)
    {blk : Block} (herrBlk : m.blocks os.errnoBlk = some blk) (hrw : blk.perm = .rw) (hsz : 4 ≤ blk.size) :
    ∃ ret m' os', Libc.ExtOk fn (.ptr bb ob :: .int .u64 sz :: .ptr bf of_ :: rest) m os ret m' os' := by
  obtain ⟨dblk, hdb, hdrw, hdin⟩ := validWritableRange_iff.mp hbuf
  let outBytes : List MemByte := List.replicate sz.toNat (.byte 0)
  have hlen : outBytes.length = sz.toNat := List.length_replicate
  have hnul : Libc.hasNul outBytes = true := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hszp)
    change Libc.hasNul (List.replicate sz.toNat (MemByte.byte 0)) = true
    rw [hk, List.replicate_succ]
    rfl
  have hdin' : Mem.inBounds dblk ob outBytes.length = true := by rw [hlen]; exact hdin
  obtain ⟨m1, hwr⟩ := writeBytes_eq_some hdb hdrw hdin'
  obtain ⟨eblk1, heb1, hprw1, hsz1⟩ : ∃ blk', m1.blocks os.errnoBlk = some blk' ∧ blk'.perm = .rw ∧ 4 ≤ blk'.size := by
    by_cases heqb : os.errnoBlk = bb
    · subst heqb
      obtain ⟨blk', hb', _, hp', hs', _, _, _⟩ := writeBytes_preserves_perm hwr herrBlk
      exact ⟨blk', hb', by rw [hp', hrw], by rw [hs']; exact hsz⟩
    · have hne := writeBytes_blocks_ne hwr heqb
      rw [herrBlk] at hne
      exact ⟨blk, hne, hrw, hsz⟩
  obtain ⟨m2, herr⟩ := writeErrno_eq_some 0 heb1 hprw1 hsz1
  exact ⟨.int .i32 (BitVec.ofInt 32 (0 : Int32).toInt), m2, os, by
    simpa only [bitVec_ofNat_toNat_self] using
      Libc.ExtOk.printf_ok fn hfn bb ob sz.toNat bf of_ rest outBytes 0 0 m m1 m2 os
        hva hszp hfmt hbuf hlen hnul hwr herr⟩

theorem call_snprintf {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 : CExpr} {restArgs : List CExpr}
    (hnenv : env.lookup "snprintf" = none)
    (henum : Sem.enumConst? prog.tags "snprintf" = none)
    (hproto : prog.fnProtos "snprintf" = some (.int .i32, [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8))], true))
    (hnfn : prog.fns "snprintf" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] (a1 :: a2 :: a3 :: restArgs) Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 bf of_ t3 rest cbuf sz blk,
        vs = (v1, t1) :: (v2, t2) :: (.ptr bf of_, t3) :: rest ∧
        Sem.castVal m2 (.ptr (.int .i8)) v1 = some cbuf ∧
        Sem.castVal m2 (.int .u64) v2 = some (.int .u64 sz) ∧
        Libc.printfFmtOk m2 bf of_ ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size ∧
        (sz = 0 ∨ ∃ bb ob, cbuf = .ptr bb ob ∧ sz.toNat > 0 ∧
          Libc.validWritableRange m2 bb ob sz.toNat = true))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 cbuf sz bf of_ ret m' os', Pargs vs m2 os2 →
      (∃ v1 t1 v2 t2 t3 rest, vs = (v1, t1) :: (v2, t2) :: (.ptr bf of_, t3) :: rest ∧
        Sem.castVal m2 (.ptr (.int .i8)) v1 = some cbuf ∧
        Sem.castVal m2 (.int .u64) v2 = some (.int .u64 sz)) →
      PrintfPost cbuf sz bf of_ m2 os2 ret m' os' →
      Post ret (.int .i32) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "snprintf") (a1 :: a2 :: a3 :: restArgs)) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, v2, t2, bf, of_, t3, rest, cbuf, sz, blk, rfl, hc1, hc2, hfmt, herrBlk, hrw, hsz, hbuf⟩ :=
    hpre vs m2 os2 hp
  have hc3 : Sem.castVal m2 (.ptr (.const_ (.int .i8))) (.ptr bf of_) = some (.ptr bf of_) :=
    castVal_ptr_eq rfl bf of_
  have hex : ∃ ret m' os',
      Libc.ExtOk "snprintf" (cbuf :: .int .u64 sz :: .ptr bf of_ :: rest.map (fun (v, _) => Sem.promoteVariadicArg v))
        m2 os2 ret m' os' := by
    rcases hbuf with rfl | ⟨bb, ob, rfl, hszp, hvr⟩
    · exact printf_zero_exists (Or.inl rfl) cbuf _ (fun h => absurd h (by decide)) os2 hfmt herrBlk hrw hsz
    · exact printf_ok_exists (Or.inl rfl) _ (fun h => absurd h (by decide)) hszp os2 hfmt hvr herrBlk hrw hsz
  refine ⟨cbuf :: .int .u64 sz :: .ptr bf of_ :: rest.map (fun (v, _) => Sem.promoteVariadicArg v),
    coerceCallArgs_variadic_3 hc1 hc2 hc3, hex, ?_⟩
  intro ret m' os' hok
  exact hpost ((v1, t1) :: (v2, t2) :: (.ptr bf of_, t3) :: rest) m2 os2 cbuf sz bf of_ ret m' os' hp
    ⟨v1, t1, v2, t2, t3, rest, rfl, hc1, hc2⟩ (printf_family_ok_elim (Or.inl rfl) hok)

theorem call_vsnprintf {prog : Prog} {cfg : PointerConfig}
    {Q : Val → Mem → OSState → Prop} {env : Env} {blks : List BlockId}
    {m : Mem} {os : OSState} {mods : ModSet} {a1 a2 a3 a4 : CExpr}
    (hnenv : env.lookup "vsnprintf" = none)
    (henum : Sem.enumConst? prog.tags "vsnprintf" = none)
    (hproto : prog.fnProtos "vsnprintf" = some (.int .i32, [.ptr (.int .i8), .int .u64, .ptr (.const_ (.int .i8)), .vaList], false))
    (hnfn : prog.fns "vsnprintf" = none)
    {Pargs : List (Val × CTy) → Mem → OSState → Prop}
    (hargs : ExprListSpec prog cfg Libc.ExtStep Q env blks m os mods [] [a1, a2, a3, a4] Pargs)
    (hpre : ∀ vs m2 os2, Pargs vs m2 os2 →
      ∃ v1 t1 v2 t2 bf of_ t3 t4 cbuf sz blk,
        vs = [(v1, t1), (v2, t2), (.ptr bf of_, t3), (.vaList true, t4)] ∧
        Sem.castVal m2 (.ptr (.int .i8)) v1 = some cbuf ∧
        Sem.castVal m2 (.int .u64) v2 = some (.int .u64 sz) ∧
        Libc.printfFmtOk m2 bf of_ ∧
        m2.blocks os2.errnoBlk = some blk ∧ blk.perm = .rw ∧ 4 ≤ blk.size ∧
        (sz = 0 ∨ ∃ bb ob, cbuf = .ptr bb ob ∧ sz.toNat > 0 ∧
          Libc.validWritableRange m2 bb ob sz.toNat = true))
    {Post : Val → CTy → Mem → OSState → ModSet → Prop}
    (hpost : ∀ vs m2 os2 cbuf sz bf of_ ret m' os', Pargs vs m2 os2 →
      (∃ v1 t1 v2 t2 t3 t4, vs = [(v1, t1), (v2, t2), (.ptr bf of_, t3), (.vaList true, t4)] ∧
        Sem.castVal m2 (.ptr (.int .i8)) v1 = some cbuf ∧
        Sem.castVal m2 (.int .u64) v2 = some (.int .u64 sz)) →
      PrintfPost cbuf sz bf of_ m2 os2 ret m' os' →
      Post ret (.int .i32) m' os' []) :
    ExprSpec prog cfg Libc.ExtStep Q env blks m os mods (.call (.var "vsnprintf") [a1, a2, a3, a4]) Post := by
  refine exprSpec_call_extOk hnenv henum hproto hnfn hargs ?_
  intro vs m2 os2 hp
  obtain ⟨v1, t1, v2, t2, bf, of_, t3, t4, cbuf, sz, blk, rfl, hc1, hc2, hfmt, herrBlk, hrw, hsz, hbuf⟩ :=
    hpre vs m2 os2 hp
  have hc3 : Sem.castVal m2 (.ptr (.const_ (.int .i8))) (.ptr bf of_) = some (.ptr bf of_) :=
    castVal_ptr_eq rfl bf of_
  have hc4 : Sem.castVal m2 .vaList (.vaList true) = some (.vaList true) := rfl
  have hex : ∃ ret m' os',
      Libc.ExtOk "vsnprintf" [cbuf, .int .u64 sz, .ptr bf of_, .vaList true] m2 os2 ret m' os' := by
    rcases hbuf with rfl | ⟨bb, ob, rfl, hszp, hvr⟩
    · exact printf_zero_exists (Or.inr rfl) cbuf [.vaList true] (fun _ => ⟨[], rfl⟩) os2 hfmt herrBlk hrw hsz
    · exact printf_ok_exists (Or.inr rfl) [.vaList true] (fun _ => ⟨[], rfl⟩) hszp os2 hfmt hvr herrBlk hrw hsz
  refine ⟨[cbuf, .int .u64 sz, .ptr bf of_, .vaList true], coerceCallArgs_4 hc1 hc2 hc3 hc4, hex, ?_⟩
  intro ret m' os' hok
  exact hpost [(v1, t1), (v2, t2), (.ptr bf of_, t3), (.vaList true, t4)] m2 os2 cbuf sz bf of_ ret m' os' hp
    ⟨v1, t1, v2, t2, t3, t4, rfl, hc1, hc2⟩ (printf_family_ok_elim (Or.inr rfl) hok)

end ExtLibc

end C99.Proof
