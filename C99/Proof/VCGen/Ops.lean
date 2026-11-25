import C99.Proof.WP

/-!
# Pure Symbolic Operators and Framed Memory Algebra (`C99.Proof.VCGen.Ops`)

Verus-inspired pure operator evaluation and framed buffer/struct algebra
over `C99.Sem` and `C99.Mem`. 100% zlib-agnostic.
-/

namespace C99.Proof.VCGen

open C99 C99.Sem C99.Proof

/-! ## Pure Integer, Truthiness, Cast, and Pointer Operations -/

@[simp] def valIntNum (k : IntKind) (v : BitVec k.bits) : Int :=
  if k.signed then v.toInt else (v.toNat : Int)

theorem valAsInt?_eq_int (k : IntKind) (v : BitVec k.bits) :
    valAsInt? (.int k v) = some (k, valIntNum k v) := rfl

@[simp] theorem bitVec_ofInt_toNat (w : Nat) (a : BitVec w) :
    BitVec.ofInt w (a.toNat : Int) = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt a.isLt]

@[simp] theorem bitVec_ofInt_toInt (w : Nat) (a : BitVec w) :
    BitVec.ofInt w a.toInt = a := by
  simp [BitVec.ofInt_toInt]

theorem cty_unqual_idem : ∀ (t : CTy), t.unqual.unqual = t.unqual
  | .const_ t => by simp [CTy.unqual, cty_unqual_idem t]
  | .typedef _ t => by simp [CTy.unqual, cty_unqual_idem t]
  | .void | .int _ | .ptr _ | .array _ _ | .structTy _ | .unionTy _
  | .anonStruct _ | .anonUnion _ | .enumTy _ _ | .fnPtr _ _ _ | .vaList => rfl

theorem int64_ofInt_toInt_self (x : Int64) : Int64.ofInt x.toInt = x := by
  rcases x with ⟨⟨bv⟩⟩
  change Int64.ofUInt64 ⟨BitVec.ofInt 64 bv.toInt⟩ = Int64.ofUInt64 ⟨bv⟩
  congr 2
  exact BitVec.ofInt_toInt

private theorem isPtr_false_of_intKind? {t : CTy} {k : IntKind} (h : t.intKind? = some k) :
    t.isPtr = false := by
  unfold CTy.intKind? at h
  unfold CTy.isPtr
  cases hu : t.unqual <;> simp [hu] at h ⊢

private theorem isFn_false_of_intKind? {t : CTy} {k : IntKind} (h : t.intKind? = some k) :
    (match t.unqual with | .fnPtr .. => true | _ => false) = false := by
  unfold CTy.intKind? at h
  cases hu : t.unqual <;> simp [hu] at h ⊢

@[simp] theorem ite_one_zero_ne_zero (c : Bool) :
    ((if c then (1 : BitVec 32) else 0) ≠ 0) ↔ c = true := by
  cases c <;> decide

theorem bv_toNat_bne_zero_iff {w : Nat} (c : BitVec w) :
    ((c.toNat != 0) = true ↔ c ≠ 0) ∧ ((c.toNat != 0) = false ↔ c = 0) := by
  have h1 : (c.toNat != 0) = true ↔ c ≠ 0 := by
    constructor
    · intro h heq
      subst heq
      simp at h
    · intro h
      by_cases hcz : c.toNat = 0
      · exact False.elim (h (BitVec.eq_of_toNat_eq hcz))
      · simp [hcz]
  constructor
  · exact h1
  · constructor
    · intro hf
      by_cases hcz : c.toNat = 0
      · exact BitVec.eq_of_toNat_eq hcz
      · have hne : (c.toNat != 0) = true := by simp [hcz]
        rw [hne] at hf
        cases hf
    · intro heq
      subst heq
      simp

@[simp] theorem bv32_ne_zero_iff (c : BitVec 32) : (c.toNat != 0) = true ↔ c ≠ 0 :=
  (bv_toNat_bne_zero_iff c).1

/-- Pure symbolic semantics of `applyBinary` on two integer values. Returns
`(sideCondition, resultVal, resultTy)` with bitvector operators already normalized. -/
def vcIntBinOp (op : BinOp) (k1 : IntKind) (v1 : BitVec k1.bits)
    (k2 : IntKind) (v2 : BitVec k2.bits) : Prop × Val × CTy :=
  let i1 := valIntNum k1 v1
  let i2 := valIntNum k2 v2
  match op with
  | .shl | .shr =>
    let lk := k1.promote
    let sh := i2.toNat
    if lk.signed then
      let raw := if op == .shl then i1 * (2 ^ sh : Int) else i1 / (2 ^ sh : Int)
      (0 ≤ i2 ∧ i2 < (lk.bits : Int) ∧ 0 ≤ i1 ∧ lk.inRange raw = true,
       .int lk (BitVec.ofInt lk.bits raw), .int lk)
    else
      let bv := BitVec.ofInt lk.bits i1
      (0 ≤ i2 ∧ i2 < (lk.bits : Int),
       .int lk (if op == .shl then bv <<< sh else bv >>> sh), .int lk)
  | _ =>
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits i1
    let c2 := BitVec.ofInt ck.bits i2
    let n1 := valIntNum ck c1
    let n2 := valIntNum ck c2
    match op with
    | .eq | .ne | .lt | .le | .gt | .ge =>
      (True, .int .i32 (if Sem.cmpOrd op n1 n2 then 1 else 0), .int .i32)
    | .add =>
      (ck.signed = true → ck.inRange (n1 + n2) = true, .int ck (c1 + c2), .int ck)
    | .sub =>
      (ck.signed = true → ck.inRange (n1 - n2) = true, .int ck (c1 - c2), .int ck)
    | .mul =>
      (ck.signed = true → ck.inRange (n1 * n2) = true, .int ck (c1 * c2), .int ck)
    | .div =>
      (n2 ≠ 0 ∧ (ck.signed = true → ck.inRange (Int.tdiv n1 n2) = true),
       .int ck (BitVec.ofInt ck.bits (Int.tdiv n1 n2)), .int ck)
    | .mod =>
      (n2 ≠ 0 ∧ (ck.signed = true → ck.inRange (Int.tmod n1 n2) = true),
       .int ck (BitVec.ofInt ck.bits (Int.tmod n1 n2)), .int ck)
    | .bitAnd => (True, .int ck (c1 &&& c2), .int ck)
    | .bitOr => (True, .int ck (c1 ||| c2), .int ck)
    | .bitXor => (True, .int ck (c1 ^^^ c2), .int ck)
    | .shl | .shr => (True, .int ck c1, .int ck)

private theorem bitVec_add_ofInt (w : Nat) (x y : Int) :
    BitVec.ofInt w (x + y) = BitVec.ofInt w x + BitVec.ofInt w y := by
  apply BitVec.eq_of_toNat_eq
  apply Int.ofNat.inj
  change ((BitVec.ofInt w (x + y)).toNat : Int) = ((BitVec.ofInt w x + BitVec.ofInt w y).toNat : Int)
  have hpos : (0 : Int) < ((2 ^ w : Nat) : Int) := Int.natCast_pos.mpr (Nat.pow_pos (by decide))
  have hx : ((x % ((2 ^ w : Nat) : Int)).toNat : Int) = x % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have hy : ((y % ((2 ^ w : Nat) : Int)).toNat : Int) = y % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg y (by omega))
  have hsum : (((x + y) % ((2 ^ w : Nat) : Int)).toNat : Int) = (x + y) % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (x + y) (by omega))
  simp only [BitVec.toNat_ofInt, BitVec.toNat_add, Int.natCast_emod, Int.natCast_add, hsum, hx, hy]
  exact Int.add_emod x y ((2 ^ w : Nat) : Int)

private theorem bitVec_sub_ofInt (w : Nat) (x y : Int) :
    BitVec.ofInt w (x - y) = BitVec.ofInt w x - BitVec.ofInt w y := by
  apply BitVec.eq_of_toNat_eq
  apply Int.ofNat.inj
  change ((BitVec.ofInt w (x - y)).toNat : Int) = ((BitVec.ofInt w x - BitVec.ofInt w y).toNat : Int)
  have hpos : (0 : Int) < ((2 ^ w : Nat) : Int) := Int.natCast_pos.mpr (Nat.pow_pos (by decide))
  have hx : ((x % ((2 ^ w : Nat) : Int)).toNat : Int) = x % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have hy : ((y % ((2 ^ w : Nat) : Int)).toNat : Int) = y % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg y (by omega))
  have hdiff : (((x - y) % ((2 ^ w : Nat) : Int)).toNat : Int) = (x - y) % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (x - y) (by omega))
  have hylt_int := Int.emod_lt_of_pos y hpos
  have hylt : (y % ((2 ^ w : Nat) : Int)).toNat ≤ 2 ^ w :=
    Int.ofNat_le.mp (by rw [hy]; exact Int.le_of_lt hylt_int)
  simp only [BitVec.toNat_ofInt, BitVec.toNat_sub, Int.natCast_emod, Int.natCast_add,
    Int.natCast_sub hylt, hdiff, hx, hy]
  have hrearr : ((2 ^ w : Nat) : Int) - y % ((2 ^ w : Nat) : Int) + x % ((2 ^ w : Nat) : Int) =
      (x % ((2 ^ w : Nat) : Int) - y % ((2 ^ w : Nat) : Int)) + ((2 ^ w : Nat) : Int) := by omega
  rw [hrearr, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod, ← Int.sub_emod]

private theorem bitVec_mul_ofInt (w : Nat) (x y : Int) :
    BitVec.ofInt w (x * y) = BitVec.ofInt w x * BitVec.ofInt w y := by
  apply BitVec.eq_of_toNat_eq
  apply Int.ofNat.inj
  change ((BitVec.ofInt w (x * y)).toNat : Int) = ((BitVec.ofInt w x * BitVec.ofInt w y).toNat : Int)
  have hpos : (0 : Int) < ((2 ^ w : Nat) : Int) := Int.natCast_pos.mpr (Nat.pow_pos (by decide))
  have hx : ((x % ((2 ^ w : Nat) : Int)).toNat : Int) = x % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have hy : ((y % ((2 ^ w : Nat) : Int)).toNat : Int) = y % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg y (by omega))
  have hmul : (((x * y) % ((2 ^ w : Nat) : Int)).toNat : Int) = (x * y) % ((2 ^ w : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg (x * y) (by omega))
  simp only [BitVec.toNat_ofInt, BitVec.toNat_mul, Int.natCast_emod, Int.natCast_mul, hmul, hx, hy]
  exact Int.mul_emod x y ((2 ^ w : Nat) : Int)

private theorem bitVec_ofInt_valIntNum_eq (k : IntKind) (c : BitVec k.bits) :
    BitVec.ofInt k.bits (valIntNum k c) = c := by
  cases hs : k.signed <;> simp [valIntNum, hs]

theorem vcIntBinOp_sound {cfg tags m op k1 v1 t1 k2 v2 t2}
    (ht1 : t1.intKind? = some k1) (ht2 : t2.intKind? = some k2)
    (hside : (vcIntBinOp op k1 v1 k2 v2).1) :
    applyBinary cfg tags m op (.int k1 v1) t1 (.int k2 v2) t2 =
      some (vcIntBinOp op k1 v1 k2 v2).2 := by
  have hbin : applyBinary cfg tags m op (.int k1 v1) t1 (.int k2 v2) t2 =
      evalIntBinary op (.int k1 v1) (.int k2 v2) := by
    clear hside
    unfold CTy.intKind? at ht1 ht2
    unfold applyBinary CTy.isPtr
    cases hu1 : t1.unqual <;> simp [hu1] at ht1 <;>
      cases hu2 : t2.unqual <;> simp [hu2] at ht2 <;>
      simp [hu1, hu2]
  rw [hbin]
  unfold vcIntBinOp at hside ⊢
  unfold evalIntBinary
  rw [valAsInt?_eq_int, valAsInt?_eq_int]
  simp only [bind, Option.bind, pure, Pure.pure]
  cases op with
  | shl =>
    dsimp only at hside ⊢
    by_cases hs : k1.promote.signed = true
    · simp only [hs, ↓reduceIte] at hside ⊢
      rcases hside with ⟨h0, hlt, hi1, hr⟩
      have hsh : (BinOp.shl == BinOp.shl) = true := rfl
      simp only [hsh, ↓reduceIte] at hr ⊢
      have hg : (decide (0 ≤ valIntNum k2 v2) && decide (valIntNum k2 v2 < ↑k1.promote.bits)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h0, hlt⟩
      simp only [hg, hi1, guard_true, ofIntExact_signed hs hr]
    · have hsf : k1.promote.signed = false := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ↓reduceIte] at hside ⊢
      rcases hside with ⟨h0, hlt⟩
      have hg : (decide (0 ≤ valIntNum k2 v2) && decide (valIntNum k2 v2 < ↑k1.promote.bits)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h0, hlt⟩
      simp only [hg, guard_true]
  | shr =>
    dsimp only at hside ⊢
    by_cases hs : k1.promote.signed = true
    · simp only [hs, ↓reduceIte] at hside ⊢
      rcases hside with ⟨h0, hlt, hi1, hr⟩
      have hsh : (BinOp.shr == BinOp.shl) = false := rfl
      simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hr ⊢
      have hg : (decide (0 ≤ valIntNum k2 v2) && decide (valIntNum k2 v2 < ↑k1.promote.bits)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h0, hlt⟩
      simp only [hg, hi1, guard_true, ofIntExact_signed hs hr]
    · have hsf : k1.promote.signed = false := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ↓reduceIte] at hside ⊢
      rcases hside with ⟨h0, hlt⟩
      have hg : (decide (0 ≤ valIntNum k2 v2) && decide (valIntNum k2 v2 < ↑k1.promote.bits)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h0, hlt⟩
      simp only [hg, guard_true]
  | eq | ne | lt | le | gt | ge => rfl
  | add =>
    dsimp only at hside ⊢
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (valIntNum k1 v1)
    let c2 := BitVec.ofInt ck.bits (valIntNum k2 v2)
    have hsum : BitVec.ofInt ck.bits (valIntNum ck c1 + valIntNum ck c2) = c1 + c2 := by
      rw [bitVec_add_ofInt, bitVec_ofInt_valIntNum_eq, bitVec_ofInt_valIntNum_eq]
    change Option.bind (ofIntExact ck (valIntNum ck c1 + valIntNum ck c2)) (fun x => some (x, CTy.int ck)) = _
    by_cases hs : ck.signed = true
    · rw [ofIntExact_signed hs (hside hs), hsum]; rfl
    · rw [ofIntExact_unsigned (Bool.eq_false_iff.mpr hs), hsum]; rfl
  | sub =>
    dsimp only at hside ⊢
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (valIntNum k1 v1)
    let c2 := BitVec.ofInt ck.bits (valIntNum k2 v2)
    have hdiff : BitVec.ofInt ck.bits (valIntNum ck c1 - valIntNum ck c2) = c1 - c2 := by
      rw [bitVec_sub_ofInt, bitVec_ofInt_valIntNum_eq, bitVec_ofInt_valIntNum_eq]
    change Option.bind (ofIntExact ck (valIntNum ck c1 - valIntNum ck c2)) (fun x => some (x, CTy.int ck)) = _
    by_cases hs : ck.signed = true
    · rw [ofIntExact_signed hs (hside hs), hdiff]; rfl
    · rw [ofIntExact_unsigned (Bool.eq_false_iff.mpr hs), hdiff]; rfl
  | mul =>
    dsimp only at hside ⊢
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (valIntNum k1 v1)
    let c2 := BitVec.ofInt ck.bits (valIntNum k2 v2)
    have hmul : BitVec.ofInt ck.bits (valIntNum ck c1 * valIntNum ck c2) = c1 * c2 := by
      rw [bitVec_mul_ofInt, bitVec_ofInt_valIntNum_eq, bitVec_ofInt_valIntNum_eq]
    change Option.bind (ofIntExact ck (valIntNum ck c1 * valIntNum ck c2)) (fun x => some (x, CTy.int ck)) = _
    by_cases hs : ck.signed = true
    · rw [ofIntExact_signed hs (hside hs), hmul]; rfl
    · rw [ofIntExact_unsigned (Bool.eq_false_iff.mpr hs), hmul]; rfl
  | div =>
    dsimp only at hside ⊢
    rcases hside with ⟨hnz, hr⟩
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (valIntNum k1 v1)
    let c2 := BitVec.ofInt ck.bits (valIntNum k2 v2)
    have hbeq : (valIntNum ck c2 == 0) = false := beq_false_of_ne hnz
    change Option.bind (if (valIntNum ck c2 == 0) = true then none
      else ofIntExact ck (Int.tdiv (valIntNum ck c1) (valIntNum ck c2))) (fun x => some (x, CTy.int ck)) = _
    by_cases hs : ck.signed = true
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [ofIntExact_signed hs (hr hs)]; rfl
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [ofIntExact_unsigned (Bool.eq_false_iff.mpr hs)]; rfl
  | mod =>
    dsimp only at hside ⊢
    rcases hside with ⟨hnz, hr⟩
    let ck := IntKind.usualArith k1 k2
    let c1 := BitVec.ofInt ck.bits (valIntNum k1 v1)
    let c2 := BitVec.ofInt ck.bits (valIntNum k2 v2)
    have hbeq : (valIntNum ck c2 == 0) = false := beq_false_of_ne hnz
    change Option.bind (if (valIntNum ck c2 == 0) = true then none
      else ofIntExact ck (Int.tmod (valIntNum ck c1) (valIntNum ck c2))) (fun x => some (x, CTy.int ck)) = _
    by_cases hs : ck.signed = true
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [ofIntExact_signed hs (hr hs)]; rfl
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [ofIntExact_unsigned (Bool.eq_false_iff.mpr hs)]; rfl
  | bitAnd | bitOr | bitXor => rfl

def vcIntUnOp (op : UnOp) (k : IntKind) (v : BitVec k.bits) : Prop × Val × CTy :=
  let lk := k.promote
  let iv := valIntNum k v
  match op with
  | .plus => (lk.signed = true → lk.inRange iv = true, .int lk (BitVec.ofInt lk.bits iv), .int lk)
  | .neg => (lk.signed = true → lk.inRange (-iv) = true, .int lk (BitVec.ofInt lk.bits (-iv)), .int lk)
  | .bitNot => (True, .int lk (~~~BitVec.ofInt lk.bits iv), .int lk)
  | .logNot => (True, .int .i32 (if v == 0 then 1 else 0), .int .i32)

theorem vcIntUnOp_sound (op : UnOp) (k : IntKind) (v : BitVec k.bits)
    (hside : (vcIntUnOp op k v).1) :
    evalUnary op (.int k v) = some (vcIntUnOp op k v).2 := by
  cases op with
  | plus =>
    unfold vcIntUnOp at hside
    unfold evalUnary vcIntUnOp
    simp only [valAsInt?, valIntNum, bind, Option.bind, pure, Pure.pure] at hside ⊢
    by_cases hs : k.promote.signed = true
    · simp only [ofIntExact, hs, ↓reduceIte, hside hs]
    · have hsf : k.promote.signed = false := Bool.eq_false_iff.mpr hs
      simp only [ofIntExact, hsf, Bool.false_eq_true, ↓reduceIte]
  | neg =>
    unfold vcIntUnOp at hside
    unfold evalUnary vcIntUnOp
    simp only [valAsInt?, valIntNum, bind, Option.bind, pure, Pure.pure] at hside ⊢
    by_cases hs : k.promote.signed = true
    · simp only [ofIntExact, hs, ↓reduceIte, hside hs]
    · have hsf : k.promote.signed = false := Bool.eq_false_iff.mpr hs
      simp only [ofIntExact, hsf, Bool.false_eq_true, ↓reduceIte]
  | bitNot => rfl
  | logNot =>
    unfold evalUnary vcIntUnOp
    simp only [Sem.isTruthy, bind, Option.bind, pure, Pure.pure]
    by_cases hz : v = 0
    · subst hz; simp
    · have hne : (v.toNat != 0) = true := (bv_toNat_bne_zero_iff v).1.mpr hz
      have hbeq : (v == 0) = false := beq_false_of_ne hz
      simp only [hne, ↓reduceIte, hbeq, Bool.false_eq_true]

/-- Memory-independent truthiness proposition for scalars and pointers. -/
def vcTruthy : Val → Option Prop
  | .int _ v => some (v ≠ 0)
  | .ptr _ _ | .fnPtr _ => some True
  | .null => some False
  | _ => none

theorem isTruthy_some_true_iff {v : Val} {P : Prop} (ht : vcTruthy v = some P) :
    Sem.isTruthy v = some true ↔ P := by
  cases v with
  | int k bv =>
    simp only [vcTruthy, Option.some.injEq] at ht
    subst ht
    simpa [Sem.isTruthy] using (bv_toNat_bne_zero_iff bv).1
  | ptr _ _ | fnPtr _ =>
    simp only [vcTruthy, Option.some.injEq] at ht
    subst ht
    simp [Sem.isTruthy]
  | null =>
    simp only [vcTruthy, Option.some.injEq] at ht
    subst ht
    simp [Sem.isTruthy]
  | void | undef | vaList _ => cases ht

theorem isTruthy_some_false_iff {v : Val} {P : Prop} (ht : vcTruthy v = some P) :
    Sem.isTruthy v = some false ↔ ¬ P := by
  cases v with
  | int k bv =>
    simp only [vcTruthy, Option.some.injEq] at ht
    subst ht
    simpa [Sem.isTruthy] using (bv_toNat_bne_zero_iff bv).2
  | ptr _ _ | fnPtr _ =>
    simp only [vcTruthy, Option.some.injEq] at ht
    subst ht
    simp [Sem.isTruthy]
  | null =>
    simp only [vcTruthy, Option.some.injEq] at ht
    subst ht
    simp [Sem.isTruthy]
  | void | undef | vaList _ => cases ht

/-- Memory-independent casts (all scalar, null-to-ptr/fnPtr, ptr-to-ptr, fnPtr-to-fnPtr). -/
def vcPureCast? (target : CTy) (v : Val) : Option Val :=
  let ut := target.unqual
  if ut.isVoid then some .void
  else if let some k := ut.intKind? then
    match v with
    | .int k1 bv => some (ofIntCast k (valIntNum k1 bv))
    | .null => some (.int k 0)
    | _ => none
  else match ut, v with
    | .ptr _, .null => some .null
    | .ptr _, .ptr b off => some (.ptr b off)
    | .ptr _, .int _ bv => if bv.toNat == 0 then some .null else none
    | .fnPtr _ _ _, .null => some .null
    | .fnPtr _ _ _, .fnPtr s => some (.fnPtr s)
    | .fnPtr _ _ _, .int _ bv => if bv.toNat == 0 then some .null else none
    | .vaList, .vaList true => some (.vaList true)
    | _, _ => none

theorem vcPureCast?_sound (m : Mem) {target : CTy} {v rv : Val}
    (h : vcPureCast? target v = some rv) :
    castVal m target v = some rv := by
  unfold vcPureCast? at h
  unfold castVal
  by_cases hv : target.unqual.isVoid
  · simp only [hv, ↓reduceIte] at h ⊢; exact h
  · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hk : target.unqual.intKind? with
    | some k =>
      simp only [hk] at h ⊢
      cases v <;> simp only [valIntNum, Option.some.injEq] at h ⊢ <;>
        first | exact h | cases h
    | none =>
      simp only [hk] at h ⊢
      cases hu : target.unqual <;> simp only [hu] at h ⊢ <;> cases v <;> exact h

/-- Memory-independent equality/inequality between pointers, fnPtrs, and null/0. -/
def vcPtrEqBool? (p q : Val) : Option Bool :=
  let isNull : Val → Bool | .null => true | .int _ bv => bv.toNat == 0 | _ => false
  match p, q with
  | .ptr b1 o1, .ptr b2 o2 => some (b1 == b2 && o1 == o2)
  | .fnPtr s1, .fnPtr s2 => some (s1 == s2)
  | .ptr _ _, _ | .fnPtr _, _ => if isNull q then some false else none
  | _, .ptr _ _ | _, .fnPtr _ => if isNull p then some false else none
  | _, _ => if isNull p && isNull q then some true else none

theorem evalPtrCmp_eq_of_vcPtrEqBool? (m : Mem) {op : BinOp} {p q : Val} {eq : Bool}
    (hop : op = .eq ∨ op = .ne) (h : vcPtrEqBool? p q = some eq) :
    evalPtrCmp m op p q = some (.int .i32 (if (if op == .eq then eq else !eq) then 1 else 0)) := by
  rcases hop with rfl | rfl <;> (
    change (vcPtrEqBool? p q).map
      (fun eq' => Val.int .i32 (if (if _ == BinOp.eq then eq' else !eq') then 1 else 0)) = _
    rw [h]; rfl)

/-! ## Verus `vstd/raw_ptr`-Style Framed Buffers and Structs -/

/-- Valid, readable byte slice `[off, off + len)` inside block `b` of `m`. -/
def BufSlice (m : Mem) (b : BlockId) (off : Int64) (len : Nat) : Prop :=
  ∃ blk, m.blocks b = some blk ∧ Mem.inBounds blk off len = true ∧
    ∀ i < len, ∃ byte, blk.bytes (off.toInt.toNat + i) = .byte byte

private theorem int64_add_nat_eq (off : Int64) (k : Nat) :
    off + Int64.ofInt k = Int64.ofInt (off.toInt + k) := by
  rcases off with ⟨⟨bv⟩⟩
  change Int64.ofUInt64 ⟨bv + BitVec.ofInt 64 k⟩ = Int64.ofUInt64 ⟨BitVec.ofInt 64 (bv.toInt + k)⟩
  congr 2
  rw [bitVec_add_ofInt, bitVec_ofInt_toInt]

private theorem int64_mul_one (x : Int64) : x * Int64.ofInt 1 = x := by
  rcases x with ⟨⟨bv⟩⟩
  change Int64.ofUInt64 ⟨bv * 1⟩ = Int64.ofUInt64 ⟨bv⟩
  simp

private theorem evalPtrAdd_byte (cfg : PointerConfig) (tags : TypeEnv) (m : Mem)
    (b : BlockId) (off : Int64) (blk : Block) (el : CTy) (k : Nat)
    (hblk : m.blocks b = some blk) (hsz : sizeofTy tags el = 1)
    (h0 : 0 ≤ off.toInt) (hle : off.toInt + (k : Int) ≤ (blk.size : Int)) :
    evalPtrAdd cfg tags m (.ptr b off) el k = some (.ptr b (Int64.ofInt (off.toInt + k))) := by
  by_cases hkz : (k : Int) == 0 && cfg.allowAddZeroAny
  · have hk0 : k = 0 := by simp at hkz; exact hkz.1
    subst hk0
    have ha : cfg.allowAddZeroAny = true := by simpa using hkz
    simp [evalPtrAdd, ha]
  · have hkz_f : ((k : Int) == 0 && cfg.allowAddZeroAny) = false := Bool.eq_false_iff.mpr hkz
    unfold evalPtrAdd
    simp only [hkz_f, Bool.false_eq_true, ↓reduceIte, hblk, hsz, bind, Option.bind, guard, Pure.pure]
    rw [Int.ofNat_one, show max (1 : Int) 1 = 1 from rfl, Int.mul_one]
    have hg : 0 ≤ off.toInt + (k : Int) ∧ off.toInt + (k : Int) ≤ (blk.size : Int) := by omega
    simp [hg]

theorem BufSlice.read_byte_at {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {len k : Nat} {el : CTy}
    (hb : BufSlice m b off len) (hk : k < len) (hel : el.unqual = .int .u8) :
    ∃ (byte : UInt8),
      evalPtrAdd cfg tags m (.ptr b off) el k = some (.ptr b (Int64.ofInt (off.toInt + k))) ∧
      Sem.readVal tags m b (Int64.ofInt (off.toInt + k)) el = some (.int .u8 byte.toBitVec) := by
  rcases hb with ⟨blk, hblk, hin, hconcr⟩
  have hsz_ty : sizeofTy tags el = 1 := by
    rw [← sizeofTy_unqual, hel, sizeofTy_int]; decide
  obtain ⟨h0, hlen⟩ := inBounds_iff.mp hin
  have hlt63 : off.toInt + (k : Int) < 2 ^ 63 := by
    have := blk.sizeLt; rw [ptrDiffLimit_val] at this; omega
  have hadd : evalPtrAdd cfg tags m (.ptr b off) el k =
      some (.ptr b (Int64.ofInt (off.toInt + k))) :=
    evalPtrAdd_byte cfg tags m b off blk el k hblk hsz_ty h0 (by omega)
  have hal : Mem.isAligned blk (Int64.ofInt (off.toInt + k)) 1 = true := by
    apply isAligned_one
    rw [int64_ofInt_toInt (by omega) hlt63]
    omega
  have hin1 : Mem.inBounds blk (Int64.ofInt (off.toInt + k)) 1 = true :=
    inBounds_add hin (by omega)
  obtain ⟨byte, hbyte⟩ := hconcr k hk
  have hoff : (Int64.ofInt (off.toInt + k)).toInt.toNat = off.toInt.toNat + k := by
    rw [int64_ofInt_toInt (by omega) hlt63]; omega
  have hrd : m.readBytes b (Int64.ofInt (off.toInt + k)) 1 = some [.byte byte] := by
    rw [readBytes_of_bounds hblk hin1, hoff]
    apply congrArg some
    change [blk.bytes (off.toInt.toNat + k + 0)] = [.byte byte]
    rw [Nat.add_zero, hbyte]
  have hrdv : Sem.readVal tags m b (Int64.ofInt (off.toInt + k)) el = some (.int .u8 byte.toBitVec) := by
    have hbyte_u8 : Mem.decodeInt .u8 [.byte byte] = some byte.toBitVec := by
      have hgd : (([MemByte.byte byte].length == IntKind.u8.bytes) = true) := rfl
      simp only [Mem.decodeInt, Mem.decodeInt.go, hgd, guard_true,
        Nat.shiftLeft_zero, Nat.zero_or, bind, Option.bind, pure, Pure.pure]
      apply congrArg some
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, UInt8.toNat_toBitVec, IntKind.bits]
      exact Nat.mod_eq_of_lt byte.toBitVec.isLt
    unfold Sem.readVal
    rw [← cty_unqual_idem el, hel]
    change (do let blk ← m.blocks b
               let _ ← guard (Mem.isAligned blk (Int64.ofInt (off.toInt + (k : Int))) 1 = true)
               let bs ← m.readBytes b (Int64.ofInt (off.toInt + (k : Int))) 1
               let v ← Mem.decodeInt .u8 bs
               pure (Val.int .u8 v)) = _
    simp only [hblk, hal, guard_true, hrd, hbyte_u8, bind, Option.bind, pure, Pure.pure]
  exact ⟨byte, hadd, hrdv⟩

theorem BufSlice.read_byte_at_bv {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {len k : Nat} {el : CTy}
    (hb : BufSlice m b off len) (hk : k < len) (hel : el.unqual = .int .u8) :
    ∃ (bv : BitVec 8),
      evalPtrAdd cfg tags m (.ptr b off) el k = some (.ptr b (Int64.ofInt (off.toInt + k))) ∧
      Sem.readVal tags m b (Int64.ofInt (off.toInt + k)) el = some (.int .u8 bv) := by
  obtain ⟨byte, h1, h2⟩ := hb.read_byte_at hk hel
  exact ⟨byte.toBitVec, h1, h2⟩

theorem BufSlice.advance {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {len k : Nat} {el : CTy}
    (hb : BufSlice m b off len) (hk : k ≤ len) (hel : el.unqual = .int .u8) :
    evalPtrAdd cfg tags m (.ptr b off) el k = some (.ptr b (Int64.ofInt (off.toInt + k))) ∧
    BufSlice m b (Int64.ofInt (off.toInt + k)) (len - k) := by
  rcases hb with ⟨blk, hblk, hin, hconcr⟩
  have hsz_ty : sizeofTy tags el = 1 := by
    rw [← sizeofTy_unqual, hel, sizeofTy_int]; decide
  obtain ⟨h0, hlen⟩ := inBounds_iff.mp hin
  have hlt63 : off.toInt + (k : Int) < 2 ^ 63 := by
    have := blk.sizeLt; rw [ptrDiffLimit_val] at this; omega
  have hadd : evalPtrAdd cfg tags m (.ptr b off) el k =
      some (.ptr b (Int64.ofInt (off.toInt + k))) :=
    evalPtrAdd_byte cfg tags m b off blk el k hblk hsz_ty h0 (by omega)
  have hoff : (Int64.ofInt (off.toInt + k)).toInt.toNat = off.toInt.toNat + k := by
    rw [int64_ofInt_toInt (by omega) hlt63]; omega
  refine ⟨hadd, blk, hblk, inBounds_add hin (by omega), fun i hi => ?_⟩
  rw [hoff, Nat.add_assoc]
  exact hconcr (k + i) (by omega)

theorem BufSlice.of_blocks_eq {m1 m2 : Mem} {b : BlockId} {off : Int64} {len : Nat}
    (hb : BufSlice m1 b off len) (heq : m2.blocks b = m1.blocks b) :
    BufSlice m2 b off len := by
  rcases hb with ⟨blk, hblk, hin, hbytes⟩
  exact ⟨blk, heq ▸ hblk, hin, hbytes⟩

theorem BufSlice.of_writeVal_ne {m m' : Mem} {b b' : BlockId} {off off' : Int64}
    {len : Nat} {ty : CTy} {v : Val}
    (hb : BufSlice m b off len) (hwr : Sem.writeVal m b' off' ty v = some m') (hne : b ≠ b') :
    BufSlice m' b off len :=
  hb.of_blocks_eq (writeVal_blocks_ne hwr hne)

/-- Valid, aligned, bounded storage cell of C struct `structTag` at `(b, off)`. -/
def StructCell (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (structTag : String)
    (reqRW : Bool := false) : Prop :=
  ∃ blk, m.blocks b = some blk ∧
    (reqRW = true → blk.perm = .rw) ∧
    Mem.inBounds blk off (sizeofTy tags (.structTy structTag)) = true ∧
    Mem.isAligned blk off (alignofTy tags (.structTy structTag)) = true

/-- Field value witness for field `fld` of C struct `structTag` at `(b, off)`. -/
def HasField (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64)
    (structTag fld : String) (v : Val) : Prop :=
  ∃ foff fty, fieldLayout? tags (.structTy structTag) fld = some (foff, fty) ∧
    Sem.readVal tags m b (Int64.ofInt (off.toInt + foff)) fty = some v

theorem StructCell.of_blocks_eq {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {structTag : String} {reqRW : Bool}
    (hs : StructCell tags m1 b off structTag reqRW) (heq : m2.blocks b = m1.blocks b) :
    StructCell tags m2 b off structTag reqRW := by
  rcases hs with ⟨blk, hblk, hp, hin, hal⟩
  exact ⟨blk, heq ▸ hblk, hp, hin, hal⟩

theorem StructCell.of_writeVal_ne {tags : TypeEnv} {m m' : Mem} {b b' : BlockId}
    {off off' : Int64} {structTag : String} {reqRW : Bool} {ty : CTy} {v : Val}
    (hs : StructCell tags m b off structTag reqRW)
    (hwr : Sem.writeVal m b' off' ty v = some m') (hne : b ≠ b') :
    StructCell tags m' b off structTag reqRW :=
  hs.of_blocks_eq (writeVal_blocks_ne hwr hne)

theorem HasField.of_blocks_eq {tags : TypeEnv} {m1 m2 : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {v : Val}
    (hf : HasField tags m1 b off structTag fld v) (heq : m2.blocks b = m1.blocks b) :
    HasField tags m2 b off structTag fld v := by
  rcases hf with ⟨foff, fty, hfl, hrd⟩
  refine ⟨foff, fty, hfl, ?_⟩
  unfold Sem.readVal Mem.readBytes at hrd ⊢
  simp only [heq]
  exact hrd

theorem HasField.of_writeVal_ne {tags : TypeEnv} {m m' : Mem} {b b' : BlockId}
    {off off' : Int64} {structTag fld : String} {v wv : Val} {ty : CTy}
    (hf : HasField tags m b off structTag fld v)
    (hwr : Sem.writeVal m b' off' ty wv = some m') (hne : b ≠ b') :
    HasField tags m' b off structTag fld v :=
  hf.of_blocks_eq (writeVal_blocks_ne hwr hne)

/-- Canonical well-typed scalar/pointer/fnPtr/`va_list` C value predicate (no structs/unions/arrays). -/
def ValScalarTyped (ty : CTy) (v : Val) : Prop :=
  match ty.unqual with
  | .int k => ∃ bv, v = .int k bv
  | .enumTy _ isU => ∃ bv, v = .int (if isU then .u32 else .i32) bv
  | .ptr _ => v = .null ∨ ∃ pb poff, v = .ptr pb poff
  | .fnPtr _ _ _ => v = .null ∨ ∃ sym, v = .fnPtr sym
  | .vaList => v = .vaList true
  | _ => False

theorem ValScalarTyped.unqual {ty : CTy} {v : Val} (h : ValScalarTyped ty v) :
    ValScalarTyped ty.unqual v := by
  unfold ValScalarTyped at h ⊢
  simpa [cty_unqual_idem] using h

private theorem writeBytes_block_props {m m' : Mem} {b : BlockId} {o : Int64} {bs : List MemByte} {blk : Block}
    (hb : m.blocks b = some blk) (hwb : m.writeBytes b o bs = some m') :
    ∃ blk', m'.blocks b = some blk' ∧
      blk'.perm = blk.perm ∧
      (∀ o2 len2, Mem.inBounds blk' o2 len2 = Mem.inBounds blk o2 len2) ∧
      (∀ o2 al, Mem.isAligned blk' o2 al = Mem.isAligned blk o2 al) ∧
      (∀ i, blk'.bytes i =
        if o.toInt.toNat ≤ i ∧ i < o.toInt.toNat + bs.length then
          bs[i - o.toInt.toNat]?.getD .undef
        else blk.bytes i) :=
  ⟨_, writeBytes_blocks_eq hb hwb, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

private theorem writeVal_enum_aux {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {ty : CTy} {tag : String} {isU : Bool} {k : IntKind} {bv : BitVec k.bits}
    (hnc : ty.isConst = false) (hb : m.blocks b = some blk) (hrw : blk.perm = .rw)
    (hin : Mem.inBounds blk off 4 = true)
    (hal : Mem.isAligned blk off 4 = true)
    (hu : ty.unqual = .enumTy tag isU)
    (hk : (if isU then IntKind.u32 else IntKind.i32) = k)
    (hsz4 : k.bytes = 4) (hal4 : k.align = 4) (hszty : sizeofTy tags ty = 4) :
    ∃ m', Sem.writeVal m b off ty (.int k bv) = some m' ∧
      (∃ bs, bs.length = sizeofTy tags ty ∧ m.writeBytes b off bs = some m') ∧
      Sem.readVal tags m' b off ty = some (.int k bv) := by
  have hbv : BitVec.ofInt k.bits (valIntNum k bv) = bv := bitVec_ofInt_valIntNum_eq k bv
  have hin2 : Mem.inBounds blk off (Mem.encodeInt k bv).length = true := by
    rw [encodeInt_length, hsz4]; exact hin
  obtain ⟨m', hwb⟩ := writeBytes_eq_some hb hrw hin2
  have hwr : Sem.writeVal m b off ty (.int k bv) = some m' := by
    unfold Sem.writeVal
    simp only [hnc, Bool.not_false, guard_true, hb, hu, CTy.unqual, CTy.intKind?, hk,
      hal4, hal, valAsInt?_eq_int, hbv, hwb, bind, Option.bind]
  have hlen : (Mem.encodeInt k bv).length = sizeofTy tags ty := by
    rw [encodeInt_length, hsz4, hszty]
  obtain ⟨blk', hblk', _, _, hsal_eq, _⟩ := writeBytes_block_props hb hwb
  have halm' : Mem.isAligned blk' off 4 = true := (hsal_eq off 4).trans hal
  have hrdbytes : m'.readBytes b off 4 = some (Mem.encodeInt k bv) :=
    readBytes_writeBytes_same hb hwb |> fun h => by rwa [encodeInt_length, hsz4] at h
  have hrd : Sem.readVal tags m' b off ty = some (.int k bv) := by
    unfold Sem.readVal
    rw [← cty_unqual_idem ty, hu]
    simp only [CTy.unqual, CTy.intKind?, hk, hblk', hal4, hsz4, halm', guard_true,
      hrdbytes, decodeInt_encodeInt, bind, Option.bind, pure, Pure.pure]
  exact ⟨m', hwr, ⟨_, hlen, hwb⟩, hrd⟩

theorem ValScalarTyped.castVal_self (m : Mem) {ty : CTy} {v : Val}
    (h : ValScalarTyped ty v) :
    castVal m ty v = some v := by
  unfold ValScalarTyped at h
  cases hu : ty.unqual with
  | int k =>
    simp only [hu] at h
    rcases h with ⟨bv, rfl⟩
    unfold castVal
    simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, ↓reduceIte, Bool.false_eq_true, ofIntCast]
    congr 2
    by_cases hs : k.signed <;> simp [hs]
  | enumTy tag isU =>
    simp only [hu] at h
    rcases h with ⟨bv, rfl⟩
    cases isU
    · simp only [castVal, hu, CTy.unqual, CTy.isVoid, CTy.intKind?, ↓reduceIte,
        Bool.false_eq_true, ofIntCast]
      congr 2
      by_cases hs : IntKind.i32.signed <;> simp [hs]
    · simp only [castVal, hu, CTy.unqual, CTy.isVoid, CTy.intKind?, ↓reduceIte,
        Bool.false_eq_true, ofIntCast]
      congr 2
      by_cases hs : IntKind.u32.signed <;> simp [hs]
  | ptr el =>
    simp only [hu] at h
    rcases h with rfl | ⟨pb, poff, rfl⟩ <;>
      simp [castVal, hu, CTy.unqual, CTy.isVoid, CTy.intKind?]
  | fnPtr r ps var =>
    simp only [hu] at h
    rcases h with rfl | ⟨s, rfl⟩ <;>
      simp [castVal, hu, CTy.unqual, CTy.isVoid, CTy.intKind?]
  | vaList =>
    simp only [hu] at h
    subst h
    simp [castVal, hu, CTy.unqual, CTy.isVoid, CTy.intKind?]
  | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
    simp [hu] at h

theorem ValScalarTyped.align_eq_sizeof {tags : TypeEnv} {ty : CTy} {v : Val}
    (h : ValScalarTyped ty v) :
    0 < alignofTy tags ty ∧ alignofTy tags ty ≤ sizeofTy tags ty := by
  unfold ValScalarTyped at h
  rw [← alignofTy_unqual, ← sizeofTy_unqual]
  cases hu : ty.unqual with
  | int k =>
    simp only [sizeofTy_int, alignofTy_int]
    cases k <;> decide
  | enumTy _ _ =>
    unfold alignofTy alignofAux sizeofTy sizeofAux
    decide
  | ptr _ | fnPtr _ _ _ | vaList =>
    unfold alignofTy alignofAux sizeofTy sizeofAux
    decide
  | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
    simp [hu] at h

theorem writeVal_scalar_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {ty : CTy} {v : Val}
    (hnc : ty.isConst = false) (hb : m.blocks b = some blk) (hrw : blk.perm = .rw)
    (hin : Mem.inBounds blk off (sizeofTy tags ty) = true)
    (hal : Mem.isAligned blk off (alignofTy tags ty) = true)
    (ht : ValScalarTyped ty v) :
    ∃ m', Sem.writeVal m b off ty v = some m' ∧
      (∃ bs, bs.length = sizeofTy tags ty ∧ m.writeBytes b off bs = some m') ∧
      Sem.readVal tags m' b off ty = some v := by
  have hal' : Mem.isAligned blk off (alignofTy tags ty.unqual) = true := by
    rwa [alignofTy_unqual]
  have hin' : Mem.inBounds blk off (sizeofTy tags ty.unqual) = true := by
    rwa [sizeofTy_unqual]
  unfold ValScalarTyped at ht
  cases hu : ty.unqual with
  | int k =>
    simp only [hu] at ht
    rcases ht with ⟨bv, rfl⟩
    simp only [hu, alignofTy_int, sizeofTy_int] at hal' hin'
    have hvi : valAsInt? (.int k bv) = some (k, valIntNum k bv) := rfl
    obtain ⟨m', hm'⟩ := writeVal_int_some hnc hu hb hrw hal' hin' hvi
    have hwb : m.writeBytes b off (Mem.encodeInt k (BitVec.ofInt k.bits (valIntNum k bv))) = some m' := by
      unfold Sem.writeVal at hm'
      simpa [hnc, hb, hu, CTy.unqual, CTy.intKind?, hal', hvi, bind, Option.bind] using hm'
    have hlen : (Mem.encodeInt k (BitVec.ofInt k.bits (valIntNum k bv))).length = sizeofTy tags ty := by
      rw [encodeInt_length, ← sizeofTy_unqual, hu, sizeofTy_int]
    have hbv : BitVec.ofInt k.bits (valIntNum k bv) = bv := bitVec_ofInt_valIntNum_eq k bv
    have hbv_raw : BitVec.ofInt k.bits (if k.signed = true then bv.toInt else ↑bv.toNat) = bv := by
      simpa [valIntNum] using hbv
    have hwb_raw : m.writeBytes b off (Mem.encodeInt k bv) = some m' := by
      rwa [hbv] at hwb
    have hm'_simp : Sem.writeVal m b off (.int k) (.int k bv) = some m' := by
      unfold Sem.writeVal
      simp [hb, CTy.isConst, CTy.unqual, CTy.intKind?, hal', hbv_raw, hwb_raw, bind, Option.bind]
    have hrd : Sem.readVal tags m' b off ty = some (.int k bv) := by
      have hrd0 := readVal_writeVal_same_int tags hb hm'_simp
      unfold Sem.readVal at hrd0 ⊢
      rw [← cty_unqual_idem ty, hu]
      exact hrd0
    exact ⟨m', hm', ⟨_, hlen, hwb⟩, hrd⟩
  | enumTy tag isU =>
    simp only [hu] at ht
    rcases ht with ⟨bv, rfl⟩
    have hals : alignofTy tags (.enumTy tag isU) = 4 := by unfold alignofTy alignofAux; rfl
    have hszs : sizeofTy tags (.enumTy tag isU) = 4 := by unfold sizeofTy sizeofAux; rfl
    have hszty : sizeofTy tags ty = 4 := by rw [← sizeofTy_unqual, hu, hszs]
    rw [hu, hals] at hal'; rw [hu, hszs] at hin'
    cases isU
    · exact writeVal_enum_aux hnc hb hrw hin' hal' hu rfl rfl rfl hszty
    · exact writeVal_enum_aux hnc hb hrw hin' hal' hu rfl rfl rfl hszty
  | ptr el =>
    simp only [hu] at ht
    have hals : alignofTy tags (.ptr el) = 8 := alignofTy_ptr tags el
    have hszs : sizeofTy tags (.ptr el) = 8 := sizeofTy_ptr tags el
    rw [hu, hals] at hal'; rw [hu, hszs] at hin'
    rcases ht with rfl | ⟨pb, poff, rfl⟩
    · have hin2 : Mem.inBounds blk off Mem.encodeNull.length = true := by simpa using hin'
      obtain ⟨m', hwb⟩ := writeBytes_eq_some hb hrw hin2
      have hwr : Sem.writeVal m b off ty .null = some m' := by
        unfold Sem.writeVal
        simp [hnc, hb, hu, hal', hwb, bind, Option.bind]
      obtain ⟨blk', hblk', _, _, hsal_eq, _⟩ := writeBytes_block_props hb hwb
      have halm' : Mem.isAligned blk' off 8 = true := (hsal_eq off 8).trans hal'
      have hrdbytes : m'.readBytes b off 8 = some Mem.encodeNull :=
        readBytes_writeBytes_same hb hwb
      have hrd : Sem.readVal tags m' b off ty = some .null := by
        unfold Sem.readVal
        rw [← cty_unqual_idem ty, hu]
        simp [CTy.unqual, hblk', halm', hrdbytes, bind, Option.bind]
      exact ⟨m', hwr, ⟨_, by rw [← sizeofTy_unqual, hu, hszs]; simp, hwb⟩, hrd⟩
    · have hin2 : Mem.inBounds blk off (Mem.encodePtr pb poff).length = true := by simpa using hin'
      obtain ⟨m', hwb⟩ := writeBytes_eq_some hb hrw hin2
      have hwr : Sem.writeVal m b off ty (.ptr pb poff) = some m' := by
        unfold Sem.writeVal
        simp [hnc, hb, hu, hal', hwb, bind, Option.bind]
      obtain ⟨blk', hblk', _, _, hsal_eq, _⟩ := writeBytes_block_props hb hwb
      have halm' : Mem.isAligned blk' off 8 = true := (hsal_eq off 8).trans hal'
      have hrdbytes : m'.readBytes b off 8 = some (Mem.encodePtr pb poff) :=
        readBytes_writeBytes_same hb hwb
      have hrd : Sem.readVal tags m' b off ty = some (.ptr pb poff) := by
        unfold Sem.readVal
        rw [← cty_unqual_idem ty, hu]
        simp [CTy.unqual, hblk', halm', hrdbytes, bind, Option.bind]
      exact ⟨m', hwr, ⟨_, by rw [← sizeofTy_unqual, hu, hszs]; simp, hwb⟩, hrd⟩
  | fnPtr r ps var =>
    simp only [hu] at ht
    have hals : alignofTy tags (.fnPtr r ps var) = 8 := by unfold alignofTy alignofAux; rfl
    have hszs : sizeofTy tags (.fnPtr r ps var) = 8 := by unfold sizeofTy sizeofAux; rfl
    rw [hu, hals] at hal'; rw [hu, hszs] at hin'
    rcases ht with rfl | ⟨sym, rfl⟩
    · have hin2 : Mem.inBounds blk off Mem.encodeNull.length = true := by simpa using hin'
      obtain ⟨m', hwb⟩ := writeBytes_eq_some hb hrw hin2
      have hwr : Sem.writeVal m b off ty .null = some m' := by
        unfold Sem.writeVal
        simp [hnc, hb, hu, hal', hwb, bind, Option.bind]
      obtain ⟨blk', hblk', _, _, hsal_eq, _⟩ := writeBytes_block_props hb hwb
      have halm' : Mem.isAligned blk' off 8 = true := (hsal_eq off 8).trans hal'
      have hrdbytes : m'.readBytes b off 8 = some Mem.encodeNull :=
        readBytes_writeBytes_same hb hwb
      have hrd : Sem.readVal tags m' b off ty = some .null := by
        unfold Sem.readVal
        rw [← cty_unqual_idem ty, hu]
        simp [CTy.unqual, hblk', halm', hrdbytes, bind, Option.bind]
      exact ⟨m', hwr, ⟨_, by rw [← sizeofTy_unqual, hu, hszs]; simp, hwb⟩, hrd⟩
    · have hin2 : Mem.inBounds blk off (Mem.encodeFnPtr sym).length = true := by simpa using hin'
      obtain ⟨m', hwb⟩ := writeBytes_eq_some hb hrw hin2
      have hwr : Sem.writeVal m b off ty (.fnPtr sym) = some m' := by
        unfold Sem.writeVal
        simp [hnc, hb, hu, hal', hwb, bind, Option.bind]
      obtain ⟨blk', hblk', _, _, hsal_eq, _⟩ := writeBytes_block_props hb hwb
      have halm' : Mem.isAligned blk' off 8 = true := (hsal_eq off 8).trans hal'
      have hrdbytes : m'.readBytes b off 8 = some (Mem.encodeFnPtr sym) :=
        readBytes_writeBytes_same hb hwb
      have hrd : Sem.readVal tags m' b off ty = some (.fnPtr sym) := by
        unfold Sem.readVal
        rw [← cty_unqual_idem ty, hu]
        simp [CTy.unqual, hblk', halm', hrdbytes, bind, Option.bind]
      exact ⟨m', hwr, ⟨_, by rw [← sizeofTy_unqual, hu, hszs]; simp, hwb⟩, hrd⟩
  | vaList =>
    simp only [hu] at ht
    subst ht
    have hszs : sizeofTy tags .vaList = 24 := by unfold sizeofTy sizeofAux; rfl
    rw [hu, hszs] at hin'
    have hin2 : Mem.inBounds blk off (List.replicate 24 (MemByte.byte 1)).length = true := by
      simpa using hin'
    obtain ⟨m', hwb⟩ := writeBytes_eq_some hb hrw hin2
    have hwr : Sem.writeVal m b off ty (.vaList true) = some m' := by
      unfold Sem.writeVal
      simp only [hnc, Bool.not_false, guard_true, hb, hu, bind, Option.bind]
      exact hwb
    have hrdbytes : m'.readBytes b off 24 = some (List.replicate 24 (.byte 1)) :=
      readBytes_writeBytes_same hb (by simpa using hwb)
    have hrd : Sem.readVal tags m' b off ty = some (.vaList true) := by
      unfold Sem.readVal
      rw [← cty_unqual_idem ty, hu]
      simp only [CTy.unqual, sizeofTy, sizeofAux, hrdbytes, bind, Option.bind]
      decide
    exact ⟨m', hwr, ⟨_, by rw [← sizeofTy_unqual, hu, hszs]; simp, hwb⟩, hrd⟩
  | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
    simp [hu] at ht

theorem readBytes_writeBytes_disjoint {m m' : Mem} {b : BlockId} {o1 o2 : Int64}
    {bs : List MemByte} {len2 : Nat} {blk : Block}
    (hb : m.blocks b = some blk)
    (hwb : m.writeBytes b o1 bs = some m')
    (ho1 : 0 ≤ o1.toInt) (ho2 : 0 ≤ o2.toInt)
    (hdisj : o1.toInt + bs.length ≤ o2.toInt ∨ o2.toInt + len2 ≤ o1.toInt) :
    m'.readBytes b o2 len2 = m.readBytes b o2 len2 := by
  obtain ⟨blk', hblk', _, hin_eq, _, hbytes⟩ := writeBytes_block_props hb hwb
  unfold Mem.readBytes
  rw [hb, hblk']
  simp only [bind, Option.bind, hin_eq o2 len2]
  by_cases hin : Mem.inBounds blk o2 len2 = true
  · simp only [hin, guard_true, pure, Pure.pure]
    apply congrArg some
    apply List.map_congr_left
    intro i hi
    have hlt := List.mem_range.mp hi
    have hnot : ¬ (o1.toNatClampNeg ≤ o2.toNatClampNeg + i ∧
        o2.toNatClampNeg + i < o1.toNatClampNeg + bs.length) := by
      simp only [Int64.toNatClampNeg]
      omega
    rw [hbytes]
    simp [hnot]
  · have hinf : Mem.inBounds blk o2 len2 = false := Bool.eq_false_iff.mpr hin
    simp [hinf, guard, failure]

theorem readVal_writeBytes_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId} {o1 o2 : Int64}
    {bs : List MemByte} {ty2 : CTy} {blk : Block}
    (hb : m.blocks b = some blk) (hwb : m.writeBytes b o1 bs = some m')
    (ho1 : 0 ≤ o1.toInt) (ho2 : 0 ≤ o2.toInt)
    (hdisj : o1.toInt + bs.length ≤ o2.toInt ∨ o2.toInt + sizeofTy tags ty2 ≤ o1.toInt) :
    Sem.readVal tags m' b o2 ty2 = Sem.readVal tags m b o2 ty2 := by
  have hblk' := writeBytes_blocks_eq hb hwb
  have hrb (len : Nat) (hlen : len ≤ sizeofTy tags ty2.unqual) :
      m'.readBytes b o2 len = m.readBytes b o2 len :=
    readBytes_writeBytes_disjoint hb hwb ho1 ho2 (by rw [sizeofTy_unqual] at hlen; omega)
  unfold Sem.readVal
  cases hu : ty2.unqual with
  | int k =>
    have hrb' := hrb k.bytes (by rw [hu, sizeofTy_int]; exact Nat.le_refl _)
    simp only [CTy.unqual, CTy.intKind?, hb, hblk', bind, Option.bind]
    congr 2
    funext _
    rw [hrb']
  | ptr _ =>
    have hrb' := hrb 8 (by rw [hu, sizeofTy_ptr]; exact Nat.le_refl _)
    simp only [hb, hblk', bind, Option.bind]
    congr 2
    funext _
    rw [hrb']
  | array _ _ => rfl
  | enumTy tag isU =>
    let k := if isU then IntKind.u32 else IntKind.i32
    have hsz : k.bytes ≤ sizeofTy tags (.enumTy tag isU) := by cases isU <;> unfold sizeofTy sizeofAux <;> decide
    have hrb' := hrb k.bytes (by rw [hu]; exact hsz)
    simp only [CTy.unqual, CTy.intKind?, hb, hblk', bind, Option.bind]
    congr 2
    funext _
    rw [hrb']
  | fnPtr r ps var =>
    have hsz : 8 ≤ sizeofTy tags (.fnPtr r ps var) := by unfold sizeofTy sizeofAux; decide
    have hrb' := hrb 8 (by rw [hu]; exact hsz)
    simp only [hb, hblk', bind, Option.bind]
    congr 2
    funext _
    rw [hrb']
  | vaList =>
    have hrb' := hrb (sizeofTy tags .vaList) (by rw [hu]; exact Nat.le_refl _)
    simp only [bind, Option.bind]
    rw [hrb']
  | void | const_ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ => rfl

/-- Writing scalar/pointer/fnPtr field `fld` of a `.rw` `StructCell` succeeds,
preserves `StructCell`, and establishes `HasField` with the newly stored value. -/
theorem StructCell.writeField_some {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {structTag fld : String} {foff : Nat} {fty : CTy} {v : Val}
    (hs : StructCell tags m b off structTag true)
    (hfl : fieldLayout? tags (.structTy structTag) fld = some (foff, fty))
    (hnc : fty.isConst = false)
    (hle : foff + sizeofTy tags fty ≤ sizeofTy tags (.structTy structTag))
    (hdiv_al : alignofTy tags fty ∣ alignofTy tags (.structTy structTag))
    (hdiv_off : alignofTy tags fty ∣ foff)
    (ht : ValScalarTyped fty v) :
    ∃ m', Sem.writeVal m b (Int64.ofInt (off.toInt + foff)) fty v = some m' ∧
      StructCell tags m' b off structTag true ∧
      HasField tags m' b off structTag fld v ∧
      (∃ bs, bs.length = sizeofTy tags fty ∧ m.writeBytes b (Int64.ofInt (off.toInt + foff)) bs = some m') := by
  rcases hs with ⟨blk, hblk, hrw, hin, hsal⟩
  have hperm := hrw rfl
  have hlt63 : off.toInt + (foff : Int) < 2 ^ 63 := by
    have := blk.sizeLt; rw [ptrDiffLimit_val] at this
    have := (inBounds_iff.mp hin).2; omega
  have hin_fld : Mem.inBounds blk (Int64.ofInt (off.toInt + foff)) (sizeofTy tags fty) = true :=
    inBounds_add hin hle
  obtain ⟨hal_pos, _⟩ := ht.align_eq_sizeof
  have hal_base : Mem.isAligned blk off (alignofTy tags fty) = true := by
    rw [isAligned_iff] at hsal ⊢
    exact ⟨hsal.1, hal_pos, Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hdiv_al (Nat.dvd_of_mod_eq_zero hsal.2.2))⟩
  have hal_fld : Mem.isAligned blk (Int64.ofInt (off.toInt + foff)) (alignofTy tags fty) = true :=
    isAligned_add hal_base hdiv_off hlt63
  obtain ⟨m', hm', ⟨bs, hbs_len, hwb⟩, hrd⟩ :=
    writeVal_scalar_some hnc hblk hperm hin_fld hal_fld ht
  have hblk' := writeBytes_blocks_eq hblk hwb
  have hs' : StructCell tags m' b off structTag true := by
    refine ⟨_, hblk', fun _ => hperm, ?_, ?_⟩
    · simpa [Mem.inBounds] using hin
    · simpa [Mem.isAligned] using hsal
  exact ⟨m', hm', hs', ⟨foff, fty, hfl, hrd⟩, ⟨bs, hbs_len, hwb⟩⟩

/-- Writing a disjoint field `fld1` (`foff1` of size `sz1`) on `(b, off)` preserves `HasField` on `fld2`. -/
theorem HasField.of_writeField_disjoint {tags : TypeEnv} {m m' : Mem} {b : BlockId} {off : Int64}
    {structTag fld2 : String} {v2 : Val} {foff1 sz1 foff2 : Nat} {fty2 : CTy}
    {bs : List MemByte}
    (hs : StructCell tags m b off structTag false)
    (hwb : m.writeBytes b (Int64.ofInt (off.toInt + foff1)) bs = some m')
    (hbs_len : bs.length = sz1)
    (hle1 : foff1 + sz1 ≤ sizeofTy tags (.structTy structTag))
    (hf2 : fieldLayout? tags (.structTy structTag) fld2 = some (foff2, fty2))
    (hle2 : foff2 + sizeofTy tags fty2 ≤ sizeofTy tags (.structTy structTag))
    (hval2 : Sem.readVal tags m b (Int64.ofInt (off.toInt + foff2)) fty2 = some v2)
    (hdisj : foff1 + sz1 ≤ foff2 ∨ foff2 + sizeofTy tags fty2 ≤ foff1) :
    HasField tags m' b off structTag fld2 v2 := by
  rcases hs with ⟨blk, hblk, _, hin, _⟩
  have ⟨ho, hlen⟩ := inBounds_iff.mp hin
  have hszlt := blk.sizeLt
  rw [ptrDiffLimit_val] at hszlt
  have h1 := int64_ofInt_toInt (x := off.toInt + foff1) (by omega) (by omega)
  have h2 := int64_ofInt_toInt (x := off.toInt + foff2) (by omega) (by omega)
  have hrd' := readVal_writeBytes_disjoint (tags := tags)
    (o2 := Int64.ofInt (off.toInt + foff2)) (ty2 := fty2) hblk hwb
    (by omega) (by omega) (by rw [h1, h2, hbs_len]; omega)
  exact ⟨foff2, fty2, hf2, hrd'.trans hval2⟩

theorem StructCell.isAligned_field {tags : TypeEnv} {blk : Block} {off : Int64}
    {structTag : String} {foff : Nat} {fty : CTy}
    (hin : Mem.inBounds blk off (sizeofTy tags (.structTy structTag)) = true)
    (hsal : Mem.isAligned blk off (alignofTy tags (.structTy structTag)) = true)
    (hpos : 0 < alignofTy tags fty)
    (hdiv_al : alignofTy tags fty ∣ alignofTy tags (.structTy structTag))
    (hdiv_off : alignofTy tags fty ∣ foff)
    (hle : foff + sizeofTy tags fty ≤ sizeofTy tags (.structTy structTag)) :
    Mem.isAligned blk (Int64.ofInt (off.toInt + foff)) (alignofTy tags fty) = true := by
  have ⟨ho, hlen⟩ := inBounds_iff.mp hin
  have hszlt := blk.sizeLt; rw [ptrDiffLimit_val] at hszlt
  have hal_base : Mem.isAligned blk off (alignofTy tags fty) = true := by
    rw [isAligned_iff] at hsal ⊢
    exact ⟨hsal.1, hpos, Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hdiv_al (Nat.dvd_of_mod_eq_zero hsal.2.2))⟩
  exact isAligned_add hal_base hdiv_off (by omega)

theorem writeVal_castVal_eq {m : Mem} {b : BlockId} {off : Int64}
    {ty : CTy} {v cv : Val}
    (ht : ValScalarTyped ty cv)
    (hc : Sem.castVal m ty v = some cv)
    (hcompat : (∃ (k1 : IntKind) (bv1 : BitVec k1.bits), v = .int k1 bv1) ∨ v = cv) :
    Sem.writeVal m b off ty v = Sem.writeVal m b off ty cv := by
  rcases hcompat with ⟨k1, bv1, rfl⟩ | rfl
  · by_cases hnc : ty.isConst = true
    · unfold Sem.writeVal
      simp [hnc, bind, Option.bind, guard, failure]
    · have hncf : ty.isConst = false := Bool.eq_false_iff.mpr hnc
      unfold ValScalarTyped at ht
      unfold Sem.castVal at hc
      unfold Sem.writeVal
      dsimp only at hc ⊢
      simp only [hncf, Bool.not_false, guard_true, bind, Option.bind]
      cases hu : ty.unqual with
      | int k =>
        simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, ↓reduceIte, Bool.false_eq_true,
          Sem.ofIntCast, Option.some.injEq] at hc
        subst hc
        simp only [CTy.unqual, CTy.intKind?]
        cases hblk : m.blocks b with
        | none => rfl
        | some blk =>
          cases ha : Mem.isAligned blk off k.align with
          | false => simp [ha, guard, failure]
          | true =>
            have heq := bitVec_ofInt_valIntNum_eq k
              (BitVec.ofInt k.bits (if k1.signed then bv1.toInt else (bv1.toNat : Int)))
            dsimp only [valIntNum] at heq
            simp only [ha, guard, ite_true, pure, Pure.pure, valAsInt?_int, heq]
      | enumTy tag isU =>
        simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, ↓reduceIte, Bool.false_eq_true,
          Sem.ofIntCast, Option.some.injEq] at hc
        subst hc
        simp only [CTy.unqual, CTy.intKind?]
        cases hblk : m.blocks b with
        | none => rfl
        | some blk =>
          cases ha : Mem.isAligned blk off (if isU then IntKind.u32 else IntKind.i32).align with
          | false => simp [ha, guard, failure]
          | true =>
            have heq := bitVec_ofInt_valIntNum_eq (if isU then IntKind.u32 else IntKind.i32)
              (BitVec.ofInt (if isU then IntKind.u32 else IntKind.i32).bits
                (if k1.signed then bv1.toInt else (bv1.toNat : Int)))
            dsimp only [valIntNum] at heq
            simp only [ha, guard, ite_true, pure, Pure.pure, valAsInt?_int, heq]
      | ptr el =>
        simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hz : (bv1.toNat == 0) = true
        · simp only [hz, ↓reduceIte, Option.some.injEq] at hc
          subst hc
          cases hblk : m.blocks b with
          | none => rfl
          | some blk =>
            cases ha : Mem.isAligned blk off 8 with
            | false => simp [ha, guard, failure]
            | true => simp [ha, guard, hz]
        · have hzf : (bv1.toNat == 0) = false := Bool.eq_false_iff.mpr hz
          simp [hzf] at hc
      | fnPtr r ps var =>
        simp only [hu, CTy.unqual, CTy.isVoid, CTy.intKind?, Bool.false_eq_true, ↓reduceIte] at hc
        by_cases hz : (bv1.toNat == 0) = true
        · simp only [hz, ↓reduceIte, Option.some.injEq] at hc
          subst hc
          cases hblk : m.blocks b with
          | none => rfl
          | some blk =>
            cases ha : Mem.isAligned blk off 8 with
            | false => simp [ha, guard, failure]
            | true => simp [ha, guard, hz]
        · have hzf : (bv1.toNat == 0) = false := Bool.eq_false_iff.mpr hz
          simp [hzf] at hc
      | vaList =>
        simp [hu, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
      | void | const_ _ | array _ _ | structTy _ | unionTy _ | anonStruct _ | anonUnion _ | typedef _ _ =>
        simp [hu] at ht
  · rfl

theorem castVal_applyBinary_add_compat {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {oldV newV cv : Val} {lty newTy : CTy} {d : Int}
    (hbin : Sem.applyBinary cfg tags m .add oldV lty (.int .i32 (BitVec.ofInt 32 d)) (.int .i32) = some (newV, newTy))
    (hc : Sem.castVal m lty newV = some cv) :
    (∃ (k1 : IntKind) (bv1 : BitVec k1.bits), newV = .int k1 bv1) ∨ newV = cv := by
  unfold Sem.applyBinary at hbin
  dsimp only at hbin
  cases hlt : lty.isPtr with
  | true =>
    simp only [hlt, Bool.true_or, ↓reduceIte] at hbin
    cases hu1 : lty.unqual
    case ptr el =>
      have hi32 : IntKind.i32.signed = true := rfl
      simp only [hu1, Sem.valAsInt?, hi32, ↓reduceIte] at hbin
      unfold Option.map at hbin
      dsimp only at hbin
      split at hbin
      · rename_i pv hadd
        rcases hbin with ⟨rfl, _⟩
        have hpv : newV = .null ∨ ∃ pb poff, newV = .ptr pb poff := by
          unfold Sem.evalPtrAdd at hadd
          cases oldV
          case ptr b off =>
            dsimp only at hadd
            split at hadd
            · cases hadd; exact .inr ⟨b, off, rfl⟩
            · simp only [bind, Option.bind] at hadd
              cases hb : m.blocks b with
              | none => simp [hb] at hadd
              | some blk =>
                simp only [hb, guard, pure, Pure.pure, failure] at hadd
                split at hadd
                · cases hadd
                · cases hadd; exact .inr ⟨b, _, rfl⟩
          case null =>
            dsimp only at hadd
            split at hadd <;> cases hadd
            exact .inl rfl
          all_goals simp at hadd
        rcases hpv with rfl | ⟨pb, poff, rfl⟩
        · right
          unfold Sem.castVal at hc
          simp [hu1, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
          exact hc
        · right
          unfold Sem.castVal at hc
          simp [hu1, CTy.unqual, CTy.isVoid, CTy.intKind?] at hc
          exact hc
      · cases hbin
    all_goals simp [hu1] at hbin
  | false =>
    have ht2p : (CTy.int .i32).isPtr = false := rfl
    simp only [hlt, ht2p, Bool.or_false, Bool.false_or] at hbin
    split at hbin
    · simp only [CTy.unqual] at hbin; cases hbin
    · simp only [CTy.unqual, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hbin
      unfold Sem.evalIntBinary at hbin
      cases hv1 : Sem.valAsInt? oldV with
      | none => simp [hv1] at hbin
      | some p1 =>
        have hi32 : Sem.valAsInt? (.int .i32 (BitVec.ofInt 32 d)) = some (.i32, (BitVec.ofInt 32 d).toInt) := rfl
        rw [hv1, hi32] at hbin
        dsimp only [bind, Option.bind, pure, Pure.pure] at hbin
        split at hbin
        · cases hbin
        · rename_i _ res ho
          cases Option.some.inj hbin
          unfold Sem.ofIntExact at ho
          split at ho
          · split at ho <;> cases ho; left; exact ⟨_, _, rfl⟩
          · cases ho; left; exact ⟨_, _, rfl⟩

theorem strlenAt_of_blocks_eq {m1 m2 : Mem} {b : BlockId} {off : Int64}
    (heq : m2.blocks b = m1.blocks b) :
    m2.strlenAt b off = m1.strlenAt b off := by
  unfold Mem.strlenAt
  simp only [heq]

theorem memchrStep_of_blocks_eq {m1 m2 : Mem} {b : BlockId} {off : Int64} {c : UInt8} {n : Nat}
    (heq : m2.blocks b = m1.blocks b) :
    Libc.memchrStep m2 b off c n = Libc.memchrStep m1 b off c n := by
  unfold Libc.memchrStep
  simp only [heq]

theorem printfFmtOk_of_blocks_eq {m1 m2 : Mem} {bf : BlockId} {of_ : Int64}
    (heq : m2.blocks bf = m1.blocks bf) :
    Libc.printfFmtOk m1 bf of_ → Libc.printfFmtOk m2 bf of_ := by
  rintro ⟨flen, rawFmt, fmtBytes, hs, hr, hc, hpn⟩
  refine ⟨flen, rawFmt, fmtBytes, ?_, ?_, hc, hpn⟩
  · rwa [strlenAt_of_blocks_eq heq]
  · unfold Mem.readBytes at hr ⊢
    rwa [heq]

end C99.Proof.VCGen
