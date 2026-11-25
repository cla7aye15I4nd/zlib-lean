import Zlib.Proof.Crc32Base

/-!
# Safety Proofs for `crc32_combine*` Functions (`Zlib.Proof.Crc32Combine`)
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec Zlib.Crc32

/-! ## 4. Expression & Statement WP Combinators -/

private theorem bitVec_ofInt_toNat (n : Nat) (v : BitVec n) :
    BitVec.ofInt n (v.toNat : Int) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)]
  rfl

private theorem bitVec_ofInt_toInt (n : Nat) (v : BitVec n) :
    BitVec.ofInt n v.toInt = v :=
  BitVec.ofInt_toInt

private theorem isTruthy_int {k : IntKind} (v : BitVec k.bits) :
    Sem.isTruthy (.int k v) = some (v != 0#k.bits) := by
  dsimp only [Sem.isTruthy]
  by_cases hv : v = 0#k.bits
  · subst hv; rfl
  · have hnz : v.toNat ≠ 0 := fun h0 => hv (BitVec.eq_of_toNat_eq h0)
    have h1 : (v.toNat != 0) = true := bne_iff_ne.mpr hnz
    have h2 : (v != 0#k.bits) = true := bne_iff_ne.mpr hv
    rw [h1, h2]

private theorem castVal_int_eq {m : Mem} {ty : CTy} {k1 k2 : IntKind}
    (hk2 : ty.unqual = .int k2) (v : BitVec k1.bits) :
    Sem.castVal m ty (.int k1 v) =
      some (.int k2 (BitVec.ofInt k2.bits (if k1.signed then v.toInt else (v.toNat : Int)))) := by
  rw [castVal_unqual, hk2]
  unfold Sem.castVal
  simp only [CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast, Bool.false_eq_true, ↓reduceIte]

private theorem castVal_u32_to_u64 (m : Mem) {ty : CTy} (hk : ty.unqual = .int .u64) (v : BitVec 32) :
    Sem.castVal m ty (.int .u32 v) = some (.int .u64 (v.zeroExtend 64)) := by
  refine (castVal_int_eq (m := m) (k1 := .u32) (k2 := .u64) hk v).trans ?_
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast (by omega : v.toNat < 2 ^ 64)),
    Int.toNat_natCast, Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64)]

private theorem castVal_i64_to_i64 (m : Mem) {ty : CTy} (hk : ty.unqual = .int .i64) (v : BitVec 64) :
    Sem.castVal m ty (.int .i64 v) = some (.int .i64 v) := by
  refine (castVal_int_eq (m := m) (k1 := .i64) (k2 := .i64) hk v).trans ?_
  refine congrArg (fun z : BitVec IntKind.i64.bits => some (Val.int .i64 z)) ?_
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, bitVec_ofInt_toInt]

private theorem evalIntBinary_u32_and_i32 (v1 : BitVec 32) (n : Int) :
    Sem.evalIntBinary .bitAnd (.int .u32 v1) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u32 (v1 &&& BitVec.ofInt 32 n), .int .u32) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u32 .i32 = .u32 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  refine congrArg (fun z : BitVec IntKind.u32.bits => some (Val.int .u32 z, CTy.int .u32)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte,
    bitVec_ofInt_toNat, bitVec_ofInt_toInt]
  rfl

private theorem evalIntBinary_u64_and_u64 (v1 v2 : BitVec 64) :
    Sem.evalIntBinary .bitAnd (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 &&& v2), .int .u64) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .u64 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u64_and_u32 (v1 : BitVec 64) (v2 : BitVec 32) :
    Sem.evalIntBinary .bitAnd (.int .u64 v1) (.int .u32 v2) =
      some (.int .u64 (v1 &&& v2.zeroExtend 64), .int .u64) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .u32 = .u64 := rfl
  have hze : BitVec.ofInt 64 (v2.toNat : Int) = v2.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.zeroExtend, BitVec.toNat_setWidth,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast (by omega : v2.toNat < 2 ^ 64)),
      Int.toNat_natCast, Nat.mod_eq_of_lt (by omega : v2.toNat < 2 ^ 64)]
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hze]
  rfl

private theorem evalIntBinary_u64_and_i32 (v1 : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .bitAnd (.int .u64 v1) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u64 (v1 &&& BitVec.ofInt 64 n), .int .u64) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hto]
  rfl

private theorem evalIntBinary_u64_xor_u64 (v1 v2 : BitVec 64) :
    Sem.evalIntBinary .bitXor (.int .u64 v1) (.int .u64 v2) = some (.int .u64 (v1 ^^^ v2), .int .u64) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .u64 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u64_xor_u32 (v1 : BitVec 64) (v2 : BitVec 32) :
    Sem.evalIntBinary .bitXor (.int .u64 v1) (.int .u32 v2) =
      some (.int .u64 (v1 ^^^ v2.zeroExtend 64), .int .u64) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u64 .u32 = .u64 := rfl
  have hze : BitVec.ofInt 64 (v2.toNat : Int) = v2.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.zeroExtend, BitVec.toNat_setWidth,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast (by omega : v2.toNat < 2 ^ 64)),
      Int.toNat_natCast, Nat.mod_eq_of_lt (by omega : v2.toNat < 2 ^ 64)]
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hze]
  rfl

private theorem evalIntBinary_u64_shl_i32 (v : BitVec 64) {sh : Nat} (hsh : sh < 64) :
    Sem.evalIntBinary .shl (.int .u64 v) (Sem.ofIntCast .i32 (sh : Int)) =
      some (.int .u64 (v <<< sh), .int .u64) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hpr : IntKind.promote .u64 = .u64 := rfl
  have hbits32 : IntKind.i32.bits = 32 := rfl
  have hto : (BitVec.ofInt IntKind.i32.bits (sh : Int)).toInt = (sh : Int) := by
    rw [hbits32, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have htonat : ((sh : Int)).toNat = sh := Int.toNat_natCast sh
  have hbits64 : (IntKind.u64.bits : Int) = 64 := rfl
  have hg : (0 ≤ (sh : Int) && (sh : Int) < (64 : Int)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hpr, hbits64]
  simp only [IntKind.signed, hto, htonat, hg, guard_true, Bool.false_eq_true, ↓reduceIte]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u64_shr_i32 (v : BitVec 64) {sh : Nat} (hsh : sh < 64) :
    Sem.evalIntBinary .shr (.int .u64 v) (Sem.ofIntCast .i32 (sh : Int)) =
      some (.int .u64 (v >>> sh), .int .u64) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hpr : IntKind.promote .u64 = .u64 := rfl
  have hbits32 : IntKind.i32.bits = 32 := rfl
  have hto : (BitVec.ofInt IntKind.i32.bits (sh : Int)).toInt = (sh : Int) := by
    rw [hbits32, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have htonat : ((sh : Int)).toNat = sh := Int.toNat_natCast sh
  have hbits64 : (IntKind.u64.bits : Int) = 64 := rfl
  have hg : (0 ≤ (sh : Int) && (sh : Int) < (64 : Int)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hpr, hbits64]
  simp only [IntKind.signed, hto, htonat, hg, guard_true, Bool.false_eq_true, ↓reduceIte]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u64_sub_i32 (v1 : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .sub (.int .u64 v1) (Sem.ofIntCast .i32 n) =
      some (.int .u64 (v1 - BitVec.ofInt 64 n), .int .u64) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hua : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hbits32 : IntKind.i32.bits = 32 := rfl
  have hto : (BitVec.ofInt IntKind.i32.bits n).toInt = n := by
    rw [hbits32, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hsub : BitVec.ofInt 64 ((v1.toNat : Int) - ((BitVec.ofInt 64 n).toNat : Int)) =
      v1 - BitVec.ofInt 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_sub]
    have hnat : (BitVec.ofInt 64 n).toNat = n.toNat := by
      rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hn0 (by exact_mod_cast (by omega : n < 2 ^ 64))]
    rw [hnat]
    have hvlt : v1.toNat < 2 ^ 64 := v1.isLt
    have hnlt : n.toNat < 2 ^ 64 := by omega
    omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  simp only [IntKind.signed, Sem.ofIntExact, Bool.false_eq_true, ↓reduceIte, hto]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toNat, hsub]

private theorem evalIntBinary_u64_eq_zero (v : BitVec 64) :
    Sem.evalIntBinary .eq (.int .u64 v) (Sem.ofIntCast .i32 0) =
      some (.int .i32 (if v == 0#64 then 1#32 else 0#32), .int .i32) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hua : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have h0nat' : ((BitVec.ofInt 64 0).toNat : Int) = 0 := rfl
  have hcond : Sem.cmpOrd .eq (v.toNat : Int) 0 = (v == 0#64) := by
    unfold Sem.cmpOrd
    by_cases hv : v = 0#64
    · subst hv; rfl
    · have hnz : v.toNat ≠ 0 := fun h0' => hv (BitVec.eq_of_toNat_eq h0')
      have hbeq : (v == 0#64) = false := beq_false_of_ne hv
      rw [hbeq]
      simp only [beq_iff_eq, decide_eq_false_iff_not]
      exact Int.natCast_ne_zero.mpr hnz
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toNat, show (BitVec.ofInt 32 0).toInt = 0 from rfl, h0nat', hcond]
  cases (v == 0#64) <;> rfl

private theorem evalIntBinary_i64_lt_zero (v : BitVec 64) :
    Sem.evalIntBinary .lt (.int .i64 v) (Sem.ofIntCast .i32 0) =
      some (.int .i32 (if v.toInt < 0 then 1#32 else 0#32), .int .i32) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hua : IntKind.usualArith .i64 .i32 = .i64 := rfl
  have h0int : (BitVec.ofInt 64 0).toInt = 0 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  simp only [IntKind.signed, ↓reduceIte]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toInt, show (BitVec.ofInt 32 0).toInt = 0 from rfl, h0int]
  by_cases h : v.toInt < 0
  · have ht : Sem.cmpOrd .lt v.toInt 0 = true := decide_eq_true h
    rw [ht]; simp only [h, ↓reduceIte]; rfl
  · have hf : Sem.cmpOrd .lt v.toInt 0 = false := decide_eq_false h
    rw [hf]; simp only [h, ↓reduceIte]; rfl

private theorem evalIntBinary_i64_and_1 (v : BitVec 64) :
    Sem.evalIntBinary .bitAnd (.int .i64 v) (Sem.ofIntCast .i32 1) =
      some (.int .i64 (v &&& 1#64), .int .i64) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hua : IntKind.usualArith .i64 .i32 = .i64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  simp only [IntKind.signed, ↓reduceIte]
  refine congrArg (fun z : BitVec IntKind.i64.bits => some (Val.int .i64 z, CTy.int .i64)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toInt, show (BitVec.ofInt 32 1).toInt = 1 from rfl]
  rfl

private theorem evalIntBinary_i64_shr_1 {v : BitVec 64} (hv : 0 ≤ v.toInt) :
    Sem.evalIntBinary .shr (.int .i64 v) (Sem.ofIntCast .i32 1) =
      some (.int .i64 (BitVec.ofInt 64 (v.toInt / 2)), .int .i64) := by
  unfold Sem.evalIntBinary Sem.ofIntCast
  have hpr : IntKind.promote .i64 = .i64 := rfl
  have hbits64 : (IntKind.i64.bits : Int) = 64 := rfl
  have hs1 : (if IntKind.i32.signed = true then (BitVec.ofInt IntKind.i32.bits 1).toInt
    else ((BitVec.ofInt IntKind.i32.bits 1).toNat : Int)) = 1 := rfl
  have hgd1 : (guard ((decide (0 ≤ (1 : Int)) && decide ((1 : Int) < (64 : Int))) = true) : Option Unit) = some () := rfl
  have hgd2 : (guard (0 ≤ v.toInt) : Option Unit) = some () := by
    simp only [guard, hv, ↓reduceIte]; rfl
  have h2 : (2 ^ (1 : Int).toNat : Int) = 2 := rfl
  have hin : IntKind.i64.inRange (v.toInt / 2) = true := by
    have hlt := v.toInt_lt
    have hmin : IntKind.i64.minVal = -(2 ^ 63) := rfl
    have hmax : IntKind.i64.maxVal = 2 ^ 63 - 1 := rfl
    unfold IntKind.inRange
    rw [hmin, hmax]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hpr, hbits64, hs1, hgd1]
  dsimp only
  simp only [IntKind.signed, ↓reduceIte]
  erw [hgd2]
  dsimp only
  simp only [IntKind.signed, Sem.ofIntExact, h2,
    show (BinOp.shr == BinOp.shl) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  erw [hin]
  simp only [↓reduceIte]
  rfl

private theorem evalIntBinary_u32_add_1 (v : BitVec 32) :
    Sem.evalIntBinary .add (.int .u32 v) (.int .i32 (BitVec.ofInt 32 1)) =
      some (.int .u32 (v + 1#32), .int .u32) := by
  unfold Sem.evalIntBinary
  have hua : IntKind.usualArith .u32 .i32 = .u32 := rfl
  have h1 : BitVec.ofInt 32 ((v.toNat : Int) + ((BitVec.ofInt 32 1).toNat : Int)) =
      v + 1#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_add]
    have h1eq : (BitVec.ofInt 32 1).toNat = 1 := rfl
    have h1nat : (1#32 : BitVec 32).toNat = 1 := rfl
    have hvlt : v.toNat < 2 ^ 32 := v.isLt
    rw [h1eq, h1nat]
    omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [hua]
  simp only [IntKind.signed, Sem.ofIntExact, Bool.false_eq_true, ↓reduceIte]
  refine congrArg (fun z : BitVec IntKind.u32.bits => some (Val.int .u32 z, CTy.int .u32)) ?_
  simp only [IntKind.bits, bitVec_ofInt_toNat, show (BitVec.ofInt 32 1).toInt = 1 from rfl]
  exact h1

private theorem evalIntBinary_u32_and_31 (v : BitVec 32) :
    Sem.evalIntBinary .bitAnd (.int .u32 v) (Sem.ofIntCast .i32 31) =
      some (.int .u32 (v &&& 31#32), .int .u32) := by
  unfold Sem.ofIntCast
  exact evalIntBinary_u32_and_i32 v 31

private def PureEval (prog : Prog) (cfg : PointerConfig) (env : Env) (m : Mem) (mods : ModSet)
    (e : CExpr) (v : Val) (ty : CTy) : Prop :=
  ∀ {ext : ExtHandler} {Q : Val → Mem → OSState → Prop}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {blks : List BlockId} {os : OSState} {k : Sem.Cont},
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) fs) ctx mods) env blks m os k) →
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m os k)

private theorem pureEval_paren {prog cfg env m mods e v ty}
    (he : PureEval prog cfg env m mods e v ty) :
    PureEval prog cfg env m mods (.paren e) v ty := by
  intro ext Q fs ctx blks os k hw
  exact WPTerm.of_exprPure (by rfl) (he hw)

private theorem pureEval_lit {prog cfg env m mods val k s r} :
    PureEval prog cfg env m mods (.lit val k s r) (Sem.ofIntCast k val) (.int k) := by
  intro ext Q fs ctx blks os kcont hw
  exact WPTerm.of_exprPure (by rfl) hw

private theorem pureEval_var_int {prog cfg env m mods nm b ty ik v}
    (hs : IntSlot env m nm b ty ik v) (hnc : mods.conflicts b 0 ik.bytes = false) :
    PureEval prog cfg env m mods (.var nm) (.int ik v) ty.decay := by
  intro ext Q fs ctx blks os kcont hw
  exact wp_read_int hs hnc hw

private theorem pureEval_var_ptr {prog cfg env m mods nm b ty el p}
    (hs : PtrSlot env m nm b ty el p) (hnc : mods.conflicts b 0 8 = false) :
    PureEval prog cfg env m mods (.var nm) p ty.decay := by
  intro ext Q fs ctx blks os kcont hw
  exact wp_read_ptr hs hnc hw

private theorem pureEval_binary {prog cfg env m mods op l r v1 t1 v2 t2 rv rt}
    (hl : PureEval prog cfg env m mods l v1 t1)
    (hr : PureEval prog cfg env m mods r v2 t2)
    (hbin : Sem.applyBinary cfg prog.tags m op v1 t1 v2 t2 = some (rv, rt)) :
    PureEval prog cfg env m mods (.binary op l r) rv rt := by
  intro ext Q fs ctx blks os kcont hw
  exact WPTerm.of_exprPure (by rfl) (hl (WPTerm.of_exprPure (by rfl) (hr
    (WPTerm.of_exprPure (by simp [Sem.stepExprPure, hbin]) hw))))

private theorem pureEval_binary_int {prog cfg env m mods op l r k1 v1 t1 k2 v2 t2 rv rt}
    (hl : PureEval prog cfg env m mods l (.int k1 v1) t1)
    (hr : PureEval prog cfg env m mods r (.int k2 v2) t2)
    (ht1 : t1.unqual = .int k1) (ht2 : t2.unqual = .int k2)
    (hev : Sem.evalIntBinary op (.int k1 v1) (.int k2 v2) = some (rv, rt)) :
    PureEval prog cfg env m mods (.binary op l r) rv rt :=
  pureEval_binary hl hr (by rw [applyBinary_int ht1 ht2]; exact hev)

private theorem pureEval_cast {prog cfg env m mods cty e v ty cv}
    (he : PureEval prog cfg env m mods e v ty)
    (hcast : Sem.castVal m cty v = some cv) :
    PureEval prog cfg env m mods (.cast cty e) cv cty := by
  intro ext Q fs ctx blks os kcont hw
  exact WPTerm.of_exprPure (by rfl) (he (WPTerm.of_exprPure (by simp [Sem.stepExprPure, hcast]) hw))

private theorem pureEval_cond {prog cfg env m c t f vc tc b vres tres}
    (hc : PureEval prog cfg env m [] c vc tc)
    (htr : Sem.isTruthy vc = some b)
    (hbr : PureEval prog cfg env m [] (if b then t else f) vres tres) :
    PureEval prog cfg env m [] (.cond c t f) vres tres := by
  intro ext Q fs ctx blks os kcont hw
  exact WPTerm.of_exprPure (by rfl) (hc (WPTerm.of_exprPure
    (by simp [Sem.stepExprPure, htr]) (hbr hw)))

private def X2nTableValid (prog : Prog) (gEnv : Env) (m : Mem) : Prop :=
  ∃ bx blk, gEnv.lookup "x2n_table" = some (bx, .array crcConstTy (some 32)) ∧
    m.blocks bx = some blk ∧ blk.size = 128 ∧
    ∀ idx < 32, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m bx (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv) ∧
      bv = BitVec.ofInt 32 Zlib.Tables.x2nTableVals[idx]! ∧
      bv.toNat ≠ 0

private theorem X2nTableValid.of_baseInv {prog gEnv m0 os0 v owned m os}
    (hlib : InitLibzProps prog gEnv m0 os0) (hb : BaseInv m0 os0 v owned m os) :
    X2nTableValid prog gEnv m := by
  obtain ⟨bx, blk, hlu, hblk, _, _, hsz, _, _, hread⟩ := hb.x2n_table hlib
  refine ⟨bx, blk, hlu, hblk, hsz, fun idx hidx => ?_⟩
  obtain ⟨bv, hrv, hval, hnz⟩ := hread idx hidx
  refine ⟨bv, ?_, hval, hnz⟩
  unfold Sem.readVal at hrv ⊢
  simpa [crcConstTy, CTy.unqual] using hrv

private theorem X2nTableValid.of_roExt {prog gEnv m m'}
    (hx : X2nTableValid prog gEnv m) (hro : ROExt m m') :
    X2nTableValid prog gEnv m' := by
  rcases hx with ⟨bx, blk, hlu, hblk, hsz, hread⟩
  have hm' : m'.blocks bx = m.blocks bx := hro.2.1 bx (lt_nextBlock_of_some hblk)
  refine ⟨bx, blk, hlu, by rw [hm', hblk], hsz, fun idx hidx => ?_⟩
  obtain ⟨bv, hrv, hval, hnz⟩ := hread idx hidx
  exact ⟨bv, by rw [readVal_eq_of_blocks_eq prog.tags hm']; exact hrv, hval, hnz⟩

private theorem X2nTableValid.of_localFrameMem {prog gEnv m m' blks}
    (hx : X2nTableValid prog gEnv m) (hf : LocalFrameMem m m' blks) :
    X2nTableValid prog gEnv m' := by
  rcases hx with ⟨bx, blk, hlu, hblk, hsz, hread⟩
  have hm' : m'.blocks bx = m.blocks bx := hf.2.1 bx (lt_nextBlock_of_some hblk)
  refine ⟨bx, blk, hlu, by rw [hm', hblk], hsz, fun idx hidx => ?_⟩
  obtain ⟨bv, hrv, hval, hnz⟩ := hread idx hidx
  exact ⟨bv, by rw [readVal_eq_of_blocks_eq prog.tags hm']; exact hrv, hval, hnz⟩

private theorem evalPtrAdd_some {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {b : BlockId} {off : Int64} {el : CTy} {idx : Int} {blk : Block}
    (hb : m.blocks b = some blk)
    (hoff0 : 0 ≤ off.toInt) (hoff_lt : off.toInt ≤ (blk.size : Int))
    (hlo : 0 ≤ off.toInt + idx * (max 1 (sizeofTy tags el) : Int))
    (hhi : off.toInt + idx * (max 1 (sizeofTy tags el) : Int) ≤ (blk.size : Int)) :
    Sem.evalPtrAdd cfg tags m (.ptr b off) el idx =
      some (.ptr b (Int64.ofInt (off.toInt + idx * (max 1 (sizeofTy tags el) : Int)))) := by
  unfold Sem.evalPtrAdd
  by_cases hz : (idx == 0 && cfg.allowAddZeroAny) = true
  · have hidx0 : idx = 0 := by simpa using (Bool.and_eq_true _ _).mp hz |>.1
    have hlt63 : off.toInt < 2 ^ 63 := by
      have := blk.sizeLt
      rw [ptrDiffLimit_val] at this
      omega
    have heq : Int64.ofInt (off.toInt + idx * (max 1 (sizeofTy tags el) : Int)) = off := by
      subst hidx0
      apply Int64.toInt_inj.mp
      rw [Int.zero_mul, Int.add_zero, int64_ofInt_toInt (by omega) hlt63]
    simp only [hz, ↓reduceIte, heq]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, hb, hlo, hhi, Bool.and_self,
      decide_true, guard_true, bind, Option.bind, pure, Pure.pure]

private theorem pureEval_x2n_table {prog cfg env m gEnv}
    {idxExpr : CExpr} {idxBv : BitVec 32} {idxTy : CTy}
    (hlu : env.lookup "x2n_table" = gEnv.lookup "x2n_table")
    (hx : X2nTableValid prog gEnv m)
    (hidx : PureEval prog cfg env m [] idxExpr (.int .u32 idxBv) idxTy)
    (hidxLt : idxBv.toNat < 32) :
    ∃ bv : BitVec 32,
      PureEval prog cfg env m [] ((CExpr.var "x2n_table").index idxExpr) (.int .u32 bv) crcConstTy.decay ∧
      bv = BitVec.ofInt 32 Zlib.Tables.x2nTableVals[idxBv.toNat]! ∧
      bv.toNat ≠ 0 := by
  rcases hx with ⟨bx, blk, hlux, hm_bx, hsz, hread⟩
  obtain ⟨bv, hrv, hval, hnz⟩ := hread idxBv.toNat hidxLt
  refine ⟨bv, ?_, hval, hnz⟩
  intro ext Q fs ctx blks os1 kcont hw
  have hlu_env : env.lookup "x2n_table" = some (bx, .array crcConstTy (some 32)) := by
    rw [hlu, hlux]
  have hread_arr : Sem.readPlace prog.tags m [] .rval bx 0 (CTy.array crcConstTy (some 32)) =
      some (.rval (.ptr bx 0) (CTy.array crcConstTy (some 32)).decay) := by
    unfold Sem.readPlace; simp only [CTy.unqual]
  have hdec_arr : (CTy.array crcConstTy (some 32)).decay.unqual = .ptr crcConstTy := rfl
  have hsz_elem : sizeofTy prog.tags crcConstTy = 4 := by
    simp only [crcConstTy, sizeofTy_const, sizeofTy_typedef, sizeofTy_int, IntKind.bytes, IntKind.bits]
  have hadd : Sem.evalPtrAdd cfg prog.tags m (.ptr bx 0) crcConstTy (idxBv.toNat : Int) =
      some (.ptr bx (Int64.ofNat (4 * idxBv.toNat))) := by
    have hmax4 : (max 1 (sizeofTy prog.tags crcConstTy) : Int) = 4 := by rw [hsz_elem]; rfl
    have hp := evalPtrAdd_some (cfg := cfg) (tags := prog.tags) (idx := (idxBv.toNat : Int)) hm_bx
      (by rw [Int64.toInt_zero]; omega) (by rw [hsz, Int64.toInt_zero]; decide)
      (by rw [Int64.toInt_zero, hmax4]; omega)
      (by rw [Int64.toInt_zero, hmax4, hsz]; omega)
    rw [hmax4] at hp
    have heqoff : Int64.ofInt ((0 : Int64).toInt + (idxBv.toNat : Int) * 4) =
        Int64.ofNat (4 * idxBv.toNat) := by
      apply Int64.toInt_inj.mp
      rw [Int64.toInt_zero, int64_ofNat_toInt (by omega), int64_ofInt_toInt (by omega) (by omega)]
      omega
    rw [heqoff] at hp
    exact hp
  have hread_el : Sem.readPlace prog.tags m [] .rval bx (Int64.ofNat (4 * idxBv.toNat)) crcConstTy =
      some (.rval (.int .u32 bv) crcConstTy.decay) := by
    unfold Sem.readPlace
    simp only [crcConstTy, CTy.unqual, modSet_conflicts_nil, Bool.not_false,
      guard_true, bind, Option.bind, Option.map]
    rw [show Sem.readVal prog.tags m bx (Int64.ofNat (4 * idxBv.toNat))
        (.const_ (.typedef "z_crc_t" (.int .u32))) = some (.int .u32 bv) from hrv]
  have hstep1 : Sem.stepExprPure prog cfg env m []
      (.eval .rval (.var "x2n_table") (.indexBaseF .rval idxExpr :: fs)) =
      some (.ret (.rval (.ptr bx 0) (CTy.array crcConstTy (some 32)).decay)
        (.indexBaseF .rval idxExpr :: fs), m, []) := by
    simp [Sem.stepExprPure, hlu_env, hread_arr]
  have hstep2 : Sem.stepExprPure prog cfg env m []
      (.ret (.rval (.int .u32 idxBv) idxTy)
        (.indexIdxF .rval (.ptr bx 0) (CTy.array crcConstTy (some 32)).decay :: fs)) =
      some (.ret (.rval (.int .u32 bv) crcConstTy.decay) fs, m, []) := by
    unfold Sem.stepExprPure
    dsimp only [bind, Option.bind]
    rw [hdec_arr]
    dsimp only [Sem.valAsInt?, IntKind.signed, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
    erw [hadd]
    dsimp only [bind, Option.bind]
    erw [hread_el]
    rfl
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure hstep1 ?_
  refine WPTerm.of_exprPure (by rfl) (hidx ?_)
  exact WPTerm.of_exprPure hstep2 hw

private theorem IntSlot.preserve_pushParam {tags : TypeEnv} {env : Env} {m m1 m2 : Mem}
    {name : String} {b : BlockId} {ty : CTy} {k : IntKind} {v : BitVec k.bits}
    (hs : IntSlot env m name b ty k v)
    {p : Param} {ba : UInt64} {vp : Val}
    {hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags p.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags p.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba = (m.nextBlock, m1))
    (hwr : Sem.writeVal m1 m.nextBlock 0 p.ty.stripConst vp = some m2)
    (hnm : name ≠ p.name) :
    IntSlot ((p.name, m.nextBlock, p.ty) :: env) m2 name b ty k v :=
  (hs.preserve_alloc ha hnm).preserve_ne hwr (Nat.ne_of_lt hs.ne_of_lt_nextBlock)

private theorem PtrSlot.preserve_pushParam {tags : TypeEnv} {env : Env} {m m1 m2 : Mem}
    {name : String} {b : BlockId} {ty el : CTy} {vp0 : Val}
    (hs : PtrSlot env m name b ty el vp0)
    {p : Param} {ba : UInt64} {vp : Val}
    {hsz : max 1 (sizeofTy tags p.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags p.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags p.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba = (m.nextBlock, m1))
    (hwr : Sem.writeVal m1 m.nextBlock 0 p.ty.stripConst vp = some m2)
    (hnm : name ≠ p.name) :
    PtrSlot ((p.name, m.nextBlock, p.ty) :: env) m2 name b ty el vp0 :=
  (hs.preserve_alloc ha hnm).preserve_ne hwr (Nat.ne_of_lt hs.ne_of_lt_nextBlock)

private theorem wp_localDecl_int_none {prog cfg ext Q d rest env innerBlks m0 outerBlks m os kcont ik}
    (hk : d.ty.unqual = .int ik) (hnc : d.ty.isConst = false) (hstat : d.isStatic = false) (hnd : d.init? = none)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw : ∀ (ba : UInt64) (bid : BlockId) (m1 : Mem)
      (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
      (hal : 0 < max 1 (alignofTy prog.tags d.ty))
      (hba : ba.toNat % max 1 (alignofTy prog.tags d.ty) = 0)
      (_ha : m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty))
        .rw .stack ba (fun _ => .undef) hsz hal hba = (bid, m1)),
      bid = m.nextBlock →
      m1.nextBlock = m.nextBlock + 1 →
      LocalFrameMem m0 m1 (bid :: innerBlks ++ outerBlks) →
      UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty ik →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: innerBlks) m1 os kcont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.decls (d :: rest))) env innerBlks m os kcont) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_bytes hk, ptrDiffLimit_val]; cases ik <;> decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hd : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env innerBlks m os kcont) =
      some (.allocLocal d none rest env innerBlks m os kcont) := by
    unfold Sem.stepDet
    simp only [hstat, hnd, Bool.false_eq_true, ↓reduceIte]
  refine WPTerm.of_localDecl_none hd hsz hal ?_
  intro ba bid m1 hba ha
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm1_eq : m1 = (m.alloc _ _ _ _ _ _ _ _ _).2 := (congrArg Prod.snd ha).symm
  have hnext : m1.nextBlock = m.nextBlock + 1 := by rw [hm1_eq, alloc_snd_nextBlock]
  have hf1 : LocalFrameMem m0 m1 (bid :: innerBlks ++ outerBlks) := hf.alloc_stack ha
  have hs1 : UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty ik :=
    UninitIntSlot.of_alloc_int hk hnc ha
  exact hw ba bid m1 hsz hal hba ha hbid hnext hf1 hs1

private theorem wp_stmt_assign_int {prog cfg ext Q x rhs env innerBlks m0 outerBlks m os kcont b lty ik kr vr rty}
    (hs : UninitIntSlot env m x b lty ik)
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hrhs : PureEval prog cfg env m [] rhs (.int kr vr) rty)
    (hw : ∀ m',
      Sem.writeVal m b 0 lty (.int ik (BitVec.ofInt ik.bits (if kr.signed then vr.toInt else (vr.toNat : Int)))) = some m' →
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' x b lty ik (BitVec.ofInt ik.bits (if kr.signed then vr.toInt else (vr.toNat : Int))) →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.assign .eq (.var x) rhs))) env innerBlks m os kcont) := by
  let vnew := BitVec.ofInt ik.bits (if kr.signed then vr.toInt else (vr.toNat : Int))
  obtain ⟨m', hwr, hf', hs'⟩ := hs.write hf hmem vnew
  have hcast : Sem.castVal m lty (.int kr vr) = some (.int ik vnew) := castVal_int_eq hs.2.1 vr
  have hwp : Sem.writePlace prog.tags m b 0 lty (.rval (.int kr vr) rty) =
      some (.rval (.int ik vnew) lty, m') := by
    unfold Sem.writePlace
    simp only [hs.2.1, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hstep : Sem.stepExprPure prog cfg env m [] (.ret (.rval (.int kr vr) rty) [.assignRhsF .eq b 0 lty]) =
      some (.ret (.rval (.int ik vnew) lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    simp [Sem.stepExprPure, hnc, Sem.assignOpToBin?, hwp]
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure rfl (hrhs ?_)
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hw m' hwr hf' hs'))

private theorem wp_stmt_assignOp_int {prog cfg ext Q op bop x rhs env innerBlks m0 outerBlks m os kcont b lty ik vold kr vr rty kv nv nt}
    (hop : Sem.assignOpToBin? op = some bop)
    (hs : IntSlot env m x b lty ik vold)
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hrhs : PureEval prog cfg env m [] rhs (.int kr vr) rty)
    (hrty : rty.unqual = .int kr)
    (hbin : Sem.evalIntBinary bop (.int ik vold) (.int kr vr) = some (.int kv nv, nt))
    (hw : ∀ m',
      Sem.writeVal m b 0 lty (.int ik (BitVec.ofInt ik.bits (if kv.signed then nv.toInt else (nv.toNat : Int)))) = some m' →
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' x b lty ik (BitVec.ofInt ik.bits (if kv.signed then nv.toInt else (nv.toNat : Int))) →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.assign op (.var x) rhs))) env innerBlks m os kcont) := by
  let vnew := BitVec.ofInt ik.bits (if kv.signed then nv.toInt else (nv.toNat : Int))
  obtain ⟨m', hwr, hf', hs'⟩ := hs.to_uninit.write hf hmem vnew
  have hcast : Sem.castVal m lty (.int kv nv) = some (.int ik vnew) := castVal_int_eq hs.2.1 nv
  have hwp : Sem.writePlace prog.tags m b 0 lty (.rval (.int kv nv) lty) =
      some (.rval (.int ik vnew) lty, m') := by
    unfold Sem.writePlace
    simp only [hs.2.1, hcast, hwr, bind, Option.bind, pure, Pure.pure]
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hrv := hs.readVal_eq prog.tags
  have happ : Sem.applyBinary cfg prog.tags m bop (.int ik vold) lty (.int kr vr) rty = some (.int kv nv, nt) := by
    rw [applyBinary_int hs.2.1 hrty]; exact hbin
  have hstep : Sem.stepExprPure prog cfg env m [] (.ret (.rval (.int kr vr) rty) [.assignRhsF op b 0 lty]) =
      some (.ret (.rval (.int ik vnew) lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    simp [Sem.stepExprPure, hnc, hop, hrv, happ, hwp]
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure rfl (hrhs ?_)
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hw m' hwr hf' hs'))

private theorem wp_stmt_postInc_u32 {prog cfg ext Q x env innerBlks m0 outerBlks m os kcont b lty}
    {v : BitVec IntKind.u32.bits}
    (hs : IntSlot env m x b lty .u32 v)
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw : ∀ m',
      Sem.writeVal m b 0 lty (.int .u32 (v + (1 : BitVec IntKind.u32.bits))) = some m' →
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' x b lty .u32 (v + (1 : BitVec IntKind.u32.bits)) →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.incDec .postInc (.var x)))) env innerBlks m os kcont) := by
  obtain ⟨m', hwr, hf', hs'⟩ := hs.write hf hmem (v + (1 : BitVec IntKind.u32.bits))
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hrv := hs.readVal_eq prog.tags
  have happ : Sem.applyBinary cfg prog.tags m .add (.int .u32 v) lty (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) =
      some (.int .u32 (v + (1 : BitVec IntKind.u32.bits)), .int .u32) := by
    rw [applyBinary_int hs.2.1 rfl]
    exact evalIntBinary_u32_add_1 v
  have hstep : Sem.stepExprPure prog cfg env m [] (.ret (.lval b 0 lty) [.incDecF .postInc]) =
      some (.ret (.rval (.int .u32 v) lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    simp only [Sem.stepExprPure, hnc, Bool.not_false, guard_true, hrv, bind, Option.bind]
    rw [happ]
    dsimp only
    rw [show Sem.writeVal m b 0 lty (.int .u32 (v + (1 : BitVec IntKind.u32.bits))) = some m' from hwr]
    rfl
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine wp_lval_var hs.1 ?_
  exact WPTerm.of_exprPure hstep (WPTerm.of_det rfl (hw m' hwr hf' hs'))

private theorem wp_if_pure {prog cfg ext Q c t f? env blks m os kcont vc tc b}
    (hc : PureEval prog cfg env m [] c vc tc)
    (htr : Sem.isTruthy vc = some b)
    (hw : WPTerm prog cfg ext Q (.running (.stmt (if b then t else f?.getD .nop)) env blks m os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.ifStmt c t f?)) env blks m os kcont) := by
  have hstep : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval vc tc) []) (.branch t (f?.getD .nop)) []) env blks m os kcont) =
      some (.next (.running (.stmt (if b then t else f?.getD .nop)) env blks m os kcont)) := by
    unfold Sem.stepDet
    simp only [Option.bind, htr, Option.map_some]
  exact WPTerm.of_det rfl (hc (WPTerm.of_det hstep hw))

private theorem wp_return_pure {prog cfg ext Q e innerEnv innerBlks m0 callBlks m_cur os env blks fnRetTy fs ctx k k_ret v ty cv}
    (hretUnw : Sem.unwindReturn m_cur innerBlks k_ret =
      some (env, blks, fnRetTy, (m_cur.freeStack innerBlks).freeStack callBlks, fs, ctx, k))
    (htop : k_ret.topRetTy = fnRetTy)
    (hnv : fnRetTy.isVoid = false)
    (hf : LocalFrameMem m0 m_cur (innerBlks ++ callBlks))
    (he : PureEval prog cfg innerEnv m_cur [] e v ty)
    (hcast : Sem.castVal m_cur fnRetTy v = some cv)
    (hcont : ∀ ret m', ROExt m0 m' → ret = cv → m' = (m_cur.freeStack innerBlks).freeStack callBlks →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval ret fnRetTy) fs) ctx []) env blks m' os k)) :
    WPTerm prog cfg ext Q (.running (.stmt (.returnStmt (some e))) innerEnv innerBlks m_cur os k_ret) := by
  have hf_call : LocalFrameMem m0 (m_cur.freeStack innerBlks) callBlks := LocalFrameMem.freeStack_sub hf
  have hro : ROExt m0 ((m_cur.freeStack innerBlks).freeStack callBlks) := LocalFrameMem.roExt_freeStack hf_call
  have hstep : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval v ty) []) .returnVal []) innerEnv innerBlks m_cur os k_ret) =
      some (.next (.running (.expr (.ret (.rval cv fnRetTy) fs) ctx [])
        env blks ((m_cur.freeStack innerBlks).freeStack callBlks) os k)) := by
    unfold Sem.stepDet
    simp only [htop, hnv, Bool.false_eq_true, ↓reduceIte, hcast, hretUnw, Option.bind_some, Option.map_some]
  exact WPTerm.of_det rfl (he (WPTerm.of_det hstep (hcont cv _ hro rfl rfl)))

/-! ## 5. Helper & Combine Proofs (`multmodp`, `x2nmodp`, `crc32_combine*`) -/

private def multmodpPre (_m : Mem) (args : List Val) : Prop :=
  ∃ a b : BitVec 64, args = [.int .u64 a, .int .u64 b] ∧
    (a &&& 0xffffffff#64) ≠ 0#64 ∧ b.toNat < 2 ^ 32

private def multmodpPost : Mem → List Val → Val → Mem → Prop
  | _, [.int .u64 a, .int .u64 b], ret, _ =>
      ret = .int .u64 ((multmodpSpec (a.truncate 32) (b.truncate 32)).zeroExtend 64)
  | _, _, _, _ => False

private theorem bv64_and_or_ne_zero {a x y : BitVec 64}
    (h : (a &&& (x ||| y)) ≠ 0#64) (hx : (a &&& x) = 0#64) : (a &&& y) ≠ 0#64 := by
  intro hy
  apply h
  apply BitVec.eq_of_getLsbD_eq; intro i _
  have hxi := congrArg (fun z : BitVec 64 => z.getLsbD i) hx
  have hyi := congrArg (fun z : BitVec 64 => z.getLsbD i) hy
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hxi hyi ⊢
  cases ha : a.getLsbD i <;> cases hxb : x.getLsbD i <;> cases hyb : y.getLsbD i <;> simp_all

private theorem bv64_shift_shr_1 {k : Nat} (hk : k < 31) :
    (1#64 <<< (k + 1)) >>> 1 = 1#64 <<< k := by
  exact beq_iff_eq.mp (of_decide_eq_true (List.all_eq_true.mp
    (by decide : (List.range 31).all (fun k => decide (((1#64 <<< (k + 1)) >>> 1) == 1#64 <<< k)) = true)
    k (List.mem_range.mpr hk)))

private theorem bv64_nextB_lt {b : BitVec 64} (hb : b.toNat < 2 ^ 32) :
    (if (b &&& 1#64) != 0#64 then (b >>> 1) ^^^ 0xedb88320#64 else b >>> 1).toNat < 2 ^ 32 := by
  have hsh : (b >>> 1).toNat < 2 ^ 31 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  split
  · simp only [BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (by omega : (b >>> 1).toNat < 2 ^ 32) (by decide)
  · omega

private theorem bv64_nextB_truncate {b : BitVec 64} (hb : b.toNat < 2 ^ 32) :
    (if (b &&& 1#64) != 0#64 then (b >>> 1) ^^^ 0xedb88320#64 else b >>> 1).truncate 32 =
      multmodpNextB (b.truncate 32) := by
  unfold multmodpNextB
  have hand : ((b.truncate 32 &&& 1#32) != 0#32) = ((b &&& 1#64) != 0#64) := by
    simpa using bv64_and_bit_trunc32 b (k := 0) (by decide)
  rw [hand]
  split
  · rw [bv64_truncate_xor, bv64_truncate_ushiftRight_1 hb]
    rfl
  · exact bv64_truncate_ushiftRight_1 hb

theorem multmodp_spec {prog : Prog} {ext : ExtHandler} :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_multmodp
      multmodpPre multmodpPost := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨a0, b0, rfl, ha_nz, hb_lt⟩
  obtain ⟨hsz0, hal0, hba0, m_a, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_b, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  cases hpush2
  let b_a := m.nextBlock
  let b_b := m_a.nextBlock
  have hnext_a : b_b = b_a + 1 := by
    dsimp [b_a, b_b]; rw [writeVal_nextBlock hwr0]; exact alloc_snd_nextBlock _ _ _ _ _ _ _ _ _ _
  have hm1_next : m1.nextBlock = b_b + 1 := by
    dsimp [b_b]; rw [writeVal_nextBlock hwr1]; exact alloc_snd_nextBlock _ _ _ _ _ _ _ _ _ _
  have hf_call : LocalFrameMem m m1 [b_b, b_a] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_multmodp.name ++ prog.globalEnv
  have ha_slot0 : IntSlot (("a", b_a, uLongTy) :: env0) m_a "a" b_a uLongTy .u64 a0 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  have ha_slot : IntSlot (("b", b_b, uLongTy) :: ("a", b_a, uLongTy) :: env0) m1 "a" b_a uLongTy .u64 a0 :=
    ha_slot0.preserve_pushParam (ha := rfl) hwr1 (by decide)
  have hb_slot : IntSlot (("b", b_b, uLongTy) :: ("a", b_a, uLongTy) :: env0) m1 "b" b_b uLongTy .u64 b0 :=
    IntSlot.of_pushCallParam rfl rfl hwr1 _
  -- Enter fn.body block
  refine WPTerm.of_det (by rfl) ?_
  -- Decl m
  refine wp_localDecl_int_none (ik := .u64) rfl rfl rfl rfl hf_call ?_
  intro ba_m bid_m m_dm hsz_m hal_m hba_m ha_m hbid_m hnext_m hf_dm hm_uninit
  have ha_dm := ha_slot.preserve_localDecl_none ha_m (by decide)
  have hb_dm := hb_slot.preserve_localDecl_none ha_m (by decide)
  -- Decl p
  refine wp_localDecl_int_none (ik := .u64) rfl rfl rfl rfl hf_dm ?_
  intro ba_p bid_p m_dp hsz_p hal_p hba_p ha_p hbid_p hnext_p hf_dp hp_uninit
  have hlt_ab : b_a < b_b := by rw [hnext_a]; exact Nat.lt_succ_self _
  have hlt_bm : b_b < bid_m := by rw [hbid_m, hm1_next]; exact Nat.lt_succ_self _
  have hlt_mp : bid_m < bid_p := by rw [hbid_p, hnext_m, ← hbid_m]; exact Nat.lt_succ_self _
  have hne_ab : b_a ≠ b_b := Nat.ne_of_lt hlt_ab
  have hne_am : b_a ≠ bid_m := Nat.ne_of_lt (Nat.lt_trans hlt_ab hlt_bm)
  have hne_ap : b_a ≠ bid_p := Nat.ne_of_lt (Nat.lt_trans hlt_ab (Nat.lt_trans hlt_bm hlt_mp))
  have hne_bm : b_b ≠ bid_m := Nat.ne_of_lt hlt_bm
  have hne_bp : b_b ≠ bid_p := Nat.ne_of_lt (Nat.lt_trans hlt_bm hlt_mp)
  have hne_mp : bid_m ≠ bid_p := Nat.ne_of_lt hlt_mp
  have ha_dp := ha_dm.preserve_localDecl_none ha_p (by decide)
  have hb_dp := hb_dm.preserve_localDecl_none ha_p (by decide)
  have hm_dp := hm_uninit.preserve_alloc (nm' := "p") (ty' := uLongTy) ha_p (by decide)
  let callEnv : Env := ("b", b_b, uLongTy) :: ("a", b_a, uLongTy) :: env0
  let loopEnv : Env := ("p", bid_p, uLongTy) :: ("m", bid_m, uLongTy) :: callEnv
  -- Step past decls [] and .stmts
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  -- m = (uLong)1 << 31
  have hm_init_expr : PureEval prog zlibPointerConfig loopEnv m_dp []
      (CExpr.binary .shl (CExpr.cast uLongTy (CExpr.lit 1)) (CExpr.lit 31))
      (.int .u64 (1#64 <<< 31)) (.int .u64) :=
    pureEval_binary_int
      (pureEval_cast pureEval_lit (castVal_int_eq (k2 := .u64) rfl _))
      pureEval_lit rfl rfl (evalIntBinary_u64_shl_i32 1#64 (sh := 31) (by decide))
  refine wp_stmt_assign_int hm_dp (by simp) hf_dp hm_init_expr ?_
  intro m_m0 hwr_m0 hf_m0 hm_slot0
  have ha_m0 := ha_dp.preserve_ne hwr_m0 hne_am
  have hb_m0 := hb_dp.preserve_ne hwr_m0 hne_bm
  have hp_m0 := hp_uninit.preserve_ne hwr_m0 hne_mp.symm
  refine WPTerm.of_det (by rfl) ?_
  -- p = 0
  have hp_init_expr : PureEval prog zlibPointerConfig loopEnv m_m0 [] (CExpr.lit 0) (Sem.ofIntCast .i32 0) (.int .i32) :=
    pureEval_lit
  refine wp_stmt_assign_int hp_m0 (by simp) hf_m0 hp_init_expr ?_
  intro m_p0 hwr_p0 hf_p0 hp_slot0
  have ha_p0 := ha_m0.preserve_ne hwr_p0 hne_ap
  have hb_p0 := hb_m0.preserve_ne hwr_p0 hne_bp
  have hm_p0 := hm_slot0.preserve_ne hwr_p0 hne_mp
  refine WPTerm.of_det (by rfl) ?_
  -- Prepare loop invariant
  let loopBlks : List BlockId := [bid_p, bid_m]
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m_cur os' =>
    env' = loopEnv ∧ blks' = loopBlks ∧ os' = os ∧ meas ≤ 31 ∧
    LocalFrameMem m m_cur (bid_p :: bid_m :: [b_b, b_a]) ∧
    ∃ b_cur p_cur : BitVec 64,
      IntSlot loopEnv m_cur "a" b_a uLongTy .u64 a0 ∧
      IntSlot loopEnv m_cur "b" b_b uLongTy .u64 b_cur ∧
      IntSlot loopEnv m_cur "m" bid_m uLongTy .u64 (1#64 <<< meas) ∧
      IntSlot loopEnv m_cur "p" bid_p uLongTy .u64 p_cur ∧
      b_cur.toNat < 2 ^ 32 ∧ p_cur.toNat < 2 ^ 32 ∧
      (a0 &&& ((1#64 <<< (meas + 1)) - 1#64)) ≠ 0#64 ∧
      multmodpLoop (a0.truncate 32) meas (p_cur.truncate 32) (b_cur.truncate 32) =
        multmodpSpec (a0.truncate 32) (b0.truncate 32)
  have hmask32 : ((1#64 <<< 32) - 1#64) = 0xffffffff#64 := by decide
  have hm_eq_1 : (BitVec.ofInt 64 (1#64 <<< 31).toNat) = 1#64 <<< 31 := bitVec_ofInt_toNat 64 _
  have hp_eq_0 : (BitVec.ofInt 64 (0#32 : BitVec 32).toInt) = 0#64 := by decide
  have hinitInv : Inv 31 loopEnv loopBlks m_p0 os := by
    refine ⟨rfl, rfl, rfl, Nat.le_refl 31, hf_p0, b0, 0#64, ha_p0, hb_p0, ?_, ?_, hb_lt, by decide, ?_, ?_⟩
    · erw [hm_eq_1] at hm_p0; exact hm_p0
    · erw [hp_eq_0] at hp_slot0; exact hp_slot0
    · rw [hmask32]; exact ha_nz
    · rfl
  let loopCont : Sem.Cont := .stmts [.returnStmt (some (.var "p"))]
    (.blockEnd callEnv [b_b, b_a] (.callFrame env blks Zlib.Crc32.crc32TU_fn_multmodp.retTy
      Zlib.Crc32.crc32TU_fn_multmodp.body fs ctx k))
  refine WPTerm.for_none_wf Inv (k := loopCont) hinitInv ?_
  intro meas env' blks' m_cur os' hinv ih
  rcases hinv with ⟨rfl, rfl, hos, hmeas_le, hf_cur, b_cur, p_cur, ha_cur, hb_cur, hm_cur, hp_cur,
    hb_cur_lt, hp_cur_lt, ha_mask_nz, hloop_eq⟩
  subst os'
  -- Unfold forLoopEntry none none forBody ...
  dsimp [forLoopEntry]
  -- Step into loop body block
  refine WPTerm.of_det (by rfl) ?_
  dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  have hnc64 : ModSet.conflicts [] b_a 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hncm : ModSet.conflicts [] bid_m 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hdec64 : uLongTy.decay.unqual = .int .u64 := by simp [uLongTy, CTy.decay, CTy.unqual]
  -- Evaluate condition a & m
  have ha_and_m : PureEval prog zlibPointerConfig loopEnv m_cur []
      (CExpr.binary .bitAnd (.var "a") (.var "m"))
      (.int .u64 (a0 &&& (1#64 <<< meas))) (.int .u64) :=
    pureEval_binary_int (pureEval_var_int ha_cur hnc64) (pureEval_var_int hm_cur hncm)
      hdec64 hdec64 (evalIntBinary_u64_and_u64 a0 _)
  let forBody : CStmt := CStmt.block [
    CStmt.ifStmt (CExpr.binary .bitAnd (.var "a") (.var "m"))
      (CStmt.block [
        CStmt.expr (.assign .xorEq (.var "p") (.var "b")),
        CStmt.ifStmt (CExpr.binary .eq (CExpr.binary .bitAnd (.var "a")
          (CExpr.binary .sub (.var "m") (.lit 1)).paren).paren (.lit 0)) CStmt.breakStmt none
      ]) none,
    CStmt.expr (.assign .shrEq (.var "m") (.lit 1)),
    CStmt.expr (.assign .eq (.var "b")
      ((CExpr.binary .bitAnd (.var "b") (.lit 1)).cond
        (CExpr.binary .bitXor (CExpr.binary .shr (.var "b") (.lit 1)).paren
          (.lit 3988292384 .u32 .none .hex))
        (CExpr.binary .shr (.var "b") (.lit 1))))
  ]
  -- Shared post-if continuation: given meas = meas' + 1, p_next, updated slots, finish loop step
  have after_if : ∀ (meas' : Nat) (_hmeas_eq : meas = meas' + 1) (m_next : Mem) (p_next : BitVec 64),
      LocalFrameMem m m_next (bid_p :: bid_m :: [b_b, b_a]) →
      IntSlot loopEnv m_next "a" b_a uLongTy .u64 a0 →
      IntSlot loopEnv m_next "b" b_b uLongTy .u64 b_cur →
      IntSlot loopEnv m_next "m" bid_m uLongTy .u64 (1#64 <<< (meas' + 1)) →
      IntSlot loopEnv m_next "p" bid_p uLongTy .u64 p_next →
      p_next.toNat < 2 ^ 32 →
      (a0 &&& ((1#64 <<< (meas' + 1)) - 1#64)) ≠ 0#64 →
      multmodpLoop (a0.truncate 32) meas' (p_next.truncate 32) (multmodpNextB (b_cur.truncate 32)) =
        multmodpSpec (a0.truncate 32) (b0.truncate 32) →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.stmt .nop) loopEnv [] m_next os
          (.stmts
            [CStmt.expr (.assign .shrEq (.var "m") (.lit 1)),
             CStmt.expr (.assign .eq (.var "b")
               ((CExpr.binary .bitAnd (.var "b") (.lit 1)).cond
                 (CExpr.binary .bitXor (CExpr.binary .shr (.var "b") (.lit 1)).paren
                   (.lit 3988292384 .u32 .none .hex))
                 (CExpr.binary .shr (.var "b") (.lit 1))))]
            (.blockEnd loopEnv loopBlks (.loop none none forBody false loopCont)))) := by
    intro meas' hmeas_eq m_next p_next hf_nx ha_nx hb_nx hm_nx hp_nx hp_nx_lt ha_nx_nz hloop_nx
    have hm_shr_val : (BitVec.ofInt 64 ((1#64 <<< (meas' + 1)) >>> 1).toNat) = 1#64 <<< meas' := by
      rw [bitVec_ofInt_toNat, bv64_shift_shr_1 (by omega)]
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_assignOp_int (op := .shrEq) (bop := .shr) rfl hm_nx (by simp) hf_nx
      pureEval_lit rfl (evalIntBinary_u64_shr_i32 _ (sh := 1) (by decide)) ?_
    intro m_m1 hwr_m1 hf_m1 hm_m1
    have hm_m1' : IntSlot loopEnv m_m1 "m" bid_m uLongTy .u64 (1#64 <<< meas') := by
      erw [hm_shr_val] at hm_m1; exact hm_m1
    have ha_m1 := ha_nx.preserve_ne hwr_m1 hne_am
    have hb_m1 := hb_nx.preserve_ne hwr_m1 hne_bm
    have hp_m1 := hp_nx.preserve_ne hwr_m1 hne_mp.symm
    refine WPTerm.of_det (by rfl) ?_
    have hncb : ModSet.conflicts [] b_b 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
    have hb_and_1 : PureEval prog zlibPointerConfig loopEnv m_m1 []
        (CExpr.binary .bitAnd (.var "b") (.lit 1)) (.int .u64 (b_cur &&& 1#64)) (.int .u64) :=
      pureEval_binary_int (pureEval_var_int hb_m1 hncb) pureEval_lit hdec64 rfl
        (evalIntBinary_u64_and_i32 b_cur (n := 1) (by decide) (by decide))
    have hb_shr1 : PureEval prog zlibPointerConfig loopEnv m_m1 []
        (CExpr.binary .shr (.var "b") (.lit 1)) (.int .u64 (b_cur >>> 1)) (.int .u64) :=
      pureEval_binary_int (pureEval_var_int hb_m1 hncb) pureEval_lit hdec64 rfl
        (evalIntBinary_u64_shr_i32 b_cur (sh := 1) (by decide))
    have hpoly : (BitVec.ofInt 32 3988292384).zeroExtend 64 = 0xedb88320#64 := by decide
    have hb_cond : PureEval prog zlibPointerConfig loopEnv m_m1 []
        ((CExpr.binary .bitAnd (.var "b") (.lit 1)).cond
          (CExpr.binary .bitXor (CExpr.binary .shr (.var "b") (.lit 1)).paren
            (.lit 3988292384 .u32 .none .hex))
          (CExpr.binary .shr (.var "b") (.lit 1)))
        (.int .u64 (if (b_cur &&& 1#64) != 0#64 then (b_cur >>> 1) ^^^ 0xedb88320#64 else b_cur >>> 1))
        (.int .u64) := by
      by_cases hb1 : ((b_cur &&& 1#64) != 0#64) = true
      · refine pureEval_cond (b := true) hb_and_1 (by erw [isTruthy_int, hb1]) ?_
        simp only [hb1, ↓reduceIte]
        rw [← hpoly]
        exact pureEval_binary_int (pureEval_paren hb_shr1)
          (pureEval_lit : PureEval prog zlibPointerConfig loopEnv m_m1 []
            (.lit 3988292384 .u32 .none .hex) _ _)
          rfl rfl (evalIntBinary_u64_xor_u32 (b_cur >>> 1) _)
      · have hb1f : ((b_cur &&& 1#64) != 0#64) = false := Bool.eq_false_iff.mpr hb1
        refine pureEval_cond (b := false) hb_and_1 (by erw [isTruthy_int, hb1f]) ?_
        simp only [hb1f, Bool.false_eq_true, ↓reduceIte]
        exact hb_shr1
    refine wp_stmt_assign_int hb_m1.to_uninit (by simp) hf_m1 hb_cond ?_
    intro m_b1 hwr_b1 hf_b1 hb_b1
    have ha_b1 := ha_m1.preserve_ne hwr_b1 hne_ab
    have hm_b1 := hm_m1'.preserve_ne hwr_b1 hne_bm.symm
    have hp_b1 := hp_m1.preserve_ne hwr_b1 hne_bp.symm
    let b_next := if (b_cur &&& 1#64) != 0#64 then (b_cur >>> 1) ^^^ 0xedb88320#64 else b_cur >>> 1
    have hb_eq : (BitVec.ofInt 64 b_next.toNat) = b_next := bitVec_ofInt_toNat 64 _
    have hb_b1' : IntSlot loopEnv m_b1 "b" b_b uLongTy .u64 b_next := by
      erw [hb_eq] at hb_b1; exact hb_b1
    -- Exit blockEnd and loopNext back to ih meas'
    refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_))
    rw [freeStack_nil]
    refine ih meas' loopEnv loopBlks m_b1 os (by omega)
      ⟨rfl, rfl, rfl, by omega, hf_b1, b_next, p_next, ha_b1, hb_b1', hm_b1, hp_b1,
        bv64_nextB_lt hb_cur_lt, hp_nx_lt, ha_nx_nz, ?_⟩
    rw [bv64_nextB_truncate hb_cur_lt]
    exact hloop_nx
  -- Branch on if (a & m)
  by_cases hbit : ((a0 &&& (1#64 <<< meas)) != 0#64) = true
  · refine wp_if_pure (b := true) ha_and_m (by erw [isTruthy_int, hbit]) ?_
    simp only [↓reduceIte]
    have hbit_nz : (a0 &&& (1#64 <<< meas)) ≠ 0#64 := by simpa using hbit
    -- Enter inner block of `if (a & m)`
    refine WPTerm.of_det (by rfl) ?_
    -- p ^= b
    have hncb : ModSet.conflicts [] b_b 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
    refine wp_stmt_assignOp_int (op := .xorEq) (bop := .bitXor) rfl hp_cur (by simp) hf_cur
      (pureEval_var_int hb_cur hncb) hdec64 (evalIntBinary_u64_xor_u64 p_cur b_cur) ?_
    intro m_p1 hwr_p1 hf_p1 hp_p1
    have hp_p1_eq : BitVec.ofInt 64 (p_cur ^^^ b_cur).toNat = p_cur ^^^ b_cur := bitVec_ofInt_toNat 64 _
    have hp_p1' : IntSlot loopEnv m_p1 "p" bid_p uLongTy .u64 (p_cur ^^^ b_cur) := by
      erw [hp_p1_eq] at hp_p1; exact hp_p1
    have ha_p1 := ha_cur.preserve_ne hwr_p1 hne_ap
    have hb_p1 := hb_cur.preserve_ne hwr_p1 hne_bp
    have hm_p1 := hm_cur.preserve_ne hwr_p1 hne_mp
    have hp1_lt : (p_cur ^^^ b_cur).toNat < 2 ^ 32 := by
      simp only [BitVec.toNat_xor]
      exact Nat.xor_lt_two_pow hp_cur_lt hb_cur_lt
    -- Step to inner `if ((a & (m - 1)) == 0) break;`
    refine WPTerm.of_det (by rfl) ?_
    have hm_sub1 : PureEval prog zlibPointerConfig loopEnv m_p1 []
        (CExpr.binary .sub (.var "m") (.lit 1))
        (.int .u64 ((1#64 <<< meas) - 1#64)) (.int .u64) :=
      pureEval_binary_int (pureEval_var_int hm_p1 hncm) pureEval_lit hdec64 rfl
        (evalIntBinary_u64_sub_i32 (1#64 <<< meas) (n := 1) (by decide) (by decide))
    have ha_and_sub : PureEval prog zlibPointerConfig loopEnv m_p1 []
        (CExpr.binary .bitAnd (.var "a") (CExpr.binary .sub (.var "m") (.lit 1)).paren)
        (.int .u64 (a0 &&& ((1#64 <<< meas) - 1#64))) (.int .u64) :=
      pureEval_binary_int (pureEval_var_int ha_p1 hnc64) (pureEval_paren hm_sub1)
        hdec64 rfl (evalIntBinary_u64_and_u64 a0 _)
    have hcmp : PureEval prog zlibPointerConfig loopEnv m_p1 []
        (CExpr.binary .eq
          (CExpr.binary .bitAnd (.var "a") (CExpr.binary .sub (.var "m") (.lit 1)).paren).paren
          (.lit 0))
        (.int .i32 (if (a0 &&& ((1#64 <<< meas) - 1#64)) == 0#64 then 1#32 else 0#32)) (.int .i32) :=
      pureEval_binary_int (pureEval_paren ha_and_sub) pureEval_lit rfl rfl
        (evalIntBinary_u64_eq_zero _)
    by_cases hlow : (a0 &&& ((1#64 <<< meas) - 1#64)) == 0#64
    · refine wp_if_pure (b := true) hcmp (by erw [isTruthy_int]; simp only [hlow, ↓reduceIte]; rfl) ?_
      simp only [↓reduceIte]
      -- break!
      have hbrk : Sem.stepDet prog zlibPointerConfig
          (.running (.stmt .breakStmt) loopEnv [] m_p1 os
            (.stmts [] (.blockEnd loopEnv loopBlks (.loop none none forBody false loopCont)))) =
          some (.next (.running (.stmt .nop) loopEnv loopBlks m_p1 os loopCont)) := by
        unfold Sem.stepDet
        dsimp only
        rw [Sem.unwindBreak.eq_def]
        dsimp only
        rw [Sem.unwindBreak.eq_def, freeStack_nil]
        dsimp only
        rw [Sem.unwindBreak.eq_def]
        rfl
      refine WPTerm.of_det hbrk ?_
      refine WPTerm.of_det (by rfl) ?_
      have hncp : ModSet.conflicts [] bid_p 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
      refine wp_return_pure (fnRetTy := uLongTy) (innerBlks := [bid_p, bid_m]) (callBlks := [b_b, b_a])
        (hretUnw := by rfl)
        (htop := by rfl) (hnv := by decide) hf_p1
        (pureEval_var_int hp_p1' hncp)
        (castVal_int_eq (k2 := .u64) (by rfl) _) ?_
      intro ret m' hro hret _
      refine hcont ret m' hro ?_
      have hlow_eq : (a0 &&& ((1#64 <<< meas) - 1#64)) = 0#64 := beq_iff_eq.mp hlow
      have hlow32 : (a0.truncate 32 &&& ((1#32 <<< meas) - 1#32)) = 0#32 :=
        (bv64_and_mask_trunc32 a0 (by omega)).mpr hlow_eq
      have hbit32 : ((a0.truncate 32 &&& (1#32 <<< meas)) != 0#32) = true := by
        rw [bv64_and_bit_trunc32 a0 (by omega)]; exact hbit
      have hspec : multmodpSpec (a0.truncate 32) (b0.truncate 32) =
          p_cur.truncate 32 ^^^ b_cur.truncate 32 := by
        rw [← hloop_eq, multmodpLoop_eq_of_low_zero _ meas hmeas_le hlow32, hbit32]
        rfl
      have hret_eq : ret = .int .u64 (p_cur ^^^ b_cur) := by
        rw [hret]
        refine congrArg (Val.int .u64) ?_
        simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
      rw [hret_eq, ← bv64_zeroExtend_truncate_of_lt hp1_lt, bv64_truncate_xor, ← hspec]
      rfl
    · have hlow_false : ((a0 &&& ((1#64 <<< meas) - 1#64)) == 0#64) = false :=
        Bool.eq_false_iff.mpr hlow
      refine wp_if_pure (b := false) hcmp
        (by erw [isTruthy_int]; simp only [hlow_false, Bool.false_eq_true, ↓reduceIte]; rfl) ?_
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hlow_nz : (a0 &&& ((1#64 <<< meas) - 1#64)) ≠ 0#64 := by simpa using hlow
      have hmeas_pos : 0 < meas := by
        rcases Nat.eq_zero_or_pos meas with rfl | hmeas_pos
        · have hz0 : ((1#64 <<< 0) - 1#64) = 0#64 := by decide
          rw [hz0, BitVec.and_zero] at hlow_nz
          exact absurd rfl hlow_nz
        · exact hmeas_pos
      obtain ⟨meas', hmeas_eq⟩ : ∃ meas', meas = meas' + 1 := ⟨meas - 1, by omega⟩
      refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
      rw [freeStack_nil]
      refine after_if meas' hmeas_eq m_p1 (p_cur ^^^ b_cur) hf_p1 ha_p1 hb_p1
        (hmeas_eq ▸ hm_p1) hp_p1' hp1_lt (hmeas_eq ▸ hlow_nz) ?_
      have hbit32 : ((a0.truncate 32 &&& (1#32 <<< (meas' + 1))) != 0#32) = true := by
        rw [bv64_and_bit_trunc32 a0 (by omega)]; exact hmeas_eq ▸ hbit
      rw [← hloop_eq, hmeas_eq]
      simp only [multmodpLoop, multmodpStep, hbit32, ↓reduceIte, bv64_truncate_xor]
  · have hbit_false : ((a0 &&& (1#64 <<< meas)) != 0#64) = false := Bool.eq_false_iff.mpr hbit
    have hbit0 : (a0 &&& (1#64 <<< meas)) = 0#64 := by simpa using hbit_false
    refine wp_if_pure (b := false) ha_and_m (by erw [isTruthy_int, hbit_false]) ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hmeas_pos : 0 < meas := by
      rcases Nat.eq_zero_or_pos meas with rfl | hmeas_pos
      · have hm1 : ((1#64 <<< 1) - 1#64) = (1#64 <<< 0) := by decide
        rw [hm1] at ha_mask_nz
        exact absurd hbit0 ha_mask_nz
      · exact hmeas_pos
    obtain ⟨meas', hmeas_eq⟩ : ∃ meas', meas = meas' + 1 := ⟨meas - 1, by omega⟩
    have hlow_nz : (a0 &&& ((1#64 <<< (meas' + 1)) - 1#64)) ≠ 0#64 := by
      have hm_split := mask64_split (k := meas' + 1) (by omega)
      have ha1 : (a0 &&& (((1#64 <<< (meas' + 1)) ||| ((1#64 <<< (meas' + 1)) - 1#64)))) ≠ 0#64 := by
        rw [← hm_split, ← hmeas_eq]; exact ha_mask_nz
      exact bv64_and_or_ne_zero ha1 (hmeas_eq ▸ hbit0)
    refine after_if meas' hmeas_eq m_cur p_cur hf_cur ha_cur hb_cur
      (hmeas_eq ▸ hm_cur) hp_cur hp_cur_lt hlow_nz ?_
    have hbit32 : ((a0.truncate 32 &&& (1#32 <<< (meas' + 1))) != 0#32) = false := by
      rw [bv64_and_bit_trunc32 a0 (by omega)]; exact hmeas_eq ▸ hbit_false
    rw [← hloop_eq, hmeas_eq]
    simp only [multmodpLoop, multmodpStep, hbit32, Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero]

private theorem bv32_zeroExtend_and_mask (x : BitVec 32) :
    x.zeroExtend 64 &&& 0xffffffff#64 = x.zeroExtend 64 := by
  have hmask : ∀ j < 32, (0xffffffff#64 : BitVec 64).getLsbD j = true := fun j hj =>
    of_decide_eq_true (List.all_eq_true.mp
      (by decide : (List.range 32).all (fun k => (0xffffffff#64 : BitVec 64).getLsbD k) = true)
      j (List.mem_range.mpr hj))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.zeroExtend, BitVec.getLsbD_setWidth]
  by_cases hi32 : i < 32
  · simp [hi, hi32, hmask i hi32]
  · have hge : x.getLsbD i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, hge]

private theorem bv32_zeroExtend_ne_zero {x : BitVec 32} (hx : x.toNat ≠ 0) :
    x.zeroExtend 64 ≠ 0#64 := by
  intro h
  apply hx
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)] at hnat
  exact hnat

private theorem bv32_zeroExtend_lt32 (x : BitVec 32) :
    (x.zeroExtend 64).toNat < 2 ^ 32 := by
  rw [BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]
  exact x.isLt

private theorem bv64_truncate_ne_zero {x : BitVec 64} (hx0 : 0 < x.toNat) (hx32 : x.toNat < 2 ^ 32) :
    x.truncate 32 ≠ 0#32 := by
  intro h
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.truncate, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx32] at hnat
  have hz : (0#32 : BitVec 32).toNat = 0 := rfl
  rw [hz] at hnat
  omega

private theorem bv64_pos_lt32_and_mask {x : BitVec 64} (hx0 : 0 < x.toNat) (hx32 : x.toNat < 2 ^ 32) :
    (x &&& 0xffffffff#64) ≠ 0#64 := by
  rw [← bv64_zeroExtend_truncate_of_lt hx32, bv32_zeroExtend_and_mask]
  refine bv32_zeroExtend_ne_zero ?_
  rw [BitVec.truncate, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx32]
  omega

private theorem bv64_and_mask_lt32 (x : BitVec 64) :
    (x &&& 0xffffffff#64).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_and]
  have hle := Nat.and_le_right (n := x.toNat) (m := (0xffffffff#64 : BitVec 64).toNat)
  have hm : (0xffffffff#64 : BitVec 64).toNat = 2 ^ 32 - 1 := by decide
  omega

private theorem bv64_ofInt_div2_toInt {v : BitVec 64} (hv : 0 ≤ v.toInt) :
    (BitVec.ofInt 64 (v.toInt / 2)).toInt = v.toInt / 2 := by
  have hlt := v.toInt_lt
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

private theorem castVal_u64_to_u64 (m : Mem) {ty : CTy} (hk : ty.unqual = .int .u64) (v : BitVec 64) :
    Sem.castVal m ty (.int .u64 v) = some (.int .u64 v) := by
  rw [castVal_unqual, hk]
  exact castVal_int_self m .u64 v

private theorem coerceCallArgs_1 (m : Mem) (t1 : CTy) (v1 cv1 : Val) (a1 : CTy)
    (hc1 : Sem.castVal m t1 v1 = some cv1) :
    Sem.coerceCallArgs m [t1] false [(v1, a1)] = some [cv1] := by
  simp [Sem.coerceCallArgs, hc1]

private theorem coerceCallArgs_2 (m : Mem) (t1 t2 : CTy) (v1 cv1 v2 cv2 : Val) (a1 a2 : CTy)
    (hc1 : Sem.castVal m t1 v1 = some cv1) (hc2 : Sem.castVal m t2 v2 = some cv2) :
    Sem.coerceCallArgs m [t1, t2] false [(v1, a1), (v2, a2)] = some [cv1, cv2] := by
  simp [Sem.coerceCallArgs, hc1, hc2]

private theorem coerceCallArgs_3 (m : Mem) (t1 t2 t3 : CTy) (v1 cv1 v2 cv2 v3 cv3 : Val) (a1 a2 a3 : CTy)
    (hc1 : Sem.castVal m t1 v1 = some cv1) (hc2 : Sem.castVal m t2 v2 = some cv2)
    (hc3 : Sem.castVal m t3 v3 = some cv3) :
    Sem.coerceCallArgs m [t1, t2, t3] false [(v1, a1), (v2, a2), (v3, a3)] = some [cv1, cv2, cv3] := by
  simp [Sem.coerceCallArgs, hc1, hc2, hc3]

private theorem wp_call1_pure {prog ext sym fn Pre Post coerced fs ctx env blks m os k Q e1 v1 t1}
    (hspec : FuncBodySpec prog zlibPointerConfig ext fn Pre Post)
    (henv : env.lookup sym = none)
    (henum : enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (fnDefSig fn))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (he1 : PureEval prog zlibPointerConfig env m [] e1 v1 t1)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false [(v1, t1)] = some coerced)
    (hpre : Pre m coerced)
    (hcont : ∀ ret m', ROExt m m' → Post m coerced ret m' →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os k)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.expr (.eval .rval (.call (.var sym) [e1]) fs) ctx []) env blks m os k) := by
  let fnTy := CTy.fnPtr fn.retTy (fn.params.map (·.ty)) fn.variadic
  have hlu : Sem.stepExprPure prog zlibPointerConfig env m [] (.eval .rval (.var sym) (.callFnF [e1] :: fs)) =
      some (.ret (.rval (.fnPtr sym) fnTy) (.callFnF [e1] :: fs), m, []) := by
    simp [Sem.stepExprPure, henv, henum, hproto, fnDefSig, fnTy]
  refine WPTerm.of_exprPure rfl (WPTerm.of_exprPure hlu (WPTerm.of_exprPure rfl (he1 ?_)))
  refine FuncBodySpec.call hspec (fnTy := fnTy) ?_ hfn hsym hnonvar hcoerce hpre hsimp hcont
  cases v1 <;> rfl

private theorem wp_call2_pure {prog ext sym fn Pre Post coerced fs ctx env blks m os k Q e1 v1 t1 e2 v2 t2}
    (hspec : FuncBodySpec prog zlibPointerConfig ext fn Pre Post)
    (henv : env.lookup sym = none)
    (henum : enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (fnDefSig fn))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (he1 : PureEval prog zlibPointerConfig env m [] e1 v1 t1)
    (he2 : PureEval prog zlibPointerConfig env m [] e2 v2 t2)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false [(v1, t1), (v2, t2)] = some coerced)
    (hpre : Pre m coerced)
    (hcont : ∀ ret m', ROExt m m' → Post m coerced ret m' →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os k)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.expr (.eval .rval (.call (.var sym) [e1, e2]) fs) ctx []) env blks m os k) := by
  let fnTy := CTy.fnPtr fn.retTy (fn.params.map (·.ty)) fn.variadic
  have hlu : Sem.stepExprPure prog zlibPointerConfig env m [] (.eval .rval (.var sym) (.callFnF [e1, e2] :: fs)) =
      some (.ret (.rval (.fnPtr sym) fnTy) (.callFnF [e1, e2] :: fs), m, []) := by
    simp [Sem.stepExprPure, henv, henum, hproto, fnDefSig, fnTy]
  refine WPTerm.of_exprPure rfl (WPTerm.of_exprPure hlu (WPTerm.of_exprPure rfl (he1 (WPTerm.of_exprPure rfl (he2 ?_)))))
  refine FuncBodySpec.call hspec (fnTy := fnTy) ?_ hfn hsym hnonvar hcoerce hpre hsimp hcont
  cases v2 <;> rfl

private theorem wp_call3_pure {prog ext sym fn Pre Post coerced fs ctx env blks m os k Q e1 v1 t1 e2 v2 t2 e3 v3 t3}
    (hspec : FuncBodySpec prog zlibPointerConfig ext fn Pre Post)
    (henv : env.lookup sym = none)
    (henum : enumConst? prog.tags sym = none)
    (hproto : prog.fnProtos sym = some (fnDefSig fn))
    (hfn : prog.fns sym = some fn)
    (hsym : fn.name = sym)
    (hnonvar : fn.variadic = false)
    (hsimp : ∀ p ∈ fn.params, IsSimpleParamTy p.ty)
    (he1 : PureEval prog zlibPointerConfig env m [] e1 v1 t1)
    (he2 : PureEval prog zlibPointerConfig env m [] e2 v2 t2)
    (he3 : PureEval prog zlibPointerConfig env m [] e3 v3 t3)
    (hcoerce : Sem.coerceCallArgs m (fn.params.map (·.ty)) false [(v1, t1), (v2, t2), (v3, t3)] = some coerced)
    (hpre : Pre m coerced)
    (hcont : ∀ ret m', ROExt m m' → Post m coerced ret m' →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.expr (.ret (.rval ret fn.retTy) fs) ctx []) env blks m' os k)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.expr (.eval .rval (.call (.var sym) [e1, e2, e3]) fs) ctx []) env blks m os k) := by
  let fnTy := CTy.fnPtr fn.retTy (fn.params.map (·.ty)) fn.variadic
  have hlu : Sem.stepExprPure prog zlibPointerConfig env m [] (.eval .rval (.var sym) (.callFnF [e1, e2, e3] :: fs)) =
      some (.ret (.rval (.fnPtr sym) fnTy) (.callFnF [e1, e2, e3] :: fs), m, []) := by
    simp [Sem.stepExprPure, henv, henum, hproto, fnDefSig, fnTy]
  refine WPTerm.of_exprPure rfl (WPTerm.of_exprPure hlu (WPTerm.of_exprPure rfl
    (he1 (WPTerm.of_exprPure rfl (he2 (WPTerm.of_exprPure rfl (he3 ?_)))))))
  refine FuncBodySpec.call hspec (fnTy := fnTy) ?_ hfn hsym hnonvar hcoerce hpre hsimp hcont
  cases v3 <;> rfl

private def x2nmodpPre (prog : Prog) (gEnv : Env) (m : Mem) (args : List Val) : Prop :=
  X2nTableValid prog gEnv m ∧ ∃ (n0 : BitVec 64) (k0 : BitVec 32), args = [.int .i64 n0, .int .u32 k0] ∧ 0 ≤ n0.toInt

private def x2nmodpPost (_m : Mem) (_args : List Val) (ret : Val) (_m' : Mem) : Prop :=
  ∃ p : BitVec 64, ret = .int .u64 p ∧ 0 < p.toNat ∧ p.toNat < 2 ^ 32

theorem x2nmodp_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_x2nmodp
      (x2nmodpPre prog gEnv) x2nmodpPost := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨hx0, n0, k0, rfl, hn0_nonneg⟩
  obtain ⟨hsz0, hal0, hba0, m_n, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_k, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  cases hpush2
  let b_n := m.nextBlock
  let b_k := m_n.nextBlock
  have hnext_n : b_k = b_n + 1 := by
    dsimp [b_n, b_k]; rw [writeVal_nextBlock hwr0]; exact alloc_snd_nextBlock _ _ _ _ _ _ _ _ _ _
  have hm1_next : m1.nextBlock = b_k + 1 := by
    dsimp [b_k]; rw [writeVal_nextBlock hwr1]; exact alloc_snd_nextBlock _ _ _ _ _ _ _ _ _ _
  have hf_call : LocalFrameMem m m1 [b_k, b_n] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  let zOff64Ty : CTy := .typedef "z_off64_t" (.int .i64)
  let u32Ty : CTy := .int .u32
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_x2nmodp.name ++ prog.globalEnv
  have hn_slot0 : IntSlot (("n", b_n, zOff64Ty) :: env0) m_n "n" b_n zOff64Ty .i64 n0 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  have hn_slot : IntSlot (("k", b_k, u32Ty) :: ("n", b_n, zOff64Ty) :: env0) m1 "n" b_n zOff64Ty .i64 n0 :=
    hn_slot0.preserve_pushParam (ha := rfl) hwr1 (by decide)
  have hk_slot : IntSlot (("k", b_k, u32Ty) :: ("n", b_n, zOff64Ty) :: env0) m1 "k" b_k u32Ty .u32 k0 :=
    IntSlot.of_pushCallParam rfl rfl hwr1 _
  -- Enter fn.body block and step .decl p to .decls [p]
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  -- Decl p
  refine wp_localDecl_int_none (ik := .u64) rfl rfl rfl rfl hf_call ?_
  intro ba_p bid_p m_dp hsz_p hal_p hba_p ha_p hbid_p hnext_p hf_dp hp_uninit
  have hlt_nk : b_n < b_k := by rw [hnext_n]; exact Nat.lt_succ_self _
  have hlt_kp : b_k < bid_p := by rw [hbid_p, hm1_next]; exact Nat.lt_succ_self _
  have hne_nk : b_n ≠ b_k := Nat.ne_of_lt hlt_nk
  have hne_np : b_n ≠ bid_p := Nat.ne_of_lt (Nat.lt_trans hlt_nk hlt_kp)
  have hne_kp : b_k ≠ bid_p := Nat.ne_of_lt hlt_kp
  have hn_dp := hn_slot.preserve_localDecl_none ha_p (by decide)
  have hk_dp := hk_slot.preserve_localDecl_none ha_p (by decide)
  let callEnv : Env := ("k", b_k, u32Ty) :: ("n", b_n, zOff64Ty) :: env0
  let loopEnv : Env := ("p", bid_p, uLongTy) :: callEnv
  -- Step past decls [] and .stmts
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  -- p = (uLong)1 << 31
  have hp_init_expr : PureEval prog zlibPointerConfig loopEnv m_dp []
      (CExpr.binary .shl (CExpr.cast uLongTy (CExpr.lit 1)) (CExpr.lit 31))
      (.int .u64 (1#64 <<< 31)) (.int .u64) :=
    pureEval_binary_int
      (pureEval_cast pureEval_lit (castVal_int_eq (k2 := .u64) rfl _))
      pureEval_lit rfl rfl (evalIntBinary_u64_shl_i32 1#64 (sh := 31) (by decide))
  refine wp_stmt_assign_int hp_uninit (by simp) hf_dp hp_init_expr ?_
  intro m_p0 hwr_p0 hf_p0 hp_slot0
  have hn_p0 := hn_dp.preserve_ne hwr_p0 hne_np
  have hk_p0 := hk_dp.preserve_ne hwr_p0 hne_kp
  have hp_eq_1 : (BitVec.ofInt 64 (1#64 <<< 31).toNat) = 1#64 <<< 31 := bitVec_ofInt_toNat 64 _
  have hp_p0 : IntSlot loopEnv m_p0 "p" bid_p uLongTy .u64 (1#64 <<< 31) := by
    erw [hp_eq_1] at hp_slot0; exact hp_slot0
  refine WPTerm.of_det (by rfl) ?_
  -- Lookup properties of loopEnv (independent of memory)
  have hx_lu : loopEnv.lookup "x2n_table" = gEnv.lookup "x2n_table" := by
    dsimp [loopEnv, callEnv, env0]
    erw [prog_fnStatics_x2nmodp hlib]
    rw [List.nil_append, hlib.globalEnv_eq,
      lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
  have hm_none : loopEnv.lookup "multmodp" = none := by
    dsimp [loopEnv, callEnv, env0]
    erw [prog_fnStatics_x2nmodp hlib]
    rw [List.nil_append, hlib.globalEnv_eq,
      lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
    exact hlib.gEnv_lookup_none "multmodp" (by decide)
  have hm_enum : enumConst? prog.tags "multmodp" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "multmodp" (by decide)
  have hm_proto := prog_fnProtos_multmodp hlib
  have hm_fn := prog_fns_multmodp hlib
  have hm_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_multmodp.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Crc32.crc32TU_fn_multmodp] at hp
    rcases hp with rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  let loopBlks : List BlockId := [bid_p]
  let loopCont : Sem.Cont := .stmts [.returnStmt (some (.var "p"))]
    (.blockEnd callEnv [b_k, b_n] (.callFrame env blks Zlib.Crc32.crc32TU_fn_x2nmodp.retTy
      Zlib.Crc32.crc32TU_fn_x2nmodp.body fs ctx k))
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m_cur os' =>
    env' = loopEnv ∧ blks' = loopBlks ∧ os' = os ∧
    LocalFrameMem m m_cur (bid_p :: [b_k, b_n]) ∧
    ∃ (n_cur p_cur : BitVec 64) (k_cur : BitVec 32),
      meas = n_cur.toInt.toNat ∧ 0 ≤ n_cur.toInt ∧
      IntSlot loopEnv m_cur "n" b_n zOff64Ty .i64 n_cur ∧
      IntSlot loopEnv m_cur "k" b_k u32Ty .u32 k_cur ∧
      IntSlot loopEnv m_cur "p" bid_p uLongTy .u64 p_cur ∧
      0 < p_cur.toNat ∧ p_cur.toNat < 2 ^ 32
  have hinitInv : Inv n0.toInt.toNat loopEnv loopBlks m_p0 os :=
    ⟨rfl, rfl, rfl, hf_p0, n0, 1#64 <<< 31, k0, rfl, hn0_nonneg, hn_p0, hk_p0, hp_p0, by decide, by decide⟩
  refine WPTerm.while_wf Inv (k := loopCont) hinitInv ?_
  intro meas env' blks' m_cur os' hinv ih
  rcases hinv with ⟨rfl, rfl, hos, hf_cur, n_cur, p_cur, k_cur, hmeas, hn_nn, hn_cur, hk_cur, hp_cur,
    hp_pos, hp_lt⟩
  subst os'
  have hnc_n : ModSet.conflicts [] b_n 0 IntKind.i64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_k : ModSet.conflicts [] b_k 0 IntKind.u32.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_p : ModSet.conflicts [] bid_p 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hdec_n : zOff64Ty.decay.unqual = .int .i64 := rfl
  have hdec_p : uLongTy.decay.unqual = .int .u64 := rfl
  -- Evaluate condition n
  refine (pureEval_var_int hn_cur hnc_n) ?_
  let whileBody : CStmt := CStmt.block [
    CStmt.ifStmt (CExpr.binary .bitAnd (.var "n") (.lit 1))
      (CStmt.expr (.assign .eq (.var "p")
        (.call (.var "multmodp") [(CExpr.var "x2n_table").index (CExpr.binary .bitAnd (.var "k") (.lit 31)), .var "p"])))
      none,
    CStmt.expr (.assign .shrEq (.var "n") (.lit 1)),
    CStmt.expr (.incDec .postInc (.var "k"))
  ]
  by_cases hn_zero : n_cur = 0#64
  · -- Loop exit: n == 0
    have htr_false : Sem.isTruthy (.int .i64 n_cur) = some false := by
      rw [hn_zero]; erw [isTruthy_int]; rfl
    have hstep_fc : Sem.stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval (.int .i64 n_cur) zOff64Ty.decay) [])
          (.forCond (.var "n") none whileBody) []) loopEnv loopBlks m_cur os loopCont) =
        some (.next (.running (.stmt .nop) loopEnv loopBlks m_cur os loopCont)) := by
      unfold Sem.stepDet
      simp only [htr_false, Bool.false_eq_true, ↓reduceIte, Option.bind_some, Option.map_some]
    refine WPTerm.of_det hstep_fc (WPTerm.of_det (by rfl) ?_)
    refine wp_return_pure (fnRetTy := uLongTy) (innerBlks := [bid_p]) (callBlks := [b_k, b_n])
      (hretUnw := by rfl) (htop := by rfl) (hnv := by decide) hf_cur
      (pureEval_var_int hp_cur hnc_p)
      (castVal_int_eq (k2 := .u64) (by rfl) _) ?_
    intro ret m' hro hret _
    refine hcont ret m' hro ?_
    have hret_eq : ret = .int .u64 p_cur := by
      rw [hret]
      refine congrArg (Val.int .u64) ?_
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
    exact ⟨p_cur, hret_eq, hp_pos, hp_lt⟩
  · -- Loop body: n ≠ 0
    have htr_true : Sem.isTruthy (.int .i64 n_cur) = some true := by
      have hne : (n_cur != 0#64) = true := bne_iff_ne.mpr hn_zero
      erw [isTruthy_int, hne]
    have hstep_fc : Sem.stepDet prog zlibPointerConfig
        (.running (.expr (.ret (.rval (.int .i64 n_cur) zOff64Ty.decay) [])
          (.forCond (.var "n") none whileBody) []) loopEnv loopBlks m_cur os loopCont) =
        some (.next (.running (.stmt whileBody) loopEnv loopBlks m_cur os
          (.loop (some (.var "n")) none whileBody false loopCont))) := by
      unfold Sem.stepDet
      simp only [htr_true, ↓reduceIte, Option.bind_some, Option.map_some]
    refine WPTerm.of_det hstep_fc ?_
    -- Enter whileBody block
    refine WPTerm.of_det (by rfl) ?_
    dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
    -- Shared continuation after `if (n & 1)`
    have after_if : ∀ (m_1 : Mem) (p_1 : BitVec 64),
        LocalFrameMem m m_1 (bid_p :: [b_k, b_n]) →
        IntSlot loopEnv m_1 "n" b_n zOff64Ty .i64 n_cur →
        IntSlot loopEnv m_1 "k" b_k u32Ty .u32 k_cur →
        IntSlot loopEnv m_1 "p" bid_p uLongTy .u64 p_1 →
        0 < p_1.toNat → p_1.toNat < 2 ^ 32 →
        WPTerm prog zlibPointerConfig ext Q
          (.running (.stmt .nop) loopEnv [] m_1 os
            (.stmts [CStmt.expr (.assign .shrEq (.var "n") (.lit 1)),
                     CStmt.expr (.incDec .postInc (.var "k"))]
              (.blockEnd loopEnv loopBlks (.loop (some (.var "n")) none whileBody false loopCont)))) := by
      intro m_1 p_1 hf_1 hn_1 hk_1 hp_1 hp_1_pos hp_1_lt
      refine WPTerm.of_det (by rfl) ?_
      -- n >>= 1
      refine wp_stmt_assignOp_int (op := .shrEq) (bop := .shr) rfl hn_1 (by simp) hf_1
        pureEval_lit rfl (evalIntBinary_i64_shr_1 hn_nn) ?_
      intro m_n1 hwr_n1 hf_n1 hn_n1
      let n_next : BitVec 64 := BitVec.ofInt 64 (n_cur.toInt / 2)
      have hn_next_eq : BitVec.ofInt IntKind.i64.bits (BitVec.ofInt 64 (n_cur.toInt / 2)).toInt = n_next := by
        exact bitVec_ofInt_toInt 64 n_next
      have hn_n1' : IntSlot loopEnv m_n1 "n" b_n zOff64Ty .i64 n_next := by
        erw [hn_next_eq] at hn_n1; exact hn_n1
      have hk_n1 := hk_1.preserve_ne hwr_n1 hne_nk.symm
      have hp_n1 := hp_1.preserve_ne hwr_n1 hne_np.symm
      refine WPTerm.of_det (by rfl) ?_
      -- k++
      refine wp_stmt_postInc_u32 hk_n1 (by simp) hf_n1 ?_
      intro m_k1 hwr_k1 hf_k1 hk_k1
      have hn_k1 := hn_n1'.preserve_ne hwr_k1 hne_nk
      have hp_k1 := hp_n1.preserve_ne hwr_k1 hne_kp.symm
      -- Exit blockEnd and loopNext back to ih
      refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_))
      rw [freeStack_nil]
      have hn_toInt_nz : n_cur.toInt ≠ 0 := by
        intro hz
        apply hn_zero
        have := BitVec.ofInt_toInt (x := n_cur)
        rw [hz] at this
        exact this.symm
      have hn_pos : 0 < n_cur.toInt := by omega
      have hn_div_nn : 0 ≤ n_next.toInt := by
        dsimp [n_next]
        rw [bv64_ofInt_div2_toInt hn_nn]
        omega
      have hn_meas_lt : n_next.toInt.toNat < meas := by
        dsimp [n_next]
        rw [bv64_ofInt_div2_toInt hn_nn, hmeas]
        omega
      exact ih n_next.toInt.toNat loopEnv loopBlks m_k1 os hn_meas_lt
        ⟨rfl, rfl, rfl, hf_k1, n_next, p_1, k_cur + 1#32, rfl, hn_div_nn, hn_k1, hk_k1, hp_k1, hp_1_pos, hp_1_lt⟩
    -- Evaluate `n & 1`
    have hn_and_1 : PureEval prog zlibPointerConfig loopEnv m_cur []
        (CExpr.binary .bitAnd (.var "n") (.lit 1))
        (.int .i64 (n_cur &&& 1#64)) (.int .i64) :=
      pureEval_binary_int (pureEval_var_int hn_cur hnc_n) pureEval_lit hdec_n rfl
        (evalIntBinary_i64_and_1 n_cur)
    by_cases hbit : ((n_cur &&& 1#64) != 0#64) = true
    · refine wp_if_pure (b := true) hn_and_1 (by erw [isTruthy_int, hbit]) ?_
      simp only [↓reduceIte]
      -- p = multmodp(x2n_table[k & 31], p)
      refine WPTerm.of_det rfl ?_
      refine WPTerm.of_exprPure rfl ?_
      refine wp_lval_var hp_cur.1 ?_
      refine WPTerm.of_exprPure rfl ?_
      have hk_and_31 : PureEval prog zlibPointerConfig loopEnv m_cur []
          (CExpr.binary .bitAnd (.var "k") (.lit 31))
          (.int .u32 (k_cur &&& 31#32)) (.int .u32) :=
        pureEval_binary_int (pureEval_var_int hk_cur hnc_k) pureEval_lit rfl rfl
          (evalIntBinary_u32_and_31 k_cur)
      have hk31_lt : (k_cur &&& 31#32).toNat < 32 := by
        rw [BitVec.toNat_and]
        have hle := Nat.and_le_right (n := k_cur.toNat) (m := (31#32 : BitVec 32).toNat)
        have hm : (31#32 : BitVec 32).toNat = 31 := by decide
        omega
      have hx_cur : X2nTableValid prog gEnv m_cur := hx0.of_localFrameMem hf_cur
      obtain ⟨bv, hbv_eval, hbv_val, hbv_nz⟩ := pureEval_x2n_table hx_lu hx_cur hk_and_31 hk31_lt
      have hcoerce : Sem.coerceCallArgs m_cur (Zlib.Crc32.crc32TU_fn_multmodp.params.map (·.ty)) false
          [(.int .u32 bv, crcConstTy.decay), (.int .u64 p_cur, uLongTy.decay)] =
          some [.int .u64 (bv.zeroExtend 64), .int .u64 p_cur] :=
        coerceCallArgs_2 m_cur _ _ _ _ _ _ _ _ (castVal_u32_to_u64 m_cur rfl bv) (castVal_u64_to_u64 m_cur rfl p_cur)
      have hpre_mul : multmodpPre m_cur [.int .u64 (bv.zeroExtend 64), .int .u64 p_cur] :=
        ⟨bv.zeroExtend 64, p_cur, rfl,
          by rw [bv32_zeroExtend_and_mask]; exact bv32_zeroExtend_ne_zero hbv_nz, hp_lt⟩
      refine wp_call2_pure multmodp_spec hm_none hm_enum hm_proto hm_fn rfl rfl hm_simp
        hbv_eval (pureEval_var_int hp_cur hnc_p) hcoerce hpre_mul ?_
      intro ret m_m hro hret_mul
      dsimp [multmodpPost] at hret_mul
      let p_next : BitVec 64 := (multmodpSpec ((bv.zeroExtend 64).truncate 32) (p_cur.truncate 32)).zeroExtend 64
      have hp_next_pos : 0 < p_next.toNat := by
        have htr_bv : (bv.zeroExtend 64).truncate 32 = bv := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.truncate, BitVec.toNat_setWidth, BitVec.zeroExtend, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by omega : bv.toNat < 2 ^ 64), Nat.mod_eq_of_lt bv.isLt]
        have hm_nz : multmodpSpec bv (p_cur.truncate 32) ≠ 0#32 := by
          rw [hbv_val]
          exact x2nTableVals_nonzero_mul (k_cur &&& 31#32).toNat hk31_lt (p_cur.truncate 32)
            (bv64_truncate_ne_zero hp_pos hp_lt)
        have hnz64 : p_next ≠ 0#64 := by
          dsimp only [p_next]
          rw [htr_bv]
          exact bv32_zeroExtend_ne_zero (fun h0 => hm_nz (BitVec.eq_of_toNat_eq h0))
        exact Nat.pos_of_ne_zero (fun h0 => hnz64 (BitVec.eq_of_toNat_eq h0))
      have hp_next_lt : p_next.toNat < 2 ^ 32 := bv32_zeroExtend_lt32 _
      have hf_m : LocalFrameMem m m_m (bid_p :: [b_k, b_n]) := hf_cur.of_roExt hro
      have hp_m : IntSlot loopEnv m_m "p" bid_p uLongTy .u64 p_cur := hp_cur.preserve_roExt hro
      have hn_m : IntSlot loopEnv m_m "n" b_n zOff64Ty .i64 n_cur := hn_cur.preserve_roExt hro
      have hk_m : IntSlot loopEnv m_m "k" b_k u32Ty .u32 k_cur := hk_cur.preserve_roExt hro
      obtain ⟨m_p1, hwr_p1, hf_p1, hp_p1⟩ := hp_m.to_uninit.write hf_m (by simp) p_next
      have hn_p1 := hn_m.preserve_ne hwr_p1 hne_np
      have hk_p1 := hk_m.preserve_ne hwr_p1 hne_kp
      have hcast_p : Sem.castVal m_m uLongTy (.int .u64 p_next) = some (.int .u64 p_next) :=
        castVal_u64_to_u64 m_m rfl p_next
      have hwp_p : Sem.writePlace prog.tags m_m bid_p 0 uLongTy (.rval (.int .u64 p_next) uLongTy) =
          some (.rval (.int .u64 p_next) uLongTy, m_p1) := by
        unfold Sem.writePlace
        simp only [show uLongTy.unqual = .int .u64 from rfl, hcast_p, hwr_p1, bind, Option.bind, pure, Pure.pure]
      have hnc_wr : ModSet.conflicts [] bid_p 0 (sizeofTy prog.tags uLongTy) = false := modSet_conflicts_nil _ _ _
      have hstep_wr : Sem.stepExprPure prog zlibPointerConfig loopEnv m_m []
          (.ret (.rval ret uLongTy) [.assignRhsF .eq bid_p 0 uLongTy]) =
          some (.ret (.rval (.int .u64 p_next) uLongTy) [], m_p1, [⟨bid_p, 0, sizeofTy prog.tags uLongTy⟩]) := by
        have hret_eq : ret = .int .u64 p_next := hret_mul
        rw [hret_eq]
        simp only [Sem.stepExprPure, hnc_wr, Bool.not_false, guard_true, Sem.assignOpToBin?,
          hwp_p, bind, Option.bind, pure, Pure.pure]
      refine WPTerm.of_exprPure hstep_wr (WPTerm.of_det rfl ?_)
      exact after_if m_p1 p_next hf_p1 hn_p1 hk_p1 hp_p1 hp_next_pos hp_next_lt
    · have hbit_false : ((n_cur &&& 1#64) != 0#64) = false := Bool.eq_false_iff.mpr hbit
      refine wp_if_pure (b := false) hn_and_1 (by erw [isTruthy_int, hbit_false]) ?_
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact after_if m_cur p_cur hf_cur hn_cur hk_cur hp_cur hp_pos hp_lt

private theorem castVal_i32_to_u32 (m : Mem) {ty : CTy} (hk : ty.unqual = .int .u32) (n : Int) :
    Sem.castVal m ty (Sem.ofIntCast .i32 n) = some (.int .u32 (BitVec.ofInt 32 (BitVec.ofInt 32 n).toInt)) := by
  unfold Sem.ofIntCast
  refine (castVal_int_eq (m := m) (k1 := .i32) (k2 := .u32) hk (BitVec.ofInt IntKind.i32.bits n)).trans ?_
  refine congrArg (fun z : BitVec IntKind.u32.bits => some (Val.int .u32 z)) ?_
  rfl

private theorem wp_return_val_u64 {prog cfg ext Q innerEnv innerBlks m0 callBlks m_cur os env blks fnRetTy fs ctx k k_ret v rty}
    (hretUnw : Sem.unwindReturn m_cur innerBlks k_ret =
      some (env, blks, fnRetTy, (m_cur.freeStack innerBlks).freeStack callBlks, fs, ctx, k))
    (htop : k_ret.topRetTy = fnRetTy)
    (hnv : fnRetTy.isVoid = false)
    (hfn : fnRetTy.unqual = .int .u64)
    (hf : LocalFrameMem m0 m_cur (innerBlks ++ callBlks))
    (hcont : ∀ m', ROExt m0 m' → m' = (m_cur.freeStack innerBlks).freeStack callBlks →
      WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.int .u64 v) fnRetTy) fs) ctx []) env blks m' os k)) :
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval (.int .u64 v) rty) []) .returnVal []) innerEnv innerBlks m_cur os k_ret) := by
  have hf_call : LocalFrameMem m0 (m_cur.freeStack innerBlks) callBlks := LocalFrameMem.freeStack_sub hf
  have hro : ROExt m0 ((m_cur.freeStack innerBlks).freeStack callBlks) := LocalFrameMem.roExt_freeStack hf_call
  have hcast : Sem.castVal m_cur fnRetTy (.int .u64 v) = some (.int .u64 v) :=
    castVal_u64_to_u64 m_cur hfn v
  have hstep : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval (.int .u64 v) rty) []) .returnVal []) innerEnv innerBlks m_cur os k_ret) =
      some (.next (.running (.expr (.ret (.rval (.int .u64 v) fnRetTy) fs) ctx [])
        env blks ((m_cur.freeStack innerBlks).freeStack callBlks) os k)) := by
    unfold Sem.stepDet
    simp only [htop, hnv, Bool.false_eq_true, ↓reduceIte, hcast, hretUnw, Option.bind_some, Option.map_some]
  exact WPTerm.of_det hstep (hcont _ hro rfl)

private theorem argsWellTyped_i64 {paramTys : List CTy} {args : List Val}
    (hp : paramTys.map CTy.unqual = [.int .i64])
    (hawt : Zlib.Spec.ArgsWellTyped paramTys false args) :
    ∃ len2 : BitVec 64, args = [.int .i64 len2] := by
  rcases hawt with ⟨hlen, hval⟩
  have hlen1 : args.length = 1 := by
    have hplen : paramTys.length = 1 := by
      have := congrArg List.length hp
      simpa using this
    simpa [hplen] using hlen
  cases args with
  | nil => simp at hlen1
  | cons x0 xs0 =>
    cases xs0 with
    | cons _ _ => simp at hlen1
    | nil =>
      cases paramTys with
      | nil => simp at hp
      | cons p0 ps0 =>
        cases ps0 with
        | cons _ _ => simp at hp
        | nil =>
          simp only [List.map_cons, List.cons.injEq] at hp
          have hv0 := hval 0 (by simp)
          simp only [List.getElem?_cons_zero, List.getElem_cons_zero,
            Zlib.Spec.ValHasCTy, hp.1] at hv0
          rcases hv0 with ⟨len2, rfl⟩
          exact ⟨len2, rfl⟩

private theorem argsWellTyped_u64_u64_u64 {paramTys : List CTy} {args : List Val}
    (hp : paramTys.map CTy.unqual = [.int .u64, .int .u64, .int .u64])
    (hawt : Zlib.Spec.ArgsWellTyped paramTys false args) :
    ∃ (a1 a2 a3 : BitVec 64), args = [.int .u64 a1, .int .u64 a2, .int .u64 a3] := by
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
      rcases hv2 with ⟨a3, rfl⟩
      exact ⟨a1, a2, a3, rfl⟩

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

private def gen64Pre (prog : Prog) (gEnv : Env) (m : Mem) (args : List Val) : Prop :=
  X2nTableValid prog gEnv m ∧ ∃ len2 : BitVec 64, args = [.int .i64 len2]

private def gen64Post (_m : Mem) (_args : List Val) (ret : Val) (_m' : Mem) : Prop :=
  ∃ p : BitVec 64, ret = .int .u64 p ∧ (p = 0#64 ∨ (0 < p.toNat ∧ p.toNat < 2 ^ 32))

theorem crc32_combine_gen64_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_combine_gen64
      (gen64Pre prog gEnv) gen64Post := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨hx0, len2, rfl⟩
  obtain ⟨hsz0, hal0, hba0, m_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  cases hpush1
  let b_len2 := m.nextBlock
  let zOff64Ty : CTy := .typedef "z_off64_t" (.int .i64)
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_combine_gen64.name ++ prog.globalEnv
  let env1 : Env := ("len2", b_len2, zOff64Ty) :: env0
  have hf_call : LocalFrameMem m m1 [b_len2] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  have hlen2_slot : IntSlot env1 m1 "len2" b_len2 zOff64Ty .i64 len2 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  -- Enter fn.body block
  refine WPTerm.of_det (by rfl) ?_
  dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  have hnc_l : ModSet.conflicts [] b_len2 0 IntKind.i64.bytes = false := modSet_conflicts_nil _ _ _
  have hcmp : PureEval prog zlibPointerConfig env1 m1 []
      (CExpr.binary .lt (.var "len2") (.lit 0))
      (.int .i32 (if len2.toInt < 0 then 1#32 else 0#32)) (.int .i32) :=
    pureEval_binary_int (pureEval_var_int hlen2_slot hnc_l) pureEval_lit rfl rfl
      (evalIntBinary_i64_lt_zero len2)
  by_cases hneg : len2.toInt < 0
  · refine wp_if_pure (b := true) hcmp (by erw [isTruthy_int]; simp only [hneg, ↓reduceIte]; rfl) ?_
    simp only [↓reduceIte]
    refine wp_return_pure (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_len2])
      (hretUnw := by rfl)
      (htop := by rfl) (hnv := by decide) hf_call
      pureEval_lit
      (castVal_int_eq (k2 := .u64) (by rfl) _) ?_
    intro ret m' hro hret _
    refine hcont ret m' hro ?_
    have h0 : BitVec.ofInt IntKind.u64.bits
        (if IntKind.i32.signed then (BitVec.ofInt IntKind.i32.bits 0).toInt
         else ↑(BitVec.ofInt IntKind.i32.bits 0).toNat) = 0#64 := rfl
    have hret0 : ret = .int .u64 0#64 := by rw [hret, h0]
    exact ⟨0#64, hret0, Or.inl rfl⟩
  · refine wp_if_pure (b := false) hcmp (by erw [isTruthy_int]; simp only [hneg, ↓reduceIte]; rfl) ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
    have hx_lu : env1.lookup "x2nmodp" = none := by
      dsimp [env1, env0]
      erw [prog_fnStatics_crc32_combine_gen64 hlib]
      rw [List.nil_append, hlib.globalEnv_eq, lookup_cons_ne _ (by decide)]
      exact hlib.gEnv_lookup_none "x2nmodp" (by decide)
    have hx_enum : enumConst? prog.tags "x2nmodp" = none :=
      enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "x2nmodp" (by decide)
    have hx_proto := prog_fnProtos_x2nmodp hlib
    have hx_fn := prog_fns_x2nmodp hlib
    have hx_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_x2nmodp.params, IsSimpleParamTy p.ty := by
      intro p hp
      simp [Zlib.Crc32.crc32TU_fn_x2nmodp] at hp
      rcases hp with rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
    have hcoerce : Sem.coerceCallArgs m1 (Zlib.Crc32.crc32TU_fn_x2nmodp.params.map (·.ty)) false
        [(.int .i64 len2, zOff64Ty.decay), (Sem.ofIntCast .i32 3, .int .i32)] =
        some [.int .i64 len2, .int .u32 3#32] :=
      coerceCallArgs_2 m1 _ _ _ _ _ _ _ _ (castVal_i64_to_i64 m1 rfl len2)
        (castVal_i32_to_u32 m1 rfl 3)
    have hx_pre : x2nmodpPre prog gEnv m1 [.int .i64 len2, .int .u32 3#32] :=
      ⟨hx0.of_localFrameMem hf_call, len2, 3#32, rfl, by omega⟩
    refine wp_call2_pure (x2nmodp_spec hlib) hx_lu hx_enum hx_proto hx_fn rfl rfl hx_simp
      (pureEval_var_int hlen2_slot hnc_l) pureEval_lit hcoerce hx_pre ?_
    intro ret m' hro ⟨p, hret, hp0, hp32⟩
    subst hret
    refine wp_return_val_u64 (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_len2])
      (hretUnw := by rfl)
      (htop := by rfl) (hnv := by decide) (hfn := by rfl) (hf_call.of_roExt hro) ?_
    intro m'' hro'' _
    exact hcont (.int .u64 p) m'' hro'' ⟨p, rfl, Or.inr ⟨hp0, hp32⟩⟩

theorem crc32_combine_gen64_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_combine_gen64_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32_combine_gen64 hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32_combine_gen64 hlib) rfl ?_ (crc32_combine_gen64_spec hlib) ?_ ?_
  · intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine_gen64] at hp
    subst hp; simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args hb _ hawt
    exact ⟨X2nTableValid.of_baseInv hlib hb, argsWellTyped_i64 rfl hawt⟩
  · intro v owned m args ret m' _ hawt _ ⟨p, hret, _⟩
    subst hret
    obtain ⟨len2, rfl⟩ := argsWellTyped_i64 rfl hawt
    have hcast : Sem.castVal m' Zlib.Crc32.crc32_combine_gen64_contract.retTy (.int .u64 p) =
        some (.int .u64 p) :=
      castVal_u64_to_u64 m' rfl p
    refine ⟨.int .u64 p, hcast, ?_⟩
    simp [Zlib.Crc32.crc32_combine_gen64_contract]

theorem crc32_combine_gen_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_combine_gen
      (gen64Pre prog gEnv) gen64Post := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨hx0, len2, rfl⟩
  obtain ⟨hsz0, hal0, hba0, m_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  cases hpush1
  let b_len2 := m.nextBlock
  let zOffTy : CTy := .typedef "z_off_t" (.int .i64)
  let zOff64Ty : CTy := .typedef "z_off64_t" (.int .i64)
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_combine_gen.name ++ prog.globalEnv
  let env1 : Env := ("len2", b_len2, zOffTy) :: env0
  have hf_call : LocalFrameMem m m1 [b_len2] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  have hlen2_slot : IntSlot env1 m1 "len2" b_len2 zOffTy .i64 len2 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  refine WPTerm.of_det (by rfl) ?_
  dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  refine WPTerm.of_det (by rfl) ?_
  have hg_lu : env1.lookup "crc32_combine_gen64" = none := by
    dsimp [env1, env0]
    erw [prog_fnStatics_crc32_combine_gen hlib]
    rw [List.nil_append, hlib.globalEnv_eq, lookup_cons_ne _ (by decide)]
    exact hlib.gEnv_lookup_none "crc32_combine_gen64" (by decide)
  have hg_enum : enumConst? prog.tags "crc32_combine_gen64" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc32_combine_gen64" (by decide)
  have hg_proto := prog_fnProtos_crc32_combine_gen64 hlib
  have hg_fn := prog_fns_crc32_combine_gen64 hlib
  have hg_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc32_combine_gen64.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine_gen64] at hp
    subst hp; simp [IsSimpleParamTy, CTy.unqual]
  have hnc_l : ModSet.conflicts [] b_len2 0 IntKind.i64.bytes = false := modSet_conflicts_nil _ _ _
  have hcast_arg : PureEval prog zlibPointerConfig env1 m1 []
      (CExpr.cast zOff64Ty (.var "len2")) (.int .i64 len2) zOff64Ty :=
    pureEval_cast (pureEval_var_int hlen2_slot hnc_l) (castVal_i64_to_i64 m1 rfl len2)
  have hcoerce : Sem.coerceCallArgs m1 (Zlib.Crc32.crc32TU_fn_crc32_combine_gen64.params.map (·.ty)) false
      [(.int .i64 len2, zOff64Ty)] = some [.int .i64 len2] :=
    coerceCallArgs_1 m1 _ _ _ _ (castVal_i64_to_i64 m1 rfl len2)
  have hg_pre : gen64Pre prog gEnv m1 [.int .i64 len2] :=
    ⟨hx0.of_localFrameMem hf_call, len2, rfl⟩
  refine wp_call1_pure (crc32_combine_gen64_spec hlib) hg_lu hg_enum hg_proto hg_fn rfl rfl hg_simp
    hcast_arg hcoerce hg_pre ?_
  intro ret m' hro ⟨p, hret, hp_disj⟩
  subst hret
  refine wp_return_val_u64 (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_len2])
    (hretUnw := by rfl)
    (htop := by rfl) (hnv := by decide) (hfn := by rfl) (hf_call.of_roExt hro) ?_
  intro m'' hro'' _
  exact hcont (.int .u64 p) m'' hro'' ⟨p, rfl, hp_disj⟩

theorem crc32_combine_gen_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_combine_gen_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32_combine_gen hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32_combine_gen hlib) rfl ?_ (crc32_combine_gen_spec hlib) ?_ ?_
  · intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine_gen] at hp
    subst hp; simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args hb _ hawt
    exact ⟨X2nTableValid.of_baseInv hlib hb, argsWellTyped_i64 rfl hawt⟩
  · intro v owned m args ret m' _ hawt _ ⟨p, hret, _⟩
    subst hret
    obtain ⟨len2, rfl⟩ := argsWellTyped_i64 rfl hawt
    refine ⟨.int .u64 p, castVal_u64_to_u64 m' rfl p, ?_⟩
    simp [Zlib.Crc32.crc32_combine_gen_contract]

private def combineOpPre (_m : Mem) (args : List Val) : Prop :=
  ∃ crc1 crc2 op : BitVec 64, args = [.int .u64 crc1, .int .u64 crc2, .int .u64 op] ∧
    (op = 0#64 ∨ (op &&& 0xffffffff#64) ≠ 0#64)

private def combineOpPost (_m : Mem) (_args : List Val) (ret : Val) (_m' : Mem) : Prop :=
  ∃ bv : BitVec 64, ret = .int .u64 bv

theorem crc32_combine_op_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_combine_op
      combineOpPre combineOpPost := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨crc1, crc2, op, rfl, hop⟩
  obtain ⟨hsz0, hal0, hba0, m_1, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_2, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m_3, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let b_1 := m.nextBlock
  let b_2 := m_1.nextBlock
  let b_3 := m_2.nextBlock
  have hnext1 : b_2 = b_1 + 1 := by
    dsimp [b_1, b_2]; rw [writeVal_nextBlock hwr0]; exact alloc_snd_nextBlock _ _ _ _ _ _ _ _ _ _
  have hnext2 : b_3 = b_2 + 1 := by
    dsimp [b_2, b_3]; rw [writeVal_nextBlock hwr1]; exact alloc_snd_nextBlock _ _ _ _ _ _ _ _ _ _
  have hlt12 : b_1 < b_2 := by rw [hnext1]; exact Nat.lt_succ_self _
  have hlt23 : b_2 < b_3 := by rw [hnext2]; exact Nat.lt_succ_self _
  have hne12 : b_1 ≠ b_2 := Nat.ne_of_lt hlt12
  have hne13 : b_1 ≠ b_3 := Nat.ne_of_lt (Nat.lt_trans hlt12 hlt23)
  have hne23 : b_2 ≠ b_3 := Nat.ne_of_lt hlt23
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_combine_op.name ++ prog.globalEnv
  let env1 : Env := ("op", b_3, uLongTy) :: ("crc2", b_2, uLongTy) :: ("crc1", b_1, uLongTy) :: env0
  have hf_call : LocalFrameMem m m1 [b_3, b_2, b_1] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  have hc1_0 : IntSlot (("crc1", b_1, uLongTy) :: env0) m_1 "crc1" b_1 uLongTy .u64 crc1 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  have hc1_1 := hc1_0.preserve_pushParam (ha := rfl) hwr1 (by decide)
  have hc2_1 : IntSlot (("crc2", b_2, uLongTy) :: ("crc1", b_1, uLongTy) :: env0) m_2 "crc2" b_2 uLongTy .u64 crc2 :=
    IntSlot.of_pushCallParam rfl rfl hwr1 _
  have hc1_slot : IntSlot env1 m1 "crc1" b_1 uLongTy .u64 crc1 :=
    hc1_1.preserve_pushParam (ha := rfl) hwr2 (by decide)
  have hc2_slot : IntSlot env1 m1 "crc2" b_2 uLongTy .u64 crc2 :=
    hc2_1.preserve_pushParam (ha := rfl) hwr2 (by decide)
  have hop_slot : IntSlot env1 m1 "op" b_3 uLongTy .u64 op :=
    IntSlot.of_pushCallParam rfl rfl hwr2 _
  -- Enter fn.body block
  refine WPTerm.of_det (by rfl) ?_
  dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  have hnc_1 : ModSet.conflicts [] b_1 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_2 : ModSet.conflicts [] b_2 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_3 : ModSet.conflicts [] b_3 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hcmp : PureEval prog zlibPointerConfig env1 m1 []
      (CExpr.binary .eq (.var "op") (.lit 0))
      (.int .i32 (if op == 0#64 then 1#32 else 0#32)) (.int .i32) :=
    pureEval_binary_int (pureEval_var_int hop_slot hnc_3) pureEval_lit rfl rfl
      (evalIntBinary_u64_eq_zero op)
  by_cases hop0 : op = 0#64
  · have hbe : (op == 0#64) = true := beq_iff_eq.mpr hop0
    refine wp_if_pure (b := true) hcmp (by erw [isTruthy_int]; simp only [hbe, ↓reduceIte]; rfl) ?_
    simp only [↓reduceIte]
    refine wp_return_pure (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_3, b_2, b_1])
      (hretUnw := by rfl)
      (htop := by rfl) (hnv := by decide) hf_call
      pureEval_lit
      (castVal_int_eq (k2 := .u64) (by rfl) _) ?_
    intro ret m' hro hret _
    refine hcont ret m' hro ?_
    have h0 : BitVec.ofInt IntKind.u64.bits
        (if IntKind.i32.signed then (BitVec.ofInt IntKind.i32.bits 0).toInt
         else ↑(BitVec.ofInt IntKind.i32.bits 0).toNat) = 0#64 := rfl
    exact ⟨0#64, by rw [hret, h0]⟩
  · have hop_nz : (op &&& 0xffffffff#64) ≠ 0#64 := by
      rcases hop with rfl | h
      · exact absurd rfl hop0
      · exact h
    have hbf : (op == 0#64) = false := beq_false_of_ne hop0
    refine wp_if_pure (b := false) hcmp
      (by erw [isTruthy_int]; simp only [hbf, Bool.false_eq_true, ↓reduceIte]; rfl) ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
    -- Push binLhsF for `^ (crc2 & 0xffffffff)`
    refine WPTerm.of_exprPure rfl ?_
    have hm_none : env1.lookup "multmodp" = none := by
      dsimp [env1, env0]
      erw [prog_fnStatics_crc32_combine_op hlib]
      rw [List.nil_append, hlib.globalEnv_eq,
        lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
      exact hlib.gEnv_lookup_none "multmodp" (by decide)
    have hm_enum : enumConst? prog.tags "multmodp" = none :=
      enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "multmodp" (by decide)
    have hm_proto := prog_fnProtos_multmodp hlib
    have hm_fn := prog_fns_multmodp hlib
    have hm_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_multmodp.params, IsSimpleParamTy p.ty := by
      intro p hp
      simp [Zlib.Crc32.crc32TU_fn_multmodp] at hp
      rcases hp with rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
    have hmask32 : (BitVec.ofInt 32 4294967295).zeroExtend 64 = 0xffffffff#64 := by decide
    have hc1_mask : PureEval prog zlibPointerConfig env1 m1 []
        (CExpr.binary .bitAnd (.var "crc1") (.lit 4294967295 .u32 .none .hex))
        (.int .u64 (crc1 &&& 0xffffffff#64)) (.int .u64) := by
      rw [← hmask32]
      exact pureEval_binary_int (pureEval_var_int hc1_slot hnc_1) pureEval_lit rfl rfl
        (evalIntBinary_u64_and_u32 crc1 _)
    have hcoerce : Sem.coerceCallArgs m1 (Zlib.Crc32.crc32TU_fn_multmodp.params.map (·.ty)) false
        [(.int .u64 op, uLongTy.decay), (.int .u64 (crc1 &&& 0xffffffff#64), .int .u64)] =
        some [.int .u64 op, .int .u64 (crc1 &&& 0xffffffff#64)] :=
      coerceCallArgs_2 m1 _ _ _ _ _ _ _ _
        (castVal_u64_to_u64 m1 rfl op) (castVal_u64_to_u64 m1 rfl (crc1 &&& 0xffffffff#64))
    have hpre_mul : multmodpPre m1 [.int .u64 op, .int .u64 (crc1 &&& 0xffffffff#64)] :=
      ⟨op, crc1 &&& 0xffffffff#64, rfl, hop_nz, bv64_and_mask_lt32 crc1⟩
    refine wp_call2_pure multmodp_spec hm_none hm_enum hm_proto hm_fn rfl rfl hm_simp
      (pureEval_var_int hop_slot hnc_3) hc1_mask hcoerce hpre_mul ?_
    intro ret m' hro hret_mul
    dsimp [multmodpPost] at hret_mul
    let mulRes : BitVec 64 := (multmodpSpec (op.truncate 32) ((crc1 &&& 0xffffffff#64).truncate 32)).zeroExtend 64
    have hret_eq : ret = .int .u64 mulRes := hret_mul
    rw [hret_eq]
    refine WPTerm.of_exprPure rfl ?_
    have hc2_slot' := hc2_slot.preserve_roExt hro
    have hc2_mask : PureEval prog zlibPointerConfig env1 m' []
        (CExpr.binary .bitAnd (.var "crc2") (.lit 4294967295 .u32 .none .hex)).paren
        (.int .u64 (crc2 &&& 0xffffffff#64)) (.int .u64) := by
      refine pureEval_paren ?_
      rw [← hmask32]
      exact pureEval_binary_int (pureEval_var_int hc2_slot' hnc_2) pureEval_lit rfl rfl
        (evalIntBinary_u64_and_u32 crc2 _)
    refine hc2_mask ?_
    have happ_xor : Sem.applyBinary zlibPointerConfig prog.tags m' .bitXor
        (.int .u64 mulRes) Zlib.Crc32.crc32TU_fn_multmodp.retTy (.int .u64 (crc2 &&& 0xffffffff#64)) (.int .u64) =
        some (.int .u64 (mulRes ^^^ (crc2 &&& 0xffffffff#64)), .int .u64) := by
      rw [applyBinary_int (k1 := .u64) (k2 := .u64) (by rfl) (by rfl)]
      exact evalIntBinary_u64_xor_u64 mulRes (crc2 &&& 0xffffffff#64)
    have hstep_xor : Sem.stepExprPure prog zlibPointerConfig env1 m' []
        (.ret (.rval (.int .u64 (crc2 &&& 0xffffffff#64)) (.int .u64))
          [.binRhsF .bitXor (.int .u64 mulRes) Zlib.Crc32.crc32TU_fn_multmodp.retTy]) =
        some (.ret (.rval (.int .u64 (mulRes ^^^ (crc2 &&& 0xffffffff#64))) (.int .u64)) [], m', []) := by
      simp [Sem.stepExprPure, happ_xor]
    refine WPTerm.of_exprPure hstep_xor ?_
    refine wp_return_val_u64 (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_3, b_2, b_1])
      (hretUnw := by rfl)
      (htop := by rfl) (hnv := by decide) (hfn := by rfl) (hf_call.of_roExt hro) ?_
    intro m'' hro'' _
    exact hcont (.int .u64 (mulRes ^^^ (crc2 &&& 0xffffffff#64))) m'' hro'' ⟨_, rfl⟩

theorem crc32_combine_op_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_combine_op_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32_combine_op hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32_combine_op hlib) rfl ?_ (crc32_combine_op_spec hlib) ?_ ?_
  · intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine_op] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args _ hpre hawt
    obtain ⟨crc1, crc2, op, rfl⟩ := argsWellTyped_u64_u64_u64 rfl hawt
    simp only [Zlib.Crc32.crc32_combine_op_contract] at hpre
    refine ⟨crc1, crc2, op, rfl, ?_⟩
    rcases hpre with h0 | hnz
    · exact Or.inl (congrArg UInt64.toBitVec h0)
    · refine Or.inr (fun h => hnz ?_)
      exact congrArg UInt64.ofBitVec h
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨crc1, crc2, op, rfl⟩ := argsWellTyped_u64_u64_u64 rfl hawt
    refine ⟨.int .u64 bv, castVal_u64_to_u64 m' rfl bv, ?_⟩
    simp [Zlib.Crc32.crc32_combine_op_contract]

private def combine64Pre (prog : Prog) (gEnv : Env) (m : Mem) (args : List Val) : Prop :=
  X2nTableValid prog gEnv m ∧
    ∃ crc1 crc2 len2 : BitVec 64, args = [.int .u64 crc1, .int .u64 crc2, .int .i64 len2]

private def combine64Post (_m : Mem) (_args : List Val) (ret : Val) (_m' : Mem) : Prop :=
  ∃ bv : BitVec 64, ret = .int .u64 bv

theorem crc32_combine64_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_combine64
      (combine64Pre prog gEnv) combine64Post := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨hx0, crc1, crc2, len2, rfl⟩
  obtain ⟨hsz0, hal0, hba0, m_1, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_2, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m_3, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let b_1 := m.nextBlock
  let b_2 := m_1.nextBlock
  let b_3 := m_2.nextBlock
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let zOff64Ty : CTy := .typedef "z_off64_t" (.int .i64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_combine64.name ++ prog.globalEnv
  let env1 : Env := ("len2", b_3, zOff64Ty) :: ("crc2", b_2, uLongTy) :: ("crc1", b_1, uLongTy) :: env0
  have hf_call : LocalFrameMem m m1 [b_3, b_2, b_1] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  have hc1_0 : IntSlot (("crc1", b_1, uLongTy) :: env0) m_1 "crc1" b_1 uLongTy .u64 crc1 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  have hc1_1 := hc1_0.preserve_pushParam (ha := rfl) hwr1 (by decide)
  have hc2_1 : IntSlot (("crc2", b_2, uLongTy) :: ("crc1", b_1, uLongTy) :: env0) m_2 "crc2" b_2 uLongTy .u64 crc2 :=
    IntSlot.of_pushCallParam rfl rfl hwr1 _
  have hc1_slot : IntSlot env1 m1 "crc1" b_1 uLongTy .u64 crc1 :=
    hc1_1.preserve_pushParam (ha := rfl) hwr2 (by decide)
  have hc2_slot : IntSlot env1 m1 "crc2" b_2 uLongTy .u64 crc2 :=
    hc2_1.preserve_pushParam (ha := rfl) hwr2 (by decide)
  have hlen2_slot : IntSlot env1 m1 "len2" b_3 zOff64Ty .i64 len2 :=
    IntSlot.of_pushCallParam rfl rfl hwr2 _
  refine WPTerm.of_det (by rfl) ?_
  dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  refine WPTerm.of_det (by rfl) ?_
  have hop_none : env1.lookup "crc32_combine_op" = none := by
    dsimp [env1, env0]
    erw [prog_fnStatics_crc32_combine64 hlib]
    rw [List.nil_append, hlib.globalEnv_eq,
      lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
    exact hlib.gEnv_lookup_none "crc32_combine_op" (by decide)
  have hop_enum : enumConst? prog.tags "crc32_combine_op" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc32_combine_op" (by decide)
  have hop_proto := prog_fnProtos_crc32_combine_op hlib
  have hop_fn := prog_fns_crc32_combine_op hlib
  have hop_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc32_combine_op.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine_op] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  have hg_none : env1.lookup "crc32_combine_gen64" = none := by
    dsimp [env1, env0]
    erw [prog_fnStatics_crc32_combine64 hlib]
    rw [List.nil_append, hlib.globalEnv_eq,
      lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
    exact hlib.gEnv_lookup_none "crc32_combine_gen64" (by decide)
  have hg_enum : enumConst? prog.tags "crc32_combine_gen64" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc32_combine_gen64" (by decide)
  have hg_proto := prog_fnProtos_crc32_combine_gen64 hlib
  have hg_fn := prog_fns_crc32_combine_gen64 hlib
  have hg_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc32_combine_gen64.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine_gen64] at hp
    subst hp; simp [IsSimpleParamTy, CTy.unqual]
  let fnTy_op := CTy.fnPtr Zlib.Crc32.crc32TU_fn_crc32_combine_op.retTy
    (Zlib.Crc32.crc32TU_fn_crc32_combine_op.params.map (·.ty))
    Zlib.Crc32.crc32TU_fn_crc32_combine_op.variadic
  have hlu_op : Sem.stepExprPure prog zlibPointerConfig env1 m1 []
      (.eval .rval (.var "crc32_combine_op")
        [.callFnF [.var "crc1", .var "crc2", .call (.var "crc32_combine_gen64") [.var "len2"]]]) =
      some (.ret (.rval (.fnPtr "crc32_combine_op") fnTy_op)
        [.callFnF [.var "crc1", .var "crc2", .call (.var "crc32_combine_gen64") [.var "len2"]]], m1, []) := by
    simp [Sem.stepExprPure, hop_none, hop_enum, hop_proto, fnDefSig, fnTy_op]
  have hnc_1 : ModSet.conflicts [] b_1 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_2 : ModSet.conflicts [] b_2 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_3 : ModSet.conflicts [] b_3 0 IntKind.i64.bytes = false := modSet_conflicts_nil _ _ _
  refine WPTerm.of_exprPure rfl (WPTerm.of_exprPure hlu_op (WPTerm.of_exprPure rfl
    (pureEval_var_int hc1_slot hnc_1 (WPTerm.of_exprPure rfl (pureEval_var_int hc2_slot hnc_2
      (WPTerm.of_exprPure rfl ?_))))))
  have hcoerce_g : Sem.coerceCallArgs m1 (Zlib.Crc32.crc32TU_fn_crc32_combine_gen64.params.map (·.ty)) false
      [(.int .i64 len2, zOff64Ty.decay)] = some [.int .i64 len2] :=
    coerceCallArgs_1 m1 _ _ _ _ (castVal_i64_to_i64 m1 rfl len2)
  have hpre_g : gen64Pre prog gEnv m1 [.int .i64 len2] :=
    ⟨hx0.of_localFrameMem hf_call, len2, rfl⟩
  refine wp_call1_pure (crc32_combine_gen64_spec hlib) hg_none hg_enum hg_proto hg_fn rfl rfl hg_simp
    (pureEval_var_int hlen2_slot hnc_3) hcoerce_g hpre_g ?_
  intro opVal m_g hro_g ⟨op, hop_eq, hop_disj⟩
  subst hop_eq
  have hcoerce_op : Sem.coerceCallArgs m_g (Zlib.Crc32.crc32TU_fn_crc32_combine_op.params.map (·.ty)) false
      [(.int .u64 crc1, uLongTy.decay), (.int .u64 crc2, uLongTy.decay), (.int .u64 op, uLongTy)] =
      some [.int .u64 crc1, .int .u64 crc2, .int .u64 op] :=
    coerceCallArgs_3 m_g _ _ _ _ _ _ _ _ _ _ _ _
      (castVal_u64_to_u64 m_g rfl crc1) (castVal_u64_to_u64 m_g rfl crc2) (castVal_u64_to_u64 m_g rfl op)
  have hop_valid : op = 0#64 ∨ (op &&& 0xffffffff#64) ≠ 0#64 := by
    rcases hop_disj with rfl | ⟨hp0, hp32⟩
    · exact Or.inl rfl
    · exact Or.inr (bv64_pos_lt32_and_mask hp0 hp32)
  have hpre_op : combineOpPre m_g [.int .u64 crc1, .int .u64 crc2, .int .u64 op] :=
    ⟨crc1, crc2, op, rfl, hop_valid⟩
  refine FuncBodySpec.call (crc32_combine_op_spec hlib) (fnTy := fnTy_op) rfl hop_fn rfl rfl
    hcoerce_op hpre_op hop_simp ?_
  intro ret m_op hro_op ⟨bv, hret⟩
  subst hret
  refine wp_return_val_u64 (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_3, b_2, b_1])
    (hretUnw := by rfl)
    (htop := by rfl) (hnv := by decide) (hfn := by rfl) ((hf_call.of_roExt hro_g).of_roExt hro_op) ?_
  intro m'' hro'' _
  exact hcont (.int .u64 bv) m'' hro'' ⟨bv, rfl⟩

theorem crc32_combine64_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_combine64_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32_combine64 hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32_combine64 hlib) rfl ?_ (crc32_combine64_spec hlib) ?_ ?_
  · intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine64] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args hb _ hawt
    exact ⟨X2nTableValid.of_baseInv hlib hb, argsWellTyped_u64_u64_i64 rfl hawt⟩
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨crc1, crc2, len2, rfl⟩ := argsWellTyped_u64_u64_i64 rfl hawt
    refine ⟨.int .u64 bv, castVal_u64_to_u64 m' rfl bv, ?_⟩
    simp [Zlib.Crc32.crc32_combine64_contract]

theorem crc32_combine_spec {prog gEnv m0 os0} {ext : ExtHandler}
    (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_combine
      (combine64Pre prog gEnv) combine64Post := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q hpre _hlen hpush hcont
  rcases hpre with ⟨hx0, crc1, crc2, len2, rfl⟩
  obtain ⟨hsz0, hal0, hba0, m_1, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m_2, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m_3, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  cases hpush3
  let b_1 := m.nextBlock
  let b_2 := m_1.nextBlock
  let b_3 := m_2.nextBlock
  let uLongTy : CTy := .typedef "uLong" (.int .u64)
  let zOffTy : CTy := .typedef "z_off_t" (.int .i64)
  let zOff64Ty : CTy := .typedef "z_off64_t" (.int .i64)
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_combine.name ++ prog.globalEnv
  let env1 : Env := ("len2", b_3, zOffTy) :: ("crc2", b_2, uLongTy) :: ("crc1", b_1, uLongTy) :: env0
  have hf_call : LocalFrameMem m m1 [b_3, b_2, b_1] :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  have hc1_0 : IntSlot (("crc1", b_1, uLongTy) :: env0) m_1 "crc1" b_1 uLongTy .u64 crc1 :=
    IntSlot.of_pushCallParam rfl rfl hwr0 _
  have hc1_1 := hc1_0.preserve_pushParam (ha := rfl) hwr1 (by decide)
  have hc2_1 : IntSlot (("crc2", b_2, uLongTy) :: ("crc1", b_1, uLongTy) :: env0) m_2 "crc2" b_2 uLongTy .u64 crc2 :=
    IntSlot.of_pushCallParam rfl rfl hwr1 _
  have hc1_slot : IntSlot env1 m1 "crc1" b_1 uLongTy .u64 crc1 :=
    hc1_1.preserve_pushParam (ha := rfl) hwr2 (by decide)
  have hc2_slot : IntSlot env1 m1 "crc2" b_2 uLongTy .u64 crc2 :=
    hc2_1.preserve_pushParam (ha := rfl) hwr2 (by decide)
  have hlen2_slot : IntSlot env1 m1 "len2" b_3 zOffTy .i64 len2 :=
    IntSlot.of_pushCallParam rfl rfl hwr2 _
  refine WPTerm.of_det (by rfl) ?_
  dsimp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte]
  refine WPTerm.of_det (by rfl) ?_
  have hc64_none : env1.lookup "crc32_combine64" = none := by
    dsimp [env1, env0]
    erw [prog_fnStatics_crc32_combine hlib]
    rw [List.nil_append, hlib.globalEnv_eq,
      lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide)]
    exact hlib.gEnv_lookup_none "crc32_combine64" (by decide)
  have hc64_enum : enumConst? prog.tags "crc32_combine64" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc32_combine64" (by decide)
  have hc64_proto := prog_fnProtos_crc32_combine64 hlib
  have hc64_fn := prog_fns_crc32_combine64 hlib
  have hc64_simp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc32_combine64.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine64] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  have hnc_1 : ModSet.conflicts [] b_1 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_2 : ModSet.conflicts [] b_2 0 IntKind.u64.bytes = false := modSet_conflicts_nil _ _ _
  have hnc_3 : ModSet.conflicts [] b_3 0 IntKind.i64.bytes = false := modSet_conflicts_nil _ _ _
  have hcast_l : PureEval prog zlibPointerConfig env1 m1 []
      (CExpr.cast zOff64Ty (.var "len2")) (.int .i64 len2) zOff64Ty :=
    pureEval_cast (pureEval_var_int hlen2_slot hnc_3) (castVal_i64_to_i64 m1 rfl len2)
  have hcoerce : Sem.coerceCallArgs m1 (Zlib.Crc32.crc32TU_fn_crc32_combine64.params.map (·.ty)) false
      [(.int .u64 crc1, uLongTy.decay), (.int .u64 crc2, uLongTy.decay), (.int .i64 len2, zOff64Ty)] =
      some [.int .u64 crc1, .int .u64 crc2, .int .i64 len2] :=
    coerceCallArgs_3 m1 _ _ _ _ _ _ _ _ _ _ _ _
      (castVal_u64_to_u64 m1 rfl crc1) (castVal_u64_to_u64 m1 rfl crc2) (castVal_i64_to_i64 m1 rfl len2)
  have hpre_64 : combine64Pre prog gEnv m1 [.int .u64 crc1, .int .u64 crc2, .int .i64 len2] :=
    ⟨hx0.of_localFrameMem hf_call, crc1, crc2, len2, rfl⟩
  refine wp_call3_pure (crc32_combine64_spec hlib) hc64_none hc64_enum hc64_proto hc64_fn rfl rfl hc64_simp
    (pureEval_var_int hc1_slot hnc_1) (pureEval_var_int hc2_slot hnc_2) hcast_l hcoerce hpre_64 ?_
  intro ret m' hro ⟨bv, hret⟩
  subst hret
  refine wp_return_val_u64 (fnRetTy := uLongTy) (innerBlks := []) (callBlks := [b_3, b_2, b_1])
    (hretUnw := by rfl)
    (htop := by rfl) (hnv := by decide) (hfn := by rfl) (hf_call.of_roExt hro) ?_
  intro m'' hro'' _
  exact hcont (.int .u64 bv) m'' hro'' ⟨bv, rfl⟩

theorem crc32_combine_safe {prog gEnv m0 os0 userExt userWrite Inv}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (Zlib.Spec.zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_combine_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32_combine hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32_combine hlib) rfl ?_ (crc32_combine_spec hlib) ?_ ?_
  · intro p hp
    simp [Zlib.Crc32.crc32TU_fn_crc32_combine] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args hb _ hawt
    exact ⟨X2nTableValid.of_baseInv hlib hb, argsWellTyped_u64_u64_i64 rfl hawt⟩
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨crc1, crc2, len2, rfl⟩ := argsWellTyped_u64_u64_i64 rfl hawt
    refine ⟨.int .u64 bv, castVal_u64_to_u64 m' rfl bv, ?_⟩
    simp [Zlib.Crc32.crc32_combine_contract]

end Zlib.Proof
