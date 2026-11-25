import Zlib.Proof.Crc32Base

/-!
# Safety Proofs for `crc32.c` Core Hashing (`Zlib.Proof.Crc32`)

Proves safety, bounded termination, and read-only frame preservation (`FuncBodySpec`
and `ContractSafe`) for the core CRC-32 hashing pipeline in `Zlib.Crc32`:
- `get_crc_table` (`get_crc_table_spec`)
- `crc_word` (`crc_word_spec`)
- `crc32_braid` (`crc32_braid_spec`)
- `crc32_z` (`crc32_z_spec`, `crc32_z_safe`)
- `crc32` (`crc32_spec`, `crc32_safe`)
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec Zlib.Crc32

/-! ## 1. Type Abbreviations & Fast BitVec / Memory / `evalIntBinary` Helpers -/

private abbrev uLongTy : CTy := .typedef "uLong" (.int .u64)
private abbrev zSizeTy : CTy := .typedef "z_size_t" (.int .u64)
private abbrev uIntTy : CTy := .typedef "uInt" (.int .u32)
private abbrev zCrcTy : CTy := .typedef "z_crc_t" (.typedef "Z_U4" (.int .u32))
private abbrev zWordTy : CTy := .typedef "z_word_t" (.typedef "Z_U4" (.int .u32))
private abbrev wordConstTy : CTy := zWordTy.const_
private abbrev wordConstPtrTy : CTy := wordConstTy.ptr
private abbrev byteConstTy : CTy := (CTy.int .u8).const_
private abbrev byteConstPtrTy : CTy := byteConstTy.ptr

private theorem nodup_getElem_ne {α : Type} {l : List α} (hn : l.Nodup)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hne : i ≠ j) :
    l[i] ≠ l[j] := by
  have hp := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hn)
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt => exact hp i j hi hj hlt
  | inr hgt => exact (hp j i hj hi hgt).symm

private theorem bitVec_ofInt_toNat (n : Nat) (v : BitVec n) :
    BitVec.ofInt n (v.toNat : Int) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)]
  rfl

private theorem isTruthy_int_nat {k : IntKind} (v : BitVec k.bits) :
    Sem.isTruthy (.int k v) = some (v.toNat != 0) := by
  unfold Sem.isTruthy
  rfl

private theorem castVal_int_eq {m : Mem} {ty : CTy} {k1 k2 : IntKind}
    (hk2 : ty.unqual = .int k2) (v : BitVec k1.bits) :
    Sem.castVal m ty (.int k1 v) =
      some (.int k2 (BitVec.ofInt k2.bits (if k1.signed then v.toInt else (v.toNat : Int)))) := by
  unfold Sem.castVal
  rw [hk2]
  simp only [CTy.unqual, CTy.isVoid, CTy.intKind?, Sem.ofIntCast]
  rfl

private theorem castVal_ptr_eq {m : Mem} {ty el : CTy}
    (hp : ty.unqual = .ptr el) {p : Val} (hptr : p = .null ∨ ∃ b off, p = .ptr b off) :
    Sem.castVal m ty p = some p := by
  unfold Sem.castVal
  rw [hp]
  rcases hptr with rfl | ⟨b, off, rfl⟩ <;>
    simp only [CTy.unqual, CTy.isVoid, CTy.intKind?, Bool.false_eq_true, ↓reduceIte]

private theorem castVal_ptr_addrOf {m : Mem} {ty : CTy} {k : IntKind}
    (hk : ty.unqual = .int k) {b : BlockId} {off : Int64} {addr : UInt64}
    (haddr : m.addrOf b off = some addr) :
    Sem.castVal m ty (.ptr b off) = some (.int k (BitVec.ofNat k.bits addr.toNat)) := by
  unfold Sem.castVal
  rw [hk]
  simp only [CTy.unqual, CTy.isVoid, CTy.intKind?, Bool.false_eq_true, ↓reduceIte,
    haddr, Option.map_some]

private theorem readVal_congr_unqual (tags : TypeEnv) {m : Mem} {b : BlockId} {off : Int64}
    {ty1 ty2 : CTy} (h : ty1.unqual = ty2.unqual) :
    Sem.readVal tags m b off ty1 = Sem.readVal tags m b off ty2 := by
  unfold Sem.readVal
  rw [h]

private theorem evalPtrAdd_eq {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64}
    {blk : Block} {elemTy : CTy} {idx : Int}
    (hb : m.blocks b = some blk)
    (hlo : 0 ≤ off.toInt + idx * (max 1 (sizeofTy tags elemTy) : Int))
    (hhi : off.toInt + idx * (max 1 (sizeofTy tags elemTy) : Int) ≤ (blk.size : Int)) :
    Sem.evalPtrAdd zlibPointerConfig tags m (.ptr b off) elemTy idx =
      some (.ptr b (Int64.ofInt (off.toInt + idx * (max 1 (sizeofTy tags elemTy) : Int)))) := by
  unfold Sem.evalPtrAdd
  by_cases h0 : idx = 0
  · subst h0
    simp only [beq_self_eq_true, zlibPointerConfig, Bool.and_self, ↓reduceIte, Int.zero_mul,
      Int.add_zero, Int64.ofInt_toInt]
  · have hcond : (idx == 0 && zlibPointerConfig.allowAddZeroAny) = false := by
      simp [beq_false_of_ne h0]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, hb, decide_eq_true hlo, decide_eq_true hhi,
      Bool.and_self, guard_true, bind, Option.bind, pure, Pure.pure]

private theorem Readable.mono {m : Mem} {p : Val} {n1 n2 : Nat}
    (hr : Readable m p n2) (hle : n1 ≤ n2) : Readable m p n1 := by
  rcases hr with ⟨b, off, blk, rfl, hblk, hin, hbytes⟩
  exact ⟨b, off, blk, rfl, hblk, inBounds_mono hin hle, fun i hi => hbytes i (by omega)⟩

private theorem mod4_add_mod2_64 (a b : Nat) :
    (a + (b + 1) % 2 ^ 64) % 4 = ((a + b % 2 ^ 64) % 2 ^ 64 + 1) % 4 := by
  have hd : 4 ∣ 2 ^ 64 := by decide
  have h1 : (a + (b + 1) % 2 ^ 64) % 4 = (a + b + 1) % 4 := by
    rw [Nat.add_mod a ((b + 1) % 2 ^ 64) 4, Nat.mod_mod_of_dvd _ hd, ← Nat.add_mod, Nat.add_assoc]
  have h2 : ((a + b % 2 ^ 64) % 2 ^ 64 + 1) % 4 = (a + b + 1) % 4 := by
    rw [Nat.add_mod ((a + b % 2 ^ 64) % 2 ^ 64) 1 4, Nat.mod_mod_of_dvd _ hd,
      Nat.add_mod a (b % 2 ^ 64) 4, Nat.mod_mod_of_dvd _ hd]
    omega
  rw [h1, h2]

private theorem Readable.addrOf_succ_mod4 {m0 m : Mem} {blks : List BlockId}
    {pb : BlockId} {poff : Int64} {n : Nat} {blk : Block} {addr : UInt64}
    (hf : LocalFrameMem m0 m blks) (hr : Readable m0 (.ptr pb poff) n) (hn : 1 ≤ n)
    (hblk : m.blocks pb = some blk)
    (haddr : addr = blk.baseAddr + UInt64.ofNat poff.toInt.toNat) :
    let poff' := Int64.ofInt (poff.toInt + 1)
    let addr' := blk.baseAddr + UInt64.ofNat poff'.toInt.toNat
    addr'.toNat % 4 = (addr.toNat + 1) % 4 := by
  rcases hr with ⟨_, _, blk0, heq, hblk0, hin, _⟩
  cases heq
  have hlt := lt_nextBlock_of_some hblk0
  rw [LocalFrameMem.blocks_eq_of_lt hf hlt, hblk0] at hblk
  cases hblk
  have hin' := inBounds_iff.mp hin
  have hlt63 : poff.toInt + 1 < 2 ^ 63 := by
    have := blk.sizeLt
    rw [ptrDiffLimit_val] at this
    omega
  have hoff' : (Int64.ofInt (poff.toInt + 1)).toInt = poff.toInt + 1 :=
    int64_ofInt_toInt (by omega) hlt63
  have hnat' : (Int64.ofInt (poff.toInt + 1)).toInt.toNat = poff.toInt.toNat + 1 := by omega
  dsimp only
  rw [hnat', haddr]
  have h1 : (blk.baseAddr + UInt64.ofNat (poff.toInt.toNat + 1)).toNat =
      (blk.baseAddr.toNat + (poff.toInt.toNat + 1) % 2 ^ 64) % 2 ^ 64 := rfl
  have h2 : (blk.baseAddr + UInt64.ofNat poff.toInt.toNat).toNat =
      (blk.baseAddr.toNat + poff.toInt.toNat % 2 ^ 64) % 2 ^ 64 := rfl
  rw [h1, h2]
  have hd : 4 ∣ 2 ^ 64 := by decide
  rw [Nat.mod_mod_of_dvd _ hd]
  exact mod4_add_mod2_64 blk.baseAddr.toNat poff.toInt.toNat

private theorem evalIntBinary_u32_and_i32 (v1 : BitVec 32) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .bitAnd (.int .u32 v1) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u32 (v1 &&& BitVec.ofInt 32 n), .int .u32) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have h1 : IntKind.usualArith .u32 .i32 = .u32 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u32.bits => some (Val.int .u32 z, CTy.int .u32)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u32_xor_u32 (v1 v2 : BitVec 32) :
    Sem.evalIntBinary .bitXor (.int .u32 v1) (.int .u32 v2) =
      some (.int .u32 (v1 ^^^ v2), .int .u32) := by
  unfold Sem.evalIntBinary
  have h1 : IntKind.usualArith .u32 .u32 = .u32 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u32.bits => some (Val.int .u32 z, CTy.int .u32)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u32_shr_i32 (v : BitVec 32) {sh : Nat} (hsh : sh < 32) :
    Sem.evalIntBinary .shr (.int .u32 v) (.int .i32 (BitVec.ofInt 32 (sh : Int))) =
      some (.int .u32 (v >>> sh), .int .u32) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 (sh : Int)).toInt = (sh : Int) := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have htonat : ((sh : Int)).toNat = sh := Int.toNat_natCast sh
  have h1 : IntKind.u32.promote = .u32 := rfl
  have hsh_g : (decide ((0 : Int) ≤ (sh : Int)) && decide ((sh : Int) < ((32 : Nat) : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, hto, htonat, hsh_g, guard_true,
    Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_i32_shl_i32 {a b : Nat} (ha : a < 4) (hb : b < 4) :
    Sem.evalIntBinary .shl (.int .i32 (BitVec.ofInt 32 (a : Int)))
        (.int .i32 (BitVec.ofInt 32 (b : Int))) =
      some (.int .i32 (BitVec.ofInt 32 ((a * 2 ^ b : Nat) : Int)), .int .i32) := by
  unfold Sem.evalIntBinary
  have hta : (BitVec.ofInt 32 (a : Int)).toInt = (a : Int) := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have htb : (BitVec.ofInt 32 (b : Int)).toInt = (b : Int) := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have htonat : ((b : Int)).toNat = b := Int.toNat_natCast b
  have h2b : (2 ^ b : Nat) ≤ 8 := by
    have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  have hlt : a * 2 ^ b < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul (by omega : a ≤ 3) h2b) (by decide)
  have hin : IntKind.i32.inRange ((a * 2 ^ b : Nat) : Int) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hsh_g : (decide ((0 : Int) ≤ (b : Int)) && decide ((b : Int) < ((32 : Nat) : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have ha_g : (0 : Int) ≤ (a : Int) := by omega
  have hguard_a : (guard ((0 : Int) ≤ (a : Int)) : Option Unit) = some () := by
    change (if (0 : Int) ≤ (a : Int) then some () else none) = some ()
    simp [ha_g]
  have hpow : (a : Int) * (2 ^ b : Int) = ((a * 2 ^ b : Nat) : Int) := by push_cast; rfl
  have hof : Sem.ofIntExact .i32 ((a : Int) * (2 ^ b : Int)) =
      some (Val.int .i32 (BitVec.ofInt IntKind.i32.bits ((a * 2 ^ b : Nat) : Int))) := by
    unfold Sem.ofIntExact
    rw [hpow]
    simp only [IntKind.signed, hin, ↓reduceIte]
  have hbeq : (BinOp.shl == BinOp.shl) = true := rfl
  have h1 : IntKind.i32.promote = .i32 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, hta, htb, htonat, hsh_g, guard_true, hguard_a,
    hbeq, ↓reduceIte]
  rw [hof]
  dsimp only [bind, Option.bind, pure, Pure.pure]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  rfl

private theorem evalIntBinary_i32_lt_4 (k : BitVec 32) :
    Sem.evalIntBinary .lt (.int .i32 k) (.int .i32 4#32) =
      some (.int .i32 (if k.toInt < 4 then 1#32 else 0#32), .int .i32) := by
  unfold Sem.evalIntBinary
  have h4 : (4#32 : BitVec 32).toInt = 4 := rfl
  have h1 : IntKind.usualArith .i32 .i32 = .i32 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, BitVec.ofInt_toInt, h4, Sem.cmpOrd,
    decide_eq_true_eq]
  rfl

private theorem evalIntBinary_i32_add_1 {k : BitVec 32} (hk0 : 0 ≤ k.toInt) (hk4 : k.toInt < 4) :
    Sem.evalIntBinary .add (.int .i32 k) (.int .i32 1#32) =
      some (.int .i32 (k + 1#32), .int .i32) := by
  unfold Sem.evalIntBinary
  have h1t : (1#32 : BitVec 32).toInt = 1 := rfl
  have h1 : IntKind.usualArith .i32 .i32 = .i32 := rfl
  have hin : IntKind.i32.inRange (k.toInt + 1) = true := by
    simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
      ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hsum : BitVec.ofInt 32 (k.toInt + 1) = k + 1#32 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega), BitVec.toInt_add, h1t,
      Int.bmod_eq_of_le (by omega) (by omega)]
  have hof : Sem.ofIntExact .i32 (k.toInt + 1) =
      some (Val.int .i32 (BitVec.ofInt IntKind.i32.bits (k.toInt + 1))) := by
    unfold Sem.ofIntExact
    simp only [IntKind.signed, hin, ↓reduceIte]
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte, BitVec.ofInt_toInt]
  rw [h1t, hof]
  dsimp only [bind, Option.bind, pure, Pure.pure]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  exact hsum

private theorem evalUnary_u64_bitNot (v : BitVec 64) :
    Sem.evalUnary .bitNot (.int .u64 v) = some (.int .u64 (~~~v), .int .u64) := by
  unfold Sem.evalUnary
  have h1 : IntKind.u64.promote = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]

private theorem evalIntBinary_u64_and_i32 (v : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .bitAnd (.int .u64 v) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u64 (v &&& BitVec.ofInt 64 n), .int .u64) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u64_and_u32 (v1 : BitVec 64) (v2 : BitVec 32) :
    Sem.evalIntBinary .bitAnd (.int .u64 v1) (.int .u32 v2) =
      some (.int .u64 (v1 &&& v2.zeroExtend 64), .int .u64) := by
  unfold Sem.evalIntBinary
  have hze : BitVec.ofInt 64 (v2.toNat : Int) = v2.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v2.toNat < 2 ^ 64)]
  have h1 : IntKind.usualArith .u64 .u32 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hze]
  rfl

private theorem evalIntBinary_u64_xor_u8 (v1 : BitVec 64) (v2 : BitVec 8) :
    Sem.evalIntBinary .bitXor (.int .u64 v1) (.int .u8 v2) =
      some (.int .u64 (v1 ^^^ v2.zeroExtend 64), .int .u64) := by
  unfold Sem.evalIntBinary
  have hze : BitVec.ofInt 64 (v2.toNat : Int) = v2.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v2.toNat < 2 ^ 64)]
  have h1 : IntKind.usualArith .u64 .u8 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hze]
  rfl

private theorem evalIntBinary_u64_xor_u32 (v1 : BitVec 64) (v2 : BitVec 32) :
    Sem.evalIntBinary .bitXor (.int .u64 v1) (.int .u32 v2) =
      some (.int .u64 (v1 ^^^ v2.zeroExtend 64), .int .u64) := by
  unfold Sem.evalIntBinary
  have hze : BitVec.ofInt 64 (v2.toNat : Int) = v2.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v2.toNat < 2 ^ 64)]
  have h1 : IntKind.usualArith .u64 .u32 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hze]
  rfl

private theorem evalIntBinary_u64_shr_i32 (v : BitVec 64) {sh : Nat} (hsh : sh < 64) :
    Sem.evalIntBinary .shr (.int .u64 v) (.int .i32 (BitVec.ofInt 32 (sh : Int))) =
      some (.int .u64 (v >>> sh), .int .u64) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 (sh : Int)).toInt = (sh : Int) := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have htonat : ((sh : Int)).toNat = sh := Int.toNat_natCast sh
  have h1 : IntKind.u64.promote = .u64 := rfl
  have hsh_g : (decide ((0 : Int) ≤ (sh : Int)) && decide ((sh : Int) < ((64 : Nat) : Int))) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, hto, htonat, hsh_g, guard_true,
    Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat]
  rfl

private theorem evalIntBinary_u64_ge_i32 (v : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .ge (.int .u64 v) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .i32 (if n.toNat ≤ v.toNat then 1#32 else 0#32), .int .i32) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hnat : (BitVec.ofInt 64 n).toNat = n.toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hn0 (by omega)]
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hcmp : Sem.cmpOrd .ge (v.toNat : Int) (n.toNat : Int) = decide (n.toNat ≤ v.toNat) := by
    unfold Sem.cmpOrd
    simp only [decide_eq_decide]
    omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat,
    hnat, hcmp]
  by_cases h : n.toNat ≤ v.toNat <;> simp [h] <;> rfl

private theorem evalIntBinary_u64_lt_i32 (v : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .lt (.int .u64 v) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .i32 (if v.toNat < n.toNat then 1#32 else 0#32), .int .i32) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hnat : (BitVec.ofInt 64 n).toNat = n.toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hn0 (by omega)]
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hcmp : Sem.cmpOrd .lt (v.toNat : Int) (n.toNat : Int) = decide (v.toNat < n.toNat) := by
    unfold Sem.cmpOrd
    simp only [decide_eq_decide]
    omega
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat,
    hnat, hcmp]
  by_cases h : v.toNat < n.toNat <;> simp [h] <;> rfl

private theorem evalIntBinary_u64_ne_0 (v : BitVec 64) :
    Sem.evalIntBinary .ne (.int .u64 v) (.int .i32 0#32) =
      some (.int .i32 (if v.toNat ≠ 0 then 1#32 else 0#32), .int .i32) := by
  unfold Sem.evalIntBinary
  have h0 : (0#32 : BitVec 32).toInt = 0 := rfl
  have h064 : (BitVec.ofInt 64 0).toNat = 0 := rfl
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have hcmp : Sem.cmpOrd .ne (v.toNat : Int) (0 : Int) = decide (v.toNat ≠ 0) := by
    unfold Sem.cmpOrd
    simp only [bne_iff_ne, ne_eq, Int.natCast_eq_zero]
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.i32.bits => some (Val.int .i32 z, CTy.int .i32)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, h0, bitVec_ofInt_toNat,
    h064]
  change (if Sem.cmpOrd .ne (v.toNat : Int) (0 : Int) = true then 1#32 else 0#32) =
    (if v.toNat ≠ 0 then 1#32 else 0#32)
  rw [hcmp]
  by_cases h : v.toNat ≠ 0 <;> simp [h]

private theorem evalIntBinary_u64_div_i32 (v : BitVec 64) {n : Int} (hn0 : 0 < n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .div (.int .u64 v) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u64 (BitVec.ofNat 64 (v.toNat / n.toNat)), .int .u64) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hnat : (BitVec.ofInt 64 n).toNat = n.toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]
  have hnz : ((n.toNat : Int) == 0) = false := beq_false_of_ne (by omega)
  have hdiv_lt : v.toNat / n.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self v.toNat n.toNat) v.isLt
  have hdiv : BitVec.ofInt 64 (Int.tdiv (v.toNat : Int) (n.toNat : Int)) =
      BitVec.ofNat 64 (v.toNat / n.toNat) := by
    apply BitVec.eq_of_toNat_eq
    have ht : Int.tdiv (v.toNat : Int) (n.toNat : Int) = ((v.toNat / n.toNat : Nat) : Int) := by
      rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _)]
      norm_cast
    rw [ht, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hdiv_lt),
      Int.toNat_natCast, Nat.mod_eq_of_lt hdiv_lt]
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have h2 : IntKind.u64.signed = false := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat,
    hnat, hnz, ofIntExact_unsigned h2, hdiv]

private theorem evalIntBinary_u64_mul_i32 (v : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .mul (.int .u64 v) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u64 (BitVec.ofNat 64 (v.toNat * n.toNat)), .int .u64) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hnat : (BitVec.ofInt 64 n).toNat = n.toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt hn0 (by omega)]
  have hmul : BitVec.ofInt 64 ((v.toNat : Int) * (n.toNat : Int)) =
      BitVec.ofNat 64 (v.toNat * n.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [← Int.natCast_mul, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    rfl
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have h2 : IntKind.u64.signed = false := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat,
    hnat, ofIntExact_unsigned h2, hmul]

private theorem evalIntBinary_u64_sub_u64 (v1 v2 : BitVec 64) :
    Sem.evalIntBinary .sub (.int .u64 v1) (.int .u64 v2) =
      some (.int .u64 (v1 - v2), .int .u64) := by
  unfold Sem.evalIntBinary
  have hsub : BitVec.ofInt 64 ((v1.toNat : Int) - (v2.toNat : Int)) = v1 - v2 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_sub]
    have hlt1 := v1.isLt
    have hlt2 := v2.isLt
    rw [show ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) from rfl]
    omega
  have h1 : IntKind.usualArith .u64 .u64 = .u64 := rfl
  have h2 : IntKind.u64.signed = false := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat,
    ofIntExact_unsigned h2, hsub]

private theorem evalIntBinary_u64_sub_i32 (v1 : BitVec 64) {n : Int} (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31) :
    Sem.evalIntBinary .sub (.int .u64 v1) (.int .i32 (BitVec.ofInt 32 n)) =
      some (.int .u64 (v1 - BitVec.ofInt 64 n), .int .u64) := by
  unfold Sem.evalIntBinary
  have hto : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hsub : BitVec.ofInt 64 ((v1.toNat : Int) - ((BitVec.ofInt 64 n).toNat : Int)) =
      v1 - BitVec.ofInt 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_sub]
    have hmod : (n % (2 ^ 64 : Int)).toNat = n.toNat := by
      rw [Int.emod_eq_of_lt hn0 (by omega)]
    have hlt1 := v1.isLt
    rw [show ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) from rfl, hmod]
    omega
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have h2 : IntKind.u64.signed = false := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hto, bitVec_ofInt_toNat,
    ofIntExact_unsigned h2, hsub]

private theorem evalIntBinary_u64_add_neg1 (v : BitVec 64) :
    Sem.evalIntBinary .add (.int .u64 v) (.int .i32 (BitVec.ofInt 32 (-1))) =
      some (.int .u64 (v - 1#64), .int .u64) := by
  unfold Sem.evalIntBinary
  have hn1 : (BitVec.ofInt 32 (-1)).toInt = -1 := by decide
  have hadd : BitVec.ofInt 64 ((v.toNat : Int) + ((BitVec.ofInt 64 (-1)).toNat : Int)) = v - 1#64 := by
    apply BitVec.eq_of_toNat_eq
    have hneg : (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 := by decide
    have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
    simp only [BitVec.toNat_ofInt, BitVec.toNat_sub, hneg, h1n]
    have hlt := v.isLt
    rw [show ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) from rfl]
    omega
  have h1 : IntKind.usualArith .u64 .i32 = .u64 := rfl
  have h2 : IntKind.u64.signed = false := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hn1, bitVec_ofInt_toNat,
    ofIntExact_unsigned h2, hadd]

/-! ## 2. `PureEval` and Compositional WP Combinators -/

private structure PureEval (prog : Prog) (cfg : PointerConfig) (env : Env) (m : Mem) (mods : ModSet)
    (e : CExpr) (v : Val) (ty : CTy) : Prop where
  run : ∀ {ext : ExtHandler} {Q : Val → Mem → OSState → Prop}
    {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {blks : List BlockId} {os : OSState} {k : Sem.Cont},
    WPTerm prog cfg ext Q (.running (.expr (.ret (.rval v ty) fs) ctx mods) env blks m os k) →
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval e fs) ctx mods) env blks m os k)

private theorem pureEval_paren {prog cfg env m mods e v ty}
    (he : PureEval prog cfg env m mods e v ty) :
    PureEval prog cfg env m mods (.paren e) v ty :=
  ⟨fun hw => WPTerm.of_exprPure rfl (he.run hw)⟩

private theorem pureEval_lit {prog cfg env m mods val k s r} :
    PureEval prog cfg env m mods (.lit val k s r) (Sem.ofIntCast k val) (.int k) :=
  ⟨fun hw => WPTerm.of_exprPure rfl hw⟩

private theorem pureEval_var_int {prog cfg env m mods nm b ty ik v}
    (hs : IntSlot env m nm b ty ik v) (hnc : mods.conflicts b 0 ik.bytes = false) :
    PureEval prog cfg env m mods (.var nm) (.int ik v) ty.decay :=
  ⟨fun hw => wp_read_int hs hnc hw⟩

private theorem pureEval_var_ptr {prog cfg env m mods nm b ty el p}
    (hs : PtrSlot env m nm b ty el p) (hnc : mods.conflicts b 0 8 = false) :
    PureEval prog cfg env m mods (.var nm) p ty.decay :=
  ⟨fun hw => wp_read_ptr hs hnc hw⟩

private theorem pureEval_unary {prog cfg env m mods op e v ty rv rt}
    (he : PureEval prog cfg env m mods e v ty)
    (hun : Sem.evalUnary op v = some (rv, rt)) :
    PureEval prog cfg env m mods (.unary op e) rv rt := by
  refine ⟨fun hw => WPTerm.of_exprPure rfl (he.run (WPTerm.of_exprPure ?_ hw))⟩
  unfold Sem.stepExprPure
  simp only [hun, Option.map_some]

private theorem pureEval_binary {prog cfg env m mods op l r v1 t1 v2 t2 rv rt}
    (hl : PureEval prog cfg env m mods l v1 t1)
    (hr : PureEval prog cfg env m mods r v2 t2)
    (hbin : Sem.applyBinary cfg prog.tags m op v1 t1 v2 t2 = some (rv, rt)) :
    PureEval prog cfg env m mods (.binary op l r) rv rt := by
  refine ⟨fun hw => WPTerm.of_exprPure rfl (hl.run (WPTerm.of_exprPure rfl (hr.run (WPTerm.of_exprPure ?_ hw))))⟩
  unfold Sem.stepExprPure
  simp only [hbin, Option.map_some]

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
  refine ⟨fun hw => WPTerm.of_exprPure rfl (he.run (WPTerm.of_exprPure ?_ hw))⟩
  unfold Sem.stepExprPure
  simp only [hcast, Option.map_some]

private theorem pureEval_ptr_eq_zero {prog cfg env m mods x b ty el p}
    (hs : PtrSlot env m x b ty el p) (hnc : mods.conflicts b 0 8 = false) :
    PureEval prog cfg env m mods (.binary .eq (.var x) (.lit 0))
      (.int .i32 (match p with | .null => 1#32 | _ => 0#32)) (.int .i32) := by
  have hdec : ty.decay.isPtr = true := by simp [CTy.isPtr, CTy.decay_of_ptr hs.2.1]
  refine pureEval_binary (pureEval_var_ptr hs hnc)
    (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) ?_
  unfold Sem.applyBinary
  simp only [hdec, Bool.true_or, ↓reduceIte, Sem.evalPtrCmp]
  rcases hs.2.2.2.1 with rfl | ⟨pb, poff, rfl⟩ <;> rfl

-- Constant arithmetic helpers matching `crc32_braid` and `crc32_z`
private theorem pureEval_const_3 {prog cfg env m mods} :
    PureEval prog cfg env m mods (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren
      (.int .i32 (BitVec.ofInt 32 3)) (.int .i32) :=
  pureEval_paren (pureEval_binary_int
    (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec))
    (pureEval_lit (val := 1) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))

private theorem pureEval_const_8 {prog cfg env m mods} :
    PureEval prog cfg env m mods (CExpr.binary .mul (CExpr.lit 2) (CExpr.lit 4)).paren
      (.int .i32 (BitVec.ofInt 32 8)) (.int .i32) :=
  pureEval_paren (pureEval_binary_int
    (pureEval_lit (val := 2) (k := .i32) (s := .none) (r := .dec))
    (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))

private theorem pureEval_const_11 {prog cfg env m mods} :
    PureEval prog cfg env m mods
      (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (CExpr.lit 2) (CExpr.lit 4))
        (CExpr.lit 4)) (CExpr.lit 1))
      (.int .i32 (BitVec.ofInt 32 11)) (.int .i32) :=
  pureEval_binary_int
    (pureEval_binary_int
      (pureEval_binary_int
        (pureEval_lit (val := 2) (k := .i32) (s := .none) (r := .dec))
        (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))
      (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))
    (pureEval_lit (val := 1) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl)

private theorem pureEval_const_20 {prog cfg env m mods} :
    PureEval prog cfg env m mods (CExpr.binary .mul (CExpr.lit 5) (CExpr.lit 4)).paren
      (.int .i32 (BitVec.ofInt 32 20)) (.int .i32) :=
  pureEval_paren (pureEval_binary_int
    (pureEval_lit (val := 5) (k := .i32) (s := .none) (r := .dec))
    (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))

private theorem pureEval_const_23 {prog cfg env m mods} :
    PureEval prog cfg env m mods
      (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (CExpr.lit 5) (CExpr.lit 4))
        (CExpr.lit 4)) (CExpr.lit 1))
      (.int .i32 (BitVec.ofInt 32 23)) (.int .i32) :=
  pureEval_binary_int
    (pureEval_binary_int
      (pureEval_binary_int
        (pureEval_lit (val := 5) (k := .i32) (s := .none) (r := .dec))
        (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))
      (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl))
    (pureEval_lit (val := 1) (k := .i32) (s := .none) (r := .dec)) rfl rfl (by rfl)

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
    (hw : ∀ bid m1,
      bid = m.nextBlock →
      LocalFrameMem m0 m1 (bid :: innerBlks ++ outerBlks) →
      UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty ik →
      (∀ {nm b ty k' v}, nm ≠ d.name → IntSlot env m nm b ty k' v →
        IntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k' v) →
      (∀ {nm b ty k'}, nm ≠ d.name → UninitIntSlot env m nm b ty k' →
        UninitIntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k') →
      (∀ {nm b ty el p}, nm ≠ d.name → PtrSlot env m nm b ty el p →
        PtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el p) →
      (∀ {nm b ty el}, nm ≠ d.name → UninitPtrSlot env m nm b ty el →
        UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el) →
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
  exact hw bid m1 (congrArg Prod.fst ha).symm (hf.alloc_stack ha)
    (UninitIntSlot.of_alloc_int hk hnc ha)
    (fun hnm hs => hs.preserve_alloc ha hnm)
    (fun hnm hs => hs.preserve_alloc ha hnm)
    (fun hnm hs => hs.preserve_alloc ha hnm)
    (fun hnm hs => hs.preserve_alloc ha hnm)

private theorem wp_localDecl_ptr_none {prog cfg ext Q d rest env innerBlks m0 outerBlks m os kcont el}
    (hp : d.ty.unqual = .ptr el) (hnc : d.ty.isConst = false) (hstat : d.isStatic = false) (hnd : d.init? = none)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw : ∀ bid m1,
      bid = m.nextBlock →
      LocalFrameMem m0 m1 (bid :: innerBlks ++ outerBlks) →
      UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty el →
      (∀ {nm b ty k' v}, nm ≠ d.name → IntSlot env m nm b ty k' v →
        IntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k' v) →
      (∀ {nm b ty k'}, nm ≠ d.name → UninitIntSlot env m nm b ty k' →
        UninitIntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k') →
      (∀ {nm b ty el' p}, nm ≠ d.name → PtrSlot env m nm b ty el' p →
        PtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el' p) →
      (∀ {nm b ty el'}, nm ≠ d.name → UninitPtrSlot env m nm b ty el' →
        UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el') →
      WPTerm prog cfg ext Q
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: innerBlks) m1 os kcont)) :
    WPTerm prog cfg ext Q
      (.running (.stmt (.decls (d :: rest))) env innerBlks m os kcont) := by
  have hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit := by
    rw [sizeofTy_eq_ptr hp, ptrDiffLimit_val]; decide
  have hal : 0 < max 1 (alignofTy prog.tags d.ty) :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hd : Sem.stepDet prog cfg (.running (.stmt (.decls (d :: rest))) env innerBlks m os kcont) =
      some (.allocLocal d none rest env innerBlks m os kcont) := by
    unfold Sem.stepDet
    simp only [hstat, hnd, Bool.false_eq_true, ↓reduceIte]
  refine WPTerm.of_localDecl_none hd hsz hal ?_
  intro ba bid m1 hba ha
  exact hw bid m1 (congrArg Prod.fst ha).symm (hf.alloc_stack ha)
    (UninitPtrSlot.of_alloc_ptr hp hnc ha)
    (fun hnm hs => hs.preserve_alloc ha hnm)
    (fun hnm hs => hs.preserve_alloc ha hnm)
    (fun hnm hs => hs.preserve_alloc ha hnm)
    (fun hnm hs => hs.preserve_alloc ha hnm)

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
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hwp : Sem.writePlace prog.tags m b 0 lty (.rval (.int kr vr) rty) =
      some (.rval (.int ik vnew) lty, m') := by
    unfold Sem.writePlace
    simp only [hs.2.1, hcast, bind, Option.bind, pure, Pure.pure, hwr]
  have hstep : Sem.stepExprPure prog cfg env m []
      (.ret (.rval (.int kr vr) rty) [.assignRhsF .eq b 0 lty]) =
      some (.ret (.rval (.int ik vnew) lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure (by rfl) (hrhs.run ?_)
  refine WPTerm.of_exprPure hstep ?_
  exact WPTerm.of_det (by rfl) (hw m' hwr hf' hs')

private theorem wp_stmt_assign_ptr {prog cfg ext Q x rhs env innerBlks m0 outerBlks m os kcont b lty el p rty}
    (hs : UninitPtrSlot env m x b lty el)
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hrhs : PureEval prog cfg env m [] rhs p rty)
    (hp : p = .null ∨ ∃ pb poff, p = .ptr pb poff)
    (hw : ∀ m',
      Sem.writeVal m b 0 lty p = some m' →
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      PtrSlot env m' x b lty el p →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.assign .eq (.var x) rhs))) env innerBlks m os kcont) := by
  obtain ⟨m', hwr, hf', hs'⟩ := hs.write hf hmem hp
  have hwp := writePlace_ptr (tags := prog.tags) (rty := rty) hp hs.2.1 hwr
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hstep : Sem.stepExprPure prog cfg env m []
      (.ret (.rval p rty) [.assignRhsF .eq b 0 lty]) =
      some (.ret (.rval p lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure (by rfl) (hrhs.run ?_)
  refine WPTerm.of_exprPure hstep ?_
  have hd : Sem.stepDet prog cfg
      (.running (.expr (.ret (.rval p lty) []) .discard [⟨b, 0, sizeofTy prog.tags lty⟩]) env innerBlks m' os kcont) =
      some (.next (.running (.stmt .nop) env innerBlks m' os kcont)) := by
    unfold Sem.stepDet
    rcases hp with rfl | ⟨pb, poff, rfl⟩ <;> rfl
  exact WPTerm.of_det hd (hw m' hwr hf' hs')

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
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hrv := hs.readVal_eq prog.tags
  have happ : Sem.applyBinary cfg prog.tags m bop (.int ik vold) lty (.int kr vr) rty = some (.int kv nv, nt) := by
    rw [applyBinary_int hs.2.1 hrty]; exact hbin
  have hwp : Sem.writePlace prog.tags m b 0 lty (.rval (.int kv nv) lty) =
      some (.rval (.int ik vnew) lty, m') := by
    unfold Sem.writePlace
    simp only [hs.2.1, hcast, bind, Option.bind, pure, Pure.pure, hwr]
  have hstep : Sem.stepExprPure prog cfg env m []
      (.ret (.rval (.int kr vr) rty) [.assignRhsF op b 0 lty]) =
      some (.ret (.rval (.int ik vnew) lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, hop, hrv, happ, hwp, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure (by rfl) (hrhs.run ?_)
  refine WPTerm.of_exprPure hstep ?_
  exact WPTerm.of_det (by rfl) (hw m' hwr hf' hs')

private theorem wp_stmt_postDec_u64 {prog cfg ext Q x env innerBlks m0 outerBlks m os kcont b lty}
    {v : BitVec 64}
    (hs : IntSlot env m x b lty .u64 v)
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw : ∀ m',
      Sem.writeVal m b 0 lty (.int .u64 (v - 1#64)) = some m' →
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' x b lty .u64 (v - 1#64) →
      WPTerm prog cfg ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.expr (.incDec .postDec (.var x)))) env innerBlks m os kcont) := by
  obtain ⟨m', hwr, hf', hs'⟩ := hs.write hf hmem (v - 1#64)
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hrv := hs.readVal_eq prog.tags
  have happ : Sem.applyBinary cfg prog.tags m .add (.int .u64 v) lty (.int .i32 (BitVec.ofInt 32 (-1))) (.int .i32) =
      some (.int .u64 (v - 1#64), .int .u64) := by
    rw [applyBinary_int hs.2.1 rfl]
    exact evalIntBinary_u64_add_neg1 v
  have hstep : Sem.stepExprPure prog cfg env m []
      (.ret (.lval b 0 lty) [.incDecF .postDec]) =
      some (.ret (.rval (.int .u64 v) lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, hrv, happ, hwr, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure hstep ?_
  exact WPTerm.of_det (by rfl) (hw m' hwr hf' hs')

private theorem wp_stmt_ptr_addEq {prog ext Q x env innerBlks m0 outerBlks m os kcont b lty el pb poff blk0 n remBytes}
    (hs : PtrSlot env m x b lty el (.ptr pb poff))
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hr : Readable m0 (.ptr pb poff) remBytes)
    (hblk0 : m0.blocks pb = some blk0)
    (hn0 : 0 ≤ n) (hn31 : n < 2 ^ 31)
    (hbound : n.toNat * max 1 (sizeofTy prog.tags el) ≤ remBytes)
    (hw : ∀ m',
      Sem.writeVal m b 0 lty (.ptr pb (Int64.ofInt (poff.toInt + n.toNat * max 1 (sizeofTy prog.tags el)))) = some m' →
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      PtrSlot env m' x b lty el (.ptr pb (Int64.ofInt (poff.toInt + n.toNat * max 1 (sizeofTy prog.tags el)))) →
      Readable m0 (.ptr pb (Int64.ofInt (poff.toInt + n.toNat * max 1 (sizeofTy prog.tags el))))
        (remBytes - n.toNat * max 1 (sizeofTy prog.tags el)) →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .addEq (.var x) (.lit n .i32 .none .dec none))))
        env innerBlks m os kcont) := by
  let stepBytes := n.toNat * max 1 (sizeofTy prog.tags el)
  obtain ⟨blk', hblk', _, _, hr'⟩ := Readable.advance hr hbound
  have hlt_pb : pb < m0.nextBlock := Readable.block_lt hr
  have hm_pb : m.blocks pb = some blk0 := by
    rw [LocalFrameMem.blocks_eq_of_lt hf hlt_pb, hblk0]
  have hblk_eq : blk' = blk0 := by rw [hblk0] at hblk'; cases hblk'; rfl
  subst hblk_eq
  have hnin : (BitVec.ofInt 32 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hmul_eq : (BitVec.ofInt 32 n).toInt * (max 1 (sizeofTy prog.tags el) : Int) = (stepBytes : Int) := by
    have hnn : n = (n.toNat : Int) := by omega
    have hmax_cast : ((max 1 (sizeofTy prog.tags el) : Nat) : Int) = max (1 : Int) (sizeofTy prog.tags el : Int) := by
      omega
    calc
      (BitVec.ofInt 32 n).toInt * (max 1 (sizeofTy prog.tags el) : Int)
          = n * (max 1 (sizeofTy prog.tags el) : Int) := by rw [hnin]
      _ = (n.toNat : Int) * (max 1 (sizeofTy prog.tags el) : Int) := congrArg (· * _) hnn
      _ = (stepBytes : Int) := by
          have hstep_int : (stepBytes : Int) = (n.toNat : Int) * ((max 1 (sizeofTy prog.tags el) : Nat) : Int) :=
            Int.natCast_mul _ _
          rw [hstep_int, hmax_cast]
  rcases hr with ⟨_, _, blk'', heq, hblk'', hin, _⟩
  cases heq
  rw [hblk0] at hblk''
  cases hblk''
  have hin' := inBounds_iff.mp hin
  have hptr_add : Sem.evalPtrAdd zlibPointerConfig prog.tags m (.ptr pb poff) el (BitVec.ofInt 32 n).toInt =
      some (.ptr pb (Int64.ofInt (poff.toInt + stepBytes))) := by
    have hlo : 0 ≤ poff.toInt + (BitVec.ofInt 32 n).toInt * (max 1 (sizeofTy prog.tags el) : Int) := by
      rw [hmul_eq]; omega
    have hhi : poff.toInt + (BitVec.ofInt 32 n).toInt * (max 1 (sizeofTy prog.tags el) : Int) ≤ (blk'.size : Int) := by
      rw [hmul_eq]; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hm_pb hlo hhi
    rw [hmul_eq] at h
    exact h
  let poff' := Int64.ofInt (poff.toInt + stepBytes)
  obtain ⟨m', hwr, hf', hs'⟩ := hs.write hf hmem (Or.inr ⟨pb, poff', rfl⟩)
  have hwp := writePlace_ptr (tags := prog.tags) (rty := lty) (Or.inr ⟨pb, poff', rfl⟩) hs.2.1 hwr
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags lty) = false := modSet_conflicts_nil _ _ _
  have hrv := hs.readVal_eq prog.tags
  have happ : Sem.applyBinary zlibPointerConfig prog.tags m .add (.ptr pb poff) lty
      (Sem.ofIntCast .i32 n) (.int .i32) = some (.ptr pb poff', lty.unqual) := by
    unfold Sem.applyBinary
    simp only [CTy.isPtr, hs.2.1, Bool.true_or, ↓reduceIte, Sem.valAsInt?, Sem.ofIntCast,
      IntKind.signed, IntKind.bits]
    rw [hptr_add]
    rfl
  have hstep : Sem.stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (Sem.ofIntCast .i32 n) (.int .i32)) [.assignRhsF .addEq b 0 lty]) =
      some (.ret (.rval (.ptr pb poff') lty) [], m', [⟨b, 0, sizeofTy prog.tags lty⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, Sem.assignOpToBin?, hrv, happ, hwp,
      bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs.1 ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine (pureEval_lit (val := n) (k := .i32) (s := .none) (r := .dec)).run ?_
  refine WPTerm.of_exprPure hstep ?_
  exact WPTerm.of_det (by rfl) (hw m' hwr hf' hs' hr')

private theorem wp_if_pure {prog cfg ext Q c t f? env blks m os kcont vc tc b}
    (hc : PureEval prog cfg env m [] c vc tc)
    (htr : Sem.isTruthy vc = some b)
    (hw : WPTerm prog cfg ext Q (.running (.stmt (if b then t else f?.getD .nop)) env blks m os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.ifStmt c t f?)) env blks m os kcont) := by
  refine WPTerm.of_det (by rfl) (hc.run (WPTerm.of_det ?_ hw))
  unfold Sem.stepDet
  simp only [htr, Option.bind, Option.map_some]

private theorem wp_forCond_true {prog cfg ext Q c stp? body vc tc env blks m os kcont}
    (hc : PureEval prog cfg env m [] c vc tc)
    (htr : Sem.isTruthy vc = some true)
    (hw : WPTerm prog cfg ext Q (.running (.stmt body) env blks m os (.loop (some c) stp? body false kcont))) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os kcont) := by
  refine hc.run (WPTerm.of_det ?_ hw)
  unfold Sem.stepDet
  simp only [htr, Option.bind, Option.map_some]
  rfl

private theorem wp_forCond_false {prog cfg ext Q c stp? body vc tc env blks m os kcont}
    (hc : PureEval prog cfg env m [] c vc tc)
    (htr : Sem.isTruthy vc = some false)
    (hw : WPTerm prog cfg ext Q (.running (.stmt .nop) env blks m os kcont)) :
    WPTerm prog cfg ext Q (.running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os kcont) := by
  refine hc.run (WPTerm.of_det ?_ hw)
  unfold Sem.stepDet
  simp only [htr, Option.bind, Option.map_some]
  rfl

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
  refine WPTerm.of_det (by rfl) (he.run (WPTerm.of_det ?_ (hcont cv _ hro rfl rfl)))
  unfold Sem.stepDet
  simp only [htop, hnv, Bool.false_eq_true, ↓reduceIte, hcast, Option.bind, Option.map_some, hretUnw]

private theorem intSlot_preserve_blocks {env m m' name b ty k v}
    (hs : IntSlot env m name b ty k v) (hb : m'.blocks b = m.blocks b) :
    IntSlot env m' name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  refine ⟨hlu, hk, hnc, blk, hb.trans hblk, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] hb, hrv]

private theorem ptrSlot_preserve_blocks {env m m' name b ty el p}
    (hs : PtrSlot env m name b ty el p) (hb : m'.blocks b = m.blocks b) :
    PtrSlot env m' name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  refine ⟨hlu, hptr, hnc, hp, blk, hb.trans hblk, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] hb, hrv]

/-! ## 3. Table Predicates and Shared CRC-32 Evaluation / Loop Combinators -/

private def CrcTableValid (prog : Prog) (gEnv : Env) (m : Mem) : Prop :=
  ∃ b, gEnv.lookup "crc_table" = some (b, .array crcConstTy (some 256)) ∧
    b < m.nextBlock ∧
    ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m b (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv)

private def CrcBraidTableValid (prog : Prog) (gEnv : Env) (m : Mem) (name : String) : Prop :=
  ∃ b, gEnv.lookup name = some (b, .array (.array crcConstTy (some 256)) (some 4)) ∧
    b < m.nextBlock ∧
    ∀ row < 4, ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m b (Int64.ofNat (1024 * row + 4 * idx)) crcConstTy = some (.int .u32 bv)

private theorem CrcTableValid.of_baseInv {prog : Prog} {gEnv : Env} {m0 m0' m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet} {blks : List BlockId}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m0' os)
    (hf : LocalFrameMem m0' m blks) :
    CrcTableValid prog gEnv m := by
  obtain ⟨b, hlu, hlt, hread⟩ := readVal_crc_table hlib hb hf
  exact ⟨b, hlu, Nat.lt_of_lt_of_le hlt hf.1, hread⟩

private theorem CrcTableValid.of_localFrameMem {prog : Prog} {gEnv : Env} {m0 m : Mem} {blks : List BlockId}
    (ht : CrcTableValid prog gEnv m0) (hf : LocalFrameMem m0 m blks) :
    CrcTableValid prog gEnv m := by
  rcases ht with ⟨b, hlu, hlt, hread⟩
  refine ⟨b, hlu, Nat.lt_of_lt_of_le hlt hf.1, fun idx hidx => ?_⟩
  obtain ⟨bv, hrv⟩ := hread idx hidx
  exact ⟨bv, by rw [readVal_eq_of_blocks_eq prog.tags (LocalFrameMem.blocks_eq_of_lt hf hlt)]; exact hrv⟩

private theorem CrcBraidTableValid.of_baseInv_2 {prog : Prog} {gEnv : Env} {m0 m0' m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet} {blks : List BlockId}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m0' os)
    (hf : LocalFrameMem m0' m blks) :
    CrcBraidTableValid prog gEnv m "crc_braid2_table" := by
  obtain ⟨b, blk, hlu, hblk, _, _, hsz, hal, hbytes⟩ := hb.crc_braid2_table hlib
  obtain ⟨_, hlt, hread⟩ := readVal_crc_braid_table (prog := prog) (gEnv := gEnv) hblk hsz hal hbytes hf hlu
  exact ⟨b, hlu, Nat.lt_of_lt_of_le hlt hf.1, hread⟩

private theorem CrcBraidTableValid.of_baseInv_5 {prog : Prog} {gEnv : Env} {m0 m0' m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet} {blks : List BlockId}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m0' os)
    (hf : LocalFrameMem m0' m blks) :
    CrcBraidTableValid prog gEnv m "crc_braid5_table" := by
  obtain ⟨b, blk, hlu, hblk, _, _, hsz, hal, hbytes⟩ := hb.crc_braid5_table hlib
  obtain ⟨_, hlt, hread⟩ := readVal_crc_braid_table (prog := prog) (gEnv := gEnv) hblk hsz hal hbytes hf hlu
  exact ⟨b, hlu, Nat.lt_of_lt_of_le hlt hf.1, hread⟩

private theorem CrcBraidTableValid.of_localFrameMem {prog : Prog} {gEnv : Env} {m0 m : Mem} {blks : List BlockId}
    {name : String} (ht : CrcBraidTableValid prog gEnv m0 name) (hf : LocalFrameMem m0 m blks) :
    CrcBraidTableValid prog gEnv m name := by
  rcases ht with ⟨b, hlu, hlt, hread⟩
  refine ⟨b, hlu, Nat.lt_of_lt_of_le hlt hf.1, fun row hrow idx hidx => ?_⟩
  obtain ⟨bv, hrv⟩ := hread row hrow idx hidx
  exact ⟨bv, by rw [readVal_eq_of_blocks_eq prog.tags (LocalFrameMem.blocks_eq_of_lt hf hlt)]; exact hrv⟩

private theorem readVal_crcConst_blk {tags : TypeEnv} {m : Mem} {b : BlockId} {off : Int64} {bv : BitVec 32}
    (hrv : Sem.readVal tags m b off crcConstTy = some (.int .u32 bv)) :
    ∃ blk, m.blocks b = some blk ∧ (blk.size : Int) ≥ off.toInt + 4 := by
  unfold Sem.readVal at hrv
  dsimp only [crcConstTy, CTy.unqual, CTy.intKind?, bind, Option.bind, pure, Pure.pure] at hrv
  cases hb : m.blocks b with
  | none => simp only [hb] at hrv; cases hrv
  | some blk =>
    simp only [hb] at hrv
    cases hal : Mem.isAligned blk off 4 with
    | false =>
      have hal' : Mem.isAligned blk off IntKind.u32.align = false := hal
      simp only [hal', guard, Bool.false_eq_true, ↓reduceIte] at hrv
      cases hrv
    | true =>
      have hal' : Mem.isAligned blk off IntKind.u32.align = true := hal
      simp only [hal', guard_true] at hrv
      cases hrd : m.readBytes b off 4 with
      | none =>
        have hrd' : m.readBytes b off IntKind.u32.bytes = none := hrd
        simp only [hrd'] at hrv
        cases hrv
      | some bs =>
        have hin : Mem.inBounds blk off 4 = true := by
          unfold Mem.readBytes at hrd
          simp only [hb, bind, Option.bind, pure, Pure.pure] at hrd
          cases hib : Mem.inBounds blk off 4 with
          | false =>
            simp only [hib, guard, Bool.false_eq_true, ↓reduceIte] at hrd
            cases hrd
          | true => rfl
        rw [inBounds_iff] at hin
        exact ⟨blk, rfl, by omega⟩

private theorem pureEval_crc_table_index {prog env m mods idxExpr k idxBv rty b_ct}
    (hlu : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)))
    (hread : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv))
    (hidx_unsign : k.signed = false)
    (hidx_lt : idxBv.toNat < 256)
    (hidx : PureEval prog zlibPointerConfig env m mods idxExpr (.int k idxBv) rty)
    (hnc : ∀ off : Int64, mods.conflicts b_ct off 4 = false) :
    ∃ bv : BitVec 32,
      PureEval prog zlibPointerConfig env m mods
        ((CExpr.var "crc_table").index idxExpr) (.int .u32 bv) crcConstTy.decay := by
  obtain ⟨bv, hrv⟩ := hread idxBv.toNat hidx_lt
  obtain ⟨blk, hblk, hsz⟩ := readVal_crcConst_blk hrv
  rw [int64_ofNat_toInt (by omega)] at hsz
  have hsz_el : sizeofTy prog.tags crcConstTy = 4 := by
    simp [crcConstTy, sizeofTy, IntKind.bytes, IntKind.bits]
  have hmax : (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) = 4 := by rw [hsz_el]; decide
  have hadd : Sem.evalPtrAdd zlibPointerConfig prog.tags m (.ptr b_ct 0) crcConstTy (idxBv.toNat : Int) =
      some (.ptr b_ct (Int64.ofNat (4 * idxBv.toNat))) := by
    have hlo : 0 ≤ (0 : Int64).toInt + (idxBv.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) := by
      rw [hmax]; simp; omega
    have hhi : (0 : Int64).toInt + (idxBv.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) ≤ (blk.size : Int) := by
      rw [hmax]; simp; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hblk hlo hhi
    have hmul : (0 : Int64).toInt + (idxBv.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) =
        ((4 * idxBv.toNat : Nat) : Int) := by
      rw [hmax]; simp; omega
    rw [hmul] at h
    exact h
  have hread_arr : Sem.readPlace prog.tags m mods .rval b_ct 0 (.array crcConstTy (some 256)) =
      some (.rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay) := by
    simp [Sem.readPlace, CTy.unqual]
  have hread_el : Sem.readPlace prog.tags m mods .rval b_ct (Int64.ofNat (4 * idxBv.toNat)) crcConstTy =
      some (.rval (.int .u32 bv) crcConstTy.decay) := by
    unfold Sem.readPlace
    have hu : crcConstTy.unqual = .int .u32 := rfl
    rw [hu, hsz_el, hnc]
    simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv]
  have hdec_arr : (CTy.array crcConstTy (some 256)).decay.unqual = .ptr crcConstTy := rfl
  refine ⟨bv, ⟨fun {ext Q fs ctx blks os kcont} hw => ?_⟩⟩
  have hstep1 : Sem.stepExprPure prog zlibPointerConfig env m mods
      (.eval .rval (CExpr.var "crc_table") (.indexBaseF .rval idxExpr :: fs)) =
      some (.ret (.rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay)
        (.indexBaseF .rval idxExpr :: fs), m, mods) := by
    unfold Sem.stepExprPure
    simp only [hlu, hread_arr, Option.map_some]
  have hstep2 : Sem.stepExprPure prog zlibPointerConfig env m mods
      (.ret (.rval (.int k idxBv) rty)
        [.indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay]) =
      some (.ret (.rval (.int .u32 bv) crcConstTy.decay) [], m, mods) := by
    unfold Sem.stepExprPure
    simp only [hdec_arr, Sem.valAsInt?, hidx_unsign, Bool.false_eq_true, ↓reduceIte,
      hadd, hread_el, bind, Option.bind, pure, Pure.pure]
  have hstep2' : ∀ {fs' : List Sem.ExprFrame}, Sem.stepExprPure prog zlibPointerConfig env m mods
      (.ret (.rval (.int k idxBv) rty)
        (.indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay :: fs')) =
      some (.ret (.rval (.int .u32 bv) crcConstTy.decay) fs', m, mods) := by
    intro fs'
    unfold Sem.stepExprPure
    simp only [hdec_arr, Sem.valAsInt?, hidx_unsign, Bool.false_eq_true, ↓reduceIte,
      hadd, hread_el, bind, Option.bind, pure, Pure.pure]
  exact WPTerm.of_exprPure (by rfl) (WPTerm.of_exprPure hstep1
    (WPTerm.of_exprPure (by rfl) (hidx.run (WPTerm.of_exprPure (hstep2' (fs' := fs)) hw))))

private def crcbExpr (tbl : String) (w : String) (k : Int) : CExpr :=
  ((CExpr.var tbl).index (CExpr.lit k)).index
    (CExpr.binary .bitAnd
      (CExpr.binary .shr (CExpr.var w).paren
        (CExpr.binary .shl (CExpr.lit k).paren (CExpr.lit 3)).paren).paren
      (CExpr.lit 255 .i32 .none .hex))

private def crcwordExpr (tbl : String) (w : String) : CExpr :=
  (CExpr.binary .bitXor
    (CExpr.binary .bitXor (crcbExpr tbl w 0) (crcbExpr tbl w 1)).paren
    (CExpr.binary .bitXor (crcbExpr tbl w 2) (crcbExpr tbl w 3)).paren).paren

private theorem pureEval_crcb {prog env m tbl b_tbl w b_w ty_w} {row : Nat} {wbv : BitVec 32}
    (hlu_tbl : env.lookup tbl = some (b_tbl, .array (.array crcConstTy (some 256)) (some 4)))
    (htbl : ∀ r < 4, ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m b_tbl (Int64.ofNat (1024 * r + 4 * idx)) crcConstTy = some (.int .u32 bv))
    (hs_w : IntSlot env m w b_w ty_w .u32 wbv)
    (hrow : row < 4) :
    ∃ bv : BitVec 32,
      PureEval prog zlibPointerConfig env m [] (crcbExpr tbl w (row : Int))
        (.int .u32 bv) crcConstTy.decay := by
  have hw_eval : PureEval prog zlibPointerConfig env m [] (CExpr.var w).paren (.int .u32 wbv) ty_w.decay :=
    pureEval_paren (pureEval_var_int hs_w (modSet_conflicts_nil _ _ _))
  have hsh_ev : Sem.evalIntBinary .shl (Sem.ofIntCast .i32 (row : Int)) (Sem.ofIntCast .i32 3) =
      some (.int .i32 (BitVec.ofInt 32 ((row * 8 : Nat) : Int)), .int .i32) := by
    have h8 : row * 8 = row * 2 ^ 3 := by omega
    rw [h8]
    exact evalIntBinary_i32_shl_i32 (a := row) (b := 3) hrow (by decide)
  have hsh_eval : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren
      (.int .i32 (BitVec.ofInt 32 ((row * 8 : Nat) : Int))) (.int .i32) :=
    pureEval_paren (pureEval_binary_int
      (pureEval_paren (pureEval_lit (val := (row : Int)) (k := .i32) (s := .none) (r := .dec)))
      (pureEval_lit (val := 3) (k := .i32) (s := .none) (r := .dec)) rfl rfl hsh_ev)
  have h8_lt : 8 * row < 32 := by omega
  have hshr_ev : Sem.evalIntBinary .shr (.int .u32 wbv)
      (.int .i32 (BitVec.ofInt 32 ((row * 8 : Nat) : Int))) =
      some (.int .u32 (wbv >>> (8 * row)), .int .u32) := by
    rw [show (row * 8 : Nat) = 8 * row from Nat.mul_comm _ _]
    exact evalIntBinary_u32_shr_i32 wbv h8_lt
  have hshr_eval : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .shr (CExpr.var w).paren
        (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren).paren
      (.int .u32 (wbv >>> (8 * row))) (.int .u32) :=
    pureEval_paren (pureEval_binary_int hw_eval hsh_eval (CTy.decay_of_int hs_w.2.1) rfl hshr_ev)
  have hidx_eval : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .bitAnd
        (CExpr.binary .shr (CExpr.var w).paren
          (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren).paren
        (CExpr.lit 255 .i32 .none .hex))
      (.int .u32 ((wbv >>> (8 * row)) &&& BitVec.ofInt 32 255)) (.int .u32) :=
    pureEval_binary_int hshr_eval (pureEval_lit (val := 255) (k := .i32) (s := .none) (r := .hex)) rfl rfl
      (evalIntBinary_u32_and_i32 (wbv >>> (8 * row)) (by decide) (by decide))
  let idxBv := (wbv >>> (8 * row)) &&& BitVec.ofInt 32 255
  have hidx_lt : idxBv.toNat < 256 := by
    dsimp [idxBv]
    exact Nat.lt_succ_of_le Nat.and_le_right
  obtain ⟨bv, hrv⟩ := htbl row hrow idxBv.toNat hidx_lt
  obtain ⟨blk, hblk, hsz⟩ := readVal_crcConst_blk hrv
  rw [int64_ofNat_toInt (by omega)] at hsz
  have hsz_row : sizeofTy prog.tags (.array crcConstTy (some 256)) = 1024 := by
    simp [crcConstTy, sizeofTy, IntKind.bytes, IntKind.bits]
  have hmax_row : (max (1 : Int) (sizeofTy prog.tags (.array crcConstTy (some 256)) : Int)) = 1024 := by
    rw [hsz_row]; decide
  have hsz_el : sizeofTy prog.tags crcConstTy = 4 := by
    simp [crcConstTy, sizeofTy, IntKind.bytes, IntKind.bits]
  have hmax_el : (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) = 4 := by rw [hsz_el]; decide
  have hrow_i : (BitVec.ofInt 32 (row : Int)).toInt = (row : Int) := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hadd_row : Sem.evalPtrAdd zlibPointerConfig prog.tags m (.ptr b_tbl 0)
      (.array crcConstTy (some 256)) (BitVec.ofInt 32 (row : Int)).toInt =
      some (.ptr b_tbl (Int64.ofNat (1024 * row))) := by
    rw [hrow_i]
    have hlo : 0 ≤ (0 : Int64).toInt + (row : Int) * (max (1 : Int) (sizeofTy prog.tags (.array crcConstTy (some 256)) : Int)) := by
      rw [hmax_row]; simp; omega
    have hhi : (0 : Int64).toInt + (row : Int) * (max (1 : Int) (sizeofTy prog.tags (.array crcConstTy (some 256)) : Int)) ≤ (blk.size : Int) := by
      rw [hmax_row]; simp; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hblk hlo hhi
    have hmul : (0 : Int64).toInt + (row : Int) * (max (1 : Int) (sizeofTy prog.tags (.array crcConstTy (some 256)) : Int)) =
        ((1024 * row : Nat) : Int) := by
      rw [hmax_row]; simp; omega
    rw [hmul] at h
    exact h
  have hadd_el : Sem.evalPtrAdd zlibPointerConfig prog.tags m
      (.ptr b_tbl (Int64.ofNat (1024 * row))) crcConstTy (idxBv.toNat : Int) =
      some (.ptr b_tbl (Int64.ofNat (1024 * row + 4 * idxBv.toNat))) := by
    have hoff_eq : (Int64.ofNat (1024 * row)).toInt = ((1024 * row : Nat) : Int) :=
      int64_ofNat_toInt (by omega)
    have hlo : 0 ≤ (Int64.ofNat (1024 * row)).toInt + (idxBv.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) := by
      rw [hoff_eq, hmax_el]; omega
    have hhi : (Int64.ofNat (1024 * row)).toInt + (idxBv.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) ≤ (blk.size : Int) := by
      rw [hoff_eq, hmax_el]; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hblk hlo hhi
    have hmul : (Int64.ofNat (1024 * row)).toInt +
        (idxBv.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) =
        ((1024 * row + 4 * idxBv.toNat : Nat) : Int) := by
      rw [hoff_eq, hmax_el]; omega
    rw [hmul] at h
    exact h
  have hread_arr2d : Sem.readPlace prog.tags m [] .rval b_tbl 0
      (.array (.array crcConstTy (some 256)) (some 4)) =
      some (.rval (.ptr b_tbl 0) (CTy.array (CTy.array crcConstTy (some 256)) (some 4)).decay) := by
    simp [Sem.readPlace, CTy.unqual]
  have hread_arr1d : Sem.readPlace prog.tags m [] .rval b_tbl (Int64.ofNat (1024 * row))
      (.array crcConstTy (some 256)) =
      some (.rval (.ptr b_tbl (Int64.ofNat (1024 * row))) (CTy.array crcConstTy (some 256)).decay) := by
    simp [Sem.readPlace, CTy.unqual]
  have hread_el : Sem.readPlace prog.tags m [] .rval b_tbl (Int64.ofNat (1024 * row + 4 * idxBv.toNat))
      crcConstTy = some (.rval (.int .u32 bv) crcConstTy.decay) := by
    unfold Sem.readPlace
    have hu : crcConstTy.unqual = .int .u32 := rfl
    have hnc0 : ModSet.conflicts [] b_tbl (Int64.ofNat (1024 * row + 4 * idxBv.toNat)) 4 = false := rfl
    rw [hu, hsz_el, hnc0]
    simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv]
  have hdec_2d : (CTy.array (.array crcConstTy (some 256)) (some 4)).decay.unqual =
      .ptr (.array crcConstTy (some 256)) := rfl
  have hdec_1d : (CTy.array crcConstTy (some 256)).decay.unqual = .ptr crcConstTy := rfl
  refine ⟨bv, ⟨fun {ext Q fs ctx blks os kcont} hw => ?_⟩⟩
  have hstep1 : Sem.stepExprPure prog zlibPointerConfig env m []
      (.eval .rval (CExpr.var tbl)
        (.indexBaseF .rval (CExpr.lit (row : Int)) ::
          .indexBaseF .rval
            (CExpr.binary .bitAnd
              (CExpr.binary .shr (CExpr.var w).paren
                (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren).paren
              (CExpr.lit 255 .i32 .none .hex)) :: fs)) =
      some (.ret (.rval (.ptr b_tbl 0) (CTy.array (CTy.array crcConstTy (some 256)) (some 4)).decay)
        (.indexBaseF .rval (CExpr.lit (row : Int)) ::
          .indexBaseF .rval
            (CExpr.binary .bitAnd
              (CExpr.binary .shr (CExpr.var w).paren
                (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren).paren
              (CExpr.lit 255 .i32 .none .hex)) :: fs), m, []) := by
    unfold Sem.stepExprPure; simp only [hlu_tbl, hread_arr2d, Option.map_some]
  have hstep2 : Sem.stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (Sem.ofIntCast .i32 (row : Int)) (.int .i32))
        (.indexIdxF .rval (.ptr b_tbl 0)
            (CTy.array (CTy.array crcConstTy (some 256)) (some 4)).decay ::
          .indexBaseF .rval
            (CExpr.binary .bitAnd
              (CExpr.binary .shr (CExpr.var w).paren
                (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren).paren
              (CExpr.lit 255 .i32 .none .hex)) :: fs)) =
      some (.ret (.rval (.ptr b_tbl (Int64.ofNat (1024 * row))) (CTy.array crcConstTy (some 256)).decay)
        (.indexBaseF .rval
          (CExpr.binary .bitAnd
            (CExpr.binary .shr (CExpr.var w).paren
              (CExpr.binary .shl (CExpr.lit (row : Int)).paren (CExpr.lit 3)).paren).paren
            (CExpr.lit 255 .i32 .none .hex)) :: fs), m, []) := by
    unfold Sem.stepExprPure
    simp only [hdec_2d, Sem.valAsInt?, Sem.ofIntCast, IntKind.signed, IntKind.bits,
      ↓reduceIte, hadd_row, hread_arr1d, bind, Option.bind, pure, Pure.pure]
  have hstep3 : Sem.stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (.int .u32 idxBv) (.int .u32))
        (.indexIdxF .rval (.ptr b_tbl (Int64.ofNat (1024 * row))) (CTy.array crcConstTy (some 256)).decay :: fs)) =
      some (.ret (.rval (.int .u32 bv) crcConstTy.decay) fs, m, []) := by
    have hval : Sem.valAsInt? (Val.int .u32 idxBv) = some (.u32, (idxBv.toNat : Int)) := rfl
    unfold Sem.stepExprPure
    simp only [hdec_1d, hval, bind, Option.bind, pure, Pure.pure]
    rw [hadd_el]
    dsimp only
    rw [hread_el]
  exact WPTerm.of_exprPure (by rfl) (WPTerm.of_exprPure (by rfl) (WPTerm.of_exprPure hstep1
    (WPTerm.of_exprPure (by rfl)
      ((pureEval_lit (val := (row : Int)) (k := .i32) (s := .none) (r := .dec)).run
        (WPTerm.of_exprPure hstep2 (WPTerm.of_exprPure (by rfl) (hidx_eval.run
          (WPTerm.of_exprPure hstep3 hw))))))))

private theorem pureEval_crcword {prog env m tbl b_tbl w b_w ty_w} {wbv : BitVec 32}
    (hlu_tbl : env.lookup tbl = some (b_tbl, .array (.array crcConstTy (some 256)) (some 4)))
    (htbl : ∀ r < 4, ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m b_tbl (Int64.ofNat (1024 * r + 4 * idx)) crcConstTy = some (.int .u32 bv))
    (hs_w : IntSlot env m w b_w ty_w .u32 wbv) :
    ∃ bv : BitVec 32,
      PureEval prog zlibPointerConfig env m [] (crcwordExpr tbl w) (.int .u32 bv) (.int .u32) := by
  obtain ⟨b0, hb0⟩ := pureEval_crcb hlu_tbl htbl hs_w (row := 0) (by decide)
  obtain ⟨b1, hb1⟩ := pureEval_crcb hlu_tbl htbl hs_w (row := 1) (by decide)
  obtain ⟨b2, hb2⟩ := pureEval_crcb hlu_tbl htbl hs_w (row := 2) (by decide)
  obtain ⟨b3, hb3⟩ := pureEval_crcb hlu_tbl htbl hs_w (row := 3) (by decide)
  have hu : crcConstTy.decay.unqual = .int .u32 := rfl
  have h01 := pureEval_paren (pureEval_binary_int hb0 hb1 hu hu (evalIntBinary_u32_xor_u32 b0 b1))
  have h23 := pureEval_paren (pureEval_binary_int hb2 hb3 hu hu (evalIntBinary_u32_xor_u32 b2 b3))
  exact ⟨_, pureEval_paren (pureEval_binary_int h01 h23 rfl rfl (evalIntBinary_u32_xor_u32 _ _))⟩

private def crcStepStmt : CStmt :=
  CStmt.expr
    (CExpr.assign .eq (CExpr.var "crc")
      (CExpr.binary .bitXor
        (CExpr.binary .shr (CExpr.var "crc") (CExpr.lit 8)).paren
        ((CExpr.var "crc_table").index
          (CExpr.binary .bitAnd
            (CExpr.binary .bitXor (CExpr.var "crc")
              (CExpr.incDec .postInc (CExpr.var "buf")).deref).paren
            (CExpr.lit 255 .i32 .none .hex)))))

private theorem wp_crc_step_byte {prog ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc b_buf ty_buf el_buf pb poff remBytes b_ct} {vc : BitVec 64}
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hbuf_mem : b_buf ∈ innerBlks ++ outerBlks)
    (hne_cb : b_crc ≠ b_buf)
    (hs_crc : IntSlot env m "crc" b_crc ty_crc .u64 vc)
    (hs_buf : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff))
    (hel_buf : el_buf.unqual = .int .u8)
    (hr : Readable m0 (.ptr pb poff) remBytes) (hrem : 1 ≤ remBytes)
    (hlu_ct : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)))
    (hb_ct_lt : b_ct < m0.nextBlock)
    (htbl_ct : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv))
    (hcont : ∀ vc' m',
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' "crc" b_crc ty_crc .u64 vc' →
      PtrSlot env m' "buf" b_buf ty_buf el_buf (.ptr pb (Int64.ofInt (poff.toInt + 1))) →
      Readable m0 (.ptr pb (Int64.ofInt (poff.toInt + 1))) (remBytes - 1) →
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog zlibPointerConfig ext Q (.running (.stmt crcStepStmt) env innerBlks m os kcont) := by
  have hpb_lt : pb < m0.nextBlock := Readable.block_lt hr
  have hbuf_ge : m0.nextBlock ≤ b_buf := (hf.2.2.2.1 b_buf hbuf_mem).1
  have hne_buf_pb : b_buf ≠ pb := Nat.ne_of_gt (Nat.lt_of_lt_of_le hpb_lt hbuf_ge)
  have hne_buf_ct : b_buf ≠ b_ct := Nat.ne_of_gt (Nat.lt_of_lt_of_le hb_ct_lt hbuf_ge)
  have hne_buf_crc : b_buf ≠ b_crc := hne_cb.symm
  obtain ⟨blk0, byteBv, hm_pb, _, _, hrv_byte⟩ := Readable.read_u8 (tags := prog.tags) hf hr hrem
  obtain ⟨blk', hblk', _, _, hr'⟩ := Readable.advance hr hrem
  have hblk'_eq : blk' = blk0 := by
    have hlt := Readable.block_lt hr
    rcases hr with ⟨_, _, blk00, heq, hblk00, _⟩
    cases heq
    rw [hblk00] at hblk'; cases hblk'
    rw [LocalFrameMem.blocks_eq_of_lt hf hlt, hblk00] at hm_pb; cases hm_pb; rfl
  subst hblk'_eq
  have hsz_el : sizeofTy prog.tags el_buf = 1 := sizeofTy_eq_bytes hel_buf
  have hmax_el : (max (1 : Int) (sizeofTy prog.tags el_buf : Int)) = 1 := by rw [hsz_el]; decide
  rcases hr with ⟨_, _, blk00, heq, hblk00, hin, _⟩
  cases heq
  have hlt_pb' := lt_nextBlock_of_some hblk00
  have hm_pb2 : m.blocks pb = some blk00 := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt_pb', hblk00]
  rw [hm_pb2] at hm_pb; cases hm_pb
  have hin' := inBounds_iff.mp hin
  have h1_i : (BitVec.ofInt 32 1).toInt = 1 := rfl
  have hptr_add : Sem.evalPtrAdd zlibPointerConfig prog.tags m (.ptr pb poff) el_buf (BitVec.ofInt 32 1).toInt =
      some (.ptr pb (Int64.ofInt (poff.toInt + 1))) := by
    rw [h1_i]
    have hlo : 0 ≤ poff.toInt + 1 * (max (1 : Int) (sizeofTy prog.tags el_buf : Int)) := by
      rw [hmax_el]; omega
    have hhi : poff.toInt + 1 * (max (1 : Int) (sizeofTy prog.tags el_buf : Int)) ≤ (blk'.size : Int) := by
      rw [hmax_el]; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hm_pb2 hlo hhi
    rw [hmax_el, Int.one_mul] at h
    exact h
  let poff' := Int64.ofInt (poff.toInt + 1)
  obtain ⟨m1, hm1, hf1, hs_buf1⟩ := hs_buf.write hf hbuf_mem (Or.inr ⟨pb, poff', rfl⟩)
  have hs_crc1 := hs_crc.preserve_ne hm1 hne_cb
  have hsz_buf : sizeofTy prog.tags ty_buf = 8 := sizeofTy_eq_ptr hs_buf.2.1
  have hnc_buf0_8 : ModSet.conflicts [] b_buf 0 8 = false := rfl
  have hrp_byte : Sem.readPlace prog.tags m1 [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩] .rval pb poff el_buf =
      some (.rval (.int .u8 byteBv) el_buf.decay) := by
    unfold Sem.readPlace
    have hrv1 : Sem.readVal prog.tags m1 pb poff el_buf = some (.int .u8 byteBv) := by
      rw [readVal_eq_of_blocks_eq prog.tags (writeVal_blocks_ne hm1 hne_buf_pb.symm),
        readVal_congr_unqual prog.tags (ty2 := (CTy.int .u8).const_) (by rw [hel_buf]; rfl)]
      simpa using hrv_byte
    have hnc_pb : ModSet.conflicts [⟨b_buf, 0, sizeofTy prog.tags ty_buf⟩] pb poff 1 = false :=
      modSet_conflicts_cons_ne hne_buf_pb (modSet_conflicts_nil _ _ _)
    rw [hel_buf, hsz_el, hnc_pb]
    simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv1]
  let xor64 := vc ^^^ byteBv.zeroExtend 64
  let idx64 := xor64 &&& BitVec.ofInt 64 255
  have hidx_lt : idx64.toNat < 256 := by
    dsimp [idx64]
    exact Nat.lt_succ_of_le Nat.and_le_right
  have htbl_ct1 : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m1 b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv) := by
    intro idx hi
    obtain ⟨bv, hrv⟩ := htbl_ct idx hi
    exact ⟨bv, by rw [readVal_eq_of_blocks_eq prog.tags (LocalFrameMem.blocks_eq_of_lt hf1 hb_ct_lt)]; exact hrv⟩
  have hmods1_ct : ∀ off : Int64, ModSet.conflicts [⟨b_buf, 0, 8⟩] b_ct off 4 = false :=
    fun off => modSet_conflicts_cons_ne hne_buf_ct (modSet_conflicts_nil _ _ _)
  have hmods1_crc : ModSet.conflicts [⟨b_buf, 0, 8⟩] b_crc 0 IntKind.u64.bytes = false :=
    modSet_conflicts_cons_ne hne_buf_crc (modSet_conflicts_nil _ _ _)
  have hinc_happ : Sem.applyBinary zlibPointerConfig prog.tags m .add (.ptr pb poff) ty_buf
      (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) = some (.ptr pb poff', ty_buf.unqual) := by
    unfold Sem.applyBinary
    simp only [CTy.isPtr, hs_buf.2.1, Bool.true_or, ↓reduceIte, Sem.valAsInt?, IntKind.signed,
      IntKind.bits]
    rw [hptr_add]
    rfl
  have hstep_postInc : Sem.stepExprPure prog zlibPointerConfig env m []
      (.ret (.lval b_buf 0 ty_buf) [.incDecF .postInc, .derefF .rval,
        .binRhsF .bitXor (.int .u64 vc) ty_crc.decay,
        .binLhsF .bitAnd (.lit 255 .i32 .none .hex),
        .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
        .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
        .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.ptr pb poff) ty_buf) [.derefF .rval,
        .binRhsF .bitXor (.int .u64 vc) ty_crc.decay,
        .binLhsF .bitAnd (.lit 255 .i32 .none .hex),
        .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
        .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
        .assignRhsF .eq b_crc 0 ty_crc], m1, [⟨b_buf, 0, 8⟩]) := by
    unfold Sem.stepExprPure
    simp only [hsz_buf, hnc_buf0_8, Bool.not_false, guard_true, hs_buf.readVal_eq,
      hinc_happ, hm1, bind, Option.bind, pure, Pure.pure]
  have hstep_deref : Sem.stepExprPure prog zlibPointerConfig env m1 [⟨b_buf, 0, 8⟩]
      (.ret (.rval (.ptr pb poff) ty_buf) [.derefF .rval,
        .binRhsF .bitXor (.int .u64 vc) ty_crc.decay,
        .binLhsF .bitAnd (.lit 255 .i32 .none .hex),
        .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
        .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
        .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u8 byteBv) el_buf.decay)
        [.binRhsF .bitXor (.int .u64 vc) ty_crc.decay,
         .binLhsF .bitAnd (.lit 255 .i32 .none .hex),
         .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
         .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc], m1, [⟨b_buf, 0, 8⟩]) := by
    unfold Sem.stepExprPure
    simp only [hs_buf.2.1, hsz_buf ▸ hrp_byte, bind, Option.bind, pure, Pure.pure]
  have hel_dec : el_buf.decay.unqual = .int .u8 := CTy.decay_of_int hel_buf
  have hcrc_dec : ty_crc.decay.unqual = .int .u64 := CTy.decay_of_int hs_crc.2.1
  have hshr_eval : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .shr (.var "crc") (.lit 8)).paren (.int .u64 (vc >>> 8)) (.int .u64) :=
    pureEval_paren (pureEval_binary_int (pureEval_var_int hs_crc (modSet_conflicts_nil _ _ _))
      (pureEval_lit (val := 8) (k := .i32) (s := .none) (r := .dec)) hcrc_dec rfl
      (evalIntBinary_u64_shr_i32 vc (by decide)))
  have hread_arr_ct : Sem.readPlace prog.tags m [] .rval b_ct 0 (.array crcConstTy (some 256)) =
      some (.rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay) := by
    simp [Sem.readPlace, CTy.unqual]
  obtain ⟨tblBv, hrv_tbl⟩ := htbl_ct1 idx64.toNat hidx_lt
  obtain ⟨blk_ct, hblk_ct_eq, hsz_ct⟩ := readVal_crcConst_blk hrv_tbl
  rw [int64_ofNat_toInt (by omega)] at hsz_ct
  have hsz_ct_el : sizeofTy prog.tags crcConstTy = 4 := by
    simp [crcConstTy, sizeofTy, IntKind.bytes, IntKind.bits]
  have hmax_ct : (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) = 4 := by rw [hsz_ct_el]; decide
  have hadd_ct : Sem.evalPtrAdd zlibPointerConfig prog.tags m1 (.ptr b_ct 0) crcConstTy (idx64.toNat : Int) =
      some (.ptr b_ct (Int64.ofNat (4 * idx64.toNat))) := by
    have hlo : 0 ≤ (0 : Int64).toInt + (idx64.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) := by
      rw [hmax_ct]; simp; omega
    have hhi : (0 : Int64).toInt + (idx64.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) ≤ (blk_ct.size : Int) := by
      rw [hmax_ct]; simp; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hblk_ct_eq hlo hhi
    have hmul : (0 : Int64).toInt + (idx64.toNat : Int) * (max (1 : Int) (sizeofTy prog.tags crcConstTy : Int)) =
        ((4 * idx64.toNat : Nat) : Int) := by
      rw [hmax_ct]; simp; omega
    rw [hmul] at h
    exact h
  have hread_ct_el : Sem.readPlace prog.tags m1 [⟨b_buf, 0, 8⟩] .rval b_ct
      (Int64.ofNat (4 * idx64.toNat)) crcConstTy =
      some (.rval (.int .u32 tblBv) crcConstTy.decay) := by
    unfold Sem.readPlace
    have hu : crcConstTy.unqual = .int .u32 := rfl
    rw [hu, hsz_ct_el, hmods1_ct]
    simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv_tbl]
  let vc' := (vc >>> 8) ^^^ tblBv.zeroExtend 64
  obtain ⟨m2, hm2, hf2, hs_crc2⟩ := hs_crc1.write hf1 hcrc_mem vc'
  have hs_buf2 := hs_buf1.preserve_ne hm2 hne_buf_crc
  have hsz_crc : sizeofTy prog.tags ty_crc = 8 := sizeofTy_eq_bytes hs_crc.2.1
  have hnc_crc : ModSet.conflicts [⟨b_buf, 0, 8⟩] b_crc 0 (sizeofTy prog.tags ty_crc) = false := by
    rw [hsz_crc]; exact hmods1_crc
  have hwp_crc : Sem.writePlace prog.tags m1 b_crc 0 ty_crc (.rval (.int .u64 vc') (.int .u64)) =
      some (.rval (.int .u64 vc') ty_crc, m2) :=
    writePlace_int hs_crc.2.1 hm2
  have hdec_ct_arr : (CTy.array crcConstTy (some 256)).decay.unqual = .ptr crcConstTy := rfl
  have hcrc_ct_dec : crcConstTy.decay.unqual = .int .u32 := rfl
  have hstep_ct : Sem.stepExprPure prog zlibPointerConfig env m []
      (.eval .rval (CExpr.var "crc_table")
        [.indexBaseF .rval
            (CExpr.binary .bitAnd
              (CExpr.binary .bitXor (CExpr.var "crc") (CExpr.incDec .postInc (CExpr.var "buf")).deref).paren
              (CExpr.lit 255 .i32 .none .hex)),
          .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
          .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay)
        [.indexBaseF .rval
            (CExpr.binary .bitAnd
              (CExpr.binary .bitXor (CExpr.var "crc") (CExpr.incDec .postInc (CExpr.var "buf")).deref).paren
              (CExpr.lit 255 .i32 .none .hex)),
          .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
          .assignRhsF .eq b_crc 0 ty_crc], m, []) := by
    unfold Sem.stepExprPure; simp only [hlu_ct, hread_arr_ct, Option.map_some]
  have hstep_xor1 : Sem.stepExprPure prog zlibPointerConfig env m1 [⟨b_buf, 0, 8⟩]
      (.ret (.rval (.int .u8 byteBv) el_buf.decay)
        [.binRhsF .bitXor (.int .u64 vc) ty_crc.decay,
         .binLhsF .bitAnd (.lit 255 .i32 .none .hex),
         .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
         .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u64 xor64) (.int .u64))
        [.binLhsF .bitAnd (.lit 255 .i32 .none .hex),
         .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
         .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc], m1, [⟨b_buf, 0, 8⟩]) := by
    unfold Sem.stepExprPure
    simp only [applyBinary_int hcrc_dec hel_dec, evalIntBinary_u64_xor_u8 vc byteBv, Option.map_some]
    rfl
  have hbin_and : Sem.evalIntBinary .bitAnd (.int .u64 xor64) (Sem.ofIntCast .i32 255) =
      some (.int .u64 idx64, .int .u64) :=
    evalIntBinary_u64_and_i32 xor64 (by decide) (by decide)
  have hstep_and : Sem.stepExprPure prog zlibPointerConfig env m1 [⟨b_buf, 0, 8⟩]
      (.ret (.rval (Sem.ofIntCast .i32 255) (.int .i32))
        [.binRhsF .bitAnd (.int .u64 xor64) (.int .u64),
         .indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
         .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u64 idx64) (.int .u64))
        [.indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
         .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc], m1, [⟨b_buf, 0, 8⟩]) := by
    unfold Sem.stepExprPure
    dsimp only
    rw [applyBinary_int (t1 := .int .u64) (t2 := .int .i32) rfl rfl, hbin_and]
    rfl
  have hstep_idx : Sem.stepExprPure prog zlibPointerConfig env m1 [⟨b_buf, 0, 8⟩]
      (.ret (.rval (.int .u64 idx64) (.int .u64))
        [.indexIdxF .rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay,
         .binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u32 tblBv) crcConstTy.decay)
        [.binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc], m1, [⟨b_buf, 0, 8⟩]) := by
    have hval : Sem.valAsInt? (Val.int .u64 idx64) = some (.u64, (idx64.toNat : Int)) := rfl
    unfold Sem.stepExprPure
    simp only [hdec_ct_arr, hval, bind, Option.bind, pure, Pure.pure]
    rw [hadd_ct]
    dsimp only
    rw [hread_ct_el]
  have hstep_xor2 : Sem.stepExprPure prog zlibPointerConfig env m1 [⟨b_buf, 0, 8⟩]
      (.ret (.rval (.int .u32 tblBv) crcConstTy.decay)
        [.binRhsF .bitXor (.int .u64 (vc >>> 8)) (.int .u64),
         .assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u64 vc') (.int .u64))
        [.assignRhsF .eq b_crc 0 ty_crc], m1, [⟨b_buf, 0, 8⟩]) := by
    unfold Sem.stepExprPure
    dsimp only
    rw [applyBinary_int (t1 := .int .u64) (t2 := crcConstTy.decay) rfl hcrc_ct_dec,
      evalIntBinary_u64_xor_u32 (vc >>> 8) tblBv]
    rfl
  have hstep_assign : Sem.stepExprPure prog zlibPointerConfig env m1 [⟨b_buf, 0, 8⟩]
      (.ret (.rval (.int .u64 vc') (.int .u64)) [.assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u64 vc') ty_crc) [], m2, [⟨b_crc, 0, sizeofTy prog.tags ty_crc⟩, ⟨b_buf, 0, 8⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc_crc, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp_crc,
      bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs_crc.1 ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine hshr_eval.run ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure hstep_ct ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine (pureEval_var_int hs_crc (modSet_conflicts_nil _ _ _)).run ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs_buf.1 ?_
  refine WPTerm.of_exprPure hstep_postInc ?_
  refine WPTerm.of_exprPure hstep_deref ?_
  refine WPTerm.of_exprPure hstep_xor1 ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine (pureEval_lit (val := 255) (k := .i32) (s := .none) (r := .hex)).run ?_
  refine WPTerm.of_exprPure hstep_and ?_
  refine WPTerm.of_exprPure hstep_idx ?_
  refine WPTerm.of_exprPure hstep_xor2 ?_
  refine WPTerm.of_exprPure hstep_assign ?_
  refine WPTerm.of_det (by rfl) (hcont vc' m2 hf2 hs_crc2 hs_buf2 hr' ?_)
  intro b' hne1 hne2
  rw [writeVal_blocks_ne hm2 hne1, writeVal_blocks_ne hm1 hne2]

private theorem wp_crc_step_n_bytes {prog ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc b_buf ty_buf el_buf pb poff remBytes b_ct} {vc : BitVec 64}
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hbuf_mem : b_buf ∈ innerBlks ++ outerBlks)
    (hne_cb : b_crc ≠ b_buf)
    (hs_crc : IntSlot env m "crc" b_crc ty_crc .u64 vc)
    (hs_buf : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff))
    (hel_buf : el_buf.unqual = .int .u8)
    (hr : Readable m0 (.ptr pb poff) remBytes)
    (hlu_ct : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)))
    (hb_ct_lt : b_ct < m0.nextBlock)
    (htbl_ct : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv))
    {steps : List CStmt}
    (hsteps : ∀ s ∈ steps, s = crcStepStmt)
    (hrem : steps.length ≤ remBytes)
    (hcont : ∀ vc' poff' m',
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' "crc" b_crc ty_crc .u64 vc' →
      PtrSlot env m' "buf" b_buf ty_buf el_buf (.ptr pb poff') →
      Readable m0 (.ptr pb poff') (remBytes - steps.length) →
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt .nop) env innerBlks m os (.stmts steps kcont)) :=
  match steps with
  | [] =>
    WPTerm.of_det (by rfl) (by
      simpa using hcont vc poff m hf hs_crc hs_buf hr (fun _ _ _ => rfl))
  | hd :: tl => by
    have hhd : hd = crcStepStmt := hsteps hd (by simp)
    subst hhd
    have hrem1 : 1 ≤ remBytes := by simp at hrem; omega
    refine WPTerm.of_det (by rfl) ?_
    refine wp_crc_step_byte hf hcrc_mem hbuf_mem hne_cb hs_crc hs_buf hel_buf hr hrem1
      hlu_ct hb_ct_lt htbl_ct ?_
    intro vc1 m1 hf1 hs_crc1 hs_buf1 hr1 hm1_eq
    refine wp_crc_step_n_bytes (vc := vc1) (poff := Int64.ofInt (poff.toInt + 1))
      (remBytes := remBytes - 1) (m := m1) hf1 hcrc_mem hbuf_mem hne_cb hs_crc1 hs_buf1
      hel_buf hr1 hlu_ct hb_ct_lt htbl_ct (steps := tl)
      (fun s hs => hsteps s (by simp [hs])) (by simp at hrem; omega) ?_
    intro vc' poff' m' hf' hs_crc' hs_buf' hr' hm'_eq
    have hsub : remBytes - 1 - tl.length = remBytes - (crcStepStmt :: tl).length := by
      simp; omega
    refine hcont vc' poff' m' hf' hs_crc' hs_buf' (hsub ▸ hr') ?_
    intro b' h1 h2
    rw [hm'_eq b' h1 h2, hm1_eq b' h1 h2]
termination_by steps.length

private def alignCondExpr : CExpr :=
  (CExpr.var "len").logAnd
    (CExpr.binary .ne
      (CExpr.binary .bitAnd
        (CExpr.cast zSizeTy (CExpr.var "buf"))
        (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
      (CExpr.lit 0))

private def loop1BodyStmt : CStmt :=
  CStmt.block [
    CStmt.expr (CExpr.incDec .postDec (CExpr.var "len")),
    crcStepStmt
  ]

private def loop8BodyStmt : CStmt :=
  CStmt.block [
    CStmt.expr (CExpr.assign .subEq (CExpr.var "len") (CExpr.lit 8)),
    crcStepStmt, crcStepStmt, crcStepStmt, crcStepStmt,
    crcStepStmt, crcStepStmt, crcStepStmt, crcStepStmt
  ]

private theorem wp_while_align {prog ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc b_buf ty_buf el_buf pb poff0 b_len ty_len b_ct minBlks} {vc0 len0 : BitVec 64}
    (hf0 : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hbuf_mem : b_buf ∈ innerBlks ++ outerBlks)
    (hlen_mem : b_len ∈ innerBlks ++ outerBlks)
    (hne_cb : b_crc ≠ b_buf) (hne_cl : b_crc ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hs_crc0 : IntSlot env m "crc" b_crc ty_crc .u64 vc0)
    (hs_buf0 : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff0))
    (hs_len0 : IntSlot env m "len" b_len ty_len .u64 len0)
    (hel_buf : el_buf.unqual = .int .u8)
    (hr0 : Readable m0 (.ptr pb poff0) len0.toNat)
    (hlen_ge : 4 * minBlks + 3 ≤ len0.toNat)
    (hlu_ct : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)))
    (hb_ct_lt : b_ct < m0.nextBlock)
    (htbl_ct : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv))
    (hcont : ∀ vc1 poff1 len1 m1 blk0,
      LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 "crc" b_crc ty_crc .u64 vc1 →
      PtrSlot env m1 "buf" b_buf ty_buf el_buf (.ptr pb poff1) →
      IntSlot env m1 "len" b_len ty_len .u64 len1 →
      m0.blocks pb = some blk0 →
      Mem.isAligned blk0 poff1 4 = true →
      4 * minBlks ≤ len1.toNat →
      Readable m0 (.ptr pb poff1) len1.toNat →
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt alignCondExpr loop1BodyStmt)) env innerBlks m os kcont) := by
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m' os' =>
    env' = env ∧ blks' = innerBlks ∧ os' = os ∧
    ∃ (vc : BitVec 64) (poff : Int64) (len : BitVec 64) (blk0 : Block) (addr : UInt64),
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) ∧
      IntSlot env m' "crc" b_crc ty_crc .u64 vc ∧
      PtrSlot env m' "buf" b_buf ty_buf el_buf (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len ∧
      m0.blocks pb = some blk0 ∧
      m'.addrOf pb poff = some addr ∧
      addr = blk0.baseAddr + UInt64.ofNat poff.toInt.toNat ∧
      Readable m0 (.ptr pb poff) len.toNat ∧
      meas = (if addr.toNat % 4 = 0 then 0 else 4 - addr.toNat % 4) ∧
      4 * minBlks + meas ≤ len.toNat ∧
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m'.blocks b' = m.blocks b')
  obtain ⟨blk0_0, addr0, hblk0_m, haddr0, haddr0_eq, _⟩ := Readable.addrOf hf0 hr0
  have hlt_pb := Readable.block_lt hr0
  have hblk0 : m0.blocks pb = some blk0_0 := by
    rw [LocalFrameMem.blocks_eq_of_lt hf0 hlt_pb] at hblk0_m; exact hblk0_m
  let meas0 := if addr0.toNat % 4 = 0 then 0 else 4 - addr0.toNat % 4
  have hmeas0_le : 4 * minBlks + meas0 ≤ len0.toNat := by dsimp [meas0]; split <;> omega
  refine WPTerm.while_wf Inv (n0 := meas0)
    (by dsimp [Inv]; exact ⟨rfl, rfl, rfl, vc0, poff0, len0, blk0_0, addr0, hf0, hs_crc0, hs_buf0, hs_len0,
      hblk0, haddr0, haddr0_eq, hr0, rfl, hmeas0_le, fun _ _ _ _ => rfl⟩) ?_
  intro meas env' blks' m' os' hinv ih
  rcases hinv with ⟨henv, hblks, hos, vc, poff, len, blk0, addr,
    hf', hs_crc', hs_buf', hs_len', hblk0', haddr', haddr_eq, hr', hmeas_eq, hlen_bound, hm_eq⟩
  subst env'
  subst blks'
  subst os'
  have hlen_eval : PureEval prog zlibPointerConfig env m' [] (.var "len") (.int .u64 len) ty_len.decay :=
    pureEval_var_int hs_len' (modSet_conflicts_nil _ _ _)
  have hlen_truthy : Sem.isTruthy (.int .u64 len) = some (len.toNat != 0) := isTruthy_int_nat (k := .u64) len
  have hz_eval : PureEval prog zlibPointerConfig env m' [] (CExpr.cast zSizeTy (CExpr.var "buf"))
      (.int .u64 (BitVec.ofNat 64 addr.toNat)) zSizeTy :=
    pureEval_cast (pureEval_var_ptr hs_buf' (modSet_conflicts_nil _ _ _))
      (castVal_ptr_addrOf rfl haddr')
  let addrBv : BitVec 64 := BitVec.ofNat 64 addr.toNat
  have hband_eval : PureEval prog zlibPointerConfig env m' []
      (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
        (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
      (.int .u64 (addrBv &&& BitVec.ofInt 64 3)) (.int .u64) :=
    pureEval_paren (pureEval_binary_int hz_eval pureEval_const_3 rfl rfl
      (evalIntBinary_u64_and_i32 addrBv (by decide) (by decide)))
  have hne_eval : PureEval prog zlibPointerConfig env m' []
      (CExpr.binary .ne
        (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
          (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
        (CExpr.lit 0))
      (.int .i32 (if (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 then 1#32 else 0#32)) (.int .i32) := by
    refine pureEval_binary_int hband_eval
      (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) rfl rfl ?_
    exact evalIntBinary_u64_ne_0 (addrBv &&& BitVec.ofInt 64 3)
  have hand_mod : (addrBv &&& BitVec.ofInt 64 3).toNat = addr.toNat % 4 := by
    have h3 : (BitVec.ofInt 64 3).toNat = 3 := rfl
    have ha64 : addrBv.toNat = addr.toNat := by
      dsimp [addrBv]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show addr.toNat < 2 ^ 64 from addr.toBitVec.isLt)]
    rw [BitVec.toNat_and, h3, ha64]
    change addr.toNat &&& (2 ^ 2 - 1) = addr.toNat % 2 ^ 2
    exact Nat.and_two_pow_sub_one_eq_mod addr.toNat 2
  by_cases hmod0 : addr.toNat % 4 = 0
  · have hband0 : addrBv.toNat &&& 3 = 0 := by
      have h : (addrBv &&& BitVec.ofInt 64 3).toNat = 0 := by rw [hand_mod, hmod0]
      exact h
    have hmeas0_eq : meas = 0 := by rw [hmeas_eq]; simp [hmod0]
    have hlen_min : 4 * minBlks ≤ len.toNat := by omega
    have hm'_pb : m'.blocks pb = some blk0 := by
      rw [LocalFrameMem.blocks_eq_of_lt hf' (Readable.block_lt hr'), hblk0']
    have hbounds : 0 ≤ poff.toInt ∧ poff.toInt ≤ (blk0.size : Int) := by
      rcases hr' with ⟨_, _, blk00, heq, hblk00, hin, _⟩
      cases heq; rw [hblk0'] at hblk00; cases hblk00
      exact inBounds_iff.mp hin |>.imp (fun h => h) (fun h => by omega)
    have hand3_0 : (addr.toNat &&& 3) = 0 := by
      change addr.toNat &&& (2 ^ 2 - 1) = 0
      rw [Nat.and_two_pow_sub_one_eq_mod, hmod0]
    have hal4 : Mem.isAligned blk0 poff 4 = true :=
      isAligned_4_of_addr_and_3 hm'_pb hbounds.1 hbounds.2 haddr' hand3_0
    have htr0 : Sem.isTruthy (.int .i32 (if (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 then 1#32 else 0#32)) =
        some false := by
      rw [isTruthy_int_nat (k := .i32)]
      refine congrArg some ?_
      have h0z : (addrBv &&& BitVec.ofInt 64 3).toNat = 0 := hband0
      simp only [h0z, ne_eq, not_true_eq_false, ↓reduceIte]
      decide
    have hcond_eval : PureEval prog zlibPointerConfig env m' [] alignCondExpr
        (.int .i32 0#32) (.int .i32) := by
      cases hlen0_b : (len.toNat != 0)
      · refine ⟨fun {ext Q fs ctx blks os kcont} hw => ?_⟩
        have hstep_log : Sem.stepExprPure prog zlibPointerConfig env m' []
            (.ret (.rval (.int .u64 len) ty_len.decay)
              (.logAndF (CExpr.binary .ne
                (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
                  (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
                (CExpr.lit 0)) :: fs)) =
            some (.ret (.rval (.int .i32 0) (.int .i32)) fs, m', []) := by
          unfold Sem.stepExprPure
          simp only [hlen_truthy, hlen0_b, Bool.not_false, ↓reduceIte, bind, Option.bind, pure, Pure.pure]
        exact WPTerm.of_exprPure (by rfl) (hlen_eval.run (WPTerm.of_exprPure hstep_log hw))
      · refine ⟨fun {ext Q fs ctx blks os kcont} hw => ?_⟩
        have hstep_log1 : Sem.stepExprPure prog zlibPointerConfig env m' []
            (.ret (.rval (.int .u64 len) ty_len.decay)
              (.logAndF (CExpr.binary .ne
                (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
                  (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
                (CExpr.lit 0)) :: fs)) =
            some (.eval .rval (CExpr.binary .ne
              (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
                (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
              (CExpr.lit 0)) (.logAndEndF :: fs), m', []) := by
          unfold Sem.stepExprPure
          simp only [hlen_truthy, hlen0_b, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            bind, Option.bind, pure, Pure.pure]
        have hret0 : Sem.stepExprPure prog zlibPointerConfig env m' []
            (.ret (.rval (.int .i32 (if (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 then 1#32 else 0#32))
              (.int .i32)) (.logAndEndF :: fs)) =
            some (.ret (.rval (.int .i32 0#32) (.int .i32)) fs, m', []) := by
          unfold Sem.stepExprPure
          simp only [htr0, bind, Option.bind, pure, Pure.pure]
          rfl
        exact WPTerm.of_exprPure (by rfl)
          (hlen_eval.run (WPTerm.of_exprPure hstep_log1 (hne_eval.run (WPTerm.of_exprPure hret0 hw))))
    refine wp_forCond_false hcond_eval (isTruthy_int_nat (k := .i32) 0#32) ?_
    exact hcont vc poff len m' blk0 hf' hs_crc' hs_buf' hs_len' hblk0' hal4 hlen_min hr' hm_eq
  · have hmeas_pos : 1 ≤ meas := by rw [hmeas_eq]; simp [hmod0]; omega
    have hlen_pos : 1 ≤ len.toNat := by omega
    have hlen_nz : (len.toNat != 0) = true := bne_iff_ne.mpr (by omega)
    have hband_nz : addrBv.toNat &&& 3 ≠ 0 := by
      have h : (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 := by rw [hand_mod]; exact hmod0
      exact h
    have htr1 : Sem.isTruthy (.int .i32 (if (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 then 1#32 else 0#32)) =
        some true := by
      rw [isTruthy_int_nat (k := .i32)]
      refine congrArg some ?_
      have h1z : (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 := hband_nz
      simp only [h1z, ne_eq, not_false_eq_true, ↓reduceIte]
      decide
    have hcond_eval : PureEval prog zlibPointerConfig env m' [] alignCondExpr
        (.int .i32 1#32) (.int .i32) := by
      refine ⟨fun {ext Q fs ctx blks os kcont} hw => ?_⟩
      have hstep_log1 : Sem.stepExprPure prog zlibPointerConfig env m' []
          (.ret (.rval (.int .u64 len) ty_len.decay)
            (.logAndF (CExpr.binary .ne
              (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
                (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
              (CExpr.lit 0)) :: fs)) =
          some (.eval .rval (CExpr.binary .ne
            (CExpr.binary .bitAnd (CExpr.cast zSizeTy (CExpr.var "buf"))
              (CExpr.binary .sub (CExpr.lit 4) (CExpr.lit 1)).paren).paren
            (CExpr.lit 0)) (.logAndEndF :: fs), m', []) := by
        unfold Sem.stepExprPure
        simp only [hlen_truthy, hlen_nz, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          bind, Option.bind, pure, Pure.pure]
      have hret1 : Sem.stepExprPure prog zlibPointerConfig env m' []
          (.ret (.rval (.int .i32 (if (addrBv &&& BitVec.ofInt 64 3).toNat ≠ 0 then 1#32 else 0#32))
            (.int .i32)) (.logAndEndF :: fs)) =
          some (.ret (.rval (.int .i32 1#32) (.int .i32)) fs, m', []) := by
        unfold Sem.stepExprPure
        simp only [htr1, bind, Option.bind, pure, Pure.pure]
        rfl
      exact WPTerm.of_exprPure (by rfl)
        (hlen_eval.run (WPTerm.of_exprPure hstep_log1 (hne_eval.run (WPTerm.of_exprPure hret1 hw))))
    refine wp_forCond_true hcond_eval (isTruthy_int_nat (k := .i32) 1#32) ?_
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_postDec_u64 hs_len' hlen_mem hf' ?_
    intro m1 hm1 hf1 hs_len1
    have hlen1_nat : (len - 1#64).toNat = len.toNat - 1 := by
      rw [BitVec.toNat_sub]
      have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
      have hlt64 := len.isLt
      rw [h1n]; omega
    have hs_crc1 := hs_crc'.preserve_ne hm1 hne_cl
    have hs_buf1 := hs_buf'.preserve_ne hm1 hne_bl
    refine WPTerm.of_det (by rfl) ?_
    refine wp_crc_step_byte hf1 hcrc_mem hbuf_mem hne_cb hs_crc1 hs_buf1 hel_buf
      hr' hlen_pos hlu_ct hb_ct_lt htbl_ct ?_
    intro vc2 m2 hf2 hs_crc2 hs_buf2 hr2 hm2_eq
    have hs_len2 := intSlot_preserve_blocks hs_len1 (hm2_eq b_len hne_cl.symm hne_bl.symm)
    refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_))
    rw [freeStack_nil]
    let poff2 := Int64.ofInt (poff.toInt + 1)
    obtain ⟨blk2, addr2, hm2_pb, haddr2, haddr2_eq, _⟩ := Readable.addrOf hf2 hr2
    have hm'_pb : m'.blocks pb = some blk0 := by
      rw [LocalFrameMem.blocks_eq_of_lt hf' (Readable.block_lt hr'), hblk0']
    have hblk2_eq : blk2 = blk0 := by
      rw [LocalFrameMem.blocks_eq_of_lt hf2 (Readable.block_lt hr2), hblk0'] at hm2_pb
      cases hm2_pb; rfl
    have haddr2_eq' : addr2 = blk0.baseAddr + UInt64.ofNat poff2.toInt.toNat := by
      rw [← hblk2_eq]; exact haddr2_eq
    have hmod_succ : addr2.toNat % 4 = (addr.toNat + 1) % 4 := by
      have h1 := Readable.addrOf_succ_mod4 hf' hr' hlen_pos hm'_pb haddr_eq
      dsimp only at h1
      rw [haddr2_eq']
      exact h1
    let meas' := if addr2.toNat % 4 = 0 then 0 else 4 - addr2.toNat % 4
    have hmod_add : (addr.toNat + 1) % 4 = (addr.toNat % 4 + 1) % 4 := by
      rw [Nat.add_mod]
    have hcases : addr.toNat % 4 = 1 ∨ addr.toNat % 4 = 2 ∨ addr.toNat % 4 = 3 := by omega
    have hmeas_lt : meas' < meas ∧ 4 * minBlks + meas' ≤ (len - 1#64).toNat := by
      rw [hlen1_nat]
      have hm' : meas' = if (addr.toNat % 4 + 1) % 4 = 0 then 0 else 4 - (addr.toNat % 4 + 1) % 4 := by
        dsimp [meas']; rw [hmod_succ, hmod_add]
      rw [hm', hmeas_eq]
      rcases hcases with h | h | h <;> (rw [h] at hmeas_eq; simp [h] at hmeas_eq ⊢; omega)
    have hm_inv : ∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m2.blocks b' = m.blocks b' := by
      intro b' hb1 hb2 hb3
      rw [hm2_eq b' hb1 hb2, writeVal_blocks_ne hm1 hb3, hm_eq b' hb1 hb2 hb3]
    exact ih meas' env innerBlks m2 os hmeas_lt.1
      ⟨rfl, rfl, rfl, vc2, poff2, len - 1#64, blk0, addr2, hf2, hs_crc2, hs_buf2, hs_len2,
        hblk0', haddr2, haddr2_eq', hlen1_nat ▸ hr2, rfl, hmeas_lt.2, hm_inv⟩

private theorem wp_while_len_ge_8 {prog ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc b_buf ty_buf el_buf pb poff0 b_len ty_len b_ct} {vc0 len0 : BitVec 64}
    (hf0 : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hbuf_mem : b_buf ∈ innerBlks ++ outerBlks)
    (hlen_mem : b_len ∈ innerBlks ++ outerBlks)
    (hne_cb : b_crc ≠ b_buf) (hne_cl : b_crc ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hs_crc0 : IntSlot env m "crc" b_crc ty_crc .u64 vc0)
    (hs_buf0 : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff0))
    (hs_len0 : IntSlot env m "len" b_len ty_len .u64 len0)
    (hel_buf : el_buf.unqual = .int .u8)
    (hr0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb poff0) len0.toNat)
    (hlu_ct : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)))
    (hb_ct_lt : b_ct < m0.nextBlock)
    (htbl_ct : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv))
    (hcont : ∀ vc1 poff1 len1 m1,
      LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 "crc" b_crc ty_crc .u64 vc1 →
      PtrSlot env m1 "buf" b_buf ty_buf el_buf (.ptr pb poff1) →
      IntSlot env m1 "len" b_len ty_len .u64 len1 →
      len1.toNat < 8 →
      (len1.toNat = 0 ∨ Readable m0 (.ptr pb poff1) len1.toNat) →
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt (CExpr.binary .ge (CExpr.var "len") (CExpr.lit 8)) loop8BodyStmt))
        env innerBlks m os kcont) := by
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m' os' =>
    env' = env ∧ blks' = innerBlks ∧ os' = os ∧
    ∃ (vc : BitVec 64) (poff : Int64) (len : BitVec 64),
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) ∧
      IntSlot env m' "crc" b_crc ty_crc .u64 vc ∧
      PtrSlot env m' "buf" b_buf ty_buf el_buf (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len ∧
      meas = len.toNat ∧
      (len.toNat = 0 ∨ Readable m0 (.ptr pb poff) len.toNat) ∧
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m'.blocks b' = m.blocks b')
  refine WPTerm.while_wf Inv (n0 := len0.toNat)
    (by dsimp [Inv]; exact ⟨rfl, rfl, rfl, vc0, poff0, len0, hf0, hs_crc0, hs_buf0, hs_len0, rfl, hr0, fun _ _ _ _ => rfl⟩) ?_
  intro meas env' blks' m' os' hinv ih
  rcases hinv with ⟨henv, hblks, hos, vc, poff, len, hf', hs_crc', hs_buf', hs_len',
    hmeas_eq, hr', hm_eq⟩
  subst env'
  subst blks'
  subst os'
  have hcond_eval : PureEval prog zlibPointerConfig env m' []
      (CExpr.binary .ge (CExpr.var "len") (CExpr.lit 8))
      (.int .i32 (if 8 ≤ len.toNat then 1#32 else 0#32)) (.int .i32) :=
    pureEval_binary_int (pureEval_var_int hs_len' (modSet_conflicts_nil _ _ _))
      (pureEval_lit (val := 8) (k := .i32) (s := .none) (r := .dec))
      (CTy.decay_of_int hs_len'.2.1) rfl
      (evalIntBinary_u64_ge_i32 len (by decide) (by decide))
  by_cases hge : 8 ≤ len.toNat
  · have hr_pos : Readable m0 (.ptr pb poff) len.toNat := by
      rcases hr' with h0 | hr
      · omega
      · exact hr
    refine wp_forCond_true hcond_eval (by rw [isTruthy_int_nat (k := .i32)]; simp [hge]) ?_
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_assignOp_int (op := .subEq) (bop := .sub) rfl hs_len' hlen_mem hf'
      (pureEval_lit (val := 8) (k := .i32) (s := .none) (r := .dec)) rfl
      (evalIntBinary_u64_sub_i32 len (by decide) (by decide)) ?_
    intro m1 hm1 hf1 hs_len1
    have hlen1_eq : BitVec.ofInt 64 ((len - BitVec.ofInt 64 8).toNat : Int) = len - BitVec.ofInt 64 8 :=
      bitVec_ofInt_toNat 64 _
    have hs_len1' : IntSlot env m1 "len" b_len ty_len .u64 (len - BitVec.ofInt 64 8) := by
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hlen1_eq] at hs_len1
      exact hs_len1
    have hlen1_nat : (len - BitVec.ofInt 64 8).toNat = len.toNat - 8 := by
      rw [BitVec.toNat_sub]
      have h8 : (BitVec.ofInt 64 8).toNat = 8 := rfl
      have hlt64 := len.isLt
      rw [h8]; omega
    have hs_crc1 := hs_crc'.preserve_ne hm1 hne_cl
    have hs_buf1 := hs_buf'.preserve_ne hm1 hne_bl
    refine wp_crc_step_n_bytes hf1 hcrc_mem hbuf_mem hne_cb hs_crc1 hs_buf1 hel_buf hr_pos
      hlu_ct hb_ct_lt htbl_ct (steps := [crcStepStmt, crcStepStmt, crcStepStmt, crcStepStmt,
        crcStepStmt, crcStepStmt, crcStepStmt, crcStepStmt])
      (fun s hs => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      (by simp; exact hge) ?_
    intro vc2 poff2 m2 hf2 hs_crc2 hs_buf2 hr2 hm2_eq
    have hs_len2 := intSlot_preserve_blocks hs_len1' (hm2_eq b_len hne_cl.symm hne_bl.symm)
    refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
    rw [freeStack_nil]
    have hr2_8 : Readable m0 (.ptr pb poff2) (len.toNat - 8) := hr2
    have hr2' : (len - BitVec.ofInt 64 8).toNat = 0 ∨
        Readable m0 (.ptr pb poff2) (len - BitVec.ofInt 64 8).toNat := by
      right
      exact hlen1_nat ▸ hr2_8
    have hmeas_eq' : len.toNat - 8 = (len - BitVec.ofInt 64 8).toNat := hlen1_nat.symm
    have hm_inv : ∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m2.blocks b' = m.blocks b' := by
      intro b' hb1 hb2 hb3
      rw [hm2_eq b' hb1 hb2, writeVal_blocks_ne hm1 hb3, hm_eq b' hb1 hb2 hb3]
    exact ih (len.toNat - 8) env innerBlks m2 os (by rw [hmeas_eq]; omega)
      ⟨rfl, rfl, rfl, vc2, poff2, len - BitVec.ofInt 64 8, hf2, hs_crc2, hs_buf2, hs_len2,
        hmeas_eq', hr2', hm_inv⟩
  · refine wp_forCond_false hcond_eval (by rw [isTruthy_int_nat (k := .i32)]; simp [hge]) ?_
    exact hcont vc poff len m' hf' hs_crc' hs_buf' hs_len' (Nat.lt_of_not_ge hge) hr' hm_eq

private theorem wp_while_len_tail {prog ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc b_buf ty_buf el_buf pb poff0 b_len ty_len b_ct} {vc0 len0 : BitVec 64}
    (hf0 : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hbuf_mem : b_buf ∈ innerBlks ++ outerBlks)
    (hlen_mem : b_len ∈ innerBlks ++ outerBlks)
    (hne_cb : b_crc ≠ b_buf) (hne_cl : b_crc ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hs_crc0 : IntSlot env m "crc" b_crc ty_crc .u64 vc0)
    (hs_buf0 : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff0))
    (hs_len0 : IntSlot env m "len" b_len ty_len .u64 len0)
    (hel_buf : el_buf.unqual = .int .u8)
    (hr0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb poff0) len0.toNat)
    (hlu_ct : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)))
    (hb_ct_lt : b_ct < m0.nextBlock)
    (htbl_ct : ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m0 b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv))
    (hcont : ∀ vc1 poff1 len1 m1,
      LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 "crc" b_crc ty_crc .u64 vc1 →
      PtrSlot env m1 "buf" b_buf ty_buf el_buf (.ptr pb poff1) →
      IntSlot env m1 "len" b_len ty_len .u64 len1 →
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt (CExpr.var "len") loop1BodyStmt)) env innerBlks m os kcont) := by
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m' os' =>
    env' = env ∧ blks' = innerBlks ∧ os' = os ∧
    ∃ (vc : BitVec 64) (poff : Int64) (len : BitVec 64),
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) ∧
      IntSlot env m' "crc" b_crc ty_crc .u64 vc ∧
      PtrSlot env m' "buf" b_buf ty_buf el_buf (.ptr pb poff) ∧
      IntSlot env m' "len" b_len ty_len .u64 len ∧
      meas = len.toNat ∧
      (len.toNat = 0 ∨ Readable m0 (.ptr pb poff) len.toNat) ∧
      (∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m'.blocks b' = m.blocks b')
  refine WPTerm.while_wf Inv (n0 := len0.toNat)
    (by dsimp [Inv]; exact ⟨rfl, rfl, rfl, vc0, poff0, len0, hf0, hs_crc0, hs_buf0, hs_len0, rfl, hr0, fun _ _ _ _ => rfl⟩) ?_
  intro meas env' blks' m' os' hinv ih
  rcases hinv with ⟨henv, hblks, hos, vc, poff, len, hf', hs_crc', hs_buf', hs_len',
    hmeas_eq, hr', hm_eq⟩
  subst env'
  subst blks'
  subst os'
  have hcond_eval : PureEval prog zlibPointerConfig env m' [] (CExpr.var "len") (.int .u64 len) ty_len.decay :=
    pureEval_var_int hs_len' (modSet_conflicts_nil _ _ _)
  by_cases h0 : len.toNat = 0
  · refine wp_forCond_false hcond_eval
      (by
        have htr := isTruthy_int_nat (k := .u64) len
        rw [htr]
        change some (len.toNat != 0) = some false
        simp [h0]) ?_
    exact hcont vc poff len m' hf' hs_crc' hs_buf' hs_len' hm_eq
  · have hpos : 1 ≤ len.toNat := by omega
    have hr_pos : Readable m0 (.ptr pb poff) len.toNat := by
      rcases hr' with h0' | hr
      · exact absurd h0' h0
      · exact hr
    have hnz : (len.toNat != 0) = true := bne_iff_ne.mpr h0
    refine wp_forCond_true hcond_eval
      (by
        have htr := isTruthy_int_nat (k := .u64) len
        rw [htr]
        change some (len.toNat != 0) = some true
        simp [hnz]) ?_
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_postDec_u64 hs_len' hlen_mem hf' ?_
    intro m1 hm1 hf1 hs_len1
    have hlen1_nat : (len - 1#64).toNat = len.toNat - 1 := by
      rw [BitVec.toNat_sub]
      have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
      have hlt64 := len.isLt
      rw [h1n]; omega
    have hs_crc1 := hs_crc'.preserve_ne hm1 hne_cl
    have hs_buf1 := hs_buf'.preserve_ne hm1 hne_bl
    refine WPTerm.of_det (by rfl) ?_
    refine wp_crc_step_byte hf1 hcrc_mem hbuf_mem hne_cb hs_crc1 hs_buf1 hel_buf
      hr_pos hpos hlu_ct hb_ct_lt htbl_ct ?_
    intro vc2 m2 hf2 hs_crc2 hs_buf2 hr2 hm2_eq
    have hs_len2 := intSlot_preserve_blocks hs_len1 (hm2_eq b_len hne_cl.symm hne_bl.symm)
    refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_))
    rw [freeStack_nil]
    have hr2' : (len - 1#64).toNat = 0 ∨
        Readable m0 (.ptr pb (Int64.ofInt (poff.toInt + 1))) (len - 1#64).toNat := by
      right; exact hlen1_nat ▸ hr2
    have hmeas_eq' : len.toNat - 1 = (len - 1#64).toNat := hlen1_nat.symm
    have hm_inv : ∀ b', b' ≠ b_crc → b' ≠ b_buf → b' ≠ b_len → m2.blocks b' = m.blocks b' := by
      intro b' hb1 hb2 hb3
      rw [hm2_eq b' hb1 hb2, writeVal_blocks_ne hm1 hb3, hm_eq b' hb1 hb2 hb3]
    exact ih (len.toNat - 1) env innerBlks m2 os (by rw [hmeas_eq]; omega)
      ⟨rfl, rfl, rfl, vc2, Int64.ofInt (poff.toInt + 1), len - 1#64, hf2, hs_crc2, hs_buf2, hs_len2,
        hmeas_eq', hr2', hm_inv⟩

/-! ## 4. `get_crc_table` and `crc_word` -/

theorem get_crc_table_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (ext : ExtHandler) (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_get_crc_table
      (fun m args => args = [] ∧ CrcTableValid prog gEnv m)
      (fun _ _ ret _ => ∃ b, ret = .ptr b 0) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q ⟨hargs, b_ct, hlu_ct, _, _⟩ _ hpush hcont
  subst hargs
  simp only [Zlib.Crc32.crc32TU_fn_get_crc_table, List.zip_nil_right, Sem.pushCallParams,
    Option.some.injEq, Prod.mk.injEq] at hpush
  rcases hpush with ⟨rfl, rfl, rfl⟩
  have hf1 : LocalFrameMem m m [] := LocalFrameMem.init m
  have hlu_env : (prog.fnStatics "get_crc_table" ++ prog.globalEnv).lookup "crc_table" =
      some (b_ct, .array crcConstTy (some 256)) := by
    rw [prog_fnStatics_get_crc_table hlib, List.nil_append, hlib.globalEnv_eq]
    exact hlu_ct
  have hread_arr : Sem.readPlace prog.tags m [] .rval b_ct 0 (.array crcConstTy (some 256)) =
      some (.rval (.ptr b_ct 0) (CTy.array crcConstTy (some 256)).decay) := by
    simp [Sem.readPlace, CTy.unqual]
  have he_ret : PureEval prog zlibPointerConfig
      (prog.fnStatics "get_crc_table" ++ prog.globalEnv) m []
      (.cast zCrcTy.const_.ptr (.var "crc_table")) (.ptr b_ct 0) zCrcTy.const_.ptr := by
    refine pureEval_cast (ty := (CTy.array crcConstTy (some 256)).decay) ⟨fun hw' => ?_⟩
      (castVal_ptr_eq rfl (Or.inr ⟨b_ct, 0, rfl⟩))
    refine WPTerm.of_exprPure ?_ hw'
    unfold Sem.stepExprPure
    simp only [hlu_env, hread_arr, Option.map_some]
  refine WPTerm.of_det (by rfl) ?_
  change WPTerm prog zlibPointerConfig ext Q
    (.running (.stmt (.returnStmt (some (.cast zCrcTy.const_.ptr (.var "crc_table")))))
      (prog.fnStatics "get_crc_table" ++ prog.globalEnv) [] m os
      (.blockEnd (prog.fnStatics "get_crc_table" ++ prog.globalEnv) []
        (.callFrame env blks Zlib.Crc32.crc32TU_fn_get_crc_table.retTy
          Zlib.Crc32.crc32TU_fn_get_crc_table.body fs ctx k)))
  refine wp_return_pure (innerBlks := []) (callBlks := [])
    (env := env) (blks := blks) (fs := fs) (ctx := ctx) (k := k)
    (k_ret := .blockEnd (prog.fnStatics "get_crc_table" ++ prog.globalEnv) []
      (.callFrame env blks Zlib.Crc32.crc32TU_fn_get_crc_table.retTy
        Zlib.Crc32.crc32TU_fn_get_crc_table.body fs ctx k))
    (fnRetTy := Zlib.Crc32.crc32TU_fn_get_crc_table.retTy)
    (by simp [Sem.unwindReturn, freeStack_nil]) rfl (by decide) hf1 he_ret
    (castVal_ptr_eq (el := zCrcTy.const_) (by simp [Zlib.Crc32.crc32TU_fn_get_crc_table, CTy.unqual]) (Or.inr ⟨b_ct, 0, rfl⟩)) ?_
  intro ret m' hro hret _
  exact hcont ret m' hro ⟨b_ct, hret⟩

theorem crc_word_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (ext : ExtHandler) (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc_word
      (fun m args => (∃ w : BitVec 32, args = [.int .u32 w]) ∧ CrcTableValid prog gEnv m)
      (fun _ _ ret _ => ∃ w' : BitVec 32, ret = .int .u32 w') := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨⟨w, hargs⟩, b_ct, hlu_ct, hb_ct_lt, htbl_ct⟩ _ hpush hcont
  subst hargs
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hsz0, hal0, hba0, m2_p, hwr0, hpush_nil⟩ := pushCallParams_cons_inv hpush
  unfold Sem.pushCallParams at hpush_nil
  cases hpush_nil
  let env0 := prog.fnStatics "crc_word" ++ prog.globalEnv
  let b_data := m.nextBlock
  let env_params : Env := ("data", b_data, zWordTy) :: env0
  have hs_data0 : IntSlot env_params m1 "data" b_data zWordTy .u32 w :=
    IntSlot.of_pushCallParam (k := .u32) rfl rfl hwr0 env0
  have hbody_eq : Zlib.Crc32.crc32TU_fn_crc_word.body =
      CStmt.block [
        CStmt.decl { name := "k", ty := CTy.int .i32 },
        CStmt.forStmt (some (CExpr.assign .eq (CExpr.var "k") (CExpr.lit 0)))
          (some (CExpr.binary .lt (CExpr.var "k") (CExpr.lit 4)))
          (some (CExpr.incDec .postInc (CExpr.var "k")))
          (CStmt.expr
            (CExpr.assign .eq (CExpr.var "data")
              (CExpr.binary .bitXor
                (CExpr.binary .shr (CExpr.var "data") (CExpr.lit 8)).paren
                ((CExpr.var "crc_table").index
                  (CExpr.binary .bitAnd (CExpr.var "data")
                    (CExpr.lit 255 .i32 .none .hex)))))),
        CStmt.returnStmt (some (CExpr.cast zCrcTy (CExpr.var "data")))
      ] := rfl
  rw [hbody_eq]
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  refine wp_localDecl_int_none (ik := .i32) (innerBlks := []) (outerBlks := [b_data])
    rfl rfl rfl rfl hf1 ?_
  intro b_k m2 hb_k_eq hf2 hu_k hi_2 _ _ _
  have hs_data2 := hi_2 (by decide) hs_data0
  let loopEnv : Env := ("k", b_k, CTy.int .i32) :: env_params
  have hlu_ct_loop : loopEnv.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)) := by
    dsimp [loopEnv, env_params, env0]
    rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
      prog_fnStatics_crc_word hlib, List.nil_append, hlib.globalEnv_eq]
    exact hlu_ct
  have hne_kd : b_k ≠ b_data :=
    nodup_getElem_ne hf2.2.2.1 (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have hbk_lt_ct : b_ct < m.nextBlock := hb_ct_lt
  have hdata_mem : b_data ∈ [b_k, b_data] := by simp
  have hk_mem : b_k ∈ [b_k, b_data] := by simp
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  let loopBody : CStmt :=
    CStmt.expr
      (CExpr.assign .eq (CExpr.var "data")
        (CExpr.binary .bitXor
          (CExpr.binary .shr (CExpr.var "data") (CExpr.lit 8)).paren
          ((CExpr.var "crc_table").index
            (CExpr.binary .bitAnd (CExpr.var "data")
              (CExpr.lit 255 .i32 .none .hex)))))
  let retStmt : CStmt := CStmt.returnStmt (some (CExpr.cast zCrcTy (CExpr.var "data")))
  let loopCont : Sem.Cont := .stmts [retStmt]
    (.blockEnd env_params [b_data]
      (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc_word.retTy
        Zlib.Crc32.crc32TU_fn_crc_word.body fs ctx k))
  let Inv : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m' os' =>
    env' = loopEnv ∧ blks' = [b_k] ∧ os' = os ∧
    ∃ (kv dv : BitVec 32),
      LocalFrameMem m m' [b_k, b_data] ∧
      IntSlot loopEnv m' "k" b_k (.int .i32) .i32 kv ∧
      IntSlot loopEnv m' "data" b_data zWordTy .u32 dv ∧
      0 ≤ kv.toInt ∧ kv.toInt ≤ 4 ∧
      meas = (4 - kv.toInt).toNat
  refine WPTerm.for_wf Inv (n0 := 4)
    (init? := some (CExpr.assign .eq (CExpr.var "k") (CExpr.lit 0)))
    (c? := some (CExpr.binary .lt (CExpr.var "k") (CExpr.lit 4)))
    (stp? := some (CExpr.incDec .postInc (CExpr.var "k")))
    (body := loopBody) ?_ ?_
  · intro hloop_enter
    obtain ⟨m3, hm3, hf3, hs_k3⟩ := hu_k.write hf2 hk_mem 0#32
    have hs_data3 := hs_data2.preserve_ne hm3 hne_kd.symm
    have hnc0 : ModSet.conflicts [] b_k 0 (sizeofTy prog.tags (.int .i32)) = false := rfl
    have hwp : Sem.writePlace prog.tags m2 b_k 0 (.int .i32)
        (.rval (Sem.ofIntCast .i32 0) (.int .i32)) =
        some (.rval (.int .i32 0#32) (.int .i32), m3) :=
      writePlace_int rfl hm3
    have hstep_init : Sem.stepExprPure prog zlibPointerConfig loopEnv m2 []
        (.ret (.rval (Sem.ofIntCast .i32 0) (.int .i32)) [.assignRhsF .eq b_k 0 (.int .i32)]) =
        some (.ret (.rval (.int .i32 0#32) (.int .i32)) [], m3,
          [⟨b_k, 0, sizeofTy prog.tags (.int .i32)⟩]) := by
      unfold Sem.stepExprPure
      simp only [hnc0, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp,
        bind, Option.bind, pure, Pure.pure]
    refine WPTerm.of_exprPure (by rfl) ?_
    refine wp_lval_var hu_k.1 ?_
    refine WPTerm.of_exprPure (by rfl) ?_
    refine (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)).run ?_
    refine WPTerm.of_exprPure hstep_init ?_
    refine WPTerm.of_det (by rfl) ?_
    exact hloop_enter loopEnv [b_k] m3 os (by dsimp [Inv]; exact ⟨rfl, rfl, rfl, 0#32, w, hf3, hs_k3, hs_data3,
      by decide, by decide, rfl⟩)
  · intro meas env' blks' m' os' hinv ih
    rcases hinv with ⟨henv, hblks, hos, kv, dv, hf', hs_k', hs_data', hk0, hk4, hmeas⟩
    subst env'
    subst blks'
    subst os'
    dsimp [forLoopEntry]
    have hcond : PureEval prog zlibPointerConfig loopEnv m' []
        (CExpr.binary .lt (CExpr.var "k") (CExpr.lit 4))
        (.int .i32 (if kv.toInt < 4 then 1#32 else 0#32)) (.int .i32) :=
      pureEval_binary_int (pureEval_var_int hs_k' (modSet_conflicts_nil _ _ _))
        (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec))
        rfl rfl (evalIntBinary_i32_lt_4 kv)
    by_cases hklt : kv.toInt < 4
    · refine wp_forCond_true hcond (by rw [isTruthy_int_nat (k := .i32)]; simp [hklt]) ?_
      have hshr_eval : PureEval prog zlibPointerConfig loopEnv m' []
          (CExpr.binary .shr (CExpr.var "data") (CExpr.lit 8)).paren
          (.int .u32 (dv >>> 8)) (.int .u32) :=
        pureEval_paren (pureEval_binary_int (pureEval_var_int hs_data' (modSet_conflicts_nil _ _ _))
          (pureEval_lit (val := 8) (k := .i32) (s := .none) (r := .dec)) rfl rfl
          (evalIntBinary_u32_shr_i32 dv (by decide)))
      have hand_eval : PureEval prog zlibPointerConfig loopEnv m' []
          (CExpr.binary .bitAnd (CExpr.var "data") (CExpr.lit 255 .i32 .none .hex))
          (.int .u32 (dv &&& BitVec.ofInt 32 255)) (.int .u32) :=
        pureEval_binary_int (pureEval_var_int hs_data' (modSet_conflicts_nil _ _ _))
          (pureEval_lit (val := 255) (k := .i32) (s := .none) (r := .hex)) rfl rfl
          (evalIntBinary_u32_and_i32 dv (by decide) (by decide))
      have hidx_lt : (dv &&& BitVec.ofInt 32 255).toNat < 256 := by
        rw [BitVec.toNat_and]
        have h255 : (BitVec.ofInt 32 255).toNat = 255 := by decide
        rw [h255]
        exact Nat.lt_succ_of_le Nat.and_le_right
      have htbl_m' : ∀ idx < 256, ∃ bv : BitVec 32,
          Sem.readVal prog.tags m' b_ct (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv) := by
        intro idx hi
        obtain ⟨bv, hrv⟩ := htbl_ct idx hi
        exact ⟨bv, by rw [readVal_eq_of_blocks_eq prog.tags (LocalFrameMem.blocks_eq_of_lt hf' hbk_lt_ct)]; exact hrv⟩
      obtain ⟨tblBv, htbl_eval⟩ := pureEval_crc_table_index hlu_ct_loop htbl_m' rfl hidx_lt hand_eval
        (fun _ => rfl)
      have hrhs_eval : PureEval prog zlibPointerConfig loopEnv m' []
          (CExpr.binary .bitXor
            (CExpr.binary .shr (CExpr.var "data") (CExpr.lit 8)).paren
            ((CExpr.var "crc_table").index
              (CExpr.binary .bitAnd (CExpr.var "data") (CExpr.lit 255 .i32 .none .hex))))
          (.int .u32 ((dv >>> 8) ^^^ tblBv)) (.int .u32) :=
        pureEval_binary_int hshr_eval htbl_eval rfl rfl (evalIntBinary_u32_xor_u32 _ _)
      refine wp_stmt_assign_int (innerBlks := [b_k]) (outerBlks := [b_data])
        hs_data'.to_uninit hdata_mem hf' hrhs_eval ?_
      intro m1 hm1 hf1 hs_data1
      have hdv1_eq : BitVec.ofInt 32 (((dv >>> 8) ^^^ tblBv).toNat : Int) = (dv >>> 8) ^^^ tblBv :=
        bitVec_ofInt_toNat 32 _
      have hs_data1' : IntSlot loopEnv m1 "data" b_data zWordTy .u32 ((dv >>> 8) ^^^ tblBv) := by
        simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hdv1_eq] at hs_data1
        exact hs_data1
      have hs_k1 := hs_k'.preserve_ne hm1 hne_kd
      refine WPTerm.of_det (by rfl) ?_
      obtain ⟨m2, hm2, hf2, hs_k2⟩ := hs_k1.write hf1 hk_mem (kv + 1#32)
      have hs_data2 := hs_data1'.preserve_ne hm2 hne_kd.symm
      have hnc_k : ModSet.conflicts [] b_k 0 (sizeofTy prog.tags (.int .i32)) = false := rfl
      have hk_happ : Sem.applyBinary zlibPointerConfig prog.tags m1 .add (.int .i32 kv) (.int .i32)
          (.int .i32 (BitVec.ofInt 32 1)) (.int .i32) = some (.int .i32 (kv + 1#32), .int .i32) := by
        rw [applyBinary_int (t1 := .int .i32) (t2 := .int .i32) rfl rfl]
        exact evalIntBinary_i32_add_1 hk0 hklt
      have hstep_inc : Sem.stepExprPure prog zlibPointerConfig loopEnv m1 []
          (.ret (.lval b_k 0 (.int .i32)) [.incDecF .postInc]) =
          some (.ret (.rval (.int .i32 kv) (.int .i32)) [], m2,
            [⟨b_k, 0, sizeofTy prog.tags (.int .i32)⟩]) := by
        unfold Sem.stepExprPure
        simp only [hnc_k, Bool.not_false, guard_true, hs_k1.readVal_eq, hk_happ, hm2,
          bind, Option.bind, pure, Pure.pure]
      refine WPTerm.of_exprPure (by rfl) ?_
      refine wp_lval_var hs_k1.1 ?_
      refine WPTerm.of_exprPure hstep_inc ?_
      refine WPTerm.of_det (by rfl) ?_
      have hk1_toInt : (kv + 1#32).toInt = kv.toInt + 1 := by
        have h1t : (1#32 : BitVec 32).toInt = 1 := rfl
        rw [BitVec.toInt_add, h1t, Int.bmod_eq_of_le (by omega) (by omega)]
      have hmeas'_lt : (4 - (kv + 1#32).toInt).toNat < meas := by
        rw [hk1_toInt, hmeas]; omega
      exact ih (4 - (kv + 1#32).toInt).toNat loopEnv [b_k] m2 os hmeas'_lt
        (by dsimp [Inv]; exact ⟨rfl, rfl, rfl, kv + 1#32, (dv >>> 8) ^^^ tblBv, hf2, hs_k2, hs_data2,
          by omega, by omega, rfl⟩)
    · refine wp_forCond_false hcond (by rw [isTruthy_int_nat (k := .i32)]; simp [hklt]) ?_
      refine WPTerm.of_det (by rfl) ?_
      have hcast_z : Sem.castVal m' zCrcTy (.int .u32 dv) = some (.int .u32 dv) := by
        have h := castVal_int_eq (m := m') (ty := zCrcTy) (k1 := .u32) (k2 := .u32) rfl dv
        simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
        exact h
      have he_ret : PureEval prog zlibPointerConfig loopEnv m' []
          (CExpr.cast zCrcTy (CExpr.var "data")) (.int .u32 dv) zCrcTy :=
        pureEval_cast (pureEval_var_int hs_data' (modSet_conflicts_nil _ _ _)) hcast_z
      have hcast_ret : Sem.castVal m' Zlib.Crc32.crc32TU_fn_crc_word.retTy (.int .u32 dv) =
          some (.int .u32 dv) := by
        have h := castVal_int_eq (m := m') (ty := Zlib.Crc32.crc32TU_fn_crc_word.retTy)
          (k1 := .u32) (k2 := .u32) (by simp [Zlib.Crc32.crc32TU_fn_crc_word, CTy.unqual]) dv
        simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
        exact h
      refine wp_return_pure (innerBlks := [b_k]) (callBlks := [b_data])
        (env := env) (blks := blks) (fs := fs) (ctx := ctx) (k := k)
        (k_ret := .stmts [] (.blockEnd env_params [b_data]
          (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc_word.retTy
            Zlib.Crc32.crc32TU_fn_crc_word.body fs ctx k)))
        (fnRetTy := Zlib.Crc32.crc32TU_fn_crc_word.retTy)
        (by simp [Sem.unwindReturn]) rfl (by decide) hf' he_ret hcast_ret ?_
      intro ret m_ret hro hret _
      exact hcont ret m_ret hro ⟨dv, hret⟩

/-! ## 5. Shared Braid Combinators and `crc32_braid` -/

private theorem evalIntBinary_u32_xor_u64 (v1 : BitVec 32) (v2 : BitVec 64) :
    Sem.evalIntBinary .bitXor (.int .u32 v1) (.int .u64 v2) =
      some (.int .u64 (v1.zeroExtend 64 ^^^ v2), .int .u64) := by
  unfold Sem.evalIntBinary
  have hze : BitVec.ofInt 64 (v1.toNat : Int) = v1.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v1.toNat < 2 ^ 64)]
  have h1 : IntKind.usualArith .u32 .u64 = .u64 := rfl
  dsimp only [Sem.valAsInt?, bind, Option.bind, pure, Pure.pure]
  rw [h1]
  refine congrArg (fun z : BitVec IntKind.u64.bits => some (Val.int .u64 z, CTy.int .u64)) ?_
  simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat, hze]
  rfl

private theorem pureEval_lit_sym {prog cfg env m mods val k s r sym?} :
    PureEval prog cfg env m mods (.lit val k s r sym?) (Sem.ofIntCast k val) (.int k) :=
  ⟨fun hw => WPTerm.of_exprPure rfl hw⟩

private theorem pureEval_words_index {prog env m0 m blks wNm b_w ty_w el_w pb poff blk0 remBytes}
    {j : Nat} (hj : j < 2 ^ 31)
    (hf : LocalFrameMem m0 m blks)
    (hs_w : PtrSlot env m wNm b_w ty_w el_w (.ptr pb poff))
    (hel : el_w.unqual = .int .u32)
    (hr : Readable m0 (.ptr pb poff) remBytes)
    (hblk0 : m0.blocks pb = some blk0)
    (hal : Mem.isAligned blk0 poff 4 = true)
    (hbound : 4 * j + 4 ≤ remBytes) :
    ∃ wbv : BitVec 32,
      PureEval prog zlibPointerConfig env m [] ((CExpr.var wNm).index (CExpr.lit (j : Int)))
        (.int .u32 wbv) el_w.decay := by
  obtain ⟨wbv, hrv⟩ := Readable.read_u32_word (tags := prog.tags) hf hr hblk0 hal hbound
  have hrv_w : Sem.readVal prog.tags m pb (Int64.ofInt (poff.toInt + 4 * j)) el_w =
      some (.int .u32 wbv) := by
    rw [readVal_congr_unqual prog.tags (ty2 := .const_ (.typedef "z_word_t" (.int .u32)))
      (by rw [hel]; rfl)]
    exact hrv
  have hsz_el : sizeofTy prog.tags el_w = 4 := sizeofTy_eq_bytes hel
  have hmax_el : (max (1 : Int) (sizeofTy prog.tags el_w : Int)) = 4 := by rw [hsz_el]; decide
  have hlt_pb : pb < m0.nextBlock := Readable.block_lt hr
  have hm_pb : m.blocks pb = some blk0 := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt_pb, hblk0]
  rcases hr with ⟨_, _, blk', heq, hblk', hin, _⟩
  cases heq; rw [hblk0] at hblk'; cases hblk'
  have hin' := inBounds_iff.mp hin
  have hji : (BitVec.ofInt 32 (j : Int)).toInt = (j : Int) := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
  have hptr_add : Sem.evalPtrAdd zlibPointerConfig prog.tags m (.ptr pb poff) el_w
      (BitVec.ofInt 32 (j : Int)).toInt = some (.ptr pb (Int64.ofInt (poff.toInt + 4 * j))) := by
    rw [hji]
    have hlo : 0 ≤ poff.toInt + (j : Int) * (max (1 : Int) (sizeofTy prog.tags el_w : Int)) := by
      rw [hmax_el]; omega
    have hhi : poff.toInt + (j : Int) * (max (1 : Int) (sizeofTy prog.tags el_w : Int)) ≤ (blk0.size : Int) := by
      rw [hmax_el]; omega
    have h := evalPtrAdd_eq (tags := prog.tags) hm_pb hlo hhi
    have hmul : poff.toInt + (j : Int) * (max (1 : Int) (sizeofTy prog.tags el_w : Int)) =
        poff.toInt + 4 * (j : Int) := by rw [hmax_el]; omega
    rw [hmul] at h
    exact h
  have hnc_w : ModSet.conflicts [] b_w 0 8 = false := modSet_conflicts_nil _ _ _
  have hnc_pb : ModSet.conflicts [] pb (Int64.ofInt (poff.toInt + 4 * j)) 4 = false :=
    modSet_conflicts_nil _ _ _
  have hrp : Sem.readPlace prog.tags m [] .rval pb (Int64.ofInt (poff.toInt + 4 * j)) el_w =
      some (.rval (.int .u32 wbv) el_w.decay) := by
    unfold Sem.readPlace
    rw [hel, hsz_el, hnc_pb]
    simp only [Bool.not_false, guard_true, bind, Option.bind, Option.map, hrv_w]
  have hdec : ty_w.decay.unqual = .ptr el_w := CTy.decay_of_ptr hs_w.2.1
  refine ⟨wbv, ⟨fun {ext Q fs ctx blks os kcont} hw => ?_⟩⟩
  have hstep_idx : Sem.stepExprPure prog zlibPointerConfig env m []
      (.ret (.rval (Sem.ofIntCast .i32 (j : Int)) (.int .i32))
        (.indexIdxF .rval (.ptr pb poff) ty_w.decay :: fs)) =
      some (.ret (.rval (.int .u32 wbv) el_w.decay) fs, m, []) := by
    unfold Sem.stepExprPure
    simp only [hdec, Sem.valAsInt?, Sem.ofIntCast, IntKind.signed, IntKind.bits, ↓reduceIte,
      bind, Option.bind, pure, Pure.pure]
    rw [hptr_add]
    dsimp only
    rw [hrp]
  exact WPTerm.of_exprPure (by rfl)
    ((pureEval_var_ptr hs_w hnc_w).run
      (WPTerm.of_exprPure (by rfl)
        ((pureEval_lit (val := (j : Int)) (k := .i32) (s := .none) (r := .dec)).run
          (WPTerm.of_exprPure hstep_idx hw))))

private theorem wp_stmt_assign_word_xor {prog ext env innerBlks m0 outerBlks m os kcont Q
    wNm b_w ty_w crcNm b_c ty_c wordsNm b_words ty_words el_words pb poff blk0 remBytes}
    {j : Nat} (hj : j < 2 ^ 31) {vc : BitVec 32}
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw_mem : b_w ∈ innerBlks ++ outerBlks)
    (hs_w : UninitIntSlot env m wNm b_w ty_w .u32)
    (hs_c : IntSlot env m crcNm b_c ty_c .u32 vc)
    (hs_words : PtrSlot env m wordsNm b_words ty_words el_words (.ptr pb poff))
    (hel : el_words.unqual = .int .u32)
    (hr : Readable m0 (.ptr pb poff) remBytes)
    (hblk0 : m0.blocks pb = some blk0)
    (hal : Mem.isAligned blk0 poff 4 = true)
    (hbound : 4 * j + 4 ≤ remBytes)
    (hcont : ∀ (wv : BitVec 32) (m1 : Mem),
      LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 wNm b_w ty_w .u32 wv →
      (∀ b', b' ≠ b_w → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .eq (CExpr.var wNm)
        (CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit (j : Int)))))))
        env innerBlks m os kcont) := by
  obtain ⟨wbv, hidx⟩ := pureEval_words_index hj hf hs_words hel hr hblk0 hal hbound
  have he_rhs : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit (j : Int))))
      (.int .u32 (vc ^^^ wbv)) (.int .u32) :=
    pureEval_binary_int (pureEval_var_int hs_c (modSet_conflicts_nil _ _ _)) hidx
      (CTy.decay_of_int hs_c.2.1) (CTy.decay_of_int hel) (evalIntBinary_u32_xor_u32 vc wbv)
  refine wp_stmt_assign_int hs_w hw_mem hf he_rhs ?_
  intro m1 hwr1 hf1 hs_w1
  have hbv : BitVec.ofInt 32 ((vc ^^^ wbv).toNat : Int) = vc ^^^ wbv := bitVec_ofInt_toNat 32 _
  have hs_w1' : IntSlot env m1 wNm b_w ty_w .u32 (vc ^^^ wbv) := by
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hbv] at hs_w1
    exact hs_w1
  exact hcont (vc ^^^ wbv) m1 hf1 hs_w1' (fun b' hne => writeVal_blocks_ne hwr1 hne)

private theorem wp_stmt_assign_crcword {prog ext env innerBlks m0 outerBlks m os kcont Q
    crcNm b_c ty_c wNm b_w ty_w tblNm b_tbl} {wbv : BitVec 32}
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hc_mem : b_c ∈ innerBlks ++ outerBlks)
    (hs_c : UninitIntSlot env m crcNm b_c ty_c .u32)
    (hs_w : IntSlot env m wNm b_w ty_w .u32 wbv)
    (hlu_tbl : env.lookup tblNm = some (b_tbl, .array (.array crcConstTy (some 256)) (some 4)))
    (htbl : ∀ row < 4, ∀ idx < 256, ∃ bv : BitVec 32,
      Sem.readVal prog.tags m b_tbl (Int64.ofNat (1024 * row + 4 * idx)) crcConstTy = some (.int .u32 bv))
    (hcont : ∀ (cbv : BitVec 32) (m1 : Mem),
      LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 crcNm b_c ty_c .u32 cbv →
      (∀ b', b' ≠ b_c → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .eq (.var crcNm) (crcwordExpr tblNm wNm))))
        env innerBlks m os kcont) := by
  obtain ⟨cbv, hcw⟩ := pureEval_crcword hlu_tbl htbl hs_w
  refine wp_stmt_assign_int hs_c hc_mem hf hcw ?_
  intro m1 hwr1 hf1 hs_c1
  have hbv : BitVec.ofInt 32 (cbv.toNat : Int) = cbv := bitVec_ofInt_toNat 32 cbv
  have hs_c1' : IntSlot env m1 crcNm b_c ty_c .u32 cbv := by
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, hbv] at hs_c1
    exact hs_c1
  exact hcont cbv m1 hf1 hs_c1' (fun b' hne => writeVal_blocks_ne hwr1 hne)

private theorem wp_forCond_preDec_u64 {prog ext env innerBlks m0 outerBlks m os kcont Q
    x b ty body} {v : BitVec 64}
    (hv : 1 ≤ v.toNat)
    (hs : IntSlot env m x b ty .u64 v)
    (hmem : b ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hdone : ∀ m1, v.toNat = 1 → LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 x b ty .u64 (v - 1#64) →
      (∀ b', b' ≠ b → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os kcont))
    (hstep : ∀ m1, 2 ≤ v.toNat → LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 x b ty .u64 (v - 1#64) →
      (∀ b', b' ≠ b → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.stmt body) env innerBlks m1 os
          (.loop (some (.incDec .preDec (.var x))) none body false kcont))) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.expr (.eval .rval (.incDec .preDec (.var x)) [])
        (.forCond (.incDec .preDec (.var x)) none body) []) env innerBlks m os kcont) := by
  obtain ⟨m1, hm1, hf1, hs1⟩ := hs.write hf hmem (v - 1#64)
  have hnc : ModSet.conflicts [] b 0 (sizeofTy prog.tags ty) = false := modSet_conflicts_nil _ _ _
  have hrv := hs.readVal_eq prog.tags
  have happ : Sem.applyBinary zlibPointerConfig prog.tags m .add (.int .u64 v) ty
      (.int .i32 (BitVec.ofInt 32 (-1))) (.int .i32) = some (.int .u64 (v - 1#64), .int .u64) := by
    rw [applyBinary_int hs.2.1 rfl]
    exact evalIntBinary_u64_add_neg1 v
  have hstep_dec : Sem.stepExprPure prog zlibPointerConfig env m []
      (.ret (.lval b 0 ty) [.incDecF .preDec]) =
      some (.ret (.rval (.int .u64 (v - 1#64)) ty) [], m1, [⟨b, 0, sizeofTy prog.tags ty⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc, Bool.not_false, guard_true, hrv, happ, hm1, bind, Option.bind, pure, Pure.pure]
  have hv1_nat : (v - 1#64).toNat = v.toNat - 1 := by
    rw [BitVec.toNat_sub]
    have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
    have hlt64 := v.isLt
    rw [h1n]; omega
  refine WPTerm.of_exprPure (by rfl) (wp_lval_var hs.1 (WPTerm.of_exprPure hstep_dec ?_))
  by_cases h1 : v.toNat = 1
  · have htr : Sem.isTruthy (.int .u64 (v - 1#64)) = some false := by
      have h := isTruthy_int_nat (k := .u64) (v - 1#64)
      rw [h]; change some ((v - 1#64).toNat != 0) = some false; simp [hv1_nat, h1]
    refine WPTerm.of_det ?_ (hdone m1 h1 hf1 hs1 (fun b' hne => writeVal_blocks_ne hm1 hne))
    unfold Sem.stepDet
    simp only [htr, Option.bind, Option.map_some]
    rfl
  · have h2 : 2 ≤ v.toNat := by omega
    have htr : Sem.isTruthy (.int .u64 (v - 1#64)) = some true := by
      have h := isTruthy_int_nat (k := .u64) (v - 1#64)
      rw [h]; change some ((v - 1#64).toNat != 0) = some true
      have hne0 : v.toNat - 1 ≠ 0 := by omega
      simp [hv1_nat, bne_iff_ne.mpr hne0]
    refine WPTerm.of_det ?_ (hstep m1 h2 hf1 hs1 (fun b' hne => writeVal_blocks_ne hm1 hne))
    unfold Sem.stepDet
    simp only [htr, Option.bind, Option.map_some]
    rfl

private theorem wp_if_endian_one {prog ext env innerBlks m0 outerBlks m os rest kcont Q
    b_end ty_end t f}
    (hend_ty : ty_end = .int .u32)
    (hend_mem : b_end ∈ innerBlks ++ outerBlks)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hu_end : UninitIntSlot env m "endian" b_end ty_end .u32)
    (hcont : ∀ m1, LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      IntSlot env m1 "endian" b_end ty_end .u32 1#32 →
      (∀ b', b' ≠ b_end → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt t) env innerBlks m1 os (.stmts rest kcont))) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .eq (.var "endian") (.lit 1)))) env innerBlks m os
        (.stmts (CStmt.ifStmt
          (.deref (.cast (.ptr (.int .u8)) (.addrOf (.var "endian")))) t (some f) :: rest) kcont)) := by
  subst hend_ty
  refine wp_stmt_assign_int hu_end hend_mem hf (pureEval_lit (val := 1) (k := .i32) (s := .none) (r := .dec)) ?_
  intro m1 hwr1 hf1 hs1
  simp only [IntKind.signed, IntKind.bits, ↓reduceIte] at hwr1 hs1
  have h1bv : BitVec.ofInt 32 (BitVec.ofInt 32 1).toInt = 1#32 := rfl
  rw [h1bv] at hwr1 hs1
  rcases hu_end with ⟨hlu_end, _, _, blk0, hm_b, _, _, _⟩
  have hrv_u8 : Sem.readVal prog.tags m1 b_end 0 (.int .u8) = some (.int .u8 1#8) :=
    endian_read_u8_one prog.tags hm_b hwr1
  have hrp_u8 : Sem.readPlace prog.tags m1 [] .rval b_end 0 (.int .u8) =
      some (.rval (.int .u8 1#8) (CTy.int .u8).decay) := by
    unfold Sem.readPlace
    simp only [CTy.unqual, hrv_u8]
    rfl
  have hcast_u8p : Sem.castVal m1 (.ptr (.int .u8)) (.ptr b_end 0) = some (.ptr b_end 0) :=
    castVal_ptr_eq (el := .int .u8) rfl (Or.inr ⟨b_end, 0, rfl⟩)
  have hstep_deref : Sem.stepExprPure prog zlibPointerConfig env m1 []
      (.ret (.rval (.ptr b_end 0) (.ptr (.int .u8))) [.derefF .rval]) =
      some (.ret (.rval (.int .u8 1#8) (CTy.int .u8).decay) [], m1, []) := by
    unfold Sem.stepExprPure
    simp only [CTy.unqual, hrp_u8, bind, Option.bind, pure, Pure.pure]
  have hstep_br : Sem.stepDet prog zlibPointerConfig
      (.running (.expr (.ret (.rval (.int .u8 1#8) (CTy.int .u8).decay) [])
        (.branch t ((some f).getD .nop)) []) env innerBlks m1 os (.stmts rest kcont)) =
      some (.next (.running (.stmt t) env innerBlks m1 os (.stmts rest kcont))) := rfl
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  refine WPTerm.of_exprPure (by rfl) (WPTerm.of_exprPure (by rfl) (WPTerm.of_exprPure (by rfl) ?_))
  refine wp_lval_var hs1.1 ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by unfold Sem.stepExprPure; simp only [hcast_u8p]; rfl) ?_
  exact WPTerm.of_exprPure hstep_deref (WPTerm.of_det hstep_br
    (hcont m1 hf1 hs1 (fun b' hne => writeVal_blocks_ne hwr1 hne)))

private theorem wp_call_crc_word_1 {prog gEnv m0_g os0_g ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc crcNm b_c ty_c wordsNm b_words ty_words el_words pb poff blk0 remBytes}
    {vc0 : BitVec 32}
    (hlib : InitLibzProps prog gEnv m0_g os0_g)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hs_crc : ∃ vc : BitVec 64, IntSlot env m "crc" b_crc ty_crc .u64 vc)
    (hs_c : IntSlot env m crcNm b_c ty_c .u32 vc0)
    (hs_words : PtrSlot env m wordsNm b_words ty_words el_words (.ptr pb poff))
    (hel : el_words.unqual = .int .u32)
    (hr : Readable m0 (.ptr pb poff) remBytes)
    (hblk0 : m0.blocks pb = some blk0)
    (hal : Mem.isAligned blk0 poff 4 = true)
    (hbound : 4 ≤ remBytes)
    (hlu_cw : env.lookup "crc_word" = none)
    (htbl_ct : CrcTableValid prog gEnv m)
    (hcont : ∀ (vc' : BitVec 64) (m' : Mem),
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' "crc" b_crc ty_crc .u64 vc' →
      m.nextBlock ≤ m'.nextBlock →
      (∀ b', b' < m.nextBlock → b' ≠ b_crc → m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .eq (CExpr.var "crc")
        (CExpr.call (CExpr.var "crc_word")
          [CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit 0))]))))
        env innerBlks m os kcont) := by
  rcases hs_crc with ⟨vc, hs_crc⟩
  obtain ⟨wbv, hidx⟩ := pureEval_words_index (j := 0) (by decide) hf hs_words hel hr hblk0 hal hbound
  have he_arg : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit 0)))
      (.int .u32 (vc0 ^^^ wbv)) (.int .u32) :=
    pureEval_binary_int (pureEval_var_int hs_c (modSet_conflicts_nil _ _ _)) hidx
      (CTy.decay_of_int hs_c.2.1) (CTy.decay_of_int hel) (evalIntBinary_u32_xor_u32 vc0 wbv)
  have henum : enumConst? prog.tags "crc_word" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc_word" (by decide)
  have hproto := prog_fnProtos_crc_word hlib
  have hfn := prog_fns_crc_word hlib
  have hsimp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc_word.params, IsSimpleParamTy p.ty := by
    intro p hp; simp [Zlib.Crc32.crc32TU_fn_crc_word] at hp; subst hp; simp [IsSimpleParamTy, CTy.unqual]
  have hcoerce : Sem.coerceCallArgs m (Zlib.Crc32.crc32TU_fn_crc_word.params.map (·.ty)) false
      [(.int .u32 (vc0 ^^^ wbv), .int .u32)] = some [.int .u32 (vc0 ^^^ wbv)] := by
    have hc : Sem.castVal m zWordTy (.int .u32 (vc0 ^^^ wbv)) = some (.int .u32 (vc0 ^^^ wbv)) := by
      have h := castVal_int_eq (m := m) (ty := zWordTy) (k1 := .u32) (k2 := .u32) rfl (vc0 ^^^ wbv)
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte] at h
      rw [bitVec_ofInt_toNat] at h
      exact h
    unfold Sem.coerceCallArgs
    simp only [Zlib.Crc32.crc32TU_fn_crc_word, List.map_cons, List.map_nil, Bool.false_eq_true,
      ↓reduceIte, List.length_cons, List.length_nil, beq_self_eq_true, guard_true, List.zip_cons_cons,
      List.zip_nil_right, List.mapM_cons, List.mapM_nil, hc, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs_crc.1 ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_call_var hlu_cw henum hproto ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine he_arg.run ?_
  refine FuncBodySpec.call (crc_word_spec ext hlib) (by unfold Sem.stepDet; rfl)
    hfn rfl rfl hcoerce ⟨⟨vc0 ^^^ wbv, rfl⟩, htbl_ct⟩ hsimp ?_
  intro ret m1 hro1 ⟨retBv, hret⟩
  subst hret
  have hf1 : LocalFrameMem m0 m1 (innerBlks ++ outerBlks) := hf.of_roExt hro1
  have hs_crc1 := hs_crc.preserve_roExt hro1
  let vc' : BitVec 64 := BitVec.ofInt 64 (retBv.toNat : Int)
  obtain ⟨m2, hwr2, hf2, hs_crc2⟩ := hs_crc1.to_uninit.write hf1 hcrc_mem vc'
  have hcast_crc : Sem.castVal m1 ty_crc (.int .u32 retBv) = some (.int .u64 vc') :=
    castVal_int_eq (k1 := .u32) (k2 := .u64) hs_crc.2.1 retBv
  have hnc_crc : ModSet.conflicts [] b_crc 0 (sizeofTy prog.tags ty_crc) = false :=
    modSet_conflicts_nil _ _ _
  have hwp_crc : Sem.writePlace prog.tags m1 b_crc 0 ty_crc (.rval (.int .u32 retBv) Zlib.Crc32.crc32TU_fn_crc_word.retTy) =
      some (.rval (.int .u64 vc') ty_crc, m2) := by
    unfold Sem.writePlace
    simp only [hs_crc.2.1, hcast_crc, bind, Option.bind, pure, Pure.pure, hwr2]
  have hstep_ass : Sem.stepExprPure prog zlibPointerConfig env m1 []
      (.ret (.rval (.int .u32 retBv) Zlib.Crc32.crc32TU_fn_crc_word.retTy) [.assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u64 vc') ty_crc) [], m2, [⟨b_crc, 0, sizeofTy prog.tags ty_crc⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc_crc, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp_crc,
      bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_exprPure hstep_ass (WPTerm.of_det (by rfl) ?_)
  refine hcont vc' m2 hf2 hs_crc2 (Nat.le_trans hro1.1 (Nat.le_of_eq (writeVal_nextBlock hwr2).symm)) ?_
  intro b' hlt hne
  rw [writeVal_blocks_ne hwr2 hne, hro1.2.1 b' hlt]

private theorem wp_call_crc_word_2 {prog gEnv m0_g os0_g ext env innerBlks m0 outerBlks m os kcont Q
    b_crc ty_crc crcNm b_c ty_c wordsNm b_words ty_words el_words pb poff blk0 remBytes}
    {j : Nat} (hj : j < 2 ^ 31) {vcj : BitVec 32} {vc : BitVec 64}
    (hlib : InitLibzProps prog gEnv m0_g os0_g)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hs_crc : IntSlot env m "crc" b_crc ty_crc .u64 vc)
    (hs_c : IntSlot env m crcNm b_c ty_c .u32 vcj)
    (hs_words : PtrSlot env m wordsNm b_words ty_words el_words (.ptr pb poff))
    (hel : el_words.unqual = .int .u32)
    (hr : Readable m0 (.ptr pb poff) remBytes)
    (hblk0 : m0.blocks pb = some blk0)
    (hal : Mem.isAligned blk0 poff 4 = true)
    (hbound : 4 * j + 4 ≤ remBytes)
    (hlu_cw : env.lookup "crc_word" = none)
    (htbl_ct : CrcTableValid prog gEnv m)
    (hcont : ∀ (vc' : BitVec 64) (m' : Mem),
      LocalFrameMem m0 m' (innerBlks ++ outerBlks) →
      IntSlot env m' "crc" b_crc ty_crc .u64 vc' →
      m.nextBlock ≤ m'.nextBlock →
      (∀ b', b' < m.nextBlock → b' ≠ b_crc → m'.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m' os kcont)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .eq (CExpr.var "crc")
        (CExpr.call (CExpr.var "crc_word")
          [CExpr.binary .bitXor
            (CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit (j : Int))))
            (CExpr.var "crc")]))))
        env innerBlks m os kcont) := by
  obtain ⟨wbv, hidx⟩ := pureEval_words_index hj hf hs_words hel hr hblk0 hal hbound
  have he_xor1 : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit (j : Int))))
      (.int .u32 (vcj ^^^ wbv)) (.int .u32) :=
    pureEval_binary_int (pureEval_var_int hs_c (modSet_conflicts_nil _ _ _)) hidx
      (CTy.decay_of_int hs_c.2.1) (CTy.decay_of_int hel) (evalIntBinary_u32_xor_u32 vcj wbv)
  have he_arg : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .bitXor
        (CExpr.binary .bitXor (CExpr.var crcNm) ((CExpr.var wordsNm).index (CExpr.lit (j : Int))))
        (CExpr.var "crc"))
      (.int .u64 ((vcj ^^^ wbv).zeroExtend 64 ^^^ vc)) (.int .u64) :=
    pureEval_binary_int he_xor1 (pureEval_var_int hs_crc (modSet_conflicts_nil _ _ _))
      rfl (CTy.decay_of_int hs_crc.2.1) (evalIntBinary_u32_xor_u64 (vcj ^^^ wbv) vc)
  let arg64 : BitVec 64 := (vcj ^^^ wbv).zeroExtend 64 ^^^ vc
  let arg32 : BitVec 32 := BitVec.ofInt 32 (arg64.toNat : Int)
  have henum : enumConst? prog.tags "crc_word" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc_word" (by decide)
  have hproto := prog_fnProtos_crc_word hlib
  have hfn := prog_fns_crc_word hlib
  have hsimp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc_word.params, IsSimpleParamTy p.ty := by
    intro p hp; simp [Zlib.Crc32.crc32TU_fn_crc_word] at hp; subst hp; simp [IsSimpleParamTy, CTy.unqual]
  have hcoerce : Sem.coerceCallArgs m (Zlib.Crc32.crc32TU_fn_crc_word.params.map (·.ty)) false
      [(.int .u64 arg64, .int .u64)] = some [.int .u32 arg32] := by
    have hc : Sem.castVal m zWordTy (.int .u64 arg64) = some (.int .u32 arg32) := by
      have h := castVal_int_eq (m := m) (ty := zWordTy) (k1 := .u64) (k2 := .u32) rfl arg64
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte] at h
      exact h
    unfold Sem.coerceCallArgs
    simp only [Zlib.Crc32.crc32TU_fn_crc_word, List.map_cons, List.map_nil, Bool.false_eq_true,
      ↓reduceIte, List.length_cons, List.length_nil, beq_self_eq_true, guard_true, List.zip_cons_cons,
      List.zip_nil_right, List.mapM_cons, List.mapM_nil, hc, bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_det (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_lval_var hs_crc.1 ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine wp_call_var hlu_cw henum hproto ?_
  refine WPTerm.of_exprPure (by rfl) ?_
  refine he_arg.run ?_
  refine FuncBodySpec.call (crc_word_spec ext hlib) (by unfold Sem.stepDet; rfl)
    hfn rfl rfl hcoerce ⟨⟨arg32, rfl⟩, htbl_ct⟩ hsimp ?_
  intro ret m1 hro1 ⟨retBv, hret⟩
  subst hret
  have hf1 : LocalFrameMem m0 m1 (innerBlks ++ outerBlks) := hf.of_roExt hro1
  have hs_crc1 := hs_crc.preserve_roExt hro1
  let vc' : BitVec 64 := BitVec.ofInt 64 (retBv.toNat : Int)
  obtain ⟨m2, hwr2, hf2, hs_crc2⟩ := hs_crc1.to_uninit.write hf1 hcrc_mem vc'
  have hcast_crc : Sem.castVal m1 ty_crc (.int .u32 retBv) = some (.int .u64 vc') :=
    castVal_int_eq (k1 := .u32) (k2 := .u64) hs_crc.2.1 retBv
  have hnc_crc : ModSet.conflicts [] b_crc 0 (sizeofTy prog.tags ty_crc) = false :=
    modSet_conflicts_nil _ _ _
  have hwp_crc : Sem.writePlace prog.tags m1 b_crc 0 ty_crc (.rval (.int .u32 retBv) Zlib.Crc32.crc32TU_fn_crc_word.retTy) =
      some (.rval (.int .u64 vc') ty_crc, m2) := by
    unfold Sem.writePlace
    simp only [hs_crc.2.1, hcast_crc, bind, Option.bind, pure, Pure.pure, hwr2]
  have hstep_ass : Sem.stepExprPure prog zlibPointerConfig env m1 []
      (.ret (.rval (.int .u32 retBv) Zlib.Crc32.crc32TU_fn_crc_word.retTy) [.assignRhsF .eq b_crc 0 ty_crc]) =
      some (.ret (.rval (.int .u64 vc') ty_crc) [], m2, [⟨b_crc, 0, sizeofTy prog.tags ty_crc⟩]) := by
    unfold Sem.stepExprPure
    simp only [hnc_crc, Bool.not_false, guard_true, Sem.assignOpToBin?, hwp_crc,
      bind, Option.bind, pure, Pure.pure]
  refine WPTerm.of_exprPure hstep_ass (WPTerm.of_det (by rfl) ?_)
  refine hcont vc' m2 hf2 hs_crc2 (Nat.le_trans hro1.1 (Nat.le_of_eq (writeVal_nextBlock hwr2).symm)) ?_
  intro b' hlt hne
  rw [writeVal_blocks_ne hwr2 hne, hro1.2.1 b' hlt]

private theorem intSlot_drop_env {nm0 b0 ty0 env m nm b ty k v}
    (hne : nm ≠ nm0) (hs : IntSlot ((nm0, b0, ty0) :: env) m nm b ty k v) :
    IntSlot env m nm b ty k v := by
  have h1 := hs.1
  rw [lookup_cons_ne env hne] at h1
  exact ⟨h1, hs.2⟩

private theorem ptrSlot_drop_env {nm0 b0 ty0 env m nm b ty el p}
    (hne : nm ≠ nm0) (hs : PtrSlot ((nm0, b0, ty0) :: env) m nm b ty el p) :
    PtrSlot env m nm b ty el p := by
  have h1 := hs.1
  rw [lookup_cons_ne env hne] at h1
  exact ⟨h1, hs.2⟩

private theorem wp_braid_setup_blks_len_words {prog ext env innerBlks m0 outerBlks m os rest kcont Q
    b_blks ty_blks b_words ty_words el_words b_len ty_len b_buf ty_buf el_buf b_crc ty_crc pb poff}
    {k : Nat} (hk_pos : 0 < k) (hk_lt : (4 * k : Int) < 2 ^ 31)
    {len0 : BitVec 64} (hlen_min : 4 * k ≤ len0.toNat)
    {vc0 : BitVec 64}
    (hf0 : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hblks_mem : b_blks ∈ innerBlks ++ outerBlks)
    (hwords_mem : b_words ∈ innerBlks ++ outerBlks)
    (hlen_mem : b_len ∈ innerBlks ++ outerBlks)
    (hne_bw : b_blks ≠ b_words) (hne_bl : b_blks ≠ b_len) (hne_bc : b_blks ≠ b_crc)
    (hne_wl : b_words ≠ b_len) (hne_wb : b_words ≠ b_buf) (hne_wc : b_words ≠ b_crc)
    (hne_lb : b_len ≠ b_buf) (hne_lc : b_len ≠ b_crc)
    (hne_l_blks : b_len ≠ b_blks) (hne_b_blks : b_buf ≠ b_blks)
    (hu_blks : UninitIntSlot env m "blks" b_blks ty_blks .u64)
    (hu_words : UninitPtrSlot env m "words" b_words ty_words el_words)
    (hs_len0 : IntSlot env m "len" b_len ty_len .u64 len0)
    (hs_buf0 : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff))
    (hs_crc0 : IntSlot env m "crc" b_crc ty_crc .u64 vc0)
    (hcont : ∀ (blks1 len2 : BitVec 64) (m1 : Mem),
      LocalFrameMem m0 m1 (innerBlks ++ outerBlks) →
      1 ≤ blks1.toNat →
      len2.toNat < 4 * k →
      4 * k * blks1.toNat + len2.toNat = len0.toNat →
      IntSlot env m1 "blks" b_blks ty_blks .u64 blks1 →
      IntSlot env m1 "len" b_len ty_len .u64 len2 →
      PtrSlot env m1 "words" b_words ty_words el_words (.ptr pb poff) →
      PtrSlot env m1 "buf" b_buf ty_buf el_buf (.ptr pb poff) →
      IntSlot env m1 "crc" b_crc ty_crc .u64 vc0 →
      (∀ b', b' ≠ b_blks → b' ≠ b_words → b' ≠ b_len → m1.blocks b' = m.blocks b') →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env innerBlks m1 os (.stmts rest kcont))) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.expr (.assign .eq (.var "blks")
        (.binary .div (.var "len") (CExpr.binary .mul (.lit (k : Int)) (.lit 4)).paren))))
        env innerBlks m os
        (.stmts
          (.expr (.assign .subEq (.var "len") (.binary .mul (.binary .mul (.var "blks") (.lit (k : Int))) (.lit 4))) ::
           .expr (.assign .eq (.var "words") (.cast wordConstPtrTy (.var "buf"))) ::
           rest)
          kcont)) := by
  have hk4_eval : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .mul (CExpr.lit (k : Int)) (CExpr.lit 4)).paren
      (.int .i32 (BitVec.ofInt 32 ((k * 4 : Nat) : Int))) (.int .i32) := by
    have hmul : Sem.evalIntBinary .mul (Sem.ofIntCast .i32 (k : Int)) (Sem.ofIntCast .i32 4) =
        some (.int .i32 (BitVec.ofInt 32 ((k * 4 : Nat) : Int)), .int .i32) := by
      unfold Sem.evalIntBinary
      have hk_i : (BitVec.ofInt 32 (k : Int)).toInt = (k : Int) := by
        rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
      have h4_i : (BitVec.ofInt 32 4).toInt = 4 := rfl
      have hin : IntKind.i32.inRange ((k * 4 : Nat) : Int) = true := by
        simp only [IntKind.inRange, IntKind.minVal, IntKind.maxVal, IntKind.signed, IntKind.bits,
          ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]; omega
      have hprod : (k : Int) * 4 = ((k * 4 : Nat) : Int) := by push_cast; rfl
      have hof : Sem.ofIntExact .i32 ((k : Int) * 4) =
          some (Val.int .i32 (BitVec.ofInt IntKind.i32.bits ((k * 4 : Nat) : Int))) := by
        unfold Sem.ofIntExact; rw [hprod]; simp only [IntKind.signed, hin, ↓reduceIte]
      have h1 : IntKind.usualArith .i32 .i32 = .i32 := rfl
      dsimp only [Sem.valAsInt?, Sem.ofIntCast, bind, Option.bind, pure, Pure.pure]
      rw [h1]; simp only [IntKind.signed, IntKind.bits, ↓reduceIte, hk_i, h4_i]
      rw [hof]; rfl
    exact pureEval_paren (pureEval_binary_int
      (pureEval_lit (val := (k : Int)) (k := .i32) (s := .none) (r := .dec))
      (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec)) rfl rfl hmul)
  have hdiv_eval : PureEval prog zlibPointerConfig env m []
      (CExpr.binary .div (CExpr.var "len") (CExpr.binary .mul (CExpr.lit (k : Int)) (CExpr.lit 4)).paren)
      (.int .u64 (BitVec.ofNat 64 (len0.toNat / (k * 4)))) (.int .u64) := by
    have hk_cast : ((k * 4 : Nat) : Int) = (k : Int) * 4 := by push_cast; rfl
    have hdiv := evalIntBinary_u64_div_i32 len0 (n := ((k * 4 : Nat) : Int)) (by omega) (by omega)
    have hnat : ((k * 4 : Nat) : Int).toNat = k * 4 := Int.toNat_natCast _
    rw [hnat] at hdiv
    exact pureEval_binary_int (pureEval_var_int hs_len0 (modSet_conflicts_nil _ _ _)) hk4_eval
      (CTy.decay_of_int hs_len0.2.1) rfl hdiv
  refine wp_stmt_assign_int hu_blks hblks_mem hf0 hdiv_eval ?_
  intro m1 hwr1 hf1 hs_blks1
  let blks1 : BitVec 64 := BitVec.ofNat 64 (len0.toNat / (k * 4))
  have hbv_blks : BitVec.ofInt 64 (blks1.toNat : Int) = blks1 := bitVec_ofInt_toNat 64 blks1
  have hs_blks1' : IntSlot env m1 "blks" b_blks ty_blks .u64 blks1 := by
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte] at hs_blks1
    rw [hbv_blks] at hs_blks1
    exact hs_blks1
  have hdiv_lt : len0.toNat / (k * 4) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) len0.isLt
  have hblks_nat : blks1.toNat = len0.toNat / (k * 4) := by
    dsimp [blks1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdiv_lt]
  have hblks_ge1 : 1 ≤ blks1.toNat := by
    rw [hblks_nat]
    exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
  have hmul_le : blks1.toNat * (k * 4) ≤ len0.toNat := by
    rw [hblks_nat]
    exact Nat.div_mul_le_self len0.toNat (k * 4)
  have hmul_lt64 : blks1.toNat * k * 4 < 2 ^ 64 := by
    have : blks1.toNat * k * 4 = blks1.toNat * (k * 4) := Nat.mul_assoc _ _ _
    omega
  have hs_len1 := hs_len0.preserve_ne hwr1 hne_l_blks
  have hs_buf1 := hs_buf0.preserve_ne hwr1 hne_b_blks
  have hs_crc1 := hs_crc0.preserve_ne hwr1 hne_bc.symm
  have hu_words1 := hu_words.preserve_ne hwr1 hne_bw.symm
  refine WPTerm.of_det (by rfl) ?_
  have hmulk_eval : PureEval prog zlibPointerConfig env m1 []
      (CExpr.binary .mul (CExpr.var "blks") (CExpr.lit (k : Int)))
      (.int .u64 (BitVec.ofNat 64 (blks1.toNat * k))) (.int .u64) := by
    have hm := evalIntBinary_u64_mul_i32 blks1 (n := (k : Int)) (by omega) (by omega)
    rw [Int.toNat_natCast] at hm
    exact pureEval_binary_int (pureEval_var_int hs_blks1' (modSet_conflicts_nil _ _ _))
      (pureEval_lit (val := (k : Int)) (k := .i32) (s := .none) (r := .dec))
      (CTy.decay_of_int hs_blks1'.2.1) rfl hm
  have hmul4_eval : PureEval prog zlibPointerConfig env m1 []
      (CExpr.binary .mul (CExpr.binary .mul (CExpr.var "blks") (CExpr.lit (k : Int))) (CExpr.lit 4))
      (.int .u64 (BitVec.ofNat 64 ((BitVec.ofNat 64 (blks1.toNat * k)).toNat * 4))) (.int .u64) :=
    pureEval_binary_int hmulk_eval (pureEval_lit (val := 4) (k := .i32) (s := .none) (r := .dec))
      rfl rfl (evalIntBinary_u64_mul_i32 _ (by decide) (by decide))
  have hmul_nat_eq : (BitVec.ofNat 64 (blks1.toNat * k)).toNat * 4 = blks1.toNat * k * 4 := by
    have hk_lt64 : blks1.toNat * k < 2 ^ 64 := by
      have : blks1.toNat * k ≤ blks1.toNat * k * 4 := Nat.le_mul_of_pos_right _ (by decide)
      omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt64]
  let mulBv : BitVec 64 := BitVec.ofNat 64 (blks1.toNat * k * 4)
  have hmul_bv_eq : BitVec.ofNat 64 ((BitVec.ofNat 64 (blks1.toNat * k)).toNat * 4) = mulBv := by
    rw [hmul_nat_eq]
  rw [hmul_bv_eq] at hmul4_eval
  refine wp_stmt_assignOp_int (op := .subEq) (bop := .sub) rfl hs_len1 hlen_mem hf1 hmul4_eval rfl
    (evalIntBinary_u64_sub_u64 len0 mulBv) ?_
  intro m2 hwr2 hf2 hs_len2
  let len2 : BitVec 64 := len0 - mulBv
  have hbv_len2 : BitVec.ofInt 64 (len2.toNat : Int) = len2 := bitVec_ofInt_toNat 64 len2
  have hs_len2' : IntSlot env m2 "len" b_len ty_len .u64 len2 := by
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte] at hs_len2
    rw [hbv_len2] at hs_len2
    exact hs_len2
  have hmul_toNat : mulBv.toNat = blks1.toNat * k * 4 := by
    dsimp [mulBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul_lt64]
  have hlen2_toNat : len2.toNat = len0.toNat - blks1.toNat * k * 4 := by
    change (len0 - mulBv).toNat = len0.toNat - blks1.toNat * k * 4
    rw [BitVec.toNat_sub, hmul_toNat]
    have hlt := len0.isLt
    have : blks1.toNat * k * 4 ≤ len0.toNat := by
      rw [Nat.mul_assoc]; exact hmul_le
    omega
  have hrem_eq : 4 * k * blks1.toNat + len2.toNat = len0.toNat := by
    rw [hlen2_toNat]
    have h1 : 4 * k * blks1.toNat = blks1.toNat * k * 4 := by
      calc 4 * k * blks1.toNat = (4 * k) * blks1.toNat := rfl
        _ = blks1.toNat * (4 * k) := Nat.mul_comm _ _
        _ = blks1.toNat * (k * 4) := by rw [Nat.mul_comm 4 k]
        _ = blks1.toNat * k * 4 := (Nat.mul_assoc _ _ _).symm
    have h2 : blks1.toNat * k * 4 ≤ len0.toNat := by
      rw [Nat.mul_assoc]; exact hmul_le
    omega
  have hlen2_lt : len2.toNat < 4 * k := by
    have hm1 : k * 4 * (len0.toNat / (k * 4)) + len0.toNat % (k * 4) = len0.toNat :=
      Nat.div_add_mod len0.toNat (k * 4)
    have hmod_lt : len0.toNat % (k * 4) < k * 4 := Nat.mod_lt _ (by omega)
    have hcomm : 4 * k * blks1.toNat = k * 4 * (len0.toNat / (k * 4)) := by
      rw [hblks_nat, Nat.mul_comm 4 k]
    omega
  have hs_blks2 := hs_blks1'.preserve_ne hwr2 hne_bl
  have hs_buf2 := hs_buf1.preserve_ne hwr2 hne_lb.symm
  have hs_crc2 := hs_crc1.preserve_ne hwr2 hne_lc.symm
  have hu_words2 := hu_words1.preserve_ne hwr2 hne_wl
  refine WPTerm.of_det (by rfl) ?_
  have he_words : PureEval prog zlibPointerConfig env m2 [] (.cast wordConstPtrTy (.var "buf"))
      (.ptr pb poff) wordConstPtrTy :=
    pureEval_cast (pureEval_var_ptr hs_buf2 (modSet_conflicts_nil _ _ _))
      (castVal_ptr_eq (el := wordConstTy) rfl (Or.inr ⟨pb, poff, rfl⟩))
  refine wp_stmt_assign_ptr hu_words2 hwords_mem hf2 he_words (Or.inr ⟨pb, poff, rfl⟩) ?_
  intro m3 hwr3 hf3 hs_words3
  have hs_blks3 := hs_blks2.preserve_ne hwr3 hne_bw
  have hs_len3 := hs_len2'.preserve_ne hwr3 hne_wl.symm
  have hs_buf3 := hs_buf2.preserve_ne hwr3 hne_wb.symm
  have hs_crc3 := hs_crc2.preserve_ne hwr3 hne_wc.symm
  refine hcont blks1 len2 m3 hf3 hblks_ge1 hlen2_lt hrem_eq hs_blks3 hs_len3 hs_words3 hs_buf3 hs_crc3 ?_
  intro b' h1 h2 h3
  rw [writeVal_blocks_ne hwr3 h2, writeVal_blocks_ne hwr2 h3, writeVal_blocks_ne hwr1 h1]

private theorem isAligned_4_add_words {blk : Block} {poff : Int64} {nWords : Nat}
    (hal : Mem.isAligned blk poff 4 = true)
    (hhi : poff.toInt + (4 * nWords : Nat) ≤ (blk.size : Int)) :
    Mem.isAligned blk (Int64.ofInt (poff.toInt + (4 * nWords : Nat))) 4 = true := by
  have hlt : poff.toInt + (4 * nWords : Nat) < 2 ^ 63 := by
    have hblk := blk.sizeLt; rw [ptrDiffLimit_val] at hblk; omega
  exact isAligned_add hal (Nat.dvd_mul_right 4 nWords) hlt

private theorem wp_stmt_decl_int {prog cfg ext Q d env innerBlks m0 outerBlks m os kcont ik}
    (hk : d.ty.unqual = .int ik) (hnc : d.ty.isConst = false) (hstat : d.isStatic = false) (hnd : d.init? = none)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw : ∀ bid m1,
      bid = m.nextBlock →
      LocalFrameMem m0 m1 (bid :: innerBlks ++ outerBlks) →
      UninitIntSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty ik →
      (∀ {nm b ty k' v}, nm ≠ d.name → IntSlot env m nm b ty k' v →
        IntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k' v) →
      (∀ {nm b ty k'}, nm ≠ d.name → UninitIntSlot env m nm b ty k' →
        UninitIntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k') →
      (∀ {nm b ty el p}, nm ≠ d.name → PtrSlot env m nm b ty el p →
        PtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el p) →
      (∀ {nm b ty el}, nm ≠ d.name → UninitPtrSlot env m nm b ty el →
        UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el) →
      WPTerm prog cfg ext Q
        (.running (.stmt .nop) ((d.name, bid, d.ty) :: env) (bid :: innerBlks) m1 os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decl d)) env innerBlks m os kcont) := by
  refine WPTerm.of_det (by rfl) ?_
  refine wp_localDecl_int_none hk hnc hstat hnd hf ?_
  intro bid m1 hbid hf1 hu hi hui hp hup
  exact WPTerm.of_det (by rfl) (hw bid m1 hbid hf1 hu hi hui hp hup)

private theorem wp_stmt_decl_ptr {prog cfg ext Q d env innerBlks m0 outerBlks m os kcont el}
    (hp : d.ty.unqual = .ptr el) (hnc : d.ty.isConst = false) (hstat : d.isStatic = false) (hnd : d.init? = none)
    (hf : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hw : ∀ bid m1,
      bid = m.nextBlock →
      LocalFrameMem m0 m1 (bid :: innerBlks ++ outerBlks) →
      UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty el →
      (∀ {nm b ty k' v}, nm ≠ d.name → IntSlot env m nm b ty k' v →
        IntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k' v) →
      (∀ {nm b ty k'}, nm ≠ d.name → UninitIntSlot env m nm b ty k' →
        UninitIntSlot ((d.name, bid, d.ty) :: env) m1 nm b ty k') →
      (∀ {nm b ty el' p}, nm ≠ d.name → PtrSlot env m nm b ty el' p →
        PtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el' p) →
      (∀ {nm b ty el'}, nm ≠ d.name → UninitPtrSlot env m nm b ty el' →
        UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 nm b ty el') →
      WPTerm prog cfg ext Q
        (.running (.stmt .nop) ((d.name, bid, d.ty) :: env) (bid :: innerBlks) m1 os kcont)) :
    WPTerm prog cfg ext Q (.running (.stmt (.decl d)) env innerBlks m os kcont) := by
  refine WPTerm.of_det (by rfl) ?_
  refine wp_localDecl_ptr_none hp hnc hstat hnd hf ?_
  intro bid m1 hbid hf1 hu hi hui hp' hup
  exact WPTerm.of_det (by rfl) (hw bid m1 hbid hf1 hu hi hui hp' hup)

private theorem pushCallParams_crc3 {tags : TypeEnv} {env0 : Env} {m m1 : Mem} {fn : FnDef}
    {base : Nat → UInt64} {callEnv : Env} {callBlks : List BlockId} {crc len : BitVec 64} {buf : Val}
    (hbuf : buf = .null ∨ ∃ pb poff, buf = .ptr pb poff)
    (hparams : fn.params =
      [{ name := "crc", ty := uLongTy },
       { name := "buf", ty := byteConstPtrTy },
       { name := "len", ty := zSizeTy }])
    (hpush : Sem.pushCallParams tags m base 0
        (fn.params.zip [.int .u64 crc, buf, .int .u64 len]) env0 [] =
      some (callEnv, callBlks, m1)) :
    ∃ b_crc b_buf b_len,
      callBlks = [b_len, b_buf, b_crc] ∧
      callEnv = ("len", b_len, zSizeTy) :: ("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0 ∧
      LocalFrameMem m m1 [b_len, b_buf, b_crc] ∧
      IntSlot callEnv m1 "crc" b_crc uLongTy .u64 crc ∧
      PtrSlot callEnv m1 "buf" b_buf byteConstPtrTy byteConstTy buf ∧
      IntSlot callEnv m1 "len" b_len zSizeTy .u64 len ∧
      b_crc ≠ b_buf ∧ b_crc ≠ b_len ∧ b_buf ≠ b_len := by
  rw [hparams] at hpush
  have hf1 : LocalFrameMem m m1 callBlks := pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨_, _, _, m2, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨_, _, _, m3, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨_, _, _, m4, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  unfold Sem.pushCallParams at hpush3
  cases hpush3
  let b_crc := m.nextBlock
  let b_buf := m2.nextBlock
  let b_len := m3.nextBlock
  have hs_crc0 : IntSlot (("crc", b_crc, uLongTy) :: env0) m2 "crc" b_crc uLongTy .u64 crc :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr0 env0
  have hne_cb_mid : b_crc ≠ m2.nextBlock := Nat.ne_of_lt hs_crc0.ne_of_lt_nextBlock
  have hs_crc1 : IntSlot (("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0)
      m3 "crc" b_crc uLongTy .u64 crc :=
    (hs_crc0.preserve_alloc rfl (by decide)).preserve_ne hwr1 hne_cb_mid
  have hs_buf1 : PtrSlot (("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0)
      m3 "buf" b_buf byteConstPtrTy byteConstTy buf :=
    PtrSlot.of_pushCallParam (el := byteConstTy) rfl rfl hbuf hwr1 _
  have hne_cl : b_crc ≠ b_len :=
    Nat.ne_of_lt (Nat.lt_trans hs_crc0.ne_of_lt_nextBlock hs_buf1.ne_of_lt_nextBlock)
  have hne_bl : b_buf ≠ b_len := Nat.ne_of_lt hs_buf1.ne_of_lt_nextBlock
  let cEnv : Env := ("len", b_len, zSizeTy) :: ("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0
  have hs_crc2 : IntSlot cEnv m1 "crc" b_crc uLongTy .u64 crc :=
    (hs_crc1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_cl
  have hs_buf2 : PtrSlot cEnv m1 "buf" b_buf byteConstPtrTy byteConstTy buf :=
    (hs_buf1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_bl
  have hs_len2 : IntSlot cEnv m1 "len" b_len zSizeTy .u64 len :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr2 _
  exact ⟨b_crc, b_buf, b_len, rfl, rfl, hf1, hs_crc2, hs_buf2, hs_len2, hne_cb_mid, hne_cl, hne_bl⟩

private theorem wp_crc_tail_8_1 {prog gEnv ext env innerBlks m0 outerBlks m os retStmt kcont Q
    b_crc ty_crc b_buf ty_buf el_buf pb poff0 b_len ty_len} {vc0 len0 : BitVec 64}
    (hf0 : LocalFrameMem m0 m (innerBlks ++ outerBlks))
    (hcrc_mem : b_crc ∈ innerBlks ++ outerBlks)
    (hbuf_mem : b_buf ∈ innerBlks ++ outerBlks)
    (hlen_mem : b_len ∈ innerBlks ++ outerBlks)
    (hne_cb : b_crc ≠ b_buf) (hne_cl : b_crc ≠ b_len) (hne_bl : b_buf ≠ b_len)
    (hs_crc0 : IntSlot env m "crc" b_crc ty_crc .u64 vc0)
    (hs_buf0 : PtrSlot env m "buf" b_buf ty_buf el_buf (.ptr pb poff0))
    (hs_len0 : IntSlot env m "len" b_len ty_len .u64 len0)
    (hel_buf : el_buf.unqual = .int .u8)
    (hr0 : len0.toNat = 0 ∨ Readable m0 (.ptr pb poff0) len0.toNat)
    (htbl0 : CrcTableValid prog gEnv m0)
    (hlu_ct : env.lookup "crc_table" = gEnv.lookup "crc_table")
    (hcont : ∀ vc2 poff2 len2 m2,
      LocalFrameMem m0 m2 (innerBlks ++ outerBlks) →
      IntSlot env m2 "crc" b_crc ty_crc .u64 vc2 →
      PtrSlot env m2 "buf" b_buf ty_buf el_buf (.ptr pb poff2) →
      IntSlot env m2 "len" b_len ty_len .u64 len2 →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt retStmt) env innerBlks m2 os (.stmts [] kcont))) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt (.whileStmt (CExpr.binary .ge (CExpr.var "len") (CExpr.lit 8)) loop8BodyStmt))
        env innerBlks m os (.stmts [.whileStmt (CExpr.var "len") loop1BodyStmt, retStmt] kcont)) := by
  rcases htbl0 with ⟨b_ct, hlu_ct0, hb_ct_lt, htbl_ct⟩
  have hlu_ct_env : env.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)) := by
    rw [hlu_ct, hlu_ct0]
  refine wp_while_len_ge_8 hf0 hcrc_mem hbuf_mem hlen_mem hne_cb hne_cl hne_bl
    hs_crc0 hs_buf0 hs_len0 hel_buf hr0 hlu_ct_env hb_ct_lt htbl_ct ?_
  intro vc1 poff1 len1 m1 hf1 hs_crc1 hs_buf1 hs_len1 _ hr1 _
  refine WPTerm.of_det (by rfl) ?_
  refine wp_while_len_tail hf1 hcrc_mem hbuf_mem hlen_mem hne_cb hne_cl hne_bl
    hs_crc1 hs_buf1 hs_len1 hel_buf hr1 hlu_ct_env hb_ct_lt htbl_ct ?_
  intro vc2 poff2 len2 m2 hf2 hs_crc2 hs_buf2 hs_len2 _
  exact WPTerm.of_det (by rfl) (hcont vc2 poff2 len2 m2 hf2 hs_crc2 hs_buf2 hs_len2)

private def Crc32BraidPre (prog : Prog) (gEnv : Env) (m : Mem) (args : List Val) : Prop :=
  ∃ (crc : BitVec 64) (pb : BlockId) (poff : Int64) (len : BitVec 64),
    args = [.int .u64 crc, .ptr pb poff, .int .u64 len] ∧
    (len.toNat = 0 ∨ Readable m (.ptr pb poff) len.toNat) ∧
    CrcTableValid prog gEnv m ∧
    CrcBraidTableValid prog gEnv m "crc_braid2_table"

theorem crc32_braid_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (ext : ExtHandler) (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_braid
      (Crc32BraidPre prog gEnv)
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨crc, pb, poff0, len0, hargs, hr0, htbl0, hbraid2_0⟩ _ hpush hcont
  subst hargs
  obtain ⟨b_crc, b_buf, b_len, hblks_eq, henv_eq, hf1, hs_crc1, hs_buf1, hs_len1,
    hne_cb, hne_cl, hne_bl⟩ :=
    pushCallParams_crc3 (Or.inr ⟨pb, poff0, rfl⟩) rfl hpush
  subst callBlks
  subst callEnv
  have hstat_cb : prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_braid.name = [] := prog_fnStatics_crc32_braid hlib
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_braid.name ++ prog.globalEnv
  let env_params : Env := ("len", b_len, zSizeTy) :: ("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0
  let ifCond : CExpr :=
    CExpr.binary .ge (CExpr.var "len")
      (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (CExpr.lit 2) (CExpr.lit 4)) (CExpr.lit 4)) (CExpr.lit 1))
  let loop8Stmt : CStmt := .whileStmt (CExpr.binary .ge (CExpr.var "len") (CExpr.lit 8)) loop8BodyStmt
  let loop1Stmt : CStmt := .whileStmt (CExpr.var "len") loop1BodyStmt
  let retStmt : CStmt := .returnStmt (some (CExpr.var "crc"))
  let bodyWrap (elseS : CStmt) : CStmt :=
      CStmt.block [
        CStmt.ifStmt ifCond
          (CStmt.block [
            CStmt.decl { name := "blks", ty := zSizeTy },
            CStmt.decl { name := "words", ty := wordConstPtrTy },
            CStmt.decl { name := "endian", ty := CTy.int .u32 },
            .whileStmt alignCondExpr loop1BodyStmt,
            .expr (.assign .eq (.var "blks")
              (.binary .div (.var "len") (CExpr.binary .mul (.lit 2) (.lit 4)).paren)),
            .expr (.assign .subEq (.var "len") (.binary .mul (.binary .mul (.var "blks") (.lit 2)) (.lit 4))),
            .expr (.assign .eq (.var "words") (.cast wordConstPtrTy (.var "buf"))),
            .expr (.assign .eq (.var "endian") (.lit 1)),
            .ifStmt (.deref (.cast (.ptr (.int .u8)) (.addrOf (.var "endian"))))
              (CStmt.block [
                CStmt.decl { name := "crc0", ty := zCrcTy },
                CStmt.decl { name := "word0", ty := zWordTy },
                CStmt.decl { name := "crc1", ty := zCrcTy },
                CStmt.decl { name := "word1", ty := zWordTy },
                .expr (.assign .eq (.var "crc0") (.cast zCrcTy (.var "crc"))),
                .expr (.assign .eq (.var "crc1") (.lit 0)),
                .whileStmt (.incDec .preDec (.var "blks"))
                  (CStmt.block [
                    .expr (.assign .eq (.var "word0") (.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0)))),
                    .expr (.assign .eq (.var "word1") (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1)))),
                    .expr (.assign .addEq (.var "words") (.lit 2)),
                    .expr (.assign .eq (.var "crc0") (crcwordExpr "crc_braid2_table" "word0")),
                    .expr (.assign .eq (.var "crc1") (crcwordExpr "crc_braid2_table" "word1"))
                  ]),
                .expr (.assign .eq (.var "crc") (.call (.var "crc_word") [.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0))])),
                .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
                  [.binary .bitXor (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1))) (.var "crc")])),
                .expr (.assign .addEq (.var "words") (.lit 2))
              ])
              (some elseS),
            .expr (.assign .eq (.var "buf") (.cast byteConstPtrTy (.var "words")))
          ])
          none,
        loop8Stmt,
        loop1Stmt,
        retStmt
      ]
  obtain ⟨elseS, hbody_eq⟩ : ∃ elseS : CStmt, Zlib.Crc32.crc32TU_fn_crc32_braid.body = bodyWrap elseS := ⟨_, rfl⟩
  rw [hbody_eq]
  let retK : Sem.Cont :=
    .stmts [loop8Stmt, loop1Stmt, retStmt]
      (.blockEnd env_params [b_len, b_buf, b_crc]
        (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc32_braid.retTy
          (bodyWrap elseS) fs ctx k))
  let joinTail : ∀ {vc poff len m_j},
      LocalFrameMem m m_j [b_len, b_buf, b_crc] →
      IntSlot env_params m_j "crc" b_crc uLongTy .u64 vc →
      PtrSlot env_params m_j "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff) →
      IntSlot env_params m_j "len" b_len zSizeTy .u64 len →
      (len.toNat = 0 ∨ Readable m (.ptr pb poff) len.toNat) →
      WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env_params [] m_j os retK) := by
    intro vc poff len m_j hf_j hs_crc_j hs_buf_j hs_len_j hr_j
    refine WPTerm.of_det (by rfl) ?_
    have hlu_ct_ep : env_params.lookup "crc_table" = gEnv.lookup "crc_table" := by
      dsimp [env_params, env0]
      rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
        hstat_cb, List.nil_append, hlib.globalEnv_eq]
    refine wp_crc_tail_8_1 (innerBlks := []) (outerBlks := [b_len, b_buf, b_crc])
      (gEnv := gEnv) hf_j (by simp) (by simp) (by simp) hne_cb hne_cl hne_bl
      hs_crc_j hs_buf_j hs_len_j rfl hr_j htbl0 hlu_ct_ep ?_
    intro vc2 poff2 len2 m2 hf2 hs_crc2 _ _
    have hcast_ret : Sem.castVal m2 Zlib.Crc32.crc32TU_fn_crc32_braid.retTy (.int .u64 vc2) =
        some (.int .u64 vc2) := by
      have h := castVal_int_eq (m := m2) (ty := Zlib.Crc32.crc32TU_fn_crc32_braid.retTy)
        (k1 := .u64) (k2 := .u64) (by simp [Zlib.Crc32.crc32TU_fn_crc32_braid, CTy.unqual]) vc2
      simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
      exact h
    refine wp_return_pure (innerBlks := []) (callBlks := [b_len, b_buf, b_crc])
      (env := env) (blks := blks) (fs := fs) (ctx := ctx) (k := k)
      (k_ret := .stmts [] (.blockEnd env_params [b_len, b_buf, b_crc]
        (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc32_braid.retTy
          (bodyWrap elseS) fs ctx k)))
      (fnRetTy := Zlib.Crc32.crc32TU_fn_crc32_braid.retTy)
      (by simp [Sem.unwindReturn, freeStack_nil]) rfl (by decide) hf2
      (pureEval_var_int hs_crc2 (modSet_conflicts_nil _ _ _)) hcast_ret ?_
    intro ret m_ret hro hret _
    exact hcont ret m_ret hro ⟨vc2, hret⟩
  refine WPTerm.of_det (by rfl) ?_
  have hge11_eval : PureEval prog zlibPointerConfig env_params m1 [] ifCond
      (.int .i32 (if 11 ≤ len0.toNat then 1#32 else 0#32)) (.int .i32) :=
    pureEval_binary_int (pureEval_var_int hs_len1 (modSet_conflicts_nil _ _ _))
      pureEval_const_11 rfl rfl (evalIntBinary_u64_ge_i32 len0 (by decide) (by decide))
  by_cases h11 : 11 ≤ len0.toNat
  · refine wp_if_pure (b := true) hge11_eval (by rw [isTruthy_int_nat (k := .i32)]; simp [h11]) ?_
    have hr0_pos : Readable m (.ptr pb poff0) len0.toNat := by
      rcases hr0 with h0 | hr
      · omega
      · exact hr
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_int (ik := .u64) (innerBlks := []) (outerBlks := [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf1 ?_
    intro b_blks m2 _ hf2 hu_blks hi2 _ hp2 _
    have hs_crc2 := hi2 (by decide) hs_crc1
    have hs_len2 := hi2 (by decide) hs_len1
    have hs_buf2 := hp2 (by decide) hs_buf1
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_ptr (el := wordConstTy) (innerBlks := [b_blks]) (outerBlks := [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf2 ?_
    intro b_words m3 _ hf3 hu_words hi3 hui3 hp3 _
    have hs_crc3 := hi3 (by decide) hs_crc2
    have hs_len3 := hi3 (by decide) hs_len2
    have hu_blks3 := hui3 (by decide) hu_blks
    have hs_buf3 := hp3 (by decide) hs_buf2
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_words, b_blks]) (outerBlks := [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf3 ?_
    intro b_end m4 _ hf4 hu_end hi4 hui4 hp4 hup4
    have hs_crc4 := hi4 (by decide) hs_crc3
    have hs_len4 := hi4 (by decide) hs_len3
    have hu_blks4 := hui4 (by decide) hu_blks3
    have hs_buf4 := hp4 (by decide) hs_buf3
    have hu_words4 := hup4 (by decide) hu_words
    let env_if : Env :=
      ("endian", b_end, CTy.int .u32) :: ("words", b_words, wordConstPtrTy) :: ("blks", b_blks, zSizeTy) :: env_params
    let blks_if : List BlockId := [b_end, b_words, b_blks]
    have hnd4 := hf4.2.2.1
    have hne_end_w : b_end ≠ b_words := nodup_getElem_ne hnd4 (i := 0) (j := 1) (by simp) (by simp) (by decide)
    have hne_end_bl : b_end ≠ b_blks := nodup_getElem_ne hnd4 (i := 0) (j := 2) (by simp) (by simp) (by decide)
    have hne_end_l : b_end ≠ b_len := nodup_getElem_ne hnd4 (i := 0) (j := 3) (by simp) (by simp) (by decide)
    have hne_end_b : b_end ≠ b_buf := nodup_getElem_ne hnd4 (i := 0) (j := 4) (by simp) (by simp) (by decide)
    have hne_end_c : b_end ≠ b_crc := nodup_getElem_ne hnd4 (i := 0) (j := 5) (by simp) (by simp) (by decide)
    have hne_w_bl : b_words ≠ b_blks := nodup_getElem_ne hnd4 (i := 1) (j := 2) (by simp) (by simp) (by decide)
    have hne_w_l : b_words ≠ b_len := nodup_getElem_ne hnd4 (i := 1) (j := 3) (by simp) (by simp) (by decide)
    have hne_w_b : b_words ≠ b_buf := nodup_getElem_ne hnd4 (i := 1) (j := 4) (by simp) (by simp) (by decide)
    have hne_w_c : b_words ≠ b_crc := nodup_getElem_ne hnd4 (i := 1) (j := 5) (by simp) (by simp) (by decide)
    have hne_bl_l : b_blks ≠ b_len := nodup_getElem_ne hnd4 (i := 2) (j := 3) (by simp) (by simp) (by decide)
    have hne_bl_b : b_blks ≠ b_buf := nodup_getElem_ne hnd4 (i := 2) (j := 4) (by simp) (by simp) (by decide)
    have hne_bl_c : b_blks ≠ b_crc := nodup_getElem_ne hnd4 (i := 2) (j := 5) (by simp) (by simp) (by decide)
    obtain ⟨b_ct, hlu_ct0, hb_ct_lt, htbl_ct⟩ := id htbl0
    have hlu_ct_if : env_if.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)) := by
      dsimp [env_if, env_params, env0]
      rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
        lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
        hstat_cb, List.nil_append, hlib.globalEnv_eq, hlu_ct0]
    refine WPTerm.of_det (by rfl) ?_
    refine wp_while_align (minBlks := 2) hf4 (by simp) (by simp) (by simp) hne_cb hne_cl hne_bl
      hs_crc4 hs_buf4 hs_len4 rfl hr0_pos (by omega) hlu_ct_if hb_ct_lt htbl_ct ?_
    intro vc5 poff5 len5 m5 blk0 hf5 hs_crc5 hs_buf5 hs_len5 hblk0_m hal5 hlen5_ge hr5 hm5_eq
    have hu_end5 : UninitIntSlot env_if m5 "endian" b_end (CTy.int .u32) .u32 := by
      rcases hu_end with ⟨h1, h2, h3, blk_e, hbe, h5, h6, h7⟩
      exact ⟨h1, h2, h3, blk_e, (hm5_eq b_end hne_end_c hne_end_b hne_end_l).trans hbe, h5, h6, h7⟩
    have hu_words5 : UninitPtrSlot env_if m5 "words" b_words wordConstPtrTy wordConstTy := by
      rcases hu_words4 with ⟨h1, h2, h3, blk_w, hbw, h5, h6, h7⟩
      exact ⟨h1, h2, h3, blk_w, (hm5_eq b_words hne_w_c hne_w_b hne_w_l).trans hbw, h5, h6, h7⟩
    have hu_blks5 : UninitIntSlot env_if m5 "blks" b_blks zSizeTy .u64 := by
      rcases hu_blks4 with ⟨h1, h2, h3, blk_bl, hbbl, h5, h6, h7⟩
      exact ⟨h1, h2, h3, blk_bl, (hm5_eq b_blks hne_bl_c hne_bl_b hne_bl_l).trans hbbl, h5, h6, h7⟩
    refine WPTerm.of_det (by rfl) ?_
    refine wp_braid_setup_blks_len_words (k := 2) (by decide) (by decide) hlen5_ge hf5
      (by simp) (by simp) (by simp)
      hne_w_bl.symm hne_bl_l hne_bl_c hne_w_l hne_w_b hne_w_c hne_bl.symm hne_cl.symm
      hne_bl_l.symm hne_bl_b.symm hu_blks5 hu_words5 hs_len5 hs_buf5 hs_crc5 ?_
    intro blks6 len6 m6 hf6 hblks6_ge1 hlen6_lt hrem6_eq hs_blks6 hs_len6 hs_words6 hs_buf6 hs_crc6 hm6_eq
    have hu_end6 : UninitIntSlot env_if m6 "endian" b_end (CTy.int .u32) .u32 := by
      rcases hu_end5 with ⟨h1, h2, h3, blk_e, hbe, h5, h6, h7⟩
      exact ⟨h1, h2, h3, blk_e, (hm6_eq b_end hne_end_bl hne_end_w hne_end_l).trans hbe, h5, h6, h7⟩
    refine WPTerm.of_det (by rfl) ?_
    refine wp_if_endian_one rfl (by simp) hf6 hu_end6 ?_
    intro m7 hf7 hs_end7 hm7_eq
    have hs_blks7 := intSlot_preserve_blocks hs_blks6 (hm7_eq b_blks hne_end_bl.symm)
    have hs_len7 := intSlot_preserve_blocks hs_len6 (hm7_eq b_len hne_end_l.symm)
    have hs_words7 := ptrSlot_preserve_blocks hs_words6 (hm7_eq b_words hne_end_w.symm)
    have hs_buf7 := ptrSlot_preserve_blocks hs_buf6 (hm7_eq b_buf hne_end_b.symm)
    have hs_crc7 := intSlot_preserve_blocks hs_crc6 (hm7_eq b_crc hne_end_c.symm)
    -- Enter `if (*(unsigned char *)&endian) { ... }`
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_int (ik := .u32) (innerBlks := []) (outerBlks := blks_if ++ [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf7 ?_
    intro b_c0 m8 _ hf8 hu_c0 hi8 _ hp8 _
    have hs_blks8 := hi8 (by decide) hs_blks7
    have hs_len8 := hi8 (by decide) hs_len7
    have hs_words8 := hp8 (by decide) hs_words7
    have hs_buf8 := hp8 (by decide) hs_buf7
    have hs_crc8 := hi8 (by decide) hs_crc7
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c0]) (outerBlks := blks_if ++ [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf8 ?_
    intro b_w0 m9 _ hf9 hu_w0 hi9 hui9 hp9 _
    have hs_blks9 := hi9 (by decide) hs_blks8
    have hs_len9 := hi9 (by decide) hs_len8
    have hu_c0_9 := hui9 (by decide) hu_c0
    have hs_words9 := hp9 (by decide) hs_words8
    have hs_buf9 := hp9 (by decide) hs_buf8
    have hs_crc9 := hi9 (by decide) hs_crc8
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_w0, b_c0]) (outerBlks := blks_if ++ [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf9 ?_
    intro b_c1 m10 _ hf10 hu_c1 hi10 hui10 hp10 _
    have hs_blks10 := hi10 (by decide) hs_blks9
    have hs_len10 := hi10 (by decide) hs_len9
    have hu_c0_10 := hui10 (by decide) hu_c0_9
    have hu_w0_10 := hui10 (by decide) hu_w0
    have hs_words10 := hp10 (by decide) hs_words9
    have hs_buf10 := hp10 (by decide) hs_buf9
    have hs_crc10 := hi10 (by decide) hs_crc9
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c1, b_w0, b_c0]) (outerBlks := blks_if ++ [b_len, b_buf, b_crc])
      rfl rfl rfl rfl hf10 ?_
    intro b_w1 m11 _ hf11 hu_w1 hi11 hui11 hp11 _
    have hs_blks11 := hi11 (by decide) hs_blks10
    have hs_len11 := hi11 (by decide) hs_len10
    have hu_c0_11 := hui11 (by decide) hu_c0_10
    have hu_w0_11 := hui11 (by decide) hu_w0_10
    have hu_c1_11 := hui11 (by decide) hu_c1
    have hs_words11 := hp11 (by decide) hs_words10
    have hs_buf11 := hp11 (by decide) hs_buf10
    have hs_crc11 := hi11 (by decide) hs_crc10
    let env_e : Env :=
      ("word1", b_w1, zWordTy) :: ("crc1", b_c1, zCrcTy) ::
      ("word0", b_w0, zWordTy) :: ("crc0", b_c0, zCrcTy) :: env_if
    let blks_e : List BlockId := [b_w1, b_c1, b_w0, b_c0]
    let outer_e : List BlockId := blks_if ++ [b_len, b_buf, b_crc]
    have hnd11 := hf11.2.2.1
    -- All blocks in `[b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]` are distinct!
    have hne_c0_blks : b_c0 ≠ b_blks := nodup_getElem_ne hnd11 (i := 3) (j := 6) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_w    : b_c0 ≠ b_words := nodup_getElem_ne hnd11 (i := 3) (j := 5) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_l    : b_c0 ≠ b_len := nodup_getElem_ne hnd11 (i := 3) (j := 7) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_b    : b_c0 ≠ b_buf := nodup_getElem_ne hnd11 (i := 3) (j := 8) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_crc  : b_c0 ≠ b_crc := nodup_getElem_ne hnd11 (i := 3) (j := 9) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_c1   : b_c0 ≠ b_c1 := nodup_getElem_ne hnd11 (i := 3) (j := 1) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_w0   : b_c0 ≠ b_w0 := nodup_getElem_ne hnd11 (i := 3) (j := 2) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c0_w1   : b_c0 ≠ b_w1 := nodup_getElem_ne hnd11 (i := 3) (j := 0) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_blks : b_c1 ≠ b_blks := nodup_getElem_ne hnd11 (i := 1) (j := 6) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_w    : b_c1 ≠ b_words := nodup_getElem_ne hnd11 (i := 1) (j := 5) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_l    : b_c1 ≠ b_len := nodup_getElem_ne hnd11 (i := 1) (j := 7) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_b    : b_c1 ≠ b_buf := nodup_getElem_ne hnd11 (i := 1) (j := 8) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_crc  : b_c1 ≠ b_crc := nodup_getElem_ne hnd11 (i := 1) (j := 9) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_w0   : b_c1 ≠ b_w0 := nodup_getElem_ne hnd11 (i := 1) (j := 2) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_c1_w1   : b_c1 ≠ b_w1 := nodup_getElem_ne hnd11 (i := 1) (j := 0) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w0_w    : b_w0 ≠ b_words := nodup_getElem_ne hnd11 (i := 2) (j := 5) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w0_blks : b_w0 ≠ b_blks := nodup_getElem_ne hnd11 (i := 2) (j := 6) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w0_l    : b_w0 ≠ b_len := nodup_getElem_ne hnd11 (i := 2) (j := 7) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w0_b    : b_w0 ≠ b_buf := nodup_getElem_ne hnd11 (i := 2) (j := 8) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w0_crc  : b_w0 ≠ b_crc := nodup_getElem_ne hnd11 (i := 2) (j := 9) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w0_w1   : b_w0 ≠ b_w1 := nodup_getElem_ne hnd11 (i := 2) (j := 0) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w1_w    : b_w1 ≠ b_words := nodup_getElem_ne hnd11 (i := 0) (j := 5) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w1_blks : b_w1 ≠ b_blks := nodup_getElem_ne hnd11 (i := 0) (j := 6) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w1_l    : b_w1 ≠ b_len := nodup_getElem_ne hnd11 (i := 0) (j := 7) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w1_b    : b_w1 ≠ b_buf := nodup_getElem_ne hnd11 (i := 0) (j := 8) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    have hne_w1_crc  : b_w1 ≠ b_crc := nodup_getElem_ne hnd11 (i := 0) (j := 9) (by simp [blks_if]) (by simp [blks_if]) (by decide)
    -- `crc0 = (z_crc_t)crc;`
    refine WPTerm.of_det (by rfl) ?_
    have he_crc0 : PureEval prog zlibPointerConfig env_e m11 [] (.cast zCrcTy (.var "crc"))
        (.int .u32 (BitVec.ofInt 32 (vc5.toNat : Int))) zCrcTy :=
      pureEval_cast (pureEval_var_int hs_crc11 (modSet_conflicts_nil _ _ _))
        (castVal_int_eq (k1 := .u64) (k2 := .u32) rfl vc5)
    refine wp_stmt_assign_int hu_c0_11 (by simp) hf11 he_crc0 ?_
    intro m12 hwr12 hf12 hs_c0_12
    have hs_blks12 := hs_blks11.preserve_ne hwr12 hne_c0_blks.symm
    have hs_len12 := hs_len11.preserve_ne hwr12 hne_c0_l.symm
    have hs_words12 := hs_words11.preserve_ne hwr12 hne_c0_w.symm
    have hs_buf12 := hs_buf11.preserve_ne hwr12 hne_c0_b.symm
    have hs_crc12 := hs_crc11.preserve_ne hwr12 hne_c0_crc.symm
    have hu_c1_12 := hu_c1_11.preserve_ne hwr12 hne_c0_c1.symm
    have hu_w0_12 := hu_w0_11.preserve_ne hwr12 hne_c0_w0.symm
    have hu_w1_12 := hu_w1.preserve_ne hwr12 hne_c0_w1.symm
    -- `crc1 = 0;`
    refine WPTerm.of_det (by rfl) ?_
    refine wp_stmt_assign_int hu_c1_12 (by simp) hf12
      (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) ?_
    intro m13 hwr13 hf13 hs_c1_13
    have hs_c0_13 := hs_c0_12.preserve_ne hwr13 hne_c0_c1
    have hs_blks13 := hs_blks12.preserve_ne hwr13 hne_c1_blks.symm
    have hs_len13 := hs_len12.preserve_ne hwr13 hne_c1_l.symm
    have hs_words13 := hs_words12.preserve_ne hwr13 hne_c1_w.symm
    have hs_buf13 := hs_buf12.preserve_ne hwr13 hne_c1_b.symm
    have hs_crc13 := hs_crc12.preserve_ne hwr13 hne_c1_crc.symm
    have hu_w0_13 := hu_w0_12.preserve_ne hwr13 hne_c1_w0.symm
    have hu_w1_13 := hu_w1_12.preserve_ne hwr13 hne_c1_w1.symm
    -- `while (--blks)`
    refine WPTerm.of_det (by rfl) ?_
    let wLoopBody : CStmt := CStmt.block [
      .expr (.assign .eq (.var "word0") (.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0)))),
      .expr (.assign .eq (.var "word1") (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1)))),
      .expr (.assign .addEq (.var "words") (.lit 2)),
      .expr (.assign .eq (.var "crc0") (crcwordExpr "crc_braid2_table" "word0")),
      .expr (.assign .eq (.var "crc1") (crcwordExpr "crc_braid2_table" "word1"))
    ]
    let InvBraid2 : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m' os' =>
      env' = env_e ∧ blks' = blks_e ∧ os' = os ∧
      ∃ (blksV : BitVec 64) (poffW : Int64) (c0v c1v : BitVec 32),
        LocalFrameMem m m' (blks_e ++ outer_e) ∧
        1 ≤ blksV.toNat ∧
        meas = blksV.toNat - 1 ∧
        IntSlot env_e m' "blks" b_blks zSizeTy .u64 blksV ∧
        PtrSlot env_e m' "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW) ∧
        IntSlot env_e m' "crc0" b_c0 zCrcTy .u32 c0v ∧
        IntSlot env_e m' "crc1" b_c1 zCrcTy .u32 c1v ∧
        IntSlot env_e m' "crc" b_crc uLongTy .u64 vc5 ∧
        IntSlot env_e m' "len" b_len zSizeTy .u64 len6 ∧
        PtrSlot env_e m' "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5) ∧
        UninitIntSlot env_e m' "word0" b_w0 zWordTy .u32 ∧
        UninitIntSlot env_e m' "word1" b_w1 zWordTy .u32 ∧
        Mem.isAligned blk0 poffW 4 = true ∧
        Readable m (.ptr pb poffW) (8 * blksV.toNat + len6.toNat)
    have hr_init : Readable m (.ptr pb poff5) (8 * blks6.toNat + len6.toNat) := by
      have hsub : 8 * blks6.toNat + len6.toNat = len5.toNat := hrem6_eq
      exact hsub ▸ hr5
    refine WPTerm.while_wf InvBraid2 (n0 := blks6.toNat - 1)
      (by dsimp [InvBraid2]; exact ⟨rfl, rfl, rfl, blks6, poff5, _, 0#32, hf13, hblks6_ge1, rfl,
        hs_blks13, hs_words13, hs_c0_13, hs_c1_13, hs_crc13, hs_len13, hs_buf13,
        hu_w0_13, hu_w1_13, hal5, hr_init⟩) ?_
    · intro meas env' blks' m' os' hinv ih
      rcases hinv with ⟨henv', hblks', hos', blksV, poffW, c0v, c1v, hf', hge1, hmeas_eq,
        hs_blks', hs_words', hs_c0', hs_c1', hs_crc', hs_len', hs_buf', hu_w0', hu_w1', halW, hrW⟩
      subst env'
      subst blks'
      subst os'
      refine wp_forCond_preDec_u64 hge1 hs_blks' (by simp [outer_e, blks_if]) hf' ?_ ?_
      · -- Exit `while (--blks)`: `blksV.toNat = 1`
        intro m_ex hblks_one hf_ex _ hm_ex_eq
        have hs_words_ex := ptrSlot_preserve_blocks hs_words' (hm_ex_eq b_words hne_w_bl)
        have hs_c0_ex := intSlot_preserve_blocks hs_c0' (hm_ex_eq b_c0 hne_c0_blks)
        have hs_c1_ex := intSlot_preserve_blocks hs_c1' (hm_ex_eq b_c1 hne_c1_blks)
        have hs_crc_ex := intSlot_preserve_blocks hs_crc' (hm_ex_eq b_crc hne_bl_c.symm)
        have hs_len_ex := intSlot_preserve_blocks hs_len' (hm_ex_eq b_len hne_bl_l.symm)
        have hs_buf_ex := ptrSlot_preserve_blocks hs_buf' (hm_ex_eq b_buf hne_bl_b.symm)
        have hrW_ex : Readable m (.ptr pb poffW) (8 + len6.toNat) := by
          have : 8 * blksV.toNat + len6.toNat = 8 + len6.toNat := by rw [hblks_one]
          exact this ▸ hrW
        have hlu_cw_e : env_e.lookup "crc_word" = none := by
          dsimp [env_e, env_if, env_params, env0]
          rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), hstat_cb, List.nil_append,
            hlib.globalEnv_eq, hlib.gEnv_lookup_none "crc_word" (by decide)]
        -- `crc = crc_word(crc0 ^ words[0]);`
        refine WPTerm.of_det (by rfl) ?_
        refine wp_call_crc_word_1 hlib hf_ex (by simp [outer_e, blks_if]) ⟨vc5, hs_crc_ex⟩ hs_c0_ex hs_words_ex
          rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl0 hf_ex) ?_
        intro vc_ex1 m_ex1 hf_ex1 hs_crc_ex1 _ hm_ex1_eq
        have hs_c1_ex1 := intSlot_preserve_blocks hs_c1_ex
          (hm_ex1_eq b_c1 hs_c1_ex.ne_of_lt_nextBlock hne_c1_crc)
        have hs_words_ex1 := ptrSlot_preserve_blocks hs_words_ex
          (hm_ex1_eq b_words hs_words_ex.ne_of_lt_nextBlock hne_w_c)
        have hs_len_ex1 := intSlot_preserve_blocks hs_len_ex
          (hm_ex1_eq b_len hs_len_ex.ne_of_lt_nextBlock hne_cl.symm)
        have hs_buf_ex1 := ptrSlot_preserve_blocks hs_buf_ex
          (hm_ex1_eq b_buf hs_buf_ex.ne_of_lt_nextBlock hne_cb.symm)
        -- `crc = crc_word(crc1 ^ words[1] ^ crc);`
        refine WPTerm.of_det (by rfl) ?_
        refine wp_call_crc_word_2 (j := 1) (by decide) hlib hf_ex1 (by simp [outer_e, blks_if]) hs_crc_ex1 hs_c1_ex1
          hs_words_ex1 rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl0 hf_ex1) ?_
        intro vc_ex2 m_ex2 hf_ex2 hs_crc_ex2 _ hm_ex2_eq
        have hs_words_ex2 := ptrSlot_preserve_blocks hs_words_ex1
          (hm_ex2_eq b_words hs_words_ex1.ne_of_lt_nextBlock hne_w_c)
        have hs_len_ex2 := intSlot_preserve_blocks hs_len_ex1
          (hm_ex2_eq b_len hs_len_ex1.ne_of_lt_nextBlock hne_cl.symm)
        have hs_buf_ex2 := ptrSlot_preserve_blocks hs_buf_ex1
          (hm_ex2_eq b_buf hs_buf_ex1.ne_of_lt_nextBlock hne_cb.symm)
        -- `words += 2;`
        refine WPTerm.of_det (by rfl) ?_
        have hsz_w : sizeofTy prog.tags wordConstTy = 4 := sizeofTy_eq_bytes (ty := wordConstTy) (k := .u32) rfl
        have hmax_w : max 1 (sizeofTy prog.tags wordConstTy) = 4 := by rw [hsz_w]; decide
        refine wp_stmt_ptr_addEq (n := 2) hs_words_ex2 (by simp [outer_e, blks_if]) hf_ex2 hrW_ex hblk0_m (by decide) (by decide)
          (by rw [hmax_w]; omega) ?_
        intro m_ex3 hwr_ex3 hf_ex3 hs_words_ex3 hrW_fin
        have hs_crc_ex3 := hs_crc_ex2.preserve_ne hwr_ex3 hne_w_c.symm
        have hs_len_ex3 := hs_len_ex2.preserve_ne hwr_ex3 hne_w_l.symm
        have hs_buf_ex3 := hs_buf_ex2.preserve_ne hwr_ex3 hne_w_b.symm
        -- Exit `if (*(unsigned char *)&endian)` block
        refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_))
        have hf_if_done : LocalFrameMem m (m_ex3.freeStack blks_e) (blks_if ++ [b_len, b_buf, b_crc]) :=
          LocalFrameMem.freeStack_sub hf_ex3
        have hnot_w_e : b_words ∉ blks_e := by
          simp only [blks_e, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_w1_w.symm, hne_c1_w.symm, hne_w0_w.symm, hne_c0_w.symm⟩
        have hnot_c_e : b_crc ∉ blks_e := by
          simp only [blks_e, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_w1_crc.symm, hne_c1_crc.symm, hne_w0_crc.symm, hne_c0_crc.symm⟩
        have hnot_l_e : b_len ∉ blks_e := by
          simp only [blks_e, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_w1_l.symm, hne_c1_l.symm, hne_w0_l.symm, hne_c0_l.symm⟩
        have hnot_b_e : b_buf ∉ blks_e := by
          simp only [blks_e, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_w1_b.symm, hne_c1_b.symm, hne_w0_b.symm, hne_c0_b.symm⟩
        let m_if_done := m_ex3.freeStack blks_e
        let poff_fin := Int64.ofInt (poffW.toInt + 2 * max 1 (sizeofTy prog.tags wordConstTy))
        have hwords_fin : PtrSlot env_if m_if_done "words" b_words wordConstPtrTy wordConstTy (.ptr pb poff_fin) :=
          ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide)
            (ptrSlot_drop_env (by decide) (hs_words_ex3.preserve_freeStack hnot_w_e))))
        have hcrc_fin : IntSlot env_if m_if_done "crc" b_crc uLongTy .u64 vc_ex2 :=
          intSlot_drop_env (by decide) (intSlot_drop_env (by decide) (intSlot_drop_env (by decide)
            (intSlot_drop_env (by decide) (hs_crc_ex3.preserve_freeStack hnot_c_e))))
        have hlen_fin : IntSlot env_if m_if_done "len" b_len zSizeTy .u64 len6 :=
          intSlot_drop_env (by decide) (intSlot_drop_env (by decide) (intSlot_drop_env (by decide)
            (intSlot_drop_env (by decide) (hs_len_ex3.preserve_freeStack hnot_l_e))))
        have hbuf_fin : PtrSlot env_if m_if_done "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5) :=
          ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide)
            (ptrSlot_drop_env (by decide) (hs_buf_ex3.preserve_freeStack hnot_b_e))))
        -- `buf = (unsigned char const *)words;`
        have he_buf_fin : PureEval prog zlibPointerConfig env_if m_if_done []
            (CExpr.cast byteConstPtrTy (CExpr.var "words")) (.ptr pb poff_fin) byteConstPtrTy :=
          pureEval_cast (pureEval_var_ptr hwords_fin (modSet_conflicts_nil _ _ _))
            (castVal_ptr_eq (el := byteConstTy) rfl (Or.inr ⟨pb, poff_fin, rfl⟩))
        refine wp_stmt_assign_ptr hbuf_fin.to_uninit (by simp) hf_if_done he_buf_fin
          (Or.inr ⟨pb, poff_fin, rfl⟩) ?_
        intro m_if2 hwr_if2 hf_if2 hs_buf_if2
        have hs_crc_if2 := hcrc_fin.preserve_ne hwr_if2 hne_cb
        have hs_len_if2 := hlen_fin.preserve_ne hwr_if2 hne_bl.symm
        -- Exit `if (len >= 11)` block
        refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
        have hf_out : LocalFrameMem m (m_if2.freeStack blks_if) [b_len, b_buf, b_crc] :=
          LocalFrameMem.freeStack_sub hf_if2
        have hnot_c_if : b_crc ∉ blks_if := by
          simp only [blks_if, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_end_c.symm, hne_w_c.symm, hne_bl_c.symm⟩
        have hnot_b_if : b_buf ∉ blks_if := by
          simp only [blks_if, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_end_b.symm, hne_w_b.symm, hne_bl_b.symm⟩
        have hnot_l_if : b_len ∉ blks_if := by
          simp only [blks_if, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_end_l.symm, hne_w_l.symm, hne_bl_l.symm⟩
        have hs_crc_out : IntSlot env_params (m_if2.freeStack blks_if) "crc" b_crc uLongTy .u64 vc_ex2 :=
          intSlot_drop_env (by decide) (intSlot_drop_env (by decide) (intSlot_drop_env (by decide)
            (hs_crc_if2.preserve_freeStack hnot_c_if)))
        have hs_buf_out : PtrSlot env_params (m_if2.freeStack blks_if) "buf" b_buf byteConstPtrTy byteConstTy
            (.ptr pb poff_fin) :=
          ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide)
            (hs_buf_if2.preserve_freeStack hnot_b_if)))
        have hs_len_out : IntSlot env_params (m_if2.freeStack blks_if) "len" b_len zSizeTy .u64 len6 :=
          intSlot_drop_env (by decide) (intSlot_drop_env (by decide) (intSlot_drop_env (by decide)
            (hs_len_if2.preserve_freeStack hnot_l_if)))
        have hr_tail : Readable m (.ptr pb poff_fin) len6.toNat := by
          have : 8 + len6.toNat - 2 * max 1 (sizeofTy prog.tags wordConstTy) = len6.toNat := by
            rw [hmax_w]; omega
          exact this ▸ hrW_fin
        exact joinTail hf_out hs_crc_out hs_buf_out hs_len_out (Or.inr hr_tail)
      · -- Step `while (--blks)`: `2 ≤ blksV.toNat`
        intro m_s hge2 hf_s hs_blks_s hm_s_eq
        have hs_words_s := ptrSlot_preserve_blocks hs_words' (hm_s_eq b_words hne_w_bl)
        have hs_c0_s := intSlot_preserve_blocks hs_c0' (hm_s_eq b_c0 hne_c0_blks)
        have hs_c1_s := intSlot_preserve_blocks hs_c1' (hm_s_eq b_c1 hne_c1_blks)
        have hs_crc_s := intSlot_preserve_blocks hs_crc' (hm_s_eq b_crc hne_bl_c.symm)
        have hs_len_s := intSlot_preserve_blocks hs_len' (hm_s_eq b_len hne_bl_l.symm)
        have hs_buf_s := ptrSlot_preserve_blocks hs_buf' (hm_s_eq b_buf hne_bl_b.symm)
        have hu_w0_s : UninitIntSlot env_e m_s "word0" b_w0 zWordTy .u32 := by
          rcases hu_w0' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_x, (hm_s_eq b_w0 hne_w0_blks).trans hbx, h5, h6, h7⟩
        have hu_w1_s : UninitIntSlot env_e m_s "word1" b_w1 zWordTy .u32 := by
          rcases hu_w1' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_x, (hm_s_eq b_w1 hne_w1_blks).trans hbx, h5, h6, h7⟩
        refine WPTerm.of_det (by rfl) ?_
        -- `word0 = crc0 ^ words[0];`
        refine wp_stmt_assign_word_xor (j := 0) (by decide) hf_s (by simp) hu_w0_s hs_c0_s hs_words_s
          rfl hrW hblk0_m halW (by omega) ?_
        intro w0v m_s1 hf_s1 hs_w0_1 hm_s1_eq
        have hs_blks_1 := intSlot_preserve_blocks hs_blks_s (hm_s1_eq b_blks hne_w0_blks.symm)
        have hs_words_1 := ptrSlot_preserve_blocks hs_words_s (hm_s1_eq b_words hne_w0_w.symm)
        have hs_c0_1 := intSlot_preserve_blocks hs_c0_s (hm_s1_eq b_c0 hne_c0_w0)
        have hs_c1_1 := intSlot_preserve_blocks hs_c1_s (hm_s1_eq b_c1 hne_c1_w0)
        have hs_crc_1 := intSlot_preserve_blocks hs_crc_s (hm_s1_eq b_crc hne_w0_crc.symm)
        have hs_len_1 := intSlot_preserve_blocks hs_len_s (hm_s1_eq b_len hne_w0_l.symm)
        have hs_buf_1 := ptrSlot_preserve_blocks hs_buf_s (hm_s1_eq b_buf hne_w0_b.symm)
        have hu_w1_1 : UninitIntSlot env_e m_s1 "word1" b_w1 zWordTy .u32 := by
          rcases hu_w1_s with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_x, (hm_s1_eq b_w1 hne_w0_w1.symm).trans hbx, h5, h6, h7⟩
        -- `word1 = crc1 ^ words[1];`
        refine WPTerm.of_det (by rfl) ?_
        refine wp_stmt_assign_word_xor (j := 1) (by decide) hf_s1 (by simp) hu_w1_1 hs_c1_1 hs_words_1
          rfl hrW hblk0_m halW (by omega) ?_
        intro w1v m_s2 hf_s2 hs_w1_2 hm_s2_eq
        have hs_blks_2 := intSlot_preserve_blocks hs_blks_1 (hm_s2_eq b_blks hne_w1_blks.symm)
        have hs_words_2 := ptrSlot_preserve_blocks hs_words_1 (hm_s2_eq b_words hne_w1_w.symm)
        have hs_c0_2 := intSlot_preserve_blocks hs_c0_1 (hm_s2_eq b_c0 hne_c0_w1)
        have hs_c1_2 := intSlot_preserve_blocks hs_c1_1 (hm_s2_eq b_c1 hne_c1_w1)
        have hs_crc_2 := intSlot_preserve_blocks hs_crc_1 (hm_s2_eq b_crc hne_w1_crc.symm)
        have hs_len_2 := intSlot_preserve_blocks hs_len_1 (hm_s2_eq b_len hne_w1_l.symm)
        have hs_buf_2 := ptrSlot_preserve_blocks hs_buf_1 (hm_s2_eq b_buf hne_w1_b.symm)
        have hs_w0_2 := intSlot_preserve_blocks hs_w0_1 (hm_s2_eq b_w0 hne_w0_w1)
        -- `words += 2;`
        refine WPTerm.of_det (by rfl) ?_
        have hsz_w : sizeofTy prog.tags wordConstTy = 4 := sizeofTy_eq_bytes (ty := wordConstTy) (k := .u32) rfl
        have hmax_w : max 1 (sizeofTy prog.tags wordConstTy) = 4 := by rw [hsz_w]; decide
        refine wp_stmt_ptr_addEq (n := 2) hs_words_2 (by simp [outer_e, blks_if]) hf_s2 hrW hblk0_m (by decide) (by decide)
          (by rw [hmax_w]; omega) ?_
        intro m_s3 hwr_s3 hf_s3 hs_words_3 hrW_next
        have hs_blks_3 := hs_blks_2.preserve_ne hwr_s3 hne_w_bl.symm
        have hs_c0_3 := hs_c0_2.preserve_ne hwr_s3 hne_c0_w
        have hs_c1_3 := hs_c1_2.preserve_ne hwr_s3 hne_c1_w
        have hs_crc_3 := hs_crc_2.preserve_ne hwr_s3 hne_w_c.symm
        have hs_len_3 := hs_len_2.preserve_ne hwr_s3 hne_w_l.symm
        have hs_buf_3 := hs_buf_2.preserve_ne hwr_s3 hne_w_b.symm
        have hs_w0_3 := hs_w0_2.preserve_ne hwr_s3 hne_w0_w
        have hs_w1_3 := hs_w1_2.preserve_ne hwr_s3 hne_w1_w
        -- `crc0 = CRCWORD(crc_braid2_table, word0);`
        refine WPTerm.of_det (by rfl) ?_
        obtain ⟨b_b2, hlu_b2_0, hb2_lt, htbl_b2⟩ := CrcBraidTableValid.of_localFrameMem hbraid2_0 hf_s3
        have hlu_b2_env : env_e.lookup "crc_braid2_table" =
            some (b_b2, .array (.array crcConstTy (some 256)) (some 4)) := by
          dsimp [env_e, env_if, env_params, env0]
          rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), hstat_cb, List.nil_append,
            hlib.globalEnv_eq, hlu_b2_0]
        refine wp_stmt_assign_crcword hf_s3 (by simp) hs_c0_3.to_uninit hs_w0_3 hlu_b2_env htbl_b2 ?_
        intro c0v' m_s4 hf_s4 hs_c0_4 hm_s4_eq
        have hs_blks_4 := intSlot_preserve_blocks hs_blks_3 (hm_s4_eq b_blks hne_c0_blks.symm)
        have hs_words_4 := ptrSlot_preserve_blocks hs_words_3 (hm_s4_eq b_words hne_c0_w.symm)
        have hs_c1_4 := intSlot_preserve_blocks hs_c1_3 (hm_s4_eq b_c1 hne_c0_c1.symm)
        have hs_crc_4 := intSlot_preserve_blocks hs_crc_3 (hm_s4_eq b_crc hne_c0_crc.symm)
        have hs_len_4 := intSlot_preserve_blocks hs_len_3 (hm_s4_eq b_len hne_c0_l.symm)
        have hs_buf_4 := ptrSlot_preserve_blocks hs_buf_3 (hm_s4_eq b_buf hne_c0_b.symm)
        have hs_w0_4 := intSlot_preserve_blocks hs_w0_3 (hm_s4_eq b_w0 hne_c0_w0.symm)
        have hs_w1_4 := intSlot_preserve_blocks hs_w1_3 (hm_s4_eq b_w1 hne_c0_w1.symm)
        -- `crc1 = CRCWORD(crc_braid2_table, word1);`
        refine WPTerm.of_det (by rfl) ?_
        obtain ⟨b_b2', hlu_b2_0', hb2_lt', htbl_b2'⟩ := CrcBraidTableValid.of_localFrameMem hbraid2_0 hf_s4
        have hlu_b2_env' : env_e.lookup "crc_braid2_table" =
            some (b_b2', .array (.array crcConstTy (some 256)) (some 4)) := by
          dsimp [env_e, env_if, env_params, env0]
          rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
            lookup_cons_ne _ (by decide), hstat_cb, List.nil_append,
            hlib.globalEnv_eq, hlu_b2_0']
        refine wp_stmt_assign_crcword hf_s4 (by simp) hs_c1_4.to_uninit hs_w1_4 hlu_b2_env' htbl_b2' ?_
        intro c1v' m_s5 hf_s5 hs_c1_5 hm_s5_eq
        have hs_blks_5 := intSlot_preserve_blocks hs_blks_4 (hm_s5_eq b_blks hne_c1_blks.symm)
        have hs_words_5 := ptrSlot_preserve_blocks hs_words_4 (hm_s5_eq b_words hne_c1_w.symm)
        have hs_c0_5 := intSlot_preserve_blocks hs_c0_4 (hm_s5_eq b_c0 hne_c0_c1)
        have hs_crc_5 := intSlot_preserve_blocks hs_crc_4 (hm_s5_eq b_crc hne_c1_crc.symm)
        have hs_len_5 := intSlot_preserve_blocks hs_len_4 (hm_s5_eq b_len hne_c1_l.symm)
        have hs_buf_5 := ptrSlot_preserve_blocks hs_buf_4 (hm_s5_eq b_buf hne_c1_b.symm)
        have hs_w0_5 := intSlot_preserve_blocks hs_w0_4 (hm_s5_eq b_w0 hne_c1_w0.symm)
        have hs_w1_5 := intSlot_preserve_blocks hs_w1_4 (hm_s5_eq b_w1 hne_c1_w1.symm)
        -- Exit `wLoopBody` block & jump to next iteration
        refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_))
        rw [freeStack_nil]
        let poffW' := Int64.ofInt (poffW.toInt + 2 * max 1 (sizeofTy prog.tags wordConstTy))
        have hpoffW'_eq : poffW' = Int64.ofInt (poffW.toInt + (4 * 2 : Nat)) := by
          dsimp [poffW']; rw [hmax_w]; rfl
        have hwords_eq : (2 : Nat) * max 1 (sizeofTy prog.tags wordConstTy) = 8 := by rw [hmax_w]
        have hhi_W : poffW.toInt + (4 * 2 : Nat) ≤ (blk0.size : Int) := by
          rcases hrW with ⟨_, _, blk', heq, hblk', hin, _⟩
          cases heq; rw [hblk0_m] at hblk'; cases hblk'; have := (inBounds_iff.mp hin).2; omega
        have halW' : Mem.isAligned blk0 poffW' 4 = true := by
          rw [hpoffW'_eq]; exact isAligned_4_add_words halW hhi_W
        have hblks_sub : (blksV - 1#64).toNat = blksV.toNat - 1 := by
          rw [BitVec.toNat_sub]; have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; have := blksV.isLt; rw [h1n]; omega
        have hge1' : 1 ≤ (blksV - 1#64).toNat := by rw [hblks_sub]; omega
        have hrem' : 8 * blksV.toNat + len6.toNat - 2 * max 1 (sizeofTy prog.tags wordConstTy) =
            8 * (blksV - 1#64).toNat + len6.toNat := by
          rw [hwords_eq, hblks_sub]; omega
        have hrW' : Readable m (.ptr pb poffW') (8 * (blksV - 1#64).toNat + len6.toNat) :=
          hrem' ▸ hrW_next
        have hmeas_lt : (blksV - 1#64).toNat - 1 < meas := by rw [hmeas_eq, hblks_sub]; omega
        exact ih ((blksV - 1#64).toNat - 1) env_e blks_e m_s5 os hmeas_lt
          ⟨rfl, rfl, rfl, blksV - 1#64, poffW', c0v', c1v', hf_s5, hge1', rfl,
            hs_blks_5, (show PtrSlot env_e m_s5 "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW') from hs_words_5),
            hs_c0_5, hs_c1_5, hs_crc_5, hs_len_5, hs_buf_5, hs_w0_5.to_uninit, hs_w1_5.to_uninit,
            halW', hrW'⟩
  · refine wp_if_pure (b := false) hge11_eval (by rw [isTruthy_int_nat (k := .i32)]; simp [h11]) ?_
    simp only [Bool.false_eq_true, ↓reduceIte, Option.getD, List.isEmpty]
    exact joinTail hf1 hs_crc1 hs_buf1 hs_len1 hr0

/-! ## 6. `crc32_z` and `crc32` -/

private def crc32ZEndianTrueStmt : CStmt :=
  CStmt.block [
    CStmt.decl { name := "crc0", ty := zCrcTy },
    CStmt.decl { name := "word0", ty := zWordTy },
    CStmt.decl { name := "crc1", ty := zCrcTy },
    CStmt.decl { name := "word1", ty := zWordTy },
    CStmt.decl { name := "crc2", ty := zCrcTy },
    CStmt.decl { name := "word2", ty := zWordTy },
    CStmt.decl { name := "crc3", ty := zCrcTy },
    CStmt.decl { name := "word3", ty := zWordTy },
    CStmt.decl { name := "crc4", ty := zCrcTy },
    CStmt.decl { name := "word4", ty := zWordTy },
    .expr (.assign .eq (.var "crc0") (.cast zCrcTy (.var "crc"))),
    .expr (.assign .eq (.var "crc1") (.lit 0)),
    .expr (.assign .eq (.var "crc2") (.lit 0)),
    .expr (.assign .eq (.var "crc3") (.lit 0)),
    .expr (.assign .eq (.var "crc4") (.lit 0)),
    .whileStmt (.incDec .preDec (.var "blks"))
      (CStmt.block [
        .expr (.assign .eq (.var "word0") (.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0)))),
        .expr (.assign .eq (.var "word1") (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1)))),
        .expr (.assign .eq (.var "word2") (.binary .bitXor (.var "crc2") ((CExpr.var "words").index (.lit 2)))),
        .expr (.assign .eq (.var "word3") (.binary .bitXor (.var "crc3") ((CExpr.var "words").index (.lit 3)))),
        .expr (.assign .eq (.var "word4") (.binary .bitXor (.var "crc4") ((CExpr.var "words").index (.lit 4)))),
        .expr (.assign .addEq (.var "words") (.lit 5)),
        .expr (.assign .eq (.var "crc0") (crcwordExpr "crc_braid5_table" "word0")),
        .expr (.assign .eq (.var "crc1") (crcwordExpr "crc_braid5_table" "word1")),
        .expr (.assign .eq (.var "crc2") (crcwordExpr "crc_braid5_table" "word2")),
        .expr (.assign .eq (.var "crc3") (crcwordExpr "crc_braid5_table" "word3")),
        .expr (.assign .eq (.var "crc4") (crcwordExpr "crc_braid5_table" "word4"))
      ]),
    .expr (.assign .eq (.var "crc") (.call (.var "crc_word") [.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0))])),
    .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
      [.binary .bitXor (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1))) (.var "crc")])),
    .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
      [.binary .bitXor (.binary .bitXor (.var "crc2") ((CExpr.var "words").index (.lit 2))) (.var "crc")])),
    .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
      [.binary .bitXor (.binary .bitXor (.var "crc3") ((CExpr.var "words").index (.lit 3))) (.var "crc")])),
    .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
      [.binary .bitXor (.binary .bitXor (.var "crc4") ((CExpr.var "words").index (.lit 4))) (.var "crc")])),
    .expr (.assign .addEq (.var "words") (.lit 5))
  ]

private abbrev braid5Blks (b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0 : BlockId) : List BlockId :=
  [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0]

private abbrev braid5Env (env_if : Env)
    (b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0 : BlockId) : Env :=
  ("word4", b_w4, zWordTy) :: ("crc4", b_c4, zCrcTy) ::
  ("word3", b_w3, zWordTy) :: ("crc3", b_c3, zCrcTy) ::
  ("word2", b_w2, zWordTy) :: ("crc2", b_c2, zCrcTy) ::
  ("word1", b_w1, zWordTy) :: ("crc1", b_c1, zCrcTy) ::
  ("word0", b_w0, zWordTy) :: ("crc0", b_c0, zCrcTy) :: env_if

private theorem wp_crc32_z_braid5_loop_exit {prog gEnv m0_g os0_g ext m0 env_if
    b_end b_words b_blks b_len b_buf b_crc b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
    pb poff5 blk0 rest kcont Q m'}
    {len6 vc5 blksV : BitVec 64} {poffW : Int64} {c0v c1v c2v c3v c4v : BitVec 32}
    (hlib : InitLibzProps prog gEnv m0_g os0_g)
    (hblk0_m : m0.blocks pb = some blk0)
    (htbl_keep : CrcTableValid prog gEnv m0)
    (hlu_cw_if : env_if.lookup "crc_word" = none)
    (hs_words' : PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW))
    (hs_c0' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc0" b_c0 zCrcTy .u32 c0v)
    (hs_c1' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc1" b_c1 zCrcTy .u32 c1v)
    (hs_c2' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc2" b_c2 zCrcTy .u32 c2v)
    (hs_c3' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc3" b_c3 zCrcTy .u32 c3v)
    (hs_c4' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc4" b_c4 zCrcTy .u32 c4v)
    (hs_crc' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc" b_crc uLongTy .u64 vc5)
    (hs_len' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "len" b_len zSizeTy .u64 len6)
    (hs_buf' : PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5))
    (halW : Mem.isAligned blk0 poffW 4 = true)
    (hrW : Readable m0 (.ptr pb poffW) (20 * blksV.toNat + len6.toNat))
    {os : OSState} {m_ex : Mem} (hblks_one : blksV.toNat = 1)
    (hf_ex : LocalFrameMem m0 m_ex
      (braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0 ++
       ([b_end, b_words, b_blks] ++ [b_len, b_buf, b_crc])))
    (hm_ex_eq : ∀ b', b' ≠ b_blks → m_ex.blocks b' = m'.blocks b')
    (hcont : ∀ (vc_fin : BitVec 64) (poff_fin : Int64) (m_fin : Mem),
      LocalFrameMem m0 m_fin ([b_end, b_words, b_blks] ++ [b_len, b_buf, b_crc]) →
      PtrSlot env_if m_fin "words" b_words wordConstPtrTy wordConstTy (.ptr pb poff_fin) →
      IntSlot env_if m_fin "crc" b_crc uLongTy .u64 vc_fin →
      IntSlot env_if m_fin "len" b_len zSizeTy .u64 len6 →
      PtrSlot env_if m_fin "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5) →
      Readable m0 (.ptr pb poff_fin) len6.toNat →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.stmt .nop) env_if [b_end, b_words, b_blks] m_fin os (.stmts rest kcont))) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt .nop)
        (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        (braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0) m_ex os
        (.stmts [
          .expr (.assign .eq (.var "crc") (.call (.var "crc_word") [.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0))])),
          .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
            [.binary .bitXor (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1))) (.var "crc")])),
          .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
            [.binary .bitXor (.binary .bitXor (.var "crc2") ((CExpr.var "words").index (.lit 2))) (.var "crc")])),
          .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
            [.binary .bitXor (.binary .bitXor (.var "crc3") ((CExpr.var "words").index (.lit 3))) (.var "crc")])),
          .expr (.assign .eq (.var "crc") (.call (.var "crc_word")
            [.binary .bitXor (.binary .bitXor (.var "crc4") ((CExpr.var "words").index (.lit 4))) (.var "crc")])),
          .expr (.assign .addEq (.var "words") (.lit 5))
        ] (.blockEnd env_if [b_end, b_words, b_blks] (.stmts rest kcont)))) := by
  let blks_e := braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
  let blks_if : List BlockId := [b_end, b_words, b_blks]
  let outer_e : List BlockId := blks_if ++ [b_len, b_buf, b_crc]
  let env_e := braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
  obtain ⟨_, h15⟩ := List.pairwise_cons.mp hf_ex.2.2.1
  obtain ⟨hc4_ne, h14⟩ := List.pairwise_cons.mp h15
  obtain ⟨_, h13⟩ := List.pairwise_cons.mp h14
  obtain ⟨hc3_ne, h12⟩ := List.pairwise_cons.mp h13
  obtain ⟨_, h11⟩ := List.pairwise_cons.mp h12
  obtain ⟨hc2_ne, h10⟩ := List.pairwise_cons.mp h11
  obtain ⟨_, h9⟩ := List.pairwise_cons.mp h10
  obtain ⟨hc1_ne, h8⟩ := List.pairwise_cons.mp h9
  obtain ⟨_, h7⟩ := List.pairwise_cons.mp h8
  obtain ⟨hc0_ne, h6⟩ := List.pairwise_cons.mp h7
  obtain ⟨_, h5⟩ := List.pairwise_cons.mp h6
  obtain ⟨hwords_ne, h4⟩ := List.pairwise_cons.mp h5
  obtain ⟨hblks_ne, h3⟩ := List.pairwise_cons.mp h4
  obtain ⟨hlen_ne, h2⟩ := List.pairwise_cons.mp h3
  obtain ⟨hbuf_ne, _⟩ := List.pairwise_cons.mp h2
  have hmem_crc : b_crc ∈ blks_e ++ outer_e := by
    change b_crc ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_words : b_words ∈ blks_e ++ outer_e := by
    change b_words ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hlu_cw_e : env_e.lookup "crc_word" = none := by
    dsimp [env_e, braid5Env]
    iterate 10 rw [lookup_cons_ne _ (by decide)]
    exact hlu_cw_if
  have hs_words_ex := ptrSlot_preserve_blocks hs_words' (hm_ex_eq _ (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c0_ex := intSlot_preserve_blocks hs_c0' (hm_ex_eq _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c1_ex := intSlot_preserve_blocks hs_c1' (hm_ex_eq _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c2_ex := intSlot_preserve_blocks hs_c2' (hm_ex_eq _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c3_ex := intSlot_preserve_blocks hs_c3' (hm_ex_eq _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_ex := intSlot_preserve_blocks hs_c4' (hm_ex_eq _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_crc_ex := intSlot_preserve_blocks hs_crc' (hm_ex_eq _ (hblks_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_len_ex := intSlot_preserve_blocks hs_len' (hm_ex_eq _ (hblks_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_buf_ex := ptrSlot_preserve_blocks hs_buf' (hm_ex_eq _ (hblks_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hrW_ex : Readable m0 (.ptr pb poffW) (20 + len6.toNat) := by
    have : 20 * blksV.toNat + len6.toNat = 20 + len6.toNat := by rw [hblks_one]
    exact this ▸ hrW
  refine WPTerm.of_det (by rfl) ?_
  refine wp_call_crc_word_1 hlib hf_ex hmem_crc ⟨vc5, hs_crc_ex⟩ hs_c0_ex hs_words_ex
    rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl_keep hf_ex) ?_
  intro vc_e1 m_e1 hf_e1 hs_crc_e1 _ hm_e1
  have hs_c1_e1 := intSlot_preserve_blocks hs_c1_ex (hm_e1 _ hs_c1_ex.ne_of_lt_nextBlock (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c2_e1 := intSlot_preserve_blocks hs_c2_ex (hm_e1 _ hs_c2_ex.ne_of_lt_nextBlock (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c3_e1 := intSlot_preserve_blocks hs_c3_ex (hm_e1 _ hs_c3_ex.ne_of_lt_nextBlock (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_e1 := intSlot_preserve_blocks hs_c4_ex (hm_e1 _ hs_c4_ex.ne_of_lt_nextBlock (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_words_e1 := ptrSlot_preserve_blocks hs_words_ex (hm_e1 _ hs_words_ex.ne_of_lt_nextBlock (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_len_e1 := intSlot_preserve_blocks hs_len_ex (hm_e1 _ hs_len_ex.ne_of_lt_nextBlock (hlen_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_buf_e1 := ptrSlot_preserve_blocks hs_buf_ex (hm_e1 _ hs_buf_ex.ne_of_lt_nextBlock (hbuf_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_call_crc_word_2 (j := 1) (by decide) hlib hf_e1 hmem_crc hs_crc_e1 hs_c1_e1
    hs_words_e1 rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl_keep hf_e1) ?_
  intro vc_e2 m_e2 hf_e2 hs_crc_e2 _ hm_e2
  have hs_c2_e2 := intSlot_preserve_blocks hs_c2_e1 (hm_e2 _ hs_c2_e1.ne_of_lt_nextBlock (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c3_e2 := intSlot_preserve_blocks hs_c3_e1 (hm_e2 _ hs_c3_e1.ne_of_lt_nextBlock (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_e2 := intSlot_preserve_blocks hs_c4_e1 (hm_e2 _ hs_c4_e1.ne_of_lt_nextBlock (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_words_e2 := ptrSlot_preserve_blocks hs_words_e1 (hm_e2 _ hs_words_e1.ne_of_lt_nextBlock (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_len_e2 := intSlot_preserve_blocks hs_len_e1 (hm_e2 _ hs_len_e1.ne_of_lt_nextBlock (hlen_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_buf_e2 := ptrSlot_preserve_blocks hs_buf_e1 (hm_e2 _ hs_buf_e1.ne_of_lt_nextBlock (hbuf_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_call_crc_word_2 (j := 2) (by decide) hlib hf_e2 hmem_crc hs_crc_e2 hs_c2_e2
    hs_words_e2 rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl_keep hf_e2) ?_
  intro vc_e3 m_e3 hf_e3 hs_crc_e3 _ hm_e3
  have hs_c3_e3 := intSlot_preserve_blocks hs_c3_e2 (hm_e3 _ hs_c3_e2.ne_of_lt_nextBlock (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_e3 := intSlot_preserve_blocks hs_c4_e2 (hm_e3 _ hs_c4_e2.ne_of_lt_nextBlock (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_words_e3 := ptrSlot_preserve_blocks hs_words_e2 (hm_e3 _ hs_words_e2.ne_of_lt_nextBlock (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_len_e3 := intSlot_preserve_blocks hs_len_e2 (hm_e3 _ hs_len_e2.ne_of_lt_nextBlock (hlen_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_buf_e3 := ptrSlot_preserve_blocks hs_buf_e2 (hm_e3 _ hs_buf_e2.ne_of_lt_nextBlock (hbuf_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_call_crc_word_2 (j := 3) (by decide) hlib hf_e3 hmem_crc hs_crc_e3 hs_c3_e3
    hs_words_e3 rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl_keep hf_e3) ?_
  intro vc_e4 m_e4 hf_e4 hs_crc_e4 _ hm_e4
  have hs_c4_e4 := intSlot_preserve_blocks hs_c4_e3 (hm_e4 _ hs_c4_e3.ne_of_lt_nextBlock (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_words_e4 := ptrSlot_preserve_blocks hs_words_e3 (hm_e4 _ hs_words_e3.ne_of_lt_nextBlock (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_len_e4 := intSlot_preserve_blocks hs_len_e3 (hm_e4 _ hs_len_e3.ne_of_lt_nextBlock (hlen_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_buf_e4 := ptrSlot_preserve_blocks hs_buf_e3 (hm_e4 _ hs_buf_e3.ne_of_lt_nextBlock (hbuf_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_call_crc_word_2 (j := 4) (by decide) hlib hf_e4 hmem_crc hs_crc_e4 hs_c4_e4
    hs_words_e4 rfl hrW_ex hblk0_m halW (by omega) hlu_cw_e (CrcTableValid.of_localFrameMem htbl_keep hf_e4) ?_
  intro vc_e5 m_e5 hf_e5 hs_crc_e5 _ hm_e5
  have hs_words_e5 := ptrSlot_preserve_blocks hs_words_e4 (hm_e5 _ hs_words_e4.ne_of_lt_nextBlock (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_len_e5 := intSlot_preserve_blocks hs_len_e4 (hm_e5 _ hs_len_e4.ne_of_lt_nextBlock (hlen_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_buf_e5 := ptrSlot_preserve_blocks hs_buf_e4 (hm_e5 _ hs_buf_e4.ne_of_lt_nextBlock (hbuf_ne b_crc (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  have hsz_w : sizeofTy prog.tags wordConstTy = 4 := sizeofTy_eq_bytes (ty := wordConstTy) (k := .u32) rfl
  have hmax_w : max 1 (sizeofTy prog.tags wordConstTy) = 4 := by rw [hsz_w]; decide
  refine wp_stmt_ptr_addEq (n := 5) hs_words_e5 hmem_words hf_e5 hrW_ex hblk0_m (by decide) (by decide)
    (by rw [hmax_w]; omega) ?_
  intro m_e6 hwr_e6 hf_e6 hs_words_e6 hrW_fin
  have hs_crc_e6 := hs_crc_e5.preserve_ne hwr_e6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  have hs_len_e6 := hs_len_e5.preserve_ne hwr_e6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  have hs_buf_e6 := hs_buf_e5.preserve_ne hwr_e6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
  have hf_if_done : LocalFrameMem m0 (m_e6.freeStack blks_e) outer_e := LocalFrameMem.freeStack_sub hf_e6
  have hdisj := (List.pairwise_append.mp hf_e6.2.2.1).2.2
  have hnot_w_e : b_words ∉ blks_e := fun hm =>
    hdisj _ hm _ (by repeat (first | exact .head _ | apply List.Mem.tail)) rfl
  have hnot_c_e : b_crc ∉ blks_e := fun hm =>
    hdisj _ hm _ (by repeat (first | exact .head _ | apply List.Mem.tail)) rfl
  have hnot_l_e : b_len ∉ blks_e := fun hm =>
    hdisj _ hm _ (by repeat (first | exact .head _ | apply List.Mem.tail)) rfl
  have hnot_b_e : b_buf ∉ blks_e := fun hm =>
    hdisj _ hm _ (by repeat (first | exact .head _ | apply List.Mem.tail)) rfl
  have hwords_fin : PtrSlot env_if (m_e6.freeStack blks_e) "words" b_words
      wordConstPtrTy wordConstTy (.ptr pb (Int64.ofInt (poffW.toInt + (5 : Int).toNat * max 1 (sizeofTy prog.tags wordConstTy)))) := by
    have h := hs_words_e6.preserve_freeStack hnot_w_e
    dsimp [env_e, braid5Env] at h
    iterate 10 replace h := ptrSlot_drop_env (by decide) h
    exact h
  have hcrc_fin : IntSlot env_if (m_e6.freeStack blks_e) "crc" b_crc uLongTy .u64 vc_e5 := by
    have h := hs_crc_e5.preserve_ne hwr_e6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
    have h' := h.preserve_freeStack hnot_c_e
    dsimp [env_e, braid5Env] at h'
    iterate 10 replace h' := intSlot_drop_env (by decide) h'
    exact h'
  have hlen_fin : IntSlot env_if (m_e6.freeStack blks_e) "len" b_len zSizeTy .u64 len6 := by
    have h' := hs_len_e6.preserve_freeStack hnot_l_e
    dsimp [env_e, braid5Env] at h'
    iterate 10 replace h' := intSlot_drop_env (by decide) h'
    exact h'
  have hbuf_fin : PtrSlot env_if (m_e6.freeStack blks_e) "buf" b_buf
      byteConstPtrTy byteConstTy (.ptr pb poff5) := by
    have h' := hs_buf_e6.preserve_freeStack hnot_b_e
    dsimp [env_e, braid5Env] at h'
    iterate 10 replace h' := ptrSlot_drop_env (by decide) h'
    exact h'
  have hr_tail : Readable m0 (.ptr pb (Int64.ofInt (poffW.toInt + (5 : Int).toNat * max 1 (sizeofTy prog.tags wordConstTy)))) len6.toNat := by
    have : 20 + len6.toNat - (5 : Int).toNat * max 1 (sizeofTy prog.tags wordConstTy) = len6.toNat := by
      rw [hmax_w]; omega
    exact this ▸ hrW_fin
  exact hcont vc_e5 _ (m_e6.freeStack blks_e) hf_if_done hwords_fin hcrc_fin hlen_fin hbuf_fin hr_tail

private theorem wp_crc32_z_braid5_loop_step {prog gEnv ext m0 env_if
    b_end b_words b_blks b_len b_buf b_crc b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
    pb poff5 blk0 k_loop Q m'}
    {len6 vc5 blksV : BitVec 64} {poffW : Int64} {c0v c1v c2v c3v c4v : BitVec 32}
    (hblk0_m : m0.blocks pb = some blk0)
    (hb5_keep : CrcBraidTableValid prog gEnv m0 "crc_braid5_table")
    (hlu_b5_if : env_if.lookup "crc_braid5_table" = gEnv.lookup "crc_braid5_table")
    (hs_words' : PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW))
    (hs_c0' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc0" b_c0 zCrcTy .u32 c0v)
    (hs_c1' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc1" b_c1 zCrcTy .u32 c1v)
    (hs_c2' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc2" b_c2 zCrcTy .u32 c2v)
    (hs_c3' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc3" b_c3 zCrcTy .u32 c3v)
    (hs_c4' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc4" b_c4 zCrcTy .u32 c4v)
    (hs_crc' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "crc" b_crc uLongTy .u64 vc5)
    (hs_len' : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "len" b_len zSizeTy .u64 len6)
    (hs_buf' : PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5))
    (hu_w0' : UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "word0" b_w0 zWordTy .u32)
    (hu_w1' : UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "word1" b_w1 zWordTy .u32)
    (hu_w2' : UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "word2" b_w2 zWordTy .u32)
    (hu_w3' : UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "word3" b_w3 zWordTy .u32)
    (hu_w4' : UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m' "word4" b_w4 zWordTy .u32)
    (halW : Mem.isAligned blk0 poffW 4 = true)
    (hrW : Readable m0 (.ptr pb poffW) (20 * blksV.toNat + len6.toNat))
    {os : OSState} {m_s : Mem} (hge2 : 2 ≤ blksV.toNat)
    (hf_s : LocalFrameMem m0 m_s
      (braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0 ++
       ([b_end, b_words, b_blks] ++ [b_len, b_buf, b_crc])))
    (hs_blks_s : IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
      m_s "blks" b_blks zSizeTy .u64 (blksV - 1#64))
    (hm_s_eq : ∀ b', b' ≠ b_blks → m_s.blocks b' = m'.blocks b')
    (hnext : ∀ (poffW' : Int64) (c0v' c1v' c2v' c3v' c4v' : BitVec 32) (m_c4 : Mem),
      LocalFrameMem m0 m_c4
        (braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0 ++
         ([b_end, b_words, b_blks] ++ [b_len, b_buf, b_crc])) →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "blks" b_blks zSizeTy .u64 (blksV - 1#64) →
      PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW') →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "crc0" b_c0 zCrcTy .u32 c0v' →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "crc1" b_c1 zCrcTy .u32 c1v' →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "crc2" b_c2 zCrcTy .u32 c2v' →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "crc3" b_c3 zCrcTy .u32 c3v' →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "crc4" b_c4 zCrcTy .u32 c4v' →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "crc" b_crc uLongTy .u64 vc5 →
      IntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "len" b_len zSizeTy .u64 len6 →
      PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5) →
      UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "word0" b_w0 zWordTy .u32 →
      UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "word1" b_w1 zWordTy .u32 →
      UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "word2" b_w2 zWordTy .u32 →
      UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "word3" b_w3 zWordTy .u32 →
      UninitIntSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "word4" b_w4 zWordTy .u32 →
      Mem.isAligned blk0 poffW' 4 = true →
      Readable m0 (.ptr pb poffW') (20 * (blksV - 1#64).toNat + len6.toNat) →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.stmt .nop)
          (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
          [] m_c4 os k_loop)) :
    WPTerm prog zlibPointerConfig ext Q
      (.running
        (.stmt (.expr (.assign .eq (.var "word0") (.binary .bitXor (.var "crc0") ((CExpr.var "words").index (.lit 0))))))
        (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        [] m_s os
        (.stmts [
          .expr (.assign .eq (.var "word1") (.binary .bitXor (.var "crc1") ((CExpr.var "words").index (.lit 1)))),
          .expr (.assign .eq (.var "word2") (.binary .bitXor (.var "crc2") ((CExpr.var "words").index (.lit 2)))),
          .expr (.assign .eq (.var "word3") (.binary .bitXor (.var "crc3") ((CExpr.var "words").index (.lit 3)))),
          .expr (.assign .eq (.var "word4") (.binary .bitXor (.var "crc4") ((CExpr.var "words").index (.lit 4)))),
          .expr (.assign .addEq (.var "words") (.lit 5)),
          .expr (.assign .eq (.var "crc0") (crcwordExpr "crc_braid5_table" "word0")),
          .expr (.assign .eq (.var "crc1") (crcwordExpr "crc_braid5_table" "word1")),
          .expr (.assign .eq (.var "crc2") (crcwordExpr "crc_braid5_table" "word2")),
          .expr (.assign .eq (.var "crc3") (crcwordExpr "crc_braid5_table" "word3")),
          .expr (.assign .eq (.var "crc4") (crcwordExpr "crc_braid5_table" "word4"))
        ] k_loop)) := by
  let blks_e := braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
  let blks_if : List BlockId := [b_end, b_words, b_blks]
  let outer_e : List BlockId := blks_if ++ [b_len, b_buf, b_crc]
  let env_e := braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
  obtain ⟨hw4_ne, h15⟩ := List.pairwise_cons.mp hf_s.2.2.1
  obtain ⟨hc4_ne, h14⟩ := List.pairwise_cons.mp h15
  obtain ⟨hw3_ne, h13⟩ := List.pairwise_cons.mp h14
  obtain ⟨hc3_ne, h12⟩ := List.pairwise_cons.mp h13
  obtain ⟨hw2_ne, h11⟩ := List.pairwise_cons.mp h12
  obtain ⟨hc2_ne, h10⟩ := List.pairwise_cons.mp h11
  obtain ⟨hw1_ne, h9⟩ := List.pairwise_cons.mp h10
  obtain ⟨hc1_ne, h8⟩ := List.pairwise_cons.mp h9
  obtain ⟨hw0_ne, h7⟩ := List.pairwise_cons.mp h8
  obtain ⟨hc0_ne, h6⟩ := List.pairwise_cons.mp h7
  obtain ⟨_, h5⟩ := List.pairwise_cons.mp h6
  obtain ⟨hwords_ne, h4⟩ := List.pairwise_cons.mp h5
  obtain ⟨hblks_ne, _⟩ := List.pairwise_cons.mp h4
  have hmem_w0 : b_w0 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_w0 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_w1 : b_w1 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_w1 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_w2 : b_w2 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_w2 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_w3 : b_w3 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_w3 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_w4 : b_w4 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_w4 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_words : b_words ∈ [] ++ (blks_e ++ outer_e) := by
    change b_words ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c0 : b_c0 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_c0 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c1 : b_c1 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_c1 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c2 : b_c2 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_c2 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c3 : b_c3 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_c3 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c4 : b_c4 ∈ [] ++ (blks_e ++ outer_e) := by
    change b_c4 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hs_words_s := ptrSlot_preserve_blocks hs_words' (hm_s_eq _ (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c0_s := intSlot_preserve_blocks hs_c0' (hm_s_eq _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c1_s := intSlot_preserve_blocks hs_c1' (hm_s_eq _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c2_s := intSlot_preserve_blocks hs_c2' (hm_s_eq _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c3_s := intSlot_preserve_blocks hs_c3' (hm_s_eq _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_s := intSlot_preserve_blocks hs_c4' (hm_s_eq _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_crc_s := intSlot_preserve_blocks hs_crc' (hm_s_eq _ (hblks_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_len_s := intSlot_preserve_blocks hs_len' (hm_s_eq _ (hblks_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_buf_s := ptrSlot_preserve_blocks hs_buf' (hm_s_eq _ (hblks_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hu_w0_s : UninitIntSlot env_e m_s "word0" b_w0 zWordTy .u32 := by
    rcases hu_w0' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_s_eq _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  have hu_w1_s : UninitIntSlot env_e m_s "word1" b_w1 zWordTy .u32 := by
    rcases hu_w1' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_s_eq _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  have hu_w2_s : UninitIntSlot env_e m_s "word2" b_w2 zWordTy .u32 := by
    rcases hu_w2' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_s_eq _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  have hu_w3_s : UninitIntSlot env_e m_s "word3" b_w3 zWordTy .u32 := by
    rcases hu_w3' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_s_eq _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  have hu_w4_s : UninitIntSlot env_e m_s "word4" b_w4 zWordTy .u32 := by
    rcases hu_w4' with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_s_eq _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  refine wp_stmt_assign_word_xor (j := 0) (by decide) hf_s hmem_w0 hu_w0_s hs_c0_s hs_words_s
    rfl hrW hblk0_m halW (by omega) ?_
  intro w0v m_s1 hf_s1 hs_w0_1 hm_s1
  have hs_words_1 := ptrSlot_preserve_blocks hs_words_s (hm_s1 _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c1_1 := intSlot_preserve_blocks hs_c1_s (hm_s1 _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c2_1 := intSlot_preserve_blocks hs_c2_s (hm_s1 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c3_1 := intSlot_preserve_blocks hs_c3_s (hm_s1 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_1 := intSlot_preserve_blocks hs_c4_s (hm_s1 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hu_w1_1 : UninitIntSlot env_e m_s1 "word1" b_w1 zWordTy .u32 := by
    rcases hu_w1_s with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_s1 _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_word_xor (j := 1) (by decide) hf_s1 hmem_w1 hu_w1_1 hs_c1_1 hs_words_1
    rfl hrW hblk0_m halW (by omega) ?_
  intro w1v m_s2 hf_s2 hs_w1_2 hm_s2
  have hs_words_2 := ptrSlot_preserve_blocks hs_words_1 (hm_s2 _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c2_2 := intSlot_preserve_blocks hs_c2_1 (hm_s2 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c3_2 := intSlot_preserve_blocks hs_c3_1 (hm_s2 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_2 := intSlot_preserve_blocks hs_c4_1 (hm_s2 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hu_w2_2 : UninitIntSlot env_e m_s2 "word2" b_w2 zWordTy .u32 := by
    rcases hu_w2_s with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    have hm := (hm_s2 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans
      (hm_s1 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
    exact ⟨h1, h2, h3, blk_x, hm.trans hbx, h5, h6, h7⟩
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_word_xor (j := 2) (by decide) hf_s2 hmem_w2 hu_w2_2 hs_c2_2 hs_words_2
    rfl hrW hblk0_m halW (by omega) ?_
  intro w2v m_s3 hf_s3 hs_w2_3 hm_s3
  have hs_words_3 := ptrSlot_preserve_blocks hs_words_2 (hm_s3 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c3_3 := intSlot_preserve_blocks hs_c3_2 (hm_s3 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_c4_3 := intSlot_preserve_blocks hs_c4_2 (hm_s3 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hu_w3_3 : UninitIntSlot env_e m_s3 "word3" b_w3 zWordTy .u32 := by
    rcases hu_w3_s with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    have hm := (hm_s3 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans
      ((hm_s2 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans
        (hm_s1 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))))
    exact ⟨h1, h2, h3, blk_x, hm.trans hbx, h5, h6, h7⟩
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_word_xor (j := 3) (by decide) hf_s3 hmem_w3 hu_w3_3 hs_c3_3 hs_words_3
    rfl hrW hblk0_m halW (by omega) ?_
  intro w3v m_s4 hf_s4 hs_w3_4 hm_s4
  have hs_words_4 := ptrSlot_preserve_blocks hs_words_3 (hm_s4 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c4_4 := intSlot_preserve_blocks hs_c4_3 (hm_s4 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hu_w4_4 : UninitIntSlot env_e m_s4 "word4" b_w4 zWordTy .u32 := by
    rcases hu_w4_s with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    have hm := (hm_s4 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans
      ((hm_s3 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans
        ((hm_s2 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans
          (hm_s1 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))))
    exact ⟨h1, h2, h3, blk_x, hm.trans hbx, h5, h6, h7⟩
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_word_xor (j := 4) (by decide) hf_s4 hmem_w4 hu_w4_4 hs_c4_4 hs_words_4
    rfl hrW hblk0_m halW (by omega) ?_
  intro w4v m_s5 hf_s5 hs_w4_5 hm_s5
  have hm_w04 : ∀ b', b' ≠ b_w0 → b' ≠ b_w1 → b' ≠ b_w2 → b' ≠ b_w3 → b' ≠ b_w4 →
      m_s5.blocks b' = m_s.blocks b' := by
    intro b' h0 h1 h2 h3 h4
    rw [hm_s5 b' h4, hm_s4 b' h3, hm_s3 b' h2, hm_s2 b' h1, hm_s1 b' h0]
  have hs_words_5 := ptrSlot_preserve_blocks hs_words_4 (hm_s5 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_blks_5 := intSlot_preserve_blocks hs_blks_s
    (hm_w04 _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c0_5 := intSlot_preserve_blocks hs_c0_s
    (hm_w04 _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c1_5 := intSlot_preserve_blocks hs_c1_s
    (hm_w04 _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c2_5 := intSlot_preserve_blocks hs_c2_s
    (hm_w04 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c3_5 := intSlot_preserve_blocks hs_c3_s
    (hm_w04 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c4_5 := intSlot_preserve_blocks hs_c4_s
    (hm_w04 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_crc_5 := intSlot_preserve_blocks hs_crc_s
    (hm_w04 _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_len_5 := intSlot_preserve_blocks hs_len_s
    (hm_w04 _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_buf_5 := ptrSlot_preserve_blocks hs_buf_s
    (hm_w04 _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_w0_5 := intSlot_preserve_blocks hs_w0_1
    (by rw [hm_s5 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
      hm_s4 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
      hm_s3 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
      hm_s2 _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_w1_5 := intSlot_preserve_blocks hs_w1_2
    (by rw [hm_s5 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
      hm_s4 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
      hm_s3 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_w2_5 := intSlot_preserve_blocks hs_w2_3
    (by rw [hm_s5 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
      hm_s4 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_w3_5 := intSlot_preserve_blocks hs_w3_4
    (hm_s5 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  -- `words += 5;`
  refine WPTerm.of_det (by rfl) ?_
  have hsz_w : sizeofTy prog.tags wordConstTy = 4 := sizeofTy_eq_bytes (ty := wordConstTy) (k := .u32) rfl
  have hmax_w : max 1 (sizeofTy prog.tags wordConstTy) = 4 := by rw [hsz_w]; decide
  refine wp_stmt_ptr_addEq (n := 5) hs_words_5 hmem_words hf_s5 hrW hblk0_m (by decide) (by decide)
    (by rw [hmax_w]; omega) ?_
  intro m_s6 hwr_s6 hf_s6 hs_words_6 hrW_next
  have hs_blks_6 := hs_blks_5.preserve_ne hwr_s6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  have hs_c0_6 := hs_c0_5.preserve_ne hwr_s6 (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_c1_6 := hs_c1_5.preserve_ne hwr_s6 (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_c2_6 := hs_c2_5.preserve_ne hwr_s6 (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_c3_6 := hs_c3_5.preserve_ne hwr_s6 (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_c4_6 := hs_c4_5.preserve_ne hwr_s6 (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_crc_6 := hs_crc_5.preserve_ne hwr_s6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  have hs_len_6 := hs_len_5.preserve_ne hwr_s6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  have hs_buf_6 := hs_buf_5.preserve_ne hwr_s6 (hwords_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
  have hs_w0_6 := hs_w0_5.preserve_ne hwr_s6 (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_w1_6 := hs_w1_5.preserve_ne hwr_s6 (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_w2_6 := hs_w2_5.preserve_ne hwr_s6 (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_w3_6 := hs_w3_5.preserve_ne hwr_s6 (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hs_w4_6 := hs_w4_5.preserve_ne hwr_s6 (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  have hlu_b5_e : env_e.lookup "crc_braid5_table" = gEnv.lookup "crc_braid5_table" := by
    dsimp [env_e, braid5Env]
    iterate 10 rw [lookup_cons_ne _ (by decide)]
    exact hlu_b5_if
  -- `crc0..4 = CRCWORD(crc_braid5_table, word0..4);`
  refine WPTerm.of_det (by rfl) ?_
  obtain ⟨b_b5_0, hlu_b5_0, _, htbl_b5_0⟩ := CrcBraidTableValid.of_localFrameMem hb5_keep hf_s6
  have hlu_b5_e0 : env_e.lookup "crc_braid5_table" = some (b_b5_0, .array (.array crcConstTy (some 256)) (some 4)) := by
    rw [hlu_b5_e, hlu_b5_0]
  refine wp_stmt_assign_crcword hf_s6 hmem_c0 hs_c0_6.to_uninit hs_w0_6 hlu_b5_e0 htbl_b5_0 ?_
  intro c0v' m_c0 hf_c0 hs_c0' hm_c0
  have hs_c1_c0 := intSlot_preserve_blocks hs_c1_6 (hm_c0 _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  have hs_w1_c0 := intSlot_preserve_blocks hs_w1_6 (hm_c0 _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  obtain ⟨b_b5_1, hlu_b5_1, _, htbl_b5_1⟩ := CrcBraidTableValid.of_localFrameMem hb5_keep hf_c0
  have hlu_b5_e1 : env_e.lookup "crc_braid5_table" = some (b_b5_1, .array (.array crcConstTy (some 256)) (some 4)) := by
    rw [hlu_b5_e, hlu_b5_1]
  refine wp_stmt_assign_crcword hf_c0 hmem_c1 hs_c1_c0.to_uninit hs_w1_c0 hlu_b5_e1 htbl_b5_1 ?_
  intro c1v' m_c1 hf_c1 hs_c1' hm_c1
  have hs_c2_c1 := intSlot_preserve_blocks hs_c2_6
    (by rw [hm_c1 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c0 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))])
  have hs_w2_c1 := intSlot_preserve_blocks hs_w2_6
    (by rw [hm_c1 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c0 _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))])
  refine WPTerm.of_det (by rfl) ?_
  obtain ⟨b_b5_2, hlu_b5_2, _, htbl_b5_2⟩ := CrcBraidTableValid.of_localFrameMem hb5_keep hf_c1
  have hlu_b5_e2 : env_e.lookup "crc_braid5_table" = some (b_b5_2, .array (.array crcConstTy (some 256)) (some 4)) := by
    rw [hlu_b5_e, hlu_b5_2]
  refine wp_stmt_assign_crcword hf_c1 hmem_c2 hs_c2_c1.to_uninit hs_w2_c1 hlu_b5_e2 htbl_b5_2 ?_
  intro c2v' m_c2 hf_c2 hs_c2' hm_c2
  have hs_c3_c2 := intSlot_preserve_blocks hs_c3_6
    (by rw [hm_c2 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c1 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c0 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))])
  have hs_w3_c2 := intSlot_preserve_blocks hs_w3_6
    (by rw [hm_c2 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c1 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c0 _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))])
  refine WPTerm.of_det (by rfl) ?_
  obtain ⟨b_b5_3, hlu_b5_3, _, htbl_b5_3⟩ := CrcBraidTableValid.of_localFrameMem hb5_keep hf_c2
  have hlu_b5_e3 : env_e.lookup "crc_braid5_table" = some (b_b5_3, .array (.array crcConstTy (some 256)) (some 4)) := by
    rw [hlu_b5_e, hlu_b5_3]
  refine wp_stmt_assign_crcword hf_c2 hmem_c3 hs_c3_c2.to_uninit hs_w3_c2 hlu_b5_e3 htbl_b5_3 ?_
  intro c3v' m_c3 hf_c3 hs_c3' hm_c3
  have hs_c4_c3 := intSlot_preserve_blocks hs_c4_6
    (by rw [hm_c3 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c2 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c1 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c0 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))])
  have hs_w4_c3 := intSlot_preserve_blocks hs_w4_6
    (by rw [hm_c3 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c2 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c1 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))),
      hm_c0 _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))])
  refine WPTerm.of_det (by rfl) ?_
  obtain ⟨b_b5_4, hlu_b5_4, _, htbl_b5_4⟩ := CrcBraidTableValid.of_localFrameMem hb5_keep hf_c3
  have hlu_b5_e4 : env_e.lookup "crc_braid5_table" = some (b_b5_4, .array (.array crcConstTy (some 256)) (some 4)) := by
    rw [hlu_b5_e, hlu_b5_4]
  refine wp_stmt_assign_crcword hf_c3 hmem_c4 hs_c4_c3.to_uninit hs_w4_c3 hlu_b5_e4 htbl_b5_4 ?_
  intro c4v' m_c4 hf_c4 hs_c4' hm_c4
  have hm_all : ∀ b', b' ≠ b_c0 → b' ≠ b_c1 → b' ≠ b_c2 → b' ≠ b_c3 → b' ≠ b_c4 →
      m_c4.blocks b' = m_s6.blocks b' := by
    intro b' h0 h1 h2 h3 h4
    rw [hm_c4 b' h4, hm_c3 b' h3, hm_c2 b' h2, hm_c1 b' h1, hm_c0 b' h0]
  have hs_blks_f := intSlot_preserve_blocks hs_blks_6
    (hm_all _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_words_f := ptrSlot_preserve_blocks hs_words_6
    (hm_all _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_c0_f := intSlot_preserve_blocks hs_c0'
    (show m_c4.blocks b_c0 = m_c0.blocks b_c0 by
      rw [hm_c4 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm_c3 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm_c2 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm_c1 _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_c1_f := intSlot_preserve_blocks hs_c1'
    (show m_c4.blocks b_c1 = m_c1.blocks b_c1 by
      rw [hm_c4 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm_c3 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm_c2 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_c2_f := intSlot_preserve_blocks hs_c2'
    (show m_c4.blocks b_c2 = m_c2.blocks b_c2 by
      rw [hm_c4 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm_c3 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_c3_f := intSlot_preserve_blocks hs_c3'
    (hm_c4 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_crc_f := intSlot_preserve_blocks hs_crc_6
    (hm_all _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_len_f := intSlot_preserve_blocks hs_len_6
    (hm_all _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_buf_f := ptrSlot_preserve_blocks hs_buf_6
    (hm_all _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_w0_f := intSlot_preserve_blocks hs_w0_6
    (hm_all _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_w1_f := intSlot_preserve_blocks hs_w1_6
    (hm_all _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_w2_f := intSlot_preserve_blocks hs_w2_6
    (hm_all _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_w3_f := intSlot_preserve_blocks hs_w3_6
    (hm_all _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_w4_f := intSlot_preserve_blocks hs_w4_6
    (hm_all _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))))
  refine WPTerm.of_det (by rfl) ?_
  let poffW' := Int64.ofInt (poffW.toInt + (Int.toNat 5) * max 1 (sizeofTy prog.tags wordConstTy))
  have hpoffW'_eq : poffW' = Int64.ofInt (poffW.toInt + (4 * 5 : Nat)) := by
    dsimp [poffW']; rw [hmax_w]; rfl
  have hwords_eq : (5 : Nat) * max 1 (sizeofTy prog.tags wordConstTy) = 20 := by rw [hmax_w]
  have hhi_W : poffW.toInt + (4 * 5 : Nat) ≤ (blk0.size : Int) := by
    rcases hrW with ⟨_, _, blk', heq, hblk', hin, _⟩
    cases heq; rw [hblk0_m] at hblk'; cases hblk'; have := (inBounds_iff.mp hin).2; omega
  have halW' : Mem.isAligned blk0 poffW' 4 = true := by
    rw [hpoffW'_eq]; exact isAligned_4_add_words halW hhi_W
  have hblks_sub : (blksV - 1#64).toNat = blksV.toNat - 1 := by
    rw [BitVec.toNat_sub]; have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; have := blksV.isLt; rw [h1n]; omega
  have hrem' : 20 * blksV.toNat + len6.toNat - 5 * max 1 (sizeofTy prog.tags wordConstTy) =
      20 * (blksV - 1#64).toNat + len6.toNat := by
    rw [hwords_eq, hblks_sub]; omega
  have hrW' : Readable m0 (.ptr pb poffW') (20 * (blksV - 1#64).toNat + len6.toNat) :=
    hrem' ▸ hrW_next
  exact hnext poffW' c0v' c1v' c2v' c3v' c4v' m_c4 hf_c4 hs_blks_f
    (show PtrSlot (braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0)
        m_c4 "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW') from hs_words_f)
    hs_c0_f hs_c1_f hs_c2_f hs_c3_f hs_c4' hs_crc_f hs_len_f hs_buf_f
    hs_w0_f.to_uninit hs_w1_f.to_uninit hs_w2_f.to_uninit hs_w3_f.to_uninit hs_w4_f.to_uninit
    halW' hrW'

private theorem wp_crc32_z_braid5_inner {prog gEnv m0_g os0_g ext m0 env_if
    b_end b_words b_blks b_len b_buf b_crc pb poff5 blk0 rest kcont Q m7}
    {blks6 len6 vc5 : BitVec 64}
    (hlib : InitLibzProps prog gEnv m0_g os0_g)
    (hf7 : LocalFrameMem m0 m7 ([b_end, b_words, b_blks] ++ [b_len, b_buf, b_crc]))
    (hblks6_ge1 : 1 ≤ blks6.toNat)
    (hs_blks7 : IntSlot env_if m7 "blks" b_blks zSizeTy .u64 blks6)
    (hs_len7 : IntSlot env_if m7 "len" b_len zSizeTy .u64 len6)
    (hs_words7 : PtrSlot env_if m7 "words" b_words wordConstPtrTy wordConstTy (.ptr pb poff5))
    (hs_buf7 : PtrSlot env_if m7 "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5))
    (hs_crc7 : IntSlot env_if m7 "crc" b_crc uLongTy .u64 vc5)
    (hal5 : Mem.isAligned blk0 poff5 4 = true)
    (hblk0_m : m0.blocks pb = some blk0)
    (hr_init : Readable m0 (.ptr pb poff5) (20 * blks6.toNat + len6.toNat))
    (htbl0 : CrcTableValid prog gEnv m0)
    (hbraid5_0 : CrcBraidTableValid prog gEnv m0 "crc_braid5_table")
    (hlu_cw_if : env_if.lookup "crc_word" = none)
    (hlu_b5_if : env_if.lookup "crc_braid5_table" = gEnv.lookup "crc_braid5_table")
    (hcont : ∀ (vc_fin : BitVec 64) (poff_fin : Int64) (m_fin : Mem),
      LocalFrameMem m0 m_fin ([b_end, b_words, b_blks] ++ [b_len, b_buf, b_crc]) →
      PtrSlot env_if m_fin "words" b_words wordConstPtrTy wordConstTy (.ptr pb poff_fin) →
      IntSlot env_if m_fin "crc" b_crc uLongTy .u64 vc_fin →
      IntSlot env_if m_fin "len" b_len zSizeTy .u64 len6 →
      PtrSlot env_if m_fin "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5) →
      Readable m0 (.ptr pb poff_fin) len6.toNat →
      WPTerm prog zlibPointerConfig ext Q
        (.running (.stmt .nop) env_if [b_end, b_words, b_blks] m_fin os (.stmts rest kcont))) :
    WPTerm prog zlibPointerConfig ext Q
      (.running (.stmt crc32ZEndianTrueStmt) env_if [b_end, b_words, b_blks] m7 os (.stmts rest kcont)) := by
  have htbl_keep : CrcTableValid prog gEnv m0 := htbl0
  have hb5_keep : CrcBraidTableValid prog gEnv m0 "crc_braid5_table" := hbraid5_0
  let blks_if : List BlockId := [b_end, b_words, b_blks]
  let outer_e : List BlockId := blks_if ++ [b_len, b_buf, b_crc]
  dsimp [crc32ZEndianTrueStmt]
  refine WPTerm.of_det (by rfl) ?_
  -- Allocate `crc0, word0, crc1, word1, crc2, word2, crc3, word3, crc4, word4`
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := []) (outerBlks := outer_e) rfl rfl rfl rfl hf7 ?_
  intro b_c0 m8 _ hf8 hu_c0 hi8 _ hp8 _
  have hs_blks8 := hi8 (by decide) hs_blks7; have hs_len8 := hi8 (by decide) hs_len7
  have hs_words8 := hp8 (by decide) hs_words7; have hs_buf8 := hp8 (by decide) hs_buf7
  have hs_crc8 := hi8 (by decide) hs_crc7
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf8 ?_
  intro b_w0 m9 _ hf9 hu_w0 hi9 hui9 hp9 _
  have hs_blks9 := hi9 (by decide) hs_blks8; have hs_len9 := hi9 (by decide) hs_len8
  have hu_c0_9 := hui9 (by decide) hu_c0; have hs_words9 := hp9 (by decide) hs_words8
  have hs_buf9 := hp9 (by decide) hs_buf8; have hs_crc9 := hi9 (by decide) hs_crc8
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf9 ?_
  intro b_c1 m10 _ hf10 hu_c1 hi10 hui10 hp10 _
  have hs_blks10 := hi10 (by decide) hs_blks9; have hs_len10 := hi10 (by decide) hs_len9
  have hu_c0_10 := hui10 (by decide) hu_c0_9; have hu_w0_10 := hui10 (by decide) hu_w0
  have hs_words10 := hp10 (by decide) hs_words9; have hs_buf10 := hp10 (by decide) hs_buf9
  have hs_crc10 := hi10 (by decide) hs_crc9
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf10 ?_
  intro b_w1 m11 _ hf11 hu_w1 hi11 hui11 hp11 _
  have hs_blks11 := hi11 (by decide) hs_blks10; have hs_len11 := hi11 (by decide) hs_len10
  have hu_c0_11 := hui11 (by decide) hu_c0_10; have hu_w0_11 := hui11 (by decide) hu_w0_10
  have hu_c1_11 := hui11 (by decide) hu_c1; have hs_words11 := hp11 (by decide) hs_words10
  have hs_buf11 := hp11 (by decide) hs_buf10; have hs_crc11 := hi11 (by decide) hs_crc10
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_w1, b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf11 ?_
  intro b_c2 m12 _ hf12 hu_c2 hi12 hui12 hp12 _
  have hs_blks12 := hi12 (by decide) hs_blks11; have hs_len12 := hi12 (by decide) hs_len11
  have hu_c0_12 := hui12 (by decide) hu_c0_11; have hu_w0_12 := hui12 (by decide) hu_w0_11
  have hu_c1_12 := hui12 (by decide) hu_c1_11; have hu_w1_12 := hui12 (by decide) hu_w1
  have hs_words12 := hp12 (by decide) hs_words11; have hs_buf12 := hp12 (by decide) hs_buf11
  have hs_crc12 := hi12 (by decide) hs_crc11
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c2, b_w1, b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf12 ?_
  intro b_w2 m13 _ hf13 hu_w2 hi13 hui13 hp13 _
  have hs_blks13 := hi13 (by decide) hs_blks12; have hs_len13 := hi13 (by decide) hs_len12
  have hu_c0_13 := hui13 (by decide) hu_c0_12; have hu_w0_13 := hui13 (by decide) hu_w0_12
  have hu_c1_13 := hui13 (by decide) hu_c1_12; have hu_w1_13 := hui13 (by decide) hu_w1_12
  have hu_c2_13 := hui13 (by decide) hu_c2; have hs_words13 := hp13 (by decide) hs_words12
  have hs_buf13 := hp13 (by decide) hs_buf12; have hs_crc13 := hi13 (by decide) hs_crc12
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_w2, b_c2, b_w1, b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf13 ?_
  intro b_c3 m14 _ hf14 hu_c3 hi14 hui14 hp14 _
  have hs_blks14 := hi14 (by decide) hs_blks13; have hs_len14 := hi14 (by decide) hs_len13
  have hu_c0_14 := hui14 (by decide) hu_c0_13; have hu_w0_14 := hui14 (by decide) hu_w0_13
  have hu_c1_14 := hui14 (by decide) hu_c1_13; have hu_w1_14 := hui14 (by decide) hu_w1_13
  have hu_c2_14 := hui14 (by decide) hu_c2_13; have hu_w2_14 := hui14 (by decide) hu_w2
  have hs_words14 := hp14 (by decide) hs_words13; have hs_buf14 := hp14 (by decide) hs_buf13
  have hs_crc14 := hi14 (by decide) hs_crc13
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf14 ?_
  intro b_w3 m15 _ hf15 hu_w3 hi15 hui15 hp15 _
  have hs_blks15 := hi15 (by decide) hs_blks14; have hs_len15 := hi15 (by decide) hs_len14
  have hu_c0_15 := hui15 (by decide) hu_c0_14; have hu_w0_15 := hui15 (by decide) hu_w0_14
  have hu_c1_15 := hui15 (by decide) hu_c1_14; have hu_w1_15 := hui15 (by decide) hu_w1_14
  have hu_c2_15 := hui15 (by decide) hu_c2_14; have hu_w2_15 := hui15 (by decide) hu_w2_14
  have hu_c3_15 := hui15 (by decide) hu_c3; have hs_words15 := hp15 (by decide) hs_words14
  have hs_buf15 := hp15 (by decide) hs_buf14; have hs_crc15 := hi15 (by decide) hs_crc14
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf15 ?_
  intro b_c4 m16 _ hf16 hu_c4 hi16 hui16 hp16 _
  have hs_blks16 := hi16 (by decide) hs_blks15; have hs_len16 := hi16 (by decide) hs_len15
  have hu_c0_16 := hui16 (by decide) hu_c0_15; have hu_w0_16 := hui16 (by decide) hu_w0_15
  have hu_c1_16 := hui16 (by decide) hu_c1_15; have hu_w1_16 := hui16 (by decide) hu_w1_15
  have hu_c2_16 := hui16 (by decide) hu_c2_15; have hu_w2_16 := hui16 (by decide) hu_w2_15
  have hu_c3_16 := hui16 (by decide) hu_c3_15; have hu_w3_16 := hui16 (by decide) hu_w3
  have hs_words16 := hp16 (by decide) hs_words15; have hs_buf16 := hp16 (by decide) hs_buf15
  have hs_crc16 := hi16 (by decide) hs_crc15
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0]) (outerBlks := outer_e) rfl rfl rfl rfl hf16 ?_
  intro b_w4 m17 _ hf17 hu_w4 hi17 hui17 hp17 _
  have hs_blks17 := hi17 (by decide) hs_blks16; have hs_len17 := hi17 (by decide) hs_len16
  have hu_c0_17 := hui17 (by decide) hu_c0_16; have hu_w0_17 := hui17 (by decide) hu_w0_16
  have hu_c1_17 := hui17 (by decide) hu_c1_16; have hu_w1_17 := hui17 (by decide) hu_w1_16
  have hu_c2_17 := hui17 (by decide) hu_c2_16; have hu_w2_17 := hui17 (by decide) hu_w2_16
  have hu_c3_17 := hui17 (by decide) hu_c3_16; have hu_w3_17 := hui17 (by decide) hu_w3_16
  have hu_c4_17 := hui17 (by decide) hu_c4
  have hs_words17 := hp17 (by decide) hs_words16; have hs_buf17 := hp17 (by decide) hs_buf16
  have hs_crc17 := hi17 (by decide) hs_crc16
  let blks_e := braid5Blks b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
  let env_e := braid5Env env_if b_w4 b_c4 b_w3 b_c3 b_w2 b_c2 b_w1 b_c1 b_w0 b_c0
  obtain ⟨hw4_ne, h15⟩ := List.pairwise_cons.mp hf17.2.2.1
  obtain ⟨hc4_ne, h14⟩ := List.pairwise_cons.mp h15
  obtain ⟨hw3_ne, h13⟩ := List.pairwise_cons.mp h14
  obtain ⟨hc3_ne, h12⟩ := List.pairwise_cons.mp h13
  obtain ⟨hw2_ne, h11⟩ := List.pairwise_cons.mp h12
  obtain ⟨hc2_ne, h10⟩ := List.pairwise_cons.mp h11
  obtain ⟨hw1_ne, h9⟩ := List.pairwise_cons.mp h10
  obtain ⟨hc1_ne, h8⟩ := List.pairwise_cons.mp h9
  obtain ⟨hw0_ne, h7⟩ := List.pairwise_cons.mp h8
  obtain ⟨hc0_ne, h6⟩ := List.pairwise_cons.mp h7
  obtain ⟨_, h5⟩ := List.pairwise_cons.mp h6
  obtain ⟨hwords_ne, h4⟩ := List.pairwise_cons.mp h5
  obtain ⟨hblks_ne, _⟩ := List.pairwise_cons.mp h4
  have hmem_c0 : b_c0 ∈ blks_e ++ outer_e := by
    change b_c0 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c1 : b_c1 ∈ blks_e ++ outer_e := by
    change b_c1 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c2 : b_c2 ∈ blks_e ++ outer_e := by
    change b_c2 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c3 : b_c3 ∈ blks_e ++ outer_e := by
    change b_c3 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_c4 : b_c4 ∈ blks_e ++ outer_e := by
    change b_c4 ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  have hmem_blks : b_blks ∈ blks_e ++ outer_e := by
    change b_blks ∈ [b_w4, b_c4, b_w3, b_c3, b_w2, b_c2, b_w1, b_c1, b_w0, b_c0, b_end, b_words, b_blks, b_len, b_buf, b_crc]
    repeat (first | exact .head _ | apply List.Mem.tail)
  -- `crc0 = (z_crc_t)crc; crc1 = 0; crc2 = 0; crc3 = 0; crc4 = 0;`
  refine WPTerm.of_det (by rfl) ?_
  have he_crc0 : PureEval prog zlibPointerConfig env_e m17 [] (.cast zCrcTy (.var "crc"))
      (.int .u32 (BitVec.ofInt 32 (vc5.toNat : Int))) zCrcTy :=
    pureEval_cast (pureEval_var_int hs_crc17 (modSet_conflicts_nil _ _ _))
      (castVal_int_eq (k1 := .u64) (k2 := .u32) rfl vc5)
  refine wp_stmt_assign_int hu_c0_17 hmem_c0 hf17 he_crc0 ?_
  intro m18 hwr18 hf18 hs_c0_18
  have hm18 : ∀ b', b' ≠ b_c0 → m18.blocks b' = m17.blocks b' := fun _ h => writeVal_blocks_ne hwr18 h
  have hu_c1_18 : UninitIntSlot env_e m18 "crc1" b_c1 zCrcTy .u32 :=
    hu_c1_17.preserve_ne hwr18 (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_int hu_c1_18 hmem_c1 hf18
    (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) ?_
  intro m19 hwr19 hf19 hs_c1_19
  have hm19 : ∀ b', b' ≠ b_c1 → m19.blocks b' = m18.blocks b' := fun _ h => writeVal_blocks_ne hwr19 h
  have hu_c2_19 : UninitIntSlot env_e m19 "crc2" b_c2 zCrcTy .u32 :=
    (hu_c2_17.preserve_ne hwr18 (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).preserve_ne hwr19
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_int hu_c2_19 hmem_c2 hf19
    (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) ?_
  intro m20 hwr20 hf20 hs_c2_20
  have hm20 : ∀ b', b' ≠ b_c2 → m20.blocks b' = m19.blocks b' := fun _ h => writeVal_blocks_ne hwr20 h
  have hu_c3_20 : UninitIntSlot env_e m20 "crc3" b_c3 zCrcTy .u32 :=
    ((hu_c3_17.preserve_ne hwr18 (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).preserve_ne hwr19
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).preserve_ne hwr20
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_int hu_c3_20 hmem_c3 hf20
    (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) ?_
  intro m21 hwr21 hf21 hs_c3_21
  have hm21 : ∀ b', b' ≠ b_c3 → m21.blocks b' = m20.blocks b' := fun _ h => writeVal_blocks_ne hwr21 h
  have hu_c4_21 : UninitIntSlot env_e m21 "crc4" b_c4 zCrcTy .u32 :=
    (((hu_c4_17.preserve_ne hwr18 (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).preserve_ne hwr19
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).preserve_ne hwr20
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).preserve_ne
      hwr21 (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
  refine WPTerm.of_det (by rfl) ?_
  refine wp_stmt_assign_int hu_c4_21 hmem_c4 hf21
    (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) ?_
  intro m22 hwr22 hf22 hs_c4_22
  have hm22 : ∀ b', b' ≠ b_c4 → m22.blocks b' = m21.blocks b' := fun _ h => writeVal_blocks_ne hwr22 h
  have hm_init_other : ∀ b', b' ≠ b_c0 → b' ≠ b_c1 → b' ≠ b_c2 → b' ≠ b_c3 → b' ≠ b_c4 →
      m22.blocks b' = m17.blocks b' := by
    intro b' h0 h1 h2 h3 h4
    rw [hm22 b' h4, hm21 b' h3, hm20 b' h2, hm19 b' h1, hm18 b' h0]
  have hs_c0_22 := intSlot_preserve_blocks hs_c0_18
    (show m22.blocks b_c0 = m18.blocks b_c0 by
      rw [hm22 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm21 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm20 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm19 _ (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_c1_22 := intSlot_preserve_blocks hs_c1_19
    (show m22.blocks b_c1 = m19.blocks b_c1 by
      rw [hm22 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm21 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm20 _ (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_c2_22 := intSlot_preserve_blocks hs_c2_20
    (show m22.blocks b_c2 = m20.blocks b_c2 by
      rw [hm22 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm,
        hm21 _ (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm])
  have hs_c3_22 := intSlot_preserve_blocks hs_c3_21
    (hm22 _ (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_blks22 := intSlot_preserve_blocks hs_blks17
    (hm_init_other _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_words22 := ptrSlot_preserve_blocks hs_words17
    (hm_init_other _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_crc22 := intSlot_preserve_blocks hs_crc17
    (hm_init_other _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_len22 := intSlot_preserve_blocks hs_len17
    (hm_init_other _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hs_buf22 := ptrSlot_preserve_blocks hs_buf17
    (hm_init_other _ (hc0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm)
  have hu_w0_22 : UninitIntSlot env_e m22 "word0" b_w0 zWordTy .u32 := by
    rcases hu_w0_17 with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_init_other _ (hw0_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm).trans hbx, h5, h6, h7⟩
  have hu_w1_22 : UninitIntSlot env_e m22 "word1" b_w1 zWordTy .u32 := by
    rcases hu_w1_17 with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_init_other _ (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw1_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm).trans hbx, h5, h6, h7⟩
  have hu_w2_22 : UninitIntSlot env_e m22 "word2" b_w2 zWordTy .u32 := by
    rcases hu_w2_17 with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_init_other _ (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw2_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm).trans hbx, h5, h6, h7⟩
  have hu_w3_22 : UninitIntSlot env_e m22 "word3" b_w3 zWordTy .u32 := by
    rcases hu_w3_17 with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_init_other _ (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw3_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hc4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail))).symm).trans hbx, h5, h6, h7⟩
  have hu_w4_22 : UninitIntSlot env_e m22 "word4" b_w4 zWordTy .u32 := by
    rcases hu_w4 with ⟨h1, h2, h3, blk_x, hbx, h5, h6, h7⟩
    exact ⟨h1, h2, h3, blk_x, (hm_init_other _ (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))
      (hw4_ne _ (by repeat (first | exact .head _ | apply List.Mem.tail)))).trans hbx, h5, h6, h7⟩
  -- `while (--blks)`
  refine WPTerm.of_det (by rfl) ?_
  let InvBraid5 : Nat → Env → List BlockId → Mem → OSState → Prop := fun meas env' blks' m' os' =>
    env' = env_e ∧ blks' = blks_e ∧ os' = os ∧
    ∃ (blksV : BitVec 64) (poffW : Int64) (c0v c1v c2v c3v c4v : BitVec 32),
      LocalFrameMem m0 m' (blks_e ++ outer_e) ∧
      1 ≤ blksV.toNat ∧
      meas = blksV.toNat - 1 ∧
      IntSlot env_e m' "blks" b_blks zSizeTy .u64 blksV ∧
      PtrSlot env_e m' "words" b_words wordConstPtrTy wordConstTy (.ptr pb poffW) ∧
      IntSlot env_e m' "crc0" b_c0 zCrcTy .u32 c0v ∧
      IntSlot env_e m' "crc1" b_c1 zCrcTy .u32 c1v ∧
      IntSlot env_e m' "crc2" b_c2 zCrcTy .u32 c2v ∧
      IntSlot env_e m' "crc3" b_c3 zCrcTy .u32 c3v ∧
      IntSlot env_e m' "crc4" b_c4 zCrcTy .u32 c4v ∧
      IntSlot env_e m' "crc" b_crc uLongTy .u64 vc5 ∧
      IntSlot env_e m' "len" b_len zSizeTy .u64 len6 ∧
      PtrSlot env_e m' "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff5) ∧
      UninitIntSlot env_e m' "word0" b_w0 zWordTy .u32 ∧
      UninitIntSlot env_e m' "word1" b_w1 zWordTy .u32 ∧
      UninitIntSlot env_e m' "word2" b_w2 zWordTy .u32 ∧
      UninitIntSlot env_e m' "word3" b_w3 zWordTy .u32 ∧
      UninitIntSlot env_e m' "word4" b_w4 zWordTy .u32 ∧
      Mem.isAligned blk0 poffW 4 = true ∧
      Readable m0 (.ptr pb poffW) (20 * blksV.toNat + len6.toNat)
  refine WPTerm.while_wf InvBraid5 (n0 := blks6.toNat - 1)
    (by dsimp [InvBraid5]; exact ⟨rfl, rfl, rfl, blks6, poff5, _, 0#32, 0#32, 0#32, 0#32, hf22,
      hblks6_ge1, rfl, hs_blks22, hs_words22, hs_c0_22, hs_c1_22, hs_c2_22, hs_c3_22, hs_c4_22,
      hs_crc22, hs_len22, hs_buf22, hu_w0_22, hu_w1_22, hu_w2_22, hu_w3_22, hu_w4_22, hal5, hr_init⟩) ?_
  · intro meas env' blks' m' os' hinv ih
    rcases hinv with ⟨henv', hblks', hos', blksV, poffW, c0v, c1v, c2v, c3v, c4v, hf', hge1, hmeas_eq,
      hs_blks', hs_words', hs_c0', hs_c1', hs_c2', hs_c3', hs_c4', hs_crc', hs_len', hs_buf',
      hu_w0', hu_w1', hu_w2', hu_w3', hu_w4', halW, hrW⟩
    subst env'
    subst blks'
    subst os'
    refine wp_forCond_preDec_u64 hge1 hs_blks' hmem_blks hf' ?_ ?_
    · -- Exit `while (--blks)`: `blksV.toNat = 1`
      intro m_ex hblks_one hf_ex _ hm_ex_eq
      exact wp_crc32_z_braid5_loop_exit hlib hblk0_m htbl_keep hlu_cw_if hs_words'
        hs_c0' hs_c1' hs_c2' hs_c3' hs_c4' hs_crc' hs_len' hs_buf'
        halW hrW hblks_one hf_ex hm_ex_eq hcont
    · -- Step `while (--blks)`: `2 ≤ blksV.toNat`
      intro m_s hge2 hf_s hs_blks_s hm_s_eq
      refine WPTerm.of_det (by rfl) ?_
      refine wp_crc32_z_braid5_loop_step hblk0_m hb5_keep hlu_b5_if hs_words'
        hs_c0' hs_c1' hs_c2' hs_c3' hs_c4' hs_crc' hs_len' hs_buf'
        hu_w0' hu_w1' hu_w2' hu_w3' hu_w4' halW hrW hge2 hf_s hs_blks_s hm_s_eq ?_
      intro poffW' c0v' c1v' c2v' c3v' c4v' m_c4 hf_c4 hs_blks_f hs_words_f
        hs_c0_f hs_c1_f hs_c2_f hs_c3_f hs_c4_f hs_crc_f hs_len_f hs_buf_f
        hu_w0_f hu_w1_f hu_w2_f hu_w3_f hu_w4_f halW' hrW'
      refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
      rw [freeStack_nil]
      have hblks_sub : (blksV - 1#64).toNat = blksV.toNat - 1 := by
        rw [BitVec.toNat_sub]; have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; have := blksV.isLt; rw [h1n]; omega
      have hge1' : 1 ≤ (blksV - 1#64).toNat := by rw [hblks_sub]; omega
      have hmeas_lt : (blksV - 1#64).toNat - 1 < meas := by rw [hmeas_eq, hblks_sub]; omega
      exact ih ((blksV - 1#64).toNat - 1) env_e blks_e m_c4 os hmeas_lt
        ⟨rfl, rfl, rfl, blksV - 1#64, poffW', c0v', c1v', c2v', c3v', c4v', hf_c4, hge1', rfl,
          hs_blks_f, hs_words_f, hs_c0_f, hs_c1_f, hs_c2_f, hs_c3_f, hs_c4_f, hs_crc_f, hs_len_f,
          hs_buf_f, hu_w0_f, hu_w1_f, hu_w2_f, hu_w3_f, hu_w4_f, halW', hrW'⟩

private def Crc32ZPre (prog : Prog) (gEnv : Env) (m : Mem) (args : List Val) : Prop :=
  ∃ (crc : BitVec 64) (buf : Val) (len : BitVec 64),
    args = [.int .u64 crc, buf, .int .u64 len] ∧
    (buf = .null ∨ ∃ pb poff, buf = .ptr pb poff) ∧
    (buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat) ∧
    CrcTableValid prog gEnv m ∧
    CrcBraidTableValid prog gEnv m "crc_braid2_table" ∧
    CrcBraidTableValid prog gEnv m "crc_braid5_table"

theorem crc32_z_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (ext : ExtHandler) (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32_z
      (Crc32ZPre prog gEnv)
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨crc, buf, len0, hargs, hbuf_ptr, hr0, htbl0, hbraid2_0, hbraid5_0⟩ _ hpush hcont
  subst hargs
  obtain ⟨b_crc, b_buf, b_len, hblks_eq, henv_eq, hf1, hs_crc1, hs_buf1, hs_len1,
    hne_cb, hne_cl, hne_bl⟩ :=
    pushCallParams_crc3 hbuf_ptr rfl hpush
  subst callBlks
  subst callEnv
  have hstat_cz : prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_z.name = [] := prog_fnStatics_crc32_z hlib
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32_z.name ++ prog.globalEnv
  let env_params : Env := ("len", b_len, zSizeTy) :: ("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0
  let nullStmt : CStmt := CStmt.ifStmt (CExpr.binary .eq (CExpr.var "buf") (CExpr.lit 0))
    (.returnStmt (some (CExpr.lit 0))) none
  let bitNotAssign : CStmt := .expr (.assign .eq (.var "crc")
    (.binary .bitAnd (CExpr.unary .bitNot (.var "crc")).paren (.lit 0xffffffff .u32 .none .hex none)))
  let ifCond : CExpr :=
    CExpr.binary .ge (CExpr.var "len")
      (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (CExpr.lit 2) (CExpr.lit 4)) (CExpr.lit 4)) (CExpr.lit 1))
  let braidCutCond : CExpr :=
    CExpr.logOr (CExpr.binary .lt (.var "len") (.lit 320))
      (CExpr.binary .lt (.var "len")
        (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (.lit 5) (.lit 4)) (.lit 4)) (.lit 1)))
  let braidCallRet : CStmt :=
    .returnStmt (some (.binary .bitXor (.call (.var "crc32_braid") [.var "crc", .var "buf", .var "len"])
      (.lit 0xffffffff .u32 .none .hex none)))
  let loop8Stmt : CStmt := .whileStmt (CExpr.binary .ge (CExpr.var "len") (CExpr.lit 8)) loop8BodyStmt
  let loop1Stmt : CStmt := .whileStmt (CExpr.var "len") loop1BodyStmt
  let retStmt : CStmt := .returnStmt (some (.binary .bitXor (.var "crc") (.lit 0xffffffff .u32 .none .hex none)))
  let bodyWrap (elseS : CStmt) : CStmt :=
      CStmt.block [
        nullStmt,
        bitNotAssign,
        CStmt.ifStmt ifCond
          (CStmt.block [
            CStmt.decl { name := "blks", ty := zSizeTy },
            CStmt.decl { name := "words", ty := wordConstPtrTy },
            CStmt.decl { name := "endian", ty := CTy.int .u32 },
            .ifStmt braidCutCond braidCallRet none,
            .whileStmt alignCondExpr loop1BodyStmt,
            .expr (.assign .eq (.var "blks")
              (.binary .div (.var "len") (CExpr.binary .mul (.lit 5) (.lit 4)).paren)),
            .expr (.assign .subEq (.var "len") (.binary .mul (.binary .mul (.var "blks") (.lit 5)) (.lit 4))),
            .expr (.assign .eq (.var "words") (.cast wordConstPtrTy (.var "buf"))),
            .expr (.assign .eq (.var "endian") (.lit 1)),
            .ifStmt (.deref (.cast (.ptr (.int .u8)) (.addrOf (.var "endian"))))
              crc32ZEndianTrueStmt (some elseS),
            .expr (.assign .eq (.var "buf") (.cast byteConstPtrTy (.var "words")))
          ])
          none,
        loop8Stmt,
        loop1Stmt,
        retStmt
      ]
  obtain ⟨elseS, hbody_eq⟩ : ∃ elseS : CStmt, Zlib.Crc32.crc32TU_fn_crc32_z.body = bodyWrap elseS := ⟨_, rfl⟩
  rw [hbody_eq]
  let retK : Sem.Cont :=
    .stmts [bitNotAssign,
        CStmt.ifStmt ifCond
          (CStmt.block [
            CStmt.decl { name := "blks", ty := zSizeTy },
            CStmt.decl { name := "words", ty := wordConstPtrTy },
            CStmt.decl { name := "endian", ty := CTy.int .u32 },
            .ifStmt braidCutCond braidCallRet none,
            .whileStmt alignCondExpr loop1BodyStmt,
            .expr (.assign .eq (.var "blks")
              (.binary .div (.var "len") (CExpr.binary .mul (.lit 5) (.lit 4)).paren)),
            .expr (.assign .subEq (.var "len") (.binary .mul (.binary .mul (.var "blks") (.lit 5)) (.lit 4))),
            .expr (.assign .eq (.var "words") (.cast wordConstPtrTy (.var "buf"))),
            .expr (.assign .eq (.var "endian") (.lit 1)),
            .ifStmt (.deref (.cast (.ptr (.int .u8)) (.addrOf (.var "endian"))))
              crc32ZEndianTrueStmt (some elseS),
            .expr (.assign .eq (.var "buf") (.cast byteConstPtrTy (.var "words")))
          ])
          none,
        loop8Stmt, loop1Stmt, retStmt]
      (.blockEnd env_params [b_len, b_buf, b_crc]
        (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc32_z.retTy
          (bodyWrap elseS) fs ctx k))
  refine WPTerm.of_det (by rfl) ?_
  rcases hbuf_ptr with rfl | ⟨pb, poff0, rfl⟩
  · -- `buf == Z_NULL`: `return 0;`
    have hnull_eval := pureEval_ptr_eq_zero (prog := prog) (cfg := zlibPointerConfig) hs_buf1 (modSet_conflicts_nil _ _ _)
    refine wp_if_pure (b := true) hnull_eval rfl ?_
    have hcast0 : Sem.castVal m1 Zlib.Crc32.crc32TU_fn_crc32_z.retTy (.int .i32 (BitVec.ofInt 32 0)) =
        some (.int .u64 0#64) :=
      castVal_int_eq (m := m1) (ty := Zlib.Crc32.crc32TU_fn_crc32_z.retTy)
        (k1 := .i32) (k2 := .u64) (by simp [Zlib.Crc32.crc32TU_fn_crc32_z, CTy.unqual]) (BitVec.ofInt 32 0)
    refine wp_return_pure (innerBlks := []) (callBlks := [b_len, b_buf, b_crc])
      (env := env) (blks := blks) (fs := fs) (ctx := ctx) (k := k) (k_ret := retK)
      (fnRetTy := Zlib.Crc32.crc32TU_fn_crc32_z.retTy)
      (by simp [retK, Sem.unwindReturn, freeStack_nil]) rfl (by decide) hf1
      (pureEval_lit (val := 0) (k := .i32) (s := .none) (r := .dec)) hcast0 ?_
    intro ret m_ret hro hret _
    exact hcont ret m_ret hro ⟨0#64, hret⟩
  · -- Non-null `buf = .ptr pb poff0`
    have hnull_eval := pureEval_ptr_eq_zero (prog := prog) (cfg := zlibPointerConfig) hs_buf1 (modSet_conflicts_nil _ _ _)
    have hr0' : len0.toNat = 0 ∨ Readable m (.ptr pb poff0) len0.toNat := by
      rcases hr0 with hnull | hrest
      · cases hnull
      · exact hrest
    refine wp_if_pure (b := false) hnull_eval rfl ?_
    dsimp only [Option.getD]
    refine WPTerm.of_det (by rfl) ?_
    -- `crc = (~crc) & 0xffffffff;`
    let vc_not : BitVec 64 := (~~~crc) &&& (0xffffffff#32).zeroExtend 64
    have he_not : PureEval prog zlibPointerConfig env_params m1 []
        (.binary .bitAnd (CExpr.unary .bitNot (.var "crc")).paren (.lit 0xffffffff .u32 .none .hex none))
        (.int .u64 vc_not) (.int .u64) :=
      pureEval_binary_int
        (pureEval_paren (pureEval_unary (pureEval_var_int hs_crc1 (modSet_conflicts_nil _ _ _))
          (evalUnary_u64_bitNot crc)))
        (pureEval_lit (val := 0xffffffff) (k := .u32) (s := .none) (r := .hex))
        rfl rfl (evalIntBinary_u64_and_u32 (~~~crc) 0xffffffff#32)
    refine wp_stmt_assign_int hs_crc1.to_uninit (by simp) hf1 he_not ?_
    intro m_not hwr_not hf_not hs_crc_not
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at hs_crc_not
    have hs_buf_not := hs_buf1.preserve_ne hwr_not hne_cb.symm
    have hs_len_not := hs_len1.preserve_ne hwr_not hne_cl.symm
    let tailK : Sem.Cont :=
      .stmts [loop8Stmt, loop1Stmt, retStmt]
        (.blockEnd env_params [b_len, b_buf, b_crc]
          (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc32_z.retTy
            (bodyWrap elseS) fs ctx k))
    let joinTail : ∀ {vc poff len m_j},
        LocalFrameMem m m_j [b_len, b_buf, b_crc] →
        IntSlot env_params m_j "crc" b_crc uLongTy .u64 vc →
        PtrSlot env_params m_j "buf" b_buf byteConstPtrTy byteConstTy (.ptr pb poff) →
        IntSlot env_params m_j "len" b_len zSizeTy .u64 len →
        (len.toNat = 0 ∨ Readable m (.ptr pb poff) len.toNat) →
        WPTerm prog zlibPointerConfig ext Q (.running (.stmt .nop) env_params [] m_j os tailK) := by
      intro vc poff len m_j hf_j hs_crc_j hs_buf_j hs_len_j hr_j
      refine WPTerm.of_det (by rfl) ?_
      have hlu_ct_ep : env_params.lookup "crc_table" = gEnv.lookup "crc_table" := by
        dsimp [env_params, env0]
        rw [lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide), lookup_cons_ne _ (by decide),
          hstat_cz, List.nil_append, hlib.globalEnv_eq]
      refine wp_crc_tail_8_1 (innerBlks := []) (outerBlks := [b_len, b_buf, b_crc])
        (gEnv := gEnv) hf_j (by simp) (by simp) (by simp) hne_cb hne_cl hne_bl
        hs_crc_j hs_buf_j hs_len_j rfl hr_j htbl0 hlu_ct_ep ?_
      intro vc2 poff2 len2 m2 hf2 hs_crc2 _ _
      let vc2' : BitVec 64 := vc2
      let mask32 : BitVec 32 := BitVec.ofInt 32 0xffffffff
      let retBv : BitVec 64 := vc2' ^^^ mask32.zeroExtend 64
      have he_ret : PureEval prog zlibPointerConfig env_params m2 []
          (.binary .bitXor (.var "crc") (.lit 0xffffffff .u32 .none .hex none))
          (.int .u64 retBv) (.int .u64) :=
        pureEval_binary_int (pureEval_var_int hs_crc2 (modSet_conflicts_nil _ _ _))
          (pureEval_lit (val := 0xffffffff) (k := .u32) (s := .none) (r := .hex))
          rfl rfl (evalIntBinary_u64_xor_u32 vc2' mask32)
      have hcast_ret : Sem.castVal m2 Zlib.Crc32.crc32TU_fn_crc32_z.retTy (.int .u64 retBv) =
          some (.int .u64 retBv) := by
        have h := castVal_int_eq (m := m2) (ty := Zlib.Crc32.crc32TU_fn_crc32_z.retTy)
          (k1 := .u64) (k2 := .u64) (by simp [Zlib.Crc32.crc32TU_fn_crc32_z, CTy.unqual]) retBv
        simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
        exact h
      refine wp_return_pure (innerBlks := []) (callBlks := [b_len, b_buf, b_crc])
        (env := env) (blks := blks) (fs := fs) (ctx := ctx) (k := k)
        (k_ret := .stmts [] (.blockEnd env_params [b_len, b_buf, b_crc]
          (.callFrame env blks Zlib.Crc32.crc32TU_fn_crc32_z.retTy
            (bodyWrap elseS) fs ctx k)))
        (fnRetTy := Zlib.Crc32.crc32TU_fn_crc32_z.retTy)
        (by simp [Sem.unwindReturn, freeStack_nil]) rfl (by decide) hf2 he_ret hcast_ret ?_
      intro ret m_ret hro hret _
      exact hcont ret m_ret hro ⟨retBv, hret⟩
    -- `if (len >= NMIN * W + W - 1)`
    refine WPTerm.of_det (by rfl) ?_
    have hge11_eval : PureEval prog zlibPointerConfig env_params m_not [] ifCond
        (.int .i32 (if 11 ≤ len0.toNat then 1#32 else 0#32)) (.int .i32) :=
      pureEval_binary_int (pureEval_var_int hs_len_not (modSet_conflicts_nil _ _ _))
        pureEval_const_11 rfl rfl (evalIntBinary_u64_ge_i32 len0 (by decide) (by decide))
    by_cases h11 : 11 ≤ len0.toNat
    · refine wp_if_pure (b := true) hge11_eval (by rw [isTruthy_int_nat (k := .i32)]; simp [h11]) ?_
      have hr0_pos : Readable m (.ptr pb poff0) len0.toNat := by
        rcases hr0' with h0 | hr
        · omega
        · exact hr
      refine WPTerm.of_det (by rfl) ?_
      refine wp_stmt_decl_int (ik := .u64) (innerBlks := []) (outerBlks := [b_len, b_buf, b_crc])
        rfl rfl rfl rfl hf_not ?_
      intro b_blks m2 _ hf2 hu_blks hi2 _ hp2 _
      have hs_crc2 := hi2 (by decide) hs_crc_not
      have hs_len2 := hi2 (by decide) hs_len_not
      have hs_buf2 := hp2 (by decide) hs_buf_not
      refine WPTerm.of_det (by rfl) ?_
      refine wp_stmt_decl_ptr (el := wordConstTy) (innerBlks := [b_blks]) (outerBlks := [b_len, b_buf, b_crc])
        rfl rfl rfl rfl hf2 ?_
      intro b_words m3 _ hf3 hu_words hi3 hui3 hp3 _
      have hs_crc3 := hi3 (by decide) hs_crc2
      have hs_len3 := hi3 (by decide) hs_len2
      have hu_blks3 := hui3 (by decide) hu_blks
      have hs_buf3 := hp3 (by decide) hs_buf2
      refine WPTerm.of_det (by rfl) ?_
      refine wp_stmt_decl_int (ik := .u32) (innerBlks := [b_words, b_blks]) (outerBlks := [b_len, b_buf, b_crc])
        rfl rfl rfl rfl hf3 ?_
      intro b_end m4 _ hf4 hu_end hi4 hui4 hp4 hup4
      have hs_crc4 := hi4 (by decide) hs_crc3
      have hs_len4 := hi4 (by decide) hs_len3
      have hu_blks4 := hui4 (by decide) hu_blks3
      have hs_buf4 := hp4 (by decide) hs_buf3
      have hu_words4 := hup4 (by decide) hu_words
      let env_if : Env :=
        ("endian", b_end, CTy.int .u32) :: ("words", b_words, wordConstPtrTy) :: ("blks", b_blks, zSizeTy) :: env_params
      let blks_if : List BlockId := [b_end, b_words, b_blks]
      have hnd4 := hf4.2.2.1
      have hne_end_w : b_end ≠ b_words := nodup_getElem_ne hnd4 (i := 0) (j := 1) (by simp) (by simp) (by decide)
      have hne_end_bl : b_end ≠ b_blks := nodup_getElem_ne hnd4 (i := 0) (j := 2) (by simp) (by simp) (by decide)
      have hne_end_l : b_end ≠ b_len := nodup_getElem_ne hnd4 (i := 0) (j := 3) (by simp) (by simp) (by decide)
      have hne_end_b : b_end ≠ b_buf := nodup_getElem_ne hnd4 (i := 0) (j := 4) (by simp) (by simp) (by decide)
      have hne_end_c : b_end ≠ b_crc := nodup_getElem_ne hnd4 (i := 0) (j := 5) (by simp) (by simp) (by decide)
      have hne_w_bl : b_words ≠ b_blks := nodup_getElem_ne hnd4 (i := 1) (j := 2) (by simp) (by simp) (by decide)
      have hne_w_l : b_words ≠ b_len := nodup_getElem_ne hnd4 (i := 1) (j := 3) (by simp) (by simp) (by decide)
      have hne_w_b : b_words ≠ b_buf := nodup_getElem_ne hnd4 (i := 1) (j := 4) (by simp) (by simp) (by decide)
      have hne_w_c : b_words ≠ b_crc := nodup_getElem_ne hnd4 (i := 1) (j := 5) (by simp) (by simp) (by decide)
      have hne_bl_l : b_blks ≠ b_len := nodup_getElem_ne hnd4 (i := 2) (j := 3) (by simp) (by simp) (by decide)
      have hne_bl_b : b_blks ≠ b_buf := nodup_getElem_ne hnd4 (i := 2) (j := 4) (by simp) (by simp) (by decide)
      have hne_bl_c : b_blks ≠ b_crc := nodup_getElem_ne hnd4 (i := 2) (j := 5) (by simp) (by simp) (by decide)
      -- `if (len < BRAID_CUT || len < N * W + W - 1)`
      refine WPTerm.of_det (by rfl) ?_
      refine WPTerm.of_det (by rfl) ?_
      refine WPTerm.of_exprPure rfl ?_
      have he_lt320 : PureEval prog zlibPointerConfig env_if m4 []
          (CExpr.binary .lt (.var "len") (.lit 320))
          (.int .i32 (if len0.toNat < 320 then 1#32 else 0#32)) (.int .i32) :=
        pureEval_binary_int (pureEval_var_int hs_len4 (modSet_conflicts_nil _ _ _))
          (pureEval_lit (val := 320) (k := .i32) (s := .none) (r := .dec))
          rfl rfl (evalIntBinary_u64_lt_i32 len0 (by decide) (by decide))
      by_cases h320 : len0.toNat < 320
      · -- `len < 320`: short-circuit `||`, `return crc32_braid(crc, buf, len) ^ 0xffffffff;`
        refine he_lt320.run ?_
        simp only [h320, ↓reduceIte]
        have hstep_or1 : Sem.stepExprPure prog zlibPointerConfig env_if m4 []
            (.ret (.rval (.int .i32 1#32) (.int .i32))
              [.logOrF (CExpr.binary .lt (.var "len")
                (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (.lit 5) (.lit 4)) (.lit 4)) (.lit 1)))]) =
            some (.ret (.rval (.int .i32 1#32) (.int .i32)) [], m4, []) := by
          unfold Sem.stepExprPure
          have ht : Sem.isTruthy (.int .i32 1#32) = some true := rfl
          simp only [ht, ↓reduceIte, bind, Option.bind, pure, Pure.pure]
          rfl
        refine WPTerm.of_exprPure hstep_or1 ?_
        have hstep_br1 (k_br : Sem.Cont) : Sem.stepDet prog zlibPointerConfig
            (.running (.expr (.ret (.rval (.int .i32 1#32) (.int .i32)) []) (.branch braidCallRet .nop) [])
              env_if blks_if m4 os k_br) =
            some (.next (.running (.stmt braidCallRet) env_if blks_if m4 os k_br)) := by
          unfold Sem.stepDet
          have ht : Sem.isTruthy (.int .i32 1#32) = some true := rfl
          simp only [ht, Option.bind, Option.map_some, ↓reduceIte]
        refine WPTerm.of_det (hstep_br1 _) ?_
        refine WPTerm.of_det (by rfl) ?_
        refine WPTerm.of_exprPure rfl ?_
        refine WPTerm.of_exprPure rfl ?_
        have hlu_cb_if : env_if.lookup "crc32_braid" = none := by
          dsimp [env_if, env_params, env0]
          iterate 6 rw [lookup_cons_ne _ (by decide)]
          rw [hstat_cz, List.nil_append, hlib.globalEnv_eq]
          exact hlib.gEnv_lookup_none "crc32_braid" (by decide)
        have henum_cb : enumConst? prog.tags "crc32_braid" = none :=
          enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc32_braid" (by decide)
        have hproto_cb := prog_fnProtos_crc32_braid hlib
        refine wp_call_var hlu_cb_if henum_cb hproto_cb ?_
        let fnTyB := CTy.fnPtr Zlib.Crc32.crc32TU_fn_crc32_braid.retTy
          (Zlib.Crc32.crc32TU_fn_crc32_braid.params.map (·.ty))
          Zlib.Crc32.crc32TU_fn_crc32_braid.variadic
        refine WPTerm.of_exprPure rfl ?_
        refine (pureEval_var_int hs_crc4 (modSet_conflicts_nil _ _ _)).run ?_
        refine WPTerm.of_exprPure rfl ?_
        refine (pureEval_var_ptr hs_buf4 (modSet_conflicts_nil _ _ _)).run ?_
        refine WPTerm.of_exprPure rfl ?_
        refine (pureEval_var_int hs_len4 (modSet_conflicts_nil _ _ _)).run ?_
        have hcoerce_cb : Sem.coerceCallArgs m4
            (Zlib.Crc32.crc32TU_fn_crc32_braid.params.map (·.ty)) false
            [(.int .u64 vc_not, uLongTy.decay),
             (.ptr pb poff0, byteConstPtrTy.decay),
             (.int .u64 len0, zSizeTy.decay)] =
            some [.int .u64 vc_not, .ptr pb poff0, .int .u64 len0] := by
          have hc1 : Sem.castVal m4 uLongTy (.int .u64 vc_not) = some (.int .u64 vc_not) := by
            have h := castVal_int_eq (m := m4) (ty := uLongTy) (k1 := .u64) (k2 := .u64) rfl vc_not
            simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
            exact h
          have hc2 : Sem.castVal m4 byteConstPtrTy (.ptr pb poff0) = some (.ptr pb poff0) :=
            castVal_ptr_eq (m := m4) (ty := byteConstPtrTy) (el := byteConstTy) rfl (Or.inr ⟨pb, poff0, rfl⟩)
          have hc3 : Sem.castVal m4 zSizeTy (.int .u64 len0) = some (.int .u64 len0) := by
            have h := castVal_int_eq (m := m4) (ty := zSizeTy) (k1 := .u64) (k2 := .u64) rfl len0
            simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
            exact h
          unfold Sem.coerceCallArgs
          simp only [Zlib.Crc32.crc32TU_fn_crc32_braid, List.map_cons, List.map_nil, Bool.false_eq_true,
            ↓reduceIte, List.length_cons, List.length_nil, beq_self_eq_true, guard_true, List.zip_cons_cons,
            List.zip_nil_right, List.mapM_cons, List.mapM_nil, hc1, hc2, hc3, bind, Option.bind, pure, Pure.pure]
        have hsimp_cb : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc32_braid.params, IsSimpleParamTy p.ty := by
          intro p hp
          simp only [Zlib.Crc32.crc32TU_fn_crc32_braid, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
        have hr_cb : Readable m4 (.ptr pb poff0) len0.toNat := Readable.of_localFrameMem hf4 hr0_pos
        refine FuncBodySpec.call (crc32_braid_spec ext hlib) (by unfold Sem.stepDet; rfl)
          (prog_fns_crc32_braid hlib) rfl rfl hcoerce_cb
          ⟨vc_not, pb, poff0, len0, rfl, Or.inr hr_cb,
            CrcTableValid.of_localFrameMem htbl0 hf4,
            CrcBraidTableValid.of_localFrameMem hbraid2_0 hf4⟩
          hsimp_cb ?_
        intro ret m_call hro_call ⟨bv_cb, hret_cb⟩
        subst hret_cb
        refine WPTerm.of_exprPure rfl ?_
        refine WPTerm.of_exprPure rfl ?_
        let bv_cb' : BitVec 64 := bv_cb
        let mask32 : BitVec 32 := BitVec.ofInt 32 0xffffffff
        let retBv : BitVec 64 := bv_cb' ^^^ mask32.zeroExtend 64
        have hbin_xor : Sem.applyBinary zlibPointerConfig prog.tags m_call .bitXor
            (.int .u64 bv_cb') Zlib.Crc32.crc32TU_fn_crc32_braid.retTy
            (.int .u32 mask32) (.int .u32) =
            some (.int .u64 retBv, .int .u64) := by
          rw [applyBinary_int (by rfl) (by rfl)]
          exact evalIntBinary_u64_xor_u32 bv_cb' mask32
        have hstep_xor : Sem.stepExprPure prog zlibPointerConfig env_if m_call []
            (.ret (.rval (.int .u32 mask32) (.int .u32))
              [.binRhsF .bitXor (.int .u64 bv_cb') Zlib.Crc32.crc32TU_fn_crc32_braid.retTy]) =
            some (.ret (.rval (.int .u64 retBv) (.int .u64)) [], m_call, []) := by
          unfold Sem.stepExprPure
          simp only [hbin_xor, Option.map_some]
        refine WPTerm.of_exprPure hstep_xor ?_
        have hcast_ret : Sem.castVal m_call (CTy.typedef "uLong" (CTy.int IntKind.u64)) (.int .u64 retBv) =
            some (.int .u64 retBv) := by
          have h := castVal_int_eq (m := m_call) (ty := CTy.typedef "uLong" (CTy.int IntKind.u64))
            (k1 := .u64) (k2 := .u64) rfl retBv
          simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
          exact h
        have hf_call : LocalFrameMem m m_call (blks_if ++ [b_len, b_buf, b_crc]) := hf4.of_roExt hro_call
        have hf_mid : LocalFrameMem m (m_call.freeStack blks_if) [b_len, b_buf, b_crc] :=
          LocalFrameMem.freeStack_sub hf_call
        have hro_fin : ROExt m ((m_call.freeStack blks_if).freeStack [b_len, b_buf, b_crc]) :=
          LocalFrameMem.roExt_freeStack hf_mid
        refine WPTerm.of_det ?_ (hcont (.int .u64 retBv) _ hro_fin ⟨retBv, rfl⟩)
        unfold Sem.stepDet
        simp only [Sem.Cont.topRetTy, Zlib.Crc32.crc32TU_fn_crc32_z, CTy.isVoid, CTy.unqual,
          Bool.false_eq_true, ↓reduceIte, Sem.unwindReturn, freeStack_nil, hcast_ret, Option.bind, Option.map_some]
      · -- `320 ≤ len0.toNat`: 5-way braid path
        have h23 : ¬ len0.toNat < 23 := by omega
        refine he_lt320.run ?_
        simp only [h320, ↓reduceIte]
        have hstep_or1 : Sem.stepExprPure prog zlibPointerConfig env_if m4 []
            (.ret (.rval (.int .i32 0#32) (.int .i32))
              [.logOrF (CExpr.binary .lt (.var "len")
                (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (.lit 5) (.lit 4)) (.lit 4)) (.lit 1)))]) =
            some (.eval .rval (CExpr.binary .lt (.var "len")
              (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (.lit 5) (.lit 4)) (.lit 4)) (.lit 1)))
              [.logOrEndF], m4, []) := by
          unfold Sem.stepExprPure
          have ht : Sem.isTruthy (.int .i32 0#32) = some false := rfl
          simp only [ht, Bool.false_eq_true, ↓reduceIte, bind, Option.bind, pure, Pure.pure]
        refine WPTerm.of_exprPure hstep_or1 ?_
        have he_lt23 : PureEval prog zlibPointerConfig env_if m4 []
            (CExpr.binary .lt (.var "len")
              (CExpr.binary .sub (CExpr.binary .add (CExpr.binary .mul (.lit 5) (.lit 4)) (.lit 4)) (.lit 1)))
            (.int .i32 (if len0.toNat < 23 then 1#32 else 0#32)) (.int .i32) :=
          pureEval_binary_int (pureEval_var_int hs_len4 (modSet_conflicts_nil _ _ _))
            pureEval_const_23 rfl rfl (evalIntBinary_u64_lt_i32 len0 (by decide) (by decide))
        refine he_lt23.run ?_
        simp only [h23, ↓reduceIte]
        have hstep_or2 : Sem.stepExprPure prog zlibPointerConfig env_if m4 []
            (.ret (.rval (.int .i32 0#32) (.int .i32)) [.logOrEndF]) =
            some (.ret (.rval (.int .i32 0#32) (.int .i32)) [], m4, []) := by
          unfold Sem.stepExprPure
          have ht : Sem.isTruthy (.int .i32 0#32) = some false := rfl
          simp only [ht, Bool.false_eq_true, ↓reduceIte, bind, Option.bind, pure, Pure.pure]
          rfl
        refine WPTerm.of_exprPure hstep_or2 ?_
        have hstep_br0 (k_br : Sem.Cont) : Sem.stepDet prog zlibPointerConfig
            (.running (.expr (.ret (.rval (.int .i32 0#32) (.int .i32)) []) (.branch braidCallRet .nop) [])
              env_if blks_if m4 os k_br) =
            some (.next (.running (.stmt .nop) env_if blks_if m4 os k_br)) := by
          unfold Sem.stepDet
          have ht : Sem.isTruthy (.int .i32 0#32) = some false := rfl
          simp only [ht, Option.bind, Option.map_some]
          rfl
        refine WPTerm.of_det (hstep_br0 _) ?_
        -- Align loop (`minBlks := 5`)
        obtain ⟨b_ct, hlu_ct0, hb_ct_lt, htbl_ct⟩ := id htbl0
        have hlu_ct_if : env_if.lookup "crc_table" = some (b_ct, .array crcConstTy (some 256)) := by
          dsimp [env_if, env_params, env0]
          iterate 6 rw [lookup_cons_ne _ (by decide)]
          rw [hstat_cz, List.nil_append, hlib.globalEnv_eq, hlu_ct0]
        refine WPTerm.of_det (by rfl) ?_
        refine wp_while_align (minBlks := 5) hf4 (by simp) (by simp) (by simp) hne_cb hne_cl hne_bl
          hs_crc4 hs_buf4 hs_len4 rfl hr0_pos (by omega) hlu_ct_if hb_ct_lt htbl_ct ?_
        intro vc5 poff5 len5 m5 blk0 hf5 hs_crc5 hs_buf5 hs_len5 hblk0_m hal5 hlen5_ge hr5 hm5_eq
        have hu_end5 : UninitIntSlot env_if m5 "endian" b_end (CTy.int .u32) .u32 := by
          rcases hu_end with ⟨h1, h2, h3, blk_e, hbe, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_e, (hm5_eq b_end hne_end_c hne_end_b hne_end_l).trans hbe, h5, h6, h7⟩
        have hu_words5 : UninitPtrSlot env_if m5 "words" b_words wordConstPtrTy wordConstTy := by
          rcases hu_words4 with ⟨h1, h2, h3, blk_w, hbw, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_w, (hm5_eq b_words hne_w_c hne_w_b hne_w_l).trans hbw, h5, h6, h7⟩
        have hu_blks5 : UninitIntSlot env_if m5 "blks" b_blks zSizeTy .u64 := by
          rcases hu_blks4 with ⟨h1, h2, h3, blk_bl, hbbl, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_bl, (hm5_eq b_blks hne_bl_c hne_bl_b hne_bl_l).trans hbbl, h5, h6, h7⟩
        -- `blks = len / (5 * 4); len -= blks * 5 * 4; words = (z_word_t const *)buf;`
        refine WPTerm.of_det (by rfl) ?_
        refine wp_braid_setup_blks_len_words (k := 5) (by decide) (by decide) hlen5_ge hf5
          (by simp [blks_if]) (by simp [blks_if]) (by simp [blks_if])
          hne_w_bl.symm hne_bl_l hne_bl_c hne_w_l hne_w_b hne_w_c hne_bl.symm hne_cl.symm
          hne_bl_l.symm hne_bl_b.symm hu_blks5 hu_words5 hs_len5 hs_buf5 hs_crc5 ?_
        intro blks6 len6 m6 hf6 hblks6_ge1 _ hrem6_eq hs_blks6 hs_len6 hs_words6 hs_buf6 hs_crc6 hm6_eq
        have hu_end6 : UninitIntSlot env_if m6 "endian" b_end (CTy.int .u32) .u32 := by
          rcases hu_end5 with ⟨h1, h2, h3, blk_e, hbe, h5, h6, h7⟩
          exact ⟨h1, h2, h3, blk_e, (hm6_eq b_end hne_end_bl hne_end_w hne_end_l).trans hbe, h5, h6, h7⟩
        -- `endian = 1; if (*(unsigned char *)&endian)`
        refine WPTerm.of_det (by rfl) ?_
        refine wp_if_endian_one rfl (by simp [blks_if]) hf6 hu_end6 ?_
        intro m7 hf7 hs_end7 hm7_eq
        have hs_blks7 := intSlot_preserve_blocks hs_blks6 (hm7_eq b_blks hne_end_bl.symm)
        have hs_len7 := intSlot_preserve_blocks hs_len6 (hm7_eq b_len hne_end_l.symm)
        have hs_words7 := ptrSlot_preserve_blocks hs_words6 (hm7_eq b_words hne_end_w.symm)
        have hs_buf7 := ptrSlot_preserve_blocks hs_buf6 (hm7_eq b_buf hne_end_b.symm)
        have hs_crc7 := intSlot_preserve_blocks hs_crc6 (hm7_eq b_crc hne_end_c.symm)
        have hr_b5 : Readable m (.ptr pb poff5) (20 * blks6.toNat + len6.toNat) := by
          have : 20 * blks6.toNat + len6.toNat = len5.toNat :=
            (show 20 * blks6.toNat + len6.toNat = 4 * 5 * blks6.toNat + len6.toNat by rfl).trans hrem6_eq
          exact this ▸ hr5
        have hlu_cw_if : env_if.lookup "crc_word" = none := by
          dsimp [env_if, env_params, env0]
          iterate 6 rw [lookup_cons_ne _ (by decide)]
          rw [hstat_cz, List.nil_append, hlib.globalEnv_eq]
          exact hlib.gEnv_lookup_none "crc_word" (by decide)
        have hlu_b5_if : env_if.lookup "crc_braid5_table" = gEnv.lookup "crc_braid5_table" := by
          dsimp [env_if, env_params, env0]
          iterate 6 rw [lookup_cons_ne _ (by decide)]
          rw [hstat_cz, List.nil_append, hlib.globalEnv_eq]
        refine wp_crc32_z_braid5_inner hlib hf7 hblks6_ge1 hs_blks7 hs_len7 hs_words7 hs_buf7
          hs_crc7 hal5 hblk0_m hr_b5 htbl0 hbraid5_0 hlu_cw_if hlu_b5_if ?_
        intro vc_fin poff_fin m_if_done hf_if_done hwords_fin hcrc_fin hlen_fin hbuf_fin hr_tail
        -- `buf = (unsigned char const *)words;`
        refine WPTerm.of_det (by rfl) ?_
        have he_buf_fin : PureEval prog zlibPointerConfig env_if m_if_done []
            (CExpr.cast byteConstPtrTy (CExpr.var "words")) (.ptr pb poff_fin) byteConstPtrTy :=
          pureEval_cast (pureEval_var_ptr hwords_fin (modSet_conflicts_nil _ _ _))
            (castVal_ptr_eq (el := byteConstTy) rfl (Or.inr ⟨pb, poff_fin, rfl⟩))
        refine wp_stmt_assign_ptr hbuf_fin.to_uninit (by simp) hf_if_done he_buf_fin
          (Or.inr ⟨pb, poff_fin, rfl⟩) ?_
        intro m_if2 hwr_if2 hf_if2 hs_buf_if2
        have hs_crc_if2 := hcrc_fin.preserve_ne hwr_if2 hne_cb
        have hs_len_if2 := hlen_fin.preserve_ne hwr_if2 hne_bl.symm
        -- Exit `if (len >= 11)` block
        refine WPTerm.of_det (by rfl) (WPTerm.of_det (by rfl) ?_)
        have hf_out : LocalFrameMem m (m_if2.freeStack blks_if) [b_len, b_buf, b_crc] :=
          LocalFrameMem.freeStack_sub hf_if2
        have hnot_c_if : b_crc ∉ blks_if := by
          simp only [blks_if, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_end_c.symm, hne_w_c.symm, hne_bl_c.symm⟩
        have hnot_b_if : b_buf ∉ blks_if := by
          simp only [blks_if, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_end_b.symm, hne_w_b.symm, hne_bl_b.symm⟩
        have hnot_l_if : b_len ∉ blks_if := by
          simp only [blks_if, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hne_end_l.symm, hne_w_l.symm, hne_bl_l.symm⟩
        have hs_crc_out : IntSlot env_params (m_if2.freeStack blks_if) "crc" b_crc uLongTy .u64 vc_fin :=
          intSlot_drop_env (by decide) (intSlot_drop_env (by decide) (intSlot_drop_env (by decide)
            (hs_crc_if2.preserve_freeStack hnot_c_if)))
        have hs_buf_out : PtrSlot env_params (m_if2.freeStack blks_if) "buf" b_buf byteConstPtrTy byteConstTy
            (.ptr pb poff_fin) :=
          ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide) (ptrSlot_drop_env (by decide)
            (hs_buf_if2.preserve_freeStack hnot_b_if)))
        have hs_len_out : IntSlot env_params (m_if2.freeStack blks_if) "len" b_len zSizeTy .u64 len6 :=
          intSlot_drop_env (by decide) (intSlot_drop_env (by decide) (intSlot_drop_env (by decide)
            (hs_len_if2.preserve_freeStack hnot_l_if)))
        exact joinTail hf_out hs_crc_out hs_buf_out hs_len_out (Or.inr hr_tail)
    · -- `len0.toNat < 11`
      refine wp_if_pure (b := false) hge11_eval (by rw [isTruthy_int_nat (k := .i32)]; simp [h11]) ?_
      dsimp only [Option.getD]
      exact joinTail hf_not hs_crc_not hs_buf_not hs_len_not hr0'

private theorem argsWellTyped_u64_ptr_int {k3 : IntKind} {prog : Prog} {paramTys : List CTy} {args : List Val} {el : CTy}
    (hp : paramTys.map CTy.unqual = [.int .u64, .ptr el, .int k3])
    (hawt : Zlib.Spec.ArgsWellTyped prog paramTys false args) :
    ∃ (a : BitVec 64) (buf : Val) (len : BitVec k3.bits),
      args = [.int .u64 a, buf, .int k3 len] ∧ (buf = .null ∨ ∃ pb poff, buf = .ptr pb poff) := by
  rcases hawt with ⟨hlen, hval, _⟩
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

theorem crc32_z_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_z_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32_z hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32_z hlib) rfl ?_ (crc32_z_spec (zlibExt userExt) hlib) ?_ ?_
  · intro p hp
    simp only [Zlib.Crc32.crc32TU_fn_crc32_z, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args hb hpre hawt
    obtain ⟨crc, buf, len, rfl, hptr⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u64) (el := byteConstTy) rfl hawt
    simp only [Zlib.Crc32.crc32_z_contract] at hpre
    exact ⟨crc, buf, len, rfl, hptr, hpre,
      CrcTableValid.of_baseInv hlib hb (LocalFrameMem.init m),
      CrcBraidTableValid.of_baseInv_2 hlib hb (LocalFrameMem.init m),
      CrcBraidTableValid.of_baseInv_5 hlib hb (LocalFrameMem.init m)⟩
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨crc, buf, len, rfl, _⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u64) (el := byteConstTy) rfl hawt
    have hcast : Sem.castVal m' Zlib.Crc32.crc32_z_contract.retTy (.int .u64 bv) =
        some (.int .u64 bv) := by
      have h := castVal_int_eq (m := m') (ty := Zlib.Crc32.crc32_z_contract.retTy)
        (k1 := .u64) (k2 := .u64) rfl bv
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
      exact h
    refine ⟨.int .u64 bv, hcast, ?_⟩
    simp [Zlib.Crc32.crc32_z_contract]

private def Crc32Pre (prog : Prog) (gEnv : Env) (m : Mem) (args : List Val) : Prop :=
  ∃ (crc : BitVec 64) (buf : Val) (len : BitVec 32),
    args = [.int .u64 crc, buf, .int .u32 len] ∧
    (buf = .null ∨ ∃ pb poff, buf = .ptr pb poff) ∧
    (buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat) ∧
    CrcTableValid prog gEnv m ∧
    CrcBraidTableValid prog gEnv m "crc_braid2_table" ∧
    CrcBraidTableValid prog gEnv m "crc_braid5_table"

theorem crc32_spec {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    (ext : ExtHandler) (hlib : InitLibzProps prog gEnv m0 os0) :
    FuncBodySpec prog zlibPointerConfig ext Zlib.Crc32.crc32TU_fn_crc32
      (Crc32Pre prog gEnv)
      (fun _ _ ret _ => ∃ bv : BitVec 64, ret = .int .u64 bv) := by
  intro args env blks m m1 os base callEnv callBlks fs ctx k Q
    ⟨crc, buf, len, hargs, hbuf_ptr, hr0, htbl0, hbraid2_0, hbraid5_0⟩ _ hpush hcont
  subst hargs
  have hf1 : LocalFrameMem m m1 callBlks :=
    pushCallParams_localFrameMem (LocalFrameMem.init m) hpush
  obtain ⟨hsz0, hal0, hba0, m2_p, hwr0, hpush1⟩ := pushCallParams_cons_inv hpush
  obtain ⟨hsz1, hal1, hba1, m3_p, hwr1, hpush2⟩ := pushCallParams_cons_inv hpush1
  obtain ⟨hsz2, hal2, hba2, m4_p, hwr2, hpush3⟩ := pushCallParams_cons_inv hpush2
  unfold Sem.pushCallParams at hpush3
  cases hpush3
  let env0 := prog.fnStatics Zlib.Crc32.crc32TU_fn_crc32.name ++ prog.globalEnv
  let b_crc := m.nextBlock
  let b_buf := m2_p.nextBlock
  let b_len := m3_p.nextBlock
  have hs_crc_0 : IntSlot (("crc", b_crc, uLongTy) :: env0) m2_p "crc" b_crc uLongTy .u64 crc :=
    IntSlot.of_pushCallParam (k := .u64) rfl rfl hwr0 env0
  have hne_cb_mid : b_crc ≠ m2_p.nextBlock :=
    Nat.ne_of_lt (lt_nextBlock_of_some hs_crc_0.2.2.2.choose_spec.1)
  have hs_crc_1 : IntSlot (("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0)
      m3_p "crc" b_crc uLongTy .u64 crc :=
    (hs_crc_0.preserve_alloc rfl (by decide)).preserve_ne hwr1 hne_cb_mid
  have hs_buf_1 : PtrSlot (("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0)
      m3_p "buf" b_buf byteConstPtrTy byteConstTy buf :=
    PtrSlot.of_pushCallParam rfl rfl hbuf_ptr hwr1 _
  have hne_c_l : b_crc ≠ b_len :=
    Nat.ne_of_lt (Nat.lt_trans hs_crc_0.ne_of_lt_nextBlock hs_buf_1.ne_of_lt_nextBlock)
  have hne_b_l : b_buf ≠ b_len :=
    Nat.ne_of_lt hs_buf_1.ne_of_lt_nextBlock
  let env_params : Env := ("len", b_len, uIntTy) ::
    ("buf", b_buf, byteConstPtrTy) :: ("crc", b_crc, uLongTy) :: env0
  have hs_crc_2 : IntSlot env_params m1 "crc" b_crc uLongTy .u64 crc :=
    (hs_crc_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_c_l
  have hs_buf_2 : PtrSlot env_params m1 "buf" b_buf byteConstPtrTy byteConstTy buf :=
    (hs_buf_1.preserve_alloc rfl (by decide)).preserve_ne hwr2 hne_b_l
  have hs_len_2 : IntSlot env_params m1 "len" b_len uIntTy .u32 len :=
    IntSlot.of_pushCallParam (k := .u32) rfl rfl hwr2 _
  have henv_none : env_params.lookup "crc32_z" = none := by
    dsimp [env_params, env0]
    iterate 3 rw [lookup_cons_ne _ (by decide)]
    have hnm : Zlib.Crc32.crc32TU_fn_crc32.name = "crc32" := rfl
    rw [hnm, prog_fnStatics_crc32 hlib, List.nil_append, hlib.globalEnv_eq]
    exact hlib.gEnv_lookup_none "crc32_z" (by decide)
  have henum : enumConst? prog.tags "crc32_z" = none :=
    enumConst_prog_crc32_fns prog.tags hlib.prog_tags_eq "crc32_z" (by decide)
  have hproto := prog_fnProtos_crc32_z hlib
  have hbody : Zlib.Crc32.crc32TU_fn_crc32.body = CStmt.block [
      .returnStmt (some (.call (.var "crc32_z") [.var "crc", .var "buf", .var "len"]))] := rfl
  rw [hbody]
  refine WPTerm.of_det rfl ?_
  simp only [List.isEmpty_nil, ↓reduceIte]
  refine WPTerm.of_det rfl ?_
  refine WPTerm.of_exprPure rfl ?_
  refine wp_call_var henv_none henum hproto ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureEval_var_int hs_crc_2 (modSet_conflicts_nil _ _ _)).run ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureEval_var_ptr hs_buf_2 (modSet_conflicts_nil _ _ _)).run ?_
  refine WPTerm.of_exprPure rfl ?_
  refine (pureEval_var_int hs_len_2 (modSet_conflicts_nil _ _ _)).run ?_
  let len64 : BitVec 64 := BitVec.ofInt 64 (len.toNat : Int)
  have hcoerce : Sem.coerceCallArgs m1
      (Zlib.Crc32.crc32TU_fn_crc32_z.params.map (·.ty)) false
      [(.int .u64 crc, uLongTy.decay), (buf, byteConstPtrTy.decay), (.int .u32 len, uIntTy.decay)] =
      some [.int .u64 crc, buf, .int .u64 len64] := by
    have hc1 : Sem.castVal m1 uLongTy (.int .u64 crc) = some (.int .u64 crc) := by
      have h := castVal_int_eq (m := m1) (ty := uLongTy) (k1 := .u64) (k2 := .u64) rfl crc
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
      exact h
    have hc2 : Sem.castVal m1 byteConstPtrTy buf = some buf :=
      castVal_ptr_eq (m := m1) (ty := byteConstPtrTy) (el := byteConstTy) rfl hbuf_ptr
    have hc3 : Sem.castVal m1 zSizeTy (.int .u32 len) = some (.int .u64 len64) := by
      have h := castVal_int_eq (m := m1) (ty := zSizeTy) (k1 := .u32) (k2 := .u64) rfl len
      simp only [IntKind.signed, Bool.false_eq_true, ↓reduceIte] at h
      exact h
    unfold Sem.coerceCallArgs
    simp only [Zlib.Crc32.crc32TU_fn_crc32_z, List.map_cons, List.map_nil, Bool.false_eq_true,
      ↓reduceIte, List.length_cons, List.length_nil, beq_self_eq_true, guard_true, List.zip_cons_cons,
      List.zip_nil_right, List.mapM_cons, List.mapM_nil, hc1, hc2, hc3, bind, Option.bind, pure, Pure.pure]
  have hsimp : ∀ p ∈ Zlib.Crc32.crc32TU_fn_crc32_z.params, IsSimpleParamTy p.ty := by
    intro p hp
    simp only [Zlib.Crc32.crc32TU_fn_crc32_z, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  have hlen64 : len64.toNat = len.toNat := by
    dsimp [len64]
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans len.isLt (by decide))
  have hr_z : buf = .null ∨ len64.toNat = 0 ∨ Readable m1 buf len64.toNat := by
    rcases hr0 with rfl | h0 | hr
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hlen64.trans h0))
    · rcases hbuf_ptr with rfl | ⟨pb, poff, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hlen64 ▸ Readable.of_localFrameMem hf1 hr))
  refine FuncBodySpec.call (crc32_z_spec ext hlib) (by unfold Sem.stepDet; rfl)
    (prog_fns_crc32_z hlib) rfl rfl hcoerce
    ⟨crc, buf, len64, rfl, hbuf_ptr, hr_z,
      CrcTableValid.of_localFrameMem htbl0 hf1,
      CrcBraidTableValid.of_localFrameMem hbraid2_0 hf1,
      CrcBraidTableValid.of_localFrameMem hbraid5_0 hf1⟩
    hsimp ?_
  intro ret m' hro ⟨retBv, hret⟩
  subst hret
  have hcast : Sem.castVal m' (CTy.typedef "uLong" (CTy.int IntKind.u64)) (.int .u64 retBv) =
      some (.int .u64 retBv) := by
    have h := castVal_int_eq (m := m') (ty := CTy.typedef "uLong" (CTy.int IntKind.u64))
      (k1 := .u64) (k2 := .u64) rfl retBv
    simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
    exact h
  refine WPTerm.of_det ?_ (hcont (.int .u64 retBv) (m'.freeStack [b_len, b_buf, b_crc])
    (LocalFrameMem.roExt_freeStack (hf1.of_roExt hro)) ⟨retBv, rfl⟩)
  unfold Sem.stepDet
  simp only [Sem.Cont.topRetTy, Zlib.Crc32.crc32TU_fn_crc32, CTy.isVoid, CTy.unqual,
    Bool.false_eq_true, ↓reduceIte, Sem.unwindReturn, freeStack_nil, hcast, Option.bind, Option.map_some]
  rfl

theorem crc32_safe
    {prog : Prog} {gEnv : Env} {m0 : Mem} {os0 : OSState}
    {userExt : ExtHandler} {userWrite : BlockSet}
    {Inv : Zlib.Spec.ClientView → Zlib.Spec.BlockSet → Mem → OSState → Prop}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hInvBase : ∀ v owned m os, Inv v owned m os → BaseInv m0 os0 v owned m os)
    (hInvRO : ∀ v owned m m' os, Inv v owned m os → ROExt m m' → Inv v owned m' os) :
    Zlib.Spec.ContractSafe prog gEnv (zlibExt userExt) Inv userWrite
      Zlib.Crc32.crc32_contract := by
  refine FuncBodySpec.to_contractSafe hInvBase hInvRO (prog_fns_crc32 hlib) rfl
    ⟨rfl, rfl⟩ (prog_fnProtos_crc32 hlib) rfl ?_ (crc32_spec (zlibExt userExt) hlib) ?_ ?_
  · intro p hp
    simp only [Zlib.Crc32.crc32TU_fn_crc32, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [IsSimpleParamTy, CTy.unqual]
  · intro v owned m os args hb hpre hawt
    obtain ⟨crc, buf, len, rfl, hptr⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u32) (el := byteConstTy) rfl hawt
    simp only [Zlib.Crc32.crc32_contract] at hpre
    exact ⟨crc, buf, len, rfl, hptr, hpre,
      CrcTableValid.of_baseInv hlib hb (LocalFrameMem.init m),
      CrcBraidTableValid.of_baseInv_2 hlib hb (LocalFrameMem.init m),
      CrcBraidTableValid.of_baseInv_5 hlib hb (LocalFrameMem.init m)⟩
  · intro v owned m args ret m' _ hawt _ ⟨bv, hret⟩
    subst hret
    obtain ⟨crc, buf, len, rfl, _⟩ :=
      argsWellTyped_u64_ptr_int (k3 := .u32) (el := byteConstTy) rfl hawt
    have hcast : Sem.castVal m' Zlib.Crc32.crc32_contract.retTy (.int .u64 bv) =
        some (.int .u64 bv) := by
      have h := castVal_int_eq (m := m') (ty := Zlib.Crc32.crc32_contract.retTy)
        (k1 := .u64) (k2 := .u64) rfl bv
      simp only [IntKind.signed, IntKind.bits, Bool.false_eq_true, ↓reduceIte, bitVec_ofInt_toNat] at h
      exact h
    refine ⟨.int .u64 bv, hcast, ?_⟩
    simp [Zlib.Crc32.crc32_contract]

end Zlib.Proof
