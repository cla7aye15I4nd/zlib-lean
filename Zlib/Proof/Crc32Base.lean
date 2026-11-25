import C99.Proof
import Zlib.Proof.ProgLookup
import Zlib.Proof.ProgSpec
import Zlib.Crc32
import Zlib.Tables.Crc32H

/-!
# Shared Infrastructure for `crc32.c` Safety Proofs (`Zlib.Proof.Crc32Base`)

Proves safety, bounded termination, frame preservation, and heap-leak freedom
for all 7 public `c_fn` contracts and internal helpers in `Zlib.Crc32`:
- Pure GF(2^32) nonzero preservation (`multmodpSpec`, `x2nTableVals_nonzero_mul`)
- `byte_swap` (`byte_swap_spec`)
- `multmodp` (`multmodp_spec`)
- `x2nmodp` (`x2nmodp_spec`)
- `get_crc_table` (`get_crc_table_spec`)
- `crc_word` (`crc_word_spec`)
- `crc32_braid` (`crc32_braid_spec`)
- `crc32_z` (`crc32_z_spec`, `crc32_z_safe`, `crc32_z_safe_of_initLibz`)
- `crc32` (`crc32_spec`, `crc32_safe`, `crc32_safe_of_initLibz`)
- `crc32_combine_gen64`, `crc32_combine_gen`, `crc32_combine_op`,
  `crc32_combine64`, `crc32_combine`
-/

namespace Zlib.Proof

open C99 C99.Sem C99.Proof Zlib.Spec Zlib.Crc32

/-! ## 1. Pure `GF(2^32)` Multiplication & Nonzero Preservation -/

def multmodpNextB (b : BitVec 32) : BitVec 32 :=
  if (b &&& 1#32) != 0#32 then (b >>> 1) ^^^ 0xedb88320#32 else b >>> 1

def multmodpStep (bit : Bool) (b : BitVec 32) : BitVec 32 :=
  if bit then b else 0#32

def multmodpLoop (a : BitVec 32) : Nat → BitVec 32 → BitVec 32 → BitVec 32
  | 0, p, b => p ^^^ multmodpStep ((a &&& 1#32) != 0#32) b
  | k + 1, p, b =>
    let p' := p ^^^ multmodpStep ((a &&& (1#32 <<< (k + 1))) != 0#32) b
    multmodpLoop a k p' (multmodpNextB b)

def multmodpSpec (a b : BitVec 32) : BitVec 32 :=
  multmodpLoop a 31 0#32 b

theorem bv32_xor_comm (a b : BitVec 32) : a ^^^ b = b ^^^ a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  exact Bool.xor_comm _ _

theorem bv32_xor_assoc (a b c : BitVec 32) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  exact Bool.xor_assoc _ _ _

theorem bv32_xor_self (a : BitVec 32) : a ^^^ a = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero]
  exact Bool.xor_self _

theorem bv32_xor_comm4 (a b c d : BitVec 32) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [bv32_xor_assoc, ← bv32_xor_assoc b c d, bv32_xor_comm b c, bv32_xor_assoc c b d, ← bv32_xor_assoc]

theorem bv32_and_one (b : BitVec 32) :
    b &&& 1#32 = if b.getLsbD 0 then 1#32 else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  cases i with
  | zero =>
    have h1 : (1#32).getLsbD 0 = true := rfl
    simp only [BitVec.getLsbD_and, h1, Bool.and_true]
    cases b.getLsbD 0 <;> simp
  | succ n =>
    have h1 : (1#32).getLsbD (n + 1) = false := by simp
    cases b.getLsbD 0 <;> simp [BitVec.getLsbD_and, h1]

theorem multmodpNextB_zero : multmodpNextB 0#32 = 0#32 := by decide

theorem multmodpNextB_xor (b1 b2 : BitVec 32) :
    multmodpNextB (b1 ^^^ b2) = multmodpNextB b1 ^^^ multmodpNextB b2 := by
  unfold multmodpNextB
  have hand : (b1 ^^^ b2) &&& 1#32 = (b1 &&& 1#32) ^^^ (b2 &&& 1#32) := by
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
    exact Bool.and_xor_distrib_right _ _ _
  have hsh : (b1 ^^^ b2) >>> 1 = (b1 >>> 1) ^^^ (b2 >>> 1) := by
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [hand, hsh, bv32_and_one b1, bv32_and_one b2]
  cases b1.getLsbD 0 <;> cases b2.getLsbD 0 <;> simp only [↓reduceIte, Bool.false_eq_true]
  · simp
  · simp [bv32_xor_assoc]
  · simp [bv32_xor_assoc, bv32_xor_comm (0xedb88320#32)]
  · simp only [bne_iff_ne, ne_eq, bv32_xor_self, not_true_eq_false, ↓reduceIte, BitVec.reduceEq,
      not_false_eq_true]
    rw [bv32_xor_comm4 (b1 >>> 1) (0xedb88320#32) (b2 >>> 1) (0xedb88320#32),
      bv32_xor_self, BitVec.xor_zero]

theorem multmodpStep_xor (bit : Bool) (b1 b2 : BitVec 32) :
    multmodpStep bit (b1 ^^^ b2) = multmodpStep bit b1 ^^^ multmodpStep bit b2 := by
  cases bit <;> simp [multmodpStep]

theorem multmodpStep_zero (bit : Bool) :
    multmodpStep bit 0#32 = 0#32 := by
  cases bit <;> simp [multmodpStep]

theorem multmodpLoop_zero (a : BitVec 32) : ∀ k, multmodpLoop a k 0#32 0#32 = 0#32
  | 0 => by simp [multmodpLoop, multmodpStep_zero]
  | k + 1 => by
    simp only [multmodpLoop, multmodpStep_zero, BitVec.xor_zero, multmodpNextB_zero]
    exact multmodpLoop_zero a k

theorem multmodpLoop_xor (a : BitVec 32) :
    ∀ k p1 p2 b1 b2,
      multmodpLoop a k (p1 ^^^ p2) (b1 ^^^ b2) =
        multmodpLoop a k p1 b1 ^^^ multmodpLoop a k p2 b2
  | 0, p1, p2, b1, b2 => by
    simp only [multmodpLoop, multmodpStep_xor]
    exact bv32_xor_comm4 p1 p2 _ _
  | k + 1, p1, p2, b1, b2 => by
    simp only [multmodpLoop, multmodpStep_xor, multmodpNextB_xor]
    rw [bv32_xor_comm4 p1 p2 _ _]
    exact multmodpLoop_xor a k _ _ _ _

theorem multmodpSpec_zero (a : BitVec 32) : multmodpSpec a 0#32 = 0#32 :=
  multmodpLoop_zero a 31

theorem multmodpSpec_xor (a b1 b2 : BitVec 32) :
    multmodpSpec a (b1 ^^^ b2) = multmodpSpec a b1 ^^^ multmodpSpec a b2 := by
  unfold multmodpSpec
  simpa using multmodpLoop_xor a 31 0#32 0#32 b1 b2

def reconBits (f : BitVec 32 → BitVec 32) (b : BitVec 32) : Nat → BitVec 32
  | 0 => 0#32
  | n + 1 => reconBits f b n ^^^ (if b.getLsbD n then f (1#32 <<< n) else 0#32)

theorem reconBits_id_getLsbD (b : BitVec 32) :
    ∀ n i, i < 32 → (reconBits id b n).getLsbD i = (decide (i < n) && b.getLsbD i)
  | 0, i, _ => by simp [reconBits]
  | n + 1, i, hi32 => by
    simp only [reconBits, BitVec.getLsbD_xor]
    rw [reconBits_id_getLsbD b n i hi32]
    by_cases hbi : b.getLsbD n = true
    · simp only [hbi, ↓reduceIte, id_eq]
      have hsh : (1#32 <<< n).getLsbD i = decide (i = n) := by
        simp only [BitVec.getLsbD_shiftLeft, hi32, decide_true, Bool.true_and]
        by_cases hle : n ≤ i
        · have hsub : (1#32).getLsbD (i - n) = decide (i - n = 0) := by
            cases h0 : i - n with
            | zero => rfl
            | succ m => simp
          rw [hsub]
          by_cases heq : i = n
          · subst heq; simp
          · have hne : i - n ≠ 0 := by omega
            simp [heq, hne]
        · have hne : i ≠ n := by omega
          simp [hle, hne]
      rw [hsh]
      by_cases hin : i < n
      · have hne : i ≠ n := by omega
        have hin1 : i < n + 1 := by omega
        simp [hin, hin1, hne]
      · by_cases heq : i = n
        · subst heq
          have hlt : i < i + 1 := Nat.lt_succ_self _
          simp [hin, hlt, hbi]
        · have hnot : ¬ (i < n + 1) := by omega
          simp [hin, hnot, heq]
    · have hbf : b.getLsbD n = false := Bool.eq_false_iff.mpr hbi
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_zero, Bool.xor_false]
      by_cases hin : i < n
      · have hin1 : i < n + 1 := by omega
        simp [hin, hin1]
      · by_cases heq : i = n
        · subst heq
          simp [hin, hbf]
        · have hnot : ¬ (i < n + 1) := by omega
          simp [hin, hnot]

theorem reconBits_id_32 (b : BitVec 32) : reconBits id b 32 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [reconBits_id_getLsbD b 32 i hi]
  simp [hi]

theorem reconBits_map (f : BitVec 32 → BitVec 32)
    (hf0 : f 0#32 = 0#32) (hfx : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (g : BitVec 32 → BitVec 32) (b : BitVec 32) :
    ∀ n, f (reconBits g b n) = reconBits (fun x => f (g x)) b n
  | 0 => hf0
  | n + 1 => by
    simp only [reconBits, hfx, reconBits_map f hf0 hfx g b n]
    cases b.getLsbD n <;> simp [hf0]

theorem reconBits_congr (f g : BitVec 32 → BitVec 32) (b : BitVec 32) :
    ∀ n, (∀ j : Nat, j < n → f (1#32 <<< j) = g (1#32 <<< j)) →
      reconBits f b n = reconBits g b n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [reconBits]
    rw [reconBits_congr f g b n (fun j hj => h j (by omega)), h n (Nat.lt_succ_self n)]

theorem multmodpSpec_nonzero_of_inv (a inv : BitVec 32)
    (hinv : ∀ j : Fin 32, multmodpSpec inv (multmodpSpec a (1#32 <<< j.val)) = 1#32 <<< j.val)
    (b : BitVec 32) (hb : b ≠ 0#32) :
    multmodpSpec a b ≠ 0#32 := by
  intro hz
  have hcomp : multmodpSpec inv (multmodpSpec a b) = b := by
    calc multmodpSpec inv (multmodpSpec a b)
        = multmodpSpec inv (multmodpSpec a (reconBits id b 32)) := by rw [reconBits_id_32]
      _ = multmodpSpec inv (reconBits (fun x => multmodpSpec a (id x)) b 32) := by
          rw [reconBits_map (multmodpSpec a) (multmodpSpec_zero a) (multmodpSpec_xor a)]
      _ = reconBits (fun x => multmodpSpec inv (multmodpSpec a (id x))) b 32 := by
          rw [reconBits_map (multmodpSpec inv) (multmodpSpec_zero inv) (multmodpSpec_xor inv)]
      _ = reconBits id b 32 :=
          reconBits_congr _ _ b 32 (fun j hj => hinv ⟨j, hj⟩)
      _ = b := reconBits_id_32 b
  rw [hz, multmodpSpec_zero] at hcomp
  exact hb hcomp.symm

private def x2nInvVals : Array (BitVec 32) :=
  #[0xdb710641#32, 0x6d930ac3#32, 0x6d3d2d4d#32, 0x6567cb95#32,
    0xd7125358#32, 0x5b358fd3#32, 0x2e9bb40b#32, 0x12a59a49#32,
    0x8df9403d#32, 0x5139de12#32, 0xba340226#32, 0x29c45641#32,
    0x12fbc105#32, 0xecd30c55#32, 0x3755ebd8#32, 0x24ee460c#32,
    0x23783fcf#32, 0x479933fc#32, 0xa39442a5#32, 0x9ea0056d#32,
    0xf42608f6#32, 0x20cacf04#32, 0x2a0cf83d#32, 0xeffd8645#32,
    0x2a39a67d#32, 0x640ebd82#32, 0x9dfd8792#32, 0x277402ab#32,
    0xad31bc4f#32, 0x31536354#32, 0x5ea35fca#32, 0x52b55e39#32]

private theorem x2nTableVals_inv_all :
    (List.range 32).all (fun i =>
      (List.range 32).all (fun j =>
        decide (multmodpSpec (x2nInvVals[i]!)
          (multmodpSpec (BitVec.ofInt 32 Zlib.Tables.x2nTableVals[i]!) (1#32 <<< j)) ==
          1#32 <<< j))) = true := by
  decide +kernel

theorem x2nTableVals_inv_check (i j : Fin 32) :
    multmodpSpec (x2nInvVals[i.val]!)
      (multmodpSpec (BitVec.ofInt 32 Zlib.Tables.x2nTableVals[i.val]!) (1#32 <<< j.val)) =
    1#32 <<< j.val := by
  have hi := List.all_eq_true.mp x2nTableVals_inv_all i.val (List.mem_range.mpr i.isLt)
  have hj := List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt)
  exact beq_iff_eq.mp (of_decide_eq_true hj)

theorem x2nTableVals_nonzero_mul :
    ∀ i < 32, ∀ b : BitVec 32, b ≠ 0#32 →
      multmodpSpec (BitVec.ofInt 32 Zlib.Tables.x2nTableVals[i]!) b ≠ 0#32 := by
  intro i hi b hb
  exact multmodpSpec_nonzero_of_inv
    (BitVec.ofInt 32 Zlib.Tables.x2nTableVals[i]!) (x2nInvVals[i]!)
    (x2nTableVals_inv_check ⟨i, hi⟩) b hb

theorem mask32_split_all :
    (List.range 31).all (fun k =>
      decide (((1#32 <<< (k + 1)) - 1#32) == (1#32 <<< k) ||| ((1#32 <<< k) - 1#32))) = true := by
  decide

theorem mask32_split {k : Nat} (hk : k < 31) :
    ((1#32 <<< (k + 1)) - 1#32) = (1#32 <<< k) ||| ((1#32 <<< k) - 1#32) :=
  beq_iff_eq.mp (of_decide_eq_true (List.all_eq_true.mp mask32_split_all k (List.mem_range.mpr hk)))

theorem mask64_split_all :
    (List.range 32).all (fun k =>
      decide (((1#64 <<< (k + 1)) - 1#64) == (1#64 <<< k) ||| ((1#64 <<< k) - 1#64))) = true := by
  decide

theorem mask64_split {k : Nat} (hk : k < 32) :
    ((1#64 <<< (k + 1)) - 1#64) = (1#64 <<< k) ||| ((1#64 <<< k) - 1#64) :=
  beq_iff_eq.mp (of_decide_eq_true (List.all_eq_true.mp mask64_split_all k (List.mem_range.mpr hk)))

theorem bv32_and_or_eq_zero {a x y : BitVec 32} (h : (a &&& (x ||| y)) = 0#32) :
    (a &&& x) = 0#32 ∧ (a &&& y) = 0#32 := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i _
    have hi := congrArg (fun z : BitVec 32 => z.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hi ⊢
    cases ha : a.getLsbD i <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
  · apply BitVec.eq_of_getLsbD_eq; intro i _
    have hi := congrArg (fun z : BitVec 32 => z.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hi ⊢
    cases ha : a.getLsbD i <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem bv64_and_or_eq_zero {a x y : BitVec 64} (h : (a &&& (x ||| y)) = 0#64) :
    (a &&& x) = 0#64 ∧ (a &&& y) = 0#64 := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i _
    have hi := congrArg (fun z : BitVec 64 => z.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hi ⊢
    cases ha : a.getLsbD i <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
  · apply BitVec.eq_of_getLsbD_eq; intro i _
    have hi := congrArg (fun z : BitVec 64 => z.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hi ⊢
    cases ha : a.getLsbD i <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

theorem multmodpLoop_eq_of_low_zero (a : BitVec 32) :
    ∀ k, k ≤ 31 → (a &&& ((1#32 <<< k) - 1#32)) = 0#32 →
      ∀ p b, multmodpLoop a k p b = p ^^^ multmodpStep ((a &&& (1#32 <<< k)) != 0#32) b
  | 0, _, _, p, b => rfl
  | k' + 1, hk, hlow, p, b => by
    rw [mask32_split (by omega)] at hlow
    obtain ⟨hbit, hlow'⟩ := bv32_and_or_eq_zero hlow
    simp only [multmodpLoop]
    rw [multmodpLoop_eq_of_low_zero a k' (by omega) hlow']
    simp [hbit, multmodpStep]

theorem bv64_and_bit_eq_zero_iff (a : BitVec 64) {k : Nat} (hk : k < 32) :
    (a.truncate 32 &&& (1#32 <<< k) = 0#32) ↔ (a &&& (1#64 <<< k) = 0#64) := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases hi32 : i < 32
    · have hi' := congrArg (fun z : BitVec 32 => z.getLsbD i) h
      simpa [BitVec.truncate, BitVec.getLsbD_setWidth, hi32,
        BitVec.getLsbD_shiftLeft, hi] using hi'
    · have hsh : (1#64 <<< k).getLsbD i = false := by
        simp only [BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
        by_cases hki : k ≤ i
        · have hne : i - k ≠ 0 := by omega
          have h1 : (1#64).getLsbD (i - k) = false := by
            cases hm : i - k with
            | zero => contradiction
            | succ _ => simp
          simp [h1]
        · simp [hki]
      simp [BitVec.getLsbD_and, hsh]
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hi' := congrArg (fun z : BitVec 64 => z.getLsbD i) h
    simpa [BitVec.truncate, BitVec.getLsbD_setWidth, hi,
      BitVec.getLsbD_shiftLeft, (by omega : i < 64)] using hi'

theorem bv64_and_bit_trunc32 (a : BitVec 64) {k : Nat} (hk : k < 32) :
    ((a.truncate 32 &&& (1#32 <<< k)) != 0#32) = ((a &&& (1#64 <<< k)) != 0#64) := by
  have h1 : (a.truncate 32 &&& (1#32 <<< k) == 0#32) = (a &&& (1#64 <<< k) == 0#64) :=
    Bool.eq_iff_iff.mpr (by simpa [beq_iff_eq] using bv64_and_bit_eq_zero_iff a hk)
  simp only [bne, h1]

theorem bv64_and_mask_trunc32 (a : BitVec 64) {k : Nat} (hk : k < 32) :
    (a.truncate 32 &&& ((1#32 <<< k) - 1#32) = 0#32) ↔
    (a &&& ((1#64 <<< k) - 1#64) = 0#64) := by
  have heq : ((1#64 <<< k) - 1#64).truncate 32 = (1#32 <<< k) - 1#32 := by
    exact beq_iff_eq.mp (of_decide_eq_true (List.all_eq_true.mp
      (by decide : (List.range 32).all (fun k =>
        decide (((1#64 <<< k) - 1#64).truncate 32 == (1#32 <<< k) - 1#32)) = true)
      k (List.mem_range.mpr hk)))
  have hhi : ∀ i, 32 ≤ i → i < 64 → ((1#64 <<< k) - 1#64).getLsbD i = false := by
    intro i hi1 hi2
    have hall : (List.range 32).all (fun k =>
        (List.range 32).all (fun j => !(((1#64 <<< k) - 1#64).getLsbD (32 + j)))) = true := by
      decide
    have h1 := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    have h2 := List.all_eq_true.mp h1 (i - 32) (List.mem_range.mpr (by omega))
    have hadd : 32 + (i - 32) = i := by omega
    rw [hadd] at h2
    simpa using h2
  rw [← heq]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases hi32 : i < 32
    · have hi' := congrArg (fun z : BitVec 32 => z.getLsbD i) h
      simpa [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi32] using hi'
    · simp [BitVec.getLsbD_and, hhi i (by omega) hi]
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hi' := congrArg (fun z : BitVec 64 => z.getLsbD i) h
    simpa [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi] using hi'

theorem bv64_truncate_xor (a b : BitVec 64) :
    (a ^^^ b).truncate 32 = a.truncate 32 ^^^ b.truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.truncate, hi]

theorem bv64_truncate_ushiftRight_1 {b : BitVec 64} (hb : b.toNat < 2 ^ 32) :
    (b >>> 1).truncate 32 = b.truncate 32 >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true,
    Bool.true_and]
  have hadd : 1 + i = i + 1 := by omega
  rw [hadd]
  by_cases hi31 : i + 1 < 32
  · simp [hi31]
  · have hi31eq : i + 1 = 32 := by omega
    have hge : b.getLsbD (i + 1) = false := by
      rw [BitVec.getLsbD_eq_getElem (by omega)]
      simp only [BitVec.getElem_eq_testBit_toNat]
      exact Nat.testBit_lt_two_pow (by rw [hi31eq]; exact hb)
    rw [hge]
    simp [hi31]

theorem bv64_zeroExtend_truncate_of_lt {b : BitVec 64} (hb : b.toNat < 2 ^ 32) :
    (b.truncate 32).zeroExtend 64 = b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.zeroExtend, BitVec.truncate, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]

/-! ## 2. `enumConst?`, Global Lookup, Memory Slices, and Stack Slots -/

def enumListHas (name : String) : List (String × Option Int) → Bool
  | [] => false
  | (k, _) :: tl => (k == name) || enumListHas name tl

def envHasEnumConst (name : String) : TypeEnv → Bool
  | [] => false
  | (_, .enumDef items _) :: rest => enumListHas name items || envHasEnumConst name rest
  | _ :: rest => envHasEnumConst name rest

theorem enumConst_none_of_false {tags : TypeEnv} {name : String}
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

def Crc32CallNames : List String :=
  ["multmodp", "x2nmodp", "crc_word", "crc32_braid", "crc32_z",
   "crc32_combine_gen64", "crc32_combine_op", "crc32_combine64"]

theorem enumConst_prog_crc32_fns (tags : TypeEnv)
    (ht : tags = (progOfTUs Zlib.allFiles).tags) :
    ∀ sym ∈ Crc32CallNames, enumConst? tags sym = none := by
  have hall : Crc32CallNames.all (fun sym =>
      !envHasEnumConst sym (progOfTUs Zlib.allFiles).tags) = true := by
    rw [progOfTUs_tags]
    decide
  intro sym hmem
  have hs := List.all_eq_true.mp hall sym hmem
  rw [ht]
  exact enumConst_none_of_false (by simpa using hs)

theorem Readable.advance {m : Mem} {pb : BlockId} {poff : Int64} {n k : Nat}
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

theorem Readable.block_lt {m : Mem} {pb : BlockId} {poff : Int64} {n : Nat}
    (hr : Readable m (.ptr pb poff) n) : pb < m.nextBlock := by
  rcases hr with ⟨_, _, blk, heq, hblk, _⟩
  cases heq
  exact lt_nextBlock_of_some hblk

theorem LocalFrameMem.blocks_eq_of_lt {m0 m : Mem} {blks : List BlockId}
    (hf : LocalFrameMem m0 m blks) {b : BlockId} (hlt : b < m0.nextBlock) :
    m.blocks b = m0.blocks b :=
  hf.2.1 b hlt

theorem Readable.of_localFrameMem {m0 m : Mem} {blks : List BlockId}
    {pb : BlockId} {poff : Int64} {n : Nat}
    (hf : LocalFrameMem m0 m blks) (hr : Readable m0 (.ptr pb poff) n) :
    Readable m (.ptr pb poff) n := by
  have hlt := Readable.block_lt hr
  rcases hr with ⟨_, _, blk, heq, hblk, hin, hbytes⟩
  cases heq
  exact ⟨pb, poff, blk, rfl, by rw [LocalFrameMem.blocks_eq_of_lt hf hlt, hblk], hin, hbytes⟩

theorem Readable.addrOf {m0 m : Mem} {blks : List BlockId}
    {pb : BlockId} {poff : Int64} {n : Nat}
    (hf : LocalFrameMem m0 m blks) (hr : Readable m0 (.ptr pb poff) n) :
    ∃ blk addr, m.blocks pb = some blk ∧
      m.addrOf pb poff = some addr ∧
      addr = blk.baseAddr + UInt64.ofNat poff.toInt.toNat ∧
      0 ≤ poff.toInt ∧ poff.toInt ≤ (blk.size : Int) := by
  have hlt := Readable.block_lt hr
  rcases hr with ⟨_, _, blk, heq, hblk, hin, _⟩
  cases heq
  have hm : m.blocks pb = some blk := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt, hblk]
  have hin' := inBounds_iff.mp hin
  exact ⟨blk, blk.baseAddr + UInt64.ofNat poff.toInt.toNat, hm,
    addrOf_some hm hin'.1 (by omega), rfl, hin'.1, by omega⟩

theorem Readable.read_u8 {tags : TypeEnv} {m0 m : Mem} {blks : List BlockId}
    {pb : BlockId} {poff : Int64} {n idx : Nat}
    (hf : LocalFrameMem m0 m blks)
    (hr : Readable m0 (.ptr pb poff) n) (hidx : idx < n) :
    ∃ blk, ∃ bv : BitVec 8, m.blocks pb = some blk ∧
      0 ≤ poff.toInt + (idx : Int) ∧ poff.toInt + (idx : Int) ≤ (blk.size : Int) ∧
      Sem.readVal tags m pb (Int64.ofInt (poff.toInt + idx)) (.const_ (.int .u8)) = some (.int .u8 bv) := by
  have hlt_pb : pb < m0.nextBlock := Readable.block_lt hr
  rcases hr with ⟨_, _, blk, heq, hblk, hin, hbytes⟩
  cases heq
  have hm_pb : m.blocks pb = some blk := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt_pb, hblk]
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
    have hi1 : i < 1 := hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [Nat.add_zero, hoff_toInt]
    have heqn : (poff.toInt + (idx : Int)).toNat = poff.toInt.toNat + idx := by
      have := (inBounds_iff.mp hin).1
      omega
    rw [heqn]
    exact hbytes idx hidx)
  have hrv' : Sem.readVal tags m pb (Int64.ofInt (poff.toInt + idx))
      (.const_ (.int .u8)) = some (.int .u8 bv) := by
    unfold Sem.readVal at hrv ⊢
    simpa [CTy.unqual] using hrv
  exact ⟨blk, bv, hm_pb, (by have := (inBounds_iff.mp hin).1; omega),
    (by have := (inBounds_iff.mp hin).2; omega), hrv'⟩

theorem Readable.read_u32_word {tags : TypeEnv} {m0 m : Mem} {blks : List BlockId}
    {pb : BlockId} {poff : Int64} {blk0 : Block} {n wordIdx : Nat}
    (hf : LocalFrameMem m0 m blks)
    (hr : Readable m0 (.ptr pb poff) n)
    (hblk0 : m0.blocks pb = some blk0)
    (hal0 : Mem.isAligned blk0 poff 4 = true)
    (hbound : 4 * wordIdx + 4 ≤ n) :
    ∃ (bv : BitVec 32),
      Sem.readVal tags m pb (Int64.ofInt (poff.toInt + 4 * wordIdx))
        (.const_ (.typedef "z_word_t" (.int .u32))) = some (.int .u32 bv) := by
  have hlt_pb : pb < m0.nextBlock := Readable.block_lt hr
  rcases hr with ⟨_, _, blk, heq, hblk, hin, hbytes⟩
  cases heq
  rw [hblk0] at hblk
  cases hblk
  have hm_pb : m.blocks pb = some blk0 := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt_pb, hblk0]
  have hlt63 : poff.toInt + ((4 * wordIdx : Nat) : Int) < 2 ^ 63 := by
    have := blk0.sizeLt
    rw [ptrDiffLimit_val] at this
    have := inBounds_iff.mp hin
    omega
  have hoff_in : Mem.inBounds blk0 (Int64.ofInt (poff.toInt + ((4 * wordIdx : Nat) : Int))) 4 = true :=
    inBounds_add hin (by omega)
  have hoff_toInt : (Int64.ofInt (poff.toInt + ((4 * wordIdx : Nat) : Int))).toInt =
      poff.toInt + ((4 * wordIdx : Nat) : Int) :=
    int64_ofInt_toInt (by have := (inBounds_iff.mp hin).1; omega) hlt63
  have hal : Mem.isAligned blk0 (Int64.ofInt (poff.toInt + ((4 * wordIdx : Nat) : Int))) 4 = true :=
    isAligned_add hal0 (Nat.dvd_mul_right 4 wordIdx) hlt63
  obtain ⟨bv, hrv⟩ := readVal_int_of_bytes tags (k := .u32) hm_pb hal hoff_in (fun i hi => by
    have hi4 : i < 4 := hi
    rw [hoff_toInt]
    have heqn : (poff.toInt + ((4 * wordIdx : Nat) : Int)).toNat + i = poff.toInt.toNat + (4 * wordIdx + i) := by
      have := (inBounds_iff.mp hin).1
      omega
    rw [heqn]
    exact hbytes (4 * wordIdx + i) (by omega))
  have hrv' : Sem.readVal tags m pb (Int64.ofInt (poff.toInt + 4 * wordIdx))
      (.const_ (.typedef "z_word_t" (.int .u32))) = some (.int .u32 bv) := by
    have hcast : ((4 * wordIdx : Nat) : Int) = 4 * (wordIdx : Int) := by push_cast; rfl
    rw [← hcast]
    unfold Sem.readVal at hrv ⊢
    simpa [CTy.unqual] using hrv
  exact ⟨bv, hrv'⟩

/-- Typed local/parameter integer slot in `(env, m)`. -/
def IntSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty : CTy)
    (k : IntKind) (v : BitVec k.bits) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .int k ∧
  ty.isConst = false ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 k.align = true ∧ Mem.inBounds blk 0 k.bytes = true ∧
    Sem.readVal [] m b 0 ty = some (.int k v)

def UninitIntSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty : CTy)
    (k : IntKind) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .int k ∧
  ty.isConst = false ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 k.align = true ∧ Mem.inBounds blk 0 k.bytes = true

def PtrSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty el : CTy)
    (p : Val) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .ptr el ∧
  ty.isConst = false ∧
  (p = .null ∨ ∃ pb poff, p = .ptr pb poff) ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 8 = true ∧ Mem.inBounds blk 0 8 = true ∧
    Sem.readVal [] m b 0 ty = some p

def UninitPtrSlot (env : Env) (m : Mem) (name : String) (b : BlockId) (ty el : CTy) : Prop :=
  env.lookup name = some (b, ty) ∧
  ty.unqual = .ptr el ∧
  ty.isConst = false ∧
  ∃ blk, m.blocks b = some blk ∧ blk.perm = .rw ∧
    Mem.isAligned blk 0 8 = true ∧ Mem.inBounds blk 0 8 = true

theorem IntSlot.to_uninit {env m name b ty k v} (h : IntSlot env m name b ty k v) :
    UninitIntSlot env m name b ty k :=
  ⟨h.1, h.2.1, h.2.2.1, let ⟨blk, h1, h2, h3, h4, _⟩ := h.2.2.2; ⟨blk, h1, h2, h3, h4⟩⟩

theorem PtrSlot.to_uninit {env m name b ty el p} (h : PtrSlot env m name b ty el p) :
    UninitPtrSlot env m name b ty el :=
  ⟨h.1, h.2.1, h.2.2.1, let ⟨blk, h1, h2, h3, h4, _⟩ := h.2.2.2.2; ⟨blk, h1, h2, h3, h4⟩⟩

theorem IntSlot.readVal_eq (tags : TypeEnv) {env m name b ty k v}
    (h : IntSlot env m name b ty k v) :
    Sem.readVal tags m b 0 ty = some (.int k v) := by
  rcases h.2.2.2 with ⟨_, _, _, _, _, hrv⟩
  have heq : Sem.readVal tags m b 0 ty = Sem.readVal [] m b 0 ty := by
    unfold Sem.readVal; simp only [h.2.1]
  rw [heq, hrv]

theorem PtrSlot.readVal_eq (tags : TypeEnv) {env m name b ty el p}
    (h : PtrSlot env m name b ty el p) :
    Sem.readVal tags m b 0 ty = some p := by
  rcases h.2.2.2.2 with ⟨_, _, _, _, _, hrv⟩
  have heq : Sem.readVal tags m b 0 ty = Sem.readVal [] m b 0 ty := by
    unfold Sem.readVal; simp only [h.2.1]
  rw [heq, hrv]

theorem UninitIntSlot.write {m0 m : Mem} {blks : List BlockId} {env name b ty k}
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
  refine ⟨m', hm', hf', hlu, hk, hnc, _, hblk', hrw, by simpa [Mem.isAligned] using hal,
    by simpa [Mem.inBounds, writeBytes_blocks_eq] using hin, hrv⟩

theorem IntSlot.write {m0 m : Mem} {blks : List BlockId} {env name b ty k v}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hs : IntSlot env m name b ty k v) (v' : BitVec k.bits) :
    ∃ m', Sem.writeVal m b 0 ty (.int k v') = some m' ∧
      LocalFrameMem m0 m' blks ∧ IntSlot env m' name b ty k v' :=
  hs.to_uninit.write hf hmem v'

theorem isAligned_with_bytes (blk : Block) (f : Nat → MemByte) (off : Int64) (al : Nat)
    (hs : blk.size < ptrDiffLimit) (ha : 0 < blk.align) (hb : blk.baseAddr.toNat % blk.align = 0) :
    Mem.isAligned { blk with bytes := f, sizeLt := hs, alignPos := ha, baseAligned := hb } off al =
      Mem.isAligned blk off al := rfl

theorem inBounds_with_bytes (blk : Block) (f : Nat → MemByte) (off : Int64) (len : Nat)
    (hs : blk.size < ptrDiffLimit) (ha : 0 < blk.align) (hb : blk.baseAddr.toNat % blk.align = 0) :
    Mem.inBounds { blk with bytes := f, sizeLt := hs, alignPos := ha, baseAligned := hb } off len =
      Mem.inBounds blk off len := rfl

theorem UninitPtrSlot.write {m0 m : Mem} {blks : List BlockId} {env name b ty el}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hs : UninitPtrSlot env m name b ty el) {p' : Val}
    (hp' : p' = .null ∨ ∃ pb poff, p' = .ptr pb poff) :
    ∃ m', Sem.writeVal m b 0 ty p' = some m' ∧
      LocalFrameMem m0 m' blks ∧ PtrSlot env m' name b ty el p' := by
  rcases hs with ⟨hlu, hptr, hnc, blk, hblk, hrw, hal, hin⟩
  obtain ⟨m', hm'⟩ := writeVal_ptr_some hnc hptr hblk hrw hal hin hp'
  obtain ⟨bs, hbs_wr, hblk'⟩ := writeVal_blocks_eq hblk hm'
  have hf' := hf.write_stack hmem hblk hbs_wr
  have hrv : Sem.readVal [] m' b 0 ty = some p' := by
    rcases hp' with rfl | ⟨pb, poff, rfl⟩
    · have hwb : m.writeBytes b 0 Mem.encodeNull = some m' := by
        unfold Sem.writeVal at hm'
        simpa [hnc, hptr, hblk, hal] using hm'
      have hrd := readBytes_writeBytes_same hblk hwb
      rw [encodeNull_length] at hrd
      unfold Sem.readVal
      simp only [hptr, hblk', hrd, bind, Option.bind, pure, Pure.pure]
      rw [isAligned_with_bytes, hal]
      simp
    · have hwb : m.writeBytes b 0 (Mem.encodePtr pb poff) = some m' := by
        unfold Sem.writeVal at hm'
        simpa [hnc, hptr, hblk, hal] using hm'
      have hrd := readBytes_writeBytes_same hblk hwb
      rw [encodePtr_length] at hrd
      unfold Sem.readVal
      simp only [hptr, hblk', hrd, bind, Option.bind, pure, Pure.pure]
      rw [isAligned_with_bytes, hal]
      simp
  refine ⟨m', hm', hf', hlu, hptr, hnc, hp', _, hblk', hrw, by simpa [Mem.isAligned] using hal,
    by simpa [Mem.inBounds] using hin, hrv⟩

theorem PtrSlot.write {m0 m : Mem} {blks : List BlockId} {env name b ty el p}
    (hf : LocalFrameMem m0 m blks) (hmem : b ∈ blks)
    (hs : PtrSlot env m name b ty el p) {p' : Val}
    (hp' : p' = .null ∨ ∃ pb poff, p' = .ptr pb poff) :
    ∃ m', Sem.writeVal m b 0 ty p' = some m' ∧
      LocalFrameMem m0 m' blks ∧ PtrSlot env m' name b ty el p' :=
  hs.to_uninit.write hf hmem hp'

theorem IntSlot.preserve_ne {env m m' name b b' ty k v ty' v'}
    (hs : IntSlot env m name b ty k v) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    IntSlot env m' name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  have hbeq : m'.blocks b = some blk := by rw [writeVal_blocks_ne hwr hne, hblk]
  refine ⟨hlu, hk, hnc, blk, hbeq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := writeVal_blocks_ne hwr hne)]
  exact hrv

theorem UninitIntSlot.preserve_ne {env m m' name b b' ty k ty' v'}
    (hs : UninitIntSlot env m name b ty k) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    UninitIntSlot env m' name b ty k := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  exact ⟨hlu, hk, hnc, blk, by rw [writeVal_blocks_ne hwr hne, hblk], hrw, hal, hin⟩

theorem PtrSlot.preserve_ne {env m m' name b b' ty el p ty' v'}
    (hs : PtrSlot env m name b ty el p) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    PtrSlot env m' name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  have hbeq : m'.blocks b = some blk := by rw [writeVal_blocks_ne hwr hne, hblk]
  refine ⟨hlu, hptr, hnc, hp, blk, hbeq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := writeVal_blocks_ne hwr hne)]
  exact hrv

theorem UninitPtrSlot.preserve_ne {env m m' name b b' ty el ty' v'}
    (hs : UninitPtrSlot env m name b ty el) (hwr : Sem.writeVal m b' 0 ty' v' = some m') (hne : b ≠ b') :
    UninitPtrSlot env m' name b ty el := by
  rcases hs with ⟨hlu, hptr, hnc, blk, hblk, hrw, hal, hin⟩
  exact ⟨hlu, hptr, hnc, blk, by rw [writeVal_blocks_ne hwr hne, hblk], hrw, hal, hin⟩

theorem IntSlot.preserve_roExt {env m m' name b ty k v}
    (hs : IntSlot env m name b ty k v) (hro : ROExt m m') :
    IntSlot env m' name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  have hbeq : m'.blocks b = some blk := by rw [hro.2.1 b (lt_nextBlock_of_some hblk), hblk]
  refine ⟨hlu, hk, hnc, blk, hbeq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := hbeq.trans hblk.symm)]
  exact hrv

theorem PtrSlot.preserve_roExt {env m m' name b ty el p}
    (hs : PtrSlot env m name b ty el p) (hro : ROExt m m') :
    PtrSlot env m' name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  have hbeq : m'.blocks b = some blk := by rw [hro.2.1 b (lt_nextBlock_of_some hblk), hblk]
  refine ⟨hlu, hptr, hnc, hp, blk, hbeq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := hbeq.trans hblk.symm)]
  exact hrv

theorem UninitIntSlot.preserve_roExt {env m m' name b ty k}
    (hs : UninitIntSlot env m name b ty k) (hro : ROExt m m') :
    UninitIntSlot env m' name b ty k := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  exact ⟨hlu, hk, hnc, blk, by rw [hro.2.1 b (lt_nextBlock_of_some hblk), hblk], hrw, hal, hin⟩

theorem IntSlot.preserve_freeStack {env m name b ty k v drop}
    (hs : IntSlot env m name b ty k v) (hnot : b ∉ drop) :
    IntSlot env (m.freeStack drop) name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  have hbeq : (m.freeStack drop).blocks b = some blk := by
    rw [freeStack_blocks_not_mem m drop hnot, hblk]
  refine ⟨hlu, hk, hnc, blk, hbeq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := hbeq.trans hblk.symm)]
  exact hrv

theorem PtrSlot.preserve_freeStack {env m name b ty el p drop}
    (hs : PtrSlot env m name b ty el p) (hnot : b ∉ drop) :
    PtrSlot env (m.freeStack drop) name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  have hbeq : (m.freeStack drop).blocks b = some blk := by
    rw [freeStack_blocks_not_mem m drop hnot, hblk]
  refine ⟨hlu, hptr, hnc, hp, blk, hbeq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := hbeq.trans hblk.symm)]
  exact hrv

theorem IntSlot.preserve_alloc {env m m1 name b ty k v sz al p kind ba init h1 h2 h3 bid}
    (hs : IntSlot env m name b ty k v)
    (ha : m.alloc sz al p kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    IntSlot ((nm', bid, ty') :: env) m1 name b ty k v := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin, hrv⟩
  have hm1 : m1 = (m.alloc sz al p kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  have hb_eq : m1.blocks b = some blk := by
    rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hblk]
  refine ⟨by rw [lookup_cons_ne env hnm, hlu], hk, hnc, blk, hb_eq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := hb_eq.trans hblk.symm)]
  exact hrv

theorem PtrSlot.preserve_alloc {env m m1 name b ty el p sz al perm kind ba init h1 h2 h3 bid}
    (hs : PtrSlot env m name b ty el p)
    (ha : m.alloc sz al perm kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    PtrSlot ((nm', bid, ty') :: env) m1 name b ty el p := by
  rcases hs with ⟨hlu, hptr, hnc, hp, blk, hblk, hrw, hal, hin, hrv⟩
  have hm1 : m1 = (m.alloc sz al perm kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  have hb_eq : m1.blocks b = some blk := by
    rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hblk]
  refine ⟨by rw [lookup_cons_ne env hnm, hlu], hptr, hnc, hp, blk, hb_eq, hrw, hal, hin, ?_⟩
  rw [readVal_eq_of_blocks_eq [] (hb := hb_eq.trans hblk.symm)]
  exact hrv

theorem UninitIntSlot.preserve_alloc {env m m1 name b ty k sz al perm kind ba init h1 h2 h3 bid}
    (hs : UninitIntSlot env m name b ty k)
    (ha : m.alloc sz al perm kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    UninitIntSlot ((nm', bid, ty') :: env) m1 name b ty k := by
  rcases hs with ⟨hlu, hk, hnc, blk, hblk, hrw, hal, hin⟩
  have hm1 : m1 = (m.alloc sz al perm kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  exact ⟨by rw [lookup_cons_ne env hnm, hlu], hk, hnc, blk,
    by rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hblk], hrw, hal, hin⟩

theorem UninitPtrSlot.preserve_alloc {env m m1 name b ty el sz al perm kind ba init h1 h2 h3 bid}
    (hs : UninitPtrSlot env m name b ty el)
    (ha : m.alloc sz al perm kind ba init h1 h2 h3 = (bid, m1))
    {nm' ty'} (hnm : name ≠ nm') :
    UninitPtrSlot ((nm', bid, ty') :: env) m1 name b ty el := by
  rcases hs with ⟨hlu, hptr, hnc, blk, hblk, hrw, hal, hin⟩
  have hm1 : m1 = (m.alloc sz al perm kind ba init h1 h2 h3).2 := (congrArg Prod.snd ha).symm
  have hne : b ≠ m.nextBlock := Nat.ne_of_lt (lt_nextBlock_of_some hblk)
  exact ⟨by rw [lookup_cons_ne env hnm, hlu], hptr, hnc, blk,
    by rw [hm1, alloc_blocks_ne _ _ _ _ _ _ _ _ _ _ hne, hblk], hrw, hal, hin⟩

theorem IntSlot.preserve_localDecl_none {tags : TypeEnv} {env m m1 name b ty k v}
    (hs : IntSlot env m name b ty k v)
    {d : VarDecl} {ba : UInt64} {bid : BlockId} {hsz : max 1 (sizeofTy tags d.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags d.ty)} {hba : ba.toNat % max 1 (alignofTy tags d.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba = (bid, m1))
    (hnm : name ≠ d.name) :
    IntSlot ((d.name, bid, d.ty) :: env) m1 name b ty k v :=
  hs.preserve_alloc ha hnm

theorem PtrSlot.preserve_localDecl_none {tags : TypeEnv} {env m m1 name b ty el p}
    (hs : PtrSlot env m name b ty el p)
    {d : VarDecl} {ba : UInt64} {bid : BlockId} {hsz : max 1 (sizeofTy tags d.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags d.ty)} {hba : ba.toNat % max 1 (alignofTy tags d.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba = (bid, m1))
    (hnm : name ≠ d.name) :
    PtrSlot ((d.name, bid, d.ty) :: env) m1 name b ty el p :=
  hs.preserve_alloc ha hnm

theorem UninitIntSlot.of_alloc_int {tags : TypeEnv} {env : Env} {m m1 : Mem} {d : VarDecl}
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

theorem UninitPtrSlot.of_alloc_ptr {tags : TypeEnv} {env : Env} {m m1 : Mem} {d : VarDecl}
    {el : CTy} (hptr : d.ty.unqual = .ptr el) (hnc : d.ty.isConst = false)
    {ba : UInt64} {bid : BlockId}
    {hsz : max 1 (sizeofTy tags d.ty) < ptrDiffLimit}
    {hal : 0 < max 1 (alignofTy tags d.ty)}
    {hba : ba.toNat % max 1 (alignofTy tags d.ty) = 0}
    (ha : m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
      .rw .stack ba (fun _ => .undef) hsz hal hba = (bid, m1)) :
    UninitPtrSlot ((d.name, bid, d.ty) :: env) m1 d.name bid d.ty el := by
  have hbid : bid = m.nextBlock := (congrArg Prod.fst ha).symm
  have hm1 : m1 = (m.alloc (max 1 (sizeofTy tags d.ty)) (max 1 (alignofTy tags d.ty))
    .rw .stack ba (fun _ => .undef) hsz hal hba).2 := (congrArg Prod.snd ha).symm
  have hsz_eq : sizeofTy tags d.ty = 8 := by rw [← sizeofTy_unqual, hptr]; simp
  have hal_eq : alignofTy tags d.ty = 8 := by rw [← alignofTy_unqual, hptr]; simp
  subst bid
  refine ⟨lookup_cons_eq env, hptr, hnc, _, by rw [hm1]; exact alloc_blocks_eq _ _ _ _ _ _ _ _ _ _, rfl, ?_, ?_⟩
  · rw [isAligned_iff]
    refine ⟨Int.le_refl _, by decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
    simpa [hal_eq] using hba
  · rw [inBounds_iff]
    refine ⟨Int.le_refl _, ?_⟩
    simp [Int64.toInt_zero, hsz_eq]

theorem IntSlot.of_pushCallParam {tags : TypeEnv} {m m2 : Mem} {p : Param} {k : IntKind}
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

theorem PtrSlot.of_pushCallParam {tags : TypeEnv} {m m2 : Mem} {p : Param} {el : CTy}
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
  let blk1 : Block := ⟨max 1 (sizeofTy tags p.ty), max 1 (alignofTy tags p.ty),
    .rw, .stack, ba, (fun _ => .undef), hsz, hal, hba⟩
  let m1 := (m.alloc (max 1 (sizeofTy tags p.ty)) (max 1 (alignofTy tags p.ty))
    .rw .stack ba (fun _ => .undef) hsz hal hba).2
  have hblk1 : m1.blocks m.nextBlock = some blk1 :=
    alloc_blocks_eq _ _ _ _ _ _ _ _ _ _
  have hsz_eq : sizeofTy tags p.ty = 8 := by rw [← sizeofTy_unqual, hptr]; simp
  have hal_eq : alignofTy tags p.ty = 8 := by rw [← alignofTy_unqual, hptr]; simp
  have hwr' : Sem.writeVal m1 m.nextBlock 0 (.ptr el) vp = some m2 := by
    unfold Sem.writeVal at hwr ⊢
    simp only [stripConst_isConst, CTy.isConst, Bool.not_false, guard_true, bind, Option.bind,
      stripConst_unqual, hptr] at hwr ⊢
    exact hwr
  obtain ⟨bs, _, hblk2⟩ := writeVal_blocks_eq hblk1 hwr'
  have hal1 : Mem.isAligned blk1 0 8 = true := by
    rw [isAligned_iff]
    refine ⟨Int.le_refl _, by decide, ?_⟩
    rw [Int64.toInt_zero, Int.toNat_zero, Nat.add_zero]
    simpa [blk1, hal_eq] using hba
  have hrv : Sem.readVal [] m2 m.nextBlock 0 p.ty = some vp := by
    rcases hvp with rfl | ⟨pb, poff, rfl⟩
    · have hwb : m1.writeBytes m.nextBlock 0 Mem.encodeNull = some m2 := by
        unfold Sem.writeVal at hwr'
        simpa [CTy.isConst, CTy.unqual, hblk1, hal1] using hwr'
      have hrd := readBytes_writeBytes_same hblk1 hwb
      rw [encodeNull_length] at hrd
      unfold Sem.readVal
      simp only [hptr, hblk2, hrd, bind, Option.bind, pure, Pure.pure]
      rw [isAligned_with_bytes, hal1]
      simp
    · have hwb : m1.writeBytes m.nextBlock 0 (Mem.encodePtr pb poff) = some m2 := by
        unfold Sem.writeVal at hwr'
        simpa [CTy.isConst, CTy.unqual, hblk1, hal1] using hwr'
      have hrd := readBytes_writeBytes_same hblk1 hwb
      rw [encodePtr_length] at hrd
      unfold Sem.readVal
      simp only [hptr, hblk2, hrd, bind, Option.bind, pure, Pure.pure]
      rw [isAligned_with_bytes, hal1]
      simp
  refine ⟨lookup_cons_eq env, hptr, hnc, hvp, _, hblk2, rfl, hal1, ?_, hrv⟩
  rw [inBounds_iff]
  refine ⟨Int.le_refl _, ?_⟩
  simp [blk1, Int64.toInt_zero, hsz_eq]

theorem IntSlot.ne_of_lt_nextBlock {env m name b ty k v}
    (hs : IntSlot env m name b ty k v) : b < m.nextBlock :=
  let ⟨_, hblk, _⟩ := hs.2.2.2; lt_nextBlock_of_some hblk

theorem PtrSlot.ne_of_lt_nextBlock {env m name b ty el p}
    (hs : PtrSlot env m name b ty el p) : b < m.nextBlock :=
  let ⟨_, hblk, _⟩ := hs.2.2.2.2; lt_nextBlock_of_some hblk

theorem UninitIntSlot.ne_of_lt_nextBlock {env m name b ty k}
    (hs : UninitIntSlot env m name b ty k) : b < m.nextBlock :=
  let ⟨_, hblk, _⟩ := hs.2.2.2; lt_nextBlock_of_some hblk

theorem UninitPtrSlot.ne_of_lt_nextBlock {env m name b ty el}
    (hs : UninitPtrSlot env m name b ty el) : b < m.nextBlock :=
  let ⟨_, hblk, _⟩ := hs.2.2.2; lt_nextBlock_of_some hblk

theorem sizeofTy_eq_bytes {tags : TypeEnv} {ty : CTy} {k : IntKind} (hk : ty.unqual = .int k) :
    sizeofTy tags ty = k.bytes := by
  rw [← sizeofTy_unqual, hk]; simp

theorem sizeofTy_eq_ptr {tags : TypeEnv} {ty el : CTy} (hp : ty.unqual = .ptr el) :
    sizeofTy tags ty = 8 := by
  rw [← sizeofTy_unqual, hp]; simp

theorem CTy.decay_of_int {k : IntKind} :
    ∀ {ty : CTy}, ty.unqual = .int k → ty.decay.unqual = .int k
  | .const_ t, hk => by simp [CTy.decay, CTy.unqual] at hk ⊢; exact CTy.decay_of_int hk
  | .typedef _ t, hk => by simp [CTy.decay, CTy.unqual] at hk ⊢; exact CTy.decay_of_int hk
  | .int k', hk => by simp [CTy.decay, CTy.unqual] at hk ⊢; exact hk
  | .void, hk | .ptr _, hk | .array _ _, hk | .structTy _, hk | .unionTy _, hk
  | .anonStruct _, hk | .anonUnion _, hk | .enumTy _ _, hk | .fnPtr _ _ _, hk | .vaList, hk => by
    simp [CTy.unqual] at hk

theorem CTy.decay_of_ptr {el : CTy} :
    ∀ {ty : CTy}, ty.unqual = .ptr el → ty.decay.unqual = .ptr el
  | .const_ t, hp => by simp [CTy.decay, CTy.unqual] at hp ⊢; exact CTy.decay_of_ptr hp
  | .typedef _ t, hp => by simp [CTy.decay, CTy.unqual] at hp ⊢; exact CTy.decay_of_ptr hp
  | .ptr el', hp => by simp [CTy.decay, CTy.unqual] at hp ⊢; exact hp
  | .void, hp | .int _, hp | .array _ _, hp | .structTy _, hp | .unionTy _, hp
  | .anonStruct _, hp | .anonUnion _, hp | .enumTy _ _, hp | .fnPtr _ _ _, hp | .vaList, hp => by
    simp [CTy.unqual] at hp

theorem readPlace_intSlot {tags : TypeEnv} {env : Env} {m : Mem} {mods : ModSet}
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

theorem readPlace_ptrSlot {tags : TypeEnv} {env : Env} {m : Mem} {mods : ModSet}
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

theorem writePlace_int {tags : TypeEnv} {m m' : Mem} {b : BlockId} {ty : CTy}
    {k : IntKind} {v : BitVec k.bits} {rty : CTy}
    (hk : ty.unqual = .int k) (hwr : Sem.writeVal m b 0 ty (.int k v) = some m') :
    writePlace tags m b 0 ty (.rval (.int k v) rty) = some (.rval (.int k v) ty, m') := by
  unfold writePlace
  have hcast : Sem.castVal m ty (.int k v) = some (.int k v) := by
    rw [castVal_unqual, hk]
    simp only [castVal_int, ofIntCast]
    by_cases hs : k.signed <;> simp [hs]
  rw [hk]
  simp only [hcast, bind, Option.bind, pure, Pure.pure, hwr]

theorem writePlace_ptr {tags : TypeEnv} {m m' : Mem} {b : BlockId} {ty el : CTy}
    {p : Val} (hp : p = .null ∨ ∃ pb poff, p = .ptr pb poff) {rty : CTy}
    (hptr : ty.unqual = .ptr el) (hwr : Sem.writeVal m b 0 ty p = some m') :
    writePlace tags m b 0 ty (.rval p rty) = some (.rval p ty, m') := by
  unfold writePlace
  have hcast : Sem.castVal m ty p = some p := by
    rw [castVal_unqual, hptr]
    rcases hp with rfl | ⟨pb, poff, rfl⟩ <;> simp
  rw [hptr]
  simp only [hcast, bind, Option.bind, pure, Pure.pure, hwr]

theorem modSet_conflicts_nil (b : BlockId) (o : Int64) (n : Nat) :
    ModSet.conflicts [] b o n = false := rfl

theorem modSet_conflicts_cons_ne {b b' : BlockId} {o o' : Int64} {n n' : Nat} {ms : ModSet}
    (hne : b' ≠ b) (hrest : ms.conflicts b o n = false) :
    ModSet.conflicts (⟨b', o', n'⟩ :: ms) b o n = false := by
  unfold ModSet.conflicts at hrest ⊢
  simp only [List.any_cons, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
  exact ⟨Or.inl (beq_false_of_ne hne), hrest⟩

theorem applyBinary_int {cfg : PointerConfig} {tags : TypeEnv} {m : Mem}
    {op : BinOp} {v1 v2 : Val} {t1 t2 : CTy}
    {k1 k2 : IntKind} (ht1 : t1.unqual = .int k1) (ht2 : t2.unqual = .int k2) :
    applyBinary cfg tags m op v1 t1 v2 t2 = evalIntBinary op v1 v2 := by
  unfold applyBinary
  simp [CTy.isPtr, ht1, ht2]

theorem wp_read_int {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {nm : String} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {b : BlockId} {ty : CTy} {ik : IntKind} {v : BitVec ik.bits}
    (hs : IntSlot env m nm b ty ik v) (hnc : mods.conflicts b 0 ik.bytes = false)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.int ik v) ty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.var nm) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by simp [stepExprPure, hs.1, readPlace_intSlot hs hnc]) hw

theorem wp_read_ptr {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {nm : String} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {b : BlockId} {ty el : CTy} {p : Val}
    (hs : PtrSlot env m nm b ty el p) (hnc : mods.conflicts b 0 8 = false)
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval p ty.decay) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.var nm) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by simp [stepExprPure, hs.1, readPlace_ptrSlot hs hnc]) hw

theorem wp_lval_var {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {nm : String} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {b : BlockId} {ty : CTy}
    (hlu : env.lookup nm = some (b, ty))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.lval b 0 ty) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .lval (.var nm) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by simp [stepExprPure, hlu]) hw

theorem wp_call_var {prog : Prog} {cfg : PointerConfig} {ext : ExtHandler}
    {Q : Val → Mem → OSState → Prop}
    {nm : String} {fs : List Sem.ExprFrame} {ctx : Sem.ExprCtx} {mods : ModSet}
    {env : Env} {blks : List BlockId} {m : Mem} {os : OSState} {k : Sem.Cont}
    {rty : CTy} {ptys : List CTy} {va : Bool}
    (hlu : env.lookup nm = none)
    (henum : enumConst? prog.tags nm = none)
    (hproto : prog.fnProtos nm = some (rty, ptys, va))
    (hw : WPTerm prog cfg ext Q
      (.running (.expr (.ret (.rval (.fnPtr nm) (.fnPtr rty ptys va)) fs) ctx mods) env blks m os k)) :
    WPTerm prog cfg ext Q
      (.running (.expr (.eval .rval (.var nm) fs) ctx mods) env blks m os k) :=
  WPTerm.of_exprPure (by simp [stepExprPure, hlu, henum, hproto]) hw

theorem endian_read_u8_one (tags : TypeEnv) {m_prev m : Mem} {b : BlockId}
    {blk : Block} (hb : m_prev.blocks b = some blk)
    (hwr : Sem.writeVal m_prev b 0 (.int .u32) (.int .u32 1#32) = some m) :
    Sem.readVal tags m b 0 (.int .u8) = some (.int .u8 1#8) := by
  have henc : Mem.encodeInt .u32 1#32 = [.byte 1, .byte 0, .byte 0, .byte 0] := by decide
  have hwb' : m_prev.writeBytes b 0 [.byte 1, .byte 0, .byte 0, .byte 0] = some m := by
    unfold Sem.writeVal at hwr
    simp only [CTy.isConst, Bool.not_false, hb, CTy.unqual, CTy.intKind?, valAsInt?,
      bind, Option.bind, guard, Pure.pure, IntKind.align, IntKind.bytes, IntKind.bits] at hwr
    cases ha : Mem.isAligned blk 0 4
    · simp [ha] at hwr
    · have h1 : BitVec.ofInt 32 (if IntKind.u32.signed = true then (1#32 : BitVec 32).toInt
          else ((1#32 : BitVec 32).toNat : Int)) = 1#32 := by decide
      simp only [ha, ↓reduceIte] at hwr
      rw [h1, henc] at hwr
      exact hwr
  have hin4 : Mem.inBounds blk 0 4 = true := by
    unfold Mem.writeBytes at hwb'
    split at hwb'
    · contradiction
    · next blk0 hblk0 =>
      rw [hb] at hblk0
      injection hblk0 with hblk0
      subst hblk0
      simp at hwb'
      exact hwb'.1.2
  have hin1 : Mem.inBounds blk 0 1 = true := inBounds_mono hin4 (by decide)
  have h0 : 0 ≤ (0 : Int64).toInt := by simp
  have hblk_eq := writeBytes_blocks_eq hb hwb'
  have hin1' : Mem.inBounds { blk with bytes := (fun i =>
      if (0 : Int64).toInt.toNat ≤ i ∧ i < (0 : Int64).toInt.toNat + ([MemByte.byte 1, MemByte.byte 0, MemByte.byte 0, MemByte.byte 0] : List MemByte).length then
        ([MemByte.byte 1, MemByte.byte 0, MemByte.byte 0, MemByte.byte 0] : List MemByte)[i - (0 : Int64).toInt.toNat]?.getD .undef
      else blk.bytes i) } 0 1 = true := by
    rw [inBounds_with_bytes]; exact hin1
  have hrd1 : m.readBytes b 0 IntKind.u8.bytes = some [.byte 1] := by
    change m.readBytes b 0 1 = some [.byte 1]
    rw [readBytes_of_bounds hblk_eq hin1']
    rfl
  have hal1 : Mem.isAligned { blk with bytes := (fun i =>
      if (0 : Int64).toInt.toNat ≤ i ∧ i < (0 : Int64).toInt.toNat + ([MemByte.byte 1, MemByte.byte 0, MemByte.byte 0, MemByte.byte 0] : List MemByte).length then
        ([MemByte.byte 1, MemByte.byte 0, MemByte.byte 0, MemByte.byte 0] : List MemByte)[i - (0 : Int64).toInt.toNat]?.getD .undef
      else blk.bytes i) } 0 IntKind.u8.align = true := isAligned_one h0
  have hdec : Mem.decodeInt .u8 [.byte 1] = some (1#8 : BitVec IntKind.u8.bits) := rfl
  unfold Sem.readVal
  simp only [CTy.unqual, CTy.intKind?, hblk_eq, hal1, guard_true, hrd1, hdec,
    bind, Option.bind, pure, Pure.pure]

/-! ## 3. Global Table Read Helpers in `LocalFrameMem` -/

theorem int64_ofNat_toInt {n : Nat} (hlt : (n : Int) < 2 ^ 63) :
    (Int64.ofNat n).toInt = (n : Int) := by
  have heq : (Int64.ofNat n).toBitVec = BitVec.ofInt 64 (n : Int) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 n).toNat = (BitVec.ofInt 64 (n : Int)).toNat
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt,
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    omega
  change (Int64.ofNat n).toBitVec.toInt = (n : Int)
  rw [heq, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

theorem readVal_crc_table {prog : Prog} {gEnv : Env} {m0 m0' m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet} {blks : List BlockId}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m0' os)
    (hf : LocalFrameMem m0' m blks) :
    ∃ b, gEnv.lookup "crc_table" = some (b, .array crcConstTy (some 256)) ∧
      b < m0'.nextBlock ∧
      ∀ idx < 256, ∃ bv : BitVec 32,
        Sem.readVal prog.tags m b (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv) := by
  obtain ⟨b, blk, hlu, hblk, _, _, hsz, hal, hbytes⟩ := hb.crc_table hlib
  have hlt : b < m0'.nextBlock := lt_nextBlock_of_some hblk
  have hm : m.blocks b = some blk := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt, hblk]
  refine ⟨b, hlu, hlt, fun idx hidx => ?_⟩
  have hlt63 : (Int64.ofNat (4 * idx)).toInt = ((4 * idx : Nat) : Int) :=
    int64_ofNat_toInt (by omega)
  have hba : blk.baseAddr.toNat % 4 = 0 := by rw [← hal]; exact blk.baseAligned
  have hal_off : Mem.isAligned blk (Int64.ofNat (4 * idx)) 4 = true := by
    rw [isAligned_iff, hlt63]
    refine ⟨by omega, by decide, ?_⟩
    have hnat : ((4 * idx : Nat) : Int).toNat = 4 * idx := by omega
    rw [hnat, Nat.add_mod, hba, Nat.zero_add,
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 4 idx)]
  have hin_off : Mem.inBounds blk (Int64.ofNat (4 * idx)) 4 = true := by
    rw [inBounds_iff, hlt63, hsz]
    omega
  obtain ⟨bv, hrv⟩ := readVal_int_of_bytes prog.tags (k := .u32) hm hal_off hin_off
    (fun i _ => hbytes _)
  refine ⟨bv, ?_⟩
  unfold Sem.readVal at hrv ⊢
  simpa [crcConstTy, CTy.unqual] using hrv

theorem readVal_x2n_table {prog : Prog} {gEnv : Env} {m0 m0' m : Mem} {os0 os : OSState}
    {v : ClientView} {owned : BlockSet} {blks : List BlockId}
    (hlib : InitLibzProps prog gEnv m0 os0)
    (hb : BaseInv m0 os0 v owned m0' os)
    (hf : LocalFrameMem m0' m blks) :
    ∃ b, gEnv.lookup "x2n_table" = some (b, .array crcConstTy (some 32)) ∧
      b < m0'.nextBlock ∧
      ∀ idx < 32, ∃ bv : BitVec 32,
        Sem.readVal prog.tags m b (Int64.ofNat (4 * idx)) crcConstTy = some (.int .u32 bv) ∧
        bv = BitVec.ofInt 32 Zlib.Tables.x2nTableVals[idx]! ∧
        bv.toNat ≠ 0 := by
  obtain ⟨b, blk, hlu, hblk, _, _, _, _, _, hread⟩ := hb.x2n_table hlib
  have hlt : b < m0'.nextBlock := lt_nextBlock_of_some hblk
  have hm : m.blocks b = m0'.blocks b := LocalFrameMem.blocks_eq_of_lt hf hlt
  refine ⟨b, hlu, hlt, fun idx hidx => ?_⟩
  obtain ⟨bv, hrv, hval, hnz⟩ := hread idx hidx
  refine ⟨bv, ?_, hval, hnz⟩
  rw [readVal_eq_of_blocks_eq prog.tags hm]
  unfold Sem.readVal at hrv ⊢
  simpa [crcConstTy, CTy.unqual] using hrv

theorem readVal_crc_braid_table {prog : Prog} {gEnv : Env} {m0' m : Mem}
    {blks : List BlockId}
    {name : String} {b : BlockId} {blk : Block}
    (hb : m0'.blocks b = some blk) (hsz : blk.size = 4096) (hal : blk.align = 4)
    (hbytes : ∀ i, ∃ u : UInt8, blk.bytes i = .byte u)
    (hf : LocalFrameMem m0' m blks)
    (hlu : gEnv.lookup name = some (b, .array (.array crcConstTy (some 256)) (some 4))) :
    gEnv.lookup name = some (b, .array (.array crcConstTy (some 256)) (some 4)) ∧
      b < m0'.nextBlock ∧
      ∀ row < 4, ∀ idx < 256, ∃ bv : BitVec 32,
        Sem.readVal prog.tags m b (Int64.ofNat (1024 * row + 4 * idx)) crcConstTy = some (.int .u32 bv) := by
  have hlt : b < m0'.nextBlock := lt_nextBlock_of_some hb
  have hm : m.blocks b = some blk := by rw [LocalFrameMem.blocks_eq_of_lt hf hlt, hb]
  refine ⟨hlu, hlt, fun row hrow idx hidx => ?_⟩
  have hlt63 : (Int64.ofNat (1024 * row + 4 * idx)).toInt = ((1024 * row + 4 * idx : Nat) : Int) :=
    int64_ofNat_toInt (by omega)
  have hdiv : 4 ∣ (1024 * row + 4 * idx) := by omega
  have hba : blk.baseAddr.toNat % 4 = 0 := by rw [← hal]; exact blk.baseAligned
  have hal_off : Mem.isAligned blk (Int64.ofNat (1024 * row + 4 * idx)) 4 = true := by
    rw [isAligned_iff, hlt63]
    refine ⟨by omega, by decide, ?_⟩
    have hnat : ((1024 * row + 4 * idx : Nat) : Int).toNat = 1024 * row + 4 * idx := by omega
    rw [hnat, Nat.add_mod, hba, Nat.zero_add,
      Nat.mod_eq_zero_of_dvd hdiv]
  have hin_off : Mem.inBounds blk (Int64.ofNat (1024 * row + 4 * idx)) 4 = true := by
    rw [inBounds_iff, hlt63, hsz]
    omega
  obtain ⟨bv, hrv⟩ := readVal_int_of_bytes prog.tags (k := .u32) hm hal_off hin_off
    (fun i _ => hbytes _)
  refine ⟨bv, ?_⟩
  unfold Sem.readVal at hrv ⊢
  simpa [crcConstTy, CTy.unqual] using hrv

end Zlib.Proof
