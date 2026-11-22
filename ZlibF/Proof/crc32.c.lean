import ZlibF.Zlib.«crc32.c»
import ZlibF.Spec.Functional.Format.Checksum
import ZlibF.Spec.Common.Crc32Statics

/-!
# crc32.c: safety and correctness

Every function of `crc32.c.lean` has a safety theorem (`*_safe`: no fault, the heap is unchanged, so every heap
invariant and frame is preserved; preconditions explicit) and a correctness theorem (`*_correct`: the value, against
`ZlibF.Spec.crc32Update` / `ZlibF.Spec.crc32` and `ZlibF.Spec.crcBit`, which do not mention the translation).

The heap hypothesis `StaticsOK` says that the static tables `crc_table` and `x2n_table` hold the contents `crc32.h`
fixes (`Zlib.Crc32.initStatics`). The other tables (`crc_braid5_table`, `crc_braid2_table`, `crc_big_table`,
`crc_braid5_big_table`, `crc_braid2_big_table`) are constants of the translation.

Method. A CRC register step is linear over GF(2) (`crcBit_xor`). `pw m` is `m` steps of `ZlibF.Spec.crcBit`
(multiplication by `x^m`). From the table contents (checked by kernel evaluation, `decide +kernel`, no axioms):
`crc_table[n] = pw 8 n` (`crc_table_eq`), `crc_braid5_table[j][n] = pw (8 * (20 - j)) n` (`braid5_eq`),
`crc_braid2_table[j][n] = pw (8 * (8 - j)) n` (`braid2_eq`), and the
squaring chain of `x2n_table` with `x^(2^32) = x` (`Xt_sq`, `Xt_wrap`). The word step of `crc_word` is a linear map of
32-bit words (`UInt32`) that agrees with the closed form `Psi` on the 32 unit vectors (`Phi_eq_Psi`), hence everywhere.
The 5-braid loop (`N = 5`, `W = 4`, `len >= 320`) keeps `Val c0 .. c4 = pw 160 R` (`loopBlk_ok`), and `crc32_braid`
(`NLOW = 2`, `W = 4`, `11 <= len < 320`) keeps `Val2 c0 c1 = pw 64 R` (`loopBlk2_ok`). The final chains of `crc_word`
calls then equal `rbFrom R ow 20` and `rbFrom R ow 8`. `multmodp` is multiplication in the algebra of registers (`mulp`):
bilinear, associative (`mulp_assoc`), with `mulp (x^m) v = pw m v` (`mulp_pw_left'`).

Pure heap preservation (`PureH`, `crc32_z_heap_unchanged`, `crc32_heap_unchanged`) holds unconditionally on every
non-faulting path of `crc32_z` and `crc32`.

Not covered: the big-endian helpers (`byte_swap`, `blockBig`, `blockBig2`, `crc_word_big`, dead at run time on the
target): only `crc_word_big_safe`; `byte_swap` is a total pure function with no correctness theorem; `blockBig` and
`blockBig2` have none.
-/

namespace Zlib.Crc32.Proofs
open C
open ZlibF.Spec (crcBit crcPoly)

/-! ### Bit lemmas -/

theorem u32_ext {x y : UInt32} (h : ∀ i, i < 32 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_getLsbD_eq h)

theorem u64_ext {x y : UInt64} (h : ∀ i, i < 64 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_getLsbD_eq h)

theorem and_xor32 (a b m : UInt32) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply u32_ext; intro i _
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

theorem and_xor64 (a b m : UInt64) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply u64_ext; intro i _
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

theorem and1_cases (x : UInt32) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [UInt32.toNat_and]; exact Nat.and_one_is_mod _
  rcases (by omega : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1) with h0 | h0
  · left; apply UInt32.toNat_inj.mp; simp [h, h0]
  · right; apply UInt32.toNat_inj.mp; simp [h, h0]

theorem xor_pp32 (a b p : UInt32) : (a ^^^ p) ^^^ (b ^^^ p) = a ^^^ b := by
  apply u32_ext; intro i _
  simp only [UInt32.toBitVec_xor, BitVec.getLsbD_xor]
  cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;> cases p.toBitVec.getLsbD i <;> rfl

theorem crcBit_xor (x y : UInt32) : crcBit (x ^^^ y) = crcBit x ^^^ crcBit y := by
  unfold crcBit
  have e : (x ^^^ y) &&& 1 = (x &&& 1) ^^^ (y &&& 1) := and_xor32 _ _ _
  rcases and1_cases x with hx | hx <;> rcases and1_cases y with hy | hy <;>
    simp [e, hx, hy, UInt32.shiftRight_xor, xor_pp32]
  · ac_rfl
  · ac_rfl

theorem crcBit_zero : crcBit 0 = 0 := by decide

/-- `m` register steps of the CRC (multiplication by `x^m` in the bit-reflected representation). -/
def pw : Nat → UInt32 → UInt32
  | 0, v => v
  | m + 1, v => pw m (ZlibF.Spec.crcBit v)

theorem pw_succ (m : Nat) (v : UInt32) : pw (m + 1) v = pw m (ZlibF.Spec.crcBit v) := rfl
theorem pw_succ' (m : Nat) (v : UInt32) : pw (m + 1) v = ZlibF.Spec.crcBit (pw m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih => rw [pw_succ, ih, pw_succ]
theorem pw_add (m n : Nat) (v : UInt32) : pw (m + n) v = pw m (pw n v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, pw_succ, ih, pw_succ]
theorem pw_xor (m : Nat) (x y : UInt32) : pw m (x ^^^ y) = pw m x ^^^ pw m y := by
  induction m generalizing x y with
  | zero => rfl
  | succ m ih => rw [pw_succ, pw_succ, pw_succ, crcBit_xor, ih]
theorem pw_zero (m : Nat) : pw m 0 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pw_succ, crcBit_zero, ih]

theorem crcByte_eq (c : UInt32) (b : UInt8) : ZlibF.Spec.crcByte c b = pw 8 (c ^^^ b.toUInt32) := by
  unfold ZlibF.Spec.crcByte
  generalize c ^^^ b.toUInt32 = v
  have : ∀ n, (List.range n).foldl (fun c _ => ZlibF.Spec.crcBit c) v = pw n v := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.foldl_append, ih, pw_succ']; rfl
  exact this 8


/-! ### Tables -/

theorem crc_table_size : Crc32H.crc_table.size = 256 := by decide +kernel

set_option maxRecDepth 100000 in
theorem crc_table_eq : ∀ n : Fin 256, Crc32H.crc_table[n.val]! = pw 8 (UInt32.ofNat n.val) := by decide +kernel


theorem braid5_size :
    Crc32H.crc_braid5_table.size = 4 ∧ ∀ j : Fin 4, Crc32H.crc_braid5_table[j.val]!.size = 256 := by
  decide +kernel

theorem braid2_size :
    Crc32H.crc_braid2_table.size = 4 ∧ ∀ j : Fin 4, Crc32H.crc_braid2_table[j.val]!.size = 256 := by
  decide +kernel

/-! `braid5_eq` and `braid2_eq` by linearity: `pw m` is linear (`pw_xor`), so on a byte it is the XOR of its values
on the set bits (`byteLin_pw`, `byteLin_id`). -/

/-- `f` applied bit by bit to the byte `n`: the XOR of `f (2 ^ b)` over the set bits `b` of `n`. -/
def byteLin (f : UInt32 → UInt32) (n : Nat) : UInt32 :=
  (List.range 8).foldl (fun acc b => if n.testBit b then acc ^^^ f (UInt32.ofNat (2 ^ b)) else acc) 0

theorem byteLin_pw (m n : Nat) : byteLin (pw m) n = pw m (byteLin id n) := by
  have : ∀ (l : List Nat) (acc : UInt32),
      l.foldl (fun acc b => if n.testBit b then acc ^^^ pw m (UInt32.ofNat (2 ^ b)) else acc) (pw m acc) =
        pw m (l.foldl (fun acc b => if n.testBit b then acc ^^^ id (UInt32.ofNat (2 ^ b)) else acc) acc) := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons b l ih =>
      intro acc
      simp only [List.foldl_cons]
      split
      · rw [← pw_xor]; exact ih _
      · exact ih _
  have h := this (List.range 8) 0
  rw [pw_zero] at h
  exact h

set_option maxRecDepth 100000 in
theorem byteLin_id : ∀ n : Fin 256, byteLin id n.val = UInt32.ofNat n.val := by decide +kernel

set_option maxRecDepth 100000 in
theorem braid5_row0 : ∀ n : Fin 256,
    Crc32H.crc_braid5_table[0]![n.val]! = byteLin (pw (8 * (20 - 0))) n.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem braid5_row1 : ∀ n : Fin 256,
    Crc32H.crc_braid5_table[1]![n.val]! = byteLin (pw (8 * (20 - 1))) n.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem braid5_row2 : ∀ n : Fin 256,
    Crc32H.crc_braid5_table[2]![n.val]! = byteLin (pw (8 * (20 - 2))) n.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem braid5_row3 : ∀ n : Fin 256,
    Crc32H.crc_braid5_table[3]![n.val]! = byteLin (pw (8 * (20 - 3))) n.val := by decide +kernel

theorem braid5_eq : ∀ j : Fin 4, ∀ n : Fin 256,
    Crc32H.crc_braid5_table[j.val]![n.val]! = pw (8 * (20 - j.val)) (UInt32.ofNat n.val) := by
  intro j n
  have hrow : Crc32H.crc_braid5_table[j.val]![n.val]! = byteLin (pw (8 * (20 - j.val))) n.val := by
    match j with
    | ⟨0, _⟩ => exact braid5_row0 n
    | ⟨1, _⟩ => exact braid5_row1 n
    | ⟨2, _⟩ => exact braid5_row2 n
    | ⟨3, _⟩ => exact braid5_row3 n
    | ⟨_ + 4, h⟩ => exact absurd h (by omega)
  rw [hrow, byteLin_pw, byteLin_id]

set_option maxRecDepth 100000 in
theorem braid2_row0 : ∀ n : Fin 256,
    Crc32H.crc_braid2_table[0]![n.val]! = byteLin (pw (8 * (8 - 0))) n.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem braid2_row1 : ∀ n : Fin 256,
    Crc32H.crc_braid2_table[1]![n.val]! = byteLin (pw (8 * (8 - 1))) n.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem braid2_row2 : ∀ n : Fin 256,
    Crc32H.crc_braid2_table[2]![n.val]! = byteLin (pw (8 * (8 - 2))) n.val := by decide +kernel
set_option maxRecDepth 100000 in
theorem braid2_row3 : ∀ n : Fin 256,
    Crc32H.crc_braid2_table[3]![n.val]! = byteLin (pw (8 * (8 - 3))) n.val := by decide +kernel

theorem braid2_eq : ∀ j : Fin 4, ∀ n : Fin 256,
    Crc32H.crc_braid2_table[j.val]![n.val]! = pw (8 * (8 - j.val)) (UInt32.ofNat n.val) := by
  intro j n
  have hrow : Crc32H.crc_braid2_table[j.val]![n.val]! = byteLin (pw (8 * (8 - j.val))) n.val := by
    match j with
    | ⟨0, _⟩ => exact braid2_row0 n
    | ⟨1, _⟩ => exact braid2_row1 n
    | ⟨2, _⟩ => exact braid2_row2 n
    | ⟨3, _⟩ => exact braid2_row3 n
    | ⟨_ + 4, h⟩ => exact absurd h (by omega)
  rw [hrow, byteLin_pw, byteLin_id]

/-! ### Linear maps are determined by their values on the unit vectors -/

theorem lin_ext_nat (w : Nat) (F G : Nat → Nat)
    (hF : ∀ x y, F (x ^^^ y) = F x ^^^ F y) (hG : ∀ x y, G (x ^^^ y) = G x ^^^ G y)
    (hb : ∀ t, t < w → F (2 ^ t) = G (2 ^ t)) : ∀ n, n ≤ w → ∀ x, x < 2 ^ n → F x = G x := by
  have F0 : F 0 = 0 := by have := hF 0 0; simpa [Nat.xor_self] using this
  have G0 : G 0 = 0 := by have := hG 0 0; simpa [Nat.xor_self] using this
  intro n
  induction n with
  | zero => intro _ x hx; have : x = 0 := by simpa using hx
            subst this; rw [F0, G0]
  | succ n ih =>
    intro hn x hx
    by_cases hbit : x.testBit n
    · have hy : (x ^^^ 2 ^ n) < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · simp [hbit]
        · have : x.testBit i = false := Nat.testBit_lt_two_pow (by
            exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
          simp [this]; omega
      have hx' : x = (x ^^^ 2 ^ n) ^^^ 2 ^ n := by
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hx', hF, hG, ih (by omega) _ hy, hb n (by omega)]
    · have : x < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · simpa using hbit
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      exact ih (by omega) x this

def Lin32 (f : UInt32 → UInt32) : Prop := ∀ x y, f (x ^^^ y) = f x ^^^ f y

/-- The unit vector with bit `s` set. -/
def e (s : Nat) : UInt32 := UInt32.ofNat (2 ^ s)

theorem lin32_ext {f g : UInt32 → UInt32} (hf : Lin32 f) (hg : Lin32 g)
    (hb : ∀ t, t < 32 → f (e t) = g (e t)) : ∀ x, f x = g x := by
  intro x
  have hf' : ∀ x y, f (x ^^^ y) = f x ^^^ f y := hf
  have hg' : ∀ x y, g (x ^^^ y) = g x ^^^ g y := hg
  have key := lin_ext_nat 32 (fun n => (f (UInt32.ofNat n)).toNat) (fun n => (g (UInt32.ofNat n)).toNat)
    (by intro a b; simp only [UInt32.ofNat_xor, hf', UInt32.toNat_xor])
    (by intro a b; simp only [UInt32.ofNat_xor, hg', UInt32.toNat_xor])
    (by intro t ht; simp only [e] at hb; rw [hb t ht]) 32 (Nat.le_refl _) x.toNat (by simpa using UInt32.toNat_lt x)
  simp only [UInt32.ofNat_toNat] at key
  exact UInt32.toNat_inj.mp key

/-! ### Multiplication in the bit-reflected representation -/

/-- coefficient of `x^j` in `a` (bit `31 - j`) -/
def bitAt (a : UInt32) (j : Nat) : Bool := decide (j < 32) && a.toNat.testBit (31 - j)

def mulpAux (a b : UInt32) : Nat → UInt32
  | 0 => 0
  | n + 1 => mulpAux a b n ^^^ (if bitAt a n then pw n b else 0)

/-- the product of `multmodp`: `a * b` modulo the CRC polynomial -/
def mulp (a b : UInt32) : UInt32 := mulpAux a b 32

theorem bitAt_xor (a b : UInt32) (j : Nat) : bitAt (a ^^^ b) j = (bitAt a j ^^ bitAt b j) := by
  unfold bitAt; rw [UInt32.toNat_xor, Nat.testBit_xor]
  by_cases h : j < 32 <;> simp [h]

theorem ite_xor (p q : Bool) (t : UInt32) :
    (if (p ^^ q) = true then t else 0) = (if p = true then t else 0) ^^^ (if q = true then t else 0) := by
  cases p <;> cases q <;> simp [UInt32.xor_self]

theorem mulpAux_xor_left (a a' b : UInt32) (n : Nat) :
    mulpAux (a ^^^ a') b n = mulpAux a b n ^^^ mulpAux a' b n := by
  induction n with
  | zero => simp [mulpAux]
  | succ n ih =>
    simp only [mulpAux, ih, bitAt_xor, ite_xor]; ac_rfl

theorem mulpAux_xor_right (a b b' : UInt32) (n : Nat) :
    mulpAux a (b ^^^ b') n = mulpAux a b n ^^^ mulpAux a b' n := by
  induction n with
  | zero => simp [mulpAux]
  | succ n ih =>
    simp only [mulpAux, ih, pw_xor]
    cases bitAt a n <;> simp <;> ac_rfl

theorem mulp_xor_left (a a' b : UInt32) : mulp (a ^^^ a') b = mulp a b ^^^ mulp a' b := mulpAux_xor_left ..
theorem mulp_xor_right (a b b' : UInt32) : mulp a (b ^^^ b') = mulp a b ^^^ mulp a b' := mulpAux_xor_right ..

theorem mulpAux_zero_left (b : UInt32) (n : Nat) : mulpAux 0 b n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [mulpAux, ih, bitAt]
theorem mulp_zero_left (b : UInt32) : mulp 0 b = 0 := mulpAux_zero_left b 32

theorem tb_e (s i : Nat) (hs : s < 32) : (e s).toNat.testBit i = decide (s = i) := by
  simp only [e, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hs), Nat.testBit_two_pow]

theorem bitAt_e (s : Nat) (hs : s < 32) (j : Nat) : bitAt (e s) j = decide (j < 32 ∧ 31 - j = s) := by
  unfold bitAt; rw [tb_e s _ hs]
  by_cases h : j < 32
  · simp [h]; omega
  · simp [h]

theorem mulpAux_e (s : Nat) (hs : s < 32) (b : UInt32) (n : Nat) (hn : n ≤ 32) :
    mulpAux (e s) b n = if 31 - s < n then pw (31 - s) b else 0 := by
  induction n with
  | zero => simp [mulpAux]
  | succ n ih =>
    simp only [mulpAux, ih (by omega), bitAt_e s hs]
    by_cases h2 : 31 - s = n
    · have h3 : n < 32 := by omega
      have h5 : 31 - n = s := by omega
      simp [h2, h3, h5]
    · have h3 : ¬ (n < 32 ∧ 31 - n = s) := by omega
      simp [h3]
      by_cases h4 : 31 - s < n
      · simp [h4, show 31 - s < n + 1 by omega]
      · simp [h4, show ¬ 31 - s < n + 1 by omega]

theorem mulp_e (s : Nat) (hs : s < 32) (b : UInt32) : mulp (e s) b = pw (31 - s) b := by
  unfold mulp; rw [mulpAux_e s hs b 32 (Nat.le_refl _)]; simp; omega

set_option maxRecDepth 100000 in
theorem crcBit_e : ∀ s : Fin 32, crcBit (e s.val) = if s.val = 0 then crcPoly else e (s.val - 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mulp_poly_basis : ∀ t : Fin 32, mulp crcPoly (e t.val) = pw 32 (e t.val) := by decide +kernel

theorem mulp_lin_right (a : UInt32) : Lin32 (mulp a) := fun x y => mulp_xor_right a x y
theorem pw_lin (m : Nat) : Lin32 (pw m) := fun x y => pw_xor m x y

theorem mulp_poly (v : UInt32) : mulp crcPoly v = pw 32 v :=
  lin32_ext (mulp_lin_right crcPoly) (pw_lin 32) (fun t ht => mulp_poly_basis ⟨t, ht⟩) v

theorem mulp_crcBit_left (a v : UInt32) : mulp (crcBit a) v = crcBit (mulp a v) := by
  refine lin32_ext (f := fun a => mulp (crcBit a) v) (g := fun a => crcBit (mulp a v)) ?_ ?_ ?_ a
  · intro x y; simp only [crcBit_xor, mulp_xor_left]
  · intro x y; simp only [mulp_xor_left, crcBit_xor]
  · intro t ht
    have h := crcBit_e ⟨t, ht⟩
    simp only at h
    show mulp (crcBit (e t)) v = crcBit (mulp (e t) v)
    rw [h, mulp_e t ht]
    by_cases h0 : t = 0
    · subst h0
      simp only [ite_true]
      rw [mulp_poly]
      show pw 32 v = crcBit (pw 31 v)
      rw [← pw_succ']
    · simp only [h0, ite_false]
      rw [mulp_e (t - 1) (by omega)]
      rw [show 31 - (t - 1) = (31 - t) + 1 by omega, pw_succ']

theorem mulp_pw_left' (j : Nat) (a v : UInt32) : mulp (pw j a) v = pw j (mulp a v) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih => rw [pw_succ', pw_succ', mulp_crcBit_left, ih]

theorem mulp_one (v : UInt32) : mulp (e 31) v = v := by
  rw [mulp_e 31 (by omega)]; rfl

theorem mulpAux_assoc (a b v : UInt32) (n : Nat) : mulp (mulpAux a b n) v = mulpAux a (mulp b v) n := by
  induction n with
  | zero => simp [mulpAux, mulp_zero_left]
  | succ n ih =>
    simp only [mulpAux, mulp_xor_left, ih]
    cases bitAt a n
    · simp [mulp_zero_left]
    · simp [mulp_pw_left']

theorem mulp_assoc (a b v : UInt32) : mulp (mulp a b) v = mulp a (mulp b v) := mulpAux_assoc a b v 32

/-! ### The table `x2n_table` -/

def Xt (i : Nat) : UInt32 := Crc32H.x2n_table[i]!

theorem x2n_size : Crc32H.x2n_table.size = 32 := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_zero : Xt 0 = pw 1 (e 31) := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_sq : ∀ i : Fin 31, Xt (i.val + 1) = mulp (Xt i.val) (Xt i.val) := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_wrap : mulp (Xt 31) (Xt 31) = Xt 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem Xt_ne : ∀ i : Fin 32, Xt i.val ≠ 0 := by decide +kernel

theorem Xt_pw : ∀ i, i < 32 → ∀ v, mulp (Xt i) v = pw (2 ^ i) v := by
  intro i
  induction i with
  | zero =>
    intro _ v
    rw [Xt_zero, mulp_pw_left', mulp_one]
  | succ i ih =>
    intro hi v
    rw [Xt_sq ⟨i, by omega⟩]
    simp only []
    rw [mulp_assoc, ih (by omega), ih (by omega), ← pw_add, Nat.pow_succ, Nat.mul_two]

theorem pw_period_one (v : UInt32) : pw (2 ^ 32) v = pw 1 v := by
  have h := mulp_assoc (Xt 31) (Xt 31) v
  have h1 : mulp (Xt 31) v = pw (2 ^ 31) v := Xt_pw 31 (by omega) v
  have h2 : mulp (Xt 31) (pw (2 ^ 31) v) = pw (2 ^ 31) (pw (2 ^ 31) v) := Xt_pw 31 (by omega) _
  have h3 : mulp (Xt 0) v = pw 1 v := Xt_pw 0 (by omega) v
  rw [Xt_wrap, h3, h1, h2, ← pw_add] at h
  rw [show 2 ^ 32 = 2 ^ 31 + 2 ^ 31 by omega]
  exact h.symm

theorem pw_period (a : Nat) (v : UInt32) : pw (2 ^ 32 * a) v = pw a v := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [Nat.mul_succ, Nat.add_comm, pw_add, ih, pw_period_one, ← pw_add, Nat.add_comm]

theorem Xt_mod (k : Nat) (v : UInt32) : mulp (Xt (k % 32)) v = pw (2 ^ k) v := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < 32
    · rw [Nat.mod_eq_of_lt hk]; exact Xt_pw k hk v
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 32 := ⟨k - 32, by omega⟩
      have := ih m (by omega)
      rw [show (m + 32) % 32 = m % 32 by omega, this, Nat.pow_add, Nat.mul_comm, pw_period]

/-! ### Bits of 64-bit values -/

theorem lowbit_aux (x : Nat) : ∀ n, x.testBit n = true →
    ∃ t, x.testBit t = true ∧ ∀ s, s < t → x.testBit s = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∃ s, s < n ∧ x.testBit s = true
    · obtain ⟨s, hs, hs2⟩ := h
      exact ih s hs hs2
    · refine ⟨n, hn, ?_⟩
      intro s hs
      cases hb : x.testBit s
      · rfl
      · exact absurd ⟨s, hs, hb⟩ h

theorem lowbit_exists (x : Nat) (hx : x ≠ 0) : ∃ t, x.testBit t = true ∧ ∀ s, s < t → x.testBit s = false := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hx
  exact lowbit_aux x i hi

theorem mod_pow_zero_iff (x t i : Nat) (ht : x.testBit t = true) (hlow : ∀ s, s < t → x.testBit s = false) :
    x % 2 ^ i = 0 ↔ i ≤ t := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hlt
    have h1 : (x % 2 ^ i).testBit t = true := by
      rw [Nat.testBit_mod_two_pow]; simp [ht]; omega
    rw [h] at h1; simp at h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hk : k < i
    · simp [hlow k (by omega)]
    · simp [hk]

def mm (j : Nat) : UInt64 := UInt64.ofNat (2 ^ (31 - j))

theorem mm_toNat (j : Nat) : (mm j).toNat = 2 ^ (31 - j) := by
  unfold mm; rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))

theorem and_pow_ne (n i : Nat) : (n &&& 2 ^ i ≠ 0) ↔ n.testBit i = true := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hb
    apply h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hk : i = k
    · subst hk; simp at hb; simp [hb]
    · simp [hk]
  · intro h h0
    have := congrArg (fun z => z.testBit i) h0
    simp [Nat.testBit_and, h] at this

theorem and_mm_ne (a : UInt64) (j : Nat) (hj : j ≤ 31) :
    (a &&& mm j != 0) = decide (a.toUInt32.toNat.testBit (31 - j) = true) := by
  have h1 : (a &&& mm j ≠ 0) ↔ a.toNat.testBit (31 - j) = true := by
    rw [← and_pow_ne, ← mm_toNat j, ← UInt64.toNat_and]
    constructor
    · intro h h0; apply h; apply UInt64.toNat_inj.mp; simpa using h0
    · intro h h0; apply h; rw [h0]; rfl
  have h2 : a.toUInt32.toNat.testBit (31 - j) = a.toNat.testBit (31 - j) := by
    rw [UInt64.toNat_toUInt32, Nat.testBit_mod_two_pow]; simp; omega
  rw [h2]
  by_cases h : a.toNat.testBit (31 - j) = true
  · simp [h, h1.mpr h]
  · have : ¬ (a &&& mm j ≠ 0) := fun hh => h (h1.mp hh)
    simp [h]; simpa using this

theorem and_mm_pred_eq (a : UInt64) (j : Nat) (_hj : j ≤ 31) :
    (a &&& (mm j - 1) == 0) = decide (a.toNat % 2 ^ (31 - j) = 0) := by
  have h1 : (mm j - 1).toNat = 2 ^ (31 - j) - 1 := by
    rw [UInt64.toNat_sub_of_le, mm_toNat]; rfl
    rw [UInt64.le_iff_toNat_le, mm_toNat]; simp
    exact Nat.one_le_two_pow
  have h2 : (a &&& (mm j - 1)).toNat = a.toNat % 2 ^ (31 - j) := by
    rw [UInt64.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h : a.toNat % 2 ^ (31 - j) = 0
  · have : a &&& (mm j - 1) = 0 := by apply UInt64.toNat_inj.mp; rw [h2, h]; rfl
    simp [this, h]
  · have : ¬ a &&& (mm j - 1) = 0 := by
      intro hh; apply h; rw [← h2, hh]; rfl
    simp [this, h]

theorem mod_32 (a : UInt64) (i : Nat) (hi : i ≤ 32) : a.toUInt32.toNat % 2 ^ i = a.toNat % 2 ^ i := by
  rw [UInt64.toNat_toUInt32]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hi)

theorem mm_shr (j : Nat) (hj : j < 31) : mm j >>> 1 = mm (j + 1) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, mm_toNat, mm_toNat]
  have h1 : (1 : UInt64).toNat % 64 = 1 := by decide
  rw [h1, Nat.shiftRight_eq_div_pow]
  have : 31 - j = (31 - (j + 1)) + 1 := by omega
  rw [this, Nat.pow_succ]; simp

theorem POLY_eq : Zlib.Crc32.POLY = crcPoly.toUInt64 := by decide

theorem b_step (v : UInt32) :
    (if (v.toUInt64 &&& 1 != 0) = true then v.toUInt64 >>> 1 ^^^ Zlib.Crc32.POLY else v.toUInt64 >>> 1)
      = (crcBit v).toUInt64 := by
  unfold crcBit
  have h1 : (v.toUInt64 &&& 1) = (v &&& 1).toUInt64 := (UInt32.toUInt64_and v 1).symm
  have hs : v.toUInt64 >>> 1 = (v >>> 1).toUInt64 := by rw [UInt32.toUInt64_shiftRight]; rfl
  rcases and1_cases v with h0 | h0
  · have hz : (v.toUInt64 &&& 1 != 0) = false := by rw [h1, h0]; decide
    have hz2 : ¬ (v &&& 1 = 1) := by rw [h0]; decide
    rw [hz, ite_eq_right hz2, ite_eq_right (by decide), hs]
  · have hz : (v.toUInt64 &&& 1 != 0) = true := by rw [h1, h0]; decide
    rw [hz, ite_eq_left h0, ite_eq_left rfl, UInt32.toUInt64_xor, POLY_eq, hs]

/-! ### `multmodp` -/

abbrev MS := UInt64 × UInt64 × UInt64 × Bool

/-- the body of the loop of `multmodp` as a pure function -/
def mmStep (a : UInt64) (s : MS) : MS :=
  match s with
  | (m, p, b, brk) =>
    if (a &&& m != 0) = true then
      if (a &&& (m - 1) == 0) = true then (m, p ^^^ b, b, true)
      else (m >>> 1, p ^^^ b, (if (b &&& 1 != 0) = true then b >>> 1 ^^^ Zlib.Crc32.POLY else b >>> 1), brk)
    else (m >>> 1, p, (if (b &&& 1 != 0) = true then b >>> 1 ^^^ Zlib.Crc32.POLY else b >>> 1), brk)

theorem mulpAux_stable (a b : UInt32) (t : Nat) (ht : t < 32) (hlow : ∀ s, s < t → a.toNat.testBit s = false) :
    ∀ n, 31 - t + 1 ≤ n → n ≤ 32 → mulpAux a b n = mulpAux a b (31 - t + 1) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h1 h2
    by_cases h : 31 - t + 1 ≤ n
    · rw [mulpAux, ih h (by omega)]
      have : bitAt a n = false := by
        unfold bitAt
        have := hlow (31 - n) (by omega)
        simp [this]
      simp [this]
    · have : n + 1 = 31 - t + 1 := by omega
      rw [this]

def Pmm (a32 b32 : UInt32) (J : Nat) : Nat → MS → Prop
  | 0, s => s.2.2.2 = true ∧ s.2.1 = (mulp a32 b32).toUInt64
  | k + 1, s => ∃ j, j + k = J ∧ s = (mm j, (mulpAux a32 b32 j).toUInt64, (pw j b32).toUInt64, false)

theorem multmodp_ok (h : Heap) (a b : UInt64) (ha : a.toUInt32 ≠ 0) (hb : b.toNat < 2 ^ 32) :
    OkOn h (multmodp a b) (mulp a.toUInt32 b.toUInt32).toUInt64 := by
  have ha' : a.toUInt32.toNat ≠ 0 := fun h0 => ha (UInt32.toNat_inj.mp (by simpa using h0))
  obtain ⟨t, ht, hlow⟩ := lowbit_exists _ ha'
  have ht32 : t < 32 := by
    apply Classical.byContradiction; intro hh
    have := Nat.testBit_lt_two_pow (x := a.toUInt32.toNat) (i := t)
      (Nat.lt_of_lt_of_le (UInt32.toNat_lt _) (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [ht] at this; simp at this
  have hb64 : b.toUInt32.toUInt64 = b := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hb]
  generalize hJ : 31 - t = J
  suffices H : ∃ y, OkOn h (multmodp a b) y ∧ y = (mulp a.toUInt32 b.toUInt32).toUInt64 by
    obtain ⟨y, hy, rfl⟩ := H; exact hy
  unfold multmodp
  refine OkOn.bind_ex (R := fun x : MS => x.2.1 = (mulp a.toUInt32 b.toUInt32).toUInt64) ?_ ?_
  · refine cwhile_ok (Pmm a.toUInt32 b.toUInt32 J) (fun x : MS => x.2.1 = (mulp a.toUInt32 b.toUInt32).toUInt64)
      ?_ ?_ (k := J + 1) (s := ((1 : UInt64) <<< 31, 0, b, false)) ?_ ?_
    · intro k s hP
      obtain ⟨j, hjk, rfl⟩ := hP
      have hj31 : j ≤ 31 := by omega
      have e1 : (a &&& mm j != 0) = bitAt a.toUInt32 j := by
        rw [and_mm_ne a j hj31]; unfold bitAt; simp [show j < 32 by omega]
      have e2 : (a &&& (mm j - 1) == 0) = decide (31 - j ≤ t) := by
        rw [and_mm_pred_eq a j hj31, ← mod_32 a (31 - j) (by omega)]
        simp only [mod_pow_zero_iff _ t _ ht hlow]
      refine ⟨(mm j, (mulpAux a.toUInt32 b.toUInt32 j).toUInt64, (pw j b.toUInt32).toUInt64, false),
        mmStep a (mm j, (mulpAux a.toUInt32 b.toUInt32 j).toUInt64, (pw j b.toUInt32).toUInt64, false), rfl, ?_, ?_⟩
      · by_cases c1 : (a &&& mm j != 0) = true <;> by_cases c2 : (a &&& mm j - 1 == 0) = true <;>
          simp [mmStep, c1, c2, OkOn]
      simp only [mmStep, e1, e2]
      cases k with
      | zero =>
        have hj : j = J := by omega
        have hbit : bitAt a.toUInt32 j = true := by
          unfold bitAt; rw [show 31 - j = t by omega, ht]; simp [show j < 32 by omega]
        have hst : decide (31 - j ≤ t) = true := by simp; omega
        rw [ite_eq_left hbit, ite_eq_left hst]
        refine ⟨rfl, ?_⟩
        have : mulpAux a.toUInt32 b.toUInt32 (j + 1) = mulpAux a.toUInt32 b.toUInt32 j ^^^ pw j b.toUInt32 := by
          simp [mulpAux, hbit]
        have hst2 := mulpAux_stable a.toUInt32 b.toUInt32 t ht32 hlow 32 (by omega) (by omega)
        show _ = (mulpAux a.toUInt32 b.toUInt32 32).toUInt64
        rw [hst2, show 31 - t + 1 = j + 1 by omega, this, UInt32.toUInt64_xor]
      | succ k =>
        have hst : decide (31 - j ≤ t) = false := by simp; omega
        have hst' : ¬ (decide (31 - j ≤ t) = true) := by rw [hst]; decide
        refine ⟨j + 1, by omega, ?_⟩
        have hb' := b_step (pw j b.toUInt32)
        rw [← pw_succ'] at hb'
        have hm : mm j >>> 1 = mm (j + 1) := mm_shr j (by omega)
        cases hbit : bitAt a.toUInt32 j
        · rw [ite_eq_right (by simp), hm, hb']; simp [mulpAux, hbit]
        · rw [ite_eq_left (by simp), ite_eq_right hst', hm, hb']; simp [mulpAux, hbit, UInt32.toUInt64_xor]
    · intro s hP
      obtain ⟨m, p, bb, brk⟩ := s
      obtain ⟨h1, h2⟩ := hP
      simp only at h1 h2
      subst h1
      exact ⟨_, rfl, h2⟩
    · refine ⟨0, by omega, ?_⟩
      simp only [mulpAux, pw]
      rw [hb64]; rfl
    · show J + 1 < 2 ^ 64
      omega
  · intro x hx
    obtain ⟨m, p, bb, brk⟩ := x
    exact ⟨p, rfl, hx⟩

theorem int64_shr (nn : Nat) (h : nn < 2 ^ 63) : (Int64.ofNat nn) >>> 1 = Int64.ofNat (nn / 2) := by
  apply Int64.toBitVec_inj.mp
  rw [Int64.toBitVec_shiftRight]
  simp [Int64.toBitVec_ofNat']
  rw [BitVec.sshiftRight_eq_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64), Nat.mod_eq_of_lt (by omega : nn / 2 < 2 ^ 64),
      Nat.shiftRight_eq_div_pow]
  · rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64)]
    omega


theorem int64_and1 (nn : Nat) (h : nn < 2 ^ 63) : ((Int64.ofNat nn) &&& 1 != 0) = decide (nn % 2 = 1) := by
  have h1 : ((Int64.ofNat nn) &&& 1).toBitVec.toNat = nn % 2 := by
    rw [Int64.toBitVec_and, BitVec.toNat_and, Int64.toBitVec_ofNat', BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64)]
    have : (Int64.toBitVec 1).toNat = 1 := by decide
    rw [this, Nat.and_one_is_mod]
  by_cases h2 : nn % 2 = 1
  · have : ((Int64.ofNat nn) &&& 1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      have : (Int64.toBitVec 0).toNat = 0 := by decide
      omega
    simp [this, h2]
  · have : ((Int64.ofNat nn) &&& 1) = 0 := by
      apply Int64.toBitVec_inj.mp
      apply BitVec.eq_of_toNat_eq
      rw [h1]; have : (Int64.toBitVec 0).toNat = 0 := by decide
      rw [this]; omega
    simp [this, h2]

theorem int64_ne0 (nn : Nat) (h : nn < 2 ^ 63) : ((Int64.ofNat nn) != 0) = decide (nn ≠ 0) := by
  by_cases h2 : nn = 0
  · subst h2; decide
  · have : Int64.ofNat nn ≠ 0 := by
      intro h0
      have := congrArg (fun x => x.toBitVec.toNat) h0
      simp only [Int64.toBitVec_ofNat', BitVec.toNat_ofNat] at this
      have h3 : (Int64.toBitVec 0).toNat = 0 := by decide
      rw [h3, Nat.mod_eq_of_lt (by omega : nn < 2 ^ 64)] at this
      exact h2 this
    simp [this, h2]

/-! ### `x2nmodp` -/

/-- the number of loop iterations of `x2nmodp` for `n`: its bit length -/
def bl (n : Nat) : Nat := if n = 0 then 0 else bl (n / 2) + 1
termination_by n
decreasing_by omega

theorem bl_zero : bl 0 = 0 := by rw [bl]; simp
theorem bl_pos (n : Nat) (h : n ≠ 0) : bl n = bl (n / 2) + 1 := by rw [bl]; simp [h]

theorem bl_div (n i : Nat) : bl (n / 2 ^ i / 2) = bl (n / 2 ^ (i + 1)) := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem bl_le (n : Nat) : bl n ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; rw [bl_zero]; exact Nat.le_refl _
    · rw [bl_pos n h]
      have := ih (n / 2) (by omega)
      omega

theorem u32_roundtrip (x : UInt32) : x.toUInt64.toUInt32 = x := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]

theorem x2nTab_ok (h : Heap) (hs : StaticsOK h) (i : UInt32) (hi : i.toNat < 32) :
    OkOn h (x2nTab i) (Xt i.toNat) := by
  unfold x2nTab
  have hg : Space.get h URef.st_x2n_table = some Crc32H.x2n_table := by rw [URef.get_st_x2n_table, hs.2]
  have hlt : 0 + i.toNat < Crc32H.x2n_table.size := by rw [x2n_size]; omega
  have := Ptr.index_ok (r := URef.st_x2n_table) (off := 0) (i := i.toNat) hg hlt
  have e : Xt i.toNat = Crc32H.x2n_table[0 + i.toNat] := by
    simp only [Xt, Nat.zero_add]; exact getElem!_pos _ _ (by omega)
  rw [e]; exact this

theorem crcTab_ok (h : Heap) (hs : StaticsOK h) (i : UInt64) (hi : i.toNat < 256) :
    OkOn h (crcTab i) Crc32H.crc_table[i.toNat]! := by
  unfold crcTab
  have hg : Space.get h URef.st_crc_table = some Crc32H.crc_table := by rw [URef.get_st_crc_table, hs.1]
  have hlt : 0 + i.toNat < Crc32H.crc_table.size := by rw [crc_table_size]; omega
  have := Ptr.index_ok (r := URef.st_crc_table) (off := 0) (i := i.toNat) hg hlt
  have e : Crc32H.crc_table[i.toNat]! = Crc32H.crc_table[0 + i.toNat] := by
    simp only [Nat.zero_add]; exact getElem!_pos _ _ (by omega)
  rw [e]; exact this

theorem and31 (x : UInt32) : (x &&& 31).toNat = x.toNat % 32 := by
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 5

def Px (n0 k0 : Nat) (cnt : Nat) (s : UInt64 × Int64 × UInt32) : Prop :=
  ∃ i, cnt = bl (n0 / 2 ^ i) ∧ s.1.toNat < 2 ^ 32 ∧ s.2.1 = Int64.ofNat (n0 / 2 ^ i) ∧
    s.2.2 = UInt32.ofNat (k0 + i) ∧ ∀ v, mulp s.1.toUInt32 v = pw ((n0 % 2 ^ i) * 2 ^ k0) v

theorem int64_nat_lt (n : Int64) (hn : 0 ≤ n.toInt) : n.toInt.toNat < 2 ^ 63 := by
  have h1 : n.toInt < 2 ^ 63 := by
    have := Int64.toInt_lt n  
    omega
  omega

theorem x2nmodp_ok (h : Heap) (hs : StaticsOK h) (n : Int64) (hn : 0 ≤ n.toInt) (k : UInt32) :
    ∃ p, OkOn h (x2nmodp n k) p ∧ p.toNat < 2 ^ 32 ∧
      ∀ v, mulp p.toUInt32 v = pw (n.toInt.toNat * 2 ^ k.toNat) v := by
  have hn63 := int64_nat_lt n hn
  generalize hn0 : n.toInt.toNat = n0 at hn63 ⊢
  have hnn : n = Int64.ofNat n0 := by
    rw [← hn0]
    have := Int64.ofNat_toNatClampNeg n (by simpa [Int64.le_iff_toInt_le] using hn)
    simpa using this.symm
  generalize hk0 : k.toNat = k0
  have hkk : k = UInt32.ofNat k0 := by rw [← hk0]; simp
  subst hnn hkk
  suffices H : ∃ y, OkOn h (x2nmodp (Int64.ofNat n0) (UInt32.ofNat k0)) y ∧
      (y.toNat < 2 ^ 32 ∧ ∀ v, mulp y.toUInt32 v = pw (n0 * 2 ^ k0) v) by
    obtain ⟨y, hy, h2⟩ := H; exact ⟨y, hy, h2⟩
  unfold x2nmodp
  refine OkOn.bind_ex (R := fun x : UInt64 × Int64 × UInt32 =>
    x.1.toNat < 2 ^ 32 ∧ ∀ v, mulp x.1.toUInt32 v = pw (n0 * 2 ^ k0) v) ?_ ?_
  · refine cwhile_ok (Px n0 k0) _ ?_ ?_ (k := bl n0) (s := ((1 : UInt64) <<< 31, Int64.ofNat n0, UInt32.ofNat k0)) ?_ ?_
    · intro cnt s hP
      obtain ⟨p, n, kk⟩ := s
      obtain ⟨i, hcnt, hp32, hn', hk', hm⟩ := hP
      simp only at hp32 hn' hk' hm
      subst hn' hk'
      have hne : n0 / 2 ^ i ≠ 0 := by
        intro h0; rw [h0, bl_zero] at hcnt; omega
      have hlt63 : n0 / 2 ^ i < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn63
      have hc : OkOn h (pure ((Int64.ofNat (n0 / 2 ^ i) != 0), p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)) :
          M (Bool × UInt64 × Int64 × UInt32)) (true, p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)) := by
        rw [int64_ne0 _ hlt63]; simp [hne]; exact OkOn.pure _ _
      have hbit : (Int64.ofNat (n0 / 2 ^ i) &&& 1 != 0) = decide ((n0 / 2 ^ i) % 2 = 1) := int64_and1 _ hlt63
      have hnext : Int64.ofNat (n0 / 2 ^ i) >>> 1 = Int64.ofNat (n0 / 2 ^ (i + 1)) := by
        rw [int64_shr _ hlt63, Nat.pow_succ, Nat.div_div_eq_div_mul]
      have hknext : UInt32.ofNat (k0 + i) + 1 = UInt32.ofNat (k0 + (i + 1)) := by
        apply UInt32.toNat_inj.mp
        simp [UInt32.toNat_add, UInt32.toNat_ofNat']
        omega
      have hcnt' : cnt = bl (n0 / 2 ^ (i + 1)) := by
        rw [bl_pos _ hne, bl_div] at hcnt; omega
      have hkt : (UInt32.ofNat (k0 + i) &&& 31).toNat = (k0 + i) % 32 := by
        rw [and31, UInt32.toNat_ofNat']
        exact Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32)
      by_cases hb : (n0 / 2 ^ i) % 2 = 1
      · have hX := x2nTab_ok h hs (UInt32.ofNat (k0 + i) &&& 31) (by rw [hkt]; omega)
        rw [hkt] at hX
        have hXne : (Xt ((k0 + i) % 32)).toUInt64.toUInt32 ≠ 0 := by
          have : (Xt ((k0 + i) % 32)).toUInt64.toUInt32 = Xt ((k0 + i) % 32) := by
            apply UInt32.toNat_inj.mp
            rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
          rw [this]; exact Xt_ne ⟨(k0 + i) % 32, by omega⟩
        have hM := multmodp_ok h (Xt ((k0 + i) % 32)).toUInt64 p hXne (by omega)
        refine ⟨(p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)),
          ((mulp (Xt ((k0 + i) % 32)).toUInt64.toUInt32 p.toUInt32).toUInt64,
          Int64.ofNat (n0 / 2 ^ (i + 1)), UInt32.ofNat (k0 + (i + 1))), hc, ?_, ?_⟩
        · simp only [hbit, hb, decide_true, ite_true]
          exact OkOn.bind hX (OkOn.bind hM (by rw [hnext, hknext]; exact OkOn.pure _ _))
        · refine ⟨i + 1, hcnt', ?_, rfl, rfl, ?_⟩
          · simp only [UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _
          · intro v
            rw [u32_roundtrip, u32_roundtrip, mulp_assoc, Xt_mod, hm v, ← pw_add]
            rw [Nat.mod_pow_succ, hb]
            congr 1
            rw [Nat.mul_one, Nat.add_mul, Nat.pow_add, Nat.mul_comm (2 ^ k0)]
            omega
      · have hb' : ¬ (n0 / 2 ^ i % 2 = 1) := hb
        refine ⟨(p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)),
          (p, Int64.ofNat (n0 / 2 ^ (i + 1)), UInt32.ofNat (k0 + (i + 1))), hc, ?_, ?_⟩
        · simp only [hbit, hb', decide_false]
          rw [ite_eq_right (by decide)]
          rw [hnext, hknext]; exact OkOn.pure _ _
        · refine ⟨i + 1, hcnt', hp32, rfl, rfl, ?_⟩
          intro v
          rw [hm v]
          congr 1
          rw [Nat.mod_pow_succ]
          have : n0 / 2 ^ i % 2 = 0 := by omega
          rw [this]; simp
    · intro s hP
      obtain ⟨p, n, kk⟩ := s
      obtain ⟨i, hcnt, hp32, hn', hk', hm⟩ := hP
      simp only at hp32 hn' hk' hm
      subst hn' hk'
      have h0 : n0 / 2 ^ i = 0 := by
        apply Classical.byContradiction; intro hne
        rw [bl_pos _ hne] at hcnt; omega
      have hlt63 : n0 / 2 ^ i < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn63
      refine ⟨(p, Int64.ofNat (n0 / 2 ^ i), UInt32.ofNat (k0 + i)), ?_, hp32, ?_⟩
      · show OkOn h (pure _) _
        rw [int64_ne0 _ hlt63]; simp [h0]; exact OkOn.pure _ _
      · have hmod : n0 % 2 ^ i = n0 := Nat.mod_eq_of_lt (by
          rcases Nat.div_eq_zero_iff.mp h0 with h1 | h1
          · have := Nat.two_pow_pos i; omega
          · exact h1)
        intro v; rw [hm v, hmod]
    · refine ⟨0, by simp, by show ((1 : UInt64) <<< 31).toNat < 2 ^ 32; decide, by simp, by simp, ?_⟩
      intro v
      have : ((1 : UInt64) <<< 31).toUInt32 = e 31 := by decide
      simp only [this, Nat.pow_zero, Nat.mod_one, Nat.zero_mul]
      exact mulp_one v
    · show bl n0 < 2 ^ 64
      have := bl_le n0
      have : 2 ^ 63 < 2 ^ 64 := by decide
      omega
  · intro x hx
    obtain ⟨p, n, kk⟩ := x
    exact ⟨p, rfl, hx⟩

/-! ### `crcBit` is injective, so a power of `x` times a nonzero register is nonzero -/

theorem crcBit_eq_zero (c : UInt32) (h : crcBit c = 0) : c = 0 := by
  have e1 : (1 : UInt32).toNat = 1 := rfl
  have e0 : (0 : UInt32).toNat = 0 := rfl
  have hb : c &&& 1 = 0 := by
    apply Classical.byContradiction; intro hne
    rcases and1_cases c with h0 | h0
    · exact hne h0
    · unfold ZlibF.Spec.crcBit at h
      rw [ite_eq_left h0] at h
      have h1 := congrArg (fun x => x.toNat.testBit 31) h
      simp only [UInt32.toNat_xor, Nat.testBit_xor, UInt32.toNat_shiftRight, e1, e0] at h1
      have h2 : (c.toNat >>> (1 % 32)).testBit 31 = false := by
        rw [Nat.testBit_shiftRight]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (UInt32.toNat_lt c) (by decide))
      have h3 : crcPoly.toNat.testBit 31 = true := by decide
      rw [h2, h3] at h1
      simp at h1
  unfold ZlibF.Spec.crcBit at h
  rw [ite_eq_right (by rw [hb]; decide)] at h
  have h1 : c.toNat >>> 1 = 0 := by
    have := congrArg UInt32.toNat h
    rw [UInt32.toNat_shiftRight, e1, e0] at this
    simpa using this
  have h2 : c.toNat < 2 := by
    rw [Nat.shiftRight_eq_div_pow] at h1
    have := Nat.div_eq_zero_iff.mp h1
    omega
  have h3 : (c &&& 1).toNat = 0 := by rw [hb]; rfl
  rw [UInt32.toNat_and, e1, Nat.and_one_is_mod] at h3
  apply UInt32.toNat_inj.mp
  rw [e0]; omega

theorem pw_eq_zero (m : Nat) (c : UInt32) (h : pw m c = 0) : c = 0 := by
  induction m generalizing c with
  | zero => exact h
  | succ m ih => exact crcBit_eq_zero c (ih _ (by rw [← pw_succ]; exact h))

theorem e_ne_zero (s : Nat) (hs : s < 32) : e s ≠ 0 := by
  intro h
  have := congrArg (fun x => x.toNat) h
  simp only [e, UInt32.toNat_ofNat'] at this
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hs)] at this
  have h0 : (0 : UInt32).toNat = 0 := rfl
  rw [h0] at this
  exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos s))


/-! ### The specification side: the CRC register is affine in its start value -/

/-- the register after processing `l` from the start value `c` -/
def rbl (c : UInt32) (l : List UInt8) : UInt32 := l.foldl ZlibF.Spec.crcByte c

theorem rbl_nil (c : UInt32) : rbl c [] = c := rfl
theorem rbl_cons (c : UInt32) (b : UInt8) (l : List UInt8) : rbl c (b :: l) = rbl (ZlibF.Spec.crcByte c b) l := rfl

theorem rbl_affine (l : List UInt8) : ∀ c : UInt32, rbl c l = pw (8 * l.length) c ^^^ rbl 0 l := by
  induction l with
  | nil => intro c; simp [rbl_nil, pw]
  | cons b l ih =>
    intro c
    rw [rbl_cons, rbl_cons, ih, ih (ZlibF.Spec.crcByte 0 b)]
    simp only [crcByte_eq, UInt32.zero_xor, pw_xor, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by omega, pw_add]
    ac_rfl

theorem not32_eq (x : UInt32) : ~~~ x = x ^^^ 0xffffffff := by
  apply UInt32.eq_of_toBitVec_eq
  have : (0xffffffff : UInt32).toBitVec = BitVec.allOnes 32 := by decide
  rw [UInt32.toBitVec_xor, this, BitVec.xor_allOnes]
  rfl

theorem crc32Update_affine (c : UInt32) (l : List UInt8) :
    ZlibF.Spec.crc32Update c l = pw (8 * l.length) c ^^^ ZlibF.Spec.crc32 l := by
  unfold ZlibF.Spec.crc32 ZlibF.Spec.crc32Update
  change ~~~ rbl (~~~ c) l = pw (8 * l.length) c ^^^ ~~~ rbl (~~~ 0) l
  rw [rbl_affine l (~~~ c), rbl_affine l (~~~ 0), not32_eq, not32_eq c, not32_eq 0, not32_eq]
  simp only [pw_xor]
  rw [pw_zero, UInt32.zero_xor]
  ac_rfl

/-- `op` is the operator for `n` bytes: a 32-bit value with a bit set among the low 32 (so `multmodp` terminates
on it) that multiplies a CRC register by `x^(8n)` (the advance over `n` zero bytes). -/
def IsOp (op : UInt64) (n : Nat) : Prop :=
  op.toNat < 2 ^ 32 ∧ op.toUInt32 ≠ 0 ∧ ∀ v, mulp op.toUInt32 v = pw (8 * n) v

theorem and_ffffffff (x : UInt64) : x &&& 0xffffffff = x.toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  have : (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem gen64_neg (h : Heap) (len2 : Int64) (hneg : len2.toInt < 0) :
    OkOn h (crc32_combine_gen64 len2) 0 := by
  unfold crc32_combine_gen64
  have : len2 < 0 := by rw [Int64.lt_iff_toInt_lt]; simpa using hneg
  rw [ite_eq_left this]; exact OkOn.pure _ _

theorem gen64_op (h : Heap) (hs : StaticsOK h) (len2 : Int64) (hpos : 0 ≤ len2.toInt) :
    ∃ op, OkOn h (crc32_combine_gen64 len2) op ∧ IsOp op len2.toInt.toNat := by
  obtain ⟨p, hp, hp32, hpv⟩ := x2nmodp_ok h hs len2 hpos 3
  have hlt : ¬ (len2 < 0) := by rw [Int64.lt_iff_toInt_lt]; simpa using hpos
  have h3 : (3 : UInt32).toNat = 3 := rfl
  have hpv' : ∀ v, mulp p.toUInt32 v = pw (8 * len2.toInt.toNat) v := by
    intro v; rw [hpv v, h3, Nat.mul_comm]
  refine ⟨p, ?_, hp32, ?_, hpv'⟩
  · unfold crc32_combine_gen64; rw [ite_eq_right hlt]; exact hp
  · intro h0
    have := hpv' (e 31)
    rw [h0, mulp_zero_left] at this
    exact e_ne_zero 31 (by omega) (pw_eq_zero _ _ this.symm)

theorem combine_op_ok (h : Heap) (crc1 crc2 op : UInt64) (hop : op.toUInt32 ≠ 0) :
    OkOn h (crc32_combine_op crc1 crc2 op) (mulp op.toUInt32 crc1.toUInt32 ^^^ crc2.toUInt32).toUInt64 := by
  have hne : ¬ (op == 0) = true := by
    intro hh
    have : op = 0 := by simpa using hh
    exact hop (by rw [this]; rfl)
  have hb : (crc1 &&& 0xffffffff).toNat < 2 ^ 32 := by
    rw [and_ffffffff, UInt32.toNat_toUInt64]; exact UInt32.toNat_lt _
  have hm := multmodp_ok h op (crc1 &&& 0xffffffff) hop hb
  rw [and_ffffffff] at hm
  rw [u32_roundtrip] at hm
  unfold crc32_combine_op
  rw [ite_eq_right hne, and_ffffffff crc1, and_ffffffff crc2, UInt32.toUInt64_xor]
  exact OkOn.bind hm (OkOn.pure _ _)

theorem combine64_ok (h : Heap) (hs : StaticsOK h) (crc1 crc2 : UInt64) (len2 : Int64) :
    OkOn h (crc32_combine64 crc1 crc2 len2)
      (if len2.toInt < 0 then 0 else (pw (8 * len2.toInt.toNat) crc1.toUInt32 ^^^ crc2.toUInt32).toUInt64) := by
  unfold crc32_combine64
  by_cases hneg : len2.toInt < 0
  · rw [ite_eq_left hneg]
    refine OkOn.bind (gen64_neg h len2 hneg) ?_
    unfold crc32_combine_op
    rw [ite_eq_left (by decide)]; exact OkOn.pure _ _
  · rw [ite_eq_right hneg]
    obtain ⟨op, hop, hnz, hlt, hv⟩ := gen64_op h hs len2 (by omega)
    refine OkOn.bind hop ?_
    have := combine_op_ok h crc1 crc2 op hlt
    rw [hv] at this
    exact this


/-! ### `multmodp` does not terminate when the low 32 bits of `a` are zero -/

theorem go_diverges {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ) (Inv : σ → Prop)
    (hstep : ∀ s, Inv s → ∀ h, cond s h = .ok ((true, s), h) ∧ ∃ s2, body s h = .ok (s2, h) ∧ Inv s2) :
    ∀ n s h, Inv s → cwhile.go cond body n s h = .error .outOfFuel := by
  intro n
  induction n with
  | zero => intro s h _; simp [cwhile.go]
  | succ n ih =>
    intro s h hI
    obtain ⟨hc, s2, hb, hI2⟩ := hstep s hI h
    simp [cwhile.go, hc, hb, ih s2 h hI2]

theorem and_low_zero (a m : UInt64) (ha : a.toUInt32 = 0) (hm : m.toNat < 2 ^ 32) : a &&& m = 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and]
  have e0 : (0 : UInt64).toNat = 0 := rfl
  rw [e0]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hk : k < 32
  · have h0 : a.toNat % 2 ^ 32 = 0 := by
      have := congrArg UInt32.toNat ha
      rwa [UInt64.toNat_toUInt32] at this
    have : a.toNat.testBit k = false := by
      have h1 := Nat.testBit_mod_two_pow a.toNat 32 k
      rw [h0, Nat.zero_testBit] at h1
      simpa [hk] using h1.symm
    simp [this]
  · have : m.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]

/-- **multmodp, non-termination.** If the low 32 bits of `a` are zero, the loop of `multmodp` never finds a set bit
(`a & m` is 0 for every `m <= 2^31`, `m` then becomes 0): the translation runs out of fuel for every `b` and every heap.
The real C (zlib `develop`) hangs on `crc32_combine_op(1, 2, 1UL << 32)`. -/
theorem multmodp_diverges (a b : UInt64) (ha : a.toUInt32 = 0) (h : Heap) :
    multmodp a b h = .error .outOfFuel := by
  unfold multmodp
  rw [bind_app]
  have key : cwhile (fun x : MS => match x with | (m, p, b, brk) => pure (!brk, m, p, b, brk))
      (fun x : MS => match x with
        | (m, p, b, brk) =>
          have p := p;
          have __do_jp := fun __r p =>
            have m := m >>> 1;
            have b := if (b &&& 1 != 0) = true then b >>> 1 ^^^ POLY else b >>> 1;
            pure (m, p, b, brk);
          if (a &&& m != 0) = true then
            have p := p ^^^ b;
            if (a &&& m - 1 == 0) = true then pure (m, p, b, true) else __do_jp () p
          else __do_jp () p)
      ((1 : UInt64) <<< 31, 0, b, false) h = .error .outOfFuel := by
    refine go_diverges _ _ (fun s : MS => s.2.2.2 = false ∧ s.1.toNat < 2 ^ 32) ?_ fuel _ h ⟨rfl, ?_⟩
    · intro s hI h
      obtain ⟨m, p, bb, brk⟩ := s
      obtain ⟨h1, h2⟩ := hI
      simp only at h1 h2
      subst h1
      have hz : (a &&& m != 0) = false := by rw [and_low_zero a m ha h2]; rfl
      refine ⟨rfl, (m >>> 1, p, (if (bb &&& 1 != 0) = true then bb >>> 1 ^^^ POLY else bb >>> 1), false), ?_, ?_⟩
      · simp [hz]
      · refine ⟨rfl, ?_⟩
        show (m >>> 1).toNat < 2 ^ 32
        rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h2
    · show ((1 : UInt64) <<< 31).toNat < 2 ^ 32
      decide
  rw [key]

theorem combine_op_diverges (h : Heap) (crc1 crc2 op : UInt64) (hop : op ≠ 0) (hlow : op.toUInt32 = 0) :
    crc32_combine_op crc1 crc2 op h = .error .outOfFuel := by
  unfold crc32_combine_op
  have hne : ¬ (op == 0) = true := by simpa using hop
  rw [ite_eq_right hne, bind_app, multmodp_diverges _ _ hlow]

/-! ### The word recurrence of `crc_word` (`W = 4`, `UInt32`) -/

/-- one step of the loop of `crc_word` -/
def wstep (d : UInt32) : UInt32 := (d >>> 8) ^^^ Crc32H.crc_table[(d &&& 0xff).toNat]!

def wsteps : Nat → UInt32 → UInt32
  | 0, d => d
  | n + 1, d => wstep (wsteps n d)

theorem and255_lt32 (d : UInt32) : (d &&& 0xff).toNat < 256 := by
  rw [UInt32.toNat_and]
  have : (0xff : UInt32).toNat = 2 ^ 8 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem and255_lt (d : UInt64) : (d &&& 0xff).toNat < 256 := by
  rw [UInt64.toNat_and]
  have : (0xff : UInt64).toNat = 2 ^ 8 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem toUInt32_ofNat_eq32 (x : UInt32) (_h : x.toNat < 256) : UInt32.ofNat x.toNat = x := by
  simp

theorem toUInt32_ofNat_eq (x : UInt64) (_h : x.toNat < 256) : UInt32.ofNat x.toNat = x.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]

theorem tab_lookup32 (d : UInt32) : Crc32H.crc_table[(d &&& 0xff).toNat]! = pw 8 (d &&& 0xff) := by
  have := crc_table_eq ⟨(d &&& 0xff).toNat, and255_lt32 d⟩
  simp only at this
  rw [this, toUInt32_ofNat_eq32 _ (and255_lt32 d)]

theorem tab_lookup (d : UInt64) : Crc32H.crc_table[(d &&& 0xff).toNat]! = pw 8 (d &&& 0xff).toUInt32 := by
  have := crc_table_eq ⟨(d &&& 0xff).toNat, and255_lt d⟩
  simp only at this
  rw [this, toUInt32_ofNat_eq _ (and255_lt d)]

theorem wstep_xor (a b : UInt32) : wstep (a ^^^ b) = wstep a ^^^ wstep b := by
  unfold wstep
  rw [UInt32.shiftRight_xor, tab_lookup32, tab_lookup32, tab_lookup32, and_xor32, pw_xor]
  ac_rfl

theorem wsteps_xor (n : Nat) (a b : UInt32) : wsteps n (a ^^^ b) = wsteps n a ^^^ wsteps n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [wsteps, ih, wstep_xor]

/-- the byte `j` of a 32-bit word `d`, as a register value -/
def bx (d : UInt32) (j : Nat) : UInt32 := (d >>> (8 * j).toUInt32) &&& 0xff

theorem bx_xor (a b : UInt32) (j : Nat) : bx (a ^^^ b) j = bx a j ^^^ bx b j := by
  unfold bx
  rw [UInt32.shiftRight_xor, and_xor32]

/-- the closed form of `crc_word` (`W = 4`): byte `j` advanced over `4 - j` bytes -/
def psiW (d : UInt32) : Nat → UInt32
  | 0 => 0
  | m + 1 => psiW d m ^^^ pw (8 * (4 - m)) (bx d m)

def Psi (d : UInt32) : UInt32 := psiW d 4

theorem psiW_xor (a b : UInt32) (m : Nat) : psiW (a ^^^ b) m = psiW a m ^^^ psiW b m := by
  induction m with
  | zero => simp [psiW]
  | succ m ih => simp only [psiW, ih, bx_xor, pw_xor]; ac_rfl

theorem Psi_xor (a b : UInt32) : Psi (a ^^^ b) = Psi a ^^^ Psi b := psiW_xor a b 4

set_option maxRecDepth 100000 in
theorem Phi_basis : ∀ t : Fin 32, wsteps 4 (e t.val) = Psi (e t.val) := by
  decide +kernel

theorem Phi_eq_Psi (d : UInt32) : wsteps 4 d = Psi d :=
  lin32_ext (f := wsteps 4) (g := Psi) (wsteps_xor 4) Psi_xor (fun t ht => Phi_basis ⟨t, ht⟩) d

/-- the 32-bit word that `loadWord` assembles from four bytes (little endian) -/
def wob (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (0 : UInt32) ||| b0.toUInt32 <<< (8 * 0).toUInt32 ||| b1.toUInt32 <<< (8 * 1).toUInt32 |||
  b2.toUInt32 <<< (8 * 2).toUInt32 ||| b3.toUInt32 <<< (8 * 3).toUInt32

theorem getLsbD_255 (i : Nat) (h : 8 ≤ i) : (255#32).getLsbD i = false := by
  rw [BitVec.getLsbD_ofNat]
  simp
  intro _
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by omega) h))

theorem bx_wob_0 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 0 = b0.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt32.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_1 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 1 = b1.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_2 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 2 = b2.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem bx_wob_3 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 3 = b3.toUInt32 := by
  unfold bx
  apply u32_ext
  intro i hi
  simp [wob, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft]
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BitVec.getLsbD_of_ge]
  · have : ¬ (255#32).getLsbD i = true := by rw [getLsbD_255 i (by omega)]; decide
    simp [this]
    intro _
    exact BitVec.getLsbD_of_ge _ _ (by omega)

set_option maxRecDepth 100000 in
theorem Psi_basis : ∀ t : Fin 32, Psi (e t.val) = pw 32 (e t.val) := by decide +kernel

theorem Psi_reg (c : UInt32) : Psi c = pw 32 c :=
  lin32_ext (f := Psi) (g := pw 32) Psi_xor (pw_lin 32) (fun t ht => Psi_basis ⟨t, ht⟩) c

theorem Psi_wob (b0 b1 b2 b3 : UInt8) :
    Psi (wob b0 b1 b2 b3) =
      pw 32 b0.toUInt32 ^^^ pw 24 b1.toUInt32 ^^^ pw 16 b2.toUInt32 ^^^ pw 8 b3.toUInt32 := by
  have : Psi (wob b0 b1 b2 b3) =
      (((0 ^^^ pw (8 * (4 - 0)) (bx (wob b0 b1 b2 b3) 0)) ^^^
        pw (8 * (4 - 1)) (bx (wob b0 b1 b2 b3) 1)) ^^^
        pw (8 * (4 - 2)) (bx (wob b0 b1 b2 b3) 2)) ^^^
        pw (8 * (4 - 3)) (bx (wob b0 b1 b2 b3) 3) := rfl
  rw [this, bx_wob_0, bx_wob_1, bx_wob_2, bx_wob_3, UInt32.zero_xor]

theorem rbl_bytes (c : UInt32) (b0 b1 b2 b3 : UInt8) :
    rbl c [b0, b1, b2, b3] =
      pw 32 c ^^^ (pw 32 b0.toUInt32 ^^^ pw 24 b1.toUInt32 ^^^ pw 16 b2.toUInt32 ^^^ pw 8 b3.toUInt32) := by
  rw [rbl_affine]
  simp only [List.length_cons, List.length_nil]
  have : rbl 0 [b0, b1, b2, b3] =
      pw 32 b0.toUInt32 ^^^ pw 24 b1.toUInt32 ^^^ pw 16 b2.toUInt32 ^^^ pw 8 b3.toUInt32 := by
    simp only [rbl_cons, rbl_nil, crcByte_eq, UInt32.zero_xor, pw_xor, ← pw_add]
  rw [this]

/-- the word that `crc_word` is applied to, for the register `c` and the four bytes: its result is the register after
the four bytes. -/
theorem Psi_word (c : UInt32) (b0 b1 b2 b3 : UInt8) :
    Psi (c ^^^ wob b0 b1 b2 b3) = rbl c [b0, b1, b2, b3] := by
  rw [Psi_xor, Psi_reg, Psi_wob, rbl_bytes]

theorem u32_and255_toUInt64 (d : UInt32) : (d &&& 0xff).toUInt64.toNat = (d &&& 0xff).toNat := by
  simp

theorem crc_word_ok (h : Heap) (hs : StaticsOK h) (data : UInt32) : OkOn h (crc_word data) (Psi data) := by
  suffices H : ∃ y, OkOn h (crc_word data) y ∧ y = Psi data by obtain ⟨y, hy, rfl⟩ := H; exact hy
  unfold crc_word
  refine OkOn.bind_ex (R := fun x : UInt32 × Int32 => x.1 = Psi data) ?_ ?_
  · refine cwhile_ok (fun cnt s => ∃ i, i + cnt = 4 ∧ s = (wsteps i data, Int32.ofNat i))
      (fun x : UInt32 × Int32 => x.1 = Psi data) ?_ ?_ (k := 4) (s := (data, (0 : Int32))) ?_ ?_
    · intro cnt s hP
      obtain ⟨i, hi, rfl⟩ := hP
      have hc : (Int32.ofNat i < (4 : Int32)) = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide
      have hk : Int32.ofNat i + 1 = Int32.ofNat (i + 1) := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide
      have ht := crcTab_ok h hs ((wsteps i data &&& 0xff).toUInt64) (by rw [u32_and255_toUInt64]; exact and255_lt32 _)
      rw [u32_and255_toUInt64] at ht
      refine ⟨(wsteps i data, Int32.ofNat i), (wsteps (i + 1) data, Int32.ofNat (i + 1)), ?_, ?_, ⟨i + 1, by omega, rfl⟩⟩
      · show OkOn h (pure _) _
        simp only [W, hc]
        exact OkOn.pure _ _
      · show OkOn h (do let t ← crcTab (wsteps i data &&& 0xff).toUInt64; pure ((wsteps i data >>> 8) ^^^ t, Int32.ofNat i + 1)) _
        rw [hk]
        exact OkOn.bind ht (OkOn.pure _ _)
    · intro s hP
      obtain ⟨i, hi, rfl⟩ := hP
      have : i = 4 := by omega
      subst this
      have hc : (Int32.ofNat 4 < (4 : Int32)) = false := by decide
      refine ⟨(wsteps 4 data, Int32.ofNat 4), ?_, ?_⟩
      · show OkOn h (pure _) _
        simp only [W, hc]
        exact OkOn.pure _ _
      · exact Phi_eq_Psi data
    · exact ⟨0, rfl, rfl⟩
    · show 4 < 2 ^ 64; omega
  · intro x hx
    obtain ⟨d, k⟩ := x
    exact ⟨d, OkOn.pure _ _, hx⟩

/-! ### Loading a word (`W = 4`, `UInt32`, any byte view) -/

theorem idx8 (h : Heap) (ref : BRef) (off i : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : off + i < bs.size) :
    OkOn h (index8 (.ref ref off) i) bs[off + i]! := by
  have := Ptr.index_ok hb hlt
  rw [getElem!_pos bs (off + i) hlt]; exact this

set_option maxRecDepth 4000 in
theorem loadWord_ok (h : Heap) (ref : BRef) (off : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : off + 4 ≤ bs.size) :
    OkOn h (loadWord (.ref ref off))
      (wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]!) := by
  unfold loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  simp only [List.range'_succ, List.range'_zero, List.forIn'_cons, List.forIn'_nil]
  refine OkOn.bind (x := wob bs[off + 0]! bs[off + 1]! bs[off + 2]! bs[off + 3]!) ?_ (OkOn.pure _ _)
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  refine OkOn.bind (x := ForInStep.yield _) (OkOn.bind (idx8 h ref off _ bs hb (by omega)) (OkOn.pure _ _)) ?_
  try dsimp only
  exact OkOn.pure _ _

/-! ### The braid tables (`N = 5`, `NLOW = 2`, `W = 4`) -/

def bw5 (d : UInt32) : UInt32 :=
  (pw (8 * 20) (bx d 0) ^^^ pw (8 * 19) (bx d 1)) ^^^
  (pw (8 * 18) (bx d 2) ^^^ pw (8 * 17) (bx d 3))

def bw2 (d : UInt32) : UInt32 :=
  (pw (8 * 8) (bx d 0) ^^^ pw (8 * 7) (bx d 1)) ^^^
  (pw (8 * 6) (bx d 2) ^^^ pw (8 * 5) (bx d 3))

theorem idx2_5_ok (h : Heap) (kn i : Nat) (hk : kn < 4) (hi : i < 256) :
    OkOn h (idx2 Crc32H.crc_braid5_table kn i) Crc32H.crc_braid5_table[kn]![i]! := by
  have hs := braid5_size
  have hrow : Crc32H.crc_braid5_table[kn]? = some Crc32H.crc_braid5_table[kn]! := by
    rw [getElem!_pos Crc32H.crc_braid5_table kn (by omega)]; simp
  have hrs := hs.2 ⟨kn, hk⟩
  have hcol : Crc32H.crc_braid5_table[kn]![i]? = some Crc32H.crc_braid5_table[kn]![i]! := by
    rw [getElem!_pos Crc32H.crc_braid5_table[kn]! i (by simp only at hrs; omega)]; simp
  unfold idx2
  rw [hrow]
  simp only
  rw [hcol]
  exact OkOn.pure _ _

theorem idx2_2_ok (h : Heap) (kn i : Nat) (hk : kn < 4) (hi : i < 256) :
    OkOn h (idx2 Crc32H.crc_braid2_table kn i) Crc32H.crc_braid2_table[kn]![i]! := by
  have hs := braid2_size
  have hrow : Crc32H.crc_braid2_table[kn]? = some Crc32H.crc_braid2_table[kn]! := by
    rw [getElem!_pos Crc32H.crc_braid2_table kn (by omega)]; simp
  have hrs := hs.2 ⟨kn, hk⟩
  have hcol : Crc32H.crc_braid2_table[kn]![i]? = some Crc32H.crc_braid2_table[kn]![i]! := by
    rw [getElem!_pos Crc32H.crc_braid2_table[kn]! i (by simp only at hrs; omega)]; simp
  unfold idx2
  rw [hrow]
  simp only
  rw [hcol]
  exact OkOn.pure _ _

theorem bx_eq_shr (w : UInt32) :
    bx w 0 = w &&& 0xff ∧ bx w 1 = (w >>> 8) &&& 0xff ∧
    bx w 2 = (w >>> 16) &&& 0xff ∧ bx w 3 = (w >>> 24) &&& 0xff := by
  simp only [bx]; exact ⟨by simp, rfl, rfl, rfl⟩

theorem crcWord5_ok (h : Heap) (w : UInt32) :
    OkOn h (crcWord Crc32H.crc_braid5_table w) (bw5 w) := by
  unfold crcWord bw5
  have hbx := bx_eq_shr w
  have hb0 := idx2_5_ok h 0 (w &&& 0xff).toNat (by decide) (and255_lt32 _)
  have hb1 := idx2_5_ok h 1 ((w >>> 8) &&& 0xff).toNat (by decide) (and255_lt32 _)
  have hb2 := idx2_5_ok h 2 ((w >>> 16) &&& 0xff).toNat (by decide) (and255_lt32 _)
  have hb3 := idx2_5_ok h 3 ((w >>> 24) &&& 0xff).toNat (by decide) (and255_lt32 _)
  rw [braid5_eq ⟨0, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.1] at hb0
  rw [braid5_eq ⟨1, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.2.1] at hb1
  rw [braid5_eq ⟨2, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.2.2.1] at hb2
  rw [braid5_eq ⟨3, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.2.2.2] at hb3
  exact OkOn.bind hb0 (OkOn.bind hb1 (OkOn.bind hb2 (OkOn.bind hb3 (OkOn.pure _ _))))

theorem crcWord2_ok (h : Heap) (w : UInt32) :
    OkOn h (crcWord Crc32H.crc_braid2_table w) (bw2 w) := by
  unfold crcWord bw2
  have hbx := bx_eq_shr w
  have hb0 := idx2_2_ok h 0 (w &&& 0xff).toNat (by decide) (and255_lt32 _)
  have hb1 := idx2_2_ok h 1 ((w >>> 8) &&& 0xff).toNat (by decide) (and255_lt32 _)
  have hb2 := idx2_2_ok h 2 ((w >>> 16) &&& 0xff).toNat (by decide) (and255_lt32 _)
  have hb3 := idx2_2_ok h 3 ((w >>> 24) &&& 0xff).toNat (by decide) (and255_lt32 _)
  rw [braid2_eq ⟨0, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.1] at hb0
  rw [braid2_eq ⟨1, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.2.1] at hb1
  rw [braid2_eq ⟨2, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.2.2.1] at hb2
  rw [braid2_eq ⟨3, by decide⟩ ⟨_, and255_lt32 _⟩, toUInt32_ofNat_eq32 _ (and255_lt32 _), ← hbx.2.2.2] at hb3
  exact OkOn.bind hb0 (OkOn.bind hb1 (OkOn.bind hb2 (OkOn.bind hb3 (OkOn.pure _ _))))

theorem bw5_eq (d : UInt32) : bw5 d = pw 128 (Psi d) := by
  simp only [bw5, Psi, psiW, pw_xor, UInt32.zero_xor, ← pw_add]
  have e0 : 128 + 8 * (4 - 0) = 8 * 20 := by decide
  have e1 : 128 + 8 * (4 - 1) = 8 * 19 := by decide
  have e2 : 128 + 8 * (4 - 2) = 8 * 18 := by decide
  have e3 : 128 + 8 * (4 - 3) = 8 * 17 := by decide
  rw [e0, e1, e2, e3]
  ac_rfl

theorem bw2_eq (d : UInt32) : bw2 d = pw 32 (Psi d) := by
  simp only [bw2, Psi, psiW, pw_xor, UInt32.zero_xor, ← pw_add]
  have e0 : 32 + 8 * (4 - 0) = 8 * 8 := by decide
  have e1 : 32 + 8 * (4 - 1) = 8 * 7 := by decide
  have e2 : 32 + 8 * (4 - 2) = 8 * 6 := by decide
  have e3 : 32 + 8 * (4 - 3) = 8 * 5 := by decide
  rw [e0, e1, e2, e3]
  ac_rfl

/-- the 32-bit word at byte offset `o` of `bs` -/
def WA (bs : Array UInt8) (o : Nat) : UInt32 :=
  wob bs[o + 0]! bs[o + 1]! bs[o + 2]! bs[o + 3]!

theorem wordAt_ok (h : Heap) (ref : BRef) (ow i : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : ow + 4 * i + 4 ≤ bs.size) :
    OkOn h (wordAt (.ref ref ow) i) (WA bs (ow + 4 * i)) := by
  unfold wordAt
  have hadd : OkOn h (Ptr.add (Ptr.ref ref ow) (4 * (i : Int))) (Ptr.ref ref (ow + 4 * i)) := by
    have := Ptr.add_ok (r := ref) (off := ow) (k := 4 * (i : Int)) (a := bs) hb (by omega) (by omega)
    have e : ((ow : Int) + 4 * (i : Int)).toNat = ow + 4 * i := by omega
    rwa [e] at this
  exact OkOn.bind hadd (loadWord_ok h ref (ow + 4 * i) bs hb hlt)

theorem bind_of {α β : Type} {h : Heap} {m : M α} {f : α → M β} {y : β} (R : α → Prop)
    (hm : ∃ x, OkOn h m x ∧ R x) (hf : ∀ x, R x → OkOn h (f x) y) : OkOn h (m >>= f) y := by
  obtain ⟨x, hx, hR⟩ := hm
  exact OkOn.bind hx (hf x hR)

theorem blockLittle_ok (h : Heap) (s : BL) (ref : BRef) (ow : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : ow + 20 ≤ bs.size) (hw : s.words = .ref ref ow) :
    OkOn h (blockLittle s)
      { crc0 := bw5 (s.crc0 ^^^ WA bs ow), crc1 := bw5 (s.crc1 ^^^ WA bs (ow + 4)),
        crc2 := bw5 (s.crc2 ^^^ WA bs (ow + 8)), crc3 := bw5 (s.crc3 ^^^ WA bs (ow + 12)),
        crc4 := bw5 (s.crc4 ^^^ WA bs (ow + 16)), words := .ref ref (ow + 20), blks := s.blks } := by
  have w0 := wordAt_ok h ref ow 0 bs hb (by omega)
  have w1 := wordAt_ok h ref ow 1 bs hb (by omega)
  have w2 := wordAt_ok h ref ow 2 bs hb (by omega)
  have w3 := wordAt_ok h ref ow 3 bs hb (by omega)
  have w4 := wordAt_ok h ref ow 4 bs hb (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at w0
  have hadd : OkOn h (Ptr.add s.words 20) (Ptr.ref ref (ow + 20)) := by
    rw [hw]
    have := Ptr.add_nat_ok (r := ref) (off := ow) (n := 20) (a := bs) hb hlt
    simpa using this
  rw [← hw] at w0 w1 w2 w3 w4
  unfold blockLittle
  refine OkOn.bind w0 ?_; try dsimp only
  refine OkOn.bind w1 ?_; try dsimp only
  refine OkOn.bind w2 ?_; try dsimp only
  refine OkOn.bind w3 ?_; try dsimp only
  refine OkOn.bind w4 ?_; try dsimp only
  refine OkOn.bind hadd ?_; try dsimp only
  refine OkOn.bind (crcWord5_ok h _) ?_; try dsimp only
  refine OkOn.bind (crcWord5_ok h _) ?_; try dsimp only
  refine OkOn.bind (crcWord5_ok h _) ?_; try dsimp only
  refine OkOn.bind (crcWord5_ok h _) ?_; try dsimp only
  refine OkOn.bind (crcWord5_ok h _) ?_; try dsimp only
  exact OkOn.pure _ _

theorem blockLittle2_ok (h : Heap) (s : BL2) (ref : BRef) (ow : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hlt : ow + 8 ≤ bs.size) (hw : s.words = .ref ref ow) :
    OkOn h (blockLittle2 s)
      { crc0 := bw2 (s.crc0 ^^^ WA bs ow), crc1 := bw2 (s.crc1 ^^^ WA bs (ow + 4)),
        words := .ref ref (ow + 8), blks := s.blks } := by
  have w0 := wordAt_ok h ref ow 0 bs hb (by omega)
  have w1 := wordAt_ok h ref ow 1 bs hb (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at w0
  have hadd : OkOn h (Ptr.add s.words 8) (Ptr.ref ref (ow + 8)) := by
    rw [hw]
    have := Ptr.add_nat_ok (r := ref) (off := ow) (n := 8) (a := bs) hb hlt
    simpa using this
  rw [← hw] at w0 w1
  unfold blockLittle2
  refine OkOn.bind w0 ?_; try dsimp only
  refine OkOn.bind w1 ?_; try dsimp only
  refine OkOn.bind hadd ?_; try dsimp only
  refine OkOn.bind (crcWord2_ok h _) ?_; try dsimp only
  refine OkOn.bind (crcWord2_ok h _) ?_; try dsimp only
  exact OkOn.pure _ _

/-! ### The register over a range of a byte array -/

/-- the register after `n` bytes of `bs` from index `o`, starting from `c` -/
def rbFrom (bs : Array UInt8) : UInt32 → Nat → Nat → UInt32
  | c, _, 0 => c
  | c, o, n + 1 => rbFrom bs (ZlibF.Spec.crcByte c bs[o]!) (o + 1) n

theorem rbFrom_zero (bs : Array UInt8) (c : UInt32) (o : Nat) : rbFrom bs c o 0 = c := rfl
theorem rbFrom_succ (bs : Array UInt8) (c : UInt32) (o n : Nat) :
    rbFrom bs c o (n + 1) = rbFrom bs (ZlibF.Spec.crcByte c bs[o]!) (o + 1) n := rfl

theorem rbFrom_add (bs : Array UInt8) (n m : Nat) : ∀ (c : UInt32) (o : Nat),
    rbFrom bs c o (n + m) = rbFrom bs (rbFrom bs c o n) (o + n) m := by
  induction n with
  | zero => intro c o; simp [rbFrom_zero]
  | succ n ih =>
    intro c o
    rw [Nat.succ_add, rbFrom_succ, ih, rbFrom_succ]
    rw [show o + 1 + n = o + (n + 1) by omega]

theorem rbFrom_aff (bs : Array UInt8) (n : Nat) : ∀ (c : UInt32) (o : Nat),
    rbFrom bs c o n = pw (8 * n) c ^^^ rbFrom bs 0 o n := by
  induction n with
  | zero => intro c o; simp [rbFrom_zero, pw]
  | succ n ih =>
    intro c o
    rw [rbFrom_succ, rbFrom_succ, ih, ih (ZlibF.Spec.crcByte 0 bs[o]!)]
    simp only [crcByte_eq, UInt32.zero_xor, pw_xor]
    rw [show 8 * (n + 1) = 8 * n + 8 by omega, pw_add]
    ac_rfl

theorem rbFrom_list (bs : Array UInt8) (n : Nat) : ∀ (c : UInt32) (o : Nat), o + n ≤ bs.size →
    rbFrom bs c o n = rbl c ((bs.toList.drop o).take n) := by
  induction n with
  | zero => intro c o _; simp [rbFrom_zero, rbl_nil]
  | succ n ih =>
    intro c o h
    have ho : o < bs.size := by omega
    have : (bs.toList.drop o) = bs[o] :: bs.toList.drop (o + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using ho)]; simp
    rw [rbFrom_succ, ih _ _ (by omega), this, List.take_succ_cons, rbl_cons]
    rw [getElem!_pos bs o ho]

theorem rbFrom4 (bs : Array UInt8) (c : UInt32) (o : Nat) :
    rbFrom bs c o 4 = rbl c [bs[o + 0]!, bs[o + 1]!, bs[o + 2]!, bs[o + 3]!] := rfl

theorem Psi_WA (c : UInt32) (bs : Array UInt8) (o : Nat) : Psi (c ^^^ WA bs o) = rbFrom bs c o 4 := by
  rw [rbFrom4]; exact Psi_word c _ _ _ _

theorem rbFrom4_xor (bs : Array UInt8) (a b : UInt32) (o : Nat) :
    rbFrom bs (a ^^^ b) o 4 = rbFrom bs a o 4 ^^^ pw 32 b := by
  rw [rbFrom_aff bs 4 (a ^^^ b), rbFrom_aff bs 4 a, pw_xor]
  simp only [Nat.reduceMul]
  ac_rfl

/-! ### The five-word (`N = 5`) and two-word (`NLOW = 2`) chains -/

def Val (c0 c1 c2 c3 c4 : UInt32) : UInt32 :=
  pw 160 c0 ^^^ pw 128 c1 ^^^ pw 96 c2 ^^^ pw 64 c3 ^^^ pw 32 c4

def chain (bs : Array UInt8) (c0 c1 c2 c3 c4 : UInt32) (o : Nat) : UInt32 :=
  rbFrom bs (c4 ^^^ rbFrom bs (c3 ^^^ rbFrom bs (c2 ^^^ rbFrom bs (c1 ^^^ rbFrom bs c0 o 4) (o + 4) 4) (o + 8) 4)
    (o + 12) 4) (o + 16) 4

theorem chain_aff (bs : Array UInt8) (c0 c1 c2 c3 c4 : UInt32) (o : Nat) :
    chain bs c0 c1 c2 c3 c4 o = Val c0 c1 c2 c3 c4 ^^^ chain bs 0 0 0 0 0 o := by
  unfold chain Val
  simp only [rbFrom4_xor]
  rw [rbFrom_aff bs 4 c0 o, rbFrom_aff bs 4 c1 (o + 4), rbFrom_aff bs 4 c2 (o + 8), rbFrom_aff bs 4 c3 (o + 12),
    rbFrom_aff bs 4 c4 (o + 16)]
  simp only [pw_xor, Nat.reduceMul, ← pw_add, Nat.reduceAdd]
  ac_rfl

theorem chain_zero (bs : Array UInt8) (o : Nat) : chain bs 0 0 0 0 0 o = rbFrom bs 0 o 20 := by
  unfold chain
  simp only [UInt32.zero_xor]
  have e1 : ∀ c o, rbFrom bs c o 20 = rbFrom bs (rbFrom bs c o 4) (o + 4) 16 := fun c o => rbFrom_add bs 4 16 c o
  have e2 : ∀ c o, rbFrom bs c o 16 = rbFrom bs (rbFrom bs c o 4) (o + 4) 12 := fun c o => rbFrom_add bs 4 12 c o
  have e3 : ∀ c o, rbFrom bs c o 12 = rbFrom bs (rbFrom bs c o 4) (o + 4) 8 := fun c o => rbFrom_add bs 4 8 c o
  have e4 : ∀ c o, rbFrom bs c o 8 = rbFrom bs (rbFrom bs c o 4) (o + 4) 4 := fun c o => rbFrom_add bs 4 4 c o
  rw [e1, e2, e3, e4]

set_option maxRecDepth 100000 in
/-- `Val` after one pass of the 5 braids: `pw 160` of the chain result -/
theorem val_step (bs : Array UInt8) (c0 c1 c2 c3 c4 : UInt32) (o : Nat) :
    Val (pw 128 (rbFrom bs c0 o 4)) (pw 128 (rbFrom bs c1 (o + 4) 4)) (pw 128 (rbFrom bs c2 (o + 8) 4))
      (pw 128 (rbFrom bs c3 (o + 12) 4)) (pw 128 (rbFrom bs c4 (o + 16) 4)) = pw 160 (chain bs c0 c1 c2 c3 c4 o) := by
  unfold chain Val
  simp only [rbFrom4_xor, pw_xor, ← pw_add, Nat.reduceAdd]
  ac_rfl

def Val2 (c0 c1 : UInt32) : UInt32 :=
  pw 64 c0 ^^^ pw 32 c1

def chain2 (bs : Array UInt8) (c0 c1 : UInt32) (o : Nat) : UInt32 :=
  rbFrom bs (c1 ^^^ rbFrom bs c0 o 4) (o + 4) 4

theorem chain2_aff (bs : Array UInt8) (c0 c1 : UInt32) (o : Nat) :
    chain2 bs c0 c1 o = Val2 c0 c1 ^^^ chain2 bs 0 0 o := by
  unfold chain2 Val2
  simp only [rbFrom4_xor]
  rw [rbFrom_aff bs 4 c0 o, rbFrom_aff bs 4 c1 (o + 4)]
  simp only [pw_xor, Nat.reduceMul, ← pw_add, Nat.reduceAdd]
  ac_rfl

theorem chain2_zero (bs : Array UInt8) (o : Nat) : chain2 bs 0 0 o = rbFrom bs 0 o 8 := by
  unfold chain2
  simp only [UInt32.zero_xor]
  exact (rbFrom_add bs 4 4 0 o).symm

/-- `Val2` after one pass of the 2 braids: `pw 64` of the chain result -/
theorem val2_step (bs : Array UInt8) (c0 c1 : UInt32) (o : Nat) :
    Val2 (pw 32 (rbFrom bs c0 o 4)) (pw 32 (rbFrom bs c1 (o + 4) 4)) = pw 64 (chain2 bs c0 c1 o) := by
  unfold chain2 Val2
  simp only [rbFrom4_xor, pw_xor, ← pw_add, Nat.reduceAdd]
  ac_rfl

/-! ### One byte of the table-driven CRC -/

set_option maxRecDepth 100000 in
theorem pw8_basis : ∀ t : Fin 32,
    pw 8 (e t.val) = (e t.val >>> 8) ^^^ pw 8 (e t.val &&& 0xff) := by decide +kernel

theorem pw8_split (v : UInt32) : pw 8 v = (v >>> 8) ^^^ pw 8 (v &&& 0xff) :=
  lin32_ext (f := pw 8) (g := fun v => (v >>> 8) ^^^ pw 8 (v &&& 0xff)) (pw_lin 8)
    (by intro x y; simp only [UInt32.shiftRight_xor, and_xor32, pw_xor]; ac_rfl)
    (fun t ht => pw8_basis ⟨t, ht⟩) v

theorem wstep_u32 (v : UInt32) : wstep v = pw 8 v := by
  unfold wstep
  rw [tab_lookup32, pw8_split v]

theorem u8_u32_u64 (b : UInt8) : b.toUInt32.toUInt64 = b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp

theorem crcByte_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (ho : o < bs.size) (c : UInt32) :
    OkOn h (crcByte c.toUInt64 (.ref ref o))
      ((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref ref (o + 1)) := by
  unfold crcByte
  have hl := Ptr.load_ok hb ho
  have hadd := Ptr.add_nat_ok (r := ref) (off := o) (n := 1) (a := bs) hb (by omega)
  have ht := crcTab_ok h hs ((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff) (and255_lt _)
  have e : ((c.toUInt64 >>> 8) ^^^ Crc32H.crc_table[((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff).toNat]!.toUInt64) =
      (ZlibF.Spec.crcByte c bs[o]).toUInt64 := by
    have hstep := congrArg UInt32.toUInt64 (wstep_u32 (c ^^^ bs[o].toUInt32))
    unfold wstep at hstep
    rw [UInt32.toUInt64_xor] at hstep
    have hshift : ((c ^^^ bs[o].toUInt32) >>> 8).toUInt64 = c.toUInt64 >>> 8 := by
      have h8 : bs[o].toUInt64 >>> 8 = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        have := UInt8.toNat_lt bs[o]
        simp; omega
      have hsh : ((c ^^^ bs[o].toUInt32) >>> 8).toUInt64 = ((c ^^^ bs[o].toUInt32).toUInt64 >>> 8) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_shiftRight, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, UInt32.toNat_shiftRight]; rfl
      rw [hsh, UInt32.toUInt64_xor, u8_u32_u64, UInt64.shiftRight_xor, h8, UInt64.xor_zero]
    have hidx : ((c ^^^ bs[o].toUInt32) &&& 0xff).toNat = ((c.toUInt64 ^^^ bs[o].toUInt64) &&& 0xff).toNat := by
      have h255 : (0xff : UInt32).toUInt64 = (0xff : UInt64) := rfl
      rw [← u8_u32_u64, ← UInt32.toUInt64_xor, ← h255, ← UInt32.toUInt64_and]; simp
    rw [hshift, hidx] at hstep
    rw [crcByte_eq, hstep]
  rw [getElem!_pos bs o ho]
  rw [← e]
  exact OkOn.bind hl (OkOn.bind hadd (OkOn.bind ht (OkOn.pure _ _)))

/-! ### The tail of `crc32_braid` and `crc32_z`: the loops over eight bytes and over single bytes -/

def cond8 (x : UInt64 × BPtr × UInt64) : M (Bool × UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) => pure (decide (l ≥ 8), c, b, l)

def body8 (x : UInt64 × BPtr × UInt64) : M (UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    have l := l - 8
    do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => do
    let __x ← crcByte c b
    match __x with
    | (c, b) => pure (c, b, l)

def cond1 (x : UInt64 × BPtr × UInt64) : M (Bool × UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) => pure (l != 0, c, b, l)

def body1 (x : UInt64 × BPtr × UInt64) : M (UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    have l := l - 1
    do
    let __x ← crcByte c b
    match __x with
    | (c, b) => pure (c, b, l)

/-- the tail of `crc32_braid` (without post-conditioning XOR) -/
def tailBraid (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  let __x ← cwhile cond8 body8 (crc, buf, len)
  match __x with
  | (c, b, l) => do
    let __x ← cwhile cond1 body1 (c, b, l)
    match __x with
    | (c, _, _) => pure c

/-- the end of `crc32_z` -/
def tailP (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  let __x ← cwhile cond8 body8 (crc, buf, len)
  match __x with
  | (c, b, l) => do
    let __x ← cwhile cond1 body1 (c, b, l)
    match __x with
    | (c, _, _) => pure (c ^^^ 4294967295)

theorem body1_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (ho : o < bs.size) (c : UInt32) (l : UInt64) :
    OkOn h (body1 (c.toUInt64, .ref ref o, l))
      ((ZlibF.Spec.crcByte c bs[o]!).toUInt64, Ptr.ref ref (o + 1), l - 1) := by
  unfold body1
  exact OkOn.bind (crcByte_ok h hs ref o bs hb ho c) (OkOn.pure _ _)

theorem body8_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (ho : o + 8 ≤ bs.size) (c : UInt32) (l : UInt64) :
    OkOn h (body8 (c.toUInt64, .ref ref o, l))
      ((rbFrom bs c o 8).toUInt64, Ptr.ref ref (o + 8), l - 8) := by
  unfold body8
  refine OkOn.bind (crcByte_ok h hs ref o bs hb (by omega) c) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  refine OkOn.bind (crcByte_ok h hs ref (o + 1 + 1 + 1 + 1 + 1 + 1 + 1) bs hb (by omega) _) ?_
  exact OkOn.pure _ _

theorem rbFrom_snoc (bs : Array UInt8) (c : UInt32) (o j : Nat) :
    rbFrom bs c o (j + 1) = ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]! := by
  have := rbFrom_add bs j 1 c o
  rw [this]; rfl

theorem ofNat_sub64 (n k : Nat) (hk : k ≤ n) (hn : n < 2 ^ 64) :
    UInt64.ofNat n - UInt64.ofNat k = UInt64.ofNat (n - k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega)]
  exact hk

theorem ofNat_toNat_lt (n : Nat) (hn : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem loop1_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (cwhile cond1 body1 (c.toUInt64, .ref ref o, UInt64.ofNat L))
      ((rbFrom bs c o L).toUInt64, Ptr.ref ref (o + L), 0) := by
  suffices H : ∃ s, OkOn h (cwhile cond1 body1 (c.toUInt64, .ref ref o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o L).toUInt64, Ptr.ref ref (o + L), 0) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  refine cwhile_ok (fun k s => ∃ j, j + k = L ∧
      s = ((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j))) _ ?_ ?_ (k := L)
    (s := (c.toUInt64, .ref ref o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩ hL
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hne : (UInt64.ofNat (L - j) != 0) = true := by
      have : UInt64.ofNat (L - j) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    refine ⟨((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)),
      ((ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]!).toUInt64, Ptr.ref ref (o + j + 1),
      UInt64.ofNat (L - j) - 1), ?_, ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · exact body1_ok h hs ref (o + j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [rbFrom_snoc, show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - j - 1 = L - (j + 1) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjL : L = j := by omega
    subst hjL
    refine ⟨((rbFrom bs c o L).toUInt64, Ptr.ref ref (o + L), UInt64.ofNat (L - L)), ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [Nat.sub_self]
      exact OkOn.pure _ _
    · simp [Nat.sub_self]

theorem loop8_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (cwhile cond8 body8 (c.toUInt64, .ref ref o, UInt64.ofNat L))
      ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8))) := by
  suffices H : ∃ s, OkOn h (cwhile cond8 body8 (c.toUInt64, .ref ref o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8))) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  refine cwhile_ok (fun k s => ∃ j, j + k = L / 8 ∧
      s = ((rbFrom bs c o (8 * j)).toUInt64, Ptr.ref ref (o + 8 * j), UInt64.ofNat (L - 8 * j))) _ ?_ ?_
    (k := L / 8) (s := (c.toUInt64, .ref ref o, UInt64.ofNat L)) ⟨0, by omega, by simp [rbFrom_zero]⟩
    (by show L / 8 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hge : (decide (UInt64.ofNat (L - 8 * j) ≥ 8)) = true := by
      simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]
      rw [ofNat_toNat_lt _ (by omega)]
      have : (8 : UInt64).toNat = 8 := rfl
      omega
    refine ⟨((rbFrom bs c o (8 * j)).toUInt64, Ptr.ref ref (o + 8 * j), UInt64.ofNat (L - 8 * j)),
      ((rbFrom bs (rbFrom bs c o (8 * j)) (o + 8 * j) 8).toUInt64, Ptr.ref ref (o + 8 * j + 8),
        UInt64.ofNat (L - 8 * j) - 8), ?_, ?_, ?_⟩
    · show OkOn h (pure _) _
      simp only [hge]
      exact OkOn.pure _ _
    · exact body8_ok h hs ref (o + 8 * j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [show 8 * (j + 1) = 8 * j + 8 by omega, rbFrom_add,
        show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - 8 * j - 8 = L - (8 * j + 8) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjq : j = L / 8 := by omega
    have hlt : (decide (UInt64.ofNat (L - 8 * j) ≥ 8)) = false := by
      simp only [decide_eq_false_iff_not, ge_iff_le, UInt64.le_iff_toNat_le, Nat.not_le]
      rw [ofNat_toNat_lt _ (by omega)]
      have : (8 : UInt64).toNat = 8 := rfl
      omega
    subst hjq
    refine ⟨((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
      UInt64.ofNat (L - 8 * (L / 8))), ?_, rfl⟩
    show OkOn h (pure _) _
    simp only [hlt]
    exact OkOn.pure _ _

theorem tailBraid_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (tailBraid c.toUInt64 (.ref ref o) (UInt64.ofNat L)) (rbFrom bs c o L).toUInt64 := by
  unfold tailBraid
  refine bind_of (fun x => x = ((rbFrom bs c o (8 * (L / 8))).toUInt64, Ptr.ref ref (o + 8 * (L / 8)),
        UInt64.ofNat (L - 8 * (L / 8)))) ⟨_, loop8_ok h hs ref o L bs hb hle hL c, rfl⟩ ?_
  intro x hx
  subst hx
  show OkOn h (cwhile cond1 body1 _ >>= _) _
  refine bind_of (fun x => x = ((rbFrom bs (rbFrom bs c o (8 * (L / 8))) (o + 8 * (L / 8)) (L - 8 * (L / 8))).toUInt64,
      Ptr.ref ref (o + 8 * (L / 8) + (L - 8 * (L / 8))), 0))
    ⟨_, loop1_ok h hs ref (o + 8 * (L / 8)) (L - 8 * (L / 8)) bs hb (by omega) (by omega) _, rfl⟩ ?_
  intro x hx
  subst hx
  rw [← rbFrom_add, show 8 * (L / 8) + (L - 8 * (L / 8)) = L by omega]
  exact OkOn.pure _ _

theorem tail_ok (h : Heap) (hs : StaticsOK h) (ref : BRef) (o L : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (c : UInt32) :
    OkOn h (tailP c.toUInt64 (.ref ref o) (UInt64.ofNat L)) ((rbFrom bs c o L).toUInt64 ^^^ 0xffffffff) := by
  have := tailBraid_ok h hs ref o L bs hb hle hL c
  unfold tailBraid at this
  unfold tailP
  refine OkOn.bind (loop8_ok h hs ref o L bs hb hle hL c) ?_
  dsimp only
  refine OkOn.bind (loop1_ok h hs ref (o + 8 * (L / 8)) (L - 8 * (L / 8)) bs hb (by omega) (by omega) _) ?_
  dsimp only
  rw [← rbFrom_add, show 8 * (L / 8) + (L - 8 * (L / 8)) = L by omega]
  exact OkOn.pure _ _

/-! ### The alignment loop (`W = 4`, any byte view) -/

theorem addrOf_ref_ok (h : Heap) (ref : BRef) (offset : Nat) :
    OkOn h (addrOf (.ref ref offset)) (UInt64.ofNat (ByteAddress.base h ref + offset)) := by
  cases ref <;> simp [OkOn, addrOf, ByteAddress.address, ByteAddress.value, ByteAddress.base]

def condA (x : UInt64 × BPtr × UInt64) : M (Bool × UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    if (l == 0) = true then pure (false, c, b, l)
    else do
      let __do_lift ← addrOf b
      pure (__do_lift &&& (W - 1).toInt.toNat.toUInt64 != 0, c, b, l)

def bodyA (x : UInt64 × BPtr × UInt64) : M (UInt64 × BPtr × UInt64) :=
  match x with
  | (c, b, l) =>
    have l := l - 1
    do
    let __x ← crcByte c b
    match __x with
    | (c, b) => pure (c, b, l)

theorem W_pred : (W - 1).toInt.toNat.toUInt64 = 3 := by decide

theorem and3 (n : Nat) : (UInt64.ofNat n &&& 3).toNat = n % 4 := by
  rw [UInt64.toNat_and, UInt64.toNat_ofNat']
  have : (3 : UInt64).toNat = 2 ^ 2 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  have : (n % 2 ^ 64) % 2 ^ 2 = n % 2 ^ 2 := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide))
  rw [this]

def alignLen (o : Nat) : Nat := (4 - o % 4) % 4

theorem loopA_ok (h : Heap) (ref : BRef) (o L : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hle : o + L ≤ bs.size) (hL : L < 2 ^ 64) (h4 : 4 ≤ L) (hs : StaticsOK h) (c : UInt32) :
    OkOn h (cwhile condA bodyA (c.toUInt64, .ref ref o, UInt64.ofNat L))
      ((rbFrom bs c o (alignLen (ByteAddress.base h ref + o))).toUInt64,
        Ptr.ref ref (o + alignLen (ByteAddress.base h ref + o)),
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + o))) := by
  suffices H : ∃ s, OkOn h (cwhile condA bodyA (c.toUInt64, .ref ref o, UInt64.ofNat L)) s ∧
      s = ((rbFrom bs c o (alignLen (ByteAddress.base h ref + o))).toUInt64,
        Ptr.ref ref (o + alignLen (ByteAddress.base h ref + o)),
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + o))) by
    obtain ⟨s, hs', rfl⟩ := H; exact hs'
  have ha3 : alignLen (ByteAddress.base h ref + o) ≤ 3 := by unfold alignLen; omega
  have hcondA : ∀ j, j ≤ alignLen (ByteAddress.base h ref + o) →
      OkOn h (condA ((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)))
        (decide (j < alignLen (ByteAddress.base h ref + o)),
          (rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)) := by
    intro j hj
    have hne : (UInt64.ofNat (L - j) == 0) = false := by
      have : UInt64.ofNat (L - j) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    have hmod : decide ((UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 3) ≠ 0) =
        decide (j < alignLen (ByteAddress.base h ref + o)) := by
      have h1 : (UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 3).toNat =
          (ByteAddress.base h ref + o + j) % 4 := and3 _
      by_cases hj' : j < alignLen (ByteAddress.base h ref + o)
      · have : (UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 3) ≠ 0 := by
          intro h0; rw [h0] at h1
          have h2 : (0 : UInt64).toNat = 0 := rfl
          unfold alignLen at hj'; omega
        rw [decide_eq_true this, decide_eq_true hj']
      · have : (UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 3) = 0 := by
          apply UInt64.toNat_inj.mp
          have h2 : (0 : UInt64).toNat = 0 := rfl
          rw [h1, h2]; unfold alignLen at hj hj'; omega
        rw [decide_eq_false (by rw [this]; simp), decide_eq_false hj']
    unfold condA
    dsimp only
    rw [ite_eq_right (by simp [hne])]
    show OkOn h (addrOf (Ptr.ref ref (o + j)) >>= _) _
    refine OkOn.bind (x := UInt64.ofNat (ByteAddress.base h ref + o + j))
      (by simpa only [Nat.add_assoc] using addrOf_ref_ok h ref (o + j)) ?_
    rw [W_pred]
    show OkOn h (pure _) _
    have hb : ((UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 3) != 0) =
        decide (j < alignLen (ByteAddress.base h ref + o)) := by
      rw [← hmod]
      generalize UInt64.ofNat (ByteAddress.base h ref + o + j) &&& 3 = x
      by_cases hx : x = 0 <;> simp [hx]
    rw [hb]
    exact OkOn.pure _ _
  refine cwhile_ok (fun k s => ∃ j, j + k = alignLen (ByteAddress.base h ref + o) ∧
      s = ((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j))) _ ?_ ?_
    (k := alignLen (ByteAddress.base h ref + o)) (s := (c.toUInt64, .ref ref o, UInt64.ofNat L))
    ⟨0, by omega, by simp [rbFrom_zero]⟩ (by show alignLen (ByteAddress.base h ref + o) < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨j, hj, rfl⟩ := hP
    refine ⟨((rbFrom bs c o j).toUInt64, Ptr.ref ref (o + j), UInt64.ofNat (L - j)),
      ((ZlibF.Spec.crcByte (rbFrom bs c o j) bs[o + j]!).toUInt64, Ptr.ref ref (o + j + 1),
      UInt64.ofNat (L - j) - 1), ?_, ?_, ?_⟩
    · have := hcondA j (by omega)
      rwa [show decide (j < alignLen (ByteAddress.base h ref + o)) = true by simp; omega] at this
    · exact body1_ok h hs ref (o + j) bs hb (by omega) _ _
    · refine ⟨j + 1, by omega, ?_⟩
      rw [rbFrom_snoc, show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      rw [show L - j - 1 = L - (j + 1) by omega]
      rfl
  · intro s hP
    obtain ⟨j, hj, rfl⟩ := hP
    have hjL : alignLen (ByteAddress.base h ref + o) = j := by omega
    subst hjL
    refine ⟨((rbFrom bs c o (alignLen (ByteAddress.base h ref + o))).toUInt64,
      Ptr.ref ref (o + alignLen (ByteAddress.base h ref + o)),
      UInt64.ofNat (L - alignLen (ByteAddress.base h ref + o))), ?_, rfl⟩
    have := hcondA (alignLen (ByteAddress.base h ref + o)) (Nat.le_refl _)
    simpa using this

/-! ### The braided loops (`N = 5` and `NLOW = 2`) -/

def condBlk (s : BL) : M (Bool × BL) :=
  have blks := s.blks - 1
  pure (blks != 0, { crc0 := s.crc0, crc1 := s.crc1, crc2 := s.crc2, crc3 := s.crc3, crc4 := s.crc4,
                     words := s.words, blks := blks })

def condBlk2 (s : BL2) : M (Bool × BL2) :=
  have blks := s.blks - 1
  pure (blks != 0, { crc0 := s.crc0, crc1 := s.crc1, words := s.words, blks := blks })

theorem bw5_Psi (c : UInt32) (bs : Array UInt8) (o : Nat) :
    bw5 (c ^^^ WA bs o) = pw 128 (rbFrom bs c o 4) := by
  rw [bw5_eq, Psi_WA]

theorem bw2_Psi (c : UInt32) (bs : Array UInt8) (o : Nat) :
    bw2 (c ^^^ WA bs o) = pw 32 (rbFrom bs c o 4) := by
  rw [bw2_eq, Psi_WA]

theorem val_inv (bs : Array UInt8) (c0 c1 c2 c3 c4 R : UInt32) (ow : Nat)
    (hV : Val c0 c1 c2 c3 c4 = pw 160 R) :
    Val (pw 128 (rbFrom bs c0 ow 4)) (pw 128 (rbFrom bs c1 (ow + 4) 4)) (pw 128 (rbFrom bs c2 (ow + 8) 4))
      (pw 128 (rbFrom bs c3 (ow + 12) 4)) (pw 128 (rbFrom bs c4 (ow + 16) 4)) = pw 160 (rbFrom bs R ow 20) := by
  rw [val_step, chain_aff, hV, chain_zero, rbFrom_aff bs 20 R ow]

theorem val2_inv (bs : Array UInt8) (c0 c1 R : UInt32) (ow : Nat)
    (hV : Val2 c0 c1 = pw 64 R) :
    Val2 (pw 32 (rbFrom bs c0 ow 4)) (pw 32 (rbFrom bs c1 (ow + 4) 4)) = pw 64 (rbFrom bs R ow 8) := by
  rw [val2_step, chain2_aff, hV, chain2_zero, rbFrom_aff bs 8 R ow]

theorem loopBlk_ok (h : Heap) (ref : BRef) (o1 B : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hB : 1 ≤ B) (hle : o1 + 20 * B ≤ bs.size) (hB64 : B < 2 ^ 64) (c : UInt32) :
    ∃ s : BL, OkOn h (cwhile condBlk blockLittle
        { crc0 := c, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := (.ref ref o1 : BPtr), blks := UInt64.ofNat B }) s ∧
      Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 160 (rbFrom bs c o1 (20 * (B - 1))) ∧
      s.words = .ref ref (o1 + 20 * (B - 1)) := by
  refine cwhile_ok (cond := condBlk) (body := blockLittle)
    (fun k s => ∃ j, j + k = B - 1 ∧ s.words = .ref ref (o1 + 20 * j) ∧
      s.blks = UInt64.ofNat (B - j) ∧
      Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 160 (rbFrom bs c o1 (20 * j)))
    (fun s => Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 = pw 160 (rbFrom bs c o1 (20 * (B - 1))) ∧
      s.words = .ref ref (o1 + 20 * (B - 1))) ?_ ?_ (k := B - 1)
    (s := { crc0 := c, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words := (.ref ref o1 : BPtr), blks := UInt64.ofNat B })
    ?_ (by show B - 1 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨c0, c1, c2, c3, c4, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hne : (UInt64.ofNat (B - j) - 1 != 0) = true := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      have : UInt64.ofNat (B - j - 1) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    let s1 : BL := { crc0 := c0, crc1 := c1, crc2 := c2, crc3 := c3, crc4 := c4,
                     words := (.ref ref (o1 + 20 * j) : BPtr), blks := UInt64.ofNat (B - j) - 1 }
    have hbk := blockLittle_ok h s1 ref (o1 + 20 * j) bs hb (by omega) rfl
    refine ⟨s1, _, ?_, hbk, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · refine ⟨j + 1, by omega, rfl, ?_, ?_⟩
      · show UInt64.ofNat (B - j) - 1 = UInt64.ofNat (B - (j + 1))
        rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
        rfl
      · show Val (bw5 (c0 ^^^ WA bs (o1 + 20 * j))) (bw5 (c1 ^^^ WA bs (o1 + 20 * j + 4)))
          (bw5 (c2 ^^^ WA bs (o1 + 20 * j + 8))) (bw5 (c3 ^^^ WA bs (o1 + 20 * j + 12)))
          (bw5 (c4 ^^^ WA bs (o1 + 20 * j + 16))) = _
        rw [bw5_Psi, bw5_Psi, bw5_Psi, bw5_Psi, bw5_Psi, val_inv bs c0 c1 c2 c3 c4 _ _ hV]
        rw [show 20 * (j + 1) = 20 * j + 20 by omega, rbFrom_add]
  · intro s hP
    obtain ⟨c0, c1, c2, c3, c4, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hjB : j = B - 1 := by omega
    subst hjB
    have hz : (UInt64.ofNat (B - (B - 1)) - 1 != 0) = false := by
      rw [show B - (B - 1) = 1 by omega]
      decide
    refine ⟨{ crc0 := c0, crc1 := c1, crc2 := c2, crc3 := c3, crc4 := c4,
              words := (.ref ref (o1 + 20 * (B - 1)) : BPtr), blks := UInt64.ofNat (B - (B - 1)) - 1 }, ?_, hV, rfl⟩
    show OkOn h (pure _) _
    simp only [hz]
    exact OkOn.pure _ _
  · refine ⟨0, by omega, rfl, rfl, ?_⟩
    simp [Val, rbFrom_zero, pw_zero]

theorem loopBlk2_ok (h : Heap) (ref : BRef) (o1 B : Nat) (bs : Array UInt8) (hb : Space.get h ref = some bs)
    (hB : 1 ≤ B) (hle : o1 + 8 * B ≤ bs.size) (hB64 : B < 2 ^ 64) (c : UInt32) :
    ∃ s : BL2, OkOn h (cwhile condBlk2 blockLittle2
        { crc0 := c, crc1 := 0, words := (.ref ref o1 : BPtr), blks := UInt64.ofNat B }) s ∧
      Val2 s.crc0 s.crc1 = pw 64 (rbFrom bs c o1 (8 * (B - 1))) ∧
      s.words = .ref ref (o1 + 8 * (B - 1)) := by
  refine cwhile_ok (cond := condBlk2) (body := blockLittle2)
    (fun k s => ∃ j, j + k = B - 1 ∧ s.words = .ref ref (o1 + 8 * j) ∧
      s.blks = UInt64.ofNat (B - j) ∧
      Val2 s.crc0 s.crc1 = pw 64 (rbFrom bs c o1 (8 * j)))
    (fun s => Val2 s.crc0 s.crc1 = pw 64 (rbFrom bs c o1 (8 * (B - 1))) ∧
      s.words = .ref ref (o1 + 8 * (B - 1))) ?_ ?_ (k := B - 1)
    (s := { crc0 := c, crc1 := 0, words := (.ref ref o1 : BPtr), blks := UInt64.ofNat B })
    ?_ (by show B - 1 < 2 ^ 64; omega)
  · intro k s hP
    obtain ⟨c0, c1, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hne : (UInt64.ofNat (B - j) - 1 != 0) = true := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
      have : UInt64.ofNat (B - j - 1) ≠ 0 := by
        intro h0
        have := congrArg UInt64.toNat h0
        rw [ofNat_toNat_lt _ (by omega)] at this
        have h1 : (0 : UInt64).toNat = 0 := rfl
        omega
      simpa using this
    let s1 : BL2 := { crc0 := c0, crc1 := c1,
                      words := (.ref ref (o1 + 8 * j) : BPtr), blks := UInt64.ofNat (B - j) - 1 }
    have hbk := blockLittle2_ok h s1 ref (o1 + 8 * j) bs hb (by omega) rfl
    refine ⟨s1, _, ?_, hbk, ?_⟩
    · show OkOn h (pure _) _
      simp only [hne]
      exact OkOn.pure _ _
    · refine ⟨j + 1, by omega, rfl, ?_, ?_⟩
      · show UInt64.ofNat (B - j) - 1 = UInt64.ofNat (B - (j + 1))
        rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ofNat_sub64 _ _ (by omega) (by omega)]
        rfl
      · show Val2 (bw2 (c0 ^^^ WA bs (o1 + 8 * j))) (bw2 (c1 ^^^ WA bs (o1 + 8 * j + 4))) = _
        rw [bw2_Psi, bw2_Psi, val2_inv bs c0 c1 _ _ hV]
        rw [show 8 * (j + 1) = 8 * j + 8 by omega, rbFrom_add]
  · intro s hP
    obtain ⟨c0, c1, words, blks⟩ := s
    obtain ⟨j, hj, hw, hbl, hV⟩ := hP
    simp only at hw hbl hV
    subst hw hbl
    have hjB : j = B - 1 := by omega
    subst hjB
    have hz : (UInt64.ofNat (B - (B - 1)) - 1 != 0) = false := by
      rw [show B - (B - 1) = 1 by omega]
      decide
    refine ⟨{ crc0 := c0, crc1 := c1,
              words := (.ref ref (o1 + 8 * (B - 1)) : BPtr), blks := UInt64.ofNat (B - (B - 1)) - 1 }, ?_, hV, rfl⟩
    show OkOn h (pure _) _
    simp only [hz]
    exact OkOn.pure _ _
  · refine ⟨0, by omega, rfl, rfl, ?_⟩
    simp [Val2, rbFrom_zero, pw_zero]

theorem ofNat_div64 (n k : Nat) (hn : n < 2 ^ 64) (_hk : 0 < k) (hk64 : k < 2 ^ 64) :
    UInt64.ofNat n / UInt64.ofNat k = UInt64.ofNat (n / k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

theorem ofNat_mul64 (a b : Nat) (h : a * b < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

theorem crc_init (crc : UInt64) : (~~~crc &&& 4294967295) = (~~~ crc.toUInt32).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have h1 : (4294967295 : UInt64).toNat = 2 ^ 32 - 1 := by decide
  rw [UInt64.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, UInt32.toNat_toUInt64]
  rw [UInt64.toNat_not, UInt32.toNat_not, UInt64.toNat_toUInt32]
  have := UInt64.toNat_lt crc
  have e1 : UInt64.size = 2 ^ 64 := rfl
  have e2 : UInt32.size = 2 ^ 32 := rfl
  simp only [e1, e2] at *
  omega

theorem ge11 (L : Nat) (hL : L < 2 ^ 64) : (UInt64.ofNat L ≥ 11) ↔ 11 ≤ L := by
  have : (11 : UInt64).toNat = 11 := rfl
  rw [ge_iff_le, UInt64.le_iff_toNat_le, this, ofNat_toNat_lt _ hL]

theorem lt320 (L : Nat) (hL : L < 2 ^ 64) : (UInt64.ofNat L < 320) ↔ L < 320 := by
  have : (320 : UInt64).toNat = 320 := rfl
  rw [UInt64.lt_iff_toNat_lt, this, ofNat_toNat_lt _ hL]

theorem lt23 (L : Nat) (hL : L < 2 ^ 64) : (UInt64.ofNat L < 23) ↔ L < 23 := by
  have : (23 : UInt64).toNat = 23 := rfl
  rw [UInt64.lt_iff_toNat_lt, this, ofNat_toNat_lt _ hL]

theorem NW_val : (N * W).toInt.toNat.toUInt64 = 20 := by decide
theorem NWW_val : (N * W + W - 1).toInt.toNat.toUInt64 = 23 := by decide
theorem NMINWW_val : (NMIN * W + W - 1).toInt.toNat.toUInt64 = 11 := by decide
theorem BRAID_CUT_val : BRAID_CUT.toInt.toNat.toUInt64 = 320 := by decide
theorem NW2_val : (NLOW * W).toInt.toNat.toUInt64 = 8 := by decide
theorem NWW2_val : (NLOW * W + W - 1).toInt.toNat.toUInt64 = 11 := by decide

theorem xor_u64_toUInt32 (a b : UInt32) : (a.toUInt64 ^^^ b.toUInt64).toUInt32 = a ^^^ b := by
  rw [← UInt32.toUInt64_xor, u32_roundtrip]

theorem crc32_braid_ok_view (h : Heap) (hs : StaticsOK h) (c : UInt32) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    OkOn h (crc32_braid c.toUInt64 (.ref ref off) len) (rbFrom bs c off len.toNat).toUInt64 := by
  have hlen' : len = UInt64.ofNat len.toNat := UInt64.ofNat_toNat.symm
  have hL : len.toNat < 2 ^ 64 := UInt64.toNat_lt len
  generalize len.toNat = L at hlen' hlen hL ⊢
  subst hlen'
  unfold crc32_braid
  dsimp only
  by_cases h11 : 11 ≤ L
  · rw [ite_eq_left (by rw [NWW2_val]; exact (ge11 L hL).mpr h11)]
    have ha3 : alignLen (ByteAddress.base h ref + off) ≤ 3 := by unfold alignLen; omega
    refine bind_of (fun x => x = ((rbFrom bs c off (alignLen (ByteAddress.base h ref + off))).toUInt64,
      Ptr.ref ref (off + alignLen (ByteAddress.base h ref + off)),
      UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off))))
      ⟨_, loopA_ok h ref off L bs hb hlen hL (by omega) hs c, rfl⟩ ?_
    intro x hx
    subst hx
    dsimp only
    rw [NW2_val]
    rw [ite_eq_left (by decide), u32_roundtrip]
    have hB1 : 1 ≤ (L - alignLen (ByteAddress.base h ref + off)) / 8 := by omega
    have hBle : off + alignLen (ByteAddress.base h ref + off) + 8 * ((L - alignLen (ByteAddress.base h ref + off)) / 8) ≤ bs.size := by omega
    have hdiv : UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off)) / 8 =
        UInt64.ofNat ((L - alignLen (ByteAddress.base h ref + off)) / 8) := by
      rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_div64 _ _ (by omega) (by omega) (by omega)]
    have hrem : UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off)) -
        UInt64.ofNat ((L - alignLen (ByteAddress.base h ref + off)) / 8) * 8 =
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off) -
          (L - alignLen (ByteAddress.base h ref + off)) / 8 * 8) := by
      rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_mul64 _ _ (by omega) (by omega) (by omega),
        ofNat_sub64 _ _ (by omega) (by omega)]
    rw [hdiv, hrem]
    refine bind_of (fun s : BL2 => Val2 s.crc0 s.crc1 =
        pw 64 (rbFrom bs (rbFrom bs c off (alignLen (ByteAddress.base h ref + off)))
          (off + alignLen (ByteAddress.base h ref + off))
          (8 * ((L - alignLen (ByteAddress.base h ref + off)) / 8 - 1))) ∧
        s.words = .ref ref (off + alignLen (ByteAddress.base h ref + off) +
          8 * ((L - alignLen (ByteAddress.base h ref + off)) / 8 - 1)))
      (loopBlk2_ok h ref (off + alignLen (ByteAddress.base h ref + off))
        ((L - alignLen (ByteAddress.base h ref + off)) / 8) bs hb hB1 hBle (by omega) _) ?_
    intro s hR
    obtain ⟨hV, hw⟩ := hR
    rw [hw]
    generalize hA : alignLen (ByteAddress.base h ref + off) = a at ha3 hB1 hBle hdiv hrem hV hw ⊢
    generalize hB : (L - a) / 8 = B at hB1 hBle hdiv hrem hV hw ⊢
    generalize hc' : rbFrom bs c off a = c' at hV ⊢
    generalize how : off + a + 8 * (B - 1) = ow at hV hw ⊢
    have w0 := wordAt_ok h ref ow 0 bs hb (by omega)
    have w1 := wordAt_ok h ref ow 1 bs hb (by omega)
    have hadd : OkOn h (Ptr.add (Ptr.ref ref ow) 8) (Ptr.ref ref (ow + 8)) := by
      have := Ptr.add_nat_ok (r := ref) (off := ow) (n := 8) (a := bs) hb (by omega)
      simpa using this
    refine OkOn.bind w0 ?_
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [Psi_WA]
    refine OkOn.bind w1 ?_
    rw [xor_u64_toUInt32]
    refine OkOn.bind (crc_word_ok h hs _) ?_
    rw [show s.crc1 ^^^ WA bs (ow + 4 * 1) ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4 =
        (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) ^^^ WA bs (ow + 4 * 1) by ac_rfl, Psi_WA]
    refine OkOn.bind hadd ?_
    have hx2 : rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4 =
        rbFrom bs c' (off + a) (8 * B) := by
      have h1 := chain2_aff bs s.crc0 s.crc1 ow
      rw [hV, chain2_zero] at h1
      change chain2 bs s.crc0 s.crc1 ow = _
      rw [h1, ← rbFrom_aff bs 8 _ ow, ← how, ← rbFrom_add]
      congr 1; omega
    have hall : rbFrom bs c' (off + a) (8 * B + (L - a - B * 8)) = rbFrom bs c off L := by
      rw [← hc']
      have := rbFrom_add bs a (L - a) c off
      rw [show a + (L - a) = L by omega] at this
      rw [this, hc', show 8 * B + (L - a - B * 8) = L - a by omega]
    rw [hx2]
    rw [rbFrom_add, show off + a + 8 * B = ow + 8 by omega] at hall
    rw [← hall]
    exact tailBraid_ok h hs ref (ow + 8) (L - a - B * 8) bs hb (by omega) (by omega) _
  · rw [ite_eq_right (by rw [NWW2_val]; exact fun hh => h11 ((ge11 L hL).mp hh))]
    exact tailBraid_ok h hs ref off L bs hb hlen hL _

theorem crc32_z_ok_view (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    OkOn h (crc32_z crc (.ref ref off) len)
      ((rbFrom bs (~~~ crc.toUInt32) off len.toNat).toUInt64 ^^^ 0xffffffff) := by
  have hlen' : len = UInt64.ofNat len.toNat := UInt64.ofNat_toNat.symm
  have hL : len.toNat < 2 ^ 64 := UInt64.toNat_lt len
  generalize len.toNat = L at hlen' hlen hL ⊢
  subst hlen'
  unfold crc32_z
  rw [ite_eq_right (by simp)]
  dsimp only
  rw [crc_init]
  by_cases h11 : 11 ≤ L
  · rw [ite_eq_left (by rw [NMINWW_val]; exact (ge11 L hL).mpr h11)]
    by_cases hshort : L < 320
    · have hcond : ((UInt64.ofNat L < BRAID_CUT.toInt.toNat.toUInt64 ||
          UInt64.ofNat L < (N * W + W - 1).toInt.toNat.toUInt64) = true) := by
        rw [BRAID_CUT_val, Bool.or_eq_true]
        exact Or.inl (by simp [lt320 L hL, hshort])
      rw [ite_eq_left hcond]
      have hbr := crc32_braid_ok_view h hs (~~~ crc.toUInt32) ref off bs hb (UInt64.ofNat L)
        (by simpa [ofNat_toNat_lt L hL] using hlen)
      rw [ofNat_toNat_lt L hL] at hbr
      exact OkOn.bind hbr (OkOn.pure _ _)
    · have hcond : ¬ ((UInt64.ofNat L < BRAID_CUT.toInt.toNat.toUInt64 ||
          UInt64.ofNat L < (N * W + W - 1).toInt.toNat.toUInt64) = true) := by
        rw [BRAID_CUT_val, NWW_val, Bool.or_eq_true]
        simp [lt320 L hL, lt23 L hL]
        omega
      rw [ite_eq_right hcond]
      have ha3 : alignLen (ByteAddress.base h ref + off) ≤ 3 := by unfold alignLen; omega
      refine bind_of (fun x => x = ((rbFrom bs (~~~ crc.toUInt32) off (alignLen (ByteAddress.base h ref + off))).toUInt64,
        Ptr.ref ref (off + alignLen (ByteAddress.base h ref + off)),
        UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off))))
        ⟨_, loopA_ok h ref off L bs hb hlen hL (by omega) hs _, rfl⟩ ?_
      intro x hx
      subst hx
      dsimp only
      rw [NW_val]
      rw [ite_eq_left (by decide), u32_roundtrip]
      have hB1 : 1 ≤ (L - alignLen (ByteAddress.base h ref + off)) / 20 := by omega
      have hBle : off + alignLen (ByteAddress.base h ref + off) + 20 * ((L - alignLen (ByteAddress.base h ref + off)) / 20) ≤ bs.size := by omega
      have hdiv : UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off)) / 20 =
          UInt64.ofNat ((L - alignLen (ByteAddress.base h ref + off)) / 20) := by
        rw [show (20 : UInt64) = UInt64.ofNat 20 from rfl, ofNat_div64 _ _ (by omega) (by omega) (by omega)]
      have hrem : UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off)) -
          UInt64.ofNat ((L - alignLen (ByteAddress.base h ref + off)) / 20) * 20 =
          UInt64.ofNat (L - alignLen (ByteAddress.base h ref + off) -
            (L - alignLen (ByteAddress.base h ref + off)) / 20 * 20) := by
        rw [show (20 : UInt64) = UInt64.ofNat 20 from rfl, ofNat_mul64 _ _ (by omega) (by omega) (by omega),
          ofNat_sub64 _ _ (by omega) (by omega)]
      rw [hdiv, hrem]
      refine bind_of (fun s : BL => Val s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 =
          pw 160 (rbFrom bs (rbFrom bs (~~~ crc.toUInt32) off (alignLen (ByteAddress.base h ref + off)))
            (off + alignLen (ByteAddress.base h ref + off))
            (20 * ((L - alignLen (ByteAddress.base h ref + off)) / 20 - 1))) ∧
          s.words = .ref ref (off + alignLen (ByteAddress.base h ref + off) +
            20 * ((L - alignLen (ByteAddress.base h ref + off)) / 20 - 1)))
        (loopBlk_ok h ref (off + alignLen (ByteAddress.base h ref + off))
          ((L - alignLen (ByteAddress.base h ref + off)) / 20) bs hb hB1 hBle (by omega) _) ?_
      intro s hR
      obtain ⟨hV, hw⟩ := hR
      rw [hw]
      generalize hA : alignLen (ByteAddress.base h ref + off) = a at ha3 hB1 hBle hdiv hrem hV hw ⊢
      generalize hB : (L - a) / 20 = B at hB1 hBle hdiv hrem hV hw ⊢
      generalize hc' : rbFrom bs (~~~crc.toUInt32) off a = c' at hV ⊢
      generalize how : off + a + 20 * (B - 1) = ow at hV hw ⊢
      have w0 := wordAt_ok h ref ow 0 bs hb (by omega)
      have w1 := wordAt_ok h ref ow 1 bs hb (by omega)
      have w2 := wordAt_ok h ref ow 2 bs hb (by omega)
      have w3 := wordAt_ok h ref ow 3 bs hb (by omega)
      have w4 := wordAt_ok h ref ow 4 bs hb (by omega)
      have hadd : OkOn h (Ptr.add (Ptr.ref ref ow) 20) (Ptr.ref ref (ow + 20)) := by
        have := Ptr.add_nat_ok (r := ref) (off := ow) (n := 20) (a := bs) hb (by omega)
        simpa using this
      refine OkOn.bind w0 ?_
      refine OkOn.bind (crc_word_ok h hs _) ?_
      rw [Psi_WA]
      refine OkOn.bind w1 ?_
      rw [xor_u64_toUInt32]
      refine OkOn.bind (crc_word_ok h hs _) ?_
      rw [show s.crc1 ^^^ WA bs (ow + 4 * 1) ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4 =
          (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) ^^^ WA bs (ow + 4 * 1) by ac_rfl, Psi_WA]
      refine OkOn.bind w2 ?_
      rw [xor_u64_toUInt32]
      refine OkOn.bind (crc_word_ok h hs _) ?_
      rw [show s.crc2 ^^^ WA bs (ow + 4 * 2) ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4 =
          (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4) ^^^ WA bs (ow + 4 * 2) by ac_rfl, Psi_WA]
      refine OkOn.bind w3 ?_
      rw [xor_u64_toUInt32]
      refine OkOn.bind (crc_word_ok h hs _) ?_
      rw [show s.crc3 ^^^ WA bs (ow + 4 * 3) ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4) (ow + 4 * 2) 4 =
          (s.crc3 ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4) (ow + 4 * 2) 4) ^^^ WA bs (ow + 4 * 3) by ac_rfl, Psi_WA]
      refine OkOn.bind w4 ?_
      rw [xor_u64_toUInt32]
      refine OkOn.bind (crc_word_ok h hs _) ?_
      rw [show s.crc4 ^^^ WA bs (ow + 4 * 4) ^^^ rbFrom bs (s.crc3 ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4) (ow + 4 * 2) 4) (ow + 4 * 3) 4 =
          (s.crc4 ^^^ rbFrom bs (s.crc3 ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4) (ow + 4 * 1) 4) (ow + 4 * 2) 4) (ow + 4 * 3) 4) ^^^ WA bs (ow + 4 * 4) by ac_rfl, Psi_WA]
      refine OkOn.bind hadd ?_
      have hx4 : rbFrom bs (s.crc4 ^^^ rbFrom bs (s.crc3 ^^^ rbFrom bs (s.crc2 ^^^ rbFrom bs (s.crc1 ^^^ rbFrom bs s.crc0 (ow + 4 * 0) 4)
          (ow + 4 * 1) 4) (ow + 4 * 2) 4) (ow + 4 * 3) 4) (ow + 4 * 4) 4 = rbFrom bs c' (off + a) (20 * B) := by
        have h1 := chain_aff bs s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 ow
        rw [hV, chain_zero] at h1
        change chain bs s.crc0 s.crc1 s.crc2 s.crc3 s.crc4 ow = _
        rw [h1, ← rbFrom_aff bs 20 _ ow, ← how, ← rbFrom_add]
        congr 1; omega
      have hall : rbFrom bs c' (off + a) (20 * B + (L - a - B * 20)) = rbFrom bs (~~~crc.toUInt32) off L := by
        rw [← hc']
        have := rbFrom_add bs a (L - a) (~~~crc.toUInt32) off
        rw [show a + (L - a) = L by omega] at this
        rw [this, hc', show 20 * B + (L - a - B * 20) = L - a by omega]
      rw [hx4]
      rw [rbFrom_add, show off + a + 20 * B = ow + 20 by omega] at hall
      rw [← hall]
      exact tail_ok h hs ref (ow + 20) (L - a - B * 20) bs hb (by omega) (by omega) _
  · rw [ite_eq_right (by rw [NMINWW_val]; exact fun hh => h11 ((ge11 L hL).mp hh))]
    exact tail_ok h hs ref off L bs hb hlen hL _

/-! ### Unconditional heap-preservation (`PureH`) -/

/-- A computation that leaves the heap untouched whenever it succeeds. -/
def PureH {α : Type} (m : M α) : Prop := ∀ h v h', m h = .ok (v, h') → h' = h

theorem pureH_pure {α : Type} (a : α) : PureH (pure a : M α) := fun _ _ _ h => by cases h; rfl
theorem pureH_ub {α : Type} (s : String) : PureH (ub s : M α) := fun _ _ _ h => by cases h

theorem pureH_bind {α β : Type} {m : M α} {f : α → M β} (hm : PureH m) (hf : ∀ x, PureH (f x)) :
    PureH (m >>= f) := by
  intro h v h' hr
  rw [bind_app] at hr
  cases he : m h with
  | error e => rw [he] at hr; cases hr
  | ok p => rw [he] at hr; exact (hf p.1 p.2 v h' hr).trans (hm h p.1 p.2 he)

theorem pureH_ite {α : Type} {P : Prop} [Decidable P] {t e : M α} (ht : PureH t) (he : PureH e) :
    PureH (if P then t else e) := by
  by_cases hP : P <;> simp [hP, ht, he]

theorem pureH_cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ s, PureH (cond s)) (hb : ∀ s, PureH (body s)) (s : σ) :
    PureH (cwhile cond body s) := by
  have key : ∀ n s, PureH (cwhile.go cond body n s) := by
    intro n
    induction n with
    | zero => intro s h v h' hr; simp [cwhile.go] at hr
    | succ n ih =>
      intro s h v h' hr
      simp only [cwhile.go, bind_app] at hr
      cases hcnd : cond s h with
      | error e => rw [hcnd] at hr; cases hr
      | ok p =>
        obtain ⟨⟨test, mid⟩, h1⟩ := p
        rw [hcnd] at hr
        have hp1 := hc s h (test, mid) h1 hcnd
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at hr
          cases hr
          exact hp1
        | true =>
          simp only [ite_true, bind_app] at hr
          cases hbd : body mid h1 with
          | error e => rw [hbd] at hr; cases hr
          | ok q =>
            rw [hbd] at hr
            exact (ih q.1 q.2 v h' hr).trans ((hb mid h1 q.1 q.2 hbd).trans hp1)
  exact key fuel s

theorem pureH_list_forIn {α β : Type} (xs : List α)
    (body : (x : α) → x ∈ xs → β → M (ForInStep β))
    (hb : ∀ x hx s, PureH (body x hx s)) (init : β) : PureH (List.forIn' xs init body) := by
  induction xs generalizing init with
  | nil => simp only [List.forIn'_eq_forIn', List.forIn'_nil]; exact pureH_pure _
  | cons a t ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine pureH_bind (hb a (by simp) init) (fun st => ?_)
    cases st with
    | done v => exact pureH_pure _
    | yield s => exact ih (fun x hx b => body x (by simp [hx]) b) (fun x hx b => hb x (by simp [hx]) b) s

theorem pureH_ptr_add {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) : PureH (Ptr.add p k) := by
  intro h v h' hr
  unfold Ptr.add at hr
  by_cases hk : k = 0
  · simp [hk] at hr; exact hr.2.symm
  · simp only [hk, ↓reduceIte] at hr
    cases p with
    | null => cases hr
    | ref r off =>
      simp only at hr
      cases hs : Space.get h r with
      | none => rw [hs] at hr; cases hr
      | some a =>
        rw [hs] at hr
        by_cases hb : 0 ≤ (off : Int) + k ∧ (off : Int) + k ≤ (a.size : Int)
        · simp [hb] at hr; exact hr.2.symm
        · simp [hb] at hr

theorem pureH_ptr_load {R T : Type} [Space Heap R T] (p : Ptr R) : PureH (Ptr.load (T := T) p) := by
  intro h v h' hr
  unfold Ptr.load at hr
  cases p with
  | null => cases hr
  | ref r off =>
    simp only at hr
    cases hs : Space.get h r with
    | none => rw [hs] at hr; cases hr
    | some a =>
      rw [hs] at hr
      by_cases hk : off < a.size
      · simp [hk] at hr; exact hr.2.symm
      · simp [hk] at hr

theorem pureH_ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (i : Int) : PureH (Ptr.index (T := T) p i) :=
  pureH_bind (pureH_ptr_add p i) (fun _ => pureH_ptr_load _)

theorem pureH_addrOf (p : BPtr) : PureH (Zlib.Crc32.addrOf p) := by
  intro h v h' hr; cases hr; rfl

theorem pureH_crcTab (i : UInt64) : PureH (Zlib.Crc32.crcTab i) :=
  pureH_ptr_index _ _

theorem pureH_idx1 {α : Type} (t : Array α) (i : Nat) : PureH (Zlib.Crc32.idx1 t i) := by
  intro h v h' hr
  unfold Zlib.Crc32.idx1 at hr
  cases hx : t[i]? with
  | none => simp [hx, C.ub] at hr
  | some _ => simp [hx] at hr; exact hr.2.symm

theorem pureH_idx2 {α : Type} (t : Array (Array α)) (k i : Nat) : PureH (Zlib.Crc32.idx2 t k i) := by
  intro h v h' hr
  unfold Zlib.Crc32.idx2 at hr
  cases hk : t[k]? with
  | none => simp [hk, C.ub] at hr
  | some r => cases hi : r[i]? with
    | none => simp [hk, hi, C.ub] at hr
    | some _ => simp [hk, hi] at hr; exact hr.2.symm

theorem pureH_loadWord (p : BPtr) : PureH (Zlib.Crc32.loadWord p) := by
  unfold Zlib.Crc32.loadWord
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  refine pureH_bind (pureH_list_forIn _ _ (fun _ _ _ => ?_) _) (fun _ => pureH_pure _)
  exact pureH_bind (pureH_ptr_index _ _) (fun _ => pureH_pure _)

theorem pureH_wordAt (words : BPtr) (i : Nat) : PureH (Zlib.Crc32.wordAt words i) := by
  unfold Zlib.Crc32.wordAt
  exact pureH_bind (pureH_ptr_add _ _) (fun _ => pureH_loadWord _)

theorem pureH_crcWord (t : Array (Array UInt32)) (w : UInt32) : PureH (Zlib.Crc32.crcWord t w) := by
  unfold Zlib.Crc32.crcWord
  exact pureH_bind (pureH_idx2 _ _ _) (fun _ =>
    pureH_bind (pureH_idx2 _ _ _) (fun _ =>
    pureH_bind (pureH_idx2 _ _ _) (fun _ =>
    pureH_bind (pureH_idx2 _ _ _) (fun _ => pureH_pure _))))

theorem pureH_crc_word (data : UInt32) : PureH (Zlib.Crc32.crc_word data) := by
  unfold Zlib.Crc32.crc_word
  refine pureH_bind (pureH_cwhile (fun _ => pureH_pure _) (fun _ => ?_) _) (fun _ => pureH_pure _)
  exact pureH_bind (pureH_crcTab _) (fun _ => pureH_pure _)

theorem pureH_crc_word_big (data : UInt32) : PureH (Zlib.Crc32.crc_word_big data) := by
  unfold Zlib.Crc32.crc_word_big
  refine pureH_bind (pureH_cwhile (fun _ => pureH_pure _) (fun _ => ?_) _) (fun _ => pureH_pure _)
  exact pureH_bind (pureH_idx1 _ _) (fun _ => pureH_pure _)

theorem pureH_blockLittle2 (s : BL2) : PureH (Zlib.Crc32.blockLittle2 s) := by
  unfold Zlib.Crc32.blockLittle2
  exact pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_ptr_add _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ => pureH_pure _)))))

theorem pureH_blockBig2 (s : BB2) : PureH (Zlib.Crc32.blockBig2 s) := by
  unfold Zlib.Crc32.blockBig2
  exact pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_ptr_add _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ => pureH_pure _)))))

theorem pureH_blockLittle (s : BL) : PureH (Zlib.Crc32.blockLittle s) := by
  unfold Zlib.Crc32.blockLittle
  exact pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_ptr_add _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ => pureH_pure _)))))))))))

theorem pureH_blockBig (s : BB) : PureH (Zlib.Crc32.blockBig s) := by
  unfold Zlib.Crc32.blockBig
  exact pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_wordAt _ _) (fun _ =>
    pureH_bind (pureH_ptr_add _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ =>
    pureH_bind (pureH_crcWord _ _) (fun _ => pureH_pure _)))))))))))

theorem pureH_crcByte (crc : UInt64) (buf : BPtr) : PureH (Zlib.Crc32.crcByte crc buf) := by
  unfold Zlib.Crc32.crcByte
  exact pureH_bind (pureH_ptr_load _) (fun _ =>
    pureH_bind (pureH_ptr_add _ _) (fun _ =>
    pureH_bind (pureH_crcTab _) (fun _ => pureH_pure _)))

theorem pureH_crc8_step (c : UInt64) (b : BPtr) (l : UInt64) : PureH (do
    let l := l - 8
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    let (c, b) ← Zlib.Crc32.crcByte c b
    pure (c, b, l)) :=
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ =>
  pureH_bind (pureH_crcByte _ _) fun _ => pureH_pure _

theorem pureH_crc32_braid (crc : UInt64) (buf : BPtr) (len : UInt64) : PureH (Zlib.Crc32.crc32_braid crc buf len) := by
  unfold Zlib.Crc32.crc32_braid
  repeat' first
    | with_reducible exact pureH_pure _
    | with_reducible exact pureH_ub _
    | with_reducible exact pureH_crc8_step _ _ _
    | with_reducible exact pureH_crcByte _ _
    | with_reducible exact pureH_addrOf _
    | with_reducible exact pureH_blockLittle2 _
    | with_reducible exact pureH_blockBig2 _
    | with_reducible exact pureH_wordAt _ _
    | with_reducible exact pureH_crc_word _
    | with_reducible exact pureH_crc_word_big _
    | with_reducible exact pureH_ptr_add _ _
    | with_reducible (refine pureH_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply pureH_ite
    | with_reducible (refine pureH_bind ?_ (fun _ => ?_))

/-- Every non-faulting execution of `crc32_z` leaves the heap unchanged. -/
theorem crc32_z_heap_unchanged (crc : UInt64) (buf : BPtr) (len : UInt64) : PureH (Zlib.Crc32.crc32_z crc buf len) := by
  unfold Zlib.Crc32.crc32_z
  by_cases h0 : buf == .null
  · simp [h0, pureH_pure]
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : len ≥ (Zlib.Crc32.NMIN * Zlib.Crc32.W + Zlib.Crc32.W - 1).toInt.toNat.toUInt64
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (len < Zlib.Crc32.BRAID_CUT.toInt.toNat.toUInt64 || len < (Zlib.Crc32.N * Zlib.Crc32.W + Zlib.Crc32.W - 1).toInt.toNat.toUInt64) = true
      · simp only [h2, ↓reduceIte]
        exact pureH_bind (pureH_crc32_braid _ _ _) (fun _ => pureH_pure _)
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        repeat' first
          | with_reducible exact pureH_pure _
          | with_reducible exact pureH_ub _
          | with_reducible exact pureH_crc32_braid _ _ _
          | with_reducible exact pureH_crc8_step _ _ _
          | with_reducible exact pureH_crcByte _ _
          | with_reducible exact pureH_addrOf _
          | with_reducible exact pureH_blockLittle _
          | with_reducible exact pureH_blockBig _
          | with_reducible exact pureH_wordAt _ _
          | with_reducible exact pureH_crc_word _
          | with_reducible exact pureH_crc_word_big _
          | with_reducible exact pureH_ptr_add _ _
          | with_reducible (refine pureH_cwhile (fun _ => ?_) (fun _ => ?_) _)
          | with_reducible apply pureH_ite
          | with_reducible (refine pureH_bind ?_ (fun _ => ?_))
    · simp only [h1, ↓reduceIte]
      repeat' first
        | with_reducible exact pureH_pure _
        | with_reducible exact pureH_crc8_step _ _ _
        | with_reducible exact pureH_crcByte _ _
        | with_reducible (refine pureH_cwhile (fun _ => ?_) (fun _ => ?_) _)
        | with_reducible (refine pureH_bind ?_ (fun _ => ?_))

/-- Every non-faulting execution of `crc32` leaves the heap unchanged. -/
theorem crc32_heap_unchanged (crc : UInt64) (buf : BPtr) (len : UInt32) : PureH (Zlib.Crc32.crc32 crc buf len) :=
  crc32_z_heap_unchanged crc buf len.toUInt64

/-! ### Statement helpers -/

theorem pw_foldl (m : Nat) (v : UInt32) : (List.range m).foldl (fun c _ => crcBit c) v = pw m v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih, pw_succ']; rfl

theorem e31_eq : (0x80000000 : UInt32) = e 31 := by decide

set_option maxRecDepth 100000 in
theorem mulp_one_basis : ∀ t : Fin 32, mulp (e t.val) (e 31) = e t.val := by decide +kernel

theorem mulp_one_right (a : UInt32) : mulp a (e 31) = a :=
  lin32_ext (f := fun a => mulp a (e 31)) (g := fun a => a)
    (by intro x y; exact mulp_xor_left x y _) (by intro x y; rfl) (fun t ht => mulp_one_basis ⟨t, ht⟩) a

theorem not32_toUInt64 (x : UInt32) : (~~~ x).toUInt64 = x.toUInt64 ^^^ 0xffffffff := by
  rw [not32_eq, UInt32.toUInt64_xor]; rfl

theorem u64_roundtrip (x : UInt64) (h : x.toNat < 2 ^ 32) : x.toUInt32.toUInt64 = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt h]

theorem crc32_append (A B : List UInt8) :
    ZlibF.Spec.crc32 (A ++ B) = pw (8 * B.length) (ZlibF.Spec.crc32 A) ^^^ ZlibF.Spec.crc32 B := by
  unfold ZlibF.Spec.crc32
  rw [← ZlibF.Spec.crc32Update_append, crc32Update_affine]
  rfl

/-! ## Theorems -/

/-- **crc32_z, `buf == NULL`.** For every heap and every `crc`, `len`: `crc32_z(crc, Z_NULL, len)` returns `0` (the
initial value of `zlib.h`) and does not touch the heap. -/
theorem crc32_z_null (h : Heap) (crc len : UInt64) :
    C.run (crc32_z crc .null len) h = .ok (0, h) := by
  unfold C.run crc32_z
  rw [ite_eq_left (by decide)]
  rfl

/-- **crc32_z, correctness over any byte view.** For every heap whose static tables are the ones of `crc32.h`
(`StaticsOK`), every `crc`, and every readable byte view slice (`Space.get h ref = some bs` and `off + len ≤ bs.size`):
`crc32_z` returns `ZlibF.Spec.crc32Update` of the byte list and leaves the heap unchanged. -/
theorem crc32_z_correct_view (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat)
    (bs : Array UInt8) (hb : Space.get h ref = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32_z crc (.ref ref off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) := by
  have := crc32_z_ok_view h hs crc ref off bs hb len hlen
  unfold OkOn at this
  unfold C.run
  rw [this, rbFrom_list bs len.toNat _ off hlen]
  have e1 : ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat) =
      ~~~ rbl (~~~ crc.toUInt32) ((bs.toList.drop off).take len.toNat) := rfl
  rw [e1, not32_toUInt64]

/-- **crc32_z, correctness.** Specialisation of `crc32_z_correct_view` to heap byte blocks. -/
theorem crc32_z_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32_z crc (.ref (.blk blk) off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) :=
  crc32_z_correct_view h hs crc (.blk blk) off bs hb len hlen

/-- **crc32, `buf == NULL`.** Returns `0` for every `crc` and `len`; heap unchanged. -/
theorem crc32_null (h : Heap) (crc : UInt64) (len : UInt32) :
    C.run (crc32 crc .null len) h = .ok (0, h) := crc32_z_null h crc len.toUInt64

/-- **crc32, correctness over any byte view.** As `crc32_z_correct_view` with `len : uInt` (32 bits). -/
theorem crc32_correct_view (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat)
    (bs : Array UInt8) (hb : Space.get h ref = some bs) (len : UInt32) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32 crc (.ref ref off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) := by
  have := crc32_z_correct_view h hs crc ref off bs hb len.toUInt64 (by rwa [UInt32.toNat_toUInt64])
  rw [UInt32.toNat_toUInt64] at this
  exact this

/-- **crc32, correctness.** As `crc32_z_correct` with `len : uInt` (32 bits). -/
theorem crc32_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (blk off : Nat) (bs : Array UInt8)
    (hb : h.bytes blk = some bs) (len : UInt32) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32 crc (.ref (.blk blk) off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) :=
  crc32_correct_view h hs crc (.blk blk) off bs hb len hlen

/-! ### `get_crc_table` -/

/-! ### `multmodp`, `x2nmodp` -/

/-! ### `crc32_combine` and friends -/

/-- **crc32_combine_gen64, correctness.** For `len2 >= 0`, the operator is `x^(8 * len2) mod p(x)`: the register
`0x80000000` advanced by `8 * len2` steps of `ZlibF.Spec.crcBit` (the effect of `len2` zero bytes on a CRC register). -/
theorem crc32_combine_gen64_correct (h : Heap) (hs : StaticsOK h) (len2 : Int64) (hpos : 0 ≤ len2.toInt) :
    C.run (crc32_combine_gen64 len2) h =
      .ok ((((List.range (8 * len2.toInt.toNat)).foldl (fun c _ => crcBit c) (0x80000000 : UInt32))).toUInt64, h) := by
  obtain ⟨op, hop, hlt, hnz, hv⟩ := gen64_op h hs len2 hpos
  rw [pw_foldl, e31_eq]
  have h1 : op.toUInt32 = pw (8 * len2.toInt.toNat) (e 31) := by
    have := hv (e 31)
    rwa [mulp_one_right] at this
  unfold OkOn at hop
  unfold C.run
  rw [hop, ← h1, u64_roundtrip op hlt]

/-- **crc32_combine_op, the candidate hang.** If `op != 0` and the low 32 bits of `op` are zero (for example
`op = 1UL << 32`), the translation of `crc32_combine_op` runs out of fuel (the C loop in `multmodp` does not end):
`multmodp` finds no set bit among bits 0..31 of `a`, so `(a & (m - 1)) == 0` is never reached. -/
theorem crc32_combine_op_diverges (h : Heap) (crc1 crc2 op : UInt64) (hop : op ≠ 0) (hlow : op.toUInt32 = 0) :
    C.run (crc32_combine_op crc1 crc2 op) h = .error .outOfFuel :=
  combine_op_diverges h crc1 crc2 op hop hlow

/-- **crc32_combine64, correctness.** For two byte sequences `A`, `B` with `len2 = B.length` and the CRC values
`crc1 = crc32 A`, `crc2 = crc32 B` (`ZlibF.Spec.crc32`), the result is `crc32 (A ++ B)`. -/
theorem crc32_combine64_correct (h : Heap) (hs : StaticsOK h) (A B : List UInt8) (len2 : Int64)
    (hlen : len2.toInt = B.length) :
    C.run (crc32_combine64 (ZlibF.Spec.crc32 A).toUInt64 (ZlibF.Spec.crc32 B).toUInt64 len2) h =
      .ok ((ZlibF.Spec.crc32 (A ++ B)).toUInt64, h) := by
  have := combine64_ok h hs (ZlibF.Spec.crc32 A).toUInt64 (ZlibF.Spec.crc32 B).toUInt64 len2
  unfold OkOn at this
  unfold C.run
  rw [this, ite_eq_right (by omega), u32_roundtrip, u32_roundtrip, hlen, Int.toNat_natCast, crc32_append]

/-! ### `crc_word` and the helpers -/

theorem crc_big_table_size : Crc32H.crc_big_table.size = 256 := by decide +kernel

theorem idx1_ok {α : Type} [Inhabited α] (h : Heap) (t : Array α) (i : Nat) (hi : i < t.size) :
    OkOn h (idx1 t i) t[i]! := by
  unfold idx1
  have : t[i]? = some t[i]! := by rw [getElem!_pos t i hi]; simp [hi]
  rw [this]
  exact OkOn.pure _ _

/-- **crc_word_big, safety.** The big-endian word step (dead on the little-endian target, translated for
completeness) does not fault for any `data`; heap unchanged. Its correctness is not proved. -/
theorem crc_word_big_safe (h : Heap) (data : UInt32) :
    ∃ r, C.run (crc_word_big data) h = .ok (r, h) := by
  have key : ∃ y, OkOn h (crc_word_big data) y ∧ True := by
    unfold crc_word_big
    refine OkOn.bind_ex (R := fun _ : UInt32 × Int32 => True) ?_ (fun x _ => ⟨x.1, OkOn.pure _ _, trivial⟩)
    refine cwhile_ok (fun cnt s => ∃ i, i + cnt = 4 ∧ s.2 = Int32.ofNat i) (fun _ => True) ?_ ?_ (k := 4)
      (s := (data, (0 : Int32))) ⟨0, rfl, rfl⟩ (by show 4 < 2 ^ 64; omega)
    · intro cnt s hP
      obtain ⟨d, k⟩ := s
      obtain ⟨i, hi, hk⟩ := hP
      simp only at hk
      subst hk
      have hc : (Int32.ofNat i < (4 : Int32)) = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide
      have hk : Int32.ofNat i + 1 = Int32.ofNat (i + 1) := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> decide
      have ht := idx1_ok h Crc32H.crc_big_table ((d >>> 24) &&& 0xff).toNat (by
        rw [crc_big_table_size]; exact and255_lt32 _)
      refine ⟨(d, Int32.ofNat i), ((d <<< 8) ^^^ Crc32H.crc_big_table[((d >>> 24) &&& 0xff).toNat]!, Int32.ofNat (i + 1)),
        ?_, ?_, ⟨i + 1, by omega, rfl⟩⟩
      · show OkOn h (pure _) _
        simp only [W, hc]
        exact OkOn.pure _ _
      · show OkOn h (do let t ← idx1 Crc32H.crc_big_table (((d >>> 24) &&& 0xff).toNat); pure ((d <<< 8) ^^^ t, Int32.ofNat i + 1)) _
        rw [hk]
        exact OkOn.bind ht (OkOn.pure _ _)
    · intro s hP
      obtain ⟨d, k⟩ := s
      obtain ⟨i, hi, hk⟩ := hP
      simp only at hk
      subst hk
      have : i = 4 := by omega
      subst this
      have hc : (Int32.ofNat 4 < (4 : Int32)) = false := by decide
      refine ⟨(d, Int32.ofNat 4), ?_, trivial⟩
      show OkOn h (pure _) _
      simp only [W, hc]
      exact OkOn.pure _ _
  obtain ⟨y, hy, _⟩ := key
  unfold OkOn at hy
  refine ⟨y, ?_⟩
  unfold C.run
  exact hy

/-! ### Non-vacuity: concrete heaps built by `allocBytes`

The heap `h0` has the static tables `crc32.c` fixes (`initStatics`); `allocBytes` (the runtime function) puts a buffer in
a fresh block; the hypotheses of the theorems hold there and the translated functions run on it. -/

/-- the empty heap with the static tables of `crc32.h` -/
def h0 : Heap := { Heap.empty with static := Zlib.Crc32.initStatics Heap.empty.static }

/-- 100 bytes, enough for `crc32_braid` (`11 <= len < 320`) at an unaligned offset -/
def buf100 : Array UInt8 := (Array.range 100).map (fun i => UInt8.ofNat (i * 7 + 3))

/-- 340 bytes, enough for the 5-braid loop (`len >= 320`) at an unaligned offset -/
def buf340 : Array UInt8 := (Array.range 340).map (fun i => UInt8.ofNat (i * 7 + 3))

example : StaticsOK h0 := ⟨rfl, rfl⟩

/-- `allocBytes` gives a pointer into block 0, in a heap where the hypotheses hold. -/
example : ∃ p h1, C.allocBytes buf100 h0 = .ok (p, h1) ∧ p = .ref (.blk 0) 0 ∧ StaticsOK h1 ∧
    h1.bytes 0 = some buf100 ∧ 3 + (90 : UInt64).toNat ≤ buf100.size :=
  ⟨_, _, rfl, rfl, ⟨rfl, rfl⟩, rfl, by decide +kernel⟩

/-- `crc32_z_correct` on a concrete heap: 90 bytes (`crc32_braid`, 2-braid) from unaligned offset 3. -/
example : ∃ p h1, C.allocBytes buf100 h0 = .ok (p, h1) ∧
    C.run (crc32_z 0 (.ref (.blk 0) 3) 90) h1 =
      .ok ((ZlibF.Spec.crc32Update 0 ((buf100.toList.drop 3).take 90)).toUInt64, h1) :=
  ⟨_, _, rfl, crc32_z_correct _ ⟨rfl, rfl⟩ 0 0 3 buf100 rfl 90 (by decide +kernel)⟩

/-- `crc32_z_correct` on a concrete heap: 330 bytes (`N = 5` braid) from unaligned offset 3. -/
example : ∃ p h1, C.allocBytes buf340 h0 = .ok (p, h1) ∧
    C.run (crc32_z 0 (.ref (.blk 0) 3) 330) h1 =
      .ok ((ZlibF.Spec.crc32Update 0 ((buf340.toList.drop 3).take 330)).toUInt64, h1) :=
  ⟨_, _, rfl, crc32_z_correct _ ⟨rfl, rfl⟩ 0 0 3 buf340 rfl 330 (by decide +kernel)⟩

/-- the heap after `allocBytes arr` on `h0` -/
def heapOf (arr : Array UInt8) : Heap := match C.allocBytes arr h0 with | .ok (_, h1) => h1 | .error _ => h0

/-- the value of a run, `0` on a fault -/
def valOf (r : Except Fault (UInt64 × Heap)) : UInt64 := match r with | .ok (v, _) => v | .error _ => 0

/-- the value computed by running the translation on the 90 bytes from offset 3 equals the specification -/
example : valOf (C.run (crc32_z 0 (.ref (.blk 0) 3) 90) (heapOf buf100)) =
    (ZlibF.Spec.crc32Update 0 ((buf100.toList.drop 3).take 90)).toUInt64 := by decide +kernel

/-- `crc32("123456789") = 0xCBF43926`, by running the translation on a block made by `allocBytes` -/
example : valOf (C.run (crc32_z 0 (.ref (.blk 0) 0) 9) (heapOf "123456789".toUTF8.data)) = 0xCBF43926 := by
  decide +kernel

/-- the same through the theorem: hypotheses hold, the result is the specification's -/
example : ∃ p h1, C.allocBytes "123456789".toUTF8.data h0 = .ok (p, h1) ∧
    C.run (crc32_z 0 p 9) h1 =
      .ok ((ZlibF.Spec.crc32Update 0 (("123456789".toUTF8.data.toList.drop 0).take 9)).toUInt64, h1) :=
  ⟨_, _, rfl, crc32_z_correct _ ⟨rfl, rfl⟩ 0 0 0 _ rfl 9 (by decide +kernel)⟩

/-- the combine functions on a concrete instance -/
example : ∃ h1, StaticsOK h1 ∧
    C.run (crc32_combine64 (ZlibF.Spec.crc32 [1, 2, 3]).toUInt64 (ZlibF.Spec.crc32 [4, 5, 6, 7]).toUInt64 4) h1 =
      .ok ((ZlibF.Spec.crc32 [1, 2, 3, 4, 5, 6, 7]).toUInt64, h1) :=
  ⟨h0, ⟨rfl, rfl⟩, crc32_combine64_correct h0 ⟨rfl, rfl⟩ [1, 2, 3] [4, 5, 6, 7] 4 (by decide)⟩

/-- the hang, on the translation -/
example : C.run (crc32_combine_op 1 2 ((1 : UInt64) <<< 32)) h0 = .error .outOfFuel :=
  crc32_combine_op_diverges h0 1 2 _ (by decide) (by decide)

end Zlib.Crc32.Proofs
