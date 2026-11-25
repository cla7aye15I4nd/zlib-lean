/-!
# Pure Deflate Huffman Tree & Coding Mathematics (`Zlib.Proof.Math.Trees`)

Heap-free mathematical library for `Zlib/Trees.lean`. Covers:
- Deflate tree constants (`LENGTH_CODES = 29`, `LITERALS = 256`, `L_CODES = 286`,
  `D_CODES = 30`, `BL_CODES = 19`, `HEAP_SIZE = 573`, `MAX_BITS = 15`,
  `MAX_BL_BITS = 7`, `SMALLEST = 1`, `END_BLOCK = 256`)
- `bi_reverse` bit-reversal & 32-bit / 16-bit bounds (`revBits`, `revBits_lt`,
  `revBits_testBit`, `bi_reverse_loop_spec`)
- `gen_codes` canonical next-code recurrence & `UInt16` fit bounds (`nextCode`,
  `countBefore`, `canonicalCode`, `storedCode`, `nextCode_le_two_pow`, `storedCode_lt`)
- `pqdownheap` heap-index bounds, preorder (`smallerNat`, `KeyOK`), `HeapOK`,
  `PermOn`, `HoleInv`, `MinChild`, and root-minimum property
- Merge-loop node & `Dad` index bounds (`node ∈ [elems, 2 * elems - 1)`,
  heap/tail separation `heap_len < heap_max`), plus Fibonacci ancestor depth
  bound (`fibChain_bound`: `depth ≤ 22 < 256`)
- `gen_bitlen` finite-sum algebra (`rs`), tree layout (`PShape`, `Clamped`),
  clamped Kraft identity (`kraft_clamped`, `blC_top`, `exactC_pos`), overflow
  repair loop termination & Kraft invariance (`deepest`, `repairStep`,
  `repairIter`, `round_kraft`, `exists_short`, `repairIter_spec`), and pass-3
  `--h` index bounds.
-/

namespace Zlib.Proof.Math.Trees

/-! ## 1. Constants (`Zlib/Headers/Common.lean`, `Zlib/Trees.lean`) -/

def LENGTH_CODES : Nat := 29
def LITERALS : Nat := 256
def L_CODES : Nat := LITERALS + 1 + LENGTH_CODES
def D_CODES : Nat := 30
def BL_CODES : Nat := 19
def HEAP_SIZE : Nat := 2 * L_CODES + 1
def MAX_BITS : Nat := 15
def MAX_BL_BITS : Nat := 7
def SMALLEST : Nat := 1
def END_BLOCK : Nat := 256
def REP_3_6 : Nat := 16
def REPZ_3_10 : Nat := 17
def REPZ_11_138 : Nat := 18
def D_TREE_SIZE : Nat := 2 * D_CODES + 1
def BL_TREE_SIZE : Nat := 2 * BL_CODES + 1

theorem l_codes_eq : L_CODES = 286 := rfl
theorem d_codes_eq : D_CODES = 30 := rfl
theorem bl_codes_eq : BL_CODES = 19 := rfl
theorem heap_size_eq : HEAP_SIZE = 573 := rfl
theorem max_bits_eq : MAX_BITS = 15 := rfl
theorem max_bl_bits_eq : MAX_BL_BITS = 7 := rfl
theorem d_tree_size_eq : D_TREE_SIZE = 61 := rfl
theorem bl_tree_size_eq : BL_TREE_SIZE = 39 := rfl

theorem tree_capacity_bounds {elems : Nat} (he : elems ≤ L_CODES) :
    2 * elems - 1 < 2 * elems + 1 ∧ 2 * elems + 1 ≤ HEAP_SIZE := by
  have hL : L_CODES = 286 := rfl
  have hH : HEAP_SIZE = 573 := rfl
  omega

theorem bl_count_bound {b : Nat} (hb : b ≤ MAX_BITS) : b < MAX_BITS + 1 := by
  omega

/-! ## 2. `bi_reverse` Bit-Reversal & Bounds -/

/-- Reverse the low `k` bits of `c`: bit `i` of `c` becomes bit `k - 1 - i`. -/
def revBits (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * revBits c k + (c / 2 ^ k) % 2

theorem revBits_lt (c k : Nat) : revBits c k < 2 ^ k := by
  induction k with
  | zero => simp [revBits]
  | succ k ih =>
    simp only [revBits, Nat.pow_succ]
    have : (c / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
    omega

theorem revBits_mod (c k : Nat) : revBits (c % 2 ^ k) k = revBits c k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [revBits]
    have h1 : c % 2 ^ (k + 1) % 2 ^ k = c % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul_right_mod]
    have h2 : c % 2 ^ (k + 1) / 2 ^ k % 2 = c / 2 ^ k % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [← ih (c % 2 ^ (k + 1)), h1, ih, h2]

theorem revBits_mod_of_le (c k m : Nat) (hk : k ≤ m) :
    revBits (c % 2 ^ m) k = revBits c k := by
  rw [← revBits_mod (c % 2 ^ m) k, ← revBits_mod c k]
  congr 1
  obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
  rw [Nat.pow_add, Nat.mod_mul_right_mod]

theorem revBits_testBit (c k i : Nat) (hi : i < k) :
    (revBits c k).testBit i = c.testBit (k - 1 - i) := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    have hb : c / 2 ^ k % 2 < 2 ^ 1 := by change c / 2 ^ k % 2 < 2; omega
    have hbit := Nat.testBit_two_pow_mul_add (revBits c k) hb i
    change (2 * revBits c k + c / 2 ^ k % 2).testBit i = _ at hbit
    rw [revBits, hbit]
    by_cases hi0 : i = 0
    · subst i
      rw [ite_eq_left (by omega), show k + 1 - 1 - 0 = k by omega]
      simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, Nat.mod_mod]
    · rw [ite_eq_right (by omega), ih (i - 1) (by omega)]
      congr 1
      omega

/-- Pure model of the `bi_reverse` loop body: `steps` remaining iterations on `(code, res)`. -/
def biReverseLoop (steps : Nat) (code res : Nat) : Nat :=
  match steps with
  | 0 => res / 2
  | s + 1 => biReverseLoop s (code / 2) (2 * (res + code % 2))

theorem biReverseLoop_eq (c : Nat) :
    ∀ k j res, res = 2 * revBits c j →
      biReverseLoop k (c / 2 ^ j) res = revBits c (j + k)
  | 0, j, res, hres => by
    simp [biReverseLoop, hres]
  | k + 1, j, res, hres => by
    simp only [biReverseLoop]
    have hdiv : c / 2 ^ j / 2 = c / 2 ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hres' : 2 * (res + c / 2 ^ j % 2) = 2 * revBits c (j + 1) := by
      rw [hres, revBits]
    rw [hdiv, hres', biReverseLoop_eq c k (j + 1) _ rfl, show j + 1 + k = j + (k + 1) by omega]

theorem biReverseLoop_spec {c len : Nat} (_hlen1 : 1 ≤ len) (hlen31 : len ≤ 31) :
    biReverseLoop len c 0 = revBits c len ∧
    revBits c len < 2 ^ len ∧
    2 * revBits c len < 2 ^ 32 := by
  have heq := biReverseLoop_eq c len 0 0 (by simp [revBits])
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add] at heq
  have hlt := revBits_lt c len
  have hpow : 2 ^ len ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) hlen31
  have h31 : 2 * 2 ^ 31 = 2 ^ 32 := by decide
  exact ⟨heq, hlt, by omega⟩

theorem biReverse_u16_fit {c len : Nat} (hlen : len ≤ MAX_BITS) :
    revBits c len < 2 ^ MAX_BITS ∧ 2 ^ MAX_BITS < 2 ^ 16 := by
  have hlt := revBits_lt c len
  have hpow : 2 ^ len ≤ 2 ^ MAX_BITS := Nat.pow_le_pow_right (by omega) hlen
  have h15 : 2 ^ MAX_BITS < 2 ^ 16 := by decide
  exact ⟨Nat.lt_of_lt_of_le hlt hpow, h15⟩

/-! ## 3. `gen_codes` Canonical Code Generation & Bounds -/

/-- First canonical code of length `b`. -/
def nextCode (bl : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => (nextCode bl b + bl b) * 2

/-- Number of earlier symbols `< n` with length `l`. -/
def countBefore (len : Nat → Nat) (l n : Nat) : Nat :=
  ((List.range n).filter (fun m => len m = l)).length

theorem countBefore_succ (len : Nat → Nat) (l n : Nat) :
    countBefore len l (n + 1) = countBefore len l n + (if len n = l then 1 else 0) := by
  unfold countBefore
  rw [List.range_succ, List.filter_append]
  by_cases h : len n = l <;> simp [h]

@[simp] theorem countBefore_zero (len : Nat → Nat) (l : Nat) : countBefore len l 0 = 0 := rfl

theorem countBefore_lt (len : Nat → Nat) (n l : Nat) (hl : len n = l) :
    countBefore len l n < countBefore len l (n + 1) := by
  rw [countBefore_succ, ite_eq_left hl]
  omega

theorem countBefore_mono (len : Nat → Nat) (l : Nat) :
    ∀ {a b : Nat}, a ≤ b → countBefore len l a ≤ countBefore len l b := by
  intro a b h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    rw [← Nat.add_assoc, countBefore_succ]
    have := ih (by omega)
    split <;> omega

/-- Canonical code assigned to symbol `n` before bit reversal. -/
def canonicalCode (bl len : Nat → Nat) (n : Nat) : Nat :=
  nextCode bl (len n) + countBefore len (len n) n

/-- Stored reversed code for symbol `n` (`tree[n].Code`). -/
def storedCode (bl len : Nat → Nat) (n : Nat) : Nat :=
  revBits (canonicalCode bl len n) (len n)

theorem storedCode_lt (bl len : Nat → Nat) (n : Nat) : storedCode bl len n < 2 ^ len n :=
  revBits_lt _ _

/-! ## 4. Finite Sums (`rs`), Counting, & Kraft Inequality Algebra -/

/-- `rs F n = F 0 + … + F (n - 1)`. -/
def rs (F : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rs F n + F n

@[simp] theorem rs_zero (F : Nat → Nat) : rs F 0 = 0 := rfl
theorem rs_succ (F : Nat → Nat) (n : Nat) : rs F (n + 1) = rs F n + F n := rfl

theorem rs_congr {F G : Nat → Nat} {n : Nat} (h : ∀ i < n, F i = G i) : rs F n = rs G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs_succ, rs_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem rs_add (F G : Nat → Nat) (n : Nat) : rs (fun i => F i + G i) n = rs F n + rs G n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs_succ, rs_succ, rs_succ, ih]; omega

theorem rs_mul (c : Nat) (F : Nat → Nat) (n : Nat) : rs (fun i => c * F i) n = c * rs F n := by
  induction n with
  | zero => simp
  | succ n ih => rw [rs_succ, rs_succ, ih, Nat.mul_add]

theorem rs_le {F G : Nat → Nat} {n : Nat} (h : ∀ i < n, F i ≤ G i) : rs F n ≤ rs G n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rs_succ, rs_succ]
    have := ih (fun i hi => h i (by omega))
    have := h n (by omega)
    omega

theorem rs_eq_zero {F : Nat → Nat} {n : Nat} (h : ∀ i < n, F i = 0) : rs F n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rs_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem le_rs {F : Nat → Nat} {n i : Nat} (hi : i < n) : F i ≤ rs F n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [rs_succ]
    by_cases e : i = n
    · subst e; omega
    · have := ih (by omega); omega

theorem rs_const (c n : Nat) : rs (fun _ => c) n = c * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [rs_succ, ih, Nat.mul_succ]

theorem rs_split (F : Nat → Nat) (a b : Nat) :
    rs F (a + b) = rs F a + rs (fun i => F (a + i)) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, rs_succ, rs_succ, ih, Nat.add_assoc]

theorem rs_single (G : Nat → Nat) (k n : Nat) :
    rs (fun i => if i = k then G i else 0) n = if k < n then G k else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rs_succ, ih]
    by_cases e : n = k
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases h1 : k < n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]; rfl
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem rs_single' (G : Nat → Nat) (k n : Nat) (hk : k < n) :
    rs (fun i => if k = i then G i else 0) n = G k := by
  rw [rs_congr (G := fun i => if i = k then G i else 0) (fun i _ => by
    by_cases e : i = k
    · subst e; simp
    · rw [ite_eq_right (Ne.symm e), ite_eq_right e])]
  rw [rs_single, ite_eq_left hk]

theorem rs_swap (F : Nat → Nat → Nat) (m n : Nat) :
    rs (fun b => rs (fun p => F b p) m) n = rs (fun p => rs (fun b => F b p) n) m := by
  induction n with
  | zero => simp only [rs_zero]; exact (rs_eq_zero (fun _ _ => rfl)).symm
  | succ n ih =>
    rw [rs_succ, ih]
    rw [show (fun p => rs (fun b => F b p) (n + 1)) = (fun p => rs (fun b => F b p) n + F n p) from rfl]
    rw [rs_add]

theorem rs_all_one {F : Nat → Nat} {n : Nat} (hle : ∀ i < n, F i ≤ 1) (hs : rs F n = n) :
    ∀ i < n, F i = 1 := by
  induction n with
  | zero => intro _ hi; omega
  | succ n ih =>
    rw [rs_succ] at hs
    have h1 := hle n (by omega)
    have h2 : rs F n ≤ n := by
      have := rs_le (n := n) (G := fun _ => 1) (fun i hi => hle i (by omega))
      rw [rs_const] at this
      omega
    intro i hi
    by_cases e : i = n
    · subst e; omega
    · exact ih (fun j hj => hle j (by omega)) (by omega) i (by omega)

/-- Indicator `0` or `1`. -/
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

theorem ind_mul (p : Prop) [Decidable p] (x : Nat) : ind p * x = if p then x else 0 := by
  unfold ind; split <;> simp

theorem rs_ind_eq (k n : Nat) (hk : k < n) : rs (fun x => ind (x = k)) n = 1 := by
  rw [rs_congr (F := fun x => ind (x = k)) (G := fun x => if x = k then 1 else 0) (fun _ _ => rfl),
    rs_single, ite_eq_left hk]

/-- Number of `i < m` with `P i = v`. -/
def cnt (P : Nat → Nat) (m v : Nat) : Nat := rs (fun i => if P i = v then 1 else 0) m

theorem rs_image (P F : Nat → Nat) (m N : Nat) (hP : ∀ i < m, P i < N) :
    rs (fun i => F (P i)) m = rs (fun v => cnt P m v * F v) N := by
  induction m with
  | zero =>
    simp only [rs_zero]
    exact (rs_eq_zero (fun v _ => by simp [cnt])).symm
  | succ m ih =>
    rw [rs_succ, ih (fun i hi => hP i (by omega))]
    have e : (fun v => cnt P (m + 1) v * F v) =
        (fun v => cnt P m v * F v + (if v = P m then F v else 0)) := by
      funext v; simp only [cnt, rs_succ]
      by_cases e : P m = v
      · subst e; simp [Nat.add_mul]
      · rw [ite_eq_right e, ite_eq_right (Ne.symm e)]; simp
    rw [e, rs_add, rs_single, ite_eq_left (hP m (by omega))]

theorem cnt_le_one (P : Nat → Nat) (m v : Nat)
    (hinj : ∀ i j, i < m → j < m → P i = P j → i = j) : cnt P m v ≤ 1 := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    simp only [cnt, rs_succ] at *
    have ih' := ih (fun i j hi hj e => hinj i j (by omega) (by omega) e)
    by_cases e : P m = v
    · rw [ite_eq_left e]
      have : rs (fun i => if P i = v then 1 else 0) m = 0 := rs_eq_zero (fun i hi => by
        rw [ite_eq_right]; intro e'; have := hinj i m (by omega) (by omega) (e'.trans e.symm); omega)
      omega
    · rw [ite_eq_right e]; omega

theorem cnt_pos {P : Nat → Nat} {m v i : Nat} (hi : i < m) (e : P i = v) : 1 ≤ cnt P m v := by
  have := le_rs (F := fun i => if P i = v then 1 else 0) hi
  simp only [e, ite_true] at this; exact this

theorem cnt_zero {P : Nat → Nat} {m v : Nat} (h : ∀ i < m, P i ≠ v) : cnt P m v = 0 :=
  rs_eq_zero (fun i hi => by rw [ite_eq_right (h i hi)])

theorem cnt_exists {P : Nat → Nat} {m v : Nat} (h : 1 ≤ cnt P m v) : ∃ i < m, P i = v := by
  by_cases hx : ∃ i < m, P i = v
  · exact hx
  · have := cnt_zero (P := P) (m := m) (v := v) (fun i hi e => hx ⟨i, hi, e⟩); omega

theorem inj_surj (P : Nat → Nat) (n : Nat) (hP : ∀ i < n, P i < n)
    (hinj : ∀ i j, i < n → j < n → P i = P j → i = j) : ∀ v < n, ∃ i < n, P i = v := by
  have h1 := rs_image P (fun _ => 1) n n hP
  rw [rs_const] at h1
  have := rs_all_one (F := fun v => cnt P n v) (n := n) (fun v _ => cnt_le_one P n v hinj)
    (by rw [← rs_congr (F := fun v => cnt P n v * 1) (fun v _ => by simp)]; omega)
  intro v hv
  exact cnt_exists (by rw [this v hv]; exact Nat.le_refl 1)

theorem rs_perm (σ F : Nat → Nat) (n : Nat) (hσ : ∀ i < n, σ i < n)
    (hinj : ∀ i j, i < n → j < n → σ i = σ j → i = j) : rs (fun i => F (σ i)) n = rs F n := by
  rw [rs_image σ F n n hσ]
  apply rs_congr
  intro v hv
  obtain ⟨i, hi, e⟩ := inj_surj σ n hσ hinj v hv
  have h1 := cnt_pos (P := σ) hi e
  have h2 := cnt_le_one σ n v hinj
  rw [show cnt σ n v = 1 by omega, Nat.one_mul]

theorem rs_regroup (Q : Nat → Prop) [DecidablePred Q] (f W : Nat → Nat) (m B : Nat)
    (hf : ∀ i < m, Q i → f i < B) :
    rs (fun i => if Q i then W (f i) else 0) m =
      rs (fun b => rs (fun i => if Q i ∧ f i = b then 1 else 0) m * W b) B := by
  have e1 : (fun b => rs (fun i => if Q i ∧ f i = b then 1 else 0) m * W b) =
      (fun b => rs (fun i => if Q i ∧ f i = b then W b else 0) m) := by
    funext b
    rw [Nat.mul_comm, ← rs_mul]
    apply rs_congr; intro i _; split <;> simp
  rw [e1, rs_swap]
  apply rs_congr
  intro i hi
  by_cases hq : Q i
  · rw [ite_eq_left hq]
    rw [rs_congr (G := fun b => if f i = b then W b else 0) (fun b _ => by
      by_cases e : f i = b
      · rw [ite_eq_left ⟨hq, e⟩, ite_eq_left e]
      · rw [ite_eq_right (fun h => e h.2), ite_eq_right e])]
    rw [rs_single' W (f i) B (hf i hi hq)]
  · rw [ite_eq_right hq]
    exact (rs_eq_zero (fun b _ => by rw [ite_eq_right (fun h => hq h.1)])).symm

theorem rs_pair (F : Nat → Nat) (J : Nat) :
    rs (fun i => F ((2 * J - 1 - i) / 2)) (2 * J) = 2 * rs F J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [show 2 * (J + 1) = 2 + 2 * J by omega, rs_split]
    rw [rs_congr (F := fun i => F ((2 + 2 * J - 1 - (2 + i)) / 2))
      (G := fun i => F ((2 * J - 1 - i) / 2)) (fun i _ => by congr 1; omega)]
    rw [ih, rs_succ]
    simp only [rs_succ, rs_zero]
    rw [show (2 + 2 * J - 1 - 0) / 2 = J by omega, show (2 + 2 * J - 1 - 1) / 2 = J by omega]
    omega

/-- Kraft sum of the counts `c b` (`b = 0 .. L`), scaled by `2^L`. -/
def kc (c : Nat → Nat) (L : Nat) : Nat := rs (fun b => c b * 2 ^ (L - b)) (L + 1)

/-- In `gen_codes`, whenever `bl 0 = 0` and `kc bl L ≤ 2^L`, every `nextCode bl b + bl b ≤ 2^b`.
Hence `next_code[len]++` never exceeds `2^len - 1 < 2^15 < 2^16`. -/
theorem nextCode_tail_sum (bl : Nat → Nat) (L : Nat) (h0 : bl 0 = 0) :
    ∀ b ≤ L, nextCode bl b * 2 ^ (L - b) +
      rs (fun j => bl (b + j) * 2 ^ (L - (b + j))) (L + 1 - b) = kc bl L
  | 0, _ => by
    simp only [nextCode, Nat.zero_mul, Nat.zero_add, Nat.sub_zero, kc]
  | b + 1, hb => by
    have ih := nextCode_tail_sum bl L h0 b (by omega)
    have hsplit : rs (fun j => bl (b + j) * 2 ^ (L - (b + j))) (L + 1 - b) =
        bl b * 2 ^ (L - b) + rs (fun j => bl (b + 1 + j) * 2 ^ (L - (b + 1 + j))) (L + 1 - (b + 1)) := by
      have hlen : L + 1 - b = 1 + (L + 1 - (b + 1)) := by omega
      rw [hlen, rs_split, rs_succ, rs_zero, Nat.zero_add, Nat.add_zero]
      congr 1
      apply rs_congr
      intro j _
      have heq : b + (1 + j) = b + 1 + j := by omega
      rw [heq]
    have hpow : 2 ^ (L - b) = 2 * 2 ^ (L - (b + 1)) := by
      rw [show L - b = (L - (b + 1)) + 1 by omega, Nat.pow_succ]; omega
    have hnc : nextCode bl (b + 1) * 2 ^ (L - (b + 1)) =
        nextCode bl b * 2 ^ (L - b) + bl b * 2 ^ (L - b) := by
      calc nextCode bl (b + 1) * 2 ^ (L - (b + 1))
          = (nextCode bl b + bl b) * 2 * 2 ^ (L - (b + 1)) := rfl
        _ = (nextCode bl b + bl b) * (2 * 2 ^ (L - (b + 1))) := Nat.mul_assoc _ _ _
        _ = (nextCode bl b + bl b) * 2 ^ (L - b) := by rw [← hpow]
        _ = nextCode bl b * 2 ^ (L - b) + bl b * 2 ^ (L - b) := Nat.add_mul _ _ _
    rw [hsplit] at ih
    omega

theorem nextCode_le_two_pow (bl : Nat → Nat) (L : Nat) (h0 : bl 0 = 0)
    (hk : kc bl L ≤ 2 ^ L) : ∀ b ≤ L, nextCode bl b + bl b ≤ 2 ^ b := by
  intro b hb
  have hsum := nextCode_tail_sum bl L h0 b hb
  have hfirst : bl b * 2 ^ (L - b) ≤ rs (fun j => bl (b + j) * 2 ^ (L - (b + j))) (L + 1 - b) := by
    have := le_rs (F := fun j => bl (b + j) * 2 ^ (L - (b + j))) (n := L + 1 - b) (i := 0) (by omega)
    simpa only [Nat.add_zero] using this
  have hmul : (nextCode bl b + bl b) * 2 ^ (L - b) ≤ 2 ^ L := by
    rw [Nat.add_mul]
    omega
  have hp : 2 ^ L = 2 ^ b * 2 ^ (L - b) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp] at hmul
  exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)

theorem canonicalCode_lt (bl len : Nat → Nat) (L : Nat) (h0 : bl 0 = 0)
    (hk : kc bl L ≤ 2 ^ L) (n : Nat) (_hn1 : 1 ≤ len n) (hnL : len n ≤ L)
    (hcnt : countBefore len (len n) n < bl (len n)) :
    canonicalCode bl len n < 2 ^ len n := by
  have hle := nextCode_le_two_pow bl L h0 hk (len n) hnL
  unfold canonicalCode
  omega

theorem nextCode_u16_fit (bl : Nat → Nat) (h0 : bl 0 = 0) (hk : kc bl MAX_BITS ≤ 2 ^ MAX_BITS)
    (b : Nat) (hb : b ≤ MAX_BITS) :
    nextCode bl b + bl b ≤ 2 ^ MAX_BITS ∧ 2 ^ MAX_BITS < 2 ^ 16 := by
  have hle := nextCode_le_two_pow bl MAX_BITS h0 hk b hb
  have hpow : 2 ^ b ≤ 2 ^ MAX_BITS := Nat.pow_le_pow_right (by omega) hb
  have h16 : 2 ^ MAX_BITS < 2 ^ 16 := by decide
  exact ⟨Nat.le_trans hle hpow, h16⟩

/-! ## 5. `pqdownheap` Heap-Index Bounds & Preorder Invariants -/

/-- Polymorphic total preorder check. -/
structure KeyOK {α : Type} (key : α → α → Bool) : Prop where
  total : ∀ a b, key a b = true ∨ key b a = true
  trans : ∀ a b c, key a b = true → key b c = true → key a c = true

/-- Pure `smaller(tree, n, m, depth)` on `Nat` indices. -/
def smallerNat (freq depth : Nat → Nat) (a b : Nat) : Bool :=
  decide (freq a < freq b) || (freq a == freq b && decide (depth a ≤ depth b))

theorem smallerNat_ok (freq depth : Nat → Nat) : KeyOK (smallerNat freq depth) := by
  constructor
  · intro a b
    simp only [smallerNat, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
    omega
  · intro a b c
    simp only [smallerNat, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
    omega

/-- `smaller` specialized to C `UInt16` frequencies, `UInt8` depths, and `Int32` node indices. -/
def smallerU16U8 (fr : Nat → UInt16) (dp : Nat → UInt8) (a b : Int32) : Bool :=
  decide (fr a.toInt.toNat < fr b.toInt.toNat) ||
    (fr a.toInt.toNat == fr b.toInt.toNat && decide (dp a.toInt.toNat ≤ dp b.toInt.toNat))

theorem smallerU16U8_ok (fr : Nat → UInt16) (dp : Nat → UInt8) : KeyOK (smallerU16U8 fr dp) := by
  constructor
  · intro a b
    simp only [smallerU16U8, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      UInt16.lt_iff_toNat_lt, ← UInt16.toNat_inj, UInt8.le_iff_toNat_le]
    omega
  · intro a b c
    simp only [smallerU16U8, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      UInt16.lt_iff_toNat_lt, ← UInt16.toNat_inj, UInt8.le_iff_toNat_le]
    omega

/-- Heap property for every parent `p > k` in `heap[1 .. len]`. -/
def HeapOK {α : Type} (key : α → α → Bool) (H : Nat → α) (len k : Nat) : Prop :=
  ∀ c, 2 ≤ c → c ≤ len → k < c / 2 → key (H (c / 2)) (H c) = true

/-- `H'` on `1 .. len` is a permutation of `H` on `1 .. len`. -/
def PermOn {α : Type} (H' H : Nat → α) (len : Nat) : Prop :=
  ∃ σ : Nat → Nat, (∀ i, 1 ≤ i → i ≤ len → 1 ≤ σ i ∧ σ i ≤ len) ∧
    (∀ i i', 1 ≤ i → i ≤ len → 1 ≤ i' → i' ≤ len → σ i = σ i' → i = i') ∧
    ∀ i, 1 ≤ i → i ≤ len → H' i = H (σ i)

theorem PermOn.refl {α : Type} (H : Nat → α) (len : Nat) : PermOn H H len :=
  ⟨id, fun _ a b => ⟨a, b⟩, fun _ _ _ _ _ _ e => e, fun _ _ _ => rfl⟩

/-- Swap positions `a`, `b`. -/
def swapAt {α : Type} (A : Nat → α) (a b : Nat) : Nat → α :=
  fun i => if i = a then A b else if i = b then A a else A i

theorem PermOn.swap {α : Type} {A H : Nat → α} {len : Nat} (hp : PermOn A H len) {a b : Nat}
    (ha : 1 ≤ a ∧ a ≤ len) (hb : 1 ≤ b ∧ b ≤ len) : PermOn (swapAt A a b) H len := by
  obtain ⟨σ, hr, hi, he⟩ := hp
  let τ : Nat → Nat := fun i => if i = a then b else if i = b then a else i
  refine ⟨σ ∘ τ, ?_, ?_, ?_⟩
  · intro i h1 h2; simp only [Function.comp, τ]; split
    · exact hr b hb.1 hb.2
    · split
      · exact hr a ha.1 ha.2
      · exact hr i h1 h2
  · intro i i' h1 h2 h3 h4 e
    simp only [Function.comp, τ] at e
    have hτ : ∀ x, 1 ≤ x → x ≤ len → 1 ≤ τ x ∧ τ x ≤ len := by
      intro x h1 h2; simp only [τ]; split
      · exact hb
      · split
        · exact ha
        · exact ⟨h1, h2⟩
    have := hi _ _ (hτ i h1 h2).1 (hτ i h1 h2).2 (hτ i' h3 h4).1 (hτ i' h3 h4).2 e
    simp only [τ] at this
    split at this <;> split at this <;> (try split at this) <;> (try split at this) <;> omega
  · intro i h1 h2; simp only [Function.comp, τ, swapAt]; split
    · exact he b hb.1 hb.2
    · split
      · exact he a ha.1 ha.2
      · exact he i h1 h2

theorem PermOn.trans' {α : Type} {A B D : Nat → α} {len : Nat}
    (h1 : PermOn A B len) (h2 : PermOn B D len) : PermOn A D len := by
  obtain ⟨σ, hr, hi, he⟩ := h1
  obtain ⟨τ, hr', hi', he'⟩ := h2
  refine ⟨τ ∘ σ, fun i a b => hr' _ (hr i a b).1 (hr i a b).2,
    fun i i' a b c d e => ?_, fun i a b => ?_⟩
  · exact hi i i' a b c d (hi' _ _ (hr i a b).1 (hr i a b).2 (hr i' c d).1 (hr i' c d).2 e)
  · simp only [Function.comp]; rw [he i a b, he' _ (hr i a b).1 (hr i a b).2]

theorem PermOn.preimage {α : Type} {A H : Nat → α} {len : Nat} (hp : PermOn A H len)
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ len) :
    ∃ j : Nat, 1 ≤ j ∧ j ≤ len ∧ A j = H i := by
  obtain ⟨σ, hr, hj, he⟩ := hp
  let P : Nat → Nat := fun q => σ (q + 1) - 1
  have hP : ∀ q < len, P q < len := by
    intro q hq
    have := hr (q + 1) (by omega) (by omega)
    dsimp only [P]; omega
  have hPi : ∀ q q', q < len → q' < len → P q = P q' → q = q' := by
    intro q q' hq hq' heq
    have ha := hr (q + 1) (by omega) (by omega)
    have hb := hr (q' + 1) (by omega) (by omega)
    have hs : σ (q + 1) = σ (q' + 1) := by dsimp only [P] at heq; omega
    have := hj (q + 1) (q' + 1) (by omega) (by omega) (by omega) (by omega) hs
    omega
  obtain ⟨q, hq, heq⟩ := inj_surj P len hP hPi (i - 1) (by omega)
  refine ⟨q + 1, by omega, by omega, ?_⟩
  rw [he (q + 1) (by omega) (by omega)]
  have := hr (q + 1) (by omega) (by omega)
  have hs : σ (q + 1) = i := by dsimp only [P] at heq; omega
  rw [hs]

theorem HeapOK.root_min {α : Type} {key : α → α → Bool} {H : Nat → α} {len : Nat}
    (hk : KeyOK key) (ho : HeapOK key H len 0) :
    ∀ q, 1 ≤ q → q ≤ len → key (H 1) (H q) = true := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro hq1 hq2
    by_cases heq : q = 1
    · subst q
      rcases hk.total (H 1) (H 1) with h | h <;> exact h
    · have hq : 2 ≤ q := by omega
      have hp : key (H 1) (H (q / 2)) = true :=
        ih (q / 2) (by omega) (by omega) (by omega)
      exact hk.trans _ _ _ hp (ho q hq hq2 (by omega))

/-- Sift-down hole invariant for `pqdownheap`. -/
def HoleInv {α : Type} (key : α → α → Bool) (A : Nat → α) (len k0 K : Nat) : Prop :=
  (∀ c, 2 ≤ c → c ≤ len → k0 ≤ c / 2 → c / 2 ≠ K → c ≠ K → key (A (c / 2)) (A c) = true) ∧
  (k0 < K → key (A (K / 2)) (A K) = true ∧
    ∀ c, c / 2 = K → 2 ≤ c → c ≤ len → key (A (K / 2)) (A c) = true)

theorem hole_init {α : Type} {key : α → α → Bool} {A : Nat → α} {len k0 : Nat}
    (h : HeapOK key A len k0) : HoleInv key A len k0 k0 :=
  ⟨fun c a b d _ _ => h c a b (by omega), fun h => absurd h (Nat.lt_irrefl _)⟩

/-- `j'` is a minimal child of `K`. -/
def MinChild {α : Type} (key : α → α → Bool) (A : Nat → α) (len K j' : Nat) : Prop :=
  j' / 2 = K ∧ 2 ≤ j' ∧ j' ≤ len ∧ ∀ c, c / 2 = K → 2 ≤ c → c ≤ len → key (A j') (A c) = true

theorem hole_break {α : Type} {key : α → α → Bool} (hk : KeyOK key) {A : Nat → α} {len k0 K j' : Nat}
    (hK : 1 ≤ k0 ∧ k0 ≤ K) (hI : HoleInv key A len k0 K) (hm : MinChild key A len K j')
    (hv : key (A K) (A j') = true) : HeapOK key A len (k0 - 1) := by
  intro c h2 hl _
  by_cases e1 : c / 2 = K
  · rw [e1]; exact hk.trans _ _ _ hv (hm.2.2.2 c e1 h2 hl)
  · by_cases e2 : c = K
    · subst e2; exact (hI.2 (by omega)).1
    · exact hI.1 c h2 hl (by omega) e1 e2

theorem hole_leaf {α : Type} {key : α → α → Bool} {A : Nat → α} {len k0 K : Nat}
    (hK : 1 ≤ k0 ∧ k0 ≤ K) (hI : HoleInv key A len k0 K) (hleaf : len < 2 * K) :
    HeapOK key A len (k0 - 1) := by
  intro c h2 hl _
  by_cases e1 : c / 2 = K
  · omega
  · by_cases e2 : c = K
    · subst e2; exact (hI.2 (by omega)).1
    · exact hI.1 c h2 hl (by omega) e1 e2

theorem hole_step {α : Type} {key : α → α → Bool} (hk : KeyOK key) {A : Nat → α} {len k0 K j' : Nat}
    (hK : 1 ≤ k0 ∧ k0 ≤ K) (hI : HoleInv key A len k0 K) (hm : MinChild key A len K j')
    (hv : key (A K) (A j') = false) : HoleInv key (swapAt A K j') len k0 j' := by
  obtain ⟨hj2, hj2', hjl, hmin⟩ := hm
  have hjK : K < j' := by omega
  have hkey : key (A j') (A K) = true := by
    rcases hk.total (A K) (A j') with h | h
    · rw [hv] at h; cases h
    · exact h
  refine ⟨?_, ?_⟩
  · intro c h2 hl hp e1 e2
    simp only [swapAt]
    by_cases f1 : c / 2 = K
    · rw [ite_eq_left f1, ite_eq_right (by omega), ite_eq_right e2]
      exact hmin c f1 h2 hl
    · by_cases f2 : c = K
      · rw [ite_eq_right f1, ite_eq_right (by omega), ite_eq_left f2]
        subst f2
        exact (hI.2 (by omega)).2 j' hj2 hj2' hjl
      · rw [ite_eq_right f1, ite_eq_right e1, ite_eq_right f2, ite_eq_right e2]
        exact hI.1 c h2 hl hp f1 f2
  · intro _
    have hne : j' ≠ K := by omega
    refine ⟨?_, ?_⟩
    · simp only [swapAt, hj2, hne, ite_true, ite_false]; exact hkey
    · intro c hc h2 hl
      have n1 : c ≠ K := by omega
      have n2 : c ≠ j' := by omega
      simp only [swapAt, hj2, n1, n2, ite_true, ite_false]
      have := hI.1 c h2 hl (by omega) (by omega) n1
      rwa [hc] at this

/-- `pqdownheap` index bounds: for `1 ≤ k ≤ heap_len ≤ L_CODES`, `2 * k ≤ 2 * L_CODES < HEAP_SIZE`,
every accessed heap slot `j` / `j + 1` is in `[1, heap_len] ⊂ [0, HEAP_SIZE)`, and descent increases `k`. -/
theorem pqdownheap_index_bounds {heap_len k : Nat}
    (hlen : heap_len ≤ L_CODES) (hk1 : 1 ≤ k) (hk2 : k ≤ heap_len) :
    let j := 2 * k
    j ≤ 2 * L_CODES ∧ 2 * L_CODES < HEAP_SIZE ∧
    (j ≤ heap_len →
      1 ≤ j ∧ j < HEAP_SIZE ∧
      (j < heap_len → j + 1 ≤ heap_len ∧ j + 1 < HEAP_SIZE) ∧
      k < j ∧ 2 * j ≤ 2 * L_CODES) := by
  intro j
  have hL : L_CODES = 286 := rfl
  have hH : HEAP_SIZE = 573 := rfl
  refine ⟨by omega, by omega, fun hj => ⟨by omega, by omega, fun hlt => ⟨by omega, by omega⟩, by omega, by omega⟩⟩

/-! ## 6. Merge-Loop Bounds & Fibonacci Ancestor Depth Bound -/

/-- Index invariants for iteration `a` (`0 ≤ a < K - 1`) of `build_tree`'s merge loop
with initial `heap_len = K` (`2 ≤ K ≤ elems ≤ L_CODES`). -/
theorem merge_loop_bounds {elems K a : Nat}
    (hK2 : 2 ≤ K) (hKe : K ≤ elems) (heL : elems ≤ L_CODES) (ha : a + 1 < K) :
    let heapLenBefore := K - a
    let heapLenAfter := heapLenBefore - 1
    let heapMaxBefore := HEAP_SIZE - 2 * a
    let slotN := heapMaxBefore - 1
    let slotM := heapMaxBefore - 2
    let node := elems + a
    2 ≤ heapLenBefore ∧ heapLenBefore ≤ L_CODES ∧
    1 ≤ heapLenAfter ∧ heapLenAfter < slotM ∧
    3 ≤ slotM ∧ slotN < HEAP_SIZE ∧
    elems ≤ node ∧ node < 2 * elems - 1 ∧
    2 * elems - 1 < 2 * elems + 1 ∧ 2 * elems + 1 ≤ HEAP_SIZE ∧
    node < 2 ^ 16 := by
  have hL : L_CODES = 286 := rfl
  have hH : HEAP_SIZE = 573 := rfl
  omega

/-- Final root store after `K - 1` merges (`hm = HEAP_SIZE - 2 * (K - 1) - 1 = 574 - 2 * K`). -/
theorem merge_root_bounds {elems K : Nat} (hK2 : 2 ≤ K) (hKe : K ≤ elems) (heL : elems ≤ L_CODES) :
    let hm := HEAP_SIZE - 2 * (K - 1) - 1
    2 ≤ hm ∧ hm + 2 * (K - 1) + 1 = HEAP_SIZE ∧ 1 < hm ∧ hm < HEAP_SIZE := by
  have hL : L_CODES = 286 := rfl
  have hH : HEAP_SIZE = 573 := rfl
  omega

/-- Standard Fibonacci sequence for depth bounding (`fib 0 = 0, fib 1 = 1`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one : fib 1 = 1 := rfl
theorem fib_two : fib 2 = 1 := rfl
theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

theorem fib_le_succ : ∀ n, fib n ≤ fib (n + 1)
  | 0 => by decide
  | n + 1 => by rw [fib_add_two]; omega

theorem fib_mono {m n : Nat} (h : m ≤ n) : fib m ≤ fib n := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (fib_le_succ n)
    · obtain rfl : m = n + 1 := by omega
      exact Nat.le_refl _

/-- `gF w d = w * fib (d + 1) + fib d`: least root weight of a leaf of weight `w` at depth `d`. -/
def gF (w d : Nat) : Nat := w * fib (d + 1) + fib d

theorem gF_zero (w : Nat) : gF w 0 = w := by simp [gF, fib_zero, fib_one]
theorem gF_one (w : Nat) : gF w 1 = w + 1 := by simp [gF, fib_two, fib_one]
theorem gF_add_two (w d : Nat) : gF w (d + 2) = gF w d + gF w (d + 1) := by
  simp only [gF, fib_add_two]; rw [Nat.mul_add]; omega

/-- Fibonacci ancestor chain bound: `w * fib (δ + 1) + fib δ ≤ p δ`. -/
theorem fibChain_bound (p s : Nat → Nat) (w δ : Nat) (h0 : p 0 = w)
    (hstep : ∀ i, i < δ → p (i + 1) = p i + s i) (hs0 : 0 < δ → 1 ≤ s 0)
    (hs : ∀ i, i + 1 < δ → p i ≤ s (i + 1)) :
    w * fib (δ + 1) + fib δ ≤ p δ := by
  have key : ∀ i, i ≤ δ → gF w i ≤ p i ∧ (i + 1 ≤ δ → gF w (i + 1) ≤ p (i + 1)) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by rw [gF_zero, h0]; exact Nat.le_refl _, fun h1 => ?_⟩
      rw [gF_one, hstep 0 (by omega), h0]; have := hs0 (by omega); omega
    | succ i ih =>
      intro hi
      have ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2 hi, fun h3 => ?_⟩
      rw [gF_add_two, hstep (i + 1) (by omega)]
      have := hs i (by omega)
      omega
  exact (key δ (Nat.le_refl _)).1

theorem fib_25_gt_u16 : 65536 ≤ fib 25 := by decide

/-- If `1 * fib (d + 1) + fib d = fib (d + 2) ≤ 65535`, then `d ≤ 22 < 256` (`uch depth` never wraps). -/
theorem depth_le_22_of_u16_weight {d w W : Nat} (hw : 1 ≤ w) (hW : W < 65536)
    (hchain : w * fib (d + 1) + fib d ≤ W) : d ≤ 22 ∧ d + 1 < 256 := by
  have h1 : fib (d + 2) ≤ w * fib (d + 1) + fib d := by
    rw [fib_add_two]
    have hmul : fib (d + 1) ≤ w * fib (d + 1) := Nat.le_mul_of_pos_left _ hw
    omega
  have hle : fib (d + 2) < 65536 := by omega
  have hd : d + 2 < 25 := by
    apply Classical.byContradiction
    intro hge
    have h25 : fib 25 ≤ fib (d + 2) := fib_mono (by omega)
    have := fib_25_gt_u16
    omega
  omega

/-! ## 7. `gen_bitlen`: Clamped Kraft Identity, Overflow Repair Loop, & Pass 3 -/

/-- `Dad` of node at heap position `p`: positions `572 - 2j` and `571 - 2j` have dad `elems + j`. -/
def dadP (elems p : Nat) : Nat := elems + (572 - p) / 2

/-- Tree shape left in `heap[hm .. HEAP_SIZE)` by `build_tree`. -/
structure PShape (H : Nat → Nat) (hm J elems maxc : Nat) : Prop where
  hm_eq : hm + 2 * J + 1 = HEAP_SIZE
  J1 : 1 ≤ J
  maxc_lt : maxc < elems
  inj : ∀ q q', hm ≤ q → q < HEAP_SIZE → hm ≤ q' → q' < HEAP_SIZE → H q = H q' → q = q'
  kind : ∀ q, hm ≤ q → q < HEAP_SIZE → H q ≤ maxc ∨ (elems ≤ H q ∧ H q < elems + J)
  root : H hm = elems + J - 1
  appears : ∀ j < J, ∃ q, hm ≤ q ∧ q < 571 - 2 * j ∧ H q = elems + j

/-- Clamped depths computed in pass 1 of `gen_bitlen`. -/
structure Clamped (H : Nat → Nat) (hm J elems L : Nat) (cl : Nat → Nat) : Prop where
  root : cl (H hm) = 0
  step : ∀ i < 2 * J, cl (H (hm + 1 + i)) = min (cl (dadP elems (hm + 1 + i)) + 1) L

section GenBitlen
variable {H : Nat → Nat} {hm J elems maxc L : Nat} {cl : Nat → Nat}

theorem PShape.dadP_eq (S : PShape H hm J elems maxc) (i : Nat) (hi : i < 2 * J) :
    dadP elems (hm + 1 + i) = elems + (2 * J - 1 - i) / 2 := by
  have := S.hm_eq
  have hH : HEAP_SIZE = 573 := rfl
  unfold dadP
  congr 2
  omega

theorem Clamped.le_all (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (q : Nat)
    (h1 : hm ≤ q) (h2 : q < HEAP_SIZE) : cl (H q) ≤ L := by
  by_cases e : q = hm
  · subst e; rw [C.root]; omega
  · have := C.step (q - hm - 1) (by have := S.hm_eq; omega)
    rw [show hm + 1 + (q - hm - 1) = q by omega] at this
    rw [this]; exact Nat.min_le_right _ _

theorem Clamped.dad_le (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (i : Nat)
    (hi : i < 2 * J) : cl (dadP elems (hm + 1 + i)) ≤ L := by
  rw [S.dadP_eq i hi]
  obtain ⟨q, h1, h2, e⟩ := S.appears ((2 * J - 1 - i) / 2) (by omega)
  have hH : HEAP_SIZE = 573 := rfl
  rw [← e]
  exact C.le_all S q h1 (by omega)

theorem PShape.internal_sum (S : PShape H hm J elems maxc) (F : Nat → Nat) :
    rs (fun i => if elems ≤ H (hm + i) then F (H (hm + i)) else 0) (2 * J + 1) =
      rs (fun j => F (elems + j)) J := by
  have hm_eq := S.hm_eq
  have hP : ∀ i < 2 * J + 1, H (hm + i) < elems + J := by
    intro i hi
    rcases S.kind (hm + i) (by omega) (by omega) with h | h
    · have := S.maxc_lt; omega
    · exact h.2
  have := rs_image (fun i => H (hm + i)) (fun v => if elems ≤ v then F v else 0) (2 * J + 1) (elems + J) hP
  rw [this, rs_split]
  rw [rs_eq_zero (fun v _ => by rw [ite_eq_right (by omega), Nat.mul_zero])]
  rw [Nat.zero_add]
  apply rs_congr
  intro j hj
  rw [ite_eq_left (by omega)]
  obtain ⟨q, h1, h2, e⟩ := S.appears j hj
  have hH : HEAP_SIZE = 573 := rfl
  have c1 := cnt_pos (P := fun i => H (hm + i)) (m := 2 * J + 1) (i := q - hm) (by omega)
    (by show H (hm + (q - hm)) = _; rw [show hm + (q - hm) = q by omega, e])
  have c2 := cnt_le_one (fun i => H (hm + i)) (2 * J + 1) (elems + j)
    (fun a b ha hb e => by have := S.inj (hm + a) (hm + b) (by omega) (by omega) (by omega) (by omega) e; omega)
  rw [show cnt (fun i => H (hm + i)) (2 * J + 1) (elems + j) = 1 by omega, Nat.one_mul]

/-- Weight of one open child slot below a node of clamped depth `x` (scaled by `2^(L+1)`). -/
def slot (L x : Nat) : Nat := if x < L then 2 ^ (L - x) else 1

theorem local_leaf (L d : Nat) (_hL : 1 ≤ L) (hd : d ≤ L) :
    2 * 2 ^ (L - min (d + 1) L) = slot L d + ind (d = L) := by
  by_cases e : d = L
  · rw [show min (d + 1) L = L by omega]
    unfold slot ind
    rw [ite_eq_right (show ¬ d < L by omega), ite_eq_left e, Nat.sub_self]
  · rw [show min (d + 1) L = d + 1 by omega]
    unfold slot ind
    rw [ite_eq_left (show d < L by omega), ite_eq_right e]
    rw [show L - d = (L - (d + 1)) + 1 by omega, Nat.pow_succ]; omega

theorem local_int (L d : Nat) (_hL : 1 ≤ L) (hd : d ≤ L) :
    2 * slot L (min (d + 1) L) = slot L d + ind (d = L) := by
  by_cases e : d = L
  · rw [show min (d + 1) L = L by omega]
    unfold slot ind
    rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_right (show ¬ d < L by omega), ite_eq_left e]
  · by_cases e2 : d + 1 = L
    · rw [show min (d + 1) L = L by omega]
      unfold slot ind
      rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left (show d < L by omega), ite_eq_right e, show L - d = 1 by omega]
    · rw [show min (d + 1) L = d + 1 by omega]
      unfold slot ind
      rw [ite_eq_left (show d + 1 < L by omega), ite_eq_left (show d < L by omega), ite_eq_right e]
      rw [show L - d = (L - (d + 1)) + 1 by omega, Nat.pow_succ]; omega

def kraftC (H : Nat → Nat) (hm J maxc L : Nat) (cl : Nat → Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc then 2 ^ (L - cl (H (hm + 1 + i))) else 0) (2 * J)

def ovfC (_H : Nat → Nat) (hm J elems L : Nat) (cl : Nat → Nat) : Nat :=
  rs (fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) (2 * J)

def exactC (_H : Nat → Nat) (hm J elems L : Nat) (cl : Nat → Nat) : Nat :=
  rs (fun i => if cl (dadP elems (hm + 1 + i)) + 1 = L then 1 else 0) (2 * J)

def blC (H : Nat → Nat) (hm J maxc : Nat) (cl : Nat → Nat) (b : Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc ∧ cl (H (hm + 1 + i)) = b then 1 else 0) (2 * J)

def nLeaves (H : Nat → Nat) (hm J maxc : Nat) : Nat :=
  rs (fun i => if H (hm + 1 + i) ≤ maxc then 1 else 0) (2 * J)

theorem PShape.internal_tail (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (F : Nat → Nat) :
    F 0 + rs (fun i => if elems ≤ H (hm + 1 + i) then F (cl (H (hm + 1 + i))) else 0) (2 * J) =
      rs (fun j => F (cl (elems + j))) J := by
  have hint := S.internal_sum (fun v => F (cl v))
  rw [show 2 * J + 1 = 1 + 2 * J by omega, rs_split] at hint
  simp only [rs_succ, rs_zero, Nat.add_zero, Nat.zero_add] at hint
  rw [S.root, ite_eq_left (by have := S.J1; omega)] at hint
  rw [show elems + J - 1 = H hm by rw [S.root], C.root] at hint
  rw [← hint]
  congr 1
  apply rs_congr; intro i _; rw [Nat.add_assoc]

/-- **Clamped Kraft identity.** `2 · Σ_leaves 2^(L - cl) = 2^(L+1) + overflow`. -/
theorem kraft_clamped (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (hL : 1 ≤ L) :
    2 * kraftC H hm J maxc L cl = 2 ^ (L + 1) + ovfC H hm J elems L cl := by
  have hm_eq := S.hm_eq
  have hloc : ∀ i < 2 * J,
      (if H (hm + 1 + i) ≤ maxc then 2 * 2 ^ (L - cl (H (hm + 1 + i))) else 0) +
        2 * (if elems ≤ H (hm + 1 + i) then slot L (cl (H (hm + 1 + i))) else 0) =
      slot L (cl (dadP elems (hm + 1 + i))) + (if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) := by
    intro i hi
    have hd := C.dad_le S i hi
    rw [C.step i hi]
    have hk := S.kind (hm + 1 + i) (by omega) (by omega)
    have := S.maxc_lt
    by_cases hl : H (hm + 1 + i) ≤ maxc
    · rw [ite_eq_left hl, ite_eq_right (by omega)]
      have := local_leaf L _ hL hd; unfold ind at this; omega
    · rw [ite_eq_right hl, ite_eq_left (by omega)]
      have := local_int L _ hL hd; unfold ind at this; omega
  have hsum := rs_congr hloc
  rw [rs_add, rs_add, rs_mul] at hsum
  have hpair : rs (fun i => slot L (cl (dadP elems (hm + 1 + i)))) (2 * J) =
      2 * rs (fun j => slot L (cl (elems + j))) J := by
    rw [rs_congr (G := fun i => (fun j => slot L (cl (elems + j))) ((2 * J - 1 - i) / 2))
      (fun i hi => by simp only; rw [S.dadP_eq i hi])]
    exact rs_pair (fun j => slot L (cl (elems + j))) J
  have hint := S.internal_tail C (slot L)
  have hs0 : slot L 0 = 2 ^ L := by unfold slot; rw [ite_eq_left (show 0 < L by omega), Nat.sub_zero]
  rw [hs0] at hint
  have hleaf : rs (fun i => if H (hm + 1 + i) ≤ maxc then 2 * 2 ^ (L - cl (H (hm + 1 + i))) else 0) (2 * J) =
      2 * kraftC H hm J maxc L cl := by
    unfold kraftC; rw [← rs_mul]; apply rs_congr; intro i _; split <;> simp
  unfold ovfC
  rw [Nat.pow_succ]
  omega

/-- `bl_count[L] = exactC + overflow / 2`, and `overflow` is even. -/
theorem blC_top (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (_hL : 1 ≤ L) :
    ovfC H hm J elems L cl % 2 = 0 ∧
    blC H hm J maxc cl L = exactC H hm J elems L cl + ovfC H hm J elems L cl / 2 := by
  have hm_eq := S.hm_eq
  have hloc : ∀ i < 2 * J,
      (if H (hm + 1 + i) ≤ maxc ∧ cl (H (hm + 1 + i)) = L then 1 else 0) +
        (if elems ≤ H (hm + 1 + i) then (if cl (H (hm + 1 + i)) = L then 1 else 0) else 0) =
      (if cl (dadP elems (hm + 1 + i)) + 1 = L then 1 else 0) +
        (if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) := by
    intro i hi
    have hd := C.dad_le S i hi
    have hk := S.kind (hm + 1 + i) (by omega) (by omega)
    have := S.maxc_lt
    rw [C.step i hi]
    by_cases hl : H (hm + 1 + i) ≤ maxc
    · rw [ite_eq_right (show ¬ elems ≤ H (hm + 1 + i) by omega)]
      by_cases a : cl (dadP elems (hm + 1 + i)) + 1 = L
      · rw [ite_eq_left ⟨hl, by omega⟩, ite_eq_left a, ite_eq_right (by omega)]
      · by_cases b : cl (dadP elems (hm + 1 + i)) = L
        · rw [ite_eq_left ⟨hl, by omega⟩, ite_eq_right a, ite_eq_left b]
        · rw [ite_eq_right (fun h => by omega), ite_eq_right a, ite_eq_right b]
    · rw [ite_eq_right (fun h => hl h.1), ite_eq_left (by omega)]
      by_cases a : cl (dadP elems (hm + 1 + i)) + 1 = L
      · rw [ite_eq_left (by omega), ite_eq_left a, ite_eq_right (by omega)]
      · by_cases b : cl (dadP elems (hm + 1 + i)) = L
        · rw [ite_eq_left (by omega), ite_eq_right a, ite_eq_left b]
        · rw [ite_eq_right (by omega), ite_eq_right a, ite_eq_right b]
  have hsum := rs_congr hloc
  rw [rs_add, rs_add] at hsum
  have hpair : rs (fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) (2 * J) =
      2 * rs (fun j => if cl (elems + j) = L then 1 else 0) J := by
    rw [rs_congr (G := fun i => (fun j => if cl (elems + j) = L then 1 else 0) ((2 * J - 1 - i) / 2))
      (fun i hi => by simp only; rw [S.dadP_eq i hi])]
    exact rs_pair (fun j => if cl (elems + j) = L then 1 else 0) J
  have hint := S.internal_tail C (fun x => if x = L then 1 else 0)
  rw [ite_eq_right (by omega), Nat.zero_add] at hint
  unfold blC exactC ovfC
  constructor <;> omega

theorem exactC_pos (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (_hL : 1 ≤ L)
    (hov : 0 < ovfC H hm J elems L cl) : 0 < exactC H hm J elems L cl := by
  have hm_eq := S.hm_eq
  have hH : HEAP_SIZE = 573 := rfl
  have key0 : ∀ n i, i < n → i < 2 * J → cl (dadP elems (hm + 1 + i)) = L →
      ∃ i' < 2 * J, cl (dadP elems (hm + 1 + i')) + 1 = L := by
    intro n
    induction n with
    | zero => intro _ hi; omega
    | succ n ihn =>
      intro i hin hi hcl
      have ih : ∀ i', i' < i → i' < 2 * J → cl (dadP elems (hm + 1 + i')) = L →
          ∃ i' < 2 * J, cl (dadP elems (hm + 1 + i')) + 1 = L :=
        fun i' h1 => ihn i' (by omega)
      rw [S.dadP_eq i hi] at hcl
      obtain ⟨q, h1, h2, e⟩ := S.appears ((2 * J - 1 - i) / 2) (by omega)
      rw [← e] at hcl
      have hq : q ≠ hm := by intro e'; subst e'; rw [C.root] at hcl; omega
      obtain ⟨i', rfl⟩ : ∃ i', q = hm + 1 + i' := ⟨q - hm - 1, by omega⟩
      have hq' : i' < i := by omega
      have := C.step i' (by omega)
      rw [hcl] at this
      have hd := C.dad_le S i' (by omega)
      by_cases a : cl (dadP elems (hm + 1 + i')) + 1 = L
      · exact ⟨i', by omega, a⟩
      · exact ih i' hq' (by omega) (by omega)
  obtain ⟨i, hi, hcl⟩ : ∃ i < 2 * J, cl (dadP elems (hm + 1 + i)) = L := by
    by_cases hx : ∃ i < 2 * J, cl (dadP elems (hm + 1 + i)) = L
    · exact hx
    · have := rs_eq_zero (F := fun i => if cl (dadP elems (hm + 1 + i)) = L then 1 else 0) (n := 2 * J)
        (fun i hi => by rw [ite_eq_right (fun e => hx ⟨i, hi, e⟩)])
      unfold ovfC at hov; omega
  obtain ⟨i', hi', e'⟩ := key0 (i + 1) i (by omega) hi hcl
  have := le_rs (F := fun i => if cl (dadP elems (hm + 1 + i)) + 1 = L then 1 else 0) hi'
  simp only [e', ite_true] at this
  unfold exactC; omega

theorem blC_zero (_S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (_hL : 1 ≤ L) :
    blC H hm J maxc cl 0 = 0 := by
  unfold blC
  apply rs_eq_zero; intro i hi
  rw [ite_eq_right]; rintro ⟨_, e⟩; rw [C.step i hi] at e; omega

theorem blC_high (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) (b : Nat) (hb : L < b) :
    blC H hm J maxc cl b = 0 := by
  have hm_eq := S.hm_eq
  unfold blC
  apply rs_eq_zero; intro i hi
  rw [ite_eq_right]; rintro ⟨_, e⟩; have := C.le_all S (hm + 1 + i) (by omega) (by omega); omega

theorem kraftC_eq (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) :
    kraftC H hm J maxc L cl = kc (blC H hm J maxc cl) L := by
  have hm_eq := S.hm_eq
  unfold kraftC kc blC
  exact rs_regroup (fun i => H (hm + 1 + i) ≤ maxc) (fun i => cl (H (hm + 1 + i))) (fun b => 2 ^ (L - b))
    (2 * J) (L + 1) (fun i hi _ => by have := C.le_all S (hm + 1 + i) (by omega) (by omega); omega)

theorem blC_total (S : PShape H hm J elems maxc) (C : Clamped H hm J elems L cl) :
    rs (fun b => blC H hm J maxc cl b) (L + 1) = nLeaves H hm J maxc := by
  have hm_eq := S.hm_eq
  have := rs_regroup (fun i => H (hm + 1 + i) ≤ maxc) (fun i => cl (H (hm + 1 + i))) (fun _ => 1)
    (2 * J) (L + 1) (fun i hi _ => by have := C.le_all S (hm + 1 + i) (by omega) (by omega); omega)
  unfold nLeaves blC
  rw [this]; apply rs_congr; intro b _; simp

theorem PShape.leaf_sum (S : PShape H hm J elems maxc) (T : Nat → Prop) [DecidablePred T]
    (hT : ∀ v ≤ maxc, T v ↔ ∃ q, hm < q ∧ q < HEAP_SIZE ∧ H q = v) (F : Nat → Nat) :
    rs (fun i => if H (hm + 1 + i) ≤ maxc then F (H (hm + 1 + i)) else 0) (2 * J) =
      rs (fun v => if T v then F v else 0) (maxc + 1) := by
  have hm_eq := S.hm_eq
  have hlt := S.maxc_lt
  have hP : ∀ i < 2 * J, H (hm + 1 + i) < elems + J := by
    intro i hi
    rcases S.kind (hm + 1 + i) (by omega) (by omega) with h | h
    · omega
    · exact h.2
  have := rs_image (fun i => H (hm + 1 + i)) (fun v => if v ≤ maxc then F v else 0) (2 * J) (elems + J) hP
  rw [this, show elems + J = (maxc + 1) + (elems + J - (maxc + 1)) by omega, rs_split]
  rw [rs_eq_zero (F := fun i => cnt (fun i => H (hm + 1 + i)) (2 * J) (maxc + 1 + i) *
      (if maxc + 1 + i ≤ maxc then F (maxc + 1 + i) else 0)) (fun _ _ => by rw [ite_eq_right (by omega), Nat.mul_zero]),
    Nat.add_zero]
  apply rs_congr
  intro v hv
  rw [ite_eq_left (by omega)]
  have hinj : ∀ a b, a < 2 * J → b < 2 * J → H (hm + 1 + a) = H (hm + 1 + b) → a = b :=
    fun a b ha hb e => by
      have := S.inj (hm + 1 + a) (hm + 1 + b) (by omega) (by omega) (by omega) (by omega) e; omega
  have c2 := cnt_le_one (fun i => H (hm + 1 + i)) (2 * J) v hinj
  by_cases ht : T v
  · rw [ite_eq_left ht]
    obtain ⟨q, h1, h2, e⟩ := (hT v (by omega)).mp ht
    have c1 := cnt_pos (P := fun i => H (hm + 1 + i)) (m := 2 * J) (i := q - hm - 1) (by omega)
      (by show H (hm + 1 + (q - hm - 1)) = _; rw [show hm + 1 + (q - hm - 1) = q by omega, e])
    rw [show cnt (fun i => H (hm + 1 + i)) (2 * J) v = 1 by omega, Nat.one_mul]
  · rw [ite_eq_right ht]
    have : cnt (fun i => H (hm + 1 + i)) (2 * J) v = 0 := cnt_zero (fun i hi e =>
      ht ((hT v (by omega)).mpr ⟨hm + 1 + i, by omega, by omega, e⟩))
    rw [this, Nat.zero_mul]

theorem nLeaves_le (S : PShape H hm J elems maxc) : nLeaves H hm J maxc ≤ maxc + 1 := by
  classical
  have hl := S.leaf_sum (fun v => ∃ q, hm < q ∧ q < HEAP_SIZE ∧ H q = v) (fun _ _ => Iff.rfl) (fun _ => 1)
  unfold nLeaves
  rw [hl]
  have := rs_le (n := maxc + 1) (F := fun v => if (∃ q, hm < q ∧ q < HEAP_SIZE ∧ H q = v) then 1 else 0)
    (G := fun _ => 1) (fun _ _ => by split <;> omega)
  rw [rs_const] at this; omega

end GenBitlen

/-! ### Overflow Repair Loop (`deepest`, `repairStep`, `repairIter`) -/

/-- Point update of a count vector. -/
def updC (c : Nat → Nat) (a v : Nat) : Nat → Nat := fun x => if x = a then v else c x

/-- Deepest level `≤ b` with nonzero count (`while (bl_count[bits] == 0) bits--;`). -/
def deepest (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => if c (b + 1) ≠ 0 then b + 1 else deepest c b

/-- One iteration of `gen_bitlen`'s overflow repair loop (`max_length = L`). -/
def repairStep (L : Nat) (c : Nat → Nat) : Nat → Nat :=
  let b := deepest c (L - 1)
  let c1 := updC c b (c b - 1)
  let c2 := updC c1 (b + 1) (c1 (b + 1) + 2)
  updC c2 L (c2 L - 1)

/-- `M` iterations of the overflow repair loop (`M = overflow / 2`). -/
def repairIter (L : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, c => c
  | M + 1, c => repairIter L M (repairStep L c)

theorem deepest_le (c : Nat → Nat) : ∀ b, deepest c b ≤ b
  | 0 => Nat.le_refl 0
  | b + 1 => by
    unfold deepest
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans (deepest_le c b) (by omega)

theorem deepest_pos {c : Nat → Nat} {b k : Nat} (hk1 : 1 ≤ k) (hkb : k ≤ b) (hkc : c k ≠ 0) :
    1 ≤ deepest c b ∧ c (deepest c b) ≠ 0 := by
  induction b with
  | zero => omega
  | succ b ih =>
    unfold deepest
    by_cases hb : c (b + 1) ≠ 0
    · rw [ite_eq_left hb]
      exact ⟨by omega, hb⟩
    · rw [ite_eq_right hb]
      have hkb' : k ≤ b := by
        by_cases heq : k = b + 1
        · subst heq; exact absurd hkc hb
        · omega
      exact ih hkb'

theorem round_kraft (c c' : Nat → Nat) (L b : Nat) (hb : b + 1 ≤ L)
    (h : ∀ x ≤ L, c' x + ind (x = b) + ind (x = L) = c x + 2 * ind (x = b + 1)) :
    kc c' L + 1 = kc c L ∧ rs c' (L + 1) = rs c (L + 1) := by
  have e1 := rs_congr (n := L + 1) (F := fun x => (c' x + ind (x = b) + ind (x = L)) * 2 ^ (L - x))
    (G := fun x => (c x + 2 * ind (x = b + 1)) * 2 ^ (L - x)) (fun x hx => by rw [h x (by omega)])
  simp only [Nat.add_mul, Nat.mul_assoc] at e1
  rw [rs_add, rs_add, rs_add] at e1
  simp only [ind_mul] at e1
  rw [rs_single _ _ _, rs_single _ _ _, ite_eq_left (by omega), ite_eq_left (by omega)] at e1
  have e3 : rs (fun i => 2 * (if i = b + 1 then 2 ^ (L - i) else 0)) (L + 1) = 2 * 2 ^ (L - (b + 1)) := by
    rw [rs_mul, rs_single, ite_eq_left (by omega)]
  rw [e3] at e1
  have e4 : 2 ^ (L - b) = 2 * 2 ^ (L - (b + 1)) := by
    rw [show L - b = (L - (b + 1)) + 1 by omega, Nat.pow_succ]; omega
  rw [e4, Nat.sub_self, Nat.pow_zero] at e1
  refine ⟨by unfold kc; omega, ?_⟩
  have e2 := rs_congr (n := L + 1) (F := fun x => c' x + ind (x = b) + ind (x = L))
    (G := fun x => c x + 2 * ind (x = b + 1)) (fun x hx => h x (by omega))
  rw [rs_add, rs_add, rs_add, rs_mul] at e2
  rw [rs_ind_eq b _ (by omega), rs_ind_eq L _ (by omega), rs_ind_eq (b + 1) _ (by omega)] at e2
  omega

theorem exists_short (c : Nat → Nat) (L R : Nat) (hR : 1 ≤ R) (hk : kc c L = 2 ^ L + R)
    (htot : rs c (L + 1) ≤ 2 ^ L) (h0 : c 0 = 0) : ∃ b, 1 ≤ b ∧ b < L ∧ c b ≠ 0 := by
  by_cases hx : ∃ b, 1 ≤ b ∧ b < L ∧ c b ≠ 0
  · exact hx
  · exfalso
    have z : rs (fun b => c b * 2 ^ (L - b)) L = 0 := rs_eq_zero (fun b hb => by
      by_cases e : b = 0
      · subst e; rw [h0, Nat.zero_mul]
      · have : c b = 0 := by
          by_cases e' : c b = 0
          · exact e'
          · exact absurd ⟨b, by omega, hb, e'⟩ hx
        rw [this, Nat.zero_mul])
    unfold kc at hk
    rw [rs_succ, z, Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hk
    have := le_rs (F := c) (n := L + 1) (i := L) (by omega)
    omega

theorem repairStep_rel (c : Nat → Nat) (L : Nat) (hL : 1 ≤ L)
    (hcb : 1 ≤ c (deepest c (L - 1))) (hcL : 1 ≤ c L) :
    let b := deepest c (L - 1)
    ∀ x, repairStep L c x + ind (x = b) + ind (x = L) = c x + 2 * ind (x = b + 1) := by
  intro b x
  have hble : b ≤ L - 1 := deepest_le c (L - 1)
  have hblt : b < L := by omega
  have hcb' : 1 ≤ c b := hcb
  have hne1 : b + 1 ≠ b := by omega
  have hne2 : L ≠ b := by omega
  change (if x = L then (if L = b + 1 then (if b + 1 = b then c b - 1 else c (b + 1)) + 2
      else if L = b then c b - 1 else c L) - 1
    else if x = b + 1 then (if b + 1 = b then c b - 1 else c (b + 1)) + 2
    else if x = b then c b - 1 else c x) +
    (if x = b then 1 else 0) + (if x = L then 1 else 0) =
    c x + 2 * (if x = b + 1 then 1 else 0)
  rw [ite_eq_right hne1]
  by_cases hxL : x = L
  · rw [hxL, ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hne2]
    by_cases hLb1 : L = b + 1
    · rw [ite_eq_left hLb1, ite_eq_left hLb1, hLb1, ite_eq_right hne1]
      omega
    · rw [ite_eq_right hLb1, ite_eq_right hne2, ite_eq_right hLb1]
      omega
  · rw [ite_eq_right hxL, ite_eq_right hxL, Nat.add_zero]
    by_cases hxb1 : x = b + 1
    · rw [hxb1, ite_eq_left rfl, ite_eq_right hne1, ite_eq_left rfl]
    · rw [ite_eq_right hxb1, ite_eq_right hxb1, Nat.mul_zero, Nat.add_zero]
      by_cases hxb : x = b
      · rw [hxb, ite_eq_left rfl, ite_eq_left rfl]
        omega
      · rw [ite_eq_right hxb, ite_eq_right hxb, Nat.add_zero]

/-- One `repairStep` preserves `c 0 = 0`, lowers `kc` by `1`, preserves total leaf count,
and leaves `c L` with at least `R` entries when `R + 1 ≤ c L`. -/
theorem repairStep_spec {c : Nat → Nat} {L R : Nat} (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hk : kc c L = 2 ^ L + R) (htot : rs c (L + 1) ≤ 2 ^ L) (h0 : c 0 = 0)
    (hcL : R + 1 ≤ c L) :
    let b := deepest c (L - 1)
    let c' := repairStep L c
    1 ≤ b ∧ b < L ∧ 1 ≤ c b ∧
    kc c' L = 2 ^ L + (R - 1) ∧ rs c' (L + 1) = rs c (L + 1) ∧ c' 0 = 0 ∧ R ≤ c' L := by
  obtain ⟨k, hk1, hkL, hkc⟩ := exists_short c L R hR hk htot h0
  obtain ⟨hb1, hcb⟩ := deepest_pos hk1 (by omega : k ≤ L - 1) hkc
  have hble : deepest c (L - 1) ≤ L - 1 := deepest_le c (L - 1)
  have hblt : deepest c (L - 1) < L := by omega
  let b := deepest c (L - 1)
  have hcb1 : 1 ≤ c b := by change 1 ≤ c (deepest c (L - 1)); omega
  have hbL : b + 1 ≤ L := by omega
  have hrel : ∀ x ≤ L, repairStep L c x + ind (x = b) + ind (x = L) =
      c x + 2 * ind (x = b + 1) :=
    fun x _ => repairStep_rel c L hL hcb1 (by omega) x
  obtain ⟨hkc', hrs'⟩ := round_kraft c (repairStep L c) L b hbL hrel
  have hc0' : repairStep L c 0 = 0 := by
    have h0' := hrel 0 (Nat.zero_le L)
    have h1 : (0 : Nat) ≠ b := by omega
    have h2 : (0 : Nat) ≠ L := by omega
    have h3 : (0 : Nat) ≠ b + 1 := by omega
    simp only [ind, h1, h2, h3, ite_false] at h0'
    omega
  have hcL' : R ≤ repairStep L c L := by
    have hL' := hrel L (Nat.le_refl L)
    have h1 : L ≠ b := by omega
    simp only [ind, h1, ite_false, ite_true] at hL'
    omega
  exact ⟨hb1, hblt, hcb1, by omega, hrs', hc0', hcL'⟩

/-- Full `repairIter L M c` termination & Kraft invariance:
after `M = overflow / 2` steps, `kc (repairIter L M c) L = 2 ^ L` (exact Kraft equality)
and `rs (repairIter L M c) (L + 1) = rs c (L + 1)`. -/
theorem repairIter_spec {L : Nat} (hL : 1 ≤ L) :
    ∀ M c, kc c L = 2 ^ L + M → rs c (L + 1) ≤ 2 ^ L → c 0 = 0 → M + 1 ≤ c L →
      kc (repairIter L M c) L = 2 ^ L ∧
      rs (repairIter L M c) (L + 1) = rs c (L + 1) ∧
      repairIter L M c 0 = 0
  | 0, c, hk, _, h0, _ => ⟨by rw [Nat.add_zero] at hk; exact hk, rfl, h0⟩
  | M + 1, c, hk, htot, h0, hcL => by
    have hs := repairStep_spec hL (R := M + 1) (by omega) hk htot h0 hcL
    dsimp only at hs
    have ih := repairIter_spec hL M (repairStep L c) (by omega) (by rw [hs.2.2.2.2.1]; exact htot)
      hs.2.2.2.2.2.1 hs.2.2.2.2.2.2
    exact ⟨ih.1, ih.2.1.trans hs.2.2.2.2.1, ih.2.2⟩

/-- In `gen_bitlen` pass 3 (`while (n != 0) { m = s->heap[--h]; ... }`), `h` starts at `HEAP_SIZE`
and decreases by 1 per scanned entry in `[hm + 1, HEAP_SIZE)`, seeing `J + 1` leaves out of `2 * J`
entries (`hm < h`). Hence `h` never underflows below `hm + 1`. -/
theorem pass3_heap_index_bounds {hm J remainingLeaves scanned : Nat}
    (S_hm : hm + 2 * J + 1 = HEAP_SIZE)
    (_hleaves : remainingLeaves ≤ J + 1)
    (hrem : 1 ≤ remainingLeaves)
    (hsc : scanned + remainingLeaves ≤ 2 * J) :
    let h' := HEAP_SIZE - scanned - 1
    hm + 1 ≤ h' ∧ h' < HEAP_SIZE := by
  omega

/-- Descending search `for (max_blindex = BL_CODES - 1; max_blindex >= 3; max_blindex--)`
in `build_bl_tree`: stays within `[2, BL_CODES - 1]`. -/
def blMaxIdx (used : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => if m + 1 < 3 then m + 1 else if used (m + 1) then m + 1 else blMaxIdx used m

theorem blMaxIdx_bounds (used : Nat → Bool) {m : Nat} (hm : 2 ≤ m) :
    2 ≤ blMaxIdx used m ∧ blMaxIdx used m ≤ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    unfold blMaxIdx
    split
    · omega
    · split
      · omega
      · have := ih (by omega); omega

theorem blMaxIdx_suffix (used : Nat → Bool) (m k : Nat)
    (hk : blMaxIdx used m < k) (hkm : k ≤ m) : used k = false := by
  induction m with
  | zero =>
    have : blMaxIdx used 0 = 0 := rfl
    omega
  | succ m ih =>
    simp only [blMaxIdx] at hk
    split at hk
    · omega
    · split at hk
      · omega
      · rename_i hu
        by_cases heq : k = m + 1
        · subst k; exact Bool.eq_false_iff.mpr hu
        · exact ih hk (by omega)

end Zlib.Proof.Math.Trees
