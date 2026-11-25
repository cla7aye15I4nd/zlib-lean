/-!
# Pure Huffman & Decoding-Table Mathematics (`Zlib.Proof.Math.Inftrees`)

Heap-free mathematical library for `Zlib/Inftrees.lean` (`inflate_table` and
`inflate_fixed`). Covers:
- Patched zlib 1.4.0.1-motley table constants (`MAXBITS = 15`, `LENBITS = 10`,
  `DISTBITS = 8`, `ENOUGH_LENS = 1332`, `ENOUGH_DISTS = 400`, `ENOUGH = 1732`,
  `CODES_CAP = 128`, `FIXED_LENBITS = 9`, `FIXED_DISTBITS = 5`)
- Canonical Huffman bit-reversal (`rev`, `rev_lt`, `rev_mul_pow`, `rev_mod_pow`,
  `rev_split`, `rev_rev`, `rev_inj`)
- Backwards increment (`incrLoop`, `succ_rev`, `huff_step`, `huff_last`)
- Counting sort & canonical code assignment (`fl`, `cnt`, `wsAux`, `Tc`, `Kc`,
  `lenAt`, `val`, `rem`, `pre`, `mxl`, `mnl`, `Fits`, `Complete`)
- Parametric subtable sizing (`sizeLoop`, `SL`, `currOf`, `block_bound`:
  `curr ≤ MAXBITS - root`, `2^curr ≤ 2^(MAXBITS - root)`)
- Root clamping, descriptor layout (`desc`, `startsAt`, `grp`, `look`, `width`,
  `gReps`, `gAddr`, `gSlot`, `GeoOK`), prefix/offset/mask write bounds, and
  `ENOUGH_LENS = 1332` / `ENOUGH_DISTS = 400` / `ENOUGH = 1732` allocation bounds
  (both guarded runtime bounds and the exact canonical combinatorial `enough`
  theorems).
-/

namespace Zlib.Proof.Math.Inftrees

/-! ## 1. Constants (`Zlib/Headers/Common.lean`, `Zlib/Inftrees.lean`) -/

def MAXBITS : Nat := 15
def LENBITS : Nat := 10
def DISTBITS : Nat := 8
def ENOUGH_LENS : Nat := 1332
def ENOUGH_DISTS : Nat := 400
def ENOUGH : Nat := ENOUGH_LENS + ENOUGH_DISTS
def CODES_ROOT : Nat := 7
def CODES_CAP : Nat := 128
def FIXED_LENBITS : Nat := 9
def FIXED_DISTBITS : Nat := 5
def L_CODES : Nat := 286
def D_CODES : Nat := 30
def BL_CODES : Nat := 19

theorem enough_eq : ENOUGH = 1732 := rfl
theorem enough_lens_eq : ENOUGH_LENS = 1332 := rfl
theorem enough_dists_eq : ENOUGH_DISTS = 400 := rfl
theorem codes_cap_eq : CODES_CAP = 2 ^ CODES_ROOT := rfl
theorem fixed_len_fit : 2 ^ FIXED_LENBITS = 512 := rfl
theorem fixed_dist_fit : 2 ^ FIXED_DISTBITS = 32 := rfl
theorem lenbits_root_fit : 2 ^ LENBITS ≤ ENOUGH_LENS := by decide
theorem distbits_root_fit : 2 ^ DISTBITS ≤ ENOUGH_DISTS := by decide

/-- Capacity passed to `inflate_table`: `0` -> `CODES` (128), `1` -> `LENS` (1332),
`_` -> `DISTS` (400). -/
def capOfKind : Nat → Nat
  | 0 => CODES_CAP
  | 1 => ENOUGH_LENS
  | _ => ENOUGH_DISTS

theorem capOfKind_ge_two (k : Nat) : 2 ≤ capOfKind k := by
  cases k with
  | zero => decide
  | succ k => cases k with
    | zero => decide
    | succ _ => simp [capOfKind, ENOUGH_DISTS]

theorem capOfKind_lt_u16 (k : Nat) : capOfKind k < 2 ^ 16 := by
  cases k with
  | zero => decide
  | succ k => cases k with
    | zero => decide
    | succ _ => simp [capOfKind, ENOUGH_DISTS]

/-! ## 2. Canonical Huffman Bit-Reversal -/

/-- Reverse the low `n` bits of `v`. -/
def rev : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => (v % 2) * 2 ^ n + rev n (v / 2)

@[simp] theorem rev_zero (v : Nat) : rev 0 v = 0 := rfl

theorem rev_succ (n v : Nat) : rev (n + 1) v = (v % 2) * 2 ^ n + rev n (v / 2) := rfl

@[simp] theorem rev_of_zero : ∀ n, rev n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [rev, rev_of_zero n]

theorem rev_one (v : Nat) : rev 1 v = v % 2 := by simp [rev]

theorem rev_lt : ∀ n v, rev n v < 2 ^ n
  | 0, _ => by simp [rev]
  | n + 1, v => by
    have := rev_lt n (v / 2)
    simp only [rev, Nat.pow_succ]
    have hbit : v % 2 ≤ 1 := by omega
    have h2 : v % 2 * 2 ^ n ≤ 2 ^ n := by
      calc v % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hbit
        _ = 2 ^ n := Nat.one_mul _
    omega

theorem rev_mul_pow : ∀ k n w, rev (n + k) (w * 2 ^ k) = rev n w
  | 0, n, w => by simp
  | k + 1, n, w => by
    have e : n + (k + 1) = (n + k) + 1 := by omega
    rw [e, rev]
    have h1 : w * 2 ^ (k + 1) % 2 = 0 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; simp [Nat.mul_mod_left]
    have h2 : w * 2 ^ (k + 1) / 2 = w * 2 ^ k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by omega)]
    rw [h1, h2, rev_mul_pow k n w]
    simp

theorem rev_mod_pow : ∀ d R v, rev (R + d) v % 2 ^ R = rev R (v / 2 ^ d)
  | 0, R, v => by
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (rev_lt R v)
  | d + 1, R, v => by
    have e : R + (d + 1) = (R + d) + 1 := by omega
    rw [e, rev]
    have hR : 2 ^ R ∣ 2 ^ (R + d) := Nat.pow_dvd_pow 2 (by omega)
    have h0 : v % 2 * 2 ^ (R + d) % 2 ^ R = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.dvd_trans hR (Nat.dvd_mul_left _ _)
    rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, rev_mod_pow d R (v / 2)]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2]

theorem rev_split : ∀ b a x, rev (a + b) x = rev a (x / 2 ^ b) + rev b (x % 2 ^ b) * 2 ^ a
  | 0, a, x => by simp [rev]
  | b + 1, a, x => by
    rw [show a + (b + 1) = (a + b) + 1 by omega, rev_succ, rev_split b a (x / 2), rev_succ]
    have h1 : x / 2 / 2 ^ b = x / 2 ^ (b + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have h2 : x % 2 ^ (b + 1) / 2 = x / 2 % 2 ^ b := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    have h3 : x % 2 ^ (b + 1) % 2 = x % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    rw [h1, h2, h3, Nat.pow_add 2 a b, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 ^ b) (2 ^ a)]
    omega

theorem rev_div_pow (d R v : Nat) : rev (R + d) v / 2 ^ R = rev d (v % 2 ^ d) := by
  rw [rev_split d R v, Nat.add_mul_div_right _ _ (Nat.two_pow_pos R),
    Nat.div_eq_of_lt (rev_lt R (v / 2 ^ d)), Nat.zero_add]

theorem rev_rev : ∀ k x, rev k (rev k x) = x % 2 ^ k
  | 0, x => by simp [rev, Nat.mod_one]
  | k + 1, x => by
    have hs := rev_split k 1 (rev (k + 1) x)
    rw [show 1 + k = k + 1 by omega] at hs
    have hlt := rev_lt k (x / 2)
    have h1 : (x % 2 * 2 ^ k + rev k (x / 2)) / 2 ^ k = x % 2 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlt]
      simp
    have h2 : (x % 2 * 2 ^ k + rev k (x / 2)) % 2 ^ k = rev k (x / 2) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [hs, rev_one, show rev (k + 1) x = x % 2 * 2 ^ k + rev k (x / 2) from rfl,
      h1, h2, rev_rev k (x / 2), Nat.mod_mod, Nat.pow_one]
    have hmod := Nat.mod_add_div (x % 2 ^ (k + 1)) 2
    have e1 : x % 2 ^ (k + 1) % 2 = x % 2 := by rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    have e2 : x % 2 ^ (k + 1) / 2 = x / 2 % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [e1, e2] at hmod
    omega

theorem rev_inj : ∀ n a b, rev n a = rev n b → a % 2 ^ n = b % 2 ^ n
  | 0, _, _, _ => by simp [Nat.mod_one]
  | n + 1, a, b, h => by
    have hrr := congrArg (rev (n + 1)) h
    rw [rev_rev, rev_rev] at hrr
    exact hrr

theorem rev_inj_lt {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : rev n a = rev n b) : a = b := by
  have := rev_inj n a b h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ## 3. Backwards Increment (`huff` Next-Code Step) -/

/-- `incr = 1U << e; while (huff & incr) incr >>= 1;` ends with `incr = incrLoop huff e`. -/
def incrLoop (h : Nat) : Nat → Nat
  | 0 => if h.testBit 0 then 0 else 1
  | e + 1 => if h.testBit (e + 1) then incrLoop h e else 2 ^ (e + 1)

theorem incrLoop_mod : ∀ e h, incrLoop h e = incrLoop (h % 2 ^ (e + 1)) e
  | 0, h => by simp [incrLoop]
  | e + 1, h => by
    simp only [incrLoop, Nat.testBit_mod_two_pow]
    have h1 := incrLoop_mod e h
    have h2 := incrLoop_mod e (h % 2 ^ (e + 1 + 1))
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))] at h2
    simp [h1, h2]

theorem incrLoop_le : ∀ e h, incrLoop h e ≤ 2 ^ e
  | 0, _ => by unfold incrLoop; split <;> omega
  | e + 1, h => by
    unfold incrLoop
    split
    · exact Nat.le_trans (incrLoop_le e h) (Nat.pow_le_pow_right (by omega) (by omega))
    · exact Nat.le_refl _

theorem incrLoop_lt (e h : Nat) : incrLoop h e < 2 ^ (e + 1) := by
  have := incrLoop_le e h
  have := Nat.two_pow_pos e
  rw [Nat.pow_succ]
  omega

/-- Adding `1` to an `(n + 1)`-bit number in reversed representation. -/
theorem succ_rev : ∀ n v, v < 2 ^ (n + 1) →
    (v + 1 < 2 ^ (n + 1) → ∃ e ≤ n, incrLoop (rev (n + 1) v) n = 2 ^ e ∧
        rev (n + 1) v % 2 ^ e + 2 ^ e = rev (n + 1) (v + 1)) ∧
    (v + 1 = 2 ^ (n + 1) → incrLoop (rev (n + 1) v) n = 0)
  | 0, v, hv => by
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · have : v = 0 := by simp at hv h1; omega
      subst this
      refine ⟨0, Nat.le_refl _, ?_, ?_⟩ <;> simp [rev, incrLoop]
    · have : v = 1 := by simp at h1; omega
      subst this
      simp [rev, incrLoop]
  | n + 1, v, hv => by
    have hlt := rev_lt (n + 1) (v / 2)
    have hP : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hP' : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
    have hrv : ∀ x, rev (n + 1 + 1) x = x % 2 * 2 ^ (n + 1) + rev (n + 1) (x / 2) := fun _ => rfl
    have ih := succ_rev n (v / 2) (by omega)
    rcases (by omega : v % 2 = 0 ∨ v % 2 = 1) with h0 | h0
    · have hh : rev (n + 1 + 1) v = rev (n + 1) (v / 2) := by rw [hrv, h0]; simp
      have hbit : (rev (n + 1 + 1) v).testBit (n + 1) = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hh]
        have : rev (n + 1) (v / 2) / 2 ^ (n + 1) = 0 := Nat.div_eq_of_lt hlt
        simp [this]
      have hv1 : rev (n + 1 + 1) (v + 1) = 2 ^ (n + 1) + rev (n + 1) (v / 2) := by
        rw [hrv]
        have : (v + 1) % 2 = 1 := by omega
        have : (v + 1) / 2 = v / 2 := by omega
        simp [*]
      refine ⟨fun _ => ⟨n + 1, Nat.le_refl _, ?_, ?_⟩, fun h1 => by omega⟩
      · simp [incrLoop, hbit]
      · rw [hv1, hh, Nat.mod_eq_of_lt hlt]
        omega
    · have hh : rev (n + 1 + 1) v = 2 ^ (n + 1) + rev (n + 1) (v / 2) := by rw [hrv, h0]; simp
      have hbit : (rev (n + 1 + 1) v).testBit (n + 1) = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hh]
        have : (2 ^ (n + 1) + rev (n + 1) (v / 2)) / 2 ^ (n + 1) = 1 := by
          rw [Nat.add_comm, Nat.add_div_right _ hP', Nat.div_eq_of_lt hlt]
        simp [this]
      have hmod : rev (n + 1 + 1) v % 2 ^ (n + 1) = rev (n + 1) (v / 2) := by
        rw [hh, Nat.add_comm, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hlt
      have hloop : incrLoop (rev (n + 1 + 1) v) (n + 1) = incrLoop (rev (n + 1) (v / 2)) n := by
        simp only [incrLoop, hbit, ite_true]
        rw [incrLoop_mod n (rev (n + 1 + 1) v), hmod]
      have hv1 : rev (n + 1 + 1) (v + 1) = rev (n + 1) (v / 2 + 1) := by
        rw [hrv]
        have : (v + 1) % 2 = 0 := by omega
        have : (v + 1) / 2 = v / 2 + 1 := by omega
        simp [*]
      refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · obtain ⟨e, he, h2, h3⟩ := ih.1 (by omega)
        refine ⟨e, by omega, by rw [hloop]; exact h2, ?_⟩
        rw [hv1, ← h3, hh]
        have hd : 2 ^ e ∣ 2 ^ (n + 1) := Nat.pow_dvd_pow 2 (by omega)
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.zero_add, Nat.mod_mod]
      · rw [hloop]; exact ih.2 (by omega)

/-! ## 4. Sorted Symbols, Cumulative Kraft Recurrence `Kc`, and Canonical Codes -/

section Model
variable (f : Nat → Nat) (n : Nat)

/-- Symbols below `k` of length `l`, in increasing order. -/
def fl (l k : Nat) : List Nat := (List.range k).filter (fun s => f s == l)

/-- Number of symbols below `n` of length `l` (`count[l]`). -/
def cnt (l : Nat) : Nat := (fl f l n).length

/-- Symbols below `n` sorted by `(length, symbol)` up to length `l`. -/
def wsAux : Nat → List Nat
  | 0 => []
  | l + 1 => wsAux l ++ fl f (l + 1) n

/-- Number of symbols of length in `1 .. l`. -/
def Tc : Nat → Nat
  | 0 => 0
  | l + 1 => Tc l + cnt f n (l + 1)

/-- Cumulative Kraft recurrence: `Kc l = ∑_{1 ≤ j ≤ l} cnt j * 2^(l - j)`.
`2^l - Kc l` corresponds to `left` after iteration `l` of the C validation loop. -/
def Kc : Nat → Nat
  | 0 => 0
  | l + 1 => 2 * Kc l + cnt f n (l + 1)

/-- `lens[work[i]]` after counting sort. -/
def lenAt (i : Nat) : Nat := f ((wsAux f n MAXBITS).getD i 0)

/-- Canonical code of the `i`-th sorted symbol (RFC 1951, §3.2.2). -/
def val (i : Nat) : Nat := 2 * Kc f n (lenAt f n i - 1) + (i - Tc f n (lenAt f n i - 1))

/-- Remaining codes of length `l` from index `i` onward. -/
def rem (i l : Nat) : Nat :=
  let a := Tc f n (l - 1)
  let b := Tc f n l
  if i ≤ a then b - a else if i < b then b - i else 0

/-- First `R` bits of the `j`-th code when `lenAt f n j ≥ R`. -/
def pre (R j : Nat) : Nat := val f n j / 2 ^ (lenAt f n j - R)

/-- Longest nonzero code length (`max` in `inflate_table`). -/
def mxl : Nat := lenAt f n (Tc f n MAXBITS - 1)

/-- Shortest nonzero code length (`min` in `inflate_table`). -/
def mnl : Nat := lenAt f n 0

end Model

/-- Kraft inequality up to `MAXBITS = 15`: no code length oversubscribes the code space. -/
def Fits (f : Nat → Nat) (n : Nat) : Prop := ∀ l, 1 ≤ l → l ≤ MAXBITS → Kc f n l ≤ 2 ^ l

/-- Complete Kraft code at `MAXBITS = 15`. -/
def Complete (f : Nat → Nat) (n : Nat) : Prop := Kc f n MAXBITS = 2 ^ MAXBITS

section ModelLemmas
variable {f : Nat → Nat} {n : Nat}

theorem fl_succ (t k : Nat) : fl f t (k + 1) = fl f t k ++ (if f k = t then [k] else []) := by
  unfold fl
  rw [List.range_succ, List.filter_append]
  by_cases h : f k = t <;> simp [h]

theorem cnt_step (t k : Nat) : cnt f (k + 1) t = cnt f k t + (if f k = t then 1 else 0) := by
  unfold cnt
  rw [fl_succ]
  by_cases h : f k = t <;> simp [h]

theorem cnt_le (t k : Nat) : cnt f k t ≤ k := by
  unfold cnt fl
  calc _ ≤ (List.range k).length := List.length_filter_le _ _
    _ = k := by simp

theorem cnt_mono {l k m : Nat} (h : k ≤ m) : cnt f k l ≤ cnt f m l := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    rw [← Nat.add_assoc, cnt_step]
    split <;> omega

theorem mem_fl {l k x : Nat} : x ∈ fl f l k ↔ x < k ∧ f x = l := by
  simp [fl]

theorem wsAux_length : ∀ l, (wsAux f n l).length = Tc f n l
  | 0 => rfl
  | l + 1 => by simp [wsAux, Tc, cnt, wsAux_length l]

theorem mem_wsAux : ∀ {l x}, x ∈ wsAux f n l ↔ x < n ∧ 1 ≤ f x ∧ f x ≤ l
  | 0, _ => by simp [wsAux]; omega
  | l + 1, _ => by
    simp only [wsAux, List.mem_append, mem_fl, mem_wsAux (l := l)]
    omega

theorem wsAux_split {l L : Nat} (h : l ≤ L) :
    ∃ rest, wsAux f n L = wsAux f n l ++ rest ∧ ∀ x ∈ rest, l < f x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ d ih =>
    obtain ⟨rest, h1, h2⟩ := ih (by omega)
    refine ⟨rest ++ fl f (l + d + 1) n, by simp [wsAux, h1], ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h2 x hx
    · have := (mem_fl.mp hx).2; omega

theorem Tc_step (k l : Nat) :
    Tc f (k + 1) l = Tc f k l + (if 1 ≤ f k ∧ f k ≤ l then 1 else 0) := by
  induction l with
  | zero => simp [Tc]; omega
  | succ l ih =>
    show Tc f (k + 1) l + cnt f (k + 1) (l + 1) = Tc f k l + cnt f k (l + 1) + _
    rw [ih, cnt_step]
    split <;> split <;> split <;> omega

theorem Tc_le (l : Nat) : ∀ k, Tc f k l ≤ k
  | 0 => by
    induction l with
    | zero => simp [Tc]
    | succ l ih => show Tc f 0 l + cnt f 0 (l + 1) ≤ 0; have := cnt_le (f := f) (l + 1) 0; omega
  | k + 1 => by
    have := Tc_le l k
    rw [Tc_step]
    split <;> omega

theorem Tc_mono {a b : Nat} (h : a ≤ b) : Tc f n a ≤ Tc f n b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    show Tc f n a ≤ Tc f n (a + d) + cnt f n (a + d + 1)
    omega

theorem Tc_succ' {l : Nat} (hl : 1 ≤ l) : Tc f n l = Tc f n (l - 1) + cnt f n l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp [Tc]

theorem Kc_succ' {l : Nat} (hl : 1 ≤ l) : Kc f n l = 2 * Kc f n (l - 1) + cnt f n l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp [Kc]

theorem Kc_mono {a b : Nat} (h : a ≤ b) : Kc f n a ≤ Kc f n b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    show Kc f n a ≤ 2 * Kc f n (a + d) + cnt f n (a + d + 1)
    omega

theorem Kc_gap : ∀ a d, Tc f n (a + d) = Tc f n a → Kc f n (a + d) = 2 ^ d * Kc f n a
  | _, 0, _ => by simp
  | a, d + 1, h => by
    have m1 := Tc_mono (f := f) (n := n) (show a ≤ a + d by omega)
    have e1 : Tc f n (a + (d + 1)) = Tc f n (a + d) + cnt f n (a + d + 1) := rfl
    rw [e1] at h
    have h1 : Tc f n (a + d) = Tc f n a := by omega
    have h2 : cnt f n (a + d + 1) = 0 := by omega
    have ih := Kc_gap a d h1
    have e2 : a + (d + 1) = a + d + 1 := by omega
    rw [e2]
    show 2 * Kc f n (a + d) + cnt f n (a + d + 1) = _
    rw [h2, ih, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    omega

theorem Kc_scaled_le {l L : Nat} (hl : l ≤ L) : Kc f n l * 2 ^ (L - l) ≤ Kc f n L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  induction d with
  | zero => simp
  | succ d ih =>
    have := ih (by omega)
    have e1 : l + (d + 1) = (l + d) + 1 := by omega
    rw [e1, show l + d + 1 - l = (l + d - l) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]
    show Kc f n l * 2 ^ (l + d - l) * 2 ≤ 2 * Kc f n (l + d) + cnt f n (l + d + 1)
    omega

/-- If `Kc f n 15 ≤ 2^15`, then `Fits f n` holds for all `1 ≤ l ≤ 15`. -/
theorem fits_of_Kc_max (h : Kc f n MAXBITS ≤ 2 ^ MAXBITS) : Fits f n := by
  intro l _ hl
  have hs := Nat.le_trans (Kc_scaled_le (f := f) (n := n) hl) h
  have hp : 2 ^ MAXBITS = 2 ^ l * 2 ^ (MAXBITS - l) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp] at hs
  exact Nat.le_of_mul_le_mul_right hs (Nat.two_pow_pos _)

/-- Correspondence with C's `left`: `left_l = 2^l - Kc l`. -/
theorem kraft_left_step (l : Nat) (leftPrev : Int)
    (hprev : leftPrev = (2 ^ l : Nat) - (Kc f n l : Int)) :
    2 * leftPrev - (cnt f n (l + 1) : Int) = (2 ^ (l + 1) : Nat) - (Kc f n (l + 1) : Int) := by
  rw [hprev]
  show 2 * ((2 ^ l : Nat) - (Kc f n l : Int)) - (cnt f n (l + 1) : Int) =
    (2 ^ (l + 1) : Nat) - ((2 * Kc f n l + cnt f n (l + 1) : Nat) : Int)
  rw [Nat.pow_succ]
  omega

theorem lenAt_le_iff {i l : Nat} (hl : l ≤ MAXBITS) (hi : i < Tc f n MAXBITS) :
    lenAt f n i ≤ l ↔ i < Tc f n l := by
  obtain ⟨rest, h1, h2⟩ := wsAux_split (f := f) (n := n) hl
  have hlen : (wsAux f n l).length = Tc f n l := wsAux_length l
  unfold lenAt
  rw [h1]
  by_cases hil : i < Tc f n l
  · have hi' : i < (wsAux f n l).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi', List.getElem?_eq_getElem hi']
    have hm := List.getElem_mem hi'
    have := (mem_wsAux.mp hm).2.2
    simp only [Option.getD_some]
    constructor <;> intro _ <;> omega
  · have hge : (wsAux f n l).length ≤ i := by omega
    have hi2 : i - (wsAux f n l).length < rest.length := by
      have := wsAux_length (f := f) (n := n) MAXBITS
      rw [h1, List.length_append] at this
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.getElem?_eq_getElem hi2]
    have hm := List.getElem_mem hi2
    have := h2 _ hm
    simp only [Option.getD_some]
    constructor <;> intro _ <;> omega

theorem lenAt_bounds {i : Nat} (hi : i < Tc f n MAXBITS) :
    1 ≤ lenAt f n i ∧ lenAt f n i ≤ MAXBITS := by
  have hlen : (wsAux f n MAXBITS).length = Tc f n MAXBITS := wsAux_length MAXBITS
  have hm := List.getElem_mem (show i < (wsAux f n MAXBITS).length by omega)
  have := mem_wsAux.mp hm
  unfold lenAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  omega

theorem lenAt_eq_iff {i l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ MAXBITS) (hi : i < Tc f n MAXBITS) :
    lenAt f n i = l ↔ Tc f n (l - 1) ≤ i ∧ i < Tc f n l := by
  have a := lenAt_le_iff (f := f) (n := n) hl hi
  have b := lenAt_le_iff (f := f) (n := n) (l := l - 1) (by omega) hi
  omega

theorem lenAt_mono {i j : Nat} (hij : i ≤ j) (hj : j < Tc f n MAXBITS) :
    lenAt f n i ≤ lenAt f n j := by
  have hi : i < Tc f n MAXBITS := by omega
  obtain ⟨_, b2⟩ := lenAt_bounds hj
  have b := lenAt_le_iff (f := f) (n := n) (l := lenAt f n j) b2 hi
  have c := lenAt_le_iff (f := f) (n := n) (l := lenAt f n j) b2 hj
  by_cases h : lenAt f n i ≤ lenAt f n j
  · exact h
  · exfalso
    have : ¬ i < Tc f n (lenAt f n j) := fun h' => h (b.mpr h')
    have := c.mp (Nat.le_refl _)
    omega

theorem mxl_bounds (hpos : 0 < Tc f n MAXBITS) : 1 ≤ mxl f n ∧ mxl f n ≤ MAXBITS :=
  lenAt_bounds (show Tc f n MAXBITS - 1 < Tc f n MAXBITS by omega)

theorem lenAt_le_mxl {i : Nat} (hi : i < Tc f n MAXBITS) : lenAt f n i ≤ mxl f n :=
  lenAt_mono (by omega) (by omega)

theorem mnl_le_lenAt {i : Nat} (hi : i < Tc f n MAXBITS) : mnl f n ≤ lenAt f n i :=
  lenAt_mono (Nat.zero_le i) hi

theorem mnl_bounds (hpos : 0 < Tc f n MAXBITS) : 1 ≤ mnl f n ∧ mnl f n ≤ MAXBITS :=
  lenAt_bounds hpos

theorem Tc_below_mnl (hpos : 0 < Tc f n MAXBITS) :
    ∀ l, l < mnl f n → Tc f n l = 0 ∧ Kc f n l = 0 := by
  have hminB : 1 ≤ mnl f n ∧ mnl f n ≤ MAXBITS := lenAt_bounds (f := f) (n := n) hpos
  intro l hl
  have hTc0 : Tc f n l = 0 := by
    apply Classical.byContradiction
    intro hne
    have h0 := (lenAt_le_iff (f := f) (n := n) (l := l) (by omega) hpos).mpr (by omega)
    change mnl f n ≤ l at h0
    omega
  have hKc0 : Kc f n l = 0 := by
    have := Kc_gap (f := f) (n := n) 0 l (by simpa [Tc] using hTc0)
    simpa [Kc] using this
  exact ⟨hTc0, hKc0⟩

/-- In any code, `Kc l * 2^mnl ≤ Tc l * 2^l`. For complete codes this bounds `2^mnl ≤ Tc 15 ≤ n`. -/
theorem Kc_mul_pow_mnl_le (hpos : 0 < Tc f n MAXBITS) :
    ∀ l, Kc f n l * 2 ^ mnl f n ≤ Tc f n l * 2 ^ l
  | 0 => by simp [Kc, Tc]
  | l + 1 => by
    have ih := Kc_mul_pow_mnl_le hpos l
    by_cases hlt : l + 1 < mnl f n
    · obtain ⟨hT, hK⟩ := Tc_below_mnl hpos (l + 1) hlt
      rw [hT, hK]
      simp
    · have hmn : mnl f n ≤ l + 1 := by omega
      have hpow : 2 ^ mnl f n ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by omega) hmn
      have hc : cnt f n (l + 1) * 2 ^ mnl f n ≤ cnt f n (l + 1) * 2 ^ (l + 1) :=
        Nat.mul_le_mul_left _ hpow
      have hk : Kc f n (l + 1) = 2 * Kc f n l + cnt f n (l + 1) := rfl
      have ht : Tc f n (l + 1) = Tc f n l + cnt f n (l + 1) := rfl
      rw [hk, ht, Nat.add_mul, Nat.add_mul, Nat.pow_succ]
      have h2 : (2 * Kc f n l) * 2 ^ mnl f n ≤ Tc f n l * (2 ^ l * 2) := by
        calc (2 * Kc f n l) * 2 ^ mnl f n
            = 2 * (Kc f n l * 2 ^ mnl f n) := by rw [Nat.mul_assoc]
          _ ≤ 2 * (Tc f n l * 2 ^ l) := Nat.mul_le_mul_left 2 ih
          _ = Tc f n l * (2 ^ l * 2) := by
            rw [← Nat.mul_assoc, Nat.mul_comm 2 (Tc f n l), Nat.mul_assoc, Nat.mul_comm 2 (2 ^ l)]
      exact Nat.add_le_add h2 hc

/-- For any complete code (`Kc 15 = 2^15`), `2 ^ mnl ≤ Tc 15 ≤ n`. -/
theorem pow_mnl_le_of_complete (hcomp : Complete f n) (hpos : 0 < Tc f n MAXBITS) :
    2 ^ mnl f n ≤ Tc f n MAXBITS ∧ Tc f n MAXBITS ≤ n := by
  have h1 := Kc_mul_pow_mnl_le hpos MAXBITS
  rw [hcomp, Nat.mul_comm (2 ^ MAXBITS) (2 ^ mnl f n)] at h1
  have hpos2 : 0 < 2 ^ MAXBITS := Nat.two_pow_pos _
  exact ⟨Nat.le_of_mul_le_mul_right h1 hpos2, Tc_le MAXBITS n⟩

theorem mnl_le_eight_of_complete_lens (hcomp : Complete f n) (hpos : 0 < Tc f n MAXBITS)
    (hn : n ≤ 288) : mnl f n ≤ 8 := by
  obtain ⟨hpow, htle⟩ := pow_mnl_le_of_complete hcomp hpos
  have hlt : 2 ^ mnl f n < 2 ^ 9 := by omega
  apply Classical.byContradiction
  intro hge
  have : 2 ^ 9 ≤ 2 ^ mnl f n := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem mnl_le_five_of_complete_dists (hcomp : Complete f n) (hpos : 0 < Tc f n MAXBITS)
    (hn : n ≤ 32) : mnl f n ≤ 5 := by
  obtain ⟨hpow, htle⟩ := pow_mnl_le_of_complete hcomp hpos
  have hle : 2 ^ mnl f n ≤ 2 ^ 5 := by omega
  apply Classical.byContradiction
  intro hge
  have : 2 ^ 6 ≤ 2 ^ mnl f n := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem val_lt_of_Fits (hfit : Fits f n) {i : Nat} (hi : i < Tc f n MAXBITS) :
    val f n i < 2 ^ lenAt f n i := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i) b1 b2 hi).mp rfl
  have hK := hfit (lenAt f n i) b1 b2
  rw [Kc_succ' b1] at hK
  unfold val
  have hT : Tc f n (lenAt f n i) = Tc f n (lenAt f n i - 1) + cnt f n (lenAt f n i) :=
    Tc_succ' b1
  omega

theorem val_succ {i : Nat} (hi : i + 1 < Tc f n MAXBITS) :
    val f n (i + 1) = (val f n i + 1) * 2 ^ (lenAt f n (i + 1) - lenAt f n i) := by
  have hi0 : i < Tc f n MAXBITS := by omega
  obtain ⟨a1, a2⟩ := lenAt_bounds (f := f) (n := n) hi0
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  have mono := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 by omega) hi
  by_cases heq : lenAt f n (i + 1) = lenAt f n i
  · have e0 : lenAt f n (i + 1) - lenAt f n i = 0 := by omega
    rw [e0, Nat.pow_zero, Nat.mul_one]
    unfold val
    rw [heq]
    have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i) a1 a2 hi0).mp rfl
    omega
  · have hlt : lenAt f n i < lenAt f n (i + 1) := by omega
    have blk0 := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i) a1 a2 hi0).mp rfl
    have blk1 := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n (i + 1)) b1 b2 hi).mp rfl
    have m0 := Tc_mono (f := f) (n := n) (show lenAt f n i ≤ lenAt f n (i + 1) - 1 by omega)
    have hTi : Tc f n (lenAt f n i) = i + 1 := by omega
    have hTgap : Tc f n (lenAt f n (i + 1) - 1) = Tc f n (lenAt f n i) := by omega
    obtain ⟨d, hd⟩ : ∃ d, lenAt f n (i + 1) - 1 = lenAt f n i + d :=
      ⟨lenAt f n (i + 1) - 1 - lenAt f n i, by omega⟩
    rw [hd] at hTgap
    have hK := Kc_gap (f := f) (n := n) (lenAt f n i) d hTgap
    rw [← hd] at hK
    have e1 : 2 * Kc f n (lenAt f n (i + 1) - 1) =
        2 ^ (d + 1) * Kc f n (lenAt f n i) := by
      rw [hK, Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have ed : d + 1 = lenAt f n (i + 1) - lenAt f n i := by omega
    rw [ed] at e1
    unfold val
    have hidx : i + 1 - Tc f n (lenAt f n (i + 1) - 1) = 0 := by
      rw [hd, hTgap, hTi]; omega
    rw [hidx, Nat.add_zero, e1]
    have hKc : Kc f n (lenAt f n i) = 2 * Kc f n (lenAt f n i - 1) + cnt f n (lenAt f n i) :=
      Kc_succ' a1
    have hTc : Tc f n (lenAt f n i) = Tc f n (lenAt f n i - 1) + cnt f n (lenAt f n i) :=
      Tc_succ' a1
    have hc : i - Tc f n (lenAt f n i - 1) + 1 = cnt f n (lenAt f n i) := by omega
    rw [hKc, ← hc, Nat.mul_comm]
    congr 1

theorem val_last_of_Complete (hc : Complete f n) {m : Nat} (hm : Tc f n MAXBITS = m + 1) :
    val f n m + 1 = 2 ^ lenAt f n m := by
  have hi : m < Tc f n MAXBITS := by omega
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi
  obtain ⟨blk1, _⟩ := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n m) b1 b2 hi).mp rfl
  have hT : Tc f n (lenAt f n m + (MAXBITS - lenAt f n m)) = Tc f n (lenAt f n m) := by
    have h1 := Tc_mono (f := f) (n := n) (show lenAt f n m ≤ MAXBITS by omega)
    have : lenAt f n m + (MAXBITS - lenAt f n m) = MAXBITS := by omega
    rw [this]; omega
  have hK := Kc_gap (f := f) (n := n) (lenAt f n m) (MAXBITS - lenAt f n m) hT
  have e : lenAt f n m + (MAXBITS - lenAt f n m) = MAXBITS := by omega
  rw [e, hc] at hK
  have ep : 2 ^ MAXBITS = 2 ^ (MAXBITS - lenAt f n m) * 2 ^ lenAt f n m := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [ep] at hK
  have hKe : Kc f n (lenAt f n m) = 2 ^ lenAt f n m :=
    Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) hK.symm
  rw [Kc_succ' b1] at hKe
  have hTc : Tc f n (lenAt f n m) = Tc f n (lenAt f n m - 1) + cnt f n (lenAt f n m) :=
    Tc_succ' b1
  have hTm : Tc f n (lenAt f n m) = m + 1 := by
    have h1 := Tc_mono (f := f) (n := n) (show lenAt f n m ≤ MAXBITS by omega)
    have blk2 := ((lenAt_eq_iff (f := f) (n := n) (l := lenAt f n m) b1 b2 hi).mp rfl).2
    omega
  unfold val
  have hcnt : cnt f n (lenAt f n m) = m + 1 - Tc f n (lenAt f n m - 1) := by omega
  rw [hcnt] at hKe
  omega

theorem val_zero (h : 0 < Tc f n MAXBITS) : val f n 0 = 0 := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) h
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n 0) b1 b2 h).mp rfl
  have hT : Tc f n (0 + (lenAt f n 0 - 1)) = Tc f n 0 := by
    have : Tc f n 0 = 0 := rfl
    simp only [Nat.zero_add]; omega
  have hK := Kc_gap (f := f) (n := n) 0 (lenAt f n 0 - 1) hT
  have hK0 : Kc f n 0 = 0 := rfl
  rw [hK0, Nat.mul_zero] at hK
  unfold val
  simp only [Nat.zero_add] at hK
  rw [hK]
  omega

theorem pre_lt (hfit : Fits f n) {R j : Nat} (hj : j < Tc f n MAXBITS) (hR : R ≤ lenAt f n j) :
    pre f n R j < 2 ^ R := by
  unfold pre
  have hv := val_lt_of_Fits hfit hj
  have e : 2 ^ lenAt f n j = 2 ^ R * 2 ^ (lenAt f n j - R) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e] at hv
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr hv

theorem huff_step (hfit : Fits f n) {i : Nat} (hi : i + 1 < Tc f n MAXBITS) :
    ∃ e, e < lenAt f n i ∧ incrLoop (rev (lenAt f n i) (val f n i)) (lenAt f n i - 1) = 2 ^ e ∧
      rev (lenAt f n i) (val f n i) % 2 ^ e + 2 ^ e = rev (lenAt f n (i + 1)) (val f n (i + 1)) := by
  have hi0 : i < Tc f n MAXBITS := by omega
  obtain ⟨b1, _⟩ := lenAt_bounds (f := f) (n := n) hi0
  have mono := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 by omega) hi
  have hs := val_succ (f := f) (n := n) hi
  have hl := val_lt_of_Fits hfit hi
  generalize lenAt f n (i + 1) = ℓ' at *
  generalize val f n (i + 1) = v' at *
  generalize hl0 : lenAt f n i = ℓ at *
  generalize hv0 : val f n i = v at *
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨Δ, rfl⟩ : ∃ Δ, ℓ' = k + 1 + Δ := ⟨ℓ' - (k + 1), by omega⟩
  have e1 : k + 1 + Δ - (k + 1) = Δ := by omega
  rw [e1] at hs
  have hvlt : v < 2 ^ (k + 1) := by
    have := val_lt_of_Fits hfit hi0
    rw [hl0, hv0] at this
    exact this
  have hlt2 : (v + 1) * 2 ^ Δ < 2 ^ (k + 1) * 2 ^ Δ := by
    rw [← hs, ← Nat.pow_add]; exact hl
  have hv1 : v + 1 < 2 ^ (k + 1) := Nat.lt_of_mul_lt_mul_right hlt2
  obtain ⟨e, he, h1, h2⟩ := (succ_rev k v hvlt).1 hv1
  refine ⟨e, by omega, ?_, ?_⟩
  · simpa using h1
  · rw [h2, hs, rev_mul_pow]

theorem huff_last (hc : Complete f n) {m : Nat} (hm : Tc f n MAXBITS = m + 1) :
    incrLoop (rev (lenAt f n m) (val f n m)) (lenAt f n m - 1) = 0 := by
  have hi : m < Tc f n MAXBITS := by omega
  obtain ⟨b1, _⟩ := lenAt_bounds (f := f) (n := n) hi
  have hl := val_last_of_Complete hc hm
  generalize lenAt f n m = ℓ at *
  generalize val f n m = v at *
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have := (succ_rev k v (by omega)).2 (by omega)
  simpa using this

theorem huff_low {R j : Nat} (hR : R ≤ lenAt f n j) :
    rev (lenAt f n j) (val f n j) % 2 ^ R = rev R (pre f n R j) := by
  unfold pre
  have h := rev_mod_pow (lenAt f n j - R) R (val f n j)
  rwa [Nat.add_sub_cancel' hR] at h

theorem rev_split_huff {R j : Nat} (hR : R ≤ lenAt f n j) :
    rev (lenAt f n j) (val f n j) =
      rev R (pre f n R j) + 2 ^ R * (rev (lenAt f n j) (val f n j) / 2 ^ R) := by
  have h := huff_low (f := f) (n := n) (R := R) (j := j) hR
  have := Nat.mod_add_div (rev (lenAt f n j) (val f n j)) (2 ^ R)
  omega

/-- A new root prefix at `i + 1` starts at an aligned canonical code (`val % 2^(len - R) = 0`). -/
theorem align_succ {R i : Nat} (hi : i + 1 < Tc f n MAXBITS) (hR : R < lenAt f n (i + 1))
    (hnew : lenAt f n i ≤ R ∨ (R < lenAt f n i ∧ pre f n R (i + 1) ≠ pre f n R i)) :
    val f n (i + 1) % 2 ^ (lenAt f n (i + 1) - R) = 0 := by
  have hi0 : i < Tc f n MAXBITS := by omega
  obtain ⟨_, _⟩ := lenAt_bounds (f := f) (n := n) hi0
  have mono := lenAt_mono (f := f) (n := n) (show i ≤ i + 1 by omega) hi
  have hs := val_succ (f := f) (n := n) hi
  unfold pre at hnew
  generalize lenAt f n (i + 1) = ℓ' at *
  generalize val f n (i + 1) = v' at *
  generalize lenAt f n i = ℓ at *
  generalize val f n i = v at *
  obtain ⟨Δ, rfl⟩ : ∃ Δ, ℓ' = ℓ + Δ := ⟨ℓ' - ℓ, by omega⟩
  have e1 : ℓ + Δ - ℓ = Δ := by omega
  rw [e1] at hs
  rcases hnew with h | h
  · have hle : ℓ + Δ - R ≤ Δ := Nat.sub_le_of_le_add (by omega)
    rw [hs]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hle) _)
  · obtain ⟨hℓ, hne⟩ := h
    have e2 : ℓ + Δ - R = Δ + (ℓ - R) := by omega
    have hq : (v + 1) * 2 ^ Δ / 2 ^ (ℓ + Δ - R) = (v + 1) / 2 ^ (ℓ - R) := by
      rw [e2, Nat.pow_add, Nat.mul_comm (2 ^ Δ) (2 ^ (ℓ - R))]
      exact Nat.mul_div_mul_right _ _ (Nat.pow_pos (by omega))
    rw [hs, hq] at hne
    have hcr : (v + 1) % 2 ^ (ℓ - R) = 0 := by
      apply Classical.byContradiction
      intro hne0
      apply hne
      have hP : 0 < 2 ^ (ℓ - R) := Nat.pow_pos (by omega)
      have hv1 := Nat.div_add_mod v (2 ^ (ℓ - R))
      have hv2 := Nat.div_add_mod (v + 1) (2 ^ (ℓ - R))
      have hr0 := Nat.mod_lt v hP
      have hr1 := Nat.mod_lt (v + 1) hP
      generalize 2 ^ (ℓ - R) = P at *
      rcases Nat.lt_trichotomy ((v + 1) / P) (v / P) with hlt2 | heq | hgt
      · have := Nat.mul_le_mul_left P (show (v + 1) / P + 1 ≤ v / P by omega)
        rw [Nat.mul_succ] at this; omega
      · exact heq
      · have := Nat.mul_le_mul_left P (show v / P + 1 ≤ (v + 1) / P by omega)
        rw [Nat.mul_succ] at this; omega
    rw [hs, e2, Nat.pow_add]
    apply Nat.mod_eq_zero_of_dvd
    have hdvd := Nat.mul_dvd_mul (Nat.dvd_of_mod_eq_zero hcr) (Nat.dvd_refl (2 ^ Δ))
    rw [Nat.mul_comm (2 ^ Δ) (2 ^ (ℓ - R))]
    exact hdvd

theorem rem_init {l : Nat} (hl1 : 1 ≤ l) : rem f n 0 l = cnt f n l := by
  have ht := Tc_succ' (f := f) (n := n) hl1
  unfold rem
  simp [Nat.zero_le, ht]

theorem rem_succ {i l : Nat} (hl1 : 1 ≤ l) (hl : l ≤ MAXBITS) (hi : i < Tc f n MAXBITS) :
    rem f n (i + 1) l = rem f n i l - (if lenAt f n i = l then 1 else 0) := by
  have a := lenAt_eq_iff (f := f) (n := n) (l := l) hl1 hl hi
  have m1 := Tc_mono (f := f) (n := n) (show l - 1 ≤ l by omega)
  unfold rem
  dsimp only
  by_cases h : lenAt f n i = l
  · obtain ⟨h1, h2⟩ := a.mp h
    rw [ite_eq_left h, ite_eq_right (by omega)]
    by_cases hle : i ≤ Tc f n (l - 1)
    · have heq : i = Tc f n (l - 1) := by omega
      rw [heq, ite_eq_left (Nat.le_refl _)]
      by_cases hlt : Tc f n (l - 1) + 1 < Tc f n l
      · rw [ite_eq_left hlt]; omega
      · rw [ite_eq_right hlt]; omega
    · rw [ite_eq_right hle, ite_eq_left h2]
      by_cases hlt : i + 1 < Tc f n l
      · rw [ite_eq_left hlt]; omega
      · rw [ite_eq_right hlt]; omega
  · rw [ite_eq_right h, Nat.sub_zero]
    have hnot : ¬ (Tc f n (l - 1) ≤ i ∧ i < Tc f n l) := fun hh => h (a.mpr hh)
    by_cases hlt : i < Tc f n (l - 1)
    · have hle1 : i + 1 ≤ Tc f n (l - 1) := by omega
      have hle2 : i ≤ Tc f n (l - 1) := by omega
      rw [ite_eq_left hle1, ite_eq_left hle2]
    · by_cases heq : i = Tc f n (l - 1)
      · have hTeq : Tc f n l = Tc f n (l - 1) := by omega
        have hlt1 : ¬ (i + 1 ≤ Tc f n (l - 1)) := by omega
        have hlt2 : ¬ (i + 1 < Tc f n l) := by omega
        rw [ite_eq_right hlt1, ite_eq_right hlt2, ite_eq_left (by omega), hTeq, Nat.sub_self]
      · have hge : Tc f n l ≤ i := by omega
        rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega)]

end ModelLemmas

/-! ## 5. Parametric Subtable Sizing (`root`, `drop`, `curr`) & Width Bounds -/

section Sizing
variable {f : Nat → Nat} {n : Nat}

/-- Models `while (curr + drop < mx) { left -= count[curr + drop]; if (left <= 0) break; curr++; left <<= 1; }`. -/
def sizeLoop (r : Nat → Nat) (R mx : Nat) : Nat → Nat → Int → Nat × Int
  | 0, curr, left => (curr, left)
  | k + 1, curr, left =>
    if R + curr < mx then
      if left - (r (R + curr) : Int) ≤ 0 then (curr, left - (r (R + curr) : Int))
      else sizeLoop r R mx k (curr + 1) ((left - (r (R + curr) : Int)) * 2)
    else (curr, left)

/-- Subtable sizing loop started at `curr` with exact fuel `mx - R - curr`. -/
def SL (r : Nat → Nat) (R mx curr : Nat) (left : Int) : Nat × Int :=
  sizeLoop r R mx (mx - R - curr) curr left

theorem SL_lt {r : Nat → Nat} {R mx curr : Nat} {left : Int} (h : R + curr < mx) :
    SL r R mx curr left =
      (if left - (r (R + curr) : Int) ≤ 0 then (curr, left - (r (R + curr) : Int))
       else SL r R mx (curr + 1) ((left - (r (R + curr) : Int)) * 2)) := by
  obtain ⟨k, hk⟩ : ∃ k, mx - R - curr = k + 1 := ⟨mx - R - curr - 1, by omega⟩
  have hk2 : mx - R - (curr + 1) = k := by omega
  unfold SL
  rw [hk, hk2]
  simp only [sizeLoop, h, ite_true]

theorem SL_ge {r : Nat → Nat} {R mx curr : Nat} {left : Int} (h : mx ≤ R + curr) :
    SL r R mx curr left = (curr, left) := by
  have : mx - R - curr = 0 := by omega
  unfold SL
  rw [this]
  simp only [sizeLoop]

theorem sizeLoop_spec (r N : Nat → Nat) (R mx p d0 : Nat)
    (hN : ∀ d, d0 ≤ d → N (d + 1) = 2 * (N d + r d)) :
    ∀ k curr left, d0 ≤ R + curr → R + curr ≤ mx → mx - (R + curr) ≤ k →
      left = ((p + 1) * 2 ^ curr : Nat) - (N (R + curr) : Int) →
      curr ≤ (sizeLoop r R mx k curr left).1 ∧ R + (sizeLoop r R mx k curr left).1 ≤ mx ∧
      (R + (sizeLoop r R mx k curr left).1 = mx ∨
        (p + 1) * 2 ^ (sizeLoop r R mx k curr left).1 ≤
          N (R + (sizeLoop r R mx k curr left).1) + r (R + (sizeLoop r R mx k curr left).1))
  | 0, curr, left, _, h1, h2, _ => by simp only [sizeLoop]; omega
  | k + 1, curr, left, h0, h1, h2, h3 => by
    simp only [sizeLoop]
    by_cases hc : R + curr < mx
    · simp only [hc, ite_true]
      by_cases hb : left - (r (R + curr) : Int) ≤ 0
      · simp only [hb, ite_true]
        refine ⟨Nat.le_refl _, h1, Or.inr ?_⟩
        rw [h3] at hb
        omega
      · simp only [hb, ite_false]
        have := sizeLoop_spec r N R mx p d0 hN k (curr + 1) ((left - (r (R + curr) : Int)) * 2)
          (by omega) (by omega) (by omega) (by
            have e : R + (curr + 1) = (R + curr) + 1 := by omega
            rw [e, hN _ h0, h3, Nat.pow_succ]
            have heq1 : ((p + 1) * (2 ^ curr * 2) : Nat) = ((p + 1) * 2 ^ curr : Nat) * 2 := by
              rw [← Nat.mul_assoc]
            rw [heq1]
            omega)
        omega
    · simp only [hc, ite_false]
      omega

/-- Subtable width `curr` chosen when symbol `i0` opens a subtable with root `R`. -/
def currOf (f : Nat → Nat) (n R i0 : Nat) : Nat :=
  (SL (rem f n i0) R (mxl f n) (lenAt f n i0 - R) ((2 ^ (lenAt f n i0 - R) : Nat) : Int)).1

/-- Parametric subtable width bound: `len i0 ≤ R + curr`, `R + curr ≤ mxl ≤ MAXBITS`
(hence `curr ≤ MAXBITS - R`), and every symbol in the same root prefix fits. -/
theorem block_bound {R i0 : Nat} (hi0 : i0 < Tc f n MAXBITS) (hR : R < lenAt f n i0)
    (halign : val f n i0 % 2 ^ (lenAt f n i0 - R) = 0) :
    lenAt f n i0 ≤ R + currOf f n R i0 ∧ R + currOf f n R i0 ≤ mxl f n ∧
    currOf f n R i0 ≤ MAXBITS - R ∧
    ∀ j, j < Tc f n MAXBITS → R < lenAt f n j → pre f n R j = pre f n R i0 →
      lenAt f n j ≤ R + currOf f n R i0 := by
  obtain ⟨b1, b2⟩ := lenAt_bounds (f := f) (n := n) hi0
  have hm : 0 < Tc f n MAXBITS := by omega
  have hmxB := mxl_bounds (f := f) (n := n) hm
  have hmx : lenAt f n i0 ≤ mxl f n :=
    lenAt_mono (f := f) (n := n) (show i0 ≤ Tc f n MAXBITS - 1 by omega) (by omega)
  have blk := (lenAt_eq_iff (f := f) (n := n) (l := lenAt f n i0) b1 b2 hi0).mp rfl
  let N : Nat → Nat := fun d =>
    if d < lenAt f n i0 then 0
    else 2 * Kc f n (d - 1) + (if d = lenAt f n i0 then i0 - Tc f n (lenAt f n i0 - 1) else 0)
  have hNgt : ∀ d, lenAt f n i0 < d → N d = 2 * Kc f n (d - 1) := by
    intro d hd
    dsimp only [N]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_zero]
  have hN : ∀ d, lenAt f n i0 ≤ d → N (d + 1) = 2 * (N d + rem f n i0 d) := by
    intro d hd
    have hc : lenAt f n i0 < d + 1 := by omega
    rw [hNgt (d + 1) hc, show d + 1 - 1 = d by omega]
    by_cases he : d = lenAt f n i0
    · subst he
      have hNd : N (lenAt f n i0) = val f n i0 := by
        dsimp only [N]
        rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
        rfl
      have hrem : rem f n i0 (lenAt f n i0) = Tc f n (lenAt f n i0) - i0 := by
        unfold rem; dsimp only
        by_cases hle0 : i0 ≤ Tc f n (lenAt f n i0 - 1)
        · have heq : i0 = Tc f n (lenAt f n i0 - 1) := by have := blk.1; omega
          rw [ite_eq_left hle0]; omega
        · rw [ite_eq_right hle0, ite_eq_left blk.2]
      rw [hNd, hrem, Kc_succ' b1]
      have hTc := Tc_succ' (f := f) (n := n) b1
      have hle1 : Tc f n (lenAt f n i0 - 1) ≤ i0 := blk.1
      have hlt2 : i0 < Tc f n (lenAt f n i0) := blk.2
      have hval_eq : val f n i0 = 2 * Kc f n (lenAt f n i0 - 1) + (i0 - Tc f n (lenAt f n i0 - 1)) := rfl
      rw [hval_eq]
      omega
    · have hlt : lenAt f n i0 < d := by omega
      rw [hNgt d hlt]
      have hd1 : 1 ≤ d := by omega
      have hTc1 := Tc_mono (f := f) (n := n) (show lenAt f n i0 ≤ d - 1 by omega)
      have hrem : rem f n i0 d = cnt f n d := by
        unfold rem; dsimp only
        rw [ite_eq_left (by omega), Tc_succ' hd1]; omega
      rw [hrem, Kc_succ' hd1]
  let p := pre f n R i0
  have hNp : N (lenAt f n i0) = p * 2 ^ (lenAt f n i0 - R) := by
    have hNd : N (lenAt f n i0) = val f n i0 := by
      dsimp only [N]
      rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
      rfl
    rw [hNd]
    have hdm := Nat.div_add_mod (val f n i0) (2 ^ (lenAt f n i0 - R))
    rw [halign, Nat.add_zero] at hdm
    rw [Nat.mul_comm] at hdm
    exact hdm.symm
  have hs := sizeLoop_spec (rem f n i0) N R (mxl f n) p (lenAt f n i0) hN
    (mxl f n - R - (lenAt f n i0 - R)) (lenAt f n i0 - R)
    ((2 ^ (lenAt f n i0 - R) : Nat) : Int)
    (by omega) (by omega) (by omega) (by
      rw [show R + (lenAt f n i0 - R) = lenAt f n i0 by omega, hNp, Nat.add_mul, Nat.one_mul]
      omega)
  change lenAt f n i0 - R ≤ currOf f n R i0 ∧ R + currOf f n R i0 ≤ mxl f n ∧
      (R + currOf f n R i0 = mxl f n ∨
        (p + 1) * 2 ^ currOf f n R i0 ≤ N (R + currOf f n R i0) + rem f n i0 (R + currOf f n R i0)) at hs
  have hc1 : lenAt f n i0 ≤ R + currOf f n R i0 := by omega
  have hc2 : R + currOf f n R i0 ≤ mxl f n := hs.2.1
  have hc_max : currOf f n R i0 ≤ MAXBITS - R := by omega
  refine ⟨hc1, hc2, hc_max, ?_⟩
  intro j hj hRj hpj
  apply Classical.byContradiction
  intro hcon
  have hgt : R + currOf f n R i0 < lenAt f n j := by omega
  rcases hs.2.2 with heq | hle
  · have := lenAt_le_mxl hj; omega
  · have hgrow : ∀ t, (p + 1) * 2 ^ (currOf f n R i0 + 1 + t) ≤ N (R + currOf f n R i0 + 1 + t) := by
      intro t
      induction t with
      | zero =>
        have hstep := hN (R + currOf f n R i0) (by omega)
        have hpow : (p + 1) * 2 ^ (currOf f n R i0 + 1 + 0) = 2 * ((p + 1) * 2 ^ currOf f n R i0) := by
          rw [Nat.add_zero, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm ((p + 1) * 2 ^ currOf f n R i0) 2]
        rw [Nat.add_zero, hstep, hpow]
        omega
      | succ t ih =>
        have hstep := hN (R + currOf f n R i0 + 1 + t) (by omega)
        have e1 : R + currOf f n R i0 + 1 + (t + 1) = (R + currOf f n R i0 + 1 + t) + 1 := by omega
        have hpow : (p + 1) * 2 ^ (currOf f n R i0 + 1 + (t + 1)) =
            2 * ((p + 1) * 2 ^ (currOf f n R i0 + 1 + t)) := by
          rw [show currOf f n R i0 + 1 + (t + 1) = (currOf f n R i0 + 1 + t) + 1 by omega,
            Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm ((p + 1) * 2 ^ (currOf f n R i0 + 1 + t)) 2]
        rw [e1, hstep, hpow]
        omega
    have hg := hgrow (lenAt f n j - (R + currOf f n R i0) - 1)
    have e3 : R + currOf f n R i0 + 1 + (lenAt f n j - (R + currOf f n R i0) - 1) = lenAt f n j := by omega
    have e4 : currOf f n R i0 + 1 + (lenAt f n j - (R + currOf f n R i0) - 1) = lenAt f n j - R := by omega
    rw [e3, e4] at hg
    have hNj : N (lenAt f n j) = 2 * Kc f n (lenAt f n j - 1) := hNgt _ (by omega)
    have hvj : 2 * Kc f n (lenAt f n j - 1) ≤ val f n j := by unfold val; omega
    have hge : (p + 1) * 2 ^ (lenAt f n j - R) ≤ val f n j := by omega
    have hdiv : p + 1 ≤ val f n j / 2 ^ (lenAt f n j - R) :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hge
    have hprej : pre f n R j = val f n j / 2 ^ (lenAt f n j - R) := rfl
    have hprei : p = pre f n R i0 := rfl
    rw [← hprej, hpj, ← hprei] at hdiv
    exact Nat.not_succ_le_self p hdiv

/-- General parametric subtable size bound: `2^curr ≤ 2^(MAXBITS - R)`. -/
theorem subtable_size_le {R curr : Nat} (h : curr ≤ MAXBITS - R) :
    2 ^ curr ≤ 2 ^ (MAXBITS - R) :=
  Nat.pow_le_pow_right (by omega) h

theorem subtable_size_lenbits {R curr : Nat} (hR : R = LENBITS) (h : curr ≤ MAXBITS - R) :
    curr ≤ 5 ∧ 2 ^ curr ≤ 32 := by
  subst hR
  have hc : curr ≤ 5 := by unfold MAXBITS LENBITS at h; omega
  exact ⟨hc, Nat.pow_le_pow_right (by omega) hc⟩

theorem subtable_size_distbits {R curr : Nat} (hR : R = DISTBITS) (h : curr ≤ MAXBITS - R) :
    curr ≤ 7 ∧ 2 ^ curr ≤ 128 := by
  subst hR
  have hc : curr ≤ 7 := by unfold MAXBITS DISTBITS at h; omega
  exact ⟨hc, Nat.pow_le_pow_right (by omega) hc⟩

end Sizing

/-! ## 6. Root Clamping & Guarded Table-Allocation Bounds -/

/-- Root width after `if (root > max) root = max; if (root < min) root = min;`. -/
def clampRoot (bits minL maxL : Nat) : Nat :=
  let r := if bits > maxL then maxL else bits
  if r < minL then minL else r

theorem clampRoot_bounds {bits minL maxL : Nat} (h1 : 1 ≤ minL) (h2 : minL ≤ maxL)
    (h3 : maxL ≤ MAXBITS) :
    1 ≤ clampRoot bits minL maxL ∧ minL ≤ clampRoot bits minL maxL ∧
    clampRoot bits minL maxL ≤ maxL ∧ clampRoot bits minL maxL ≤ MAXBITS := by
  unfold clampRoot
  dsimp only
  split <;> split <;> omega

theorem clampRoot_codes {bits minL maxL : Nat} (hb : 7 ≤ bits) (_h1 : 1 ≤ minL)
    (h2 : minL ≤ maxL) (h3 : maxL ≤ 7) :
    clampRoot bits minL maxL = maxL ∧ 2 ^ clampRoot bits minL maxL ≤ CODES_CAP := by
  unfold clampRoot
  dsimp only
  have heq : (if bits > maxL then maxL else bits) = maxL := by
    split <;> omega
  rw [heq, ite_eq_right (by omega)]
  exact ⟨rfl, Nat.le_trans (Nat.pow_le_pow_right (by omega) h3) (by decide)⟩

theorem clampRoot_le_of_min {bits minL maxL R0 : Nat} (hb : bits ≤ R0) (hmin : minL ≤ R0) :
    clampRoot bits minL maxL ≤ R0 := by
  unfold clampRoot
  dsimp only
  split <;> split <;> omega

theorem clampRoot_lenbits_fit {f : Nat → Nat} {n : Nat} (hcomp : Complete f n) (hpos : 0 < Tc f n MAXBITS)
    (hn : n ≤ 288) :
    clampRoot LENBITS (mnl f n) (mxl f n) ≤ LENBITS ∧
    2 ^ clampRoot LENBITS (mnl f n) (mxl f n) ≤ ENOUGH_LENS := by
  have hm := mnl_le_eight_of_complete_lens hcomp hpos hn
  have hr := clampRoot_le_of_min (bits := LENBITS) (minL := mnl f n) (maxL := mxl f n)
    (R0 := LENBITS) (Nat.le_refl _) (by unfold LENBITS; omega)
  refine ⟨hr, ?_⟩
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) hr) lenbits_root_fit

theorem clampRoot_distbits_fit {f : Nat → Nat} {n : Nat} (hcomp : Complete f n) (hpos : 0 < Tc f n MAXBITS)
    (hn : n ≤ 32) :
    clampRoot DISTBITS (mnl f n) (mxl f n) ≤ DISTBITS ∧
    2 ^ clampRoot DISTBITS (mnl f n) (mxl f n) ≤ ENOUGH_DISTS := by
  have hm := mnl_le_five_of_complete_dists hcomp hpos hn
  have hr := clampRoot_le_of_min (bits := DISTBITS) (minL := mnl f n) (maxL := mxl f n)
    (R0 := DISTBITS) (Nat.le_refl _) (by unfold DISTBITS; omega)
  refine ⟨hr, ?_⟩
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) hr) distbits_root_fit

/-- `used += 1U << curr` never wraps `uint32` before the `used > ENOUGH_*` check,
whenever prior `used ≤ ENOUGH_LENS` and `curr < MAXBITS`. -/
theorem used_step_no_overflow {used curr : Nat} (hu : used ≤ ENOUGH_LENS)
    (hc : curr ≤ MAXBITS - 1) :
    used + 2 ^ curr ≤ ENOUGH_LENS + 2 ^ 14 ∧ used + 2 ^ curr < 2 ^ 16 ∧ used + 2 ^ curr < 2 ^ 32 := by
  have hpow : 2 ^ curr ≤ 2 ^ 14 := Nat.pow_le_pow_right (by omega) (by unfold MAXBITS at hc; omega)
  have hu2 : used + 2 ^ curr ≤ ENOUGH_LENS + 2 ^ 14 := by omega
  unfold ENOUGH_LENS at hu2
  omega

/-- Guarded subtable advance: if `nextOff + 2^currPrev = usedPrev` and `usedPrev + 2^curr ≤ cap`,
then `nextOff' = nextOff + 2^currPrev = usedPrev`, `nextOff' + 2^curr ≤ cap`, and `nextOff' < 2^16`. -/
theorem guarded_next_advance {nextOff currPrev usedPrev curr cap : Nat}
    (hprev : nextOff + 2 ^ currPrev = usedPrev)
    (hcap : usedPrev + 2 ^ curr ≤ cap) (hcap16 : cap < 2 ^ 16) :
    let nextOff' := nextOff + 2 ^ currPrev
    nextOff' + 2 ^ curr ≤ cap ∧ nextOff' < cap ∧ nextOff' < 2 ^ 16 := by
  have hpos := Nat.two_pow_pos curr
  omega

/-- Every write `next[(huff >> drop) + fill]` stays inside `[nextOff, nextOff + 2^curr) ⊆ [0, cap)`. -/
theorem write_idx_bounds {nextOff hd len drop curr m cap : Nat}
    (hle : len - drop ≤ curr)
    (hhd : hd < 2 ^ (len - drop))
    (hm : m < 2 ^ (curr - (len - drop)))
    (hroom : nextOff + 2 ^ curr ≤ cap) :
    hd + m * 2 ^ (len - drop) < 2 ^ curr ∧ nextOff + (hd + m * 2 ^ (len - drop)) < cap := by
  have h1 : m + 1 ≤ 2 ^ (curr - (len - drop)) := hm
  have hmul : (m + 1) * 2 ^ (len - drop) ≤ 2 ^ curr := by
    calc (m + 1) * 2 ^ (len - drop) ≤ 2 ^ (curr - (len - drop)) * 2 ^ (len - drop) :=
          Nat.mul_le_mul_right _ h1
      _ = 2 ^ curr := by rw [← Nat.pow_add]; congr 1; omega
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have hloc : hd + m * 2 ^ (len - drop) < 2 ^ curr := by omega
  exact ⟨hloc, by omega⟩

/-- Mask & low-bit bounds for `mask = (1U << root) - 1`. -/
theorem mask_and_mod_lt (h root : Nat) :
    h &&& (2 ^ root - 1) = h % 2 ^ root ∧ h % 2 ^ root < 2 ^ root := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact ⟨rfl, Nat.mod_lt h (Nat.two_pow_pos root)⟩

/-- Sequential `LENS` followed by `DISTS` inside `state->codes[ENOUGH]` (`ENOUGH = 1732`). -/
theorem sequential_lens_dists_room {usedLens : Nat} (hlens : usedLens ≤ ENOUGH_LENS) :
    usedLens + ENOUGH_DISTS ≤ ENOUGH := by
  unfold ENOUGH ENOUGH_LENS ENOUGH_DISTS at *
  omega

/-! ## 7. List-Model Descriptor Layout & Prefix Geometry -/

/-- Symbols of length `l` in increasing order. -/
def symsOf (ls : List Nat) (l : Nat) : List Nat :=
  (List.range ls.length).filter fun s => ls.getD s 0 == l

/-- Number of symbols with nonzero length `< l`. -/
def offL (ls : List Nat) (l : Nat) : Nat :=
  ((List.range l).map fun l' => if l' = 0 then 0 else ls.count l').sum

/-- Allocation order: lengths `1 .. 15`, increasing symbol within a length. -/
def ord (ls : List Nat) : List Nat :=
  (List.range MAXBITS).flatMap fun i => symsOf ls (i + 1)

/-- Total number of coded (nonzero-length) symbols. -/
def nz (ls : List Nat) : Nat := (ord ls).length

/-- `j`-th symbol in allocation order. -/
def sy (ls : List Nat) (j : Nat) : Nat := (ord ls).getD j 0

/-- Length of the `j`-th symbol in allocation order. -/
def L (ls : List Nat) (j : Nat) : Nat := ls.getD (sy ls j) 0

/-- Cumulative Kraft sum scaled by `2^15` at allocation index `j`. -/
def K (ls : List Nat) (j : Nat) : Nat := ((List.range j).map fun i => 2 ^ (MAXBITS - L ls i)).sum

/-- Canonical code value of allocation index `j`. -/
def cv (ls : List Nat) (j : Nat) : Nat := K ls j / 2 ^ (MAXBITS - L ls j)

/-- Bit-reversed canonical code of allocation index `j` (`huff`). -/
def H (ls : List Nat) (j : Nat) : Nat := rev (L ls j) (cv ls j)

/-- Remaining codes of length `l` at or after allocation index `a`. -/
def cntGE (ls : List Nat) (a l : Nat) : Nat := offL ls (l + 1) - max a (offL ls l)

/-- Root group index of allocation index `j` (`cv / 2^(L - root)`). -/
def grp (ls : List Nat) (root j : Nat) : Nat := K ls j / 2 ^ (MAXBITS - root)

/-- Lookahead loop on list model. -/
def look (ls : List Nat) (a root mx : Nat) : Nat → Int → Nat → Nat
  | c, _, 0 => c
  | c, left, fuel + 1 =>
    if c + root < mx then
      if left - (cntGE ls a (c + root) : Int) ≤ 0 then c
      else look ls a root mx (c + 1) (2 * (left - (cntGE ls a (c + root) : Int))) fuel
    else c

/-- Subtable width chosen for group starting at allocation index `a`. -/
def width (ls : List Nat) (a root mx : Nat) : Nat :=
  look ls a root mx (L ls a - root) (2 ^ (L ls a - root) : Nat) (MAXBITS + 1)

/-- Table descriptor `(drop, curr, base, used, low)` in force at allocation index `i`. -/
structure Desc where
  drop : Nat
  curr : Nat
  base : Nat
  used : Nat
  low : Nat
  deriving Repr

/-- Whether a new subtable starts at allocation index `i + 1`. -/
def startsAt (ls : List Nat) (root i : Nat) : Prop :=
  root < L ls (i + 1) ∧ (L ls i ≤ root ∨ grp ls root (i + 1) ≠ grp ls root i)

instance (ls : List Nat) (root i : Nat) : Decidable (startsAt ls root i) := by
  unfold startsAt; infer_instance

/-- Closed-form descriptor sequence of `inflate_table`. -/
def desc (ls : List Nat) (root mx : Nat) : Nat → Desc
  | 0 => ⟨0, root, 0, 2 ^ root, 2 ^ 32 - 1⟩
  | i + 1 =>
    let d := desc ls root mx i
    if startsAt ls root i then
      ⟨root, width ls (i + 1) root mx, d.base + 2 ^ d.curr,
        d.used + 2 ^ width ls (i + 1) root mx, rev root (grp ls root (i + 1))⟩
    else d

theorem desc_used (ls : List Nat) (root mx i : Nat) :
    (desc ls root mx i).used = (desc ls root mx i).base + 2 ^ (desc ls root mx i).curr := by
  induction i with
  | zero => simp [desc]
  | succ i ih =>
    simp only [desc]
    split
    · simp only; rw [ih]
    · exact ih

theorem desc_used_mono (ls : List Nat) (root mx : Nat) {i j : Nat} (h : i ≤ j) :
    (desc ls root mx i).used ≤ (desc ls root mx j).used := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · subst hij; exact Nat.le_refl _
    · have := ih (by omega)
      simp only [desc]
      split
      · simp only; have := Nat.two_pow_pos (width ls (j + 1) root mx); omega
      · exact this

theorem desc_regions (ls : List Nat) (root mx : Nat) {i j : Nat} (order : i ≤ j) :
    desc ls root mx i = desc ls root mx j ∨
      (desc ls root mx i).used ≤ (desc ls root mx j).base := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i; exact Or.inl rfl
  | succ j ih =>
    by_cases same : i = j + 1
    · subst i; exact Or.inl rfl
    · have previous := ih (by omega)
      by_cases start : startsAt ls root j
      · simp only [desc, start, ite_true]
        right
        rcases previous with equal | separated
        · rw [equal, desc_used]; exact Nat.le_refl _
        · have := Nat.two_pow_pos (desc ls root mx j).curr; omega
      · simp only [desc, start, ite_false]
        exact previous

/-! ## 8. Exact Canonical `ENOUGH_LENS = 1332` and `ENOUGH_DISTS = 400` Bounds -/

section EnoughMath

/-- Number of root slots covered by short codes (`1 ≤ l ≤ R`) in `c : Nat → Nat`. -/
def shortSlots (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => 2 * shortSlots c r + c (r + 1)

/-- Number of short symbols (`1 ≤ l ≤ R`). -/
def shortSyms (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => shortSyms c r + c (r + 1)

private theorem two_pow_add_sub_ge (m c : Nat) (hc : 1 ≤ c) :
    2 ^ m + c ≤ 2 ^ (m + c) := by
  induction c with
  | zero => omega
  | succ c ih =>
    by_cases hc0 : c = 0
    · subst hc0
      have : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      rw [Nat.pow_succ]
      omega
    · have hih := ih (by omega)
      rw [show m + (c + 1) = (m + c) + 1 by omega, Nat.pow_succ]
      have hpos : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      omega

/-- Key binary-covering lemma: if `k ≤ R` short symbols cover `S < 2^R` root slots,
then `S ≤ 2^R - 2^(R - k)`. -/
theorem shortSlots_le_two_pow_sub (c : Nat → Nat) :
    ∀ R, shortSyms c R ≤ R → shortSlots c R < 2 ^ R →
      shortSlots c R ≤ 2 ^ R - 2 ^ (R - shortSyms c R)
  | 0, _, _ => by simp [shortSlots, shortSyms] at *
  | R + 1, hk, hs => by
    have hS : shortSlots c (R + 1) = 2 * shortSlots c R + c (R + 1) := rfl
    have hK : shortSyms c (R + 1) = shortSyms c R + c (R + 1) := rfl
    have hSR : shortSlots c R < 2 ^ R := by
      rw [hS, Nat.pow_succ] at hs; omega
    by_cases hc0 : c (R + 1) = 0
    · by_cases htop : shortSyms c (R + 1) = R + 1
      · have hsub : R + 1 - shortSyms c (R + 1) = 0 := by omega
        rw [hsub, Nat.pow_zero]
        omega
      · have hle : shortSyms c R ≤ R := by rw [hK, hc0] at hk htop; omega
        have ih := shortSlots_le_two_pow_sub c R hle hSR
        have heq : R + 1 - shortSyms c (R + 1) = (R - shortSyms c R) + 1 := by
          rw [hK, hc0]; omega
        rw [hS, hc0, Nat.add_zero, heq, Nat.pow_succ, Nat.pow_succ]
        have hle2 : 2 ^ (R - shortSyms c R) ≤ 2 ^ R :=
          Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
        omega
    · have hle : shortSyms c R ≤ R := by rw [hK] at hk; omega
      have ih := shortSlots_le_two_pow_sub c R hle hSR
      have hdiff := two_pow_add_sub_ge (R + 1 - shortSyms c (R + 1)) (c (R + 1)) (by omega)
      have heq : R + 1 - shortSyms c (R + 1) + c (R + 1) = R - shortSyms c R + 1 := by
        rw [hK]; omega
      rw [heq, Nat.pow_succ] at hdiff
      have hpow_le : 2 ^ (R - shortSyms c R) ≤ 2 ^ R :=
        Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
      rw [hS, Nat.pow_succ]
      omega

/-- Ceiling division by `2^k`. -/
def ceilDivPow2 (r k : Nat) : Nat := (r + 2 ^ k - 1) / 2 ^ k

/-- Slack `2^k * ceil(r / 2^k) - r` for a single level `k ≥ 1`. -/
def levelSlack (r k : Nat) : Nat := 2 ^ k * ceilDivPow2 r k - r

theorem ceilDivPow2_mul_ge (r k : Nat) : r ≤ 2 ^ k * ceilDivPow2 r k := by
  unfold ceilDivPow2
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmod := Nat.div_add_mod (r + 2 ^ k - 1) (2 ^ k)
  have hlt := Nat.mod_lt (r + 2 ^ k - 1) hpos
  omega

theorem levelSlack_le (r k : Nat) : levelSlack r k ≤ 2 ^ k - 1 := by
  unfold levelSlack ceilDivPow2
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv : 2 ^ k * ((r + 2 ^ k - 1) / 2 ^ k) ≤ r + 2 ^ k - 1 := Nat.mul_div_le _ _
  omega

theorem levelSlack_even_le {r k : Nat} (hk : 1 ≤ k) (heven : r % 2 = 0) :
    levelSlack r k ≤ 2 ^ k - 2 := by
  unfold levelSlack ceilDivPow2
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h2le : 2 ≤ 2 ^ k := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simpa using this
  have h2dvd : 2 ∣ 2 ^ k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.pow_succ]
    exact Nat.dvd_mul_left 2 (2 ^ k')
  by_cases hz : r = 0
  · subst hz
    have hdiv : (2 ^ k - 1) / 2 ^ k = 0 := Nat.div_eq_of_lt (by omega)
    rw [Nat.zero_add, hdiv, Nat.mul_zero, Nat.sub_zero]
    omega
  · have hm : r % 2 ^ k % 2 = 0 := by
      rw [Nat.mod_mod_of_dvd r h2dvd, heven]
    by_cases hrem : r % 2 ^ k = 0
    · have hdvd : 2 ^ k ∣ r := Nat.dvd_of_mod_eq_zero hrem
      obtain ⟨q, rfl⟩ := hdvd
      have hq : (2 ^ k * q + 2 ^ k - 1) / 2 ^ k = q := by
        have h1 : 2 ^ k * q + 2 ^ k - 1 = 2 ^ k * q + (2 ^ k - 1) := by omega
        rw [h1, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      rw [hq]
      omega
    · have hrem2 : 2 ≤ r % 2 ^ k := by omega
      have hdm := Nat.div_add_mod r (2 ^ k)
      have hq : (r + 2 ^ k - 1) / 2 ^ k = r / 2 ^ k + 1 := by
        have h1 : r + 2 ^ k - 1 = (r % 2 ^ k - 1) + 2 ^ k * (r / 2 ^ k + 1) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
        rw [h1, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by have := Nat.mod_lt r hpos; omega),
          Nat.zero_add]
      rw [hq, Nat.mul_add, Nat.mul_one]
      omega

/-- Total subtable cost in the canonical `r_d` representation for `D` levels beyond `R`:
`cost = 2 * G + ∑_{d=1}^{D-1} 2^d * ceil(r_d / 2^d)` where `r_d` is `rs d`. -/
def subCostOfRem (G : Nat) (rs : Nat → Nat) : Nat → Nat
  | 0 => 2 * G
  | d + 1 => subCostOfRem G rs d + 2 ^ (d + 1) * ceilDivPow2 (rs d) (d + 1)

/-- Sum of `rs 0 + ... + rs (m - 1)`. -/
def sumRem (rs : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => sumRem rs m + rs m

/-- Sum of `(2^1 - 1) + ... + (2^m - 1)`. -/
def sumMaxSlack : Nat → Nat
  | 0 => 0
  | m + 1 => sumMaxSlack m + (2 ^ (m + 1) - 1)

theorem sumMaxSlack_four : sumMaxSlack 4 = 26 := by decide
theorem sumMaxSlack_six : sumMaxSlack 6 = 120 := by decide

/-- Core parity-slack bound on `subCostOfRem`:
for `m` levels beyond `R+1`, `subCostOfRem G rs m ≤ 2*G + sumRem rs m + sumMaxSlack m`,
and if at least one `rs i` (`i < m`) is even then `subCostOfRem G rs m + 1 ≤ 2*G + sumRem rs m + sumMaxSlack m`. -/
theorem subCostOfRem_bound (G : Nat) (rs : Nat → Nat) (m : Nat) :
    subCostOfRem G rs m ≤ 2 * G + sumRem rs m + sumMaxSlack m ∧
    ((∃ i < m, rs i % 2 = 0) →
      subCostOfRem G rs m + 1 ≤ 2 * G + sumRem rs m + sumMaxSlack m) := by
  induction m with
  | zero =>
    refine ⟨by simp [subCostOfRem, sumRem, sumMaxSlack], fun ⟨i, hi, _⟩ => by omega⟩
  | succ m ih =>
    have h1 := levelSlack_le (rs m) (m + 1)
    have hr := ceilDivPow2_mul_ge (rs m) (m + 1)
    have hpow : 2 ≤ 2 ^ (m + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    unfold levelSlack at h1
    simp only [subCostOfRem, sumRem, sumMaxSlack]
    constructor
    · have := ih.1; omega
    · rintro ⟨i, hi, heven⟩
      by_cases him : i < m
      · have := ih.2 ⟨i, him, heven⟩
        omega
      · have him' : i = m := by omega
        subst him'
        have he := levelSlack_even_le (r := rs i) (k := i + 1) (by omega) heven
        unfold levelSlack at he
        have := ih.1
        omega

private theorem sumRem_mod_two_of_all_odd (rs : Nat → Nat) :
    ∀ m, (∀ i < m, rs i % 2 = 1) → sumRem rs m % 2 = m % 2
  | 0, _ => by simp [sumRem]
  | m + 1, h => by
    have ih := sumRem_mod_two_of_all_odd rs m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    simp only [sumRem]
    omega

theorem subCostOfRem_even_levels_parity (G : Nat) (rs : Nat → Nat) (m : Nat)
    (hm : m % 2 = 0) :
    subCostOfRem G rs m + (2 * G + sumRem rs m) % 2 ≤ 2 * G + sumRem rs m + sumMaxSlack m := by
  have hb := subCostOfRem_bound G rs m
  by_cases hodd : (2 * G + sumRem rs m) % 2 = 0
  · rw [hodd, Nat.add_zero]; exact hb.1
  · have hsum_odd : sumRem rs m % 2 = 1 := by omega
    have hex : ∃ i < m, rs i % 2 = 0 := by
      apply Classical.byContradiction
      intro hnone
      have hall : ∀ i < m, rs i % 2 = 1 := by
        intro i hi
        have : rs i % 2 ≠ 0 := fun hz => hnone ⟨i, hi, hz⟩
        omega
      have hp := sumRem_mod_two_of_all_odd rs m hall
      rw [hm] at hp
      omega
    have hb2 := hb.2 hex
    have hpar : (2 * G + sumRem rs m) % 2 = 1 := by omega
    rw [hpar]
    exact hb2

/-- Canonical `ENOUGH_LENS = 1332` bound at `R = 10` (`LENBITS`), `n ≤ 286`, `MAXBITS = 15`. -/
theorem canonical_lens_enough_bound (c rs : Nat → Nat)
    (hshortLt : shortSlots c LENBITS < 2 ^ LENBITS)
    (hle : shortSyms c LENBITS + (2 * (2 ^ LENBITS - shortSlots c LENBITS) + sumRem rs 4) ≤ L_CODES) :
    2 ^ LENBITS + subCostOfRem (2 ^ LENBITS - shortSlots c LENBITS) rs 4 ≤ ENOUGH_LENS := by
  let S := shortSlots c LENBITS
  let K := shortSyms c LENBITS
  let G := 2 ^ LENBITS - S
  let L_long := 2 * G + sumRem rs 4
  have h1024 : 2 ^ LENBITS = 1024 := by decide
  have hK3 : 3 ≤ K := by
    apply Classical.byContradiction
    intro hKlt
    have hKle2 : K ≤ 2 := by omega
    have hKle10 : K ≤ LENBITS := by unfold LENBITS at *; omega
    have hs := shortSlots_le_two_pow_sub c LENBITS hKle10 hshortLt
    have hpow : 2 ^ (LENBITS - K) ≥ 2 ^ 8 :=
      Nat.pow_le_pow_right (by omega) (by unfold LENBITS; dsimp only [K]; omega)
    have h28 : 2 ^ 8 = 256 := by decide
    have hG : G ≥ 256 := by
      dsimp only [G, S, K] at *
      omega
    unfold L_CODES at hle
    dsimp only [G, S, K] at *
    omega
  have hLlong : L_long ≤ 283 := by
    unfold L_CODES at hle
    dsimp only [L_long, G, S, K] at *
    omega
  have hsub := subCostOfRem_even_levels_parity G rs 4 (by decide)
  rw [sumMaxSlack_four] at hsub
  have hcost : subCostOfRem G rs 4 ≤ 308 := by
    change subCostOfRem G rs 4 + L_long % 2 ≤ L_long + 26 at hsub
    omega
  unfold ENOUGH_LENS
  dsimp only [G, S] at *
  omega

/-- Canonical `ENOUGH_DISTS = 400` bound at `R = 8` (`DISTBITS`), `n ≤ 30`, `MAXBITS = 15`. -/
theorem canonical_dists_enough_bound (c rs : Nat → Nat)
    (hshortLt : shortSlots c DISTBITS < 2 ^ DISTBITS)
    (hle : shortSyms c DISTBITS + (2 * (2 ^ DISTBITS - shortSlots c DISTBITS) + sumRem rs 6) ≤ D_CODES) :
    2 ^ DISTBITS + subCostOfRem (2 ^ DISTBITS - shortSlots c DISTBITS) rs 6 ≤ ENOUGH_DISTS := by
  let S := shortSlots c DISTBITS
  let K := shortSyms c DISTBITS
  let G := 2 ^ DISTBITS - S
  let L_long := 2 * G + sumRem rs 6
  have h256 : 2 ^ DISTBITS = 256 := by decide
  have hK5 : 5 ≤ K := by
    apply Classical.byContradiction
    intro hKlt
    have hKle4 : K ≤ 4 := by omega
    have hKle8 : K ≤ DISTBITS := by unfold DISTBITS at *; omega
    have hs := shortSlots_le_two_pow_sub c DISTBITS hKle8 hshortLt
    have hpow : 2 ^ (DISTBITS - K) ≥ 2 ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by unfold DISTBITS; dsimp only [K]; omega)
    have h16 : 2 ^ 4 = 16 := by decide
    have hG : G ≥ 16 := by
      dsimp only [G, S, K] at *
      omega
    unfold D_CODES at hle
    dsimp only [G, S, K] at *
    omega
  have hLlong : L_long ≤ 25 := by
    unfold D_CODES at hle
    dsimp only [L_long, G, S, K] at *
    omega
  have hsub := subCostOfRem_even_levels_parity G rs 6 (by decide)
  rw [sumMaxSlack_six] at hsub
  have hcost : subCostOfRem G rs 6 ≤ 144 := by
    change subCostOfRem G rs 6 + L_long % 2 ≤ L_long + 120 at hsub
    omega
  unfold ENOUGH_DISTS
  dsimp only [G, S] at *
  omega

/-- Recurrence generating `rs d = r_{R + 1 + d}` from symbol length counts `c`. -/
def remSeq (c : Nat → Nat) (R G : Nat) : Nat → Nat
  | 0 => 2 * G - c (R + 1)
  | d + 1 => 2 * remSeq c R G d - c (R + d + 2)

/-- Sum of long symbol counts `c (R + 1) + ... + c (R + d)`. -/
def sumLongCounts (c : Nat → Nat) (R : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => sumLongCounts c R d + c (R + d + 1)

theorem sumLongCounts_eq_remSeq (c : Nat → Nat) (R G : Nat) :
    ∀ m, (∀ d ≤ m, c (R + d + 1) ≤ (if d = 0 then 2 * G else 2 * remSeq c R G (d - 1))) →
      remSeq c R G m = 0 →
      2 * G + sumRem (remSeq c R G) m = sumLongCounts c R (m + 1) := by
  intro m hle hlast
  suffices h : ∀ k ≤ m,
      2 * G + sumRem (remSeq c R G) k = sumLongCounts c R (k + 1) + remSeq c R G k by
    have := h m (Nat.le_refl m)
    rw [hlast, Nat.add_zero] at this
    exact this
  intro k hk
  induction k with
  | zero =>
    have h0 := hle 0 (Nat.zero_le m)
    simp only [Nat.add_zero, ite_true] at h0
    simp only [sumRem, sumLongCounts, remSeq, Nat.add_zero, Nat.zero_add]
    omega
  | succ k ih =>
    have hprev := ih (by omega)
    have hk1 := hle (k + 1) hk
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel] at hk1
    have hr : R + (k + 1) + 1 = R + k + 2 := by omega
    rw [hr] at hk1
    have hsum : sumLongCounts c R (k + 1 + 1) = sumLongCounts c R (k + 1) + c (R + k + 2) := by
      simp only [sumLongCounts, hr]
    simp only [sumRem, remSeq]
    rw [hsum]
    omega

end EnoughMath

end Zlib.Proof.Math.Inftrees
