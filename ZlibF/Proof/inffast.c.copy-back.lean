import ZlibF.Proof.«inffast.c.match»

/-!
# inffast.c: `load64`, `store64`, and `copy_back`

Low-level byte-packing and LZ77 block-copy proofs for the 64-bit fast path
(`Z_INFLATE_FETCH == 64`). `copy_back` writes exact LZ77 match bytes to `[o, o + len)`
and at most 15 scratch bytes in `[o + len, o + len + 15)`.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-! ### Little-endian 64-bit loads and stores -/

private theorem add_lit_ok {R T : Type} [Space Heap R T] {h : Heap} {r : R} {a : Array T}
    {off : Nat} (ki : Int) (k : Nat) (hki : ki = k) (hg : Space.get h r = some a)
    (h1 : off + k ≤ a.size) :
    OkOn h (Ptr.add (Ptr.ref r off) ki) (Ptr.ref r (off + k)) := by
  subst hki
  exact Ptr.add_nat_ok hg h1

private theorem index8_lit {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (ki : Int) (k : Nat) (hki : ki = k)
    (hg : Space.get h r = some a) (hlt : off + k < a.size) :
    OkOn h (index8 (.ref r off) ki) (a.getD (off + k) 0) := by
  subst hki
  have hk := Ptr.index_ok (i := k) hg hlt
  have hd : a[off + k] = a.getD (off + k) 0 := by simp [Array.getD_eq_getD_getElem?, hlt]
  rw [hd] at hk
  exact hk

/-- Little-endian 64-bit word assembled from 8 bytes of `a` starting at `off`. -/
def leBytes64 (a : Array UInt8) (off : Nat) : UInt64 :=
  let b0 := a.getD off 0
  let b1 := a.getD (off + 1) 0
  let b2 := a.getD (off + 2) 0
  let b3 := a.getD (off + 3) 0
  let b4 := a.getD (off + 4) 0
  let b5 := a.getD (off + 5) 0
  let b6 := a.getD (off + 6) 0
  let b7 := a.getD (off + 7) 0
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

theorem load64_ok {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (hg : Space.get h r = some a) (hroom : off + 8 ≤ a.size) :
    OkOn h (load64 (.ref r off)) (leBytes64 a off) := by
  unfold OkOn load64 leBytes64
  rw [bind_ok (index8_lit 0 0 rfl hg (by omega)),
      bind_ok (index8_lit 1 1 rfl hg (by omega)),
      bind_ok (index8_lit 2 2 rfl hg (by omega)),
      bind_ok (index8_lit 3 3 rfl hg (by omega)),
      bind_ok (index8_lit 4 4 rfl hg (by omega)),
      bind_ok (index8_lit 5 5 rfl hg (by omega)),
      bind_ok (index8_lit 6 6 rfl hg (by omega)),
      bind_ok (index8_lit 7 7 rfl hg (by omega))]
  rfl

private theorem u64_byte_shift (b : UInt8) (k : Nat) (hk : k ≤ 56) :
    (b.toUInt64 <<< UInt64.ofNat k).toNat = b.toNat * 2 ^ k := by
  have hklt : k < UInt64.size := Nat.lt_of_le_of_lt hk (by decide)
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' hklt,
    Nat.mod_eq_of_lt (by omega : k < 64), Nat.shiftLeft_eq]
  have hb : b.toNat < 2 ^ 8 := b.toNat_lt
  have hpow : 2 ^ 8 * 2 ^ k ≤ 2 ^ 64 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  simpa [UInt64.size] using
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos k)) hpow)

private theorem testBit_u64_shift (x : UInt64) (s m : Nat) (hs : s < 64) :
    (x <<< UInt64.ofNat s).toNat.testBit m =
      (decide (m < 64) && decide (s ≤ m) && x.toNat.testBit (m - s)) := by
  have hslt : s < UInt64.size := Nat.lt_of_lt_of_le hs (by decide)
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' hslt,
    Nat.mod_eq_of_lt hs]
  change ((x.toNat <<< s) % 2 ^ 64).testBit m = _
  by_cases hm64 : m < 64
  · rw [Nat.testBit_mod_two_pow, decide_eq_true hm64, Bool.true_and, Nat.testBit_shiftLeft]
    by_cases hsm : s ≤ m <;> simp [hsm]
  · rw [Nat.testBit_mod_two_pow, decide_eq_false hm64]
    simp

private theorem testBit_byte_shift (b : UInt8) (s j : Nat) (hs : s ≤ 56) :
    (b.toUInt64 <<< UInt64.ofNat s).toNat.testBit j =
      (decide (s ≤ j ∧ j < s + 8) && b.toNat.testBit (j - s)) := by
  rw [testBit_u64_shift b.toUInt64 s j (by omega)]
  by_cases hj : s ≤ j ∧ j < s + 8
  · have h64 : j < 64 := by omega
    simp [hj, h64]
  · simp only [hj]
    by_cases h64 : j < 64
    · by_cases hsj : s ≤ j
      · have hhi : 8 ≤ j - s := by omega
        have hfalse : b.toNat.testBit (j - s) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by decide) hhi))
        simp [h64, hsj, hfalse]
      · simp [h64, hsj]
    · simp [h64]

theorem leBytes64_testBit (a : Array UInt8) (off j : Nat) (hj : j < 64) :
    (leBytes64 a off).toNat.testBit j = (a.getD (off + j / 8) 0).toNat.testBit (j % 8) := by
  unfold leBytes64
  have hs0 : (a.getD off 0).toUInt64.toNat.testBit j =
      ((a.getD off 0).toUInt64 <<< UInt64.ofNat 0).toNat.testBit j := by simp
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
      UInt64.toNat_or, UInt64.toNat_or]
  simp only [Nat.testBit_or, hs0,
    show (8 : UInt64) = UInt64.ofNat 8 from rfl,
    show (16 : UInt64) = UInt64.ofNat 16 from rfl,
    show (24 : UInt64) = UInt64.ofNat 24 from rfl,
    show (32 : UInt64) = UInt64.ofNat 32 from rfl,
    show (40 : UInt64) = UInt64.ofNat 40 from rfl,
    show (48 : UInt64) = UInt64.ofNat 48 from rfl,
    show (56 : UInt64) = UInt64.ofNat 56 from rfl,
    testBit_byte_shift _ 0 j (by omega), testBit_byte_shift _ 8 j (by omega),
    testBit_byte_shift _ 16 j (by omega), testBit_byte_shift _ 24 j (by omega),
    testBit_byte_shift _ 32 j (by omega), testBit_byte_shift _ 40 j (by omega),
    testBit_byte_shift _ 48 j (by omega), testBit_byte_shift _ 56 j (by omega)]
  rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 32) ∨
      (32 ≤ j ∧ j < 40) ∨ (40 ≤ j ∧ j < 48) ∨ (48 ≤ j ∧ j < 56) ∨ (56 ≤ j ∧ j < 64) by omega) with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have q : j / 8 = 0 := by omega
    have r : j % 8 = j := by omega
    simp [q, r, h0, show ¬ (8 ≤ j) by omega, show ¬ (16 ≤ j) by omega, show ¬ (24 ≤ j) by omega,
      show ¬ (32 ≤ j) by omega, show ¬ (40 ≤ j) by omega, show ¬ (48 ≤ j) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 1 := by omega
    have r : j % 8 = j - 8 := by omega
    simp [q, r, h1, show ¬ (j < 8) by omega, show ¬ (16 ≤ j) by omega, show ¬ (24 ≤ j) by omega,
      show ¬ (32 ≤ j) by omega, show ¬ (40 ≤ j) by omega, show ¬ (48 ≤ j) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 2 := by omega
    have r : j % 8 = j - 16 := by omega
    simp [q, r, h2, show ¬ (j < 8) by omega, show ¬ (j < 16) by omega, show ¬ (24 ≤ j) by omega,
      show ¬ (32 ≤ j) by omega, show ¬ (40 ≤ j) by omega, show ¬ (48 ≤ j) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 3 := by omega
    have r : j % 8 = j - 24 := by omega
    simp [q, r, h3, show ¬ (j < 8) by omega, show ¬ (j < 16) by omega, show ¬ (j < 24) by omega,
      show ¬ (32 ≤ j) by omega, show ¬ (40 ≤ j) by omega, show ¬ (48 ≤ j) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 4 := by omega
    have r : j % 8 = j - 32 := by omega
    simp [q, r, h4, show ¬ (j < 8) by omega, show ¬ (j < 16) by omega, show ¬ (j < 24) by omega,
      show ¬ (j < 32) by omega, show ¬ (40 ≤ j) by omega, show ¬ (48 ≤ j) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 5 := by omega
    have r : j % 8 = j - 40 := by omega
    simp [q, r, h5, show ¬ (j < 8) by omega, show ¬ (j < 16) by omega, show ¬ (j < 24) by omega,
      show ¬ (j < 32) by omega, show ¬ (j < 40) by omega, show ¬ (48 ≤ j) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 6 := by omega
    have r : j % 8 = j - 48 := by omega
    simp [q, r, h6, show ¬ (j < 8) by omega, show ¬ (j < 16) by omega, show ¬ (j < 24) by omega,
      show ¬ (j < 32) by omega, show ¬ (j < 40) by omega, show ¬ (j < 48) by omega, show ¬ (56 ≤ j) by omega]
  · have q : j / 8 = 7 := by omega
    have r : j % 8 = j - 56 := by omega
    simp [q, r, h7, show ¬ (j < 8) by omega, show ¬ (j < 16) by omega, show ¬ (j < 24) by omega,
      show ¬ (j < 32) by omega, show ¬ (j < 40) by omega, show ¬ (j < 48) by omega, show ¬ (j < 56) by omega]

/-- Array with 8 little-endian bytes of `v` stored starting at `off`. -/
def store8Bytes (A : Array UInt8) (off : Nat) (v : UInt64) : Array UInt8 :=
  (((((((A.set! off (v &&& 0xff).toUInt8)
    |>.set! (off + 1) ((v >>> 8) &&& 0xff).toUInt8)
    |>.set! (off + 2) ((v >>> 16) &&& 0xff).toUInt8)
    |>.set! (off + 3) ((v >>> 24) &&& 0xff).toUInt8)
    |>.set! (off + 4) ((v >>> 32) &&& 0xff).toUInt8)
    |>.set! (off + 5) ((v >>> 40) &&& 0xff).toUInt8)
    |>.set! (off + 6) ((v >>> 48) &&& 0xff).toUInt8)
    |>.set! (off + 7) ((v >>> 56) &&& 0xff).toUInt8

theorem store8Bytes_size (A : Array UInt8) (off : Nat) (v : UInt64) :
    (store8Bytes A off v).size = A.size := by
  simp [store8Bytes]

theorem store8Bytes_outside (A : Array UInt8) (off : Nat) (v : UInt64) {j : Nat}
    (hj : j < off ∨ off + 8 ≤ j) : (store8Bytes A off v)[j]? = A[j]? := by
  simp [store8Bytes, show off ≠ j by omega,
    show off + 1 ≠ j by omega, show off + 2 ≠ j by omega, show off + 3 ≠ j by omega,
    show off + 4 ≠ j by omega, show off + 5 ≠ j by omega, show off + 6 ≠ j by omega,
    show off + 7 ≠ j by omega]

theorem store8Bytes_at (A : Array UInt8) (off k : Nat) (v : UInt64)
    (hk : k < 8) (hroom : off + 8 ≤ A.size) :
    (store8Bytes A off v)[off + k]? = some ((v >>> UInt64.ofNat (8 * k)) &&& 0xff).toUInt8 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [store8Bytes, show off < A.size by omega]
  · simp [store8Bytes, show off + 1 < A.size by omega]
  · simp [store8Bytes, show off + 2 < A.size by omega]
  · simp [store8Bytes, show off + 3 < A.size by omega]
  · simp [store8Bytes, show off + 4 < A.size by omega]
  · simp [store8Bytes, show off + 5 < A.size by omega]
  · simp [store8Bytes, show off + 6 < A.size by omega]
  · simp [store8Bytes, show off + 7 < A.size by omega]

theorem store64_ok {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (off : Nat) (v : UInt64) (hroom : off + 8 ≤ A.size) :
    store64 (.ref e.ob off) v (e.heap A msg m) = .ok ((), e.heap (store8Bytes A off v) msg m) := by
  unfold store64 store8Bytes
  let A0 := A.set! off (v &&& 0xff).toUInt8
  let A1 := A0.set! (off + 1) ((v >>> 8) &&& 0xff).toUInt8
  let A2 := A1.set! (off + 2) ((v >>> 16) &&& 0xff).toUInt8
  let A3 := A2.set! (off + 3) ((v >>> 24) &&& 0xff).toUInt8
  let A4 := A3.set! (off + 4) ((v >>> 32) &&& 0xff).toUInt8
  let A5 := A4.set! (off + 5) ((v >>> 40) &&& 0xff).toUInt8
  let A6 := A5.set! (off + 6) ((v >>> 48) &&& 0xff).toUInt8
  let A7 := A6.set! (off + 7) ((v >>> 56) &&& 0xff).toUInt8
  have hs0 : A0.size = A.size := by simp [A0]
  have hs1 : A1.size = A.size := by simp [A1, hs0]
  have hs2 : A2.size = A.size := by simp [A2, hs1]
  have hs3 : A3.size = A.size := by simp [A3, hs2]
  have hs4 : A4.size = A.size := by simp [A4, hs3]
  have hs5 : A5.size = A.size := by simp [A5, hs4]
  have hs6 : A6.size = A.size := by simp [A6, hs5]
  have s0 : store8 (.ref e.ob off) (v &&& 0xff).toUInt8 (e.heap A msg m) = .ok ((), e.heap A0 msg m) := by
    rw [← e.heap_put A A0 msg m]
    exact Ptr.store_ok (off := off) (e.heap_bytes_ob A msg m) (e.heap_ro_ob A msg m) (by omega)
  have s1 : store8 (.ref e.ob (off + 1)) ((v >>> 8) &&& 0xff).toUInt8 (e.heap A0 msg m) = .ok ((), e.heap A1 msg m) := by
    rw [← e.heap_put A0 A1 msg m]
    exact Ptr.store_ok (off := off + 1) (e.heap_bytes_ob A0 msg m) (e.heap_ro_ob A0 msg m) (by rw [hs0]; omega)
  have s2 : store8 (.ref e.ob (off + 2)) ((v >>> 16) &&& 0xff).toUInt8 (e.heap A1 msg m) = .ok ((), e.heap A2 msg m) := by
    rw [← e.heap_put A1 A2 msg m]
    exact Ptr.store_ok (off := off + 2) (e.heap_bytes_ob A1 msg m) (e.heap_ro_ob A1 msg m) (by rw [hs1]; omega)
  have s3 : store8 (.ref e.ob (off + 3)) ((v >>> 24) &&& 0xff).toUInt8 (e.heap A2 msg m) = .ok ((), e.heap A3 msg m) := by
    rw [← e.heap_put A2 A3 msg m]
    exact Ptr.store_ok (off := off + 3) (e.heap_bytes_ob A2 msg m) (e.heap_ro_ob A2 msg m) (by rw [hs2]; omega)
  have s4 : store8 (.ref e.ob (off + 4)) ((v >>> 32) &&& 0xff).toUInt8 (e.heap A3 msg m) = .ok ((), e.heap A4 msg m) := by
    rw [← e.heap_put A3 A4 msg m]
    exact Ptr.store_ok (off := off + 4) (e.heap_bytes_ob A3 msg m) (e.heap_ro_ob A3 msg m) (by rw [hs3]; omega)
  have s5 : store8 (.ref e.ob (off + 5)) ((v >>> 40) &&& 0xff).toUInt8 (e.heap A4 msg m) = .ok ((), e.heap A5 msg m) := by
    rw [← e.heap_put A4 A5 msg m]
    exact Ptr.store_ok (off := off + 5) (e.heap_bytes_ob A4 msg m) (e.heap_ro_ob A4 msg m) (by rw [hs4]; omega)
  have s6 : store8 (.ref e.ob (off + 6)) ((v >>> 48) &&& 0xff).toUInt8 (e.heap A5 msg m) = .ok ((), e.heap A6 msg m) := by
    rw [← e.heap_put A5 A6 msg m]
    exact Ptr.store_ok (off := off + 6) (e.heap_bytes_ob A5 msg m) (e.heap_ro_ob A5 msg m) (by rw [hs5]; omega)
  have s7 : store8 (.ref e.ob (off + 7)) ((v >>> 56) &&& 0xff).toUInt8 (e.heap A6 msg m) =
      .ok ((), e.heap A7 msg m) := by
    rw [← e.heap_put A6 A7 msg m]
    exact Ptr.store_ok (off := off + 7) (e.heap_bytes_ob A6 msg m) (e.heap_ro_ob A6 msg m) (by rw [hs6]; omega)
  rw [bind_ok s0,
      bind_ok (add_lit_ok 1 1 rfl (e.heap_bytes_ob A0 msg m) (by rw [hs0]; omega)), bind_ok s1,
      bind_ok (add_lit_ok 2 2 rfl (e.heap_bytes_ob A1 msg m) (by rw [hs1]; omega)), bind_ok s2,
      bind_ok (add_lit_ok 3 3 rfl (e.heap_bytes_ob A2 msg m) (by rw [hs2]; omega)), bind_ok s3,
      bind_ok (add_lit_ok 4 4 rfl (e.heap_bytes_ob A3 msg m) (by rw [hs3]; omega)), bind_ok s4,
      bind_ok (add_lit_ok 5 5 rfl (e.heap_bytes_ob A4 msg m) (by rw [hs4]; omega)), bind_ok s5,
      bind_ok (add_lit_ok 6 6 rfl (e.heap_bytes_ob A5 msg m) (by rw [hs5]; omega)), bind_ok s6,
      bind_ok (add_lit_ok 7 7 rfl (e.heap_bytes_ob A6 msg m) (by rw [hs6]; omega)), s7]

/-! ### Byte characterization of `memcpyB` and `cpyN` -/

private theorem if_t {α : Type _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  by_cases hc : c
  · simp [hc]
  · exact absurd h hc

private theorem if_f {α : Type _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  by_cases hc : c
  · exact absurd hc h
  · simp [hc]

theorem memcpyB_env_ok {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (fb : BRef) (S : Array UInt8) (oo fo n : Nat)
    (hf : Space.get e.h0 fb = some S) (hsep : fb ≠ e.ob ∨ fo + n ≤ oo ∨ oo + n ≤ fo)
    (hS : fb = e.ob → S = A)
    (hoo : oo + n ≤ A.size) (hfo : fo + n ≤ S.size) :
    memcpyB (.ref e.ob oo) (.ref fb fo) n (e.heap A msg m) =
      .ok ((), e.heap (copyRange A S oo fo n) msg m) := by
  have hAg := e.heap_bytes_ob A msg m
  have hSg : Space.get (e.heap A msg m) fb = some S := by
    by_cases eq : fb = e.ob
    · subst eq; rw [hAg, hS rfl]
    · rw [e.heap_get_ne A msg m eq]; exact hf
  have hro := e.heap_ro_ob A msg m
  have hsep' : e.ob ≠ fb ∨ oo + n ≤ fo ∨ fo + n ≤ oo := by
    rcases hsep with ne | l | r
    · exact Or.inl ne.symm
    · exact Or.inr (Or.inr l)
    · exact Or.inr (Or.inl r)
  unfold memcpyB Ptr.memcpy
  dsimp only
  rw [hAg, hSg]
  have hroBool : (Space.ro (e.heap A msg m) e.ob && decide (n ≠ 0)) = false := by simp [hro]
  rw [hroBool]
  have hbnd : oo + n ≤ A.size ∧ fo + n ≤ S.size := ⟨hoo, hfo⟩
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_t hbnd, if_t hsep']
  exact congrArg (fun hp => Except.ok ((), hp))
    ((Space.modify_eq (e.heap A msg m) e.ob A _ hAg).trans (e.heap_put A _ msg m))

private theorem foldl_range_size (n : Nat) (d s : Array UInt8) (doff soff : Nat) :
    ((List.range n).foldl (fun a i => a.set! (doff + i) s[soff + i]!) d).size = d.size := by
  have h : ∀ (l : List Nat) (a : Array UInt8),
      (l.foldl (fun a i => a.set! (doff + i) s[soff + i]!) a).size = a.size := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x xs ih => intro a; simp only [List.foldl]; rw [ih]; simp
  exact h _ _

private theorem array_set!_getElem? (a : Array UInt8) (i : Nat) (v : UInt8) (j : Nat) :
    (a.set! i v)[j]? = if i < a.size then (if i = j then some v else a[j]?) else a[j]? := by
  by_cases hi : i < a.size
  · rw [if_t hi, Array.set!, Array.setIfInBounds]
    simp only [hi, ↓reduceDIte]
    by_cases hj : j < a.size
    · rw [Array.getElem?_eq_getElem (by simpa using hj), Array.getElem?_eq_getElem hj,
        Array.getElem_set]
      by_cases hij : i = j <;> simp [hij]
    · have hnot : i ≠ j := by omega
      rw [Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj),
        Array.getElem?_eq_none (Nat.le_of_not_lt hj), if_f hnot]
  · rw [if_f hi, Array.set!, Array.setIfInBounds]
    simp only [hi, ↓reduceDIte]

private theorem foldl_range_getElem? (n : Nat) : ∀ (d s : Array UInt8) (doff soff : Nat),
    soff + n ≤ s.size → doff + n ≤ d.size → ∀ (j : Nat),
    ((List.range n).foldl (fun a i => a.set! (doff + i) s[soff + i]!) d)[j]? =
      if doff ≤ j ∧ j < doff + n then some s[soff + (j - doff)]! else d[j]? := by
  induction n with
  | zero =>
    intro d s doff soff _ _ j
    rw [List.range_zero, List.foldl_nil]
    have hnot : ¬ (doff ≤ j ∧ j < doff + 0) := by omega
    rw [if_f hnot]
  | succ n ih =>
    intro d s doff soff hs hd j
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih d s doff soff (by omega) (by omega) j
    have hsz := foldl_range_size n d s doff soff
    rw [array_set!_getElem?, if_t (by rw [hsz]; omega)]
    by_cases hcur : doff + n = j
    · subst hcur
      rw [if_t rfl, if_t (by omega), Nat.add_sub_cancel_left]
    · rw [if_f hcur, hprev]
      by_cases h1 : doff ≤ j ∧ j < doff + n
      · rw [if_t h1, if_t (by omega)]
      · rw [if_f h1, if_f (by omega)]

theorem copyRange_getElem? (d s : Array UInt8) (doff soff n : Nat) (hs : soff + n ≤ s.size)
    (hd : doff + n ≤ d.size) (j : Nat) :
    (copyRange d s doff soff n)[j]? =
      if doff ≤ j ∧ j < doff + n then some s[soff + (j - doff)]! else d[j]? :=
  foldl_range_getElem? n d s doff soff hs hd j

theorem blitN_getElem? (S : Array UInt8) : ∀ n fo oo (A : Array UInt8),
    fo + n ≤ S.size → oo + n ≤ A.size → ∀ j,
    (blitN S n fo oo A)[j]? = if oo ≤ j ∧ j < oo + n then some S[fo + (j - oo)]! else A[j]?
  | 0, fo, oo, A, _, _, j => by
    simp only [blitN]
    rw [if_f (by omega)]
  | n + 1, fo, oo, A, hfo, hoo, j => by
    have ih := blitN_getElem? S n (fo + 1) (oo + 1) (A.set! oo (S.getD fo 0)) (by omega) (by simp; omega) j
    simp only [blitN]
    rw [ih]
    by_cases hj : oo = j
    · subst hj
      rw [if_f (by omega), if_t (by omega)]
      simp [show oo < A.size by omega, Array.getD_eq_getD_getElem?, show fo < S.size by omega]
    · by_cases htail : oo + 1 ≤ j ∧ j < oo + 1 + n
      · have h2 : S[fo + 1 + (j - (oo + 1))]! = S[fo + (j - oo)]! := by congr 1; omega
        rw [if_t htail, if_t (by omega), h2]
      · rw [if_f htail, if_f (by omega)]
        simp [hj]

theorem copyRange_eq_blitN (A S : Array UInt8) (oo fo n : Nat) (hs : fo + n ≤ S.size) (hd : oo + n ≤ A.size) :
    copyRange A S oo fo n = blitN S n fo oo A := by
  apply Array.ext_getElem?
  intro j
  rw [copyRange_getElem? A S oo fo n hs hd j, blitN_getElem? S n fo oo A hs hd j]

theorem cpyN_outside : ∀ n fo oo (A : Array UInt8) j,
    (j < oo ∨ oo + n ≤ j) → (cpyN n fo oo A)[j]? = A[j]?
  | 0, _, _, _, _, _ => rfl
  | n + 1, fo, oo, A, j, hj => by
    simp only [cpyN]
    rw [cpyN_outside n (fo + 1) (oo + 1) _ j (by omega)]
    simp [show oo ≠ j by omega]

theorem cpyN_invariant : ∀ n fo oo (A : Array UInt8),
    1 ≤ oo - fo → fo ≤ oo → oo + n ≤ A.size →
    ∀ j, oo ≤ j → j < oo + n →
      (cpyN n fo oo A)[j]? = (cpyN n fo oo A)[j - (oo - fo)]?
  | 0, _, _, _, _, _, _, j, hj1, hj2 => by omega
  | n + 1, fo, oo, A, hd, hfo, hoo, j, hj1, hj2 => by
    let dist := oo - fo
    have ih := cpyN_invariant n (fo + 1) (oo + 1) (A.set! oo (A.getD fo 0)) (by omega) (by omega) (by simp; omega)
    simp only [cpyN]
    by_cases hj0 : j = oo
    · subst j
      rw [cpyN_outside n (fo + 1) (oo + 1) _ oo (by omega)]
      rw [cpyN_outside n (fo + 1) (oo + 1) _ (oo - dist) (by omega)]
      have hfq : oo - dist = fo := by omega
      rw [array_set!_getElem?, array_set!_getElem?, if_t (by omega), if_t rfl,
        if_t (by omega), if_f (by omega), hfq, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by omega)]
      rfl
    · have hj_succ := ih j (by omega) (by omega)
      have heq : (oo + 1) - (fo + 1) = oo - fo := by omega
      simpa only [heq] using hj_succ

theorem cpyN_dist_one (oo len : Nat) (A : Array UInt8) (hoo : 1 ≤ oo) (hlen : oo + len ≤ A.size) :
    ∀ j, oo ≤ j → j < oo + len → (cpyN len (oo - 1) oo A)[j]? = A[oo - 1]? := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro h1 h2
    have inv := cpyN_invariant len (oo - 1) oo A (by omega) (by omega) hlen j h1 h2
    have hdist : oo - (oo - 1) = 1 := by omega
    rw [hdist] at inv
    by_cases hfirst : j = oo
    · subst j
      rw [inv, cpyN_outside len (oo - 1) oo A (oo - 1) (by omega)]
    · have prev := ih (j - 1) (by omega) (by omega) (by omega)
      exact inv.trans prev

private theorem run_rep_byte (b : UInt8) (k : Nat) (hk : k < 8) :
    let r0 : UInt64 := b.toUInt64
    let r1 := r0 ||| (r0 <<< 8)
    let r2 := r1 ||| (r1 <<< 16)
    let r3 := r2 ||| (r2 <<< 32)
    ((r3 >>> UInt64.ofNat (8 * k)) &&& 0xff).toUInt8 = b := by
  intro r0 r1 r2 r3
  have hb8 : b.toNat < 2 ^ 8 := b.toNat_lt
  have h16lt : 16 < UInt64.size := by decide
  have hr0Nat : r0.toNat = b.toNat := by simp [r0]
  have hr1 : ∀ m, m < 16 → r1.toNat.testBit m = b.toNat.testBit (m % 8) := by
    intro m hm
    simp only [r1, UInt64.toNat_or, Nat.testBit_or, show (8 : UInt64) = UInt64.ofNat 8 from rfl,
      hr0Nat, show r0 <<< UInt64.ofNat 8 = b.toUInt64 <<< UInt64.ofNat 8 from rfl,
      testBit_byte_shift b 8 m (by omega)]
    by_cases hm8 : m < 8
    · rw [Bool.and_eq_false_iff.mpr (Or.inl (decide_eq_false (by omega))), Bool.or_false,
        Nat.mod_eq_of_lt hm8]
    · have hfalse : b.toNat.testBit m = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb8 (Nat.pow_le_pow_right (by decide) (by omega)))
      have h8 : 8 ≤ m ∧ m < 16 := ⟨by omega, hm⟩
      have hrem : m % 8 = m - 8 := by omega
      rw [hfalse, Bool.false_or, decide_eq_true h8, Bool.true_and, hrem]
  have hr2 : ∀ m, m < 32 → r2.toNat.testBit m = b.toNat.testBit (m % 8) := by
    intro m hm
    simp only [r2, UInt64.toNat_or, Nat.testBit_or, show (16 : UInt64) = UInt64.ofNat 16 from rfl,
      testBit_u64_shift r1 16 m (by omega)]
    by_cases hm16 : m < 16
    · have hnot : ¬ (16 ≤ m) := by omega
      rw [hr1 m hm16, decide_eq_false hnot, Bool.and_false, Bool.false_and, Bool.or_false]
    · have hr1lt : r1.toNat < 2 ^ 16 := by
        change (r0.toNat ||| (r0 <<< UInt64.ofNat 8).toNat) < 2 ^ 16
        have hs8 : (r0 <<< UInt64.ofNat 8).toNat < 2 ^ 16 := by
          rw [show r0 = b.toUInt64 from rfl, u64_byte_shift b 8 (by omega)]; omega
        exact Nat.or_lt_two_pow (n := 16) (Nat.lt_of_lt_of_le (by rw [hr0Nat]; exact hb8) (by decide)) hs8
      have hfalse : r1.toNat.testBit m = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr1lt (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hfalse, Bool.false_or, decide_eq_true (by omega), decide_eq_true (by omega),
        Bool.true_and, Bool.true_and, hr1 (m - 16) (by omega), show (m - 16) % 8 = m % 8 by omega]
  have hr3 : ∀ m, m < 64 → r3.toNat.testBit m = b.toNat.testBit (m % 8) := by
    intro m hm
    simp only [r3, UInt64.toNat_or, Nat.testBit_or, show (32 : UInt64) = UInt64.ofNat 32 from rfl,
      testBit_u64_shift r2 32 m (by omega)]
    by_cases hm32 : m < 32
    · have hnot : ¬ (32 ≤ m) := by omega
      rw [hr2 m hm32, decide_eq_false hnot, Bool.and_false, Bool.false_and, Bool.or_false]
    · have hr2lt : r2.toNat < 2 ^ 32 := by
        change (r1.toNat ||| (r1 <<< UInt64.ofNat 16).toNat) < 2 ^ 32
        have hr1lt : r1.toNat < 2 ^ 16 := by
          change (r0.toNat ||| (r0 <<< UInt64.ofNat 8).toNat) < 2 ^ 16
          have hs8 : (r0 <<< UInt64.ofNat 8).toNat < 2 ^ 16 := by
            rw [show r0 = b.toUInt64 from rfl, u64_byte_shift b 8 (by omega)]; omega
          exact Nat.or_lt_two_pow (n := 16) (Nat.lt_of_lt_of_le (by rw [hr0Nat]; exact hb8) (by decide)) hs8
        have hs16 : (r1 <<< UInt64.ofNat 16).toNat < 2 ^ 32 := by
          rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat_of_lt' h16lt,
            show (16 % 64 : Nat) = 16 from rfl, Nat.shiftLeft_eq]
          rw [Nat.mod_eq_of_lt (by simpa [UInt64.size] using (by omega : r1.toNat * 2 ^ 16 < 2 ^ 64))]
          omega
        exact Nat.or_lt_two_pow (n := 32) (Nat.lt_of_lt_of_le hr1lt (by decide)) hs16
      have hfalse : r2.toNat.testBit m = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr2lt (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [hfalse, Bool.false_or, decide_eq_true hm, decide_eq_true (by omega),
        Bool.true_and, Bool.true_and, hr2 (m - 32) (by omega), show (m - 32) % 8 = m % 8 by omega]
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro d
  rcases (show d < 8 ∨ 8 ≤ d by omega) with hd | hd
  · have hmod : ((r3 >>> UInt64.ofNat (8 * k) &&& 0xff).toUInt8).toNat.testBit d =
        (r3 >>> UInt64.ofNat (8 * k)).toNat.testBit d := by
      change ((_ &&& 255) % 256).testBit d = _
      rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (n := 8) (by decide)), Nat.testBit_and]
      have h255 : (255 : Nat).testBit d = true := by
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [h255]
    have hklt : 8 * k < UInt64.size := Nat.lt_of_lt_of_le (by omega : 8 * k < 64) (by decide)
    rw [hmod, UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' hklt,
      Nat.mod_eq_of_lt (by omega : 8 * k < 64), Nat.testBit_shiftRight, hr3 (8 * k + d) (by omega)]
    have hrem : (8 * k + d) % 8 = d := by omega
    rw [hrem]
  · have hu8 : ((r3 >>> UInt64.ofNat (8 * k) &&& 0xff).toUInt8).toNat < 2 ^ 8 := UInt8.toNat_lt _
    have hL : (((r3 >>> UInt64.ofNat (8 * k) &&& 0xff).toUInt8).toNat.testBit d) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu8 (Nat.pow_le_pow_right (by decide) hd))
    have hR : b.toNat.testBit d = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb8 (Nat.pow_le_pow_right (by decide) hd))
    exact hL.trans hR.symm

/-! ### `copy_back` weakest precondition -/

private structure CopyBackInv (A C : Array UInt8) (o len written : Nat) (B : Array UInt8) : Prop where
  sz : B.size = A.size
  outside : ∀ j, (j < o ∨ o + len + 15 ≤ j) → B[j]? = A[j]?
  pref : ∀ j, j < o + min written len → B[j]? = C[j]?

private theorem CopyBackInv.init (A : Array UInt8) (o dist len : Nat)
    (_hd : 1 ≤ dist) (_hdo : dist ≤ o) (_hlen : o + len ≤ A.size) :
    CopyBackInv A (cpyN len (o - dist) o A) o len 0 A := by
  refine ⟨rfl, fun _ _ => rfl, fun j hj => ?_⟩
  rw [Nat.zero_min, Nat.add_zero] at hj
  exact (cpyN_outside len (o - dist) o A j (Or.inl hj)).symm

private theorem copyBack_memcpy_step {α : Bool} (e : EnvG α) (A B : Array UInt8) (msg : BPtr) (m : UInt32)
    (o dist len written step : Nat)
    (hd : step ≤ dist) (hstep : 1 ≤ step) (hdo : dist ≤ o)
    (hw : written < len) (hroom : o + len + 15 ≤ A.size) (hstep15 : step ≤ 16)
    (inv : CopyBackInv A (cpyN len (o - dist) o A) o len written B) :
    memcpyB (.ref e.ob (o + written)) (.ref e.ob (o + written - dist)) step (e.heap B msg m) =
      .ok ((), e.heap (copyRange B B (o + written) (o + written - dist) step) msg m) ∧
    CopyBackInv A (cpyN len (o - dist) o A) o len (written + step)
      (copyRange B B (o + written) (o + written - dist) step) := by
  let C := cpyN len (o - dist) o A
  have hBsz : B.size = A.size := inv.sz
  have hBroom : o + written + step ≤ B.size := by omega
  have hFrom : o + written - dist + step ≤ B.size := by omega
  have hsep : (e.ob ≠ e.ob ∨ o + written + step ≤ o + written - dist ∨ o + written - dist + step ≤ o + written) :=
    Or.inr (Or.inr (by omega))
  have hcall : memcpyB (.ref e.ob (o + written)) (.ref e.ob (o + written - dist)) step (e.heap B msg m) =
      .ok ((), e.heap (copyRange B B (o + written) (o + written - dist) step) msg m) := by
    have hBg := e.heap_bytes_ob B msg m
    have hro := e.heap_ro_ob B msg m
    unfold memcpyB Ptr.memcpy
    dsimp only
    rw [hBg]
    have hroBool : (Space.ro (e.heap B msg m) e.ob && decide (step ≠ 0)) = false := by simp [hro]
    rw [hroBool]
    have hbnd : o + written + step ≤ B.size ∧ o + written - dist + step ≤ B.size := ⟨hBroom, hFrom⟩
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [if_t hbnd, if_t hsep]
    exact congrArg (fun hp => Except.ok ((), hp))
      ((Space.modify_eq (e.heap B msg m) e.ob B _ hBg).trans (e.heap_put B _ msg m))
  refine ⟨hcall, ?_⟩
  refine ⟨by rw [size_copyRange, hBsz], ?_, ?_⟩
  · intro j hj
    rw [copyRange_getElem? B B (o + written) (o + written - dist) step hFrom hBroom j]
    have hnot : ¬ (o + written ≤ j ∧ j < o + written + step) := by omega
    rw [if_f hnot]
    exact inv.outside j hj
  · intro j hj
    rw [copyRange_getElem? B B (o + written) (o + written - dist) step hFrom hBroom j]
    by_cases hcur : o + written ≤ j ∧ j < o + written + step
    · rw [if_t hcur]
      have hsrcIdx : o + written - dist + (j - (o + written)) < o + min written len := by omega
      have hjLtLen : j < o + len := by omega
      have hjGeO : o ≤ j := by omega
      have hBsrc := inv.pref (o + written - dist + (j - (o + written))) hsrcIdx
      have hBget : B[o + written - dist + (j - (o + written))]! =
          (C[j - dist]?).getD 0 := by
        rw [show o + written - dist + (j - (o + written)) = j - dist by omega] at hBsrc ⊢
        have hlt : j - dist < B.size := by omega
        rw [Array.getElem?_eq_getElem hlt] at hBsrc
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, ← hBsrc]
        rfl
      have hCinv := cpyN_invariant len (o - dist) o A (by omega) (by omega) (by omega) j hjGeO hjLtLen
      have hdistSub : o - (o - dist) = dist := by omega
      rw [hdistSub] at hCinv
      have hCbound : j < C.size := by rw [cpyN_size]; omega
      have hCdist : j - dist < C.size := by rw [cpyN_size]; omega
      rw [Array.getElem?_eq_getElem hCbound] at hCinv ⊢
      rw [Array.getElem?_eq_getElem hCdist] at hCinv hBget
      rw [hBget, Option.getD_some, hCinv]
    · simp only [hcur, ↓reduceIte]
      exact inv.pref j (by omega)

private theorem cond_ptr_lt_u32 {α : Bool} (e : EnvG α) (B : Array UInt8) (msg : BPtr) (m : UInt32)
    (p q : Nat) (hp : p ≤ B.size) (hq : q ≤ B.size) :
    Ptr.lt (.ref e.ob p) (.ref e.ob q) (e.heap B msg m) = .ok (decide (p < q), e.heap B msg m) :=
  Ptr.lt_ok (e.heap_bytes_ob B msg m) hp hq

private theorem cdoWhile_memcpy_loop {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (o dist len : Nat) (step : Nat) (stepI : Int) (hstepI : stepI = (step : Int))
    (hd : step ≤ dist) (hstep : 1 ≤ step) (hstep15 : step ≤ 16)
    (hdo : dist ≤ o) (hroom : o + len + 15 ≤ A.size) :
    ∀ k written (B : Array UInt8) fu,
      written < len → len - written ≤ step * (k + 1) → k ≤ fu →
      CopyBackInv A (cpyN len (o - dist) o A) o len written B →
      ∃ out' from' B',
        cdoWhile.go
          (fun x : BPtr × BPtr => do
            memcpyB x.1 x.2 step
            let out ← x.1.add stepI
            let from_ ← x.2.add stepI
            pure (out, from_))
          (fun x : BPtr × BPtr => do
            let __do_lift ← Ptr.lt x.1 (.ref e.ob (o + len))
            pure (__do_lift, x.1, x.2))
          (fu + 1) (.ref e.ob (o + written), .ref e.ob (o + written - dist)) (e.heap B msg m) =
          .ok ((out', from'), e.heap B' msg m) ∧
        CopyBackInv A (cpyN len (o - dist) o A) o len len B' := by
  intro k
  have runStep : ∀ written (B : Array UInt8), written < len →
      CopyBackInv A (cpyN len (o - dist) o A) o len written B →
      (do
        memcpyB (.ref e.ob (o + written)) (.ref e.ob (o + written - dist)) step
        let out ← Ptr.add (.ref e.ob (o + written)) stepI
        let from_ ← Ptr.add (.ref e.ob (o + written - dist)) stepI
        pure (out, from_)) (e.heap B msg m) =
        .ok ((.ref e.ob (o + written + step), .ref e.ob (o + written - dist + step)),
          e.heap (copyRange B B (o + written) (o + written - dist) step) msg m) ∧
      CopyBackInv A (cpyN len (o - dist) o A) o len (written + step)
        (copyRange B B (o + written) (o + written - dist) step) := by
    intro written B hw inv
    obtain ⟨hmem, inv'⟩ := copyBack_memcpy_step e A B msg m o dist len written step hd hstep hdo hw hroom hstep15 inv
    have hB'sz : _ = A.size := inv'.sz
    have hadd1 := Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by rw [hB'sz]; omega : o + written + step ≤ _)
    have hadd2 := Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by rw [hB'sz]; omega : o + written - dist + step ≤ _)
    refine ⟨?_, inv'⟩
    rw [hstepI, bind_ok hmem, bind_ok hadd1, bind_ok hadd2]
    rfl
  induction k with
  | zero =>
    intro written B fu hw hk _ inv
    obtain ⟨hbody, inv'⟩ := runStep written B hw inv
    have hB'sz : _ = A.size := inv'.sz
    have hlt := cond_ptr_lt_u32 e _ msg m (o + written + step) (o + len) (by rw [hB'sz]; omega) (by rw [hB'sz]; omega)
    have hfalse : decide (o + written + step < o + len) = false := decide_eq_false (by omega)
    rw [cdoWhile.go]
    dsimp only
    rw [bind_ok hbody]
    simp only [bind_app, hlt, hfalse, pure_app, Bool.false_eq_true, ite_false]
    refine ⟨_, _, _, rfl, ?_⟩
    exact ⟨inv'.sz, inv'.outside, fun j hj => inv'.pref j (by rw [Nat.min_eq_right (by omega)] at hj ⊢; exact hj)⟩
  | succ k ih =>
    intro written B fu hw hk hfu inv
    obtain ⟨hbody, inv'⟩ := runStep written B hw inv
    have hB'sz : _ = A.size := inv'.sz
    have hlt := cond_ptr_lt_u32 e _ msg m (o + written + step) (o + len) (by rw [hB'sz]; omega) (by rw [hB'sz]; omega)
    by_cases hdone : written + step < len
    · obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
      have htrue : decide (o + written + step < o + len) = true := decide_eq_true (by omega)
      have hk' : len - (written + step) ≤ step * (k + 1) := by
        have hmul : step * (k + 1 + 1) = step * (k + 1) + step := by rw [Nat.mul_add, Nat.mul_one]
        omega
      obtain ⟨out', from', B'', hgo, inv''⟩ := ih (written + step) _ fu' hdone hk' (by omega) inv'
      have hsubEq : o + written - dist + step = o + (written + step) - dist := by omega
      rw [← hsubEq, ← Nat.add_assoc o written step] at hgo
      rw [cdoWhile.go]
      dsimp only
      rw [bind_ok hbody]
      simp only [bind_app, hlt, htrue, pure_app, ite_true]
      exact ⟨out', from', B'', hgo, inv''⟩
    · have hfalse : decide (o + written + step < o + len) = false := decide_eq_false (by omega)
      rw [cdoWhile.go]
      dsimp only
      rw [bind_ok hbody]
      simp only [bind_app, hlt, hfalse, pure_app, Bool.false_eq_true, ite_false]
      refine ⟨_, _, _, rfl, ?_⟩
      exact ⟨inv'.sz, inv'.outside, fun j hj => inv'.pref j (by rw [Nat.min_eq_right (by omega)] at hj ⊢; exact hj)⟩

private theorem cdoWhile_dist1_loop {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (o len : Nat) (b : UInt8) (hb : A.getD (o - 1) 0 = b)
    (ho : 1 ≤ o) (hroom : o + len + 15 ≤ A.size) :
    let run : UInt64 :=
      let r0 := b.toUInt64
      let r1 := r0 ||| (r0 <<< 8)
      let r2 := r1 ||| (r1 <<< 16)
      r2 ||| (r2 <<< 32)
    ∀ k written (B : Array UInt8) fu,
      written < len → len - written ≤ 8 * (k + 1) → k ≤ fu →
      CopyBackInv A (cpyN len (o - 1) o A) o len written B →
      ∃ out' B',
        cdoWhile.go
          (fun out => do store64 out run; out.add 8)
          (fun out => do pure (← Ptr.lt out (.ref e.ob (o + len)), out))
          (fu + 1) (.ref e.ob (o + written)) (e.heap B msg m) =
          .ok (out', e.heap B' msg m) ∧
        CopyBackInv A (cpyN len (o - 1) o A) o len len B' := by
  intro run k
  have stepLemma : ∀ written (B : Array UInt8), written < len →
      CopyBackInv A (cpyN len (o - 1) o A) o len written B →
      store64 (.ref e.ob (o + written)) run (e.heap B msg m) =
        .ok ((), e.heap (store8Bytes B (o + written) run) msg m) ∧
      CopyBackInv A (cpyN len (o - 1) o A) o len (written + 8)
        (store8Bytes B (o + written) run) := by
    intro written B hw inv
    have hBroom : o + written + 8 ≤ B.size := by rw [inv.sz]; omega
    have hst := store64_ok e B msg m (o + written) run hBroom
    refine ⟨hst, ?_⟩
    refine ⟨by rw [store8Bytes_size, inv.sz], ?_, ?_⟩
    · intro j hj
      rw [store8Bytes_outside _ _ _ (by omega)]
      exact inv.outside j hj
    · intro j hj
      by_cases hcur : o + written ≤ j ∧ j < o + written + 8
      · obtain ⟨t, rfl, ht⟩ : ∃ t, j = o + written + t ∧ t < 8 := ⟨j - (o + written), by omega, by omega⟩
        rw [store8Bytes_at _ _ _ _ ht hBroom]
        have hrep := run_rep_byte b t ht
        dsimp only [run] at hrep ⊢
        rw [hrep]
        have hC := cpyN_dist_one o len A ho (by omega) (o + written + t) (by omega) (by omega)
        have hb' : A[o - 1]? = some b := by
          rw [← hb, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
          rfl
        exact hb'.symm.trans hC.symm
      · rw [store8Bytes_outside _ _ _ (by omega)]
        exact inv.pref j (by omega)
  induction k with
  | zero =>
    intro written B fu hw hk _ inv
    obtain ⟨hst, inv'⟩ := stepLemma written B hw inv
    have hB'sz : _ = A.size := inv'.sz
    have hadd := add_lit_ok 8 8 rfl (e.heap_bytes_ob _ msg m) (by rw [hB'sz]; omega : o + written + 8 ≤ _)
    have hlt := cond_ptr_lt_u32 e _ msg m (o + written + 8) (o + len) (by rw [hB'sz]; omega) (by rw [hB'sz]; omega)
    have hfalse : decide (o + written + 8 < o + len) = false := decide_eq_false (by omega)
    rw [cdoWhile.go, bind_ok (by rw [bind_ok hst]; exact hadd)]
    simp only [bind_app, hlt, hfalse, pure_app, Bool.false_eq_true, ite_false]
    refine ⟨_, _, rfl, ?_⟩
    exact ⟨inv'.sz, inv'.outside, fun j hj => inv'.pref j (by rw [Nat.min_eq_right (by omega)] at hj ⊢; exact hj)⟩
  | succ k ih =>
    intro written B fu hw hk hfu inv
    obtain ⟨hst, inv'⟩ := stepLemma written B hw inv
    have hB'sz : _ = A.size := inv'.sz
    have hadd := add_lit_ok 8 8 rfl (e.heap_bytes_ob _ msg m) (by rw [hB'sz]; omega : o + written + 8 ≤ _)
    have hlt := cond_ptr_lt_u32 e _ msg m (o + written + 8) (o + len) (by rw [hB'sz]; omega) (by rw [hB'sz]; omega)
    by_cases hdone : written + 8 < len
    · obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
      have htrue : decide (o + written + 8 < o + len) = true := decide_eq_true (by omega)
      obtain ⟨out', B'', hgo, inv''⟩ := ih (written + 8) _ fu' hdone (by omega) (by omega) inv'
      rw [cdoWhile.go, bind_ok (by rw [bind_ok hst]; exact hadd)]
      simp only [bind_app, hlt, htrue, pure_app, ite_true]
      exact ⟨out', B'', hgo, inv''⟩
    · have hfalse : decide (o + written + 8 < o + len) = false := decide_eq_false (by omega)
      rw [cdoWhile.go, bind_ok (by rw [bind_ok hst]; exact hadd)]
      simp only [bind_app, hlt, hfalse, pure_app, Bool.false_eq_true, ite_false]
      refine ⟨_, _, rfl, ?_⟩
      exact ⟨inv'.sz, inv'.outside, fun j hj => inv'.pref j (by rw [Nat.min_eq_right (by omega)] at hj ⊢; exact hj)⟩

private theorem cdoWhile_dist27_loop {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (o dist len : Nat) (hdist : 2 ≤ dist) (hd7 : dist ≤ 7) (hdo : dist ≤ o) (hroom : o + len + 15 ≤ A.size) :
    ∀ k written (B : Array UInt8) fu,
      written < len → len - written ≤ dist * (k + 1) → k ≤ fu →
      CopyBackInv A (cpyN len (o - dist) o A) o len written B →
      ∃ out' from' B',
        cdoWhile.go
          (fun x : BPtr × BPtr => do
            let v ← load64 x.2
            store64 x.1 v
            let out ← x.1.add (dist : Int)
            let from_ ← x.2.add (dist : Int)
            pure (out, from_))
          (fun x : BPtr × BPtr => do
            let __do_lift ← Ptr.lt x.1 (.ref e.ob (o + len))
            pure (__do_lift, x.1, x.2))
          (fu + 1) (.ref e.ob (o + written), .ref e.ob (o + written - dist)) (e.heap B msg m) =
          .ok ((out', from'), e.heap B' msg m) ∧
        CopyBackInv A (cpyN len (o - dist) o A) o len len B' := by
  let C := cpyN len (o - dist) o A
  have runStep : ∀ written (B : Array UInt8), written < len →
      CopyBackInv A C o len written B →
      (do
        let v ← load64 (.ref e.ob (o + written - dist))
        store64 (.ref e.ob (o + written)) v
        let out ← Ptr.add (.ref e.ob (o + written)) (dist : Int)
        let from_ ← Ptr.add (.ref e.ob (o + written - dist)) (dist : Int)
        pure (out, from_)) (e.heap B msg m) =
        .ok ((.ref e.ob (o + written + dist), .ref e.ob (o + written - dist + dist)),
          e.heap (store8Bytes B (o + written) (leBytes64 B (o + written - dist))) msg m) ∧
      CopyBackInv A C o len (written + dist)
        (store8Bytes B (o + written) (leBytes64 B (o + written - dist))) := by
    intro written B hw inv
    have hBsz : B.size = A.size := inv.sz
    have hfromRoom : o + written - dist + 8 ≤ B.size := by omega
    have htoRoom : o + written + 8 ≤ B.size := by omega
    have hld := load64_ok (e.heap_bytes_ob B msg m) hfromRoom
    have hst := store64_ok e B msg m (o + written) (leBytes64 B (o + written - dist)) htoRoom
    have hsz' : (store8Bytes B (o + written) (leBytes64 B (o + written - dist))).size = A.size := by
      rw [store8Bytes_size, hBsz]
    have hadd1 := Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by rw [hsz']; omega : o + written + dist ≤ _)
    have hadd2 := Ptr.add_nat_ok (e.heap_bytes_ob _ msg m) (by rw [hsz']; omega : o + written - dist + dist ≤ _)
    refine ⟨by rw [bind_ok hld, bind_ok hst, bind_ok hadd1, bind_ok hadd2]; rfl, ⟨hsz', ?_, ?_⟩⟩
    · intro j hj
      rw [store8Bytes_outside _ _ _ (by omega)]
      exact inv.outside j hj
    · intro j hj
      by_cases hcur : o + written ≤ j ∧ j < o + written + dist
      · obtain ⟨t, rfl, ht⟩ : ∃ t, j = o + written + t ∧ t < dist := ⟨j - (o + written), by omega, by omega⟩
        rw [store8Bytes_at _ _ _ _ (by omega) htoRoom]
        have hbyte : (((leBytes64 B (o + written - dist) >>> UInt64.ofNat (8 * t)) &&& 0xff).toUInt8) =
            B.getD (o + written - dist + t) 0 := by
          apply UInt8.toNat_inj.mp
          apply Nat.eq_of_testBit_eq
          intro d
          rcases (show d < 8 ∨ 8 ≤ d by omega) with hd | hd
          · have hmod : ∀ u : UInt64, ((u &&& 0xff).toUInt8).toNat.testBit d = u.toNat.testBit d := by
              intro u
              change ((u.toNat &&& 255) % 256).testBit d = u.toNat.testBit d
              rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow u.toNat (n := 8) (by decide)), Nat.testBit_and]
              have h255 : (255 : Nat).testBit d = true := by
                rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 by omega) with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
              simp [h255]
            have hklt : 8 * t < UInt64.size := Nat.lt_of_lt_of_le (by omega : 8 * t < 64) (by decide)
            rw [hmod, UInt64.toNat_shiftRight, UInt64.toNat_ofNat_of_lt' hklt,
              Nat.mod_eq_of_lt (by omega : 8 * t < 64), Nat.testBit_shiftRight]
            rw [leBytes64_testBit B (o + written - dist) (8 * t + d) (by omega)]
            have hdiv : (8 * t + d) / 8 = t := by omega
            have hrem : (8 * t + d) % 8 = d := by omega
            rw [hdiv, hrem]
          · have hu8 : ((leBytes64 B (o + written - dist) >>> UInt64.ofNat (8 * t) &&& 0xff).toUInt8).toNat < 2 ^ 8 :=
              UInt8.toNat_lt _
            have hL : (((leBytes64 B (o + written - dist) >>> UInt64.ofNat (8 * t)) &&& 0xff).toUInt8).toNat.testBit d = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu8 (Nat.pow_le_pow_right (by decide) hd))
            have hB8 : (B.getD (o + written - dist + t) 0).toNat < 2 ^ 8 := UInt8.toNat_lt _
            have hR : (B.getD (o + written - dist + t) 0).toNat.testBit d = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hB8 (Nat.pow_le_pow_right (by decide) hd))
            exact hL.trans hR.symm
        rw [hbyte]
        have hsrcIdx : o + written - dist + t < o + min written len := by omega
        have hBsrc := inv.pref (o + written - dist + t) hsrcIdx
        have hjLtLen : o + written + t < o + len := by omega
        have hBget : some (B.getD (o + written - dist + t) 0) = B[o + written - dist + t]? := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
          rfl
        have hCinv := cpyN_invariant len (o - dist) o A (by omega) (by omega) (by omega) (o + written + t) (by omega) hjLtLen
        have hdistSub : o - (o - dist) = dist := by omega
        rw [hdistSub] at hCinv
        have hprevEq : o + written + t - dist = o + written - dist + t := by omega
        rw [hprevEq] at hCinv
        rw [hBget, hBsrc, ← hCinv]
      · rw [store8Bytes_outside _ _ _ (by omega)]
        exact inv.pref j (by omega)
  intro k
  induction k with
  | zero =>
    intro written B fu hw hk _ inv
    obtain ⟨hbody, inv'⟩ := runStep written B hw inv
    have hB'sz : _ = A.size := inv'.sz
    have hlt := cond_ptr_lt_u32 e _ msg m (o + written + dist) (o + len) (by rw [hB'sz]; omega) (by rw [hB'sz]; omega)
    have hfalse : decide (o + written + dist < o + len) = false := decide_eq_false (by omega)
    rw [cdoWhile.go]
    dsimp only
    rw [bind_ok hbody]
    simp only [bind_app, hlt, hfalse, pure_app, Bool.false_eq_true, ite_false]
    refine ⟨_, _, _, rfl, ?_⟩
    exact ⟨inv'.sz, inv'.outside, fun j hj => inv'.pref j (by rw [Nat.min_eq_right (by omega)] at hj ⊢; exact hj)⟩
  | succ k ih =>
    intro written B fu hw hk hfu inv
    obtain ⟨hbody, inv'⟩ := runStep written B hw inv
    have hB'sz : _ = A.size := inv'.sz
    have hlt := cond_ptr_lt_u32 e _ msg m (o + written + dist) (o + len) (by rw [hB'sz]; omega) (by rw [hB'sz]; omega)
    by_cases hdone : written + dist < len
    · obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
      have htrue : decide (o + written + dist < o + len) = true := decide_eq_true (by omega)
      have hk' : len - (written + dist) ≤ dist * (k + 1) := by
        have hmul : dist * (k + 1 + 1) = dist * (k + 1) + dist := by rw [Nat.mul_add, Nat.mul_one]
        omega
      obtain ⟨out', from', B'', hgo, inv''⟩ := ih (written + dist) _ fu' hdone hk' (by omega) inv'
      have hsubEq : o + written - dist + dist = o + (written + dist) - dist := by omega
      rw [← hsubEq, ← Nat.add_assoc o written dist] at hgo
      rw [cdoWhile.go]
      dsimp only
      rw [bind_ok hbody]
      simp only [bind_app, hlt, htrue, pure_app, ite_true]
      exact ⟨out', from', B'', hgo, inv''⟩
    · have hfalse : decide (o + written + dist < o + len) = false := decide_eq_false (by omega)
      rw [cdoWhile.go]
      dsimp only
      rw [bind_ok hbody]
      simp only [bind_app, hlt, hfalse, pure_app, Bool.false_eq_true, ite_false]
      refine ⟨_, _, _, rfl, ?_⟩
      exact ⟨inv'.sz, inv'.outside, fun j hj => inv'.pref j (by rw [Nat.min_eq_right (by omega)] at hj ⊢; exact hj)⟩

/-- `copy_back` writes exact LZ77 match bytes `[o, o + len)` and at most 15 scratch bytes
in `[o + len, o + len + 15)`, preserving the array size and all bytes outside `[o, o + len + 15)`. -/
theorem copy_back_wp {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (o : Nat) (dist len : UInt32)
    (hdist : 1 ≤ dist.toNat) (hdo : dist.toNat ≤ o) (hlen : 1 ≤ len.toNat)
    (hroom : o + len.toNat + 15 ≤ A.size) :
    Wp (copy_back (.ref e.ob o) dist len) (e.heap A msg m)
      (fun p h' => ∃ A', p = .ref e.ob (o + len.toNat) ∧ h' = e.heap A' msg m ∧
        A'.size = A.size ∧
        (∀ j, (j < o ∨ o + len.toNat + 15 ≤ j) → A'[j]? = A[j]?) ∧
        (∀ j, j < o + len.toNat → A'[j]? = (cpyN len.toNat (o - dist.toNat) o A)[j]?)) := by
  have hAg := e.heap_bytes_ob A msg m
  have hsub := subn_ok hAg hdo (by omega)
  have hstop := Ptr.add_nat_ok hAg (by omega : o + len.toNat ≤ A.size)
  have inv0 := CopyBackInv.init A o dist.toNat len.toNat hdist hdo (by omega)
  have hfuel : len.toNat ≤ fuel - 1 := by
    have := UInt32.toNat_lt len
    unfold fuel
    omega
  unfold Wp copy_back
  rw [bind_ok hsub, bind_ok hstop]
  dsimp only
  by_cases h16 : dist ≥ 16
  · have h16n : 16 ≤ dist.toNat := by simpa [UInt32.le_iff_toNat_le] using h16
    simp only [h16, ite_true]
    obtain ⟨out', from', B', hgo, inv'⟩ :=
      cdoWhile_memcpy_loop e A msg m o dist.toNat len.toNat 16 (16 : Int) rfl h16n (by decide) (by decide) hdo hroom
        len.toNat 0 A (fuel - 1) hlen (by omega) hfuel inv0
    simp only [Nat.add_zero] at hgo
    unfold cdoWhile
    rw [← fuel_pred, bind_ok hgo]
    exact ⟨.ref e.ob (o + len.toNat), e.heap B' msg m, rfl, B', rfl, rfl, inv'.sz, inv'.outside,
      fun j hj => inv'.pref j (by simpa using hj)⟩
  · have h16n : dist.toNat < 16 := by
      have : ¬ (16 ≤ dist) := h16
      exact Nat.lt_of_not_ge (fun h => this (UInt32.le_iff_toNat_le.mpr h))
    simp only [h16, ite_false]
    by_cases h8 : dist ≥ 8
    · have h8n : 8 ≤ dist.toNat := by simpa [UInt32.le_iff_toNat_le] using h8
      simp only [h8, ite_true]
      obtain ⟨out', from', B', hgo, inv'⟩ :=
        cdoWhile_memcpy_loop e A msg m o dist.toNat len.toNat 8 (8 : Int) rfl h8n (by decide) (by decide) hdo hroom
          len.toNat 0 A (fuel - 1) hlen (by omega) hfuel inv0
      simp only [Nat.add_zero] at hgo
      unfold cdoWhile
      rw [← fuel_pred, bind_ok hgo]
      exact ⟨.ref e.ob (o + len.toNat), e.heap B' msg m, rfl, B', rfl, rfl, inv'.sz, inv'.outside,
        fun j hj => inv'.pref j (by simpa using hj)⟩
    · have h8n : dist.toNat < 8 := by
        have : ¬ (8 ≤ dist) := h8
        exact Nat.lt_of_not_ge (fun h => this (UInt32.le_iff_toNat_le.mpr h))
      simp only [h8, ite_false]
      by_cases h1 : (dist == 1) = true
      · have h1n : dist.toNat = 1 := by
          have := beq_iff_eq.mp h1
          subst this; rfl
        simp only [h1, ite_true]
        have hld8 := Ptr.load_ok (r := e.ob) hAg (by omega : o - 1 < A.size)
        have hldEq : load8 (Ptr.ref e.ob (o - dist.toNat)) (e.heap A msg m) =
            .ok (A.getD (o - 1) 0, e.heap A msg m) := by
          rw [h1n]; simpa [OkOn, load8, Array.getD_eq_getD_getElem?, show o - 1 < A.size by omega] using hld8
        rw [bind_ok hldEq]
        rw [h1n] at inv0
        obtain ⟨out', B', hgo, inv'⟩ :=
          cdoWhile_dist1_loop e A msg m o len.toNat (A.getD (o - 1) 0) rfl (by omega) hroom
            len.toNat 0 A (fuel - 1) hlen (by omega) hfuel inv0
        simp only [Nat.add_zero] at hgo
        unfold cdoWhile
        rw [← fuel_pred, bind_ok hgo]
        refine ⟨.ref e.ob (o + len.toNat), e.heap B' msg m, rfl, B', rfl, rfl, inv'.sz, inv'.outside, ?_⟩
        intro j hj
        rw [h1n]
        exact inv'.pref j (by simpa using hj)
      · have h2n : 2 ≤ dist.toNat := by
          have : dist ≠ 1 := fun eq => h1 (beq_iff_eq.mpr eq)
          have hd1 : dist.toNat ≠ 1 := fun hn => this (UInt32.toNat_inj.mp hn)
          omega
        simp only [h1, Bool.false_eq_true, ite_false]
        have hmul2 : len.toNat - 0 ≤ dist.toNat * (len.toNat + 1) := by
          have := Nat.mul_le_mul_right (len.toNat + 1) h2n
          omega
        obtain ⟨out', from', B', hgo, inv'⟩ :=
          cdoWhile_dist27_loop e A msg m o dist.toNat len.toNat h2n (by omega) hdo hroom
            len.toNat 0 A (fuel - 1) hlen hmul2 hfuel inv0
        simp only [Nat.add_zero] at hgo
        unfold cdoWhile
        rw [← fuel_pred, bind_ok hgo]
        exact ⟨.ref e.ob (o + len.toNat), e.heap B' msg m, rfl, B', rfl, rfl, inv'.sz, inv'.outside,
          fun j hj => inv'.pref j (by simpa using hj)⟩

end Zlib.Inffast.Proofs
