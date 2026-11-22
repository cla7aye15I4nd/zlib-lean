import ZlibF.Proof.«inffast.c.origin-steps»
import ZlibF.Proof.«inffast.c.copy-back»

/-!
# inffast.c: 64-bit bit buffer invariant, `refill64`, and end-of-loop unpack

Models the `Z_INFLATE_FETCH == 64` bit buffer (`hold8`, `bits`, `in`) via `Inv64`:
`hold8` holds `valid` (`bits ≤ valid ≤ 64`) exact lookahead bits of `Origin.initial e`
starting at cursor `used`. Because bits `[bits, valid)` in `hold8` already match the unread
bytes at `in`, `hold8 |= load64(in) << bits` without masking preserves the bit stream by OR
idempotence (`b || b = b`).
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.Origin
open ZlibF.Spec

/-! ### Frame helper for output-capacity-bounded writes -/

/-- An output array matching `e.A0` outside `[e.o0, cap)` (for `α = false`, `cap = e.o0 + avail_out`;
for `α = true`, `cap = o`) keeps the unread input range intact when input and output alias one block. -/
theorem EnvG.inputFrame_of_cap_frame {α : Bool} (e : EnvG α) {A : Array UInt8} {i o : Nat}
    (size : A.size = e.A0.size)
    (outside : ∀ j, (j < e.o0 ∨ (if α then o else e.o0 + e.sm0.avail_out.toNat) ≤ j) → A[j]? = e.A0[j]?)
    (hi : o ≤ e.o0 + e.sm0.avail_out.toNat) (start : e.i0 ≤ i) : e.InputFrame A i :=
  e.inputFrame_of_frame size outside (by cases α <;> simp [hi]) start

/-! ### Bit-stream and byte-packing helpers -/

theorem inBits_drop_bytes {α : Bool} (e : EnvG α) :
    ∀ (i k : Nat), i + k ≤ e.i0 + e.sm0.avail_in.toNat →
      (inBits e i).drop (8 * k) = inBits e (i + k) := by
  intro i k
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    intro available
    have first : i < e.i0 + e.sm0.avail_in.toNat := by omega
    rw [inBits_pull e i first, show 8 * (k + 1) = 8 + 8 * k by omega, ← List.drop_drop]
    have removed : (byteBits (e.IN.getD i 0) ++ inBits e (i + 1)).drop 8 = inBits e (i + 1) := by
      rw [List.drop_append]
      simp [byteBits]
    rw [removed, ih (i + 1) (by omega)]
    congr 1
    omega

private theorem inBits_length {α : Bool} (e : EnvG α) (i : Nat) :
    (inBits e i).length = 8 * (e.i0 + e.sm0.avail_in.toNat - i) := by
  have hsz := e.hINsz
  unfold inBits bytesToBits
  have hcb : ∀ xs : List UInt8, (xs.flatMap byteBits).length = 8 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, ih,
        byteBits, List.length_map, List.length_range]
      omega
  rw [hcb]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

theorem initial_drop_eq_inBits {e : Env} {u i : Nat}
    (hi0 : e.i0 ≤ i) (hi1 : i ≤ e.i0 + e.sm0.avail_in.toNat)
    (hacc : u = e.s0.bits.toNat + 8 * (i - e.i0)) :
    (initial e).drop u = inBits e i := by
  rw [hacc, initial, Sg, List.drop_append]
  have removed : (bitsOfNat e.s0.hold.toNat e.s0.bits.toNat).drop
      (e.s0.bits.toNat + 8 * (i - e.i0)) = [] :=
    List.drop_eq_nil_of_le (by rw [bitsOfNat_length]; omega)
  rw [removed, List.nil_append, bitsOfNat_length, Nat.add_sub_cancel_left]
  have h := inBits_drop_bytes e e.i0 (i - e.i0) (by omega)
  simpa only [Nat.add_sub_of_le hi0] using h

private theorem drop_take_append_drop {α : Type _} (l : List α) (u n : Nat) :
    ((l.drop u).take n) ++ (l.drop (u + n)) = l.drop u := by
  rw [← List.drop_drop, List.take_append_drop]

private theorem u32_or56_spec :
    ∀ n, n ≤ 63 →
      let b := UInt32.ofNat n
      (b ||| 56).toNat = b.toNat + 8 * ((63 - b.toNat) / 8) ∧
      56 ≤ (b ||| 56).toNat ∧ (b ||| 56).toNat ≤ 63 := by
  have hfin : ∀ k : Fin 64,
      let b := UInt32.ofNat k.val
      (b ||| 56).toNat = b.toNat + 8 * ((63 - b.toNat) / 8) ∧
      56 ≤ (b ||| 56).toNat ∧ (b ||| 56).toNat ≤ 63 := by
    decide +kernel
  intro n hn
  simpa using hfin ⟨n, Nat.lt_succ_of_le hn⟩

theorem u32_or56_eq {b : UInt32} (hb : b.toNat ≤ 63) :
    (b ||| 56).toNat = b.toNat + 8 * ((63 - b.toNat) / 8) ∧
    56 ≤ (b ||| 56).toNat ∧ (b ||| 56).toNat ≤ 63 := by
  have h := u32_or56_spec b.toNat hb
  simpa [UInt32.ofNat_toNat] using h

theorem u32_div8_eq (b : UInt32) : (b >>> 3).toNat = b.toNat / 8 := by
  rw [UInt32.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

theorem u32_shl3_eq {b : UInt32} (hb : b.toNat ≤ 63) : ((b >>> 3) <<< 3).toNat = b.toNat / 8 * 8 := by
  rw [UInt32.toNat_shiftLeft, u32_div8_eq, Nat.shiftLeft_eq]
  change (b.toNat / 8 * 8) % 2 ^ 32 = b.toNat / 8 * 8
  exact Nat.mod_eq_of_lt (by omega)

theorem u32_mod8_eq {b : UInt32} (hb : b.toNat ≤ 63) : (b - ((b >>> 3) <<< 3)).toNat = b.toNat % 8 := by
  rw [u32_toNat_sub (by rw [u32_shl3_eq hb]; omega), u32_shl3_eq hb]
  omega

private theorem bitsOfNat_leBytes64_inArr {e : Env} {A : Array UInt8} {i : Nat}
    (hfr : e.InputFrame A i) (hi8 : i + 8 ≤ e.i0 + e.sm0.avail_in.toNat) :
    bitsOfNat (leBytes64 (e.inArr A) i).toNat 64 = (inBits e i).take 64 := by
  apply List.ext_getElem
  · rw [bitsOfNat_length, List.length_take, inBits_length]
    omega
  · intro j hj1 hj2
    have hj64 : j < 64 := by rw [bitsOfNat_length] at hj1; exact hj1
    simp only [bitsOfNat, List.getElem_map, List.getElem_range]
    rw [leBytes64_testBit (e.inArr A) i j hj64]
    have hq8 : j / 8 < 8 := by omega
    have hget := hfr.get (s := i) (k := i + j / 8) (by omega) (by omega)
    have hinLen : i + j / 8 < e.IN.size := by have := e.hINsz; omega
    have haLen : i + j / 8 < (e.inArr A).size := by rw [e.inArr_size hfr]; exact hinLen
    have hbyteEq : (e.inArr A).getD (i + j / 8) 0 = e.IN.getD (i + j / 8) 0 := by
      simp only [Array.getD_eq_getD_getElem?, hget]
    rw [hbyteEq]
    have hdrop := inBits_drop_bytes e i (j / 8) (by omega)
    have hiq : i + j / 8 < e.i0 + e.sm0.avail_in.toNat := by omega
    rw [inBits_pull e (i + j / 8) hiq] at hdrop
    have hsplit : j = 8 * (j / 8) + j % 8 := (Nat.div_add_mod j 8).symm
    have hjIn : j < (inBits e i).length := by rw [inBits_length]; omega
    have hr8 : j % 8 < 8 := Nat.mod_lt _ (by decide)
    have helem : (inBits e i)[j] = (byteBits (e.IN.getD (i + j / 8) 0) ++ inBits e (i + j / 8 + 1))[j % 8]'(by
        simp [byteBits]; omega) := by
      have hdg : ((inBits e i).drop (8 * (j / 8)))[j % 8]'(by rw [List.length_drop]; omega) =
          (inBits e i)[8 * (j / 8) + j % 8]'(by omega) := List.getElem_drop
      calc
        (inBits e i)[j] = (inBits e i)[8 * (j / 8) + j % 8]'(by omega) := by congr 1
        _ = ((inBits e i).drop (8 * (j / 8)))[j % 8]'(by rw [List.length_drop]; omega) := hdg.symm
        _ = (byteBits (e.IN.getD (i + j / 8) 0) ++ inBits e (i + j / 8 + 1))[j % 8]'(by
          simp [byteBits]; omega) := by congr 1
    rw [List.getElem_take, helem, List.getElem_append_left (by simp [byteBits]; exact hr8)]
    simp [byteBits]

/-! ### 64-bit bit-buffer invariant (`Inv64`) -/

/-- Exact 64-bit bit-buffer invariant for the `Z_INFLATE_FETCH == 64` loop:
- `hold` holds `valid` lookahead bits (`bits ≤ valid ≤ 64`),
- the low `bits` bits are guaranteed buffered from entry bytes `[i0, i)`,
- all `valid` bits in `hold` match `(Origin.initial e).drop used |>.take valid`. -/
structure Inv64 (e : Env) (hold : UInt64) (bits : UInt32) (i used valid : Nat) : Prop where
  bitsLe : bits.toNat ≤ valid
  validLe : valid ≤ 64
  holdLt : hold.toNat < 2 ^ valid
  inputLower : e.i0 ≤ i
  inputUpper : i ≤ e.i0 + e.sm0.avail_in.toNat
  accounting : used + bits.toNat = e.s0.bits.toNat + 8 * (i - e.i0)
  stream : bitsOfNat hold.toNat valid = ((initial e).drop used).take valid

theorem Inv64.init (e : Env) : Inv64 e e.s0.hold e.s0.bits e.i0 0 e.s0.bits.toNat := by
  refine ⟨Nat.le_refl _, by have := e.hbits; omega, e.hhold, Nat.le_refl _, by omega, by simp, ?_⟩
  simp only [List.drop_zero, initial, Sg]
  rw [List.take_append_of_le_length (by rw [bitsOfNat_length]; exact Nat.le_refl _)]
  exact (List.take_of_length_le (by rw [bitsOfNat_length]; exact Nat.le_refl _)).symm

theorem Inv64.testBit {e : Env} {hold : UInt64} {bits : UInt32} {i u valid j : Nat}
    (inv : Inv64 e hold bits i u valid) (hj : j < valid) :
    some (hold.toNat.testBit j) = ((initial e).drop u)[j]? := by
  have hjBits : j < (bitsOfNat hold.toNat valid).length := by rw [bitsOfNat_length]; exact hj
  have htake : j < (((initial e).drop u).take valid).length := by
    rw [← inv.stream]; exact hjBits
  have hget := congrArg (fun xs : List Bool => xs[j]?) inv.stream
  rw [List.getElem?_eq_getElem hjBits, List.getElem?_eq_getElem htake] at hget
  simp only [bitsOfNat, List.getElem_map, List.getElem_range, List.getElem_take] at hget
  rw [hget]
  have hjDrop : j < ((initial e).drop u).length := by
    rw [List.length_take] at htake; omega
  rw [List.getElem?_eq_getElem hjDrop]

theorem Inv64.take_eq {e : Env} {hold : UInt64} {bits : UInt32} {i u valid k : Nat}
    (inv : Inv64 e hold bits i u valid) (hk : k ≤ valid) :
    bitsOfNat hold.toNat k = ((initial e).drop u).take k := by
  have h1 : (bitsOfNat hold.toNat valid).take k = bitsOfNat hold.toNat k := by
    simp only [bitsOfNat, ← List.map_take, List.take_range, Nat.min_eq_left hk]
  have h2 : (((initial e).drop u).take valid).take k = ((initial e).drop u).take k := by
    rw [List.take_take, Nat.min_eq_left hk]
  rw [← h1, inv.stream, h2]

theorem Inv64.readBits {e : Env} {hold : UInt64} {bits : UInt32} {i u valid k : Nat}
    (inv : Inv64 e hold bits i u valid) (hk : k ≤ valid) :
    ZlibF.Spec.readBits k ((initial e).drop u) =
      some (hold.toNat % 2 ^ k, (initial e).drop (u + k)) := by
  have hsplit : (initial e).drop u = bitsOfNat hold.toNat valid ++ (initial e).drop (u + valid) := by
    rw [inv.stream]
    exact (drop_take_append_drop (initial e) u valid).symm
  rw [hsplit, readBits_bitsOfNat k valid hold.toNat ((initial e).drop (u + valid)) hk]
  congr 1
  congr 1
  rw [bitsOfNat_drop _ _ _ hk, inv.stream]
  have hd : (((initial e).drop u).take valid).drop k = ((initial e).drop (u + k)).take (valid - k) := by
    rw [List.drop_take, List.drop_drop, Nat.add_comm]
  rw [hd]
  simpa only [show u + k + (valid - k) = u + valid by omega] using
    drop_take_append_drop (initial e) (u + k) (valid - k)

theorem Inv64.drop {e : Env} {hold : UInt64} {bits : UInt32} {i u valid : Nat}
    (inv : Inv64 e hold bits i u valid) (k : UInt32) (hk : k.toNat ≤ bits.toNat)
    (hk64 : k.toNat < 64) :
    Inv64 e (hold >>> k.toUInt64) (bits - k) i (u + k.toNat) (valid - k.toNat) := by
  have hble := inv.bitsLe
  have hkValid : k.toNat ≤ valid := by omega
  have hsub : (bits - k).toNat = bits.toNat - k.toNat := u32_toNat_sub hk
  have hshr : (hold >>> k.toUInt64).toNat = hold.toNat / 2 ^ k.toNat := u64_shr hk64
  refine ⟨by rw [hsub]; omega, by have := inv.validLe; omega, ?_, inv.inputLower, inv.inputUpper, ?_, ?_⟩
  · rw [hshr]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k.toNat)).mpr
    rw [← Nat.pow_add, Nat.sub_add_cancel hkValid]
    exact inv.holdLt
  · rw [hsub]; have := inv.accounting; omega
  · rw [hshr, bitsOfNat_drop _ _ _ hkValid, inv.stream, List.drop_take, List.drop_drop, Nat.add_comm]

theorem Inv64.mask_val {hold : UInt64} {k : UInt32} (hk : k.toNat < 32) :
    (hold &&& (((1 : UInt32) <<< k) - 1).toUInt64).toNat = hold.toNat % 2 ^ k.toNat :=
  hold_low64 hk

theorem Inv64.mask32_val {hold : UInt64} {k : UInt32} (hk : k.toNat < 32) :
    (hold.toUInt32 &&& (((1 : UInt32) <<< k) - 1)).toNat = hold.toNat % 2 ^ k.toNat :=
  hold_low32 hk

/-! ### `refill64` weakest precondition -/

/-- `refill64` loads 8 bytes from `in`, ORs them shifted left by `bits` into `hold`, advances `in`
by `(63 - bits) >>> 3`, and sets `bits := bits ||| 56`. Because bits `[bits, valid)` in `hold`
already agree with `in`, unmasked ORing is exact and restores `valid = 64`. -/
theorem refill64_wp {e : Env} (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i u valid : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i)
    (hb63 : l.bits.toNat ≤ 63)
    (hi8 : i + 8 ≤ e.i0 + e.sm0.avail_in.toNat)
    (hfr : e.InputFrame A i) :
    Wp (refill64 l) (e.heap A msg m) (fun l' h' =>
      let adv := (63 - l.bits.toNat) / 8
      h' = e.heap A msg m ∧
      l' = { l with
        in_ := .ref e.ib (i + adv),
        hold := l.hold ||| (leBytes64 (e.inArr A) i <<< l.bits.toUInt64),
        bits := l.bits ||| 56 } ∧
      (l.bits ||| 56).toNat = l.bits.toNat + 8 * adv ∧
      56 ≤ (l.bits ||| 56).toNat ∧ (l.bits ||| 56).toNat ≤ 63 ∧
      adv ≤ 7 ∧ i + adv ≤ e.i0 + e.sm0.avail_in.toNat ∧
      Inv64 e l'.hold l'.bits (i + adv) u 64) := by
  let w := leBytes64 (e.inArr A) i
  let adv := (63 - l.bits.toNat) / 8
  have hadv7 : adv ≤ 7 := by dsimp only [adv]; omega
  have hInSz : (e.inArr A).size = e.IN.size := e.inArr_size hfr
  have hInRoom : i + 8 ≤ (e.inArr A).size := by have := e.hINsz; omega
  have hload := load64_ok (e.heap_bytes_in A msg m) hInRoom
  have hshl := shl64_eq (x := w) (n := l.bits.toUInt64)
    (by rw [UInt32.toNat_toUInt64]; omega)
  have hsub63 : (63 - l.bits).toNat = 63 - l.bits.toNat := by
    rw [u32_toNat_sub (by change l.bits.toNat ≤ 63; exact hb63)]
    rfl
  have hadvEq : ((63 - l.bits) >>> 3).toNat = adv := by
    rw [u32_div8_eq, hsub63]
  have hadd := Ptr.add_nat_ok (h := e.heap A msg m) (r := e.ib) (a := e.inArr A)
    (off := i) (n := ((63 - l.bits) >>> 3).toNat) (e.heap_bytes_in A msg m) (by omega)
  obtain ⟨horEq, h56, h63⟩ := u32_or56_eq hb63
  change (l.bits ||| 56).toNat = l.bits.toNat + 8 * adv at horEq
  have hinvNew : Inv64 e (l.hold ||| (w <<< l.bits.toUInt64)) (l.bits ||| 56) (i + adv) u 64 := by
    refine ⟨by omega, Nat.le_refl _, UInt64.toNat_lt _, by have := inv.inputLower; omega, by omega, ?_, ?_⟩
    · rw [horEq]; have := inv.accounting; have := inv.inputLower; omega
    · apply List.ext_getElem
      · rw [bitsOfNat_length, List.length_take]
        have hdrop : u + 64 ≤ (initial e).length := by
          have hlo := inv.inputLower
          have hu : u + l.bits.toNat = e.s0.bits.toNat + 8 * (i - e.i0) := inv.accounting
          have hin0 : (inBits e e.i0).length = 8 * e.sm0.avail_in.toNat := by
            rw [inBits_length e e.i0, Nat.add_sub_cancel_left]
          have hinitL : (initial e).length = e.s0.bits.toNat + 8 * e.sm0.avail_in.toNat := by
            rw [initial, Sg, List.length_append, bitsOfNat_length, hin0]
          rw [hinitL]
          omega
        rw [List.length_drop]; omega
      · intro j hj1 hj2
        have hj64 : j < 64 := by rw [bitsOfNat_length] at hj1; exact hj1
        have hjDrop : j < ((initial e).drop u).length := by
          rw [List.length_take] at hj2; omega
        simp only [bitsOfNat, List.getElem_map, List.getElem_range, List.getElem_take]
        rw [UInt64.toNat_or, Nat.testBit_or]
        have hsl : (w <<< l.bits.toUInt64).toNat.testBit j =
            (decide (l.bits.toNat ≤ j) && w.toNat.testBit (j - l.bits.toNat)) := by
          have hlt64 : l.bits.toNat < UInt64.size := Nat.lt_of_le_of_lt hb63 (by decide)
          rw [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (by omega : l.bits.toNat < 64),
            Nat.testBit_mod_two_pow]
          have hd64 : decide (j < 64) = true := decide_eq_true hj64
          rw [Nat.testBit_shiftLeft]
          by_cases hlj : l.bits.toNat ≤ j
          · simp [hd64, hlj]
          · simp [hd64, hlj]
        rw [hsl]
        have hwBit : ∀ m, m < 64 - l.bits.toNat →
            some (w.toNat.testBit m) = ((initial e).drop (u + l.bits.toNat))[m]? := by
          intro m hm
          have hm64 : m < 64 := by omega
          have hbitsEq := congrArg (fun xs : List Bool => xs[m]?) (bitsOfNat_leBytes64_inArr hfr hi8)
          have hmLen : m < (bitsOfNat w.toNat 64).length := by rw [bitsOfNat_length]; exact hm64
          have hmTake : m < ((inBits e i).take 64).length := by
            rw [List.length_take, inBits_length]; omega
          rw [List.getElem?_eq_getElem hmLen, List.getElem?_eq_getElem hmTake] at hbitsEq
          simp only [bitsOfNat, List.getElem_map, List.getElem_range, List.getElem_take] at hbitsEq
          rw [initial_drop_eq_inBits inv.inputLower inv.inputUpper inv.accounting]
          have hmIn : m < (inBits e i).length := by rw [inBits_length]; omega
          rw [List.getElem?_eq_getElem hmIn]
          exact hbitsEq
        by_cases hlj : l.bits.toNat ≤ j
        · rw [decide_eq_true hlj, Bool.true_and]
          have hwSome := hwBit (j - l.bits.toNat) (by omega)
          have hshiftIdx : ((initial e).drop (u + l.bits.toNat))[j - l.bits.toNat]? =
              some (((initial e).drop u)[j]'hjDrop) := by
            rw [← List.drop_drop, List.getElem?_drop, Nat.add_sub_of_le hlj, List.getElem?_eq_getElem hjDrop]
          rw [hshiftIdx, Option.some.injEq] at hwSome
          rw [hwSome]
          by_cases hjv : j < valid
          · have hprev := inv.testBit hjv
            rw [List.getElem?_eq_getElem hjDrop, Option.some.injEq] at hprev
            rw [hprev, Bool.or_self]
          · have hhi : valid ≤ j := by omega
            have hfalse : l.hold.toNat.testBit j = false :=
              Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le inv.holdLt (Nat.pow_le_pow_right (by decide) hhi))
            rw [hfalse, Bool.false_or]
        · have hjv : j < valid := by have := inv.bitsLe; omega
          have hprev := inv.testBit hjv
          rw [List.getElem?_eq_getElem hjDrop, Option.some.injEq] at hprev
          simp [hlj, hprev]
  unfold Wp refill64
  rw [hlIn, bind_ok hload, hshl, M_pure_bind, bind_ok hadd, hadvEq]
  exact ⟨_, _, rfl, rfl, rfl, horEq, h56, h63, hadv7, by omega, hinvNew⟩

/-! ### Unpack at end of 64-bit loop (`len = bits >>> 3; in -= len; bits -= len << 3; hold &= (1U << bits) - 1;`) -/

/-- The 4-statement byte-unpack sequence converts `Inv64 e hold bits i u valid` (`bits ≤ 63`)
into exact `LS e l' i' o` and `Origin.Inv e hold'.toNat bits'.toNat i' u` with `bits' < 8`
and `i' = i - bits / 8`. -/
theorem unpack64_wp {e : Env} (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (in_ out : BPtr) (hold : UInt64) (bits : UInt32) (i o u valid : Nat)
    (inv : Inv64 e hold bits i u valid)
    (hin : in_ = .ref e.ib i) (hout : out = .ref e.ob o)
    (hb63 : bits.toNat ≤ 63) (ho0 : e.o0 ≤ o)
    (hfr : e.InputFrame A i) :
    Wp (do
      let len := bits >>> 3
      let in_ ← subn in_ len
      let bits := bits - (len <<< 3)
      let hold := hold &&& ((← shl32 1 bits) - 1).toUInt64
      pure (in_, bits, hold)) (e.heap A msg m) (fun res h' =>
      let i' := i - bits.toNat / 8
      let bits' := bits - ((bits >>> 3) <<< 3)
      let hold' := hold &&& (((1 : UInt32) <<< bits') - 1).toUInt64
      h' = e.heap A msg m ∧
      res = (.ref e.ib i', bits', hold') ∧
      i' = i - bits.toNat / 8 ∧ bits.toNat / 8 ≤ i - e.i0 ∧
      bits'.toNat = bits.toNat % 8 ∧ bits'.toNat < 8 ∧
      hold'.toNat = hold.toNat % 2 ^ bits'.toNat ∧
      e.i0 ≤ i' ∧ i' ≤ e.i0 + e.sm0.avail_in.toNat ∧
      LS e (L.mk (.ref e.ib i') out hold' bits' default 0 0 0 default false false false) i' o ∧
      Origin.Inv e hold'.toNat bits'.toNat i' u) := by
  let len := bits >>> 3
  let bits' := bits - (len <<< 3)
  let hold' := hold &&& (((1 : UInt32) <<< bits') - 1).toUInt64
  have hlen : len.toNat = bits.toNat / 8 := u32_div8_eq bits
  have hback : bits.toNat / 8 ≤ i - e.i0 := by
    have hacc := inv.accounting
    have hb0 := e.hbits
    omega
  have hi0' : e.i0 ≤ i - bits.toNat / 8 := by have := inv.inputLower; omega
  have hi1' : i - bits.toNat / 8 ≤ e.i0 + e.sm0.avail_in.toNat := by
    have := inv.inputUpper; omega
  have hInSz : (e.inArr A).size = e.IN.size := e.inArr_size hfr
  have hsub := subn_ok (h := e.heap A msg m) (r := e.ib) (a := e.inArr A)
    (e.heap_bytes_in A msg m) (n := len) (off := i) (by rw [hlen]; omega)
    (by have := inv.inputUpper; have := e.hINsz; omega)
  have hbits' : bits'.toNat = bits.toNat % 8 := u32_mod8_eq hb63
  have hbits8 : bits'.toNat < 8 := by rw [hbits']; omega
  have hshl := shl32_eq (x := 1) (n := bits') (by omega)
  have hholdLt : hold'.toNat < 2 ^ bits'.toNat := by
    dsimp only [hold']
    rw [Inv64.mask_val (by omega)]
    exact Nat.mod_lt _ (Nat.two_pow_pos bits'.toNat)
  have hholdEq : hold'.toNat = hold.toNat % 2 ^ bits'.toNat := Inv64.mask_val (by omega)
  have hacc' : u + bits'.toNat = e.s0.bits.toNat + 8 * (i - bits.toNat / 8 - e.i0) := by
    have := inv.accounting
    have := inv.inputLower
    omega
  have hdropTail : (initial e).drop (u + bits'.toNat) = inBits e (i - bits.toNat / 8) :=
    initial_drop_eq_inBits hi0' hi1' hacc'
  have hsg : Sg e hold'.toNat bits'.toNat (i - bits.toNat / 8) = (initial e).drop u := by
    unfold Sg
    have htake : bitsOfNat hold'.toNat bits'.toNat = ((initial e).drop u).take bits'.toNat := by
      have hmodBits : bitsOfNat hold'.toNat bits'.toNat = bitsOfNat hold.toNat bits'.toNat := by
        dsimp only [hold']
        rw [Inv64.mask_val (by omega)]
        unfold bitsOfNat
        apply List.map_congr_left
        intro j hj
        have hjb := List.mem_range.mp hj
        simp [Nat.testBit_mod_two_pow, hjb]
      rw [hmodBits]
      exact inv.take_eq (by have := inv.bitsLe; omega)
    rw [htake, ← hdropTail]
    exact drop_take_append_drop (initial e) u bits'.toNat
  have hls : LS e (L.mk (.ref e.ib (i - bits.toNat / 8)) out hold' bits' default 0 0 0 default false false false)
      (i - bits.toNat / 8) o := by
    refine ⟨rfl, hout, hi0', hi1', ho0, ?_, hholdLt, ?_⟩
    · change bits'.toNat ≤ 30; omega
    · change bits'.toNat + 8 * e.i0 ≤ e.s0.bits.toNat + 8 * (i - bits.toNat / 8)
      have := inv.inputLower
      omega
  have horigin : Origin.Inv e hold'.toNat bits'.toNat (i - bits.toNat / 8) u :=
    ⟨hi0', hi1', hholdLt, hacc', hsg⟩
  unfold Wp
  dsimp only
  rw [hin, bind_ok hsub, hlen, hshl]
  exact ⟨_, _, rfl, rfl, rfl, rfl, hback, hbits', hbits8, hholdEq, hi0', hi1', hls, horigin⟩

end Zlib.Inffast.Proofs
