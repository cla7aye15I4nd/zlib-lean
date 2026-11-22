import ZlibF.Proof.«inffast.c.fast64-bits»
import ZlibF.Proof.«inffast.c.lp»
import ZlibF.Spec.Functional.Inflate.InflateFastLengthSemantics

/-!
# inffast.c: one iteration of the 64-bit loop (`Z_INFLATE_FETCH == 64`)

Proves safety, bit-buffer preservation (`Inv64`), bounded cursor progress, output framing,
and lookup/match trace for `copyMatch8`, `dodist8`, `dolen8`, and `inflate_fast_body8`.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.Origin
open ZlibF.Spec

/-! ### Bit, table, and array congruence helpers -/

private theorem wp_bind_ok {α β : Type _} {f : M α} {g : α → M β} {h h1 : Heap} {a : α}
    {Q : β → Heap → Prop} (hf : f h = .ok (a, h1)) :
    Wp (f >>= g) h Q = Wp (g a) h1 Q :=
  propext ⟨fun ⟨b, h2, hrb, hq⟩ => by rw [bind_ok hf] at hrb; exact ⟨b, h2, hrb, hq⟩,
           fun ⟨b, h2, hrb, hq⟩ => ⟨b, h2, by rw [bind_ok hf, hrb], hq⟩⟩

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

private theorem mod_div_mod_two_pow (x b c d : Nat) (h : c + d ≤ b) :
    ((x % 2 ^ b) / 2 ^ c) % 2 ^ d = (x / 2 ^ c) % 2 ^ d := by
  have h1 : x = x % 2 ^ b + 2 ^ b * (x / 2 ^ b) := (Nat.mod_add_div x (2 ^ b)).symm
  have hdiv : x / 2 ^ c = (x % 2 ^ b) / 2 ^ c + 2 ^ (b - c) * (x / 2 ^ b) := by
    have hmul : 2 ^ b * (x / 2 ^ b) = 2 ^ c * (2 ^ (b - c) * (x / 2 ^ b)) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    calc
      x / 2 ^ c = (x % 2 ^ b + 2 ^ b * (x / 2 ^ b)) / 2 ^ c := by rw [← h1]
      _ = (x % 2 ^ b + 2 ^ c * (2 ^ (b - c) * (x / 2 ^ b))) / 2 ^ c := by rw [hmul]
      _ = (x % 2 ^ b) / 2 ^ c + 2 ^ (b - c) * (x / 2 ^ b) :=
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos c)
  rw [hdiv]
  have hd2 : 2 ^ d ∣ 2 ^ (b - c) * (x / 2 ^ b) :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_mul_right _ _)
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd2, Nat.add_zero, Nat.mod_mod]

private theorem bitsOfNat_eq_of_testBit {x y b : Nat}
    (h : ∀ j, j < b → x.testBit j = y.testBit j) : x % 2 ^ b = y % 2 ^ b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < b
  · simp [Nat.testBit_mod_two_pow, hj, h j hj]
  · simp [Nat.testBit_mod_two_pow, hj]

theorem Inv64.hold_mod_eq {e : Env} {h1 : UInt64} {b1 : UInt32} {i1 v1 : Nat}
    {h2 : UInt64} {b2 : UInt32} {i2 v2 u k : Nat}
    (inv1 : Inv64 e h1 b1 i1 u v1) (inv2 : Inv64 e h2 b2 i2 u v2)
    (hk1 : k ≤ v1) (hk2 : k ≤ v2) :
    h1.toNat % 2 ^ k = h2.toNat % 2 ^ k := by
  apply bitsOfNat_eq_of_testBit
  intro j hj
  have p1 := inv1.testBit (by omega : j < v1)
  have p2 := inv2.testBit (by omega : j < v2)
  exact Option.some.inj (p1.trans p2.symm)

theorem Inv64.sg_mod {e : Env} {hold : UInt64} {bits : UInt32} {i u valid : Nat}
    (inv : Inv64 e hold bits i u valid) :
    Sg e (hold.toNat % 2 ^ bits.toNat) bits.toNat i = (initial e).drop u := by
  unfold Sg
  have htake : bitsOfNat (hold.toNat % 2 ^ bits.toNat) bits.toNat =
      ((initial e).drop u).take bits.toNat := by
    have hm : bitsOfNat (hold.toNat % 2 ^ bits.toNat) bits.toNat = bitsOfNat hold.toNat bits.toNat := by
      unfold bitsOfNat
      apply List.map_congr_left
      intro j hj
      have hb := List.mem_range.mp hj
      simp [Nat.testBit_mod_two_pow, hb]
    rw [hm]
    exact inv.take_eq inv.bitsLe
  rw [htake, ← initial_drop_eq_inBits inv.inputLower inv.inputUpper inv.accounting]
  rw [← List.drop_drop, List.take_append_drop]

private theorem lenRoot_info {e : Env} (hts : LenTableSafe e.LCA e.ol e.s0.lenbits.toNat)
    (kidx : Nat) (hk : kidx < 2 ^ e.s0.lenbits.toNat) :
    e.ol + kidx < e.LCA.size ∧
    ((LenLink (e.LCA.getD (e.ol + kidx) default) →
        LinkOK LenLeaf e.LCA e.ol (e.LCA.getD (e.ol + kidx) default)) ∧
     (¬ LenLink (e.LCA.getD (e.ol + kidx) default) →
        LenLeaf 0 (e.LCA.getD (e.ol + kidx) default))) := by
  obtain ⟨_, hsz, hall⟩ := hts
  refine ⟨by omega, ?_⟩
  have hh := hall kidx hk
  by_cases hl : LenLink (e.LCA.getD (e.ol + kidx) default)
  · rw [ite_eq_left hl] at hh
    exact ⟨fun _ => hh, fun h => absurd hl h⟩
  · rw [ite_eq_right hl] at hh
    exact ⟨fun h => absurd h hl, fun _ => hh⟩

theorem blitN_outside (S : Array UInt8) : ∀ n fo oo (A : Array UInt8) j,
    (j < oo ∨ oo + n ≤ j) → (blitN S n fo oo A)[j]? = A[j]?
  | 0, _, _, _, _, _ => rfl
  | n + 1, fo, oo, A, j, hj => by
    simp only [blitN]
    rw [blitN_outside S n (fo + 1) (oo + 1) _ j (by omega)]
    simp [show oo ≠ j by omega]

theorem blitN_eq_prefix (S : Array UInt8) : ∀ n fo oo (B C : Array UInt8),
    fo + n ≤ S.size → oo + n ≤ B.size → B.size = C.size →
    (∀ j, j < oo → B[j]? = C[j]?) →
    ∀ j, j < oo + n → (blitN S n fo oo B)[j]? = (blitN S n fo oo C)[j]? := by
  intro n fo oo B C hfo hoo hsz hpre j hj
  rw [blitN_getElem? S n fo oo B hfo hoo j, blitN_getElem? S n fo oo C hfo (by omega) j]
  by_cases hcur : oo ≤ j ∧ j < oo + n
  · rw [if_t hcur, if_t hcur]
  · rw [if_f hcur, if_f hcur]
    exact hpre j (by omega)

theorem cpyN_eq_prefix : ∀ n fo oo (B C : Array UInt8),
    fo < oo → oo + n ≤ B.size → B.size = C.size →
    (∀ j, j < oo → B[j]? = C[j]?) →
    ∀ j, j < oo + n → (cpyN n fo oo B)[j]? = (cpyN n fo oo C)[j]?
  | 0, _, oo, B, C, _, _, _, hpre, j, hj => hpre j hj
  | n + 1, fo, oo, B, C, hfo, hoo, hsz, hpre, j, hj => by
    simp only [cpyN]
    apply cpyN_eq_prefix n (fo + 1) (oo + 1) _ _ (by omega) (by simp; omega) (by simp; omega) _ j
      (by omega)
    intro j' hj'
    by_cases heq : oo = j'
    · subst j'
      have hBfo : B[fo]? = some (B.getD fo 0) := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]; rfl
      have hCfo : C[fo]? = some (C.getD fo 0) := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]; rfl
      have hget : B.getD fo 0 = C.getD fo 0 := by
        have hp := hpre fo hfo
        rw [hBfo, hCfo, Option.some.injEq] at hp
        exact hp
      have h1 : (B.set! oo (B.getD fo 0))[oo]? = some (B.getD fo 0) := by
        simp [Array.set!, Array.setIfInBounds, show oo < B.size by omega]
      have h2 : (C.set! oo (C.getD fo 0))[oo]? = some (C.getD fo 0) := by
        simp [Array.set!, Array.setIfInBounds, show oo < C.size by omega]
      rw [h1, h2, hget]
    · have hp := hpre j' (by omega)
      simp [Array.set!, Array.setIfInBounds, show oo < B.size by omega, show oo < C.size by omega,
        heq, hp]

/-! ### `copyMatch8` weakest precondition -/

private theorem copyMatch8_tail_wp (e : Env) (A B target : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (o o_cur fo op0 len0 : Nat)
    (hwb : BRef.blk e.wb ≠ e.ob) (hWb : e.h0.bytes e.wb = some e.W)
    (hout : l.out = .ref e.ob o_cur) (hfrom : l.from_ = .ref (.blk e.wb) fo)
    (hop : l.op.toNat = op0) (hlen : l.len.toNat = len0)
    (hop1 : 1 ≤ op0) (hlen1 : 1 ≤ len0) (hdist1 : 1 ≤ l.dist.toNat)
    (hoo : o ≤ o_cur) (hroom : o_cur + len0 + 15 ≤ A.size)
    (hBsz : B.size = A.size) (hTsz : target.size = A.size)
    (hBout : ∀ j, (j < o ∨ o_cur ≤ j) → B[j]? = A[j]?)
    (hBpre : ∀ j, j < o_cur → B[j]? = target[j]?)
    (hWroom : fo + min op0 len0 ≤ e.W.size)
    (hdo : min op0 len0 < len0 → l.dist.toNat ≤ o_cur + op0) :
    Wp (do
      let mut l := l
      if l.op > l.len then l := { l with op := l.len }
      memcpyB l.out l.from_ l.op.toNat
      l := { l with out := ← l.out.add l.op.toNat, len := l.len - l.op }
      if l.len != 0 then
        l := { l with out := ← copy_back l.out l.dist l.len }
      pure l) (e.heap B msg m) (fun l' h' =>
      ∃ A', l' = { l with out := .ref e.ob (o_cur + len0),
                          op := if op0 > len0 then l.len else l.op,
                          len := l.len - (if op0 > len0 then l.len else l.op) } ∧
      h' = e.heap A' msg m ∧
      A'.size = A.size ∧
      (∀ j, (j < o ∨ o_cur + len0 + 15 ≤ j) → A'[j]? = A[j]?) ∧
      (∀ j, j < o_cur + len0 →
        A'[j]? = (cpyN (len0 - min op0 len0) (o_cur + min op0 len0 - l.dist.toNat) (o_cur + min op0 len0)
          (blitN e.W (min op0 len0) fo o_cur target))[j]?)) := by
  have hWg : Space.get e.h0 (BRef.blk e.wb) = some e.W := hWb
  let opUsed := if op0 > len0 then l.len else l.op
  have hopUsed : opUsed.toNat = min op0 len0 := by
    dsimp only [opUsed]
    split <;> omega
  have hmin1 : 1 ≤ min op0 len0 := by omega
  have hmem := memcpyB_env_ok e B msg m (BRef.blk e.wb) e.W o_cur fo (min op0 len0)
    hWg (Or.inl hwb) (fun h => absurd h hwb) (by omega) hWroom
  let B1 := copyRange B e.W o_cur fo (min op0 len0)
  have hB1Eq : B1 = blitN e.W (min op0 len0) fo o_cur B :=
    copyRange_eq_blitN B e.W o_cur fo (min op0 len0) hWroom (by omega)
  have hB1sz : B1.size = A.size := by rw [hB1Eq, blitN_size, hBsz]
  have hB1out : ∀ j, (j < o ∨ o_cur + min op0 len0 ≤ j) → B1[j]? = A[j]? := by
    intro j hj
    rw [hB1Eq, blitN_outside _ _ _ _ _ j (by omega)]
    exact hBout j (by omega)
  have hB1pre : ∀ j, j < o_cur + min op0 len0 →
      B1[j]? = (blitN e.W (min op0 len0) fo o_cur target)[j]? := by
    intro j hj
    rw [hB1Eq]
    exact blitN_eq_prefix e.W (min op0 len0) fo o_cur B target hWroom (by omega) (by omega) hBpre j hj
  have hadd := Ptr.add_nat_ok (e.heap_bytes_ob B1 msg m) (by omega : o_cur + min op0 len0 ≤ B1.size)
  dsimp only
  have hprog :
      (if l.op > l.len then do
        memcpyB l.out l.from_ l.len.toNat
        let __do_lift ← Ptr.add l.out (l.len.toNat : Int)
        if (l.len - l.len != 0) = true then do
          let __do_lift ← copy_back __do_lift l.dist (l.len - l.len)
          pure { l with out := __do_lift, op := l.len, len := l.len - l.len }
        else
          pure { l with out := __do_lift, op := l.len, len := l.len - l.len }
      else do
        memcpyB l.out l.from_ l.op.toNat
        let __do_lift ← Ptr.add l.out (l.op.toNat : Int)
        if (l.len - l.op != 0) = true then do
          let __do_lift ← copy_back __do_lift l.dist (l.len - l.op)
          pure { l with out := __do_lift, op := l.op, len := l.len - l.op }
        else
          pure { l with out := __do_lift, op := l.op, len := l.len - l.op }) =
      (do
        memcpyB (.ref e.ob o_cur) l.from_ (min op0 len0)
        let __do_lift ← Ptr.add (.ref e.ob o_cur) ((min op0 len0 : Nat) : Int)
        if (l.len - opUsed != 0) = true then do
          let __do_lift ← copy_back __do_lift l.dist (l.len - opUsed)
          pure { l with out := __do_lift, op := opUsed, len := l.len - opUsed }
        else
          pure { l with out := __do_lift, op := opUsed, len := l.len - opUsed }) := by
    by_cases hlt : l.op > l.len
    · have hgt : op0 > len0 := by
        have := UInt32.lt_iff_toNat_lt.mp hlt
        omega
      have hmin : min op0 len0 = len0 := by omega
      simp only [hlt, ↓reduceIte, opUsed, hgt, hout, hlen, hmin]
    · have hgt : ¬ (op0 > len0) := fun hx => hlt (UInt32.lt_iff_toNat_lt.mpr (by omega))
      have hmin : min op0 len0 = op0 := by omega
      simp only [hlt, ↓reduceIte, opUsed, hgt, hout, hop, hmin]
  have hmem' : memcpyB (.ref e.ob o_cur) l.from_ (min op0 len0) (e.heap B msg m) =
      .ok ((), e.heap B1 msg m) := by
    rw [hfrom]; exact hmem
  rw [hprog, wp_bind_ok hmem', wp_bind_ok hadd]
  have hsubLen : (l.len - opUsed).toNat = len0 - min op0 len0 := by
    rw [u32_toNat_sub (by rw [hlen, hopUsed]; exact Nat.min_le_right _ _), hlen, hopUsed]
  by_cases hrem : min op0 len0 < len0
  · have hremNz : ((l.len - opUsed) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro hz
      have h0 : (l.len - opUsed).toNat = 0 := by rw [hz]; rfl
      omega
    rw [if_t hremNz]
    have hcb := copy_back_wp e B1 msg m (o_cur + min op0 len0) l.dist (l.len - opUsed)
      hdist1 (by have := hdo hrem; omega) (by rw [hsubLen]; omega) (by rw [hB1sz, hsubLen]; omega)
    obtain ⟨p', hp', hrCb, A', rfl, rfl, hAsz', hAout', hApre'⟩ := hcb
    unfold Wp
    rw [bind_ok hrCb]
    have hsum : o_cur + min op0 len0 + (l.len - opUsed).toNat = o_cur + len0 := by
      rw [hsubLen]; omega
    rw [hsum] at hAout' hApre' ⊢
    refine ⟨_, _, rfl, A', rfl, rfl, hAsz'.trans hB1sz, ?_, ?_⟩
    · intro j hj
      rw [hAout' j (by omega)]
      exact hB1out j (by omega)
    · intro j hj
      rw [hApre' j hj, hsubLen]
      exact cpyN_eq_prefix (len0 - min op0 len0) (o_cur + min op0 len0 - l.dist.toNat)
        (o_cur + min op0 len0) B1 (blitN e.W (min op0 len0) fo o_cur target)
        (by omega) (by omega) (by rw [blitN_size, hTsz, hB1sz]) hB1pre j (by omega)
  · have hzero : len0 - min op0 len0 = 0 := by omega
    have hsub0 : l.len - opUsed = 0 := UInt32.toNat_inj.mp (by rw [hsubLen, hzero]; rfl)
    have hremZ : ¬ (((l.len - opUsed) != 0) = true) := by simp [hsub0]
    rw [if_f hremZ]
    have haddEq : o_cur + min op0 len0 = o_cur + len0 := by omega
    rw [haddEq]
    refine ⟨_, _, rfl, B1, rfl, rfl, hB1sz, ?_, ?_⟩
    · intro j hj; exact hB1out j (by omega)
    · intro j hj
      rw [hzero]
      exact (by simpa only [cpyN, haddEq] using hB1pre j (haddEq ▸ hj))

/-- `copyMatch8`: either the match distance exceeds available history (`badData`, `mode = BAD`,
`broke = true`, array `A` unchanged), or `copyMatch8` copies the match using `memcpyB` and/or
`copy_back`, agreeing with `matchArr` on `[0, o + len)` and framing `[0, o) ∪ [o + len + 15, ...)`. -/
theorem copyMatch8_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (o : Nat) (hout : l.out = .ref e.ob o) (hbg : e.bg ≤ o) (hop : l.op.toNat = o - e.bg)
    (hdist : 1 ≤ l.dist.toNat) (hlen : 1 ≤ l.len.toNat)
    (hAsz : A.size = e.A0.size) (hroom : o + l.len.toNat + 15 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false) :
    Wp (copyMatch8 c l) (e.heap A msg m) (fun l' h' =>
      l'.in_ = l.in_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧
      l'.againL = l.againL ∧ l'.againD = l.againD ∧
      l'.broke = decide (e.s0.whave.toNat + (o - e.bg) < l.dist.toNat) ∧
      ((l'.broke = false ∧ l'.out = .ref e.ob (o + l.len.toNat) ∧
          ∃ A', h' = e.heap A' msg m ∧ A'.size = A.size ∧
            (∀ j, (j < o ∨ o + l.len.toNat + 15 ≤ j) → A'[j]? = A[j]?) ∧
            (∀ j, j < o + l.len.toNat →
              A'[j]? = (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o l.dist.toNat l.len.toNat A)[j]?)) ∨
       (l'.broke = true ∧ ∃ p, h' = e.heap A p BAD ∧ l'.out = l.out))) := by
  have hoA : o + l.len.toNat + 15 ≤ A.size := by
    have := e.hAsz; rw [hAsz]; omega
  unfold copyMatch8
  dsimp only
  by_cases hd : l.dist > l.op
  · have hlt : o - e.bg < l.dist.toNat := by
      have := UInt32.lt_iff_toNat_lt.mp hd; omega
    have hop1 : (l.dist - l.op).toNat = l.dist.toNat - (o - e.bg) := by
      rw [u32_toNat_sub (by omega)]; omega
    rw [if_t hd]
    by_cases hw : l.dist - l.op > c.whave
    · have hhw : e.s0.whave.toNat < (l.dist - l.op).toNat := by
        rw [← hc.whave]; exact UInt32.lt_iff_toNat_lt.mp hw
      have htoo : e.s0.whave.toNat + (o - e.bg) < l.dist.toNat := by omega
      rw [if_t hw, wp_bind_ok (e.heap_ldstate hc A msg m)]
      have hsane : (({ e.s0 with mode := m } : InflateState).sane != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; exact e.hsane
      rw [if_t hsane]
      obtain ⟨si, hsi⟩ := badData_run hc A msg m "invalid distance too far back" (by decide +kernel)
      rw [wp_bind_ok hsi]
      refine Wp.pure' ⟨rfl, rfl, rfl, rfl, rfl, by simp [htoo], Or.inr ⟨rfl, _, rfl, rfl⟩⟩
    · have hhw' : (l.dist - l.op).toNat ≤ e.s0.whave.toNat := by
        have h1 : ¬ (c.whave < l.dist - l.op) := hw
        have h2 : ¬ (c.whave.toNat < (l.dist - l.op).toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        rw [← hc.whave]; omega
      have hnotToo : ¬ (e.s0.whave.toNat + (o - e.bg) < l.dist.toNat) := by omega
      rw [if_f hw]
      have hwne : e.s0.whave ≠ 0 := by
        intro h0
        have : e.s0.whave.toNat = 0 := by rw [h0]; rfl
        omega
      obtain ⟨hwptr, hwb, hWb, hWsz⟩ := e.hwin hwne
      have hwptr' : c.window = Ptr.ref (.blk e.wb) e.woff := by rw [hc.window]; exact hwptr
      have hWg : Space.get (e.heap A msg m) (BRef.blk e.wb) = some e.W := by
        rw [e.heap_get_ne A msg m hwb]; exact hWb
      have hwh : e.s0.whave.toNat ≤ e.s0.wsize.toNat := e.hwh
      have hwn : e.s0.wnext.toNat ≤ e.s0.wsize.toNat := e.hwn
      have hws : e.s0.wsize.toNat ≤ 32768 := e.hws
      let op1 := l.dist - l.op
      have hop1' : op1.toNat = l.dist.toNat - (o - e.bg) := hop1
      by_cases hn0 : c.wnext == 0
      · have hn0n : e.s0.wnext.toNat = 0 := by
          have := beq_iff_eq.mp hn0; rw [← hc.wnext, this]; rfl
        rw [if_t hn0]
        have hsubw : (c.wsize - op1).toNat = e.s0.wsize.toNat - op1.toNat := by
          rw [u32_toNat_sub (by rw [hc.wsize]; omega), hc.wsize]
        have haddW := Ptr.add_nat_ok hWg (by rw [hsubw]; omega : e.woff + (c.wsize - op1).toNat ≤ e.W.size)
        rw [hwptr', wp_bind_ok haddW]
        let l1 : L := { l with op := op1, from_ := .ref (.blk e.wb) (e.woff + (c.wsize - op1).toNat) }
        have htail := copyMatch8_tail_wp e A A A msg m l1 o o (e.woff + (c.wsize - op1).toNat) op1.toNat l.len.toNat
          hwb hWb hout rfl rfl rfl (by omega) hlen hdist (Nat.le_refl _) hoA rfl rfl
          (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hsubw]; omega) (fun _ => by dsimp only [l1]; omega)
        refine Wp.mono htail ?_
        intro l' h' hq
        obtain ⟨A', rfl, rfl, hA'sz, hA'out, hA'pre⟩ := hq
        refine ⟨rfl, rfl, rfl, rfl, rfl, by rw [hbroke]; simp [hnotToo],
          Or.inl ⟨by dsimp only [l1]; exact hbroke, rfl, A', rfl, hA'sz, hA'out, fun j hj => ?_⟩⟩
        rw [hA'pre j hj]
        unfold matchArr
        rw [if_t hlt, if_t hn0n]
        have hwoffEq : e.woff + (c.wsize - op1).toNat = e.woff + e.s0.wsize.toNat - (l.dist.toNat - (o - e.bg)) := by
          rw [hsubw, hop1']; omega
        by_cases hcmp : l.dist.toNat - (o - e.bg) < l.len.toNat
        · have hmin : min op1.toNat l.len.toNat = l.dist.toNat - (o - e.bg) := by omega
          rw [if_t hcmp, hmin, hwoffEq]
        · have hmin : min op1.toNat l.len.toNat = l.len.toNat := by omega
          have hz : l.len.toNat - l.len.toNat = 0 := by omega
          rw [if_f hcmp, hmin, hz, cpyN, hwoffEq]
      · have hn0n : e.s0.wnext.toNat ≠ 0 := by
          intro hz
          apply hn0
          apply beq_iff_eq.mpr
          rw [hc.wnext]
          apply UInt32.toNat_inj.mp
          exact hz
        rw [if_f hn0]
        by_cases hwno : c.wnext < op1
        · have hwnon : e.s0.wnext.toNat < op1.toNat := by
            rw [← hc.wnext]; exact UInt32.lt_iff_toNat_lt.mp hwno
          rw [if_t hwno]
          have hsum32 : c.wsize.toNat + c.wnext.toNat < 2 ^ 32 := by
            rw [hc.wsize, hc.wnext]; omega
          have haddC : (c.wsize + c.wnext).toNat = e.s0.wsize.toNat + e.s0.wnext.toNat := by
            rw [u32_toNat_add hsum32, hc.wsize, hc.wnext]
          have hsubW : (c.wsize + c.wnext - op1).toNat = e.s0.wsize.toNat + e.s0.wnext.toNat - op1.toNat := by
            rw [u32_toNat_sub (by rw [haddC]; omega), haddC]
          have haddW := Ptr.add_nat_ok hWg (by rw [hsubW]; omega : e.woff + (c.wsize + c.wnext - op1).toNat ≤ e.W.size)
          rw [hwptr', wp_bind_ok haddW]
          let op2 := op1 - c.wnext
          have hop2 : op2.toNat = op1.toNat - e.s0.wnext.toNat := by
            rw [u32_toNat_sub (by rw [hc.wnext]; omega), hc.wnext]
          have hop2ge : 1 ≤ op2.toNat := by omega
          have hfo2 : e.woff + (c.wsize + c.wnext - op1).toNat =
              e.woff + e.s0.wsize.toNat + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by
            rw [hsubW, hop1']; omega
          by_cases hopl : op2 < l.len
          · have hopln : op2.toNat < l.len.toNat := UInt32.lt_iff_toNat_lt.mp hopl
            rw [if_t hopl]
            let B1 := copyRange A e.W o (e.woff + (c.wsize + c.wnext - op1).toNat) op2.toNat
            have hmem1 := memcpyB_env_ok e A msg m (BRef.blk e.wb) e.W o (e.woff + (c.wsize + c.wnext - op1).toNat)
              op2.toNat hWb (Or.inl hwb) (fun h => absurd h hwb) (by omega) (by rw [hsubW]; omega)
            have hB1Eq : B1 = blitN e.W op2.toNat (e.woff + (c.wsize + c.wnext - op1).toNat) o A :=
              copyRange_eq_blitN A e.W o _ op2.toNat (by rw [hsubW]; omega) (by omega)
            have hB1sz : B1.size = A.size := by rw [hB1Eq, blitN_size]
            have hadd1 := Ptr.add_nat_ok (e.heap_bytes_ob B1 msg m) (by omega : o + op2.toNat ≤ B1.size)
            rw [hout, wp_bind_ok hmem1, wp_bind_ok hadd1]
            let l2 : L := { l with out := .ref e.ob (o + op2.toNat), op := c.wnext,
                                   len := l.len - op2, from_ := .ref (.blk e.wb) e.woff }
            have hl2len : l2.len.toNat = l.len.toNat - op2.toNat := u32_toNat_sub (by omega)
            have htail := copyMatch8_tail_wp e A B1 B1 msg m l2 o (o + op2.toNat) e.woff
              e.s0.wnext.toNat (l.len.toNat - op2.toNat) hwb hWb rfl rfl
              (by simp only [l2, hc.wnext]) hl2len (by omega) (by omega) hdist (by omega)
              (by omega) hB1sz hB1sz
              (fun j hj => by rw [hB1Eq, blitN_outside _ _ _ _ _ j (by omega)])
              (fun _ _ => rfl) (by omega) (fun h => by simp only [l2]; omega)
            refine Wp.mono htail ?_
            intro l' h' hq
            obtain ⟨A', rfl, rfl, hA'sz, hA'out, hA'pre⟩ := hq
            refine ⟨rfl, rfl, rfl, rfl, rfl, by rw [hbroke]; simp [hnotToo],
              Or.inl ⟨by dsimp only [l2]; exact hbroke, ?_, A', rfl, hA'sz, ?_, fun j hj => ?_⟩⟩
            · congr 1
              rw [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_lt hopln)]
            · intro j hj'; exact hA'out j (by omega)
            · rw [hA'pre j (by omega)]
              unfold matchArr
              rw [if_t hlt, if_f hn0n, if_t (by omega : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg))]
              rw [if_t (by omega : l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat)]
              rw [hB1Eq, hfo2]
              by_cases htail3 : e.s0.wnext.toNat < l.len.toNat - (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat)
              · have hmin : min e.s0.wnext.toNat (l.len.toNat - op2.toNat) = e.s0.wnext.toNat := by omega
                rw [if_t htail3, hmin, hop2, hop1']
              · have hmin : min e.s0.wnext.toNat (l.len.toNat - op2.toNat) = l.len.toNat - op2.toNat := by omega
                have hz : l.len.toNat - op2.toNat - (l.len.toNat - op2.toNat) = 0 := by omega
                rw [if_f htail3, hmin, hz, cpyN, hop2, hop1']
          · have hopln : l.len.toNat ≤ op2.toNat := by
              have h1 : ¬ (op2.toNat < l.len.toNat) := fun h => hopl (UInt32.lt_iff_toNat_lt.mpr h)
              omega
            rw [if_f hopl]
            let l2 : L := { l with op := op2, from_ := .ref (.blk e.wb) (e.woff + (c.wsize + c.wnext - op1).toNat) }
            have htail := copyMatch8_tail_wp e A A A msg m l2 o o (e.woff + (c.wsize + c.wnext - op1).toNat)
              op2.toNat l.len.toNat hwb hWb hout rfl rfl rfl hop2ge hlen hdist (Nat.le_refl _) hoA rfl rfl
              (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hsubW]; omega) (fun h => by dsimp only [l2]; omega)
            refine Wp.mono htail ?_
            intro l' h' hq
            obtain ⟨A', rfl, rfl, hA'sz, hA'out, hA'pre⟩ := hq
            refine ⟨rfl, rfl, rfl, rfl, rfl, by rw [hbroke]; simp [hnotToo],
              Or.inl ⟨by dsimp only [l2]; exact hbroke, rfl, A', rfl, hA'sz, hA'out, fun j hj => ?_⟩⟩
            rw [hA'pre j hj]
            have hmin : min op2.toNat l.len.toNat = l.len.toNat := by omega
            have hz : l.len.toNat - l.len.toNat = 0 := by omega
            rw [hmin, hz, cpyN]
            unfold matchArr
            rw [if_t hlt, if_f hn0n, if_t (by omega : e.s0.wnext.toNat < l.dist.toNat - (o - e.bg)),
              if_f (by omega : ¬ (l.dist.toNat - (o - e.bg) - e.s0.wnext.toNat < l.len.toNat)), hfo2]
        · have hwnon : op1.toNat ≤ e.s0.wnext.toNat := by
            have h1 : ¬ (c.wnext.toNat < op1.toNat) := fun h => hwno (UInt32.lt_iff_toNat_lt.mpr h)
            rw [← hc.wnext]; omega
          rw [if_f hwno]
          have hsubW : (c.wnext - op1).toNat = e.s0.wnext.toNat - op1.toNat := by
            rw [u32_toNat_sub (by rw [hc.wnext]; omega), hc.wnext]
          have haddW := Ptr.add_nat_ok hWg (by rw [hsubW]; omega : e.woff + (c.wnext - op1).toNat ≤ e.W.size)
          rw [hwptr', wp_bind_ok haddW]
          let l1 : L := { l with op := op1, from_ := .ref (.blk e.wb) (e.woff + (c.wnext - op1).toNat) }
          have htail := copyMatch8_tail_wp e A A A msg m l1 o o (e.woff + (c.wnext - op1).toNat)
            op1.toNat l.len.toNat hwb hWb hout rfl rfl rfl (by omega) hlen hdist (Nat.le_refl _) hoA rfl rfl
            (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hsubW]; omega) (fun _ => by dsimp only [l1]; omega)
          refine Wp.mono htail ?_
          intro l' h' hq
          obtain ⟨A', rfl, rfl, hA'sz, hA'out, hA'pre⟩ := hq
          refine ⟨rfl, rfl, rfl, rfl, rfl, by rw [hbroke]; simp [hnotToo],
            Or.inl ⟨by dsimp only [l1]; exact hbroke, rfl, A', rfl, hA'sz, hA'out, fun j hj => ?_⟩⟩
          rw [hA'pre j hj]
          unfold matchArr
          rw [if_t hlt, if_f hn0n, if_f (by omega : ¬ (e.s0.wnext.toNat < l.dist.toNat - (o - e.bg)))]
          have hwoffEq : e.woff + (c.wnext - op1).toNat = e.woff + e.s0.wnext.toNat - (l.dist.toNat - (o - e.bg)) := by
            rw [hsubW, hop1']; omega
          by_cases hcmp : l.dist.toNat - (o - e.bg) < l.len.toNat
          · have hmin : min op1.toNat l.len.toNat = l.dist.toNat - (o - e.bg) := by omega
            rw [if_t hcmp, hmin, hwoffEq]
          · have hmin : min op1.toNat l.len.toNat = l.len.toNat := by omega
            have hz : l.len.toNat - l.len.toNat = 0 := by omega
            rw [if_f hcmp, hmin, hz, cpyN, hwoffEq]
  · have hd' : l.dist.toNat ≤ o - e.bg := by
      have h1 : ¬ (l.op.toNat < l.dist.toNat) := fun h => hd (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    have hnotToo : ¬ (e.s0.whave.toNat + (o - e.bg) < l.dist.toNat) := by omega
    simp only [hd, ↓reduceIte, hout]
    have hcb := copy_back_wp e A msg m o l.dist l.len hdist (by omega) hlen hoA
    obtain ⟨p', hp', hrCb, A', rfl, rfl, hA'sz, hA'out, hA'pre⟩ := hcb
    rw [wp_bind_ok hrCb]
    refine Wp.pure' ⟨rfl, rfl, rfl, rfl, rfl, by rw [hbroke]; simp [hnotToo],
      Or.inl ⟨hbroke, rfl, A', rfl, hA'sz, hA'out, fun j hj => ?_⟩⟩
    rw [hA'pre j hj]
    unfold matchArr
    rw [if_f (by omega : ¬ (o - e.bg < l.dist.toNat))]

/-! ### `dodist8` and `dolen8` events and weakest preconditions -/

/-- One atomic decode event produced by a `dolen8` pass (or a fast literal in `inflate_fast_body8`). -/
inductive Dolen8Event (e : Env) (m : UInt32) (A : Array UInt8) (o u : Nat) :
    Array UInt8 → Nat → Nat → Bool → UInt32 → Prop
  | lit (hold bits i : Nat) (entry : Code) (cb : Nat) :
      15 ≤ bits → hold < 2 ^ bits → Sg e hold bits i = (initial e).drop u →
      cb ≤ 15 → LengthSemantics.Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry cb →
      entry.op = 0 →
      Dolen8Event e m A o u (A.set! o entry.val.toUInt8) (o + 1) (u + cb) false m
  | copy (holdL bitsL iL : Nat) (entryL : Code) (cL xL extraL : Nat)
      (holdD bitsD iD : Nat) (entryD : Code) (cD xD extraD dist : Nat) (A' : Array UInt8)
      (hbL : 15 ≤ bitsL) (hholdLLt : holdL < 2 ^ bitsL) (hsgL : Sg e holdL bitsL iL = (initial e).drop u)
      (hcL : cL ≤ 15) (hlkL : LengthSemantics.Look e holdL (holdL % 2 ^ e.s0.lenbits.toNat) entryL cL)
      (hEnz : entryL.op ≠ 0) (hE16 : entryL.op &&& 16 ≠ 0)
      (hxL : xL = (entryL.op &&& 15).toNat) (hxL5 : xL ≤ 5)
      (hval3 : 3 ≤ entryL.val.toNat) (hval259 : entryL.val.toNat + 2 ^ xL ≤ 259)
      (hreadL : readBits xL ((initial e).drop (u + cL)) = some (extraL, (initial e).drop (u + cL + xL)))
      (hbD : 15 ≤ bitsD) (hholdDLt : holdD < 2 ^ bitsD) (hsgD : Sg e holdD bitsD iD = (initial e).drop (u + cL + xL))
      (hcD : cD ≤ 15) (hlkD : DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) entryD cD)
      (hD16 : entryD.op &&& 16 ≠ 0)
      (hxD : xD = (entryD.op &&& 15).toNat) (hxD13 : xD ≤ 13) (hDval1 : 1 ≤ entryD.val.toNat)
      (hreadD : readBits xD ((initial e).drop (u + cL + xL + cD)) =
        some (extraD, (initial e).drop (u + cL + xL + cD + xD)))
      (hdistEq : dist = entryD.val.toNat + extraD)
      (hnotToo : ¬ (e.s0.whave.toNat + (o - e.bg) < dist))
      (hAsz' : A'.size = A.size)
      (hpre : ∀ j, j < o + (entryL.val.toNat + extraL) →
        A'[j]? = (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist (entryL.val.toNat + extraL) A)[j]?)
      (hframe : ∀ j, (j < o ∨ o + 273 ≤ j) → A'[j]? = A[j]?) :
      Dolen8Event e m A o u A' (o + (entryL.val.toNat + extraL)) (u + cL + xL + cD + xD) false m
  | eob (hold bits i : Nat) (entry : Code) (cb : Nat) :
      15 ≤ bits → hold < 2 ^ bits → Sg e hold bits i = (initial e).drop u →
      cb ≤ 15 → LengthSemantics.Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry cb →
      entry.op ≠ 0 → entry.op &&& 16 = 0 → entry.op &&& 64 ≠ 0 → entry.op &&& 32 ≠ 0 →
      Dolen8Event e m A o u A o (u + cb) true TYPE
  | badLen (hold bits i : Nat) (entry : Code) (cb : Nat) :
      15 ≤ bits → hold < 2 ^ bits → Sg e hold bits i = (initial e).drop u →
      cb ≤ 15 → LengthSemantics.Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry cb →
      entry.op ≠ 0 → entry.op &&& 16 = 0 → entry.op &&& 64 ≠ 0 → entry.op &&& 32 = 0 →
      Dolen8Event e m A o u A o (u + cb) true BAD
  | badDist (holdL bitsL iL : Nat) (entryL : Code) (cL xL extraL : Nat)
      (holdD bitsD iD : Nat) (entryD : Code) (cD : Nat) :
      15 ≤ bitsL → holdL < 2 ^ bitsL → Sg e holdL bitsL iL = (initial e).drop u →
      cL ≤ 15 → LengthSemantics.Look e holdL (holdL % 2 ^ e.s0.lenbits.toNat) entryL cL →
      entryL.op ≠ 0 → entryL.op &&& 16 ≠ 0 →
      xL = (entryL.op &&& 15).toNat → xL ≤ 5 →
      3 ≤ entryL.val.toNat → entryL.val.toNat + 2 ^ xL ≤ 259 →
      readBits xL ((initial e).drop (u + cL)) = some (extraL, (initial e).drop (u + cL + xL)) →
      15 ≤ bitsD → holdD < 2 ^ bitsD → Sg e holdD bitsD iD = (initial e).drop (u + cL + xL) →
      cD ≤ 15 → DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) entryD cD →
      entryD.op &&& 16 = 0 →
      Dolen8Event e m A o u A o (u + cL + xL + cD) true BAD
  | badTooFar (holdL bitsL iL : Nat) (entryL : Code) (cL xL extraL : Nat)
      (holdD bitsD iD : Nat) (entryD : Code) (cD xD extraD dist : Nat) :
      15 ≤ bitsL → holdL < 2 ^ bitsL → Sg e holdL bitsL iL = (initial e).drop u →
      cL ≤ 15 → LengthSemantics.Look e holdL (holdL % 2 ^ e.s0.lenbits.toNat) entryL cL →
      entryL.op ≠ 0 → entryL.op &&& 16 ≠ 0 →
      xL = (entryL.op &&& 15).toNat → xL ≤ 5 →
      3 ≤ entryL.val.toNat → entryL.val.toNat + 2 ^ xL ≤ 259 →
      readBits xL ((initial e).drop (u + cL)) = some (extraL, (initial e).drop (u + cL + xL)) →
      15 ≤ bitsD → holdD < 2 ^ bitsD → Sg e holdD bitsD iD = (initial e).drop (u + cL + xL) →
      cD ≤ 15 → DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) entryD cD →
      entryD.op &&& 16 ≠ 0 →
      xD = (entryD.op &&& 15).toNat → xD ≤ 13 → 1 ≤ entryD.val.toNat →
      readBits xD ((initial e).drop (u + cL + xL + cD)) =
        some (extraD, (initial e).drop (u + cL + xL + cD + xD)) →
      dist = entryD.val.toNat + extraD →
      e.s0.whave.toNat + (o - e.bg) < dist →
      Dolen8Event e m A o u A o (u + cL + xL + cD + xD) true BAD

/-- Sequence of 1..3 `Dolen8Event` steps executed by one `inflate_fast_body8` iteration. -/
inductive Body8Trace (e : Env) (m : UInt32) :
    Array UInt8 → Nat → Nat → Array UInt8 → Nat → Nat → Bool → UInt32 → Prop
  | base {A o u A' o' u' broke m'} :
      Dolen8Event e m A o u A' o' u' broke m' → Body8Trace e m A o u A' o' u' broke m'
  | step {A o u A1 o1 u1 A' o' u' broke m'} :
      Dolen8Event e m A o u A1 o1 u1 false m → Body8Trace e m A1 o1 u1 A' o' u' broke m' →
      Body8Trace e m A o u A' o' u' broke m'

theorem Body8Trace.output_bounds {e : Env} {m : UInt32} {A A' : Array UInt8} {o u o' u' : Nat}
    {broke : Bool} {m' : UInt32} (tr : Body8Trace e m A o u A' o' u' broke m') :
    A'.size = A.size ∧ o ≤ o' ∧
    (broke = false → o < o' ∧ m' = m) ∧
    (broke = true → m' = TYPE ∨ m' = BAD) ∧
    u ≤ u' := by
  have hev : ∀ (A0 A1 : Array UInt8) o0 u0 o1 u1 br m1,
      Dolen8Event e m A0 o0 u0 A1 o1 u1 br m1 →
      A1.size = A0.size ∧ o0 ≤ o1 ∧ (br = false → o0 < o1 ∧ m1 = m) ∧
      (br = true → m1 = TYPE ∨ m1 = BAD) ∧ u0 ≤ u1 := by
    intro A0 A1 o0 u0 o1 u1 br m1 ev
    match ev with
    | .lit _ _ _ _ cb .. =>
      exact ⟨by simp, by omega, (fun _ => ⟨by omega, rfl⟩), (fun h => by cases h), by omega⟩
    | .copy (hval3 := hval3) (hAsz' := hsz) .. =>
      exact ⟨hsz, by omega, (fun _ => ⟨by omega, rfl⟩), (fun h => by cases h), by omega⟩
    | .eob .. => exact ⟨rfl, Nat.le_refl _, (fun h => by cases h), (fun _ => Or.inl rfl), by omega⟩
    | .badLen .. => exact ⟨rfl, Nat.le_refl _, (fun h => by cases h), (fun _ => Or.inr rfl), by omega⟩
    | .badDist .. => exact ⟨rfl, Nat.le_refl _, (fun h => by cases h), (fun _ => Or.inr rfl), by omega⟩
    | .badTooFar .. => exact ⟨rfl, Nat.le_refl _, (fun h => by cases h), (fun _ => Or.inr rfl), by omega⟩
  induction tr with
  | base ev => exact hev _ _ _ _ _ _ _ _ ev
  | step ev _ ih =>
    obtain ⟨hsz1, ho1, hok1, _, hu1⟩ := hev _ _ _ _ _ _ _ _ ev
    obtain ⟨hsz2, ho2, hok2, hbr2, hu2⟩ := ih
    refine ⟨hsz2.trans hsz1, Nat.le_trans ho1 ho2, ?_, hbr2, Nat.le_trans hu1 hu2⟩
    intro hnb
    have hok1' := (hok1 rfl).1
    have hok2' := hok2 hnb
    exact ⟨Nat.lt_trans hok1' hok2'.1, hok2'.2⟩

/-- `readBits` returns a value strictly less than `2 ^ n`. -/
private theorem readBits_val_lt : ∀ n inp v (rest : List Bool),
    ZlibF.Spec.readBits n inp = some (v, rest) → v < 2 ^ n
  | 0, inp, v, rest, h => by simp [ZlibF.Spec.readBits] at h; omega
  | n + 1, [], v, rest, h => by simp [ZlibF.Spec.readBits] at h
  | n + 1, b :: r, v, rest, h => by
    simp only [ZlibF.Spec.readBits] at h
    cases hr : ZlibF.Spec.readBits n r with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      have ih := readBits_val_lt n r v' r' hr
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      cases b <;> simp at h <;> omega

theorem Dolen8Event.frame_and_pos {e : Env} {m : UInt32} {A A' : Array UInt8} {o u o' u' : Nat}
    {broke : Bool} {m' : UInt32} (ev : Dolen8Event e m A o u A' o' u' broke m')
    (hroom : o + 273 ≤ e.o0 + e.sm0.avail_out.toNat) (hAsz : A.size = e.A0.size) :
    (∀ j, (j < o ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A'[j]? = A[j]?) ∧
    (LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat → broke = false → u < u') := by
  have hlpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat →
      ∀ (hold : Nat) (entry : Code) (cb : Nat),
        LengthSemantics.Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry cb → 1 ≤ cb := by
    intro hpos hold entry cb hlk
    have hm : hold % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hp := hpos (hold % 2 ^ e.s0.lenbits.toNat) hm
    rcases hlk with ⟨hget, rfl, hnl⟩ | ⟨E0, j, hget, hlink, hjlt, _, hE1, rfl, _, _⟩
    · rw [hget, if_f hnl] at hp; exact hp
    · rw [hget, if_t hlink] at hp; have hle := hp j hjlt; rw [hE1] at hle; omega
  have hAsz0 : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  match ev with
  | .lit hold _ _ entry cb _ _ _ _ hlk _ =>
    refine ⟨fun j hj => ?_, fun hpos _ => by have := hlpos hpos hold entry cb hlk; omega⟩
    have hoLt : o < A.size := by omega
    have hne : o ≠ j := by omega
    simp [Array.set!, Array.setIfInBounds, hoLt, hne]
  | .copy (holdL := holdL) (entryL := entryL) (cL := cL) (hlkL := hlk) (hframe := hframe) .. =>
    exact ⟨fun j hj => hframe j (by omega),
      fun hpos _ => by have := hlpos hpos holdL entryL cL hlk; omega⟩
  | .eob .. => exact ⟨fun _ _ => rfl, fun _ h => by cases h⟩
  | .badLen .. => exact ⟨fun _ _ => rfl, fun _ h => by cases h⟩
  | .badDist .. => exact ⟨fun _ _ => rfl, fun _ h => by cases h⟩
  | .badTooFar .. => exact ⟨fun _ _ => rfl, fun _ h => by cases h⟩

theorem Body8Trace.pos {e : Env} {m : UInt32} {A A' : Array UInt8} {o u o' u' : Nat}
    {broke : Bool} {m' : UInt32} (tr : Body8Trace e m A o u A' o' u' broke m')
    (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat) (hnb : broke = false) :
    u < u' := by
  have hlpos : ∀ (hold : Nat) (entry : Code) (cb : Nat),
      LengthSemantics.Look e hold (hold % 2 ^ e.s0.lenbits.toNat) entry cb → 1 ≤ cb := by
    intro hold entry cb hlk
    have hm : hold % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hp := hpos (hold % 2 ^ e.s0.lenbits.toNat) hm
    rcases hlk with ⟨hget, rfl, hnl⟩ | ⟨E0, j, hget, hlink, hjlt, _, hE1, rfl, _, _⟩
    · rw [hget, if_f hnl] at hp; exact hp
    · rw [hget, if_t hlink] at hp; have hle := hp j hjlt; rw [hE1] at hle; omega
  induction tr with
  | base ev =>
    match ev with
    | .lit hold _ _ entry cb _ _ _ _ hlk _ => have := hlpos hold entry cb hlk; omega
    | .copy (holdL := holdL) (entryL := entryL) (cL := cL) (hlkL := hlk) .. =>
      have := hlpos holdL entryL cL hlk; omega
    | .eob .. => cases hnb
    | .badLen .. => cases hnb
    | .badDist .. => cases hnb
    | .badTooFar .. => cases hnb
  | step ev rest ih =>
    have hlt := ih hnb
    match ev with
    | .lit .. => omega
    | .copy .. => omega

private theorem dodist8_pass_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o u valid d kidx : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i) (hlOut : l.out = .ref e.ob o)
    (hdbits : 36 ≤ l.bits.toNat + d) (hb63 : l.bits.toNat ≤ 63)
    (hAsz : A.size = e.A0.size) (hbgo : e.bg ≤ o)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hroom : o + l.len.toNat + 15 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false)
    (hhere : l.here = .ref e.rd kidx) (hk : kidx < e.DCA.size)
    (hEd : (e.DCA.getD kidx default).bits.toNat + d ≤ 15)
    (hcl : (DistLink (e.DCA.getD kidx default) ∧ LinkOK DistLeaf e.DCA e.od (e.DCA.getD kidx default)) ∨
      DistLeaf d (e.DCA.getD kidx default)) :
    Wp (dodist8 c l) (e.heap A msg m) (fun l' h' =>
      let E := e.DCA.getD kidx default
      l'.in_ = .ref e.ib i ∧ l'.againL = l.againL ∧
      ((l'.againD = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧ DistLink E ∧
          ∃ j, j < 2 ^ E.op.toNat ∧
            j = (l.hold.toNat / 2 ^ E.bits.toNat) % 2 ^ E.op.toNat ∧
            l'.here = .ref e.rd (e.od + E.val.toNat + j) ∧
            l'.out = .ref e.ob o ∧ l'.len = l.len ∧ l'.bits.toNat = l.bits.toNat - E.bits.toNat ∧
            Inv64 e l'.hold l'.bits i (u + E.bits.toNat) (valid - E.bits.toNat)) ∨
       (l'.againD = false ∧ ¬ DistLink E ∧
          ∃ u' A' o' valid' m' msg',
            Inv64 e l'.hold l'.bits i u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
            l'.out = .ref e.ob o' ∧ o ≤ o' ∧ o' ≤ o + l.len.toNat ∧
            h' = e.heap A' msg' m' ∧ A'.size = A.size ∧
            (∀ j, (j < o ∨ o + l.len.toNat + 15 ≤ j) → A'[j]? = A[j]?) ∧
            ((l'.broke = false ∧ m' = m ∧ msg' = msg ∧ o' = o + l.len.toNat ∧
                ∃ (xd extra dist : Nat),
                  E.op &&& 16 ≠ 0 ∧ xd = (E.op &&& 15).toNat ∧ xd ≤ 13 ∧ 1 ≤ E.val.toNat ∧
                  u' = u + E.bits.toNat + xd ∧
                  ZlibF.Spec.readBits xd ((initial e).drop (u + E.bits.toNat)) = some (extra, (initial e).drop u') ∧
                  dist = E.val.toNat + extra ∧ ¬ (e.s0.whave.toNat + (o - e.bg) < dist) ∧
                  ∀ j, j < o + l.len.toNat →
                    A'[j]? = (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist l.len.toNat A)[j]?) ∨
             (l'.broke = true ∧ m' = BAD ∧ A' = A ∧ o' = o ∧
                ((E.op &&& 16 = 0 ∧ u' = u + E.bits.toNat) ∨
                 (∃ (xd extra dist : Nat),
                    E.op &&& 16 ≠ 0 ∧ xd = (E.op &&& 15).toNat ∧ xd ≤ 13 ∧ 1 ≤ E.val.toNat ∧
                    u' = u + E.bits.toNat + xd ∧
                    ZlibF.Spec.readBits xd ((initial e).drop (u + E.bits.toNat)) = some (extra, (initial e).drop u') ∧
                    dist = E.val.toNat + extra ∧ e.s0.whave.toNat + (o - e.bg) < dist))))))) := by
  have hkE : e.DCA[kidx]'hk = e.DCA.getD kidx default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.DCA.getD kidx default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_DCA A msg m) hk
  generalize hE : e.DCA.getD kidx default = E at hld hEd hcl
  have hEb : E.bits.toNat ≤ 15 := by omega
  have hEb32 : E.bits.toUInt32.toNat = E.bits.toNat := toNat32 E.bits
  have hEbLe : E.bits.toUInt32.toNat ≤ l.bits.toNat := by rw [hEb32]; omega
  have inv1 := inv.drop E.bits.toUInt32 hEbLe (by rw [hEb32]; omega)
  rw [hEb32] at inv1
  have hb1 : (l.bits - E.bits.toUInt32).toNat = l.bits.toNat - E.bits.toNat := by
    rw [u32_toNat_sub hEbLe, hEb32]
  have hbitsGe21 : 21 ≤ (l.bits - E.bits.toUInt32).toNat := by rw [hb1]; omega
  have hbitsLe63 : (l.bits - E.bits.toUInt32).toNat ≤ 63 := by rw [hb1]; omega
  have hshr1 := shr64_ok (h := e.heap A msg m) (x := l.hold) (n := E.bits.toUInt32.toUInt64) (by simp; omega)
  unfold dodist8
  dsimp only
  rw [wp_bind_ok hld, wp_bind_ok hshr1, wp_bind_ok hld]
  by_cases h16 : (E.op.toUInt32 &&& 16 != 0) = true
  · have h16' : E.op &&& 16 ≠ 0 := by rw [mask16] at h16; simpa using h16
    have hnl : ¬ DistLink E := fun h => h16' h.1
    have hbase : (E.op &&& 15).toNat ≤ 13 ∧ 1 ≤ E.val.toNat := by
      rcases hcl with ⟨hlink, _⟩ | hleaf
      · exact False.elim (hnl hlink)
      · rcases hleaf.2 with h | h
        · exact ⟨h.2.1, h.2.2⟩
        · exact False.elim (h16' h.1)
    let xd := E.op.toUInt32 &&& 15
    have hxd : xd.toNat = (E.op &&& 15).toNat := mask15 E.op
    have hxd32 : xd.toNat < 32 := by omega
    have hxdLe : xd.toNat ≤ (l.bits - E.bits.toUInt32).toNat := by omega
    have hshlM := shl32_ok (h := e.heap A msg m) (x := 1) (n := xd) hxd32
    have hshr2 := shr64_ok (h := e.heap A msg m) (x := l.hold >>> E.bits.toUInt32.toUInt64) (n := xd.toUInt64)
      (by simp; omega)
    let hold1 := l.hold >>> E.bits.toUInt32.toUInt64
    let bits1 := l.bits - E.bits.toUInt32
    have inv2 := inv1.drop xd hxdLe (by omega)
    have hbits2 : (bits1 - xd).toNat = bits1.toNat - xd.toNat := u32_toNat_sub hxdLe
    have hlow32 : (hold1.toUInt32 &&& (((1 : UInt32) <<< xd) - 1)).toNat = hold1.toNat % 2 ^ xd.toNat :=
      hold_low32 hxd32
    have hextraLt : hold1.toNat % 2 ^ xd.toNat < 2 ^ 13 := by
      have hm := Nat.mod_lt hold1.toNat (Nat.two_pow_pos xd.toNat)
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : xd.toNat ≤ 13)
      omega
    have hval16 : E.val.toNat < 65536 := E.val.toNat_lt
    have hdistSum : (E.val.toUInt32 + (hold1.toUInt32 &&& (((1 : UInt32) <<< xd) - 1))).toNat =
        E.val.toNat + hold1.toNat % 2 ^ xd.toNat := by
      rw [u32_toNat_add (by rw [UInt16.toNat_toUInt32, hlow32]; omega), UInt16.toNat_toUInt32, hlow32]
    have hrb := inv1.readBits (k := xd.toNat) (by have := inv1.bitsLe; omega)
    have hoAsz : o ≤ A.size := by have := e.hAsz; rw [hAsz]; omega
    have hAbig : A.size < 2 ^ 63 := by rw [hAsz]; exact e.hAbig
    have hst32 := UInt32.toNat_lt e.start
    have hstart := e.hstart
    have hao := e.hao
    have hdiffLen : o - e.bg < 2 ^ 32 := by
      have : e.bg = e.o0 - (e.start.toNat - e.sm0.avail_out.toNat) := rfl
      omega
    have hdiff := Ptr.diff_ok (e.heap_bytes_ob A msg m) hoAsz (by omega) (by omega) (r := e.ob) (o1 := o) (o2 := e.bg)
    have hdiffInt : (o : Int) - (e.bg : Int) = ((o - e.bg : Nat) : Int) := by omega
    rw [hdiffInt] at hdiff
    have hopn : (Int64.ofInt ((o - e.bg : Nat) : Int)).toUInt64.toUInt32.toNat = o - e.bg :=
      i64_toU32 _ hdiffLen
    rw [if_t h16, wp_bind_ok hld, wp_bind_ok hshlM]
    rw [wp_bind_ok hshr2, hlOut, hc.beg, wp_bind_ok hdiff]
    let lcm : L :=
      { l with
        out := .ref e.ob o
        hold := hold1 >>> xd.toUInt64
        bits := bits1 - xd
        op := (Int64.ofInt ((o - e.bg : Nat) : Int)).toUInt64.toUInt32
        dist := E.val.toUInt32 + (hold1.toUInt32 &&& (((1 : UInt32) <<< xd) - 1))
        againD := false }
    have hcm := copyMatch8_wp hc A msg m lcm o rfl hbgo hopn (by rw [hdistSum]; omega)
      (by dsimp only [lcm]; omega) hAsz hroom hbroke
    change Wp (copyMatch8 c lcm) (e.heap A msg m) _
    refine Wp.mono hcm ?_
    intro l' h' hq
    obtain ⟨hin', hhold', hbits', hagL', hagD', hbrkDec, hout'⟩ := hq
    have inv2' : Inv64 e l'.hold l'.bits i (u + E.bits.toNat + xd.toNat) (valid - E.bits.toNat - xd.toNat) := by
      have heq1 : l'.hold = hold1 >>> xd.toUInt64 := hhold'
      have heq2 : l'.bits = bits1 - xd := hbits'
      rw [heq1, heq2]; exact inv2
    refine ⟨hin'.trans hlIn, hagL', Or.inr ⟨hagD', hnl, ?_⟩⟩
    rcases hout' with ⟨hnb', ho', A', rfl, hA'sz, hA'out, hA'pre⟩ | ⟨hbr', p', rfl, hout''⟩
    · have hb' : l'.bits.toNat = l.bits.toNat - E.bits.toNat - xd.toNat := by
        rw [hbits']; dsimp only [lcm]; rw [hbits2]; dsimp only [bits1]; rw [hb1]
      refine ⟨u + E.bits.toNat + xd.toNat, A', o + l.len.toNat, valid - E.bits.toNat - xd.toNat,
        m, msg, inv2', by omega, by omega,
        ho', by omega, by omega, rfl, hA'sz, hA'out, Or.inl ⟨hnb', rfl, rfl, rfl,
          xd.toNat, hold1.toNat % 2 ^ xd.toNat, E.val.toNat + hold1.toNat % 2 ^ xd.toNat,
          h16', hxd.symm, by omega, hbase.2, by rw [hxd], ?_, rfl, ?_, fun j hj => ?_⟩⟩
      · simpa only [hxd] using hrb
      · rw [hnb', eq_comm, decide_eq_false_iff_not] at hbrkDec
        simpa [lcm, hdistSum] using hbrkDec
      · rw [hA'pre j hj, hdistSum]
    · have hb' : l'.bits.toNat = l.bits.toNat - E.bits.toNat - xd.toNat := by
        rw [hbits']; dsimp only [lcm]; rw [hbits2]; dsimp only [bits1]; rw [hb1]
      have htoo : e.s0.whave.toNat + (o - e.bg) < E.val.toNat + hold1.toNat % 2 ^ xd.toNat := by
        rw [hbr', eq_comm, decide_eq_true_eq] at hbrkDec
        simpa [lcm, hdistSum] using hbrkDec
      exact ⟨u + E.bits.toNat + xd.toNat, A, o, valid - E.bits.toNat - xd.toNat,
        BAD, p', inv2', by omega, by omega,
        hout'', Nat.le_refl _, by omega, rfl, rfl, fun _ _ => rfl, Or.inr ⟨hbr', rfl, rfl, rfl, Or.inr
          ⟨xd.toNat, hold1.toNat % 2 ^ xd.toNat, E.val.toNat + hold1.toNat % 2 ^ xd.toNat,
            h16', hxd.symm, by omega, hbase.2, by rw [hxd], by simpa only [hxd] using hrb, rfl, htoo⟩⟩⟩
  · have h16' : E.op &&& 16 = 0 := by rw [mask16] at h16; simpa using h16
    by_cases h64 : (E.op.toUInt32 &&& 64 == 0) = true
    · have h64' : E.op &&& 64 = 0 := by rw [mask64] at h64; simpa using h64
      have hlink : DistLink E := ⟨h16', h64'⟩
      have hlk : LinkOK DistLeaf e.DCA e.od E := by
        rcases hcl with ⟨_, hlk⟩ | hleaf
        · exact hlk
        · rcases hleaf.2 with h | h
          · exact False.elim (h.1 h16')
          · exact False.elim (h.2 h64')
      have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
      have hopLt : E.op.toUInt32.toNat < 32 := by rw [toNat32]; have := hlk.2.2.1; omega
      have hadd1 := Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (r := e.rd) (off := e.od) (n := E.val.toNat)
        (by have := hlk.2.2.2.1; have := Nat.two_pow_pos E.op.toNat; omega)
      have hshl := shl32_ok (h := e.heap A msg m) (x := 1) (n := E.op.toUInt32) hopLt
      let hold1 := l.hold >>> E.bits.toUInt32.toUInt64
      let j := (hold1 &&& (((1 : UInt32) <<< E.op.toUInt32) - 1).toUInt64).toNat
      have hjEq : j = (l.hold.toNat / 2 ^ E.bits.toNat) % 2 ^ E.op.toNat := by
        dsimp only [j, hold1]
        rw [hold_low64 hopLt, u64_shr (by simp; omega), toNat32]
        rfl
      have hjLt : j < 2 ^ E.op.toNat := by rw [hjEq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have hadd2 := Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (r := e.rd) (off := e.od + E.val.toNat) (n := j)
        (by have := hlk.2.2.2.1; omega)
      rw [if_f h16, if_t h64, wp_bind_ok hld, hdc, wp_bind_ok hadd1, wp_bind_ok hshl]
      rw [wp_bind_ok hadd2]
      refine Wp.pure' ⟨hlIn, rfl, Or.inl ⟨rfl, hbroke, rfl, hlink, j, hjLt, ?_, ?_, hlOut, rfl, hb1, inv1⟩⟩
      · exact hjEq
      · simp [hold1, j]
    · have h64' : E.op &&& 64 ≠ 0 := by rw [mask64] at h64; simpa using h64
      have hnl : ¬ DistLink E := fun h => h64' h.2
      rw [if_f h16, if_f h64]
      obtain ⟨si, hsi⟩ := badData_run hc A msg m "invalid distance code" (by decide +kernel)
      rw [wp_bind_ok hsi]
      refine Wp.pure' ⟨hlIn, rfl, Or.inr ⟨rfl, hnl, u + E.bits.toNat, A, o, valid - E.bits.toNat,
        BAD, .ref (BRef.str si) 0, inv1, by rw [hb1]; omega, by rw [hb1]; omega, hlOut, Nat.le_refl _,
        by omega, rfl, rfl, fun _ _ => rfl, Or.inr ⟨rfl, rfl, rfl, rfl, Or.inl ⟨h16', rfl⟩⟩⟩⟩

/-- `cdoWhile (dodist8 c) ...` terminates in at most two passes and produces an exact `DistLook`
at entry bits together with either `matchArr`-exact copying or a `BAD` exit. -/
theorem dodist8_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o u valid : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i) (hlOut : l.out = .ref e.ob o)
    (hb36 : 36 ≤ l.bits.toNat) (hb63 : l.bits.toNat ≤ 63)
    (hAsz : A.size = e.A0.size) (hbgo : e.bg ≤ o)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hroom : o + l.len.toNat + 15 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false)
    (hhere : l.here = .ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat)) :
    Wp (cdoWhile (dodist8 c) (fun l => pure (l.againD, l)) l) (e.heap A msg m) (fun l' h' =>
      ∃ E cb, cb ≤ 15 ∧
        DistLook e (l.hold.toNat % 2 ^ l.bits.toNat) (l.hold.toNat % 2 ^ e.s0.distbits.toNat) E cb ∧
        ∃ u' A' o' valid' m' msg',
          Inv64 e l'.hold l'.bits i u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
          l'.in_ = .ref e.ib i ∧ l'.againL = l.againL ∧ l'.out = .ref e.ob o' ∧
          o ≤ o' ∧ o' ≤ o + l.len.toNat ∧ h' = e.heap A' msg' m' ∧ A'.size = A.size ∧
          (∀ j, (j < o ∨ o + l.len.toNat + 15 ≤ j) → A'[j]? = A[j]?) ∧
          ((l'.broke = false ∧ m' = m ∧ msg' = msg ∧ o' = o + l.len.toNat ∧
              ∃ (xd extra dist : Nat),
                E.op &&& 16 ≠ 0 ∧ xd = (E.op &&& 15).toNat ∧ xd ≤ 13 ∧ 1 ≤ E.val.toNat ∧
                u' = u + cb + xd ∧
                ZlibF.Spec.readBits xd ((initial e).drop (u + cb)) = some (extra, (initial e).drop u') ∧
                dist = E.val.toNat + extra ∧ ¬ (e.s0.whave.toNat + (o - e.bg) < dist) ∧
                ∀ j, j < o + l.len.toNat →
                  A'[j]? = (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist l.len.toNat A)[j]?) ∨
           (l'.broke = true ∧ m' = BAD ∧ A' = A ∧ o' = o ∧
              ((E.op &&& 16 = 0 ∧ u' = u + cb) ∨
               (∃ (xd extra dist : Nat),
                  E.op &&& 16 ≠ 0 ∧ xd = (E.op &&& 15).toNat ∧ xd ≤ 13 ∧ 1 ≤ E.val.toNat ∧
                  u' = u + cb + xd ∧
                  ZlibF.Spec.readBits xd ((initial e).drop (u + cb)) = some (extra, (initial e).drop u') ∧
                  dist = E.val.toNat + extra ∧ e.s0.whave.toNat + (o - e.bg) < dist))))) := by
  have hkIdx : l.hold.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨hk0, hlk0, hnl0⟩ := distRoot e.hdt _ hkIdx
  have hEd0 : (e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : DistLink (e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default)
    · have := (hlk0 hl).1; omega
    · have := (hnl0 hl).1; omega
  have hcl0 : (DistLink (e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default) ∧
      LinkOK DistLeaf e.DCA e.od (e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default)) ∨
      DistLeaf 0 (e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default) := by
    by_cases hl : DistLink (e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default)
    · exact Or.inl ⟨hl, hlk0 hl⟩
    · exact Or.inr (hnl0 hl)
  have hp1 := dodist8_pass_wp hc A msg m l i o u valid 0 (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat)
    inv hlIn hlOut hb36 hb63 hAsz hbgo hlen hroom hbroke hhere hk0 hEd0 hcl0
  obtain ⟨l1, h1, hr1, hin1, hagL1, hres1⟩ := hp1
  generalize hE0 : e.DCA.getD (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) default = E0 at *
  have hmodDist : l.hold.toNat % 2 ^ l.bits.toNat % 2 ^ e.s0.distbits.toNat =
      l.hold.toNat % 2 ^ e.s0.distbits.toNat := by
    have hdb := e.hdt.1
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rcases hres1 with ⟨hagD1, hbr1, rfl, hlink0, j, hjlt, hjEq, hhere1, hout1, hlen1, hbits1, inv1⟩ |
      ⟨hagD1, hnl0', u', A', o', valid', m', msg', inv', hb8, hb63', hout', hoLo, hoHi,
        rfl, hAsz', hOut', hcase⟩
  · have hlk0' := hlk0 hlink0
    have hleaf1 := hlk0'.2.2.2.2 j hjlt
    have hk1 : e.od + E0.val.toNat + j < e.DCA.size := by have := hlk0'.2.2.2.1; omega
    have hdb2 : 36 ≤ l1.bits.toNat + E0.bits.toNat := by omega
    have hroom2 : o + l1.len.toNat + 15 ≤ e.o0 + e.sm0.avail_out.toNat := by rw [hlen1]; exact hroom
    have hlen2 : 3 ≤ l1.len.toNat ∧ l1.len.toNat ≤ 258 := by rw [hlen1]; exact hlen
    have hp2 := dodist8_pass_wp hc A msg m l1 i o (u + E0.bits.toNat) (valid - E0.bits.toNat)
      E0.bits.toNat (e.od + E0.val.toNat + j) inv1 hin1 hout1 hdb2 (by omega)
      hAsz hbgo hlen2 hroom2 hbr1 hhere1 hk1 hleaf1.1 (Or.inr hleaf1)
    obtain ⟨l2, h2, hr2, hin2, hagL2, hres2⟩ := hp2
    generalize hE1 : e.DCA.getD (e.od + E0.val.toNat + j) default = E1 at *
    rcases hres2 with ⟨_, _, _, hlink1, -⟩ |
        ⟨hagD2, hnl1, u', A', o', valid', m', msg', inv', hb8, hb63', hout', hoLo, hoHi,
          rfl, hAsz', hOut', hcase⟩
    · rcases hleaf1.2 with h | h
      · exact False.elim (h.1 hlink1.1)
      · exact False.elim (h.2 hlink1.2)
    · have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [hagD1]
      have c2 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l2 (e.heap A' msg' m') =
          .ok ((false, l2), e.heap A' msg' m') := by simp [hagD2]
      refine Wp.of_eq (cdoWhile_two hr1 c1 hr2 c2) ⟨E1, E0.bits.toNat + E1.bits.toNat, by have := hleaf1.1; omega, ?_,
        u', A', o', valid', m', msg', inv', hb8, hb63', hin2, hagL2.trans hagL1, hout', hoLo,
        by rw [← hlen1]; exact hoHi, rfl, hAsz', by rw [← hlen1]; exact hOut', ?_⟩
      · refine Or.inr ⟨E0, j, hE0, hlink0, hjlt, ?_, ?_, rfl, by have := hleaf1.1; omega, hnl1⟩
        · rw [hjEq]
          exact (mod_div_mod_two_pow l.hold.toNat l.bits.toNat E0.bits.toNat E0.op.toNat
            (by have := hlk0'.1; have := hlk0'.2.2.1; omega)).symm
        · exact hE1
      · simpa only [hlen1, Nat.add_assoc] using hcase
  · have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 (e.heap A' msg' m') =
        .ok ((false, l1), e.heap A' msg' m') := by simp [hagD1]
    refine Wp.of_eq (cdoWhile_one hr1 c1) ⟨E0, E0.bits.toNat, by omega,
      Or.inl ⟨hE0, rfl, hnl0'⟩,
      u', A', o', valid', m', msg', inv', hb8, hb63', hin1, hagL1, hout', hoLo, hoHi,
      rfl, hAsz', hOut', hcase⟩

private theorem dolen8_pass_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o u valid d kidx : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i) (hlOut : l.out = .ref e.ob o)
    (hdbits : 56 ≤ l.bits.toNat + d) (hb63 : l.bits.toNat ≤ 63)
    (hAsz : A.size = e.A0.size) (hbgo : e.bg ≤ o)
    (hroom : o + 273 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false)
    (hhere : l.here = .ref e.rl kidx) (hk : kidx < e.LCA.size)
    (hEd : (e.LCA.getD kidx default).bits.toNat + d ≤ 15)
    (hcl : (LenLink (e.LCA.getD kidx default) ∧ LinkOK LenLeaf e.LCA e.ol (e.LCA.getD kidx default)) ∨
      LenLeaf d (e.LCA.getD kidx default)) :
    Wp (dolen8 c l) (e.heap A msg m) (fun l' h' =>
      let E := e.LCA.getD kidx default
      l'.in_ = .ref e.ib i ∧
      ((l'.againL = true ∧ l'.broke = false ∧ h' = e.heap A msg m ∧ LenLink E ∧
          ∃ j, j < 2 ^ E.op.toNat ∧
            j = (l.hold.toNat / 2 ^ E.bits.toNat) % 2 ^ E.op.toNat ∧
            l'.here = .ref e.rl (e.ol + E.val.toNat + j) ∧
            l'.out = .ref e.ob o ∧ l'.bits.toNat = l.bits.toNat - E.bits.toNat ∧
            Inv64 e l'.hold l'.bits i (u + E.bits.toNat) (valid - E.bits.toNat)) ∨
       (l'.againL = false ∧ ¬ LenLink E ∧
          ∃ u' A' o' valid' m' msg',
            Inv64 e l'.hold l'.bits i u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
            l'.out = .ref e.ob o' ∧ o ≤ o' ∧ o' ≤ o + 258 ∧
            h' = e.heap A' msg' m' ∧ A'.size = A.size ∧
            (∀ j, (j < o ∨ o + 273 ≤ j) → A'[j]? = A[j]?) ∧
            ((l'.broke = false ∧ m' = m ∧ msg' = msg ∧ o < o' ∧
                ((E.op = 0 ∧ o' = o + 1 ∧ u' = u + E.bits.toNat ∧ A' = A.set! o E.val.toUInt8) ∨
                 (E.op &&& 16 ≠ 0 ∧ ∃ xL extraL E2 cD xD extraD dist,
                    xL = (E.op &&& 15).toNat ∧ xL ≤ 5 ∧ 3 ≤ E.val.toNat ∧ E.val.toNat + 2 ^ xL ≤ 259 ∧
                    ZlibF.Spec.readBits xL ((initial e).drop (u + E.bits.toNat)) =
                      some (extraL, (initial e).drop (u + E.bits.toNat + xL)) ∧
                    o' = o + (E.val.toNat + extraL) ∧
                    cD ≤ 15 ∧
                    (∃ holdD bitsD, 15 ≤ bitsD ∧ holdD < 2 ^ bitsD ∧
                      Sg e holdD bitsD i = (initial e).drop (u + E.bits.toNat + xL) ∧
                      DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) E2 cD) ∧
                    E2.op &&& 16 ≠ 0 ∧ xD = (E2.op &&& 15).toNat ∧ xD ≤ 13 ∧ 1 ≤ E2.val.toNat ∧
                    u' = u + E.bits.toNat + xL + cD + xD ∧
                    ZlibF.Spec.readBits xD ((initial e).drop (u + E.bits.toNat + xL + cD)) =
                      some (extraD, (initial e).drop u') ∧
                    dist = E2.val.toNat + extraD ∧ ¬ (e.s0.whave.toNat + (o - e.bg) < dist) ∧
                    ∀ j, j < o' →
                      A'[j]? = (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist
                        (E.val.toNat + extraL) A)[j]?))) ∨
             (l'.broke = true ∧ A' = A ∧ o' = o ∧
                ((m' = TYPE ∧ msg' = msg ∧ E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0 ∧ E.op &&& 32 ≠ 0 ∧
                    u' = u + E.bits.toNat) ∨
                 (m' = BAD ∧
                    ((E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0 ∧ E.op &&& 32 = 0 ∧ u' = u + E.bits.toNat) ∨
                     (E.op &&& 16 ≠ 0 ∧ ∃ xL extraL E2 cD,
                        xL = (E.op &&& 15).toNat ∧ xL ≤ 5 ∧ 3 ≤ E.val.toNat ∧ E.val.toNat + 2 ^ xL ≤ 259 ∧
                        ZlibF.Spec.readBits xL ((initial e).drop (u + E.bits.toNat)) =
                          some (extraL, (initial e).drop (u + E.bits.toNat + xL)) ∧
                        cD ≤ 15 ∧
                        (∃ holdD bitsD, 15 ≤ bitsD ∧ holdD < 2 ^ bitsD ∧
                          Sg e holdD bitsD i = (initial e).drop (u + E.bits.toNat + xL) ∧
                          DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) E2 cD) ∧
                        ((E2.op &&& 16 = 0 ∧ u' = u + E.bits.toNat + xL + cD) ∨
                         (∃ xD extraD dist,
                            E2.op &&& 16 ≠ 0 ∧ xD = (E2.op &&& 15).toNat ∧ xD ≤ 13 ∧ 1 ≤ E2.val.toNat ∧
                            u' = u + E.bits.toNat + xL + cD + xD ∧
                            ZlibF.Spec.readBits xD ((initial e).drop (u + E.bits.toNat + xL + cD)) =
                              some (extraD, (initial e).drop u') ∧
                            dist = E2.val.toNat + extraD ∧ e.s0.whave.toNat + (o - e.bg) < dist))))))))))) := by
  have hkE : e.LCA[kidx]'hk = e.LCA.getD kidx default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.LCA.getD kidx default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk
  generalize hE : e.LCA.getD kidx default = E at hld hEd hcl
  have hEb : E.bits.toNat ≤ 15 := by omega
  have hEb32 : E.bits.toUInt32.toNat = E.bits.toNat := toNat32 E.bits
  have hEbLe : E.bits.toUInt32.toNat ≤ l.bits.toNat := by rw [hEb32]; omega
  have inv1 := inv.drop E.bits.toUInt32 hEbLe (by rw [hEb32]; omega)
  rw [hEb32] at inv1
  have hb1 : (l.bits - E.bits.toUInt32).toNat = l.bits.toNat - E.bits.toNat := by
    rw [u32_toNat_sub hEbLe, hEb32]
  have hbitsGe41 : 41 ≤ (l.bits - E.bits.toUInt32).toNat := by rw [hb1]; omega
  have hshr1 := shr64_ok (h := e.heap A msg m) (x := l.hold) (n := E.bits.toUInt32.toUInt64) (by simp; omega)
  have hAsz0 : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  unfold dolen8
  dsimp only
  rw [wp_bind_ok hld, wp_bind_ok hshr1, wp_bind_ok hld]
  by_cases hz : (E.op.toUInt32 == 0) = true
  · have hz' : E.op = 0 := by
      apply UInt8.toNat_inj.mp
      have h1 := beq_iff_eq.mp hz
      have h2 := congrArg UInt32.toNat h1
      simpa using h2
    have hnl : ¬ LenLink E := fun h => h.1 hz'
    have hst : store8 (.ref e.ob o) E.val.toUInt8 (e.heap A msg m) =
        .ok ((), e.heap (A.set! o E.val.toUInt8) msg m) := by
      rw [← e.heap_put A (A.set! o E.val.toUInt8) msg m]
      exact Ptr.store_ok (off := o) (e.heap_bytes_ob A msg m) (e.heap_ro_ob A msg m) (by omega)
    have hadd : OkOn (e.heap (A.set! o E.val.toUInt8) msg m) (Ptr.add (.ref e.ob o) (1 : Int))
        (.ref e.ob (o + 1)) := by
      simpa using Ptr.add_nat_ok (e.heap_bytes_ob (A.set! o E.val.toUInt8) msg m)
        (r := e.ob) (off := o) (n := 1) (by simp; omega)
    rw [if_t hz, wp_bind_ok hld]
    rw [hlOut, wp_bind_ok hst, wp_bind_ok hadd]
    refine Wp.pure' ⟨hlIn, Or.inr ⟨rfl, hnl, u + E.bits.toNat, A.set! o E.val.toUInt8, o + 1,
      valid - E.bits.toNat, m, msg, inv1, by rw [hb1]; omega, by rw [hb1]; omega, rfl, by omega, by omega,
      rfl, by simp, fun j hj => ?_,
      Or.inl ⟨hbroke, rfl, rfl, by omega, Or.inl ⟨hz', rfl, rfl, rfl⟩⟩⟩⟩
    have hoLt : o < A.size := by omega
    have hne : o ≠ j := by omega
    simp [Array.set!, Array.setIfInBounds, hoLt, hne]
  · have hz' : E.op ≠ 0 := fun h0 => hz (by simp [h0])
    by_cases h16 : (E.op.toUInt32 &&& 16 != 0) = true
    · have h16' : E.op &&& 16 ≠ 0 := by rw [mask16] at h16; simpa using h16
      have hnl : ¬ LenLink E := fun h => h16' h.2.1
      have hbase : (E.op &&& 15).toNat ≤ 5 ∧ 3 ≤ E.val.toNat ∧ E.val.toNat + 2 ^ (E.op &&& 15).toNat ≤ 259 := by
        rcases hcl with ⟨hlink, _⟩ | hleaf
        · exact False.elim (hnl hlink)
        · rcases hleaf.2 with h0 | h | h
          · exact False.elim (hz' h0)
          · exact h.2
          · exact False.elim (h16' h.1)
      let xL := E.op.toUInt32 &&& 15
      have hxL : xL.toNat = (E.op &&& 15).toNat := mask15 E.op
      have hxL32 : xL.toNat < 32 := by omega
      have hxLLe : xL.toNat ≤ (l.bits - E.bits.toUInt32).toNat := by omega
      have hshlM := shl32_ok (h := e.heap A msg m) (x := 1) (n := xL) hxL32
      have hshr2 := shr64_ok (h := e.heap A msg m) (x := l.hold >>> E.bits.toUInt32.toUInt64) (n := xL.toUInt64)
        (by simp; omega)
      let hold1 := l.hold >>> E.bits.toUInt32.toUInt64
      let bits1 := l.bits - E.bits.toUInt32
      have inv2 := inv1.drop xL hxLLe (by omega)
      have hbits2 : (bits1 - xL).toNat = bits1.toNat - xL.toNat := u32_toNat_sub hxLLe
      have hlow32 : (hold1.toUInt32 &&& (((1 : UInt32) <<< xL) - 1)).toNat = hold1.toNat % 2 ^ xL.toNat :=
        hold_low32 hxL32
      have hextraLt : hold1.toNat % 2 ^ xL.toNat < 2 ^ xL.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hpowEq : 2 ^ xL.toNat = 2 ^ (E.op &&& 15).toNat := by rw [hxL]
      have hlenSum : (E.val.toUInt32 + (hold1.toUInt32 &&& (((1 : UInt32) <<< xL) - 1))).toNat =
          E.val.toNat + hold1.toNat % 2 ^ xL.toNat := by
        rw [u32_toNat_add (by rw [UInt16.toNat_toUInt32, hlow32]; omega), UInt16.toNat_toUInt32, hlow32]
      have hlenBound : 3 ≤ E.val.toNat + hold1.toNat % 2 ^ xL.toNat ∧
          E.val.toNat + hold1.toNat % 2 ^ xL.toNat ≤ 258 := by omega
      have hrbL := inv1.readBits (k := xL.toNat) (by have := inv1.bitsLe; omega)
      let hold2 := hold1 >>> xL.toUInt64
      let bits2 := bits1 - xL
      have hR : e.s0.distbits.toNat < 32 := by have := e.hdt.1; omega
      have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
      have hmask : c.dmask.toUInt64.toNat = 2 ^ e.s0.distbits.toNat - 1 := by
        rw [hc.dmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
      have hidx := u64_and_mask (x := hold2) hmask
      have hmod : hold2.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have haddD := Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (r := e.rd) (off := e.od)
        (n := (hold2 &&& c.dmask.toUInt64).toNat) (by rw [hidx]; have := e.hdt.2.1; omega)
      rw [if_f hz, if_t h16, wp_bind_ok hld, wp_bind_ok hshlM]
      rw [wp_bind_ok hshr2, hdc, wp_bind_ok haddD]
      let ldist : L :=
        { l with
          hold := hold2
          bits := bits2
          here := .ref e.rd (e.od + (hold2 &&& c.dmask.toUInt64).toNat)
          op := xL
          len := E.val.toUInt32 + (hold1.toUInt32 &&& (((1 : UInt32) <<< xL) - 1))
          againL := false }
      have hbits2' : ldist.bits.toNat = l.bits.toNat - E.bits.toNat - xL.toNat := by
        dsimp only [ldist]; rw [hbits2]; dsimp only [bits1]; rw [hb1]
      have inv2' : Inv64 e hold2 bits2 i (u + E.bits.toNat + xL.toNat) (valid - E.bits.toNat - xL.toNat) := by
        dsimp only [hold2, bits2]; exact inv2
      have hdRes := dodist8_wp hc A msg m ldist i o (u + E.bits.toNat + xL.toNat)
        (valid - E.bits.toNat - xL.toNat) inv2' hlIn hlOut (by rw [hbits2']; omega)
        (by rw [hbits2']; omega) hAsz hbgo (by dsimp only [ldist]; rw [hlenSum]; exact hlenBound)
        (by dsimp only [ldist]; rw [hlenSum, hpowEq]; omega) hbroke (by simp [ldist, hidx])
      change Wp (cdoWhile (dodist8 c) (fun l => pure (l.againD, l)) ldist) (e.heap A msg m) _
      refine Wp.mono hdRes ?_
      intro l' h' ⟨E2, cD, hcD, hDlk, u', A', o', valid', m', msg', inv', hb8, hb63', hin',
        hagL', hout', hoLo, hoHi, hh', hAsz', hOut', hcase⟩
      subst hh'
      have hb2_ge : 15 ≤ bits2.toNat := by rw [hbits2]; dsimp only [bits1]; rw [hb1]; omega
      have hdistMod : (hold2.toNat % 2 ^ bits2.toNat) % 2 ^ e.s0.distbits.toNat =
          hold2.toNat % 2 ^ e.s0.distbits.toNat := by
        have hdb := e.hdt.1
        rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
      have hDistWit : ∃ holdD bitsD, 15 ≤ bitsD ∧ holdD < 2 ^ bitsD ∧
          Sg e holdD bitsD i = (initial e).drop (u + E.bits.toNat + (E.op &&& 15).toNat) ∧
          DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) E2 cD := by
        refine ⟨hold2.toNat % 2 ^ bits2.toNat, bits2.toNat, hb2_ge,
          Nat.mod_lt _ (Nat.two_pow_pos _), (by rw [← hxL]; exact inv2'.sg_mod), ?_⟩
        rw [hdistMod]
        simpa only [ldist] using hDlk
      refine ⟨hin', Or.inr ⟨hagL', hnl, u', A', o', valid', m', msg', inv', hb8, hb63', hout', hoLo,
        by dsimp only [ldist] at hoHi; omega, rfl, hAsz',
        fun j hj => hOut' j (by dsimp only [ldist]; omega), ?_⟩⟩
      rcases hcase with ⟨hnb', rfl, rfl, ho', xd, extraD, dist, hE2_16, hxd, hxd13, hE2_1, hu',
          hrbD, hdistEq, hnotToo, hpre'⟩ |
          ⟨hbr', rfl, rfl, ho', hcBad⟩
      · refine Or.inl ⟨hnb', rfl, rfl, by dsimp only [ldist] at ho'; omega, Or.inr ⟨h16',
          (E.op &&& 15).toNat, hold1.toNat % 2 ^ xL.toNat, E2, cD, xd, extraD, dist,
          rfl, hbase.1, hbase.2.1, hbase.2.2, by rw [← hxL]; exact hrbL,
          by dsimp only [ldist] at ho'; rw [hlenSum] at ho'; exact ho', hcD, hDistWit,
          hE2_16, hxd, hxd13, hE2_1, by rw [← hxL]; exact hu', by rw [← hxL]; exact hrbD,
          hdistEq, hnotToo, fun j hj => ?_⟩⟩
        dsimp only [ldist] at ho' hpre'; rw [hlenSum] at ho' hpre'; exact hpre' j (ho' ▸ hj)
      · refine Or.inr ⟨hbr', rfl, ho', Or.inr ⟨rfl, Or.inr ⟨h16', (E.op &&& 15).toNat,
          hold1.toNat % 2 ^ xL.toNat, E2, cD, rfl, hbase.1, hbase.2.1, hbase.2.2,
          by rw [← hxL]; exact hrbL, hcD, hDistWit, ?_⟩⟩⟩
        rcases hcBad with ⟨hE2_0, hu'⟩ | ⟨xd, extraD, dist, hE2_16, hxd, hxd13, hE2_1, hu',
            hrbD, hdistEq, htoo⟩
        · exact Or.inl ⟨hE2_0, by rw [← hxL]; exact hu'⟩
        · exact Or.inr ⟨xd, extraD, dist, hE2_16, hxd, hxd13, hE2_1, by rw [← hxL]; exact hu',
            by rw [← hxL]; exact hrbD, hdistEq, htoo⟩
    · have h16' : E.op &&& 16 = 0 := by rw [mask16] at h16; simpa using h16
      by_cases h64 : (E.op.toUInt32 &&& 64 == 0) = true
      · have h64' : E.op &&& 64 = 0 := by rw [mask64] at h64; simpa using h64
        have hlink : LenLink E := ⟨hz', h16', h64'⟩
        have hlk : LinkOK LenLeaf e.LCA e.ol E := by
          rcases hcl with ⟨_, hlk⟩ | hleaf
          · exact hlk
          · rcases hleaf.2 with h0 | h | h
            · exact False.elim (hz' h0)
            · exact False.elim (h.1 h16')
            · exact False.elim (h.2 h64')
        have hlc : c.lcode = .ref e.rl e.ol := by rw [hc.lcode]; exact e.hlc
        have hopLt : E.op.toUInt32.toNat < 32 := by rw [toNat32]; have := hlk.2.2.1; omega
        have hadd1 := Ptr.add_nat_ok (e.heap_cget_LCA A msg m) (r := e.rl) (off := e.ol) (n := E.val.toNat)
          (by have := hlk.2.2.2.1; have := Nat.two_pow_pos E.op.toNat; omega)
        have hshl := shl32_ok (h := e.heap A msg m) (x := 1) (n := E.op.toUInt32) hopLt
        let hold1 := l.hold >>> E.bits.toUInt32.toUInt64
        let j := (hold1 &&& (((1 : UInt32) <<< E.op.toUInt32) - 1).toUInt64).toNat
        have hjEq : j = (l.hold.toNat / 2 ^ E.bits.toNat) % 2 ^ E.op.toNat := by
          dsimp only [j, hold1]
          rw [hold_low64 hopLt, u64_shr (by simp; omega), toNat32]
          rfl
        have hjLt : j < 2 ^ E.op.toNat := by rw [hjEq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
        have hadd2 := Ptr.add_nat_ok (e.heap_cget_LCA A msg m) (r := e.rl) (off := e.ol + E.val.toNat) (n := j)
          (by have := hlk.2.2.2.1; omega)
        rw [if_f hz, if_f h16, if_t h64, wp_bind_ok hld, hlc, wp_bind_ok hadd1, wp_bind_ok hshl]
        rw [wp_bind_ok hadd2]
        refine Wp.pure' ⟨hlIn, Or.inl ⟨rfl, hbroke, rfl, hlink, j, hjLt, ?_, ?_, hlOut, hb1, inv1⟩⟩
        · exact hjEq
        · simp [hold1, j]
      · have h64' : E.op &&& 64 ≠ 0 := by rw [mask64] at h64; simpa using h64
        have hnl : ¬ LenLink E := fun h => h64' h.2.2
        by_cases h32 : (E.op.toUInt32 &&& 32 != 0) = true
        · have h32' : E.op &&& 32 ≠ 0 := by rw [mask32] at h32; simpa using h32
          rw [if_f hz, if_f h16, if_f h64, if_t h32]
          rw [wp_bind_ok (e.heap_ldstate hc A msg m), wp_bind_ok (e.heap_stmode hc A msg m TYPE _ rfl)]
          refine Wp.pure' ⟨hlIn, Or.inr ⟨rfl, hnl, u + E.bits.toNat, A, o, valid - E.bits.toNat,
            TYPE, msg, inv1, by rw [hb1]; omega, by rw [hb1]; omega, hlOut, Nat.le_refl _, by omega, rfl, rfl,
            fun _ _ => rfl, Or.inr ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl, h16', h64', h32', rfl⟩⟩⟩⟩
        · have h32' : E.op &&& 32 = 0 := by rw [mask32] at h32; simpa using h32
          rw [if_f hz, if_f h16, if_f h64, if_f h32]
          obtain ⟨si, hsi⟩ := badData_run hc A msg m "invalid literal/length code" (by decide +kernel)
          rw [wp_bind_ok hsi]
          refine Wp.pure' ⟨hlIn, Or.inr ⟨rfl, hnl, u + E.bits.toNat, A, o, valid - E.bits.toNat,
            BAD, .ref (BRef.str si) 0, inv1, by rw [hb1]; omega, by rw [hb1]; omega, hlOut, Nat.le_refl _,
            by omega, rfl, rfl, fun _ _ => rfl, Or.inr ⟨rfl, rfl, rfl, Or.inr ⟨rfl, Or.inl ⟨h16', h64', h32', rfl⟩⟩⟩⟩⟩

private theorem dolen8_build_event {e : Env} {m : UInt32} {A A' : Array UInt8}
    {o u uMid cb o' u' : Nat} {msg msg' : BPtr} {m' : UInt32} {br : Bool}
    {hold bits i : Nat} {E : Code}
    (hb : 15 ≤ bits) (hholdLt : hold < 2 ^ bits)
    (hsg : Sg e hold bits i = (initial e).drop u)
    (hcb : cb ≤ 15)
    (hlook : LengthSemantics.Look e hold (hold % 2 ^ e.s0.lenbits.toNat) E cb)
    (huMid : uMid + E.bits.toNat = u + cb)
    (hAsz' : A'.size = A.size)
    (hOut' : ∀ j, (j < o ∨ o + 273 ≤ j) → A'[j]? = A[j]?)
    (hcase : (br = false ∧ m' = m ∧ msg' = msg ∧ o < o' ∧
        ((E.op = 0 ∧ o' = o + 1 ∧ u' = uMid + E.bits.toNat ∧ A' = A.set! o E.val.toUInt8) ∨
         (E.op &&& 16 ≠ 0 ∧ ∃ xL extraL E2 cD xD extraD dist,
            xL = (E.op &&& 15).toNat ∧ xL ≤ 5 ∧ 3 ≤ E.val.toNat ∧ E.val.toNat + 2 ^ xL ≤ 259 ∧
            ZlibF.Spec.readBits xL ((initial e).drop (uMid + E.bits.toNat)) =
              some (extraL, (initial e).drop (uMid + E.bits.toNat + xL)) ∧
            o' = o + (E.val.toNat + extraL) ∧
            cD ≤ 15 ∧
            (∃ holdD bitsD, 15 ≤ bitsD ∧ holdD < 2 ^ bitsD ∧
              Sg e holdD bitsD i = (initial e).drop (uMid + E.bits.toNat + xL) ∧
              DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) E2 cD) ∧
            E2.op &&& 16 ≠ 0 ∧ xD = (E2.op &&& 15).toNat ∧ xD ≤ 13 ∧ 1 ≤ E2.val.toNat ∧
            u' = uMid + E.bits.toNat + xL + cD + xD ∧
            ZlibF.Spec.readBits xD ((initial e).drop (uMid + E.bits.toNat + xL + cD)) =
              some (extraD, (initial e).drop u') ∧
            dist = E2.val.toNat + extraD ∧ ¬ (e.s0.whave.toNat + (o - e.bg) < dist) ∧
            ∀ j, j < o' →
              A'[j]? = (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist
                (E.val.toNat + extraL) A)[j]?))) ∨
      (br = true ∧ A' = A ∧ o' = o ∧
        ((m' = TYPE ∧ msg' = msg ∧ E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0 ∧ E.op &&& 32 ≠ 0 ∧
            u' = uMid + E.bits.toNat) ∨
         (m' = BAD ∧
            ((E.op &&& 16 = 0 ∧ E.op &&& 64 ≠ 0 ∧ E.op &&& 32 = 0 ∧ u' = uMid + E.bits.toNat) ∨
             (E.op &&& 16 ≠ 0 ∧ ∃ xL extraL E2 cD,
                xL = (E.op &&& 15).toNat ∧ xL ≤ 5 ∧ 3 ≤ E.val.toNat ∧ E.val.toNat + 2 ^ xL ≤ 259 ∧
                ZlibF.Spec.readBits xL ((initial e).drop (uMid + E.bits.toNat)) =
                  some (extraL, (initial e).drop (uMid + E.bits.toNat + xL)) ∧
                cD ≤ 15 ∧
                (∃ holdD bitsD, 15 ≤ bitsD ∧ holdD < 2 ^ bitsD ∧
                  Sg e holdD bitsD i = (initial e).drop (uMid + E.bits.toNat + xL) ∧
                  DistLook e holdD (holdD % 2 ^ e.s0.distbits.toNat) E2 cD) ∧
                ((E2.op &&& 16 = 0 ∧ u' = uMid + E.bits.toNat + xL + cD) ∨
                 (∃ xD extraD dist,
                    E2.op &&& 16 ≠ 0 ∧ xD = (E2.op &&& 15).toNat ∧ xD ≤ 13 ∧ 1 ≤ E2.val.toNat ∧
                    u' = uMid + E.bits.toNat + xL + cD + xD ∧
                    ZlibF.Spec.readBits xD ((initial e).drop (uMid + E.bits.toNat + xL + cD)) =
                      some (extraD, (initial e).drop u') ∧
                    dist = E2.val.toNat + extraD ∧ e.s0.whave.toNat + (o - e.bg) < dist)))))))) :
    Dolen8Event e m A o u A' o' u' br m' := by
  rcases hcase with ⟨rfl, rfl, rfl, _, ⟨h0, rfl, hu', rfl⟩ |
      ⟨h16, xL, extraL, E2, cD, xD, extraD, dist, hxL, hxL5, hval3, hval259, hrbL, rfl, hcD,
        ⟨holdD, bitsD, hbD, hholdDLt, hsgD, hDlk⟩, hE2_16, hxd, hxd13, hE2_1, hu', hrbD,
        hdistEq, hnotToo, hpre'⟩⟩ |
      ⟨rfl, rfl, rfl, ⟨rfl, rfl, h16, h64, h32, rfl⟩ |
        ⟨rfl, ⟨h16, h64, h32, rfl⟩ | ⟨h16, xL, extraL, E2, cD, hxL, hxL5, hval3, hval259,
          hrbL, hcD, ⟨holdD, bitsD, hbD, hholdDLt, hsgD, hDlk⟩,
          ⟨hE2_0, hu'⟩ | ⟨xD, extraD, dist, hE2_16, hxd, hxd13, hE2_1, hu', hrbD, hdistEq, htoo⟩⟩⟩⟩
  · rw [hu', huMid]
    exact Dolen8Event.lit hold bits i E cb hb hholdLt hsg hcb hlook h0
  · have hEnz : E.op ≠ 0 := fun h0 => by simp [h0] at h16
    have hxlLt := readBits_val_lt xL _ _ _ hrbL
    have hPow258 : E.val.toNat + extraL ≤ 258 := by omega
    rw [huMid] at hrbL hsgD hrbD hu'
    rw [hu'] at hrbD ⊢
    exact Dolen8Event.copy hold bits i E cb xL extraL holdD bitsD i E2 cD xD extraD dist A'
      hb hholdLt hsg hcb hlook hEnz h16 hxL hxL5 hval3 hval259 hrbL hbD hholdDLt hsgD hcD hDlk
      hE2_16 hxd hxd13 hE2_1 hrbD hdistEq hnotToo hAsz' hpre'
      (fun j hj => hOut' j (by omega))
  · have hEnz : E.op ≠ 0 := fun h0 => by simp [h0] at h64
    rw [huMid]
    exact Dolen8Event.eob hold bits i E cb hb hholdLt hsg hcb hlook hEnz h16 h64 h32
  · have hEnz : E.op ≠ 0 := fun h0 => by simp [h0] at h64
    rw [huMid]
    exact Dolen8Event.badLen hold bits i E cb hb hholdLt hsg hcb hlook hEnz h16 h64 h32
  · have hEnz : E.op ≠ 0 := fun h0 => by simp [h0] at h16
    rw [huMid] at hrbL hsgD hu'
    rw [hu']
    exact Dolen8Event.badDist hold bits i E cb xL extraL holdD bitsD i E2 cD
      hb hholdLt hsg hcb hlook hEnz h16 hxL hxL5 hval3 hval259 hrbL hbD hholdDLt hsgD hcD hDlk hE2_0
  · have hEnz : E.op ≠ 0 := fun h0 => by simp [h0] at h16
    rw [huMid] at hrbL hsgD hrbD hu'
    rw [hu'] at hrbD ⊢
    exact Dolen8Event.badTooFar hold bits i E cb xL extraL holdD bitsD i E2 cD xD extraD dist
      hb hholdLt hsg hcb hlook hEnz h16 hxL hxL5 hval3 hval259 hrbL hbD hholdDLt hsgD hcD hDlk
      hE2_16 hxd hxd13 hE2_1 hrbD hdistEq htoo

private theorem dolen8_msg_of_case {m m' : UInt32} {msg msg' : BPtr} {br : Bool}
    {o o' : Nat} {A A' : Array UInt8} {h1 h2 h3 : Prop}
    (hc : (br = false ∧ m' = m ∧ msg' = msg ∧ o < o' ∧ h1) ∨
      (br = true ∧ A' = A ∧ o' = o ∧ ((m' = TYPE ∧ msg' = msg ∧ h2) ∨ (m' = BAD ∧ h3)))) :
    (br = false → msg' = msg) ∧ (m' = TYPE → msg' = msg) := by
  rcases hc with ⟨_, _, rfl, _⟩ | ⟨hbr, _, _, ⟨rfl, rfl, _⟩ | ⟨rfl, _⟩⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨(fun h => by cases hbr.symm.trans h), (fun _ => rfl)⟩
  · exact ⟨(fun h => by cases hbr.symm.trans h), (fun h => False.elim ((by decide : BAD ≠ TYPE) h))⟩

private theorem dolen8_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o u valid : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i) (hlOut : l.out = .ref e.ob o)
    (hb56 : 56 ≤ l.bits.toNat) (hb63 : l.bits.toNat ≤ 63)
    (hAsz : A.size = e.A0.size) (hbgo : e.bg ≤ o)
    (hroom : o + 273 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hbroke : l.broke = false)
    (hhere : l.here = .ref e.rl (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat)) :
    Wp (cdoWhile (dolen8 c) (fun l => pure (l.againL, l)) l) (e.heap A msg m) (fun l' h' =>
      ∃ u' A' o' valid' m' msg',
        Inv64 e l'.hold l'.bits i u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
        l'.in_ = .ref e.ib i ∧ l'.out = .ref e.ob o' ∧ o ≤ o' ∧ o' ≤ o + 258 ∧
        h' = e.heap A' msg' m' ∧ A'.size = A.size ∧
        (∀ j, (j < o ∨ o + 273 ≤ j) → A'[j]? = A[j]?) ∧
        (l'.broke = false → msg' = msg) ∧ (m' = TYPE → msg' = msg) ∧
        Dolen8Event e m A o u A' o' u' l'.broke m') := by
  have hkIdx : l.hold.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨hk0, hlk0, hnl0⟩ := lenRoot_info e.hlt _ hkIdx
  have hEd0 : (e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : LenLink (e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default)
    · have := (hlk0 hl).1; omega
    · have := (hnl0 hl).1; omega
  have hcl0 : (LenLink (e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default) ∧
      LinkOK LenLeaf e.LCA e.ol (e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default)) ∨
      LenLeaf 0 (e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default) := by
    by_cases hl : LenLink (e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default)
    · exact Or.inl ⟨hl, hlk0 hl⟩
    · exact Or.inr (hnl0 hl)
  have hholdLt0 : l.hold.toNat % 2 ^ l.bits.toNat < 2 ^ l.bits.toNat :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsg0 : Sg e (l.hold.toNat % 2 ^ l.bits.toNat) l.bits.toNat i = (initial e).drop u := inv.sg_mod
  have hmodLen0 : l.hold.toNat % 2 ^ l.bits.toNat % 2 ^ e.s0.lenbits.toNat =
      l.hold.toNat % 2 ^ e.s0.lenbits.toNat := by
    have hlb := e.hlt.1
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hp1 := dolen8_pass_wp hc A msg m l i o u valid 0 (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat)
    inv hlIn hlOut (by omega) hb63 hAsz hbgo hroom hbroke hhere hk0 hEd0 hcl0
  obtain ⟨l1, h1, hr1, hin1, hres1⟩ := hp1
  generalize hE0 : e.LCA.getD (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat) default = E0 at *
  rcases hres1 with ⟨hagL1, hbr1, rfl, hlink0, j, hjlt, hjEq, hhere1, hout1, hbits1, inv1⟩ |
      ⟨hagL1, hnl0', u', A', o', valid', m', msg', inv', hb8, hb63', hout', hoLo, hoHi,
        rfl, hAsz', hOut', hcase⟩
  · have hlk0' := hlk0 hlink0
    have hleaf1 := hlk0'.2.2.2.2 j hjlt
    have hk1 : e.ol + E0.val.toNat + j < e.LCA.size := by have := hlk0'.2.2.2.1; omega
    have hp2 := dolen8_pass_wp hc A msg m l1 i o (u + E0.bits.toNat) (valid - E0.bits.toNat)
      E0.bits.toNat (e.ol + E0.val.toNat + j) inv1 hin1 hout1 (by omega) (by omega)
      hAsz hbgo hroom hbr1 hhere1 hk1 hleaf1.1 (Or.inr hleaf1)
    obtain ⟨l2, h2, hr2, hin2, hres2⟩ := hp2
    generalize hE1 : e.LCA.getD (e.ol + E0.val.toNat + j) default = E1 at *
    rcases hres2 with ⟨_, _, _, hlink1, -⟩ |
        ⟨hagL2, hnl1, u', A', o', valid', m', msg', inv', hb8, hb63', hout', hoLo, hoHi,
          rfl, hAsz', hOut', hcase⟩
    · rcases hleaf1.2 with h0 | h | h
      · exact False.elim (hlink1.1 h0)
      · exact False.elim (h.1 hlink1.2.1)
      · exact False.elim (h.2 hlink1.2.2)
    · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true, l1), e.heap A msg m) := by simp [hagL1]
      have c2 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l2 (e.heap A' msg' m') =
          .ok ((false, l2), e.heap A' msg' m') := by simp [hagL2]
      have hlook : LengthSemantics.Look e (l.hold.toNat % 2 ^ l.bits.toNat)
          ((l.hold.toNat % 2 ^ l.bits.toNat) % 2 ^ e.s0.lenbits.toNat) E1 (E0.bits.toNat + E1.bits.toNat) := by
        refine Or.inr ⟨E0, j, ?_, hlink0, hjlt, ?_, hE1, rfl, by have := hleaf1.1; omega, hnl1⟩
        · rw [hmodLen0]; exact hE0
        · rw [hjEq]
          exact (mod_div_mod_two_pow l.hold.toNat l.bits.toNat E0.bits.toNat E0.op.toNat
            (by have := hlk0'.1; have := hlk0'.2.2.1; omega)).symm
      exact Wp.of_eq (cdoWhile_two hr1 c1 hr2 c2)
        ⟨u', A', o', valid', m', msg', inv', hb8, hb63', hin2, hout', hoLo, hoHi, rfl, hAsz', hOut',
          (dolen8_msg_of_case hcase).1, (dolen8_msg_of_case hcase).2,
          dolen8_build_event (by omega) hholdLt0 hsg0 (by have := hleaf1.1; omega) hlook
            (Nat.add_assoc u _ _) hAsz' hOut' hcase⟩
  · have c1 : (fun l : L => (pure (l.againL, l) : M (Bool × L))) l1 (e.heap A' msg' m') =
        .ok ((false, l1), e.heap A' msg' m') := by simp [hagL1]
    have hlook : LengthSemantics.Look e (l.hold.toNat % 2 ^ l.bits.toNat)
        ((l.hold.toNat % 2 ^ l.bits.toNat) % 2 ^ e.s0.lenbits.toNat) E0 E0.bits.toNat :=
      Or.inl ⟨by rw [hmodLen0]; exact hE0, rfl, hnl0'⟩
    exact Wp.of_eq (cdoWhile_one hr1 c1)
      ⟨u', A', o', valid', m', msg', inv', hb8, hb63', hin1, hout', hoLo, hoHi, rfl, hAsz', hOut',
        (dolen8_msg_of_case hcase).1, (dolen8_msg_of_case hcase).2,
        dolen8_build_event (by omega) hholdLt0 hsg0 (by omega) hlook rfl hAsz' hOut' hcase⟩

private theorem refill_dolen8_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o u valid : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i) (hlOut : l.out = .ref e.ob o)
    (hb26 : 26 ≤ l.bits.toNat) (hb63 : l.bits.toNat ≤ 63)
    (hi8 : i + 8 ≤ e.i0 + e.sm0.avail_in.toNat)
    (hAsz : A.size = e.A0.size) (_ho0 : e.o0 ≤ o) (hbgo : e.bg ≤ o)
    (hroom : o + 273 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAout : ∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A[j]? = e.A0[j]?)
    (hbroke : l.broke = false)
    (hhere : l.here = .ref e.rl (e.ol + l.hold.toNat % 2 ^ e.s0.lenbits.toNat)) :
    Wp (do
      let l ← refill64 l
      cdoWhile (dolen8 c) (fun l => pure (l.againL, l)) l) (e.heap A msg m) (fun l' h' =>
      let i1 := i + (63 - l.bits.toNat) / 8
      ∃ u' A' o' valid' m' msg',
        Inv64 e l'.hold l'.bits i1 u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
        l'.in_ = .ref e.ib i1 ∧ i ≤ i1 ∧ i1 ≤ i + 4 ∧
        l'.out = .ref e.ob o' ∧ o ≤ o' ∧ o' ≤ o + 258 ∧
        h' = e.heap A' msg' m' ∧ A'.size = A.size ∧
        (∀ j, (j < o ∨ o + 273 ≤ j) → A'[j]? = A[j]?) ∧
        (l'.broke = false → msg' = msg) ∧ (m' = TYPE → msg' = msg) ∧
        Dolen8Event e m A o u A' o' u' l'.broke m') := by
  have hfr : e.InputFrame A i :=
    e.inputFrame_of_cap_frame hAsz hAout (by omega) inv.inputLower
  have href := refill64_wp A msg m l i u valid inv hlIn hb63 hi8 hfr
  obtain ⟨l1, h1, hr1, rfl, hin1, hbits1, hb56, hb63', _, _, inv1⟩ := href
  have hhere1 : l1.here = .ref e.rl (e.ol + l1.hold.toNat % 2 ^ e.s0.lenbits.toNat) := by
    have hlb := e.hlt.1
    have hmodEq := Inv64.hold_mod_eq inv inv1
      (Nat.le_trans hlb (by have := inv.bitsLe; omega))
      (Nat.le_trans hlb (by have := inv1.bitsLe; omega))
    have hl1Here : l1.here = l.here := by rw [hin1]
    rw [hl1Here, hhere, hmodEq]
  have hin1_in : l1.in_ = .ref e.ib (i + (63 - l.bits.toNat) / 8) := by rw [hin1]
  have hin1_out : l1.out = .ref e.ob o := by rw [hin1]; exact hlOut
  have hin1_br : l1.broke = false := by rw [hin1]; exact hbroke
  have hin1_56 : 56 ≤ l1.bits.toNat := by rw [hin1]; exact hb56
  have hin1_63 : l1.bits.toNat ≤ 63 := by rw [hin1]; exact hb63'
  have hd := dolen8_wp hc A msg m l1 (i + (63 - l.bits.toNat) / 8) o u 64
    inv1 hin1_in hin1_out hin1_56 hin1_63 hAsz hbgo hroom hin1_br hhere1
  obtain ⟨l2, h2, hr2, u', A', o', valid', m', msg', inv', hb8, hb63'', hin2, hout', hoLo, hoHi,
    rfl, hAsz', hOut', hmsgBr, hmsgTy, hev⟩ := hd
  refine Wp.of_eq (bind_ok hr1 |>.trans hr2) ⟨u', A', o', valid', m', msg', inv', hb8, hb63'',
    hin2, by omega, by omega, hout', hoLo, hoHi, rfl, hAsz', hOut', hmsgBr, hmsgTy, hev⟩

private theorem root_lit_step {e : Env} (A : Array UInt8) (msg : BPtr) (m : UInt32)
    {hold : UInt64} {bits : UInt32} {i o u valid : Nat}
    (inv : Inv64 e hold bits i u valid) (hb15 : 15 ≤ bits.toNat) (hb63 : bits.toNat ≤ 63)
    (hAsz : A.size = e.A0.size) (hroom : o + 1 ≤ e.o0 + e.sm0.avail_out.toNat) :
    let idx := e.ol + hold.toNat % 2 ^ e.s0.lenbits.toNat
    let E := e.LCA.getD idx default
    E.op = 0 →
    E.bits.toNat ≤ 15 ∧
    E.bits.toUInt32.toNat ≤ bits.toNat ∧
    (bits - E.bits.toUInt32).toNat = bits.toNat - E.bits.toNat ∧
    Inv64 e (hold >>> E.bits.toUInt32.toUInt64) (bits - E.bits.toUInt32) i
      (u + E.bits.toNat) (valid - E.bits.toNat) ∧
    OkOn (e.heap A msg m) (shr64 hold E.bits.toUInt64) (hold >>> E.bits.toUInt32.toUInt64) ∧
    store8 (.ref e.ob o) E.val.toUInt8 (e.heap A msg m) =
      .ok ((), e.heap (A.set! o E.val.toUInt8) msg m) ∧
    OkOn (e.heap (A.set! o E.val.toUInt8) msg m) (Ptr.add (.ref e.ob o) 1) (.ref e.ob (o + 1)) ∧
    Dolen8Event e m A o u (A.set! o E.val.toUInt8) (o + 1) (u + E.bits.toNat) false m := by
  intro idx E hE0
  have hkIdx : hold.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨_, _, hnl⟩ := lenRoot_info e.hlt _ hkIdx
  have hnlE : ¬ LenLink E := fun h => h.1 hE0
  have hleaf := hnl hnlE
  have hEb : E.bits.toNat ≤ 15 := hleaf.1
  have hEb32 : E.bits.toUInt32.toNat = E.bits.toNat := by simp
  have hEb64 : E.bits.toUInt32.toUInt64 = E.bits.toUInt64 := UInt8.toUInt64_toUInt32 E.bits
  have hEbLe : E.bits.toUInt32.toNat ≤ bits.toNat := by rw [hEb32]; omega
  have inv1 := inv.drop E.bits.toUInt32 hEbLe (by omega)
  rw [hEb32] at inv1
  have hbSub : (bits - E.bits.toUInt32).toNat = bits.toNat - E.bits.toNat := by
    rw [u32_toNat_sub hEbLe, hEb32]
  have hshr : OkOn (e.heap A msg m) (shr64 hold E.bits.toUInt64) (hold >>> E.bits.toUInt32.toUInt64) := by
    simpa only [hEb64] using shr64_ok (h := e.heap A msg m) (x := hold) (n := E.bits.toUInt32.toUInt64) (by simp; omega)
  have hAsz0 : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hst : store8 (.ref e.ob o) E.val.toUInt8 (e.heap A msg m) =
      .ok ((), e.heap (A.set! o E.val.toUInt8) msg m) := by
    rw [← e.heap_put A (A.set! o E.val.toUInt8) msg m]
    exact Ptr.store_ok (off := o) (e.heap_bytes_ob A msg m) (e.heap_ro_ob A msg m) (by omega)
  have hadd := Ptr.add_nat_ok (e.heap_bytes_ob (A.set! o E.val.toUInt8) msg m)
    (r := e.ob) (off := o) (n := 1) (by simp; omega)
  have hlook : LengthSemantics.Look e (hold.toNat % 2 ^ bits.toNat)
      ((hold.toNat % 2 ^ bits.toNat) % 2 ^ e.s0.lenbits.toNat) E E.bits.toNat := by
    have hlb := e.hlt.1
    refine Or.inl ⟨?_, rfl, hnlE⟩
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hev := Dolen8Event.lit (m := m) (A := A) (o := o) (u := u)
    (hold.toNat % 2 ^ bits.toNat) bits.toNat i E E.bits.toNat hb15
    (Nat.mod_lt _ (Nat.two_pow_pos _)) inv.sg_mod hEb hlook hE0
  exact ⟨hEb, hEbLe, hbSub, inv1, hshr, hst, by simpa using hadd, hev⟩

private theorem set_bang_ne (A : Array UInt8) (o j : Nat) (v : UInt8) (ho : o < A.size) (hne : o ≠ j) :
    (A.set! o v)[j]? = A[j]? := by
  simp [Array.set!, Array.setIfInBounds, ho, hne]

/-- One iteration of the 64-bit fast loop (`inflate_fast_body8`). Executes 1 or 2 `refill64`
calls, handles 0–3 fast literals and an optional `dolen8` match/literal/exit, updates output inside
`[o, e.o0 + avail_out)`, preserves `Inv64` with `8 ≤ l'.bits ≤ 63`, advances `in_` by at most 11
and `out` by at most 260, and builds a `Body8Trace`. -/
theorem inflate_fast_body8_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o u valid : Nat)
    (inv : Inv64 e l.hold l.bits i u valid)
    (hlIn : l.in_ = .ref e.ib i) (hlOut : l.out = .ref e.ob o)
    (hb63 : l.bits.toNat ≤ 63)
    (hi16 : i + 16 ≤ e.i0 + e.sm0.avail_in.toNat)
    (ho275 : o + 275 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAsz : A.size = e.A0.size) (_ho0 : e.o0 ≤ o) (hbgo : e.bg ≤ o)
    (hAout : ∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A[j]? = e.A0[j]?)
    (hbroke : l.broke = false) :
    Wp (inflate_fast_body8 c l) (e.heap A msg m) (fun l' h' =>
      ∃ i' u' A' o' valid' m' msg',
        Inv64 e l'.hold l'.bits i' u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
        l'.in_ = .ref e.ib i' ∧ i ≤ i' ∧ i' ≤ i + 11 ∧
        l'.out = .ref e.ob o' ∧ o ≤ o' ∧ o' ≤ o + 260 ∧
        h' = e.heap A' msg' m' ∧ A'.size = A.size ∧
        (∀ j, (j < o ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A'[j]? = A[j]?) ∧
        (l'.broke = false → msg' = msg) ∧ (m' = TYPE → msg' = msg) ∧
        Body8Trace e m A o u A' o' u' l'.broke m') := by
  have hAsz0 : e.o0 + e.sm0.avail_out.toNat ≤ A.size := by rw [hAsz]; exact e.hAsz
  have hfr0 : e.InputFrame A i :=
    e.inputFrame_of_cap_frame hAsz hAout (by omega) inv.inputLower
  have href1 := refill64_wp A msg m l i u valid inv hlIn hb63 (by omega) hfr0
  obtain ⟨l1, h1, hr1, rfl, hin1, hbits1, hb1_56, hb1_63, _, _, inv1⟩ := href1
  let i1 := i + (63 - l.bits.toNat) / 8
  have hl1_in : l1.in_ = .ref e.ib i1 := by rw [hin1]
  have hl1_56 : 56 ≤ l1.bits.toNat := by rw [hin1]; exact hb1_56
  have hl1_63 : l1.bits.toNat ≤ 63 := by rw [hin1]; exact hb1_63
  have hl1_out : l1.out = .ref e.ob o := by rw [hin1]; exact hlOut
  have hl1_br : l1.broke = false := by rw [hin1]; exact hbroke
  have hi1Bnd : i ≤ i1 ∧ i1 ≤ i + 7 := ⟨by omega, by omega⟩
  have hlc : c.lcode = .ref e.rl e.ol := by rw [hc.lcode]; exact e.hlc
  have hR : e.s0.lenbits.toNat < 32 := by have := e.hlt.1; omega
  have hlmask : c.lmask.toUInt64.toNat = 2 ^ e.s0.lenbits.toNat - 1 := by
    rw [hc.lmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx1 := u64_and_mask (x := l1.hold) hlmask
  have hmod1Lt : l1.hold.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨hk1, _, _⟩ := lenRoot_info e.hlt _ hmod1Lt
  have haddH1 := Ptr.add_nat_ok (e.heap_cget_LCA A msg m) (r := e.rl) (off := e.ol)
    (n := (l1.hold &&& c.lmask.toUInt64).toNat) (by rw [hidx1]; have := e.hlt.2.1; omega)
  have hld1 : OkOn (e.heap A msg m) (Ptr.load (.ref e.rl (e.ol + (l1.hold &&& c.lmask.toUInt64).toNat)))
      (e.LCA.getD (e.ol + l1.hold.toNat % 2 ^ e.s0.lenbits.toNat) default) := by
    have hkE : e.LCA[e.ol + l1.hold.toNat % 2 ^ e.s0.lenbits.toNat]'hk1 =
        e.LCA.getD (e.ol + l1.hold.toNat % 2 ^ e.s0.lenbits.toNat) default := by
      simp [Array.getD_eq_getD_getElem?, hk1]
    rw [hidx1, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A msg m) hk1
  generalize hE1 : e.LCA.getD (e.ol + l1.hold.toNat % 2 ^ e.s0.lenbits.toNat) default = E1 at *
  unfold inflate_fast_body8
  rw [wp_bind_ok hr1, hlc, wp_bind_ok haddH1]
  dsimp only
  rw [wp_bind_ok hld1]
  by_cases hE1_0 : (E1.op == 0) = true
  · have hE1z : E1.op = 0 := by simpa using hE1_0
    obtain ⟨hEb1, _, hsub1, inv2, hshr2, hst1, haddO1, hev1⟩ :=
      root_lit_step (o := o) A msg m inv1 (by omega) hl1_63 hAsz (by omega) (by rw [hE1]; exact hE1z)
    rw [hE1] at hEb1 hsub1 inv2 hshr2 hst1 haddO1 hev1
    let hold2 := l1.hold >>> E1.bits.toUInt32.toUInt64
    let bits2 := l1.bits - E1.bits.toUInt32
    let A1 := A.set! o E1.val.toUInt8
    let u1 := u + E1.bits.toNat
    have hb2_ge41 : 41 ≤ bits2.toNat := by dsimp only [bits2]; rw [hsub1]; omega
    have hb2_le63 : bits2.toNat ≤ 63 := by dsimp only [bits2]; rw [hsub1]; omega
    have hA1sz : A1.size = e.A0.size := by simp [A1, hAsz]
    have hidx2 := u64_and_mask (x := hold2) hlmask
    have hmod2Lt : hold2.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨hk2, _, _⟩ := lenRoot_info e.hlt _ hmod2Lt
    have haddH2 := Ptr.add_nat_ok (e.heap_cget_LCA A1 msg m) (r := e.rl) (off := e.ol)
      (n := (hold2 &&& c.lmask.toUInt64).toNat) (by rw [hidx2]; have := e.hlt.2.1; omega)
    have hld2 : OkOn (e.heap A1 msg m) (Ptr.load (.ref e.rl (e.ol + (hold2 &&& c.lmask.toUInt64).toNat)))
        (e.LCA.getD (e.ol + hold2.toNat % 2 ^ e.s0.lenbits.toNat) default) := by
      have hkE : e.LCA[e.ol + hold2.toNat % 2 ^ e.s0.lenbits.toNat]'hk2 =
          e.LCA.getD (e.ol + hold2.toNat % 2 ^ e.s0.lenbits.toNat) default := by
        simp [Array.getD_eq_getD_getElem?, hk2]
      rw [hidx2, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A1 msg m) hk2
    generalize hE2 : e.LCA.getD (e.ol + hold2.toNat % 2 ^ e.s0.lenbits.toNat) default = E2 at *
    rw [if_t hE1_0, wp_bind_ok hshr2]
    rw [hl1_out, wp_bind_ok hst1, wp_bind_ok haddO1, wp_bind_ok haddH2]
    rw [wp_bind_ok hld2]
    by_cases hE2_0 : (E2.op == 0) = true
    · have hE2z : E2.op = 0 := by simpa using hE2_0
      obtain ⟨hEb2, _, hsub2, inv3, hshr3, hst2, haddO2, hev2⟩ :=
        root_lit_step (o := o + 1) A1 msg m inv2 (by omega) hb2_le63 hA1sz (by omega) (by rw [hE2]; exact hE2z)
      rw [hE2] at hEb2 hsub2 inv3 hshr3 hst2 haddO2 hev2
      let hold3 := hold2 >>> E2.bits.toUInt32.toUInt64
      let bits3 := bits2 - E2.bits.toUInt32
      let A2 := A1.set! (o + 1) E2.val.toUInt8
      let u2 := u1 + E2.bits.toNat
      have hb3_ge26 : 26 ≤ bits3.toNat := by dsimp only [bits3]; rw [hsub2]; omega
      have hb3_le63 : bits3.toNat ≤ 63 := by dsimp only [bits3]; rw [hsub2]; omega
      have hA2sz : A2.size = e.A0.size := by simp [A2, hA1sz]
      have hidx3 := u64_and_mask (x := hold3) hlmask
      have hmod3Lt : hold3.toNat % 2 ^ e.s0.lenbits.toNat < 2 ^ e.s0.lenbits.toNat :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      obtain ⟨hk3, _, _⟩ := lenRoot_info e.hlt _ hmod3Lt
      have haddH3 := Ptr.add_nat_ok (e.heap_cget_LCA A2 msg m) (r := e.rl) (off := e.ol)
        (n := (hold3 &&& c.lmask.toUInt64).toNat) (by rw [hidx3]; have := e.hlt.2.1; omega)
      have hld3 : OkOn (e.heap A2 msg m) (Ptr.load (.ref e.rl (e.ol + (hold3 &&& c.lmask.toUInt64).toNat)))
          (e.LCA.getD (e.ol + hold3.toNat % 2 ^ e.s0.lenbits.toNat) default) := by
        have hkE : e.LCA[e.ol + hold3.toNat % 2 ^ e.s0.lenbits.toNat]'hk3 =
            e.LCA.getD (e.ol + hold3.toNat % 2 ^ e.s0.lenbits.toNat) default := by
          simp [Array.getD_eq_getD_getElem?, hk3]
        rw [hidx3, ← hkE]; exact Ptr.load_ok (e.heap_cget_LCA A2 msg m) hk3
      generalize hE3 : e.LCA.getD (e.ol + hold3.toNat % 2 ^ e.s0.lenbits.toNat) default = E3 at *
      rw [if_t hE2_0, wp_bind_ok hshr3, wp_bind_ok hst2, wp_bind_ok haddO2, wp_bind_ok haddH3]
      rw [wp_bind_ok hld3]
      by_cases hE3_0 : (E3.op == 0) = true
      · have hE3z : E3.op = 0 := by simpa using hE3_0
        obtain ⟨hEb3, _, hsub3, inv4, hshr4, hst3, haddO3, hev3⟩ :=
          root_lit_step (o := o + 2) A2 msg m inv3 (by omega) hb3_le63 hA2sz (by omega) (by rw [hE3]; exact hE3z)
        rw [hE3] at hEb3 hsub3 inv4 hshr4 hst3 haddO3 hev3
        let hold4 := hold3 >>> E3.bits.toUInt32.toUInt64
        let bits4 := bits3 - E3.bits.toUInt32
        let A3 := A2.set! (o + 2) E3.val.toUInt8
        let u3 := u2 + E3.bits.toNat
        have hb4_ge8 : 8 ≤ bits4.toNat := by dsimp only [bits4]; rw [hsub3]; omega
        have hb4_le63 : bits4.toNat ≤ 63 := by dsimp only [bits4]; rw [hsub3]; omega
        rw [if_t hE3_0, wp_bind_ok hshr4, wp_bind_ok hst3, wp_bind_ok haddO3]
        refine Wp.pure' ⟨i1, u3, A3, o + 3, _, m, msg, inv4, hb4_ge8, hb4_le63, hl1_in,
          by omega, by omega, rfl, by omega, by omega, rfl, by simp [A3, A2, A1],
          fun j hj => ?_, fun _ => rfl, fun _ => rfl, ?_⟩
        · have hlt0 : o < A.size := by omega
          have hlt1 : o + 1 < A1.size := by simp [A1]; omega
          have hlt2 : o + 2 < A2.size := by simp [A2, A1]; omega
          rw [set_bang_ne _ _ _ _ hlt2 (by omega), set_bang_ne _ _ _ _ hlt1 (by omega),
            set_bang_ne _ _ _ _ hlt0 (by omega)]
        · rw [hl1_br]; exact Body8Trace.step hev1 (Body8Trace.step hev2 (Body8Trace.base hev3))
      · rw [if_f hE3_0]
        let l3 : L := { l1 with hold := hold3, bits := bits3, out := .ref e.ob (o + 2),
                                here := .ref e.rl (e.ol + (hold3 &&& c.lmask.toUInt64).toNat) }
        have hA2out : ∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A2[j]? = e.A0[j]? := by
          intro j hj
          have hlt0 : o < A.size := by omega
          have hlt1 : o + 1 < A1.size := by simp [A1]; omega
          rw [← hAout j hj, set_bang_ne _ _ _ _ hlt1 (by omega), set_bang_ne _ _ _ _ hlt0 (by omega)]
        have hrd := refill_dolen8_wp hc A2 msg m l3 i1 (o + 2) u2 _ inv3 hl1_in rfl hb3_ge26 hb3_le63
          (by omega) hA2sz (by omega) (by omega) (by omega) hA2out hl1_br (by simp [l3, hidx3])
        obtain ⟨l', h', hrD, u', A', o', valid', m', msg', inv', hb8, hb63', hin', hi1Lo, hi1Hi,
          hout', hoLo, hoHi, rfl, hAsz', hOut', hmsgBr, hmsgTy, hevD⟩ := hrd
        refine Wp.of_eq hrD ⟨_, u', A', o', valid', m', msg', inv', hb8, hb63', hin',
          by omega, by omega, hout', by omega, by omega, rfl, by rw [hAsz']; simp [A2, A1],
          fun j hj => ?_, hmsgBr, hmsgTy, Body8Trace.step hev1 (Body8Trace.step hev2 (Body8Trace.base hevD))⟩
        have hlt0 : o < A.size := by omega
        have hlt1 : o + 1 < A1.size := by simp [A1]; omega
        rw [hOut' j (by omega), set_bang_ne _ _ _ _ hlt1 (by omega), set_bang_ne _ _ _ _ hlt0 (by omega)]
    · rw [if_f hE2_0]
      let l2 : L := { l1 with hold := hold2, bits := bits2, out := .ref e.ob (o + 1),
                              here := .ref e.rl (e.ol + (hold2 &&& c.lmask.toUInt64).toNat) }
      have hA1out : ∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A1[j]? = e.A0[j]? := by
        intro j hj
        have hlt0 : o < A.size := by omega
        rw [← hAout j hj, set_bang_ne _ _ _ _ hlt0 (by omega)]
      have hrd := refill_dolen8_wp hc A1 msg m l2 i1 (o + 1) u1 _ inv2 hl1_in rfl (by dsimp only [l2]; omega) hb2_le63
        (by omega) hA1sz (by omega) (by omega) (by omega) hA1out hl1_br (by simp [l2, hidx2])
      obtain ⟨l', h', hrD, u', A', o', valid', m', msg', inv', hb8, hb63', hin', hi1Lo, hi1Hi,
        hout', hoLo, hoHi, rfl, hAsz', hOut', hmsgBr, hmsgTy, hevD⟩ := hrd
      refine Wp.of_eq hrD ⟨_, u', A', o', valid', m', msg', inv', hb8, hb63', hin',
        by omega, by omega, hout', by omega, by omega, rfl, by rw [hAsz']; simp [A1],
        fun j hj => ?_, hmsgBr, hmsgTy, Body8Trace.step hev1 (Body8Trace.base hevD)⟩
      have hlt0 : o < A.size := by omega
      rw [hOut' j (by omega), set_bang_ne _ _ _ _ hlt0 (by omega)]
  · rw [if_f hE1_0]
    let l1' : L := { l1 with here := .ref e.rl (e.ol + (l1.hold &&& c.lmask.toUInt64).toNat) }
    have hd := dolen8_wp hc A msg m l1' i1 o u _
      inv1 hl1_in hl1_out hl1_56 hl1_63 hAsz hbgo (by omega) hl1_br (by simp [l1', hidx1])
    obtain ⟨l', h', hrD, u', A', o', valid', m', msg', inv', hb8, hb63', hin', hout', hoLo, hoHi,
      rfl, hAsz', hOut', hmsgBr, hmsgTy, hevD⟩ := hd
    exact Wp.of_eq hrD ⟨i1, u', A', o', valid', m', msg', inv', hb8, hb63', hin',
      hi1Bnd.1, by omega, hout', hoLo, by omega, rfl, hAsz',
      fun j hj => hOut' j (by omega), hmsgBr, hmsgTy, Body8Trace.base hevD⟩

end Zlib.Inffast.Proofs



