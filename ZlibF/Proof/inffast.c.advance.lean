import ZlibF.Spec.Common.Inflate.InflateFast
import ZlibF.Proof.«inffast.c.len»
import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«inffast.c.advance-dodist»

/-!
# inffast.c: exact input advancement in the distance and length branches

These proofs retain the single-pull consequence of the existing bit bounds.
No new semantic definition or caller contract is introduced.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

variable {α : Bool} {e : EnvG α} {c : Ctx}

theorem dodistLoop_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o kidx : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat) (hk : kidx < 2 ^ e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd (e.od + kidx)) (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat))
    (hfr : e.InputFrame A i) :
    Wp (cdoWhile (dodist c) (fun l => pure (l.againD, l)) l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ i + 2 ∧ (20 ≤ l.bits.toNat → i' ≤ i + 1) ∧
        l'.in_ = .ref e.ib i') := by
  obtain ⟨hksz, hlk, hnl⟩ := distRoot hts kidx hk
  have hcl0 := distClass_of (e := e) _ hlk hnl
  have hEd0 : (e.DCA.getD (e.od + kidx) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : DistLink (e.DCA.getD (e.od + kidx) default)
    · have := (hlk hl).1; omega
    · have := (hnl hl).1; omega
  obtain ⟨l1, h1, e1, hq1⟩ := dodist_pass hc A msg m l i o 0 (e.od + kidx) hls hA ho hAb hbroke hlen hhere hksz
    (by omega) hEd0 hcl0 (by simpa using hpull) (hfr.mono (by omega))
  have hadv1 := Wp.at_run (dodist_advance_wp hc A msg m l i o 0 (e.od + kidx) hls hA ho hAb hbroke hlen hhere hksz
    (by omega) hEd0 hcl0 (by simpa using hpull) (hfr.mono (by omega))) e1
  obtain ⟨E0, hE0⟩ : ∃ E0, e.DCA.getD (e.od + kidx) default = E0 := ⟨_, rfl⟩
  rw [hE0] at hq1 hlk hnl hcl0 hEd0
  rcases hq1 with ⟨hag, hbr, hh, ⟨hl16, hl64⟩, j, hjlt, hjd, hhere1, hls1, hsg1, hb1, hlen1, hout1, hdist1, hagL1⟩ | ⟨hNL, hag, hend⟩
  · -- a link: the second pass ends the block
    subst hh
    have hlink : DistLink E0 := ⟨hl16, hl64⟩
    have hlk' := hlk hlink
    have hleaf := hlk'.2.2.2.2 j hjlt
    have hk2 : e.od + E0.val.toNat + j < e.DCA.size := by
      have := hlk'.2.2.2.1; omega
    have hcl1 : DistClass e (e.DCA.getD (e.od + E0.val.toNat + j) default) := by
      rcases hleaf.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hb15' : E0.bits.toNat ≤ 15 := hlk'.1
    obtain ⟨l2, h2, e2, hq2⟩ := dodist_pass hc A msg m l1 i o E0.bits.toNat (e.od + E0.val.toNat + j) hls1 hA ho hAb hbr
      (by rw [hlen1]; exact hlen) hhere1 hk2 (by have := hleaf.1; omega) (by omega) hcl1 (by
        rcases hpull with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩) (hfr.mono (by omega))
    have hadv2 := Wp.at_run (dodist_advance_wp hc A msg m l1 i o E0.bits.toNat (e.od + E0.val.toNat + j) hls1 hA ho hAb hbr
      (by rw [hlen1]; exact hlen) hhere1 hk2 (by have := hleaf.1; omega) (by omega) hcl1 (by
        rcases hpull with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩) (hfr.mono (by omega))) e2
    rcases hq2 with ⟨hag2, -, -, ⟨hl16', hl64'⟩, -⟩ | hend2
    · rcases hleaf.2 with h | h
      · exact absurd hl16' h.1
      · exact absurd hl64' h.2
    · have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 (e.heap A msg m) = .ok ((true, l1), e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l2 h2 = .ok ((false, l2), h2) := by simp [hend2.2.1]
      have e1' : dodist c l (e.heap A msg m) = .ok (l1, e.heap A msg m) := e1
      refine Wp.of_eq (cdoWhile_two e1' c1 e2 c2) ?_
      obtain ⟨i', hi1, hi2, htight, hin⟩ := hadv2
      exact ⟨i', hi1, hi2, (by intro h; apply htight; omega), hin⟩
  · -- the first pass ended the block
    have c1 : (fun l : L => (pure (l.againD, l) : M (Bool × L))) l1 h1 = .ok ((false, l1), h1) := by simp [hag]
    refine Wp.of_eq (cdoWhile_one e1 c1) ?_
    obtain ⟨i', hi1, hi2, htight, hin⟩ := hadv1
    exact ⟨i', hi1, hi2, (by intro h; apply htight; omega), hin⟩


theorem dolenDist_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat))
    (hfr : e.InputFrame A i) :
    Wp (dolenDist c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ i + 2 ∧ (20 ≤ l.bits.toNat → i' ≤ i + 1) ∧
        l'.in_ = .ref e.ib i') := by
  unfold dolenDist
  have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
  have hR : e.s0.distbits.toNat < 32 := by have := hts.1; omega
  have hmask : c.dmask.toUInt64.toNat = 2 ^ e.s0.distbits.toNat - 1 := by
    rw [hc.dmask, UInt32.toNat_toUInt64]; exact u32_shl1_sub1 hR
  have hidx := u64_and_mask (x := l.hold) hmask
  have hmod : l.hold.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
    Nat.mod_lt _ (Nat.pow_pos (by omega))
  refine Wp.bindO (x := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat)) ?_ ?_
  · rw [hdc, hidx]
    exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (by have := hts.2.1; omega)
  · exact Wp.mono (dodistLoop_advance_wp hc A msg m { l with here := Ptr.ref e.rd (e.od + l.hold.toNat % 2 ^ e.s0.distbits.toNat) }
      i o _ hts hmod (LS.congr hls rfl rfl rfl rfl) hA ho hAb hbroke hlen rfl hb15 hpull (hfr.mono (by omega))) (fun _ _ h => h)

theorem dolenRefill_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3) (hT3 : i = s + 3 → 4 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenRefill c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ s + 6 ∧ l'.in_ = .ref e.ib i') := by
  unfold dolenRefill
  by_cases h1 : l.bits < 15
  · rw [ite_eq_left h1]
    have h1' : l.bits.toNat < 15 := by simpa using UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref e.ib (i + 1)) hls.hb
    have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
    have hb3' : (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).bits.toNat ≤ 22 := by
      simp only [pullL] at hb3 ⊢; omega
    refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl4 := hl3.pullL hb3' hi2
    have hs4 := Sg_pullL hl3 hb3' hi2
    have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))) (e.IN.getD (i + 1) 0)
      (.ref e.ib (i + 1 + 1)) hl3.hb
    simp only [pullL] at hb3 hb4
    refine Wp.mono (dolenDist_advance_wp hc A msg m _ (i + 1 + 1) o hts hl4 hA ho hAb hbroke hlen (by simp only [pullL]; omega) ?_ (hfr.mono (by omega))) ?_
    · by_cases hc3 : i = s + 3
      · right; have := hT3 hc3; simp only [pullL]; omega
      · left; omega
    · intro l' h' hq
      obtain ⟨i', hi1, hi2, htight, hin⟩ := hq
      refine ⟨i', by omega, ?_, hin⟩
      by_cases hc3 : i = s + 3
      · have hb : 20 ≤ (pullL (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1)))
          (e.IN.getD (i + 1) 0) (.ref e.ib (i + 1 + 1))).bits.toNat := by
          have := hT3 hc3
          simp only [pullL] at hb3 hb4 ⊢
          omega
        have := htight hb
        omega
      · omega
  · rw [ite_eq_right h1]
    have h1' : 15 ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < 15) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr (by simpa using h))
      omega
    refine Wp.mono (dolenDist_advance_wp hc A msg m l i o hts hls hA ho hAb hbroke hlen h1' (Or.inl (by omega)) (hfr.mono (by omega))) ?_
    intro l' h' hq
    obtain ⟨i', hi1, hi2, _, hin⟩ := hq
    exact ⟨i', hi1, by omega, hin⟩


theorem dolenExt_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5) (hxb : l.op.toNat ≤ l.bits.toNat)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 3)
    (hT3 : i = s + 3 → 4 + l.op.toNat ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenExt c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ s + 6 ∧ l'.in_ = .ref e.ib i') := by
  unfold dolenExt
  have hxs : l.op.toNat < 32 := by omega
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
  have hlen' : (l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.len.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have hbn := dropL_bits l l.op hxb
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (dolenRefill_advance_wp hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here, op := l.op,
      len := l.len + (l.hold.toUInt32 &&& (1 <<< l.op) - 1), dist := l.dist, from_ := l.from_, broke := l.broke,
      againL := l.againL, againD := l.againD } i o s hts (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb hbroke
    (by rw [hlen']; omega) hs6 hT (by intro h3; have := hT3 h3; show 4 ≤ (l.bits - l.op).toNat; simp only [dropL] at hbn; omega) (hfr.mono (by omega))) ?_
  exact fun _ _ hq => hq


theorem dolenLen_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o s : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hx : l.op.toNat ≤ 5)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat + 2 ^ l.op.toNat ≤ 259)
    (hs6 : s + 6 ≤ e.i0 + e.sm0.avail_in.toNat) (hT : i ≤ s + 2) (hb2 : i = s + 2 → 1 ≤ l.bits.toNat)
    (hfr : e.InputFrame A i) :
    Wp (dolenLen c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ s + 6 ∧ l'.in_ = .ref e.ib i') := by
  unfold dolenLen
  by_cases h0 : l.op != 0
  · rw [ite_eq_left h0]
    have h0' : l.op.toNat ≠ 0 := by
      intro h; apply (by simpa using h0 : l.op ≠ 0); exact UInt32.toNat_inj.mp (by simpa using h)
    by_cases h1 : l.bits < l.op
    · rw [ite_eq_left h1]
      have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
      have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
      refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
      have hl3 := hls.pullL (by omega) hiin
      have hs3 := Sg_pullL hls (by omega) hiin
      have hb3 := pullL_bits l (e.IN.getD i 0) (.ref e.ib (i + 1)) hls.hb
      refine Wp.mono (dolenExt_advance_wp hc A msg m _ (i + 1) o s hts hl3 hA ho hAb hbroke (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 ⊢; omega) (by simp only [pullL]; omega) hs6 (by omega)
        (by intro h3; simp only [pullL] at hb3 ⊢; have := hb2 (by omega); omega) (hfr.mono (by omega))) ?_
      intro l' h' hq
      obtain ⟨i', hi1, hi2, hin⟩ := hq
      exact ⟨i', by omega, hi2, hin⟩
    · rw [ite_eq_right h1]
      have h1' : l.op.toNat ≤ l.bits.toNat := by
        have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (dolenExt_advance_wp hc A msg m l i o s hts hls hA ho hAb hbroke hx h1' hlen hs6 (by omega)
        (by intro h3; omega) (hfr.mono (by omega))) ?_
      exact fun _ _ hq => hq
  · simp only [h0]
    have h0' : l.op.toNat = 0 := by
      have : l.op = 0 := by simpa using h0
      rw [this]; rfl
    refine Wp.mono (dolenRefill_advance_wp hc A msg m l i o s hts hls hA ho hAb hbroke ⟨hlen.1, by
      have : 0 < 2 ^ l.op.toNat := Nat.pow_pos (by omega)
      omega⟩ hs6 (by omega) (by intro h3; omega) (hfr.mono (by omega))) ?_
    exact fun _ _ hq => hq


theorem readBits_value_lt {n : Nat} {inp rest : List Bool} {v : Nat}
    (hr : readBits n inp = some (v, rest)) : v < 2 ^ n := by
  induction n generalizing inp v rest with
  | zero => simp only [readBits, Option.some.injEq, Prod.mk.injEq] at hr; omega
  | succ n ih =>
    cases inp with
    | nil => cases hr
    | cons b r =>
      cases hread : readBits n r with
      | none => simp [readBits, hread] at hr
      | some vr =>
        rcases vr with ⟨v1, r1⟩
        have hv := ih hread
        simp only [readBits, hread, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, rfl⟩
        rw [Nat.pow_succ]
        cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end Zlib.Inffast.Proofs
