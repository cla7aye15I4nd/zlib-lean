import ZlibF.Spec.Functional.Inflate.InflateFastDistanceOrigin
import ZlibF.Proof.«inffast.c.origin-steps»

/-! One pass of the block at `dodist:` and its distance base keep the source origin, for
`inffast.c.distance-origin`. They do not use `inffast.c.origin` or `inffast.c.advance`, so they build
beside them. -/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec
variable {e : Env} {c : Ctx}

theorem distCont_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o used : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63)
    (hx : l.op.toNat ≤ 13) (hxb : l.op.toNat ≤ l.bits.toNat) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used) :
    Wp (distCont c l) (e.heap A msg m) (fun l' _ =>
      l'.in_ = .ref e.ib i ∧
      Origin.Inv e l'.hold.toNat l'.bits.toNat i (used + l.op.toNat)) := by
  have hbgo : e.bg ≤ o := by have := e.bg_le; have := hls.ho0; omega
  have hoA : o ≤ A.size := by omega
  have hxs : l.op.toNat < 32 := by omega
  unfold distCont
  refine Wp.bindO (shl32_ok hxs) ?_
  dsimp only
  have hlow := hold_low32 (x := l.hold) (k := l.op) hxs
  have hlowlt : l.hold.toNat % 2 ^ l.op.toNat < 2 ^ l.op.toNat := Nat.mod_lt _ (Nat.pow_pos (by omega))
  have hpow : 2 ^ l.op.toNat ≤ 2 ^ 13 := Nat.pow_le_pow_right (by omega) hx
  have hdist' : (l.dist + (l.hold.toUInt32 &&& (1 <<< l.op) - 1)).toNat = l.dist.toNat + l.hold.toNat % 2 ^ l.op.toNat := by
    rw [u32_toNat_add (by rw [hlow]; omega), hlow]
  refine Wp.bindO (shr64_ok (x := l.hold) (n := l.op.toUInt64) (by rw [UInt32.toNat_toUInt64]; omega)) ?_
  have hbgdef : e.bg = e.o0 - (e.start.toNat - e.sm0.avail_out.toNat) := rfl
  have hst32 := UInt32.toNat_lt e.start
  have hstart := e.hstart
  have hbeg := e.hbeg
  have hdiff : OkOn (e.heap A msg m) (Ptr.diff l.out c.beg) (Int64.ofInt (((o - e.bg : Nat)) : Int)) := by
    rw [hls.hout, hc.beg]
    have := Ptr.diff_ok (r := e.ob) (a := A) (o1 := o) (o2 := e.bg) (e.heap_bytes_ob A msg m) hoA (by omega)
      ⟨by omega, by omega⟩
    have e1 : (o : Int) - (e.bg : Int) = ((o - e.bg : Nat) : Int) := by omega
    rw [e1] at this
    exact this
  refine Wp.bindO hdiff ?_
  have hopn : (Int64.ofInt (((o - e.bg : Nat)) : Int)).toUInt64.toUInt32.toNat = o - e.bg := i64_toU32 _ (by omega)
  have hls1 : LS e (dropL l l.op) i o := hls.dropL l.op hxb (by omega)
  have hrb := readBits_bitsOfNat l.op.toNat l.bits.toNat l.hold.toNat (inBits e i) hxb
  have hsg := Sg_dropL (e := e) l l.op i hxb (by omega)
  refine Wp.mono (copyMatch_run (e := e) (c := c) hc A msg m
    { in_ := l.in_, out := l.out, hold := l.hold >>> l.op.toUInt64, bits := l.bits - l.op, here := l.here,
      op := (Int64.ofInt (((o - e.bg : Nat)) : Int)).toUInt64.toUInt32, len := l.len,
      dist := l.dist + (l.hold.toUInt32 &&& 1 <<< l.op - 1), from_ := l.from_, broke := l.broke, againL := l.againL,
      againD := l.againD } o hls.hout hbgo hopn (by simp only [hdist']; omega) hlen.1 (by simp; omega) hA hbroke) ?_
  intro l' h' hq
  obtain ⟨hin, hhold, hbits, _, _, _⟩ := hq
  refine ⟨hin.trans hls.hin, ?_⟩
  have dropped := drop_preserves_origin e l.hold.toNat l.bits.toNat i used l.op.toNat origin hxb
  have afterDrop : Origin.Inv e (dropL l l.op).hold.toNat (dropL l l.op).bits.toNat i
      (used + l.op.toNat) := by
    simpa only [dropL_hold l l.op (by omega), dropL_bits l l.op hxb] using dropped
  simpa only [hhold, hbits, dropL] using afterDrop

theorem pullL_origin (l : L) (i o used : Nat)
    (hls : LS e l i o) (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (available : i < e.i0 + e.sm0.avail_in.toNat) :
    Origin.Inv e (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).hold.toNat
      (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).bits.toNat (i+1) used := by
  have result := pull_preserves_origin e l.hold.toNat l.bits.toNat i used origin available
  simpa only [pullL_hold l _ _ hls.hb hls.hH, pullL_bits l _ _ hls.hb] using result

theorem dodistBase_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o used : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hAb : A.size < 2 ^ 63)
    (hx : l.op.toNat ≤ 13) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 5 ≤ l.bits.toNat))
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (dodistBase c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', l'.in_ = .ref e.ib i' ∧
        Origin.Inv e l'.hold.toNat l'.bits.toNat i' (used + l.op.toNat)) := by
  unfold dodistBase
  by_cases h1 : l.bits < l.op
  · rw [ite_eq_left h1]
    have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
    have hi : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hi (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have locals3 := hls.pullL (by omega) hi
    have origin3 := pullL_origin l i o used hls origin hi
    have bits3 := pullL_bits l (e.IN.getD i 0) (.ref e.ib (i+1)) hls.hb
    by_cases h2 : (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).bits <
        (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).op
    · rw [ite_eq_left h2]
      have h2' : l.bits.toNat + 8 < l.op.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp h2
        simp only [pullL] at this bits3 ⊢
        omega
      have hi2 : i+1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have bound3 : (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).bits.toNat ≤ 22 := by omega
      refine Wp.bindO (pull_run e _ _ (i+1) o locals3 bound3 hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
      have locals4 := locals3.pullL bound3 hi2
      have origin4 := pullL_origin _ (i+1) o used locals3 origin3 hi2
      have bits4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref e.ib (i+1)))
        (e.IN.getD (i+1) 0) (.ref e.ib (i+1+1)) locals3.hb
      refine Wp.mono (distCont_origin_wp hc A msg m _ (i+1+1) o used locals4 hA ho hAb
        (by simp only [pullL]; omega) (by simp only [pullL] at bits3 bits4 ⊢; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega) origin4) ?_
      intro l' h' result
      exact ⟨i+1+1, result⟩
    · rw [ite_eq_right h2]
      have fits3 : (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).op.toNat ≤
          (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).bits.toNat := by
        have : ¬ ((pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).bits.toNat <
            (pullL l (e.IN.getD i 0) (.ref e.ib (i+1))).op.toNat) :=
          fun h => h2 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (distCont_origin_wp hc A msg m _ (i+1) o used locals3 hA ho hAb
        (by simp only [pullL]; omega) fits3 (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) origin3) ?_
      intro l' h' result
      exact ⟨i+1, result⟩
  · rw [ite_eq_right h1]
    have fits : l.op.toNat ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    exact Wp.mono (distCont_origin_wp hc A msg m l i o used hls hA ho hAb hx fits hd1 hd2 hlen hbroke origin)
      (fun _ _ result => ⟨i, result⟩)

set_option maxHeartbeats 1000000 in
theorem dodist_pass_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o d k used : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd k) (hk : k < e.DCA.size)
    (hEb : (e.DCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.DCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : DistClass e (e.DCA.getD k default))
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat + d))
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (dodist c l) (e.heap A msg m) (fun l' _ =>
      ∃ i' used', l'.in_ = .ref e.ib i' ∧
        Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  have hkE : e.DCA[k]'hk = e.DCA.getD k default := by simp [Array.getD_eq_getD_getElem?, hk]
  have hld : OkOn (e.heap A msg m) (Ptr.load l.here) (e.DCA.getD k default) := by
    rw [hhere, ← hkE]; exact Ptr.load_ok (e.heap_cget_DCA A msg m) hk
  have hEb64 : (((e.DCA.getD k default).bits.toUInt32).toUInt64).toNat = (e.DCA.getD k default).bits.toNat := by
    simp
  have hEbn : ((e.DCA.getD k default).bits.toUInt32).toNat = (e.DCA.getD k default).bits.toNat := toNat32 _
  have hls1 : LS e (dropL l (e.DCA.getD k default).bits.toUInt32) i o :=
    hls.dropL _ (by omega) (by omega)
  have hEb64 : (((e.DCA.getD k default).bits.toUInt32).toUInt64).toNat = (e.DCA.getD k default).bits.toNat := by
    simp
  have hEbn : ((e.DCA.getD k default).bits.toUInt32).toNat = (e.DCA.getD k default).bits.toNat := toNat32 _
  have hls1 : LS e (dropL l (e.DCA.getD k default).bits.toUInt32) i o :=
    hls.dropL _ (by omega) (by omega)
  have hsg1 := Sg_dropL (e := e) l (e.DCA.getD k default).bits.toUInt32 i (by omega) (by omega)
  have hlow64 : ∀ x : UInt32, x.toNat < 32 → (l.hold >>> (e.DCA.getD k default).bits.toUInt32.toUInt64).toNat = l.hold.toNat / 2 ^ (e.DCA.getD k default).bits.toNat := by
    intro x _; rw [u64_shr (by omega), hEbn]
  have origin1 : Origin.Inv e (dropL l (e.DCA.getD k default).bits.toUInt32).hold.toNat
      (dropL l (e.DCA.getD k default).bits.toUInt32).bits.toNat i (used + (e.DCA.getD k default).bits.toNat) := by
    have result := drop_preserves_origin e l.hold.toNat l.bits.toNat i used (e.DCA.getD k default).bits.toNat
      origin hEb
    simpa only [dropL_hold l (e.DCA.getD k default).bits.toUInt32 (by rw [hEbn]; omega),
      dropL_bits l (e.DCA.getD k default).bits.toUInt32 (by rw [hEbn]; exact hEb), hEbn] using result
  unfold dodist
  dsimp only
  refine Wp.bindO hld ?_
  refine Wp.bindO (shr64_ok (x := l.hold) (by omega)) ?_
  refine Wp.bindO hld ?_
  generalize e.DCA.getD k default = E at *
  have hsg1' : Sg e (l.hold >>> E.bits.toUInt32.toUInt64).toNat (l.bits - E.bits.toUInt32).toNat i =
      (Sg e l.hold.toNat l.bits.toNat i).drop E.bits.toNat := by
    have := hsg1; rw [hEbn] at this; exact this
  by_cases hb16 : (E.op.toUInt32 &&& 16 != 0) = true
  · rw [ite_eq_left hb16]
    have hb16' : E.op &&& 16 ≠ 0 := by
      rw [mask16] at hb16; simpa using hb16
    have hbase : E.op &&& 16 ≠ 0 ∧ ((E.op &&& 15).toNat ≤ 13) ∧ 1 ≤ E.val.toNat := by
      rcases hcl with h | h | h
      · exact h
      · exact absurd h.1 hb16'
      · exact absurd h.1 hb16'
    refine Wp.bindO hld ?_
    have hv : E.val.toUInt32.toNat = E.val.toNat := by simp
    have hv2 := UInt16.toNat_lt E.val
    have hbn := dropL_bits l E.bits.toUInt32 (by omega)
    have key := (dodistBase_origin_wp hc A msg m
      { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
        here := l.here, op := E.op.toUInt32 &&& 15, len := l.len, dist := E.val.toUInt32, from_ := l.from_,
        broke := l.broke, againL := l.againL, againD := false } i o (used + E.bits.toNat) (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb
      (by rw [mask15]; exact hbase.2.1) (by rw [hv]; exact hbase.2.2) (by rw [hv]; omega) hlen hbroke
      (by rcases hpull with h | h
          · exact Or.inl h
          · refine Or.inr ⟨h.1, ?_⟩
            show 5 ≤ (l.bits - E.bits.toUInt32).toNat
            have hbn' : (l.bits - E.bits.toUInt32).toNat = l.bits.toNat - E.bits.toNat := by
              rw [u32_toNat_sub (by omega), hEbn]
            omega) origin1 (hfr.mono (by omega)))
    unfold dodistBase distCont at key
    dsimp only at key
    refine Wp.mono key ?_
    intro l' h' result
    obtain ⟨i', hin, result⟩ := result
    exact ⟨i', used + E.bits.toNat + (E.op.toUInt32 &&& 15).toNat, hin, result, by omega⟩
  · -- not a base: a link or an invalid code
    have hb16' : E.op &&& 16 = 0 := by
      rw [mask16] at hb16; simpa using hb16
    by_cases hb64 : (E.op.toUInt32 &&& 64 == 0) = true
    · rw [ite_eq_right hb16, ite_eq_left hb64]
      have hb64' : E.op &&& 64 = 0 := by
        rw [mask64] at hb64; simpa using hb64
      have hlink : 1 ≤ E.op.toNat ∧ E.op.toNat ≤ 15 ∧ e.od + E.val.toNat + 2 ^ E.op.toNat ≤ e.DCA.size := by
        rcases hcl with h | h | h
        · exact absurd hb16' h.1
        · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
        · exact absurd hb64' h.2
      refine Wp.bindO hld ?_
      have hdc : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
      have hop32 : E.op.toUInt32.toNat < 32 := by rw [toNat32]; omega
      refine Wp.bindO (x := Ptr.ref e.rd (e.od + E.val.toNat)) ?_ ?_
      · rw [hdc]
        exact Ptr.add_nat_ok (e.heap_cget_DCA A msg m) (Nat.le_trans (Nat.le_add_right _ _) hlink.2.2)
      refine Wp.bindO (shl32_ok hop32) ?_
      have hlow := hold_low64 (x := l.hold >>> E.bits.toUInt32.toUInt64) (k := E.op.toUInt32) hop32
      have hjlt : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat < 2 ^ E.op.toNat := by
        rw [toNat32]; exact Nat.mod_lt _ (Nat.pow_pos (by omega))
      generalize hjd : (l.hold >>> E.bits.toUInt32.toUInt64).toNat % 2 ^ E.op.toUInt32.toNat = j at hlow hjlt
      refine Wp.bindO (x := Ptr.ref e.rd (e.od + E.val.toNat + j)) ?_ ?_
      · rw [hlow]
        exact Ptr.add_nat_ok (h := e.heap A msg m) (r := e.rd) (a := e.DCA) (off := e.od + E.val.toNat)
          (n := j) (e.heap_cget_DCA A msg m) (by have := hlink.2.2; omega)
      refine Wp.pure' ⟨i, used + E.bits.toNat, hls.hin, origin1, by omega⟩
    · rw [ite_eq_right hb16, ite_eq_right hb64]
      obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid distance code" (by decide +kernel)
      refine Wp.bindE hip (Wp.pure' ⟨i, used + E.bits.toNat, hls.hin, origin1, by omega⟩)

end Zlib.Inffast.Proofs
