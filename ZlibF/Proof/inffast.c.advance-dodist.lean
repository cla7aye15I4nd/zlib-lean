import ZlibF.Spec.Common.Inflate.InflateFast
import ZlibF.Proof.«inffast.c.dist»
import ZlibF.Proof.«deflate.c.base»

/-! One pass of the block at `dodist:` with exact input advancement, for `inffast.c.advance`. It does
not use the loops of `inffast.c.lp` and `inffast.c.len`, so it builds beside them. -/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

theorem Wp.at_run {α : Type} {m : M α} {h h' : Heap} {a : α}
    {Q : α → Heap → Prop} (hw : Wp m h Q) (hr : m h = .ok (a, h')) : Q a h' := by
  obtain ⟨a1, h1, hr1, hq⟩ := hw
  have he := Except.ok.inj (hr1.symm.trans hr)
  rcases Prod.mk.inj he with ⟨rfl, rfl⟩
  exact hq

variable {α : Bool} {e : EnvG α} {c : Ctx}

theorem dodistBase_tight_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hx : l.op.toNat ≤ 13) (hd1 : 1 ≤ l.dist.toNat) (hd2 : l.dist.toNat ≤ 65536)
    (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258) (hbroke : l.broke = false)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 5 ≤ l.bits.toNat))
    (hfr : e.InputFrame A i) :
    Wp (dodistBase c l) (e.heap A msg m) (fun l' h' =>
      ∃ i' xv rest, i ≤ i' ∧ i' ≤ i + 2 ∧ (5 ≤ l.bits.toNat → i' ≤ i + 1) ∧ readBits l.op.toNat (Sg e l.hold.toNat l.bits.toNat i) = some (xv, rest) ∧
        l'.againD = l.againD ∧
        ((l'.broke = false ∧ LS e l' i' (o + l.len.toNat) ∧ Sg e l'.hold.toNat l'.bits.toNat i' = rest ∧
            h' = e.heap (e.mArr e.bg o (l.dist.toNat + xv) l.len.toNat A) msg m) ∨
         (l'.broke = true ∧ LS e l' i' o ∧ ∃ p, h' = e.heap A p BAD))) := by
  unfold dodistBase
  by_cases h1 : l.bits < l.op
  · rw [ite_eq_left h1]
    have h1' : l.bits.toNat < l.op.toNat := UInt32.lt_iff_toNat_lt.mp h1
    have hiin : i < e.i0 + e.sm0.avail_in.toNat := by omega
    refine Wp.bindO (pull_run e _ l i o hls (by omega) hiin (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
    have hl3 := hls.pullL (by omega) hiin
    have hs3 := Sg_pullL hls (by omega) hiin
    have hb3 := pullL_bits l (e.IN.getD i 0) (.ref e.ib (i + 1)) hls.hb
    by_cases h2 : (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).bits <
        (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).op
    · rw [ite_eq_left h2]
      have h2' : l.bits.toNat + 8 < l.op.toNat := by
        have := UInt32.lt_iff_toNat_lt.mp h2
        simp only [pullL] at this hb3 ⊢
        omega
      have hi2 : i + 1 < e.i0 + e.sm0.avail_in.toNat := by omega
      have hb3' : (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).bits.toNat ≤ 22 := by omega
      refine Wp.bindO (pull_run e _ _ (i + 1) o hl3 hb3' hi2 (e.heap_bytes_in A msg m) (hfr.get (by omega) (by omega))) ?_
      have hl4 := hl3.pullL hb3' hi2
      have hs4 := Sg_pullL hl3 hb3' hi2
      have hb4 := pullL_bits (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))) (e.IN.getD (i + 1) 0)
        (.ref e.ib (i + 1 + 1)) hl3.hb
      refine Wp.mono (distCont_wp hc A msg m _ (i + 1 + 1) o hl4 hA ho hAb (by simp only [pullL]; omega)
        (by simp only [pullL] at hb3 hb4 ⊢; omega) (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
      refine ⟨i + 1 + 1, xv, rest, by omega, by omega, (by intro h; omega), ?_, hagD, ?_⟩
      · simp only [pullL] at hr hs4 hs3 ⊢
        rw [hs4, hs3] at hr
        exact hr
      · simp only [pullL] at hres ⊢
        exact Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres
    · rw [ite_eq_right h2]
      have h2n : (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).op.toNat ≤
          (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).bits.toNat := by
        have : ¬ ((pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).bits.toNat <
            (pullL l (e.IN.getD i 0) (.ref e.ib (i + 1))).op.toNat) :=
          fun h => h2 (UInt32.lt_iff_toNat_lt.mpr h)
        omega
      refine Wp.mono (distCont_wp hc A msg m _ (i + 1) o hl3 hA ho hAb (by simp only [pullL]; omega)
        h2n (by simp only [pullL]; omega) (by simp only [pullL]; omega)
        (by simp only [pullL]; omega) (by simp only [pullL]; omega)) ?_
      intro l' h' hq
      obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
      refine ⟨i + 1, xv, rest, by omega, by omega, (by intro h; omega), ?_, hagD, ?_⟩
      · simp only [pullL] at hr hs3 ⊢
        rw [hs3] at hr
        exact hr
      · simp only [pullL] at hres ⊢
        exact Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres
  · rw [ite_eq_right h1]
    have h1' : l.op.toNat ≤ l.bits.toNat := by
      have : ¬ (l.bits.toNat < l.op.toNat) := fun h => h1 (UInt32.lt_iff_toNat_lt.mpr h)
      omega
    refine Wp.mono (distCont_wp hc A msg m l i o hls hA ho hAb hx h1' hd1 hd2 hlen hbroke) ?_
    intro l' h' hq
    obtain ⟨xv, rest, hr, hin, hagD, hres⟩ := hq
    exact ⟨i, xv, rest, by omega, by omega, (by intro h; omega), hr, hagD, Or.imp id (fun h => ⟨h.1, h.2.1, h.2.2.2⟩) hres⟩


set_option maxHeartbeats 1000000 in
/-- One pass of the block at `dodist:`. Either it follows a link (`againD`), or it ends the distance block. -/
theorem dodist_advance_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32) (l : L) (i o d k : Nat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size) (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (hAb : A.size < 2 ^ 63) (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd k) (hk : k < e.DCA.size)
    (hEb : (e.DCA.getD k default).bits.toNat ≤ l.bits.toNat)
    (hEd : (e.DCA.getD k default).bits.toNat + d ≤ 15)
    (hcl : DistClass e (e.DCA.getD k default))
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨ (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat + d))
    (hfr : e.InputFrame A i) :
    Wp (dodist c l) (e.heap A msg m) (fun l' _ =>
      ∃ i', i ≤ i' ∧ i' ≤ i + 2 ∧ (20 ≤ l.bits.toNat + d → i' ≤ i + 1) ∧
        l'.in_ = .ref e.ib i') := by
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
    have key := (dodistBase_tight_wp hc A msg m
      { in_ := l.in_, out := l.out, hold := l.hold >>> E.bits.toUInt32.toUInt64, bits := l.bits - E.bits.toUInt32,
        here := l.here, op := E.op.toUInt32 &&& 15, len := l.len, dist := E.val.toUInt32, from_ := l.from_,
        broke := l.broke, againL := l.againL, againD := false } i o (LS.congr hls1 rfl rfl rfl rfl) hA ho hAb
      (by rw [mask15]; exact hbase.2.1) (by rw [hv]; exact hbase.2.2) (by rw [hv]; omega) hlen hbroke
      (by rcases hpull with h | h
          · exact Or.inl h
          · refine Or.inr ⟨h.1, ?_⟩
            show 5 ≤ (l.bits - E.bits.toUInt32).toNat
            have hbn' : (l.bits - E.bits.toUInt32).toNat = l.bits.toNat - E.bits.toNat := by
              rw [u32_toNat_sub (by omega), hEbn]
            omega) (hfr.mono (by omega)))
    unfold dodistBase distCont at key
    dsimp only at key
    refine Wp.mono key ?_
    intro l' h' hq
    obtain ⟨i', xv, rest, hi1, hi2, htight, _, _, hres⟩ := hq
    have hbound : 20 ≤ l.bits.toNat + d → i' ≤ i + 1 := by
      intro hh
      apply htight
      show 5 ≤ (l.bits - E.bits.toUInt32).toNat
      rw [u32_toNat_sub (by omega), hEbn]
      omega
    rcases hres with ⟨_, hls', _, _⟩ | ⟨_, hls', _⟩
    · exact ⟨i', hi1, hi2, hbound, hls'.hin⟩
    · exact ⟨i', hi1, hi2, hbound, hls'.hin⟩
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
      refine Wp.pure' ⟨i, by omega, by omega, by omega, hls.hin⟩
    · rw [ite_eq_right hb16, ite_eq_right hb64]
      obtain ⟨ip, hip⟩ := badData_run hc A msg m "invalid distance code" (by decide +kernel)
      refine Wp.bindE hip ?_
      exact Wp.pure' ⟨i, by omega, by omega, by omega, hls.hin⟩

end Zlib.Inffast.Proofs
