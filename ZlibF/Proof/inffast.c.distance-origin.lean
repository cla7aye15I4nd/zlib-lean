import ZlibF.Spec.Functional.Inflate.InflateFastDistanceOrigin
import ZlibF.Proof.«inffast.c.origin»
import ZlibF.Proof.«inffast.c.advance»
import ZlibF.Proof.«inffast.c.distance-origin-dodist»

/-!
# Source origin through actual distance lookup, extra bits and copying

Every error path retains the exact input suffix. Existing execution
results are joined only after identifying the same deterministic run.
-/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec
variable {e : Env} {c : Ctx}

private theorem origin_at_locals {l : L} {i o input used : Nat}
    (locals : LS e l i o) (hin : l.in_ = .ref e.ib input)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat input used) :
    Origin.Inv e l.hold.toNat l.bits.toNat i used := by
  have hi : input = i := (Ptr.ref.inj (hin.symm.trans locals.hin)).2
  simpa only [hi] using origin

private theorem dodistLoop_origin_wp (hc : CtxOK e c) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o kidx used : Nat)
    (hts : DistTableSafe e.DCA e.od e.s0.distbits.toNat) (hk : kidx < 2 ^ e.s0.distbits.toNat)
    (hls : LS e l i o) (hA : e.o0 + e.sm0.avail_out.toNat ≤ A.size)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat) (hAb : A.size < 2 ^ 63)
    (hbroke : l.broke = false) (hlen : 3 ≤ l.len.toNat ∧ l.len.toNat ≤ 258)
    (hhere : l.here = .ref e.rd (e.od + kidx)) (hb15 : 15 ≤ l.bits.toNat)
    (hpull : i + 2 ≤ e.i0 + e.sm0.avail_in.toNat ∨
      (i + 1 ≤ e.i0 + e.sm0.avail_in.toNat ∧ 20 ≤ l.bits.toNat))
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used)
    (hfr : e.InputFrame A i) :
    Wp (cdoWhile (dodist c) (fun l => pure (l.againD, l)) l) (e.heap A msg m) (fun l' _ =>
      ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
  obtain ⟨hksz, hlk, hnl⟩ := distRoot hts kidx hk
  have hcl0 := distClass_of (e := e) _ hlk hnl
  have hEd0 : (e.DCA.getD (e.od + kidx) default).bits.toNat + 0 ≤ 15 := by
    by_cases hl : DistLink (e.DCA.getD (e.od + kidx) default)
    · have := (hlk hl).1; omega
    · have := (hnl hl).1; omega
  obtain ⟨l1, h1, e1, hq1⟩ := dodist_pass hc A msg m l i o 0 (e.od+kidx)
    hls hA ho hAb hbroke hlen hhere hksz (by omega) hEd0 hcl0 (by simpa using hpull) (hfr.mono (by omega))
  obtain ⟨input1, used1, hin1, origin1, mono1⟩ := Wp.at_run
    (dodist_pass_origin_wp hc A msg m l i o 0 (e.od+kidx) used
      hls hA ho hAb hbroke hlen hhere hksz (by omega) hEd0 hcl0 (by simpa using hpull) origin (hfr.mono (by omega))) e1
  obtain ⟨E0, hE0⟩ : ∃ E0, e.DCA.getD (e.od+kidx) default = E0 := ⟨_, rfl⟩
  rw [hE0] at hq1 hlk hnl hcl0 hEd0
  rcases hq1 with ⟨hag,hbr,hh,⟨hl16,hl64⟩,j,hjlt,hjd,hhere1,hls1,hsg1,hb1,hlen1,hout1,hdist1,hagL1⟩ |
    ⟨hNL,hag,hend⟩
  · subst hh
    have origin1' := origin_at_locals hls1 hin1 origin1
    have hlink : DistLink E0 := ⟨hl16,hl64⟩
    have hlk' := hlk hlink
    have hleaf := hlk'.2.2.2.2 j hjlt
    have hk2 : e.od + E0.val.toNat + j < e.DCA.size := by have := hlk'.2.2.2.1; omega
    have hcl1 : DistClass e (e.DCA.getD (e.od + E0.val.toNat + j) default) := by
      rcases hleaf.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hb15' : E0.bits.toNat ≤ 15 := hlk'.1
    obtain ⟨l2,h2,e2,hq2⟩ := dodist_pass hc A msg m l1 i o E0.bits.toNat (e.od+E0.val.toNat+j)
      hls1 hA ho hAb hbr (by rw [hlen1]; exact hlen) hhere1 hk2
      (by have := hleaf.1; omega) (by omega) hcl1 (by
        rcases hpull with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1,by omega⟩) (hfr.mono (by omega))
    obtain ⟨input2,used2,hin2,origin2,mono2⟩ := Wp.at_run
      (dodist_pass_origin_wp hc A msg m l1 i o E0.bits.toNat (e.od+E0.val.toNat+j) used1
        hls1 hA ho hAb hbr (by rw [hlen1]; exact hlen) hhere1 hk2
        (by have := hleaf.1; omega) (by omega) hcl1 (by
          rcases hpull with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h.1,by omega⟩) origin1' (hfr.mono (by omega))) e2
    rcases hq2 with ⟨hag2,_,_,⟨hl16',hl64'⟩,_⟩ | hend2
    · rcases hleaf.2 with h | h
      · exact absurd hl16' h.1
      · exact absurd hl64' h.2
    · have c1 : (fun l : L => (pure (l.againD,l) : M (Bool × L))) l1 (e.heap A msg m) =
          .ok ((true,l1),e.heap A msg m) := by simp [hag]
      have c2 : (fun l : L => (pure (l.againD,l) : M (Bool × L))) l2 h2 =
          .ok ((false,l2),h2) := by simp [hend2.2.1]
      have e1' : dodist c l (e.heap A msg m) = .ok (l1,e.heap A msg m) := e1
      refine Wp.of_eq (cdoWhile_two e1' c1 e2 c2) ?_
      rcases hend2.2.2 with ⟨i',xv,rest,_,_,_,_,locals,_,_⟩ | ⟨i',p,_,_,_,locals,_⟩
      · exact ⟨i',o+l1.len.toNat,used2,locals,origin_at_locals locals hin2 origin2,by omega⟩
      · exact ⟨i',o,used2,locals,origin_at_locals locals hin2 origin2,by omega⟩
  · have c1 : (fun l : L => (pure (l.againD,l) : M (Bool × L))) l1 h1 = .ok ((false,l1),h1) := by simp [hag]
    refine Wp.of_eq (cdoWhile_one e1 c1) ?_
    rcases hend with ⟨i',xv,rest,_,_,_,_,locals,_,_⟩ | ⟨i',p,_,_,_,locals,_⟩
    · exact ⟨i',o+l.len.toNat,used1,locals,origin_at_locals locals hin1 origin1,mono1⟩
    · exact ⟨i',o,used1,locals,origin_at_locals locals hin1 origin1,mono1⟩

/-- Every actual distance sub-block exit preserves its exact source suffix,
including invalid-distance and too-far-back errors. -/
theorem actual_distance_block_preserves_origin : DistanceOrigin.Goal.actual_distance_block_preserves_origin := by
  intro e c bytes msg mode l i o used hc locals size room big notBroke length enough pullRoom origin hfr
  have execution : Wp (dolenDist c l) (e.heap bytes msg mode) (fun l' _ =>
      ∃ i' o' used', LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used') := by
    unfold dolenDist
    have codePtr : c.dcode = .ref e.rd e.od := by rw [hc.dcode]; exact e.hdc
    have rootBound : e.s0.distbits.toNat < 32 := by have := e.hdt.1; omega
    have mask : c.dmask.toUInt64.toNat = 2 ^ e.s0.distbits.toNat - 1 := by
      rw [hc.dmask,UInt32.toNat_toUInt64]
      exact u32_shl1_sub1 rootBound
    have idx := u64_and_mask (x:=l.hold) mask
    have idxBound : l.hold.toNat % 2 ^ e.s0.distbits.toNat < 2 ^ e.s0.distbits.toNat :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    refine Wp.bindO (x:=Ptr.ref e.rd (e.od+l.hold.toNat%2^e.s0.distbits.toNat)) ?_ ?_
    · rw [codePtr,idx]
      exact Ptr.add_nat_ok (e.heap_cget_DCA bytes msg mode) (by have := e.hdt.2.1; omega)
    · exact dodistLoop_origin_wp hc bytes msg mode
        {l with here := .ref e.rd (e.od+l.hold.toNat%2^e.s0.distbits.toNat)} i o _ used
        e.hdt idxBound (LS.congr locals rfl rfl rfl rfl) size room big notBroke length rfl enough pullRoom origin (hfr.mono (by omega))
  obtain ⟨l',after,run,result⟩ := execution
  have original := Wp.at_run (dolenDist_wp hc bytes msg mode l i o e.hdt locals size room big notBroke length enough pullRoom (hfr.mono (by omega))) run
  exact ⟨l',after,run,original,result⟩

end Zlib.Inffast.Proofs
