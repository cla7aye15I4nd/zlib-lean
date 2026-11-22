import ZlibF.Spec.Common.Inflate.InflateFastCallOrigin
import ZlibF.Proof.«inffast.c.body-origin»
import ZlibF.Proof.«inffast.c.origin»
import ZlibF.Proof.«inffast.c.final»
import ZlibF.Spec.Safety.Inflate.FastOrigin

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.CallOrigin

private theorem loop_origin_wp (hc : CtxOK e c) (l : L) (i o : Nat) (A : Array UInt8) (msg : BPtr) (mode : UInt32) (used : Nat)
    (hl : LS e l i o) (hA : A.size = e.A0.size) (hb : l.broke = false)
    (hi : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat)
    (ho : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat)
    (origin : Origin.Inv e l.hold.toNat l.bits.toNat i used) (hfr : e.InputFrame A i) :
    Wp (cdoWhile (inflate_fast_body c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
        else pure (false, l)) l) (e.heap A msg mode)
      (fun l' h' => ∃ i' o' A' msg' mode' used',
        LS e l' i' o' ∧ o' ≤ e.o0 + e.sm0.avail_out.toNat ∧ A'.size = e.A0.size ∧
        h' = e.heap A' msg' mode' ∧
        Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used' ∧
        e.InputFrame A' i') := by
  let Inv : L → Heap → Prop := fun l h => ∃ i o A msg mode cursor,
    LS e l i o ∧ A.size = e.A0.size ∧ h = e.heap A msg mode ∧ l.broke = false ∧
    i + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 258 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    Origin.Inv e l.hold.toNat l.bits.toNat i cursor ∧ used ≤ cursor ∧ e.InputFrame A i
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ l i o, LS e l i o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l i o hl
    simp only [μ, hl.hout]
  refine Wp.cdoWhile Inv μ _ ?_
    ⟨i, o, A, msg, mode, used, hl, hA, rfl, hb, hi, ho, origin, Nat.le_refl _, hfr⟩ ?_
  · intro l h hI
    obtain ⟨i, o, A, msg, mode, cursor, hl, hA, rfl, hb, hi, ho, origin, hused, hfrI⟩ := hI
    have hp : StepPre e c A l i o := ⟨hc, hl, hA, hi, ho, hb, hfrI⟩
    obtain ⟨l1, h1, hr, hpost, j, k, cursor', resultLocals, resultOrigin, hcursor⟩ :=
      actual_body_preserves_origin e c A msg mode l i o cursor hp origin
    obtain ⟨i', o', A', msg', mode', hl', hii, hi6, hoo, ho258, hsz, hh,
      _, hframe, hcont, _⟩ := hpost
    have sameInput : j = i' := by
      have eq := Ptr.ref.inj (resultLocals.hin.symm.trans hl'.hin)
      omega
    have sameOutput : k = o' := by
      have eq := Ptr.ref.inj (resultLocals.hout.symm.trans hl'.hout)
      omega
    subst j k
    have hAsz : A'.size = e.A0.size := hsz.trans hA
    have hoend : o' ≤ e.o0 + e.sm0.avail_out.toNat := by omega
    have hused' : used ≤ cursor' := Nat.le_trans hused hcursor
    have hfr' : e.InputFrame A' i' := hfrI.write hii hl.hi0 hl.ho0 hoend hsz hframe
    refine ⟨l1, h1, hr, ?_⟩
    cases hstop : l1.broke with
    | true =>
      refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', mode', cursor', hl',
        hoend, hAsz, hh, resultOrigin, hused', hfr'⟩
      simp
    | false =>
      obtain ⟨progress, _, _⟩ := hcont hstop
      have hcnd := fast_cond_live hc A' msg' mode' l1 i' o' hl' hAsz hoend hstop
      by_cases hroom : i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧
          o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat
      · refine Or.inr ⟨l1, h1, ?_, ?_, ?_⟩
        · rw [hh]; simpa [hstop, hroom.1, hroom.2] using hcnd
        · exact ⟨i', o', A', msg', mode', cursor', hl', hAsz, hh, hstop,
            hroom.1, hroom.2, resultOrigin, hused', hfr'⟩
        · rw [hμ _ _ _ hl', hμ _ _ _ hl]
          omega
      · refine Or.inl ⟨l1, h1, ?_, i', o', A', msg', mode', cursor', hl',
          hoend, hAsz, hh, resultOrigin, hused', hfr'⟩
        have hcfalse : (decide (i' + 6 ≤ e.i0 + e.sm0.avail_in.toNat) &&
            decide (o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        rw [hh]
        simpa [hstop, hcfalse] using hcnd
  · rw [hμ _ _ _ hl]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    have := hl.ho0
    omega

private theorem finish_origin_wp (e : Env) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (usedBits : Nat) (origin : Origin.Inv e l.hold.toNat l.bits.toNat i usedBits)
    (hfr : e.InputFrame A i) :
    Wp (do
      let len := l.bits >>> 3
      let input ← subn l.in_ len
      let bits := l.bits - (len <<< 3)
      let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
      let ai : Int64 ←
        if ← Ptr.lt input (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5)) then do
          let d ← Ptr.diff (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5)) input
          chk64 (5 + d.toInt)
        else do
          let d ← Ptr.diff input (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5))
          chk64 (5 - d.toInt)
      let ao : Int64 ←
        if ← Ptr.lt l.out (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)) then do
          let d ← Ptr.diff (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)) l.out
          chk64 (257 + d.toInt)
        else do
          let d ← Ptr.diff l.out (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257))
          chk64 (257 - d.toInt)
      let sm ← ldZStream e.strm
      stZStream e.strm { sm with next_in := input, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
      let st ← ldInflateState (some (.tab e.stid))
      stInflateState (some (.tab e.stid)) { st with hold, bits })
      (e.heap A msg mode) (fun _ after => HasOrigin e after) := by
  let buf := l.bits.toNat / 8
  let used := i - e.i0 - buf
  let produced := o - e.o0
  let bits := l.bits - ((l.bits >>> 3) <<< 3)
  let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  have hbuf : buf ≤ i - e.i0 := hl.buffered_le
  have hsmall : buf ≤ 3 := by dsimp only [buf]; have := hl.hb; omega
  have hused : used + buf = i - e.i0 := by dsimp only [used]; omega
  have hui : used + buf ≤ e.sm0.avail_in.toNat := by have := hl.hi0; have := hl.hi1; omega
  have hup : produced ≤ e.sm0.avail_out.toNat := by dsimp only [produced]; have := hl.ho0; omega
  have hio : i - (l.bits >>> 3).toNat = e.i0 + used := by
    rw [bits_whole]
    change i - buf = e.i0 + used
    have := hl.hi0
    omega
  have hout : o = e.o0 + produced := by dsimp only [produced]; have := hl.ho0; omega
  have hbits : bits.toNat < 8 := by dsimp only [bits]; rw [bits_residual _ hl.hb]; omega
  have hinbuf : OkOn (e.heap A msg mode) (subn l.in_ (l.bits >>> 3))
      (.ref e.ib (e.i0 + used)) := by
    rw [hl.hin]
    have hr := subn_ok (h := e.heap A msg mode) (r := e.ib) (a := e.inArr A) (e.heap_bytes_in A msg mode)
      (n := l.bits >>> 3) (off := i) (by rw [bits_whole]; have := hl.hi0; omega)
      (by have := hl.hi1; have := e.hINsz; have := e.inArr_size hfr; omega)
    simpa only [hio] using hr
  refine Wp.bindO hinbuf ?_
  refine Wp.bindO (shl32_ok (x := 1) (n := bits) (by omega)) ?_
  have hu32 : e.sm0.avail_in.toNat - used < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_in; omega
  have ho32 : e.sm0.avail_out.toNat - produced < 2 ^ 32 := by have := UInt32.toNat_lt e.sm0.avail_out; omega
  have hei : e.i0 + e.sm0.avail_in.toNat - 5 + 5 - (e.i0 + used) = e.sm0.avail_in.toNat - used := by
    have := e.hai; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := e.ib) (A := e.inArr A)
    (p := e.i0 + used) (q := e.i0 + e.sm0.avail_in.toNat - 5) (k := 5)
    (e.heap_bytes_in A msg mode) (by have := e.hINsz; have := e.inArr_size hfr; omega)
    (by have := e.hINsz; have := e.inArr_size hfr; omega)
    (by rw [e.inArr_size hfr]; exact e.hINbig) (by have := e.hai; omega) (by decide) (by rw [hei]; exact hu32) ?_
  rw [hei]
  rw [hl.hout]
  have heo : e.o0 + e.sm0.avail_out.toNat - 257 + 257 - o = e.sm0.avail_out.toNat - produced := by
    have := e.hao; omega
  refine ptr_avail_wp (h := e.heap A msg mode) (r := e.ob) (A := A)
    (p := o) (q := e.o0 + e.sm0.avail_out.toNat - 257) (k := 257)
    (e.heap_bytes_ob A msg mode) (by rw [hAsz]; have := e.hAsz; omega) (by rw [hAsz]; have := e.hAsz; omega)
    (by rw [hAsz]; exact e.hAbig) (by have := e.hao; omega) (by decide) (by rw [heo]; exact ho32) ?_
  rw [heo]
  rw [i64_to_u32_eq _ hu32, i64_to_u32_eq _ ho32]
  refine Wp.of_eq (fast_stores_run e A msg mode (.ref e.ib (e.i0 + used)) (.ref e.ob o)
    (UInt32.ofNat (e.sm0.avail_in.toNat - used)) (UInt32.ofNat (e.sm0.avail_out.toNat - produced)) hold bits) ?_
  have rollback := actual_rollback_preserves_origin e A msg mode l i o usedBits hl origin hfr
  have newOrigin : Origin.Inv e hold.toNat bits.toNat (e.i0 + used) usedBits := by
    have sameIndex : i - l.bits.toNat / 8 = e.i0 + used := by simpa only [bits_whole] using hio
    simpa only [sameIndex] using rollback.2.2.1
  let stream : ZStream := { e.sm0 with
    next_in := .ref e.ib (e.i0 + used)
    next_out := .ref e.ob o
    avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used)
    avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - produced)
    msg := msg }
  refine ⟨{ e.s0 with mode, hold, bits }, stream,
    e.i0 + used, usedBits, ?_, ?_, rfl, ?_, newOrigin⟩
  · rw [put_istates, Zlib.Inflate.Proofs.byte_view_put_istates]
    exact upd_same _ _ _
  · exact put_get e.r _ e.sm0 _ (e.stream_get_frame _ _)
  · change (e.i0 + used) + (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat = _
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hu32]
    omega

theorem actual_fast_preserves_origin : CallOrigin.Goal.actual_fast_preserves_origin := by
  intro e
  have hw : Wp (inflate_fast e.strm e.start) e.h0 (fun _ after => HasOrigin e after) := by
    refine inflate_fast_split_wp e fun l1 skip8 h1 hpost64 => ?_
    obtain ⟨i1, o1, A1, msg1, m1, hl1, _, _, ho1, hAsz1, hh1, hf1, _, hgo1, _, _, horig1⟩ := hpost64
    have horig1' := horig1 rfl
    dsimp only at horig1'
    rw [cast_eq] at horig1'
    obtain ⟨u1, origin1, _⟩ := horig1'
    refine ⟨fun hskip => ?_, fun hskip => ?_⟩
    · dsimp only [fastLoop8]
      obtain ⟨hm1, hmsg1, hbr1, hi1_6, ho1_258⟩ := hgo1 hskip
      obtain ⟨l, h, hr, hpost⟩ := loop_origin_wp (fastCtx_ok e) l1 i1 o1 A1 msg1 m1 u1
        hl1 hAsz1 hbr1 hi1_6 ho1_258 origin1
        (e.inputFrame_of_cap_frame hAsz1 hf1 (by omega) hl1.hi0)
      rw [hh1]
      refine Wp.bindE hr ?_
      dsimp only [fastFinish]
      obtain ⟨i, o, A, msg, mode, usedBits, hl, ho, hA, hh, origin, _, hfrEnd⟩ := hpost
      rw [hh]
      exact finish_origin_wp e A msg mode l i o hl hA ho usedBits origin hfrEnd
    · dsimp only [fastFinish]
      rw [hh1]
      exact finish_origin_wp e A1 msg1 m1 l1 i1 o1 hl1 hAsz1 ho1 u1 origin1
        (e.inputFrame_of_cap_frame hAsz1 hf1 ho1 hl1.hi0)
  obtain ⟨⟨⟩, after, hr, hp⟩ := hw
  obtain ⟨safeAfter, safeRun, safePost⟩ := inflate_fast_safe e
  have same : safeAfter = after := by
    have eq := safeRun.symm.trans hr
    cases eq
    rfl
  subst safeAfter
  exact ⟨after, hr, safePost, hp⟩

end Zlib.Inffast.Proofs
