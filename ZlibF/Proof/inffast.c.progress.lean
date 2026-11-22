import ZlibF.Proof.«inffast.c.final»
import ZlibF.Proof.«inffast.c.loop-progress»

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec

/-- A complete nonterminal fast call strictly consumes output room.
The state and stream are the actual records on the returned heap. -/
def FastProgress {α : Bool} (e : EnvG α) (after : Heap) : Prop :=
  ∃ stream state, e.r.get after = some stream ∧ after.istates e.stid = some state ∧
    (state.mode ≠ TYPE → state.mode ≠ BAD → stream.avail_out.toNat < e.sm0.avail_out.toNat)

theorem fast_finish_progress_wp {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o : Nat) (hl : LS e l i o) (hAsz : A.size = e.A0.size)
    (ho : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (hf : ∀ j, (j < e.o0 ∨ (if α then o else e.o0 + e.sm0.avail_out.toNat) ≤ j) → A[j]? = e.A0[j]?)
    (hclass : (mode = e.s0.mode ∧ msg = e.sm0.msg) ∨ (mode = TYPE ∧ msg = e.sm0.msg) ∨ mode = BAD)
    (hstop : mode ≠ TYPE → mode ≠ BAD → i + 6 > e.i0 + e.sm0.avail_in.toNat ∨
      o + 258 > e.o0 + e.sm0.avail_out.toNat)
    (progress : mode ≠ TYPE → mode ≠ BAD → e.o0 < o)
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
      (e.heap A msg mode) (fun _ after => FastPost e after ∧ FastProgress e after) := by
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
  constructor
  · refine ⟨used, produced, buf, A, msg, mode, bits, hold, hui, hsmall, hup, hAsz, hbits,
      normalized_hold_lt l.hold bits (by omega), ?_, ?_, hclass, ?_⟩
    · rw [← hout]
    · intro j hj
      exact hf j (by rw [← hout] at hj; exact hj)
    · intro hnt hnb
      rcases hstop hnt hnb with hi | ho
      · exact Or.inl (by have := hl.hi0; omega)
      · exact Or.inr (by omega)

  · let stream := { e.sm0 with next_in := .ref e.ib (e.i0 + used), next_out := .ref e.ob o, avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - produced), msg }
    let state := { e.s0 with mode, hold, bits }
    have baseGet : e.r.get (Space.put (Zlib.Inflate.Spec.setI e.h0 e.stid state) e.ob A) = some e.sm0 :=
      e.stream_get_frame A state
    refine ⟨stream, state, put_get _ _ _ _ baseGet, ?_, ?_⟩
    · rw [put_istates, Zlib.Inflate.Proofs.byte_view_put_istates]; exact upd_same _ _ _
    · intro nonterminal nonbad
      have positive : 0 < produced := by
        dsimp only [produced]
        have advancing := progress nonterminal nonbad
        omega
      change (UInt32.ofNat (e.sm0.avail_out.toNat - produced)).toNat < e.sm0.avail_out.toNat
      rw [UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; exact ho32)]
      omega

/-- The actual complete fast decoder retains safety and strict nonterminal output progress. -/
theorem inflate_fast_safe_progress {α : Bool} (e : EnvG α) :
    ∃ after, C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
      FastPost e after ∧ FastProgress e after := by
  have hw : Wp (inflate_fast e.strm e.start) e.h0 (fun _ after => FastPost e after ∧ FastProgress e after) := by
    refine inflate_fast_split_wp e fun l1 skip8 h1 hpost64 => ?_
    obtain ⟨i1, o1, A1, msg1, m1, hl1, _, _, ho1, hAsz1, hh1, hf1, hclass1, hgo1, hstop1,
      hskipAlpha1, horig1⟩ := hpost64
    refine ⟨fun hskip => ?_, fun hskip => ?_⟩
    · dsimp only [fastLoop8]
      obtain ⟨hm1, hmsg1, hbr1, hi1_6, ho1_258⟩ := hgo1 hskip
      obtain ⟨l, h, hr, hpost⟩ :=
        fast_loop_wp_progress (fastCtx_ok e) l1 i1 o1 A1 hl1 hAsz1 hbr1 hi1_6 ho1_258 hf1
      rw [hh1, hmsg1, hm1]
      refine Wp.bindE hr ?_
      dsimp only [fastFinish]
      obtain ⟨i, o, A, msg, mode, hl, ho, hA, hh, hf, hclass, hstop, _, progress⟩ := hpost
      rw [hh]
      exact fast_finish_progress_wp e A msg mode l i o hl hA ho hf hclass hstop
        (fun hnt hnb => Nat.lt_of_le_of_lt hl1.ho0 (progress hnt hnb))
        (e.inputFrame_of_cap_frame hA hf ho hl.hi0)
    · have hα := hskipAlpha1 hskip
      subst hα
      dsimp only [fastFinish]
      have horig1' := horig1 rfl
      dsimp only at horig1'
      rw [cast_eq] at horig1'
      obtain ⟨u1, _, htr1⟩ := horig1'
      rw [hh1]
      have hprog1 : m1 ≠ TYPE → m1 ≠ BAD → e.o0 < o1 := by
        intro hmT hmB
        rcases htr1 with ⟨_, _, _, _, _, _, hbad⟩ | ⟨hpg, htr⟩
        · simp [hskip] at hbad
        · cases hbr1 : l1.broke
          · exact hpg.resolve_right (by intro h; simp [hbr1] at h)
          · rcases htr.output_bounds.2.2.2.1 hbr1 with hT | hB
            · exact False.elim (hmT hT)
            · exact False.elim (hmB hB)
      exact fast_finish_progress_wp e A1 msg1 m1 l1 i1 o1 hl1 hAsz1 ho1 hf1 hclass1
        (fun hmT hmB => by
          rcases hstop1 hskip with ⟨hT, _⟩ | hB | ⟨_, _, hoBig⟩
          · exact False.elim (hmT hT)
          · exact False.elim (hmB hB)
          · exact Or.inr hoBig)
        hprog1 (e.inputFrame_of_cap_frame hAsz1 hf1 ho1 hl1.hi0)
  obtain ⟨⟨⟩, after, hr, hp⟩ := hw
  exact ⟨after, hr, hp⟩

end Zlib.Inffast.Proofs
