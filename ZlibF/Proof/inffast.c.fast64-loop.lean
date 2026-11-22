import ZlibF.Proof.«inffast.c.fast64-body»
import ZlibF.Proof.«inffast.c.loop»

/-!
# inffast.c: `back` check, 64-bit fast loop, and byte-unpack handoff

Proves:
- `back_check_ok`: `back == α` for `EnvG α` without UB.
- `Fast64Trace`: non-empty chain of `Body8Trace` iterations preserving bounds and strict bit progress.
- `fast64_loop_wp`: `Wp` for `cdoWhile (inflate_fast_body8 c) ...` on `Env` (`α = false`).
- `fast64_phase_wp`: unified `Wp` for lines 637–657 (`if !back && avail_in >= 16 && avail_out >= 275 ...`)
  on `EnvG α`, producing `skip8` and exact 8-bit loop / `leave:` preconditions.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Spec.Origin
open ZlibF.Spec

set_option autoImplicit false

private theorem if_t {α : Type _} {c : Prop} [Decidable c] (h : c) {t e : α} : (if c then t else e) = t := by
  simp only [h, ↓reduceIte]

private theorem if_f {α : Type _} {c : Prop} [Decidable c] (h : ¬ c) {t e : α} : (if c then t else e) = e := by
  simp only [h, ↓reduceIte]

theorem ptr_le_ok {h : Heap} {r : BRef} {a : Array UInt8} {o1 o2 : Nat}
    (hg : Space.get h r = some a) (h1 : o1 ≤ a.size) (h2 : o2 ≤ a.size) :
    OkOn h (Ptr.le (.ref r o1) (.ref r o2)) (decide (o1 ≤ o2)) := by
  unfold OkOn Ptr.le
  rw [bind_ok (Ptr.lt_ok hg h2 h1)]
  have hdec : (!decide (o2 < o1)) = decide (o1 ≤ o2) := by
    by_cases h : o1 ≤ o2
    · simp [h, show ¬ (o2 < o1) by omega]
    · simp [h, show o2 < o1 by omega]
  simp [hdec]

/-- Evaluating the `back` window-overlap check at `inflate_fast` entry never faults and equals `α`. -/
theorem back_check_ok {α : Bool} (e : EnvG α) :
    OkOn e.h0
      (if e.s0.window != .null then do
        let outEnd ← e.sm0.next_out.add (e.sm0.avail_out.toNat : Int)
        let winEnd ← e.s0.window.add (e.s0.wsize.toNat : Int)
        pure (outEnd == winEnd)
      else pure false) α := by
  unfold OkOn
  cases α
  · by_cases hnull : e.s0.window = .null
    · simp [hnull]
    · obtain ⟨hwptr, hwb, hWb, hWsz⟩ := e.hwinLive hnull
      have hne : (e.s0.window != .null) = true := by rw [hwptr]; rfl
      have hAddOut := Ptr.add_nat_ok e.hA0 e.hAsz
      have hAddWin : OkOn e.h0 (Ptr.add e.s0.window (e.s0.wsize.toNat : Int))
          (.ref (BRef.blk e.wb) (e.woff + e.s0.wsize.toNat)) := by
        rw [hwptr]
        exact Ptr.add_nat_ok (r := BRef.blk e.wb) hWb hWsz
      have hcmp : (Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat) ==
          Ptr.ref (BRef.blk e.wb) (e.woff + e.s0.wsize.toNat)) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact hwb (Ptr.ref.inj (beq_iff_eq.mp h)).1.symm
      rw [if_t hne, e.hnout, bind_ok hAddOut, bind_ok hAddWin, hcmp]
      rfl
  · have hnull : e.s0.window ≠ .null := e.halias_win rfl
    obtain ⟨hwptr, ⟨hwb, _, hweq⟩, hWb, hWsz⟩ := e.hwinLive hnull
    have hne : (e.s0.window != .null) = true := by rw [hwptr]; rfl
    have hAddOut := Ptr.add_nat_ok e.hA0 e.hAsz
    have hAddWin : OkOn e.h0 (Ptr.add e.s0.window (e.s0.wsize.toNat : Int))
        (.ref (BRef.blk e.wb) (e.woff + e.s0.wsize.toNat)) := by
      rw [hwptr]
      exact Ptr.add_nat_ok (r := BRef.blk e.wb) hWb hWsz
    have hptreq : Ptr.ref (BRef.blk e.wb) (e.woff + e.s0.wsize.toNat) =
        Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat) := by
      rw [hwb, hweq]
    have hcmp : (Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat) ==
        Ptr.ref (BRef.blk e.wb) (e.woff + e.s0.wsize.toNat)) = true := by
      rw [hptreq]
      exact beq_self_eq_true _
    rw [if_t hne, e.hnout, bind_ok hAddOut, bind_ok hAddWin, hcmp]
    rfl

/-! ### Multi-iteration 64-bit trace -/

/-- A non-empty sequence of `inflate_fast_body8` iteration traces (`Body8Trace`). -/
inductive Fast64Trace (e : Env) (m : UInt32) :
    Array UInt8 → Nat → Nat → Array UInt8 → Nat → Nat → Bool → UInt32 → Prop
  | single {A o u A' o' u' broke m'} :
      Body8Trace e m A o u A' o' u' broke m' →
      Fast64Trace e m A o u A' o' u' broke m'
  | cons {A o u A1 o1 u1 A' o' u' broke m'} :
      Body8Trace e m A o u A1 o1 u1 false m →
      Fast64Trace e m A1 o1 u1 A' o' u' broke m' →
      Fast64Trace e m A o u A' o' u' broke m'

private theorem Fast64Trace.append_aux {e : Env} {m : UInt32} {A0 A1 A2 : Array UInt8}
    {o0 u0 o1 u1 o2 u2 : Nat} {br1 br2 : Bool} {m1 m2 : UInt32}
    (t1 : Fast64Trace e m A0 o0 u0 A1 o1 u1 br1 m1)
    (hnb : br1 = false) (hm1 : m1 = m)
    (b2 : Body8Trace e m A1 o1 u1 A2 o2 u2 br2 m2) :
    Fast64Trace e m A0 o0 u0 A2 o2 u2 br2 m2 := by
  induction t1 with
  | single b1 => subst hnb hm1; exact Fast64Trace.cons b1 (Fast64Trace.single b2)
  | cons b1 _ ih => exact Fast64Trace.cons b1 (ih hnb hm1 b2)

theorem Fast64Trace.append {e : Env} {m : UInt32} {A0 A1 A2 : Array UInt8}
    {o0 u0 o1 u1 o2 u2 : Nat} {br2 : Bool} {m2 : UInt32}
    (t1 : Fast64Trace e m A0 o0 u0 A1 o1 u1 false m)
    (b2 : Body8Trace e m A1 o1 u1 A2 o2 u2 br2 m2) :
    Fast64Trace e m A0 o0 u0 A2 o2 u2 br2 m2 :=
  Fast64Trace.append_aux t1 rfl rfl b2

theorem Fast64Trace.output_bounds {e : Env} {m : UInt32} {A A' : Array UInt8}
    {o u o' u' : Nat} {broke : Bool} {m' : UInt32}
    (tr : Fast64Trace e m A o u A' o' u' broke m') :
    A'.size = A.size ∧ o ≤ o' ∧
    (broke = false → o < o' ∧ m' = m) ∧
    (broke = true → m' = TYPE ∨ m' = BAD) ∧
    u ≤ u' := by
  induction tr with
  | single b => exact b.output_bounds
  | cons b _ ih =>
    obtain ⟨hsz1, ho1, hok1, _, hu1⟩ := b.output_bounds
    obtain ⟨hsz2, ho2, hok2, hbr2, hu2⟩ := ih
    refine ⟨hsz2.trans hsz1, Nat.le_trans ho1 ho2, ?_, hbr2, Nat.le_trans hu1 hu2⟩
    intro hnb
    have hk1 := (hok1 rfl).1
    have hk2 := hok2 hnb
    exact ⟨Nat.lt_trans hk1 hk2.1, hk2.2⟩

theorem Fast64Trace.pos {e : Env} {m : UInt32} {A A' : Array UInt8}
    {o u o' u' : Nat} {broke : Bool} {m' : UInt32}
    (tr : Fast64Trace e m A o u A' o' u' broke m')
    (hpos : LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat) (hnb : broke = false) :
    u < u' := by
  induction tr with
  | single b => exact b.pos hpos hnb
  | cons b _ ih =>
    have hlt := ih hnb
    have hle := b.output_bounds.2.2.2.2
    omega

/-! ### Condition and weakest precondition of the 64-bit loop -/

private theorem fast64_cond_live (e : Env) (A : Array UInt8) (msg : BPtr) (m : UInt32)
    (l : L) (i o : Nat) (hIn : l.in_ = .ref e.ib i) (hOut : l.out = .ref e.ob o)
    (hA : A.size = e.A0.size) (hb : l.broke = false)
    (_hi0 : e.i0 ≤ i) (hi1 : i ≤ e.i0 + e.sm0.avail_in.toNat)
    (_ho0 : e.o0 ≤ o) (ho1 : o ≤ e.o0 + e.sm0.avail_out.toNat)
    (hi16_0 : 16 ≤ e.sm0.avail_in.toNat) (ho275_0 : 275 ≤ e.sm0.avail_out.toNat) :
    (do
      if l.broke then pure (false, l)
      else if ← Ptr.le l.in_ (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 16)) then
        pure (← Ptr.le l.out (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 275)), l)
      else pure (false, l)) (e.heap A msg m) =
    .ok ((decide (i + 16 ≤ e.i0 + e.sm0.avail_in.toNat) &&
      decide (o + 275 ≤ e.o0 + e.sm0.avail_out.toNat), l), e.heap A msg m) := by
  have hiSz := e.inArr_size_of hA
  have hINsz := e.hINsz
  have hAsz := e.hAsz
  have hleIn : OkOn (e.heap A msg m) (Ptr.le l.in_ (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 16)))
      (decide (i ≤ e.i0 + e.sm0.avail_in.toNat - 16)) := by
    rw [hIn]
    exact ptr_le_ok (e.heap_bytes_in A msg m) (by omega) (by omega)
  have hleOut : OkOn (e.heap A msg m) (Ptr.le l.out (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 275)))
      (decide (o ≤ e.o0 + e.sm0.avail_out.toNat - 275)) := by
    rw [hOut]
    exact ptr_le_ok (e.heap_bytes_ob A msg m) (by rw [hA]; omega) (by rw [hA]; omega)
  have hei : decide (i ≤ e.i0 + e.sm0.avail_in.toNat - 16) =
      decide (i + 16 ≤ e.i0 + e.sm0.avail_in.toNat) := by
    simp only [decide_eq_decide]; omega
  have heo : decide (o ≤ e.o0 + e.sm0.avail_out.toNat - 275) =
      decide (o + 275 ≤ e.o0 + e.sm0.avail_out.toNat) := by
    simp only [decide_eq_decide]; omega
  simp only [hb, Bool.false_eq_true, ite_false]
  rw [bind_ok hleIn]
  by_cases hi' : i ≤ e.i0 + e.sm0.avail_in.toNat - 16
  · simp only [hi', decide_true, ite_true]
    rw [bind_ok hleOut, ← hei, ← heo]
    simp [hi']
  · simp only [hi', decide_false, Bool.false_eq_true, ite_false]
    rw [← hei]
    simp [hi']

theorem fast64_loop_wp {e : Env} {c : Ctx} (hc : CtxOK e c) (l0 : L)
    (hIn0 : l0.in_ = .ref e.ib e.i0) (hOut0 : l0.out = .ref e.ob e.o0)
    (hHold0 : l0.hold = e.s0.hold) (hBits0 : l0.bits = e.s0.bits) (hBr0 : l0.broke = false)
    (hi16 : 16 ≤ e.sm0.avail_in.toNat) (ho275 : 275 ≤ e.sm0.avail_out.toNat) :
    Wp (cdoWhile (inflate_fast_body8 c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.le l.in_ (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 16)) then
          pure (← Ptr.le l.out (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 275)), l)
        else pure (false, l)) l0) (e.heap e.A0 e.sm0.msg e.s0.mode) (fun l' h' =>
      ∃ i' u' A' o' valid' m' msg',
        Inv64 e l'.hold l'.bits i' u' valid' ∧ 8 ≤ l'.bits.toNat ∧ l'.bits.toNat ≤ 63 ∧
        l'.in_ = .ref e.ib i' ∧ e.i0 ≤ i' ∧ i' ≤ e.i0 + e.sm0.avail_in.toNat - 5 ∧
        l'.out = .ref e.ob o' ∧ e.o0 ≤ o' ∧ o' ≤ e.o0 + e.sm0.avail_out.toNat - 15 ∧
        h' = e.heap A' msg' m' ∧ A'.size = e.A0.size ∧
        (∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A'[j]? = e.A0[j]?) ∧
        Fast64Trace e e.s0.mode e.A0 e.o0 0 A' o' u' l'.broke m' ∧
        ((l'.broke = false ∧ m' = e.s0.mode ∧ msg' = e.sm0.msg ∧
            (i' + 16 > e.i0 + e.sm0.avail_in.toNat ∨ o' + 275 > e.o0 + e.sm0.avail_out.toNat)) ∨
         (l'.broke = true ∧ ((m' = TYPE ∧ msg' = e.sm0.msg) ∨ m' = BAD)))) := by
  let Inv : L → Heap → Prop := fun l h => ∃ i o u valid A,
    Inv64 e l.hold l.bits i u valid ∧ l.bits.toNat ≤ 63 ∧
    l.in_ = .ref e.ib i ∧ l.out = .ref e.ob o ∧ l.broke = false ∧
    i + 16 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o + 275 ≤ e.o0 + e.sm0.avail_out.toNat ∧
    A.size = e.A0.size ∧ e.o0 ≤ o ∧ e.bg ≤ o ∧
    (∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A[j]? = e.A0[j]?) ∧
    h = e.heap A e.sm0.msg e.s0.mode ∧
    ((o = e.o0 ∧ u = 0 ∧ A = e.A0) ∨
      Fast64Trace e e.s0.mode e.A0 e.o0 0 A o u false e.s0.mode)
  let μ : L → Nat := fun l => match l.out with
    | .null => 0
    | .ref _ k => e.o0 + e.sm0.avail_out.toNat - k
  have hμ : ∀ (l : L) (o : Nat), l.out = .ref e.ob o → μ l = e.o0 + e.sm0.avail_out.toNat - o := by
    intro l o ho
    simp only [μ, ho]
  have hInv0 : Inv l0 (e.heap e.A0 e.sm0.msg e.s0.mode) := by
    refine ⟨e.i0, e.o0, 0, e.s0.bits.toNat, e.A0, ?_, ?_, hIn0, hOut0, hBr0,
      by omega, by omega, rfl, Nat.le_refl _, ?_, fun _ _ => rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · rw [hHold0, hBits0]; exact Inv64.init e
    · rw [hBits0]; have := e.hbits; omega
    · have : e.bg = e.o0 - (e.start.toNat - e.sm0.avail_out.toNat) := rfl; omega
  refine Wp.cdoWhile Inv μ _ ?_ hInv0 ?_
  · intro l h hI
    obtain ⟨i, o, u, valid, A, inv, hb63, hlIn, hlOut, hbr, hi16', ho275', hAsz, ho0, hbgo,
      hAout, rfl, htr⟩ := hI
    have hbody := inflate_fast_body8_wp hc A e.sm0.msg e.s0.mode l i o u valid inv
      hlIn hlOut hb63 hi16' ho275' hAsz ho0 hbgo hAout hbr
    obtain ⟨l1, h1, hr1, i', u', A', o', valid', m', msg', inv', hb8', hb63', hin', hiLo, hiHi,
      hout', hoLo, hoHi, hh', hAsz', hOut', hmsgBr, hmsgTy, hBtr⟩ := hbody
    have hA'sz : A'.size = e.A0.size := hAsz'.trans hAsz
    have hA'out : ∀ j, (j < e.o0 ∨ e.o0 + e.sm0.avail_out.toNat ≤ j) → A'[j]? = e.A0[j]? := by
      intro j hj
      rw [hOut' j (by omega)]
      exact hAout j hj
    have hi'lo : e.i0 ≤ i' := by have := inv.inputLower; omega
    have hi'ub : i' ≤ e.i0 + e.sm0.avail_in.toNat - 5 := by omega
    have ho'lo : e.o0 ≤ o' := by omega
    have ho'ub : o' ≤ e.o0 + e.sm0.avail_out.toNat - 15 := by omega
    have ⟨hboSz, hboLe, hboOk, hboBr, hboU⟩ := hBtr.output_bounds
    have htr' : Fast64Trace e e.s0.mode e.A0 e.o0 0 A' o' u' l1.broke m' := by
      rcases htr with ⟨rfl, rfl, rfl⟩ | t0
      · exact Fast64Trace.single hBtr
      · exact t0.append hBtr
    refine ⟨l1, h1, hr1, ?_⟩
    cases hstop : l1.broke with
    | true =>
      have hbrClass := hboBr hstop
      refine Or.inl ⟨l1, h1, ?_, i', u', A', o', valid', m', msg', inv', hb8', hb63', hin',
        hi'lo, hi'ub, hout', ho'lo, ho'ub, hh', hA'sz, hA'out, htr', Or.inr ⟨hstop, ?_⟩⟩
      · rw [hh']; simp
      · rcases hbrClass with rfl | rfl
        · exact Or.inl ⟨rfl, hmsgTy rfl⟩
        · exact Or.inr rfl
    | false =>
      have hnb := hboOk hstop
      have hm' : m' = e.s0.mode := hnb.2
      have hmsg' : msg' = e.sm0.msg := hmsgBr hstop
      have hcnd := fast64_cond_live e A' msg' m' l1 i' o' hin' hout' hA'sz hstop
        hi'lo (by omega) ho'lo (by omega) hi16 ho275
      by_cases hroom : i' + 16 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o' + 275 ≤ e.o0 + e.sm0.avail_out.toNat
      · refine Or.inr ⟨l1, h1, ?_, ?_, ?_⟩
        · rw [hh']; simpa [hstop, hroom.1, hroom.2] using hcnd
        · have htrF : Fast64Trace e e.s0.mode e.A0 e.o0 0 A' o' u' false e.s0.mode := by
            rw [hstop, hm'] at htr'; exact htr'
          exact ⟨i', o', u', valid', A', inv', hb63', hin', hout', hstop, hroom.1, hroom.2,
            hA'sz, ho'lo, by omega, hA'out, by rw [hh', hm', hmsg'], Or.inr htrF⟩
        · rw [hμ l1 o' hout', hμ l o hlOut]
          omega
      · refine Or.inl ⟨l1, h1, ?_, i', u', A', o', valid', m', msg', inv', hb8', hb63', hin',
          hi'lo, hi'ub, hout', ho'lo, ho'ub, hh', hA'sz, hA'out, htr', Or.inl ⟨hstop, hm', hmsg', ?_⟩⟩
        · have hcfalse : (decide (i' + 16 ≤ e.i0 + e.sm0.avail_in.toNat) &&
              decide (o' + 275 ≤ e.o0 + e.sm0.avail_out.toNat)) = false := by
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
            omega
          rw [hh']
          simpa [hstop, hcfalse] using hcnd
        · omega
  · rw [hμ l0 e.o0 hOut0]
    apply lt_fuel_of
    have := UInt32.toNat_lt e.sm0.avail_out
    omega

/-! ### Complete 64-bit phase (`if !back && avail_in >= 16 && avail_out >= 275 ...`) -/

/-- The postcondition established by lines 637–657 of `inflate_fast` on `EnvG α`,
delivering valid normalized 8-bit state (`bits < 8`) and `skip8` with exact 8-bit loop
entry preconditions when `skip8 = false`. -/
def Fast64PhasePost {α : Bool} (e : EnvG α) (l1 : L) (skip8 : Bool) (h1 : Heap) : Prop :=
  ∃ i1 o1 A1 msg1 m1,
    LS e l1 i1 o1 ∧ l1.bits.toNat < 8 ∧ l1.hold.toNat < 2 ^ l1.bits.toNat ∧
    o1 ≤ e.o0 + e.sm0.avail_out.toNat ∧ A1.size = e.A0.size ∧
    h1 = e.heap A1 msg1 m1 ∧
    (∀ j, (j < e.o0 ∨ (if α then o1 else e.o0 + e.sm0.avail_out.toNat) ≤ j) → A1[j]? = e.A0[j]?) ∧
    ((m1 = e.s0.mode ∧ msg1 = e.sm0.msg) ∨ (m1 = TYPE ∧ msg1 = e.sm0.msg) ∨ m1 = BAD) ∧
    (skip8 = false →
      m1 = e.s0.mode ∧ msg1 = e.sm0.msg ∧ l1.broke = false ∧
      i1 + 6 ≤ e.i0 + e.sm0.avail_in.toNat ∧ o1 + 258 ≤ e.o0 + e.sm0.avail_out.toNat) ∧
    (skip8 = true →
      (m1 = TYPE ∧ msg1 = e.sm0.msg) ∨ m1 = BAD ∨
      (m1 = e.s0.mode ∧ msg1 = e.sm0.msg ∧ o1 + 258 > e.o0 + e.sm0.avail_out.toNat)) ∧
    (skip8 = true → α = false) ∧
    (∀ hα : α = false,
      let e0 : Env := cast (congrArg EnvG hα) e
      ∃ u1, Origin.Inv e0 l1.hold.toNat l1.bits.toNat i1 u1 ∧
        ((u1 = 0 ∧ i1 = e0.i0 ∧ o1 = e0.o0 ∧ A1 = e0.A0 ∧
            m1 = e0.s0.mode ∧ msg1 = e0.sm0.msg ∧ skip8 = false) ∨
         (e0.o0 < o1 ∨ l1.broke = true) ∧
           Fast64Trace e0 e0.s0.mode e0.A0 e0.o0 0 A1 o1 u1 l1.broke m1))

theorem fast64_phase_wp {α : Bool} {e : EnvG α} {c : Ctx} (hc : CtxOK e c) (l0 : L)
    (hIn0 : l0.in_ = .ref e.ib e.i0) (hOut0 : l0.out = .ref e.ob e.o0)
    (hHold0 : l0.hold = e.s0.hold) (hBits0 : l0.bits = e.s0.bits) (hBr0 : l0.broke = false)
    (back : Bool) (hback : back = α) :
    Wp (if !back && e.sm0.avail_in >= 16 && e.sm0.avail_out >= 2 + 258 + 15 then do
      let last8 ← Ptr.add l0.in_ (e.sm0.avail_in - 16).toNat
      let end8 ← Ptr.add l0.out (e.sm0.avail_out - (2 + 258 + 15)).toNat
      let l ← cdoWhile (inflate_fast_body8 c)
        (fun l => do
          if l.broke then pure (false, l)
          else if ← Ptr.le l.in_ last8 then pure (← Ptr.le l.out end8, l)
          else pure (false, l)) l0
      let len := l.bits >>> 3
      let in_ ← subn l.in_ len
      let bits := l.bits - (len <<< 3)
      let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
      let l := { l with in_, bits, hold, len }
      let st ← ldInflateState c.state
      let skip8 ←
        if st.mode != LEN then pure true
        else pure !(← Ptr.lt l.out c.end_)
      pure (l, skip8)
    else
      pure (l0, false)) (e.heap e.A0 e.sm0.msg e.s0.mode)
      (fun res h1 => Fast64PhasePost e res.1 res.2 h1) := by
  have hno : Fast64PhasePost e l0 false (e.heap e.A0 e.sm0.msg e.s0.mode) := by
    refine ⟨e.i0, e.o0, e.A0, e.sm0.msg, e.s0.mode, ?_, ?_, ?_, ?_, rfl, rfl,
      (fun _ _ => rfl), Or.inl ⟨rfl, rfl⟩, ?_, (fun h => by cases h), (fun h => by cases h), ?_⟩
    · refine ⟨hIn0, hOut0, Nat.le_refl _, ?_, Nat.le_refl _, ?_, ?_, ?_⟩
      · have := e.hai; omega
      · rw [hBits0]; change e.s0.bits.toNat ≤ 30; have := e.hbits; omega
      · rw [hHold0, hBits0]; exact e.hhold
      · rw [hBits0]; exact Nat.le_refl _
    · rw [hBits0]; exact e.hbits
    · rw [hHold0, hBits0]; exact e.hhold
    · have := e.hao; omega
    · intro _
      refine ⟨rfl, rfl, hBr0, ?_, ?_⟩
      · have := e.hai; omega
      · have := e.hao; omega
    · intro hα
      subst hα
      dsimp only
      rw [cast_eq]
      refine ⟨0, ⟨Nat.le_refl _, by have := e.hai; omega, ?_, by rw [hBits0]; simp, ?_⟩,
        Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      · rw [hHold0, hBits0]; exact e.hhold
      · rw [hHold0, hBits0]; unfold Sg initial; rfl
  by_cases hcond : (!back && e.sm0.avail_in >= 16 && e.sm0.avail_out >= 2 + 258 + 15) = true
  · have hbF : (!back) = true := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hcond).1).1
    have hbf : back = false := by cases back <;> simp_all
    have hα : α = false := hback.symm.trans hbf
    subst hα
    have h16 : 16 ≤ e.sm0.avail_in.toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact UInt32.le_iff_toNat_le.mp hcond.1.2
    have h275 : 275 ≤ e.sm0.avail_out.toNat := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact UInt32.le_iff_toNat_le.mp hcond.2
    have hsub16 : (e.sm0.avail_in - 16).toNat = e.sm0.avail_in.toNat - 16 := by
      rw [u32_toNat_sub (by change 16 ≤ e.sm0.avail_in.toNat; exact h16)]; rfl
    have hsub275 : (e.sm0.avail_out - (2 + 258 + 15)).toNat = e.sm0.avail_out.toNat - 275 := by
      have h275u : ((2 + 258 + 15 : UInt32).toNat) = 275 := by decide
      rw [u32_toNat_sub (by rw [h275u]; exact h275), h275u]
    have hInSz0 := e.inArr_size_of (A := e.A0) rfl
    have hlast8 : OkOn (e.heap e.A0 e.sm0.msg e.s0.mode)
        (Ptr.add l0.in_ (e.sm0.avail_in - 16).toNat) (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 16)) := by
      rw [hIn0, hsub16]
      have hr := Ptr.add_nat_ok (e.heap_bytes_in e.A0 e.sm0.msg e.s0.mode)
        (off := e.i0) (n := e.sm0.avail_in.toNat - 16) (by have := e.hINsz; omega)
      have hoff : e.i0 + (e.sm0.avail_in.toNat - 16) = e.i0 + e.sm0.avail_in.toNat - 16 := by omega
      simpa [hoff] using hr
    have hend8 : OkOn (e.heap e.A0 e.sm0.msg e.s0.mode)
        (Ptr.add l0.out (e.sm0.avail_out - (2 + 258 + 15)).toNat)
        (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 275)) := by
      rw [hOut0, hsub275]
      have hr := Ptr.add_nat_ok (e.heap_bytes_ob e.A0 e.sm0.msg e.s0.mode)
        (off := e.o0) (n := e.sm0.avail_out.toNat - 275) (by have := e.hAsz; omega)
      have hoff : e.o0 + (e.sm0.avail_out.toNat - 275) = e.o0 + e.sm0.avail_out.toNat - 275 := by omega
      simpa [hoff] using hr
    have hloop := fast64_loop_wp hc l0 hIn0 hOut0 hHold0 hBits0 hBr0 h16 h275
    obtain ⟨l', h', hrL, i', u', A', o', valid', m', msg', inv', hb8', hb63', hin',
      hi'lo, hi'ub, hout', ho'lo, ho'ub, rfl, hAsz', hOut', htr', hExit⟩ := hloop
    have hfr' : e.InputFrame A' i' :=
      e.inputFrame_of_cap_frame (o := o') hAsz' hOut' (by omega) inv'.inputLower
    obtain ⟨resU, hU, hrU, hUeq, _, hiUeq, _, hbitsU, hbits8, hholdU, _, _, hlsU, horigU⟩ :=
      unpack64_wp A' msg' m' l'.in_ l'.out l'.hold l'.bits i' o' u' valid' inv' hin' hout' hb63' ho'lo hfr'
    let bitsU := l'.bits - ((l'.bits >>> 3) <<< 3)
    let holdU := l'.hold &&& (((1 : UInt32) <<< bitsU) - 1).toUInt64
    let iU := i' - l'.bits.toNat / 8
    let lFinal : L := { l' with in_ := .ref e.ib iU, bits := bitsU, hold := holdU, len := l'.bits >>> 3 }
    have hlFinal_ls : LS e lFinal iU o' :=
      ⟨rfl, hout', hlsU.hi0, hlsU.hi1, hlsU.ho0, hlsU.hb, hlsU.hH, hlsU.hacc⟩
    have hInSz' := e.inArr_size_of hAsz'
    have hdiv1 : 1 ≤ l'.bits.toNat / 8 := by omega
    have hiU6 : iU + 6 ≤ e.i0 + e.sm0.avail_in.toNat := by omega
    have hsubEq : OkOn (e.heap A' msg' m') (subn l'.in_ (l'.bits >>> 3)) (.ref e.ib iU) := by
      rw [hin']
      have hr := subn_ok (e.heap_bytes_in A' msg' m') (r := e.ib) (off := i') (n := l'.bits >>> 3)
        (by rw [u32_div8_eq]; have := inv'.accounting; have := e.hbits; omega)
        (by have := inv'.inputUpper; have := e.hINsz; omega)
      dsimp only [iU]
      rwa [u32_div8_eq] at hr
    have hshlOk := shl32_ok (h := e.heap A' msg' m') (x := 1) (n := bitsU) (by have : bitsU.toNat < 8 := hbits8; omega)
    have hldSt := e.heap_ldstate hc A' msg' m'
    have hmodeClass : (m' = e.s0.mode ∧ msg' = e.sm0.msg) ∨ (m' = TYPE ∧ msg' = e.sm0.msg) ∨ m' = BAD := by
      rcases hExit with ⟨_, hm, hmsg, _⟩ | ⟨_, hm⟩
      · exact Or.inl ⟨hm, hmsg⟩
      · rcases hm with ⟨hm, hmsg⟩ | hm
        · exact Or.inr (Or.inl ⟨hm, hmsg⟩)
        · exact Or.inr (Or.inr hm)
    have hltOut : OkOn (e.heap A' msg' m') (Ptr.lt lFinal.out c.end_)
        (decide (o' < e.o0 + e.sm0.avail_out.toNat - 257)) := by
      rw [show lFinal.out = .ref e.ob o' from hout', hc.end_]
      exact Ptr.lt_ok (e.heap_bytes_ob A' msg' m')
        (by rw [hAsz']; have := e.hAsz; omega) (by rw [hAsz']; have := e.hAsz; omega)
    have hprog : e.o0 < o' ∨ lFinal.broke = true := by
      cases hbrF : l'.broke with
      | false =>
        exact Or.inl ((htr'.output_bounds.2.2.1 hbrF).1)
      | true =>
        exact Or.inr rfl
    rw [if_t hcond]
    refine Wp.bindO hlast8 ?_
    refine Wp.bindO hend8 ?_
    refine Wp.bindE hrL ?_
    refine Wp.bindO hsubEq ?_
    refine Wp.bindO hshlOk ?_
    refine Wp.bindO hldSt ?_
    by_cases hmLen : (({ e.s0 with mode := m' } : InflateState).mode != LEN) = true
    · have hmNe : m' ≠ LEN := by simpa using hmLen
      have hNotMode : m' ≠ e.s0.mode := by rw [e.hmode]; exact hmNe
      have hBr : l'.broke = true := by
        rcases hExit with ⟨_, hm, _⟩ | ⟨hbr, _⟩
        · exact False.elim (hNotMode hm)
        · exact hbr
      rw [if_t hmLen, M_pure_bind]
      refine Wp.pure' ⟨iU, o', A', msg', m', hlFinal_ls, hbits8, hlsU.hH,
        by omega, hAsz', rfl, hOut', hmodeClass, (fun h => by cases h), ?_, (fun _ => rfl), ?_⟩
      · intro _
        rcases hExit with ⟨_, hm, _⟩ | ⟨_, hbrC⟩
        · exact False.elim (hNotMode hm)
        · rcases hbrC with ⟨hm, hmsg⟩ | hm
          · exact Or.inl ⟨hm, hmsg⟩
          · exact Or.inr (Or.inl hm)
      · intro _
        simp only [cast_eq]
        exact ⟨u', horigU, Or.inr ⟨hprog, htr'⟩⟩
    · have hmEq : m' = LEN := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hmLen
        exact hmLen
      have hNotBr : l'.broke = false := by
        rcases hExit with ⟨hnb, _⟩ | ⟨_, hbrC⟩
        · exact hnb
        · rcases hbrC with ⟨hm, _⟩ | hm
          · exact False.elim ((by decide : TYPE ≠ LEN) (hm.symm.trans hmEq))
          · exact False.elim ((by decide : BAD ≠ LEN) (hm.symm.trans hmEq))
      have hmS0 : m' = e.s0.mode := hmEq.trans e.hmode.symm
      have hmsgS0 : msg' = e.sm0.msg := by
        rcases hExit with ⟨_, _, hmsg, _⟩ | ⟨hbr, _⟩
        · exact hmsg
        · cases hNotBr.symm.trans hbr
      rw [if_f hmLen]
      refine Wp.bindO hltOut ?_
      rw [M_pure_bind]
      by_cases hoom : o' + 258 ≤ e.o0 + e.sm0.avail_out.toNat
      · have hltT : decide (o' < e.o0 + e.sm0.avail_out.toNat - 257) = true := by
          simp only [decide_eq_true_eq]; omega
        rw [hltT]
        refine Wp.pure' ⟨iU, o', A', msg', m', hlFinal_ls, hbits8, hlsU.hH,
          by omega, hAsz', rfl, hOut', hmodeClass, ?_, (fun h => by cases h), (fun h => by cases h), ?_⟩
        · intro _
          exact ⟨hmS0, hmsgS0, hNotBr, hiU6, hoom⟩
        · intro _
          simp only [cast_eq]
          exact ⟨u', horigU, Or.inr ⟨hprog, htr'⟩⟩
      · have hltF : decide (o' < e.o0 + e.sm0.avail_out.toNat - 257) = false := by
          simp only [decide_eq_false_iff_not]; omega
        rw [hltF]
        refine Wp.pure' ⟨iU, o', A', msg', m', hlFinal_ls, hbits8, hlsU.hH,
          by omega, hAsz', rfl, hOut', hmodeClass, (fun h => by cases h), ?_, (fun _ => rfl), ?_⟩
        · intro _
          exact Or.inr (Or.inr ⟨hmS0, hmsgS0, by omega⟩)
        · intro _
          simp only [cast_eq]
          exact ⟨u', horigU, Or.inr ⟨hprog, htr'⟩⟩
  · rw [if_f hcond]
    exact Wp.pure' hno

/-! ### Shared whole-call entrypoint split after the 64-bit phase -/

/-- Canonical `Ctx` constructed at entry to `inflate_fast` for `e : EnvG α`. -/
def fastCtx {α : Bool} (e : EnvG α) : Ctx := {
  strm := e.strm, state := some (.tab e.stid),
  last := .ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5),
  beg := .ref e.ob e.bg,
  end_ := .ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257),
  wsize := e.s0.wsize, whave := e.s0.whave, wnext := e.s0.wnext, window := e.s0.window,
  lcode := e.s0.lencode, dcode := e.s0.distcode,
  lmask := ((1 : UInt32) <<< e.s0.lenbits) - 1, dmask := ((1 : UInt32) <<< e.s0.distbits) - 1 }

theorem fastCtx_ok {α : Bool} (e : EnvG α) : CtxOK e (fastCtx e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The 8-bit `do ... while` loop of `inflate_fast` against `fastCtx e`. -/
def fastLoop8 {α : Bool} (e : EnvG α) (l : L) : M L :=
  let c := fastCtx e
  cdoWhile (inflate_fast_body c)
    (fun l => do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) l

/-- The `leave:` epilogue of `inflate_fast` for `e : EnvG α`. -/
def fastFinish {α : Bool} (e : EnvG α) (l : L) : M Unit := do
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
  stInflateState (some (.tab e.stid)) { st with hold, bits }

/-- Lines 637–657 of `inflate_fast` packaged sequentially. -/
def fastPhase64 {α : Bool} (e : EnvG α) (l0 : L) : M (L × Bool) :=
  let c := fastCtx e
  if !α && e.sm0.avail_in >= 16 && e.sm0.avail_out >= 2 + 258 + 15 then do
    let last8 ← Ptr.add l0.in_ (e.sm0.avail_in - 16).toNat
    let end8 ← Ptr.add l0.out (e.sm0.avail_out - (2 + 258 + 15)).toNat
    let l ← cdoWhile (inflate_fast_body8 c)
      (fun l => do
        if l.broke then pure (false, l)
        else if ← Ptr.le l.in_ last8 then pure (← Ptr.le l.out end8, l)
        else pure (false, l)) l0
    let len := l.bits >>> 3
    let in_ ← subn l.in_ len
    let bits := l.bits - (len <<< 3)
    let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
    let l := { l with in_, bits, hold, len }
    let st ← ldInflateState c.state
    let skip8 ←
      if st.mode != LEN then pure true
      else pure !(← Ptr.lt l.out c.end_)
    pure (l, skip8)
  else
    pure (l0, false)

/-- Remainder after the 64-bit phase: run `fastLoop8` unless `skip8`, then `fastFinish`. -/
def fastTailAfter64 {α : Bool} (e : EnvG α) (p : L × Bool) : M Unit := do
  let l ← if p.2 then pure p.1 else fastLoop8 e p.1
  fastFinish e l

private def fastBodyCore {α : Bool} (e : EnvG α) (back : Bool) : M Unit := do
  let lmask := (← shl32 1 e.s0.lenbits) - 1
  let dmask := (← shl32 1 e.s0.distbits) - 1
  let c : Ctx := {
    strm := e.strm, state := some (.tab e.stid),
    last := .ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5),
    beg := .ref e.ob e.bg,
    end_ := .ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257),
    wsize := e.s0.wsize, whave := e.s0.whave, wnext := e.s0.wnext, window := e.s0.window,
    lcode := e.s0.lencode, dcode := e.s0.distcode, lmask, dmask }
  let l : L := {
    in_ := .ref e.ib e.i0, out := .ref e.ob e.o0,
    hold := e.s0.hold, bits := e.s0.bits, here := default, op := 0, len := 0, dist := 0,
    from_ := default, broke := false, againL := false, againD := false }
  let (l, skip8) ←
    if !back && e.sm0.avail_in >= 16 && e.sm0.avail_out >= 2 + 258 + 15 then
      let last8 ← Ptr.add l.in_ (e.sm0.avail_in - 16).toNat
      let end8 ← Ptr.add l.out (e.sm0.avail_out - (2 + 258 + 15)).toNat
      let l ← cdoWhile (inflate_fast_body8 c)
        (fun l => do
          if l.broke then pure (false, l)
          else if ← Ptr.le l.in_ last8 then pure (← Ptr.le l.out end8, l)
          else pure (false, l)) l
      let len := l.bits >>> 3
      let in_ ← subn l.in_ len
      let bits := l.bits - (len <<< 3)
      let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
      let l := { l with in_, bits, hold, len }
      let st ← ldInflateState c.state
      let skip8 ←
        if st.mode != LEN then pure true
        else pure !(← Ptr.lt l.out c.end_)
      pure (l, skip8)
    else
      pure (l, false)
  let l ←
    if skip8 then pure l
    else
      cdoWhile (inflate_fast_body c)
        (fun l => do
          if l.broke then pure (false, l)
          else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
          else pure (false, l)) l
  let len := l.bits >>> 3
  let in_ ← subn l.in_ len
  let bits := l.bits - (len <<< 3)
  let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
  let ai : Int64 ←
    if ← Ptr.lt in_ (Ptr.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5)) then do
      let d ← Ptr.diff (Ptr.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5)) in_
      chk64 (5 + d.toInt)
    else do
      let d ← Ptr.diff in_ (Ptr.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5))
      chk64 (5 - d.toInt)
  let ao : Int64 ←
    if ← Ptr.lt l.out (Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)) then do
      let d ← Ptr.diff (Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)) l.out
      chk64 (257 + d.toInt)
    else do
      let d ← Ptr.diff l.out (Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257))
      chk64 (257 - d.toInt)
  let sm ← ldZStream e.strm
  stZStream e.strm { sm with next_in := in_, next_out := l.out, avail_in := ai.toUInt64.toUInt32, avail_out := ao.toUInt64.toUInt32 }
  let s ← ldInflateState (some (.tab e.stid))
  stInflateState (some (.tab e.stid)) { s with hold, bits }

private theorem inflate_fast_eq_bodyCore {α : Bool} (e : EnvG α) :
    inflate_fast e.strm e.start e.h0 = fastBodyCore e α e.h0 := by
  have hlast : OkOn e.h0 (Ptr.add e.sm0.next_in (e.sm0.avail_in - 5).toNat)
      (.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5)) := by
    rw [e.hnin, u32_toNat_sub (by change 5 ≤ e.sm0.avail_in.toNat; have := e.hai; omega)]
    have hr := Ptr.add_nat_ok (h := e.h0) (r := e.ib) (a := e.IN)
      (off := e.i0) (n := e.sm0.avail_in.toNat - 5) e.hIN (by have := e.hINsz; omega)
    have hoff : e.i0 + (e.sm0.avail_in.toNat - 5) = e.i0 + e.sm0.avail_in.toNat - 5 := by
      have := e.hai; omega
    simpa [hoff] using hr
  have hbeg : OkOn e.h0 (subn e.sm0.next_out (e.start - e.sm0.avail_out))
      (.ref e.ob e.bg) := by
    rw [e.hnout]
    have hn : (e.start - e.sm0.avail_out).toNat = e.start.toNat - e.sm0.avail_out.toNat :=
      u32_toNat_sub e.hstart
    have hr := subn_ok (h := e.h0) (r := e.ob) (a := e.A0)
      (off := e.o0) (n := e.start - e.sm0.avail_out) e.hA0 (by rw [hn]; exact e.hbeg)
      (by have := e.hAsz; omega)
    simpa only [hn, EnvG.bg] using hr
  have hend : OkOn e.h0 (Ptr.add e.sm0.next_out (e.sm0.avail_out - 257).toNat)
      (.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)) := by
    rw [e.hnout, u32_toNat_sub (by change 257 ≤ e.sm0.avail_out.toNat; have := e.hao; omega)]
    have hr := Ptr.add_nat_ok (h := e.h0) (r := e.ob) (a := e.A0)
      (off := e.o0) (n := e.sm0.avail_out.toNat - 257) e.hA0 (by have := e.hAsz; omega)
    have hoff : e.o0 + (e.sm0.avail_out.toNat - 257) = e.o0 + e.sm0.avail_out.toNat - 257 := by
      have := e.hao; omega
    simpa [hoff] using hr
  have hback := back_check_ok e
  dsimp only [OkOn, C.run] at hlast hbeg hend hback
  unfold inflate_fast
  rw [bind_app, e.hstrm, ldZStream_ok e.hsm]
  dsimp only
  rw [bind_app, e.hstate, castInflateState_ok]
  dsimp only
  rw [bind_app, hlast]
  dsimp only
  rw [bind_app, hbeg]
  dsimp only
  rw [bind_app, hend]
  dsimp only
  rw [bind_app, ldInflateState_tab e.hs0]
  dsimp only
  by_cases hwin : (e.s0.window != .null) = true
  · simp only [hwin, ↓reduceIte] at hback ⊢
    rw [bind_app] at hback ⊢
    cases h1 : Ptr.add e.sm0.next_out (e.sm0.avail_out.toNat : Int) e.h0 with
    | error f => rw [h1] at hback; cases hback
    | ok p1 =>
      rw [h1] at hback
      dsimp only at hback ⊢
      rw [bind_app] at hback ⊢
      cases h2 : Ptr.add e.s0.window (e.s0.wsize.toNat : Int) p1.2 with
      | error f => rw [h2] at hback; cases hback
      | ok p2 =>
        rw [h2] at hback
        simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hback
        obtain ⟨hval, hhp⟩ := hback
        dsimp only [fastBodyCore]
        rw [hval, hhp, ← e.hstrm, e.hnin, e.hnout]
        rfl
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte] at hback ⊢
    simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at hback
    have hα : false = α := hback.1
    dsimp only [fastBodyCore]
    rw [hα, ← e.hstrm, e.hnin, e.hnout]
    rfl

private theorem fastBodyCore_eq_seq {α : Bool} (e : EnvG α) :
    let l0 : L := {
      in_ := .ref e.ib e.i0, out := .ref e.ob e.o0, hold := e.s0.hold, bits := e.s0.bits,
      here := default, op := 0, len := 0, dist := 0, from_ := default, broke := false,
      againL := false, againD := false }
    fastBodyCore e α e.h0 = (fastPhase64 e l0 >>= fastTailAfter64 e) e.h0 := by
  intro l0
  have hshlL : OkOn e.h0 (shl32 1 e.s0.lenbits) ((1 : UInt32) <<< e.s0.lenbits) :=
    shl32_ok (x := 1) (n := e.s0.lenbits) (by have := e.hlt.1; omega)
  have hshlD : OkOn e.h0 (shl32 1 e.s0.distbits) ((1 : UInt32) <<< e.s0.distbits) :=
    shl32_ok (x := 1) (n := e.s0.distbits) (by have := e.hdt.1; omega)
  dsimp only [OkOn, C.run] at hshlL hshlD
  dsimp only [fastBodyCore]
  rw [bind_app, hshlL]
  dsimp only
  rw [bind_app, hshlD]
  dsimp only
  dsimp only [fastPhase64, fastTailAfter64, fastLoop8, fastFinish, fastCtx]
  by_cases hcond : (!α && e.sm0.avail_in >= 16 && e.sm0.avail_out >= 2 + 258 + 15) = true
  · simp only [hcond, ↓reduceIte, bind_app]
    cases Ptr.add (Ptr.ref e.ib e.i0) (e.sm0.avail_in - 16).toNat e.h0 with
    | error _ => rfl
    | ok p1 =>
      dsimp only
      cases Ptr.add (Ptr.ref e.ob e.o0) (e.sm0.avail_out - (2 + 258 + 15)).toNat p1.2 with
      | error _ => rfl
      | ok p2 =>
        dsimp only
        cases cdoWhile
            (inflate_fast_body8
              { strm := e.strm, state := some (InflateStateRef.tab e.stid),
                last := Ptr.ref e.ib (e.i0 + e.sm0.avail_in.toNat - 5), beg := Ptr.ref e.ob e.bg,
                end_ := Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257), wsize := e.s0.wsize,
                whave := e.s0.whave, wnext := e.s0.wnext, window := e.s0.window,
                lcode := e.s0.lencode, dcode := e.s0.distcode,
                lmask := 1 <<< e.s0.lenbits - 1, dmask := 1 <<< e.s0.distbits - 1 })
            (fun l => do
              if l.broke then pure (false, l)
              else if ← Ptr.le l.in_ p1.1 then pure (← Ptr.le l.out p2.1, l)
              else pure (false, l)) l0 p2.2 with
        | error _ => rfl
        | ok p3 =>
          dsimp only
          cases subn p3.1.in_ (p3.1.bits >>> 3) p3.2 with
          | error _ => rfl
          | ok p4 =>
            dsimp only
            cases shl32 1 (p3.1.bits - (p3.1.bits >>> 3) <<< 3) p4.2 with
            | error _ => rfl
            | ok p5 =>
              dsimp only
              cases ldInflateState (some (InflateStateRef.tab e.stid)) p5.2 with
              | error _ => rfl
              | ok p6 =>
                dsimp only
                by_cases hmode : (p6.1.mode != LEN) = true
                · simp only [hmode, ↓reduceIte]
                  rfl
                · simp only [hmode, Bool.false_eq_true, ↓reduceIte, bind_app]
                  cases Ptr.lt p3.1.out (Ptr.ref e.ob (e.o0 + e.sm0.avail_out.toNat - 257)) p6.2 with
                  | error _ => rfl
                  | ok p7 =>
                    dsimp only [pure_app]
                    cases p7.1 <;> rfl
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, bind_app, pure_app]
    rfl

/-- Single factored `inflate_fast` split after the 64-bit phase (`fast64_phase_wp`).
Discharges the common prologue and `back` check once for all five whole-call theorems. -/
theorem inflate_fast_split_wp {α : Bool} (e : EnvG α) {Q : Unit → Heap → Prop}
    (hstep : ∀ l1 skip8 h1, Fast64PhasePost e l1 skip8 h1 →
      (skip8 = false → Wp (fastLoop8 e l1 >>= fastFinish e) h1 Q) ∧
      (skip8 = true → Wp (fastFinish e l1) h1 Q)) :
    Wp (inflate_fast e.strm e.start) e.h0 Q := by
  let l0 : L := {
    in_ := .ref e.ib e.i0, out := .ref e.ob e.o0, hold := e.s0.hold, bits := e.s0.bits,
    here := default, op := 0, len := 0, dist := 0, from_ := default, broke := false,
    againL := false, againD := false }
  obtain ⟨⟨l1, skip8⟩, h1, hr64, hpost64⟩ :=
    fast64_phase_wp (fastCtx_ok e) l0 rfl rfl rfl rfl rfl α rfl
  rw [e.heap_initial] at hr64
  have hr64' : fastPhase64 e l0 e.h0 = .ok ((l1, skip8), h1) := hr64
  have htail : Wp (fastTailAfter64 e (l1, skip8)) h1 Q := by
    dsimp only [fastTailAfter64]
    cases hskip : skip8
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (hstep l1 false h1 (hskip ▸ hpost64)).1 rfl
    · simp only [↓reduceIte]
      exact (hstep l1 true h1 (hskip ▸ hpost64)).2 rfl
  have hseq : Wp (fastPhase64 e l0 >>= fastTailAfter64 e) e.h0 Q :=
    Wp.bindE hr64' htail
  have heq : inflate_fast e.strm e.start e.h0 = (fastPhase64 e l0 >>= fastTailAfter64 e) e.h0 :=
    (inflate_fast_eq_bodyCore e).trans (fastBodyCore_eq_seq e)
  obtain ⟨u, after, hrun, hq⟩ := hseq
  exact ⟨u, after, heq.trans hrun, hq⟩

end Zlib.Inffast.Proofs
