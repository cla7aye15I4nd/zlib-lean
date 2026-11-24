import Lean2C.OriginalUncompressDispatch
import ZlibF.Proof.«public-uncompress-loop»
import ZlibF.Proof.«public-inflate»

/-! The repeated zero-capacity calls in the two imported uncompress2_z wrappers. -/
namespace Lean2C.OriginalUncompress
open C ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Public.Proofs.Uncompress
open Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Uncompr Zlib.Gzguts OriginalUncompressLoop
open Refill (WrapperMode)
set_option autoImplicit false

private theorem refill_call {e : Proofs.Uncompress.Env} {l : UncLoop} {H : Heap} {log : DataLog}
    {i : Nat} {z : ZStream} {s : InflateState} (ok : EnvOK e) (cap : e.cap = 0)
    (st : SafeState e l H log i z s) (mode : WrapperMode s) (window : s.window = .null)
    (p : BPtr) (address : p ≠ .null) :
    ∃ rc g t, inflate (some e.r) Z_NO_FLUSH H = .ok (rc, g) ∧
      inflate (some e.r) Z_NO_FLUSH (Refill.heap e.k p H) = .ok (rc, Refill.heap e.k p g) ∧
      g.istates i = some t ∧ WrapperMode t ∧ t.window = .null := by
  have inv := (inflate_reachable_invariant st.reach st.good).1
  have counts := st.outCount
  have noOutput : log.output.length = 0 := by omega
  have full : z.avail_out = 0 := UInt32.toNat_inj.mp (by change z.avail_out.toNat = 0; omega)
  have dest : z.next_out ≠ .null := by
    rw [st.nextOut, noOutput, advance_zero]
    exact ok.outNotNull
  have src : z.next_in = .null → z.avail_in = 0 := by
    intro h
    have bytes := (call_ranges ok st).1
    rcases bytes with ⟨_, len, _⟩ | ⟨_, _, _, ptr, _⟩
    · exact UInt32.toNat_inj.mp len
    · rw [h] at ptr; cases ptr
  exact Refill.inflate_call p address (inv.to_origin st.fit).toDefaultStateJ st.alloc
    (st.call_buffers ok) dest src mode window full Z_NO_FLUSH

private def again (l : UncLoop) : M (Bool × UncLoop) := pure (l.err == Z_OK, l)

private theorem loop_body (k : Nat) : BodyOK (.tab k) (abiBody (some (.tab k))) := by
  unfold abiBody
  body_ok

private theorem pair_refill {H : Heap} {k : Nat} {z : ZStream}
    (live : H.streams k = some z) (p : BPtr) (l : UncLoop) :
    let r := ZStreamRef.tab k
    r.put (Refill.heap k p H) (refilled {z with next_out := p} l) =
      Refill.heap k p (r.put H (refilled z l)) := by
  dsimp only
  have seen : (ZStreamRef.tab k).get H = some z := live
  have after : ((ZStreamRef.tab k).put H (refilled z l)).streams k = some (refilled z l) :=
    ZStreamRef.get_put_same seen _
  rw [Refill.heap_eq_put live, ZStreamRef.put_put, Refill.heap_eq_put after, ZStreamRef.put_put]
  rfl

/-- The strict decrease from the reachable baseline bounds both runs. The
replacement cursor needs no byte range, even across a continuing call. -/
private theorem loop_go {e : Proofs.Uncompress.Env} (ok : EnvOK e) (cap : e.cap = 0)
    (p : BPtr) (address : p ≠ .null) (fuel : Nat) {l : UncLoop} {H : Heap} {log : DataLog}
    {i : Nat} {z : ZStream} {s : InflateState} (st : SafeState e l H log i z s)
    (mode : WrapperMode s) (window : s.window = .null) (enough : measure e l H < fuel) :
    ∃ l' g t, cdoWhile.go (abiBody (some e.r)) again fuel l H = .ok (l', g) ∧
      cdoWhile.go (abiBody (some e.r)) again fuel l (Refill.heap e.k p H) = .ok (l', Refill.heap e.k p g) ∧
      SafeEnded e i l' g ∧ g.istates i = some t ∧ t.window = .null := by
  induction fuel generalizing l H log z s with
  | zero => omega
  | succ n ih =>
    have hz : e.r.get H = some z := st.good.live.hz
    have seen : H.streams e.k = some z := hz
    have hs : e.r.get (Refill.heap e.k p H) = some {z with next_out := p} := by
      rw [Refill.heap_eq_put seen]
      exact ZStreamRef.get_put_same hz _
    have body : BodyOK e.r (abiBody (some e.r)) := loop_body e.k
    have reb : e.r.put (Refill.heap e.k p H) (refilled {z with next_out := p} l) =
        Refill.heap e.k p (e.r.put H (refilled z l)) := pair_refill seen p l
    have st1 := st.refill ok
    obtain ⟨rc, g, t, run, alt, state, nextMode, noWin⟩ := refill_call ok cap st1 mode window p address
    obtain ⟨rc', g', base, more, last⟩ := call_phase_safe inflate_public ok st1
      (refilled_full_in z l) (refilled_full_out z l)
    change inflate _ _ _ = .ok _ at base
    cases Except.ok.inj (run.symm.trans base)
    let step := {refilledLoop z l with err := rc}
    have first : abiBody (some e.r) l H = .ok (step, g) := by
      rw [body l H z hz, bind_app, run]
      rfl
    have second : abiBody (some e.r) l (Refill.heap e.k p H) = .ok (step, Refill.heap e.k p g) := by
      rw [body l _ _ hs, reb, bind_app, alt]
      rfl
    by_cases cont : rc = Z_OK
    · obtain ⟨_, _, _, z', s', _, _, _, next, lt⟩ := more cont
      have same := Option.some.inj (next.good.live.hs.symm.trans state)
      subst s'
      rw [measure_refill st] at lt
      obtain ⟨l', g', t', left, right, ended, get, null⟩ := ih next nextMode noWin (by omega)
      refine ⟨l', g', t', ?_, ?_, ended, get, null⟩
      · simpa only [cdoWhile.go, bind_app, first, again, pure_app, step, cont, beq_self_eq_true, ite_true] using left
      · simpa only [cdoWhile.go, bind_app, second, again, pure_app, step, cont, beq_self_eq_true, ite_true] using right
    · obtain ⟨input, output, u, z', s', fin⟩ := last cont
      refine ⟨step, g, t, ?_, ?_, ⟨_, _, input, output, u, _, z', _, s', fin⟩, state, noWin⟩
      all_goals simp only [cdoWhile.go, bind_app, first, second, again, pure_app, step,
        beq_false_of_ne cont, Bool.false_eq_true, ite_false]

/-- Both imported loop bodies return the same leftover lengths and status
for arbitrary input at zero capacity. -/
theorem zero_output_loop {e : Proofs.Uncompress.Env} {l : UncLoop} {H : Heap} {log : DataLog}
    {i : Nat} {z : ZStream} {s : InflateState} (ok : EnvOK e) (cap : e.cap = 0)
    (st : SafeState e l H log i z s) (mode : WrapperMode s) (window : s.window = .null)
    (p : BPtr) (address : p ≠ .null) :
    ∃ l' g t, (∀ generated, cdoWhile (sourceBody generated e.r) (sourceCond generated) l H = .ok (l', g) ∧
      cdoWhile (sourceBody generated e.r) (sourceCond generated) l (Refill.heap e.k p H) =
        .ok (l', Refill.heap e.k p g)) ∧ SafeEnded e i l' g ∧ g.istates i = some t ∧ t.window = .null := by
  obtain ⟨l', g, t, left, right, ended, get, null⟩ := loop_go ok cap p address fuel st mode window (measure_bound ok st)
  exact ⟨l', g, t, fun gen => by rw [loop_eq]; exact ⟨left, right⟩, ended, get, null⟩

#print axioms zero_output_loop
end Lean2C.OriginalUncompress
