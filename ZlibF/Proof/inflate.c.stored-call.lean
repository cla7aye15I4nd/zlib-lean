import ZlibF.Proof.«inflate.c.main.stored2»
import ZlibF.Proof.«inflate.c.main.check0»
import ZlibF.Proof.«inflate.c.sync3»
import ZlibF.Proof.«inflate.c.ring»

/-!
# inflate.c: complete raw stored-block calls

Execution lemmas connect the actual dispatch loop and exit to the stored-copy
proof. The restricted raw-stream domain is explicit in each statement.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

set_option maxRecDepth 100000

/-- A finite sequence of actual mode executions, ending in an exception,
executes within the translated dispatch loop's fuel. -/
theorem xwhile_run_chain (body : X Unit) (locals : Nat → IL) (heaps : Nat → Heap)
    (n : Nat) (hn : n + 1 < fuel) (e : Ex) (final : IL) (after : Heap)
    (steps : ∀ j, j < n → runX body (locals j) (heaps j) =
      .ok ((.ok (), locals (j + 1)), heaps (j + 1)))
    (stop : runX body (locals n) (heaps n) = .ok ((.error e, final), after)) :
    runX (xwhile (pure true) body) (locals 0) (heaps 0) = .ok ((.error e, final), after) := by
  let P : Nat → IL → Heap → Prop := fun k l h =>
    ∃ j, j ≤ n ∧ k = n + 1 - j ∧ l = locals j ∧ h = heaps j
  let Q : Except Ex Unit → IL → Heap → Prop := fun result l h =>
    result = .error e ∧ l = final ∧ h = after
  have step : ∀ k l h, P (k + 1) l h → ∃ l1 h1,
      runX (pure true : X Bool) l h = .ok ((.ok true, l1), h1) ∧
      ∃ result l2 h2, runX (do body; pure false) l1 h1 = .ok ((result, l2), h2) ∧
        (match result with
        | .ok true => Q (.ok ()) l2 h2
        | .ok false => P k l2 h2
        | .error ex => Q (.error ex) l2 h2) := by
    rintro k l h ⟨j, hj, hk, rfl, rfl⟩
    refine ⟨locals j, heaps j, rfl, ?_⟩
    by_cases he : j = n
    · subst j
      exact ⟨.error e, final, after, by rw [runX_bind, stop], rfl, rfl, rfl⟩
    · have hjn : j < n := by omega
      refine ⟨.ok false, locals (j + 1), heaps (j + 1), ?_, j + 1, by omega, by omega, rfl, rfl⟩
      rw [runX_bind, steps j hjn]
      rfl
  obtain ⟨result, l, h, run, hQ⟩ := xwhileBrk_run P Q step
    (by rintro l h ⟨j, hj, hk, _, _⟩; omega)
    (k := n + 1) (l := locals 0) (h := heaps 0) ⟨0, by omega, by omega, rfl, rfl⟩ hn
  obtain ⟨rfl, rfl, rfl⟩ := hQ
  exact run

/-- `int inflate(z_streamp strm, int flush)`.
LOAD copies the actual boundary fields into the local registers. -/
theorem LOAD_run {c : Ctx} {h : Heap} {r zs z s}
    (E : Env c h r zs z s) (l : IL) :
    runX (LOAD c.strm c.st) l h = .ok ((.ok (),
      { l with
        put := z.next_out, left := z.avail_out, next := z.next_in,
        have_ := z.avail_in, hold := s.hold, bits := s.bits }), h) := by
  unfold LOAD
  have hz : ldZStream c.strm h = .ok (z, h) := by rw [E.strm]; exact ldZStream_ok E.hz
  rw [runX_bind, runX_lift_ok hz]
  simp only []
  rw [runX_bind, runX_ldS E]
  rfl

end Zlib.Inflate.Proofs
