import ZlibF.Proof.«public-compress-loop-facts»
import ZlibF.Proof.«deflate.c.universal-call-entry-all»
import ZlibF.Proof.«deflate.c.universal-call-phases»
import ZlibF.Proof.«deflate.c.universal-params-publish»

/-!
# deflate.c: new input after the first `Z_FINISH` (`FinishedNewInput`)

A call on a finished stream with new input that is not refused returns `Z_BUF_ERROR` or writes a
byte. The entry phase of `deflate`: with no output room it returns `Z_BUF_ERROR`; with nothing
pending the no-progress test returns `Z_BUF_ERROR` (`entry_empty_all`); with output pending it
calls `flush_pending`, which either fills the output (`Z_OK` with `avail_out = 0`, so a byte was
written) or keeps the status and `avail_in`, and the test
`s->status == FINISH_STATE && strm->avail_in != 0` returns `Z_BUF_ERROR`.

The frame of `flush_pending` used here: `_tr_flush_bits` leaves the stream tables unchanged
(`StreamsKept`), `flush_pending` writes only `next_out`, `total_out` and `avail_out` of the
stream record, and keeps the status (`exact_flush_pending`).
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal
open Zlib.Deflate.Universal.Call Zlib.Deflate.Proofs
set_option autoImplicit false

/-- A returning run leaves the stream tables unchanged. -/
def StreamsKept {α : Type} (m : M α) : Prop :=
  ∀ h a h', m h = .ok (a, h') → h'.streams = h.streams ∧ h'.gzstates = h.gzstates

theorem StreamsKept.pure {α : Type} (a : α) : StreamsKept (Pure.pure a : M α) := by
  intro h v h' run; cases run; exact ⟨rfl, rfl⟩

theorem StreamsKept.ub {α : Type} (what : String) : StreamsKept (C.ub what : M α) := by
  intro h v h' run; cases run

theorem StreamsKept.bind {α β : Type} {m : M α} {f : α → M β} (hm : StreamsKept m)
    (hf : ∀ a, StreamsKept (f a)) : StreamsKept (m >>= f) := by
  intro h value after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    rcases p with ⟨a, h1⟩
    rw [e] at run
    obtain ⟨s1, g1⟩ := hm h a h1 e
    obtain ⟨s2, g2⟩ := hf a h1 value after run
    exact ⟨s2.trans s1, g2.trans g1⟩

theorem StreamsKept.ite {α : Type} (p : Prop) [Decidable p] {a b : M α} (ha : StreamsKept a)
    (hb : StreamsKept b) : StreamsKept (if p then a else b) := by
  split <;> assumption

theorem kept_ldDeflateState (p : DeflateStatePtr) : StreamsKept (ldDeflateState p) := by
  intro h value after run
  unfold ldDeflateState at run
  repeat' first | split at run | (cases run; exact ⟨rfl, rfl⟩) | contradiction

theorem dput_streams (h : Heap) (r : DeflateStateRef) (v : DeflateState) :
    (r.put h v).streams = h.streams ∧ (r.put h v).gzstates = h.gzstates := by
  cases r with
  | tab i => simp only [DeflateStateRef.put]; split <;> simp

theorem kept_stDeflateState (p : DeflateStatePtr) (v : DeflateState) : StreamsKept (stDeflateState p v) := by
  intro h value after run
  unfold stDeflateState at run
  repeat' first | split at run | contradiction
  cases run
  exact dput_streams _ _ _

theorem kept_ptr_add (p : BPtr) (k : Int) : StreamsKept (p.add k) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run; exact ⟨rfl, rfl⟩) | contradiction

theorem space_put_streams (h : Heap) (r : BRef) (a : Array UInt8) :
    (Space.put h r a).streams = h.streams ∧ (Space.put h r a).gzstates = h.gzstates := by
  cases r <;> simp only [Space.put] <;> (try split) <;> simp

theorem space_modify_streams (h : Heap) (r : BRef) (f : Array UInt8 → Array UInt8) :
    (Space.modify h r f).streams = h.streams ∧ (Space.modify h r f).gzstates = h.gzstates := by
  cases r <;> exact ⟨rfl, rfl⟩

theorem kept_store8 (p : BPtr) (v : UInt8) : StreamsKept (store8 p v) := by
  intro h value after run
  unfold store8 Ptr.store at run
  repeat' first | split at run | contradiction
  cases run
  first | exact space_put_streams _ _ _ | exact space_modify_streams _ _ _

theorem kept_memcpy (dst src : BPtr) (n : Nat) : StreamsKept (Ptr.memcpy dst src n) := by
  intro h value after run
  unfold Ptr.memcpy at run
  repeat' first | split at run | (cases run; exact ⟨rfl, rfl⟩) | contradiction
  all_goals (cases run; exact space_modify_streams _ _ _)

/-- `_tr_flush_bits` leaves the stream tables unchanged. -/
theorem kept_tr_flush_bits (s : DeflateStatePtr) : StreamsKept (Zlib.Trees.«_tr_flush_bits» s) := by
  unfold Zlib.Trees.«_tr_flush_bits» Zlib.Trees.bi_flush Zlib.Trees.put_short Zlib.Trees.put_byte Zlib.Trees.md
    Zlib.Trees.rd Zlib.Trees.isub Zlib.Trees.ck
  repeat' first
    | exact kept_ldDeflateState _
    | exact kept_stDeflateState _ _
    | exact kept_ptr_add _ _
    | exact kept_store8 _ _
    | exact StreamsKept.pure _
    | exact StreamsKept.ub _
    | apply StreamsKept.ite
    | apply StreamsKept.bind
    | intro _

theorem get_of_kept {h h' : Heap} (r : ZStreamRef) (s1 : h'.streams = h.streams) (s2 : h'.gzstates = h.gzstates) :
    r.get h' = r.get h := by
  cases r <;> simp [ZStreamRef.get, s1, s2]

theorem kept_wr (p : DeflateStatePtr) (f : DeflateState → DeflateState) : StreamsKept (wr p f) := by
  unfold wr
  exact StreamsKept.bind (kept_ldDeflateState p) (fun d => kept_stDeflateState p (f d))

/-- A successful operation preserves the amount of input present at this stream. -/
private def KeepsAvail (r : ZStreamRef) {α : Type} (m : M α) : Prop :=
  ∀ h a after, m h = .ok (a, after) →
    (r.get after).map ZStream.avail_in = (r.get h).map ZStream.avail_in

private theorem KeepsAvail.bind {r : ZStreamRef} {α β : Type} {m : M α} {f : α → M β}
    (hm : KeepsAvail r m) (hf : ∀ a, KeepsAvail r (f a)) : KeepsAvail r (m >>= f) := by
  intro h v after run
  rw [bind_app] at run
  cases e : m h with
  | error _ => simp [e] at run
  | ok p =>
    obtain ⟨a, middle⟩ := p
    rw [e] at run
    exact (hf a middle v after run).trans (hm h a middle e)

private theorem KeepsAvail.of_kept {r : ZStreamRef} {α : Type} {m : M α} (keeps : StreamsKept m) :
    KeepsAvail r m := by
  intro h a after run
  obtain ⟨streams, gz⟩ := keeps h a after run
  rw [get_of_kept r streams gz]

private theorem KeepsAvail.ite {r : ZStreamRef} {α : Type} (p : Prop) [Decidable p] {a b : M α}
    (ha : KeepsAvail r a) (hb : KeepsAvail r b) : KeepsAvail r (if p then a else b) := by
  split <;> assumption

private theorem KeepsAvail.update (r : ZStreamRef) (f : ZStream → ZStream)
    (field : ∀ z, (f z).avail_in = z.avail_in) : KeepsAvail r (zwr (some r) f) := by
  intro h a after run
  rw [zwr_eq] at run
  cases get : r.get h <;> simp [get] at run
  obtain ⟨rfl, rfl⟩ := run
  simp [get, field]

/-- `flush_pending` keeps the stream's `avail_in`. -/
theorem flush_pending_avail_in {h after : Heap} {r : ZStreamRef} {z : ZStream}
    (getz : r.get h = some z) (run : flush_pending (some r) h = .ok ((), after)) :
    ∃ z', r.get after = some z' ∧ z'.avail_in = z.avail_in := by
  have ld (p : ZStreamPtr) : StreamsKept (ldZStream p) := by
    intro before v later load
    unfold ldZStream at load
    repeat' first | split at load | (cases load; exact ⟨rfl, rfl⟩) | contradiction
  have cast (p : Option StateRef) : StreamsKept (castDeflateState p) := by
    intro before v later load
    unfold castDeflateState at load
    split at load <;> cases load <;> exact ⟨rfl, rfl⟩
  have keeps : KeepsAvail r (flush_pending (some r)) := by
    unfold flush_pending advance_pending zrd rd
    repeat' first
      | exact KeepsAvail.update _ _ (fun _ => rfl)
      | exact KeepsAvail.of_kept (kept_tr_flush_bits _)
      | exact KeepsAvail.of_kept (kept_wr _ _)
      | exact KeepsAvail.of_kept (kept_memcpy _ _ _)
      | exact KeepsAvail.of_kept (kept_ptr_add _ _)
      | exact KeepsAvail.of_kept (kept_ldDeflateState _)
      | exact KeepsAvail.of_kept (ld _)
      | exact KeepsAvail.of_kept (cast _)
      | exact KeepsAvail.of_kept (StreamsKept.pure _)
      | apply KeepsAvail.ite
      | apply KeepsAvail.bind
      | intro _
  have field := keeps h () after run
  cases next : r.get after <;> simp_all

/-- **`FinishedNewInput`**: new input offered to a finished stream gives `Z_BUF_ERROR`, or the
pending flush fills the output first (`Z_OK` after writing a byte). -/
theorem finished_new_input : FinishedNewInput := by
  intro h after r ds z d flush rc inv buffers active run notRef fs ain
  have good := inv.good
  have run' : deflate (some r) flush h = .ok (rc, after) := run
  rw [deflate_phases] at run'
  by_cases room : z.avail_out = 0
  · obtain ⟨i, entry, -⟩ := entry_full good notRef room
      (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))
    rw [entry] at run'
    left
    simp only [Except.ok.injEq, Prod.mk.injEq] at run'
    exact run'.1.symm
  by_cases pend : d.pending = 0
  · obtain ⟨np, -⟩ := entry_empty_all good pend notRef room inv.shape.lastFlush
      (fun s => headerPhase (some r) s flush (strategyPhase (some r) s flush (trailerPhase (some r) s flush)))
    obtain ⟨i, entry, -⟩ := np (Or.inr ⟨fs, ain⟩)
    rw [entry] at run'
    left
    simp only [Except.ok.injEq, Prod.mk.injEq] at run'
    exact run'.1.symm
  -- output is pending: the flush, then the test of new input after `Z_FINISH`
  have accepted := notRef
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have inp : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, ain⟩))))
  have fin : flush = Z_FINISH := Classical.byContradiction fun ne => accepted (Or.inr (Or.inr (Or.inr (Or.inr ⟨fs, ne⟩))))
  have checked := stateCheck_live good.live
  obtain ⟨high, low⟩ := entry_valid_flags flushLow flushHigh
  have test : (z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH)) = false := by
    simp [out, inp, fin]
  unfold entryPhase at run'
  simp only [bind_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs, test,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr room,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pend, ite_true] at run'
  split at run'
  · rename_i x1 H1 ef
    have getz0 : r.get (setD h ds { d with last_flush := flush }) = some z := by
      rw [ZStreamRef.get_setD]; exact good.live.hz
    obtain ⟨z1, getz1, ain1⟩ := flush_pending_avail_in getz0 ef
    obtain ⟨d1, getd1, pars1⟩ :=
      (Zlib.Deflate.Universal.Params.exact_flush_pending (some r) _ _ H1 ef).1 ds _ (setD_dstates_same _ _ _)
    have st1 : d1.status = FINISH_STATE := by
      simp only [Zlib.Deflate.Universal.Params.Pars, Prod.mk.injEq] at pars1
      rw [pars1.2.2.2.2.2.2.1]; exact fs
    simp only [getz1] at run'
    by_cases full : z1.avail_out = 0
    · rw [ite_eq_left (by simp [full])] at run'
      simp only [bind_app, wrD_eq, getd1, pure_app, Except.ok.injEq, Prod.mk.injEq] at run'
      obtain ⟨-, rfl⟩ := run'
      right
      intro z' getz'
      rw [ZStreamRef.get_setD, getz1] at getz'
      cases getz'
      rw [full]; exact Ne.symm room
    · left
      obtain ⟨i, err, -⟩ := err_return_static getz1 Z_BUF_ERROR
      rw [ite_eq_right (by simp [full])] at run'
      simp only [bind_app, ldDeflateState_tab getd1, ldZStream_ok getz1] at run'
      rw [ite_eq_left (by simp [st1, ain1, ain]), err] at run'
      simp only [Except.ok.injEq, Prod.mk.injEq] at run'
      exact run'.1.symm
  · cases run'

#print axioms finished_new_input

/-- `DeflateLoopFacts` from the three statements `ReachableInv`, `DeflateCall` and `CallFrameFacts`. -/
theorem deflate_loop_facts (reach : ReachableInv) (call : DeflateCall) (frame : CallFrameFacts) :
    DeflateLoopFacts :=
  deflate_loop_facts_of reach call frame finished_new_input

#print axioms deflate_loop_facts

end ZlibF.Spec.Public.Proofs.Compress
