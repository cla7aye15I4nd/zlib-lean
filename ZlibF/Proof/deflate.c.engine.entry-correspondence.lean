import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«deflate.c.engine.public-rank»
import ZlibF.Proof.«trees.c.monad»
import ZlibF.Proof.«zutil.c»

/-! # Correspondence for the checked entry to the compiled deflate function -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- Entry prefix used by the earlier whole-function decomposition, through the last refusal. -/
def previousPublicEntry (strm : ZStreamPtr) (flush : Int32) (k : DeflateStatePtr → M Int32) : M Int32 := do
  if (← deflateStateCheck strm) != 0 || flush > Z_BLOCK || flush < 0 then return Z_STREAM_ERROR
  let s ← castDeflateState (← zrd strm (·.state))
  let z ← ldZStream strm
  let d ← ldDeflateState s
  if z.next_out == .null || (z.avail_in != 0 && z.next_in == .null) ||
      (d.status == FINISH_STATE && flush != Z_FINISH) then
    return ← ERR_RETURN strm Z_STREAM_ERROR
  if z.avail_out == 0 then return ← ERR_RETURN strm Z_BUF_ERROR
  let old_flush := d.last_flush
  wr s (fun d => { d with last_flush := flush })
  if d.pending != 0 then
    flush_pending strm
    if (← zrd strm (·.avail_out)) == 0 then
      wr s (fun d => { d with last_flush := -1 })
      return Z_OK
  else if z.avail_in == 0 && (← RANK flush) ≤ (← RANK old_flush) && flush != Z_FINISH then
    return ← ERR_RETURN strm Z_BUF_ERROR
  if (← rd s (·.status)) == FINISH_STATE && (← zrd strm (·.avail_in)) != 0 then
    return ← ERR_RETURN strm Z_BUF_ERROR
  k s

theorem entryPhase_eq_previousPublicEntry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (live : DLive h r ds z d) (flush : Int32) (requested : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5)
    (saved : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5) (k : DeflateStatePtr → M Int32) :
    Phases.entryPhase (some r) flush k h = previousPublicEntry (some r) flush k h := by
  obtain ⟨f, hf⟩ := public_rank_request_total flush (by omega) requested.2
  obtain ⟨g, hg⟩ := public_rank_request_total d.last_flush saved.1 saved.2
  have checked := stateCheck_live live
  have stream := ldZStream_ok live.hz
  have state := ldDeflateState_tab live.hs
  have low : ¬ flush < 0 := by rw [Int32.lt_iff_toInt_lt]; change ¬ flush.toInt < 0; omega
  have high : ¬ Z_BLOCK < flush := by rw [Int32.lt_iff_toInt_lt]; change ¬ 5 < flush.toInt; omega
  by_cases empty : z.avail_in = 0 <;>
    simp [Phases.entryPhase, previousPublicEntry, checked, bind_app, rd, zrd, stream, live.zst, state,
      castDeflateState_ok, cinline, hf, hg, empty, C.M_bind_assoc, C.M_pure_bind, low, high]

/-- The compiled definition runs the earlier entry on the protocol range, followed by
the actual header, strategy, and trailer. Every returning heap and every fault is included. -/
theorem deflate_entry_on_domain {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} (live : DLive h r ds z d) (flush : Int32) (requested : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5)
    (saved : -2 ≤ d.last_flush.toInt ∧ d.last_flush.toInt ≤ 5) :
    deflate (some r) flush h = previousPublicEntry (some r) flush (fun s =>
      Phases.headerPhase (some r) s flush (Phases.strategyPhase (some r) s flush
        (Phases.trailerPhase (some r) s flush))) h :=
  entryPhase_eq_previousPublicEntry live flush requested saved _

namespace EntryCounterexample
private def stream : ZStreamRef := .tab 0
private def strm : ZStreamPtr := some stream
private def record : ZStream := { (default : ZStream) with
    state := some (.deflate 1), zalloc := .fn "zcalloc", zfree := .fn "zcfree",
    next_in := .ref (.blk 2) 0, next_out := .ref (.blk 3) 0, avail_in := 1, avail_out := 1 }
private def state : DeflateState := { (default : DeflateState) with
    strm := strm, status := FINISH_STATE, last_flush := 2147483647, pending := 0 }
private def witness : Heap := { Heap.empty with
    streams := upd Heap.empty.streams 0 (some record)
    dstates := upd Heap.empty.dstates 1 (some state), bytes := upd (upd Heap.empty.bytes 2 (some #[0])) 3 (some #[0]), nextBlk := 4 }
private def observe (m : M Int32) : Except Fault Int32 := (m witness).map Prod.fst
private theorem old_faults (k : DeflateStatePtr → M Int32) :
    observe (previousPublicEntry strm Z_FINISH k) = .error (.ub "signed int overflow") := by rfl
private theorem emitted_returns :
    observe (deflate strm Z_FINISH) = .ok Z_BUF_ERROR := by
  let after := { witness with dstates := upd witness.dstates 1 (some { state with last_flush := Z_FINISH }) }
  change (ERR_RETURN strm Z_BUF_ERROR after).map Prod.fst = _
  obtain ⟨i, run, _⟩ := Zlib.Zutil.Proofs.strLit_run after _ (Zlib.Zutil.Proofs.errText_lit Z_BUF_ERROR.toInt)
  unfold ERR_RETURN ERR_MSG
  rw [Zlib.Zutil.Proofs.errorMessage_eval]
  simp only [bind_app, run]
  rfl

private theorem unequal_for_every_tail (k : DeflateStatePtr → M Int32) :
    deflate strm Z_FINISH ≠ previousPublicEntry strm Z_FINISH k := by
  intro eq
  have h := congrArg observe eq
  rw [old_faults, emitted_returns] at h
  contradiction

/-- A stored flush outside the protocol range invalidates whole-function equality
on arbitrary heaps, even if the continuation of the earlier entry can be chosen freely. -/
theorem deflate_differs_on_unrestricted_entry :
    ∃ p : ZStreamPtr, ∀ k : DeflateStatePtr → M Int32,
      deflate p Z_FINISH ≠ previousPublicEntry p Z_FINISH k :=
  ⟨strm, unequal_for_every_tail⟩

end EntryCounterexample
end Zlib.Deflate.Engine.Proofs
