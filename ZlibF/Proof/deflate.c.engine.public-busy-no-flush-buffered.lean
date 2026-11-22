import ZlibF.Proof.«deflate.c.engine.public-no-flush-buffered»
import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»

/-! # Complete accepted BUSY NO_FLUSH calls retain the working boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The accepted entry uses the actual pending run, then reaches the
header/data tail when caller output remains. No callee contract is assumed. -/
theorem public_pending_no_flush_continue {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result) (status : d.status = BUSY_STATE)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (run : flush_pending (some r) (setD h ds { d with last_flush := Z_NO_FLUSH }) = .ok ((), middle))
    (remaining : zm.avail_out ≠ 0) (finishedInput : result.status = FINISH_STATE → zm.avail_in = 0) :
    deflate (some r) Z_NO_FLUSH h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH) middle := by
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have finishInput : (result.status == FINISH_STATE && zm.avail_in != 0) = false := by
    by_cases status : result.status = FINISH_STATE
    · simp [status, finishedInput status]
    · simp [status]
  have checked := stateCheck_live good.live
  rw [public_deflate_source]
  simp only [bind_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide, show (Z_NO_FLUSH < 0) = False from by decide,
    decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, show (d.status == FINISH_STATE) = false from by rw [status]; rfl,
    show (Z_NO_FLUSH != Z_FINISH) = true from rfl, Bool.false_and, Bool.or_false,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending,
    ite_true, run, goodM.live.hz,
    show (zm.avail_out == 0) = false from beq_eq_false_iff_ne.mpr remaining,
    rdD_eq, goodM.live.hs, finishInput]

/-- BUSY states skip the zlib header statements on every continuation. -/
theorem public_busy_no_flush_header_skip {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) :
    publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH) h =
      publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h := by
  unfold publicZlibHeader
  simp only [bind_app, rdD_eq, good.live.hs, status,
    show (BUSY_STATE == INIT_STATE) = false from rfl, Bool.false_and, Bool.false_eq_true, ite_false]

end Zlib.Deflate.Engine.Proofs
