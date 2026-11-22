import ZlibF.Proof.«deflate.c.engine.trailer-output»

/-! # Public Z_FINISH calls after the final block has drained -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Init and accepted calls keep last_flush in this range. The arithmetic
check in the actual entry is total throughout that range. -/
theorem rank_legal_last_flush (f : Int32) (lower : -2 ≤ f.toInt) (upper : f.toInt ≤ 5) :
    ∃ value, RANK f = pure value := by
  have values : f = -2 ∨ f = -1 ∨ f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 := by
    have : f.toInt = -2 ∨ f.toInt = -1 ∨ f.toInt = 0 ∨ f.toInt = 1 ∨
        f.toInt = 2 ∨ f.toInt = 3 ∨ f.toInt = 4 ∨ f.toInt = 5 := by omega
    simp only [← Int32.toInt_inj]
    exact this
  rcases values with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl⟩

/-- The exact public entry reaches the final source statements for an
already-finished engine. The last_flush range is a phase invariant still
to be connected to arbitrary public histories, not a caller restriction. -/
theorem public_finish_entry {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = FINISH_STATE)
    (empty : z.avail_in = 0) (look : d.lookahead = 0) (pending : d.pending = 0)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5) :
    deflate (some r) Z_FINISH h = publicFinishTail (some r) (some (.tab ds)) Z_FINISH
      (setD h ds { d with last_flush := Z_FINISH }) := by
  have good0 := last_flush_good good Z_FINISH
  have tail := public_finish_source good0.live.hz good0.live.hs status empty look
  have header : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH)
      (setD h ds { d with last_flush := Z_FINISH }) =
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH (setD h ds { d with last_flush := Z_FINISH }) := by
    have getStatus : rd (some (.tab ds)) (·.status) (setD h ds { d with last_flush := Z_FINISH }) =
        .ok (FINISH_STATE, setD h ds { d with last_flush := Z_FINISH }) := by
      simp only [rdD_eq, setD_dstates_same, status]
    have getWrap : rd (some (.tab ds)) (·.wrap) (setD h ds { d with last_flush := Z_FINISH }) =
        .ok (d.wrap, setD h ds { d with last_flush := Z_FINISH }) := by
      simp only [rdD_eq, setD_dstates_same]
    unfold publicZlibHeader
    simp only [bind_app, getStatus, getWrap,
      show (FINISH_STATE == INIT_STATE) = false from rfl, Bool.false_and,
      Bool.false_eq_true, ite_false, tail]
  obtain ⟨rank, ranked⟩ := rank_legal_last_flush d.last_flush lower upper
  have checked := stateCheck_live good.live
  have rankFinish : RANK Z_FINISH = pure 8 := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_FINISH > Z_BLOCK) = False from by decide, show (Z_FINISH < 0) = False from by decide,
    decide_false, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    empty, show ((0 : UInt32) != 0) = false from rfl, Bool.false_and, Bool.or_false,
    show (Z_FINISH != Z_FINISH) = false from rfl,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, good.live.hs, pending, show ((0 : UInt64) != 0) = false from rfl,
    BEq.rfl, rankFinish, ranked, Bool.and_false, rdD_eq, setD_dstates_same,
    ZStreamRef.get_setD, status]
  simpa only [status, pending] using header

/-- Recording the actual finishing flag retains the exact tree representation. -/
theorem last_flush_trees {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d pb buf) (flush : Int32) :
    TreesInvAt (setD h ds { d with last_flush := flush }) ds { d with last_flush := flush } pb buf := by
  refine ⟨⟨by simp, trees.base.wf, trees.base.static, trees.base.pbuf,
    trees.base.bytes, trees.base.rw, trees.base.size, trees.base.psize,
    trees.base.sym, trees.base.lit_lo, trees.base.lit_hi, trees.base.sym_end, trees.base.pending_le⟩,
    ⟨trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat, trees.run.bldyn, trees.run.blstat,
      trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩⟩

/-- After the one-time trailer flag is negative, the source's complete
header/data tail returns STREAM_END without emitting another trailer. -/
theorem public_finished_headers {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = FINISH_STATE)
    (empty : z.avail_in = 0) (look : d.lookahead = 0) (wrap : d.wrap = -1) :
    publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h = .ok (Z_STREAM_END, h) := by
  have tail : publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (Z_STREAM_END, h) := by
    rw [public_finish_source good.live.hz good.live.hs status empty look]
    unfold publicFinishTail
    simp only [bind_app, pure_app, show (Z_FINISH != Z_FINISH) = false from rfl,
      Bool.false_eq_true, ite_false, rdD_eq, good.live.hs, wrap,
      show (-1 : Int32) ≤ 0 from by decide, ite_true]
  unfold publicZlibHeader
  simp only [bind_app, rdD_eq, good.live.hs, status,
    show (FINISH_STATE == INIT_STATE) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ite_false, tail]

end Zlib.Deflate.Engine.Proofs
