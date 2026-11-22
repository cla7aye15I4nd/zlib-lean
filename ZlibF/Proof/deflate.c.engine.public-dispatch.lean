import ZlibF.Proof.«deflate.c.engine.public-header»

/-! # Actual default entry checks and slow-strategy dispatch -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (entry prefix).
An actually initialized default stream with valid nonnull buffers reaches
the zlib-header statements after recording Z_NO_FLUSH. Empty input is
included. This is an accepted-entry path, not the refusal theorem. -/
theorem public_default_entry {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    deflate (some r) Z_NO_FLUSH h =
      publicZlibHeader (some r) (some (.tab ds))
        (publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH)
        (setD h ds { d with last_flush := Z_NO_FLUSH }) := by
  have checked := stateCheck_live start.good.live
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · simp [input empty]
  have rank0 : RANK Z_NO_FLUSH = pure 0 := by rfl
  have rankOld : RANK (-2) = pure (-4) := by rfl
  rw [public_deflate_source]
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    show (Z_NO_FLUSH > Z_BLOCK) = False from by decide,
    show (Z_NO_FLUSH < 0) = False from by decide, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, start.good.live.hz, start.good.live.zst, castDeflateState,
    ldZStream_ok start.good.live.hz, ldDeflateState_tab start.good.live.hs, inputs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    start.status, show (INIT_STATE == FINISH_STATE) = false from by decide,
    Bool.false_and, show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr positive,
    wrD_eq, start.good.live.hs, start.pending, show ((0 : UInt64) != 0) = false from rfl,
    start.lastFlush, rank0, rankOld, show ((0 : Int32) ≤ -4) = False from by decide,
    Bool.and_false, rdD_eq, setD_dstates_same, ZStreamRef.get_setD]

end Zlib.Deflate.Engine.Proofs
