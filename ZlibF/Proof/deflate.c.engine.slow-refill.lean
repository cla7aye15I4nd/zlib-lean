import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»

/-! # The slow strategy's actual refill and early return -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real fill producing enough lookahead reaches exactly the existing
complete body on its actual returned heap. -/
theorem slow_body_fill_ready {h after : Heap} {ds : Nat} {d filled : DeflateState}
    (state : h.dstates ds = some d) (stateA : after.dstates ds = some filled)
    (short : d.lookahead.toNat < 262) (ready : 262 ≤ filled.lookahead.toNat)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (flush : Int32) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) flush st h =
      deflate_slow_body (some (.tab ds)) flush st after := by
  have before : d.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using short
  have enough : ¬ filled.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using Nat.not_lt.mpr ready
  have nonzero : filled.lookahead ≠ 0 := by
    intro zero
    simp [zero] at ready
  simp [slow_body_source, bind_app, rdD_eq, state, stateA, before, enough, run, nonzero]

/-- With Z_NO_FLUSH the source returns need_more before search when the
actual fill leaves short lookahead. The returned state is that fill's
state; no insertion or tally occurs after it. -/
theorem slow_body_fill_wait {h after : Heap} {ds : Nat} {d filled : DeflateState}
    (state : h.dstates ds = some d) (stateA : after.dstates ds = some filled)
    (short : d.lookahead.toNat < 262) (shortA : filled.lookahead.toNat < 262)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (st : LoopS) :
    deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h =
      .ok ({ st with ret := some need_more }, after) := by
  have before : d.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using short
  have smaller : filled.lookahead < MIN_LOOKAHEAD_u := by
    simpa only [UInt32.lt_iff_toNat_lt, show MIN_LOOKAHEAD_u.toNat = 262 from rfl] using shortA
  simp [slow_body_source, bind_app, rdD_eq, state, before, run, stateA, smaller]

end Zlib.Deflate.Engine.Proofs
