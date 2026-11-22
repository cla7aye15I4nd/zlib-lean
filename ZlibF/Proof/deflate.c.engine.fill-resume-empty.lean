import ZlibF.Proof.«deflate.c.engine.fill-call»
import ZlibF.Spec.Functional.Checksums

/-! # Resuming fill_window after consuming bytes without new input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem fill_body_no_input {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (input : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    fillBody (some (.tab ds)) d.w_size false h = .ok (true, h) := by
  simp only [fillBody, bind_app, ldDeflateState_tab good.live.hs, noSlide, ite_false,
    rdD_eq, good.live.hs, good.live.back, zrd_eq, good.live.hz, input]
  rfl

end Zlib.Deflate.Engine.Proofs
