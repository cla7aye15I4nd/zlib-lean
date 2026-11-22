import ZlibF.Proof.«deflate.c.engine.match-advance»
import ZlibF.Proof.«deflate.c.engine.lazy-logical»
import ZlibF.Proof.«deflate.c.engine.slow-source»
import ZlibF.Proof.«deflate.c.engine.tally-literal»
import ZlibF.Proof.«deflate.c.engine.advance»

/-! # All slow-loop decisions with input and symbol room -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def DeferredByte (d : DeflateState) : Prop := d.match_available ≠ 0 → 1 ≤ d.strstart.toNat

theorem initialized_deferred_byte {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d) : DeferredByte d := by
  intro available
  exact False.elim (available start.matchAvailable)

end Zlib.Deflate.Engine.Proofs
