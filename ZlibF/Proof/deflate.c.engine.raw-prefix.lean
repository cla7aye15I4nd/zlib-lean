import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.eof-stream-encoding»
import ZlibF.Proof.«deflate.c.engine.body-prefix-step»
import ZlibF.Proof.«deflate.c.engine.encoding-output-slices»
import ZlibF.Proof.«deflate.c.engine.body-all-scalar-output»
import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»
import ZlibF.Proof.«deflate.c.engine.eof-output-interval»
import ZlibF.Proof.«deflate.c.engine.pending-buffered»
import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

/-! # An initialized raw encoding invariant for publication and caller replacement -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Independent raw nonfinal-block meaning of already published bytes
and the actual remaining pending bits. This is the raw data phase; pending
wrapper header/trailer bytes have their separate public phases. The input
history and private representation are supplied by BufferedBoundary. -/
def RawPrefix (h : Heap) (d : DeflateState) (input : Nat → UInt8) (base : Nat)
    (published : List UInt8) : Prop :=
  ∃ remaining encoded, PendingBits h d remaining ∧
    ZlibF.Spec.bytesToBits published ++ remaining = encoded ∧
    BlockPrefix [] 0 [] encoded (inputPrefix input base)

/-- Legal caller replacement keeps the exact private raw pending sequence
and its independent meaning. Earlier published bytes are ghost history,
so the caller may reuse or replace the former public output buffer. -/
theorem RawPrefix.rebuffer {h g : Heap} {r : ZStreamRef} {ds base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {published : List UInt8}
    (encoding : RawPrefix h d input base published) (good : DGood h r ds z d)
    (edit : Rebuffer h g r) : RawPrefix g d input base published := by
  obtain ⟨remaining, encoded, pending, wire, meaning⟩ := encoding
  exact ⟨remaining, encoded, rebuffer_pending_bits good edit pending, wire, meaning⟩

end Zlib.Deflate.Engine.Proofs
