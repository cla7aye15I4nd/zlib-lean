import ZlibF.Proof.«deflate.c.engine.raw-prefix»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-buffered»

/-! # Actual public data dispatch preserves independent raw encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The public request/retry marker changes neither pending bits nor their
raw encoding meaning. It is an actual state store, not an extra call. -/
theorem RawPrefix.last_flush {h : Heap} {r : ZStreamRef} {ds base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {published : List UInt8}
    (encoding : RawPrefix h d input base published) (good : DGood h r ds z d) (flush : Int32) :
    RawPrefix (setD h ds { d with last_flush := flush }) { d with last_flush := flush } input base published := by
  obtain ⟨remaining, encoded, pending, wire, meaning⟩ := encoding
  exact ⟨remaining, encoded, last_flush_pending_bits good pending flush, wire, meaning⟩

/-- A state-record write preserves an already captured raw caller slice. -/
theorem raw_output_bytes_setD {h : Heap} {ds ob offset count : Nat} {d : DeflateState} {written : List UInt8}
    (bytes : Bytes h (.ref (.blk ob) offset) count written) :
    Bytes (setD h ds d) (.ref (.blk ob) offset) count written := by
  rcases bytes with ⟨impossible, _⟩ | ⟨ref, off, array, pointer, get, bound, value⟩
  · cases impossible
  · obtain ⟨rfl, rfl⟩ := Ptr.ref.inj pointer
    exact Or.inr ⟨.blk ob, offset, array, rfl, get, bound, value⟩

end Zlib.Deflate.Engine.Proofs
