import ZlibF.Proof.«deflate.c.engine.header-pending-encoding»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»
import ZlibF.Proof.«deflate.c.engine.no-flush-resume»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»

/-! # The next actual public request completes a split initial header -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The split header invariant determines the actual remaining byte count;
it is not an extra caller restriction. -/
theorem HeaderPending.one_remaining {h : Heap} {d : DeflateState}
    (encoding : HeaderPending h d [120]) :
    d.pending.toNat = 1 ∧ PendingBits h d (ZlibF.Spec.bytesToBits [156]) := by
  obtain ⟨remaining, pending, wire, bits, _start, _look⟩ := encoding
  change (120 : UInt8) :: remaining = 120 :: [156] at wire
  have tail : remaining = [156] := (List.cons.inj wire).2
  rw [tail] at pending
  obtain ⟨bytes, data, equal⟩ := pending
  have value : bytes = [156] := by
    apply encoded_bytes_injective
    simpa only [bits, Zlib.Trees.Proofs.Out.natBits, List.range_zero,
      List.map_nil, List.append_nil] using equal.symm
  have count := public_bytes_length data
  rw [value] at count
  exact ⟨count.symm, bytes, data, equal⟩

/-- The actual public last-flush store does not change pending header bytes. -/
theorem HeaderPending.last_flush {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {published : List UInt8}
    (encoding : HeaderPending h d published) (good : DGood h r ds z d) (flush : Int32) :
    HeaderPending (setD h ds { d with last_flush := flush }) { d with last_flush := flush } published := by
  obtain ⟨remaining, pending, wire, bits, start, look⟩ := encoding
  exact ⟨remaining, last_flush_pending_bits good pending flush, wire, bits, start, look⟩


/-- Publishing the last header byte cannot leave raw pending bits. The
independent empty raw history follows from the exact byte equation. -/
theorem header_byte_drain_encoding {after : Heap} {result : DeflateState}
    {input : Nat → UInt8} {written : List UInt8} {remaining : List Bool}
    (pending : PendingBits after result remaining)
    (empty : result.pending.toNat = 0) (bits : result.bi_valid.toInt.toNat = 0)
    (wire : ZlibF.Spec.bytesToBits written ++ remaining = ZlibF.Spec.bytesToBits [156]) :
    written = [156] ∧ RawPrefix after result input 0 [] := by
  have remainingEmpty := pending_bits_empty pending empty bits
  have byteEq : written = [156] := by
    apply encoded_bytes_injective
    simpa only [remainingEmpty, List.append_nil] using wire
  rw [remainingEmpty] at pending
  refine ⟨byteEq, [], [], pending, rfl, ?_⟩
  simpa only [inputPrefix, List.range_zero, List.map_nil] using block_prefix_empty ([] : List UInt8) [] 0

end Zlib.Deflate.Engine.Proofs
