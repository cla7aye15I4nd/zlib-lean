import ZlibF.Proof.«deflate.c.engine.public-header-resume-encoding»
import ZlibF.Proof.«deflate.c.engine.public-pending-checksum»
import ZlibF.Proof.«deflate.c.engine.public-no-flush-encoding»
import ZlibF.Proof.«deflate.c.engine.raw-prefix»
import ZlibF.Proof.«deflate.c.engine.body-prefix-step»
import ZlibF.Proof.«deflate.c.engine.encoding-output-slices»
import ZlibF.Proof.«deflate.c.engine.body-all-scalar-output»
import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»
import ZlibF.Proof.«deflate.c.engine.body-logical-checksum»
import ZlibF.Proof.«deflate.c.engine.body-ready-phase»
import ZlibF.Proof.«deflate.c.engine.eof-checksum»
import ZlibF.Proof.«deflate.c.engine.eof-stream-encoding»
import ZlibF.Proof.«deflate.c.engine.eof-output-interval»
import ZlibF.Proof.«deflate.c.engine.no-flush-loop-control»
import ZlibF.Proof.«deflate.c.engine.no-flush-resume»
import ZlibF.Proof.«deflate.c.engine.public-data-output-interval»

/-! # Actual split header resumption retains encoding and checksum together -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- Every accepted flush with a one-byte caller buffer completes an actual
split header before dispatch. The public call consumes no input, writes
exactly 156 and establishes the empty raw phase on the same returned heap. -/
theorem public_header_pending_one_output_encoding_adler {h : Heap} {r : ZStreamRef} {ds ob oo origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (flush : Int32) (boundary : BufferedBoundary h r ds z d input origin 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (status : d.status = BUSY_STATE) (one : z.avail_out = 1)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : HeaderPending h d [120]) :
    ∃ after z' result,
      deflate (some r) flush h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧ Bytes after z.next_out 1 [156] ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      result.pending = 0 ∧ RawPrefix after result input 0 [] ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd result))).toUInt64 := by
  have shape := encoding.one_remaining
  obtain ⟨_pb, after, z', result, written, remaining, _base,
      run, stateA, buffersA, accountA, _sizes, _storage, outputA, lastA, countA,
      _bits, fields, bytesA, pendingA, wireA, adlerA⟩ :=
    public_pending_buffered_exhausted_adler flush boundary buffers pointer inputValid flagLo flagHi
      (by intro impossible; rw [status] at impossible; cases impossible)
      (by rw [one]; decide) (by rw [one, shape.1]; decide) shape.2
  have empty : result.pending.toNat = 0 := by rw [one, shape.1] at countA; change result.pending.toNat + 1 = 1 at countA; omega
  have bits : result.bi_valid.toInt.toNat = 0 := by
    rw [fields]
    obtain ⟨_, _, _, bits, _, _⟩ := encoding
    exact bits
  obtain ⟨writtenEq, encodingA⟩ := header_byte_drain_encoding pendingA empty bits wireA
  have endA : fillEnd result = fillEnd d := by rw [fields]; rfl
  have checksumA : z'.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd result))).toUInt64 := by
    rw [endA, adlerA]
    exact checksum
  refine ⟨after, z', result, run, stateA, buffersA, ?_, ?_, outputA, ?_, lastA,
    UInt64.toNat_inj.mp empty, encodingA, checksumA⟩
  · simpa only [one, UInt32.toNat_one] using accountA
  · simpa only [one, UInt32.toNat_one, writtenEq] using bytesA
  · rw [fields]; exact status


end Zlib.Deflate.Engine.Proofs
