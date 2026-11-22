import ZlibF.Spec.Common.Sequences
import ZlibF.Spec.Common.GzState
import ZlibF.Spec.Functional.Format

/-!
# Completion of the default zlib decoder

The default decoder is the one `inflateInit` makes: zlib wrapper, 32 KiB window, no dictionary.
Its history is the actual `inflateInit`, legal edits of the buffers by the caller and actual
`inflate` calls; every allocation of the history succeeds. For a stream `S` that the format
accepts (`Zlib.Decodes [] S D`), two goals say that the decoder reads it to `Z_STREAM_END`.

* `Goal.default_inflate_progress`: a call with output room (or with none once all of `D` is
  written), given input that continues `S` (not empty, unless all of `S` is consumed), ends the stream with exactly `S` consumed and
  exactly `D` written, or returns `Z_OK` (`Z_BUF_ERROR` under `Z_FINISH`) having consumed input or
  written output; the consumed input stays a prefix of `S` and the written output a prefix of
  `D`. A caller that keeps offering the rest of `S` and output room ends the stream after at
  most `|S| + |D| + 1` such calls, under any chunking.
* `Goal.default_inflate_completes`: one call given the whole rest of `S` and room for the rest of
  `D` ends the stream.

A stream whose header sets `FDICT` asks for a dictionary: the call returns `Z_NEED_DICT` before
any output, as `zlib.h` documents.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec
set_option autoImplicit false

/-- The log after one observed `inflate` call (as the `step` constructor of `InflateDataTrace`). -/
def inflateLogStep (log : DataLog) (rc : Int32) (input output : List UInt8) (used : Nat) : DataLog :=
  { log with
    input := log.input ++ input.take used, output := log.output ++ output
    result := rc, finished := log.finished || rc == Z_STREAM_END }

/-- The history of a default decoder: the actual `inflateInit` (`inflateInit_` with
`sizeof(z_stream)` = 112), then caller edits of the buffers and actual `inflate` calls. Every
heap a call runs on, and every heap a caller edit leaves, satisfies the LP64 object-size limit,
as in `InflateDataTrace`. Every call runs on a heap whose allocations succeed. -/
inductive DefaultInflateTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Inflate.inflateInit_ (some r) version 112) h = .ok (Z_OK, after) →
      DefaultInflateTrace r after {}
  | caller {h after log} : DefaultInflateTrace r h log → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DefaultInflateTrace r after log
  | step {h after log flush rc input output used} : DefaultInflateTrace r h log →
      ZlibF.PlatformMemory.ByteObjectsFit h → NoAllocationFailure h →
      DataStep .inflate h after r flush rc input output used →
      DefaultInflateTrace r after (inflateLogStep log rc input output used)

/-- The zlib header of `S` sets `FDICT`. -/
def AsksDictionary (S : List UInt8) : Prop :=
  ∃ cmf flg tail, S = cmf :: flg :: tail ∧ flg.toNat / 32 % 2 = 1

/-- The flush values of an ordinary call: every value except `Z_BLOCK` and `Z_TREES`, which stop
at block boundaries. -/
def OrdinaryFlush (flush : Int32) : Prop :=
  flush = Z_NO_FLUSH ∨ flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH ∨ flush = Z_FULL_FLUSH ∨
    flush = Z_FINISH

/-- Progress of the default decoder on a valid stream, under any chunking. -/
def Goal.default_inflate_progress : Prop :=
  ∀ (r : ZStreamRef) (h : Heap) (log : DataLog) (S D input : List UInt8) (z : ZStream) (flush : Int32),
    DefaultInflateTrace r h log → log.finished = false →
    Zlib.Decodes [] S D → log.input <+: S →
    ZlibF.PlatformMemory.ByteObjectsFit h → NoAllocationFailure h → StreamBuffers h r →
    r.get h = some z → z.next_out ≠ .null → (z.avail_out ≠ 0 ∨ log.output = D) →
    Bytes h z.next_in z.avail_in.toNat input → log.input ++ input <+: S →
    (input ≠ [] ∨ log.input = S) → OrdinaryFlush flush →
    ∃ rc after output used, DataStep .inflate h after r flush rc input output used ∧
      ((rc = Z_STREAM_END ∧ log.input ++ input.take used = S ∧ log.output ++ output = D) ∨
       ((rc = Z_OK ∨ (rc = Z_BUF_ERROR ∧ flush = Z_FINISH)) ∧ (used ≠ 0 ∨ output ≠ []) ∧
         log.input ++ input.take used <+: S ∧ log.output ++ output <+: D) ∨
       (rc = Z_NEED_DICT ∧ AsksDictionary S ∧ log.output ++ output = []))

/-- Completion of the default decoder in one call: the whole rest of a valid stream and room for
the rest of its decoding. -/
def Goal.default_inflate_completes : Prop :=
  ∀ (r : ZStreamRef) (h : Heap) (log : DataLog) (S D : List UInt8) (z : ZStream) (flush : Int32),
    DefaultInflateTrace r h log → log.finished = false →
    Zlib.Decodes [] S D → log.input <+: S →
    ZlibF.PlatformMemory.ByteObjectsFit h → NoAllocationFailure h → StreamBuffers h r →
    r.get h = some z → z.next_out ≠ .null →
    Bytes h z.next_in z.avail_in.toNat (S.drop log.input.length) →
    D.length ≤ log.output.length + z.avail_out.toNat → OrdinaryFlush flush →
    ∃ rc after output used, DataStep .inflate h after r flush rc (S.drop log.input.length) output used ∧
      ((rc = Z_STREAM_END ∧ used = S.length - log.input.length ∧ log.output ++ output = D) ∨
       (rc = Z_NEED_DICT ∧ AsksDictionary S ∧ log.output ++ output = []))

end ZlibF.Spec.Public
