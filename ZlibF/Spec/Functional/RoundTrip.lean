import ZlibF.Spec.Functional.Sequences
import ZlibF.Spec.Functional.InflateCompletion
import ZlibF.Spec.Functional.Api.Compress
import ZlibF.Spec.Common.Utilities

/-!
# The round trip of the default zlib stream

The planned functional result of `AGENTS.md`: the default zlib stream written by `deflateInit` at
the default level and `deflate`, then read by `inflateInit` and `inflate`, gives back the input;
and `uncompress(compress(x)) = x`. The histories are the actual calls of a caller: the init, data
calls, and caller edits of the buffers between calls (`Rebuffer`). No dictionary call and no other
operation occurs.

* `DefaultDeflateHistory`: `deflateInit_(strm, Z_DEFAULT_COMPRESSION)`, then `deflate` calls with any
  flush value. `DefaultCleanHistory`: the same with only `Z_NO_FLUSH` and `Z_FINISH`, the histories
  that `deflateBound` speaks of (`zlib.h`).
* `DefaultInflateHistory`: `inflateInit_(strm)` (window 15), then `inflate` calls, for the
  conditional form; completion uses `DefaultInflateTrace` (`InflateCompletion.lean`), whose calls
  also run where every allocation succeeds. In `DefaultInflateHistory` every heap a
  call runs on and every heap a caller edit leaves keeps the LP64 object-size limit.

Goals:

* `Goal.stream_roundtrip`: the conditional form. When both histories reach `Z_STREAM_END` and the
  decoder read a prefix of the encoder's output, the decoder's output is the encoder's input.
* `Goal.deflate_completes_default`: after a clean history (only `Z_NO_FLUSH` and `Z_FINISH`: other
  flushes write output without input), one
  `deflate(Z_FINISH)` call with all the remaining input and room for more than the rest of the
  unsaturated `compressBound` sum of the whole input (`deflateBound` at these parameters, below
  saturation) returns `Z_STREAM_END`, and the whole output decodes to the whole input.
* `Goal.deflate_bound_default`: after `deflateInit` and caller edits, one `deflate(Z_FINISH)` call
  with all `n` input bytes and at least `deflateBound(strm, n)` bytes of room returns
  `Z_STREAM_END` with a stream that decodes to the input.
* `Goal.compress_completes`, `Goal.compress_z_completes`: `compressBound` room gives `Z_OK` and a
  stream that decodes to the source, when every allocation succeeds.
* `Goal.inflate_completes_default`: a default decoder that has read a prefix of a complete
  default stream, offered the rest of it with room for the rest of the decoding, returns
  `Z_STREAM_END` and writes the rest, when every allocation succeeds.
* `Goal.inflate_chain_ends`: the decoder ends under every chunking of the rest of the stream,
  with exactly the encoder's input.
* `Goal.deflate_finish_ends`: after any default history (any flush values), every continuation by
  `Z_FINISH` calls with positive room ends within a number of calls fixed by the state, with all
  input accepted and an output that decodes to it. No bound on the room.
* `Goal.stream_roundtrip_total`: the unconditional stream round trip.
* `Goal.uncompress_completes`: `uncompress` of a complete zlib stream without dictionary, with room
  for its decoding, returns `Z_OK` and the decoding, when every allocation succeeds.
* `Goal.compress_uncompress_roundtrip`: `uncompress(compress(x)) = x`.
* `Goal.compress_uncompress_roundtrip_witness`: its premises can all hold.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec

/-- A default zlib deflate history: `deflateInit_` at the default level, caller edits, and
actual `deflate` calls with any flush value. -/
inductive DefaultDeflateHistory (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Deflate.deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h =
        .ok (Z_OK, after) →
      DefaultDeflateHistory r after {}
  | caller {h after log} : DefaultDeflateHistory r h log → Rebuffer h after r →
      DefaultDeflateHistory r after log
  | step {h after log flush rc input output used} : DefaultDeflateHistory r h log →
      DataStep .deflate h after r flush rc input output used →
      DefaultDeflateHistory r after (deflateLogStep log flush rc input output used)

/-- A default deflate history whose `deflate` calls all used `Z_NO_FLUSH` or `Z_FINISH`. -/
inductive DefaultCleanHistory (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Deflate.deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h =
        .ok (Z_OK, after) →
      DefaultCleanHistory r after {}
  | caller {h after log} : DefaultCleanHistory r h log → Rebuffer h after r →
      DefaultCleanHistory r after log
  | step {h after log flush rc input output used} : DefaultCleanHistory r h log →
      (flush = Z_NO_FLUSH ∨ flush = Z_FINISH) →
      DataStep .deflate h after r flush rc input output used →
      DefaultCleanHistory r after (deflateLogStep log flush rc input output used)

/-- A default zlib inflate history: `inflateInit_` (window 15), caller edits, and actual
`inflate` calls with any flush value, each on a heap within the object-size limit. -/
inductive DefaultInflateHistory (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Inflate.inflateInit_ (some r) version 112) h = .ok (Z_OK, after) →
      DefaultInflateHistory r after {}
  | caller {h after log} : DefaultInflateHistory r h log → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DefaultInflateHistory r after log
  | step {h after log flush rc input output used} : DefaultInflateHistory r h log →
      ZlibF.PlatformMemory.ByteObjectsFit h →
      DataStep .inflate h after r flush rc input output used →
      DefaultInflateHistory r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END }

/-- A clean default history is a default history. -/
theorem DefaultCleanHistory.toDefault {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultCleanHistory r h log) : DefaultDeflateHistory r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ _ actual ih => exact .step ih actual

/-- **The stream round trip, conditional form.** A default zlib stream written by `deflate`
under any flush values and any chunking, and read by `inflate` under any chunking: when both
histories reach `Z_STREAM_END` and the decoder read a prefix of the encoder's output, the
decoder's output is the encoder's input. The two histories run on separate heaps. -/
def Goal.stream_roundtrip : Prop :=
  ∀ (rd ri : ZStreamRef) (hd hi : Heap) (encoded decoded : DataLog),
    DefaultDeflateHistory rd hd encoded → DefaultInflateHistory ri hi decoded →
    encoded.result = Z_STREAM_END → decoded.result = Z_STREAM_END →
    (∃ trailing, encoded.output = decoded.input ++ trailing) →
    decoded.output = encoded.input

/-- The unsaturated sum of `compressBound`: `m + m/4096 + m/16384 + m/33554432 + 13`. It is
`Api.compressBound m` as long as that does not saturate (`compressBound_eq_unsaturated`); unlike
`compressBound`, it keeps growing past `2^64`. -/
def unsaturatedBound (m : Nat) : Nat := m + m / 4096 + m / 16384 + m / 33554432 + 13

/-- **Completion of the default stream from the bound.** After a clean default history that has
not ended, a `deflate(Z_FINISH)` call offered all the remaining input `input`, with output room
more than what the bound of the whole input leaves after the output so far, returns
`Z_STREAM_END`: it accepts all of `input`, and the whole output decodes to the whole input. The
stream can be exactly as long as the bound, and a call that first delivers pending output and is
left with no room returns `Z_OK` (`deflate.c`), so room equal to the rest is not enough after an
earlier call; one call from a fresh stream needs only the bound (`Goal.deflate_bound_default`). The room is measured against `unsaturatedBound` of the whole input, which is
`compressBound` of the whole input below the saturation point. `zlib.h` promises nothing once
`compressBound` saturates at `2^64 - 1`, and a history may accept more input than that. At these
parameters `deflateBound` is `compressBound` (`Goal.deflate_bound_default`). Before
`Z_STREAM_END`, a `Z_FINISH` already given keeps the caller from offering new input. -/
def Goal.deflate_completes_default : Prop :=
  ∀ r h log z input,
    DefaultCleanHistory r h log → log.finished = false →
    r.get h = some z → StreamBuffers h r → z.next_out ≠ .null →
    Bytes h z.next_in z.avail_in.toNat input →
    (∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = []) →
    0 < z.avail_out.toNat →
    unsaturatedBound (log.input.length + input.length) < log.output.length + z.avail_out.toNat →
    ∃ after output, DataStep .deflate h after r Z_FINISH Z_STREAM_END input output input.length ∧
      Zlib.Decodes [] (log.output ++ output) (log.input ++ input)

/-- **The promise of `deflateBound`, default stream** (`zlib.h`): after `deflateInit` and caller
edits only, `deflateBound(strm, n)` returns `b`; then one `deflate(Z_FINISH)` offered all `n`
input bytes with at least `b` bytes of room returns `Z_STREAM_END`, accepts all input, and writes
a stream that decodes to the input. -/
def Goal.deflate_bound_default : Prop :=
  ∀ r h log z input n b,
    DefaultCleanHistory r h log → log.input = [] → log.output = [] → log.finished = false →
    C.run (Zlib.Deflate.deflateBound (some r) n) h = .ok (b, h) →
    r.get h = some z → StreamBuffers h r → z.next_out ≠ .null →
    Bytes h z.next_in z.avail_in.toNat input → input.length = n.toNat →
    b.toNat ≤ z.avail_out.toNat →
    ∃ after output, DataStep .deflate h after r Z_FINISH Z_STREAM_END input output input.length ∧
      Zlib.Decodes [] output input

/-- **A compressor completes with `compressBound` room**, at the default level, when every
allocation succeeds: the call returns `Z_OK`, stores the length `m` it wrote, at most
`compressBound n`, and the `m` bytes at `dest` decode to the source and do not ask for a preset
dictionary. `Zlib.Decodes []` also accepts a stream with `FDICT` set and the Adler-32 of the empty
dictionary as `DICTID`, which `uncompress` refuses with `Z_DATA_ERROR`. -/
def CompressCompletes
    (program : BPtr → Option UInt64 → BPtr → UInt64 → M (Int32 × Option UInt64)) : Prop :=
  ∀ h dest c source n xs,
    Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    NoAllocationFailure h →
    Bytes h source n.toNat xs → Writable h dest c.toNat → Separate source n.toNat dest c.toNat →
    ¬ compressRejected dest (some c) source n →
    Api.compressBound n.toNat ≤ c.toNat →
    ∃ stored after out, C.run (program dest (some c) source n) h = .ok ((Z_OK, some stored), after) ∧
      stored.toNat ≤ Api.compressBound n.toNat ∧ out.length = stored.toNat ∧
      Bytes after dest stored.toNat out ∧ Zlib.Decodes [] out xs ∧ ¬ AsksDictionary out

/-- `compress` (the default level) completes with `compressBound` room. -/
def Goal.compress_completes : Prop :=
  CompressCompletes (fun d c s n => do
    let (rc, size) ← Zlib.Compress.compress d c s n
    pure (rc, some size))

/-- `compress_z` (the default level) completes with `compressBound` room. -/
def Goal.compress_z_completes : Prop :=
  CompressCompletes Zlib.Compress.compress_z

/-- **Completion of `inflate` on a default stream.** `encoded` is a complete default stream: the
output of a default deflate history that ended. A default decoder (`DefaultInflateTrace`) that has
read a prefix of it and has not ended, offered exactly the rest of the stream with room for the
rest of the input, on a heap where every allocation succeeds, returns `Z_STREAM_END` and writes
exactly the rest of the input. -/
def Goal.inflate_completes_default : Prop :=
  ∀ rd hd encoded ri hi decoded z flush,
    DefaultDeflateHistory rd hd encoded → encoded.result = Z_STREAM_END →
    DefaultInflateTrace ri hi decoded → decoded.finished = false →
    decoded.input <+: encoded.output →
    ri.get hi = some z → StreamBuffers hi ri → z.next_out ≠ .null →
    ZlibF.PlatformMemory.ByteObjectsFit hi → NoAllocationFailure hi →
    Bytes hi z.next_in z.avail_in.toNat (encoded.output.drop decoded.input.length) →
    encoded.input.length ≤ decoded.output.length + z.avail_out.toNat → OrdinaryFlush flush →
    ∃ after, C.run (Zlib.Inflate.inflate (some ri) flush) hi = .ok (Z_STREAM_END, after) ∧
      Bytes after z.next_out (encoded.input.length - decoded.output.length)
        (encoded.input.drop decoded.output.length)

/-- A continuation of `inflate` calls on the stream `S` that decodes to `D`, counted by the number
of calls; caller edits between calls. Each call runs on a heap within the object-size limit where
every allocation succeeds, has a non-null output pointer and positive room (or all of `D` is
written), offers a further piece of `S` (not empty unless all of `S` is consumed), and uses an
ordinary flush value. The chain stops at the end of the stream: a call after `Z_STREAM_END` is not
part of it. -/
inductive DefaultInflateChain (r : ZStreamRef) (S D : List UInt8) :
    Nat → Heap → DataLog → Heap → DataLog → Prop
  | refl (h log) : DefaultInflateChain r S D 0 h log h log
  | caller {k start initial h log after} :
      DefaultInflateChain r S D k start initial h log → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after →
      DefaultInflateChain r S D k start initial after log
  | step {k start initial h log after z flush rc input output used} :
      DefaultInflateChain r S D k start initial h log → log.finished = false →
      ZlibF.PlatformMemory.ByteObjectsFit h → NoAllocationFailure h →
      r.get h = some z → z.next_out ≠ .null → (z.avail_out ≠ 0 ∨ log.output = D) →
      Bytes h z.next_in z.avail_in.toNat input → log.input ++ input <+: S →
      (input ≠ [] ∨ log.input = S) → OrdinaryFlush flush →
      DataStep .inflate h after r flush rc input output used →
      DefaultInflateChain r S D (k + 1) start initial after (inflateLogStep log rc input output used)

/-- **The default decoder ends under every chunking.** `encoded` is a complete default stream. From
a default decoder that has read a prefix of it and has not ended, there is a number `N` such that
every continuation of `inflate` calls on the rest of the stream (`DefaultInflateChain`) has, while
unfinished, made at most `N` calls; and once it ends it has consumed the whole stream and written
exactly the encoder's input. -/
def Goal.inflate_chain_ends : Prop :=
  ∀ rd hd encoded ri hi decoded,
    DefaultDeflateHistory rd hd encoded → encoded.result = Z_STREAM_END →
    DefaultInflateTrace ri hi decoded → decoded.finished = false →
    decoded.input <+: encoded.output →
    ∃ N, ∀ k after final,
      DefaultInflateChain ri encoded.output encoded.input k hi decoded after final →
      (final.finished = false → k ≤ N) ∧
      (final.finished = true → final.input = encoded.output ∧ final.output = encoded.input)

/-- A continuation of `Z_FINISH` calls that each offer the not yet accepted part of one fixed input
`source` (accepted after `accepted`), with a non-null output pointer and positive output room,
counted by the number of calls; caller edits of the buffers between calls. Once the final block
is begun (`FINISH_STATE`) the caller offers no input (`zlib.h`). The chain stops at the end of the
stream: a call after `Z_STREAM_END` is not part of it. -/
inductive DefaultFinishChain (r : ZStreamRef) (accepted source : List UInt8) :
    Nat → Heap → DataLog → Heap → DataLog → Prop
  | refl (h log) : DefaultFinishChain r accepted source 0 h log h log
  | caller {k start initial h log after} :
      DefaultFinishChain r accepted source k start initial h log → Rebuffer h after r →
      DefaultFinishChain r accepted source k start initial after log
  | step {k start initial h log after z rc input output used} :
      DefaultFinishChain r accepted source k start initial h log → log.finished = false →
      r.get h = some z → z.next_out ≠ .null → 0 < z.avail_out.toNat →
      (∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
        d.status = FINISH_STATE → input = []) →
      input = source.drop (log.input.length - accepted.length) →
      DataStep .deflate h after r Z_FINISH rc input output used →
      DefaultFinishChain r accepted source (k + 1) start initial after
        (deflateLogStep log Z_FINISH rc input output used)

/-- **The default encoder ends under every finishing schedule.** After any default history (any
flush values, any chunking) that has not ended, with the remaining input `input` at the input
pointer: there is a number `N` such that every continuation by `Z_FINISH` calls with positive
room that offers the rest of `input` has, while unfinished, made at most `N` calls; and once it
ends it has accepted all of `input` and its whole output decodes to its whole input. No bound on
the room is needed. -/
def Goal.deflate_finish_ends : Prop :=
  ∀ r h log z input,
    DefaultDeflateHistory r h log → log.finished = false →
    r.get h = some z → StreamBuffers h r → Bytes h z.next_in z.avail_in.toNat input →
    (∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = []) →
    ∃ N, ∀ k after final, DefaultFinishChain r log.input input k h log after final →
      (final.finished = false → k ≤ N) ∧
      (final.finished = true → final.input = log.input ++ input ∧
        Zlib.Decodes [] final.output final.input)

/-- **The stream round trip, unconditional form.** The default encoder ends under every finishing
schedule, with an output that decodes to its input (`Goal.deflate_finish_ends`); and the default
decoder, given that output under every chunking, ends with exactly the encoder's input
(`Goal.inflate_chain_ends`). -/
def Goal.stream_roundtrip_total : Prop :=
  Goal.deflate_finish_ends ∧ Goal.inflate_chain_ends

/-- **`uncompress` completes on a complete stream.** The `n` source bytes are a zlib stream that
does not ask for a preset dictionary and decodes to `xs`, and the destination holds at least
`xs.length` bytes:
when every allocation succeeds, `uncompress` returns `Z_OK`, writes `xs` and stores its length. -/
def Goal.uncompress_completes : Prop :=
  ∀ h dest destLen source capacity n stream xs,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    NoAllocationFailure h →
    LengthCell h destLen capacity → destLen ≠ .null → source ≠ .null → dest ≠ .null →
    Bytes h source n.toNat stream → Writable h dest capacity.toNat →
    Separate source n.toNat dest capacity.toNat →
    Separate destLen 8 dest capacity.toNat → Separate destLen 8 source n.toNat →
    Zlib.Decodes [] stream xs → ¬ AsksDictionary stream → xs.length ≤ capacity.toNat →
    ∃ after, C.run (Zlib.Uncompr.uncompress dest destLen source n) h = .ok (Z_OK, after) ∧
      Bytes after dest xs.length xs ∧ LengthCell after destLen (UInt64.ofNat xs.length)

/-- **`uncompress(compress(x)) = x`.** When every allocation succeeds, `compress` with
`compressBound` room returns `Z_OK` and stores the length `m` it wrote; the `m` bytes it wrote,
given to `uncompress` on any heap where every allocation succeeds, with room for the source, give
back the source and its length, with `Z_OK`. -/
def Goal.compress_uncompress_roundtrip : Prop :=
  ∀ h dest c source n xs,
    Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    NoAllocationFailure h →
    Bytes h source n.toNat xs → Writable h dest c.toNat → Separate source n.toNat dest c.toNat →
    ¬ compressRejected dest (some c) source n →
    Api.compressBound n.toNat ≤ c.toNat →
    ∃ stored after out, C.run (Zlib.Compress.compress dest (some c) source n) h = .ok ((Z_OK, stored), after) ∧
      out.length = stored.toNat ∧ Bytes after dest stored.toNat out ∧
      ∀ h₂ dest₂ destLen₂ source₂ capacity₂,
        Fresh h₂ → Zlib.Inflate.Spec.Uniq h₂ → LibraryGlobals h₂ →
        ZlibF.PlatformMemory.ByteObjectsFit h₂ → NoAllocationFailure h₂ →
        LengthCell h₂ destLen₂ capacity₂ → destLen₂ ≠ .null → source₂ ≠ .null → dest₂ ≠ .null →
        Bytes h₂ source₂ stored.toNat out → Writable h₂ dest₂ capacity₂.toNat →
        Separate source₂ stored.toNat dest₂ capacity₂.toNat →
        Separate destLen₂ 8 dest₂ capacity₂.toNat → Separate destLen₂ 8 source₂ stored.toNat →
        n.toNat ≤ capacity₂.toNat →
        ∃ after₂, C.run (Zlib.Uncompr.uncompress dest₂ destLen₂ source₂ stored) h₂ = .ok (Z_OK, after₂) ∧
          Bytes after₂ dest₂ n.toNat xs ∧ LengthCell after₂ destLen₂ n

/-- **Non-vacuity of `Goal.compress_uncompress_roundtrip`.** There is a heap, a destination and a
non-empty source on which every premise of the `compress` half holds; and for every output `out`
that `compress` can produce there (`stored` bytes, at most `compressBound n`), a second heap,
destination, length cell and source holding `out` on which every premise of the `uncompress` half
holds. -/
def Goal.compress_uncompress_roundtrip_witness : Prop :=
  ∃ h dest c source n xs,
    Fresh h ∧ Zlib.Deflate.Spec.Uniq h ∧ LibraryGlobals h ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧
    NoAllocationFailure h ∧
    xs ≠ [] ∧
    Bytes h source n.toNat xs ∧ Writable h dest c.toNat ∧ Separate source n.toNat dest c.toNat ∧
    ¬ compressRejected dest (some c) source n ∧ Api.compressBound n.toNat ≤ c.toNat ∧
    ∀ (stored : UInt64) (out : List UInt8), stored.toNat ≤ Api.compressBound n.toNat →
      out.length = stored.toNat →
      ∃ h₂ dest₂ destLen₂ source₂ capacity₂,
        Fresh h₂ ∧ Zlib.Inflate.Spec.Uniq h₂ ∧ LibraryGlobals h₂ ∧
        ZlibF.PlatformMemory.ByteObjectsFit h₂ ∧ NoAllocationFailure h₂ ∧
        LengthCell h₂ destLen₂ capacity₂ ∧ destLen₂ ≠ .null ∧ source₂ ≠ .null ∧ dest₂ ≠ .null ∧
        Bytes h₂ source₂ stored.toNat out ∧ Writable h₂ dest₂ capacity₂.toNat ∧
        Separate source₂ stored.toNat dest₂ capacity₂.toNat ∧
        Separate destLen₂ 8 dest₂ capacity₂.toNat ∧ Separate destLen₂ 8 source₂ stored.toNat ∧
        n.toNat ≤ capacity₂.toNat

end ZlibF.Spec.Public
