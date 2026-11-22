import ZlibF.Spec.Common.Sequences

/-!
# Streams: one safety goal per inflate and deflate function

Safety goals (`docs/en/design/safety-functional-split.md`, "Two goals per public function"). Each goal is clause 2 of `StreamSequenceSafety`
(one more call on a reachable stream) specialised to the `Call` constructor of one function, or
clause 3 for `inflateEnd` and `deflateEnd`. Each can fail: the executed call must return `.ok`, keep
`StreamInvariant`, write only its frame and change the live blocks as the allocation ledger says.
None is true by definition.

The reachable set is non-empty: `Goal.inflate_initialisation_domain` and
`Goal.deflate_initialisation_domain` give a reachable stream from a concrete heap. Each goal also
states the function's refusal of a `NULL` or inconsistent stream (`RefusedInflate`,
`RefusedDeflate`); the proofs are in `ZlibF/Proof/public-stream-call-safety.lean`.
`Goal.inflate_refusal` and `Goal.deflate_refusal` stay. The premise `StreamArguments` is the
caller's part of `zlib.h` for that call (buffers, dictionary and header regions, and zlib.h's
ordering rules); it is `True` for calls with no caller memory.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec

/-- The conclusion of clause 2 of `StreamSequenceSafety` for one call on stream `r`, written out
unchanged: the call returns without a fault, keeps the stream invariant, writes only the stream's
blocks, its record, a gzip header record it was given and the declared caller regions, and changes
the live blocks exactly as the allocation ledger says. -/
def StreamCallSafe (kind : StreamKind) (h : Heap) (r : ZStreamRef) (call : Call) : Prop :=
  ∃ value after, call.execute default h = .ok ((value, default), after) ∧
    StreamInvariant kind after r ∧
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
      (StreamWriteRegions h r call) ∧
    LiveChange h after
      (fun b => StreamOwned after r b ∧ ¬ h.live b)
      (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b)

/-- The premises of clause 2 of `StreamSequenceSafety` for one call on stream `r`, except
`StreamOperation`, which each goal below satisfies by its form (`strm = r`, matching kind). -/
def StreamCallDomain (kind : StreamKind) (h : Heap) (r : ZStreamRef) (call : Call) : Prop :=
  StreamReachable kind h r ∧ ZlibF.PlatformMemory.ByteObjectsFit h ∧ StreamArguments h r call

/-- `int inflate(z_streamp strm, int flush)`.
**Safety of `inflate`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR`; on a `Fresh` heap it writes no block that was live and leaves the live blocks as
they were (the local array it makes is freed); and on every reachable inflate stream, with the
caller's arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflate_safety : Prop :=
  (∀ h p flush, Fresh h → RefusedInflate h p →
    ∃ after, C.run (Zlib.Inflate.inflate p flush) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧ LiveChange h after (fun _ => False) (fun _ => False)) ∧
  (∀ h r flush,
     StreamCallDomain .inflate h r (.inflate (some r) flush) →
     StreamCallSafe .inflate h r (.inflate (some r) flush))

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`.
**Safety of `inflateSetDictionary`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused
with `Z_STREAM_ERROR` and nothing changed; and on every reachable inflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateSetDictionary_safety : Prop :=
  (∀ h p dictionary dictLength, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateSetDictionary p dictionary dictLength) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r dictionary dictLength,
     StreamCallDomain .inflate h r (.inflateSetDictionary (some r) dictionary dictLength) →
     StreamCallSafe .inflate h r (.inflateSetDictionary (some r) dictionary dictLength))

/-- `int inflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`.
**Safety of `inflateGetDictionary`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused
with `Z_STREAM_ERROR` and nothing changed; and on every reachable inflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateGetDictionary_safety : Prop :=
  (∀ h p dictionary dictLength, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateGetDictionary p dictionary dictLength) h =
      .ok ((Z_STREAM_ERROR, dictLength), h)) ∧
  (∀ h r dictionary dictLength,
     StreamCallDomain .inflate h r (.inflateGetDictionary (some r) dictionary dictLength) →
     StreamCallSafe .inflate h r (.inflateGetDictionary (some r) dictionary dictLength))

/-- `int inflateSync(z_streamp strm)`.
**Safety of `inflateSync`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR`; on a `Fresh` heap it writes no block that was live and leaves the live blocks as
they were (the local array it makes is freed); and on every reachable inflate stream, with the
caller's arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateSync_safety : Prop :=
  (∀ h p, Fresh h → RefusedInflate h p →
    ∃ after, C.run (Zlib.Inflate.inflateSync p) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧ LiveChange h after (fun _ => False) (fun _ => False)) ∧
  (∀ h r,
     StreamCallDomain .inflate h r (.inflateSync (some r)) →
     StreamCallSafe .inflate h r (.inflateSync (some r)))

/-- `int inflateReset(z_streamp strm)`.
**Safety of `inflateReset`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable inflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateReset_safety : Prop :=
  (∀ h p, RefusedInflate h p → C.run (Zlib.Inflate.inflateReset p) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r,
     StreamCallDomain .inflate h r (.inflateReset (some r)) →
     StreamCallSafe .inflate h r (.inflateReset (some r)))

/-- `int inflateReset2(z_streamp strm, int windowBits)`.
**Safety of `inflateReset2`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable inflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateReset2_safety : Prop :=
  (∀ h p windowBits, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateReset2 p windowBits) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r windowBits,
     StreamCallDomain .inflate h r (.inflateReset2 (some r) windowBits) →
     StreamCallSafe .inflate h r (.inflateReset2 (some r) windowBits))

/-- `int inflatePrime(z_streamp strm, int bits, int value)`.
**Safety of `inflatePrime`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable inflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflatePrime_safety : Prop :=
  (∀ h p bits value, RefusedInflate h p →
    C.run (Zlib.Inflate.inflatePrime p bits value) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r bits value,
     StreamCallDomain .inflate h r (.inflatePrime (some r) bits value) →
     StreamCallSafe .inflate h r (.inflatePrime (some r) bits value))

/-- `long inflateMark(z_streamp strm)`.
**Safety of `inflateMark`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
-65536 and nothing changed; and on every reachable inflate stream, with the caller's arguments as
`zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateMark_safety : Prop :=
  (∀ h p, RefusedInflate h p → C.run (Zlib.Inflate.inflateMark p) h = .ok ((-65536), h)) ∧
  (∀ h r,
     StreamCallDomain .inflate h r (.inflateMark (some r)) →
     StreamCallSafe .inflate h r (.inflateMark (some r)))

/-- `int inflateGetHeader(z_streamp strm, gz_headerp head)`.
**Safety of `inflateGetHeader`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable inflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.inflateGetHeader_safety : Prop :=
  (∀ h p head, RefusedInflate h p →
    C.run (Zlib.Inflate.inflateGetHeader p head) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r head,
     StreamCallDomain .inflate h r (.inflateGetHeader (some r) head) →
     StreamCallSafe .inflate h r (.inflateGetHeader (some r) head))

/-- `int deflate(z_streamp strm, int flush)`.
**Safety of `deflate`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflate_safety : Prop :=
  (∀ h p flush, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflate p flush) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r flush,
     StreamCallDomain .deflate h r (.deflate (some r) flush) →
     StreamCallSafe .deflate h r (.deflate (some r) flush))

/-- `int deflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`.
**Safety of `deflateSetDictionary`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused
with `Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateSetDictionary_safety : Prop :=
  (∀ h p dictionary dictLength, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateSetDictionary p dictionary dictLength) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r dictionary dictLength,
     StreamCallDomain .deflate h r (.deflateSetDictionary (some r) dictionary dictLength) →
     StreamCallSafe .deflate h r (.deflateSetDictionary (some r) dictionary dictLength))

/-- `int deflateGetDictionary(z_streamp strm, Bytef *dictionary, uInt *dictLength)`.
**Safety of `deflateGetDictionary`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused
with `Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateGetDictionary_safety : Prop :=
  (∀ h p dictionary hasDictLength, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateGetDictionary p dictionary hasDictLength) h =
      .ok ((Z_STREAM_ERROR, none), h)) ∧
  (∀ h r dictionary hasDictLength,
     StreamCallDomain .deflate h r (.deflateGetDictionary (some r) dictionary hasDictLength) →
     StreamCallSafe .deflate h r (.deflateGetDictionary (some r) dictionary hasDictLength))

/-- `int deflateReset(z_streamp strm)`.
**Safety of `deflateReset`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateReset_safety : Prop :=
  (∀ h p, RefusedDeflate h p → C.run (Zlib.Deflate.deflateReset p) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r,
     StreamCallDomain .deflate h r (.deflateReset (some r)) →
     StreamCallSafe .deflate h r (.deflateReset (some r)))

/-- `int deflateParams(z_streamp strm, int level, int strategy)`.
**Safety of `deflateParams`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateParams_safety : Prop :=
  (∀ h p level strategy, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateParams p level strategy) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r level strategy,
     StreamCallDomain .deflate h r (.deflateParams (some r) level strategy) →
     StreamCallSafe .deflate h r (.deflateParams (some r) level strategy))

/-- `int deflateTune(z_streamp strm, int good_length, int max_lazy, int nice_length, int max_chain)`.
**Safety of `deflateTune`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateTune_safety : Prop :=
  (∀ h p good_length max_lazy nice_length max_chain, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateTune p good_length max_lazy nice_length max_chain) h =
      .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r good_length max_lazy nice_length max_chain,
     StreamCallDomain .deflate h r (.deflateTune (some r) good_length max_lazy nice_length max_chain) →
     StreamCallSafe .deflate h r (.deflateTune (some r) good_length max_lazy nice_length max_chain))

/-- `uLong deflateBound(z_streamp strm, uLong sourceLen)`.
**Safety of `deflateBound`**: a `NULL` or inconsistent stream (`RefusedDeflate`) gets the
conservative bound of a `NULL` stream (not an error, as in the C) and nothing changes; and on every
reachable deflate stream, with the caller's arguments as `zlib.h` asks, the call is safe
(`StreamCallSafe`). -/
def Goal.deflateBound_safety : Prop :=
  (∀ h p n, RefusedDeflate h p → ∃ v, C.run (Zlib.Deflate.deflateBound p n) h = .ok (v, h) ∧
    C.run (Zlib.Deflate.deflateBound none n) h = .ok (v, h)) ∧
  (∀ h r sourceLen,
     StreamCallDomain .deflate h r (.deflateBound (some r) sourceLen) →
     StreamCallSafe .deflate h r (.deflateBound (some r) sourceLen))

/-- `z_size_t deflateBound_z(z_streamp strm, z_size_t sourceLen)`.
**Safety of `deflateBound_z`**: a `NULL` or inconsistent stream (`RefusedDeflate`) gets the
conservative bound of a `NULL` stream (not an error, as in the C) and nothing changes; and on every
reachable deflate stream, with the caller's arguments as `zlib.h` asks, the call is safe
(`StreamCallSafe`). -/
def Goal.deflateBound_z_safety : Prop :=
  (∀ h p n, RefusedDeflate h p → ∃ v, C.run (Zlib.Deflate.deflateBound_z p n) h = .ok (v, h) ∧
    C.run (Zlib.Deflate.deflateBound_z none n) h = .ok (v, h)) ∧
  (∀ h r sourceLen,
     StreamCallDomain .deflate h r (.deflateBound_z (some r) sourceLen) →
     StreamCallSafe .deflate h r (.deflateBound_z (some r) sourceLen))

/-- `int deflatePending(z_streamp strm, unsigned *pending, int *bits)`.
**Safety of `deflatePending`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflatePending_safety : Prop :=
  (∀ h p hasPending hasBits, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflatePending p hasPending hasBits) h =
      .ok ((Z_STREAM_ERROR, none, none), h)) ∧
  (∀ h r hasPending hasBits,
     StreamCallDomain .deflate h r (.deflatePending (some r) hasPending hasBits) →
     StreamCallSafe .deflate h r (.deflatePending (some r) hasPending hasBits))

/-- `int deflateUsed(z_streamp strm, int *bits)`.
**Safety of `deflateUsed`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateUsed_safety : Prop :=
  (∀ h p hasBits, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateUsed p hasBits) h = .ok ((Z_STREAM_ERROR, none), h)) ∧
  (∀ h r hasBits,
     StreamCallDomain .deflate h r (.deflateUsed (some r) hasBits) →
     StreamCallSafe .deflate h r (.deflateUsed (some r) hasBits))

/-- `int deflatePrime(z_streamp strm, int bits, int value)`.
**Safety of `deflatePrime`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflatePrime_safety : Prop :=
  (∀ h p bits value, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflatePrime p bits value) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r bits value,
     StreamCallDomain .deflate h r (.deflatePrime (some r) bits value) →
     StreamCallSafe .deflate h r (.deflatePrime (some r) bits value))

/-- `int deflateSetHeader(z_streamp strm, gz_headerp head)`.
**Safety of `deflateSetHeader`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and on every reachable deflate stream, with the caller's
arguments as `zlib.h` asks, the call is safe (`StreamCallSafe`). -/
def Goal.deflateSetHeader_safety : Prop :=
  (∀ h p head, RefusedDeflate h p →
    C.run (Zlib.Deflate.deflateSetHeader p head) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r head,
     StreamCallDomain .deflate h r (.deflateSetHeader (some r) head) →
     StreamCallSafe .deflate h r (.deflateSetHeader (some r) head))

/-- `int inflateEnd(z_streamp strm)`.
**Safety of `inflateEnd`**: a `NULL` or inconsistent stream (`RefusedInflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and, by clause 3 of `StreamSequenceSafety .inflate`: on every
reachable inflate stream the call returns `Z_OK` without a fault, clears the state pointer, writes
only the stream record and its blocks, and frees exactly the blocks the stream owns (no leak). -/
def Goal.inflateEnd_safety : Prop :=
  (∀ h p, RefusedInflate h p → C.run (Zlib.Inflate.inflateEnd p) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r, StreamReachable .inflate h r →
     ∃ rc after z, C.run (Zlib.Inflate.inflateEnd (some r)) h = .ok (rc, after) ∧ rc = Z_OK ∧
       r.get after = some z ∧ z.state = none ∧
       Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
       LiveChange h after (fun _ => False) (StreamOwned h r))

/-- `int deflateEnd(z_streamp strm)`.
**Safety of `deflateEnd`**: a `NULL` or inconsistent stream (`RefusedDeflate`) is refused with
`Z_STREAM_ERROR` and nothing changed; and, by clause 3 of `StreamSequenceSafety .deflate`: on every
reachable deflate stream the call returns `Z_OK`, or `Z_DATA_ERROR` when the stream was freed
prematurely, without a fault; it clears the state pointer, writes only the stream record and its
blocks, and frees exactly the blocks the stream owns (no leak). -/
def Goal.deflateEnd_safety : Prop :=
  (∀ h p, RefusedDeflate h p → C.run (Zlib.Deflate.deflateEnd p) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r, StreamReachable .deflate h r →
     ∃ rc after z, C.run (Zlib.Deflate.deflateEnd (some r)) h = .ok (rc, after) ∧
       (rc = Z_OK ∨ rc = Z_DATA_ERROR) ∧
       r.get after = some z ∧ z.state = none ∧
       Frame h after (fun b => StreamRoot r b ∨ StreamOwned h r b) ∧
       LiveChange h after (fun _ => False) (StreamOwned h r))

end ZlibF.Spec.Public
