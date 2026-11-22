import ZlibF.Spec.Common.Sequences
import ZlibF.Spec.Common.Domains
import ZlibF.Spec.Safety.Initialisation

/-!
# Callback decoder: one safety goal per function

Safety goals (`docs/en/design/safety-functional-split.md`, "Two goals per public function"). `Goal.inflateBack_safety` and
`Goal.inflateBackEnd_safety` restrict `Goal.inflate_back_sequence_safety` to one function: the
refusal of a null stream and one more call on a history of `BackSafeReachable` (clauses 1 and 3),
and the end call (clause 4). Each also has the other refusals `zlib.h` allows for that function: a
stream record with a `NULL` state, and for `inflateBackEnd` a `NULL` `zfree`.
`Goal.inflateBackInit__safety` is the safety of the init call on `InitArguments`, every call that
`zlib.h` allows, as `Goal.inflateInit2__safety` is for `inflateInit2_`. The histories are non-empty
(`Goal.inflate_back_initialisation_domain`).
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec
set_option autoImplicit false

/-- `int inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window, const char *version, int stream_size)`.
**Safety of `inflateBackInit_`** (macro `inflateBackInit`): on `InitArguments`, for every
`windowBits`, every `stream_size` and every allocation outcome, the call returns without a fault.
zlib.h requires a window of `2^windowBits` bytes, so where the bits are in range and the window is
not `NULL` it is writable for that length. A `NULL` stream is refused with `Z_VERSION_ERROR` or
`Z_STREAM_ERROR` and the heap unchanged. Otherwise the call writes only the stream record and fresh
blocks; on `Z_OK` the stream holds a valid callback-decoder state over the caller's window, and only
the new state block is new; on any other code the live blocks are unchanged. -/
def Goal.inflateBackInit__safety : Prop :=
  ∀ h strm version size wb window, InitArguments h strm version →
    (window ≠ .null → 8 ≤ wb.toInt → wb.toInt ≤ 15 → Writable h window (2 ^ wb.toInt.toNat)) →
    ∃ rc after, C.run (Zlib.Infback.inflateBackInit_ strm wb window version size) h = .ok (rc, after) ∧
      match strm with
      | none => (rc = Z_VERSION_ERROR ∨ rc = Z_STREAM_ERROR) ∧ after = h
      | some r => Frame h after (StreamRoot r) ∧
          ((rc = Z_OK ∧ (∃ z s, BackValid after r h.nextBlk z s ∧ s.window = window) ∧
              LiveChange h after (fun b => b = h.nextBlk) (fun _ => False)) ∨
           (rc ≠ Z_OK ∧ LiveChange h after (fun _ => False) (fun _ => False)))

/-- `int inflateBack(z_streamp strm, in_func in, void FAR *in_desc, out_func out, void FAR *out_desc)`.
**Safety of `inflateBack`**: a `NULL` stream, and a stream record whose state is `NULL`, are refused
with `Z_STREAM_ERROR` and nothing changed; one more call on a history of `BackSafeReachable` returns
without a fault, keeps the state valid over the same window, and changes only its frame (clauses 1
and 3 of `Goal.inflate_back_sequence_safety`). -/
def Goal.inflateBack_safety : Prop :=
  (∀ h input inDesc output outDesc,
    C.run (Zlib.Infback.inflateBack none input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z input inDesc output outDesc, r.get h = some z → z.state = none →
    C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i window n z s input inDesc output outDesc
      (protocol : CallbackProtocol r i window n input inDesc output outDesc) first,
    BackSafeReachable h r i window n → BackValid h r i z s →
    (if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first) →
    Separate z.next_in first.length window n →
    protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first } →
    protocol.inputBound < 2 ^ 48 →
    ZlibF.PlatformMemory.ByteObjectsFit h → BackPlatform protocol → BackFirstChunk z first →
    ∃ rc after z' s' log,
      C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) ∧
      BackValid after r i z' s' ∧ s'.window = window ∧ s'.wsize = s.wsize ∧
      protocol.invariant after log ∧
      (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
      CallbackFrame protocol.own h after r i window n ∧
      (∀ b, ¬ protocol.own b → (after.live b ↔ h.live b)))

/-- `int inflateBackEnd(z_streamp strm)`.
**Safety of `inflateBackEnd`**: a `NULL` stream, and a stream record whose state or `zfree` is
`NULL`, are refused with `Z_STREAM_ERROR` and nothing changed (clauses 1 and 2 of
`Goal.inflateBackEnd`); on a history of `BackSafeReachable` it returns `Z_OK`, clears the state
field, and frees exactly the state block (clause 4 of `Goal.inflate_back_sequence_safety`). -/
def Goal.inflateBackEnd_safety : Prop :=
  (∀ h, C.run (Zlib.Infback.inflateBackEnd none) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z, r.get h = some z → z.state = none ∨ z.zfree = .null →
    C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_STREAM_ERROR, h)) ∧
  ∀ h r i window n, BackSafeReachable h r i window n →
    ∃ after z, C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ b = i) ∧
      LiveChange h after (fun _ => False) (fun b => b = i)

end ZlibF.Spec.Public
