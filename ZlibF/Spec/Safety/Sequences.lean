import ZlibF.Spec.Common.Sequences

/-!
# Sequences: safety goals

The split into safety and functional modules: `docs/en/design/safety-functional-split.md`. The
namespace is `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs ZlibF.Spec

/-- **Safety of every permitted deflate call sequence** (the safety half of
`Goal.deflate_sequence`): every reachable stream satisfies the stream invariant, and one more
permitted call returns without a fault, keeps the invariant, writes only the stream's own blocks,
the stream record and the declared caller regions, and changes the live blocks exactly as the
allocation ledger says (no leak). The functional clauses of `Goal.deflate_sequence` are not planned. -/
def Goal.deflate_sequence_safety : Prop := StreamSequenceSafety .deflate

/-- **Safety of every permitted inflate call sequence** (the safety half of
`Goal.inflate_sequence`): every reachable stream satisfies the stream invariant, and one more
permitted call returns without a fault, keeps the invariant, writes only the stream's own blocks,
the stream record, the gzip header record and the declared caller regions, and changes the live
blocks exactly as the allocation ledger says (no leak); `inflateEnd` frees every block the stream
owns. The functional clauses of `Goal.inflate_sequence` are not planned (`docs/en/progress.md`,
"Not planned"). -/
def Goal.inflate_sequence_safety : Prop := StreamSequenceSafety .inflate

/-- **Safety of every permitted callback-decoder sequence** (the safety half of
`Goal.inflate_back_sequence`). A null stream is refused. Every reachable history leaves a valid
state over the caller's window. One more `inflateBack` call, for every caller protocol whose total
input is below `2^48` bytes (the runtime bounds every loop by `2^64` iterations; `docs/en/deviations.md`),
returns without a fault with one of its three results, keeps the state valid over the same window,
changes only the stream record, the state record, the callback's own blocks and the window slice,
and leaves the live blocks outside the callback's own unchanged (no leak). `inflateBackEnd` frees the
state. The histories are those of `BackSafeReachable`: the window is a slice of a heap byte block,
every byte object has fewer than `2^63` bytes on the heap of each call and after each call-back
step (`BackPlatform`), and every input chunk lies in a heap byte block (`BackFirstChunk`,
`BackPlatform`); `docs/en/deviations.md` lists these premises. The decoding clauses of
`Goal.inflateBack` (what reaches `out`, `Decodes`) are not planned (`docs/en/progress.md`, "Not planned"). -/
def Goal.inflate_back_sequence_safety : Prop :=
  (∀ h input inDesc output outDesc,
    C.run (Zlib.Infback.inflateBack none input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i window n, BackSafeReachable h r i window n →
    ∃ z s, BackValid h r i z s ∧ s.window = window ∧ s.wsize.toNat = n) ∧
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
      (∀ b, ¬ protocol.own b → (after.live b ↔ h.live b))) ∧
  (∀ h r i window n, BackSafeReachable h r i window n →
    ∃ after z, C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some z ∧ z.state = none ∧
      Frame h after (fun b => StreamRoot r b ∨ b = i) ∧
      LiveChange h after (fun _ => False) (fun b => b = i))

end ZlibF.Spec.Public
