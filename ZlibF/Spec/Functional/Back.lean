import ZlibF.Spec.Common.Back
import ZlibF.Spec.Functional.Format.Deflate

/-!
# The callback decoder: the functional goal of `inflateBack`

`Goal.inflateBack` (`docs/en/design/safety-functional-split.md`): it states that the delivered output
decodes the input (`Deflate.Decodes`). The namespace is `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.Infback ZlibF.Spec

/-- `int inflateBack(z_streamp strm, in_func in, void *in_desc, out_func out, void *out_desc)`.
For every finite, returning caller protocol, decode raw DEFLATE and deliver the chunks through
that actual output callback. The protocol's observation relation records the bytes delivered.
No allocation or free by the library is charged to the caller's callbacks. -/
def Goal.inflateBack : Prop :=
  (∀ h input inDesc output outDesc,
    C.run (Zlib.Infback.inflateBack none input inDesc output outDesc) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i z s input inDesc output outDesc
      (protocol : CallbackProtocol r i s.window s.wsize.toNat input inDesc output outDesc) first,
    BackValid h r i z s →
    (if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first) →
    Separate z.next_in first.length s.window s.wsize.toNat →
    protocol.invariant h { supplied := first, chunks := [], active := z.next_in, held := first } →
    ∃ rc after z' s' log unused consumed,
      C.run (Zlib.Infback.inflateBack (some r) input inDesc output outDesc) h = .ok (rc, after) ∧
      BackValid after r i z' s' ∧ s'.window = s.window ∧ s'.wsize = s.wsize ∧
      protocol.invariant after log ∧
      (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧
      consumed ++ unused = log.supplied ∧ unused.length = z'.avail_in.toNat ∧
      unused <:+ log.held ∧
      (log.exhausted = true → z'.next_in = .null ∧ unused = []) ∧
      (log.exhausted = false → z'.next_in = advance log.active (log.held.length - unused.length)) ∧
      (∀ chunk, chunk ∈ log.chunks → chunk ≠ [] ∧ chunk.length ≤ s.wsize.toNat) ∧
      (rc = Z_STREAM_END → Deflate.Decodes [] consumed log.chunks.flatten ∧ log.failed = false) ∧
      (rc = Z_BUF_ERROR → log.exhausted = true ∨ log.failed = true) ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out ∧ z'.adler = z.adler ∧
      CallbackFrame protocol.own h after r i s.window s.wsize.toNat ∧
      (∀ b, ¬ protocol.own b → (after.live b ↔ h.live b)))

/-- `int inflateBackInit_(z_streamp strm, int windowBits, unsigned char *window,
const char *version, int stream_size)`.
The caller retains the window. Only the state record is allocated; its other integer fields
remain arbitrary. Refusal precedes allocation, and allocation failure retains the old state field. -/
def Goal.inflateBackInit_ : Prop :=
  (∀ h p wb window version head size, VersionValue h version head →
    (head ≠ some 49 ∨ size ≠ 112) →
    C.run (Zlib.Infback.inflateBackInit_ p wb window version size) h = .ok (Z_VERSION_ERROR, h)) ∧
  (∀ h p wb window version, VersionValue h version (some 49) →
    (p = none ∨ window = .null ∨ wb.toInt < 8 ∨ 15 < wb.toInt) →
    C.run (Zlib.Infback.inflateBackInit_ p wb window version 112) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z wb window version,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → r.get h = some z →
    DefaultOrNull z → VersionValue h version (some 49) →
    8 ≤ wb.toInt → wb.toInt ≤ 15 → window ≠ .null → Writable h window (2 ^ wb.toInt.toNat) →
    ∃ rc after,
      C.run (Zlib.Infback.inflateBackInit_ (some r) wb window version 112) h = .ok (rc, after) ∧
      after.nalloc = h.nalloc + 1 ∧
      if h.allocOk h.nalloc = false then
        rc = Z_MEM_ERROR ∧ SameObjects (r.put h (preparedStream z)) after
      else rc = Z_OK ∧
        let z' := { preparedStream z with state := some (.inflate h.nextBlk) }
        let s := backInitialState (h.garbage h.nalloc) window wb
        BackValid after r h.nextBlk z' s ∧
        Frame h after (StreamRoot r) ∧
        LiveChange h after (fun b => b = h.nextBlk) (fun _ => False))

/-- `int inflateBackEnd(z_streamp strm)`.
Free only the state record. The caller's window is retained, even when it is a slice of another object. -/
def Goal.inflateBackEnd : Prop :=
  (∀ h, C.run (Zlib.Infback.inflateBackEnd none) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r z, r.get h = some z → z.state = none ∨ z.zfree = .null →
    C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_STREAM_ERROR, h)) ∧
  (∀ h r i z s, BackValid h r i z s →
    ∃ after, C.run (Zlib.Infback.inflateBackEnd (some r)) h = .ok (Z_OK, after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (fun b => b = i) ∧
      Frame h after (fun b => StreamRoot r b ∨ b = i) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk)

end ZlibF.Spec.Public
