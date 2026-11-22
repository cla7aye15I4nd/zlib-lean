import ZlibF.Spec.Common.Domains
import ZlibF.Spec.Common.Sequences

/-!
# Initialisation: one safety goal per inflate and deflate init function

Safety goals (`docs/en/design/safety-functional-split.md`, "Two goals per public function"). The domain is `InitArguments`: every call that
`zlib.h` allows. The stream pointer is `NULL` or a readable record with the default allocator (or
`NULL` allocator fields, which the call fills in); every other field of the record, `state`
included, may hold any value, since init overwrites it without reading it. The version pointer is
`NULL` or readable for its first byte, which may be any byte. `stream_size` is any value. The heap
is well formed. No history is needed. The goals can fail: the call must return without a fault;
on a `NULL` stream it returns `Z_VERSION_ERROR` or `Z_STREAM_ERROR` with the heap unchanged;
otherwise it writes only the stream record and fresh blocks, and on `Z_OK` leaves a reachable
stream whose new blocks it owns, while on any other code it leaves the live blocks as they were.
`Goal.inflate_initialisation_domain` and `Goal.deflate_initialisation_domain` show that the `Z_OK`
branch is non-empty.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec

/-- The outcome of an init call on stream `r` from `h` to `after` with code `rc`: only the stream
record and fresh blocks are written; on `Z_OK` the stream is reachable and every new live block
is owned by it (no leak); on any other code the live blocks are unchanged. -/
def InitCallSafe (kind : StreamKind) (h after : Heap) (r : ZStreamRef) (rc : Int32) : Prop :=
  Frame h after (StreamRoot r) ∧
  ((rc = Z_OK ∧ StreamReachable kind after r ∧
      ∃ created : Nat → Prop, (∀ b, created b → StreamOwned after r b) ∧
        LiveChange h after created (fun _ => False)) ∨
   (rc ≠ Z_OK ∧ LiveChange h after (fun _ => False) (fun _ => False)))

/-- The arguments of an init call that `zlib.h` allows, on a well-formed heap. The stream is `NULL`
or a readable record whose `zalloc` and `zfree` are each `NULL` or the default function
(`DefaultOrNull`); its other fields, `state` included, are arbitrary. The version is `NULL` or
readable for one byte, with any value. -/
def InitArguments (h : Heap) (strm : ZStreamPtr) (version : BPtr) : Prop :=
  Fresh h ∧ Zlib.Inflate.Spec.Uniq h ∧ LibraryGlobals h ∧ (∃ head, VersionValue h version head) ∧
  ∀ r, strm = some r → ∃ z, r.get h = some z ∧ DefaultOrNull z

/-- The outcome of an init call on `strm`: a `NULL` stream is refused with the version or stream
error and the heap unchanged; a stream record gets `InitCallSafe`. -/
def InitResultSafe (kind : StreamKind) (h after : Heap) (strm : ZStreamPtr) (rc : Int32) : Prop :=
  match strm with
  | none => (rc = Z_VERSION_ERROR ∨ rc = Z_STREAM_ERROR) ∧ after = h
  | some r => InitCallSafe kind h after r rc

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
**Safety of `inflateInit2_`** (macro `inflateInit2`): for every `windowBits`, every
`stream_size` and every allocation outcome, on `InitArguments` the call is safe
(`InitResultSafe`). -/
def Goal.inflateInit2__safety : Prop :=
  ∀ h strm version size wb, InitArguments h strm version →
    ∃ rc after, C.run (Zlib.Inflate.inflateInit2_ strm wb version size) h = .ok (rc, after) ∧
      InitResultSafe .inflate h after strm rc

/-- `int inflateInit_(z_streamp strm, const char *version, int stream_size)`.
**Safety of `inflateInit_`** (macro `inflateInit`): as `Goal.inflateInit2__safety` at window
bits 15. -/
def Goal.inflateInit__safety : Prop :=
  ∀ h strm version size, InitArguments h strm version →
    ∃ rc after, C.run (Zlib.Inflate.inflateInit_ strm version size) h = .ok (rc, after) ∧
      InitResultSafe .inflate h after strm rc

/-- `int deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel,
int strategy, const char *version, int stream_size)`.
**Safety of `deflateInit2_`** (macro `deflateInit2`): for every level, method, window, memory
level and strategy, every `stream_size` and every allocation outcome, on `InitArguments` the
call is safe (`InitResultSafe`). -/
def Goal.deflateInit2__safety : Prop :=
  ∀ h strm version size level method wb mem strategy, InitArguments h strm version →
    ∃ rc after, C.run (Zlib.Deflate.deflateInit2_ strm level method wb mem strategy version size) h =
      .ok (rc, after) ∧ InitResultSafe .deflate h after strm rc

/-- `int deflateInit_(z_streamp strm, int level, const char *version, int stream_size)`.
**Safety of `deflateInit_`** (macro `deflateInit`): as `Goal.deflateInit2__safety` with the
default method, window, memory level and strategy, for every level. -/
def Goal.deflateInit__safety : Prop :=
  ∀ h strm version size level, InitArguments h strm version →
    ∃ rc after, C.run (Zlib.Deflate.deflateInit_ strm level version size) h = .ok (rc, after) ∧
      InitResultSafe .deflate h after strm rc

end ZlibF.Spec.Public
