import ZlibF.Spec.Common.GzState

namespace ZlibF.Spec.Public
open C Zlib.Infback ZlibF.Spec

def BackValid (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : InflateState) : Prop :=
  r.get h = some z ∧ h.istates i = some s ∧ z.state = some (.inflate i) ∧
  z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree" ∧ s.WellFormed ∧
  8 ≤ s.wbits.toNat ∧ s.wbits.toNat ≤ 15 ∧ s.wsize.toNat = 2 ^ s.wbits.toNat ∧
  s.window ≠ .null ∧ Writable h s.window s.wsize.toNat ∧
  Fresh h ∧ Zlib.Inflate.Spec.Uniq h ∧ LibraryGlobals h

def backInitialState (garbage : Nat → UInt64) (window : BPtr) (bits : Int32) : InflateState :=
  { InflateState.garbage garbage with
    dmax := 32768, wbits := bits.toUInt32, wsize := 1 <<< bits.toUInt32
    window := window, wnext := 0, whave := 0, sane := 1 }

structure BackLog where
  supplied : List UInt8
  chunks : List (List UInt8)
  active : BPtr
  held : List UInt8
  exhausted : Bool := false
  failed : Bool := false

/-- Caller callbacks may allocate, free, and update any of their own objects, including records.
They cannot change whether a block that stays live is read-only: C code has no way to make memory
read-only or writable (the model's `ro` marks `const` storage from its allocation on). -/
def ExternalFrame (own : Nat → Prop) (h after : Heap) : Prop :=
  Frame h after own ∧ Fresh after ∧ Zlib.Inflate.Spec.Uniq after ∧
  (∀ b, ¬ h.live b → after.live b → own b) ∧
  (∀ b, h.live b → after.live b → after.ro b = h.ro b)

def ExternalAgreement (own : Nat → Prop) (h after : Heap) : Prop :=
  h.nextBlk = after.nextBlk ∧ h.nalloc = after.nalloc ∧ h.allocOk = after.allocOk ∧
  h.garbage = after.garbage ∧ h.static = after.static ∧
  ∀ b, own b → h.bytes b = after.bytes b ∧ h.words b = after.words b ∧
    h.streams b = after.streams b ∧ h.gzheaders b = after.gzheaders b ∧
    h.dstates b = after.dstates b ∧ h.istates b = after.istates b ∧
    h.gzstates b = after.gzstates b ∧ h.ro b = after.ro b

/-- Hide only the window slice when comparing a callback's private state. A descriptor can
share the allocation while using bytes outside that slice. -/
def restoreWindow (before after : Heap) (window : BPtr) (capacity : Nat) : Heap :=
  match window with
  | .null => after
  | .ref r off => match Space.get before r, Space.get after r with
    | some old, some current => Space.put after r
        (current.extract 0 off ++ old.extract off (off + capacity) ++
          current.extract (off + capacity) current.size)
    | _, _ => after

def CallbackFrame (own : Nat → Prop) (h after : Heap) (r : ZStreamRef) (state : Nat)
    (window : BPtr) (capacity : Nat) : Prop :=
  Frame h after (fun b => StreamRoot r b ∨ b = state ∨ own b ∨ ByteRoot window b) ∧
  ((∀ b, ByteRoot window b → ¬ own b) →
    BufferFrame h after (fun b => StreamRoot r b ∨ b = state ∨ own b) [⟨window, capacity⟩])

/-- What the library guarantees whenever it calls `in` or `out`: the stream is a valid callback
decoder over this window (`BackValid`). In particular the heap is a library heap (`Fresh`, `Uniq`,
`LibraryGlobals`) and the window is writable. A callback contract needs to hold only on such heaps. -/
def CallbackEntry (h : Heap) (r : ZStreamRef) (state : Nat) (window : BPtr) (capacity : Nat) : Prop :=
  ∃ z s, BackValid h r state z s ∧ s.window = window ∧ s.wsize.toNat = capacity

/-- These are contracts of caller code, not assumed library callee contracts.
The input may depend on previous output. A finite source has an explicit total-input bound.
Output must preserve the current input until the next input callback.

`inStep` and `outStep` are required only on a heap that satisfies `CallbackEntry`, which is what
the library provides at each call of `in` and `out`. Without that premise no protocol exists:
`local_` makes the invariant insensitive to every block outside `own`, so the invariant would also
hold on a heap whose state block holds two objects, where no step can end in a `Uniq` heap. -/
structure CallbackProtocol (r : ZStreamRef) (state : Nat) (window : BPtr) (capacity : Nat)
    (input : InCb) (inDesc : BPtr) (output : OutCb) (outDesc : BPtr) where
  own : Nat → Prop
  invariant : Heap → BackLog → Prop
  inputBound : Nat
  disjoint : (¬ own state) ∧ (∀ b, StreamRoot r b → ¬ own b)
  local_ : ∀ h after log, ExternalAgreement own h (restoreWindow h after window capacity) →
    (invariant h log ↔ invariant after log)
  bounded : ∀ h log, invariant h log → log.supplied.length ≤ inputBound
  liveInput : ∀ h log, invariant h log → log.held ≠ [] → Bytes h log.active log.held.length log.held
  inStep : ∀ h log next, CallbackEntry h r state window capacity → invariant h log →
    ∃ n pointer after bytes,
    input inDesc next h = .ok ((n, pointer), after) ∧
    bytes.length = n.toNat ∧ ExternalFrame own h after ∧
    SameBytePrefix h after window window capacity ∧
    (n ≠ 0 → Bytes after pointer n.toNat bytes ∧ Separate pointer n.toNat window capacity ∧
      ∀ b, ByteRoot pointer b → b ≠ state ∧ ¬ StreamRoot r b) ∧
    invariant after { log with
      supplied := log.supplied ++ bytes, active := pointer, held := bytes, exhausted := n == 0 }
  outStep : ∀ h log pointer n bytes, CallbackEntry h r state window capacity → invariant h log →
    Bytes h pointer n.toNat bytes → n.toNat ≤ capacity →
    ∃ rc after, output outDesc pointer n h = .ok (rc, after) ∧ ExternalFrame own h after ∧
      SameBytePrefix h after window window capacity ∧
      (log.held ≠ [] → Bytes after log.active log.held.length log.held) ∧
      invariant after { log with chunks := log.chunks ++ [bytes], failed := log.failed || rc != 0 }

end ZlibF.Spec.Public
