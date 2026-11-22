import ZlibF.Zlib.«inflate.c»
import ZlibF.Spec.Common.HeapUniq

/-!
# inflate.c: the stream invariant

The definitions of namespace `Zlib.Inflate.Spec` that the goals about inflate streams name. They are part of what a
theorem means. The lemmas about them are in `ZlibF/Proof/inflate.c.base.lean`.

* `WinInv`: the window of an inflate state.
* `StInv`: the representation invariant of an inflate state (window, bit buffer, table pointers).
* `Live`: the stream is one that `inflateStateCheck` accepts, and its state is the record `st` at block `zs`.
* `Good`: `Live`, `StInv`, `Uniq` and `Fresh` together.
-/

namespace Zlib.Inflate.Spec
open C

/-- The heap with the state record `zs` replaced. -/
def setI (h : Heap) (zs : Nat) (s : InflateState) : Heap := { h with istates := upd h.istates zs (some s) }

/-- The window of an inflate state `st`: `NULL` with nothing in use, or a writable byte block of `2^wbits` bytes.
`wsize` is 0 or `2^wbits`; `whave` bytes are valid; `wnext` is the next write position, which equals `whave` while the
window is not full (`docs/en/proof/inflate.md`, invariant W). -/
structure WinInv (h : Heap) (st : InflateState) : Prop where
  wbits : st.wbits.toNat ≤ 15
  block : st.window = .null ∨
    ∃ w a, st.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧ a.size = 2 ^ st.wbits.toNat
  nullws : st.window = .null → st.wsize = 0
  ws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat
  hv : st.whave.toNat ≤ st.wsize.toNat
  wn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0)
  eq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat

/-- The table pointers of the state `zs`: `next` is in `codes`; `lencode` and `distcode` are both in `codes` (a
dynamic block, or the start) or are the two static fixed tables (a stream stopped inside a fixed block). -/
def PtrInv (zs : Nat) (st : InflateState) : Prop :=
  (∃ i, st.next = .ref (.istate_codes zs) i ∧ i ≤ 1732) ∧
  ((∃ i j, st.lencode = .ref (.istate_codes zs) i ∧ st.distcode = .ref (.istate_codes zs) j ∧ i ≤ 1731 ∧ j ≤ 1731) ∨
   (st.lencode = .ref .st_lenfix 0 ∧ st.distcode = .ref .st_distfix 0))

/-- The representation invariant of an inflate state, as far as the stream functions need it: the arrays have the
size of the C declaration, the window invariant, `reqbits` is a valid window size, the bit buffer holds at most 39 bits
(`NEEDBITS` of at most 32 bits pulls whole bytes while fewer are present), and the table pointers. -/
structure StInv (h : Heap) (zs : Nat) (st : InflateState) : Prop where
  wf : st.WellFormed
  win : WinInv h st
  reqbits : st.reqbits.toNat ≤ 15
  bits : st.bits.toNat ≤ 39
  ptr : PtrInv zs st

/-- The stream `r` is the record `z`; its state is the record `st` at block `zs`, which points back to the stream; the
mode is in the range `inflateStateCheck` accepts; the stream has the default allocator functions or none. -/
structure Live (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (st : InflateState) : Prop where
  hz : r.get h = some z
  hs : h.istates zs = some st
  zst : z.state = some (.inflate zs)
  back : st.strm = some r
  mode : HEAD ≤ st.mode ∧ st.mode ≤ SYNC
  zalloc : z.zalloc ≠ .null
  zfree : z.zfree ≠ .null

/-- The stream functions can allocate and free: the allocator functions are the default ones (the only ones the model
has; any other makes the translation fault). -/
def DefAlloc (z : ZStream) : Prop := z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree"

/-- Everything the stream functions assume of the heap around a live stream. -/
structure Good (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (st : InflateState) : Prop where
  live : Live h r zs z st
  inv : StInv h zs st
  uniq : Uniq h
  fresh : Fresh h

end Zlib.Inflate.Spec
