import ZlibF.Zlib.«deflate.c»
import ZlibF.Spec.Common.HeapUniq
import ZlibF.Spec.Common.TreesInv

/-!
# deflate.c: the stream invariant

The definitions of namespace `Zlib.Deflate.Spec` that the goals about deflate streams name. They are part of what a
theorem means. The lemmas about them are in `ZlibF/Proof/deflate.c.base.lean`.

* `DBlocks`: the four buffers of a deflate state (window, prev, head, pending_buf) are live blocks of the right size.
* `DStInv`: the representation invariant of a deflate state record.
* `DLive`: the stream is one that `deflateStateCheck` accepts, and its state is the record `d` at block `ds`.
* `DGood`: `DLive`, `DStInv`, `Uniq`, `Fresh` and the trees invariant together.
-/

namespace Zlib.Deflate.Spec
open C

/-- The status values `deflateStateCheck` accepts: the zlib header, the gzip header, extra, name, comment, header CRC,
busy and finish. -/
def GoodStatus (s : Int32) : Prop :=
  s = INIT_STATE ∨ s = GZIP_STATE ∨ s = EXTRA_STATE ∨ s = NAME_STATE ∨ s = COMMENT_STATE ∨ s = HCRC_STATE ∨
  s = BUSY_STATE ∨ s = FINISH_STATE

/-- The user's gzip header pointer: `NULL`, or a reference to a `gz_header` record. The record
is caller memory. A call that reads it requires it live (`ActiveHeader`, `StreamArguments`);
between calls the caller may release it once the header is written, and `deflate` does not
read it again. `h` is kept for the callers of this definition. -/
def GzOk (_h : Heap) (g : Option GzHeaderRef) : Prop :=
  g = none ∨ ∃ i, g = some (.tab i)

/-- The four buffers of the deflate state record `d`: `window` is the writable byte block `w` of `2 * w_size` bytes,
`pending_buf` the writable byte block `b` of `4 * lit_bufsize` bytes, `prev` and `head` are blocks of 16-bit words that
hold `w_size` and `hash_size` entries. The four blocks are different. `pending_out` lies in `pending_buf`
and `pending_out + pending` does not leave it. -/
structure DBlocks (h : Heap) (d : DeflateState) (w p q b : Nat) : Prop where
  win : d.window = .ref (.blk w) 0
  prev : d.prev = .ref (.blk p) 0
  head : d.head = .ref (.blk q) 0
  pbuf : d.pending_buf = .ref (.blk b) 0
  wa : ∃ a, h.bytes w = some a ∧ a.size = 2 * d.w_size.toNat
  wro : h.ro w = false
  pa : ∃ a, h.words p = some a ∧ a.size = d.w_size.toNat
  qa : ∃ a, h.words q = some a ∧ a.size = d.hash_size.toNat
  ba : ∃ a, h.bytes b = some a ∧ a.size = 4 * d.lit_bufsize.toNat
  bro : h.ro b = false
  psize : d.pending_buf_size.toNat = 4 * d.lit_bufsize.toNat
  wb : w ≠ b
  pq : p ≠ q
  pout : ∃ off, d.pending_out = .ref (.blk b) off ∧ off + d.pending.toNat ≤ d.pending_buf_size.toNat

/-- The representation invariant of a deflate state record `d` at block `ds`, as far as the stream functions and the
engine need it (`deflateInit2_` establishes it).

* sizes: `w_bits` is 9 to 15, `w_size = 2^w_bits`, `w_mask = w_size - 1`, `window_size = 2 * w_size`; `hash_bits` is 8 to
  16 (`memLevel + 7`), `hash_size = 2^hash_bits`, `hash_mask = hash_size - 1`, `hash_shift = (hash_bits + 2) / 3`,
  `lit_bufsize = hash_size / 2 = 2^(memLevel + 6)`;
* ranges: `level` 0 to 9, `strategy` 0 to 4, `method = Z_DEFLATED`, `wrap` from `-2` to `2` (negative after the trailer);
* `high_water <= window_size`;
* the symbol buffer overlays `pending_buf` at `lit_bufsize`, `sym_end = 3 (lit_bufsize - 1)`, `sym_next <= sym_end`
  and a multiple of 3;
* the bit buffer holds `bi_valid` bits (0 to 16) and no bit above them. -/
structure DStInv (h : Heap) (ds : Nat) (d : DeflateState) : Prop where
  wf : d.WellFormed
  wbits_lo : 9 ≤ d.w_bits.toNat
  wbits_hi : d.w_bits.toNat ≤ 15
  wsize : d.w_size.toNat = 2 ^ d.w_bits.toNat
  wmask : d.w_mask.toNat = d.w_size.toNat - 1
  wsz : d.window_size.toNat = 2 * d.w_size.toNat
  hbits_lo : 8 ≤ d.hash_bits.toNat
  hbits_hi : d.hash_bits.toNat ≤ 16
  hsize : d.hash_size.toNat = 2 ^ d.hash_bits.toNat
  hmask : d.hash_mask.toNat = d.hash_size.toNat - 1
  hshift : d.hash_shift.toNat = (d.hash_bits.toNat + 2) / 3
  lit : 2 * d.lit_bufsize.toNat = d.hash_size.toNat
  level_lo : 0 ≤ d.level.toInt
  level_hi : d.level.toInt ≤ 9
  strat_lo : 0 ≤ d.strategy.toInt
  strat_hi : d.strategy.toInt ≤ 4
  method : d.method = 8
  wrap_lo : -2 ≤ d.wrap.toInt
  wrap_hi : d.wrap.toInt ≤ 2
  hw : d.high_water.toNat ≤ d.window_size.toNat
  blocks : ∃ w p q b, DBlocks h d w p q b
  sym : (∃ b, d.pending_buf = .ref (.blk b) 0 ∧ d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat) ∧
    d.sym_end.toNat = 3 * (d.lit_bufsize.toNat - 1) ∧ d.sym_next.toNat ≤ d.sym_end.toNat ∧ d.sym_next.toNat % 3 = 0
  bits : 0 ≤ d.bi_valid.toInt ∧ d.bi_valid.toInt ≤ 16 ∧ d.bi_buf.toNat < 2 ^ d.bi_valid.toInt.toNat
  gz : GzOk h d.gzhead

/-- The stream `r` is the record `z`; its state is the record `d` at block `ds`, which points back to the stream; the
status is one `deflateStateCheck` accepts; the allocator functions are not `NULL`. -/
structure DLive (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  hz : r.get h = some z
  hs : h.dstates ds = some d
  zst : z.state = some (.deflate ds)
  back : d.strm = some r
  status : GoodStatus d.status
  zalloc : z.zalloc ≠ .null
  zfree : z.zfree ≠ .null

/-- The stream functions can allocate and free: the allocator functions are the default ones (the only ones the model
has; any other makes the translation fault). -/
def DefAlloc (z : ZStream) : Prop := z.zalloc = .fn "zcalloc" ∧ z.zfree = .fn "zcfree"

/-- Everything the stream functions assume of the heap around a live deflate stream. -/
structure DGood (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) : Prop where
  live : DLive h r ds z d
  inv : DStInv h ds d
  uniq : Uniq h
  fresh : Fresh h
  trees : Zlib.Trees.Proofs.Out.TreesInv h ds

end Zlib.Deflate.Spec
