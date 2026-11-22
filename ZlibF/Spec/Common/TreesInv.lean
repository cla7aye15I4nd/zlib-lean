import ZlibF.Zlib.«trees.c»

/-!
# trees.c: the invariant of the deflate state that the functions of `trees.c` need

`TreesInv h id` is part of `DGood`. The lemmas about it are in `ZlibF/Proof/trees.c.inv.lean`.
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

/-- The static tables and descriptors of `trees.c` are installed: `install_trees` (`trees.c.lean`) provides this on
any heap, and no function of `trees.c` changes `h.static`. -/
def TreesStatic (st : Statics) : Prop := trees_statics st = st

/-- **What `deflateInit2_` establishes before `_tr_init` runs.** The deflate record `d` of block `id` is live and
well formed (`dyn_ltree`, `heap`, `depth` have `HEAP_SIZE` = 573 entries, `dyn_dtree` 61, `bl_tree` 39, `bl_count`
16); the static tables of `trees.c` are installed; `pending_buf` is the start of the writable byte block `b`, whose
content is `buf` and whose size is `4 * lit_bufsize` (`ZALLOC(strm, lit_bufsize, LIT_BUFS)`, with
`pending_buf_size = 4 * lit_bufsize`); `sym_buf = pending_buf + lit_bufsize` is in the same block
(`deflate.c` L519: the overlay of the symbols on the output); `sym_end = (lit_bufsize - 1) * 3`;
`lit_bufsize = 1 << (memLevel + 6)` lies in `128 .. 32768`; and `pending <= pending_buf_size` (zero after
`deflateResetKeep`). -/
structure TreesBase (h : Heap) (id : Nat) (d : DeflateState) (b : Nat) (buf : Array UInt8) : Prop where
  dstate : h.dstates id = some d
  wf : d.WellFormed
  static : TreesStatic h.static
  pbuf : d.pending_buf = .ref (.blk b) 0
  bytes : h.bytes b = some buf
  rw : h.ro b = false
  size : buf.size = 4 * d.lit_bufsize.toNat
  psize : d.pending_buf_size.toNat = buf.size
  sym : d.sym_buf = .ref (.blk b) d.lit_bufsize.toNat
  lit_lo : 128 ≤ d.lit_bufsize.toNat
  lit_hi : d.lit_bufsize.toNat ≤ 32768
  sym_end : d.sym_end.toNat = 3 * (d.lit_bufsize.toNat - 1)
  pending_le : d.pending.toNat ≤ d.pending_buf_size.toNat

/-- **What `_tr_init` adds.** The three tree descriptors point at the arrays of the record and at the static
descriptors; the bit buffer holds `bi_valid <= 16 = Buf_size` bits (fact F9 of `docs/en/proof/trees.md`: `send_bits`
shifts by at most 16) and no bit above them; the symbol count is a multiple of 3 and at most `sym_end`
(`_tr_tally` is always followed by a flush when `sym_next == sym_end`). -/
structure TreesRun (id : Nat) (d : DeflateState) : Prop where
  ldyn : d.l_desc.dyn_tree = .ref (.dstate_dyn_ltree id) 0
  lstat : d.l_desc.stat_desc = some .st_static_l_desc
  ddyn : d.d_desc.dyn_tree = .ref (.dstate_dyn_dtree id) 0
  dstat : d.d_desc.stat_desc = some .st_static_d_desc
  bldyn : d.bl_desc.dyn_tree = .ref (.dstate_bl_tree id) 0
  blstat : d.bl_desc.stat_desc = some .st_static_bl_desc
  bi_lo : 0 ≤ d.bi_valid.toInt
  bi_hi : d.bi_valid.toInt ≤ 16
  bi_buf : d.bi_buf.toNat < 2 ^ d.bi_valid.toInt.toNat
  sym_next_le : d.sym_next.toNat ≤ d.sym_end.toNat
  sym_next_mod : d.sym_next.toNat % 3 = 0

/-- **The deflate state is well formed for the code of `trees.c`**, with the byte block `b` (content `buf`) that
holds `pending_buf` and `sym_buf`. -/
structure TreesInvAt (h : Heap) (id : Nat) (d : DeflateState) (b : Nat) (buf : Array UInt8) : Prop where
  base : TreesBase h id d b buf
  run : TreesRun id d

/-- `TreesInv h id`: the deflate state of block `id` is well formed for the code of `trees.c` (see `TreesInvAt`). -/
def TreesInv (h : Heap) (id : Nat) : Prop := ∃ d b buf, TreesInvAt h id d b buf

end Zlib.Trees.Proofs.Out
