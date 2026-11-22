import ZlibF.Proof.«deflate.c.engine.stored-block»

/-! # Complete actual flush execution when computed costs select stored bytes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt storedTag)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false

/-- Actual positive-level preparation and both possible byte-cost choices
dispatch to the original stored writer when its real comparison wins. -/
theorem flush_stored_dispatch {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {mb : Int32}
    (good : DGood h r ds z d) (positive : 0 < d.level.toInt)
    (run : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared))
    (after : DGood (setD (r.put h z') ds prepared) r ds z' prepared)
    (source : BPtr) (nonnull : source ≠ .null) (stored : UInt64) (last : Int32)
    (selected : stored + (4 : UInt64) ≤ selectedCost (byteCost prepared.opt_len)
      (byteCost prepared.static_len) (prepared.strategy == Z_FIXED)) :
    Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored last h =
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) source stored last
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) last) (setD (r.put h z') ds prepared) := by
  rw [flush_block_prepare_source]
  simp only [bind_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
    positive, ite_true, run, Zlib.Trees.Proofs.Out.rd_run after.live.hs]
  unfold selectedCost byteCost at selected
  split at selected <;> rename_i prefer <;>
    simp only [prefer, ite_true, ite_false, selected, show (source != .null) = true from bne_iff_ne.mpr nonnull,
      and_self, bind_app]

end Zlib.Deflate.Engine.Proofs
