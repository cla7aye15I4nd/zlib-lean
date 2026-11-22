import ZlibF.Proof.«deflate.c.engine.block-prepare»
import ZlibF.Proof.«deflate.c.engine.dynamic-block»

/-! # Actual positive-level flush dispatch to constructed dynamic coding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Whole-function equality retains actual preparation and cost selection
while naming the already checked dynamic-header fragment. -/
theorem flush_block_dynamic_prepare_source (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) :
    Zlib.Trees.«_tr_flush_block» s buf stored_len last = (do
  let mut max_blindex : Int32 := 0
  let mut opt_lenb : UInt64 := 0
  let mut static_lenb : UInt64 := 0
  if (← Zlib.Trees.rd s).level.toInt > 0 then
    max_blindex ← blockPrepare s
    opt_lenb := ((← Zlib.Trees.rd s).opt_len + 3 + 7) >>> 3
    static_lenb := ((← Zlib.Trees.rd s).static_len + 3 + 7) >>> 3
    if static_lenb ≤ opt_lenb ∨ (← Zlib.Trees.rd s).strategy == Z_FIXED then opt_lenb := static_lenb
  else
    opt_lenb := stored_len + 5
    static_lenb := stored_len + 5
  if stored_len + 4 ≤ opt_lenb ∧ buf != .null then
    Zlib.Trees.«_tr_stored_block» s buf stored_len last
  else if static_lenb == opt_lenb then
    Zlib.Trees.Proofs.fixedBlockPayload s last
  else
    Zlib.Trees.Proofs.dynamicBlockHeader s last max_blindex
    Zlib.Trees.compress_block s (← Zlib.Trees.pLtree s) (← Zlib.Trees.pDtree s)
  Zlib.Trees.Proofs.flushBlockTail s last) := by
  rw [Zlib.Trees.Proofs.flush_block_dynamic_header_source]
  unfold blockPrepare blockDataType Zlib.Trees.Proofs.blPrepare
  simp only [M_bind_assoc, M_pure_bind, Zlib.Trees.Proofs.merge_ite_bind]

/-- If the actual rounded costs choose neither stored nor fixed coding,
the full translated flush reaches its original dynamic header/payload and
common tail on the computed prepared heap. -/
theorem flush_dynamic_dispatch {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {mb : Int32}
    (good : DGood h r ds z d) (positive : 0 < d.level.toInt)
    (run : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared))
    (after : DGood (setD (r.put h z') ds prepared) r ds z' prepared)
    (source : BPtr) (stored : UInt64) (last : Int32)
    (prefer : ¬ (((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
      (prepared.strategy == Z_FIXED) = true))
    (avoid : ¬ (stored + (4 : UInt64) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∧ source != .null))
    (dynamic : ((prepared.static_len + 3 + 7) >>> 3) ≠ ((prepared.opt_len + 3 + 7) >>> 3)) :
    Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored last h =
      (do Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) last mb
          Zlib.Trees.compress_block (some (.tab ds)) (← Zlib.Trees.pLtree (some (.tab ds)))
            (← Zlib.Trees.pDtree (some (.tab ds)))
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) last) (setD (r.put h z') ds prepared) := by
  rw [flush_block_dynamic_prepare_source]
  simp only [bind_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
    positive, ite_true, run, Zlib.Trees.Proofs.Out.rd_run after.live.hs,
    prefer, ite_false, avoid, show ((((prepared.static_len + 3 + 7) >>> 3) ==
      ((prepared.opt_len + 3 + 7) >>> 3))) = false from beq_eq_false_iff_ne.mpr dynamic,
    Bool.false_eq_true]

end Zlib.Deflate.Engine.Proofs
