import ZlibF.Proof.«deflate.c.universal-params-helpers»
import ZlibF.Proof.«deflate.c.universal-params-trees»

/-!
# deflate.c: the parameter frame for `flush_pending` and the block macros
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

theorem exact_flush_pending (strm : ZStreamPtr) : ExactM (flush_pending strm) := by
  unfold flush_pending advance_pending
  repeat' first
    | exact Zlib.Trees.ParamsProofs.exact__tr_flush_bits _
    | x_step

theorem exact_FLUSH_BLOCK_ONLY (s : DeflateStatePtr) (last : Int32) : ExactM (FLUSH_BLOCK_ONLY s last) := by
  unfold FLUSH_BLOCK_ONLY
  repeat' first
    | exact Zlib.Trees.ParamsProofs.exact__tr_flush_block _ _ _ _
    | exact exact_flush_pending _
    | x_step

theorem exact_FLUSH_BLOCK (s : DeflateStatePtr) (last : Int32) : ExactM (FLUSH_BLOCK s last) := by
  unfold FLUSH_BLOCK
  repeat' first
    | exact exact_FLUSH_BLOCK_ONLY _ _
    | x_step

theorem exact_finish_tail (s : DeflateStatePtr) (flush : Int32) : ExactM (finish_tail s flush) := by
  unfold finish_tail
  repeat' first
    | exact exact_FLUSH_BLOCK _ _
    | x_step

end Zlib.Deflate.Universal.Params
