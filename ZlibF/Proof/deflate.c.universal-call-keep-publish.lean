import ZlibF.Proof.«deflate.c.universal-call-keep-helpers»
import ZlibF.Proof.«deflate.c.universal-call-keep-trees»

/-!
# deflate.c: `KeepRel` for `flush_pending` and the block macros
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- A byte array change leaves every stream record as it is. -/
theorem stream_get_modify_B (h : Heap) (b : BRef) (f : Array UInt8 → Array UInt8) (r : ZStreamRef) :
    r.get (Space.modify h b f) = r.get h := by
  cases b <;> cases r <;> rfl

theorem stream_get_memcpy {dst src : BPtr} {n : Nat} {h h1 : Heap} {u : Unit}
    (run : Ptr.memcpy dst src n h = .ok (u, h1)) (r : ZStreamRef) : r.get h1 = r.get h := by
  unfold Ptr.memcpy at run
  repeat' first | split at run | (cases run; exact stream_get_modify_B _ _ _ _) | contradiction

theorem heap_padd {p q : BPtr} {n : Nat} {h h1 : Heap} (run : padd p n h = .ok (q, h1)) : h1 = h := by
  unfold padd Ptr.add at run
  repeat' first | split at run | (cases run; rfl) | contradiction

theorem keep_flush_pending (strm : ZStreamPtr) : KeepM (flush_pending strm) := by
  unfold flush_pending advance_pending
  repeat' first
    | exact Zlib.Trees.KeepProofs.keep__tr_flush_bits _
    | k_step

theorem keep_FLUSH_BLOCK_ONLY (s : DeflateStatePtr) (last : Int32) : KeepM (FLUSH_BLOCK_ONLY s last) := by
  unfold FLUSH_BLOCK_ONLY
  repeat' first
    | exact Zlib.Trees.KeepProofs.keep__tr_flush_block _ _ _ _
    | exact keep_flush_pending _
    | k_step

theorem keep_FLUSH_BLOCK (s : DeflateStatePtr) (last : Int32) : KeepM (FLUSH_BLOCK s last) := by
  unfold FLUSH_BLOCK
  repeat' first
    | exact keep_FLUSH_BLOCK_ONLY _ _
    | k_step

theorem keep_finish_tail (s : DeflateStatePtr) (flush : Int32) : KeepM (finish_tail s flush) := by
  unfold finish_tail
  repeat' first
    | exact keep_FLUSH_BLOCK _ _
    | k_step

end Zlib.Deflate.Universal.Keep
