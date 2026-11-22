import ZlibF.Proof.«inflate.c.completes-keep-x»

/-! The fast decoder keeps `Keeps` (mirrors `inflate.c.borrow-stable-dispatch-fast`). -/
namespace Zlib.Inflate.KeepProofs
open C Zlib.Inflate Zlib.Inffast
set_option autoImplicit false

theorem keep_fast_shl32 (x n : UInt32) : KeepM (Zlib.Inffast.shl32 x n) := by
  unfold Zlib.Inffast.shl32
  repeat' first
    | keep_m_step

theorem keep_fast_shl64 (x n : UInt64) : KeepM (Zlib.Inffast.shl64 x n) := by
  unfold Zlib.Inffast.shl64
  repeat' first
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_shr64 (x n : UInt64) : KeepM (Zlib.Inffast.shr64 x n) := by
  unfold Zlib.Inffast.shr64
  repeat' first
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_chk64 (v : Int) : KeepM (Zlib.Inffast.chk64 v) := by
  unfold Zlib.Inffast.chk64
  repeat' first
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_subn (p : BPtr) (n : UInt32) : KeepM (Zlib.Inffast.subn p n) := by
  unfold Zlib.Inffast.subn
  repeat' first
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_pull (l : L) : KeepM (Zlib.Inffast.pull l) := by
  unfold Zlib.Inffast.pull
  repeat' first
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_copy1 (l : L) : KeepM (Zlib.Inffast.copy1 l) := by
  unfold Zlib.Inffast.copy1
  repeat' first
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_copyOp (l : L) : KeepM (Zlib.Inffast.copyOp l) := by
  unfold Zlib.Inffast.copyOp
  repeat' first
    | with_reducible exact keep_fast_copy1 _
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_badData (c : Zlib.Inffast.Ctx) (msg : String) : KeepM (Zlib.Inffast.badData c msg) := by
  unfold Zlib.Inffast.badData Zlib.Zutil.strLit
  repeat' first
    | with_reducible exact keep_fast_copyOp _
    | with_reducible exact keep_fast_copy1 _
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_copyMatch (c : Zlib.Inffast.Ctx) (l : L) : KeepM (Zlib.Inffast.copyMatch c l) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_copyOp _
    | with_reducible exact keep_fast_copy1 _
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_dodist (c : Zlib.Inffast.Ctx) (l : L) : KeepM (Zlib.Inffast.dodist c l) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact keep_fast_copyMatch _ _
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_copyOp _
    | with_reducible exact keep_fast_copy1 _
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_dolen (c : Zlib.Inffast.Ctx) (l : L) : KeepM (Zlib.Inffast.dolen c l) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact keep_fast_dodist _ _
    | with_reducible exact keep_fast_copyMatch _ _
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_copyOp _
    | with_reducible exact keep_fast_copy1 _
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_inflate_fast_body (c : Zlib.Inffast.Ctx) (l : L) : KeepM (Zlib.Inffast.inflate_fast_body c l) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact keep_fast_dolen _ _
    | with_reducible exact keep_fast_dodist _ _
    | with_reducible exact keep_fast_copyMatch _ _
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_copyOp _
    | with_reducible exact keep_fast_copy1 _
    | with_reducible exact keep_fast_pull _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_ptr_le {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    KeepM (Ptr.le p q) :=
  KeepM.bind (keep_ptr_lt q p) (fun b => KeepM.pure (!b))

theorem keep_fast_load64 (p : BPtr) : KeepM (Zlib.Inffast.load64 p) := by
  unfold Zlib.Inffast.load64
  keep_m

theorem keep_fast_store64 (out : BPtr) (v : UInt64) : KeepM (Zlib.Inffast.store64 out v) := by
  unfold Zlib.Inffast.store64
  keep_m

theorem keep_fast_copy_back (out : BPtr) (dist len : UInt32) :
    KeepM (Zlib.Inffast.copy_back out dist len) := by
  unfold Zlib.Inffast.copy_back
  repeat' first
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_load64 _
    | with_reducible exact keep_fast_store64 _ _
    | keep_m_step

theorem keep_fast_refill64 (l : L) : KeepM (Zlib.Inffast.refill64 l) := by
  unfold Zlib.Inffast.refill64
  repeat' first
    | with_reducible exact keep_fast_load64 _
    | with_reducible exact keep_fast_shl64 _ _
    | keep_m_step

theorem keep_fast_copyMatch8 (c : Zlib.Inffast.Ctx) (l : L) :
    KeepM (Zlib.Inffast.copyMatch8 c l) := by
  unfold Zlib.Inffast.copyMatch8
  repeat' first
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_copy_back _ _ _
    | with_reducible exact keep_fast_subn _ _
    | keep_m_step

theorem keep_fast_dodist8 (c : Zlib.Inffast.Ctx) (l : L) : KeepM (Zlib.Inffast.dodist8 c l) := by
  unfold Zlib.Inffast.dodist8
  repeat' first
    | with_reducible exact keep_fast_copyMatch8 _ _
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_refill64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_dolen8 (c : Zlib.Inffast.Ctx) (l : L) : KeepM (Zlib.Inffast.dolen8 c l) := by
  unfold Zlib.Inffast.dolen8
  repeat' first
    | with_reducible exact keep_fast_dodist8 _ _
    | with_reducible exact keep_fast_badData _ _
    | with_reducible exact keep_fast_refill64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

theorem keep_fast_inflate_fast_body8 (c : Zlib.Inffast.Ctx) (l : L) :
    KeepM (Zlib.Inffast.inflate_fast_body8 c l) := by
  unfold Zlib.Inffast.inflate_fast_body8
  repeat' first
    | with_reducible exact keep_fast_dolen8 _ _
    | with_reducible exact keep_fast_refill64 _
    | with_reducible exact keep_fast_shr64 _ _
    | with_reducible exact keep_fast_shl32 _ _
    | keep_m_step

set_option maxHeartbeats 400000 in
theorem keep_fast_inflate_fast (strm : ZStreamPtr) (start : UInt32) : KeepM (Zlib.Inffast.inflate_fast strm start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact keep_fast_inflate_fast_body _ _
    | with_reducible exact keep_fast_inflate_fast_body8 _ _
    | with_reducible exact keep_fast_subn _ _
    | with_reducible exact keep_fast_chk64 _
    | with_reducible exact keep_fast_shl32 _ _
    | with_reducible exact keep_ptr_le _ _
    | keep_m_step


#print axioms keep_fast_copyMatch
#print axioms keep_fast_dolen
#print axioms keep_fast_inflate_fast
end Zlib.Inflate.KeepProofs
