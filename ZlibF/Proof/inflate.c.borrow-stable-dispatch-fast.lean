import ZlibF.Proof.«inflate.c.borrow-stable-dispatch-primitives»

/-! Actual fast decoder operations and loops preserve the libc borrow on returning runs. -/
namespace Zlib.Inflate.BorrowProofs
open C C.LibcBorrow Zlib.Inflate Zlib.Inffast

theorem stable_fast_shl32 (x n : UInt32) : StableM (Zlib.Inffast.shl32 x n) := by
  unfold Zlib.Inffast.shl32
  repeat' first
    | inflate_borrow_m_step

theorem stable_fast_shl64 (x n : UInt64) : StableM (Zlib.Inffast.shl64 x n) := by
  unfold Zlib.Inffast.shl64
  repeat' first
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_shr64 (x n : UInt64) : StableM (Zlib.Inffast.shr64 x n) := by
  unfold Zlib.Inffast.shr64
  repeat' first
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_chk64 (v : Int) : StableM (Zlib.Inffast.chk64 v) := by
  unfold Zlib.Inffast.chk64
  repeat' first
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_subn (p : BPtr) (n : UInt32) : StableM (Zlib.Inffast.subn p n) := by
  unfold Zlib.Inffast.subn
  repeat' first
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_pull (l : L) : StableM (Zlib.Inffast.pull l) := by
  unfold Zlib.Inffast.pull
  repeat' first
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_copy1 (l : L) : StableM (Zlib.Inffast.copy1 l) := by
  unfold Zlib.Inffast.copy1
  repeat' first
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_copyOp (l : L) : StableM (Zlib.Inffast.copyOp l) := by
  unfold Zlib.Inffast.copyOp
  repeat' first
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_badData (c : Zlib.Inffast.Ctx) (msg : String) : StableM (Zlib.Inffast.badData c msg) := by
  unfold Zlib.Inffast.badData Zlib.Zutil.strLit
  repeat' first
    | with_reducible exact stable_fast_copyOp _
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_copyMatch (c : Zlib.Inffast.Ctx) (l : L) : StableM (Zlib.Inffast.copyMatch c l) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_copyOp _
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_dodist (c : Zlib.Inffast.Ctx) (l : L) : StableM (Zlib.Inffast.dodist c l) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact stable_fast_copyMatch _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_copyOp _
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_dolen (c : Zlib.Inffast.Ctx) (l : L) : StableM (Zlib.Inffast.dolen c l) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact stable_fast_dodist _ _
    | with_reducible exact stable_fast_copyMatch _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_copyOp _
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_inflate_fast_body (c : Zlib.Inffast.Ctx) (l : L) : StableM (Zlib.Inffast.inflate_fast_body c l) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact stable_fast_dolen _ _
    | with_reducible exact stable_fast_dodist _ _
    | with_reducible exact stable_fast_copyMatch _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_copyOp _
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_ptr_le {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    StableM (Ptr.le p q) :=
  StableM.bind (stable_ptr_lt q p) (fun b => StableM.pure (!b))

theorem stable_fast_load64 (p : BPtr) : StableM (Zlib.Inffast.load64 p) := by
  unfold Zlib.Inffast.load64
  inflate_borrow_m

theorem stable_fast_store64 (out : BPtr) (v : UInt64) : StableM (Zlib.Inffast.store64 out v) := by
  unfold Zlib.Inffast.store64
  inflate_borrow_m

theorem stable_fast_copy_back (out : BPtr) (dist len : UInt32) :
    StableM (Zlib.Inffast.copy_back out dist len) := by
  unfold Zlib.Inffast.copy_back
  repeat' first
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_load64 _
    | with_reducible exact stable_fast_store64 _ _
    | with_reducible exact C.LibcBorrow.stable_memcpyB _ _ _
    | inflate_borrow_m_step

theorem stable_fast_refill64 (l : L) : StableM (Zlib.Inffast.refill64 l) := by
  unfold Zlib.Inffast.refill64
  repeat' first
    | with_reducible exact stable_fast_load64 _
    | with_reducible exact stable_fast_shl64 _ _
    | inflate_borrow_m_step

theorem stable_fast_copyMatch8 (c : Zlib.Inffast.Ctx) (l : L) :
    StableM (Zlib.Inffast.copyMatch8 c l) := by
  unfold Zlib.Inffast.copyMatch8
  repeat' first
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_copy_back _ _ _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact C.LibcBorrow.stable_memcpyB _ _ _
    | inflate_borrow_m_step

theorem stable_fast_dodist8 (c : Zlib.Inffast.Ctx) (l : L) : StableM (Zlib.Inffast.dodist8 c l) := by
  unfold Zlib.Inffast.dodist8
  repeat' first
    | with_reducible exact stable_fast_copyMatch8 _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_refill64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_dolen8 (c : Zlib.Inffast.Ctx) (l : L) : StableM (Zlib.Inffast.dolen8 c l) := by
  unfold Zlib.Inffast.dolen8
  repeat' first
    | with_reducible exact stable_fast_dodist8 _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_refill64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_inflate_fast_body8 (c : Zlib.Inffast.Ctx) (l : L) :
    StableM (Zlib.Inffast.inflate_fast_body8 c l) := by
  unfold Zlib.Inffast.inflate_fast_body8
  repeat' first
    | with_reducible exact stable_fast_dolen8 _ _
    | with_reducible exact stable_fast_dodist8 _ _
    | with_reducible exact stable_fast_copyMatch8 _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_refill64 _
    | with_reducible exact stable_fast_copy_back _ _ _
    | with_reducible exact stable_fast_store64 _ _
    | with_reducible exact stable_fast_load64 _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | inflate_borrow_m_step

theorem stable_fast_inflate_fast (strm : ZStreamPtr) (start : UInt32) : StableM (Zlib.Inffast.inflate_fast strm start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact stable_fast_inflate_fast_body _ _
    | with_reducible exact stable_fast_inflate_fast_body8 _ _
    | with_reducible exact stable_fast_dolen _ _
    | with_reducible exact stable_fast_dodist _ _
    | with_reducible exact stable_fast_copyMatch _ _
    | with_reducible exact stable_fast_badData _ _
    | with_reducible exact stable_fast_copyOp _
    | with_reducible exact stable_fast_copy1 _
    | with_reducible exact stable_fast_pull _
    | with_reducible exact stable_fast_subn _ _
    | with_reducible exact stable_fast_chk64 _
    | with_reducible exact stable_fast_shr64 _ _
    | with_reducible exact stable_fast_shl64 _ _
    | with_reducible exact stable_fast_shl32 _ _
    | with_reducible exact stable_ptr_le _ _
    | inflate_borrow_m_step


#print axioms stable_fast_copyMatch
#print axioms stable_fast_dolen
#print axioms stable_fast_inflate_fast
end Zlib.Inflate.BorrowProofs
