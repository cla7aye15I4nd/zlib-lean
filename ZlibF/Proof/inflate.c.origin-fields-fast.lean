import ZlibF.Proof.«inflate.c.origin-fields-updates»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem originFieldFrameM_fast_shl32 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt32) : OriginFieldFrameM r owner (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_fast_shl64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : OriginFieldFrameM r owner (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_fast_shr64 (r : ZStreamRef) (owner : InflateStatePtr) (value shift : UInt64) : OriginFieldFrameM r owner (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_fast_chk64 (r : ZStreamRef) (owner : InflateStatePtr) (value : Int) : OriginFieldFrameM r owner (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact originFieldFrameM_ite (originFieldFrameM_pure r owner _) (originFieldFrameM_ub r owner _)

theorem originFieldFrameM_fast_subn (r : ZStreamRef) (owner : InflateStatePtr) (pointer : BPtr) (count : UInt32) : OriginFieldFrameM r owner (Zlib.Inffast.subn pointer count) :=
  originFieldFrameM_ptr_add r owner _ _

theorem originFieldFrameM_fast_pull (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : OriginFieldFrameM r owner (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact originFieldFrameM_bind (originFieldFrameM_ptr_load r owner _) (fun _ =>
    originFieldFrameM_bind (originFieldFrameM_ptr_add r owner _ _) (fun _ =>
      originFieldFrameM_bind (originFieldFrameM_fast_shl64 r owner _ _) (fun _ => originFieldFrameM_pure r owner _)))

theorem originFieldFrameM_fast_copy1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : OriginFieldFrameM r owner (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact originFieldFrameM_bind (originFieldFrameM_ptr_load r owner _) (fun _ =>
    originFieldFrameM_bind (originFieldFrameM_ptr_add r owner _ _) (fun _ =>
      originFieldFrameM_bind (originFieldFrameM_store8 r owner _ _) (fun _ =>
        originFieldFrameM_bind (originFieldFrameM_ptr_add r owner _ _) (fun _ => originFieldFrameM_pure r owner _))))

theorem originFieldFrameM_fast_copyOp (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) : OriginFieldFrameM r owner (Zlib.Inffast.copyOp state) :=
  originFieldFrameM_cdoWhile (originFieldFrameM_fast_copy1 r owner) (fun _ => originFieldFrameM_pure r owner _) state

/-- Actual fast-decoder diagnostics retain the decoder origin fields. -/
theorem originFieldFrameM_fast_badData (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : OriginFieldFrameM r owner (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  repeat' first
    | with_reducible exact originFieldFrameM_strLit r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_stZ r owner _ _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_bind ?_ (fun _ => ?_)

/-- Successful actual fast copyMatch execution preserves decoder origin fields. -/
theorem originFieldFrameM_fast_copyMatch (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_copyOp r owner _
    | with_reducible exact originFieldFrameM_fast_copy1 r owner _
    | with_reducible exact originFieldFrameM_fast_pull r owner _
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves decoder origin fields. -/
theorem originFieldFrameM_fast_dodist (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_copyOp r owner _
    | with_reducible exact originFieldFrameM_fast_copy1 r owner _
    | with_reducible exact originFieldFrameM_fast_pull r owner _
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves decoder origin fields. -/
theorem originFieldFrameM_fast_dolen (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_copyOp r owner _
    | with_reducible exact originFieldFrameM_fast_copy1 r owner _
    | with_reducible exact originFieldFrameM_fast_pull r owner _
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact originFieldFrameM_fast_dodist r owner _ root _
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves decoder origin fields. -/
theorem originFieldFrameM_fast_body (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_copyOp r owner _
    | with_reducible exact originFieldFrameM_fast_copy1 r owner _
    | with_reducible exact originFieldFrameM_fast_pull r owner _
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_fast_copyMatch r owner _ root _
    | with_reducible exact originFieldFrameM_fast_dodist r owner _ root _
    | with_reducible exact originFieldFrameM_fast_dolen r owner _ root _
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_ptr_le {R T : Type} [Space Heap R T] [DecidableEq R]
    (r : ZStreamRef) (owner : InflateStatePtr) (p q : Ptr R) :
    OriginFieldFrameM r owner (p.le q) :=
  originFieldFrameM_bind (originFieldFrameM_ptr_lt r owner q p) (fun b => originFieldFrameM_pure r owner (!b))

theorem originFieldFrameM_fast_load64 (r : ZStreamRef) (owner : InflateStatePtr) (p : BPtr) :
    OriginFieldFrameM r owner (Zlib.Inffast.load64 p) := by
  unfold Zlib.Inffast.load64
  repeat' first
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_fast_store64 (r : ZStreamRef) (owner : InflateStatePtr) (out : BPtr) (v : UInt64) :
    OriginFieldFrameM r owner (Zlib.Inffast.store64 out v) := by
  unfold Zlib.Inffast.store64
  repeat' first
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_fast_copy_back (r : ZStreamRef) (owner : InflateStatePtr) (out : BPtr)
    (dist len : UInt32) : OriginFieldFrameM r owner (Zlib.Inffast.copy_back out dist len) := by
  unfold Zlib.Inffast.copy_back
  repeat' first
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_fast_load64 r owner _
    | with_reducible exact originFieldFrameM_fast_store64 r owner _ _
    | with_reducible exact originFieldFrameM_memcpyB r owner _ _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))
    | (intro p; cases p; dsimp only)

theorem originFieldFrameM_fast_refill64 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.refill64 state) := by
  unfold Zlib.Inffast.refill64
  repeat' first
    | with_reducible exact originFieldFrameM_fast_load64 r owner _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_fast_copyMatch8 (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.copyMatch8 context state) := by
  unfold Zlib.Inffast.copyMatch8
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_copy_back r owner _ _ _
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_memcpyB r owner _ _ _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_fast_dodist8 (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.dodist8 context state) := by
  unfold Zlib.Inffast.dodist8
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_copyMatch8 r owner _ root _
    | with_reducible exact originFieldFrameM_fast_refill64 r owner _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_fast_dolen8 (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.dolen8 context state) := by
  unfold Zlib.Inffast.dolen8
  repeat' first
    | with_reducible exact originFieldFrameM_fast_badData r owner _ root _
    | with_reducible exact originFieldFrameM_fast_dodist8 r owner _ root _
    | with_reducible exact originFieldFrameM_fast_refill64 r owner _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_fast_body8 (r : ZStreamRef) (owner : InflateStatePtr) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    OriginFieldFrameM r owner (Zlib.Inffast.inflate_fast_body8 context state) := by
  unfold Zlib.Inffast.inflate_fast_body8
  repeat' first
    | with_reducible exact originFieldFrameM_fast_dolen8 r owner _ root _
    | with_reducible exact originFieldFrameM_fast_refill64 r owner _
    | with_reducible exact originFieldFrameM_fast_shr64 r owner _ _
    | with_reducible exact originFieldFrameM_store8 r owner _ _
    | with_reducible exact originFieldFrameM_ptr_load r owner _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves decoder origin fields, through its actual record writes, on every successful run. -/
theorem originFieldFrameM_inflate_fast (r : ZStreamRef) (owner : InflateStatePtr) (start : UInt32) :
    OriginFieldFrameM r owner (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact originFieldFrameM_fast_body r owner _ rfl _
    | with_reducible exact originFieldFrameM_fast_body8 r owner _ rfl _
    | with_reducible exact originFieldFrameM_fast_subn r owner _ _
    | with_reducible exact originFieldFrameM_fast_shl32 r owner _ _
    | with_reducible exact originFieldFrameM_fast_chk64 r owner _
    | with_reducible exact originFieldFrameM_ldZ r owner _
    | with_reducible exact originFieldFrameM_ldS r owner _
    | with_reducible exact originFieldFrameM_ldS_store r owner _ _ (fun _ => rfl)
    | with_reducible refine originFieldFrameM_ldS_update r owner _ _ _ (fun _ => rfl) (fun _ => ?_)
    | with_reducible exact originFieldFrameM_castI r owner _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_ptr_diff r owner _ _
    | with_reducible exact originFieldFrameM_ptr_lt r owner _ _
    | with_reducible exact originFieldFrameM_ptr_le r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible exact originFieldFrameM_ub r owner _
    | with_reducible exact originFieldFrameM_stZ r owner _ _
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
