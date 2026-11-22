import ZlibF.Proof.«inflate.c.fast-memory-shape-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem fastMemoryMetaFrameM_fast_shl32 (r : ZStreamRef) (value shift : UInt32) : FastMemoryMetaFrameM r (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_fast_shl64 (r : ZStreamRef) (value shift : UInt64) : FastMemoryMetaFrameM r (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_fast_shr64 (r : ZStreamRef) (value shift : UInt64) : FastMemoryMetaFrameM r (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_fast_chk64 (r : ZStreamRef) (value : Int) : FastMemoryMetaFrameM r (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact fastMemoryMetaFrameM_ite (fastMemoryMetaFrameM_pure r _) (fastMemoryMetaFrameM_ub r _)

theorem fastMemoryMetaFrameM_fast_subn (r : ZStreamRef) (pointer : BPtr) (count : UInt32) : FastMemoryMetaFrameM r (Zlib.Inffast.subn pointer count) :=
  fastMemoryMetaFrameM_ptr_add r _ _

theorem fastMemoryMetaFrameM_fast_pull (r : ZStreamRef) (state : Zlib.Inffast.L) : FastMemoryMetaFrameM r (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_load r _) (fun _ =>
    fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r _ _) (fun _ =>
      fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_fast_shl64 r _ _) (fun _ => fastMemoryMetaFrameM_pure r _)))

theorem fastMemoryMetaFrameM_fast_copy1 (r : ZStreamRef) (state : Zlib.Inffast.L) : FastMemoryMetaFrameM r (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_load r _) (fun _ =>
    fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r _ _) (fun _ =>
      fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_store8 r _ _) (fun _ =>
        fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r _ _) (fun _ => fastMemoryMetaFrameM_pure r _))))

theorem fastMemoryMetaFrameM_fast_copyOp (r : ZStreamRef) (state : Zlib.Inffast.L) : FastMemoryMetaFrameM r (Zlib.Inffast.copyOp state) :=
  fastMemoryMetaFrameM_cdoWhile (fastMemoryMetaFrameM_fast_copy1 r) (fun _ => fastMemoryMetaFrameM_pure r _) state

/-- Actual fast-decoder diagnostics retain the allocation metadata. -/
theorem fastMemoryMetaFrameM_fast_badData (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (message : String) : FastMemoryMetaFrameM r (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  rw [root]
  refine fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_strLit r _) (fun pointer => ?_)
  refine fastMemoryMetaFrameM_ldZ_update r (fun z => { z with msg := pointer }) _ (fun _ => rfl) (fun _ => ?_)
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ldS r _) (fun _ => fastMemoryMetaFrameM_stS r _ _)

/-- Successful actual fast copyMatch execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_fast_copyMatch (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyOp r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copy1 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_pull r _
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dodist execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_fast_dodist (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyOp r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copy1 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_pull r _
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyMatch r _ root _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast dolen execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_fast_dolen (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyOp r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copy1 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_pull r _
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyMatch r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_dodist r _ root _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- Successful actual fast inflate_fast_body execution preserves allocation metadata. -/
theorem fastMemoryMetaFrameM_fast_body (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyOp r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copy1 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_pull r _
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyMatch r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_dodist r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_dolen r _ root _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_ptr_le {R T : Type} [Space Heap R T] [DecidableEq R]
    (r : ZStreamRef) (p q : Ptr R) : FastMemoryMetaFrameM r (p.le q) :=
  fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_lt r q p)
    (fun b => fastMemoryMetaFrameM_pure r (!b))

private theorem fast_meta_byte_put_self {h : Heap} {ref : BRef} {old : Array UInt8}
    (get : Space.get h ref = some old) : Space.put h ref old = h := by
  cases ref with
  | blk id => simp only [Space.get] at get; simp [Space.put, upd_self _ _ _ get]
  | dstate_depth id =>
    cases state : h.dstates id with
    | none => simp [Space.get, state] at get
    | some s =>
      have same : s.depth = old := by simpa [Space.get, state] using get
      rw [← same]
      simp [Space.put, state, upd_self _ _ _ state]
  | str id => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

private theorem fastMemoryMetaFrameM_fast_memcpyB (r : ZStreamRef)
    (destination source : BPtr) (count : Nat) :
    FastMemoryMetaFrameM r (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first | cases run | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      by_cases zero : count = 0
      · subst count
        simp only [copyRange, List.range_zero, List.foldl_nil, fast_meta_byte_put_self destGet] at run
        repeat' first | split at run | (cases run <;> rfl)
      · repeat' first
          | split at run
          | (cases run <;> exact fast_byte_view_put_memory_meta _ _ array _ destGet
              (by cases ro : Space.ro h dest <;> simp_all))

theorem fastMemoryMetaFrameM_fast_load64 (r : ZStreamRef) (p : BPtr) :
    FastMemoryMetaFrameM r (Zlib.Inffast.load64 p) := by
  unfold Zlib.Inffast.load64
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_fast_store64 (r : ZStreamRef) (out : BPtr) (v : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Inffast.store64 out v) := by
  unfold Zlib.Inffast.store64
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_fast_copy_back (r : ZStreamRef) (out : BPtr) (dist len : UInt32) :
    FastMemoryMetaFrameM r (Zlib.Inffast.copy_back out dist len) := by
  unfold Zlib.Inffast.copy_back
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_load64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_store64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_memcpyB r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))
    | (intro p; cases p; dsimp only)

theorem fastMemoryMetaFrameM_fast_refill64 (r : ZStreamRef) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.refill64 state) := by
  unfold Zlib.Inffast.refill64
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_load64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_fast_copyMatch8 (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.copyMatch8 context state) := by
  unfold Zlib.Inffast.copyMatch8
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_copy_back r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_memcpyB r _ _ _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_fast_dodist8 (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.dodist8 context state) := by
  unfold Zlib.Inffast.dodist8
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_copyMatch8 r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_refill64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_fast_dolen8 (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.dolen8 context state) := by
  unfold Zlib.Inffast.dolen8
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_badData r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_dodist8 r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_refill64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_fast_body8 (r : ZStreamRef) (context : Zlib.Inffast.Ctx)
    (root : context.strm = some r) (state : Zlib.Inffast.L) :
    FastMemoryMetaFrameM r (Zlib.Inffast.inflate_fast_body8 context state) := by
  unfold Zlib.Inffast.inflate_fast_body8
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_dolen8 r _ root _
    | with_reducible exact fastMemoryMetaFrameM_fast_refill64 r _
    | with_reducible exact fastMemoryMetaFrameM_fast_shr64 r _ _
    | with_reducible exact fastMemoryMetaFrameM_store8 r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_load r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

/-- The whole actual fast decoder preserves allocation shape, including
live objects and the exact allocation ledger, on every successful run. -/
theorem fastMemoryMetaFrameM_inflate_fast (r : ZStreamRef) (start : UInt32) :
    FastMemoryMetaFrameM r (Zlib.Inffast.inflate_fast (some r) start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_fast_body r _ rfl _
    | with_reducible exact fastMemoryMetaFrameM_fast_body8 r _ rfl _
    | with_reducible exact fastMemoryMetaFrameM_fast_subn r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_shl32 r _ _
    | with_reducible exact fastMemoryMetaFrameM_fast_chk64 r _
    | with_reducible exact fastMemoryMetaFrameM_ldZ r _
    | with_reducible exact fastMemoryMetaFrameM_ldS r _
    | with_reducible exact fastMemoryMetaFrameM_stS r _ _
    | with_reducible exact fastMemoryMetaFrameM_castI r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_diff r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_lt r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_le r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible exact fastMemoryMetaFrameM_ub r _
    | with_reducible (refine fastMemoryMetaFrameM_ldZ_update r _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))
    | rfl

end Zlib.Inflate.Proofs
