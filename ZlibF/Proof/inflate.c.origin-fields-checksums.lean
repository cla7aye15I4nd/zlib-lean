import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.origin-fields-stores»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! These source proofs establish the origin-field frame for every successful
checksum execution. Fault freedom and checksum meaning are proved separately. -/

theorem originFieldFrameM_adler_do1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) (index : Int) :
    OriginFieldFrameM r owner (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact originFieldFrameM_bind (originFieldFrameM_ptr_index r owner _ _) (fun _ => originFieldFrameM_pure r owner _)

theorem originFieldFrameM_adler_do16 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    OriginFieldFrameM r owner (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact originFieldFrameM_adler_do1 r owner _ _
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_adler_step (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    OriginFieldFrameM r owner (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact originFieldFrameM_bind (originFieldFrameM_ptr_load r owner _) (fun _ =>
    originFieldFrameM_bind (originFieldFrameM_ptr_add r owner _ _) (fun _ => originFieldFrameM_pure r owner _))

theorem originFieldFrameM_adler32_z (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    OriginFieldFrameM r owner (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact originFieldFrameM_adler_do16 r owner _
    | with_reducible exact originFieldFrameM_adler_step r owner _
    | with_reducible exact originFieldFrameM_ptr_index r owner _ _
    | with_reducible exact originFieldFrameM_ptr_add r owner _ _
    | with_reducible exact originFieldFrameM_pure r owner _
    | with_reducible (refine originFieldFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine originFieldFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply originFieldFrameM_ite
    | with_reducible (refine originFieldFrameM_bind ?_ (fun _ => ?_))

theorem originFieldFrameM_adler32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OriginFieldFrameM r owner (Zlib.Adler32.adler32 seed buffer length) := originFieldFrameM_adler32_z r owner seed buffer length.toUInt64

theorem originFieldFrameM_crc_whole (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    OriginFieldFrameM r owner (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  exact OriginFieldFrame.refl r owner h

theorem originFieldFrameM_crc32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OriginFieldFrameM r owner (Zlib.Crc32.crc32 seed buffer length) := originFieldFrameM_crc_whole r owner seed buffer length.toUInt64

end Zlib.Inflate.Proofs
