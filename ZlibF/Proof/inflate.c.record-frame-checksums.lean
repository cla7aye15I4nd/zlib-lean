import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.record-frame-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! These source proofs establish the record frame for every successful
checksum execution. Fault freedom and checksum meaning are proved separately. -/

theorem recordFrameM_adler_do1 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) (index : Int) :
    RecordFrameM r owner (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact recordFrameM_bind (recordFrameM_ptr_index r owner _ _) (fun _ => recordFrameM_pure r owner _)

theorem recordFrameM_adler_do16 (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    RecordFrameM r owner (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact recordFrameM_adler_do1 r owner _ _
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_adler_step (r : ZStreamRef) (owner : InflateStatePtr) (state : Zlib.Adler32.Locals) :
    RecordFrameM r owner (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact recordFrameM_bind (recordFrameM_ptr_load r owner _) (fun _ =>
    recordFrameM_bind (recordFrameM_ptr_add r owner _ _) (fun _ => recordFrameM_pure r owner _))

theorem recordFrameM_adler32_z (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    RecordFrameM r owner (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact recordFrameM_adler_do16 r owner _
    | with_reducible exact recordFrameM_adler_step r owner _
    | with_reducible exact recordFrameM_ptr_index r owner _ _
    | with_reducible exact recordFrameM_ptr_add r owner _ _
    | with_reducible exact recordFrameM_pure r owner _
    | with_reducible (refine recordFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine recordFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply recordFrameM_ite
    | with_reducible (refine recordFrameM_bind ?_ (fun _ => ?_))

theorem recordFrameM_adler32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    RecordFrameM r owner (Zlib.Adler32.adler32 seed buffer length) := recordFrameM_adler32_z r owner seed buffer length.toUInt64

theorem recordFrameM_crc_whole (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    RecordFrameM r owner (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  exact RecordFrame.refl r owner h

theorem recordFrameM_crc32 (r : ZStreamRef) (owner : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    RecordFrameM r owner (Zlib.Crc32.crc32 seed buffer length) := recordFrameM_crc_whole r owner seed buffer length.toUInt64

end Zlib.Inflate.Proofs
