import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.output-counter-frame-primitives»

namespace Zlib.Inflate.Proofs.OutputCounter
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem outputCounterM_adler_do1 (r : ZStreamRef) (state : Zlib.Adler32.Locals) (index : Int) :
    OutputCounterM r (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact outputCounterM_bind (outputCounterM_ptr_index r _ _) (fun _ => outputCounterM_pure r _)

theorem outputCounterM_adler_do16 (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    OutputCounterM r (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact outputCounterM_adler_do1 r _ _
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_adler_step (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    OutputCounterM r (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact outputCounterM_bind (outputCounterM_ptr_load r _) (fun _ =>
    outputCounterM_bind (outputCounterM_ptr_add r _ _) (fun _ => outputCounterM_pure r _))

theorem outputCounterM_adler32_z (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    OutputCounterM r (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact outputCounterM_adler_do16 r _
    | with_reducible exact outputCounterM_adler_step r _
    | with_reducible exact outputCounterM_ptr_index r _ _
    | with_reducible exact outputCounterM_ptr_add r _ _
    | with_reducible exact outputCounterM_pure r _
    | with_reducible (refine outputCounterM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine outputCounterM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply outputCounterM_ite
    | with_reducible (refine outputCounterM_bind ?_ (fun _ => ?_))

theorem outputCounterM_adler32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OutputCounterM r (Zlib.Adler32.adler32 seed buffer length) := outputCounterM_adler32_z r seed buffer length.toUInt64

theorem outputCounterM_crc_whole (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    OutputCounterM r (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  rfl

theorem outputCounterM_crc32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    OutputCounterM r (Zlib.Crc32.crc32 seed buffer length) := outputCounterM_crc_whole r seed buffer length.toUInt64

end Zlib.Inflate.Proofs.OutputCounter
