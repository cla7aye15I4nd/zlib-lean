import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.stream-frame-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual Adler byte reads preserve the caller's fixed stream fields. -/
theorem streamFrameM_adler_do1 (r : ZStreamRef) (state : Zlib.Adler32.Locals) (index : Int) :
    StreamFrameM r (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact streamFrameM_bind (streamFrameM_ptr_index r _ _) (fun _ => streamFrameM_pure r _)

theorem streamFrameM_adler_do16 (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    StreamFrameM r (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact streamFrameM_adler_do1 r _ _
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

theorem streamFrameM_adler_step (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    StreamFrameM r (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact streamFrameM_bind (streamFrameM_ptr_load r _) (fun _ =>
    streamFrameM_bind (streamFrameM_ptr_add r _ _) (fun _ => streamFrameM_pure r _))

/-- Every successful execution of the actual whole Adler callee preserves
fixed stream fields, including every length/seed/null-query branch. This
frame theorem assumes no checksum safety or desired callee contract. -/
theorem streamFrameM_adler32_z (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    StreamFrameM r (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact streamFrameM_adler_do16 r _
    | with_reducible exact streamFrameM_adler_step r _
    | with_reducible exact streamFrameM_ptr_index r _ _
    | with_reducible exact streamFrameM_ptr_add r _ _
    | with_reducible exact streamFrameM_pure r _
    | with_reducible (refine streamFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine streamFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply streamFrameM_ite
    | with_reducible (refine streamFrameM_bind ?_ (fun _ => ?_))

theorem streamFrameM_adler32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    StreamFrameM r (Zlib.Adler32.adler32 seed buffer length) := streamFrameM_adler32_z r seed buffer length.toUInt64

theorem streamFrameM_crc_whole (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    StreamFrameM r (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  rfl

theorem streamFrameM_crc32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    StreamFrameM r (Zlib.Crc32.crc32 seed buffer length) := streamFrameM_crc_whole r seed buffer length.toUInt64

end Zlib.Inflate.Proofs
