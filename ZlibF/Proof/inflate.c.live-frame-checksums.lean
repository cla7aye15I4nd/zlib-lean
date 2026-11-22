import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.live-frame-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual Adler byte reads preserve the caller's allocation metadata. -/
theorem fastMemoryMetaFrameM_adler_do1 (r : ZStreamRef) (state : Zlib.Adler32.Locals) (index : Int) :
    FastMemoryMetaFrameM r (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_index r _ _) (fun _ => fastMemoryMetaFrameM_pure r _)

theorem fastMemoryMetaFrameM_adler_do16 (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    FastMemoryMetaFrameM r (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_adler_do1 r _ _
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_adler_step (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    FastMemoryMetaFrameM r (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_load r _) (fun _ =>
    fastMemoryMetaFrameM_bind (fastMemoryMetaFrameM_ptr_add r _ _) (fun _ => fastMemoryMetaFrameM_pure r _))

/-- Every successful execution of the actual whole Adler callee preserves
allocation metadata, including every length/seed/null-query branch. This
frame theorem assumes no checksum safety or desired callee contract. -/
theorem fastMemoryMetaFrameM_adler32_z (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact fastMemoryMetaFrameM_adler_do16 r _
    | with_reducible exact fastMemoryMetaFrameM_adler_step r _
    | with_reducible exact fastMemoryMetaFrameM_ptr_index r _ _
    | with_reducible exact fastMemoryMetaFrameM_ptr_add r _ _
    | with_reducible exact fastMemoryMetaFrameM_pure r _
    | with_reducible (refine fastMemoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine fastMemoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply fastMemoryMetaFrameM_ite
    | with_reducible (refine fastMemoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem fastMemoryMetaFrameM_adler32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    FastMemoryMetaFrameM r (Zlib.Adler32.adler32 seed buffer length) := fastMemoryMetaFrameM_adler32_z r seed buffer length.toUInt64

theorem fastMemoryMetaFrameM_crc_whole (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  rfl

theorem fastMemoryMetaFrameM_crc32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    FastMemoryMetaFrameM r (Zlib.Crc32.crc32 seed buffer length) := fastMemoryMetaFrameM_crc_whole r seed buffer length.toUInt64

end Zlib.Inflate.Proofs
