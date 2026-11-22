import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.memory-meta-frame-primitives»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual Adler byte reads preserve the caller's allocation metadata. -/
theorem memoryMetaFrameM_adler_do1 (r : ZStreamRef) (state : Zlib.Adler32.Locals) (index : Int) :
    MemoryMetaFrameM r (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact memoryMetaFrameM_bind (memoryMetaFrameM_ptr_index r _ _) (fun _ => memoryMetaFrameM_pure r _)

theorem memoryMetaFrameM_adler_do16 (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    MemoryMetaFrameM r (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  repeat' first
    | with_reducible exact memoryMetaFrameM_adler_do1 r _ _
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem memoryMetaFrameM_adler_step (r : ZStreamRef) (state : Zlib.Adler32.Locals) :
    MemoryMetaFrameM r (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact memoryMetaFrameM_bind (memoryMetaFrameM_ptr_load r _) (fun _ =>
    memoryMetaFrameM_bind (memoryMetaFrameM_ptr_add r _ _) (fun _ => memoryMetaFrameM_pure r _))

/-- Every successful execution of the actual whole Adler callee preserves
allocation metadata, including every length/seed/null-query branch. This
frame theorem assumes no checksum safety or desired callee contract. -/
theorem memoryMetaFrameM_adler32_z (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    MemoryMetaFrameM r (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  repeat' first
    | with_reducible exact memoryMetaFrameM_adler_do16 r _
    | with_reducible exact memoryMetaFrameM_adler_step r _
    | with_reducible exact memoryMetaFrameM_ptr_index r _ _
    | with_reducible exact memoryMetaFrameM_ptr_add r _ _
    | with_reducible exact memoryMetaFrameM_pure r _
    | with_reducible (refine memoryMetaFrameM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine memoryMetaFrameM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply memoryMetaFrameM_ite
    | with_reducible (refine memoryMetaFrameM_bind ?_ (fun _ => ?_))

theorem memoryMetaFrameM_adler32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    MemoryMetaFrameM r (Zlib.Adler32.adler32 seed buffer length) := memoryMetaFrameM_adler32_z r seed buffer length.toUInt64

theorem memoryMetaFrameM_crc_whole (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    MemoryMetaFrameM r (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  rfl

theorem memoryMetaFrameM_crc32 (r : ZStreamRef) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    MemoryMetaFrameM r (Zlib.Crc32.crc32 seed buffer length) := memoryMetaFrameM_crc_whole r seed buffer length.toUInt64

end Zlib.Inflate.Proofs
