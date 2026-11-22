import ZlibF.Proof.«deflate.c.engine.fill-history»
import ZlibF.Spec.Common.Streams
import ZlibF.Spec.Functional.Checksums
import ZlibF.Spec.Functional.Api.Compress

/-! # Resumed fill from the public buffer and engine boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem read_stream_accounting (z : ZStream) (n : UInt32) (ref : BRef) (io : Nat) (checksum : UInt64)
    (pointer : z.next_in = .ref ref io) (bound : n.toNat ≤ z.avail_in.toNat) :
    StreamAccounting z (readStream z n ref io checksum) n.toNat 0 := by
  have sub : (z.avail_in - n).toNat = z.avail_in.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr bound)
  unfold StreamAccounting readStream
  refine ⟨bound, by omega, ?_, by simp, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [sub]
    omega
  · rw [pointer]
    rfl
  · cases z.next_out <;> simp [advance]

end Zlib.Deflate.Engine.Proofs
