import ZlibF.Spec.Functional.Crc32ByteViews
import ZlibF.Proof.«crc32.c»

/-!
# CRC over all represented byte views

The physical loads and pointer updates use the actual byte-array view.
Alignment observes its arbitrary stable origin residue. The checksum
algebra is reused without changing the independent CRC definition.
-/

namespace Zlib.Crc32.Proofs.ViewsProof
open C Zlib.Crc32.Proofs

theorem crc32_z_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt64) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32_z crc (.ref ref off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) :=
  crc32_z_correct_view h hs crc ref off bs hb len hlen

theorem crc32_correct (h : Heap) (hs : StaticsOK h) (crc : UInt64) (ref : BRef) (off : Nat) (bs : Array UInt8)
    (hb : Space.get h ref = some bs) (len : UInt32) (hlen : off + len.toNat ≤ bs.size) :
    C.run (crc32 crc (.ref ref off) len) h =
      .ok (((ZlibF.Spec.crc32Update crc.toUInt32 ((bs.toList.drop off).take len.toNat))).toUInt64, h) :=
  crc32_correct_view h hs crc ref off bs hb len hlen

end Zlib.Crc32.Proofs.ViewsProof

namespace Zlib.Crc32.Proofs
open C

/-- `uLong crc32_z(uLong crc, const unsigned char *buf, z_size_t len)`.
The exact general-view goal includes every represented origin residue and
leaves all heap fields unchanged. -/
theorem crc32_z_all_byte_views : Spec.ByteViews.Goal.crc32_z_all_byte_views := by
  intro h hs crc ref offset bytes hg len readable
  exact ViewsProof.crc32_z_correct h hs crc ref offset bytes hg len readable

/-- `uLong crc32(uLong crc, const unsigned char *buf, uInt len)`.
The compatibility entry has the same complete byte-view and layout scope. -/
theorem crc32_all_byte_views : Spec.ByteViews.Goal.crc32_all_byte_views := by
  intro h hs crc ref offset bytes hg len readable
  exact ViewsProof.crc32_correct h hs crc ref offset bytes hg len readable

end Zlib.Crc32.Proofs
