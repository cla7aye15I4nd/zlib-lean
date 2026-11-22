import ZlibF.Proof.«public-adler-update»
import ZlibF.Proof.«inflate.c.output-invariant»
import ZlibF.Spec.Functional.Checksums

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual zlib-wrapper checksum update accepts every represented
readable byte view. Its value follows from the proved translated Adler
callee for every seed, including the one-byte special case. -/
theorem UPDATE_CHECK_zlib_view {h : Heap} {zs : Nat} {s : InflateState} {ref : BRef}
    {off : Nat} {array : Array UInt8} {len : UInt32}
    (state : h.istates zs = some s) (flags : s.flags = 0)
    (get : Space.get h ref = some array) (fit : off + len.toNat ≤ array.size) (check : UInt64) :
    UPDATE_CHECK (some (.tab zs)) check (.ref ref off) len h =
      .ok (adlerValue check ((array.toList.drop off).take len.toNat), h) := by
  have run := ZlibF.Spec.Public.AdlerUpdateProof.adler_z_any_public get check off len.toUInt64
    (by simpa only [UInt32.toNat_toUInt64] using fit)
  have update : Zlib.Adler32.adler32 check (.ref ref off) len h =
      .ok (adlerValue check ((array.toList.drop off).take len.toNat), h) := by
    simpa only [C.run, Zlib.Adler32.adler32, UInt32.toNat_toUInt64] using run
  unfold UPDATE_CHECK
  simp only [bind_app, rdS, ldInflateState_tab state, flags, pure_app]
  change Zlib.Adler32.adler32 check (.ref ref off) len h = _
  with_reducible exact update

end Zlib.Inflate.Proofs
