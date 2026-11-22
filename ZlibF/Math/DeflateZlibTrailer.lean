import ZlibF.Spec.Functional.Format.Wrapper
import ZlibF.Math.DeflateFixedBlock

/-! # The default compressor's two trailer words encode big-endian Adler-32 -/

namespace Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- Bytes of the actual two word stores, in their source order. -/
def zlibTrailerWord (a : UInt64) : List UInt8 :=
  [((a >>> 16).toUInt32 >>> 8).toUInt8,
   ((a >>> 16).toUInt32 &&& 0xff).toUInt8,
   ((a &&& 0xffff).toUInt32 >>> 8).toUInt8,
   ((a &&& 0xffff).toUInt32 &&& 0xff).toUInt8]

/-- Both machine-word truncations retain exactly the independent format's
four low bytes. High bits of the machine checksum need no assumption. -/
theorem zlib_trailer_word (a : UInt64) : zlibTrailerWord a = ZlibF.Spec.be32 a.toNat := by
  have mask8 (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
  have mask16 (n : Nat) : n &&& 65535 = n % 65536 := Nat.and_two_pow_sub_one_eq_mod n 16
  unfold zlibTrailerWord ZlibF.Spec.be32
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt64.toNat_toUInt32,
      UInt64.toNat_shiftRight, mask8, mask16, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow] <;>
    omega

end Zlib.Deflate.Engine.Proofs
