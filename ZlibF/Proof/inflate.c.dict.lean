import ZlibF.Proof.«inflate.c.ring»
import ZlibF.Proof.«adler32.c»

/-!
# inflate.c: `inflateGetDictionary` and `inflateSetDictionary`
-/

namespace Zlib.Inflate.Spec
open C

/-- The caller's dictionary buffer after `inflateGetDictionary` copied the window: `whave` bytes at offset `off`,
oldest first, in two pieces (`window[wnext .. whave)`, then `window[0 .. wnext)`). -/
def getDictBytes (D win : Array UInt8) (off wn wh : Nat) : Array UInt8 :=
  copyRange (copyRange D win off wn (wh - wn)) win (off + wh - wn) 0 wn

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem mode_mem : HEAD ≤ MEM ∧ MEM ≤ SYNC := by decide

theorem adler32_init (H : Heap) : Zlib.Adler32.adler32 0 .null 0 H = .ok (1, H) := by
  simp [Zlib.Adler32.adler32, Zlib.Adler32.adler32_z]

end Zlib.Inflate.Proofs
