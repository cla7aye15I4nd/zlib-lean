import ZlibF.Spec.Common.Inflate.FastEnv

/-!
# Provenance of the fast decoder's bit buffer

Scalar bounds do not relate the buffer's value to input already read.
The origin invariant records both consumed-bit accounting and the actual
remaining stream. Whole-byte rollback must preserve that exact stream.
-/

namespace Zlib.Inffast.Spec.Origin
open C Zlib.Inffast Zlib.Inffast.Proofs

/-- The complete logical input remaining at entry to this fast call. -/
def initial (e : Env) : List Bool := Sg e e.s0.hold.toNat e.s0.bits.toNat e.i0

/-- Current buffered bits followed by unread bytes are the exact suffix
after consuming `used` entry bits. The accounting prevents an unrelated
suffix or guessed buffered value from satisfying the invariant. -/
structure Inv (e : Env) (hold bits input used : Nat) : Prop where
  inputLower : e.i0 ≤ input
  inputUpper : input ≤ e.i0 + e.sm0.avail_in.toNat
  normalized : hold < 2 ^ bits
  accounting : used + bits = e.s0.bits.toNat + 8 * (input - e.i0)
  stream : Sg e hold bits input = (initial e).drop used

end Zlib.Inffast.Spec.Origin
