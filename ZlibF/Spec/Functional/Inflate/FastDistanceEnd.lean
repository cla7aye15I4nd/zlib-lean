import ZlibF.Spec.Common.Inflate.FastEnv
import ZlibF.Spec.Functional.Format.Bits

/-!
# inffast.c: the end of a distance block

`DistEnd` says how a distance block of `inflate_fast` that found no link ends: a match was copied after the extra
bits were read from the bit stream, or an error was found. It reads the extra bits with `readBits` of the format
model. The lemmas about it are in `ZlibF/Proof/inffast.c.dist.lean`.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast Zlib.Inffast.Spec ZlibF.Spec

/-- A distance block that ended (no link): a match of length `len` was copied, or an error was found. `S` is the bit
stream after the code of the distance symbol. -/
def DistEnd {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) (S : List Bool) (i o len : Nat) (E : Code) (l' : L)
    (h' : Heap) : Prop :=
  ¬ DistLink E ∧ l'.againD = false ∧
  ((∃ i' xv rest, i ≤ i' ∧ i' ≤ i + 2 ∧ readBits (E.op &&& 15).toNat S = some (xv, rest) ∧
      l'.broke = false ∧ LS e l' i' (o + len) ∧ Sg e l'.hold.toNat l'.bits.toNat i' = rest ∧
      h' = e.heap (e.mArr e.bg o (E.val.toNat + xv) len A) msg m) ∨
   (∃ i' p, i ≤ i' ∧ i' ≤ i + 2 ∧ l'.broke = true ∧ LS e l' i' o ∧ h' = e.heap A p BAD))

/-- What follows the refill: the stream, and the lookup and the end of the distance block. -/
def RefillPost {α : Bool} (e : EnvG α) (A : Array UInt8) (msg : BPtr) (m : UInt32) (S : List Bool) (i o len : Nat)
    (l' : L) (h' : Heap) : Prop :=
  ∃ i3 H3 b3 E cb, i ≤ i3 ∧ i3 ≤ i + 2 ∧ Sg e H3 b3 i3 = S ∧ H3 < 2 ^ b3 ∧ 15 ≤ b3 ∧ b3 ≤ 30 ∧ cb ≤ 15 ∧
    DistLook e H3 (H3 % 2 ^ e.s0.distbits.toNat) E cb ∧ DistEnd e A msg m (S.drop cb) i3 o len E l' h'

end Zlib.Inffast.Proofs
