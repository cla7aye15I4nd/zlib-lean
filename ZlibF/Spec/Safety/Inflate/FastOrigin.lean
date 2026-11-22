import ZlibF.Spec.Common.Inflate.InflateFast
import ZlibF.Spec.Common.Inflate.InflateFastOrigin
import ZlibF.Spec.Common.Inflate.InflateFastCallOrigin

/-!
# Goals on the origin of the fast decoder's bit buffer

The bit buffer and unread input of the fast decoder are the exact remaining source input,
stated over `ZlibF/Spec/Common/Inflate/InflateFastOrigin.lean` and
`ZlibF/Spec/Common/Inflate/InflateFastCallOrigin.lean`.
-/

namespace Zlib.Inffast.Spec.Origin
open C Zlib.Inffast Zlib.Inffast.Proofs

def Goal.initial_origin : Prop :=
  ∀ e : Env, Inv e e.s0.hold.toNat e.s0.bits.toNat e.i0 0

/-- Reading the actual next byte preserves the source suffix without
consuming any logical bit. This is the data equation used by actual pull. -/
def Goal.pull_preserves_origin : Prop :=
  ∀ (e : Env) (hold bits input used : Nat),
    Inv e hold bits input used → input < e.i0 + e.sm0.avail_in.toNat →
    Inv e (hold + (e.IN.getD input 0).toNat * 2 ^ bits) (bits + 8) (input + 1) used

/-- Dropping available low bits consumes exactly that entry-stream prefix. -/
def Goal.drop_preserves_origin : Prop :=
  ∀ (e : Env) (hold bits input used count : Nat),
    Inv e hold bits input used → count ≤ bits →
    Inv e (hold / 2 ^ count) (bits - count) input (used + count)

/-- Returning unused whole bytes restores the exact same remaining input,
not merely its length. The retained low bits are the actual mask result.
The byte rollback bound follows from origin accounting and entry bits < 8. -/
def Goal.rollback_preserves_origin : Prop :=
  ∀ (e : Env) (hold bits input used : Nat),
    Inv e hold bits input used →
    let returned := bits / 8
    let residual := bits % 8
    returned ≤ input - e.i0 ∧
    Sg e (hold % 2 ^ residual) residual (input - returned) = Sg e hold bits input ∧
    Inv e (hold % 2 ^ residual) residual (input - returned) used

/-- The actual input-byte load and register updates establish the same
origin relation. The bound is the source pull helper's internal bound. -/
def Goal.actual_pull_preserves_origin : Prop :=
  ∀ (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    LS e l i o → Inv e l.hold.toNat l.bits.toNat i used →
    l.bits.toNat ≤ 22 → i < e.i0 + e.sm0.avail_in.toNat → e.InputFrame bytes i →
    ∃ l',
      C.run (pull l) (e.heap bytes msg mode) = .ok (l', e.heap bytes msg mode) ∧
      LS e l' (i + 1) o ∧ Inv e l'.hold.toNat l'.bits.toNat (i + 1) used

/-- The source shift and unsigned count subtraction consume exactly the
available low bits, with no heap effect or unchecked shift. -/
def Goal.actual_drop_preserves_origin : Prop :=
  ∀ (e : Env) (h : Heap) (l : L) (i o used : Nat) (count : UInt32),
    LS e l i o → Inv e l.hold.toNat l.bits.toNat i used →
    count.toNat ≤ l.bits.toNat →
    C.run (do
      let hold ← shr64 l.hold count.toUInt64
      pure { l with hold, bits := l.bits - count }) h = .ok (dropL l count, h) ∧
    LS e (dropL l count) i o ∧
    Inv e (dropL l count).hold.toNat (dropL l count).bits.toNat i (used + count.toNat)

/-- Actual epilogue pointer rollback and masking preserve the same exact
stream. This source prefix is checked separately from counter writeback;
the loop still has to establish origin at its exit. -/
def Goal.actual_rollback_preserves_origin : Prop :=
  ∀ (e : Env) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    LS e l i o → Inv e l.hold.toNat l.bits.toNat i used → e.InputFrame bytes i →
    let returned := l.bits >>> 3
    let bits := l.bits - (returned <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    C.run (do
      let input ← subn l.in_ returned
      let mask ← shl32 1 bits
      pure (input, l.hold &&& (mask - 1).toUInt64, bits)) (e.heap bytes msg mode) =
        .ok ((.ref e.ib (i - l.bits.toNat / 8), hold, bits), e.heap bytes msg mode) ∧
    bits.toNat < 8 ∧
    Inv e hold.toNat bits.toNat (i - l.bits.toNat / 8) used ∧
    Sg e hold.toNat bits.toNat (i - l.bits.toNat / 8) = Sg e l.hold.toNat l.bits.toNat i

end Zlib.Inffast.Spec.Origin

namespace Zlib.Inffast.Spec.BodyOrigin
open C Zlib.Inffast Zlib.Inffast.Proofs

/-- Actual bit movement consumes a nonnegative exact prefix of the
original fast-call input and retains the complete existing body result.
This property alone does not assign DEFLATE meanings to the consumed bits. -/
def Goal.actual_body_preserves_origin : Prop :=
  ∀ (e : Env) (c : Ctx) (bytes : Array UInt8) (msg : BPtr) (mode : UInt32)
    (l : L) (i o used : Nat),
    StepPre e c bytes l i o → Origin.Inv e l.hold.toNat l.bits.toNat i used →
    ∃ (l' : L) (after : Heap),
      C.run (inflate_fast_body c l) (e.heap bytes msg mode) = .ok (l', after) ∧
      StepPost e bytes msg mode i o l' after ∧
      ∃ i' o' used',
        LS e l' i' o' ∧ Origin.Inv e l'.hold.toNat l'.bits.toNat i' used' ∧ used ≤ used'

end Zlib.Inffast.Spec.BodyOrigin

namespace Zlib.Inffast.Spec.CallOrigin
open C Zlib.Inffast Zlib.Inffast.Proofs

/-- The actual whole call preserves the source suffix through every
body and rollback, retaining its full existing safety/frame result.
The actual body-origin theorem must be proved, not taken as a premise. -/
def Goal.actual_fast_preserves_origin : Prop :=
  ∀ e : Env, ∃ after,
    C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧
    FastPost e after ∧ HasOrigin e after

end Zlib.Inffast.Spec.CallOrigin
