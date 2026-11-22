import ZlibF.Math.DeflateSymbolBudget
import ZlibF.Proof.«deflate.c.engine.slow-caller-storage»

/-! # Input accounting and symbol room for the actual outer loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem advance_add (p : BPtr) (first second : Nat) :
    advance (advance p first) second = advance p (first + second) := by
  cases p <;> simp [advance, Nat.add_assoc]

theorem remaining_below_fuel {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) :
    d.lookahead.toNat + z.avail_in.toNat + 1 < fuel := by
  have window := slide_window_sizes boundary.good
  have size := boundary.good.inv.wsz
  have range := boundary.range
  have input := z.avail_in.toNat_lt
  dsimp only [fillEnd] at range
  change d.lookahead.toNat + z.avail_in.toNat + 1 < 18446744073709551616
  omega

end Zlib.Deflate.Engine.Proofs
