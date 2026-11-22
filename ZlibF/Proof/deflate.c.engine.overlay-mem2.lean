import ZlibF.Proof.«deflate.c.engine.overlay-tiny»
import ZlibF.Proof.«trees.c.overlay-scan-cost»
import ZlibF.Math.DeflateOverlayTiny

/-!
# deflate.c: reference header cost and table equivalences at `memLevel` 2

Defines `refHeaderCost` (the scanned bit-length symbols of both source trees weighted by `κ0` plus
extra bits) and `HeaderRefBound Δ` (proved for `Δ = 245` in `deflate.c.engine.overlay-header-ref`
and consumed in `deflate.c.engine.overlay-mem2c`), together with the static-table equivalences
shared by both small-`memLevel` overlay proofs.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs (dynamicHeaderBits sendLengths fixedLiteralWords)
open Zlib.Trees.Proofs.Out (scanFreqUpTo refWeight)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateOverlayTiny (lengthExtra distanceExtra staticLen mass_split)
set_option autoImplicit false

/-- The cost of the bit-length symbols `scan_tree` counts for both trees of `ready`, each at the
reference code `κ0` plus its extra bits. -/
def refHeaderCost (ready : DeflateState) : Nat :=
  mass (fun k => (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
    scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k) * refWeight k) 19

set_option maxRecDepth 10000 in
/-- The extra-bit tables of the translation agree with `DeflateOverlayTiny`. -/
theorem extra_tables :
    (∀ c : Fin 29, sourceLiteralExtra c.val = lengthExtra c.val) ∧
    (∀ c : Fin 30, sourceDistanceExtra c.val = distanceExtra c.val) := by decide +kernel

set_option maxRecDepth 10000 in
/-- The fixed literal/length code lengths of the translation agree with `staticLen`. -/
theorem fixed_static_len : ∀ v : Fin 286, (fixedLiteralWords v.val).2.toNat = staticLen v.val := by
  decide +kernel

theorem rs_eq_mass (f : Nat → Nat) (n : Nat) : Zlib.Trees.Proofs.GB.rs f n = mass f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Zlib.Trees.Proofs.GB.rs_succ, ih]; rfl

theorem mass_le_of_le (f : Nat → Nat) {n m : Nat} (le : n ≤ m) : mass f n ≤ mass f m := by
  have := mass_split f n (m - n)
  rw [show n + (m - n) = m by omega] at this
  omega

/-- **The header bound at `lit_bufsize = 256`** (proved for `Δ = 245`: `header_ref_bound_256`,
`deflate.c.engine.overlay-header-ref`): the header of every prepared block at `lit_bufsize = 256` is
at most `71 + Δ` plus the `κ0` reference header cost. -/
def HeaderRefBound (Δ : Nat) : Prop :=
  ∀ {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState},
    TinyPrepared h ds d xs mb ready → d.lit_bufsize.toNat = 256 →
    (dynamicHeaderBits ready mb).length ≤ 71 + Δ + refHeaderCost ready

end Zlib.Deflate.Engine.Proofs
