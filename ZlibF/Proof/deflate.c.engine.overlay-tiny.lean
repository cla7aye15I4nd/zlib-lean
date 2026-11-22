import ZlibF.Proof.«deflate.c.engine.overlay-gain»
import ZlibF.Math.DeflateOverlayFibActual
import ZlibF.Proof.«trees.c.universal-overlay-mid»

/-!
# deflate.c: a second route to `TinyOverlay` (statements only)

A route to the overlay room at `memLevel` 1 and 2 (`lit_bufsize < 512`). Split on the gain
`G` of the block:

* `G + 30 ≤ 8 * lit_bufsize`: the dynamic choice bounds the header and the excess (half A,
  `dynamic_overlay_of_gain`);
* otherwise: a header bound `Hb` (`HeaderFibBound`), the excess at the actual frequencies (B3,
  `excess_fib_actual`) and the link `LinkC` give the budget.

`HeaderFibBound` and `LinkC` are not proved, and no theorem uses them. `TinyOverlay`
itself is proved on another route: `tinyOverlay` (`deflate.c.engine.overlay-header-ref`) from the
reference-code header bounds `header_ref_bound_256` and `header_ref_bound_128w`. Both hypotheses
here take the header bound `Hb` as a parameter and are stated for every prepared dynamic block
(`TinyPrepared`) on any heap.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost)
open ZlibF.Math.DeflateOverlaySmall (excessFibActual)
open Zlib.Deflate.Universal.Block (DynamicRoom DynamicOverlay TinyOverlay treesInvAt_put)
set_option autoImplicit false

/-- A prepared dynamic block at `memLevel` 1 or 2: the block entry `d` with its symbols `xs`, the
state `ready` after both trees and the bit-length tree, and every fact `DynamicOverlay` supplies. -/
structure TinyPrepared (h : Heap) (ds : Nat) (d : DeflateState) (xs : List Symbol) (mb : Int32)
    (ready : DeflateState) : Prop where
  base : ∃ pb buf, TreesInvAt h ds d pb buf ∧ SymbolLedger buf d xs
  clear : BlockInit.BlockClear d
  tiny : d.lit_bufsize.toNat < 512
  run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds ready)
  frame : TreePreparationFrame d ready
  header : (dynamicHeaderBits ready mb).length ≤ 2283
  excess : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3)
  dynamic : ¬ (byteCost ready.static_len ≤ byteCost ready.opt_len ∨ (ready.strategy == Z_FIXED) = true)

/-- **B1/B2 (not proved; `tinyOverlay` does not need it)**: the header of every prepared tiny block is at most `Hb` (for the Fibonacci
route: `71 + Σ_c f_c (λ7(f_c, W_bl) + xbits_c) + push`, with zlib's 7-bit repair). -/
def HeaderFibBound (Hb : DeflateState → Int32 → List Symbol → Nat) : Prop :=
  ∀ {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState},
    TinyPrepared h ds d xs mb ready → (dynamicHeaderBits ready mb).length ≤ Hb ready mb xs

/-- **C (not proved; `tinyOverlay` does not need it)**: when the gain is large, the header bound, the excess at the actual frequencies
and the 25-bit margin fit `8 * lit_bufsize`. -/
def LinkC (Hb : DeflateState → Int32 → List Symbol → Nat) : Prop :=
  ∀ {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState},
    TinyPrepared h ds d xs mb ready → 8 * d.lit_bufsize.toNat < dynamicGain ready xs + 30 →
    Hb ready mb xs + excessFibActual (d.lit_bufsize.toNat + 2) (literalFrequency symbolLengthCode xs)
      (distanceFrequency dcodeN xs) sourceLiteralExtra sourceDistanceExtra + 25 ≤ 8 * d.lit_bufsize.toNat

end Zlib.Deflate.Engine.Proofs
