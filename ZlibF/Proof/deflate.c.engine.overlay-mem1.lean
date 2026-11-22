import ZlibF.Proof.«deflate.c.engine.overlay-mem2»
import ZlibF.Proof.«deflate.c.engine.overlay-choice-row»
import ZlibF.Proof.«trees.c.overlay-scan-region»
import ZlibF.Proof.«trees.c.build.two-leaves»
import ZlibF.Math.DeflateOverlayTiny

/-!
# deflate.c: the reference header cost at `memLevel` 1

The cost of the scanned bit-length symbols under the reference code `κ1`
(`DeflateOverlayTiny.refLen1`), extra bits included: `refHeaderCost128`. The header bound
`HeaderRefBound128W` and the overlay room at `lit_bufsize = 128` (`overlay-mem1w`) are stated with
it.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (sendLengths)
open Zlib.Trees.Proofs.Out (scanFreqUpTo)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateOverlayTiny (refLen1)
set_option autoImplicit false

/-- The cost of bit-length symbol `k` under `κ1`, extra bits included. -/
def refWeight1 (k : Nat) : Nat := refLen1 k + Zlib.Trees.Proofs.Out.blExtraBits k

/-- The cost of the bit-length symbols `scan_tree` counts for both trees of `ready`, under `κ1`. -/
def refHeaderCost128 (ready : DeflateState) : Nat :=
  mass (fun k => (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
    scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k) * refWeight1 k) 19

end Zlib.Deflate.Engine.Proofs
