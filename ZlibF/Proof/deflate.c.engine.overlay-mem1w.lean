import ZlibF.Proof.«deflate.c.engine.overlay-lengths»

/-!
# deflate.c: the overlay room at `memLevel` 1 with a repair excess growing with `W`

At `lit_bufsize = 128`, every prepared dynamic block satisfies `H + bitExcess ≤ 999`
(`header_excess_128_w`), from the header hypothesis `HeaderRefBound128W α` with `α ≤ 29`
(instantiated at `α = 29` by `header_ref_bound_128w`): `scan_cost_region` bounds
`2 * refHeaderCost128 + bitLengthCount` by the region charges under `κ1` plus `2`, and
`prepared_tiny_facts` supplies the Kraft, Fibonacci, symbol-count, match-balance, and choice-row
bounds to `DeflateOverlayTiny.header_excess_cert_128`. The order-free budget (`overlay_budget_128_w`)
and overlay room (`dynamic_overlay_128_w`) follow.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicHeaderBits sendLengths TK)
open Zlib.Trees.Proofs.Out (TreesInvAt scanFreqUpTo blExtraBits_zero mass_mul_add
  ScanCharges regionCharge scan_cost_region)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateOverlayTiny (refLen1 literalRegionCharge128 lengthRegionCharge128
  distanceRegionCharge128 literalCharge128 header_excess_cert_128)
open Zlib.Deflate.Universal.Block (DynamicOverlay treesInvAt_put)
set_option autoImplicit false

/-- The number `W` of bit-length symbols `scan_tree` counts for both trees of `ready`. -/
def bitLengthCount (ready : DeflateState) : Nat :=
  mass (fun k => scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
    scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k) 19

/-- **The header bound at `lit_bufsize = 128`, with the repair excess growing with `W`** (proved for
`α = 29`: `header_ref_bound_128w`, `deflate.c.engine.overlay-header-ref`): twice the header is at
most `2 * (71 + α) + W` plus twice the `κ1` reference header cost. -/
def HeaderRefBound128W (α : Nat) : Prop :=
  ∀ {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState},
    TinyPrepared h ds d xs mb ready → d.lit_bufsize.toNat = 128 →
    2 * (dynamicHeaderBits ready mb).length ≤ 2 * (71 + α) + bitLengthCount ready + 2 * refHeaderCost128 ready

/-- Region credits and zero-entry charges of the literal/length scan at `B = 128`: credit `10` and
`1` per zero in the literal region (`0..256`), `2` and `4` per zero in the length region. -/
def literalA_w (i : Nat) : Nat := if i ≤ 256 then 10 else 2
def literalB_w (i : Nat) : Nat := if i ≤ 256 then 1 else 4

theorem charges_128_w :
    ScanCharges (fun k => 2 * refWeight1 k + 1) distanceRegionCharge128 literalA_w literalB_w ∧
    ScanCharges (fun k => 2 * refWeight1 k + 1) distanceRegionCharge128 (fun _ => 0) (fun _ => 5) := by
  have short : ∀ x, 1 ≤ x → x ≤ 15 → 2 * refWeight1 x + 1 ≤ distanceRegionCharge128 x := by
    intro x h1 h2
    simp [refWeight1, blExtraBits_zero h2, distanceRegionCharge128, show x ≠ 0 by omega]
  have rep : ∀ x, 1 ≤ x → x ≤ 15 → 2 * refWeight1 16 + 1 ≤ 3 * distanceRegionCharge128 x := by
    intro x h1 h2
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
      simp [refWeight1, refLen1, distanceRegionCharge128, Zlib.Trees.Proofs.Out.blExtraBits] at h1 h2 ⊢
  have w0 : 2 * refWeight1 0 + 1 = 5 := rfl
  have w17 : 2 * refWeight1 17 + 1 = 13 := rfl
  have w18 : 2 * refWeight1 18 + 1 = 21 := rfl
  refine ⟨⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩, ⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;>
    simp only [literalA_w, literalB_w, w0, w17, w18] <;> (try split) <;> omega

theorem literal_regionCharge_w (L : Nat → Nat) (i : Nat) :
    regionCharge L distanceRegionCharge128 literalA_w literalB_w i = literalCharge128 i (L i) := by
  unfold regionCharge literalCharge128 literalRegionCharge128 lengthRegionCharge128
    distanceRegionCharge128 literalA_w literalB_w
  by_cases r : i ≤ 256 <;> by_cases z : L i = 0 <;> simp [r, z] <;> omega

theorem distance_regionCharge_w (L : Nat → Nat) (i : Nat) :
    regionCharge L distanceRegionCharge128 (fun _ => 0) (fun _ => 5) i = distanceRegionCharge128 (L i) := by
  unfold regionCharge distanceRegionCharge128
  by_cases z : L i = 0 <;> simp [z]

/-- **Header plus excess at `lit_bufsize = 128`**: at most `983` bits for `α ≤ 29`. -/
theorem header_excess_128_w {α : Nat} (small : α ≤ 29) (headerBound : HeaderRefBound128W α)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 128) :
    (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 983 := by
  have hdrBound := headerBound prepared size
  obtain ⟨⟨ll, fl, dl, fd, lenL, lenD, kL, kD, leafL, eob, leafD, symbols, balance, choice, excess,
    maxL256, maxL_lt, maxD_lt, lowL, lowD⟩⟩ := prepared_tiny_facts prepared (by omega)
  rw [size] at leafL eob leafD symbols
  have bound16 : ∀ (tk : TK) (n : Nat), sendLengths ready tk n < 2 ^ 16 := fun _ _ => UInt16.toNat_lt _
  have keepL : ∀ i, sendLengths ready .lit i = 0 →
      literalA_w (i + 1) = literalA_w i ∧ literalB_w (i + 1) = literalB_w i := by
    intro i z
    by_cases e : i = 256
    · subst e; rw [lowL 256 maxL256] at z; have := eob.2.1; omega
    · simp only [literalA_w, literalB_w]
      by_cases r : i ≤ 255
      · simp [show i + 1 ≤ 256 by omega, show i ≤ 256 by omega]
      · simp [show ¬ (i + 1 ≤ 256) by omega, show ¬ (i ≤ 256) by omega]
  have scanL := scan_cost_region (sendLengths ready .lit) _ _ _ _ charges_128_w.1 (bound16 .lit) keepL
    (ready.l_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowL i (by omega)]; exact lenL i (by omega))
  have scanD := scan_cost_region (sendLengths ready .dist) _ _ _ _ charges_128_w.2 (bound16 .dist)
    (fun _ _ => ⟨rfl, rfl⟩) (ready.d_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowD i (by omega)]; exact lenD i (by omega))
  have endA : literalA_w (ready.l_desc.max_code.toInt.toNat + 1) = 2 := by
    unfold literalA_w; rw [ite_eq_right (by omega)]
  rw [endA] at scanL
  have chargesL : mass (regionCharge (sendLengths ready .lit) distanceRegionCharge128 literalA_w literalB_w)
      (ready.l_desc.max_code.toInt.toNat + 1) ≤ mass (fun v => literalCharge128 v (ll v)) 286 := by
    rw [mass_congr (g := fun v => literalCharge128 v (ll v)) (fun i hi => by
      rw [literal_regionCharge_w, lowL i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have chargesD : mass (regionCharge (sendLengths ready .dist) distanceRegionCharge128 (fun _ => 0) (fun _ => 5))
      (ready.d_desc.max_code.toInt.toNat + 1) ≤ mass (fun v => distanceRegionCharge128 (dl v)) 30 := by
    rw [mass_congr (g := fun v => distanceRegionCharge128 (dl v)) (fun i hi => by
      rw [distance_regionCharge_w, lowD i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have twice : 2 * refHeaderCost128 ready + bitLengthCount ready ≤
      mass (fun v => literalCharge128 v (ll v)) 286 +
      mass (fun v => distanceRegionCharge128 (dl v)) 30 + 2 := by
    unfold refHeaderCost128 bitLengthCount
    rw [mass_mul_add, Nat.mul_add, ← mass_mul_left, ← mass_mul_left, ← mass_add]
    have eL : ∀ k, 2 * (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k *
        refWeight1 k) + 2 * (scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k *
        refWeight1 k) + (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k +
        scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k) =
        scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k * (2 * refWeight1 k + 1) +
        scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k * (2 * refWeight1 k + 1) := by
      intro k
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      omega
    rw [← mass_add, mass_congr (fun k _ => eL k), mass_add]
    omega
  have cert := header_excess_cert_128 ll fl dl fd (dynamicHeaderBits ready mb).length (α + 1) (by omega)
    kL kD leafL eob leafD symbols balance (by omega) choice
  omega

/-- **The order-free budget at `memLevel` 1**, from the header bound with `α ≤ 29`. -/
theorem overlay_budget_128_w {α : Nat} (small : α ≤ 29) (headerBound : HeaderRefBound128W α)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 128) :
    OverlayBudget ready mb xs := by
  have bound := header_excess_128_w small headerBound prepared size
  have litR : ready.lit_bufsize = d.lit_bufsize := by rw [prepared.frame]
  unfold OverlayBudget
  rw [litR, size]
  omega

/-- **The overlay room at `memLevel` 1**, from the header bound with `α ≤ 29`: the premises of
`TinyOverlay` with `lit_bufsize = 128`. -/
theorem dynamic_overlay_128_w {α : Nat} (small : α ≤ 29) (headerBound : HeaderRefBound128W α)
    {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (_good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (pending : d.pending = 0)
    (bits : d.bi_valid.toInt ≤ 7) (size : d.lit_bufsize.toNat = 128) (z' : ZStream) :
    DynamicOverlay (r.put h z') ds d xs := by
  intro mb ready run frame header excess dynamic
  have treesP := treesInvAt_put (r := r) (z' := z') trees
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have prepared : TinyPrepared (r.put h z') ds d xs mb ready :=
    ⟨⟨pb, buf, treesP, ledger⟩, clear, by omega, run, frame, header, excess, dynamic⟩
  exact dynamic_room_of_budget frame pending bits capacity (overlay_budget_128_w small headerBound prepared size)

#print axioms header_excess_128_w
#print axioms dynamic_overlay_128_w

end Zlib.Deflate.Engine.Proofs
