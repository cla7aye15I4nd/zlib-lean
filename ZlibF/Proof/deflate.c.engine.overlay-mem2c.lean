import ZlibF.Proof.«deflate.c.engine.overlay-lengths»

/-!
# deflate.c: the overlay room at `memLevel` 2 with the region scan and the choice row

At `lit_bufsize = 256`, every prepared dynamic block satisfies `H + bitExcess ≤ 2023`
(`header_excess_256c`), from the header hypothesis `HeaderRefBound Δ` with `Δ ≤ 419` (instantiated
at `Δ = 245` by `header_ref_bound_256`): `scan_cost_region` bounds `2 * refHeaderCost` by the
region charges under `κ0`, and `prepared_tiny_facts` supplies the Kraft, Fibonacci, symbol-count,
match-balance, and choice-row bounds to `DeflateOverlayTiny.header_excess_cert_256`. The order-free
budget (`overlay_budget_256c`) and overlay room (`dynamic_overlay_256c`) follow.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicHeaderBits sendLengths TK)
open Zlib.Trees.Proofs.Out (TreesInvAt scanFreqUpTo refWeight blExtraBits_zero mass_mul_add
  ScanCharges regionCharge scan_cost_region)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateOverlayTiny (refLen literalRegionCharge256 otherRegionCharge256
  literalCharge256 header_excess_cert_256)
open Zlib.Deflate.Universal.Block (DynamicOverlay treesInvAt_put)
set_option autoImplicit false

/-- Region credits and zero-entry charges of the literal/length scan at `B = 256`: credit `6` and
`2` per zero in the literal region (`0..256`), `0` and `4` per zero in the length region. -/
def literalA_256c (i : Nat) : Nat := if i ≤ 256 then 6 else 0
def literalB_256c (i : Nat) : Nat := if i ≤ 256 then 2 else 4

theorem charges_256c :
    ScanCharges (fun k => 2 * refWeight k) otherRegionCharge256 literalA_256c literalB_256c ∧
    ScanCharges (fun k => 2 * refWeight k) otherRegionCharge256 (fun _ => 0) (fun _ => 4) := by
  have short : ∀ x, 1 ≤ x → x ≤ 15 → 2 * refWeight x ≤ otherRegionCharge256 x := by
    intro x h1 h2
    simp [refWeight, blExtraBits_zero h2, otherRegionCharge256, show x ≠ 0 by omega]
  have rep : ∀ x, 1 ≤ x → x ≤ 15 → 2 * refWeight 16 ≤ 3 * otherRegionCharge256 x := by
    intro x h1 h2
    rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
      simp [refWeight, refLen, otherRegionCharge256, Zlib.Trees.Proofs.Out.blExtraBits] at h1 h2 ⊢
  have w0 : 2 * refWeight 0 = 4 := rfl
  have w17 : 2 * refWeight 17 = 12 := rfl
  have w18 : 2 * refWeight 18 = 28 := rfl
  refine ⟨⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩, ⟨short, rep, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;>
    simp only [literalA_256c, literalB_256c, w0, w17, w18] <;> (try split) <;> omega

theorem literal_regionCharge_256c (L : Nat → Nat) (i : Nat) :
    regionCharge L otherRegionCharge256 literalA_256c literalB_256c i = literalCharge256 i (L i) := by
  unfold regionCharge literalCharge256 literalRegionCharge256 otherRegionCharge256 literalA_256c literalB_256c
  by_cases r : i ≤ 256 <;> by_cases z : L i = 0 <;> simp [r, z]

theorem distance_regionCharge_256c (L : Nat → Nat) (i : Nat) :
    regionCharge L otherRegionCharge256 (fun _ => 0) (fun _ => 4) i = otherRegionCharge256 (L i) := by
  unfold regionCharge otherRegionCharge256
  by_cases z : L i = 0 <;> simp [z]

/-- **Header plus excess at `lit_bufsize = 256`**: at most `1899` bits for `Δ ≤ 245`. -/
theorem header_excess_256c {Δ : Nat} (small : Δ ≤ 245) (headerBound : HeaderRefBound Δ)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 256) :
    (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 1899 := by
  have hdrBound := headerBound prepared size
  obtain ⟨⟨ll, fl, dl, fd, lenL, lenD, kL, kD, leafL, eob, leafD, symbols, balance, choice, excess,
    maxL256, maxL_lt, maxD_lt, lowL, lowD⟩⟩ := prepared_tiny_facts prepared (by omega)
  rw [size] at leafL eob leafD symbols
  have bound16 : ∀ (tk : TK) (n : Nat), sendLengths ready tk n < 2 ^ 16 := fun _ _ => UInt16.toNat_lt _
  have keepL : ∀ i, sendLengths ready .lit i = 0 →
      literalA_256c (i + 1) = literalA_256c i ∧ literalB_256c (i + 1) = literalB_256c i := by
    intro i z
    by_cases e : i = 256
    · subst e; rw [lowL 256 maxL256] at z; have := eob.2.1; omega
    · simp only [literalA_256c, literalB_256c]
      by_cases r : i ≤ 255
      · simp [show i + 1 ≤ 256 by omega, show i ≤ 256 by omega]
      · simp [show ¬ (i + 1 ≤ 256) by omega, show ¬ (i ≤ 256) by omega]
  have scanL := scan_cost_region (sendLengths ready .lit) _ _ _ _ charges_256c.1 (bound16 .lit) keepL
    (ready.l_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowL i (by omega)]; exact lenL i (by omega))
  have scanD := scan_cost_region (sendLengths ready .dist) _ _ _ _ charges_256c.2 (bound16 .dist)
    (fun _ _ => ⟨rfl, rfl⟩) (ready.d_desc.max_code.toInt.toNat + 1)
    (fun i hi => by rw [lowD i (by omega)]; exact lenD i (by omega))
  have endA : literalA_256c (ready.l_desc.max_code.toInt.toNat + 1) = 0 := by
    unfold literalA_256c; rw [ite_eq_right (by omega)]
  rw [endA] at scanL
  have chargesL : mass (regionCharge (sendLengths ready .lit) otherRegionCharge256 literalA_256c literalB_256c)
      (ready.l_desc.max_code.toInt.toNat + 1) ≤ mass (fun v => literalCharge256 v (ll v)) 286 := by
    rw [mass_congr (g := fun v => literalCharge256 v (ll v)) (fun i hi => by
      rw [literal_regionCharge_256c, lowL i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have chargesD : mass (regionCharge (sendLengths ready .dist) otherRegionCharge256 (fun _ => 0) (fun _ => 4))
      (ready.d_desc.max_code.toInt.toNat + 1) ≤ mass (fun v => otherRegionCharge256 (dl v)) 30 := by
    rw [mass_congr (g := fun v => otherRegionCharge256 (dl v)) (fun i hi => by
      rw [distance_regionCharge_256c, lowD i (by omega)])]
    exact mass_le_of_le _ (by omega)
  have twice : 2 * refHeaderCost ready ≤ mass (fun v => literalCharge256 v (ll v)) 286 +
      mass (fun v => otherRegionCharge256 (dl v)) 30 := by
    unfold refHeaderCost
    rw [mass_mul_add, Nat.mul_add, ← mass_mul_left, ← mass_mul_left]
    have eL : mass (fun k => 2 * (scanFreqUpTo (sendLengths ready .lit) (ready.l_desc.max_code.toInt.toNat + 1) k *
        refWeight k)) 19 = mass (fun k => scanFreqUpTo (sendLengths ready .lit)
        (ready.l_desc.max_code.toInt.toNat + 1) k * (2 * refWeight k)) 19 := by
      apply mass_congr; intro k _; rw [Nat.mul_left_comm]
    have eD : mass (fun k => 2 * (scanFreqUpTo (sendLengths ready .dist) (ready.d_desc.max_code.toInt.toNat + 1) k *
        refWeight k)) 19 = mass (fun k => scanFreqUpTo (sendLengths ready .dist)
        (ready.d_desc.max_code.toInt.toNat + 1) k * (2 * refWeight k)) 19 := by
      apply mass_congr; intro k _; rw [Nat.mul_left_comm]
    rw [eL, eD]; omega
  have cert := header_excess_cert_256 ll fl dl fd (dynamicHeaderBits ready mb).length Δ small
    kL kD leafL eob leafD symbols balance (by omega) choice
  omega

/-- **The order-free budget at `memLevel` 2**, from the header bound with `Δ ≤ 245`. -/
theorem overlay_budget_256c {Δ : Nat} (small : Δ ≤ 245) (headerBound : HeaderRefBound Δ)
    {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol} {mb : Int32} {ready : DeflateState}
    (prepared : TinyPrepared h ds d xs mb ready) (size : d.lit_bufsize.toNat = 256) :
    OverlayBudget ready mb xs := by
  have bound := header_excess_256c small headerBound prepared size
  have litR : ready.lit_bufsize = d.lit_bufsize := by rw [prepared.frame]
  unfold OverlayBudget
  rw [litR, size]
  omega

/-- **The overlay room at `memLevel` 2**, from the header bound with `Δ ≤ 245`: the premises of
`TinyOverlay` with `lit_bufsize = 256`. -/
theorem dynamic_overlay_256c {Δ : Nat} (small : Δ ≤ 245) (headerBound : HeaderRefBound Δ)
    {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (_good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (pending : d.pending = 0)
    (bits : d.bi_valid.toInt ≤ 7) (size : d.lit_bufsize.toNat = 256) (z' : ZStream) :
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
  exact dynamic_room_of_budget frame pending bits capacity (overlay_budget_256c small headerBound prepared size)

#print axioms header_excess_256c
#print axioms dynamic_overlay_256c

end Zlib.Deflate.Engine.Proofs
