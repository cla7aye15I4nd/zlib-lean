import ZlibF.Proof.«deflate.c.engine.overlay-mem1»

/-!
# deflate.c: source-tree facts and code-length bounds of small blocks

At `lit_bufsize = B ≤ 256` every entry of both prepared source trees satisfies `LeafBound (B + 2)`:
a used symbol keeps its unclamped Fibonacci depth bound (`f · F(l + 1) + F(l) ≤ B + 2`), while any
forced leaf (`f = 0, l ≠ 0`) occurs in a two-leaf tree whose Kraft sum `2^15` forces `l = 1`
(`tree_leaf_bound`). Two consequences follow:

* every nonzero length read by `scan_tree` is at most `9` at `B = 128` (`prepared_lengths_128`) and
  at most `11` at `B = 256` (`prepared_lengths_256`), so bit-length symbols above that cap are
  absent (`scanFreq_absent`);
* every `TinyPrepared` block delivers the complete bundle of heap-free tree, frequency, choice, and
  excess facts (`prepared_tiny_facts`) consumed by `overlay-mem1w` and `overlay-mem2c`.
-/

namespace Zlib.Trees.Proofs.Out
open ZlibF.Math.DeflateSymbols (mass)

/-- `scan_tree` counts a length symbol only for a length it reads. -/
theorem scanFreq_absent (L : Nat → Nat) (n k : Nat) (low : k < 16) (above : ∀ i, i < n → L i ≠ k) :
    scanFreqUpTo L n k = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scanFreqUpTo]
    rw [ih (fun i lt => above i (by omega))]
    have cur := runStep_cur L n
    generalize hr : (runStep L n (runAt L n)).2 = o at cur
    rcases o with _ | ⟨c, p, cnt, mn⟩
    · rfl
    · have e := cur c p cnt mn rfl
      have ne : k ≠ c := by rw [e]; exact fun h => above n (by omega) h.symm
      simp [runFreq, ne, show k ≠ 16 by omega, show k ≠ 17 by omega, show k ≠ 18 by omega]

end Zlib.Trees.Proofs.Out

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare BLInput curL same_record_of_runs dynamicHeaderBits sendLengths TK btFreq
  fixedLiteralWords)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateOverlaySmall (symbol_excess_le_mass literal_end_frequency literal_symbol_count
  match_balance)
open ZlibF.Math.DeflateOverlayTiny (kraftTerm staticLen literalExcess distanceExcess LeafBound
  leaf_len_le_9 leaf_len_le_11)
open Zlib.Trees.HuffmanAbstract (fib)
set_option autoImplicit false

/-- A sum of terms each at most `c` on the used entries, over exactly two used entries, that
reaches `2c`, has every used term equal to `c`. -/
theorem mass_two_tight (f u : Nat → Nat) (n c : Nat) (each : ∀ v, v < n → f v ≤ c * u v)
    (_unit : ∀ v, u v ≤ 1) (two : mass u n = 2) (full : mass f n = 2 * c) :
    ∀ v, v < n → u v = 1 → f v = c := by
  have split : mass (fun v => c * u v) n = mass (fun v => c * u v - f v) n + mass f n := by
    rw [← mass_add]
    apply mass_congr
    intro v hv
    have := each v hv
    omega
  rw [mass_mul_left, two, full] at split
  have zero : mass (fun v => c * u v - f v) n = 0 := by omega
  intro v hv used
  have le := mass_point_le (fun v => c * u v - f v) n v hv
  rw [zero] at le
  have e := each v hv
  simp only [used, Nat.mul_one] at e le
  omega
where
  mass_point_le (g : Nat → Nat) (n v : Nat) (hv : v < n) : g v ≤ mass g n := by
    induction n with
    | zero => omega
    | succ n ih =>
      show g v ≤ mass g n + g n
      by_cases e : v = n
      · subst e; omega
      · have := ih (by omega); omega

theorem fib_le_of_used (f x W : Nat) (pos : 1 ≤ f) (fit : f * fib (x + 1) + fib x ≤ W) : fib (x + 2) ≤ W := by
  have step : fib (x + 2) = fib x + fib (x + 1) := Zlib.Trees.HuffmanAbstract.fib_add_two x
  have : fib (x + 1) ≤ f * fib (x + 1) := Nat.le_mul_of_pos_left _ pos
  omega

/-- Every entry of an unclamped Huffman tree with Kraft sum `2^15` and two-leaf forced-leaf
invariant satisfies `LeafBound M`. -/
theorem tree_leaf_bound (T : Array CtData) (n W M : Nat) (freq : Nat → UInt16)
    (fibs : ∀ v, v < n → (freq v).toNat ≠ 0 → 1 ≤ curL T v ∧ (freq v).toNat * fib (curL T v + 1) + fib (curL T v) ≤ W)
    (weight : W ≤ M)
    (len : ∀ v, v < n → curL T v ≤ 15)
    (kraft : Zlib.Trees.Proofs.GB.rs (fun v => if T[v]!.dl.toNat ≠ 0 then 2 ^ (15 - T[v]!.dl.toNat) else 0) n = 2 ^ 15)
    (two : (∃ v, v < n ∧ T[v]!.dl.toNat ≠ 0 ∧ freq v = 0) →
      mass (fun v => if T[v]!.dl.toNat ≠ 0 then 1 else 0) n = 2) :
    ∀ v, v < n → LeafBound M (curL T v) (freq v).toNat := by
  intro v hv
  by_cases hz : (freq v).toNat = 0
  · left
    refine ⟨hz, ?_⟩
    by_cases l0 : curL T v = 0
    · omega
    · have fz : freq v = 0 := UInt16.toNat_inj.mp (by rw [hz]; rfl)
      have nz' : T[v]!.dl.toNat ≠ 0 := l0
      have count := two ⟨v, hv, nz', fz⟩
      rw [rs_eq_mass] at kraft
      have tight := mass_two_tight (fun w => if T[w]!.dl.toNat ≠ 0 then 2 ^ (15 - T[w]!.dl.toNat) else 0)
        (fun w => if T[w]!.dl.toNat ≠ 0 then 1 else 0) n (2 ^ 14)
        (fun w _ => by
          by_cases z : T[w]!.dl.toNat ≠ 0
          · rw [ite_eq_left z, ite_eq_left z, Nat.mul_one]
            exact Nat.pow_le_pow_right (by omega) (by omega)
          · rw [ite_eq_right z, ite_eq_right z]; omega)
        (fun _ => by split <;> omega) count (by rw [kraft]) v hv (by rw [ite_eq_left nz'])
      rw [ite_eq_left nz'] at tight
      have lv : T[v]!.dl.toNat ≤ 15 := len v hv
      show T[v]!.dl.toNat ≤ 1
      generalize T[v]!.dl.toNat = x at nz' lv tight ⊢
      rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | x <;>
        simp at tight nz' lv ⊢
  · right
    obtain ⟨pos, fit⟩ := fibs v hv hz
    exact ⟨by omega, pos, by omega⟩

/-- **The prepared lengths are short**: every nonzero length `x` read by `scan_tree` has
`F(x + 2) ≤ lit_bufsize + 2` or is `1`. -/
theorem prepared_lengths_fib {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (small : d.lit_bufsize.toNat ≤ 256) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    (∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≠ 0 →
      fib (sendLengths ready .lit v + 2) ≤ d.lit_bufsize.toNat + 2 ∨ sendLengths ready .lit v = 1) ∧
    (∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≠ 0 →
      fib (sendLengths ready .dist v + 2) ≤ d.lit_bufsize.toNat + 2 ∨ sendLengths ready .dist v = 1) := by
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  have budgetL : mass (fun v => (btFreq .lit d v).toNat) 286 + 2 < 1597 := by
    change mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 + 2 < 1597; omega
  have budgetD : mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 1597 := by
    change mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 + 2 < 1597; omega
  obtain ⟨readyP, prepare, fibL, fibD⟩ := Zlib.Trees.Proofs.bl_prepare_fib_plus trees budgetL budgetD
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have e1 := same_record_of_runs prepare otherRun; subst e1
  obtain ⟨other, otherRun, _, _, kraftL, kraftD, usedL, usedD⟩ := Zlib.Trees.Proofs.bl_prepare_leaf_facts trees
  have e2 := same_record_of_runs prepare otherRun; subst e2
  obtain ⟨other, otherRun, twoL, twoD⟩ := Zlib.Trees.Proofs.bl_prepare_two_leaves trees
  have e3 := same_record_of_runs prepare otherRun; subst e3
  obtain ⟨other, otherRun, input, treesR, _, _⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have e4 := same_record_of_runs prepare otherRun; subst e4
  replace prepare : blPrepare (some (.tab ds)) h = .ok ((), setD h ds readyP) := prepare
  replace treesR : TreesInvAt (setD h ds readyP) ds readyP pb buf := treesR
  obtain ⟨mb', result, run', lDesc, dDesc, lTree, dTree, _, _⟩ :=
    Zlib.Trees.Proofs.build_bl_preserves_source_codes treesR input
  have complete : (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb', setD h ds result) := by
    rw [bind_app, prepare]
    simp only [Zlib.Trees.Proofs.setD, setD, upd_upd] at run' ⊢
    exact run'
  have eR := same_record_of_runs run complete; subst eR
  have l286 := input.l286
  have d30 := input.d30
  obtain ⟨WL, weightL, symbolL⟩ := fibL.symbol_fib_plus
  obtain ⟨WD, weightD, symbolD⟩ := fibD.symbol_fib_plus
  change WL ≤ mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 at weightD
  have nzU16 : ∀ u : UInt16, u.toNat ≠ 0 → u ≠ 0 := fun u nz z => nz (by rw [z]; rfl)
  have leafL := tree_leaf_bound readyP.dyn_ltree 286 WL (d.lit_bufsize.toNat + 2) (btFreq .lit d)
    (fun v hv nz => ⟨usedL v hv (nzU16 _ nz), symbolL v hv nz⟩) (by omega)
    (fun v hv => facts.literal v hv) kraftL twoL
  have leafD := tree_leaf_bound readyP.dyn_dtree 30 WD (d.lit_bufsize.toNat + 2) (btFreq .dist d)
    (fun v hv nz => ⟨usedD v hv (nzU16 _ nz), symbolD v hv nz⟩) (by omega)
    (fun v hv => facts.distance v hv) kraftD twoD
  refine ⟨?_, ?_⟩
  · intro v hv nz
    rw [lDesc] at hv
    have same : sendLengths ready .lit v = curL readyP.dyn_ltree v := by
      simp only [sendLengths, TK.arr, curL]; rw [lTree v hv]
    rw [same] at nz ⊢
    rcases leafL v (by omega) with ⟨_, le1⟩ | ⟨hf, _, hfib⟩
    · exact Or.inr (by omega)
    · exact Or.inl (fib_le_of_used _ _ _ hf hfib)
  · intro v hv nz
    rw [dDesc] at hv
    have same : sendLengths ready .dist v = curL readyP.dyn_dtree v := by
      simp only [sendLengths, TK.arr, curL]; rw [dTree v hv]
    rw [same] at nz ⊢
    rcases leafD v (by omega) with ⟨_, le1⟩ | ⟨hf, _, hfib⟩
    · exact Or.inr (by omega)
    · exact Or.inl (fib_le_of_used _ _ _ hf hfib)

/-- **At `lit_bufsize = 128` every length `scan_tree` reads is at most 9.** -/
theorem prepared_lengths_128 {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (size : d.lit_bufsize.toNat = 128) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    (∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≤ 9) ∧
    (∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≤ 9) := by
  obtain ⟨lit, dist⟩ := prepared_lengths_fib trees ledger (by omega) run
  have bound : ∀ x, x ≠ 0 → fib (x + 2) ≤ 130 ∨ x = 1 → x ≤ 9 := by
    intro x _ h
    rcases h with h | rfl
    · have step : fib (x + 2) = fib x + fib (x + 1) := Zlib.Trees.HuffmanAbstract.fib_add_two x
      exact leaf_len_le_9 (f := 1) (Or.inr ⟨Nat.le_refl 1, by omega, by omega⟩)
    · omega
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_cases z : sendLengths ready .lit v = 0
    · omega
    · exact bound _ z (by rw [size] at lit; exact lit v hv z)
  · by_cases z : sendLengths ready .dist v = 0
    · omega
    · exact bound _ z (by rw [size] at dist; exact dist v hv z)

/-- **At `lit_bufsize = 256` every length `scan_tree` reads is at most 11.** -/
theorem prepared_lengths_256 {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (size : d.lit_bufsize.toNat = 256) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    (∀ v, v ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit v ≤ 11) ∧
    (∀ v, v ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist v ≤ 11) := by
  obtain ⟨lit, dist⟩ := prepared_lengths_fib trees ledger (by omega) run
  have bound : ∀ x, x ≠ 0 → fib (x + 2) ≤ 258 ∨ x = 1 → x ≤ 11 := by
    intro x _ h
    rcases h with h | rfl
    · have step : fib (x + 2) = fib x + fib (x + 1) := Zlib.Trees.HuffmanAbstract.fib_add_two x
      exact leaf_len_le_11 (f := 1) (Or.inr ⟨Nat.le_refl 1, by omega, by omega⟩)
    · omega
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_cases z : sendLengths ready .lit v = 0
    · omega
    · exact bound _ z (by rw [size] at lit; exact lit v hv z)
  · by_cases z : sendLengths ready .dist v = 0
    · omega
    · exact bound _ z (by rw [size] at dist; exact dist v hv z)

/-- Heap-free source-tree, frequency, choice, and excess facts extracted from a `TinyPrepared` run. -/
structure PreparedTinyFacts (d ready : DeflateState) (mb : Int32) (xs : List Symbol) : Prop where
  data : ∃ (ll fl dl fd : Nat → Nat),
    (∀ v, v < 286 → ll v ≤ 15) ∧
    (∀ v, v < 30 → dl v ≤ 15) ∧
    mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15 ∧
    mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15 ∧
    (∀ v, v < 286 → v ≠ 256 → LeafBound (d.lit_bufsize.toNat + 2) (ll v) (fl v)) ∧
    (fl 256 = 1 ∧ 1 ≤ ll 256 ∧ fib (ll 256 + 1) + fib (ll 256) ≤ d.lit_bufsize.toNat + 2) ∧
    (∀ v, v < 30 → LeafBound (d.lit_bufsize.toNat + 2) (dl v) (fd v)) ∧
    mass (fun v => if v = 256 then 0 else fl v) 286 ≤ d.lit_bufsize.toNat - 1 ∧
    mass (fun v => if v < 257 then 0 else fl v) 286 = mass fd 30 ∧
    (dynamicHeaderBits ready mb).length + mass (fun v => fl v * ll v) 286 +
      mass (fun v => fd v * dl v) 30 + 1 ≤
      mass (fun v => fl v * staticLen v) 286 + 5 * mass fd 30 ∧
    Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤
      mass (fun v => fl v * literalExcess v (ll v)) 286 +
      mass (fun v => fd v * distanceExcess v (dl v)) 30 ∧
    256 ≤ ready.l_desc.max_code.toInt.toNat ∧
    ready.l_desc.max_code.toInt.toNat < 286 ∧
    ready.d_desc.max_code.toInt.toNat < 30 ∧
    (∀ i, i ≤ ready.l_desc.max_code.toInt.toNat → sendLengths ready .lit i = ll i) ∧
    (∀ i, i ≤ ready.d_desc.max_code.toInt.toNat → sendLengths ready .dist i = dl i)

/-- Extract `PreparedTinyFacts` from any `TinyPrepared` block with `lit_bufsize ≤ 256`. -/
theorem prepared_tiny_facts {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol}
    {mb : Int32} {ready : DeflateState} (prepared : TinyPrepared h ds d xs mb ready)
    (small : d.lit_bufsize.toNat ≤ 256) :
    PreparedTinyFacts d ready mb xs := by
  obtain ⟨pb, buf, trees, ledger⟩ := prepared.base
  have run := prepared.run
  have choice := choice_row trees ledger prepared.clear run prepared.header prepared.excess prepared.dynamic
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have literalMass := ledger_literal_mass ledger
  have distanceMass := ledger_distance_mass ledger
  have budgetL : mass (fun v => (btFreq .lit d v).toNat) 286 + 2 < 1597 := by
    change mass (fun k => (d.dyn_ltree[k]!).fc.toNat) 286 + 2 < 1597; omega
  have budgetD : mass (fun v => (btFreq .dist d v).toNat) 30 + 2 < 1597 := by
    change mass (fun k => (d.dyn_dtree[k]!).fc.toNat) 30 + 2 < 1597; omega
  obtain ⟨readyP, prepare, fibL, fibD⟩ := Zlib.Trees.Proofs.bl_prepare_fib_plus trees budgetL budgetD
  obtain ⟨other, otherRun, facts⟩ := Zlib.Trees.Proofs.bl_prepare_length_facts trees
  have e1 := same_record_of_runs prepare otherRun; subst e1
  obtain ⟨other, otherRun, _, _, kraftL, kraftD, usedL, usedD⟩ := Zlib.Trees.Proofs.bl_prepare_leaf_facts trees
  have e2 := same_record_of_runs prepare otherRun; subst e2
  obtain ⟨other, otherRun, twoL, twoD⟩ := Zlib.Trees.Proofs.bl_prepare_two_leaves trees
  have e3 := same_record_of_runs prepare otherRun; subst e3
  obtain ⟨other, otherRun, input, treesR, _, _⟩ := Zlib.Trees.Proofs.bl_prepare trees
  have e4 := same_record_of_runs prepare otherRun; subst e4
  replace prepare : blPrepare (some (.tab ds)) h = .ok ((), setD h ds readyP) := prepare
  replace treesR : TreesInvAt (setD h ds readyP) ds readyP pb buf := treesR
  obtain ⟨mb', result, run', lDesc, dDesc, lTree, dTree, _, _⟩ :=
    Zlib.Trees.Proofs.build_bl_preserves_source_codes treesR input
  have complete : (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb', setD h ds result) := by
    rw [bind_app, prepare]
    simp only [Zlib.Trees.Proofs.setD, setD, upd_upd] at run' ⊢
    exact run'
  have eR := same_record_of_runs run complete; subst eR
  obtain ⟨WL, weightL, symbolL⟩ := fibL.symbol_fib_plus
  obtain ⟨WD, weightD, symbolD⟩ := fibD.symbol_fib_plus
  change WL ≤ mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 at weightL
  change WD ≤ mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 at weightD
  let ll : Nat → Nat := fun v => curL readyP.dyn_ltree v
  let dl : Nat → Nat := fun v => curL readyP.dyn_dtree v
  let fl : Nat → Nat := literalFrequency symbolLengthCode xs
  let fd : Nat → Nat := distanceFrequency dcodeN xs
  have freqL : ∀ v, v < 286 → (btFreq .lit d v).toNat = fl v := fun v hv => ledger.literal v hv
  have freqD : ∀ v, v < 30 → (btFreq .dist d v).toNat = fd v := fun v hv => ledger.distance v hv
  have nzU16 : ∀ u : UInt16, u.toNat ≠ 0 → u ≠ 0 := fun u nz z => nz (by rw [z]; rfl)
  have rawLeafL := tree_leaf_bound readyP.dyn_ltree 286 WL (d.lit_bufsize.toNat + 2) (btFreq .lit d)
    (fun v hv nz => ⟨usedL v hv (nzU16 _ nz), symbolL v hv nz⟩) (by omega)
    (fun v hv => facts.literal v hv) kraftL twoL
  have rawLeafD := tree_leaf_bound readyP.dyn_dtree 30 WD (d.lit_bufsize.toNat + 2) (btFreq .dist d)
    (fun v hv nz => ⟨usedD v hv (nzU16 _ nz), symbolD v hv nz⟩) (by omega)
    (fun v hv => facts.distance v hv) kraftD twoD
  have leafL : ∀ v, v < 286 → v ≠ 256 → LeafBound (d.lit_bufsize.toNat + 2) (ll v) (fl v) := by
    intro v hv _
    have h := rawLeafL v hv
    rw [freqL v hv] at h
    exact h
  have leafD : ∀ v, v < 30 → LeafBound (d.lit_bufsize.toNat + 2) (dl v) (fd v) := by
    intro v hv
    have h := rawLeafD v hv
    rw [freqD v hv] at h
    exact h
  have eobF := literal_end_frequency symbolLengthCode xs ledger.valid
  have eobUsed : btFreq .lit d 256 ≠ 0 := by
    apply nzU16
    rw [freqL 256 (by omega)]
    show literalFrequency symbolLengthCode xs 256 ≠ 0
    omega
  have eob : fl 256 = 1 ∧ 1 ≤ ll 256 ∧ fib (ll 256 + 1) + fib (ll 256) ≤ d.lit_bufsize.toNat + 2 := by
    have h256 := rawLeafL 256 (by omega)
    rw [freqL 256 (by omega), show fl 256 = 1 from eobF] at h256
    rcases h256 with ⟨h0, _⟩ | ⟨_, h1, hfib⟩
    · omega
    · rw [Nat.one_mul] at hfib
      exact ⟨eobF, h1, hfib⟩
  have kL : mass (fun v => kraftTerm (ll v)) 286 ≤ 2 ^ 15 := by
    rw [rs_eq_mass] at kraftL
    apply Nat.le_of_eq; rw [← kraftL]; apply mass_congr; intro v _
    simp only [kraftTerm, ll, curL]
    by_cases z : (readyP.dyn_ltree[v]!).dl.toNat = 0 <;> simp [z]
  have kD : mass (fun v => kraftTerm (dl v)) 30 ≤ 2 ^ 15 := by
    rw [rs_eq_mass] at kraftD
    apply Nat.le_of_eq; rw [← kraftD]; apply mass_congr; intro v _
    simp only [kraftTerm, dl, curL]
    by_cases z : (readyP.dyn_dtree[v]!).dl.toNat = 0 <;> simp [z]
  have chL : mass (fun v => literalFrequency symbolLengthCode xs v * curL ready.dyn_ltree v) 286 =
      mass (fun v => fl v * ll v) 286 := by
    apply mass_congr; intro v hv
    by_cases z : fl v = 0
    · show fl v * _ = fl v * _; rw [z, Nat.zero_mul, Nat.zero_mul]
    · show fl v * curL ready.dyn_ltree v = fl v * curL readyP.dyn_ltree v
      unfold curL
      rw [lTree v (facts.literal_used v hv (nzU16 _ (by show (btFreq .lit d v).toNat ≠ 0; rw [freqL v hv]; exact z)))]
  have chD : mass (fun v => distanceFrequency dcodeN xs v * curL ready.dyn_dtree v) 30 =
      mass (fun v => fd v * dl v) 30 := by
    apply mass_congr; intro v hv
    by_cases z : fd v = 0
    · show fd v * _ = fd v * _; rw [z, Nat.zero_mul, Nat.zero_mul]
    · show fd v * curL ready.dyn_dtree v = fd v * curL readyP.dyn_dtree v
      unfold curL
      rw [dTree v (facts.distance_used v hv (nzU16 _ (by show (btFreq .dist d v).toNat ≠ 0; rw [freqD v hv]; exact z)))]
  have chS : mass (fun v => literalFrequency symbolLengthCode xs v * (fixedLiteralWords v).2.toNat) 286 =
      mass (fun v => fl v * staticLen v) 286 :=
    mass_congr fun v hv => by rw [fixed_static_len ⟨v, hv⟩]
  rw [chL, chD, chS] at choice
  have costsSame := dynamicSymbolCosts_live_congr ledger facts lTree dTree
  have excess := symbol_excess_le_mass xs (curL readyP.dyn_ltree) (curL readyP.dyn_dtree)
    sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
    (fun v hv _ => facts.literal v hv)
  have tables := extra_tables
  have exL : mass (fun v => literalFrequency symbolLengthCode xs v *
      ZlibF.Math.DeflatePush.literalExcess (curL readyP.dyn_ltree) sourceLiteralExtra v) 286 =
      mass (fun v => fl v * literalExcess v (ll v)) 286 := by
    apply mass_congr; intro v hv
    simp only [ZlibF.Math.DeflatePush.literalExcess, literalExcess, fl, ll]
    by_cases low : v < 257
    · simp [low]
    · simp only [low, ite_false]; rw [tables.1 ⟨v - 257, by omega⟩]
  have exD : mass (fun v => distanceFrequency dcodeN xs v *
      ZlibF.Math.DeflatePush.distanceExcess (curL readyP.dyn_dtree) sourceDistanceExtra v) 30 =
      mass (fun v => fd v * distanceExcess v (dl v)) 30 := by
    apply mass_congr; intro v hv
    simp only [ZlibF.Math.DeflatePush.distanceExcess, distanceExcess, fd, dl]
    rw [tables.2 ⟨v, hv⟩]
  have costs : dynamicSymbolCosts readyP xs = xs.map (symbolCost (curL readyP.dyn_ltree) (curL readyP.dyn_dtree)
      sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN) := rfl
  rw [exL, exD, ← costs, ← costsSame] at excess
  have symbols : mass (fun v => if v = 256 then 0 else fl v) 286 ≤ d.lit_bufsize.toNat - 1 := by
    rw [literal_symbol_count symbolLengthCode xs ledger.valid
      (fun s member => valid_literal_key (ledger.valid s member))]
    omega
  have balance := match_balance symbolLengthCode dcodeN xs ledger.valid
    (fun s member => valid_literal_key (ledger.valid s member))
    (fun s member k selected => valid_distance_key (ledger.valid s member) selected)
  have maxL256 := facts.literal_used 256 (by omega) eobUsed
  have l286 := input.l286
  have d30 := input.d30
  exact ⟨⟨ll, fl, dl, fd,
    fun v hv => facts.literal v hv,
    fun v hv => facts.distance v hv,
    kL, kD, leafL, eob, leafD, symbols, balance, choice, excess,
    by rw [lDesc]; exact maxL256,
    by rw [lDesc]; omega,
    by rw [dDesc]; omega,
    fun i hi => by rw [lDesc] at hi; simp only [sendLengths, TK.arr, ll, curL]; rw [lTree i hi],
    fun i hi => by rw [dDesc] at hi; simp only [sendLengths, TK.arr, dl, curL]; rw [dTree i hi]⟩⟩

#print axioms prepared_lengths_128
#print axioms prepared_lengths_256
#print axioms prepared_tiny_facts

end Zlib.Deflate.Engine.Proofs
