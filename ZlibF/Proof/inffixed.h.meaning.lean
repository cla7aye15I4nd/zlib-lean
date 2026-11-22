import ZlibF.Proof.«inftrees.c.decode.install»
import ZlibF.Proof.«inffast.c.tableok»

set_option autoImplicit false

namespace Zlib.InffixedH.Proofs
open C ZlibF.Spec
open Zlib.Inffast.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeSoundness

/-- A property of every entry of an array, from one pass over its list (`List.all`). The kernel checks the pass
much faster than one lookup per index, and in far less memory. -/
theorem getD_of_toList_all {α : Type} [Inhabited α] {a : Array α} {P : α → Prop} [DecidablePred P]
    (h : a.toList.all (fun x => decide (P x)) = true) {i : Nat} (hi : i < a.size) : P (a.getD i default) := by
  rw [List.all_eq_true] at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  exact of_decide_eq_true (h _ (Array.getElem_mem_toList hi))

/-- The same for `a[i]!`. -/
theorem getElem!_of_toList_all {α : Type} [Inhabited α] {a : Array α} {P : α → Prop} [DecidablePred P]
    (h : a.toList.all (fun x => decide (P x)) = true) {i : Nat} (hi : i < a.size) : P a[i]! := by
  rw [List.all_eq_true] at h
  rw [getElem!_pos a i hi]
  exact of_decide_eq_true (h _ (Array.getElem_mem_toList hi))

/-- A finite cell check against the independent fixed distance alphabet.
The lookup index is the low five bits in the order read by the decoder. -/
def fixedDistCellCorrect (i : Fin 32) : Prop :=
  match decodeSym fixedDistLens (bitsOfNat i.val 5), Zlib.InffixedH.distfix[i.val]? with
  | some (symbol, rest), some entry =>
      rest = (bitsOfNat i.val 5).drop entry.bits.toNat ∧
      entry.bits.toNat = fixedDistLens.getD symbol 0 ∧
      SymbolEntry DISTS symbol entry ∧
      (LeafAccepted DISTS entry ↔ ValidSymbol DISTS symbol)
  | _, _ => False

instance (i : Fin 32) : Decidable (fixedDistCellCorrect i) := by
  unfold fixedDistCellCorrect
  split
  · unfold SymbolEntry LeafAccepted ValidSymbol
    infer_instance
  · infer_instance

set_option maxRecDepth 100000 in
theorem fixedDistCellCorrect_all : ∀ i : Fin 32, fixedDistCellCorrect i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem distfix_no_links : ∀ i : Fin 32,
    ((Zlib.InffixedH.distfix[i.val]!).op &&& 0xf0) != 0 := by
  decide +kernel

/-- A finite cell check against the independent fixed literal/length alphabet.
This includes the four static cells that differ from `inflate_table` output. -/
def fixedLitCellCorrect (i : Fin 512) : Prop :=
  match decodeSym fixedLitLens (bitsOfNat i.val 9), Zlib.InffixedH.lenfix[i.val]? with
  | some (symbol, rest), some entry =>
      rest = (bitsOfNat i.val 9).drop entry.bits.toNat ∧
      entry.bits.toNat = fixedLitLens.getD symbol 0 ∧
      SymbolEntry LENS symbol entry ∧
      (LeafAccepted LENS entry ↔ ValidSymbol LENS symbol)
  | _, _ => False

instance (i : Fin 512) : Decidable (fixedLitCellCorrect i) := by
  unfold fixedLitCellCorrect
  split
  · unfold SymbolEntry LeafAccepted ValidSymbol
    infer_instance
  · infer_instance

/-! The 512 cells are checked in four blocks of 128: one check of all of them took 6 GB. -/

set_option maxRecDepth 100000 in
theorem fixedLitCellCorrect_chunk0 : ∀ i : Fin 128, fixedLitCellCorrect ⟨0 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fixedLitCellCorrect_chunk1 : ∀ i : Fin 128, fixedLitCellCorrect ⟨128 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fixedLitCellCorrect_chunk2 : ∀ i : Fin 128, fixedLitCellCorrect ⟨256 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fixedLitCellCorrect_chunk3 : ∀ i : Fin 128, fixedLitCellCorrect ⟨384 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fixedLitCellCorrect_all : ∀ i : Fin 512, fixedLitCellCorrect i := by
  intro ⟨v, hv⟩
  rcases (show v < 128 ∨ (128 ≤ v ∧ v < 256) ∨ (256 ≤ v ∧ v < 384) ∨ 384 ≤ v by omega) with h | h | h | h
  · have c := fixedLitCellCorrect_chunk0 ⟨v, h⟩
    simp only [Nat.zero_add] at c
    exact c
  · have c := fixedLitCellCorrect_chunk1 ⟨v - 128, by omega⟩
    simp only [show 128 + (v - 128) = v by omega] at c
    exact c
  · have c := fixedLitCellCorrect_chunk2 ⟨v - 256, by omega⟩
    simp only [show 256 + (v - 256) = v by omega] at c
    exact c
  · have c := fixedLitCellCorrect_chunk3 ⟨v - 384, by omega⟩
    simp only [show 384 + (v - 384) = v by omega] at c
    exact c

set_option maxRecDepth 100000 in
theorem lenfix_no_links : ∀ i : Fin 512,
    ¬ ((Zlib.InffixedH.lenfix[i.val]!).op != 0 &&
      ((Zlib.InffixedH.lenfix[i.val]!).op &&& 0xf0) == 0) := fun i =>
  getElem!_of_toList_all (P := fun c : Code => ¬ (c.op != 0 && (c.op &&& 0xf0) == 0)) (by decide +kernel)
    (by rw [show Zlib.InffixedH.lenfix.size = 512 by decide]; exact i.isLt)

end Zlib.InffixedH.Proofs
