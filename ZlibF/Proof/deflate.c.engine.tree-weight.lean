import ZlibF.Proof.«deflate.c.engine.symbol-mass»
import ZlibF.Proof.«trees.c.build.depth-bound»

/-! # Real symbol capacity establishes the actual Huffman merge budget -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs (TK btFreq Hn BTBuilt)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols (Symbol mass)
set_option autoImplicit false

/-- Literal and distance leaf totals follow from the same actual symbol
ledger used by payload emission. Legal memory levels, including the default,
leave room for the at-most-two dummy writes in the 16-bit frequency type. -/
theorem source_tree_mass_budget {h : Heap} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (count : d.sym_next.toNat ≤ d.sym_end.toNat) (tk : TK) (source : tk = .lit ∨ tk = .dist) :
    mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat ≤ d.lit_bufsize.toNat ∧
    mass (fun v => (btFreq tk d v).toNat) tk.buildDesc.elems.toInt.toNat + 2 < 2 ^ 16 := by
  have capacity := ledger_tree_capacity trees.base ledger count
  have high := trees.base.lit_hi
  rcases source with equal | equal
  · subst tk
    change mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 ≤ _ ∧ _
    exact ⟨capacity.1, by change mass (fun v => (d.dyn_ltree[v]!).fc.toNat) 286 + 2 < 65536; omega⟩
  · subst tk
    change mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 ≤ _ ∧ _
    exact ⟨Nat.le_of_lt capacity.2,
      by change mass (fun v => (d.dyn_dtree[v]!).fc.toNat) 30 + 2 < 65536; omega⟩

end Zlib.Deflate.Engine.Proofs
