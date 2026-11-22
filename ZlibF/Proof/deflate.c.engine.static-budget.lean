import ZlibF.Proof.«deflate.c.engine.static-budget-data»
import ZlibF.Proof.«deflate.c.engine.block-initial»
import ZlibF.Proof.«deflate.c.engine.block-prepare»
import ZlibF.Proof.«trees.c.static-counter»
import ZlibF.Math.DeflateBlockSelection

/-! # The actual branch-selection counter is bounded by the original symbols -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def originalStaticCost (d : DeflateState) : Nat :=
  mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
    mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30

set_option maxRecDepth 10000 in
/-- Real source-tree calls produce the original weighted fixed cost, then
both scans and the entire BL call preserve it. Frequencies are measured
before their unions are reused for canonical words. -/
theorem all_trees_static_budget_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ TreePreparationFrame d result ∧
      result.static_len = UInt64.ofNat (originalStaticCost d) ∧
      result.static_len.toNat ≤ 31 * xs.length + 7 := by
  obtain ⟨literal, ready, prepare, goodR, treesR, buffersR, _sizesR, _storageR,
    input, _frameL, _frameD, _outputR⟩ := source_trees_engine (ob := ob) good trees buffers
  obtain ⟨otherReady, otherPrepare, cost⟩ := Zlib.Trees.Proofs.bl_prepare_static_cost trees
  have sameReady : otherReady = ready := Zlib.Trees.Proofs.same_record_of_runs otherPrepare prepare
  subst otherReady
  change ready.static_len = d.static_len + UInt64.ofNat (originalStaticCost d) at cost
  rw [clear.fixed, UInt64.zero_add] at cost
  obtain ⟨mb, result, finish, static⟩ := Zlib.Trees.Proofs.build_bl_tree_static_cost treesR input
  change Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds ready) =
    .ok (mb, setD (setD h ds ready) ds result) at finish
  rw [setD_setD] at finish
  have complete : (do
      Zlib.Trees.Proofs.blPrepare (some (.tab ds))
      Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds result) := by
    rw [bind_app, prepare]
    exact finish
  obtain ⟨otherMb, lit, prepared, scanned, built, other, B, run, goodA, treesA, buffersA,
    sizes, storage, _input, frameL, frameD, scans, frame, finishFields, _lower, _upper,
    _guards, _codes, _output⟩ := all_trees_engine (ob := ob) good trees buffers
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs complete run
  have fullFrame := all_tree_frames frameL frameD scans frame finishFields
  rw [← same] at goodA treesA buffersA sizes storage fullFrame
  have exactCost : result.static_len = UInt64.ofNat (originalStaticCost d) := static.trans cost
  have budget : originalStaticCost d ≤ 31 * xs.length + 7 := ledger_static_cost_budget ledger
  have bound : result.static_len.toNat ≤ 31 * xs.length + 7 := by
    rw [exactCost, UInt64.toNat_ofNat']
    exact Nat.le_trans (Nat.mod_le _ _) budget
  exact ⟨mb, result, complete, goodA, treesA, buffersA, sizes, storage,
    fullFrame, exactCost, bound⟩

end Zlib.Deflate.Engine.Proofs
