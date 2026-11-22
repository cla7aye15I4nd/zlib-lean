import ZlibF.Proof.«trees.c.build.weight-start»
import ZlibF.Proof.«trees.c.build.static»
import ZlibF.Proof.«trees.c.build.values»
import ZlibF.Proof.«trees.c.build.removal-order»
import ZlibF.Proof.«trees.c.build.leaf-values»

/-! # The complete actual heap prefix retains its parent-value equations -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
open ZlibF.Math.DeflateSymbols (mass)
set_option autoImplicit false

/-- Complete source heap construction retains the natural weight sums,
exact depth updates and the chronological order of all removals. -/
theorem ws_btHeap_trace {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : 2 * sd.elems.toInt.toNat - 1 ≤ (tk.arr d).size)
    (hD : 2 * sd.elems.toInt.toNat - 1 ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl)
    (budget : mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 < 2 ^ 16) :
    WS h0 id (btHeap (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧
      (btFreq tk e (Hn e e.heap_max.toInt.toNat)).toNat ≤
        mass (fun v => (btFreq tk d v).toNat) sd.elems.toInt.toNat + 2 ∧
      ∃ prepared K, BTBuilt tk sd.elems.toInt.toNat K a.2 prepared e ∧ BTMergeValues tk sd.elems.toInt.toNat (K - 1) e ∧ BTMergeOrder tk K (K - 1) e ∧ BTLeafValues tk sd.elems.toInt.toNat (574 - 2 * K) e) := by
  have hT0 : sd.elems.toInt ≤ (tk.arr d).size := by omega
  have hD0 : sd.elems.toInt ≤ d.depth.size := by omega
  unfold btHeap btMergedStart
  simp only [M_bind_assoc, M_pure_bind]
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSortedStart hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)
    (ws_btSortedStart_sizes hdd hsd hstat htree he3 he286 hT0 hD0 hH hs))
    (ws_btSortedStart_weight hdd hsd hstat htree he3 he286 hT0 hD0 hH hs)) ?_
  intro a prepared ⟨⟨⟨ht, hst, he, leaf, h2, hm, _desc, ho, _minimum⟩, hTs, hDs⟩, weight⟩
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he leaf ⊢
  subst tree; subst stree; subst elems
  have count := leaf.count
  have maxCount := Math.scanCount_le (btFreq tk prepared) sd.elems.toInt.toNat
  have initial := BTForest.of_leaf leaf h2 hm (node := sd.elems) (by omega)
    (by rw [hTs]; omega) (by rw [hDs]; omega) ho
  have total : btQueueWeight tk prepared prepared.heap_len.toInt.toNat < 2 ^ 16 := by omega
  refine WS.bind' (merge_ws_and (ws_btMergeLoop_values initial total)
    (ws_btMergeLoop_order initial total)) ?_
  intro next before ⟨⟨forest, frame, len, rootWeight, values⟩, _forest, _frame, _len, _weight, order⟩
  have max := forest.queue.max
  have size := forest.queue.heap
  have k2 := forest.queue.k2
  have kN := forest.queue.kN
  have n286 := forest.queue.n286
  refine WS.bind' (merge_ws_and (merge_ws_and
    (ws_btSaveRoot_forest forest frame) (ws_btSaveRoot_values forest values))
    (merge_ws_and (merge_ws_and (ws_btSaveRoot_order forest order) (ws_btSaveRoot_leaf_values forest))
      (ws_btSaveRoot before (by omega) (by omega) (by omega) (by omega)))) ?_
  intro _ e ⟨⟨built, valuesA⟩, ⟨orderA, leaves⟩, rootIndex, _index, fields, _size, rootStore, _heapFrame⟩
  have array : tk.arr e = tk.arr before := by rw [fields]; cases tk <;> rfl
  have index : e.heap_max = rootIndex := by rw [fields]
  have root : Hn e e.heap_max.toInt.toNat = before.heap[1]!.toInt.toNat := by
    unfold Hn
    rw [index, rootStore]
  have freq : btFreq tk e (Hn e e.heap_max.toInt.toNat) = btFreq tk before before.heap[1]!.toInt.toNat := by
    rw [root]
    unfold btFreq
    rw [array]
  refine WS.pure' ⟨rfl, ?_, prepared, prepared.heap_len.toInt.toNat, built, valuesA, orderA, leaves⟩
  rw [freq, rootWeight]
  exact weight

end Zlib.Trees.Proofs
