import ZlibF.Proof.«trees.c.build.leaves»
import ZlibF.Proof.«trees.c.build.heapify»

/-! # trees.c: actual leaf preparation followed by heap ordering

The existing leaf, heap and source-comparison facts are composed on one
actual state. The residual suffix is named only for whole-function equality.
No execution or correctness of that suffix is assumed.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB

/-- Actual leaf preparation, descriptor maximum store and heap construction. -/
def btSortedStart (s : DeflateStatePtr) (desc : TreeDescPtr) :
    M (CtDataPtr × CtDataPtr × Int32 × Int32) := do
  let (tree, stree, elems, mc) ← btLeavesStart s desc
  btOrder s desc tree mc
  pure (tree, stree, elems, mc)

/-- The actual scan invariant retains the sizes of the two arrays needed
for internal-node creation. -/
theorem BTScanInv.merge_sizes {tk : TK} {d e : DeflateState} {N : Nat} {mc : Int32}
    (hi : BTScanInv tk d N mc e) :
    (tk.arr e).size = (tk.arr d).size ∧ e.depth.size = d.depth.size := by
  obtain ⟨T, H, D, hl, rfl, hT, hH, hD, rest⟩ := hi
  exact ⟨by simpa only [btScanState_tree] using hT, hD⟩

/-- Every actual dummy-leaf update retains both array sizes. -/
theorem BTForceTrace.merge_sizes {tk : TK} {sl : Option (Nat → UInt16)}
    {k : Nat} {mc0 mc : Int32} {d0 d : DeflateState} (hi : BTForceTrace tk sl k mc0 d0 mc d) :
    (tk.arr d).size = (tk.arr d0).size ∧ d.depth.size = d0.depth.size := by
  induction hi with
  | nil => exact ⟨rfl, rfl⟩
  | snoc node hl before hn hnT hm hhl ih =>
    simpa only [btForceState_tree, btForceState_depth, size_set!] using ih


/-- The complete actual prefix before merging: descriptors are read, the
heap is reset, symbols are scanned, the alphabet is repaired, its maximum is
stored, and the heap is constructed. It establishes the full live-leaf
representation, heap order and root minimality on the same actual heap.
No old length, depth, heap length or heap-order premise is required. -/
theorem ws_btSortedStart {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ a.2.1 = sd.static_tree ∧ a.2.2.1 = sd.elems ∧
        BTLeafInv tk sd.elems.toInt.toNat a.2.2.2 e ∧ 2 ≤ e.heap_len.toInt ∧ e.heap_max = HEAP_SIZE ∧
        (dk.descRef id).get (setD h0 id e) = some { dd with max_code := a.2.2.2 } ∧
        HeapOK (sm (tk.arr e) e.depth) (fun q => e.heap[q]!) e.heap_len.toInt.toNat 0 ∧
        ∀ q : Nat, 1 ≤ q → (q : Int) ≤ e.heap_len.toInt →
          sm (tk.arr e) e.depth e.heap[1]! e.heap[q]! = true) := by
  unfold btSortedStart
  refine WS.bind' (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    fun a mid ⟨ht, hst, he, hleaf, scan, scanMc, k, hscan, hlen, hk, hkexact, htrace⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf htrace ⊢
  subst tree; subst stree; subst elems
  have hmid := htrace.desc_heap_max dk
  have hscanframe := hscan.desc_heap_max dk
  have hresetdesc : dk.getDesc { d with heap_len := 0, heap_max := HEAP_SIZE } = dk.getDesc d := by cases dk <;> rfl
  have hddval : dk.getDesc d = dd := by
    cases dk <;> simpa [TK.descRef, TK.getDesc, TreeDescRef.get, setD] using hdd
  have hdesc : dk.getDesc mid = dd := hmid.1.trans (hscanframe.1.trans (hresetdesc.trans hddval))
  have hmax : mid.heap_max = HEAP_SIZE := hmid.2.trans hscanframe.2
  have htwo : 2 ≤ mid.heap_len.toInt := by omega
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc hleaf)
    fun _ e ⟨hleaf', H, he, hsH, hf, hp, ho, hdesc', hmin⟩ => ?_
  subst e
  have hmax' : (dk.setDesc mid { dk.getDesc mid with max_code := mc }).heap_max = HEAP_SIZE := by
    cases dk <;> exact hmax
  refine WS.pure' ⟨rfl, rfl, rfl, hleaf', ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tk_setDesc_len]; exact htwo
  · exact hmax'
  · simpa only [hdesc] using hdesc'
  · cases tk <;> cases dk <;> exact ho
  · intro q hq1 hq2
    simp only [tk_setDesc_len] at hq2
    have hmin' := hmin q hq1 (by omega)
    cases tk <;> cases dk <;> exact hmin'

/-- The complete actual leaf prefix preserves internal-node array capacity.
This supplements the already proved leaf/order result with a separate exact
frame property. -/
theorem ws_btSortedStart_sizes {h0 : Heap} {id : Nat} {tk dk : TK} {d : DeflateState}
    {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc} {sl : Option (Nat → UInt16)}
    (hdd : (dk.descRef id).get (setD h0 id d) = some dd)
    (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btSortedStart (Sp id) (some (dk.descRef id))) d (fun _ e =>
      (tk.arr e).size = (tk.arr d).size ∧ e.depth.size = d.depth.size) := by
  unfold btSortedStart
  refine WS.bind' (ws_btLeavesStart hdd hsd hstat htree he3 he286 hT hD hH hs)
    fun a mid ⟨ht, hst, he, hleaf, scan, scanMc, k, hscan, hlen, hk, hkexact, htrace⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hleaf htrace ⊢
  subst tree; subst stree; subst elems
  have hsz := htrace.merge_sizes
  have hsz0 := hscan.merge_sizes
  have ht0 : tk.arr { d with heap_len := 0, heap_max := HEAP_SIZE } = tk.arr d := by cases tk <;> rfl
  rw [ht0] at hsz0
  have htMid : (tk.arr mid).size = (tk.arr d).size := hsz.1.trans hsz0.1
  have hdMid : mid.depth.size = d.depth.size := hsz.2.trans hsz0.2
  refine WS.bind' (ws_btOrder_leaf tk dk mid sd.elems.toInt.toNat mc hleaf)
    fun _ e ⟨hleaf', H, he, hsH, hf, hp, ho, hdesc', hmin⟩ => ?_
  subst e
  refine WS.pure' ⟨?_, ?_⟩
  · rw [tk_arr_heap, tk_arr_setDesc]
    exact htMid
  · cases dk <;> exact hdMid


end Zlib.Trees.Proofs
