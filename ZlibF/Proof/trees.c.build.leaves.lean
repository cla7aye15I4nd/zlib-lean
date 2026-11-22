import ZlibF.Proof.«trees.c.build.force»
import ZlibF.Proof.«trees.c.heap.gbtop»

/-! # trees.c: actual descriptor/reset/scan/repair prefix

The two prefix definitions and execution statements retain their saved
statements. The suffix is copied from current main only to check the complete
source decomposition; no safety or correctness of that suffix is assumed.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB

/-- The actual descriptor reads, heap reset and first symbol scan. -/
def btScanStart (s : DeflateStatePtr) (desc : TreeDescPtr) :
    M (CtDataPtr × CtDataPtr × Int32 × Int32) := do
  let dd ← ldTreeDesc desc
  let tree := dd.dyn_tree
  let sd ← ldStaticTreeDesc dd.stat_desc
  let stree := sd.static_tree
  let elems := sd.elems
  md s fun d => { d with heap_len := 0 }
  md s fun d => { d with heap_max := HEAP_SIZE }
  let max_code ← btScan s tree elems
  pure (tree, stree, elems, max_code.2)

/-- The actual scan followed by the actual two-leaf repair. -/
def btLeavesStart (s : DeflateStatePtr) (desc : TreeDescPtr) :
    M (CtDataPtr × CtDataPtr × Int32 × Int32) := do
  let (tree, stree, elems, mc) ← btScanStart s desc
  let mc ← btForce s tree stree mc
  pure (tree, stree, elems, mc)

/-- The actual start of `build_tree` establishes the scan invariant. Neither
the old heap length, the old depths nor the old code lengths are restricted.
Both heap-control writes preceding the scan execute on the actual heap. -/
theorem ws_btScanStart {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he0 : 0 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) :
    WS h0 id (btScanStart (Sp id) (some r)) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ a.2.1 = sd.static_tree ∧ a.2.2.1 = sd.elems ∧
        BTScanInv tk { d with heap_len := 0, heap_max := HEAP_SIZE } sd.elems.toInt.toNat a.2.2.2 e) := by
  unfold btScanStart
  refine WS.bind' (ws_ldTreeDesc r dd hdd) fun dd' e1 ⟨hdd', he1⟩ => ?_
  subst e1; subst dd'
  rw [hstat]
  refine WS.bind' (ws_ldStaticTreeDesc sref sd hsd) fun sd' e1 ⟨hsd', he1⟩ => ?_
  subst e1; subst sd'
  rw [htree]
  refine WS.bind' (ws_md (fun e => { e with heap_len := 0 })) fun _ e1 he1 => ?_
  subst e1
  refine WS.bind' (ws_md (fun e => { e with heap_max := HEAP_SIZE })) fun _ e1 he1 => ?_
  subst e1
  let d0 : DeflateState := { d with heap_len := 0, heap_max := HEAP_SIZE }
  have ht0 : tk.arr d0 = tk.arr d := by cases tk <;> rfl
  refine WS.bind' (ws_btScan tk d0 sd.elems he0 he286 (by rw [ht0]; exact hT)
    hD (by change sd.elems.toInt < (d.heap.size : Int); omega)
    (by change d.heap.size ≤ 573; omega) rfl) fun a e ⟨hn, hi⟩ => ?_
  exact WS.pure' ⟨rfl, rfl, rfl, hi⟩

/-- The actual descriptor/reset/scan/repair prefix establishes the live leaf
representation needed by heap construction. Every repair premise comes from
the actual scan result. The postcondition retains the exact intermediate
scan state and the repair's bounded update trace and final heap length. -/
theorem ws_btLeavesStart {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {sl : Option (Nat → UInt16)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (he3 : 3 ≤ sd.elems.toInt) (he286 : sd.elems.toInt ≤ 286)
    (hT : sd.elems.toInt ≤ (tk.arr d).size) (hD : sd.elems.toInt ≤ d.depth.size)
    (hH : d.heap.size = 573) (hs : BTStatic h0 id sd.static_tree sd.elems.toInt.toNat sl) :
    WS h0 id (btLeavesStart (Sp id) (some r)) d (fun a e =>
      a.1 = .ref (tk.ref id) 0 ∧ a.2.1 = sd.static_tree ∧ a.2.2.1 = sd.elems ∧
        BTLeafInv tk sd.elems.toInt.toNat a.2.2.2 e ∧
          ∃ (mid : DeflateState) (mc : Int32) (k : Nat),
            BTScanInv tk { d with heap_len := 0, heap_max := HEAP_SIZE } sd.elems.toInt.toNat mc mid ∧
            e.heap_len.toInt = max 2 mid.heap_len.toInt ∧ k ≤ 2 ∧
            k = (2 - mid.heap_len.toInt).toNat ∧ BTForceTrace tk sl k mc mid a.2.2.2 e) := by
  unfold btLeavesStart
  refine WS.bind' (ws_btScanStart hdd hsd hstat htree (by omega) he286 hT hD hH)
    fun a mid ⟨ht, hst, he, hscan⟩ => ?_
  rcases a with ⟨tree, stree, elems, mc⟩
  dsimp only at ht hst he hscan ⊢
  subst tree; subst stree; subst elems
  let d0 : DeflateState := { d with heap_len := 0, heap_max := HEAP_SIZE }
  have ht0 : tk.arr d0 = tk.arr d := by cases tk <;> rfl
  have hleaf := BTLeafInv.of_scan hscan (by omega) (by omega)
    (by change _ ≤ (tk.arr d0).size; rw [ht0]; omega) (by change _ ≤ d.depth.size; omega) hH
  refine WS.bind' (ws_btForce tk mid mc sd.elems.toInt.toNat sd.static_tree sl hs hleaf)
    fun mc' e ⟨hleaf', hlen, k, hk, hkexact, htrace⟩ => ?_
  exact WS.pure' ⟨rfl, rfl, rfl, hleaf', mid, mc, k, hscan, hlen, hk, hkexact, htrace⟩


end Zlib.Trees.Proofs
