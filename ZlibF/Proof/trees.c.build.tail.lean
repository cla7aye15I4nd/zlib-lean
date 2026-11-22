import ZlibF.Proof.«deflate.c.engine.loops»
import ZlibF.Proof.«trees.c.heap.gbtop»
import ZlibF.Proof.«trees.c.codes»
import ZlibF.Proof.«trees.c.build.order»
import ZlibF.Proof.«trees.c.build.force»
import ZlibF.Proof.«trees.c.build.heapify»
import ZlibF.Proof.«trees.c.build.merge»

/-!
# trees.c: the heap-building prefix and the code-assignment suffix

The prefix copies the actual translation in source order. The suffix uses
proved executions of both callees, rather than assumed callee contracts.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB

/-- The actual ordered leaf prefix followed by the full merge loop. -/
def btMergedStart (s : DeflateStatePtr) (desc : TreeDescPtr) : M (CtDataPtr × Int32) := do
  let (tree, _stree, elems, mc) ← btSortedStart s desc
  let _ ← btMergeLoop s tree elems
  pure (tree, mc)

/-- `build_tree` up to the root heap store. -/
def btHeap (s : DeflateStatePtr) (desc : TreeDescPtr) : M (CtDataPtr × Int32) := do
  let (tree, max_code) ← btMergedStart s desc
  -- s->heap[--(s->heap_max)] = s->heap[SMALLEST];
  btSaveRoot s
  pure (tree, max_code)

/-- The final two calls of `build_tree`, verbatim. -/
def btCodes (s : DeflateStatePtr) (desc : TreeDescPtr) (tree : CtDataPtr) (max_code : Int32) : M Unit := do
  gen_bitlen s desc
  gen_codes tree max_code (← pBlCount s)

set_option maxHeartbeats 1000000 in
/-- Naming the two source fragments leaves the actual function unchanged. -/
theorem build_tree_eq_heap_codes (s : DeflateStatePtr) (desc : TreeDescPtr) :
    build_tree s desc = (do
      let (tree, max_code) ← btHeap s desc
      btCodes s desc tree max_code) := by
  simp only [build_tree, btHeap, btMergedStart, btSortedStart, btLeavesStart, btScanStart, btScan, btForce, btOrder, btHeapify, btCodes, M_bind_assoc, M_pure_bind]
  unfold btSaveRoot btMergeLoop btMergeBody btMergeOpen btPick2 btKeepChildren btMakeParent btSetFreq btSetDepth btSetParents btMergeClose
  simp only [M_bind_assoc, M_pure_bind, merge_ite_bind]
  rfl

/-- The actual bit-length result supplies all length and count-array bounds
needed by code assignment. Symbols absent from the heap have the zero length
written by the first `build_tree` scan. -/
theorem GBDone.code_inputs {tk : TK} {d e : DeflateState}
    {hm J elems maxc L : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (shape : PShape (Hn d) hm J elems maxc) (hfit : elems ≤ (tk.arr d).size)
    (hL : L ≤ 15)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → ((tk.arr d)[v]!).dl = 0)
    (done : GBDone tk d hm J maxc L xb slOpt e) :
    e.bl_count.size = 16 ∧ maxc + 1 ≤ (tk.arr e).size ∧
      ∀ v ≤ maxc, ((tk.arr e)[v]!).dl.toNat ≤ 15 := by
  obtain ⟨T, B, O, S, rfl, hsz, hbsz, hfreq, hout, hlengths, rest⟩ := done
  simp only [mkP1_bl_count, tk_arr_mkP1]
  refine ⟨hbsz, by have := shape.maxc_lt; omega, ?_⟩
  intro v hv
  by_cases hseen : ∃ q, hm ≤ q ∧ q < 573 ∧ Hn d q = v
  · obtain ⟨q, hq1, hq2, hqv⟩ := hseen
    have hqne : q ≠ hm := by
      intro heq; subst q
      have hr := shape.root
      have hj := shape.J1
      have hc := shape.maxc_lt
      omega
    have hidx : q - hm - 1 < 2 * J := by have := shape.hm_eq; omega
    have hq : hm + 1 + (q - hm - 1) = q := by omega
    have hl := (hlengths (q - hm - 1) hidx (by rw [hq, hqv]; exact hv)).2
    rw [hq, hqv] at hl
    exact Nat.le_trans hl hL
  · have hnone : ∀ q, hm ≤ q → q < 573 → Hn d q ≠ v := by
      intro q hq1 hq2 heq
      exact hseen ⟨q, hq1, hq2, heq⟩
    rw [hout v hnone, hzero v hv hnone]
    decide

/-- The actual final two calls compose on one heap. The length limit and
count-array size passed to `gen_codes` are conclusions of `gen_bitlen`.
The zero-length condition concerns only symbols absent from the heap; the
first scan establishes it. No callee specification appears as a hypothesis. -/
theorem ws_btCodes {h0 : Heap} {id : Nat} {tk : TK} {d : DeflateState}
    {r : TreeDescRef} {sref : StaticTreeDescRef} {dd : TreeDesc} {sd : StaticTreeDesc}
    {hm J elems maxc L baseN : Nat} {xb : Nat → Nat} {slOpt : Option (Nat → Nat)}
    (hdd : r.get (setD h0 id d) = some dd) (hsd : StaticTreeDescRef.get h0 sref = some sd)
    (hstat : dd.stat_desc = some sref) (htree : dd.dyn_tree = .ref (tk.ref id) 0)
    (ctx : P1Ctx h0 id tk d sd.static_tree sd.extra_bits dd.max_code sd.extra_base sd.max_length
      hm J elems maxc L baseN xb slOpt)
    (hHM : d.heap_max.toInt = hm) (hel : elems ≤ 2 ^ L) (helem : elems ≤ 286)
    (hzero : ∀ v ≤ maxc, (∀ q, hm ≤ q → q < 573 → Hn d q ≠ v) → ((tk.arr d)[v]!).dl = 0) :
    WS h0 id (btCodes (Sp id) (some r) (.ref (tk.ref id) 0) dd.max_code) d
      (fun _ e => ∃ mid : DeflateState, GBDone tk d hm J maxc L xb slOpt mid ∧
        ∃ a : Array CtData, e = tk.setArr mid a ∧ a.size = (tk.arr mid).size ∧
          ∀ j < a.size, a[j]! =
            if j < (dd.max_code.toInt + 1).toNat ∧ ((tk.arr mid)[j]!).dl ≠ 0 then
              { (tk.arr mid)[j]! with fc := UInt16.ofNat (Math.storedCode
                (fun i => mid.bl_count[i]!.toNat) (fun i => ((tk.arr mid)[i]!).dl.toNat) j) }
            else (tk.arr mid)[j]!) := by
  unfold btCodes
  refine WS.bind' (ws_gen_bitlen hdd hsd hstat htree ctx hHM hel) fun _ mid hdone => ?_
  have hfit : elems ≤ (tk.arr d).size := by have := ctx.nc; omega
  obtain ⟨hbsz, hsize, hlengths⟩ := hdone.code_inputs ctx.shape hfit ctx.L15 hzero
  have hm : dd.max_code.toInt = maxc := ctx.mcv
  have hmc : maxc < elems := ctx.shape.maxc_lt
  have hrange : (dd.max_code.toInt + 1).toNat = maxc + 1 := by omega
  refine WS.bind' ws_pBlCount fun p e1 ⟨hp, he1⟩ => ?_
  subst e1; subst p
  refine WS.mono (ws_gen_codes mid tk dd.max_code (by omega) (by omega) (by omega)
    (by rw [hrange]; exact hsize) ?_) ?_
  · intro j hj
    exact hlengths j (by rw [hrange] at hj; omega)
  · intro _ e he
    exact ⟨mid, hdone, he⟩

end Zlib.Trees.Proofs
