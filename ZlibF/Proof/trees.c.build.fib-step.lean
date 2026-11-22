import ZlibF.Math.DeflateOverlay
import ZlibF.Proof.«trees.c.build.forest»

/-!
# trees.c: the weight facts needed by the Huffman refinement

The translated selection really removes the two least-weight nodes. Parent
creation uses their mathematical sum when its explicit 16-bit bound holds.
These are the first operational links to the pure Fibonacci argument; they
do not establish that argument for an entire translated build_tree run.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

/-- The source comparison orders frequencies before its depth tie-break. -/
theorem sm_frequency_le {T : Array CtData} {D : Array UInt8} {n m : Int32}
    (order : sm T D n m = true) :
    T[n.toInt.toNat]!.fc.toNat ≤ T[m.toInt.toNat]!.fc.toNat := by
  simp only [sm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq, UInt16.lt_iff_toNat_lt] at order
  rcases order with less | ⟨eq, _⟩
  · omega
  · rw [eq]
    exact Nat.le_refl _

/-- Total mathematical frequency in the populated source queue. -/
def btQueueWeight (tk : TK) (d : DeflateState) (len : Nat) : Nat :=
  GB.rs (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat) len

/-- A complete actual merge preserves the queue's mathematical weight.
The selected child sum fits because both children are distinct members of
the bounded queue. Consequently the source UInt16 addition does not wrap.
The forest and total-weight premises are data about this run state; no
called-function contract is assumed. -/
theorem ws_btMergeBody_weight {h0 : Heap} {id : Nat} {tk : TK} {d0 d : DeflateState}
    {N K j : Nat} {mc node : Int32} (hi : BTForest tk N K j mc d0 node d)
    (more : j + 1 < K) (total : btQueueWeight tk d (K - j) < 2 ^ 16) :
    WS h0 id (btMergeBody (Sp id) (.ref (tk.ref id) 0) node) d (fun _ e =>
      btQueueWeight tk e (K - (j + 1)) = btQueueWeight tk d (K - j)) := by
  have hcounter := hi.queue.counter
  have hlen := hi.queue.len
  have hmax := hi.queue.max
  have hsize := hi.queue.heap
  have hTsize := hi.queue.tree
  have hDsize := hi.queue.depth
  have hstage := hi.queue.stage
  have hK := hi.queue.kN
  have hN := hi.queue.n286
  have hnode : NV (tk.arr d) d.depth node := ⟨by omega, by omega, by omega⟩
  refine WS.mono (ws_btMergeBody_forest tk d (K - j) node hlen
    (by omega) (by omega) (by omega) (by omega) (by omega) hnode (by omega)
    (fun i a b => hi.queue.valid i a (by omega))
    (fun i i' a b c e => hi.queue.injective i i' a (by omega) c (by omega)) hi.queue.order) ?_
  intro next e ⟨counter, n, m, distinct, ⟨pn, pnlo, pnhi, first⟩,
    ⟨pm, pmlo, pmhi, second⟩, len, boundary, keepn, keepm, tail, tree, depth, root, counts⟩
  have nv := hi.queue.valid pn pnlo (by omega)
  have mv := hi.queue.valid pm pmlo (by omega)
  rw [← first] at nv
  rw [← second] at mv
  have hn : NV (tk.arr d) d.depth n := ⟨nv.1, by omega, by omega⟩
  have hm : NV (tk.arr d) d.depth m := ⟨mv.1, by omega, by omega⟩
  have indices : pn ≠ pm := by
    intro eq
    exact distinct (first.trans (eq ▸ second.symm))
  have child_sum := GB.two_le_rs
    (fun i => (btFreq tk d d.heap[i + 1]!.toInt.toNat).toNat)
    (K - j) (pn - 1) (pm - 1) (by omega) (by omega) (by omega)
  simp only [Nat.sub_add_cancel pnlo, Nat.sub_add_cancel pmlo] at child_sum
  rw [← first, ← second] at child_sum
  have nowrap : (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat < 2 ^ 16 := by
    unfold btQueueWeight at total
    omega
  have frequencies (v : Nat) : btFreq tk e v =
      if v = node.toInt.toNat then btFreq tk d n.toInt.toNat + btFreq tk d m.toInt.toNat
      else btFreq tk d v := by
    unfold btFreq
    rw [tree, btParentState_fc tk d n m node hn hm hnode]
  have unchanged (v : Int32) (vlo : 0 ≤ v.toInt) (vhi : v.toInt < node.toInt) :
      (btFreq tk e v.toInt.toNat).toNat = (btFreq tk d v.toInt.toNat).toNat := by
    rw [frequencies, ite_eq_right (by omega)]
  have parent_weight : (btFreq tk e node.toInt.toNat).toNat =
      (btFreq tk d n.toInt.toNat).toNat + (btFreq tk d m.toInt.toNat).toNat := by
    rw [frequencies, ite_eq_left rfl, UInt16.toNat_add, Nat.mod_eq_of_lt nowrap]
  have old_weight : GB.rs (fun i => (btFreq tk e d.heap[i + 1]!.toInt.toNat).toNat) (K - j) =
      btQueueWeight tk d (K - j) := by
    apply GB.rs_congr
    intro i hidx
    have valid := hi.queue.valid (i + 1) (by omega) (by omega)
    exact unchanged _ valid.1 valid.2
  have count_weight := counts (fun v => (btFreq tk e v.toInt.toNat).toNat)
  rw [old_weight, parent_weight, unchanged n nv.1 nv.2, unchanged m mv.1 mv.2] at count_weight
  have new_length : K - (j + 1) = K - j - 1 := by omega
  unfold btQueueWeight
  rw [new_length]
  rw [Nat.add_assoc] at count_weight
  exact Nat.add_right_cancel count_weight

end Zlib.Trees.Proofs
