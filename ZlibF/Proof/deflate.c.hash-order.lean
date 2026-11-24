import ZlibF.Zlib.«deflate_base.c»
import ZlibF.Proof.HeapWP

open C Zlib.Deflate
namespace Zlib.Deflate.Proofs.HashOrder

/-- The shift and the indexed read can change evaluation order without changing the returned
heap or fault when the shift count is in range. The byte pointer may still be invalid. -/
theorem updateHashAt_eq {s : DeflateStatePtr} {h : Heap} {d : DeflateState}
    (state : ldDeflateState s h = .ok (d, h)) (legal : d.hash_shift < 32)
    (window : BPtr) (i : UInt32) :
    updateHashAt s window i h = (do UPDATE_HASH s (← index8 window i.toNat)) h := by
  simp only [updateHashAt, UPDATE_HASH, bind_app, state, ushl, ite_eq_left legal, pure_app]
  cases rd : index8 window i.toNat h with
  | error e => rfl
  | ok pair =>
    obtain ⟨v, after⟩ := pair
    have eqHeap := C.Ptr.index_heap rd
    subst after
    simp only [state, ite_eq_left legal, pure_app]

theorem insertStringAt_eq {s : DeflateStatePtr} {h : Heap} {d : DeflateState}
    (state : ldDeflateState s h = .ok (d, h)) (legal : d.hash_shift < 32) (str : UInt32) :
    insertStringAt s str h = INSERT_STRING s str h := by
  simp only [insertStringAt, INSERT_STRING, bind_app, state]
  rw [updateHashAt_eq state legal]
  simp only [bind_app]
  cases rd : index8 d.window (str + (MIN_MATCH_u - 1)).toNat h with
  | error e => rfl
  | ok pair => cases pair; rfl

/-- The C assignment and its earlier model have exactly the same returning executions.
    Independent invalid reads and shifts may report a different first fault. -/
theorem updateHashAt_ok_iff (s : DeflateStatePtr) (window : BPtr) (i : UInt32)
    (h after : Heap) (u : Unit) :
    updateHashAt s window i h = .ok (u, after) ↔
      (do UPDATE_HASH s (← index8 window i.toNat)) h = .ok (u, after) := by
  cases read : index8 window i.toNat h with
  | error fault =>
    cases s with
    | none => simp [updateHashAt, bind_app, ldDeflateState, read]
    | some r =>
      cases ds : r.get h with
      | none => simp [updateHashAt, bind_app, ldDeflateState, ds, read]
      | some d =>
        by_cases good : d.hash_shift < 32 <;>
          simp [updateHashAt, bind_app, ldDeflateState, ds, ushl, good, pure_app, read, ub]
  | ok pair =>
    obtain ⟨byte, mid⟩ := pair
    have same := C.Ptr.index_heap read
    subst mid
    cases s with
    | none => simp [updateHashAt, UPDATE_HASH, bind_app, ldDeflateState, read]
    | some r =>
      cases ds : r.get h with
      | none => simp [updateHashAt, UPDATE_HASH, bind_app, ldDeflateState, ds, read]
      | some d =>
        by_cases good : d.hash_shift < 32 <;>
          simp [updateHashAt, UPDATE_HASH, bind_app, ldDeflateState, ds, ushl, good, pure_app, read, ub]

theorem insertStringAt_ok_iff (s : DeflateStatePtr) (str : UInt32) (h after : Heap) (v : UInt32) :
    insertStringAt s str h = .ok (v, after) ↔ INSERT_STRING s str h = .ok (v, after) := by
  cases s with
  | none => simp [insertStringAt, INSERT_STRING, bind_app, ldDeflateState]
  | some r =>
    cases ds : r.get h with
    | none => simp [insertStringAt, INSERT_STRING, bind_app, ldDeflateState, ds]
    | some d =>
      have state : ldDeflateState (some r) h = .ok (d, h) := ldDeflateState_ok ds
      by_cases good : d.hash_shift < 32
      · rw [insertStringAt_eq state good]
      · simp only [insertStringAt, INSERT_STRING, updateHashAt, UPDATE_HASH, bind_app, state,
          ushl, ite_eq_right good, ub]
        cases read : index8 d.window (str + (MIN_MATCH_u - 1)).toNat h with
        | error => simp
        | ok pair =>
          obtain ⟨byte, mid⟩ := pair
          have unchanged := C.Ptr.index_heap read
          subst mid
          simp [state, good, ub]

#print axioms updateHashAt_eq
#print axioms insertStringAt_eq
#print axioms updateHashAt_ok_iff
#print axioms insertStringAt_ok_iff
end Zlib.Deflate.Proofs.HashOrder
