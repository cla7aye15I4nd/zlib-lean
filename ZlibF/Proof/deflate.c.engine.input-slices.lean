import ZlibF.Proof.«deflate.c.engine.body-input-ledger»

/-! # Actual input slices at advanced caller cursors -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A readable range contains precisely its declared number of bytes. -/
theorem caller_bytes_length {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8}
    (bytes : Bytes h p n xs) : xs.length = n := by
  rcases bytes with ⟨_null, rfl, rfl⟩ | ⟨ref, off, a, _pointer, _get, fit, rfl⟩
  · rfl
  · simp only [List.length_take, List.length_drop, Array.length_toList]
    omega

/-- Bytes consumed at the advanced cursor are exactly the corresponding
slice of a full input snapshot on the same actual heap. -/
theorem caller_bytes_advanced_slice {h : Heap} {p : BPtr} {n used count : Nat}
    {snapshot copied : List UInt8} (bytes : Bytes h p n snapshot)
    (slice : Bytes h (advance p used) count copied) (bound : used + count ≤ n) :
    copied = (snapshot.drop used).take count := by
  rcases bytes with ⟨rfl, rfl, rfl⟩ | ⟨ref, off, a, rfl, get, fit, rfl⟩
  · have empty : count = 0 := by omega
    have length := caller_bytes_length slice
    have nil : copied = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    simp only [nil, List.drop_nil, List.take_nil]
  · rcases slice with ⟨impossible, _⟩ | ⟨other, nextOff, next, pointer, getNext, _fitNext, value⟩
    · cases impossible
    · have same : ref = other ∧ off + used = nextOff := Ptr.ref.inj pointer
      obtain ⟨rfl, rfl⟩ := same
      have arrays : next = a := Option.some.inj (getNext.symm.trans get)
      subst next
      rw [value, List.drop_take, List.take_take, Nat.min_eq_left (by omega), List.drop_drop]

end Zlib.Deflate.Engine.Proofs
