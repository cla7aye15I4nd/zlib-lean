import ZlibF.Runtime.Monad

namespace C

/-- The index of the first NUL byte of `a` at or after `i`. -/
def strlenFrom (a : Array UInt8) (i : Nat) : Option Nat :=
  if h : i < a.size then (if a[i] == 0 then some i else strlenFrom a (i + 1)) else none
termination_by a.size - i

/-- `strlen(p)`. Faults if `p` is null or dangling, or if no NUL byte follows inside the block (the C reads outside
the object). -/
def strlenB (p : BPtr) : M UInt64 := fun h =>
  match p with
  | .null => .error (.ub "strlen of a null pointer")
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "strlen through a dangling pointer")
    | some a =>
      match strlenFrom a off with
      | some j => .ok (UInt64.ofNat (j - off), h)
      | none => .error (.ub "strlen: no terminating NUL inside the object")

theorem strlenFrom_eq (a : Array UInt8) (k : Nat) (hz : a[k]? = some 0) :
    ∀ d i, i + d = k → (∀ j, i ≤ j → j < k → a[j]? ≠ some 0) → strlenFrom a i = some k := by
  intro d
  induction d with
  | zero =>
    intro i hi _
    subst hi
    have hlt : i < a.size := by
      rcases Nat.lt_or_ge i a.size with hh | hh
      · exact hh
      · simp [Array.getElem?_eq_none hh] at hz
    rw [strlenFrom]
    simp [hlt]
    have : a[i] = 0 := by simpa [hlt] using hz
    simp [this]
  | succ d ih =>
    intro i hi hn
    have hlt : i < a.size := by
      rcases Nat.lt_or_ge i a.size with hh | hh
      · exact hh
      · simp [Array.getElem?_eq_none (by omega : a.size ≤ k)] at hz
    have hne : a[i] ≠ 0 := by
      intro h0
      exact hn i (Nat.le_refl _) (by omega) (by simp [hlt, h0])
    rw [strlenFrom]
    simp only [hlt, dite_true]
    have : (a[i] == 0) = false := by simpa using hne
    simp only [this, Bool.false_eq_true, ite_false]
    exact ih (i + 1) (by omega) (fun j hj hjk => hn j (by omega) hjk)

theorem strlenB_ok {h : Heap} {r : BRef} {a : Array UInt8} {off k : Nat}
    (hg : Space.get h r = some a) (hk : off ≤ k) (hz : a[k]? = some 0)
    (hn : ∀ j, off ≤ j → j < k → a[j]? ≠ some 0) :
    OkOn h (strlenB (Ptr.ref r off)) (UInt64.ofNat (k - off)) := by
  unfold OkOn strlenB
  simp [hg, strlenFrom_eq a k hz (k - off) off (by omega) hn]

/-! ### String literals

A literal is a static, read-only object that is never freed and never consumes an allocation (`BRef.str`, `strTable`
in `Schema.lean`). `strLitRef s` is the pointer to the literal `s`: the same pointer every time, no change to the heap.
The set of literals is closed (the string literals of the library sources); any other text is a fault. -/

/-- The number of the literal `s` in `strTable`, if it is one. -/
def strIndex (s : String) : Option Nat := strTable.findIdx? (fun t => t == s)

/-- A string literal of the C sources: a pointer to its first byte. It reads the heap and does not change it; it
faults if `s` is not a literal of the sources (`strTable`). -/
def strLitRef (s : String) : M BPtr := fun h =>
  match strIndex s with
  | some i => .ok (.ref (.str i) 0, h)
  | none => .error (.ub "string literal not in the table of literals of the sources")

theorem strLitRef_of_index {h : Heap} {s : String} {i : Nat} (hi : strIndex s = some i) :
    strLitRef s h = .ok (.ref (.str i) 0, h) := by
  simp [strLitRef, hi]

theorem strIndex_get {s : String} {i : Nat} (hi : strIndex s = some i) : strTable[i]? = some s := by
  unfold strIndex at hi
  rw [Array.findIdx?_eq_some_iff_getElem] at hi
  obtain ⟨h1, h2, -⟩ := hi
  rw [Array.getElem?_eq_getElem h1]
  simpa using h2

/-- Every text of `strTable` is found. -/
theorem strIndex_of_mem {s : String} (hs : s ∈ strTable) : ∃ i, strIndex s = some i := by
  cases hx : strIndex s with
  | some i => exact ⟨i, rfl⟩
  | none =>
    exfalso
    unfold strIndex at hx
    rw [Array.findIdx?_eq_none_iff] at hx
    have := hx s hs
    simp at this

/-- A literal of the sources: the pointer is the start of the read-only static array of its text and a NUL, and the
heap is unchanged (no block is allocated). -/
theorem strLitRef_of_mem {h : Heap} {s : String} (hs : s ∈ strTable) :
    ∃ i, strLitRef s h = .ok (.ref (.str i) 0, h) ∧ strTable[i]? = some s := by
  obtain ⟨i, hi⟩ := strIndex_of_mem hs
  exact ⟨i, strLitRef_of_index hi, strIndex_get hi⟩

/-- The bytes behind the pointer of a literal: the text and a NUL. -/
theorem strLitRef_get {h : Heap} {s : String} {i : Nat} (hi : strIndex s = some i) :
    Space.get h (BRef.str i) = some (strBytes s) := by
  have hlt : i < strTable.size := (Array.getElem?_eq_some_iff.mp (strIndex_get hi)).1
  rw [BRef.get_str]
  simp only [staticStringBytes, hlt, ite_true, strIndex_get hi, Option.map_some]

/-- A literal is read-only. -/
theorem strLitRef_ro (h : Heap) (i : Nat) : Space.ro h (BRef.str i) = true := rfl

end C
