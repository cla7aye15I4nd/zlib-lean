import ZlibF.Proof.LibcMemory

open C Std.WP
open scoped C.HeapWP

-- Touching endpoints are allowed. Both sides of the written interval keep their bytes.
example (block watched : Nat) (a : Array UInt8) (different : watched ≠ block)
    (fits : 4 ≤ a.size) (F : Option (Array UInt8) → Prop) :
    ⦃ fun h => h.bytes block = some a ∧ h.ro block = false ∧ F (h.bytes watched) ⦄
      memcpyB (.ref (.blk block) 2) (.ref (.blk block) 0) 2
    ⦃ fun _ h => h.bytes block = some (copyRange a a 2 0 2) ∧ F (h.bytes watched) ∧
        ∀ i, i < 2 ∨ 4 ≤ i → (h.bytes block).bind (·[i]?) = a[i]? ⦄ := by
  have frame := memcpyB_range_frame block block watched 2 0 2 a a F different
    (Or.inr (Or.inr (by decide))) fits (by omega)
  exact ⟨fun h ⟨live, writable, kept⟩ => frame.le_wp h ⟨live, live, writable, kept⟩⟩

-- Moving the destination one byte back produces the overlap fault.
example (h : Heap) (b : Nat) (a : Array UInt8) (live : h.bytes b = some a)
    (fits : 3 ≤ a.size) (writable : h.ro b = false) :
    memcpyB (.ref (.blk b) 1) (.ref (.blk b) 0) 2 h =
      .error (.ub "memcpy with overlapping ranges") := by
  have get : Space.get h (.blk b : BRef) = some a := live
  have ro : Space.ro h (.blk b : BRef) = false := writable
  simp [memcpyB, Ptr.memcpy, get, ro, fits, show 2 ≤ a.size by omega]

-- A live one-past pointer is valid for a zero-byte copy, even on a read-only block.
example (h : Heap) (b : Nat) (a : Array UInt8) (live : h.bytes b = some a) :
    memcpyB (.ref (.blk b) a.size) (.ref (.blk b) a.size) 0 h = .ok ((), h) := by
  have get : Space.get h (.blk b : BRef) = some a := live
  simp [memcpyB, Ptr.memcpy, get, Space.modify_eq _ _ _ _ get, copyRange]
  change { h with bytes := upd h.bytes b (some a) } = h
  rw [upd_self _ _ _ live]

example (h : Heap) (p : BPtr) :
    memcpyB .null p 0 h = .error (.ub "memcpy through a null pointer") := rfl

-- A one-iteration loop needs two condition checks, including the final false one.
private def belowOne (n : Nat) : M (Bool × Nat) := pure (decide (n < 1), n)
private def increment (n : Nat) : M Nat := pure (n + 1)

example (h : Heap) : cwhile.go belowOne increment 1 0 h = .error .outOfFuel := rfl
example (h : Heap) : cwhile.go belowOne increment 2 0 h = .ok (1, h) := rfl
