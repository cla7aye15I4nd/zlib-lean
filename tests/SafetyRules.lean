import ZlibF.Proof.LibcMemory
import ZlibF.Proof.CountedLoop
import ZlibF.Proof.LibcScalar
import ZlibF.Runtime.CAbi

open C Std.WP
open scoped C.HeapWP

-- An unsigned output store checks the address, including the origin of an embedded array.
example (h : Heap) (b : Nat) (v : UInt32) :
    storeU32 (.ref (.blk b) 1) v h = .error (.ub "misaligned unsigned int store") := rfl

example (h : Heap) (b : Nat) :
    loadU32 (.ref (.blk b) 1) h = .error (.ub "misaligned unsigned int load") := rfl

example (h : Heap) (b : Nat) (v : Int32) :
    storeI32 (.ref (.blk b) 1) v h = .error (.ub "misaligned int store") := rfl

example (h : Heap) (b : Nat) (v : UInt32) :
    storeU32 (.ref (.blk b) 4) v h = store32 (.ref (.blk b) 4) v.toInt32 h := by
  simp [storeU32, ByteAddress.value]

example (h : Heap) (i : Nat) (v : UInt32) (origin : (h.byteBase (.dstate_depth i)).val = 1) :
    storeU32 (.ref (.dstate_depth i) 3) v h = store32 (.ref (.dstate_depth i) 3) v.toInt32 h := by
  simp [storeU32, ByteAddress.value, ByteAddress.base, origin]

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

-- Overlapping intra-block `memmoveB` succeeds (where `memcpyB` faults) and frames the untouched slice.
example (block watched : Nat) (a : Array UInt8) (different : watched ≠ block)
    (fits : 3 ≤ a.size) (F : Option (Array UInt8) → Prop) :
    ⦃ fun h => h.bytes block = some a ∧ h.ro block = false ∧ F (h.bytes watched) ⦄
      memmoveB (.ref (.blk block) 1) (.ref (.blk block) 0) 2
    ⦃ fun _ h => h.bytes block = some (copyRange a a 1 0 2) ∧ F (h.bytes watched) ∧
        ∀ i, i < 1 ∨ 3 ≤ i → (h.bytes block).bind (·[i]?) = a[i]? ⦄ := by
  have frame := memmoveB_range_frame block block watched 1 0 2 a a F different (by omega) (by omega)
  exact ⟨fun h ⟨live, writable, kept⟩ => frame.le_wp h ⟨live, live, writable, kept⟩⟩

-- `memsetB_range_frame` writes the exact slice value while framing surrounding indices and a watched block.
example (block watched : Nat) (a : Array UInt8) (val : UInt8) (different : watched ≠ block)
    (fits : 4 ≤ a.size) (F : Option (Array UInt8) → Prop) :
    ⦃ fun h => h.bytes block = some a ∧ h.ro block = false ∧ F (h.bytes watched) ⦄
      memsetB (.ref (.blk block) 1) val 2
    ⦃ fun _ h => h.bytes block = some (fillRange a 1 2 val) ∧ F (h.bytes watched) ∧
        ∀ i, (h.bytes block).bind (·[i]?) = if 1 ≤ i ∧ i < 3 then some val else a[i]? ⦄ :=
  memsetB_range_frame block watched 1 2 a val F different (by omega)

-- Stateful `cwhile_inv_spec`: write `0xAA` to `n` consecutive bytes while preserving `watched`.
example (block watched n : Nat) (different : watched ≠ block) (bound : n < fuel)
    (fits : n ≤ 64) (a₀ : Array UInt8) (F : Option (Array UInt8) → Prop) :
    ⦃ fun h => h.bytes block = some a₀ ∧ a₀.size = 64 ∧ h.ro block = false ∧ F (h.bytes watched) ⦄
      cwhile (fun j => pure (decide (j < n), j))
        (fun j => do store8 (.ref (.blk block) j) 0xAA; pure (j + 1)) 0
    ⦃ fun j h => j = n ∧ (∃ a, h.bytes block = some a ∧ a.size = 64) ∧ F (h.bytes watched) ⦄ := by
  have hspec := cwhile_inv_spec
    (cond := fun j => pure (decide (j < n), j))
    (body := fun j => do store8 (.ref (.blk block) j) 0xAA; pure (j + 1))
    (fun j s h => s = j ∧ j ≤ n ∧ (∃ a, h.bytes block = some a ∧ a.size = 64) ∧
      h.ro block = false ∧ F (h.bytes watched))
    0 n bound
    (fun j s h hj ⟨hs, _, _, _, _⟩ => by subst s; rfl)
    (fun j s h hj ⟨hs, _, ⟨a, hb, hsz⟩, hro, hF⟩ => by
      subst s
      have hst := Ptr.store_ok (h := h) (r := BRef.blk block) (off := j) (v := (0xAA : UInt8))
        hb hro (by omega)
      refine ⟨j + 1, Space.put h (BRef.blk block) (a.set! j 0xAA), ?_, rfl, by omega,
        ⟨a.set! j 0xAA, by simp [Space.put], by simpa using hsz⟩, hro,
        by simpa [Space.put, upd_ne _ _ _ _ different] using hF⟩
      rw [bind_app, show store8 (.ref (BRef.blk block) j) 0xAA h = _ from hst]
      rfl)
  refine ⟨fun h ⟨hb, hsz, hro, hF⟩ => ?_⟩
  exact hspec.entails_wp_of_post (fun j h ⟨rfl, _, ha, _, hF'⟩ => ⟨rfl, ha, hF'⟩) h
    ⟨rfl, Nat.zero_le n, ⟨a₀, hb, hsz⟩, hro, hF⟩

-- Stateful `cdoWhile_inv_spec`: execute `n + 1` heap-mutating iterations while preserving `watched`.
example (block watched n : Nat) (different : watched ≠ block) (bound : n < fuel)
    (fits : n + 1 ≤ 64) (a₀ : Array UInt8) (F : Option (Array UInt8) → Prop) :
    ⦃ fun h => h.bytes block = some a₀ ∧ a₀.size = 64 ∧ h.ro block = false ∧ F (h.bytes watched) ⦄
      cdoWhile (fun j => do store8 (.ref (.blk block) j) 0x55; pure (j + 1))
        (fun j => pure (decide (j - 1 < n), j)) 0
    ⦃ fun j h => j = n + 1 ∧ (∃ a, h.bytes block = some a ∧ a.size = 64) ∧ F (h.bytes watched) ⦄ := by
  have hspec := cdoWhile_inv_spec
    (body := fun j => do store8 (.ref (.blk block) j) 0x55; pure (j + 1))
    (cond := fun j => pure (decide (j - 1 < n), j))
    (fun j s h => s = j ∧ j ≤ n + 1 ∧ (∃ a, h.bytes block = some a ∧ a.size = 64) ∧
      h.ro block = false ∧ F (h.bytes watched))
    0 n bound
    (fun j s h hj ⟨hs, _, ⟨a, hb, hsz⟩, hro, hF⟩ => by
      subst s
      have hst := Ptr.store_ok (h := h) (r := BRef.blk block) (off := j) (v := (0x55 : UInt8))
        hb hro (by omega)
      refine ⟨j + 1, Space.put h (BRef.blk block) (a.set! j 0x55), ?_, rfl, by omega,
        ⟨a.set! j 0x55, by simp [Space.put], by simpa using hsz⟩, hro,
        by simpa [Space.put, upd_ne _ _ _ _ different] using hF⟩
      rw [bind_app, show store8 (.ref (BRef.blk block) j) 0x55 h = _ from hst]
      rfl)
    (fun j s h hj ⟨hs, _, _, _, _⟩ => by subst s; simp)
  refine ⟨fun h ⟨hb, hsz, hro, hF⟩ => ?_⟩
  exact hspec.entails_wp_of_post (fun j h ⟨rfl, _, ha, _, hF'⟩ => ⟨rfl, ha, hF'⟩) h
    ⟨rfl, Nat.zero_le _, ⟨a₀, hb, hsz⟩, hro, hF⟩

-- `store64_load64_spec`: storing and immediately loading a `UInt64` recovers `v` while framing `watched`.
example (b watched off : Nat) (a : Array UInt8) (v : UInt64) (different : watched ≠ b)
    (fit : off + 8 ≤ a.size) (F : Option (Array UInt8) → Prop) :
    ⦃ fun h => h.bytes b = some a ∧ h.ro b = false ∧ F (h.bytes watched) ⦄
      (do store64 (.ref (.blk b) off) v; load64 (.ref (.blk b) off))
    ⦃ fun out h => out = v ∧ h.bytes b = some (writeLE64 a off v) ∧ F (h.bytes watched) ⦄ :=
  store64_load64_spec b watched off a v F different fit
