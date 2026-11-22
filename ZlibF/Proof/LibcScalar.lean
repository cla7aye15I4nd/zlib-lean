import ZlibF.Proof.HeapWP
import ZlibF.Runtime.CAbi
import Std.Tactic.BVDecide

/-!
# Little-endian 32-bit and 64-bit scalar memory contracts

`Std.WP` Hoare triples and byte-slice frame theorems for `C.load32`, `C.store32`,
`C.load64`, and `C.store64`, together with bit-vector verified roundtrip identities.
-/

namespace C
open Std.WP
open scoped HeapWP

/-- Assemble four little-endian bytes into a 32-bit signed integer (matching `C.load32`). -/
def packLE32 (b0 b1 b2 b3 : UInt8) : Int32 :=
  (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toInt32

/-- Assemble eight little-endian bytes into a 64-bit unsigned integer (matching `C.load64`). -/
def packLE64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
  (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)

/-- Writing `v : Int32` as four little-endian bytes and reassembling yields `v`. -/
theorem pack32_unpack32 (v : Int32) :
    let u := v.toUInt32
    packLE32 u.toUInt8 (u >>> 8).toUInt8 (u >>> 16).toUInt8 (u >>> 24).toUInt8 = v := by
  dsimp [packLE32]
  apply Int32.toBitVec.inj
  bv_decide

/-- Writing `v : UInt64` as eight little-endian bytes and reassembling yields `v`. -/
theorem pack64_unpack64 (v : UInt64) :
    packLE64 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      (v >>> 32).toUInt8 (v >>> 40).toUInt8 (v >>> 48).toUInt8 (v >>> 56).toUInt8 = v := by
  dsimp [packLE64]
  bv_decide

/-- Array updated with four little-endian bytes of `v : Int32` at `off`. -/
def writeLE32 (a : Array UInt8) (off : Nat) (v : Int32) : Array UInt8 :=
  let u := v.toUInt32
  (((a.set! off u.toUInt8).set! (off + 1) (u >>> 8).toUInt8).set!
    (off + 2) (u >>> 16).toUInt8).set! (off + 3) (u >>> 24).toUInt8

/-- Array updated with eight little-endian bytes of `v : UInt64` at `off`. -/
def writeLE64 (a : Array UInt8) (off : Nat) (v : UInt64) : Array UInt8 :=
  (((((((a.set! off v.toUInt8).set! (off + 1) (v >>> 8).toUInt8).set!
    (off + 2) (v >>> 16).toUInt8).set! (off + 3) (v >>> 24).toUInt8).set!
    (off + 4) (v >>> 32).toUInt8).set! (off + 5) (v >>> 40).toUInt8).set!
    (off + 6) (v >>> 48).toUInt8).set! (off + 7) (v >>> 56).toUInt8

theorem size_writeLE32 (a : Array UInt8) (off : Nat) (v : Int32) :
    (writeLE32 a off v).size = a.size := by
  simp [writeLE32]

theorem size_writeLE64 (a : Array UInt8) (off : Nat) (v : UInt64) :
    (writeLE64 a off v).size = a.size := by
  simp [writeLE64]

private theorem set_getElem?_eq (a : Array UInt8) (idx i : Nat) (x : UInt8) (h : idx < a.size) :
    (a.set! idx x)[i]? = if i = idx then some x else a[i]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hi : idx = i
  · subst hi; simp [h]
  · have hi' : i ≠ idx := fun e => hi e.symm
    simp [hi, hi']

theorem writeLE32_getElem? (a : Array UInt8) (off : Nat) (v : Int32) (fit : off + 4 ≤ a.size)
    (i : Nat) (out : i < off ∨ off + 4 ≤ i) :
    (writeLE32 a off v)[i]? = a[i]? := by
  unfold writeLE32
  have s0 : off < a.size := by omega
  have s1 : off + 1 < (a.set! off v.toUInt32.toUInt8).size := by simp; omega
  have s2 : off + 2 < ((a.set! off v.toUInt32.toUInt8).set! (off + 1) (v.toUInt32 >>> 8).toUInt8).size := by
    simp; omega
  have s3 : off + 3 < (((a.set! off v.toUInt32.toUInt8).set! (off + 1) (v.toUInt32 >>> 8).toUInt8).set!
      (off + 2) (v.toUInt32 >>> 16).toUInt8).size := by simp; omega
  rw [set_getElem?_eq _ (off + 3) i _ s3, set_getElem?_eq _ (off + 2) i _ s2,
      set_getElem?_eq _ (off + 1) i _ s1, set_getElem?_eq _ off i _ s0]
  have n0 : i ≠ off := by omega
  have n1 : i ≠ off + 1 := by omega
  have n2 : i ≠ off + 2 := by omega
  have n3 : i ≠ off + 3 := by omega
  simp [n0, n1, n2, n3]

theorem writeLE64_getElem? (a : Array UInt8) (off : Nat) (v : UInt64) (fit : off + 8 ≤ a.size)
    (i : Nat) (out : i < off ∨ off + 8 ≤ i) :
    (writeLE64 a off v)[i]? = a[i]? := by
  unfold writeLE64
  rw [set_getElem?_eq _ (off + 7) i _ (by simp; omega),
      set_getElem?_eq _ (off + 6) i _ (by simp; omega),
      set_getElem?_eq _ (off + 5) i _ (by simp; omega),
      set_getElem?_eq _ (off + 4) i _ (by simp; omega),
      set_getElem?_eq _ (off + 3) i _ (by simp; omega),
      set_getElem?_eq _ (off + 2) i _ (by simp; omega),
      set_getElem?_eq _ (off + 1) i _ (by simp; omega),
      set_getElem?_eq _ off i _ (by omega)]
  have n0 : i ≠ off := by omega
  have n1 : i ≠ off + 1 := by omega
  have n2 : i ≠ off + 2 := by omega
  have n3 : i ≠ off + 3 := by omega
  have n4 : i ≠ off + 4 := by omega
  have n5 : i ≠ off + 5 := by omega
  have n6 : i ≠ off + 6 := by omega
  have n7 : i ≠ off + 7 := by omega
  simp [n0, n1, n2, n3, n4, n5, n6, n7]

theorem load32_ok {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (hg : Space.get h r = some a) (fit : off + 4 ≤ a.size) :
    OkOn h (load32 (.ref r off)) (packLE32 a[off] a[off + 1] a[off + 2] a[off + 3]) := by
  unfold load32
  have i0 : OkOn h (index8 (.ref r off) 0) a[off] := by
    simpa using Ptr.index_ok (h := h) (r := r) (a := a) (off := off) (i := 0) hg (by omega)
  have i1 : OkOn h (index8 (.ref r off) 1) a[off + 1] :=
    Ptr.index_ok (h := h) (r := r) (a := a) (off := off) (i := 1) hg (by omega)
  have i2 : OkOn h (index8 (.ref r off) 2) a[off + 2] :=
    Ptr.index_ok (h := h) (r := r) (a := a) (off := off) (i := 2) hg (by omega)
  have i3 : OkOn h (index8 (.ref r off) 3) a[off + 3] :=
    Ptr.index_ok (h := h) (r := r) (a := a) (off := off) (i := 3) hg (by omega)
  exact OkOn.bind i0 (OkOn.bind i1 (OkOn.bind i2 (OkOn.bind i3 (OkOn.pure h _))))

/-- `C.load32` reads 4 little-endian bytes while preserving arbitrary heap predicates. -/
theorem load32_spec (r : BRef) (off : Nat) (a : Array UInt8) (F : Heap → Prop) :
    ⦃ fun h => (Space.get h r = some a ∧ off + 4 ≤ a.size) ∧ F h ⦄
      load32 (.ref r off)
    ⦃ fun v h => v = packLE32 a[off]! a[off + 1]! a[off + 2]! a[off + 3]! ∧ F h ⦄ := by
  apply OkOn.frame
  intro h ⟨hg, fit⟩
  have h0 : a[off] = a[off]! := (getElem!_pos a off (by omega)).symm
  have h1 : a[off + 1] = a[off + 1]! := (getElem!_pos a (off + 1) (by omega)).symm
  have h2 : a[off + 2] = a[off + 2]! := (getElem!_pos a (off + 2) (by omega)).symm
  have h3 : a[off + 3] = a[off + 3]! := (getElem!_pos a (off + 3) (by omega)).symm
  simpa only [h0, h1, h2, h3] using load32_ok hg fit

theorem load64_ok {h : Heap} {r : BRef} {a : Array UInt8} {off : Nat}
    (hg : Space.get h r = some a) (fit : off + 8 ≤ a.size) :
    OkOn h (load64 (.ref r off))
      (packLE64 a[off] a[off + 1] a[off + 2] a[off + 3]
        a[off + 4] a[off + 5] a[off + 6] a[off + 7]) := by
  have idx : ∀ (k : Nat) (hk : k < 8),
      index8 (.ref r off) (k : Int) h = .ok (a[off + k]'(by omega), h) :=
    fun k hk => Ptr.index_ok (h := h) (r := r) (a := a) (off := off) (i := k) hg (by omega)
  have s0 := idx 0 (by omega); have s1 := idx 1 (by omega); have s2 := idx 2 (by omega)
  have s3 := idx 3 (by omega); have s4 := idx 4 (by omega); have s5 := idx 5 (by omega)
  have s6 := idx 6 (by omega); have s7 := idx 7 (by omega)
  unfold OkOn load64
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  rw [show List.range' 0 ((8 - 0 + 1 - 1) / 1) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.forIn'_cons, List.forIn'_nil, bind_app, pure_app, s0, s1, s2, s3, s4, s5, s6, s7]
  dsimp [packLE64]
  simp only [show (8 * 0 : Nat).toUInt64 = 0 by decide, UInt64.zero_or,
    UInt64.shiftLeft_zero,
    show (8 * 1 : Nat).toUInt64 = 8 by decide,
    show (8 * 2 : Nat).toUInt64 = 16 by decide,
    show (8 * 3 : Nat).toUInt64 = 24 by decide,
    show (8 * 4 : Nat).toUInt64 = 32 by decide,
    show (8 * 5 : Nat).toUInt64 = 40 by decide,
    show (8 * 6 : Nat).toUInt64 = 48 by decide,
    show (8 * 7 : Nat).toUInt64 = 56 by decide]

/-- `C.load64` reads 8 little-endian bytes while preserving arbitrary heap predicates. -/
theorem load64_spec (r : BRef) (off : Nat) (a : Array UInt8) (F : Heap → Prop) :
    ⦃ fun h => (Space.get h r = some a ∧ off + 8 ≤ a.size) ∧ F h ⦄
      load64 (.ref r off)
    ⦃ fun v h => v = packLE64 a[off]! a[off + 1]! a[off + 2]! a[off + 3]!
        a[off + 4]! a[off + 5]! a[off + 6]! a[off + 7]! ∧ F h ⦄ := by
  apply OkOn.frame
  intro h ⟨hg, fit⟩
  have h0 : a[off] = a[off]! := (getElem!_pos a off (by omega)).symm
  have h1 : a[off + 1] = a[off + 1]! := (getElem!_pos a (off + 1) (by omega)).symm
  have h2 : a[off + 2] = a[off + 2]! := (getElem!_pos a (off + 2) (by omega)).symm
  have h3 : a[off + 3] = a[off + 3]! := (getElem!_pos a (off + 3) (by omega)).symm
  have h4 : a[off + 4] = a[off + 4]! := (getElem!_pos a (off + 4) (by omega)).symm
  have h5 : a[off + 5] = a[off + 5]! := (getElem!_pos a (off + 5) (by omega)).symm
  have h6 : a[off + 6] = a[off + 6]! := (getElem!_pos a (off + 6) (by omega)).symm
  have h7 : a[off + 7] = a[off + 7]! := (getElem!_pos a (off + 7) (by omega)).symm
  simpa only [h0, h1, h2, h3, h4, h5, h6, h7] using load64_ok hg fit

private theorem add_at_blk {h : Heap} {b : Nat} {arr : Array UInt8} {off k : Nat}
    (hk : off + k ≤ arr.size) :
    Ptr.add (.ref (BRef.blk b) off) (k : Int) { h with bytes := upd h.bytes b (some arr) } =
      .ok (.ref (BRef.blk b) (off + k), { h with bytes := upd h.bytes b (some arr) }) :=
  Ptr.add_nat_ok (h := { h with bytes := upd h.bytes b (some arr) })
    (r := BRef.blk b) (a := arr) (off := off) (n := k) (by simp) hk

private theorem store_at_blk {h : Heap} {b : Nat} {arr : Array UInt8} {j : Nat} {x : UInt8}
    (hro : h.ro b = false) (hj : j < arr.size) :
    store8 (.ref (BRef.blk b) j) x { h with bytes := upd h.bytes b (some arr) } =
      .ok ((), { h with bytes := upd h.bytes b (some (arr.set! j x)) }) := by
  have st := Ptr.store_ok (h := { h with bytes := upd h.bytes b (some arr) })
    (r := BRef.blk b) (off := j) (v := x) (a := arr) (by simp) hro hj
  simpa [store8, Space.put, upd_upd] using st

theorem store32_ok {h : Heap} {b : Nat} {a : Array UInt8} {off : Nat} {v : Int32}
    (hb : h.bytes b = some a) (hro : h.ro b = false) (fit : off + 4 ≤ a.size) :
    store32 (.ref (.blk b) off) v h =
      .ok ((), { h with bytes := upd h.bytes b (some (writeLE32 a off v)) }) := by
  have hput : { h with bytes := upd h.bytes b (some a) } = h := by
    cases h; simp only [Heap.mk.injEq, and_true]; exact upd_self _ _ _ hb
  suffices store32 (.ref (.blk b) off) v { h with bytes := upd h.bytes b (some a) } =
      .ok ((), { h with bytes := upd h.bytes b (some (writeLE32 a off v)) }) by
    simpa only [hput] using this
  unfold store32
  simp only [bind_app]
  rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, add_at_blk (by omega)]
  simp only [Nat.add_zero]
  rw [store_at_blk hro (by omega)]
  simp only []
  rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, add_at_blk (by simp; omega)]
  simp only []
  rw [store_at_blk hro (by simp; omega)]
  simp only []
  rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, add_at_blk (by simp; omega)]
  simp only []
  rw [store_at_blk hro (by simp; omega)]
  simp only []
  rw [show (3 : Int) = ((3 : Nat) : Int) from rfl, add_at_blk (by simp; omega)]
  simp only []
  rw [store_at_blk hro (by simp; omega)]
  rfl

/-- `C.store32` updates four little-endian bytes, frames `F (h.bytes watched)`, and preserves
all untouched indices outside `[off, off + 4)`. -/
theorem store32_frame (b watched off : Nat) (a : Array UInt8) (v : Int32)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ b) (fit : off + 4 ≤ a.size) :
    ⦃ fun h => h.bytes b = some a ∧ h.ro b = false ∧ F (h.bytes watched) ⦄
      store32 (.ref (.blk b) off) v
    ⦃ fun _ h => h.bytes b = some (writeLE32 a off v) ∧ F (h.bytes watched) ∧
        ∀ i, i < off ∨ off + 4 ≤ i → (h.bytes b).bind (·[i]?) = a[i]? ⦄ := by
  refine ⟨fun h ⟨hb, hro, frame⟩ => ?_⟩
  rw [wp_run, store32_ok hb hro fit]
  refine ⟨by simp, by simpa [upd_ne _ _ _ _ outside] using frame, fun i hi => ?_⟩
  simp [writeLE32_getElem? a off v fit i hi]

theorem store64_ok {h : Heap} {b : Nat} {a : Array UInt8} {off : Nat} {v : UInt64}
    (hb : h.bytes b = some a) (hro : h.ro b = false) (fit : off + 8 ≤ a.size) :
    store64 (.ref (.blk b) off) v h =
      .ok ((), { h with bytes := upd h.bytes b (some (writeLE64 a off v)) }) := by
  have hput : { h with bytes := upd h.bytes b (some a) } = h := by
    cases h; simp only [Heap.mk.injEq, and_true]; exact upd_self _ _ _ hb
  suffices store64 (.ref (.blk b) off) v { h with bytes := upd h.bytes b (some a) } =
      .ok ((), { h with bytes := upd h.bytes b (some (writeLE64 a off v)) }) by
    simpa only [hput] using this
  unfold store64
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  rw [show List.range' 0 ((8 - 0 + 1 - 1) / 1) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.forIn'_cons, List.forIn'_nil, bind_app, pure_app]
  rw [add_at_blk (by omega)]; simp only [Nat.add_zero]
  rw [store_at_blk hro (by omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]; simp only [bind_app, pure_app]
  rw [add_at_blk (by simp; omega)]; simp only []
  rw [store_at_blk hro (by simp; omega)]
  simp [writeLE64]

/-- `C.store64` updates eight little-endian bytes, frames `F (h.bytes watched)`, and preserves
all untouched indices outside `[off, off + 8)`. -/
theorem store64_frame (b watched off : Nat) (a : Array UInt8) (v : UInt64)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ b) (fit : off + 8 ≤ a.size) :
    ⦃ fun h => h.bytes b = some a ∧ h.ro b = false ∧ F (h.bytes watched) ⦄
      store64 (.ref (.blk b) off) v
    ⦃ fun _ h => h.bytes b = some (writeLE64 a off v) ∧ F (h.bytes watched) ∧
        ∀ i, i < off ∨ off + 8 ≤ i → (h.bytes b).bind (·[i]?) = a[i]? ⦄ := by
  refine ⟨fun h ⟨hb, hro, frame⟩ => ?_⟩
  rw [wp_run, store64_ok hb hro fit]
  refine ⟨by simp, by simpa [upd_ne _ _ _ _ outside] using frame, fun i hi => ?_⟩
  simp [writeLE64_getElem? a off v fit i hi]

private theorem getElem_eq_of_getElem?_some (a : Array UInt8) (i : Nat) (x : UInt8)
    (hi : i < a.size) (h : a[i]? = some x) : a[i] = x := by
  rw [Array.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

private theorem writeLE32_bytes (a : Array UInt8) (off : Nat) (v : Int32) (fit : off + 4 ≤ a.size) :
    let u := v.toUInt32
    let a' := writeLE32 a off v
    have hsz : a'.size = a.size := size_writeLE32 a off v
    a'[off]'(by omega) = u.toUInt8 ∧
    a'[off + 1]'(by omega) = (u >>> 8).toUInt8 ∧
    a'[off + 2]'(by omega) = (u >>> 16).toUInt8 ∧
    a'[off + 3]'(by omega) = (u >>> 24).toUInt8 := by
  dsimp only
  have hsz : (writeLE32 a off v).size = a.size := size_writeLE32 a off v
  have r0 : (writeLE32 a off v)[off]? = some v.toUInt32.toUInt8 := by
    unfold writeLE32
    rw [set_getElem?_eq _ (off + 3) off _ (by simp; omega),
        set_getElem?_eq _ (off + 2) off _ (by simp; omega),
        set_getElem?_eq _ (off + 1) off _ (by simp; omega),
        set_getElem?_eq _ off off _ (by omega)]
    simp
  have r1 : (writeLE32 a off v)[off + 1]? = some (v.toUInt32 >>> 8).toUInt8 := by
    unfold writeLE32
    rw [set_getElem?_eq _ (off + 3) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 2) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 1) (off + 1) _ (by simp; omega)]
    simp
  have r2 : (writeLE32 a off v)[off + 2]? = some (v.toUInt32 >>> 16).toUInt8 := by
    unfold writeLE32
    rw [set_getElem?_eq _ (off + 3) (off + 2) _ (by simp; omega),
        set_getElem?_eq _ (off + 2) (off + 2) _ (by simp; omega)]
    simp
  have r3 : (writeLE32 a off v)[off + 3]? = some (v.toUInt32 >>> 24).toUInt8 := by
    unfold writeLE32
    rw [set_getElem?_eq _ (off + 3) (off + 3) _ (by simp; omega)]
    simp
  exact ⟨getElem_eq_of_getElem?_some _ off _ (by omega) r0,
         getElem_eq_of_getElem?_some _ (off + 1) _ (by omega) r1,
         getElem_eq_of_getElem?_some _ (off + 2) _ (by omega) r2,
         getElem_eq_of_getElem?_some _ (off + 3) _ (by omega) r3⟩

private theorem writeLE64_bytes (a : Array UInt8) (off : Nat) (v : UInt64) (fit : off + 8 ≤ a.size) :
    let a' := writeLE64 a off v
    have hsz : a'.size = a.size := size_writeLE64 a off v
    a'[off]'(by omega) = v.toUInt8 ∧
    a'[off + 1]'(by omega) = (v >>> 8).toUInt8 ∧
    a'[off + 2]'(by omega) = (v >>> 16).toUInt8 ∧
    a'[off + 3]'(by omega) = (v >>> 24).toUInt8 ∧
    a'[off + 4]'(by omega) = (v >>> 32).toUInt8 ∧
    a'[off + 5]'(by omega) = (v >>> 40).toUInt8 ∧
    a'[off + 6]'(by omega) = (v >>> 48).toUInt8 ∧
    a'[off + 7]'(by omega) = (v >>> 56).toUInt8 := by
  dsimp only
  have hsz : (writeLE64 a off v).size = a.size := size_writeLE64 a off v
  have r0 : (writeLE64 a off v)[off]? = some v.toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) off _ (by simp; omega),
        set_getElem?_eq _ (off + 6) off _ (by simp; omega),
        set_getElem?_eq _ (off + 5) off _ (by simp; omega),
        set_getElem?_eq _ (off + 4) off _ (by simp; omega),
        set_getElem?_eq _ (off + 3) off _ (by simp; omega),
        set_getElem?_eq _ (off + 2) off _ (by simp; omega),
        set_getElem?_eq _ (off + 1) off _ (by simp; omega),
        set_getElem?_eq _ off off _ (by omega)]
    simp
  have r1 : (writeLE64 a off v)[off + 1]? = some (v >>> 8).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 6) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 5) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 4) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 3) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 2) (off + 1) _ (by simp; omega),
        set_getElem?_eq _ (off + 1) (off + 1) _ (by simp; omega)]
    simp
  have r2 : (writeLE64 a off v)[off + 2]? = some (v >>> 16).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 2) _ (by simp; omega),
        set_getElem?_eq _ (off + 6) (off + 2) _ (by simp; omega),
        set_getElem?_eq _ (off + 5) (off + 2) _ (by simp; omega),
        set_getElem?_eq _ (off + 4) (off + 2) _ (by simp; omega),
        set_getElem?_eq _ (off + 3) (off + 2) _ (by simp; omega),
        set_getElem?_eq _ (off + 2) (off + 2) _ (by simp; omega)]
    simp
  have r3 : (writeLE64 a off v)[off + 3]? = some (v >>> 24).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 3) _ (by simp; omega),
        set_getElem?_eq _ (off + 6) (off + 3) _ (by simp; omega),
        set_getElem?_eq _ (off + 5) (off + 3) _ (by simp; omega),
        set_getElem?_eq _ (off + 4) (off + 3) _ (by simp; omega),
        set_getElem?_eq _ (off + 3) (off + 3) _ (by simp; omega)]
    simp
  have r4 : (writeLE64 a off v)[off + 4]? = some (v >>> 32).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 4) _ (by simp; omega),
        set_getElem?_eq _ (off + 6) (off + 4) _ (by simp; omega),
        set_getElem?_eq _ (off + 5) (off + 4) _ (by simp; omega),
        set_getElem?_eq _ (off + 4) (off + 4) _ (by simp; omega)]
    simp
  have r5 : (writeLE64 a off v)[off + 5]? = some (v >>> 40).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 5) _ (by simp; omega),
        set_getElem?_eq _ (off + 6) (off + 5) _ (by simp; omega),
        set_getElem?_eq _ (off + 5) (off + 5) _ (by simp; omega)]
    simp
  have r6 : (writeLE64 a off v)[off + 6]? = some (v >>> 48).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 6) _ (by simp; omega),
        set_getElem?_eq _ (off + 6) (off + 6) _ (by simp; omega)]
    simp
  have r7 : (writeLE64 a off v)[off + 7]? = some (v >>> 56).toUInt8 := by
    unfold writeLE64
    rw [set_getElem?_eq _ (off + 7) (off + 7) _ (by simp; omega)]
    simp
  exact ⟨getElem_eq_of_getElem?_some _ off _ (by omega) r0,
         getElem_eq_of_getElem?_some _ (off + 1) _ (by omega) r1,
         getElem_eq_of_getElem?_some _ (off + 2) _ (by omega) r2,
         getElem_eq_of_getElem?_some _ (off + 3) _ (by omega) r3,
         getElem_eq_of_getElem?_some _ (off + 4) _ (by omega) r4,
         getElem_eq_of_getElem?_some _ (off + 5) _ (by omega) r5,
         getElem_eq_of_getElem?_some _ (off + 6) _ (by omega) r6,
         getElem_eq_of_getElem?_some _ (off + 7) _ (by omega) r7⟩

/-- Storing a 32-bit signed integer and immediately reading it back yields the exact value `v`
while preserving `F (h.bytes watched)`. -/
theorem store32_load32_spec (b watched off : Nat) (a : Array UInt8) (v : Int32)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ b) (fit : off + 4 ≤ a.size) :
    ⦃ fun h => h.bytes b = some a ∧ h.ro b = false ∧ F (h.bytes watched) ⦄
      (do store32 (.ref (.blk b) off) v; load32 (.ref (.blk b) off))
    ⦃ fun out h => out = v ∧ h.bytes b = some (writeLE32 a off v) ∧ F (h.bytes watched) ⦄ := by
  refine ⟨fun h ⟨hb, hro, frame⟩ => ?_⟩
  have hst := store32_ok (v := v) hb hro fit
  let a' := writeLE32 a off v
  let h' := { h with bytes := upd h.bytes b (some a') }
  have hb' : Space.get h' (BRef.blk b) = some a' := by simp [h', Space.get]
  have hsz' : a'.size = a.size := size_writeLE32 a off v
  have hld := load32_ok (off := off) hb' (by omega)
  have hrun : (do store32 (.ref (.blk b) off) v; load32 (.ref (.blk b) off)) h =
      .ok (packLE32 (a'[off]'(by omega)) (a'[off + 1]'(by omega))
        (a'[off + 2]'(by omega)) (a'[off + 3]'(by omega)), h') := by
    rw [bind_app, hst]
    exact hld
  rw [wp_run, hrun]
  obtain ⟨e0, e1, e2, e3⟩ := writeLE32_bytes a off v fit
  refine ⟨?_, by simp [h', a'], by simpa [h', upd_ne _ _ _ _ outside] using frame⟩
  dsimp only [a'] at e0 e1 e2 e3 ⊢
  rw [e0, e1, e2, e3]
  exact pack32_unpack32 v

/-- Storing a 64-bit unsigned integer and immediately reading it back yields the exact value `v`
while preserving `F (h.bytes watched)`. -/
theorem store64_load64_spec (b watched off : Nat) (a : Array UInt8) (v : UInt64)
    (F : Option (Array UInt8) → Prop) (outside : watched ≠ b) (fit : off + 8 ≤ a.size) :
    ⦃ fun h => h.bytes b = some a ∧ h.ro b = false ∧ F (h.bytes watched) ⦄
      (do store64 (.ref (.blk b) off) v; load64 (.ref (.blk b) off))
    ⦃ fun out h => out = v ∧ h.bytes b = some (writeLE64 a off v) ∧ F (h.bytes watched) ⦄ := by
  refine ⟨fun h ⟨hb, hro, frame⟩ => ?_⟩
  have hst := store64_ok (v := v) hb hro fit
  let a' := writeLE64 a off v
  let h' := { h with bytes := upd h.bytes b (some a') }
  have hb' : Space.get h' (BRef.blk b) = some a' := by simp [h', Space.get]
  have hsz' : a'.size = a.size := size_writeLE64 a off v
  have hld := load64_ok (off := off) hb' (by omega)
  have hrun : (do store64 (.ref (.blk b) off) v; load64 (.ref (.blk b) off)) h =
      .ok (packLE64 (a'[off]'(by omega)) (a'[off + 1]'(by omega))
        (a'[off + 2]'(by omega)) (a'[off + 3]'(by omega))
        (a'[off + 4]'(by omega)) (a'[off + 5]'(by omega))
        (a'[off + 6]'(by omega)) (a'[off + 7]'(by omega)), h') := by
    rw [bind_app, hst]
    exact hld
  rw [wp_run, hrun]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := writeLE64_bytes a off v fit
  refine ⟨?_, by simp [h', a'], by simpa [h', upd_ne _ _ _ _ outside] using frame⟩
  dsimp only [a'] at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  exact pack64_unpack64 v

end C