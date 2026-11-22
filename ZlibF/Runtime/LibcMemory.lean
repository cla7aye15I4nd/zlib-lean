import ZlibF.Runtime.Ptr

namespace C

/-! ## `memcpy`, `memmove`, `memset` on arrays -/

/-- The value of an element of type `T` whose every byte is `c`: what `memset(p, c, n * sizeof(T))` stores in each
element. -/
class ByteRepeat (T : Type) where
  ofByte : UInt8 → T

instance : ByteRepeat UInt8 := ⟨id⟩
instance : ByteRepeat UInt16 := ⟨fun c => (c.toUInt16 <<< 8) ||| c.toUInt16⟩
instance : ByteRepeat UInt32 := ⟨fun c => let x := c.toUInt32; (x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x⟩
instance : ByteRepeat UInt64 :=
  ⟨fun c => let x := c.toUInt64; (x <<< 56) ||| (x <<< 48) ||| (x <<< 40) ||| (x <<< 32) ||| (x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x⟩
instance : ByteRepeat Int8 := ⟨UInt8.toInt8⟩
instance : ByteRepeat Int16 := ⟨fun c => ((c.toUInt16 <<< 8) ||| c.toUInt16).toInt16⟩
instance : ByteRepeat Int32 := ⟨fun c => let x := c.toUInt32; ((x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x).toInt32⟩
instance : ByteRepeat Int64 :=
  ⟨fun c => let x := c.toUInt64; ((x <<< 56) ||| (x <<< 48) ||| (x <<< 40) ||| (x <<< 32) ||| (x <<< 24) ||| (x <<< 16) ||| (x <<< 8) ||| x).toInt64⟩

section generic
variable {R T : Type} [Space Heap R T]

/-- `d` with `n` elements from `s` copied to it: element `doff + i` becomes element `soff + i` of `s`
(read before any write, so it is also the result of `memmove`). -/
def copyRange [Inhabited T] (d s : Array T) (doff soff n : Nat) : Array T :=
  (List.range n).foldl (fun a i => a.set! (doff + i) s[soff + i]!) d

/-- `d` with `n` elements from `off` on set to `v`. -/
def fillRange (d : Array T) (off n : Nat) (v : T) : Array T :=
  (List.range n).foldl (fun a i => a.set! (off + i) v) d

/-- `memcpy(dst, src, n)` for `n` elements. Faults if either pointer is null (even for `n = 0`) or dangling, if a
range leaves its array, if the destination is read-only and `n > 0`, or if the ranges overlap. -/
def Ptr.memcpy [DecidableEq R] [Inhabited T] (dst src : Ptr R) (n : Nat) : M Unit := fun h =>
  match dst, src with
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some da, some sa =>
      if Space.ro h rd && decide (n ≠ 0) then .error (.ub "memcpy into a read-only object")
      else if od + n ≤ da.size ∧ os + n ≤ sa.size then
        if rd ≠ rs ∨ od + n ≤ os ∨ os + n ≤ od then .ok ((), Space.modify h rd (fun da => copyRange da sa od os n))
        else .error (.ub "memcpy with overlapping ranges")
      else .error (.ub "memcpy outside its objects")
    | _, _ => .error (.ub "memcpy through a dangling pointer")
  | _, _ => .error (.ub "memcpy through a null pointer")

/-- `memmove(dst, src, n)` for `n` elements: as `memcpy`, and the ranges may overlap (a read-only destination is a
fault only when `n > 0`). -/
def Ptr.memmove [DecidableEq R] [Inhabited T] (dst src : Ptr R) (n : Nat) : M Unit := fun h =>
  match dst, src with
  | .ref rd od, .ref rs os =>
    match Space.get h rd, Space.get h rs with
    | some da, some sa =>
      if Space.ro h rd && decide (n ≠ 0) then .error (.ub "memmove into a read-only object")
      else if od + n ≤ da.size ∧ os + n ≤ sa.size then .ok ((), Space.modify h rd (fun da => copyRange da sa od os n))
      else .error (.ub "memmove outside its objects")
    | _, _ => .error (.ub "memmove through a dangling pointer")
  | _, _ => .error (.ub "memmove through a null pointer")

/-- Set `n` elements to the value `v`. This is `memset(dst, c, n * sizeof(T))` only for a byte array, and for any
element type when the value is zero (`zmemzero`). For a wider element type and another byte, use `Ptr.memset`, which
stores the element whose every byte is `c`. Faults if `dst` is null or dangling, the range leaves the array, or the
array is read-only and `n > 0`. -/
def Ptr.fill (dst : Ptr R) (v : T) (n : Nat) : M Unit := fun h =>
  match dst with
  | .ref r off =>
    match Space.get h r with
    | none => .error (.ub "memset through a dangling pointer")
    | some a =>
      if Space.ro h r && decide (n ≠ 0) then .error (.ub "memset of a read-only object")
      else if off + n ≤ a.size then .ok ((), Space.modify h r (fun a => fillRange a off n v))
      else .error (.ub "memset outside its object")
  | .null => .error (.ub "memset through a null pointer")

/-- `memset(dst, c, n * sizeof(T))`: `n` elements, each with every byte equal to `c`. For a byte array it is `Ptr.fill`
with `c`. The faults are those of `Ptr.fill`. -/
def Ptr.memset [ByteRepeat T] (dst : Ptr R) (c : UInt8) (n : Nat) : M Unit :=
  Ptr.fill dst (ByteRepeat.ofByte c) n

/-! ### Rules -/

theorem size_copyRange [Inhabited T] (d s : Array T) (doff soff n : Nat) :
    (copyRange d s doff soff n).size = d.size := by
  unfold copyRange
  suffices ∀ (l : List Nat) (a : Array T), (l.foldl (fun a i => a.set! (doff + i) s[soff + i]!) a).size = a.size by
    exact this _ _
  intro l
  induction l with
  | nil => intro a; rfl
  | cons i l ih => intro a; simp only [List.foldl]; rw [ih]; simp

theorem size_fillRange (d : Array T) (off n : Nat) (v : T) : (fillRange d off n v).size = d.size := by
  unfold fillRange
  suffices ∀ (l : List Nat) (a : Array T), (l.foldl (fun a i => a.set! (off + i) v) a).size = a.size by
    exact this _ _
  intro l
  induction l with
  | nil => intro a; rfl
  | cons i l ih => intro a; simp only [List.foldl]; rw [ih]; simp

theorem Ptr.memcpy_ok [DecidableEq R] [Inhabited T] {h : Heap} {rd rs : R} {od os n : Nat} {da sa : Array T}
    (hd : Space.get h rd = some da) (hs : Space.get h rs = some sa) (hro : Space.ro h rd = false)
    (h1 : od + n ≤ da.size) (h2 : os + n ≤ sa.size) (hdis : rd ≠ rs ∨ od + n ≤ os ∨ os + n ≤ od) :
    Ptr.memcpy (Ptr.ref rd od) (Ptr.ref rs os) n h = .ok ((), Space.put h rd (copyRange da sa od os n)) := by
  simp [Ptr.memcpy, hd, hs, hro, h1, h2, hdis, Space.modify_eq _ _ _ _ hd]

theorem Ptr.memmove_ok [DecidableEq R] [Inhabited T] {h : Heap} {rd rs : R} {od os n : Nat} {da sa : Array T}
    (hd : Space.get h rd = some da) (hs : Space.get h rs = some sa) (hro : Space.ro h rd = false)
    (h1 : od + n ≤ da.size) (h2 : os + n ≤ sa.size) :
    Ptr.memmove (Ptr.ref rd od) (Ptr.ref rs os) n h = .ok ((), Space.put h rd (copyRange da sa od os n)) := by
  simp [Ptr.memmove, hd, hs, hro, h1, h2, Space.modify_eq _ _ _ _ hd]

theorem Ptr.fill_ok {h : Heap} {r : R} {a : Array T} {off n : Nat} {v : T}
    (hg : Space.get h r = some a) (hro : Space.ro h r = false) (h1 : off + n ≤ a.size) :
    Ptr.fill (Ptr.ref r off) v n h = .ok ((), Space.put h r (fillRange a off n v)) := by
  simp [Ptr.fill, hg, hro, h1, Space.modify_eq _ _ _ _ hg]

end generic

/-- `memcpy(dst, src, n)` for byte pointers (`zmemcpy`). -/
abbrev memcpyB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memcpy dst src n
/-- `memmove(dst, src, n)` for byte pointers. -/
abbrev memmoveB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memmove dst src n
/-- `memset(dst, c, n)` for a byte pointer. -/
abbrev memsetB (dst : BPtr) (c : UInt8) (n : Nat) : M Unit := Ptr.fill dst c n

/-- `memcpy` between two different byte blocks, both writable-or-readable as needed: the destination block `nb` is
writable, the ranges are inside the blocks. The result is the heap with the block `nb` replaced. -/
theorem memcpyB_blk_ok {h : Heap} {nb no pb po n : Nat} {ob pbuf : Array UInt8}
    (e1 : h.bytes nb = some ob) (e2 : h.bytes pb = some pbuf) (hro : h.ro nb = false) (hne : nb ≠ pb)
    (h1 : no + n ≤ ob.size) (h2 : po + n ≤ pbuf.size) :
    memcpyB (.ref (.blk nb) no) (.ref (.blk pb) po) n h =
      .ok ((), { h with bytes := upd h.bytes nb (some (copyRange ob pbuf no po n)) }) :=
  Ptr.memcpy_ok (rd := BRef.blk nb) (rs := BRef.blk pb) e1 e2 hro h1 h2 (Or.inl (fun hh => hne (BRef.blk.inj hh)))

end C
