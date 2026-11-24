import ZlibF.Proof.«inflate.c.copy-dynamic-window»
import ZlibF.Proof.«inflate.c.copy-fixed-window»
import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.HeapWP

/-!
# Baseline lemma and runtime equivalence checks against commit `85cd20c`

Provides machine-checked kernel equivalence between:
1. The pre-split `ZlibF/Runtime/Libc.lean` operations at commit `85cd20c` and the
   post-split `C.*` operations (`LibcMemory.lean`, `LibcCString.lean`, `LibcAllocation.lean`).
2. The verbatim `85cd20c` theorem statements of refactored `inflateCopy` window lemmas and
   `crc32` bit-vector / polynomial lemmas and their current refactored proofs.
3. The `OkOn` specification form and `Std.Do.Triple` (`WP`) form via `C.okOn_iff_triple`.
-/

namespace Baseline85cd20c
open C

section RuntimeLibcSplit

section generic
variable {R T : Type} [Space Heap R T]

/-- Verbatim `85cd20c` `Libc.copyRange`. -/
def copyRange [Inhabited T] (d s : Array T) (doff soff n : Nat) : Array T :=
  (List.range n).foldl (fun a i => a.set! (doff + i) s[soff + i]!) d

/-- Verbatim `85cd20c` `Libc.fillRange`. -/
def fillRange (d : Array T) (off n : Nat) (v : T) : Array T :=
  (List.range n).foldl (fun a i => a.set! (off + i) v) d

/-- Verbatim `85cd20c` `Libc.Ptr.memcpy`. -/
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

/-- Verbatim `85cd20c` `Libc.Ptr.memmove`. -/
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

/-- Verbatim `85cd20c` `Libc.Ptr.fill`. -/
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

theorem copyRange_eq [Inhabited T] (d s : Array T) (doff soff n : Nat) :
    copyRange d s doff soff n = C.copyRange d s doff soff n := rfl

theorem fillRange_eq (d : Array T) (off n : Nat) (v : T) :
    fillRange d off n v = C.fillRange d off n v := rfl

theorem Ptr.memcpy_eq [DecidableEq R] [Inhabited T] (dst src : Ptr R) (n : Nat) :
    Ptr.memcpy dst src n = C.Ptr.memcpy dst src n := rfl

theorem Ptr.memmove_eq [DecidableEq R] [Inhabited T] (dst src : Ptr R) (n : Nat) :
    Ptr.memmove dst src n = C.Ptr.memmove dst src n := rfl

theorem Ptr.fill_eq (dst : Ptr R) (v : T) (n : Nat) :
    Ptr.fill dst v n = C.Ptr.fill dst v n := rfl

end generic

/-- Verbatim `85cd20c` `Libc.memcpyB`. -/
abbrev memcpyB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memcpy dst src n
/-- Verbatim `85cd20c` `Libc.memmoveB`. -/
abbrev memmoveB (dst src : BPtr) (n : Nat) : M Unit := Ptr.memmove dst src n
/-- Verbatim `85cd20c` `Libc.memsetB`. -/
abbrev memsetB (dst : BPtr) (c : UInt8) (n : Nat) : M Unit := Ptr.fill dst c n

theorem memcpyB_eq (dst src : BPtr) (n : Nat) : memcpyB dst src n = C.memcpyB dst src n := rfl
theorem memmoveB_eq (dst src : BPtr) (n : Nat) : memmoveB dst src n = C.memmoveB dst src n := rfl
theorem memsetB_eq (dst : BPtr) (c : UInt8) (n : Nat) : memsetB dst c n = C.memsetB dst c n := rfl

/-- Verbatim `85cd20c` `Libc.strlenFrom`. -/
def strlenFrom (a : Array UInt8) (i : Nat) : Option Nat :=
  if h : i < a.size then (if a[i] == 0 then some i else strlenFrom a (i + 1)) else none
termination_by a.size - i

/-- Verbatim `85cd20c` `Libc.strlenB`. -/
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

theorem strlenFrom_eq (a : Array UInt8) (i : Nat) :
    strlenFrom a i = C.strlenFrom a i := by
  have key : ∀ k i, a.size - i = k → strlenFrom a i = C.strlenFrom a i := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro i hk
      unfold strlenFrom C.strlenFrom
      split
      · rename_i hlt
        split
        · rfl
        · exact ih (a.size - (i + 1)) (by omega) (i + 1) rfl
      · rfl
  exact key (a.size - i) i rfl

theorem strlenB_eq (p : BPtr) : strlenB p = C.strlenB p := by
  funext h
  cases p with
  | null => rfl
  | ref r off =>
    dsimp [strlenB, C.strlenB]
    cases Space.get h r with
    | none => rfl
    | some a => dsimp only; rw [strlenFrom_eq a off]; rfl

/-- Verbatim `85cd20c` `Libc.mallocLimit`. -/
def mallocLimit : Nat := 2 ^ 63

/-- Verbatim `85cd20c` `Libc.allocB`. -/
def allocB (n : Nat) : M BPtr := fun h =>
  if h.allocOk h.nalloc = true ∧ n < mallocLimit then
    if h.slotUsed h.nextBlk then .error (.ub "allocation: the block number is in use (the heap is not Fresh)")
    else
      .ok (.ref (.blk h.nextBlk) 0,
        { h with bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
                 ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 })
  else .ok (.null, { h with nalloc := h.nalloc + 1 })

/-- Verbatim `85cd20c` `Libc.freeB`. -/
def freeB (p : BPtr) : M Unit := fun h =>
  match p with
  | .null => .ok ((), h)
  | .ref (.blk b) 0 =>
    match h.bytes b with
    | some _ => if h.ro b then .error (.ub "free of a read-only block") else .ok ((), { h with bytes := upd h.bytes b none })
    | none => .error (.ub "free of a freed or invalid pointer")
  | _ => .error (.ub "free of a pointer that is not the start of an allocated block")

theorem mallocLimit_eq : mallocLimit = C.mallocLimit := rfl
theorem allocB_eq (n : Nat) : allocB n = C.allocB n := rfl
theorem freeB_eq (p : BPtr) : freeB p = C.freeB p := rfl

end RuntimeLibcSplit

section RefactoredInflateCopy
open Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public

/-- Verbatim `85cd20c` statement of `Zlib.Inflate.Proofs.inflateCopy_dynamic_window_exec`. -/
theorem inflateCopy_dynamic_window_exec
    {h : Heap} {source dest : ZStreamRef} {zs nextOff distOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (nextBound : nextOff ≤ 1732)
    (len0 : s.lencode = .ref (.istate_codes zs) 0)
    (distPtr : s.distcode = .ref (.istate_codes zs) distOff)
    (distBound : distOff ≤ 1731) :
    ∃ finished,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, finished) ∧
      source.get finished = some z ∧ finished.istates zs = some s ∧
      dest.get finished = some { z with state := some (.inflate h.nextBlk) } ∧
      finished.istates h.nextBlk =
        some (copiedGeneric dest zs h.nextBlk nextOff distOff (.ref (.blk (h.nextBlk + 1)) 0) s) ∧
      ∃ sourceArray, finished = copiedWindowHeap h dest z s
        (copiedGeneric dest zs h.nextBlk nextOff distOff
          (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray :=
  Zlib.Inflate.Proofs.inflateCopy_dynamic_window_exec good allocator destGet different
    first second window nextPtr nextBound len0 distPtr distBound

/-- Verbatim `85cd20c` statement of `Zlib.Inflate.Proofs.inflateCopy_fixed_window_exec`. -/
theorem inflateCopy_fixed_window_exec
    {h : Heap} {source dest : ZStreamRef} {zs nextOff : Nat}
    {z oldDest : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (destGet : dest.get h = some oldDest)
    (different : source ≠ dest)
    (first : h.allocOk h.nalloc = true)
    (second : h.allocOk (h.nalloc + 1) = true)
    (window : s.window ≠ .null)
    (nextPtr : s.next = .ref (.istate_codes zs) nextOff)
    (nextBound : nextOff ≤ 1732)
    (fixed : s.lencode = .ref .st_lenfix 0 ∧
      s.distcode = .ref .st_distfix 0) :
    ∃ finished,
      C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, finished) ∧
      source.get finished = some z ∧ finished.istates zs = some s ∧
      dest.get finished = some { z with state := some (.inflate h.nextBlk) } ∧
      finished.istates h.nextBlk =
        some (copiedGeneric dest zs h.nextBlk nextOff 0 (.ref (.blk (h.nextBlk + 1)) 0) s) ∧
      ∃ sourceArray, finished = copiedWindowHeap h dest z s
        (copiedGeneric dest zs h.nextBlk nextOff 0
          (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray :=
  Zlib.Inflate.Proofs.inflateCopy_fixed_window_exec good allocator destGet different
    first second window nextPtr nextBound fixed

end RefactoredInflateCopy

section RefactoredCrc32
open Zlib.Crc32.Proofs

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.u32_roundtrip`. -/
theorem u32_roundtrip (x : UInt32) : x.toUInt64.toUInt32 = x :=
  Zlib.Crc32.Proofs.u32_roundtrip x

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.getLsbD_255`. -/
theorem getLsbD_255 (i : Nat) (h : 8 ≤ i) : (255#32).getLsbD i = false :=
  Zlib.Crc32.Proofs.getLsbD_255 i h

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.bx_wob_0`. -/
theorem bx_wob_0 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 0 = b0.toUInt32 :=
  Zlib.Crc32.Proofs.bx_wob_0 b0 b1 b2 b3

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.bx_wob_1`. -/
theorem bx_wob_1 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 1 = b1.toUInt32 :=
  Zlib.Crc32.Proofs.bx_wob_1 b0 b1 b2 b3

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.bx_wob_2`. -/
theorem bx_wob_2 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 2 = b2.toUInt32 :=
  Zlib.Crc32.Proofs.bx_wob_2 b0 b1 b2 b3

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.bx_wob_3`. -/
theorem bx_wob_3 (b0 b1 b2 b3 : UInt8) : bx (wob b0 b1 b2 b3) 3 = b3.toUInt32 :=
  Zlib.Crc32.Proofs.bx_wob_3 b0 b1 b2 b3

/-- Verbatim `85cd20c` statement of `Zlib.Crc32.Proofs.Psi_wob`. -/
theorem Psi_wob (b0 b1 b2 b3 : UInt8) :
    Psi (wob b0 b1 b2 b3) =
      pw 32 b0.toUInt32 ^^^ pw 24 b1.toUInt32 ^^^ pw 16 b2.toUInt32 ^^^ pw 8 b3.toUInt32 :=
  Zlib.Crc32.Proofs.Psi_wob b0 b1 b2 b3

end RefactoredCrc32

section WpEquivalence
open Std.WP
open scoped C.HeapWP

/-- Equivalence between `C.OkOn` and `Std.Do.Triple` (`Std.WP`) on `C.M`. -/
theorem okOn_iff_triple {α : Type} {m : M α} {h : Heap} {x : α} :
    OkOn h m x ↔ ⦃ fun s => s = h ⦄ m ⦃ fun y s => y = x ∧ s = h ⦄ :=
  C.okOn_iff_triple

end WpEquivalence

#print axioms copyRange_eq
#print axioms Ptr.memcpy_eq
#print axioms strlenFrom_eq
#print axioms strlenB_eq
#print axioms allocB_eq
#print axioms freeB_eq
#print axioms inflateCopy_dynamic_window_exec
#print axioms inflateCopy_fixed_window_exec
#print axioms u32_roundtrip
#print axioms getLsbD_255
#print axioms bx_wob_0
#print axioms bx_wob_1
#print axioms bx_wob_2
#print axioms bx_wob_3
#print axioms Psi_wob
#print axioms okOn_iff_triple

end Baseline85cd20c
