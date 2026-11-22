import ZlibF.Proof.«infback.c.inv»
import ZlibF.Proof.«infback.c.pure»
import ZlibF.Proof.«infback.c.wf»
import ZlibF.Proof.«inflate.c.main.stored»
import ZlibF.Proof.«inflate.c.main.stored2»

/-!
# infback.c: `ROOM()` on the loop invariant, and `case STORED`
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-! ## `case STORED` -/

/-- The copy count of `case STORED`: `min(length, have, left)`, written with the two `if`s of the C. -/
def clampCopy (len hv lf : UInt32) : UInt32 :=
  let c1 := if len > hv then hv else len
  if c1 > lf then lf else c1

theorem clampCopy_le (len hv lf : UInt32) : (clampCopy len hv lf).toNat ≤ len.toNat ∧
    (clampCopy len hv lf).toNat ≤ hv.toNat ∧ (clampCopy len hv lf).toNat ≤ lf.toNat := by
  unfold clampCopy
  simp only [GT.gt, UInt32.lt_iff_toNat_lt]
  split <;> split <;> omega

theorem clampCopy_pos (len hv lf : UInt32) (h1 : len ≠ 0) (h2 : hv ≠ 0) (h3 : lf ≠ 0) : clampCopy len hv lf ≠ 0 := by
  have e1 : 0 < len.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h1 (UInt32.toNat_inj.mp (by simpa using e))
  have e2 : 0 < hv.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h2 (UInt32.toNat_inj.mp (by simpa using e))
  have e3 : 0 < lf.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h3 (UInt32.toNat_inj.mp (by simpa using e))
  intro e
  have := congrArg UInt32.toNat e
  unfold clampCopy at this
  simp only [GT.gt, UInt32.lt_iff_toNat_lt] at this
  split at this <;> split at this <;> simp at this <;> omega

/-- The part of the copy loop after `ROOM()`. -/
def storedTail (c : BCtx) : X Unit := do
  let l ← get
  let mut copy := l.copy
  if copy > l.have_ then copy := l.have_
  if copy > l.left then copy := l.left
  memcpyB l.put l.next copy.toNat
  let nx ← l.next.add (copy.toNat : Int)
  let pt ← l.put.add (copy.toNat : Int)
  set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
  wrS c.st fun s => { s with length := s.length - copy }

/-- The loop body of `case STORED`. -/
def storedBody (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  modify fun l => { l with copy := s.length }
  PULL c
  ROOM c
  storedTail c

/-- The condition of the copy loop. -/
def storedCond (c : BCtx) : X Bool := do return (← rdS c.st (·.length)) != 0

/-- `case STORED` as the function `back_STORED`, with the loop split into `storedCond` and `storedBody`. -/
theorem back_STORED_eq (c : BCtx) : back_STORED c = (do
    BYTEBITS
    NEEDBITS c 32
    let l ← get
    if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
      badMode c "invalid stored block lengths"
      return
    wrS c.st fun s => { s with length := l.hold.toUInt32 &&& 0xffff }
    INITBITS
    xwhile (storedCond c) (storedBody c)
    setMode c.st TYPE) := rfl

/-- The length of the state record in the heap (0 if there is none): the measure of the copy loop. -/
def stLen (zs : Nat) (h : Heap) : Nat := match h.istates zs with
  | some s => s.length.toNat
  | none => 0

theorem stLen_of {zs : Nat} {h : Heap} {s : InflateState} (hs : h.istates zs = some s) : stLen zs h = s.length.toNat := by
  simp [stLen, hs]

end Zlib.Infback.Proofs
