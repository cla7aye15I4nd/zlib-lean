import ZlibF.Proof.«inflate.c.misc2»
import ZlibF.Proof.«pointer-arithmetic»

/-!
# inflate.c: the ring buffer of `updatewindow`

The copy lemmas establish the two ring-buffer branches for `wbits ≤ 15`.
Pointer arithmetic uses the checked rules in `ZlibF.Proof.PointerArithmetic`.
-/

namespace Zlib.Inflate.Proofs.W
open C ZlibF.Proof


/-- `if (state->wsize == 0) { wsize = 1U << wbits; wnext = 0; whave = 0; }` -/
def initWin (st : InflateState) : InflateState :=
  if st.wsize == 0 then { st with wsize := (1 : UInt32) <<< st.wbits, wnext := 0, whave := 0 } else st

/-- `if (copy >= wsize)`: copy the last `wsize` bytes before `end` into the whole window. -/
def uw_big (ist : InflateStatePtr) (st : InflateState) (e : BPtr) : M UInt32 := do
  let src ← PointerArithmetic.subNat e st.wsize.toNat
  memcpyB st.window src st.wsize.toNat
  stInflateState ist { st with wnext := 0, whave := st.wsize }
  return 0

/-- `else`: copy `copy` bytes into the ring buffer, in at most two pieces. -/
def uw_small (ist : InflateStatePtr) (st : InflateState) (e : BPtr) (copy : UInt32) : M UInt32 := do
  let dist : UInt32 := if st.wsize - st.wnext > copy then copy else st.wsize - st.wnext
  let dst ← PointerArithmetic.addNat st.window st.wnext.toNat
  let src ← PointerArithmetic.subNat e copy.toNat
  memcpyB dst src dist.toNat
  let copy' : UInt32 := copy - dist
  if copy' != 0 then
    let src2 ← PointerArithmetic.subNat e copy'.toNat
    memcpyB st.window src2 copy'.toNat
    stInflateState ist { st with wnext := copy', whave := st.wsize }
    return 0
  else
    let wn : UInt32 := st.wnext + dist
    let wn : UInt32 := if wn == st.wsize then 0 else wn
    let wh : UInt32 := if st.whave < st.wsize then st.whave + dist else st.whave
    stInflateState ist { st with wnext := wn, whave := wh }
    return 0

/-- The part of `updatewindow(strm, end, copy)` after the window has been allocated. -/
def update2 (sr : Nat) (e : BPtr) (copy : UInt32) : M UInt32 := do
  let z ← ldZStream (some (.tab sr))
  let ist ← castInflateState z.state
  let st0 ← ldInflateState ist
  let st := initWin st0
  if copy ≥ st.wsize then uw_big ist st e else uw_small ist st e copy

/-- The window invariant W of `docs/en/proof/inflate.md`: the window is a writable byte block of `2^wbits` bytes. -/
structure WInv (h : Heap) (st : InflateState) : Prop where
  k : st.wbits.toNat ≤ 15
  win : ∃ w a, st.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧ a.size = 2 ^ st.wbits.toNat
  ws : st.wsize.toNat = 0 ∨ st.wsize.toNat = 2 ^ st.wbits.toNat
  hv : st.whave.toNat ≤ st.wsize.toNat
  wn : st.wnext.toNat < st.wsize.toNat ∨ (st.wsize.toNat = 0 ∧ st.wnext.toNat = 0)
  eq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat

theorem shl_toNat (b : UInt32) (hb : b.toNat ≤ 15) : ((1 : UInt32) <<< b).toNat = 2 ^ b.toNat := by
  have h15 : 2 ^ b.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hb
  have e32 : b.toNat % 32 = b.toNat := Nat.mod_eq_of_lt (by omega)
  rw [UInt32.toNat_shiftLeft, e32]
  simp [Nat.shiftLeft_eq]
  omega

/-- The tables other than `bytes` and `istates` are unchanged, and so are the read-only flags and the block counter. -/
def Same (h h' : Heap) : Prop :=
  h'.words = h.words ∧ h'.dstates = h.dstates ∧ h'.gzheaders = h.gzheaders ∧ h'.gzstates = h.gzstates ∧
    h'.streams = h.streams ∧ h'.ro = h.ro ∧ h'.nextBlk = h.nextBlk

end Zlib.Inflate.Proofs.W
