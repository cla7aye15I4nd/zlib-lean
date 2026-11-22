import ZlibF.Runtime.Schema

/-!
# inffast.c and inflate.c: copying bytes into the output and the window ring

The pure array functions of a match copy (`blitN`, `cpyN`, `matchArr`) and the slot of the window ring that holds a
byte of the history (`ringSlot`). The lemmas about them are in `ZlibF/Proof/inffast.c.copy.lean`,
`ZlibF/Proof/inffast.c.match.lean` and `ZlibF/Proof/inflate.c.ring.lean`.
-/

namespace Zlib.Inffast.Proofs
open C

/-- `k` bytes copied from the fixed array `S` (offset `fo`) into `A` (offset `oo`), one at a time. -/
def blitN (S : Array UInt8) : Nat → Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, _, A => A
  | k + 1, fo, oo, A => blitN S k (fo + 1) (oo + 1) (A.set! oo (S.getD fo 0))

/-- `k` bytes copied inside `A` from offset `fo` to offset `oo`, one at a time (the source may be written meanwhile). -/
def cpyN : Nat → Nat → Nat → Array UInt8 → Array UInt8
  | 0, _, _, A => A
  | k + 1, fo, oo, A => cpyN k (fo + 1) (oo + 1) (A.set! oo (A.getD fo 0))

/-- The output block after a match copy: `len` bytes, `dist` back, with `o - bg` bytes of the current call before `o`
and the window (`W` at offset `woff`, ring of size `wsize`, next write position `wnext`) before that. This follows
the case split of `copyMatch`. -/
def matchArr (wsize wnext woff : Nat) (W : Array UInt8) (bg o dist len : Nat) (A : Array UInt8) : Array UInt8 :=
  if o - bg < dist then
    let op := dist - (o - bg)
    if wnext = 0 then
      if op < len then cpyN (len - op) (o + op - dist) (o + op) (blitN W op (woff + wsize - op) o A)
      else blitN W len (woff + wsize - op) o A
    else if wnext < op then
      if op - wnext < len then
        if wnext < len - (op - wnext) then
          cpyN (len - (op - wnext) - wnext) (o + (op - wnext) + wnext - dist) (o + (op - wnext) + wnext)
            (blitN W wnext woff (o + (op - wnext)) (blitN W (op - wnext) (woff + wsize + wnext - op) o A))
        else blitN W (len - (op - wnext)) woff (o + (op - wnext)) (blitN W (op - wnext) (woff + wsize + wnext - op) o A)
      else blitN W len (woff + wsize + wnext - op) o A
    else
      if op < len then cpyN (len - op) (o + op - dist) (o + op) (blitN W op (woff + wnext - op) o A)
      else blitN W len (woff + wnext - op) o A
  else cpyN len (o - dist) o A

/-- The output block after a match copy when the window is the output block itself (`inflateBack`,
`wnext = 0`): the bytes before `o` are copied one at a time from the current block, first from the
window's tail, then from `o + op - dist`. -/
def matchArrA (wsize woff : Nat) (bg o dist len : Nat) (A : Array UInt8) : Array UInt8 :=
  if o - bg < dist then
    let op := dist - (o - bg)
    if op < len then cpyN (len - op) (o + op - dist) (o + op) (cpyN op (woff + wsize - op) o A)
    else cpyN len (woff + wsize - op) o A
  else cpyN len (o - dist) o A

end Zlib.Inffast.Proofs

namespace Zlib.Inflate.Spec

/-- The slot of the ring buffer (of size `ws`, next write position `wn`, `wh` valid bytes) that holds the `j`-th oldest
valid byte: the valid bytes end just before `wn` and wrap around the end of the buffer. -/
def ringSlot (ws wn wh j : Nat) : Nat :=
  if wh ≤ wn then wn - wh + j else if j < wh - wn then ws - (wh - wn) + j else j - (wh - wn)

end Zlib.Inflate.Spec
