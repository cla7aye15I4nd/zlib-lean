import ZlibF.Proof.«inflate.c.copy-generic-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The common final heap of either successful windowed table-origin branch.
Only the code-pointer repair differs between those branches. -/
def copiedWindowHeap (h : Heap) (dest : ZStreamRef) (z : ZStream)
    (s copied : InflateState) (sourceArray : Array UInt8) : Heap :=
  let size := 2 ^ s.wbits.toNat
  let zNext := { z with state := some (.inflate h.nextBlk) }
  let stateHeap := allocIstHeap (dest.put h zNext) copied
  let freshArray : Array UInt8 := Array.ofFn (n := size)
    (fun i => Junk.of (h.garbage (h.nalloc + 1) i.val))
  let allocated := Zlib.Zutil.Proofs.allocHeap stateHeap size
  { allocated with bytes := (upd allocated.bytes (h.nextBlk + 1)
      (some (copyRange freshArray sourceArray 0 0 s.whave.toNat))) }

/-- Successful windowed `inflateCopy` on either table-origin branch. The frame
describes memory at return, after the destination stream and state are updated. -/
structure WindowCopyResult (h finished : Heap) (source dest : ZStreamRef) (zs : Nat)
    (z : ZStream) (s copied : InflateState) : Prop where
  run : C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, finished)
  sourceStream : source.get finished = some z
  sourceState : finished.istates zs = some s
  destStream : dest.get finished = some { z with state := some (.inflate h.nextBlk) }
  destState : finished.istates h.nextBlk = some copied
  window : ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
    finished = copiedWindowHeap h dest z s copied a ∧ finished.bytes w = some a ∧
    ∀ i : Fin (2 ^ s.wbits.toNat), s.whave.toNat ≤ i.val →
      (finished.bytes (h.nextBlk + 1)).bind (·[i.val]?) =
        some (Junk.of (h.garbage (h.nalloc + 1) i.val))

end Zlib.Inflate.Proofs
