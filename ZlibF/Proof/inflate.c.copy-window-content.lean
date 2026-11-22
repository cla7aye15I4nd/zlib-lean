import ZlibF.Proof.«inflate.c.copy-origin-state»
import ZlibF.Proof.«inflate.c.copy-window-failure»
import ZlibF.Proof.«inflate.c.record-frame»
namespace Zlib.Inflate.Proofs.CopyResource
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem inflateCopy_dynamic_window_contents
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
      ∃ sourceArray w, s.window = .ref (.blk w) 0 ∧ h.bytes w = some sourceArray ∧
        finished = copiedWindowHeap h dest z s
        (copiedGeneric dest zs h.nextBlk nextOff distOff
          (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray := by
  obtain ⟨f, result⟩ := inflateCopy_dynamic_window_framed good allocator destGet different
    first second window nextPtr nextBound len0 distPtr distBound
  obtain ⟨w, a, ptr, live, heapEq, _⟩ := result.window
  exact ⟨f, result.run, result.sourceStream, result.sourceState, result.destStream, result.destState,
    a, w, ptr, live, heapEq⟩

#print axioms inflateCopy_dynamic_window_contents

theorem inflateCopy_fixed_window_contents
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
      ∃ sourceArray w, s.window = .ref (.blk w) 0 ∧ h.bytes w = some sourceArray ∧
        finished = copiedWindowHeap h dest z s
        (copiedGeneric dest zs h.nextBlk nextOff 0
          (.ref (.blk (h.nextBlk + 1)) 0) s) sourceArray := by
  obtain ⟨f, result⟩ := inflateCopy_fixed_window_framed good allocator destGet different
    first second window nextPtr nextBound fixed
  obtain ⟨w, a, ptr, live, heapEq, _⟩ := result.window
  exact ⟨f, result.run, result.sourceStream, result.sourceState, result.destStream, result.destState,
    a, w, ptr, live, heapEq⟩

#print axioms inflateCopy_fixed_window_contents

end Zlib.Inflate.Proofs.CopyResource
