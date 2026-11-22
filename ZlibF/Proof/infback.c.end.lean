import ZlibF.Proof.«infback.c.init»

/-!
# infback.c: `inflateBackEnd`

`inflateBackEnd` frees the state record and clears the stream's state pointer. It does not run `inflateStateCheck`, and
it never touches the window, which belongs to the caller.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

/-- The heap after a successful `inflateBackEnd`: the state record is freed and the stream's state pointer is `NULL`. -/
def backEndHeap (h : Heap) (r : ZStreamRef) (z : ZStream) (zs : Nat) : Heap :=
  r.put (freeIst h zs) { z with state := none }

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- A null stream: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBackEnd_nullstream (h : Heap) : inflateBackEnd none h = .ok (Z_STREAM_ERROR, h) := by
  simp [inflateBackEnd]

/-- No state, or no `zfree`: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBackEnd_refused {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z)
    (hno : z.state = none ∨ z.zfree = .null) :
    inflateBackEnd (some r) h = .ok (Z_STREAM_ERROR, h) := by
  rcases hno with e | e <;> isimp [inflateBackEnd, hz, e]

end Zlib.Infback.Proofs
