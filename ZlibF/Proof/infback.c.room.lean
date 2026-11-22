import ZlibF.Proof.«infback.c.macros»
import ZlibF.Proof.«inflate.c.main.simple»

/-!
# infback.c: `ROOM()` and the mode setters

`ROOM()` hands the full window to `out` and starts again at its beginning. The call-back sees the window as `len` readable
bytes; it may not change them (`CbContract`).
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- `ROOM()` while there is room: nothing happens. -/
theorem ROOM_have (c : BCtx) {l : IL} {h : Heap} (hl : l.left ≠ 0) :
    runX (ROOM c) l h = .ok ((.ok (), l), h) := by
  have hb : (l.left == 0) = false := by simpa using hl
  unfold ROOM
  simp [runX_bind, runX_get, hl, runX_pure]

end Zlib.Infback.Proofs
