import ZlibF.Proof.«inflate.c.main.macros»

/-!
# inflate.c: the modes that touch only the registers and the state record

`DONE` and `LIT`. A mode theorem is stated for a mode function run by `runX` from registers `l` on heap `h`; the
state record is `s` at table entry `zs` (`c.st = some (.tab zs)`). The heap after a write is `setI` of the base module.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem wrS_tab {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) (f : InflateState → InflateState) :
    wrS (some (.tab zs)) f h = .ok ((), setI h zs (f s)) := by
  unfold wrS
  rw [bind_app, ldInflateState_tab e]
  simp only []
  rw [stInflateState_tab e]
  rfl

theorem setMode_tab {h : Heap} {zs : Nat} {s : InflateState} (e : h.istates zs = some s) (m : UInt32) :
    setMode (some (.tab zs)) m h = .ok ((), setI h zs { s with mode := m }) := wrS_tab e _

/-- `case DONE:` -- `ret = Z_STREAM_END; goto inf_leave`. -/
theorem inflate_DONE_run (c : Ctx) (l : IL) (h : Heap) :
    runX (inflate_DONE c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) := rfl

/-- `case LIT:` with no room (`left = 0`): `goto inf_leave`, nothing changes. -/
theorem inflate_LIT_full (c : Ctx) (l : IL) (h : Heap) (h0 : l.left = 0) :
    runX (inflate_LIT c) l h = .ok ((.error Ex.leave, l), h) := by
  unfold inflate_LIT
  rw [runX_bind, runX_get]
  simp [h0, runX_throw, runX_bind]

end Zlib.Inflate.Proofs
