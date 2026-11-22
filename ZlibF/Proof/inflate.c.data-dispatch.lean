import ZlibF.Proof.«inflate.c.match-output»
import ZlibF.Proof.«inflate.c.literal-step»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

theorem inflate_dispatch_LEN {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LEN) :
    runX (inflate_dispatch c) l h = runX (inflate_LEN c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  rfl

theorem inflate_dispatch_LIT {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LIT) :
    runX (inflate_dispatch c) l h = runX (inflate_LIT c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  rfl

theorem inflate_dispatch_MATCH {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = MATCH) :
    runX (inflate_dispatch c) l h = runX (inflate_MATCH c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  simp only [mode]
  rfl

end Zlib.Inflate.Proofs
