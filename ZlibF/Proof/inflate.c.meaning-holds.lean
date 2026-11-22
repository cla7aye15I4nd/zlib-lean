import ZlibF.Proof.«inflate.c.meaning-loop»

/-!
# inflate.c: a leave for want of output room holds output

`HoldsOutput c h`: the decoder record of the call is in `LIT`, `MATCH`, or `COPY` with bytes of
the stored block left. A mode step that leaves because the output is full (`left == 0`) leaves in
one of these, with output still due.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- The decoder record of the call holds output that is due. -/
def HoldsOutput (c : Ctx) (h : Heap) : Prop :=
  ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
    s.mode = LIT ∨ s.mode = MATCH ∨ (s.mode = COPY ∧ s.length ≠ 0)

theorem HoldsOutput.of_state {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (holds : s.mode = LIT ∨ s.mode = MATCH ∨ (s.mode = COPY ∧ s.length ≠ 0)) : HoldsOutput c h := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  rw [hs] at hs'
  cases hs'
  exact holds

end Zlib.Inflate.Proofs
