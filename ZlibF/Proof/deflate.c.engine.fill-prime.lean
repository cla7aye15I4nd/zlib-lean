import ZlibF.Proof.«deflate.c.engine.fill-source»

/-! # Priming the first window without deferred insertions -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem while_stops {α : Type} {cond : α → M (Bool × α)} {body : α → M α}
    {h g : Heap} {a b : α} (stop : cond a h = .ok ((false, b), g)) :
    cwhile cond body a h = .ok (b, g) := by
  unfold cwhile
  change cwhile.go cond body (18446744073709551615 + 1) a h = _
  rw [cwhile.go, bind_app, stop]
  rfl

theorem empty_insert_loop {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (insert : d.insert = 0)
    (body : UInt32 × Bool → M (UInt32 × Bool)) (str : UInt32) :
    cwhile (fun (str, brk) => do
        let ins ← rd (some (.tab ds)) (·.insert)
        pure (ins != 0 && !brk, (str, brk))) body (str, false) h = .ok ((str, false), h) := by
  apply while_stops
  simp [bind_app, rdD_eq, state, insert]

def primeState (d : DeflateState) (wa : Array UInt8) : DeflateState :=
  if d.lookahead ≥ 3 then
    { d with ins_h := updHash d.hash_shift d.hash_mask wa[0]!.toUInt32 wa[1]! }
  else d

end Zlib.Deflate.Engine.Proofs
