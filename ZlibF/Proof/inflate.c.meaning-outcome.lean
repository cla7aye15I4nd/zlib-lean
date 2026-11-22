import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.leave-cause-run»

/-!
# inflate.c: what one trip of the mode loop can end in

The loop assembly of `meaning_step` composes per-mode steps whose results are
`TripOutcome`s:

* the trip continues (`break` or fall-through) with `LoopMatches`, or with
  the decoder in `BAD` and the input read so far doomed (`LoopBad`);
* the trip leaves (`goto inf_leave`) with `LoopMatches` (input or output
  exhausted, `Z_BLOCK`), or from `DONE` with `Z_STREAM_END`, or from `BAD`
  with `Z_DATA_ERROR`.

`DICT` without a dictionary returns `Z_NEED_DICT` directly (no `inf_leave`)
and `MEM` returns `Z_MEM_ERROR`; both are handled by the call-level
assembly, not here.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The decoder is in `BAD` after this trip: the configuration and the input
cursor are those of the loop, and no valid full-window stream begins with
the input read so far. The return register is not constrained: `TABLE`,
`LENLENS` and `CODELENS` store the result of `inflate_table` in `ret` before
they enter `BAD`, and `case BAD:` overwrites it with `Z_DATA_ERROR`. -/
def LoopBad (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL) : Prop :=
  ∃ (zs : Nat) (s : InflateState), c.st = some (.tab zs) ∧ h.istates zs = some s ∧
    s.mode = BAD ∧ ConfigMatches (loopState s l) f.wrap f.configured ∧
    l.have_.toNat ≤ l.in_.toNat ∧ l.in_.toNat = f.inp.length ∧ LoopDoomed f l

/-- The possible ends of one trip of the mode loop (one `inflate_dispatch`). -/
def TripOutcome (c : Ctx) (f : LoopFrame) (result : Except Ex Unit) (h : Heap) (l : IL) : Prop :=
  (result = .ok () ∧ (LoopMatches c f h l ∨ LoopBad c f h l)) ∨
  (result = .error Ex.leave ∧
    (LoopMatches c f h l ∨
     (l.ret = Z_STREAM_END ∧ LoopMatches c f h { l with ret := Z_OK }) ∨
     (l.ret = Z_DATA_ERROR ∧ LoopBad c f h { l with ret := Z_OK })))

/-- The one in-call state that `LoopMatches` does not cover: raw data after the final block, in
`CHECK`. `TYPEDO` sets `CHECK` and ends its trip with `break`; the next trip runs `CHECK`,
`LENGTH` and `DONE` without reading anything (no wrapper), so no call leaves in this state. The
facts are those of the end stage: `LoopMatches` for the heap whose decoder record is in `DONE`,
with the record actually in `CHECK`. -/
def RawCheck (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL) : Prop :=
  f.wrap = .raw ∧ ∃ (zs : Nat) (s : InflateState), c.st = some (.tab zs) ∧
    h.istates zs = some s ∧ s.mode = CHECK ∧ LoopMatches c f (setI h zs { s with mode := DONE }) l

/-- `case BAD:` sets `Z_DATA_ERROR` and leaves. -/
theorem bad_trip {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (bad : LoopBad c f h l) (strm : c.strm = some r) (hz : r.get h = some z) :
    runX (inflate_dispatch c) l h = .ok ((.error .leave, { l with ret := Z_DATA_ERROR }), h) ∧
      TripOutcome c f (.error .leave) h { l with ret := Z_DATA_ERROR } := by
  obtain ⟨zs, s, st, hs, mode, rest⟩ := bad
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  exact ⟨inflate_dispatch_BAD_leave E l mode, Or.inr ⟨rfl, Or.inr (Or.inr ⟨rfl, ⟨zs, s, st, hs, mode, rest⟩⟩)⟩⟩

#print axioms bad_trip

end Zlib.Inflate.Proofs
