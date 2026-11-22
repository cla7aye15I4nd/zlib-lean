import ZlibF.Proof.«infback.c.end»
import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«trees.c»

/-!
# infback.c: `inflateBack`, the entry checks and the end-of-input exit

Proved here: the `Z_STREAM_ERROR` exits of the entry, and the exit when `in` has no input at the first `PULL`
(`Z_BUF_ERROR`, `next_in` is `NULL`, `avail_in` is 0, `out` is not called). The loop over the blocks is proved in
the safety modules: `inflate_back_sequence_safety` (`infback.c.safety-fast`) is
`Goal.inflate_back_sequence_safety` (see `docs/en/proof/callbacks.md`).
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-! ### Running the monad `X` -/

theorem xrun_bind {α β : Type} (m : X α) (f : α → X β) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (m >>= f)) l h =
      match StateT.run (ExceptT.run m) l h with
      | .ok ((.ok a, l'), h') => StateT.run (ExceptT.run (f a)) l' h'
      | .ok ((.error e, l'), h') => .ok ((.error e, l'), h')
      | .error e => .error e := by
  cases hm : StateT.run (ExceptT.run m) l h with
  | error e => simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, ExceptT.run, ExceptT.mk, StateT.run] at hm ⊢; simp [hm]
  | ok p =>
    obtain ⟨⟨r, l'⟩, h'⟩ := p
    cases r <;> simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, ExceptT.run, ExceptT.mk, StateT.run,
      pure] at hm ⊢ <;> simp [hm, StateT.pure]

theorem xrun_get (l : IL) (h : Heap) : StateT.run (ExceptT.run (get : X IL)) l h = .ok ((.ok l, l), h) := rfl
theorem xrun_set (l l0 : IL) (h : Heap) : StateT.run (ExceptT.run (set l0 : X PUnit)) l h = .ok ((.ok ⟨⟩, l0), h) := rfl
theorem xrun_lift {α : Type} (m : M α) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (liftM m : X α)) l h =
      match m h with | .ok (a, h') => .ok ((.ok a, l), h') | .error e => .error e := by
  cases hm : m h <;> simp [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, StateT.lift, ExceptT.run, ExceptT.mk,
    StateT.run, bind, pure, Functor.map, StateT.map, hm]

theorem PULL_eof {c : BCtx} {l : IL} {h h3 : Heap} {nx : BPtr} (h0 : l.have_ = 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (PULL c)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  simp [PULL, xrun_bind, xrun_get, xrun_set, xrun_lift, hin, h0]

/-- A null stream: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBack_nullstream (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) (h : Heap) :
    inflateBack none inCb inDesc outCb outDesc h = .ok (Z_STREAM_ERROR, h) := by
  simp [inflateBack]

/-- No state: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBack_nostate {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hno : z.state = none)
    (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) :
    inflateBack (some r) inCb inDesc outCb outDesc h = .ok (Z_STREAM_ERROR, h) := by
  isimp [inflateBack, hz, hno]

end Zlib.Infback.Proofs
