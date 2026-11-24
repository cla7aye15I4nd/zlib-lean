import ZlibF.Proof.«infback.c.addressed-dispatch»

/-! Running the addressed dispatcher from the last stored block through inf_leave. -/
namespace Zlib.Infback.AddressedStored
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.AddressedType
set_option autoImplicit false

/-- Each successful dispatch provides the registers and heap for the next one. -/
private inductive ToLeave (body : X Unit) (regs : IL) (after : Heap) : Nat → IL → Heap → Prop
  | leave {l h} : runX body l h = .ok ((.error Ex.leave, regs), after) → ToLeave body regs after 1 l h
  | more {l h mid H n} : runX body l h = .ok ((.ok (), mid), H) →
      ToLeave body regs after n mid H → ToLeave body regs after (n+1) l h

private theorem ToLeave.run {body : X Unit} {regs l : IL} {after h : Heap} {n : Nat}
    (path : ToLeave body regs after n l h) (bound : n < fuel) :
    runX (xwhile (pure true) body) l h = .ok ((.error Ex.leave, regs), after) := by
  let post := fun (v : Except Ex Unit) (r : IL) (H : Heap) => v = .error Ex.leave ∧ r = regs ∧ H = after
  obtain ⟨v, r, H, run, eqs⟩ := xwhileBrk_run (cond := pure true) (body := do body; pure false)
    (ToLeave body regs after) post (fun _ b G step => by
      refine ⟨b, G, rfl, ?_⟩
      cases step with
      | leave endRun => exact ⟨.error Ex.leave, regs, after, by rw [runX_bind, endRun], rfl, rfl, rfl⟩
      | more first tail => exact ⟨.ok false, _, _, by rw [runX_bind, first]; rfl, tail⟩)
    (fun _ _ empty => nomatch empty) path bound
  obtain ⟨rfl, rfl, rfl⟩ := eqs
  exact run

/-- Starting in the last stored block, arbitrary conforming callbacks may
redirect the unread range between any two copies. The actual loop reaches
its exit on refusal, invalid block lengths, or completion of this block. -/
theorem final_stored {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    (message : ∀ cs H z msg, admitted cs H → r.get H = some z → admitted cs (r.put H {z with msg := msg}))
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (mode : s.mode = STORED) (final : s.last ≠ 0) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    ∃ regs after t, runX (xwhile (pure true) (back_dispatch c)) l h = .ok ((.error Ex.leave, regs), after) ∧
      after.istates owner = some t ∧ Buffers cell w off cap t regs after ∧ admitted regs.pointerLocals after ∧
      (regs.ret = Z_BUF_ERROR ∨ regs.ret = Z_DATA_ERROR ∨ regs.ret = Z_STREAM_END) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have read {t : InflateState} {H : Heap} (present : H.istates owner = some t) :
      rdS c.st (·.mode) H = .ok (t.mode,H) := by
    change rdS (some (.tab owner)) _ H = _
    simp only [rdI_eq, present]
  obtain ⟨v, reg, H, t, first, st, b, success, fail, shape, _, _, frame⟩ :=
    stored_safe cb stream state buf allowed
  have dispatch : runX (back_dispatch c) l h = .ok ((v,reg), H) := by
    rw [back_dispatch, runX_bind, runX_lift_ok (read state), mode]
    exact first
  have accepted := frame edit message
  change ∃ _ _ _, runX (xwhile (pure true) (back_dispatch c)) l h = _ ∧ _
  cases v with
  | error e =>
    obtain ⟨rfl, ret⟩ := fail e rfl
    exact ⟨reg,H,t,(ToLeave.leave dispatch).run (by decide), st,b,accepted,Or.inl ret⟩
  | ok u =>
    cases u
    rcases success rfl with bad | ⟨nextMode, _⟩
    · have atBad := read st
      rw [bad] at atBad
      have stop := back_dispatch_exit c reg H BAD atBad (by decide) (by decide) (by decide) (by decide)
      exact ⟨_,H,t,(ToLeave.more dispatch (.leave stop)).run (by decide),st,{b with},accepted,Or.inr (Or.inl rfl)⟩
    · have same := congrArg InflateState.last shape
      have last : t.last ≠ 0 := fun zero => final (same.symm.trans zero)
      have ty := type_safe cb stream st b accepted
      simp only [show (t.last != 0) = true by simpa using last, ↓reduceIte] at ty
      have dispatchType : runX (back_dispatch c) reg H =
          .ok ((.ok (), bytebits reg), setI H owner {t with mode := DONE}) := by
        rw [back_dispatch, runX_bind, runX_lift_ok (read st), nextMode]
        exact ty
      let done := {t with mode := DONE}
      let A := setI H owner done
      have got : A.istates owner = some done := upd_same ..
      have stop := back_dispatch_exit c (bytebits reg) A DONE (read got) (by decide) (by decide) (by decide) (by decide)
      exact ⟨_,A,done,(ToLeave.more dispatch (.more dispatchType (.leave stop))).run (by decide),got,
        {b with window := ⟨b.window.storage,b.window.writable⟩}, edit _ _ _ accepted,Or.inr (Or.inr rfl)⟩

#print axioms final_stored
end Zlib.Infback.AddressedStored
