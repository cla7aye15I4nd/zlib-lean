import ZlibF.Proof.«inflate.c.register-frame»
import ZlibF.Proof.«inflate.c.exit-code-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

/-- A source observer of the saved input count. It assumes neither safety
nor termination; it describes every successfully returning execution. -/
def InputBaseX {α : Type} (base : UInt32) (program : X α) : Prop :=
  ∀ l h result regs after, l.in_ = base →
    runX program l h = .ok ((result, regs), after) → regs.in_ = base

theorem inputBaseX_pure {α : Type} (base : UInt32) (value : α) : InputBaseX base (pure value) :=
  registerFrame_pure (fun regs => regs.in_ = base) value

theorem inputBaseX_get (base : UInt32) : InputBaseX base (get : X IL) :=
  registerFrame_get (fun regs => regs.in_ = base)

theorem inputBaseX_set (base : UInt32) (l : IL) (current : l.in_ = base) :
    InputBaseX base (set l : X Unit) :=
  registerFrame_set (fun regs => regs.in_ = base) l current

theorem inputBaseX_modify (base : UInt32) (update : IL → IL)
    (fixed : ∀ l, l.in_ = base → (update l).in_ = base) :
    InputBaseX base (modify update : X Unit) :=
  registerFrame_modify (fun regs => regs.in_ = base) update fixed

theorem inputBaseX_lift {α : Type} (base : UInt32) (program : M α) :
    InputBaseX base (monadLift program : X α) :=
  registerFrame_lift (fun regs => regs.in_ = base) program

theorem inputBaseX_throw {α : Type} (base : UInt32) (exit : Ex) :
    InputBaseX base (throw exit : X α) :=
  registerFrame_throw (fun regs => regs.in_ = base) exit

theorem inputBaseX_bind {α β : Type} {base : UInt32} {first : X α} {next : α → X β}
    (hf : InputBaseX base first) (hn : ∀ value, InputBaseX base (next value)) :
    InputBaseX base (first >>= next) :=
  registerFrame_bind (invariant := (fun regs => regs.in_ = base)) hf hn

/-- Reading the current registers exposes their saved count to the actual
continuation. This accounts for source snapshots later written by set. -/
theorem inputBaseX_get_bind {α : Type} {base : UInt32} {next : IL → X α}
    (body : ∀ l, l.in_ = base → InputBaseX base (next l)) :
    InputBaseX base (get >>= next) :=
  registerFrame_get_bind (invariant := (fun regs => regs.in_ = base)) body

theorem inputBaseX_ite {α : Type} {base : UInt32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : InputBaseX base yes) (hn : InputBaseX base no) : InputBaseX base (if test then yes else no) :=
  registerFrame_ite (invariant := (fun regs => regs.in_ = base)) hy hn

theorem inputBaseX_xwhileBrk {base : UInt32} {cond body : X Bool}
    (hc : InputBaseX base cond) (hb : InputBaseX base body) : InputBaseX base (xwhileBrk cond body) :=
  registerFrame_xwhileBrk (invariant := fun l => l.in_ = base) hc hb

theorem inputBaseX_xwhile {base : UInt32} {cond : X Bool} {body : X Unit}
    (hc : InputBaseX base cond) (hb : InputBaseX base body) : InputBaseX base (xwhile cond body) :=
  registerFrame_xwhile (invariant := (fun regs => regs.in_ = base)) hc hb

theorem inputBaseX_xdoWhile {base : UInt32} {body : X Unit} {cond : X Bool}
    (hb : InputBaseX base body) (hc : InputBaseX base cond) : InputBaseX base (xdoWhile body cond) :=
  registerFrame_xdoWhile (invariant := (fun regs => regs.in_ = base)) hb hc

theorem inputBaseX_xloopBrk {base : UInt32} {body : X Bool} (hb : InputBaseX base body) :
    InputBaseX base (xloopBrk body) :=
  registerFrame_xloopBrk (invariant := (fun regs => regs.in_ = base)) hb

macro "input_base_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact inputBaseX_pure _ _
    | with_reducible exact inputBaseX_get _
    | with_reducible exact inputBaseX_lift _ _
    | with_reducible exact inputBaseX_throw _ _
    | with_reducible refine inputBaseX_set _ _ ?_
    | with_reducible refine inputBaseX_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine inputBaseX_get_bind (fun _ fixed => ?_)
    | with_reducible apply inputBaseX_xdoWhile
    | with_reducible apply inputBaseX_xwhile
    | with_reducible apply inputBaseX_xwhileBrk
    | with_reducible apply inputBaseX_xloopBrk
    | with_reducible apply inputBaseX_ite
    | with_reducible refine inputBaseX_bind ?_ (fun _ => ?_)
    | rfl
    | split)


end Zlib.Inflate.Proofs
