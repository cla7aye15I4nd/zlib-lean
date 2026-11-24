import ZlibF.Proof.«inflate.c.exit-codes»
import ZlibF.Proof.«inflate.c.main.macros»

/-! # Register invariants across decoder loops and their exits -/
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

def RegisterFrame {α : Type} (invariant : IL → Prop) (program : X α) : Prop :=
  ∀ l h result regs after, invariant l →
    runX program l h = .ok ((result, regs), after) → invariant regs

theorem registerFrame_pure {α : Type} (invariant : IL → Prop) (value : α) : RegisterFrame invariant (pure value) := by
  intro l h result regs after current run
  cases run
  exact current

theorem registerFrame_get (invariant : IL → Prop) : RegisterFrame invariant (get : X IL) := by
  intro l h result regs after current run
  cases run
  exact current

theorem registerFrame_set (invariant : IL → Prop) (l : IL) (current : invariant l) :
    RegisterFrame invariant (set l : X Unit) := by
  intro before h result regs after _ run
  cases run
  exact current

theorem registerFrame_modify (invariant : IL → Prop) (update : IL → IL)
    (fixed : ∀ l, invariant l → invariant (update l)) :
    RegisterFrame invariant (modify update : X Unit) := by
  intro l h result regs after current run
  cases run
  exact fixed l current

theorem registerFrame_lift {α : Type} (invariant : IL → Prop) (program : M α) :
    RegisterFrame invariant (monadLift program : X α) := by
  intro l h result regs after current run
  rw [runX_lift] at run
  cases source : program h with
  | error fault => simp only [source] at run; cases run
  | ok pair =>
    obtain ⟨value, heap1⟩ := pair
    simp only [source] at run
    cases run
    exact current

theorem registerFrame_throw {α : Type} (invariant : IL → Prop) (exit : Ex) :
    RegisterFrame invariant (throw exit : X α) := by
  intro l h result regs after current run
  cases run
  exact current

theorem registerFrame_bind {α β : Type} {invariant : IL → Prop} {first : X α} {next : α → X β}
    (hf : RegisterFrame invariant first) (hn : ∀ value, RegisterFrame invariant (next value)) :
    RegisterFrame invariant (first >>= next) := by
  intro l h result regs after current run
  rw [runX_bind] at run
  cases firstRun : runX first l h with
  | error fault => rw [firstRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨decision, middleRegs⟩, middleHeap⟩ := pair
    rw [firstRun] at run
    have middle := hf _ _ _ _ _ current firstRun
    cases decision with
    | error exit => cases run; exact middle
    | ok value => exact hn value _ _ _ _ _ middle run

/-- A register snapshot satisfies the invariant at the point where it is taken. -/
theorem registerFrame_get_bind {α : Type} {invariant : IL → Prop} {next : IL → X α}
    (body : ∀ l, invariant l → RegisterFrame invariant (next l)) :
    RegisterFrame invariant (get >>= next) := by
  intro l h result regs after current run
  rw [runX_bind, runX_get] at run
  exact body l current _ _ _ _ _ current run

theorem registerFrame_ite {α : Type} {invariant : IL → Prop} {test : Prop} [Decidable test] {yes no : X α}
    (hy : RegisterFrame invariant yes) (hn : RegisterFrame invariant no) : RegisterFrame invariant (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

theorem registerFrame_xwhileBrk {invariant : IL → Prop} {cond body : X Bool}
    (hc : RegisterFrame invariant cond) (hb : RegisterFrame invariant body) : RegisterFrame invariant (xwhileBrk cond body) := by
  intro l h result regs after current run
  let P := fun (state : IL × Stop) (_heap : Heap) => invariant state.1
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (outcome, next) ← runX cond current.1
      pure (match outcome with
        | .ok value => (value, (next, Stop.go))
        | .error exit => (false, (next, Stop.ex exit)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (outcome, next) ← runX body current.1
    pure (match outcome with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error exit => (next, Stop.ex exit))
  have condInv : ∀ state h test next after, P state h →
      loopCond state h = .ok ((test, next), after) → P next after := by
    intro ⟨state, stop⟩ h test next after stateP executed
    cases stop with
    | go =>
      change (do let (outcome, next) ← runX cond state; pure _) h = _ at executed
      rw [bind_app] at executed
      cases source : runX cond state h with
      | error fault => rw [source] at executed; cases executed
      | ok pair =>
        obtain ⟨⟨outcome, nextRegs⟩, heap1⟩ := pair
        rw [source] at executed
        have fixed := hc _ _ _ _ _ stateP source
        cases outcome <;> cases executed <;> exact fixed
    | brk => cases executed; exact stateP
    | ex exit => cases executed; exact stateP
  have bodyInv : ∀ state h next after, P state h →
      loopBody state h = .ok (next, after) → P next after := by
    intro ⟨state, stop⟩ h next after stateP executed
    change (do let (outcome, next) ← runX body state; pure _) h = _ at executed
    rw [bind_app] at executed
    cases source : runX body state h with
    | error fault => rw [source] at executed; cases executed
    | ok pair =>
      obtain ⟨⟨outcome, nextRegs⟩, heap1⟩ := pair
      rw [source] at executed
      have fixed := hb _ _ _ _ _ stateP source
      cases outcome <;> cases executed <;> exact fixed
  unfold xwhileBrk runX at run
  change (do let (next, stop) ← cwhile loopCond loopBody (l, Stop.go); pure _) h = _ at run
  rw [bind_app] at run
  cases source : cwhile loopCond loopBody (l, Stop.go) h with
  | error fault => rw [source] at run; cases run
  | ok pair =>
    obtain ⟨⟨nextRegs, stop⟩, heap1⟩ := pair
    rw [source] at run
    have fixed := cwhile_success_invariant P condInv bodyInv current source
    cases stop <;> cases run <;> exact fixed

theorem registerFrame_xwhile {invariant : IL → Prop} {cond : X Bool} {body : X Unit}
    (hc : RegisterFrame invariant cond) (hb : RegisterFrame invariant body) : RegisterFrame invariant (xwhile cond body) :=
  registerFrame_xwhileBrk hc (registerFrame_bind hb (fun _ => registerFrame_pure invariant false))

theorem registerFrame_xdoWhile {invariant : IL → Prop} {body : X Unit} {cond : X Bool}
    (hb : RegisterFrame invariant body) (hc : RegisterFrame invariant cond) : RegisterFrame invariant (xdoWhile body cond) := by
  unfold xdoWhile
  exact registerFrame_bind hb (fun _ => registerFrame_xwhile hc hb)

theorem registerFrame_xloopBrk {invariant : IL → Prop} {body : X Bool} (hb : RegisterFrame invariant body) :
    RegisterFrame invariant (xloopBrk body) := registerFrame_xwhileBrk (registerFrame_pure invariant true) hb

macro "register_frame_source" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact registerFrame_pure _ _
    | with_reducible exact registerFrame_get _
    | with_reducible exact registerFrame_lift _ _
    | with_reducible exact registerFrame_throw _ _
    | with_reducible refine registerFrame_set _ _ ?_
    | with_reducible refine registerFrame_modify _ _ (fun _ fixed => ?_)
    | with_reducible refine registerFrame_get_bind (fun _ fixed => ?_)
    | with_reducible apply registerFrame_xdoWhile
    | with_reducible apply registerFrame_xwhile
    | with_reducible apply registerFrame_xwhileBrk
    | with_reducible apply registerFrame_xloopBrk
    | with_reducible apply registerFrame_ite
    | with_reducible refine registerFrame_bind ?_ (fun _ => ?_)
    | rfl
    | split)

end Zlib.Inflate.Proofs
