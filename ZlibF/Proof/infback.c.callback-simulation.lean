import ZlibF.Proof.«infback.c.back»
import ZlibF.Proof.«inflate.c.register-frame»

/-! Simulating the value callback interface when its callbacks are adapted to the C ABI.
All ordinary registers and the heap agree. The private cursor cell may be updated. -/
namespace Zlib.Infback.CallbackSimulation
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback.Proofs
set_option autoImplicit false

def Sim {α : Type} (P : PointerLocals → Prop) (addressed value : X α) : Prop :=
  ∀ l cs h res regs H, P cs → runX value l h = .ok ((res,regs),H) →
    ∃ after, P after ∧ runX addressed {l with pointerLocals := cs} h = .ok ((res,{regs with pointerLocals := after}),H)

theorem simPure {α : Type} (P : PointerLocals → Prop) (a : α) : Sim P (pure a) (pure a) := by
  intro l cs h res regs H ok run
  cases run
  exact ⟨cs,ok,rfl⟩

theorem simThrow {α : Type} (P : PointerLocals → Prop) (e : Ex) : Sim (α := α) P (throw e) (throw e) := by
  intro l cs h res regs H ok run
  cases run
  exact ⟨cs,ok,rfl⟩

theorem simLift {α : Type} (P : PointerLocals → Prop) (m : M α) : Sim P (liftM m) (liftM m) := by
  intro l cs h res regs H ok run
  rw [runX_lift] at run
  cases call : m h with
  | error e => rw [call] at run; cases run
  | ok p =>
    obtain ⟨a,G⟩ := p
    rw [call] at run; cases run
    exact ⟨cs,ok,by rw [runX_lift_ok call]⟩

theorem simSet {P : PointerLocals → Prop} (addressed value : IL)
    (fields : addressed = {value with pointerLocals := addressed.pointerLocals}) (ok : P addressed.pointerLocals) :
    Sim P (set addressed : X Unit) (set value) := by
  intro b before h res regs H _ run
  cases run
  exact ⟨addressed.pointerLocals,ok,by change Except.ok ((Except.ok (),addressed),h) = _; rw [← fields]⟩

theorem simModify {P : PointerLocals → Prop} (f g : IL → IL)
    (same : ∀ l cs, P cs → f {l with pointerLocals := cs} = {g l with pointerLocals := cs}) :
    Sim P (modify f : X Unit) (modify g) := by
  intro l cs h res regs H valid run
  cases run
  exact ⟨cs,valid,by rw [runX_modify,same l cs valid]⟩

theorem simBind {α β : Type} {P : PointerLocals → Prop} {x y : X α} {k j : α → X β}
    (first : Sim P x y) (next : ∀ a, Sim P (k a) (j a)) : Sim P (x >>= k) (y >>= j) := by
  intro l cs h res regs H ok run
  rw [runX_bind] at run
  cases before : runX y l h with
  | error e => rw [before] at run; cases run
  | ok p =>
    obtain ⟨⟨v,b⟩,G⟩ := p
    obtain ⟨newCs,valid,other⟩ := first _ _ _ _ _ _ ok before
    rw [before] at run
    cases v with
    | error e => cases run; exact ⟨newCs,valid,by rw [runX_bind,other]⟩
    | ok a =>
      obtain ⟨last,kept,tail⟩ := next a _ _ _ _ _ _ valid run
      exact ⟨last,kept,by rw [runX_bind,other]; exact tail⟩

theorem simGetBind {α : Type} {P : PointerLocals → Prop} {f g : IL → X α}
    (body : ∀ l cs, P cs → Sim P (f {l with pointerLocals := cs}) (g l)) :
    Sim P (get >>= f) (get >>= g) := by
  intro l cs h res regs H ok run
  rw [runX_bind,runX_get] at run
  obtain ⟨after,valid,other⟩ := body l cs ok _ _ _ _ _ _ ok run
  exact ⟨after,valid,by rw [runX_bind,runX_get]; exact other⟩

theorem simIf {α : Type} {P : PointerLocals → Prop} {c : Prop} [Decidable c] {x y u v : X α}
    (yes : Sim P x y) (no : Sim P u v) : Sim P (if c then x else u) (if c then y else v) := by
  split <;> assumption

private def Flow (cond : X Bool) : IL × Stop → M (Bool × (IL × Stop)) := fun (l,s) =>
  match s with
  | .go => do
    let (v,l') ← runX cond l
    pure (match v with | .ok b => (b,(l',.go)) | .error e => (false,(l',.ex e)))
  | other => pure (false,(l,other))

private def Trip (body : X Bool) : IL × Stop → M (IL × Stop) := fun (l,_) => do
  let (v,l') ← runX body l
  pure (match v with | .ok b => (l',if b then .brk else .go) | .error e => (l',.ex e))

private def withCells (state : IL × Stop) (cs : PointerLocals) : IL × Stop :=
  ({state.1 with pointerLocals := cs},state.2)

private theorem flowSim {P : PointerLocals → Prop} {x y : X Bool} (step : Sim P x y)
    {l : IL × Stop} {cs : PointerLocals} {h H : Heap} {next : IL × Stop} {test : Bool}
    (ok : P cs) (run : Flow y l h = .ok ((test,next),H)) :
    ∃ after, P after ∧ Flow x (withCells l cs) h = .ok ((test,withCells next after),H) := by
  obtain ⟨l,s⟩ := l
  cases s with
  | go =>
    simp only [Flow,bind_app] at run
    cases call : runX y l h with
    | error e => rw [call] at run; cases run
    | ok p =>
      obtain ⟨⟨v,b⟩,G⟩ := p
      obtain ⟨c,valid,other⟩ := step _ _ _ _ _ _ ok call
      rw [call] at run
      cases v <;> cases run <;> exact ⟨c,valid,by simp only [withCells,Flow,bind_app,other]; rfl⟩
  | brk => cases run; exact ⟨cs,ok,rfl⟩
  | ex e => cases run; exact ⟨cs,ok,rfl⟩

private theorem tripSim {P : PointerLocals → Prop} {x y : X Bool} (step : Sim P x y)
    {l : IL × Stop} {cs : PointerLocals} {h H : Heap} {next : IL × Stop}
    (ok : P cs) (run : Trip y l h = .ok (next,H)) :
    ∃ after, P after ∧ Trip x (withCells l cs) h = .ok (withCells next after,H) := by
  obtain ⟨l,s⟩ := l
  simp only [Trip,bind_app] at run
  cases call : runX y l h with
  | error e => rw [call] at run; cases run
  | ok p =>
    obtain ⟨⟨v,b⟩,G⟩ := p
    obtain ⟨c,valid,other⟩ := step _ _ _ _ _ _ ok call
    rw [call] at run
    cases v <;> cases run <;> exact ⟨c,valid,by simp only [withCells,Trip,bind_app,other]; rfl⟩

theorem simWhileBrk {P : PointerLocals → Prop} {c d x y : X Bool}
    (test : Sim P c d) (body : Sim P x y) : Sim P (xwhileBrk c x) (xwhileBrk d y) := by
  have loop : ∀ n l cs h next H, P cs → cwhile.go (Flow d) (Trip y) n l h = .ok (next,H) →
      ∃ after, P after ∧ cwhile.go (Flow c) (Trip x) n (withCells l cs) h = .ok (withCells next after,H) := by
    intro n
    induction n with
    | zero => intro _ _ _ _ _ _ run; cases run
    | succ n ih =>
      intro l cs h next H ok run
      rw [cwhile.go, bind_app] at run
      cases check : Flow d l h with
      | error e => rw [check] at run; cases run
      | ok p =>
        obtain ⟨⟨b,reg⟩,G⟩ := p
        obtain ⟨cs₁,one,check'⟩ := flowSim test ok check
        rw [check] at run
        cases b with
        | false => cases run; exact ⟨cs₁,one,by rw [cwhile.go,bind_ok check']; rfl⟩
        | true =>
          change (Trip y reg >>= cwhile.go (Flow d) (Trip y) n) G = _ at run
          rw [bind_app] at run
          cases oneRun : Trip y reg G with
          | error e => rw [oneRun] at run; cases run
          | ok p =>
            obtain ⟨reg₂,G₂⟩ := p
            obtain ⟨cs₂,two,step⟩ := tripSim body one oneRun
            rw [oneRun] at run
            obtain ⟨cs₃,three,tail⟩ := ih _ _ _ _ _ two run
            refine ⟨cs₃,three,?_⟩
            rw [cwhile.go,bind_ok check']
            exact (bind_ok step).trans tail
  intro l cs h res regs H ok run
  change (do let (r,s) ← cwhile (Flow d) (Trip y) (l,Stop.go); pure _) h = _ at run
  rw [bind_app] at run
  cases executed : cwhile (Flow d) (Trip y) (l,Stop.go) h with
  | error e => rw [executed] at run; cases run
  | ok p =>
    obtain ⟨⟨last,s⟩,G⟩ := p
    obtain ⟨cs',valid,same⟩ := loop fuel (l,Stop.go) cs h _ _ ok executed
    change cwhile (Flow c) (Trip x) ({l with pointerLocals := cs},Stop.go) h = .ok (({last with pointerLocals := cs'},s),G) at same
    rw [executed] at run
    refine ⟨cs',valid,?_⟩
    change (do let (r,s) ← cwhile (Flow c) (Trip x) _; pure _) h = _
    rw [bind_ok same]
    cases s <;> cases run <;> rfl

theorem simWhile {P : PointerLocals → Prop} {x y : X Unit} {c d : X Bool}
    (test : Sim P c d) (body : Sim P x y) : Sim P (xwhile c x) (xwhile d y) :=
  simWhileBrk test (simBind body (fun _ => simPure P false))

theorem simDoWhile {P : PointerLocals → Prop} {x y : X Unit} {c d : X Bool}
    (body : Sim P x y) (test : Sim P c d) : Sim P (xdoWhile x c) (xdoWhile y d) :=
  simBind body fun _ => simWhile test body

theorem simLoopBrk {P : PointerLocals → Prop} {x y : X Bool}
    (body : Sim P x y) : Sim P (xloopBrk x) (xloopBrk y) := simWhileBrk (simPure P true) body

end Zlib.Infback.CallbackSimulation
