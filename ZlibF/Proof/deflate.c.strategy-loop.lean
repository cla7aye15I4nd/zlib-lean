import ZlibF.Zlib.«deflate_strategies.c»
import ZlibF.Proof.«deflate.c.base»

namespace Zlib.Deflate.StrategyLoop
open C Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem assocM {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= fun a => f a >>= g := by
  funext h
  simp only [bind_app]
  cases m h <;> rfl

theorem pure_bindM {α β : Type} (x : α) (k : α → M β) : (pure x >>= k) = k x := rfl

theorem wr_then_wr (s : DeflateStatePtr) (f g : DeflateState → DeflateState) :
    (wr s f >>= fun _ => wr s g) = wr s (fun d => g (f d)) := by
  funext h
  cases s with
  | none => rfl
  | some r =>
    cases r with
    | tab i =>
      cases e : h.dstates i with
      | none => simp [wr, ldDeflateState, bind_app, DeflateStateRef.get, e]
      | some d =>
        have put (v : DeflateState) : stDeflateState (some (.tab i)) v h = .ok ((),setD h i v) := stDeflateState_tab e
        have again : stDeflateState (some (.tab i)) (g (f d)) (setD h i (f d)) =
            .ok ((),setD (setD h i (f d)) i (g (f d))) := stDeflateState_tab (setD_dstates_same ..)
        simp only [wr, bind_app, ldDeflateState_tab e, put, ldDeflateState_tab (setD_dstates_same ..),
          again, setD_setD]

theorem wr_cursor (s : DeflateStatePtr) {α : Type} (k : Unit → M α) :
    (wr s (fun d => {d with lookahead := d.lookahead - 1}) >>= fun _ =>
      wr s (fun d => {d with strstart := d.strstart + 1}) >>= k) =
    wr s (fun d => {d with lookahead := d.lookahead - 1, strstart := d.strstart + 1}) >>= k := by
  rw [← assocM, wr_then_wr]

/-- The three history fields reset by a full flush occupy the same live state record. -/
theorem wr_reset_history_then {α : Type} (s : DeflateStatePtr) (k : Unit → M α) :
    (wr s (fun d => { d with strstart := 0 }) >>= fun _ =>
      wr s (fun d => { d with block_start := 0 }) >>= fun _ =>
      wr s (fun d => { d with insert := 0 }) >>= k) =
    (wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 }) >>= k) := by
  rw [← assocM, wr_then_wr, ← assocM, wr_then_wr]

def Sim {α β : Type} (R : α → β → Prop) (a : M α) (b : M β) : Prop :=
  ∀ h, match a h with
    | .error e => b h = .error e
    | .ok (u, h') => ∃ v, b h = .ok (v, h') ∧ R u v

theorem Sim.bind {α β γ : Type} {R : α → β → Prop} (m : M γ) {f : γ → M α} {g : γ → M β}
    (each : ∀ x, Sim R (f x) (g x)) : Sim R (m >>= f) (m >>= g) := by
  intro h
  simp only [bind_app]
  cases m h with
  | error e => rfl
  | ok pair => rcases pair with ⟨x,h'⟩; exact each x h'

theorem Sim.pure {α β : Type} {R : α → β → Prop} {u : α} {v : β}
    (rel : R u v) : Sim R (pure u) (pure v) := fun _ => ⟨v,rfl,rel⟩

def pack (b : Bool) : LoopS := {bflush := b}

def Corresponds : LoopStep Bool block_state → LoopS → Prop
  | .next b, st | .cont b, st => st = pack b
  | .brk _, st => st.ret = none ∧ st.brk = true
  | .ret r, st => st.ret = some r

theorem finish_eq (s : DeflateStatePtr) (flush : Int32) :
    finishSymbolBlock s flush = (do
      wr s (fun d => { d with insert := 0 })
      finish_tail s flush) := by
  simp only [finishSymbolBlock, finish_tail, FLUSH_BLOCK, rd, zrd, assocM, pure_bindM]
  repeat' first
    | rfl
    | apply congrArg (Bind.bind _); funext _
    | split
    | simp only [assocM, pure_bindM, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

private def legacyTail (s : DeflateStatePtr) (flush : Int32) (st : LoopS) : M block_state := do
  if let some r := st.ret then return r
  wr s (fun d => {d with insert := 0})
  finish_tail s flush

/-- The flag loop spends one step testing its condition after a break or return. -/
def legacy (s : DeflateStatePtr) (flush : Int32) (body : LoopS → M LoopS) (n : Nat) : M block_state :=
  cwhile.go forever body n {} >>= legacyTail s flush

variable (s : DeflateStatePtr) (flush : Int32)
variable (step : Bool → M (LoopStep Bool block_state)) (body : LoopS → M LoopS)
variable (step_sim : ∀ b, Sim Corresponds (step b) (body (pack b)))
include step_sim

theorem eq_of_not_outOfFuel (h : Heap)
    (defined : legacy s flush body fuel h ≠ .error .outOfFuel) :
    cforEverRet step false (fun _ => finishSymbolBlock s flush) h = legacy s flush body fuel h := by
  apply cforEverRet_eq_cwhile_of_nofuel (proj := pack)
    (IsBrk := fun st _ => st.ret = none ∧ st.brk = true)
    (IsRet := fun st r => st.ret = some r) (tail' := legacyTail s flush)
  · intros; rfl
  · intro b h0
    have sim := step_sim b h0
    cases e : step b h0 with
    | error err => simpa [Sim, e] using sim
    | ok p =>
      rcases p with ⟨out,h'⟩
      obtain ⟨st, run, rel⟩ := (show ∃ st, body (pack b) h0 = .ok (st,h') ∧
          Corresponds out st by simpa [Sim,e] using sim)
      cases out with
      | next b' | cont b' => subst st; exact run
      | brk b' | ret b' => exact ⟨st,run,rel⟩
  · rintro st _ _ ⟨_,brk⟩; simp [forever, brk, pure_app]
  · intro st r _ ret; simp [forever, ret, pure_app]
  · rintro st b h' ⟨ret,_⟩; simp only [legacyTail,ret,finish_eq]
  · intro st r h' ret; simp [legacyTail,ret,pure_app]
  · exact defined

private def ExitRel : Except block_state Bool → LoopS → Prop
  | .error r, st => st.ret = some r
  | .ok _, st => st.ret = none ∧ st.brk = true

private theorem loop_exit (n : Nat) (b : Bool) {h h' : Heap}
    {u : Except block_state Bool} (run : cforEver.go step n b h = .ok (u,h')) :
    ∃ st, cwhile.go forever body (n+1) (pack b) h = .ok (st,h') ∧ ExitRel u st := by
  induction n generalizing b h with
  | zero => cases run
  | succ n ih =>
    rw [cforEver.go, bind_app] at run
    cases step : step b h with
    | error e => rw [step] at run; cases run
    | ok p =>
      rcases p with ⟨out,h1⟩
      obtain ⟨st,prev,rel⟩ := (show ∃ st, body (pack b) h = .ok (st,h1) ∧
        Corresponds out st by simpa [Sim,step] using step_sim b h)
      rw [step] at run
      rw [cwhile.go]
      have cond : forever (pack b) h = .ok ((true,pack b),h) := rfl
      simp only [bind_app,cond,ite_true,prev]
      cases out with
      | next x | cont x =>
        subst st
        exact ih x run
      | ret r =>
        cases run
        exact ⟨st,by simp [cwhile.go,forever,bind_app,pure_app,show st.ret = some r from rel],rel⟩
      | brk x =>
        cases run
        exact ⟨st,by simp [cwhile.go,forever,bind_app,pure_app,show st.brk = true from rel.2],rel⟩

/-- Any successful native-shaped run is also a run of the flag loop given its final condition test. -/
theorem to_legacy_ok {h after : Heap} {result : block_state}
    (run : cforEverRet step false (fun _ => finishSymbolBlock s flush) h = .ok (result,after)) :
    legacy s flush body (fuel+1) h = .ok (result,after) := by
  change (cforEver.go step fuel false >>= _) h = _ at run
  rw [bind_app] at run
  cases e : cforEver.go step fuel false h with
  | error err => rw [e] at run; cases run
  | ok p =>
    rcases p with ⟨u,h'⟩
    obtain ⟨st,prev,rel⟩ := loop_exit step body step_sim fuel false e
    rw [e] at run
    change (cwhile.go forever body (fuel+1) (pack false) >>= _) h = _
    rw [bind_app,prev]
    cases u with
    | error r => simpa [legacyTail,show st.ret = some r from rel] using run
    | ok b => simpa [legacyTail,show st.ret = none from rel.1,finish_eq] using run

end Zlib.Deflate.StrategyLoop
