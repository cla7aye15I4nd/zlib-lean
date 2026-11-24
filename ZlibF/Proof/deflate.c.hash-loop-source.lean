import ZlibF.Proof.«deflate.c.strategy-loop»
import ZlibF.Proof.«deflate.c.universal-params-publish»

/-! Transfer successful iterations of the flag-based fast and slow compression loops to their C control flow. -/

namespace Zlib.Deflate.HashLoop
open C Zlib.Deflate.Proofs StrategyLoop
set_option autoImplicit false

/-- Relate returning computations, including their complete resulting heaps. -/
private def Forward {α β : Type} (R : α → β → Prop) (old : M α) (src : M β) : Prop :=
  ∀ h a after, old h = .ok (a,after) → ∃ b, src h = .ok (b,after) ∧ R a b

private theorem Forward.bind {α β γ : Type} {R : α → β → Prop} (m : M γ)
    {f : γ → M α} {g : γ → M β} (each : ∀ x, Forward R (f x) (g x)) :
    Forward R (m >>= f) (m >>= g) := by
  intro h a after run
  simp only [bind_app] at run ⊢
  rcases eq : m h with fault | ⟨x,h1⟩ <;> simp only [eq] at run ⊢
  · cases run
  · exact each x h1 a after run

private theorem Forward.convertBind {α β γ : Type} {R : α → β → Prop} {m m' : M γ}
    (convert : ∀ h x after, m h = .ok (x,after) → m' h = .ok (x,after))
    {f : γ → M α} {g : γ → M β} (each : ∀ x, Forward R (f x) (g x)) :
    Forward R (m >>= f) (m' >>= g) := by
  intro h a after run
  rw [bind_app] at run
  rcases eq : m h with fault | ⟨x,h1⟩ <;> simp only [eq] at run
  · cases run
  · simp only [bind_app,convert h x h1 eq]
    exact each x h1 a after run

private theorem Forward.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β}
    (rel : R a b) : Forward R (pure a) (pure b) := by
  rintro h _ _ eq
  cases eq
  exact ⟨b,rfl,rel⟩

private theorem doWhile_ok {α : Type} {old src : α → M α}
    (each : ∀ a h b after, old a h = .ok (b,after) → src a h = .ok (b,after))
    (cond : α → M (Bool × α)) (n : Nat) (a : α) {h after : Heap} {b : α}
    (run : cdoWhile.go old cond n a h = .ok (b,after)) :
    cdoWhile.go src cond n a h = .ok (b,after) := by
  induction n generalizing a h with
  | zero => cases run
  | succ n ih =>
    simp only [cdoWhile.go, bind_app] at run ⊢
    rcases e : old a h with fault | ⟨v,h1⟩ <;> rw [e] at run
    · cases run
    rw [each a h v h1 e]
    rcases c : cond v h1 with fault | ⟨⟨test,v'⟩,h2⟩ <;> simp only [c] at run ⊢
    · cases run
    cases test
    · exact run
    · exact ih v' run

private def pack (p : UInt32 × Bool) : LoopS := { hash_head := p.1, bflush := p.2 }
private def StepRel (st : LoopS) : LoopStep (UInt32 × Bool) block_state → Prop
  | .next p | .cont p => st = pack p
  | .brk _ => st.ret = none ∧ st.brk = true
  | .ret r => st.ret = some r

private def ExitRel (st : LoopS) : Except block_state (UInt32 × Bool) → Prop
  | .ok _ => st.ret = none ∧ st.brk = true
  | .error r => st.ret = some r

private theorem from_loop {old : LoopS → M LoopS} {src : (UInt32 × Bool) → M (LoopStep (UInt32 × Bool) block_state)}
    (each : ∀ p, Forward StepRel (old (pack p)) (src p))
    (n : Nat) (p : UInt32 × Bool) {h after : Heap} {st : LoopS}
    (run : cwhile.go forever old n (pack p) h = .ok (st,after)) :
    ∃ outcome, cforEver.go src n p h = .ok (outcome,after) ∧ ExitRel st outcome := by
  induction n generalizing p h with
  | zero => cases run
  | succ n ih =>
    have cond : forever (pack p) h = .ok ((true,pack p),h) := rfl
    simp only [cwhile.go, bind_app,cond,ite_true] at run
    rcases e : old (pack p) h with fault | ⟨v,h1⟩ <;> rw [e] at run
    · cases run
    obtain ⟨out,eq,rel⟩ := each p h v h1 e
    simp only [cforEver.go, bind_app,eq]
    cases out with
    | next p' | cont p' => subst v; exact ih p' run
    | brk p' =>
      cases n with
      | zero => cases run
      | succ k =>
        have done_ : forever v h1 = .ok ((false,v),h1) := by simp [forever,show v.brk = true from rel.2,pure_app]
        simp only [cwhile.go, bind_app,done_,Bool.false_eq_true,ite_false,pure_app] at run
        cases run
        exact ⟨_,rfl,rel⟩
    | ret r =>
      cases n with
      | zero => cases run
      | succ k =>
        have done_ : forever v h1 = .ok ((false,v),h1) := by simp [forever,show v.ret = some r from rel,pure_app]
        simp only [cwhile.go,bind_app,done_,Bool.false_eq_true,ite_false,pure_app] at run
        cases run
        exact ⟨_,rfl,rel⟩

theorem _root_.Zlib.Deflate.SlowProofs.finish_hash_eq (s : DeflateStatePtr) (flush : Int32) :
    finishHashBlock s flush = (do
      wr s (fun d => { d with insert := if d.strstart < MIN_MATCH_u - 1 then d.strstart else MIN_MATCH_u - 1 })
      finish_tail s flush) := by
  simp only [finishHashBlock, finish_tail, FLUSH_BLOCK, rd, zrd, assocM, pure_bindM]
  repeat' first
    | rfl
    | apply congrArg (Bind.bind _); funext _
    | split
    | simp only [assocM, pure_bindM, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

private theorem wr_pair {α : Type} (s : DeflateStatePtr) (f g : DeflateState → DeflateState) (k : Unit → M α) :
    (wr s f >>= fun _ => wr s g >>= k) = wr s (fun d => g (f d)) >>= k := by
  rw [← assocM, wr_then_wr]

private theorem read_write {α : Type} (s : DeflateStatePtr) (f : DeflateState → DeflateState → DeflateState)
    (k : Unit → M α) :
    (ldDeflateState s >>= fun d => wr s (f d) >>= k) = wr s (fun d => f d d) >>= k := by
  funext h
  cases s with
  | none => rfl
  | some r =>
    cases r with
    | tab i =>
      cases e : h.dstates i with
      | none => simp [ldDeflateState, wr, bind_app, DeflateStateRef.get,e]
      | some d => simp only [wr,bind_app,ldDeflateState_tab e]

private theorem inner_ok (s : DeflateStatePtr) (bound hh : UInt32) :
    ∀ h x after, (do
      wr s (fun d => {d with strstart := d.strstart + 1})
      let d ← ldDeflateState s
      if d.strstart ≤ bound then INSERT_STRING s d.strstart else pure hh) h = .ok (x,after) →
      (do
      wr s (fun d => {d with strstart := d.strstart + 1})
      let d ← ldDeflateState s
      if d.strstart ≤ bound then insertStringAt s d.strstart else pure hh) h = .ok (x,after) := by
  intro h x after run
  simp only [bind_app] at run ⊢
  rcases e : wr s _ h with fault | ⟨u,h1⟩ <;> simp only [e] at run ⊢
  · cases run
  rcases e : ldDeflateState s h1 with fault | ⟨d,h2⟩ <;> simp only [e] at run ⊢
  · cases run
  by_cases c : d.strstart ≤ bound <;> simp only [c,↓reduceIte] at run ⊢
  · exact (HashOrder.insertStringAt_ok_iff ..).2 run
  · exact run

private theorem forward_ite {α β : Type} {R : α → β → Prop} {a₁ a₂ : M α} {b₁ b₂ : M β}
    {c : Prop} [Decidable c] (left : Forward R a₁ b₁) (right : Forward R a₂ b₂) :
    Forward R (if c then a₁ else a₂) (if c then b₁ else b₂) := by split <;> assumption

open Zlib.Deflate.Universal.Params

private def AtHeap {α β : Type} (P : Heap → Prop) (R : α → β → Prop) (old : M α) (src : M β) : Prop :=
  ∀ h, P h → ∀ a after, old h = .ok (a,after) → ∃ b, src h = .ok (b,after) ∧ R a b

private def HasState (s : DeflateStatePtr) (d : DeflateState) (h : Heap) : Prop :=
  ldDeflateState s h = .ok (d,h)
private def HasStream (s : DeflateStatePtr) (d : DeflateState) (h : Heap) : Prop :=
  ∃ d', HasState s d' h ∧ d'.strm = d.strm

private theorem snapshot {α β : Type} {R : α → β → Prop} (s : DeflateStatePtr)
    {f : DeflateState → M α} {g : DeflateState → M β}
    (each : ∀ d, AtHeap (HasState s d) R (f d) (g d)) :
    Forward R (ldDeflateState s >>= f) (ldDeflateState s >>= g) := by
  intro h a after
  cases s with
  | none => intro run; cases run
  | some r =>
    cases e : r.get h with
    | none => simp [bind_app,ldDeflateState,e]
    | some d => simp only [bind_app,ldDeflateState_ok e]; exact each d h (ldDeflateState_ok e) a after

private theorem at_free {α β : Type} {P : Heap → Prop} {R : α → β → Prop} {m : M α} {n : M β}
    (all_ : Forward R m n) : AtHeap P R m n := fun h _ => all_ h

private theorem at_ite {α β : Type} {P : Heap → Prop} {R : α → β → Prop} {a₁ a₂ : M α} {b₁ b₂ : M β}
    {c : Prop} [Decidable c] (left : AtHeap P R a₁ b₁) (right : AtHeap P R a₂ b₂) :
    AtHeap P R (if c then a₁ else a₂) (if c then b₁ else b₂) := by split <;> assumption

private theorem fromState {α β : Type} {R : α → β → Prop} {s : DeflateStatePtr} {d : DeflateState}
    {m : M α} {n : M β} (all_ : AtHeap (HasStream s d) R m n) :
    AtHeap (HasState s d) R m n := fun h e => all_ h ⟨d,e,rfl⟩

private theorem stateRight {α β : Type} {R : α → β → Prop} {s : DeflateStatePtr} {d : DeflateState}
    {m : M α} {g : DeflateState → M β} (next : AtHeap (HasState s d) R m (g d)) :
    AtHeap (HasState s d) R m (ldDeflateState s >>= g) := by
  intro h e
  simpa only [bind_app, show ldDeflateState s h = _ from e] using next h e

private theorem stateLeft {α β : Type} {R : α → β → Prop} {s : DeflateStatePtr} {d : DeflateState}
    {f : DeflateState → M α} {n : M β} (next : AtHeap (HasState s d) R (f d) n) :
    AtHeap (HasState s d) R (ldDeflateState s >>= f) n := by
  intro h e
  simpa only [bind_app,show ldDeflateState s h = _ from e] using next h e

private theorem keep_stream {s : DeflateStatePtr} {d : DeflateState} {h after : Heap}
    (known : HasStream s d h) (frame : ExactRel h after) : HasStream s d after := by
  obtain ⟨v, read, same⟩ := known
  cases s with
  | none => cases read
  | some r =>
    cases r with
    | tab i =>
      cases e : h.dstates i with
      | none => simp [HasState,ldDeflateState,DeflateStateRef.get,e] at read
      | some v0 =>
        have eq : v0 = v := by simpa only [HasState,ldDeflateState_tab e,Except.ok.injEq,Prod.mk.injEq,and_true] using read
        subst v0
        obtain ⟨v',get,fields⟩ := (ExactRel.par (keep := true) frame).1 i v e
        exact ⟨v',ldDeflateState_tab get,fields.strm.trans same⟩

private theorem streamBind {α β γ : Type} {R : α → β → Prop} {s : DeflateStatePtr} {d : DeflateState}
    (m : M γ) (keep : ExactM m) {f : γ → M α} {g : γ → M β}
    (each : ∀ x, AtHeap (HasStream s d) R (f x) (g x)) :
    AtHeap (HasStream s d) R (m >>= f) (m >>= g) := by
  intro h known a after run
  simp only [bind_app] at run ⊢
  rcases e : m h with fault | ⟨v,h1⟩ <;> simp only [e] at run ⊢
  · cases run
  · exact each v h1 (keep_stream known (keep h v h1 e)) a after run

private theorem streamCursor {α β : Type} {R : α → β → Prop} (s : DeflateStatePtr) (d : DeflateState)
    {f : Unit → M α} {g : Unit → M β} (each : ∀ x, AtHeap (HasStream s d) R (f x) (g x)) :
    AtHeap (HasStream s d) R
      (wr s (fun v => {v with strstart := v.strstart + 1, lookahead := v.lookahead - 1}) >>= f)
      (wr s (fun v => {v with strstart := v.strstart + 1, lookahead := v.lookahead - 1}) >>= g) :=
    streamBind _ (exact_wr s (fun v => {v with strstart := v.strstart + 1, lookahead := v.lookahead - 1}) (fun _ => rfl)) each

private theorem streamRead {α β : Type} {R : α → β → Prop} {s : DeflateStatePtr} {d : DeflateState}
    {f : ZStream → M α} {g : ZStream → M β} (each : ∀ z, Forward R (f z) (g z)) :
    AtHeap (HasStream s d) R (ldZStream d.strm >>= f)
      (ldDeflateState s >>= fun d' => ldZStream d'.strm >>= g) := by
  intro h known
  obtain ⟨v,eq,same⟩ := known
  simp only [bind_app,show ldDeflateState s h = _ from eq,same]
  simpa only [bind_app] using Forward.bind (ldZStream d.strm) each h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2400000 in
private theorem slow_step_sim (s : DeflateStatePtr) (flush : Int32) (p : UInt32 × Bool) :
    Forward StepRel (deflate_slow_body s flush (pack p)) (deflate_slow_step s flush p) := by
  unfold deflate_slow_body deflate_slow_step
  simp only [rd,zrd,assocM,pure_bindM,wr_pair,read_write]
  repeat' first
    | apply snapshot; intro d
    | apply at_ite
    | apply stateRight
    | apply stateLeft
    | apply fromState
    | apply streamRead; intro z
    | apply streamBind _ (exact_index8 _ _); intro v
    | apply streamBind _ (exact_tally_lit _ _); intro v
    | apply streamBind _ (exact_FLUSH_BLOCK_ONLY _ _); intro v
    | apply streamCursor; intro v
    | apply at_free
    | apply Forward.bind; intro x
    | apply Forward.convertBind (fun h x after => (HashOrder.insertStringAt_ok_iff _ _ h after x).2); intro x
    | apply Forward.convertBind (fun h x after => doWhile_ok (inner_ok s _) _ fuel _ (h := h) (after := after) (b := x)); intro x
    | apply forward_ite
    | exact Forward.pure rfl
    | exact Forward.pure ⟨rfl,rfl⟩
    | split

/-- An early return or break in a returning flag loop determines the native loop's
result and heap. Its final condition check costs no fuel in the native loop. -/
theorem _root_.Zlib.Deflate.SlowProofs.after_loop {s : DeflateStatePtr} {flush : Int32} {h after : Heap} {st : LoopS}
    (run : cwhile forever (deflate_slow_body s flush) {} h = .ok (st,after)) :
    deflate_slow s flush h = (match st.ret with
      | some r => pure r | none => slowFinish s flush) after := by
  obtain ⟨out,exec,rel⟩ := from_loop (slow_step_sim s flush) fuel (0,false) run
  change (cforEver.go (deflate_slow_step s flush) fuel (0,false) >>= _) h = _
  rw [bind_app,exec]
  cases out with
  | error r => rw [show st.ret = some r from rel]
  | ok p => rw [show st.ret = none from rel.1]

private theorem fast_inner_ok (s : DeflateStatePtr) (_ : UInt32) :
    ∀ h x after, (do
      wr s (fun d => { d with strstart := d.strstart + 1 })
      let d ← ldDeflateState s
      INSERT_STRING s d.strstart) h = .ok (x,after) →
      (do
      wr s (fun d => { d with strstart := d.strstart + 1 })
      let d ← ldDeflateState s
      insertStringAt s d.strstart) h = .ok (x,after) := by
  intro h x after run
  simp only [bind_app] at run ⊢
  rcases e : wr s _ h with fault | ⟨u,h1⟩ <;> simp only [e] at run ⊢
  · cases run
  rcases e : ldDeflateState s h1 with fault | ⟨d,h2⟩ <;> simp only [e] at run ⊢
  · cases run
  exact (HashOrder.insertStringAt_ok_iff ..).2 run

private theorem fast_hash_cont {α β : Type} {R : α → β → Prop} {s : DeflateStatePtr}
    {p : BPtr} {i : UInt32} {k : Unit → M α} {k' : Unit → M β}
    (next : ∀ u, Forward R (k u) (k' u)) :
    Forward R (index8 p i.toNat >>= fun c => UPDATE_HASH s c >>= k) (updateHashAt s p i >>= k') := by
  rw [← assocM]
  exact Forward.convertBind (fun h x after => (HashOrder.updateHashAt_ok_iff s p i h after x).2) next

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2400000 in
private theorem fast_step_sim (s : DeflateStatePtr) (flush : Int32) (p : UInt32 × Bool) :
    Forward StepRel (deflate_fast_body s flush (pack p)) (deflate_fast_step s flush p) := by
  unfold deflate_fast_body deflate_fast_step
  simp only [rd, assocM, pure_bindM, wr_pair, show ((0 : UInt32) != 0) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  repeat' first
    | apply snapshot; intro d
    | apply at_ite
    | apply stateRight
    | apply stateLeft
    | apply fromState
    | apply streamRead; intro z
    | apply streamBind _ (exact_index8 _ _); intro v
    | apply streamBind _ (exact_tally_lit _ _); intro v
    | apply streamBind _ (exact_FLUSH_BLOCK_ONLY _ _); intro v
    | apply streamCursor; intro v
    | apply at_free
    | apply Forward.bind; intro x
    | apply Forward.convertBind (fun h x after => (HashOrder.insertStringAt_ok_iff _ _ h after x).2); intro x
    | apply fast_hash_cont; intro u
    | apply Forward.convertBind (fun h x after => doWhile_ok (fast_inner_ok s) _ fuel _ (h := h) (after := after) (b := x)); intro x
    | apply forward_ite
    | exact Forward.pure rfl
    | exact Forward.pure ⟨rfl,rfl⟩
    | split

/-- A successful run of the flag-based fast loop determines the source loop’s return or its finishing path, including the entire heap. -/
theorem _root_.Zlib.Deflate.FastProofs.after_loop {s : DeflateStatePtr} {flush : Int32} {h after : Heap} {st : LoopS}
    (run : cwhile forever (deflate_fast_body s flush) {} h = .ok (st,after)) :
    deflate_fast s flush h = (match st.ret with
      | some r => pure r | none => finishHashBlock s flush) after := by
  obtain ⟨out,exec,rel⟩ := from_loop (fast_step_sim s flush) fuel (0,false) run
  change (cforEver.go (deflate_fast_step s flush) fuel (0,false) >>= _) h = _
  rw [bind_app,exec]
  cases out with
  | error r => rw [show st.ret = some r from rel]
  | ok p => rw [show st.ret = none from rel.1]

end Zlib.Deflate.HashLoop
