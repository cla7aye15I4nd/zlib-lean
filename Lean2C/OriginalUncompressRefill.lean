import Lean2C.OriginalUncompressMember

/-! Changing only the output address during input-side decoder operations. -/
namespace Lean2C.OriginalUncompress
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false

namespace Refill

def registers (p : BPtr) (l : IL) : IL := {l with put := p}

def heap (k : Nat) (p : BPtr) (h : Heap) : Heap :=
  {h with streams := match h.streams k with
    | none => h.streams
    | some z => upd h.streams k (some {z with next_out := p})}

def mapped {α : Type} (s : α → α) (H : Heap → Heap) (r : Except Fault (α × Heap)) :=
  r.map fun (a, h) => (s a, H h)

/-- The operation returns the same value or exception after replacing the
output address in the local registers and the automatic stream. -/
def Independent {α : Type} (k : Nat) (p : BPtr) (x : X α) : Prop :=
  ∀ l h, runX x (registers p l) (heap k p h) =
    mapped (fun (r, l') => (r, registers p l')) (heap k p) (runX x l h)

theorem memBind {α β : Type} {k : Nat} {p : BPtr} {a : M α} {f : α → M β}
    (first : ∀ h, a (heap k p h) = mapped id (heap k p) (a h))
    (next : ∀ v h, f v (heap k p h) = mapped id (heap k p) (f v h)) (h : Heap) :
    (a >>= f) (heap k p h) = mapped id (heap k p) ((a >>= f) h) := by
  simp only [bind_app, first h]
  rcases a h with e | ⟨v, H⟩
  · rfl
  · exact next v H

theorem while_map_on {α : Type} (I : α → Heap → Prop) (s : α → α) (H : Heap → Heap) (cond : α → M (Bool × α)) (body : α → M α)
    (hc : ∀ a h, I a h → cond (s a) (H h) = mapped (fun (b, a') => (b, s a')) H (cond a h))
    (hb : ∀ a h, I a h → body (s a) (H h) = mapped s H (body a h))
    (ct : ∀ a h b a' h', I a h → cond a h = .ok ((b, a'), h') → I a' h')
    (bt : ∀ a h a' h', I a h → body a h = .ok (a', h') → I a' h')
    (a : α) (h : Heap) (start : I a h) :
    cwhile cond body (s a) (H h) = mapped s H (cwhile cond body a h) := by
  unfold cwhile
  induction fuel generalizing a h with
  | zero => rfl
  | succ n ih =>
    rw [cwhile.go, cwhile.go]
    simp only [bind_app, hc a h start]
    cases e : cond a h with
    | error err => rfl
    | ok pair =>
      obtain ⟨⟨b, a'⟩, h'⟩ := pair
      cases b with
      | false => rfl
      | true =>
        change (match body (s a') (H h') with
          | .ok (v, g) => cwhile.go cond body n v g | .error e => .error e) =
            mapped s H (match body a' h' with
              | .ok (v, g) => cwhile.go cond body n v g | .error e => .error e)
        have middle := ct a h true a' h' start e
        rw [hb a' h' middle]
        cases step : body a' h' with
        | error e => rfl
        | ok pair =>
          obtain ⟨v, g⟩ := pair
          exact ih v g (bt _ _ _ _ middle step)

theorem while_map {α : Type} (s : α → α) (H : Heap → Heap) (cond : α → M (Bool × α)) (body : α → M α)
    (hc : ∀ a h, cond (s a) (H h) = mapped (fun (b, a') => (b, s a')) H (cond a h))
    (hb : ∀ a h, body (s a) (H h) = mapped s H (body a h)) (a : α) (h : Heap) :
    cwhile cond body (s a) (H h) = mapped s H (cwhile cond body a h) :=
  while_map_on (fun _ _ => True) s H cond body (fun a h _ => hc a h) (fun a h _ => hb a h)
    (by intros; trivial) (by intros; trivial) a h trivial

/-- Two executions of a decoder loop agree while the original execution
maintains the specified invariant on registers and the live heap. -/
theorem xloop_on {k : Nat} {p : BPtr} {cond body : X Bool} (I : IL → Heap → Prop)
    (hc : ∀ l h, I l h → runX cond (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX cond l h))
    (hb : ∀ l h, I l h → runX body (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX body l h))
    (ct : ∀ l h v regs after, I l h → runX cond l h = .ok ((v, regs), after) → I regs after)
    (bt : ∀ l h v regs after, I l h → runX body l h = .ok ((v, regs), after) → I regs after)
    (l : IL) (h : Heap) (start : I l h) :
    runX (xwhileBrk cond body) (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX (xwhileBrk cond body) l h) := by
  let S : IL × Stop → IL × Stop := fun (l, why) => (registers p l, why)
  let H := heap k p
  let test : IL × Stop → M (Bool × (IL × Stop)) := fun (l, why) => match why with
    | .go => do
      let (r, l') ← runX cond l
      pure (match r with | .ok b => (b, (l', .go)) | .error e => (false, (l', .ex e)))
    | why => pure (false, (l, why))
  let step : IL × Stop → M (IL × Stop) := fun (l, _) => do
    let (r, l') ← runX body l
    pure (match r with | .ok b => (l', if b then .brk else .go) | .error e => (l', .ex e))
  have testMap : ∀ a h, I a.1 h → test (S a) (H h) = mapped (fun (b, a') => (b, S a')) H (test a h) := by
    rintro ⟨l, why⟩ h inv
    cases why with
    | brk | ex => rfl
    | go =>
      simp only [test, S, H, bind_app, hc l h inv]
      rcases runX cond l h with e | ⟨⟨res, l'⟩, h'⟩
      · rfl
      · cases res <;> rfl
  have stepMap : ∀ a h, I a.1 h → step (S a) (H h) = mapped S H (step a h) := by
    rintro ⟨l, why⟩ h inv
    simp only [step, S, H, bind_app, hb l h inv]
    rcases runX body l h with e | ⟨⟨res, l'⟩, h'⟩
    · rfl
    · cases res <;> rfl
  have checkInv : ∀ (a : IL × Stop) g flag (v : IL × Stop) after, I a.1 g →
      test a g = .ok ((flag, v), after) → I v.1 after := by
    rintro ⟨regs, why⟩ g flag v after inv run
    cases why with
    | go =>
      simp only [test, bind_app] at run
      rcases baseline : runX cond regs g with e | ⟨⟨res, regs'⟩, g'⟩ <;> rw [baseline] at run
      · cases run
      · have holds := ct _ _ _ _ _ inv baseline
        cases res <;> cases run <;> exact holds
    | brk | ex => cases run; exact inv
  have stepInv : ∀ (a : IL × Stop) g (v : IL × Stop) after, I a.1 g →
      step a g = .ok (v, after) → I v.1 after := by
    rintro ⟨regs, why⟩ g v after inv run
    simp only [step, bind_app] at run
    rcases baseline : runX body regs g with e | ⟨⟨res, regs'⟩, g'⟩ <;> rw [baseline] at run
    · cases run
    · have holds := bt _ _ _ _ _ inv baseline
      cases res <;> cases run <;> exact holds
  have loop := while_map_on (fun a g => I a.1 g) S H test step testMap stepMap checkInv stepInv (l, .go) h start
  let finish : IL × Stop → M (Except Ex Unit × IL) := fun (l, why) => pure (match why with | .ex e => (.error e, l) | _ => (.ok (), l))
  have view (a : IL) (g : Heap) : runX (xwhileBrk cond body) a g = ((cwhile test step (a, .go)) >>= finish) g := rfl
  rw [view, view, bind_app, bind_app]
  dsimp only [S, H] at loop
  rw [loop]
  rcases cwhile test step (l, .go) h with err | ⟨⟨l', why⟩, g'⟩
  · rfl
  · cases why <;> rfl

private theorem xloop {k : Nat} {p : BPtr} {cond body : X Bool}
    (hc : Independent k p cond) (hb : Independent k p body) : Independent k p (xwhileBrk cond body) :=
  fun l h => xloop_on (fun _ _ => True) (fun a g _ => hc a g) (fun a g _ => hb a g)
    (by intros; trivial) (by intros; trivial) l h trivial

private theorem same_bytes (k : Nat) (p : BPtr) (h : Heap) (b : BRef) :
    (Space.get (heap k p h) b : Option (Array UInt8)) = Space.get h b := by
  cases b <;> rfl

private theorem read_byte (k : Nat) (p q : BPtr) (h : Heap) :
    load8 q (heap k p h) = mapped id (heap k p) (load8 q h) := by
  cases q with
  | null => rfl
  | ref b n =>
    simp only [load8, Ptr.load, same_bytes]
    cases Space.get h b with
    | none => rfl
    | some a => dsimp only; split <;> rfl

private theorem advance_byte (k : Nat) (p q : BPtr) (h : Heap) :
    q.add 1 (heap k p h) = mapped id (heap k p) (q.add 1 h) := by
  cases q with
  | null => rfl
  | ref b n =>
    simp only [Ptr.add, Int.one_ne_zero, ↓reduceIte, same_bytes]
    cases Space.get h b with
    | none => rfl
    | some a => dsimp only; split <;> rfl

private theorem shift_byte (k : Nat) (p : BPtr) (h : Heap) (v : UInt64) (n : UInt32) :
    shl64 v n (heap k p h) = mapped id (heap k p) (shl64 v n h) := by
  unfold shl64
  split <;> rfl

/-- Changing the output cursor does not affect even a faulting input-byte
load, pointer advance or shift. This applies to all input pointer views. -/
theorem pull (k : Nat) (p : BPtr) : Independent k p PULLBYTE := by
  intro l h
  by_cases empty : l.have_ = 0
  · rw [PULLBYTE_zero (l := registers p l) empty, PULLBYTE_zero empty]; rfl
  simp only [PULLBYTE, absorbInputByte, runX_bind, runX_get, registers, beq_false_of_ne empty,
    Bool.false_eq_true, ↓reduceIte, runX_lift, read_byte, runX_set]
  rcases load8 l.next h with e | ⟨b, g⟩
  · rfl
  simp only [mapped, Except.map, id_eq, advance_byte]
  rcases l.next.add 1 g with e | ⟨nx, g'⟩
  · rfl
  simp only [mapped, Except.map, id_eq, shift_byte]
  rcases shl64 b.toUInt64 l.bits g' with e | ⟨sh, g''⟩ <;> rfl

/-- Every iteration of NEEDBITS reads exactly the same input in both runs,
including premature exhaustion, invalid input and the loop fuel boundary. -/
theorem need_bits (k : Nat) (p : BPtr) (n : UInt32) : Independent k p (NEEDBITS n) := by
  unfold NEEDBITS xwhile
  apply xloop
  · intro l h
    rw [runX_bind, runX_get, runX_bind, runX_get]
    rfl
  · intro l h
    simp only [runX_bind, pull k p l h]
    rcases runX PULLBYTE l h with e | ⟨⟨res, l'⟩, h'⟩
    · rfl
    · cases res <;> rfl

private theorem constant {α : Type} (k : Nat) (p : BPtr) (v : α) : Independent k p (pure v) := by
  intro l h; rfl

private theorem bind {α β : Type} {k : Nat} {p : BPtr} {a : X α} {f : α → X β}
    (ha : Independent k p a) (hf : ∀ v, Independent k p (f v)) : Independent k p (a >>= f) := by
  intro l h
  simp only [runX_bind, ha l h]
  rcases runX a l h with err | ⟨⟨v, regs⟩, H⟩
  · rfl
  · cases v with
    | error e => rfl
    | ok v => exact hf v regs H

private theorem observe {α : Type} {k : Nat} {p : BPtr} {f : IL → X α}
    (same : ∀ l, f (registers p l) = f l) (hf : ∀ l, Independent k p (f l)) :
    Independent k p ((get : X IL) >>= f) := by
  intro l h
  simp only [runX_bind, runX_get, same]
  exact hf l l h

private theorem modify_registers {k : Nat} {p : BPtr} (f : IL → IL)
    (same : ∀ l, f (registers p l) = registers p (f l)) : Independent k p (modify f) := by
  intro l h
  rw [runX_modify, runX_modify, same]; rfl

theorem lift_eq {α : Type} {k : Nat} {p : BPtr} {m : M α}
    (mem : ∀ h, m (heap k p h) = mapped id (heap k p) (m h)) : Independent k p (monadLift m) := by
  intro l h
  rw [runX_lift, runX_lift, mem]
  rcases m h with err | ⟨v, H⟩ <;> rfl

theorem decoder_state (k : Nat) (p : BPtr) (st : InflateStatePtr) :
    Independent k p (monadLift (ldInflateState st)) := by
  apply lift_eq
  intro h
  rcases st with _ | ⟨i⟩
  · rfl
  · rcases i with ⟨i⟩
    simp only [ldI_eq, heap]
    cases h.istates i <;> rfl

private theorem code_get (k : Nat) (p : BPtr) (h : Heap) (r : CodeRef) :
    (Space.get (heap k p h) r : Option (Array Code)) = Space.get h r := by cases r <;> rfl

private theorem code_index (k : Nat) (p : BPtr) (ptr : CodePtr) (j : Int) :
    Independent k p (monadLift (ptr.index j)) := by
  apply lift_eq
  intro h
  have load (q : CodePtr) (h : Heap) : q.load (heap k p h) = mapped id (heap k p) (q.load h) := by
    cases q with
    | null => rfl
    | ref r n =>
      simp only [Ptr.load, code_get]
      cases Space.get h r with
      | none => rfl
      | some a => dsimp only; split <;> rfl
  have add : ptr.add j (heap k p h) = mapped id (heap k p) (ptr.add j h) := by
    by_cases zero : j = 0
    · simp only [Ptr.add, zero, ↓reduceIte]; rfl
    · cases ptr with
      | null => simp only [Ptr.add, zero, ↓reduceIte]; rfl
      | ref r n =>
        simp only [Ptr.add, zero, ↓reduceIte, code_get]
        cases Space.get h r with
        | none => rfl
        | some a => dsimp only; split <;> rfl
  simp only [Ptr.index, bind_app, add]
  rcases ptr.add j h with e | ⟨q, g⟩
  · rfl
  · exact load q g

theorem extract_bits (k : Nat) (p : BPtr) (n : UInt32) : Independent k p (BITS n) := by
  intro l h
  by_cases hn : n < 32 <;> simp [BITS, runX_bind, runX_get, runX_lift, shl32, hn, pure_app,
    runX_pure, mapped, registers, ub, Except.map]

/-- Both the literal/length and distance root tables use the same table index
and refills after rebinding the stream's output address. -/
theorem lookup_root (k : Nat) (p : BPtr) (c : Ctx) (dist : Bool) : Independent k p (lookup1 c dist) := by
  unfold lookup1 lookupRoot xloopBrk
  apply xloop (constant k p _)
  apply bind (decoder_state k p c.st)
  intro s
  apply bind (extract_bits k p _)
  intro b
  apply bind (code_index k p _ _)
  intro e
  apply bind (modify_registers _ (by intro; rfl))
  intro _
  apply observe (by intro; rfl)
  intro l
  split
  · exact constant k p _
  · exact bind (pull k p) (fun _ => constant k p _)

theorem lookup_link (k : Nat) (p : BPtr) (c : Ctx) (dist : Bool) : Independent k p (lookup2 c dist) := by
  unfold lookup2 lookupLink xloopBrk
  apply xloop (constant k p _)
  apply bind (decoder_state k p c.st)
  intro s
  apply observe (by intro; rfl)
  intro l
  apply bind (extract_bits k p _)
  intro b
  apply bind (lift_eq (m := shr32 b l.last.bits.toUInt32) (by intro; unfold shr32; split <;> rfl))
  intro sh
  apply bind (code_index k p _ _)
  intro e
  apply bind (modify_registers _ (by intro; rfl))
  intro _
  apply observe (by intro; rfl)
  intro regs
  split
  · exact constant k p _
  · exact bind (pull k p) (fun _ => constant k p _)

#print axioms lookup_root
#print axioms lookup_link
#print axioms need_bits
end Refill

/-- With zero capacity the three output-producing dispatch modes stop before
examining the destination address. COPY also records the zero copy count. -/
theorem zero_output_wait {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (full : l.left = 0)
    (mode : s.mode = LIT ∨ s.mode = MATCH ∨ (s.mode = COPY ∧ s.length ≠ 0)) :
    runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, if s.mode == COPY then {l with copy := 0} else l), h) := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  rcases mode with m | m | ⟨m, more⟩
  · rw [m]
    exact inflate_LIT_full c l h full
  · rw [m]
    change runX (inflate_MATCH c) l h = .ok ((.error Ex.leave, l), h)
    simp only [inflate_MATCH, runX_bind, runX_get, full, beq_self_eq_true, ↓reduceIte, runX_throw]
  · rw [m]
    apply inflate_COPY_leave E l more
    rw [full]
    simp [copyAmt]

/-- CHECK accounts for the output produced since the previous checkpoint.
When both counts are zero, this operation preserves all registers and the
entire heap, for every decoder input and output pointer. -/
theorem zero_output_account {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (l : IL) (full : l.left = 0) (empty : l.out_ = 0) :
    runX (accountCheckedOutput c.strm c.st) l h = .ok ((.ok (), l), h) := by
  have stream : wrZ c.strm (fun zz => {zz with total_out := zz.total_out + (0 : UInt64)}) h = .ok ((), h) := by
    simp only [E.strm, wrZ_eq, E.hz, UInt64.add_zero, ZStreamRef.put_self E.hz]
  have state : wrS c.st (fun ss => {ss with total := ss.total + (0 : UInt64)}) h = .ok ((), h) := by
    simp only [E.st, wrI_eq, E.hs, UInt64.add_zero, setI, upd_self _ _ _ E.hs]
  have idRegs : {l with left := 0, out_ := 0} = l := by
    cases l
    simp only [IL.mk.injEq]
    simp_all
  simp only [accountCheckedOutput, runX_bind, runX_modify, runX_get, empty, full, UInt32.sub_zero,
    idRegs, show (0 : UInt32).toUInt64 = 0 from rfl, runX_lift_ok stream, runX_lift_ok state,
    runX_ldS E, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

#print axioms zero_output_wait
#print axioms zero_output_account
end Lean2C.OriginalUncompress
