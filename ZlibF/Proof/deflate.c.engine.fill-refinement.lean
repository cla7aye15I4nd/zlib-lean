import ZlibF.Proof.«deflate.c.engine.fill-source»
import ZlibF.Proof.«deflate.c.hash-order»

/-! # Returning executions of the earlier refill loop on the emitted deflate source -/

open C Zlib.Deflate Zlib.Deflate.Proofs.HashOrder
namespace Zlib.Deflate.Engine.Proofs

/-- If a flag-based loop returns, an explicit break gives the same value and heap.
    Its extra condition read after setting the flag can only observe the heap. -/
private theorem cwhileBrk_of_flag_return {σ : Type} (test : σ → M Bool)
    (oldStep : σ → M (σ × Bool)) (newStep : σ → M (LoopStep σ Empty))
    (readonly : ∀ x h yes after, test x h = .ok (yes, after) → after = h)
    (step : ∀ x h y stop after, oldStep x h = .ok ((y, stop), after) →
      newStep x h = .ok ((if stop then .brk y else .next y), after))
    (x y : σ) (h after : Heap) (stopped : Bool)
    (returned : cwhile (fun (v, brk) => do return ( (← test v) && !brk, (v, brk)))
      (fun (v, _) => oldStep v) (x, false) h = .ok ((y, stopped), after)) :
    cwhileBrk (fun v => do return (← test v, v)) newStep x h = .ok (y, after) := by
  let cond : σ × Bool → M (Bool × σ × Bool) := fun (v, b) => do return ((← test v) && !b, (v,b))
  let body : σ × Bool → M (σ × Bool) := fun (v, _) => oldStep v
  let shortCond : σ → M (Bool × σ) := fun v => do return (← test v, v)
  have exit_flag (n : Nat) (v : σ) (g : Heap) (out : σ × Bool) (g' : Heap)
      (e : cwhile.go cond body n (v, true) g = .ok (out, g')) : v = out.1 ∧ g = g' := by
    cases n with
    | zero => cases e
    | succ n =>
      rw [cwhile.go] at e
      cases t : test v g with
      | error f => simp [cond, bind_app, t] at e
      | ok pair =>
        obtain ⟨yes, mid⟩ := pair
        obtain rfl := readonly _ _ _ _ t
        simp [cond, bind_app, t, pure_app] at e
        obtain ⟨rfl,rfl⟩ := e
        exact ⟨rfl,rfl⟩
  have go (n : Nat) (v : σ) (g : Heap) (out : σ × Bool) (g' : Heap)
      (e : cwhile.go cond body n (v, false) g = .ok (out,g')) :
      cwhileCtrl.go shortCond newStep n v g = .ok (.ok out.1,g') := by
    induction n generalizing v g with
    | zero => cases e
    | succ n ih =>
      rw [cwhile.go] at e
      rw [cwhileCtrl.go]
      cases t : test v g with
      | error f => simp [cond, bind_app, t] at e
      | ok pair =>
        obtain ⟨yes, mid⟩ := pair
        cases yes with
        | false =>
          simp [cond, bind_app, t, pure_app] at e
          obtain ⟨rfl,rfl⟩ := e
          simp [shortCond, bind_app, t, pure_app]
        | true =>
          simp only [cond, shortCond, bind_app, t, pure_app, Bool.not_false,
            Bool.true_and, ite_true, body] at e ⊢
          cases b : oldStep v mid with
          | error f => simp [b] at e
          | ok pair =>
            obtain ⟨⟨next, flag⟩, heap⟩ := pair
            rw [b] at e
            rw [step _ _ _ _ _ b]
            cases flag with
            | false => exact ih next heap e
            | true =>
              obtain ⟨same, sameHeap⟩ := exit_flag _ _ _ _ _ e
              simp [pure_app,same,sameHeap]
  have run := go fuel x h (y,stopped) after returned
  change (cwhileCtrl.go shortCond newStep fuel x >>= _) h = _
  simp only [bind_app, run, pure_app]


private def oldInsert (s : DeflateStatePtr) (str : UInt32) : M (UInt32 × Bool) := do
  let d ← ldDeflateState s
  -- UPDATE_HASH(s, s->ins_h, s->window[str + MIN_MATCH-1]);
  UPDATE_HASH s (← index8 d.window (str + (MIN_MATCH_u - 1)).toNat)
  let d ← ldDeflateState s
  -- s->prev[str & s->w_mask] = s->head[s->ins_h];
  let v ← Ptr.index d.head d.ins_h.toNat
  Ptr.store (← padd d.prev (str &&& d.w_mask).toNat) v
  -- s->head[s->ins_h] = (Pos)str;
  Ptr.store (← padd d.head d.ins_h.toNat) str.toUInt16
  -- str++; s->insert--;
  let str := str + 1
  wr s (fun d => { d with insert := d.insert - 1 })
  -- if (s->lookahead + s->insert < MIN_MATCH) break;
  let d ← ldDeflateState s
  pure (str, d.lookahead + d.insert < MIN_MATCH_u)

private theorem binds {α β γ δ : Type} {m : M α} {n : M β}
    {f : α → M γ} {g : β → M δ} {map₁ : α → β} {map₂ : γ → δ}
    (first : ∀ h x mid, m h = .ok (x, mid) → n h = .ok (map₁ x, mid))
    (next : ∀ x h y after, f x h = .ok (y, after) → g (map₁ x) h = .ok (map₂ y, after))
    (h : Heap) (y : γ) (after : Heap) (run : (m >>= f) h = .ok (y, after)) :
    (n >>= g) h = .ok (map₂ y, after) := by
  rw [bind_app] at run ⊢
  cases st : m h with
  | error e => rw [st] at run; cases run
  | ok pair =>
    obtain ⟨x, mid⟩ := pair
    rw [st] at run
    rw [first _ _ _ st]
    exact next x mid y after run

private theorem sharedPrefix {α β γ : Type} {m : M α} {f : α → M β} {g : α → M γ}
    {map : β → γ}
    (k : ∀ x h y after, f x h = .ok (y,after) → g x h = .ok (map y,after))
    (h : Heap) (y : β) (after : Heap) (run : (m >>= f) h = .ok (y,after)) :
    (m >>= g) h = .ok (map y,after) :=
  binds (map₁ := id) (fun _ _ _ e => e) k h y after run

private def stepOfFlag (pair : UInt32 × Bool) : LoopStep UInt32 Empty :=
  if pair.2 then .brk pair.1 else .next pair.1

private theorem insert_return (s : DeflateStatePtr) (str : UInt32) (h : Heap) (p : UInt32 × Bool)
    (after : Heap) (run : oldInsert s str h = .ok (p, after)) :
    fillWindowInsert s str h = .ok (stepOfFlag p,after) := by
  unfold oldInsert at run
  unfold fillWindowInsert
  apply sharedPrefix (map := stepOfFlag) _ h p after run
  rintro d h p after run
  rw [← M_bind_assoc] at run
  apply binds (map₁ := id) (map₂ := stepOfFlag)
    (fun h u mid e => (updateHashAt_ok_iff s d.window _ h mid u).mpr e) _ h p after run
  intro u h p after run
  repeat' (apply sharedPrefix (map := stepOfFlag) _ _ _ _ run; clear run; intro v h p after run)
  simp only [pure_app, Except.ok.injEq, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  split <;> simp_all [stepOfFlag, pure_app]


private abbrev oldTest (s : DeflateStatePtr) (_ : UInt32) : M Bool := do return (← rd s (·.insert)) != 0

private theorem test_readonly (s : DeflateStatePtr) (v : UInt32) (h : Heap) (yes : Bool) (after : Heap)
    (e : oldTest s v h = .ok (yes,after)) : after = h := by
  cases s with
  | none => cases e
  | some r =>
    cases live : r.get h with
    | none => simp [oldTest, rd, ldDeflateState, bind_app, live] at e
    | some d =>
      simp [oldTest, rd, ldDeflateState, bind_app, live, pure_app] at e
      exact e.2.symm

private theorem returnLoop (s : DeflateStatePtr) (str : UInt32) (h after : Heap)
    (p : UInt32 × Bool)
    (run : cwhile (fun (x, brk) => do let ins ← rd s (·.insert); pure (ins != 0 && !brk, (x,brk)))
      (fun (x, _) => oldInsert s x) (str,false) h = .ok (p,after)) :
    cwhileBrk (fun x => do let ins ← rd s (·.insert); pure (ins != 0, x))
      (fillWindowInsert s) str h = .ok (p.1,after) := by
  let test := oldTest s
  have old (v : UInt32 × Bool) :
      (do let ins ← rd s (·.insert); pure (ins != 0 && !v.2, v)) =
        (do let yes ← test v.1; pure (yes && !v.2, v)) := by
    funext g
    cases e : rd s (·.insert) g with
    | error => simp [test, oldTest, bind_app, e]
    | ok pair => cases pair; simp [test, oldTest, bind_app, e, pure_app]
  have new (x : UInt32) :
      (do let ins ← rd s (·.insert); pure (ins != 0, x)) =
        (do let yes ← test x; pure (yes, x)) := by
    funext g
    cases e : rd s (·.insert) g with
    | error => simp [test, oldTest, bind_app, e]
    | ok pair => cases pair; simp [test, oldTest, bind_app, e, pure_app]
  obtain ⟨v, stopped⟩ := p
  simp only [new]
  apply cwhileBrk_of_flag_return test (oldInsert s) (fillWindowInsert s) (test_readonly s)
    (fun x g y b a hr => insert_return _ _ _ (y,b) _ hr) _ _ _ _ stopped
  have align : (fun (v, b) => do let ins ← rd s (·.insert); pure (ins != 0 && !b,(v,b))) =
      (fun (v, b) => do let yes ← test v; pure (yes && !b,(v,b))) := by
    funext ⟨x,b⟩
    exact old (x,b)
  rwa [align] at run


private def seedPrior (s : DeflateStatePtr) (d : DeflateState) (x : UInt32) : M Unit := do
  let v ← index8 d.window x.toNat
  wr s fun q => {q with ins_h := v.toUInt32}
  UPDATE_HASH s (← index8 d.window (x+1).toNat)

private def seedActual (s : DeflateStatePtr) (d : DeflateState) (x : UInt32) : M Unit := do
  let v ← index8 d.window x.toNat
  wr s fun q => {q with ins_h := v.toUInt32}
  updateHashAt s (← ldDeflateState s).window (x+1)

private theorem seed_return (s : DeflateStatePtr) (d : DeflateState) (x : UInt32)
    (h after : Heap) (state : ldDeflateState s h = .ok (d,h)) (result : Unit)
    (run : seedPrior s d x h = .ok (result,after)) : seedActual s d x h = .ok (result,after) := by
  cases s with
  | none => cases state
  | some r =>
    cases r with
    | tab i =>
      cases eq : h.dstates i with
      | none => simp [ldDeflateState, DeflateStateRef.get, eq] at state
      | some old =>
        have same : old = d := by simpa [ldDeflateState, DeflateStateRef.get, eq] using state
        subst old
        cases load : index8 d.window x.toNat h with
        | error => simp [seedPrior, bind_app, load] at run
        | ok pair =>
          obtain ⟨v,mid⟩ := pair
          have same := C.Ptr.index_heap load
          subst mid
          let d' : DeflateState := {d with ins_h := v.toUInt32}
          let hh := {h with dstates := upd h.dstates i (some d')}
          have write : wr (some (.tab i)) (fun q => {q with ins_h := v.toUInt32}) h = .ok ((),hh) := by
            simp only [wr, bind_app, state, stDeflateState_tab eq, hh, d']
          have read : ldDeflateState (some (.tab i)) hh = .ok (d',hh) := ldDeflateState_tab (upd_same _ _ _)
          simp only [seedActual, bind_app, load, write, read]
          apply (updateHashAt_ok_iff _ _ _ _ _ _).mpr
          simpa only [seedPrior, bind_app, load, write, d'] using run

private def oldPrimingLoop (s : DeflateStatePtr) (str : UInt32) : M (UInt32 × Bool) :=
  cwhile (fun (v, brk) => do let ins ← rd s (·.insert); pure (ins != 0 && !brk, (v,brk)))
    (fun (v, _) => oldInsert s v) (str,false)
private def actualPrimingLoop (s : DeflateStatePtr) (str : UInt32) : M UInt32 :=
  cwhileBrk (fun v => do let ins ← rd s (·.insert); pure (ins != 0,v)) (fillWindowInsert s) str

private theorem prime_return (s : DeflateStatePtr) (h after : Heap)
    (run : fillPrime s h = .ok ((),after)) : primeWindowHash s h = .ok ((),after) := by
  let prior (d : DeflateState) : M Unit := do
    if d.lookahead + d.insert ≥ MIN_MATCH_u then
      let x := d.strstart - d.insert
      seedPrior s d x
      let (_,_) ← oldPrimingLoop s x
  let actual (d : DeflateState) : M Unit := do
    if d.lookahead + d.insert ≥ MIN_MATCH_u then
      let x := d.strstart - d.insert
      seedActual s d x
      let _ ← actualPrimingLoop s x
  have repr₁ : fillPrime s = (ldDeflateState s >>= prior) := by
    unfold fillPrime prior seedPrior oldPrimingLoop oldInsert
    simp only [M_bind_assoc]
  have repr₂ : primeWindowHash s = (ldDeflateState s >>= actual) := by
    unfold primeWindowHash actual seedActual actualPrimingLoop
    simp only [M_bind_assoc]
  rw [repr₁,bind_app] at run
  rw [repr₂,bind_app]
  cases state : ldDeflateState s h with
  | error => simp [state] at run
  | ok pair =>
    obtain ⟨d,mid⟩ := pair
    have heaps : mid = h := by
      cases s with
      | none => cases state
      | some r =>
        cases e : r.get h <;> simp [ldDeflateState, e] at state
        exact state.2.symm
    subst mid
    rw [state] at run
    dsimp only at run ⊢
    by_cases guard : d.lookahead + d.insert ≥ MIN_MATCH_u
    · simp only [prior, actual, guard, ite_true, bind_app] at run ⊢
      cases a : seedPrior s d (d.strstart-d.insert) h with
      | error => simp [a] at run
      | ok pair =>
        obtain ⟨u, hh⟩ := pair
        rw [a] at run
        rw [seed_return _ _ _ _ _ state _ a]
        dsimp only at run ⊢
        cases b : oldPrimingLoop s (d.strstart-d.insert) hh with
        | error => simp [b] at run
        | ok pair =>
          obtain ⟨v, heap⟩ := pair
          rw [b] at run
          have t : actualPrimingLoop s (d.strstart-d.insert) hh = .ok (v.1,heap) := returnLoop _ _ _ _ _ b
          rw [t]
          obtain ⟨x,flag⟩ := v
          exact run
    · simpa [prior, actual, guard] using run


private def fillPriorFromStream (s : DeflateStatePtr) (more : UInt32) : M Bool := do
  -- if (s->strm->avail_in == 0) break;
  let strm ← rd s (·.strm)
  if (← zrd strm (·.avail_in)) == 0 then return true
  -- n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more);
  let d ← ldDeflateState s
  let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
  let n ← read_buf strm dst more
  wr s (fun d => { d with lookahead := d.lookahead + n })            -- s->lookahead += n;
  fillPrime s
  pure false

private def fillFlag (b : Bool) : LoopStep Unit Empty := if b then .brk () else .next ()

private theorem from_stream_return (s : DeflateStatePtr) (more : UInt32) (h after : Heap) (b : Bool)
    (run : fillPriorFromStream s more h = .ok (b, after)) :
    fillFromStream s more h = .ok (fillFlag b,after) := by
  unfold fillPriorFromStream at run
  unfold fillFromStream
  repeat' (apply sharedPrefix (map := fillFlag) _ _ _ _ run; clear run; intro v h b after run)
  split at run <;> rename_i cond <;> simp only [cond, ↓reduceIte]
  · cases run; rfl
  · repeat' (apply sharedPrefix (map := fillFlag) _ _ _ _ run; clear run; intro v h b after run)
    apply binds (map₁ := id) (map₂ := fillFlag) (fun h u after e => by cases u; exact prime_return s h after e) _ _ _ _ run
    intro u h b after e
    cases e
    rfl

private theorem body_shape (s : DeflateStatePtr) (wsize : UInt32) :
    fillBody s wsize false = (do
      let d ← ldDeflateState s
      let mut more : UInt32 := (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toUInt32
      if d.strstart ≥ wsize + (d.w_size - MIN_LOOKAHEAD_u) then
        slideWindowForFill s d wsize more
        more := more + wsize
      fillPriorFromStream s more) := by
  unfold fillBody fillPriorFromStream slideWindowForFill
  simp only [M_bind_assoc]
  rw [← clampInsert_eq]
  simp only [M_bind_assoc, fill_ite_bind, M_pure_bind]

private theorem body_return (s : DeflateStatePtr) (wsize : UInt32) (h after : Heap) (b : Bool)
    (run : fillBody s wsize false h = .ok (b,after)) :
    fillWindowBody s wsize () h = .ok (fillFlag b,after) := by
  rw [body_shape] at run
  unfold fillWindowBody
  apply sharedPrefix (map := fillFlag) _ _ _ _ run
  intro d h b after run
  dsimp only at run ⊢
  split at run <;> rename_i cond <;> simp only [cond, ↓reduceIte]
  · apply sharedPrefix (map := fillFlag) _ _ _ _ run
    intro _u h b after run
    exact from_stream_return _ _ _ _ _ run
  · exact from_stream_return _ _ _ _ _ run


private theorem cond_next (s : DeflateStatePtr) :
    fillCond s false = (do let (b, _) ← fillWindowCondition s (); pure (b,false)) := by
  unfold fillCond fillWindowCondition
  simp only [Bool.false_eq_true, ite_false, M_bind_assoc, fill_ite_bind, M_pure_bind]

private theorem outer_return (s : DeflateStatePtr) (wsize : UInt32) (h after : Heap) (flag : Bool)
    (run : cdoWhile (fillBody s wsize) (fillCond s) false h = .ok (flag,after)) :
    cdoWhileBrk (fillWindowBody s wsize) (fillWindowCondition s) () h = .ok ((),after) := by
  have go (n : Nat) (g : Heap)
      (e : cdoWhile.go (fillBody s wsize) (fillCond s) n false g = .ok (flag,after)) :
      cdoWhileCtrl.go (fillWindowBody s wsize) (fillWindowCondition s) n () g = .ok (.ok (),after) := by
    induction n generalizing g with
    | zero => cases e
    | succ n ih =>
      rw [cdoWhile.go,bind_app] at e
      rw [cdoWhileCtrl.go,bind_app]
      cases a : fillBody s wsize false g with
      | error => simp [a] at e
      | ok pair =>
        obtain ⟨b,mid⟩ := pair
        rw [a] at e
        rw [body_return _ _ _ _ _ a]
        cases b with
        | true =>
          simp [fillCond, bind_app, pure_app] at e
          rw [← e.2]
          rfl
        | false =>
          simp only [cond_next, bind_app] at e
          simp only [fillFlag, Bool.false_eq_true, ite_false, bind_app]
          cases t : fillWindowCondition s () mid with
          | error => simp [t] at e
          | ok pair =>
            obtain ⟨⟨again, value⟩,g'⟩ := pair
            cases value
            simp only [t, pure_app] at e
            cases again with
            | true => exact ih _ e
            | false =>
              cases e
              rfl
  change (cdoWhileCtrl.go _ _ fuel () >>= _) h = _
  simp only [bind_app, go _ _ run, pure_app]

/-- Each returning refill of the earlier model returns on the emitted definition
    with exactly the same final heap, on arbitrary initial heaps. -/
theorem fill_window_of_return (s : DeflateStatePtr) (h after : Heap)
    (run : (do let wsize ← rd s (·.w_size)
               let _ ← cdoWhile (fillBody s wsize) (fillCond s) false
               fillHighWater s) h = .ok ((),after)) :
    fill_window s h = .ok ((),after) := by
  rw [fill_window_source]
  apply sharedPrefix (map := id) _ h () after run
  intro wsize h u after e
  apply binds (map₁ := fun _ => ()) (map₂ := id) (fun h b mid => outer_return s wsize h mid b) _ _ _ _ e
  exact fun _ _ _ _ x => x

#print axioms fill_window_of_return
end Zlib.Deflate.Engine.Proofs
