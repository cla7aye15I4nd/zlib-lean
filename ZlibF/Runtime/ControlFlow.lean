import ZlibF.Runtime.Alloc

/-!
# Runtime: C control-flow and exact-shape primitives

Defines first-class fuel-bounded control-flow combinators (`LoopStep`, `cforEver`, `cwhileCtrl`,
`cdoWhileCtrl`, `clabel`, `cforwardLabel`), ordered C local declarations (`cdecl`), and compound
pointer post-increment operations so `Lean2C.Simple` can emit exact C99 shapes (including `goto`,
labels, `break`, `continue`, early `return`, and post-increments) while retaining purely functional
Lean semantics and clean equivalence lemmas back to existing `cwhile`/`cdoWhile` translations.
-/

namespace C

/-- Control-flow outcome of one iteration of a C loop body. -/
inductive LoopStep (σ ρ : Type) where
  /-- Normal fallthrough at the end of the loop body. -/
  | next (s : σ)
  /-- Explicit C `continue;`. -/
  | cont (s : σ)
  /-- Explicit C `break;` (exits a `do ... while` loop without evaluating its condition). -/
  | brk (s : σ)
  /-- Explicit early `return r;` from the enclosing function. -/
  | ret (r : ρ)
  deriving Repr, DecidableEq, Inhabited

/-- Infinite C loop (`for (;;)`), bounded by `C.fuel`, returning `.error r` on early `return` or
`.ok s` on `break`. -/
def cforEver {σ ρ : Type} (body : σ → M (LoopStep σ ρ)) (s : σ) : M (Except ρ σ) :=
  go fuel s
where
  go : Nat → σ → M (Except ρ σ)
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      match ← body s with
      | .next s' | .cont s' => go n s'
      | .brk s' => pure (.ok s')
      | .ret r => pure (.error r)

/-- Infinite C loop (`for (;;)`), bounded by `C.fuel`, with explicit continuation `k` run after
`break`. Lowered in tail position without emitting any `Except` wrapper. -/
def cforEverRet {σ ρ : Type} (body : σ → M (LoopStep σ ρ)) (s : σ) (k : σ → M ρ) : M ρ := do
  match ← cforEver body s with
  | .error r => pure r
  | .ok s' => k s'

/-- C `while (cond) body` supporting `break`, `continue`, and early `return`. -/
def cwhileCtrl {σ ρ : Type} (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ ρ))
    (s : σ) : M (Except ρ σ) :=
  go fuel s
where
  go : Nat → σ → M (Except ρ σ)
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      let (c, s) ← cond s
      if c then
        match ← body s with
        | .next s' | .cont s' => go n s'
        | .brk s' => pure (.ok s')
        | .ret r => pure (.error r)
      else pure (.ok s)

/-- C `while (cond) body` with `break`, `continue`, and early `return`, in tail position with
post-loop continuation `k`. -/
def cwhileRet {σ ρ : Type} (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ ρ))
    (s : σ) (k : σ → M ρ) : M ρ := do
  match ← cwhileCtrl cond body s with
  | .error r => pure r
  | .ok s' => k s'

/-- C `while (cond) body` with `break`/`continue` (no early `return`), returning `σ`. -/
def cwhileBrk {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ Empty))
    (s : σ) : M σ := do
  match ← cwhileCtrl cond body s with
  | .error e => nomatch e
  | .ok s' => pure s'

/-- C `do body while (cond);` supporting `break` (leaving without evaluating `cond`), `continue`
(jumping directly to evaluating `cond`), and early `return`. -/
def cdoWhileCtrl {σ ρ : Type} (body : σ → M (LoopStep σ ρ)) (cond : σ → M (Bool × σ))
    (s : σ) : M (Except ρ σ) :=
  go fuel s
where
  go : Nat → σ → M (Except ρ σ)
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      match ← body s with
      | .brk s' => pure (.ok s')
      | .ret r => pure (.error r)
      | .next s' | .cont s' =>
        let (c, s'') ← cond s'
        if c then go n s'' else pure (.ok s'')

/-- C `do body while (cond);` with `break`/`continue` (no early `return`), returning `σ`. -/
def cdoWhileBrk {σ : Type} (body : σ → M (LoopStep σ Empty)) (cond : σ → M (Bool × σ))
    (s : σ) : M σ := do
  match ← cdoWhileCtrl body cond s with
  | .error e => nomatch e
  | .ok s' => pure s'

/-- Outcome of a backward/intra-block C label `_name:` body (`goto _name;` or fallthrough). -/
inductive GotoStep (σ α : Type) where
  | goto (s : σ)
  | done (a : α)
  deriving Repr, DecidableEq, Inhabited

/-- Backward C label block `_name: body`, where `.goto s'` emits `goto _name;` and re-enters at
`_name:` (consuming 1 `fuel`). -/
def clabel {σ α : Type} (_name : String) (body : σ → M (GotoStep σ α)) (s : σ) : M α :=
  go fuel s
where
  go : Nat → σ → M α
    | 0, _ => fun _ => .error .outOfFuel
    | n + 1, s => do
      match ← body s with
      | .goto s' => go n s'
      | .done a => pure a

/-- Outcome of code preceding a forward `goto _name;`: either jump straight to `_name:` or
fall through to `skipped`. -/
inductive FwdStep (σ : Type) where
  | fall (s : σ)
  | goto (s : σ)
  deriving Repr, DecidableEq, Inhabited

/-- Forward C `goto _name;` skipping `skipped` and landing at `_name: afterLabel`. -/
def cforwardLabel {σ α : Type} (_name : String)
    (before : M (FwdStep σ)) (skipped : σ → M σ) (afterLabel : σ → M α) : M α := do
  match ← before with
  | .goto s => afterLabel s
  | .fall s => afterLabel (← skipped s)

/-- Ordered local-variable declaration anchor: definitionally `pure s` in Lean; lowered by
`Lean2C.Simple` as C local variable declarations in field order (`Inhabited.default` left
uninitialized, other fields initialized inline). -/
def cdecl {σ : Type} (s : σ) : M σ := pure s

/-- Keep the block scopes of explicit `cdecl` locals while allocating compiler temporaries
at function entry. Evaluation of initializers stays at the original Lean bind. -/
def withScopedLocals {α : Type} (body : M α) : M α := body

@[simp] theorem cdecl_eq {σ : Type} (s : σ) : cdecl s = pure s := rfl

/-- Inline expression marker: definitionally `m` in Lean, emitted inline without a temporary
local variable in C so `alloca` declaration order stays unchanged. -/
def cinline {α : Type} (m : M α) : M α := m

@[simp] theorem cinline_eq {α : Type} (m : M α) : cinline m = m := rfl

/-- `*p++ = v` for `code *p`. -/
def storePostIncCode (p : CodePtr) (v : Code) : M CodePtr := do
  Ptr.store p v
  p.add 1

/-- `dst[offs[idx]++] = v` for `unsigned short *dst` and local array `offs`. -/
def storeAtPostInc (dst : WPtr) (offs : Array UInt16) (idx : Nat) (v : UInt16) : M (Array UInt16) :=
  match offs[idx]? with
  | none => ub "array index outside its object"
  | some o => do
    let q ← dst.add o.toNat
    Ptr.store q v
    pure (offs.set! idx (o + 1))

/-- `*out++ = *from++`. -/
def copyBytePostInc (out from_ : BPtr) : M (BPtr × BPtr) := do
  let b ← load8 from_
  let from_' ← from_.add 1
  store8 out b
  let out' ← out.add 1
  pure (out', from_')

/-- `hold += (unsigned long)(*in++) << bits; bits += 8;`. -/
def pullByte64 (in_ : BPtr) (hold : UInt64) (bits : UInt32) : M (BPtr × UInt64 × UInt32) := do
  let b ← load8 in_
  let in_' ← in_.add 1
  if bits.toUInt64 < 64 then
    pure (in_', hold + (b.toUInt64 <<< bits.toUInt64), bits + 8)
  else
    ub "shift count out of range"

/-! ## Control-flow equivalence lemmas -/

private theorem clabel_go_succ {σ α : Type} (body : σ → M (GotoStep σ α)) (n : Nat) (s : σ) (h : Heap) :
    clabel.go body (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (.goto s', h') => clabel.go body n s' h'
      | .ok (.done a, h') => .ok (a, h') := by
  rw [clabel.go, bind_app]
  rcases h1 : body s h with e | ⟨st, h'⟩
  · rfl
  · cases st <;> rfl

private theorem cdoWhile_go_succ {σ : Type} (body : σ → M σ) (cond : σ → M (Bool × σ))
    (n : Nat) (s : σ) (h : Heap) :
    cdoWhile.go body cond (n + 1) s h =
      match (body s >>= cond) h with
      | .error e => .error e
      | .ok ((true, s'), h') => cdoWhile.go body cond n s' h'
      | .ok ((false, s'), h') => .ok (s', h') := by
  rw [cdoWhile.go, bind_app, bind_app]
  rcases h1 : body s h with e | ⟨sb, hb⟩
  · rfl
  · dsimp only
    rw [bind_app]
    rcases h2 : cond sb hb with e | ⟨⟨c, s'⟩, h'⟩
    · rfl
    · cases c <;> rfl

private theorem cwhile_go_succ {σ : Type} (cond : σ → M (Bool × σ)) (body : σ → M σ)
    (n : Nat) (s : σ) (h : Heap) :
    cwhile.go cond body (n + 1) s h =
      match cond s h with
      | .error e => .error e
      | .ok ((false, s1), h1) => .ok (s1, h1)
      | .ok ((true, s1), h1) =>
        match body s1 h1 with
        | .error e => .error e
        | .ok (s2, h2) => cwhile.go cond body n s2 h2 := by
  rw [cwhile.go, bind_app]
  rcases h1 : cond s h with e | ⟨⟨c, s1⟩, h1'⟩
  · rfl
  · cases c
    · rfl
    · simp only [ite_true, bind_app]
      rcases h2 : body s1 h1' with e | ⟨s2, h2'⟩ <;> rfl

private theorem cdoWhileCtrl_go_succ {σ ρ : Type} (body : σ → M (LoopStep σ ρ))
    (cond : σ → M (Bool × σ)) (n : Nat) (s : σ) (h : Heap) :
    cdoWhileCtrl.go body cond (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (.brk s', h') => .ok (.ok s', h')
      | .ok (.ret r, h') => .ok (.error r, h')
      | .ok (.next s', h') | .ok (.cont s', h') =>
        match cond s' h' with
        | .error e => .error e
        | .ok ((true, s''), h'') => cdoWhileCtrl.go body cond n s'' h''
        | .ok ((false, s''), h'') => .ok (.ok s'', h'') := by
  rw [cdoWhileCtrl.go, bind_app]
  rcases h1 : body s h with e | ⟨st, h'⟩
  · rfl
  · cases st with
    | brk => rfl
    | ret => rfl
    | next s' =>
      dsimp only; rw [bind_app]
      rcases h2 : cond s' h' with e | ⟨⟨c, s''⟩, h''⟩
      · rfl
      · cases c <;> rfl
    | cont s' =>
      dsimp only; rw [bind_app]
      rcases h2 : cond s' h' with e | ⟨⟨c, s''⟩, h''⟩
      · rfl
      · cases c <;> rfl

private theorem cwhileCtrl_go_succ {σ ρ : Type} (cond : σ → M (Bool × σ))
    (body : σ → M (LoopStep σ ρ)) (n : Nat) (s : σ) (h : Heap) :
    cwhileCtrl.go cond body (n + 1) s h =
      match cond s h with
      | .error e => .error e
      | .ok ((false, s1), h1) => .ok (.ok s1, h1)
      | .ok ((true, s1), h1) =>
        match body s1 h1 with
        | .error e => .error e
        | .ok (.next s2, h2) | .ok (.cont s2, h2) => cwhileCtrl.go cond body n s2 h2
        | .ok (.brk s2, h2) => .ok (.ok s2, h2)
        | .ok (.ret r, h2) => .ok (.error r, h2) := by
  rw [cwhileCtrl.go, bind_app]
  rcases h1 : cond s h with e | ⟨⟨c, s1⟩, h1'⟩
  · rfl
  · cases c
    · rfl
    · simp only [ite_true, bind_app]
      rcases h2 : body s1 h1' with e | ⟨st, h2'⟩
      · rfl
      · cases st <;> rfl

private theorem cforEver_go_succ {σ ρ : Type} (body : σ → M (LoopStep σ ρ))
    (n : Nat) (s : σ) (h : Heap) :
    cforEver.go body (n + 1) s h =
      match body s h with
      | .error e => .error e
      | .ok (.next s', h') | .ok (.cont s', h') => cforEver.go body n s' h'
      | .ok (.brk s', h') => .ok (.ok s', h')
      | .ok (.ret r, h') => .ok (.error r, h') := by
  rw [cforEver.go, bind_app]
  rcases h1 : body s h with e | ⟨st, h'⟩
  · rfl
  · cases st <;> rfl

theorem clabel_go_eq_cdoWhile_go {σ α σ' : Type}
    (body : σ → M (GotoStep σ α)) (body' : σ' → M σ') (cond' : σ' → M (Bool × σ'))
    (proj : σ → σ') (ret : α → σ')
    (hstep : ∀ s h,
      (do
        match ← body s with
        | .goto s1 => pure (true, proj s1)
        | .done a => pure (false, ret a)) h =
      (body' (proj s) >>= cond') h) :
    ∀ n s h,
      (clabel.go body n s >>= fun a => pure (ret a)) h =
      cdoWhile.go body' cond' n (proj s) h := by
  intro n
  induction n with
  | zero =>
    intro s h
    rw [bind_app, clabel.go, cdoWhile.go]
  | succ n ih =>
    intro s h
    have hs := hstep s h
    rw [bind_app] at hs
    rw [bind_app, clabel_go_succ, cdoWhile_go_succ]
    rcases h1 : body s h with e | ⟨st, h1'⟩
    · rw [h1] at hs; rw [← hs]
    · cases st with
      | goto s1 =>
        rw [h1] at hs; dsimp only at hs
        rw [← hs]; dsimp only
        exact ih s1 h1'
      | done a =>
        rw [h1] at hs; dsimp only at hs
        rw [← hs]
        rfl

theorem clabel_eq_cdoWhile {σ α σ' : Type} (name : String)
    (body : σ → M (GotoStep σ α)) (body' : σ' → M σ') (cond' : σ' → M (Bool × σ'))
    (proj : σ → σ') (ret : α → σ')
    (hstep : ∀ s h,
      (do
        match ← body s with
        | .goto s1 => pure (true, proj s1)
        | .done a => pure (false, ret a)) h =
      (body' (proj s) >>= cond') h)
    (s : σ) (h : Heap) :
    (clabel name body s >>= fun a => pure (ret a)) h =
    cdoWhile body' cond' (proj s) h :=
  clabel_go_eq_cdoWhile_go body body' cond' proj ret hstep fuel s h

theorem cdoWhileCtrl_go_eq_cdoWhile_go {σ σ' β : Type}
    (body : σ → M (LoopStep σ Empty)) (cond : σ → M (Bool × σ))
    (body' : σ' → M σ') (cond' : σ' → M (Bool × σ'))
    (k : σ → M β) (k' : σ' → M β)
    (proj : σ → σ') (brkProj : σ → σ')
    (hk : ∀ s h, k s h = k' (proj s) h ∧ k s h = k' (brkProj s) h)
    (hstep : ∀ s h,
      (do
        match ← body s with
        | .brk s1 => pure (false, brkProj s1)
        | .ret e => nomatch e
        | .next s1 | .cont s1 =>
          let (c, s2) ← cond s1
          pure (c, proj s2)) h =
      (body' (proj s) >>= cond') h) :
    ∀ n s h,
      ((cdoWhileCtrl.go body cond n s >>= fun
        | .error e => nomatch e
        | .ok s1 => pure s1) >>= k) h =
      (cdoWhile.go body' cond' n (proj s) >>= k') h := by
  intro n
  induction n with
  | zero =>
    intro s h
    rw [bind_app, bind_app, cdoWhileCtrl.go, cdoWhile.go]
    rfl
  | succ n ih =>
    intro s h
    have hs := hstep s h
    rw [bind_app] at hs
    rw [bind_app, bind_app, cdoWhileCtrl_go_succ, bind_app, cdoWhile_go_succ]
    rcases h1 : body s h with e | ⟨st, h1'⟩
    · rw [h1] at hs; rw [← hs]
    · cases st with
      | ret e => nomatch e
      | brk s1 =>
        rw [h1] at hs; dsimp only at hs
        rw [← hs]; dsimp only
        exact (hk s1 h1').2
      | next s1 =>
        rw [h1] at hs; dsimp only at hs ⊢; rw [bind_app] at hs
        rcases h2 : cond s1 h1' with e | ⟨⟨c, s2⟩, h2'⟩
        · rw [h2] at hs; rw [← hs]
        · rw [h2] at hs; dsimp only at hs
          rw [← hs]
          cases c
          · dsimp only; exact (hk s2 h2').1
          · rw [show (pure (true, proj s2) : M (Bool × σ')) h2' = .ok ((true, proj s2), h2') from rfl]
            dsimp only; simpa only [bind_app] using ih s2 h2'
      | cont s1 =>
        rw [h1] at hs; dsimp only at hs ⊢; rw [bind_app] at hs
        rcases h2 : cond s1 h1' with e | ⟨⟨c, s2⟩, h2'⟩
        · rw [h2] at hs; rw [← hs]
        · rw [h2] at hs; dsimp only at hs
          rw [← hs]
          cases c
          · dsimp only; exact (hk s2 h2').1
          · rw [show (pure (true, proj s2) : M (Bool × σ')) h2' = .ok ((true, proj s2), h2') from rfl]
            dsimp only; simpa only [bind_app] using ih s2 h2'

theorem cdoWhileBrk_eq_cdoWhile {σ σ' β : Type}
    (body : σ → M (LoopStep σ Empty)) (cond : σ → M (Bool × σ))
    (body' : σ' → M σ') (cond' : σ' → M (Bool × σ'))
    (k : σ → M β) (k' : σ' → M β)
    (proj : σ → σ') (brkProj : σ → σ')
    (hk : ∀ s h, k s h = k' (proj s) h ∧ k s h = k' (brkProj s) h)
    (hstep : ∀ s h,
      (do
        match ← body s with
        | .brk s1 => pure (false, brkProj s1)
        | .ret e => nomatch e
        | .next s1 | .cont s1 =>
          let (c, s2) ← cond s1
          pure (c, proj s2)) h =
      (body' (proj s) >>= cond') h)
    (s : σ) (h : Heap) :
    (cdoWhileBrk body cond s >>= k) h =
    (cdoWhile body' cond' (proj s) >>= k') h :=
  cdoWhileCtrl_go_eq_cdoWhile_go body cond body' cond' k k' proj brkProj hk hstep fuel s h

theorem cwhileCtrl_go_eq_cwhile_go_of_nofuel {σ σ' ρ β : Type}
    (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ ρ))
    (cond' : σ' → M (Bool × σ')) (body' : σ' → M σ')
    (k : Except ρ σ → M β) (tail' : σ' → M β)
    (proj : σ → σ') (IsBrk : σ' → σ → Prop) (IsRet : σ' → ρ → Prop)
    (hcond : ∀ s h,
      (cond s >>= fun (c, s1) => pure (c, proj s1)) h = cond' (proj s) h)
    (hbody : ∀ s h,
      match body s h with
      | .error e => body' (proj s) h = .error e
      | .ok (.next s1, h1) | .ok (.cont s1, h1) => body' (proj s) h = .ok (proj s1, h1)
      | .ok (.brk s1, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsBrk st s1
      | .ok (.ret r, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsRet st r)
    (hbrkCond : ∀ st s1 h, IsBrk st s1 → cond' st h = .ok ((false, st), h))
    (hretCond : ∀ st r h, IsRet st r → cond' st h = .ok ((false, st), h))
    (hdone : ∀ s h, tail' (proj s) h = k (.ok s) h)
    (hbrk : ∀ st s1 h, IsBrk st s1 → tail' st h = k (.ok s1) h)
    (hret : ∀ st r h, IsRet st r → tail' st h = k (.error r) h) :
    ∀ n s h,
      (cwhile.go cond' body' n (proj s) >>= tail') h ≠ .error .outOfFuel →
      (cwhileCtrl.go cond body n s >>= k) h =
      (cwhile.go cond' body' n (proj s) >>= tail') h := by
  intro n
  induction n with
  | zero =>
    intro s h hnf
    rw [bind_app, cwhile.go] at hnf
    exact absurd rfl hnf
  | succ n ih =>
    intro s h hnf
    have hc := hcond s h
    rw [bind_app] at hc
    rw [bind_app, cwhile_go_succ] at hnf
    rw [bind_app, cwhileCtrl_go_succ, bind_app, cwhile_go_succ]
    rcases hco : cond s h with e | ⟨⟨c, s1⟩, h1⟩
    · rw [hco] at hc; rw [← hc]
    · rw [hco] at hc
      have hc' : cond' (proj s) h = .ok ((c, proj s1), h1) := hc.symm
      rw [hc'] at hnf ⊢
      cases c with
      | false => exact (hdone s1 h1).symm
      | true =>
        dsimp only at hnf ⊢
        have hb := hbody s1 h1
        rcases hbo : body s1 h1 with e | ⟨step, h2⟩
        · rw [hbo] at hb; simp only [hb]
        · rw [hbo] at hb
          cases step with
          | next s2 =>
            rw [hb] at hnf ⊢
            exact ih s2 h2 hnf
          | cont s2 =>
            rw [hb] at hnf ⊢
            exact ih s2 h2 hnf
          | brk s2 =>
            rcases hb with ⟨st, hbe, his⟩
            rw [hbe] at hnf ⊢
            dsimp only at hnf ⊢
            cases n with
            | zero =>
              rw [cwhile.go] at hnf
              exact absurd rfl hnf
            | succ m =>
              rw [cwhile_go_succ, hbrkCond st s2 h2 his]
              dsimp only
              exact (hbrk st s2 h2 his).symm
          | ret r =>
            rcases hb with ⟨st, hbe, his⟩
            rw [hbe] at hnf ⊢
            dsimp only at hnf ⊢
            cases n with
            | zero =>
              rw [cwhile.go] at hnf
              exact absurd rfl hnf
            | succ m =>
              rw [cwhile_go_succ, hretCond st r h2 his]
              dsimp only
              exact (hret st r h2 his).symm

theorem cwhileCtrl_eq_cwhile_of_nofuel {σ σ' ρ β : Type}
    (cond : σ → M (Bool × σ)) (body : σ → M (LoopStep σ ρ))
    (s : σ) (k : Except ρ σ → M β)
    (cond' : σ' → M (Bool × σ')) (body' : σ' → M σ') (tail' : σ' → M β)
    (proj : σ → σ') (IsBrk : σ' → σ → Prop) (IsRet : σ' → ρ → Prop)
    (hcond : ∀ s h,
      (cond s >>= fun (c, s1) => pure (c, proj s1)) h = cond' (proj s) h)
    (hbody : ∀ s h,
      match body s h with
      | .error e => body' (proj s) h = .error e
      | .ok (.next s1, h1) | .ok (.cont s1, h1) => body' (proj s) h = .ok (proj s1, h1)
      | .ok (.brk s1, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsBrk st s1
      | .ok (.ret r, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsRet st r)
    (hbrkCond : ∀ st s1 h, IsBrk st s1 → cond' st h = .ok ((false, st), h))
    (hretCond : ∀ st r h, IsRet st r → cond' st h = .ok ((false, st), h))
    (hdone : ∀ s h, tail' (proj s) h = k (.ok s) h)
    (hbrk : ∀ st s1 h, IsBrk st s1 → tail' st h = k (.ok s1) h)
    (hret : ∀ st r h, IsRet st r → tail' st h = k (.error r) h)
    (h : Heap)
    (hnf : (cwhile cond' body' (proj s) >>= tail') h ≠ .error .outOfFuel) :
    (cwhileCtrl cond body s >>= k) h = (cwhile cond' body' (proj s) >>= tail') h :=
  cwhileCtrl_go_eq_cwhile_go_of_nofuel cond body cond' body' k tail' proj IsBrk IsRet
    hcond hbody hbrkCond hretCond hdone hbrk hret fuel s h hnf

theorem cforEverRet_go_eq_cwhile_go_of_nofuel {σ σ' ρ : Type}
    (body : σ → M (LoopStep σ ρ)) (k : σ → M ρ)
    (cond' : σ' → M (Bool × σ')) (body' : σ' → M σ') (tail' : σ' → M ρ)
    (proj : σ → σ') (IsBrk : σ' → σ → Prop) (IsRet : σ' → ρ → Prop)
    (hcondRun : ∀ s h, cond' (proj s) h = .ok ((true, proj s), h))
    (hbody : ∀ s h,
      match body s h with
      | .error e => body' (proj s) h = .error e
      | .ok (.next s1, h1) | .ok (.cont s1, h1) => body' (proj s) h = .ok (proj s1, h1)
      | .ok (.brk s1, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsBrk st s1
      | .ok (.ret r, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsRet st r)
    (hbrkCond : ∀ st s1 h, IsBrk st s1 → cond' st h = .ok ((false, st), h))
    (hretCond : ∀ st r h, IsRet st r → cond' st h = .ok ((false, st), h))
    (hbrk : ∀ st s1 h, IsBrk st s1 → tail' st h = k s1 h)
    (hret : ∀ st r h, IsRet st r → tail' st h = .ok (r, h)) :
    ∀ n s h,
      (cwhile.go cond' body' n (proj s) >>= tail') h ≠ .error .outOfFuel →
      (cforEver.go body n s >>= fun | .error r => pure r | .ok s1 => k s1) h =
      (cwhile.go cond' body' n (proj s) >>= tail') h := by
  intro n
  induction n with
  | zero =>
    intro s h hnf
    rw [bind_app, cwhile.go] at hnf
    exact absurd rfl hnf
  | succ n ih =>
    intro s h hnf
    rw [bind_app, cwhile_go_succ, hcondRun s h] at hnf
    rw [bind_app, cforEver_go_succ, bind_app, cwhile_go_succ, hcondRun s h]
    dsimp only at hnf ⊢
    have hb := hbody s h
    rcases hbo : body s h with e | ⟨step, h1⟩
    · rw [hbo] at hb; simp [hb]
    · rw [hbo] at hb
      cases step with
      | next s1 =>
        rw [hb] at hnf ⊢
        exact ih s1 h1 hnf
      | cont s1 =>
        rw [hb] at hnf ⊢
        exact ih s1 h1 hnf
      | brk s1 =>
        rcases hb with ⟨st, hbe, his⟩
        rw [hbe] at hnf ⊢
        dsimp only at hnf ⊢
        cases n with
        | zero =>
          rw [cwhile.go] at hnf
          exact absurd rfl hnf
        | succ m =>
          rw [cwhile_go_succ, hbrkCond st s1 h1 his]
          dsimp only
          exact (hbrk st s1 h1 his).symm
      | ret r =>
        rcases hb with ⟨st, hbe, his⟩
        rw [hbe] at hnf ⊢
        dsimp only at hnf ⊢
        cases n with
        | zero =>
          rw [cwhile.go] at hnf
          exact absurd rfl hnf
        | succ m =>
          rw [cwhile_go_succ, hretCond st r h1 his]
          dsimp only
          exact (hret st r h1 his).symm

theorem cforEverRet_eq_cwhile_of_nofuel {σ σ' ρ : Type}
    (body : σ → M (LoopStep σ ρ)) (s : σ) (k : σ → M ρ)
    (cond' : σ' → M (Bool × σ')) (body' : σ' → M σ') (tail' : σ' → M ρ)
    (proj : σ → σ') (IsBrk : σ' → σ → Prop) (IsRet : σ' → ρ → Prop)
    (hcondRun : ∀ s h, cond' (proj s) h = .ok ((true, proj s), h))
    (hbody : ∀ s h,
      match body s h with
      | .error e => body' (proj s) h = .error e
      | .ok (.next s1, h1) | .ok (.cont s1, h1) => body' (proj s) h = .ok (proj s1, h1)
      | .ok (.brk s1, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsBrk st s1
      | .ok (.ret r, h1) => ∃ st, body' (proj s) h = .ok (st, h1) ∧ IsRet st r)
    (hbrkCond : ∀ st s1 h, IsBrk st s1 → cond' st h = .ok ((false, st), h))
    (hretCond : ∀ st r h, IsRet st r → cond' st h = .ok ((false, st), h))
    (hbrk : ∀ st s1 h, IsBrk st s1 → tail' st h = k s1 h)
    (hret : ∀ st r h, IsRet st r → tail' st h = .ok (r, h))
    (h : Heap)
    (hnf : (cwhile cond' body' (proj s) >>= tail') h ≠ .error .outOfFuel) :
    cforEverRet body s k h = (cwhile cond' body' (proj s) >>= tail') h :=
  cforEverRet_go_eq_cwhile_go_of_nofuel body k cond' body' tail' proj IsBrk IsRet
    hcondRun hbody hbrkCond hretCond hbrk hret fuel s h hnf

end C
