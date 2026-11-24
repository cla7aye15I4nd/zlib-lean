import ZlibF.Proof.«infback.c.code-register»

/-! # Decoder field reads and writes used by the length and distance codes -/
namespace Zlib.Infback.Equality
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback

private theorem extra_after_write (st : InflateStatePtr) (extra : UInt32) (k : UInt32 → X α) :
    (do wrS st fun s => { s with extra }
        k (← rdS st (·.extra)) : X α) =
    (do wrS st fun s => { s with extra }
        k extra : X α) := by
  funext l h
  change runX _ l h = runX _ l h
  cases st with
  | none => rfl
  | some ref =>
    obtain ⟨i⟩ := ref
    cases hs : h.istates i with
    | none => simp [runX_bind, runX_lift, wrI_eq, hs]
    | some s =>
      simp [runX_bind, runX_lift, wrI_eq, rdI_eq, hs]

theorem two_state_writes (st : InflateStatePtr) (f g : InflateState → InflateState)
    (k : X α) :
    (do wrS st f
        wrS st g
        k : X α) =
    (do wrS st (fun s => g (f s))
        k : X α) := by
  funext l h
  change runX _ l h = runX _ l h
  cases st with
  | none => rfl
  | some ref =>
    obtain ⟨i⟩ := ref
    cases hs : h.istates i with
    | none => simp [runX_bind, runX_lift, wrI_eq, hs]
    | some s => simp [runX_bind, runX_lift, wrI_eq, hs]

set_option linter.unusedSimpArgs false in
theorem extend_known (c : DecoderCtx) (dist : Bool) (ex : UInt32) (k : X α) :
    (do wrS c.st (fun s => {s with extra := ex})
        extendExtra c dist
        k : X α) =
    (do wrS c.st (fun s => {s with extra := ex})
        if ex != 0 then
          needExtra c
          let b ← BITS (← rdS c.st (·.extra))
          if dist then wrS c.st fun s => { s with offset := s.offset + b }
          else wrS c.st fun s => { s with length := s.length + b }
          DROPBITS (← rdS c.st (·.extra))
        k : X α) := by
  unfold extendExtra
  simp only [x_bind_assoc]
  rw [extra_after_write]
  by_cases he : (ex != 0) = true <;> cases dist <;> simp only [he, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, ite_false, x_bind_assoc, x_pure_bind]

theorem zeroCount (base width : UInt32) (k : X Bool) :
    (do modify fun l => {l with len := 0}
        setRepeatCount base width
        k : X Bool) =
    (do let bits ← BITS width
        modify fun l => {l with len := 0, copy := base + bits}
        k : X Bool) := by
  funext l h
  change runX _ l h = runX _ l h
  simp only [setRepeatCount, BITS, runX_bind, runX_modify, runX_get, runX_lift, runX_pure]
  cases sh : shl32 1 width h with
  | error e => rfl
  | ok pair => obtain ⟨n, after⟩ := pair; rfl

set_option linter.unusedSimpArgs false in
theorem prevCountAt (st : InflateStatePtr) (reject : M Unit) (k : X Bool) :
    (do if (← rdS st (·.«have»)) == 0 then
          reject
          return true
        setPreviousLength st
        setRepeatCount 3 2
        k : X Bool) =
    (do let s ← ldInflateState st
        if s.«have» == 0 then
          reject
          return true
        let v ← Ptr.index (lensP st) ((s.«have» - 1).toNat : Int)
        let b ← BITS 2
        modify fun l => { l with len := v.toUInt32, copy := 3 + b }
        k : X Bool) := by
  funext l h
  change runX _ l h = runX _ l h
  cases st with
  | none => rfl
  | some ref =>
    obtain ⟨i⟩ := ref
    cases hs : h.istates i with
    | none => simp [runX_bind, runX_lift, rdI_eq, ldInflateState, InflateStateRef.get, hs]
    | some s =>
      simp only [runX_bind, runX_lift, rdI_eq, hs, ldInflateState_ok (r := .tab i) hs,
        setPreviousLength, setRepeatCount, BITS, runX_get, runX_pure, runX_modify]
      by_cases noPrior : (s.«have» == 0) = true
      · simp only [noPrior, Bool.false_eq_true, ↓reduceIte, ite_false]
      · simp only [noPrior, Bool.false_eq_true, ↓reduceIte, ite_false, runX_bind, runX_lift, rdI_eq, hs, setPreviousLength,
          setRepeatCount, BITS, runX_get, runX_pure, runX_modify]
        cases read : Ptr.index (lensP (some (.tab i))) ((s.«have» - 1).toNat : Int) h with
        | error e => rfl
        | ok pair => obtain ⟨v, after⟩ := pair; rfl

theorem prevCount (c : BCtx) (k : X Bool) :
    (do if (← rdS c.st (·.«have»)) == 0 then
          badMode c "invalid bit length repeat"
          return true
        setPreviousLength c.st
        setRepeatCount 3 2
        k : X Bool) =
    (do let s ← ldInflateState c.st
        if s.«have» == 0 then
          badMode c "invalid bit length repeat"
          return true
        let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
        let b ← BITS 2
        modify fun l => { l with len := v.toUInt32, copy := 3 + b }
        k : X Bool) :=
  prevCountAt c.st (badMode c "invalid bit length repeat") k

theorem codeAfter (prog : X α) (keeps : ∀ v, CodeFrame.KeepsCode v prog)
    (k : Code → α → X β) (l : IL) (h : Heap) :
    runX (do let a ← prog; k (← get).here a) l h =
    runX (do let a ← prog; k l.here a) l h := by
  simp only [runX_bind, runX_get]
  cases ran : runX prog l h with
  | error e => rfl
  | ok pair =>
    obtain ⟨⟨v, regs⟩, after⟩ := pair
    cases v with
    | error e => rfl
    | ok a => simp only [keeps l.here _ _ _ _ _ rfl ran]

end Zlib.Infback.Equality
