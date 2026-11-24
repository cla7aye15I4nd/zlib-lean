import ZlibF.Proof.«infback.c.repeat-fields»

/-! # Source equality for literal code lengths and the three repeat symbols -/
namespace Zlib.Infback.Equality
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback

namespace Shared

/-- Decode one code length with the current registers. `tail` checks and writes a repeat. -/
def currentStep (st : InflateStatePtr) (need : UInt32 → X Unit) (reject : M Unit) (tail : X Bool) : X Bool := do
  if (← get).here.val < 16 then
    DROPBITS (← get).here.bits.toUInt32
    appendCurrentCode st
    return false
  else
    if (← get).here.val == 16 then
      need ((← get).here.bits.toUInt32 + 2)
      DROPBITS (← get).here.bits.toUInt32
      if (← rdS st (·.«have»)) == 0 then
        reject
        return true
      -- len = (unsigned)(state->lens[state->have - 1]); copy = 3 + BITS(2); DROPBITS(2);
      setPreviousLength st
      setRepeatCount 3 2
      DROPBITS 2
    else if (← get).here.val == 17 then
      need ((← get).here.bits.toUInt32 + 3)
      DROPBITS (← get).here.bits.toUInt32
      modify fun l => { l with len := 0 }
      setRepeatCount 3 3
      DROPBITS 3
    else
      need ((← get).here.bits.toUInt32 + 7)
      DROPBITS (← get).here.bits.toUInt32
      modify fun l => { l with len := 0 }
      setRepeatCount 11 7
      DROPBITS 7
    tail

/-- The safety proof takes a snapshot of the decoded symbol before refilling input. -/
def earlierStep (st : InflateStatePtr) (need : UInt32 → X Unit) (reject : M Unit) (tail : X Bool) : X Bool := do
  let here := (← get).here
  if here.val < 16 then
    DROPBITS here.bits.toUInt32
    let s ← ldInflateState st
    Ptr.store (← (lensP st).add (s.«have».toNat : Int)) here.val
    wrS st fun s => { s with «have» := s.«have» + 1 }
    return false
  else
    if here.val == 16 then
      need (here.bits.toUInt32 + 2)
      DROPBITS here.bits.toUInt32
      let s ← ldInflateState st
      if s.«have» == 0 then
        reject
        return true
      -- len = (unsigned)(state->lens[state->have - 1]); copy = 3 + BITS(2); DROPBITS(2);
      let v ← Ptr.index (lensP st) ((s.«have» - 1).toNat : Int)
      let b ← BITS 2
      modify fun l => { l with len := v.toUInt32, copy := 3 + b }
      DROPBITS 2
    else if here.val == 17 then
      need (here.bits.toUInt32 + 3)
      DROPBITS here.bits.toUInt32
      let b ← BITS 3
      modify fun l => { l with len := 0, copy := 3 + b }
      DROPBITS 3
    else
      need (here.bits.toUInt32 + 7)
      DROPBITS here.bits.toUInt32
      let b ← BITS 7
      modify fun l => { l with len := 0, copy := 11 + b }
      DROPBITS 7
    tail

private def consume (need : UInt32 → X Unit) (added : UInt32) (k : X Bool) : X Bool := do
  need ((← get).here.bits.toUInt32 + added)
  DROPBITS (← get).here.bits.toUInt32
  k

private def saved (need : UInt32 → X Unit) (code : Code) (added : UInt32) (k : X Bool) : X Bool := do
  need (code.bits.toUInt32 + added)
  DROPBITS code.bits.toUInt32
  k

private theorem consume_run (need : UInt32 → X Unit) (keep : ∀ (n : UInt32) (code : Code), CodeFrame.KeepsCode code (need n)) (n : UInt32) (k : X Bool) (l : IL) (h : Heap) :
    runX (consume need n k) l h = runX (saved need l.here n k) l h := by
  unfold consume saved
  rw [runX_bind, runX_get]
  exact codeAfter _ (fun v => keep (l.here.bits.toUInt32+n) v)
    (fun code _ => do DROPBITS code.bits.toUInt32; k) l h

private def putLiteral (st : InflateStatePtr) : X Bool := do
  DROPBITS (← get).here.bits.toUInt32
  appendCurrentCode st
  return false

private def savedLiteral (st : InflateStatePtr) (code : Code) : X Bool := do
  DROPBITS code.bits.toUInt32
  appendLength st code.val
  return false

private theorem literal_run (st : InflateStatePtr) (l : IL) (h : Heap) :
    runX (putLiteral st) l h = runX (savedLiteral st l.here) l h := by
  unfold putLiteral savedLiteral appendCurrentCode
  simp only [x_bind_assoc]
  rw [runX_bind, runX_get]
  simpa only [x_bind_assoc] using codeAfter _ (fun v => CodeFrame.drop v l.here.bits.toUInt32)
    (fun code _ => do appendLength st code.val; return false) l h

private def previous (st : InflateStatePtr) (reject : M Unit) (tail : X Bool) : X Bool := do
  let s ← ldInflateState st
  if s.«have» == 0 then
    reject
    return true
  let v ← Ptr.index (lensP st) ((s.«have» - 1).toNat : Int)
  let b ← BITS 2
  modify fun l => { l with len := v.toUInt32, copy := 3 + b }
  DROPBITS 2
  tail

private def zeros (n base : UInt32) (tail : X Bool) : X Bool := do
  let b ← BITS n
  modify fun l => {l with len := 0, copy := base + b}
  DROPBITS n
  tail

private def splitCurrent (st : InflateStatePtr) (need : UInt32 → X Unit) (reject : M Unit) (tail : X Bool) : X Bool := do
  if (← get).here.val < 16 then putLiteral st
  else if (← get).here.val == 16 then consume need 2 (previous st reject tail)
  else if (← get).here.val == 17 then consume need 3 (zeros 3 3 tail)
  else consume need 7 (zeros 7 11 tail)

private def splitEarlier (st : InflateStatePtr) (need : UInt32 → X Unit) (reject : M Unit) (tail : X Bool) : X Bool := do
  let code := (← get).here
  if code.val < 16 then savedLiteral st code
  else if code.val == 16 then saved need code 2 (previous st reject tail)
  else if code.val == 17 then saved need code 3 (zeros 3 3 tail)
  else saved need code 7 (zeros 7 11 tail)

private theorem split_eq (st : InflateStatePtr) (need : UInt32 → X Unit) (reject : M Unit) (keep : ∀ (n : UInt32) (code : Code), CodeFrame.KeepsCode code (need n)) (tail : X Bool) : splitCurrent st need reject tail = splitEarlier st need reject tail := by
  funext l h
  change runX _ l h = runX _ l h
  rw [runX_bind, runX_get, runX_bind, runX_get]
  by_cases a : l.here.val < 16
  · simpa only [a, ↓reduceIte] using literal_run st l h
  · simp only [a, ↓reduceIte]
    rw [runX_bind, runX_get]
    by_cases b : (l.here.val == 16) = true
    · simpa only [b, ↓reduceIte] using consume_run need keep 2 (previous st reject tail) l h
    · simp only [b, Bool.false_eq_true, ↓reduceIte]
      rw [runX_bind, runX_get]
      by_cases d : (l.here.val == 17) = true
      · simpa only [d, ↓reduceIte] using consume_run need keep 3 (zeros 3 3 tail) l h
      · simpa only [d, Bool.false_eq_true, ↓reduceIte] using consume_run need keep 7 (zeros 7 11 tail) l h

/-- Equal executions for every continuation, heap, and callback of the value-style protocol. -/
theorem steps_factored_eq (st : InflateStatePtr) (need : UInt32 → X Unit) (reject : M Unit) (keep : ∀ (n : UInt32) (code : Code), CodeFrame.KeepsCode code (need n)) (tail : X Bool) : currentStep st need reject tail = earlierStep st need reject tail := by
  calc
    _ = splitCurrent st need reject tail := by
      delta currentStep splitCurrent putLiteral consume previous zeros
      simp only [prevCountAt st reject, zeroCount]
    _ = splitEarlier st need reject tail := split_eq st need reject keep tail
    _ = _ := by
      delta splitEarlier earlierStep saved savedLiteral previous zeros
      simp only [appendLiteralFalse]
end Shared

abbrev currentStep (c : DecoderCtx) := Shared.currentStep c.st (Zlib.Infback.NEEDBITS c) (badMode c "invalid bit length repeat")
abbrev earlierStep (c : DecoderCtx) := Shared.earlierStep c.st (Zlib.Infback.NEEDBITS c) (badMode c "invalid bit length repeat")

theorem steps_factored_eq (c : BCtx) (tail : X Bool) : currentStep c tail = earlierStep c tail :=
  Shared.steps_factored_eq c.st (Zlib.Infback.NEEDBITS c) (badMode c "invalid bit length repeat")
    (fun n code => CodeFrame.need c code n) tail
end Zlib.Infback.Equality
