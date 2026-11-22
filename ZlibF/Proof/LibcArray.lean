import ZlibF.Runtime.LibcMemory

namespace C

theorem copyRange.succ {T : Type} [Inhabited T] (d s : Array T) (doff soff n : Nat) :
    copyRange d s doff soff (n + 1) = (copyRange d s doff soff n).set! (doff + n) s[soff + n]! := by
  unfold copyRange; rw [List.range_succ, List.foldl_append]; rfl

/-- `copyRange`, pointwise: positions in `[doff, doff + n)` get the source bytes, the others keep their value. -/
theorem copyRange.getElem? {T : Type} [Inhabited T] (d s : Array T) (doff soff n : Nat) (i : Nat)
    (hfit : doff + n ≤ d.size) :
    (copyRange d s doff soff n)[i]? = if doff ≤ i ∧ i < doff + n then some s[soff + (i - doff)]! else d[i]? := by
  induction n generalizing i with
  | zero => simp [copyRange]; intro h1 h2; omega
  | succ n ih =>
    rw [copyRange.succ, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ih i (by omega)]
    have hs : (copyRange d s doff soff n).size = d.size := size_copyRange _ _ _ _ _
    by_cases hi : doff + n = i
    · subst hi
      simp [hs, show doff + n < d.size by omega]
    · simp [hi]
      by_cases h1 : doff ≤ i ∧ i < doff + n
      · simp [h1]; omega
      · simp [h1]; intro _ ; omega

end C
