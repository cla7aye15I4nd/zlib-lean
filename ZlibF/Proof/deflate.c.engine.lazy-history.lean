import ZlibF.Proof.«deflate.c.engine.slow-defer»
import ZlibF.Proof.«deflate.c.engine.tally-match»

/-! # Matching history across the slow strategy's lazy step

Only an improving search establishes a new current match. A stale
position returned at the old length is never treated as such a witness.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- At loop entry a retained match belongs to the previous byte. -/
def WindowLazyHistory (d : DeflateState) (wa : Array UInt8) : Prop :=
  d.match_length.toNat ≤ 258 ∧
    (3 ≤ d.match_length.toNat →
      1 ≤ d.strstart.toNat ∧ d.match_available ≠ 0 ∧
      d.match_length.toNat ≤ d.lookahead.toNat + 1 ∧
      GoodMatch wa (d.strstart.toNat - 1) d.w_size.toNat d.match_start.toNat d.match_length.toNat)

/-- The actual match-emission test has failed. A current match of length
at least MIN_MATCH must therefore improve the previous lazy length. -/
theorem literal_search_improves {d : DeflateState}
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (large : 3 ≤ d.match_length.toNat) : d.prev_length.toNat < d.match_length.toNat := by
  by_cases previous : MIN_MATCH_u ≤ d.prev_length
  · have notle : ¬ d.match_length ≤ d.prev_length := by
      intro le
      have same : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true := by
        simp only [previous, le, decide_true, Bool.true_and]
      rw [branch] at same
      contradiction
    rw [UInt32.le_iff_toNat_le] at notle
    omega
  · rw [UInt32.le_iff_toNat_le] at previous
    change ¬ 3 ≤ d.prev_length.toNat at previous
    omega

end Zlib.Deflate.Engine.Proofs
