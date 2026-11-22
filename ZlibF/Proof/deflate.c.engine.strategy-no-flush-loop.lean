import ZlibF.Proof.«deflate.c.engine.strategy-refill»
import ZlibF.Proof.«deflate.c.engine.loops»

/-! # The complete NO_FLUSH strategy loop including full block output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Input-pointer validity is independent of simultaneous output. -/
theorem input_valid_accounting_output {z z' : ZStream} {used produced : Nat}
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (account : StreamAccounting z z' used produced) :
    z'.avail_in ≠ 0 → z'.next_in ≠ .null := by
  intro nonempty
  have oldNonempty : z.avail_in ≠ 0 := by
    intro zero
    have count := account.2.2.1
    rw [zero] at count
    simp only [show (0 : UInt32).toNat = 0 from rfl] at count
    have empty : z'.avail_in.toNat = 0 := by omega
    exact nonempty (UInt32.toNat_inj.mp empty)
  cases pointer : z.next_in with
  | null => exact False.elim (valid oldNonempty pointer)
  | ref ref off =>
    rw [account.2.2.2.2.1, pointer]
    simp only [advance, ne_eq, reduceCtorEq, not_false_eq_true]

end Zlib.Deflate.Engine.Proofs
