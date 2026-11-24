import Lean
import ZlibF.Zlib.«zutil.c»

namespace Lean2C.ErrorIndex
open Lean Elab Term

/-- Extract the index from the table lookup itself. A different table, index
conversion, success continuation, or failure action requires a new lowering. -/
def extract? (env : Environment) (body : Expr) : Option Expr := do
  let .lam _ _ forward _ := body | none
  guard (forward.isAppOfArity ``Zlib.Zutil.errorMessage 1 && forward.appArg! == .bvar 0)
  let some (.defnInfo shared) := env.find? ``Zlib.Zutil.errorMessage | none
  let .lam n t inner bi := shared.value | none
  let .letE _ _ index lookup _ := inner | none
  guard (lookup.isAppOfArity `Zlib.Zutil.errorMessage.match_1 4)
  let a := lookup.getAppArgs
  guard (a[1]!.isAppOfArity ``GetElem?.getElem? 7)
  let la := a[1]!.getAppArgs
  guard (la[5]!.isConstOf ``Zlib.Zutil.z_errmsg && la[6]!.isAppOfArity ``Int.toNat 1)
  let signed := la[6]!.getAppArgs.back!
  guard (signed.isAppOfArity ``Int32.toInt 1 && signed.getAppArgs.back! == .bvar 0)
  let .lam _ _ hit _ := a[2]! | none
  let .lam _ _ miss _ := a[3]! | none
  guard (hit.isAppOfArity ``Zlib.Zutil.strLit 1 && hit.getAppArgs.back! == .bvar 0 &&
    miss.isAppOfArity ``C.ub 2)
  return .lam n t index bi

elab "errorIndex%" : term => do
  let some (.defnInfo d) := (← getEnv).find? ``Zlib.Zutil.zError | throwError "missing zError"
  let some idx := extract? (← getEnv) d.value | throwError "unsupported zError table lookup"
  return idx

def index : Int32 → Int32 := errorIndex%

/-- Inside the table guard the C subtraction has its mathematical value, between zero and eight. -/
theorem difference_on_domain (err : Int32) (inside : ¬ (err < -6 || err > 2) = true) :
    (2 - err).toInt = 2 - err.toInt ∧ 0 ≤ 2 - err.toInt ∧ 2 - err.toInt ≤ 8 := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int32.not_lt] at inside
  have lo : -6 ≤ err.toInt := by simpa using Int32.le_iff_toInt_le.mp inside.1
  have hi : err.toInt ≤ 2 := by simpa using Int32.le_iff_toInt_le.mp inside.2
  refine ⟨?_, by omega, by omega⟩
  rw [Int32.toInt_sub]
  exact Int.bmod_eq_of_le (by change -2147483648 ≤ 2 - err.toInt; omega)
    (by change 2 - err.toInt < 2147483648; omega)

/-- The signed C expression can index the array directly on every input. -/
theorem inBounds (err : Int32) :
    0 ≤ index err ∧ index err < Int32.ofNat Zlib.Zutil.z_errmsg.size := by
  change 0 ≤ index err ∧ index err < (10 : Int32)
  unfold index
  split
  · decide
  · rename_i inside
    obtain ⟨eq, lo, hi⟩ := difference_on_domain err inside
    rw [Int32.le_iff_toInt_le, Int32.lt_iff_toInt_lt, eq]
    change 0 ≤ 2 - err.toInt ∧ 2 - err.toInt < 10
    omega

end Lean2C.ErrorIndex
