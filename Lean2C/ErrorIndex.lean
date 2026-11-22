import Lean
import Std.Tactic.BVDecide
import ZlibF.Zlib.«zutil.c»

namespace Lean2C.ErrorIndex
open Lean Elab Term

/-- Extract the index from the table lookup itself. A different table, index
conversion, success continuation, or failure action requires a new lowering. -/
def extract? (body : Expr) : Option Expr := do
  let .lam n t inner bi := body | none
  let .letE _ _ index lookup _ := inner | none
  guard (lookup.isAppOfArity `Zlib.Zutil.zError.match_1 4)
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
  let some idx := extract? d.value | throwError "unsupported zError table lookup"
  return idx

def index : Int32 → Int32 := errorIndex%

/-- The signed C expression can index the array directly on every input. -/
theorem inBounds (err : Int32) :
    0 ≤ index err ∧ index err < Int32.ofNat Zlib.Zutil.z_errmsg.size := by
  change 0 ≤ index err ∧ index err < (10 : Int32)
  unfold index
  bv_decide

end Lean2C.ErrorIndex
