import Lean
import ZlibF.Zlib.«compress.c»
import ZlibF.Zlib.«uncompr.c»
import ZlibF.Zlib.«infback.c»
import ZlibF.Zlib.«gzclose.c»
import ZlibF.Zlib.«zlib.h»

/-! Recover direct C calls from elaborated definitions. Only explicit, recognized
forms have a source-level rendering. Unsupported definitions still have native C. -/

namespace Lean2C.Forward
open Lean Elab Term

private def cName? (n : Name) : Option String := do
  let .str _ s := n | none
  guard (!s.isEmpty && (s.toList.all fun c => c.isAlphanum || c == '_'))
  return s

private partial def expr? (params : List String) (e : Expr) : Option String := do
  match e.consumeMData with
  | .bvar i => params[i]?
  | .lit (.natVal n) => some (toString n)
  | e =>
    let .const n _ := e.getAppFn | none
    let args := e.getAppArgs
    if n == ``OfNat.ofNat then
      let .lit (.natVal value) := args[1]! | none
      return toString value
    if n == ``Neg.neg then return "-" ++ (← expr? params args.back!)
    -- An unsigned 32-to-64 widening is implicit in a C argument of type z_size_t.
    if n == ``UInt32.toUInt64 then return ← expr? params args.back!
    if n == ``Zlib.Zutil.strLit then return ← expr? params args.back!
    guard ((`Zlib).isPrefixOf n || (`C).isPrefixOf n)
    let name ← cName? n
    if args.isEmpty then return name
    let values ← args.toList.mapM (expr? params)
    return name ++ "(" ++ String.intercalate ", " values ++ ")"

private def body? (unitResult : Bool) (e : Expr) (params : List String := []) : Option String := do
  match e with
  | .lam n _ b _ => body? unitResult b ((← cName? n) :: params)
  | e =>
    guard e.isApp
    let .const callee _ := e.getAppFn | none
    guard ((`Zlib).isPrefixOf callee)
    let stmt := if unitResult then "" else "return "
    return "{\n    " ++ stmt ++ (← expr? params e) ++ ";\n}"

/-- Read the kernel expressions of real definitions. No docstrings or C inputs
are available to this traversal. -/
elab "forwardBodies%" : term => do
  let env ← getEnv
  let mut bodies : Array (String × String) := #[]
  for (name, info) in env.constants.toList do
    unless (`Zlib).isPrefixOf name do continue
    let .defnInfo defn := info | continue
    let unitResult := defn.type.getForallBody.getAppArgs.back? == some (Lean.mkConst ``Unit)
    if let some body := body? unitResult defn.value then bodies := bodies.push (name.toString, body)
  return toExpr (bodies.qsort fun a b => a.1 < b.1)

/-- Record the pinned compiler's symbol spelling for each model definition. -/
elab "nativeSymbols%" : term => do
  let env ← getEnv
  let mut symbols : Array (String × String) := #[]
  for (name, info) in env.constants.toList do
    if (`Zlib).isPrefixOf name && info matches .defnInfo _ then
      symbols := symbols.push (name.toString, getSymbolStem env name)
  return toExpr (symbols.qsort fun a b => a.1 < b.1)

def symbols : Array (String × String) := nativeSymbols%
def bodies : Array (String × String) := forwardBodies%

end Lean2C.Forward
