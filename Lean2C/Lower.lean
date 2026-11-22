import Lean2C.C
import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«uncompr.c»

namespace Lean2C.Lower
open Lean CSource

private structure Locals where
  values : List (Option Value) := []
  /-- Exclusive bounds from true branches on immutable unsigned Lean locals. -/
  bounds : List (Value × Nat) := []

private def Locals.push (ctx : Locals) (v : Option Value) : Locals :=
  { ctx with values := v :: ctx.values }

private def uintWidth? : Ty → Option Nat
  | .u8 => some 8 | .u16 => some 16 | .u32 => some 32 | .u64 => some 64
  | _ => none

private def Locals.inTrueBranch (ctx : Locals) (cond : Value) : Locals := Id.run do
  if let .op _ op (v@(.var t _)) (.num rt k) := cond then
    if let some bits := uintWidth? t then
      if rt == t && k < 2^bits && ctx.values.contains (some v) && (op == "<" || op == "<=") then
        let limit := if op == "<" then k else k + 1
        return { ctx with bounds := (v, limit) :: ctx.bounds }
  return ctx

private def boundedCount (ctx : Locals) (r : Value) (width : Nat) : Bool :=
  match r with
  | .num _ k => k < width
  | .op _ "&" _ (.num _ mask) => mask < width
  | .op _ "%" _ (.num _ divisor) => 0 < divisor && divisor ≤ width
  | .var .. => ctx.bounds.any fun (v, limit) => r == v && limit ≤ width
  | _ => false

private def ty? (e : Expr) : Option Ty :=
  match e.getAppFn.constName? with
  | some ``UInt8 => some .u8 | some ``UInt16 => some .u16
  | some ``UInt32 => some .u32 | some ``UInt64 => some .u64
  | some ``Int32 => some .i32 | some ``Int64 => some .i64
  | some ``Bool => some .bool | some ``C.BPtr => some (.ptr .u8)
  | _ => none

private def ident? (n : Name) : Option String := do
  let .str _ s := n | none
  guard (!s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_'))
  return s

private def fresh (n : Name) (ctx : Locals) : String := Id.run do
  let suggested := (ident? n).getD "tmp"
  let base := if suggested.startsWith "__" then "tmp" else suggested
  let used := ctx.values.filterMap fun v => match v with
    | some (.var _ s) => some s
    | _ => none
  if !used.contains base then return base
  for i in [:used.length + 1] do
    let s := base ++ "_" ++ toString i
    if !used.contains s then return s
  return base ++ "_local"

private def operator? (n : Name) : Option String := do
  let symbols := [(``HAdd.hAdd, "+"), (``HSub.hSub, "-"), (``HMul.hMul, "*"),
    (``HMod.hMod, "%"), (``HAnd.hAnd, "&"), (``HOr.hOr, "|"), (``HXor.hXor, "^"),
    (``HShiftLeft.hShiftLeft, "<<"), (``HShiftRight.hShiftRight, ">>"),
    (``LT.lt, "<"), (``LE.le, "<="), (``GT.gt, ">"), (``GE.ge, ">="),
    (``BEq.beq, "=="), (``Eq, "=="), (``bne, "!="), (``Bool.and, "&&"), (``Bool.or, "||")]
  (symbols.lookup n)

private def asTy (v : Value) (t : Ty) : Value := if v.type == t then v else .cast t v

private partial def value? (e : Expr) (ctx : Locals) (wanted : Option Ty := none) : Option Value := do
  let e := e.consumeMData
  if let .bvar i := e then return ← ctx.values[i]?.join
  if let .lit (.natVal k) := e then return .num (wanted.getD .i32) k
  let n ← e.getAppFn.constName?
  let a := e.getAppArgs
  if n == ``OfNat.ofNat then
    let .lit (.natVal k) := a[1]! | none
    let t := ((ty? a[0]!).orElse (fun _ => wanted) |>.getD .i32)
    return .num t ((uintWidth? t).map (fun bits => k % (2^bits)) |>.getD k)
  if n == ``Bool.true then return .num .bool 1
  if n == ``Bool.false then return .num .bool 0
  if n == ``Decidable.decide then return ← value? a[0]! ctx (.some .bool)
  if n == ``Eq && a.back!.isConstOf ``Bool.true then return ← value? a[a.size-2]! ctx
  if n == ``ite then
    let cond ← value? a[1]! ctx
    return .choose cond (← value? a[3]! (ctx.inTrueBranch cond) wanted) (← value? a[4]! ctx wanted)
  if n == ``Pure.pure || n == ``liftM then return ← value? a.back! ctx wanted
  if n == ``C.index8 then return .index .u8 (← value? a[0]! ctx) (← value? a[1]! ctx)
  if n == ``C.load8 then return .load .u8 (← value? a.back! ctx)
  if n == ``UInt32.toNat || n == ``UInt8.toNat then return ← value? a.back! ctx
  if n == ``Nat.cast then
    -- C.index8 takes an Int offset. A zero-extended byte or unsigned index
    -- fits the signed LP64 offset without truncation.
    let x ← value? a.back! ctx
    guard (a[0]!.isConstOf ``Int && (x.type == .u8 || x.type == .u32))
    return x
  if n == ``UInt32.toUInt64 then return asTy (← value? a.back! ctx) .u64
  if n == ``UInt64.toUInt32 then return asTy (← value? a.back! ctx) .u32
  if let some op := operator? n then
    let l ← value? a[a.size-2]! ctx
    let r ← value? a.back! ctx
    let rel := ["<", "<=", ">", ">=", "==", "!=", "&&", "||"].contains op
    if !rel then
      -- A Nat/Int operator has unbounded semantics; a C-width result requires
      -- an explicit model type. Narrow unsigned operations wrap after promotion.
      let t ← ty? a[2]!
      let mut rhs := r
      if op == "<<" || op == ">>" then
        let width ← uintWidth? t
        guard (l.type == t && r.type == t)
        -- Lean reduces every count modulo its word width. A raw C shift
        -- is valid only when a bound already follows from this expression.
        unless boundedCount ctx r width do rhs := .op t "%" r (.num .i32 width)
      -- A small int constant beside an unsigned word gets the C promotions
      -- of the original bitwise expression. Shift operands promote separately.
      if (t == .u32 || t == .u64) && ["&", "|", "^", "<<", ">>"].contains op then
        if let .num _ k := rhs then
          if k < 2^31 then rhs := .num .i32 k
      if t == .u8 || t == .u16 then
        -- C promotes small integers to signed int. Use unsigned arithmetic
        -- before narrowing so a 16-bit product cannot overflow signed int.
        return .cast t (.op .u32 op (asTy l .u32) (asTy rhs .u32))
      return .op t op l rhs
    return .op .bool op l r
  if a.isEmpty && ((`C).isPrefixOf n || (`Zlib).isPrefixOf n) then
    let s ← ident? n
    guard (s.toUpper == s)
    return .var (← wanted) s
  if (`Zlib).isPrefixOf n && !a.isEmpty then
    return .call (← wanted) (← ident? n) (← a.toList.mapM (fun x => value? x ctx))
  none

private def pair? (e : Expr) : Option (Expr × Expr) := do
  guard (e.isAppOfArity ``Prod.mk 4)
  return (e.getAppArgs[2]!, e.getAppArgs[3]!)

/-- A match on a product generated by Lean's equation compiler. The scrutinee
is the lambda argument and the only alternative binds its two fields. -/
private def splitPair? (env : Environment) (fn : Expr) : Option (Name × Ty × Name × Ty × Expr) := do
  let .lam _ domain body _ := fn | none
  guard (domain.isAppOfArity ``Prod 2)
  let matcher ← body.getAppFn.constName?
  guard (Meta.isMatcherCore env matcher && body.getAppArgs.size == 3)
  guard (body.getAppArgs[1]! == .bvar 0)
  let .lam x xt (.lam y yt inner _) _ := body.getAppArgs[2]! | none
  return (x, ← ty? xt, y, ← ty? yt, inner)

private inductive Sink where
  | ret (type : Ty)
  | outParam (ptr : Value) (type : Ty)
  | update (x y : Value)

private def finish (sink : Sink) (e : Expr) (ctx : Locals) : Option (List Stmt) := do
  match sink with
  | .ret t => return [.ret (← value? e ctx t)]
  | .outParam p t =>
    let (a, b) ← pair? e
    return [.assign (.load t p) (← value? b ctx t), .ret (← value? a ctx t)]
  | .update x y =>
    let (a, b) ← pair? e
    let vx ← value? a ctx x.type
    let vy ← value? b ctx y.type
    let tmp := fresh `next_value ctx
    -- Tuple updates are simultaneous. Save the first RHS before changing y.
    return [.decl x.type tmp (some vx), .assign y vy, .assign x (.var x.type tmp)]

private partial def stmts? (env : Environment) (e : Expr) (ctx : Locals) (sink : Sink) : Option (List Stmt) := do
  let e := e.consumeMData
  if let .letE n t rhs body _ := e then
    let ct ← ty? t
    let v ← value? rhs ctx ct
    let name := fresh n ctx
    return .decl ct name (some v) :: (← stmts? env body (ctx.push (some (.var ct name))) sink)
  if e.isAppOfArity ``ite 5 then
    let a := e.getAppArgs
    let cond ← value? a[1]! ctx
    return [.branch cond (← stmts? env a[3]! (ctx.inTrueBranch cond) sink) (← stmts? env a[4]! ctx sink)]
  if e.isAppOfArity ``Pure.pure 4 then return ← finish sink e.getAppArgs.back! ctx
  if e.isAppOfArity ``Bind.bind 6 then
    let a := e.getAppArgs
    let action := a[4]!
    let cont := a[5]!
    if action.isAppOfArity ``C.cwhile 4 then
      let w := action.getAppArgs
      let (_, xt, _, yt, test) ← splitPair? env w[1]!
      let (xn, xt', yn, yt', step) ← splitPair? env w[2]!
      let (_, xt'', _, yt'', afterLoop) ← splitPair? env cont
      guard (xt == xt' && xt == xt'' && yt == yt' && yt == yt'')
      let x := Value.var xt (fresh xn ctx)
      let y := Value.var yt (fresh yn (ctx.push (some x)))
      let locals := ((ctx.push none).push (some x)).push (some y)
      guard (test.isAppOfArity ``Pure.pure 4)
      let (guardExpr, remaining) ← pair? test.getAppArgs.back!
      let (left, right) ← pair? remaining
      guard (left == .bvar 1 && right == .bvar 0)
      let (ix, iy) ← pair? w[3]!
      let cond ← value? guardExpr locals
      let loopBody ← stmts? env step (locals.inTrueBranch cond) (.update x y)
      return [.decl xt x.render (some (← value? ix ctx xt)), .decl yt y.render (some (← value? iy ctx yt)),
        .loop cond loopBody] ++ (← stmts? env afterLoop locals sink)
    let .lam n t rest _ := cont | none
    let ct ← ty? t
    let v ← value? action ctx ct
    let name := fresh n ctx
    return .decl ct name (some v) :: (← stmts? env rest (ctx.push (some (.var ct name))) sink)
  finish sink e ctx

/-- Name of the C out-parameter represented by the first scalar argument. -/
def firstOutParam? (name : Name) : Option String :=
  if name == ``Zlib.Inflate.syncsearch then some "have" else none

/-- The out-parameter adapter supplies the C ABI information removed by the
original model. All operations in the function body still come from its Expr. -/
def lower? (env : Environment) (name : Name) (type body : Expr) : Option String := do
  let outName := firstOutParam? name
  let rec args (e : Expr) (ctx : Locals) : Option (List Stmt) := do
    if let .lam n t b _ := e then
      let ct ← ty? t
      let mut v := Value.var ct (← ident? n)
      if ctx.values.isEmpty then
        if let some p := outName then v := .load ct (.var (.ptr ct) p)
      return ← args b (ctx.push (some v))
    let rt := type.getForallBody
    let result := if rt.isAppOfArity ``C.M 1 then rt.getAppArgs.back! else rt
    if let some p := outName then
      return ← stmts? env e ctx (.outParam (.var (.ptr .u32) p) .u32)
    return ← stmts? env e ctx (.ret (← ty? result))
  return renderBody (← args body {})

end Lean2C.Lower
