import Lean2C.C
import Lean2C.ErrorIndex
import ZlibF.Runtime.CAbi
import ZlibF.Zlib.«compress.c»
import ZlibF.Zlib.«inflate.c»
import ZlibF.Zlib.«uncompr.c»
import ZlibF.Zlib.«gzclose.c»

namespace Lean2C.Lower
open Lean CSource

private structure Locals where
  abi : Bool := false
  constBytes : Bool := false
  env? : Option Environment := none
  values : List (Option Value) := []
  reserved : List String := []
  stackStreams : List String := []
  stackScalars : List String := []
  reservedVals : List Value := []
  tupleAt0 : List Value := []
  bounds : List (Value × Nat) := []

private def Locals.push (ctx : Locals) (v : Option Value) : Locals :=
  { ctx with values := v :: ctx.values }

private def Locals.localType (ctx : Locals) (t : Ty) : Ty :=
  if ctx.constBytes && t == .ptr .u8 then .ptr (.named "const unsigned char") else t

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

private partial def stripCAbi (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``C.CExport 1 || e.isAppOfArity ``C.CHidden 1 ||
     e.isAppOfArity ``C.CStatic 1 || e.isAppOfArity ``C.CStaticInline 1 then
    stripCAbi e.getAppArgs[0]!
  else if e.isAppOfArity ``C.CExportAs 2 || e.isAppOfArity ``C.COrder 2 then
    stripCAbi e.getAppArgs[1]!
  else e

private def ty? (e : Expr) (abi : Bool := false) : Option Ty := do
  let e := stripCAbi e
  if abi && e.isAppOfArity ``C.Ptr 1 && e.getAppArgs.back!.isConstOf ``C.BRef then return .ptr .u8
  match e.getAppFn.constName? with
  | some ``UInt8 => some .u8 | some ``UInt16 => some .u16
  | some ``UInt32 => some .u32 | some ``UInt64 => some .u64
  | some ``Int32 => some .i32 | some ``Int64 => some .i64
  | some ``C.ZOffT | some ``C.ZOff64T => some .i64
  | some ``C.CodeType | some ``C.ZCrcT | some ``C.ZWordT | some ``C.OutUInt32 => some .u32
  | some ``C.ConstBPtr | some ``C.CStr | some ``C.ConstCStr | some ``C.VoidPtr
  | some ``C.ConstVoidPtr | some ``C.PtrU64 | some ``C.OutInt32 | some ``C.StackScalar64 => some (.ptr .u8)
  | some ``C.StackStream => if !abi then none else some (.ptr (.named "z_stream"))
  | some ``Zlib.Adler32.Locals => if !abi then none else some (.named "adler_state")
  | some ``Zlib.Uncompr.UncLoop => if !abi then none else some (.named "unc_loop")
  | some ``C.ZStream => if !abi then none else some (.named "z_stream")
  | some ``C.ZStreamPtr => if !abi then none else some (.ptr (.named "z_stream"))
  | some ``C.GzFilePtr => if !abi then none else some (.named "gzFile")
  | some ``C.GzStatePtr => if !abi then none else some (.named "gz_statep")
  | some ``C.GzState => if !abi then none else some (.named "gz_state")
  | some ``Bool => some .bool | some ``C.BPtr => some (.ptr .u8)
  | _ => none

private def ident? (n : Name) : Option String := do
  let .str _ s := n | none
  guard (!s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '_'))
  return s

private def fresh (n : Name) (ctx : Locals) : String := Id.run do
  let suggested := (ident? n).getD "tmp"
  let base := if suggested.startsWith "__" then "tmp" else suggested
  let used := ctx.reserved ++ ctx.values.filterMap fun v => match v with
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

private def zstreamFields : List (String × Ty × Name) :=
  [("next_in", .ptr .u8, ``C.ZStream.next_in),
   ("avail_in", .u32, ``C.ZStream.avail_in),
   ("total_in", .u64, ``C.ZStream.total_in),
   ("next_out", .ptr .u8, ``C.ZStream.next_out),
   ("avail_out", .u32, ``C.ZStream.avail_out),
   ("total_out", .u64, ``C.ZStream.total_out),
   ("msg", .ptr (.named "char"), ``C.ZStream.msg),
   ("state", .ptr (.named "struct internal_state"), ``C.ZStream.state),
   ("zalloc", .named "alloc_func", ``C.ZStream.zalloc),
   ("zfree", .named "free_func", ``C.ZStream.zfree),
   ("opaque", .ptr .void, ``C.ZStream.opaque),
   ("data_type", .i32, ``C.ZStream.data_type),
   ("adler", .u64, ``C.ZStream.adler),
   ("reserved", .u64, ``C.ZStream.reserved)]

private def projTupleAt0? (ctx : Locals) (e : Expr) : Option Value := do
  guard (!ctx.tupleAt0.isEmpty)
  let rec index? (e : Expr) : Option Nat :=
    match e with
    | .bvar 0 => some 0
    | .app (.app (.app (.const ``Prod.snd _) _) _) arg => return (← index? arg) + 1
    | _ => none
  if e.isAppOfArity ``Prod.fst 3 then
    let idx ← index? e.getAppArgs.back!
    return ← ctx.tupleAt0[idx]?
  none

private partial def value? (e : Expr) (ctx : Locals) (wanted : Option Ty := none) : Option Value := do
  let e := e.consumeMData
  if let .bvar i := e then return ← ctx.values[i]?.join
  if let .lit (.natVal k) := e then return .num (wanted.getD .i32) k
  if ctx.abi then
    if let some v := projTupleAt0? ctx e then return v
  let n ← e.getAppFn.constName?
  let a := e.getAppArgs
  if n == ``OfNat.ofNat then
    let .lit (.natVal k) := a[1]! | none
    let t := ((ty? a[0]! ctx.abi).orElse (fun _ => wanted) |>.getD .i32)
    return .num t ((uintWidth? t).map (fun bits => k % (2^bits)) |>.getD k)
  if n == ``Bool.true then return .num .bool 1
  if n == ``Bool.false then return .num .bool 0
  if n == ``Decidable.decide then return ← value? a[0]! ctx (.some .bool)
  if n == ``Eq && a.back!.isConstOf ``Bool.true then return ← value? a[a.size-2]! ctx
  if n == ``ite then
    let cond ← value? a[1]! ctx
    return .choose cond (← value? a[3]! (ctx.inTrueBranch cond) wanted) (← value? a[4]! ctx wanted)
  if ctx.abi then
    if n == ``Zlib.Adler32.Locals.mk then
      return .record (.named "adler_state") (← a.toList.mapM (fun x => value? x ctx))
    if n.getPrefix == ``Zlib.Adler32.Locals && a.size == 1 then
      let field ← ident? n
      let ct ← [("adler", Ty.u64), ("sum2", .u64), ("buf", .ptr .u8),
                ("len", .u64), ("n", .u32)].lookup field
      return .field ct (← value? a[0]! ctx) field
    if n == ``Zlib.Uncompr.UncLoop.mk then
      return .record (.named "unc_loop") (← a.toList.mapM (fun x => value? x ctx))
    if n.getPrefix == ``Zlib.Uncompr.UncLoop && a.size == 1 then
      let field ← ident? n
      let ct ← [("err", Ty.i32), ("len", .u64), ("left", .u64)].lookup field
      return .field ct (← value? a[0]! ctx) field
    if n.getPrefix == ``C.ZStream && a.size == 1 then
      let (field, ct) ← zstreamFields.findSome? fun (f, t, proj) =>
        if proj == n then some (f, t) else none
      return .field ct (← value? a[0]! ctx) field
    if n == ``Zlib.Deflate.zrd && a.size == 3 then
      let strm ← value? a[1]! ctx
      let .lam _ _ projBody _ := a[2]! | none
      return ← value? projBody (ctx.push (some strm)) wanted
    if n == ``Zlib.Gzguts.ldZ && a.size == 1 then
      return ← value? a[0]! ctx
    if n == ``Zlib.Gzguts.load64 && a.size == 1 then
      let p ← value? a[0]! ctx
      if let .var _ s := p then
        if ctx.stackScalars.contains s then return p
      return .load .u64 p
    if n == ``C.Ptr.diff && a.size ≥ 2 then
      let p ← value? a[a.size-2]! ctx
      let q ← value? a.back! ctx
      return .op .i64 "-" p q
    if n == ``C.Ptr.null then return .num (.ptr .u8) 0
    if n == ``C.FnPtr.null then return .num (wanted.getD (.ptr .void)) 0
    if n == ``Zlib.Deflate.sizeof_z_stream then return .num .i32 112
    if n == ``Zlib.Zutil.zlibVersion then return .var (.ptr (.named "const char")) "ZLIB_VERSION"
    if n == ``Zlib.GzFs.strLit && a.size == 1 then
      guard (a[0]!.isConstOf ``C.ZLIB_VERSION)
      return .var (.ptr (.named "const char")) "ZLIB_VERSION"
    if n == ``Option.getD && a.size == 3 then
      let opt ← value? a[1]! ctx
      if opt == .var .void "__opt_out" then
        return ← value? a[2]! ctx wanted
    if n == ``C.Ptr.add then
      return .op (.ptr .u8) "+" (← value? a[a.size-2]! ctx) (← value? a.back! ctx)
    if n == ``UInt8.toUInt64 || n == ``Int64.toUInt64 then return asTy (← value? a.back! ctx) .u64
    if n == ``Zlib.Adler32.BASE || n == ``Zlib.Adler32.NMAX then return .var .u64 (← ident? n)
    if n == ``HDiv.hDiv && a[2]!.isConstOf ``UInt64 then
      let denominator ← value? a.back! ctx
      let .num _ k := denominator | none
      guard (k != 0)
      return .op .u64 "/" (← value? a[a.size-2]! ctx) denominator
    if n == ``Option.isNone && a[0]!.isConstOf ``C.GzFileRef then
      return .op .bool "==" (← value? a.back! ctx) (.num .i32 0)
    if n == ``Zlib.Gzguts.castState then
      return .cast (.named "gz_statep") (← value? a.back! ctx)
    if n == ``Zlib.Gzguts.ldS then
      return .load (.named "gz_state") (← value? a.back! ctx)
    if n == ``C.GzState.mode then
      return .field .i32 (← value? a.back! ctx) "mode"
    if n == ``Neg.neg && a[0]!.isConstOf ``Int32 then
      let .num .i32 k ← value? a.back! ctx | none
      guard (k < 2^31)
      return .op .i32 "-" (.num .i32 0) (.num .i32 k)
    if n == ``C.allocB && a.back!.isAppOfArity ``UInt32.toNat 1 then
      return .call (.ptr .u8) "malloc" [← value? a.back!.getAppArgs.back! ctx]
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
      let t ← ty? a[2]! ctx.abi
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
  if ctx.abi && (n == ``C.GZ_READ || n == ``C.GZ_WRITE) then return .var .i32 (← ident? n)
  if a.isEmpty && ((`C).isPrefixOf n || (`Zlib).isPrefixOf n) then
    let s ← ident? n
    guard (s.toUpper == s)
    let t ← if ctx.abi then
      match wanted with
      | some t => some t
      | none => ctx.env? >>= fun env => env.find? n >>= fun info => ty? info.type true
    else wanted
    return .var t s
  if (`Zlib).isPrefixOf n && !a.isEmpty then
    let args ← a.toList.mapM fun x => do
      if ctx.abi && x.isAppOfArity ``Option.some 2 then
        let inner ← value? x.getAppArgs.back! ctx
        if let .var _ s := inner then
          if ctx.stackScalars.contains s then return Value.addr inner
      let v ← value? x ctx
      if ctx.abi then
        if let .var _ s := v then
          if ctx.stackStreams.contains s || ctx.stackScalars.contains s then
            return Value.addr v
      return v
    return .call (← wanted) (← ident? n) args
  none

private def pair? (e : Expr) : Option (Expr × Expr) := do
  guard (e.isAppOfArity ``Prod.mk 4)
  return (e.getAppArgs[2]!, e.getAppArgs[3]!)

private partial def flattenProd : Expr → List Expr
  | e =>
    if e.isAppOfArity ``Prod.mk 4 then
      e.getAppArgs[2]! :: flattenProd e.getAppArgs[3]!
    else [e]

private partial def flattenProdTy (e : Expr) (abi : Bool) : Option (List Ty) := do
  if e.isAppOfArity ``Prod 2 then
    let l ← flattenProdTy e.getAppArgs[0]! abi
    let r ← flattenProdTy e.getAppArgs[1]! abi
    return l ++ r
  return [← ty? e abi]

private partial def splitTupleLam (e : Expr) (abi : Bool) : Option (List (Name × Ty) × Expr) := do
  match e with
  | .lam n t b _ =>
    let ct ← ty? t abi
    if let some (rest, inner) := splitTupleLam b abi then
      return ((n, ct) :: rest, inner)
    return ([(n, ct)], b)
  | _ => none

private def splitTupleMatch? (env : Environment) (fn : Expr) (abi : Bool) : Option (List (Name × Ty) × Expr) := do
  let .lam _ domain body _ := fn | none
  guard (domain.isAppOfArity ``Prod 2)
  let matcher ← body.getAppFn.constName?
  guard (Meta.isMatcherCore env matcher && body.getAppArgs.size == 3)
  guard (body.getAppArgs[1]! == .bvar 0)
  splitTupleLam body.getAppArgs[2]! abi

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
  | retOptU64 (destLenPtr : Value) (zeroed : Bool := false)
  | retPairU64 (destLenPtr : Value)
  | jump (marker target : Value) (unitArg : Bool)
  | store (place : Value)
  | loopTest (state condition : Value)
  | outParam (ptr : Value) (type : Ty)
  | update (x y : Value)
  | updateMany (vars : List Value)

private def finish (sink : Sink) (e : Expr) (ctx : Locals) : Option (List Stmt) := do
  match sink with
  | .ret t => return [.ret (← value? e ctx t)]
  | .retOptU64 destLenPtr zeroed =>
    let (rc, opt) ← pair? e
    let rcVal ← value? rc ctx (some .i32)
    if opt.isAppOfArity ``Option.none 1 then
      return [.ret rcVal]
    if opt.isAppOfArity ``Option.some 2 then
      let val ← value? opt.getAppArgs.back! ctx (some .u64)
      if zeroed && val == .num .u64 0 then
        return [.ret rcVal]
      return [.assign (.load .u64 destLenPtr) val, .ret rcVal]
    let optVal ← value? opt ctx
    guard (optVal == destLenPtr)
    return [.ret rcVal]
  | .retPairU64 destLenPtr =>
    let (rc, valExpr) ← pair? e
    let rcVal ← value? rc ctx (some .i32)
    let val ← value? valExpr ctx (some .u64)
    return [.assign (.load .u64 destLenPtr) val, .ret rcVal]
  | .jump marker target unitArg =>
    let .bvar i := e.getAppFn | none
    guard (ctx.values[i]?.join == some marker)
    let a := e.getAppArgs
    guard (a.size == (if unitArg then 2 else 1))
    if unitArg then guard (a[0]!.isConstOf ``Unit.unit)
    return [.assign target (← value? a.back! ctx target.type)]
  | .store place => return [.assign place (← value? e ctx place.type)]
  | .loopTest state condition =>
    let (c, s) ← pair? e
    let mut ss := [Stmt.assign condition (← value? c ctx)]
    let next ← value? s ctx state.type
    if next != state then ss := ss ++ [.assign state next]
    return ss ++ [.branch (.op .bool "==" condition (.num .bool 0)) [.stop] []]
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
  | .updateMany vars =>
    let exprs := flattenProd e
    guard (exprs.length == vars.length)
    let mut stmts : List Stmt := []
    for (v, rhsExpr) in vars.zip exprs do
      let rhs ← value? rhsExpr ctx v.type
      if rhs != v then
        stmts := stmts ++ [.assign v rhs]
    return stmts

private def zstreamUpdates? (ctx : Locals) (strmExpr fnExpr : Expr) : Option (List Stmt) := do
  let strm ← value? strmExpr ctx
  let .lam _ _ body _ := fnExpr | none
  guard (body.isAppOfArity ``C.ZStream.mk 14)
  let args := body.getAppArgs
  let subCtx := ctx.push (some strm)
  let mut updates : List (String × Stmt) := []
  for ((fieldName, fieldTy, projName), argExpr) in zstreamFields.zip args.toList do
    if argExpr.isAppOfArity projName 1 && argExpr.getAppArgs[0]! == .bvar 0 then
      continue
    let raw ← value? argExpr subCtx (some fieldTy)
    let rhs := if raw.type == fieldTy then raw else .cast fieldTy raw
    updates := updates ++ [(fieldName, .assign (.field fieldTy strm fieldName) rhs)]
  -- Emit output cursor writes before input cursor writes to match C stream setup order.
  let outUpdates := updates.filter fun (f, _) => f == "next_out" || f == "avail_out"
  let otherUpdates := updates.filter fun (f, _) => f != "next_out" && f != "avail_out"
  return (outUpdates ++ otherUpdates).map (·.2)

private def isStackScalarVal (ctx : Locals) (v : Value) : Bool :=
  match v with
  | .var _ s => ctx.stackScalars.contains s
  | _ => false

private def isStackFreeVal (ctx : Locals) (v : Value) : Bool :=
  ctx.reservedVals.contains v || isStackScalarVal ctx v

private partial def isStackCleanup (ctx : Locals) (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``C.freeB 1 then
    match value? e.getAppArgs.back! ctx with
    | some v => isStackFreeVal ctx v
    | none => false
  else if e.isAppOfArity ``C.freeZStream 1 then
    match value? e.getAppArgs.back! ctx with
    | some (.var _ s) => ctx.stackStreams.contains s
    | _ => false
  else if e.isAppOfArity ``Bind.bind 6 then
    let a := e.getAppArgs
    match a[5]! with
    | .lam _ _ rest _ => isStackCleanup ctx a[4]! && isStackCleanup (ctx.push none) rest
    | _ => false
  else false

private def unitAction? (ctx : Locals) (action : Expr) : Option (List Stmt) := do
  if let .bvar i := action then
    guard (ctx.values[i]? == some (some (.var .void "__noop")))
    return []
  if (action.isAppOfArity ``Zlib.Deflate.zwr 2 || action.isAppOfArity ``Zlib.Gzguts.updZ 2) then
    let a := action.getAppArgs
    return ← zstreamUpdates? ctx a[0]! a[1]!
  if action.isAppOfArity ``Zlib.Gzguts.store64 2 then
    let a := action.getAppArgs
    let p ← value? a[0]! ctx
    let v ← value? a[1]! ctx (some .u64)
    if isStackScalarVal ctx p then
      return [.assign p v]
    return [.assign (.load .u64 p) v]
  if action.isAppOfArity ``C.freeB 1 then
    let p ← value? action.getAppArgs.back! ctx
    if isStackFreeVal ctx p then return []
    return [.eval (.call .void "free" [p])]
  if action.isAppOfArity ``C.freeZStream 1 then
    let .var _ s ← value? action.getAppArgs.back! ctx | none
    guard (ctx.stackStreams.contains s)
    return []
  none

private partial def exprMentionsLoadOrStore64 (idx : Nat) (e : Expr) : Bool :=
  match e with
  | .app f a =>
    (f.isConstOf ``Zlib.Gzguts.load64 && a == .bvar idx) ||
    (f.getAppFn.isConstOf ``Zlib.Gzguts.store64 && f.getAppArgs.size == 1 && f.getAppArgs[0]! == .bvar idx) ||
    exprMentionsLoadOrStore64 idx f || exprMentionsLoadOrStore64 idx a
  | .lam _ t b _ => exprMentionsLoadOrStore64 idx t || exprMentionsLoadOrStore64 (idx + 1) b
  | .letE _ t v b _ =>
    exprMentionsLoadOrStore64 idx t || exprMentionsLoadOrStore64 idx v || exprMentionsLoadOrStore64 (idx + 1) b
  | _ => false

/-- A branch of a do-notation join that only computes a new scalar. The
continuation must be the bound jump, with no other references to that binder. -/
private partial def jumpArg? (branch : Expr) (unitArg : Bool) : Option Expr := do
  let e := branch.consumeMData
  if let .letE _ _ rhs rest _ := e then return ← jumpArg? (rest.instantiate1 rhs) unitArg
  guard (e.getAppFn == .bvar 0)
  let args := e.getAppArgs
  guard (args.size == (if unitArg then 2 else 1))
  if unitArg then guard (args[0]!.isConstOf ``Unit.unit)
  let v := args.back!
  guard (!v.hasLooseBVar 0)
  return v.instantiate1 (.const ``Unit.unit [])

private def join? (rhs arms : Expr) (ctx : Locals) : Option (List Stmt × Locals × Expr) := do
  guard (arms.isAppOfArity ``ite 5)
  let .lam n t cont _ := rhs | none
  let unitArg := t.isConstOf ``Unit
  let (n, t, tail) ← if unitArg then do
    let .lam n' t' rest _ := cont | none
    pure (n', t', rest)
  else pure (n, t, cont)
  let ct ← ty? t ctx.abi
  let name := fresh n ctx
  let a := arms.getAppArgs
  guard (!a[1]!.hasLooseBVar 0)
  let cond ← value? (a[1]!.instantiate1 (.const ``Unit.unit [])) ctx
  let yes ← value? (← jumpArg? a[3]! unitArg) (ctx.inTrueBranch cond) ct
  let no ← value? (← jumpArg? a[4]! unitArg) ctx ct
  let locals := if unitArg then ctx.push none else ctx
  let target := Value.var ct name
  return ([.decl ct name none, .branch cond [.assign target yes] [.assign target no]],
    locals.push (some target), tail)

/-- Recognize pure tests and pre/post-decrements on one unsigned loop-carried
field. All other fields must be unchanged in the state returned by the test. -/
private partial def loopGuard? (test : Expr) (ctx : Locals) (state : Value) : Option Value := do
  if let .letE _ _ rhs body _ := test then
    return ← loopGuard? (body.instantiate1 rhs) ctx state
  guard (test.isAppOfArity ``Pure.pure 4)
  let (c, next) ← pair? test.getAppArgs.back!
  let pred ← value? c ctx
  let next ← value? next ctx state.type
  if next == state then return pred
  let .record _ items := next | none
  let fields := ["adler", "sum2", "buf", "len", "n"]
  guard (fields.length == items.length)
  let mut changed : Option (Value × Value) := none
  for (field, v) in fields.zip items do
    let old := Value.field v.type state field
    if v != old then
      guard changed.isNone
      let .op t "-" lhs (.num _ 1) := v | none
      guard ((uintWidth? t).isSome && lhs == old)
      changed := some (old, v)
  let (old, newVal) ← changed
  let .op _ "!=" lhs (.num _ 0) := pred | none
  if lhs == old then return .postDec old
  guard (lhs == newVal)
  return .preDec old

private def hoistStackStreams (ss : List Stmt) : List Stmt :=
  let rec extract : List Stmt → List Stmt × List Stmt
    | [] => ([], [])
    | s :: rest =>
      let (h1, r1) := match s with
        | .decl (.named "z_stream") _ none => ([s], [])
        | .branch c yes no =>
          let (hy, y') := extract yes
          let (hn, n') := extract no
          (hy ++ hn, [.branch c y' n'])
        | _ => ([], [s])
      let (h2, r2) := extract rest
      (h1 ++ h2, r1 ++ r2)
  let (hoisted, body) := extract ss
  hoisted ++ body

private partial def stmts? (env : Environment) (e : Expr) (ctx : Locals) (sink : Sink) : Option (List Stmt) := do
  let e := if ctx.abi then e.consumeMData.headBeta else e.consumeMData
  if let .letE n t rhs body _ := e then
    if ctx.abi && t.isAppOfArity ``C.M 1 && t.getAppArgs.back!.isConstOf ``Unit && isStackCleanup ctx rhs then
      return ← stmts? env body (ctx.push (some (.var .void "__noop"))) sink
    if ctx.abi && rhs.isLambda then
      if let some (decl, locals, rest) := join? rhs body ctx then
        return decl ++ (← stmts? env rest locals sink)
      if body.isAppOfArity ``ite 5 then
        let .lam _ t cont _ := rhs | none
        let unitArg := t.isConstOf ``Unit
        let next := if unitArg then cont else rhs
        if let .lam arg domain rest _ := next then
          if let some ct := ty? domain ctx.abi then
            let target := Value.var ct (fresh arg ctx)
            let marker := Value.var .void (fresh `joinPoint (ctx.push (some target)))
            let branchCtx := { ctx with reserved := target.render :: ctx.reserved }
            if let some branches := stmts? env body (branchCtx.push (some marker)) (.jump marker target unitArg) then
              let locals := if unitArg then ctx.push none else ctx
              let tail ← stmts? env rest (locals.push (some target)) sink
              return .decl ct target.render none :: branches ++ tail
      return ← stmts? env (body.instantiate1 rhs) ctx sink
    let ct ← ty? t ctx.abi
    let v ← value? rhs ctx ct
    let name := fresh n ctx
    return .decl ct name (some v) :: (← stmts? env body (ctx.push (some (.var ct name))) sink)
  if e.isAppOfArity ``ite 5 then
    let a := e.getAppArgs
    let cond ← value? a[1]! ctx
    return [.branch cond (← stmts? env a[3]! (ctx.inTrueBranch cond) sink) (← stmts? env a[4]! ctx sink)]
  if ctx.abi then
    if let some matcher := e.getAppFn.constName? then
      if Meta.isMatcherCore env matcher && e.getAppArgs.size == 4 then
        let ma := e.getAppArgs
        if let some p := value? ma[1]! ctx then
          if p.type == .ptr .u64 then
            let .lam dlName _ someBody _ := ma[2]! | none
            let .lam _ _ noneBody _ := ma[3]! | none
            let varName := fresh dlName ctx
            if noneBody.isAppOfArity ``C.ub 2 then
              let v := Value.var .u64 varName
              let subCtx := { (ctx.push (some v)) with stackScalars := varName :: ctx.stackScalars }
              return .decl .u64 varName (some (.load .u64 p)) :: (← stmts? env someBody subCtx sink)
            let noneStmts ← stmts? env noneBody (ctx.push none) sink
            if someBody.isAppOfArity ``ite 5 then
              let sa := someBody.getAppArgs
              let condExpr := if sa[1]!.isAppOfArity ``Eq 3 && sa[1]!.getAppArgs.back!.isConstOf ``Bool.true then
                sa[1]!.getAppArgs[sa[1]!.getAppArgs.size - 2]! else sa[1]!
              if condExpr.isAppOfArity ``Bool.or 2 then
                let aOr := condExpr.getAppArgs[0]!
                let bOr := condExpr.getAppArgs[1]!
                if !aOr.hasLooseBVar 0 then
                  if let (some cA, some cB, some yesStmts) :=
                      (value? aOr (ctx.push none),
                       value? bOr (ctx.push (some (.load .u64 p))),
                       stmts? env sa[3]! (ctx.push none) sink) then
                    if renderStmts yesStmts 0 == renderStmts noneStmts 0 then
                      let combined := Value.op .bool "||" (Value.op .bool "||" cA (Value.op .bool "==" p (.num .i32 0))) cB
                      let (pre, nextSink) : List Stmt × Sink := match sink with
                        | .retOptU64 dp false => ([Stmt.assign (.load .u64 dp) (.num .u64 0)], Sink.retOptU64 dp true)
                        | _ => ([], sink)
                      let dlVar := Value.var .u64 varName
                      if let .letE ln _ (.bvar 0) elseInner _ := sa[4]! then
                        let lName := fresh ln ctx
                        let lVar := Value.var .u64 lName
                        let innerStmts ← stmts? env elseInner ((ctx.push (some dlVar)).push (some lVar)) nextSink
                        return [Stmt.branch combined noneStmts [], Stmt.decl .u64 lName (some (.load .u64 p))] ++ pre ++ innerStmts
                      let elseStmts ← stmts? env sa[4]! (ctx.push (some dlVar)) nextSink
                      return [Stmt.branch combined noneStmts [], Stmt.decl .u64 varName (some (.load .u64 p))] ++ pre ++ elseStmts
            let dlVar := Value.var .u64 varName
            let someStmts ← stmts? env someBody (ctx.push (some dlVar)) sink
            return [.branch (.op .bool "==" p (.num .i32 0)) noneStmts []] ++
              [.decl .u64 varName (some (.load .u64 p))] ++ someStmts
  if e.isAppOfArity ``Pure.pure 4 then return ← finish sink e.getAppArgs.back! ctx
  if e.isAppOfArity ``Bind.bind 6 then
    let a := e.getAppArgs
    let action := a[4]!
    let cont := a[5]!
    if ctx.abi && (action.isAppOfArity ``C.cwhile 4 || action.isAppOfArity ``C.cdoWhile 4) then
      let w := action.getAppArgs
      let structTy? :=
        if w[0]!.isConstOf ``Zlib.Adler32.Locals then some (Ty.named "adler_state", `state)
        else if w[0]!.isConstOf ``Zlib.Uncompr.UncLoop then some (Ty.named "unc_loop", `l)
        else none
      if let some (cTy, baseName) := structTy? then
        let pretest := action.isAppOfArity ``C.cwhile 4
        let .lam _ _ afterLoop _ := cont | none
        let bodyOf := fun (f : Expr) => do
          let f ← if let .const fn _ := f then do
            let some (.defnInfo d) := env.find? fn | none
            pure d.value
          else pure f
          let .lam _ _ b _ := f | none
          pure b
        let state := Value.var cTy (fresh baseName ctx)
        let locals := ctx.push (some state)
        let condition := Value.var .bool (fresh `keepGoing locals)
        let test ← bodyOf (if pretest then w[1]! else w[2]!)
        let step ← stmts? env (← bodyOf (if pretest then w[2]! else w[1]!)) locals (.store state)
        let loop ← if let some c := loopGuard? test locals state then
          pure (if pretest then Stmt.loop c step else Stmt.doLoop step c)
        else do
          let before ← stmts? env test locals (.loopTest state condition)
          let iteration := if pretest then before ++ step else step ++ before
          pure (Stmt.loop (.num .bool 1) (.decl .bool condition.render none :: iteration))
        return [.decl state.type state.render (some (← value? w[3]! ctx state.type)), loop] ++
          (← stmts? env afterLoop locals sink)
      if action.isAppOfArity ``C.cdoWhile 4 then
        if let some _ := flattenProdTy w[0]! true then
          let (bodyBinders, step) ← splitTupleMatch? env w[1]! true
          let .lam _ _ condLamBody _ := w[2]! | none
          guard (condLamBody.isAppOfArity ``Pure.pure 4)
          let (condExpr, condNext) ← pair? condLamBody.getAppArgs.back!
          guard (condNext == .bvar 0)
          let initExprs := flattenProd w[3]!
          guard (initExprs.length == bodyBinders.length)
          let mut decls : List Stmt := []
          let mut loopVars : List Value := []
          let mut scanCtx := ctx
          for ((bn, bt), ie) in bodyBinders.zip initExprs do
            let vName := fresh bn scanCtx
            let v := Value.var bt vName
            decls := decls ++ [.decl bt vName (some (← value? ie ctx bt))]
            loopVars := loopVars ++ [v]
            scanCtx := scanCtx.push (some v)
          let bodyCtx := loopVars.foldl (fun c v => c.push (some v)) (ctx.push none)
          let cond ← value? condExpr { ctx with tupleAt0 := loopVars }
          let stepStmts ← stmts? env step bodyCtx (.updateMany loopVars)
          let (afterBinders, afterLoop) ← splitTupleMatch? env cont true
          guard (afterBinders.length == loopVars.length)
          let afterCtx := loopVars.foldl (fun c v => c.push (some v)) (ctx.push none)
          let tail ← stmts? env afterLoop afterCtx sink
          return decls ++ [.doLoop stepStmts cond] ++ tail
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
    if ctx.abi then
      if t.isConstOf ``Unit then
        let stmts ← unitAction? ctx action
        return stmts ++ (← stmts? env rest (ctx.push none) sink)
      if action.isAppOfArity ``Zlib.Compress.allocLocalZ 0 || action.isAppOfArity ``Zlib.Uncompr.allocLocalZ 0 then
        let sName := fresh n ctx
        let strm := Value.var (.named "z_stream") sName
        let nextCtx := { (ctx.push (some strm)) with stackStreams := sName :: ctx.stackStreams }
        return .decl (.named "z_stream") sName none :: (← stmts? env rest nextCtx sink)
      if action.isAppOfArity ``Zlib.Gzguts.allocLocal 1 then
        if exprMentionsLoadOrStore64 0 rest then
          let sName := fresh n ctx
          let v := Value.var .u64 sName
          let nextCtx := { (ctx.push (some v)) with stackScalars := sName :: ctx.stackScalars }
          return .decl .u64 sName none :: (← stmts? env rest nextCtx sink)
        else
          let some sName := ctx.stackStreams.head? | none
          let expr := Value.cast (.ptr .u8) (.addr (.field .u64 (.var (.named "z_stream") sName) "reserved"))
          let nextCtx := { (ctx.push (some expr)) with reservedVals := expr :: ctx.reservedVals }
          return ← stmts? env rest nextCtx sink
      if t.isAppOfArity ``Prod 2 && t.getAppArgs[0]!.isConstOf ``Int32 &&
          t.getAppArgs[1]!.isAppOfArity ``Option 1 then
        let .lam _ _ body _ := cont | none
        let matcher ← body.getAppFn.constName?
        guard (Meta.isMatcherCore env matcher && body.getAppArgs.size == 3 && body.getAppArgs[1]! == .bvar 0)
        let .lam retName _ (.lam _ _ tailBody _) _ := body.getAppArgs[2]! | none
        let rName := fresh retName ctx
        let rVar := Value.var .i32 rName
        let v ← value? action ctx (some .i32)
        let tailCtx := ((ctx.push none).push (some rVar)).push (some (.var .void "__opt_out"))
        return .decl .i32 rName (some v) :: (← stmts? env tailBody tailCtx sink)
    let ct ← ty? t ctx.abi
    let place := Value.var (ctx.localType ct) (fresh n ctx)
    let tail ← stmts? env rest (ctx.push (some place)) sink
    if let some v := value? action ctx ct then
      if ctx.abi && !rest.hasLooseBVar 0 then
        if action.isAppOfArity ``Zlib.Deflate.deflateEnd 1 then
          if let [st@(.assign _ _), r@(.ret _)] := tail then
            return [st, .eval v, r]
        return .eval v :: tail
      let declTy := if ctx.abi && v == .var (.ptr (.named "const char")) "ZLIB_VERSION" then
        Ty.ptr (.named "const char") else place.type
      return .decl declTy place.render (some v) :: tail
    guard (ctx.abi && action.isAppOfArity ``ite 5)
    return .decl place.type place.render none :: (← stmts? env action { ctx with reserved := place.render :: ctx.reserved } (.store place)) ++ tail
  if ctx.abi && e.isAppOfArity ``C.freeB 1 then
    if let .ret .void := sink then
      return [.eval (.call .void "free" [← value? e.getAppArgs.back! ctx])]
  finish sink e ctx

/-- Name of the C out-parameter represented by the first scalar argument. -/
def firstOutParam? (name : Name) : Option String :=
  if name == ``Zlib.Inflate.syncsearch then some "have" else none

private def paramType? (name paramName : Name) (t : Expr) (abi : Bool) : Option Ty := do
  if abi && t.isAppOfArity ``Option 1 && t.getAppArgs.back!.isConstOf ``UInt64 then
    return .ptr .u64
  if abi && (name.getPrefix == `Zlib.Compress || name.getPrefix == `Zlib.Uncompr) then
    if t.isConstOf ``C.BPtr then
      if paramName == `source then return .ptr (.named "const unsigned char")
      if paramName == `destLen || paramName == `sourceLen then return .ptr .u64
  ty? t abi

/-- Lower a translated Lean function definition into its parameter signature and C statement list.
All operations in the function body still come from its `Expr`. -/
def lowerStmts? (env : Environment) (name : Name) (type body : Expr) (abi : Bool := false) :
    Option (List (String × Ty) × List Stmt) := do
  if abi && name == ``Zlib.Zutil.zError then
    let some (.defnInfo d) := env.find? name | none
    guard (d.value == body)
    let .lam n _ index _ ← ErrorIndex.extract? env body | none
    let paramName ← ident? n
    let i ← value? index (({ abi } : Locals).push (some (.var .i32 paramName))) (some .i32)
    -- ErrorIndex.inBounds checks precisely the index extracted above.
    return ([(paramName, .i32)], [.ret (.index (.ptr .u8) (.var (.ptr (.ptr (.named "char"))) "z_errmsg") i)])
  let outName := firstOutParam? name
  let rec args (e : Expr) (ctx : Locals) (params : List (String × Ty)) :
      Option (List (String × Ty) × List Stmt) := do
    if let .lam n t b _ := e then
      -- do1 is an inline helper instantiated with byte offsets 0..15 by do16.
      let ct ← if abi && name == ``Zlib.Adler32.do1 && t.isConstOf ``Int then some Ty.i64 else paramType? name n t ctx.abi
      let paramName ← ident? n
      let mut v := Value.var ct paramName
      let paramInfo :=
        if ctx.values.isEmpty then
          if let some p := outName then (p, Ty.ptr ct) else (paramName, ct)
        else (paramName, ct)
      if ctx.values.isEmpty then
        if let some p := outName then v := .load ct (.var (.ptr ct) p)
      return ← args b (ctx.push (some v)) (params ++ [paramInfo])
    let rt := stripCAbi type.getForallBody
    let result := stripCAbi (if rt.isAppOfArity ``C.M 1 || (abi && rt.isAppOfArity ``Zlib.GzFs.G 1) then rt.getAppArgs.back! else rt)
    let bodyStmts ←
      if let some p := outName then
        stmts? env e ctx (.outParam (.var (.ptr .u32) p) .u32)
      else if abi && result.isAppOfArity ``Prod 2 then
        let lhs := result.getAppArgs[0]!
        let rhs := result.getAppArgs[1]!
        if lhs.isConstOf ``Int32 then
          let destLenPtr := Value.var (.ptr .u64) "destLen"
          if rhs.isAppOfArity ``Option 1 && rhs.getAppArgs.back!.isConstOf ``UInt64 then
            stmts? env e ctx (.retOptU64 destLenPtr)
          else if rhs.isConstOf ``UInt64 then
            stmts? env e ctx (.retPairU64 destLenPtr)
          else
            stmts? env e ctx (.ret (← ty? result ctx.abi))
        else
          stmts? env e ctx (.ret (← ty? result ctx.abi))
      else if abi && result.isConstOf ``Unit then
        stmts? env e ctx (.ret .void)
      else
        stmts? env e ctx (.ret (← ty? result ctx.abi))
    return (params, bodyStmts)
  let (params, stmts) ← args body { abi, env? := some env, constBytes := abi && name.getPrefix == `Zlib.Adler32 } []
  return (params, if abi then hoistStackStreams stmts else stmts)

/-- The out-parameter adapter supplies the C ABI information removed by the
original model. All operations in the function body still come from its Expr. -/
def lower? (env : Environment) (name : Name) (type body : Expr) (abi : Bool := false) : Option String := do
  let (_, stmts) ← lowerStmts? env name type body abi
  return renderBody stmts

end Lean2C.Lower
