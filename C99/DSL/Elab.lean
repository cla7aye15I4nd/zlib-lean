import C99.DSL.Macro
import C99.DSL.Contract

/-!
# Fast Direct C99 AST Elaborator (`C99.DSL.Elab`)

Elaborates `C99.DSL.Syntax` commands directly in `CommandElabM` into concrete
`C99.AST` values (applying `C99.DSL.Macro` expansion first) and serializes them
to kernel expressions via `Lean.toExpr` for O(N) elaboration speed.
-/

namespace C99.DSL

open Lean Elab Command Term Meta

/-! ## `ToExpr` Instances for `C99.AST` -/

private def mkCon (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) args
private def mkListCons (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun hd tl => mkApp3 (mkConst ``List.cons [Level.zero]) ty hd tl)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)
private partial def mkAppendChunks (ty : Expr) (chunks : List Expr) : Expr :=
  match chunks with
  | [] => mkApp (mkConst ``List.nil [Level.zero]) ty
  | [c] => c
  | _ =>
    let mid := chunks.length / 2
    mkApp3 (mkConst ``List.append [Level.zero]) ty
      (mkAppendChunks ty (chunks.take mid)) (mkAppendChunks ty (chunks.drop mid))
private partial def mkListExpr (ty : Expr) (xs : List Expr) : Expr :=
  if xs.length ≤ 32 then mkListCons ty xs
  else
    let mid := xs.length / 2
    mkApp3 (mkConst ``List.append [Level.zero]) ty
      (mkListExpr ty (xs.take mid)) (mkListExpr ty (xs.drop mid))
private def mkOptExpr (ty : Expr) : Option Expr → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) ty
  | some x => mkApp2 (mkConst ``Option.some [Level.zero]) ty x
private def mkPairExpr (t1 t2 : Expr) (a b : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) t1 t2 a b

instance : ToExpr IntKind where
  toTypeExpr := mkConst ``IntKind
  toExpr k := mkConst <| match k with
    | .i8 => ``IntKind.i8 | .u8 => ``IntKind.u8
    | .i16 => ``IntKind.i16 | .u16 => ``IntKind.u16
    | .i32 => ``IntKind.i32 | .u32 => ``IntKind.u32
    | .i64 => ``IntKind.i64 | .u64 => ``IntKind.u64

instance : ToExpr LitRadix where
  toTypeExpr := mkConst ``LitRadix
  toExpr r := mkConst <| match r with
    | .dec => ``LitRadix.dec | .hex => ``LitRadix.hex
    | .oct => ``LitRadix.oct | .char => ``LitRadix.char

instance : ToExpr LitSuffix where
  toTypeExpr := mkConst ``LitSuffix
  toExpr s := mkConst <| match s with
    | .none => ``LitSuffix.none | .U => ``LitSuffix.U | .L => ``LitSuffix.L
    | .UL => ``LitSuffix.UL | .LL => ``LitSuffix.LL | .ULL => ``LitSuffix.ULL

instance : ToExpr UnOp where
  toTypeExpr := mkConst ``UnOp
  toExpr o := mkConst <| match o with
    | .neg => ``UnOp.neg | .bitNot => ``UnOp.bitNot | .logNot => ``UnOp.logNot | .plus => ``UnOp.plus

instance : ToExpr BinOp where
  toTypeExpr := mkConst ``BinOp
  toExpr o := mkConst <| match o with
    | .add => ``BinOp.add | .sub => ``BinOp.sub | .mul => ``BinOp.mul
    | .div => ``BinOp.div | .mod => ``BinOp.mod | .bitAnd => ``BinOp.bitAnd
    | .bitOr => ``BinOp.bitOr | .bitXor => ``BinOp.bitXor
    | .shl => ``BinOp.shl | .shr => ``BinOp.shr
    | .eq => ``BinOp.eq | .ne => ``BinOp.ne
    | .lt => ``BinOp.lt | .le => ``BinOp.le | .gt => ``BinOp.gt | .ge => ``BinOp.ge

instance : ToExpr AssignOp where
  toTypeExpr := mkConst ``AssignOp
  toExpr o := mkConst <| match o with
    | .eq => ``AssignOp.eq | .addEq => ``AssignOp.addEq | .subEq => ``AssignOp.subEq
    | .mulEq => ``AssignOp.mulEq | .divEq => ``AssignOp.divEq | .modEq => ``AssignOp.modEq
    | .andEq => ``AssignOp.andEq | .orEq => ``AssignOp.orEq | .xorEq => ``AssignOp.xorEq
    | .shlEq => ``AssignOp.shlEq | .shrEq => ``AssignOp.shrEq

instance : ToExpr IncDecOp where
  toTypeExpr := mkConst ``IncDecOp
  toExpr o := mkConst <| match o with
    | .preInc => ``IncDecOp.preInc | .preDec => ``IncDecOp.preDec
    | .postInc => ``IncDecOp.postInc | .postDec => ``IncDecOp.postDec

instance : ToExpr Linkage where
  toTypeExpr := mkConst ``Linkage
  toExpr l := mkConst <| match l with
    | .export_ => ``Linkage.export_ | .hidden => ``Linkage.hidden
    | .static_ => ``Linkage.static_ | .staticInline => ``Linkage.staticInline
    | .extern_ => ``Linkage.extern_

private partial def exprOfCTy : CTy → Expr
  | .void => mkConst ``CTy.void
  | .int k => mkCon ``CTy.int #[toExpr k]
  | .const_ t => mkCon ``CTy.const_ #[exprOfCTy t]
  | .ptr t => mkCon ``CTy.ptr #[exprOfCTy t]
  | .array el len? => mkCon ``CTy.array #[exprOfCTy el, toExpr len?]
  | .structTy s => mkCon ``CTy.structTy #[toExpr s]
  | .unionTy s => mkCon ``CTy.unionTy #[toExpr s]
  | .anonStruct flds =>
    let pty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``CTy)
    let xs := flds.map fun (n, t) => mkPairExpr (mkConst ``String) (mkConst ``CTy) (toExpr n) (exprOfCTy t)
    mkCon ``CTy.anonStruct #[mkListExpr pty xs]
  | .anonUnion flds =>
    let pty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``CTy)
    let xs := flds.map fun (n, t) => mkPairExpr (mkConst ``String) (mkConst ``CTy) (toExpr n) (exprOfCTy t)
    mkCon ``CTy.anonUnion #[mkListExpr pty xs]
  | .enumTy s u => mkCon ``CTy.enumTy #[toExpr s, toExpr u]
  | .fnPtr ret ps v =>
    mkCon ``CTy.fnPtr #[exprOfCTy ret, mkListExpr (mkConst ``CTy) (ps.map exprOfCTy), toExpr v]
  | .vaList => mkConst ``CTy.vaList
  | .typedef s t => mkCon ``CTy.typedef #[toExpr s, exprOfCTy t]

instance : ToExpr CTy where toExpr := exprOfCTy; toTypeExpr := mkConst ``CTy

private partial def exprOfCExpr : CExpr → Expr
  | .lit v k s r sym? => mkCon ``CExpr.lit #[toExpr v, toExpr k, toExpr s, toExpr r, toExpr sym?]
  | .strLit s => mkCon ``CExpr.strLit #[toExpr s]
  | .var s => mkCon ``CExpr.var #[toExpr s]
  | .sizeOfTy t => mkCon ``CExpr.sizeOfTy #[exprOfCTy t]
  | .sizeOfExpr e => mkCon ``CExpr.sizeOfExpr #[exprOfCExpr e]
  | .unary op e => mkCon ``CExpr.unary #[toExpr op, exprOfCExpr e]
  | .binary op l r => mkCon ``CExpr.binary #[toExpr op, exprOfCExpr l, exprOfCExpr r]
  | .logAnd l r => mkCon ``CExpr.logAnd #[exprOfCExpr l, exprOfCExpr r]
  | .logOr l r => mkCon ``CExpr.logOr #[exprOfCExpr l, exprOfCExpr r]
  | .cond c t f => mkCon ``CExpr.cond #[exprOfCExpr c, exprOfCExpr t, exprOfCExpr f]
  | .comma l r => mkCon ``CExpr.comma #[exprOfCExpr l, exprOfCExpr r]
  | .cast t e => mkCon ``CExpr.cast #[exprOfCTy t, exprOfCExpr e]
  | .deref e => mkCon ``CExpr.deref #[exprOfCExpr e]
  | .addrOf e => mkCon ``CExpr.addrOf #[exprOfCExpr e]
  | .index b i => mkCon ``CExpr.index #[exprOfCExpr b, exprOfCExpr i]
  | .member b f => mkCon ``CExpr.member #[exprOfCExpr b, toExpr f]
  | .arrow b f => mkCon ``CExpr.arrow #[exprOfCExpr b, toExpr f]
  | .assign op l r => mkCon ``CExpr.assign #[toExpr op, exprOfCExpr l, exprOfCExpr r]
  | .incDec op l => mkCon ``CExpr.incDec #[toExpr op, exprOfCExpr l]
  | .call f args => mkCon ``CExpr.call #[exprOfCExpr f, mkListExpr (mkConst ``CExpr) (args.map exprOfCExpr)]
  | .vaStart a b => mkCon ``CExpr.vaStart #[toExpr a, toExpr b]
  | .vaEnd a => mkCon ``CExpr.vaEnd #[toExpr a]
  | .paren e => mkCon ``CExpr.paren #[exprOfCExpr e]

instance : ToExpr CExpr where toExpr := exprOfCExpr; toTypeExpr := mkConst ``CExpr

private partial def exprOfInit : InitVal → Expr
  | .expr e => mkCon ``InitVal.expr #[exprOfCExpr e]
  | .list xs => mkCon ``InitVal.list #[mkListExpr (mkConst ``InitVal) (xs.map exprOfInit)]
  | .intArray k r vs => mkCon ``InitVal.intArray #[toExpr k, toExpr r, toExpr vs]
  | .intArray2D k r rs => mkCon ``InitVal.intArray2D #[toExpr k, toExpr r, toExpr rs]
  | .tupleArray b rs => mkCon ``InitVal.tupleArray #[toExpr b, toExpr rs]

instance : ToExpr InitVal where toExpr := exprOfInit; toTypeExpr := mkConst ``InitVal

instance : ToExpr VarDecl where
  toTypeExpr := mkConst ``VarDecl
  toExpr d := mkCon ``VarDecl.mk
    #[toExpr d.name, exprOfCTy d.ty, toExpr d.isStatic, toExpr d.isConst,
      mkOptExpr (mkConst ``InitVal) (d.init?.map exprOfInit)]

private partial def exprOfStmt : CStmt → Expr
  | .nop => mkConst ``CStmt.nop
  | .expr e => mkCon ``CStmt.expr #[exprOfCExpr e]
  | .decl d => mkCon ``CStmt.decl #[toExpr d]
  | .decls ds => mkCon ``CStmt.decls #[mkListExpr (mkConst ``VarDecl) (ds.map toExpr)]
  | .block ss => mkCon ``CStmt.block #[mkListExpr (mkConst ``CStmt) (ss.map exprOfStmt)]
  | .ifStmt c t f? => mkCon ``CStmt.ifStmt #[exprOfCExpr c, exprOfStmt t, mkOptExpr (mkConst ``CStmt) (f?.map exprOfStmt)]
  | .whileStmt c b => mkCon ``CStmt.whileStmt #[exprOfCExpr c, exprOfStmt b]
  | .doWhileStmt b c => mkCon ``CStmt.doWhileStmt #[exprOfStmt b, exprOfCExpr c]
  | .forStmt i? c? s? b =>
    let eo := mkOptExpr (mkConst ``CExpr)
    mkCon ``CStmt.forStmt #[eo (i?.map exprOfCExpr), eo (c?.map exprOfCExpr), eo (s?.map exprOfCExpr), exprOfStmt b]
  | .switchStmt s b => mkCon ``CStmt.switchStmt #[exprOfCExpr s, exprOfStmt b]
  | .caseStmt v b => mkCon ``CStmt.caseStmt #[toExpr v, exprOfStmt b]
  | .defaultStmt b => mkCon ``CStmt.defaultStmt #[exprOfStmt b]
  | .breakStmt => mkConst ``CStmt.breakStmt
  | .continueStmt => mkConst ``CStmt.continueStmt
  | .returnStmt e? => mkCon ``CStmt.returnStmt #[mkOptExpr (mkConst ``CExpr) (e?.map exprOfCExpr)]
  | .labelStmt l b => mkCon ``CStmt.labelStmt #[toExpr l, exprOfStmt b]
  | .gotoStmt l => mkCon ``CStmt.gotoStmt #[toExpr l]

instance : ToExpr CStmt where toExpr := exprOfStmt; toTypeExpr := mkConst ``CStmt

instance : ToExpr Param where
  toTypeExpr := mkConst ``Param
  toExpr p := mkCon ``Param.mk #[toExpr p.name, exprOfCTy p.ty]

instance : ToExpr FnDef where
  toTypeExpr := mkConst ``FnDef
  toExpr f := mkCon ``FnDef.mk #[toExpr f.linkage, exprOfCTy f.retTy, toExpr f.name,
    mkListExpr (mkConst ``Param) (f.params.map toExpr), toExpr f.variadic, exprOfStmt f.body]

instance : ToExpr TopItem where
  toTypeExpr := mkConst ``TopItem
  toExpr
    | .includeSys p => mkCon ``TopItem.includeSys #[toExpr p]
    | .includeLocal p => mkCon ``TopItem.includeLocal #[toExpr p]
    | .ppRaw t => mkCon ``TopItem.ppRaw #[toExpr t]
    | .typedefDecl n ty => mkCon ``TopItem.typedefDecl #[toExpr n, exprOfCTy ty]
    | .fwdTag u t => mkCon ``TopItem.fwdTag #[toExpr u, toExpr t]
    | .tagDecl u t? td? flds =>
      let pty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``CTy)
      let xs := flds.map fun (n, t) => mkPairExpr (mkConst ``String) (mkConst ``CTy) (toExpr n) (exprOfCTy t)
      mkCon ``TopItem.tagDecl #[toExpr u, toExpr t?, toExpr td?, mkListExpr pty xs]
    | .enumDecl t? td? items =>
      let optI := mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)
      let pty := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) optI
      let xs := items.map fun (n, v?) => mkPairExpr (mkConst ``String) optI (toExpr n) (toExpr v?)
      mkCon ``TopItem.enumDecl #[toExpr t?, toExpr td?, mkListExpr pty xs]
    | .globalDecl l d => mkCon ``TopItem.globalDecl #[toExpr l, toExpr d]
    | .fnProto l r n ps v =>
      mkCon ``TopItem.fnProto #[toExpr l, exprOfCTy r, toExpr n, mkListExpr (mkConst ``Param) (ps.map toExpr), toExpr v]
    | .fnDef f => mkCon ``TopItem.fnDef #[toExpr f]

instance : ToExpr TU where
  toTypeExpr := mkConst ``TU
  toExpr tu := mkCon ``TU.mk #[toExpr tu.fileName, mkListExpr (mkConst ``TopItem) (tu.items.map toExpr)]

/-! ## Constant Expression Evaluation & Literal Parsing -/

private def parseOctal (s : String) : Option Nat :=
  s.toList.foldlM (fun acc ch =>
    if '0' ≤ ch && ch ≤ '7' then some (acc * 8 + (ch.toNat - '0'.toNat)) else none) 0

private def parseLitSuffix (opt : Syntax) : CoreM LitSuffix := do
  match opt.getOptional? with
  | none => return .none
  | some idStx =>
    match idStx.getId.toString.toUpper with
    | "U" => return .U | "L" => return .L | "UL" => return .UL
    | "LL" => return .LL | "ULL" => return .ULL
    | other => throwErrorAt opt "invalid C integer suffix `{other}`"

private def inferLitKind (v : Nat) (rad : LitRadix) (suf : LitSuffix) : IntKind :=
  match suf, rad with
  | .ULL, _ => .u64 | .UL, _ => .u64 | .LL, _ => .i64
  | .U, _ => if v < 2^32 then .u32 else .u64
  | .L, _ => if v < 2^63 then .i64 else .u64
  | .none, .dec => if v < 2^31 then .i32 else .i64
  | .none, _ =>
    if v < 2^31 then .i32 else if v < 2^32 then .u32 else if v < 2^63 then .i64 else .u64

private partial def evalConstCExpr (env : Environment) (e : CExpr) : CoreM Int := do
  let tags : TypeEnv := (getScopeData env).tags.map fun (s, d) => (s, d)
  match e with
  | .lit v _ _ _ _ => return v
  | .paren inner => evalConstCExpr env inner
  | .var s => match lookupConst? env s with
    | some v => return v
    | none => throwError "unknown compile-time C constant `{s}`"
  | .sizeOfTy ty => return sizeofTy tags ty
  | .unary op inner =>
    let v ← evalConstCExpr env inner
    match op with
    | .plus => return v | .neg => return -v
    | .bitNot => return (~~~v) | .logNot => return (if v == 0 then 1 else 0)
  | .cast (.int k) inner =>
    let v ← evalConstCExpr env inner
    let bv := BitVec.ofInt k.bits v
    return if k.signed then bv.toInt else (bv.toNat : Int)
  | .cast (.typedef _ t) inner => evalConstCExpr env (.cast t inner)
  | .cond c t f =>
    let vc ← evalConstCExpr env c
    evalConstCExpr env (if vc != 0 then t else f)
  | .logAnd l r =>
    let vl ← evalConstCExpr env l
    if vl == 0 then return 0 else return (if (← evalConstCExpr env r) != 0 then 1 else 0)
  | .logOr l r =>
    let vl ← evalConstCExpr env l
    if vl != 0 then return 1 else return (if (← evalConstCExpr env r) != 0 then 1 else 0)
  | .binary op l r =>
    let a ← evalConstCExpr env l
    let b ← evalConstCExpr env r
    match op with
    | .add => return a + b | .sub => return a - b | .mul => return a * b
    | .div => if b == 0 then throwError "division by zero in C constant expression" else return Int.tdiv a b
    | .mod => if b == 0 then throwError "modulo by zero in C constant expression" else return Int.tmod a b
    | .shl => return a * (2 ^ b.toNat : Int)
    | .shr => return a / (2 ^ b.toNat : Int)
    | .bitAnd => return ((BitVec.ofInt 64 a) &&& (BitVec.ofInt 64 b)).toInt
    | .bitOr => return ((BitVec.ofInt 64 a) ||| (BitVec.ofInt 64 b)).toInt
    | .bitXor => return ((BitVec.ofInt 64 a) ^^^ (BitVec.ofInt 64 b)).toInt
    | .eq => return (if a == b then 1 else 0) | .ne => return (if a != b then 1 else 0)
    | .lt => return (if a < b then 1 else 0)  | .le => return (if a ≤ b then 1 else 0)
    | .gt => return (if a > b then 1 else 0)  | .ge => return (if a ≥ b then 1 else 0)
  | _ => throwError "expression is not a compile-time C constant"

/-! ## Syntax -> C99.AST Elaborators -/

private def optArgs? (stx : Syntax) : Option (Array Syntax) :=
  if stx.getNumArgs == 0 then none else some stx.getArgs

private def qualsHaveConst (stx : Syntax) : Bool :=
  stx.getArgs.any fun q =>
    let k := q.getKind
    k == ``cQualConst || k == ``cQualZConst || k == ``cQualTConst

private def wrapConst (isConst : Bool) (t : CTy) : CTy :=
  if isConst && !t.isConst then .const_ t else t

private def signRestKind (isSigned : Bool) (opt : Syntax) : IntKind :=
  match opt.getOptional? with
  | none => if isSigned then .i32 else .u32
  | some s =>
    let k := s.getKind
    if k == ``cSignChar then if isSigned then .i8 else .u8
    else if k == ``cSignShort then if isSigned then .i16 else .u16
    else if k == ``cSignLLong || k == ``cSignLong then if isSigned then .i64 else .u64
    else if isSigned then .i32 else .u32

mutual
private partial def elabExprExpanded (env : Environment) (stx : Syntax) : CommandElabM CExpr := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cLitExpr then
    let numStx := args[0]!
    let raw := numStx[0].getAtomVal
    let (v, rad) ←
      if raw.startsWith "0x" || raw.startsWith "0X" then
        let some n := numStx.isNatLit? | throwErrorAt numStx "invalid hex literal `{raw}`"
        pure (n, LitRadix.hex)
      else if raw.length > 1 && raw.startsWith "0" then
        match parseOctal (raw.drop 1).toString with
        | some n => pure (n, LitRadix.oct)
        | none => throwErrorAt numStx "invalid octal literal `{raw}`"
      else
        let some n := numStx.isNatLit? | throwErrorAt numStx "invalid decimal literal `{raw}`"
        pure (n, LitRadix.dec)
    let suf ← liftCoreM <| parseLitSuffix args[1]!
    return .lit (v : Int) (inferLitKind v rad suf) suf rad none
  else if k == ``cCharExpr then
    let some ch := args[0]!.isCharLit? | throwErrorAt stx "invalid char literal"
    return .lit (ch.toNat : Int) .i32 .none .char none
  else if k == ``cStrExpr then
    let strs ← args[0]!.getArgs.mapM fun s => do
      let some v := s.isStrLit? | throwErrorAt s "expected string literal"
      return v
    return .strLit (String.join strs.toList)
  else if k == ``cVarExpr then
    let nm := args[0]!.getId.toString
    match lookupMacro? env nm with
    | some (.constExpr v ty suf rad sym) => return .lit v ty suf rad (some sym)
    | _ => return .var nm
  else if k == ``cVaStart then
    return .vaStart args[2]!.getId.toString args[4]!.getId.toString
  else if k == ``cVaEnd then
    return .vaEnd args[2]!.getId.toString
  else if k == ``cSizeofTy then
    return .sizeOfTy (← elabTyExpanded env args[2]!)
  else if k == ``cSizeofEx then
    return .sizeOfExpr (← elabExprExpanded env args[1]!)
  else if k == ``cParenExpr then
    return .paren (← elabExprExpanded env args[1]!)
  else if k == ``cIndex then
    return .index (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!)
  else if k == ``cCall then
    let fn ← elabExprExpanded env args[0]!
    let cargs ← args[2]!.getSepArgs.toList.mapM (elabExprExpanded env)
    return .call fn cargs
  else if k == ``cMember then
    return .member (← elabExprExpanded env args[0]!) args[2]!.getId.toString
  else if k == ``cArrow then
    return .arrow (← elabExprExpanded env args[0]!) args[2]!.getId.toString
  else if k == ``cPostInc then return .incDec .postInc (← elabExprExpanded env args[0]!)
  else if k == ``cPostDec then return .incDec .postDec (← elabExprExpanded env args[0]!)
  else if k == ``cPreInc then return .incDec .preInc (← elabExprExpanded env args[1]!)
  else if k == ``cPreDec then return .incDec .preDec (← elabExprExpanded env args[1]!)
  else if k == ``cUnPlus then return .unary .plus (← elabExprExpanded env args[1]!)
  else if k == ``cUnNeg then return .unary .neg (← elabExprExpanded env args[1]!)
  else if k == ``cBitNot then return .unary .bitNot (← elabExprExpanded env args[1]!)
  else if k == ``cLogNot then return .unary .logNot (← elabExprExpanded env args[1]!)
  else if k == ``cDeref then return .deref (← elabExprExpanded env args[1]!)
  else if k == ``cAddrOf then return .addrOf (← elabExprExpanded env args[1]!)
  else if k == ``cCast then
    return .cast (← elabTyExpanded env args[1]!) (← elabExprExpanded env args[3]!)
  else if k == ``cCond then
    return .cond (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!) (← elabExprExpanded env args[4]!)
  else if k == ``cComma then
    return .comma (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!)
  else if k == ``cLogAnd then
    return .logAnd (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!)
  else if k == ``cLogOr then
    return .logOr (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!)
  else
    let binMap : List (Name × BinOp) :=
      [ (``cMul, .mul), (``cDiv, .div), (``cMod, .mod), (``cAdd, .add), (``cSub, .sub),
        (``cShl, .shl), (``cShr, .shr), (``cLt, .lt), (``cLe, .le), (``cGt, .gt), (``cGe, .ge),
        (``cEq, .eq), (``cNe, .ne), (``cBitAnd, .bitAnd), (``cBitXor, .bitXor), (``cBitOr, .bitOr) ]
    if let some bop := binMap.lookup k then
      return .binary bop (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!)
    let asgMap : List (Name × AssignOp) :=
      [ (``cAssignEq, .eq), (``cAssignAdd, .addEq), (``cAssignSub, .subEq), (``cAssignMul, .mulEq),
        (``cAssignDiv, .divEq), (``cAssignMod, .modEq), (``cAssignAnd, .andEq), (``cAssignOr, .orEq),
        (``cAssignXor, .xorEq), (``cAssignShl, .shlEq), (``cAssignShr, .shrEq) ]
    if let some aop := asgMap.lookup k then
      return .assign aop (← elabExprExpanded env args[0]!) (← elabExprExpanded env args[2]!)
    throwErrorAt stx "unsupported C expression syntax `{k}`"

private partial def elabDimsExpanded (env : Environment) (stx : Syntax) :
    CommandElabM (List (Option Nat)) := do
  stx.getArgs.toList.mapM fun grp => do
    match grp.getArgs[1]!.getOptional? with
    | none => return none
    | some eStx =>
      let e ← elabExprExpanded env eStx
      let n ← liftCoreM <| evalConstCExpr env e
      if n < 0 then throwErrorAt eStx "negative array dimension `{n}`"
      return some n.toNat

private partial def applyPtrMods (stx : Syntax) (base : CTy) : CTy :=
  stx.getArgs.foldl (fun acc pm => wrapConst (qualsHaveConst pm.getArgs[1]!) (.ptr acc)) base

private partial def elabTyBase (env : Environment) (stx : Syntax) : CommandElabM CTy := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cBaseVoid then return .void
  else if k == ``cBaseVaList then return .vaList
  else if k == ``cBaseChar then return .int .i8
  else if k == ``cBaseInt then return .int .i32
  else if k == ``cBaseShort then return .int .i16
  else if k == ``cBaseLong then return .int .i64
  else if k == ``cBaseUnsigned then return .int (signRestKind false args[1]!)
  else if k == ``cBaseSigned then return .int (signRestKind true args[1]!)
  else if k == ``cBaseStruct then return .structTy args[1]!.getId.toString
  else if k == ``cBaseUnion then return .unionTy args[1]!.getId.toString
  else if k == ``cBaseEnum then
    let tag := args[1]!.getId.toString
    let isU := match lookupTag? env tag with | some (.enumDef _ u) => u | _ => true
    return .enumTy tag isU
  else if k == ``cBaseAnonStruct then
    let flds ← elabFieldList env args[2]!
    return .anonStruct flds
  else if k == ``cBaseAnonUnion then
    let flds ← elabFieldList env args[2]!
    return .anonUnion flds
  else if k == ``cBaseTypedef then
    let id := args[0]!.getId.toString
    let some under := lookupTypedef? env id | throwErrorAt stx "unknown typedef `{id}`"
    return .typedef id under
  else throwErrorAt stx "unsupported C base type `{k}`"

private partial def elabTySpec (env : Environment) (stx : Syntax) : CommandElabM CTy := do
  let args := stx.getArgs
  let isC := qualsHaveConst args[0]! || qualsHaveConst args[2]!
  let base ← elabTyBase env args[1]!
  return wrapConst isC base

private partial def elabParams (env : Environment) (sepStx : Syntax) :
    CommandElabM (List Param × Bool) := do
  let elems := sepStx.getSepArgs.toList
  if elems.length == 1 && elems[0]!.getKind == ``cParamSimple then
    let args := elems[0]!.getArgs
    let ty ← elabTySpec env args[0]!
    if ty.unqual == .void && args[1]!.getArgs.isEmpty && args[2]!.getOptional?.isNone then
      return ([], false)
  let mut ps : List Param := []
  let mut variadic := false
  for i in [:elems.length] do
    let p := elems[i]!
    if p.getKind == ``cParamEllipsis then
      if i + 1 != elems.length then throwErrorAt p "`...` must be the last parameter"
      variadic := true
    else if p.getKind == ``cParamSimple then
      let args := p.getArgs
      let mut ty ← elabTySpec env args[0]!
      ty := applyPtrMods args[1]! ty
      let nm := (args[2]!.getOptional?.map (·.getId.toString)).getD ""
      let dims ← elabDimsExpanded env args[3]!
      ty := dims.foldr (fun d? acc => .array acc d?) ty
      ps := ps ++ [{ name := nm, ty }]
    else if p.getKind == ``cParamFnPtr then
      let args := p.getArgs
      let ret := applyPtrMods args[1]! (← elabTySpec env args[0]!)
      let nm := (args[4]!.getOptional?.map (·.getId.toString)).getD ""
      let (fps, fv) ← elabParams env args[7]!
      ps := ps ++ [{ name := nm, ty := .fnPtr ret (fps.map (·.ty)) fv }]
    else throwErrorAt p "unsupported C parameter `{p.getKind}`"
  return (ps, variadic)

private partial def elabTyExpanded (env : Environment) (stx : Syntax) : CommandElabM CTy := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cTySimple then
    let mut ty ← elabTySpec env args[0]!
    ty := applyPtrMods args[1]! ty
    let dims ← elabDimsExpanded env args[2]!
    return dims.foldr (fun d? acc => .array acc d?) ty
  else if k == ``cTyFnPtr then
    let ret := applyPtrMods args[1]! (← elabTySpec env args[0]!)
    let (ps, v) ← elabParams env args[6]!
    return .fnPtr ret (ps.map (·.ty)) v
  else throwErrorAt stx "unsupported C type `{k}`"

private partial def elabInitExpanded (env : Environment) (stx : Syntax) : CommandElabM InitVal := do
  if stx.getKind == ``cInitList then
    let xs ← stx.getArgs[1]!.getSepArgs.toList.mapM (elabInitExpanded env)
    return .list xs
  else if stx.getKind == ``cInitExpr then
    return .expr (← elabExprExpanded env stx.getArgs[0]!)
  else throwErrorAt stx "unsupported C initializer `{stx.getKind}`"

private partial def elabInitDeclExpanded (env : Environment) (baseTy : CTy) (isStatic : Bool)
    (stx : Syntax) : CommandElabM VarDecl := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cDeclVar then
    let mut ty := applyPtrMods args[0]! baseTy
    let nm := args[1]!.getId.toString
    let dims ← elabDimsExpanded env args[2]!
    ty := dims.foldr (fun d? acc => .array acc d?) ty
    let init? ← match optArgs? args[3]! with
      | none => pure none
      | some grp => some <$> elabInitExpanded env grp[1]!
    return { name := nm, ty, isStatic, isConst := ty.isConst, init? }
  else if k == ``cDeclFnPtr then
    let ret := applyPtrMods args[0]! baseTy
    let nm := args[3]!.getId.toString
    let (ps, v) ← elabParams env args[6]!
    let ty := CTy.fnPtr ret (ps.map (·.ty)) v
    let init? ← match optArgs? args[8]! with
      | none => pure none
      | some grp => some <$> elabInitExpanded env grp[1]!
    return { name := nm, ty, isStatic, isConst := false, init? }
  else throwErrorAt stx "unsupported C declarator `{k}`"

private partial def elabFieldList (env : Environment) (listStx : Syntax) :
    CommandElabM (List (String × CTy)) := do
  let mut out : List (String × CTy) := []
  for grp in listStx.getArgs do
    let fld := grp.getArgs[0]!
    let base ← elabTySpec env fld.getArgs[0]!
    for dStx in fld.getArgs[1]!.getSepArgs do
      let d ← elabInitDeclExpanded env base false dStx
      out := out ++ [(d.name, d.ty)]
  return out
end

private partial def elabStmtExpanded (env : Environment) (stx : Syntax) : CommandElabM CStmt := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cStmtNop then return .nop
  else if k == ``cStmtLocalDecls then
    let sym := args[1]!.getId
    let decls ← liftTermElabM do
      let ty := mkApp (mkConst ``List [Level.zero]) (mkConst ``VarDecl)
      unsafe Meta.evalExpr (List VarDecl) ty (mkConst sym)
    return .decls decls
  else if k == ``cStmtDecl then
    let dStx := args[0]!.getArgs
    let isStat := dStx[0]!.getNumArgs > 0
    let base ← elabTySpec env dStx[1]!
    let ds ← dStx[2]!.getSepArgs.toList.mapM (elabInitDeclExpanded env base isStat)
    return match ds with | [d] => .decl d | _ => .decls ds
  else if k == ``cStmtBlock then
    return .block (← args[1]!.getArgs.toList.mapM (elabStmtExpanded env))
  else if k == ``cStmtIf then
    let c ← elabExprExpanded env args[2]!
    let t ← elabStmtExpanded env args[4]!
    let f? ← match optArgs? args[5]! with
      | none => pure none
      | some grp => some <$> elabStmtExpanded env grp[1]!
    return .ifStmt c t f?
  else if k == ``cStmtWhile then
    return .whileStmt (← elabExprExpanded env args[2]!) (← elabStmtExpanded env args[4]!)
  else if k == ``cStmtDoWhile then
    return .doWhileStmt (← elabStmtExpanded env args[1]!) (← elabExprExpanded env args[4]!)
  else if k == ``cStmtFor then
    let optE (s : Syntax) : CommandElabM (Option CExpr) :=
      match s.getOptional? with | none => pure none | some e => some <$> elabExprExpanded env e
    return .forStmt (← optE args[2]!) (← optE args[4]!) (← optE args[6]!) (← elabStmtExpanded env args[8]!)
  else if k == ``cStmtSwitch then
    return .switchStmt (← elabExprExpanded env args[2]!) (← elabStmtExpanded env args[4]!)
  else if k == ``cStmtCase then
    let v ← liftCoreM <| evalConstCExpr env (← elabExprExpanded env args[1]!)
    return .caseStmt v .nop
  else if k == ``cStmtDefault then return .defaultStmt .nop
  else if k == ``cStmtBreak then return .breakStmt
  else if k == ``cStmtContinue then return .continueStmt
  else if k == ``cStmtGoto then return .gotoStmt args[1]!.getId.toString
  else if k == ``cStmtReturn then
    let e? ← match args[1]!.getOptional? with
      | none => pure none
      | some e => some <$> elabExprExpanded env e
    return .returnStmt e?
  else if k == ``cStmtLabel then
    return .labelStmt args[0]!.getId.toString .nop
  else if k == ``cStmtExpr then
    return .expr (← elabExprExpanded env args[0]!)
  else throwErrorAt stx "unsupported C statement `{k}`"

private def resolveLinkage (pre? mid? : Syntax) : Linkage :=
  match mid?.getOptional? with
  | some m =>
    if m.getKind == ``cLinkHidden then .hidden else .export_
  | none =>
    match pre?.getOptional? with
    | some p =>
      let pk := p.getKind
      if pk == ``cLinkLocal || pk == ``cLinkStatic then .static_
      else if pk == ``cLinkStaticInline then .staticInline
      else if pk == ``cLinkExtern then .extern_
      else .export_
    | none => .export_

private def appendItemChunk (chunk : Expr) : CommandElabM Unit :=
  modifyEnv fun env => activeTUExt.modifyState env fun opt =>
    opt.map fun atu => { atu with itemChunks := atu.itemChunks.push chunk }

private def appendTopItems (items : List TopItem) : CommandElabM Unit := do
  match items with
  | [.fnDef f] =>
    let env ← getEnv
    if let some atu := activeTUExt.getState env then
      let ns ← getCurrNamespace
      let helperName := ns ++ Name.mkSimple s!"{atu.leanName}_fn_{f.name}"
      liftTermElabM <| addAndCompile <| Declaration.defnDecl {
        name := helperName, levelParams := [], type := mkConst ``FnDef, value := toExpr f,
        hints := .abbrev, safety := .safe
      }
      appendItemChunk (mkListExpr (mkConst ``TopItem) [mkCon ``TopItem.fnDef #[mkConst helperName]])
    else
      appendItemChunk (mkListExpr (mkConst ``TopItem) (items.map toExpr))
  | _ =>
    appendItemChunk (mkListExpr (mkConst ``TopItem) (items.map toExpr))

private def expandAndElabExpr (stx : Syntax) : CommandElabM CExpr := do
  let env ← getEnv
  let exp ← liftCoreM <| expandCMacros env [] 64 stx
  elabExprExpanded env exp

private def elabEnumItems (env : Environment) (sepStx : Syntax) :
    CommandElabM (List (String × Option Int) × List (String × Int)) := do
  let mut items : List (String × Option Int) := []
  let mut consts : List (String × Int) := []
  let mut nextV : Int := 0
  for item in sepStx.getSepArgs do
    let nm := item.getArgs[0]!.getId.toString
    let v? ← match optArgs? item.getArgs[1]! with
      | none => pure none
      | some grp =>
        let exp ← liftCoreM <| expandCMacros env [] 64 grp[1]!
        let ce ← elabExprExpanded env exp
        some <$> liftCoreM (evalConstCExpr env ce)
    let val := v?.getD nextV
    items := items ++ [(nm, v?)]
    consts := (nm, val) :: consts
    nextV := val + 1
  return (items, consts)

/-! ## Command Elaborators (`c_*`) -/

@[command_elab cTuBegin]
def elabCTuBegin : CommandElab := fun stx => do
  modifyEnv fun env =>
    let env := localScopeExt.setState env {}
    activeTUExt.setState env (some { leanName := stx[1].getId, fileName := stx[2].isStrLit?.getD "", isHeader := false })

@[command_elab cHeaderBegin]
def elabCHeaderBegin : CommandElab := fun stx => do
  modifyEnv fun env =>
    let env := localScopeExt.setState env {}
    activeTUExt.setState env (some { leanName := stx[1].getId, fileName := stx[2].isStrLit?.getD "", isHeader := true })

private def finishTU (expectHeader : Bool) (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let some atu := activeTUExt.getState env | throwErrorAt stx "no active `c_tu_begin` / `c_header_begin`"
  if atu.isHeader != expectHeader then throwErrorAt stx "mismatched begin/end header vs translation unit"
  let reqName := stx[1].getId
  if atu.leanName != reqName then throwErrorAt stx "expected closing name `{atu.leanName}`, got `{reqName}`"
  let itemsExpr := mkAppendChunks (mkConst ``TopItem) atu.itemChunks.toList
  let ns ← getCurrNamespace
  let declName := ns ++ reqName
  let val := mkCon ``TU.mk #[toExpr atu.fileName, itemsExpr]
  liftTermElabM <| addAndCompile <| Declaration.defnDecl {
    name := declName, levelParams := [], type := mkConst ``TU, value := val,
    hints := .abbrev, safety := .safe
  }
  let viewName? := lookupSpecView? env
  let emitContracts := !expectHeader && (atu.contractNames.size > 0 || viewName?.isSome)
  let cListId := mkIdent (Name.mkSimple s!"{reqName}Contracts")
  let viewId := mkIdent (viewName?.getD ``Unit)
  let cIdents := atu.contractNames.map fun n => mkIdent (n.replacePrefix ns Name.anonymous)
  modifyEnv fun env =>
    let env := activeTUExt.setState env none
    if expectHeader then env else localScopeExt.setState env {}
  if emitContracts then
    let listStx ← `(term| [$cIdents,*])
    let cmdStx ← `(command| def $cListId : List (C99.FnContract $viewId) := $listStx)
    elabCommand cmdStx

@[command_elab cTuEnd] def elabCTuEnd : CommandElab := finishTU false
@[command_elab cHeaderEnd] def elabCHeaderEnd : CommandElab := finishTU true

@[command_elab cIncludeStr]
def elabCInclude : CommandElab := fun stx => do
  let some p := stx[1].isStrLit? | throwErrorAt stx "expected header path string"
  appendTopItems [.includeSys p]

@[command_elab cIncludeLocal]
def elabCIncludeLocal : CommandElab := fun stx => do
  let some p := stx[1].isStrLit? | throwErrorAt stx "expected local header path string"
  appendTopItems [.includeLocal p]

@[command_elab cPpRaw]
def elabCPpRaw : CommandElab := fun stx => do
  let some txt := stx[1].isStrLit? | throwErrorAt stx "expected preprocessor text"
  appendTopItems [.ppRaw txt]

@[command_elab cItemsCmd]
def elabCItems : CommandElab := fun stx => do
  let chunk ← liftTermElabM do
    let e ← Term.elabTerm stx[1] (some (mkApp (mkConst ``List [Level.zero]) (mkConst ``TopItem)))
    Term.synthesizeSyntheticMVarsNoPostponing
    pure e
  appendItemChunk chunk

@[command_elab cDefineConst]
def elabCDefineConst : CommandElab := fun stx => do
  let sym := stx[1].getId.toString
  let ce ← expandAndElabExpr stx[3]
  let env ← getEnv
  let v ← liftCoreM <| evalConstCExpr env ce
  let (ty, suf, rad) := match ce with
    | .lit _ k s r _ => (k, s, r)
    | _ => (.i32, .none, .dec)
  modifyEnv fun env => pushScopeData env {
    consts := [(sym, v)]
    macros := [(sym, .constExpr v ty suf rad sym)]
  }

@[command_elab cDefineExpr]
def elabCDefineExpr : CommandElab := fun stx => do
  let sym := stx[1].getId.toString
  let rhs := stx[3]
  let env ← getEnv
  let exp ← liftCoreM <| expandCMacros env [] 64 rhs
  let ce ← elabExprExpanded env exp
  let constEntry ← try
    let v ← liftCoreM <| evalConstCExpr env ce
    pure [(sym, v)]
  catch _ => pure []
  modifyEnv fun env => pushScopeData env { consts := constEntry, macros := [(sym, .objExpr rhs)] }

@[command_elab cDefineField]
def elabCDefineField : CommandElab := fun stx => do
  let sym := stx[1].getId.toString
  let path := stx[3].getSepArgs.toList.map (·.getId.toString)
  modifyEnv fun env => pushScopeData env { macros := [(sym, .fieldAlias path)] }

@[command_elab cMacroFn]
def elabCMacroFn : CommandElab := fun stx => do
  let sym := stx[1].getId.toString
  let ps := stx[3].getSepArgs.toList.map (·.getId.toString)
  modifyEnv fun env => pushScopeData env { macros := [(sym, .fnExpr ps stx[6])] }

@[command_elab cMacroStmt]
def elabCMacroStmt : CommandElab := fun stx => do
  let sym := stx[1].getId.toString
  let ps := stx[3].getSepArgs.toList.map (·.getId.toString)
  modifyEnv fun env => pushScopeData env { macros := [(sym, .fnStmt ps stx[6])] }

@[command_elab cTypedefCmd]
def elabCTypedef : CommandElab := fun stx => do
  let env ← getEnv
  let expSpec ← liftCoreM <| expandCMacros env [] 64 stx[1]
  let base ← elabTySpec env expSpec
  let mut items : List TopItem := []
  let mut tds : List (String × CTy) := []
  for dStx in stx[2].getSepArgs do
    let expD ← liftCoreM <| expandCMacros env [] 64 dStx
    let d ← elabInitDeclExpanded env base false expD
    items := items ++ [.typedefDecl d.name d.ty]
    tds := (d.name, d.ty) :: tds
  modifyEnv fun env => pushScopeData env { typedefs := tds }
  appendTopItems items

@[command_elab cFwdTag]
def elabCFwdTag : CommandElab := fun stx => do
  let isUnion := stx[1].getAtomVal == "union"
  let tag := stx[2].getId.toString
  appendTopItems [.fwdTag isUnion tag]

private def elabTagDefCmd (isUnion isTypedef : Bool) (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let (tag?, fldsStx, td?) :=
    if isTypedef then (stx[2].getOptional?.map (·.getId.toString), stx[4], some stx[6].getId.toString)
    else (some stx[1].getId.toString, stx[3], none)
  let expFlds ← liftCoreM <| expandCMacros env [] 64 fldsStx
  let flds ← elabFieldList env expFlds
  let defn := if isUnion then TagDef.unionDef flds else TagDef.structDef flds
  let mut tagsAcc : List (String × TagDef) := []
  let mut tdsAcc : List (String × CTy) := []
  if let some t := tag? then tagsAcc := [(t, defn)]
  if let some td := td? then
    tagsAcc := (td, defn) :: tagsAcc
    let under := match tag? with
      | some t => if isUnion then CTy.unionTy t else CTy.structTy t
      | none => if isUnion then CTy.anonUnion flds else CTy.anonStruct flds
    tdsAcc := [(td, under)]
  modifyEnv fun env => pushScopeData env { tags := tagsAcc, typedefs := tdsAcc }
  appendTopItems [.tagDecl isUnion tag? td? flds]

@[command_elab cStructCmd] def elabCStruct : CommandElab := elabTagDefCmd false false
@[command_elab cUnionCmd] def elabCUnion : CommandElab := elabTagDefCmd true false
@[command_elab cTypedefStructCmd] def elabCTypedefStruct : CommandElab := elabTagDefCmd false true
@[command_elab cTypedefUnionCmd] def elabCTypedefUnion : CommandElab := elabTagDefCmd true true

private def elabEnumCmdCommon (isTypedef : Bool) (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let (tag?, itemsStx, td?) :=
    if isTypedef then (stx[2].getOptional?.map (·.getId.toString), stx[4], some stx[6].getId.toString)
    else (stx[1].getOptional?.map (·.getId.toString), stx[3], none)
  let (items, consts) ← elabEnumItems env itemsStx
  let isU := items.all fun (_, v?) => match v? with | some v => v ≥ 0 | none => true
  let defn := TagDef.enumDef items isU
  let mut tagsAcc : List (String × TagDef) := []
  let mut tdsAcc : List (String × CTy) := []
  if let some t := tag? then tagsAcc := [(t, defn)]
  if let some td := td? then
    tagsAcc := (td, defn) :: tagsAcc
    let under := match tag? with | some t => CTy.enumTy t isU | none => CTy.int (if isU then .u32 else .i32)
    tdsAcc := [(td, under)]
  modifyEnv fun env => pushScopeData env { tags := tagsAcc, typedefs := tdsAcc, consts }
  appendTopItems [.enumDecl tag? td? items]

@[command_elab cEnumCmd] def elabCEnum : CommandElab := elabEnumCmdCommon false
@[command_elab cTypedefEnumCmd] def elabCTypedefEnum : CommandElab := elabEnumCmdCommon true

@[command_elab cVarCmd]
def elabCVar : CommandElab := fun stx => do
  let env ← getEnv
  let link := resolveLinkage stx[1] stx[3]
  let expSpec ← liftCoreM <| expandCMacros env [] 64 stx[2]
  let base ← elabTySpec env expSpec
  let mut items : List TopItem := []
  for dStx in stx[4].getSepArgs do
    let expD ← liftCoreM <| expandCMacros env [] 64 dStx
    let d ← elabInitDeclExpanded env base (link == .static_) expD
    items := items ++ [.globalDecl link d]
  appendTopItems items

@[command_elab cProtoCmd]
def elabCProto : CommandElab := fun stx => do
  let env ← getEnv
  let link := resolveLinkage stx[1] stx[4]
  let ret := applyPtrMods (← liftCoreM <| expandCMacros env [] 64 stx[3])
    (← elabTySpec env (← liftCoreM <| expandCMacros env [] 64 stx[2]))
  let nm := stx[5].getId.toString
  let (ps, v) ← elabParams env (← liftCoreM <| expandCMacros env [] 64 stx[7])
  appendTopItems [.fnProto link ret nm ps v]

private def intKindCtorName : IntKind → Name
  | .i8 => ``IntKind.i8 | .u8 => ``IntKind.u8
  | .i16 => ``IntKind.i16 | .u16 => ``IntKind.u16
  | .i32 => ``IntKind.i32 | .u32 => ``IntKind.u32
  | .i64 => ``IntKind.i64 | .u64 => ``IntKind.u64

private def intKindOfBitVecCtor : IntKind → Name
  | .i8 => ``Int8.ofBitVec | .u8 => ``UInt8.ofBitVec
  | .i16 => ``Int16.ofBitVec | .u16 => ``UInt16.ofBitVec
  | .i32 => ``Int32.ofBitVec | .u32 => ``UInt32.ofBitVec
  | .i64 => ``Int64.ofBitVec | .u64 => ``UInt64.ofBitVec

private def wrapParamUnpack (ps : List Param) (variadic : Bool)
    (argsScrut : Ident) (body : Term) : CommandElabM Term := do
  let vaId := mkIdent (Name.mkSimple "vaArgs")
  let mut entries : List (Term × Option (Ident × Name × Ident)) := []
  for (p, i) in ps.zipIdx do
    let pId ← if p.name == "" then
        mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple s!"__p_{i}")
      else
        pure (mkIdent (Name.mkSimple p.name))
    match p.ty.unqual.intKind? with
    | some k =>
      let bvId ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple s!"__bv_{i}")
      let kId := mkIdent (intKindCtorName k)
      let pat ← `(term| C99.Val.int $kId $bvId)
      entries := entries ++ [(pat, some (pId, intKindOfBitVecCtor k, bvId))]
    | none =>
      let pat ← `(term| $pId)
      entries := entries ++ [(pat, none)]
  let tailPat ← if variadic then `(term| $vaId) else `(term| [])
  let listPat ← entries.foldrM (fun (pat, _) acc => `(term| $pat :: $acc)) tailPat
  let boundBody ← entries.foldrM (fun (_, bind?) inner => do
    match bind? with
    | some (pId, convName, bvId) =>
      let convId := mkIdent convName
      `(term| let $pId := $convId $bvId; $inner)
    | none => pure inner) body
  `(term| match ($argsScrut) with | $listPat => $boundBody | _ => False)

private def wrapRetUnpack (retTy : CTy) (retScrut : Ident) (body : Term) : CommandElabM Term := do
  let retId := mkIdent (Name.mkSimple "ret")
  if retTy.isVoid then
    `(term| match ($retScrut) with | C99.Val.void => let $retId := (); $body | _ => False)
  else if let some k := retTy.unqual.intKind? then
    let bvId ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "__ret_bv")
    let kId := mkIdent (intKindCtorName k)
    let convId := mkIdent (intKindOfBitVecCtor k)
    `(term| match ($retScrut) with
      | C99.Val.int $kId $bvId => let $retId := $convId $bvId; $body
      | _ => False)
  else
    `(term| let $retId := $retScrut; $body)

@[command_elab cSpecViewCmd]
def elabCSpecView : CommandElab := fun stx => do
  let viewName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  modifyEnv fun env => pushScopeData env { specView := some viewName }

@[command_elab cFnCmd]
def elabCFn : CommandElab := fun stx => do
  let env ← getEnv
  let link := resolveLinkage stx[1] stx[4]
  let ret := applyPtrMods (← liftCoreM <| expandCMacros env [] 64 stx[3])
    (← elabTySpec env (← liftCoreM <| expandCMacros env [] 64 stx[2]))
  let nm := stx[5].getId.toString
  let (ps, v) ← elabParams env (← liftCoreM <| expandCMacros env [] 64 stx[7])
  let clauses := stx[9].getArgs
  let expBody ← liftCoreM <| expandCMacros env [] 64 stx[10]
  let body ← elabStmtExpanded env expBody
  appendTopItems [.fnDef { linkage := link, retTy := ret, name := nm, params := ps, variadic := v, body }]
  if !clauses.isEmpty then
    let envAfter ← getEnv
    let some atu := activeTUExt.getState envAfter
      | throwErrorAt stx "Verus contracts on `c_fn` require an enclosing `c_tu_begin`"
    let mut reqs : Array Term := #[]
    let mut mods : Array Term := #[]
    let mut enss : Array Term := #[]
    for cl in clauses do
      let ck := cl.getKind
      let t : Term := ⟨cl[1]!⟩
      if ck == ``cSpecRequires then reqs := reqs.push t
      else if ck == ``cSpecModifies then mods := mods.push t
      else if ck == ``cSpecEnsures then enss := enss.push t
      else throwErrorAt cl "unsupported `c_fn` spec clause `{ck}`"
    let tagsId := mkIdent (Name.mkSimple "tags")
    let ownedId := mkIdent (Name.mkSimple "owned")
    let viewId := mkIdent (Name.mkSimple "view")
    let mId := mkIdent (Name.mkSimple "m")
    let m'Id := mkIdent (Name.mkSimple "m'")
    let view'Id := mkIdent (Name.mkSimple "view'")
    let argsScrut ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "args")
    let retScrut ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "retVal")
    let bScrut ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "b")
    let reqBody ← if reqs.size > 0 then
        let mut acc := reqs.back!
        for i in [0 : reqs.size - 1] do
          let idx := reqs.size - 2 - i
          let t := reqs[idx]!
          acc ← `(term| ($t) ∧ ($acc))
        pure acc
      else `(term| True)
    let modBody ← if mods.size > 0 then
        let first := mods[0]!
        let mut acc ← `(term| ($first) $bScrut)
        for i in [1 : mods.size] do
          let t := mods[i]!
          acc ← `(term| ($acc) ∨ (($t) $bScrut))
        pure acc
      else `(term| False)
    let ensBody ← if enss.size > 0 then
        let mut acc := enss.back!
        for i in [0 : enss.size - 1] do
          let idx := enss.size - 2 - i
          let t := enss[idx]!
          acc ← `(term| ($t) ∧ ($acc))
        pure acc
      else `(term| $view'Id = $viewId)
    let wrappedPre ← wrapParamUnpack ps v argsScrut reqBody
    let wrappedMod ← if mods.size > 0 then wrapParamUnpack ps v argsScrut modBody else `(term| False)
    let wrappedPost ← wrapParamUnpack ps v argsScrut (← wrapRetUnpack ret retScrut ensBody)
    let viewTyId := mkIdent ((lookupSpecView? envAfter).getD ``Unit)
    let cDeclId := mkIdent (Name.mkSimple s!"{nm}_contract")
    let fnHelperId := mkIdent (Name.mkSimple s!"{atu.leanName}_fn_{nm}")
    let nmLit := Syntax.mkStrLit nm
    let cmdStx ← `(command|
      set_option linter.unusedVariables false in
      def $cDeclId : C99.FnContract $viewTyId where
        fnName := $nmLit
        paramTys := (C99.FnDef.params $fnHelperId).map C99.Param.ty
        variadic := C99.FnDef.variadic $fnHelperId
        retTy := C99.FnDef.retTy $fnHelperId
        pre := fun $tagsId $ownedId $viewId $mId $argsScrut => $wrappedPre
        modSet := fun $tagsId $ownedId $viewId $mId $argsScrut $bScrut => $wrappedMod
        post := fun $tagsId $ownedId $viewId $mId $argsScrut $retScrut $m'Id $view'Id => $wrappedPost)
    elabCommand cmdStx
    let ns ← getCurrNamespace
    let fullContractName := ns ++ Name.mkSimple s!"{nm}_contract"
    modifyEnv fun env => activeTUExt.modifyState env fun opt =>
      opt.map fun a => { a with contractNames := a.contractNames.push fullContractName }

end C99.DSL
