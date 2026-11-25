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

private def mkArrayIntExpr (vals : Array Int) : Expr :=
  mkApp2 (mkConst ``Array.mk [Level.zero]) (mkConst ``Int)
    (mkListExpr (mkConst ``Int) (vals.toList.map toExpr))

private partial def exprOfInit : InitVal → Expr
  | .expr e => mkCon ``InitVal.expr #[exprOfCExpr e]
  | .list xs => mkCon ``InitVal.list #[mkListExpr (mkConst ``InitVal) (xs.map exprOfInit)]
  | .intSeq r vs => mkCon ``InitVal.intSeq #[toExpr r, mkArrayIntExpr vs]

instance : ToExpr InitVal where toExpr := exprOfInit; toTypeExpr := mkConst ``InitVal

instance : ToExpr VarDecl where
  toTypeExpr := mkConst ``VarDecl
  toExpr d := mkCon ``VarDecl.mk
    #[toExpr d.name, exprOfCTy d.ty, toExpr d.isStatic,
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

private def qualsHaveConst (env : Environment) (stx : Syntax) : Bool :=
  stx.getArgs.any fun q =>
    let k := q.getKind
    k == ``cQualConst ||
      (k == ``cQualAlias && lookupQualAlias? env q[0].getId.toString == some true)

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

private partial def applyPtrMods (env : Environment) (stx : Syntax) (base : CTy) : CTy :=
  stx.getArgs.foldl (fun acc pm => wrapConst (qualsHaveConst env pm.getArgs[1]!) (.ptr acc)) base

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
  let isC := qualsHaveConst env args[0]! || qualsHaveConst env args[2]!
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
      ty := applyPtrMods env args[1]! ty
      let nm := (args[2]!.getOptional?.map (·.getId.toString)).getD ""
      let dims ← elabDimsExpanded env args[3]!
      ty := dims.foldr (fun d? acc => .array acc d?) ty
      ps := ps ++ [{ name := nm, ty }]
    else if p.getKind == ``cParamFnPtr then
      let args := p.getArgs
      let ret := applyPtrMods env args[1]! (← elabTySpec env args[0]!)
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
    ty := applyPtrMods env args[1]! ty
    let dims ← elabDimsExpanded env args[2]!
    return dims.foldr (fun d? acc => .array acc d?) ty
  else if k == ``cTyFnPtr then
    let ret := applyPtrMods env args[1]! (← elabTySpec env args[0]!)
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
    let mut ty := applyPtrMods env args[0]! baseTy
    let nm := args[1]!.getId.toString
    let dims ← elabDimsExpanded env args[2]!
    ty := dims.foldr (fun d? acc => .array acc d?) ty
    let init? ← match optArgs? args[3]! with
      | none => pure none
      | some grp => some <$> elabInitExpanded env grp[1]!
    return { name := nm, ty, isStatic, init? }
  else if k == ``cDeclFnPtr then
    let ret := applyPtrMods env args[0]! baseTy
    let nm := args[3]!.getId.toString
    let (ps, v) ← elabParams env args[6]!
    let ty := CTy.fnPtr ret (ps.map (·.ty)) v
    let init? ← match optArgs? args[8]! with
      | none => pure none
      | some grp => some <$> elabInitExpanded env grp[1]!
    return { name := nm, ty, isStatic, init? }
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

private def resolveLinkage (env : Environment) (pre? mid? : Syntax) : Linkage :=
  match mid?.getOptional? with
  | some m =>
    if m.getKind == ``cLinkMidAlias then
      (lookupLinkAlias? env m[0].getId.toString).getD .export_
    else .export_
  | none =>
    match pre?.getOptional? with
    | some p =>
      let pk := p.getKind
      if pk == ``cLinkStatic then .static_
      else if pk == ``cLinkStaticInline then .staticInline
      else if pk == ``cLinkExtern then .extern_
      else if pk == ``cLinkPreAlias then
        (lookupLinkAlias? env p[0].getId.toString).getD .export_
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

@[command_elab cIncludeTuCmd]
def elabCIncludeTu : CommandElab := fun stx => do
  let chunk ← liftTermElabM do
    let tuExpr ← Term.elabTerm stx[1] (some (mkConst ``TU))
    Term.synthesizeSyntheticMVarsNoPostponing
    pure (mkApp (mkConst ``TU.items) tuExpr)
  appendItemChunk chunk

@[command_elab cQualAliasCmd]
def elabCQualAlias : CommandElab := fun stx => do
  let aliasName := stx[1].getId.toString
  let isConst ← match stx[3].getId.toString with
    | "const" => pure true
    | "none" => pure false
    | other => throwErrorAt stx[3] "expected `const` or `none`, got `{other}`"
  modifyEnv fun env => pushScopeData env { qualAliases := [(aliasName, isConst)] }

@[command_elab cLinkAliasCmd]
def elabCLinkAlias : CommandElab := fun stx => do
  let aliasName := stx[1].getId.toString
  let link ← match stx[3].getId.toString with
    | "static" => pure Linkage.static_
    | "export" => pure Linkage.export_
    | "hidden" => pure Linkage.hidden
    | "staticInline" => pure Linkage.staticInline
    | "extern" => pure Linkage.extern_
    | other => throwErrorAt stx[3] "expected `static`, `export`, or `hidden`, got `{other}`"
  modifyEnv fun env => pushScopeData env { linkAliases := [(aliasName, link)] }

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

private def extractPureIntLit? : CExpr → Option (Int × LitRadix)
  | .lit v _ _ r none => some (v, r)
  | .unary .neg (.lit v _ _ r none) => some (-v, r)
  | .unary .plus (.lit v _ _ r none) => some (v, r)
  | .paren e => extractPureIntLit? e
  | _ => none

private partial def collectIntSeq (ty : CTy) (iv : InitVal) (acc : Array Int) (rad? : Option LitRadix) :
    Option (Array Int × Option LitRadix) := do
  match ty.unqual, iv with
  | .array el len?, .list xs =>
    guard (!xs.isEmpty)
    match len? with
    | some n => guard (xs.length == n)
    | none => pure ()
    if el.isArray then
      xs.foldlM (fun (a, r?) x => collectIntSeq el x a r?) (acc, rad?)
    else
      match el.unqual with
      | .int _ =>
        xs.foldlM (fun (a, r?) x => do
          match x with
          | .expr e =>
            let (v, r) ← extractPureIntLit? e
            pure (a.push v, r?.orElse fun _ => some r)
          | _ => none) (acc, rad?)
      | _ => none
  | _, _ => none

private def tryFoldIntSeq (ty : CTy) (iv : InitVal) : Option (LitRadix × Array Int) := do
  let (vals, rad?) ← collectIntSeq ty iv #[] none
  return (rad?.getD .dec, vals)

@[command_elab cGlobalCmd]
def elabCGlobal : CommandElab := fun stx => do
  let env ← getEnv
  let link := resolveLinkage env stx[1] stx[3]
  let expSpec ← liftCoreM <| expandCMacros env [] 64 stx[2]
  let base ← elabTySpec env expSpec
  let mut items : List Expr := []
  let ns ← getCurrNamespace
  let atu? := activeTUExt.getState env
  for dStx in stx[4].getSepArgs do
    let expD ← liftCoreM <| expandCMacros env [] 64 dStx
    let mut d ← elabInitDeclExpanded env base false expD
    if d.ty.isArray && d.ty.arrayLeafIntKind?.isSome then
      if let some iv := d.init? then
        if let some (rad, vals) := tryFoldIntSeq d.ty iv then
          d := { d with init? := some (.intSeq rad vals) }
    match atu?, link != .extern_ with
    | some atu, true =>
      let dExpr ← match d.init? with
        | some (.intSeq rad vals) =>
          let valsName := ns ++ Name.mkSimple s!"{atu.leanName}_vals_{d.name}"
          liftTermElabM <| addAndCompile <| Declaration.defnDecl {
            name := valsName, levelParams := [], type := mkApp (mkConst ``Array [Level.zero]) (mkConst ``Int),
            value := mkArrayIntExpr vals, hints := .abbrev, safety := .safe
          }
          let seqExpr := mkCon ``InitVal.intSeq #[toExpr rad, mkConst valsName]
          pure <| mkCon ``VarDecl.mk #[toExpr d.name, exprOfCTy d.ty, toExpr d.isStatic,
            mkOptExpr (mkConst ``InitVal) (some seqExpr)]
        | _ => pure (toExpr d)
      let globalName := ns ++ Name.mkSimple s!"{atu.leanName}_global_{d.name}"
      liftTermElabM <| addAndCompile <| Declaration.defnDecl {
        name := globalName, levelParams := [], type := mkConst ``VarDecl,
        value := dExpr, hints := .abbrev, safety := .safe
      }
      items := items ++ [mkCon ``TopItem.globalDecl #[toExpr link, mkConst globalName]]
    | _, _ =>
      items := items ++ [toExpr (TopItem.globalDecl link d)]
  appendItemChunk (mkListExpr (mkConst ``TopItem) items)

@[command_elab cProtoCmd]
def elabCProto : CommandElab := fun stx => do
  let env ← getEnv
  let link := resolveLinkage env stx[1] stx[4]
  let ret := applyPtrMods env (← liftCoreM <| expandCMacros env [] 64 stx[3])
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

@[command_elab cSpecLibCmd]
def elabCSpecLib : CommandElab := fun stx => do
  modifyEnv fun env => pushScopeData env { specLib := some stx[1].getId }

private def validSpecCtxArgs : List String :=
  ["tags", "owned", "view", "m", "m'", "view'", "ret"]

@[command_elab cSpecPredCmd]
def elabCSpecPred : CommandElab := fun stx => do
  let predName := stx[1].getId.toString
  let ctxArgs := stx[3].getSepArgs.toList.map (·.getId.toString)
  for a in ctxArgs do
    if !validSpecCtxArgs.contains a then
      throwErrorAt stx[3] "invalid spec context argument `{a}`; expected one of {validSpecCtxArgs}"
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[6]
  modifyEnv fun env => pushScopeData env { specPreds := [(predName, ctxArgs, constName)] }

@[command_elab cSpecConstCmd]
def elabCSpecConst : CommandElab := fun stx => do
  let aliasName := stx[1].getId.toString
  let constName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  modifyEnv fun env => pushScopeData env { specConsts := [(aliasName, constName)] }

/-! ## C-Style Spec Elaborator (`c_spec`) -/

private inductive SpecValTy where
  | sint (k : IntKind)
  | uint (k : IntKind)
  | nat
  | lit
  | bool
  | ptr (pointee : CTy)
  | fnPtr
  | val
  | other
  deriving Inhabited

private def SpecValTy.isNumericLike : SpecValTy → Bool
  | .sint _ | .uint _ | .nat | .lit => true
  | _ => false

private def shouldUseNatCmp (lTy rTy : SpecValTy) : Bool :=
  lTy.isNumericLike && rTy.isNumericLike &&
  match lTy, rTy with
  | .nat, _ | _, .nat => true
  | .sint _, _ | _, .sint _ => false
  | .uint _, _ | _, .uint _ => true
  | _, _ => false

private def combineSpecArithTy (lTy rTy : SpecValTy) : SpecValTy :=
  match lTy, rTy with
  | .nat, _ | _, .nat => .nat
  | .sint k, _ | _, .sint k => .sint k
  | .uint k, _ | _, .uint k => .uint k
  | .lit, .lit => .lit
  | _, _ => .other

private def classifyCTy (t : CTy) : SpecValTy :=
  match t.intKind? with
  | some k => if k.signed then .sint k else .uint k
  | none =>
    match t.unqual with
    | .ptr inner => .ptr inner
    | .array inner _ => .ptr inner
    | .fnPtr .. => .fnPtr
    | _ => .val

private partial def ctyToTerm (ty : CTy) : CommandElabM Term := do
  match ty.unqual with
  | .void => `(term| C99.CTy.void)
  | .int k =>
    let kId := mkIdent (intKindCtorName k)
    `(term| C99.CTy.int $kId)
  | .ptr inner =>
    let innerT ← ctyToTerm inner
    `(term| C99.CTy.ptr $innerT)
  | .structTy tag =>
    let s := Syntax.mkStrLit tag
    `(term| C99.CTy.structTy $s)
  | .unionTy tag =>
    let s := Syntax.mkStrLit tag
    `(term| C99.CTy.unionTy $s)
  | .enumTy tag isU =>
    let s := Syntax.mkStrLit tag
    let uId := mkIdent (if isU then ``Bool.true else ``Bool.false)
    `(term| C99.CTy.enumTy $s $uId)
  | .vaList => `(term| C99.CTy.vaList)
  | .array elem len? =>
    let elT ← ctyToTerm elem
    match len? with
    | none => `(term| C99.CTy.array $elT Option.none)
    | some n =>
      let nLit := Syntax.mkNumLit (toString n)
      `(term| C99.CTy.array $elT (Option.some $nLit))
  | .fnPtr r ps v =>
    let rT ← ctyToTerm r
    let psT ← ps.mapM ctyToTerm
    let psArr := psT.toArray
    let vId := mkIdent (if v then ``Bool.true else ``Bool.false)
    `(term| C99.CTy.fnPtr $rT [$psArr,*] $vId)
  | _ => throwError "unsupported pointee C type in spec"

private inductive UnivRead where
  | field (key : String) (readFn : Term) (memId : Ident) (pTerm : Term)
      (tag fld : String) (varId : Ident) (ty : SpecValTy)
  | strlen (key : String) (memId : Ident) (pTerm : Term) (bId oId lenId : Ident)
  deriving Inhabited

private def UnivRead.key : UnivRead → String
  | .field k .. => k
  | .strlen k .. => k

private def UnivRead.boundEntry : UnivRead → String × Ident × SpecValTy
  | .field k _ _ _ _ _ vId ty => (k, vId, ty)
  | .strlen k _ _ _ _ lId => (k, lId, .nat)

private structure ExistRead where
  key : String
  ptrName? : Option String
  readTerm : Term
  varId : Ident
  deriving Inhabited

private structure SpecState where
  existReads : Array ExistRead := #[]
  univReads : Array UnivRead := #[]
  deriving Inhabited

private structure SpecCtx where
  env : Environment
  libNs? : Option Name
  tagsId : Ident
  ownedId : Ident
  viewId : Ident
  view'Id : Ident
  mId : Ident
  m'Id : Ident
  memId : Ident
  retId : Ident
  varTys : List (String × SpecValTy)
  boundUniv : List (String × Ident × SpecValTy) := []

private partial def stxShapeKey : Syntax → String
  | .ident _ _ n _ => s!"I({n})"
  | .atom _ s => s!"A({s})"
  | .node _ k args => s!"N({k}:{(args.map stxShapeKey).toList |> String.intercalate ","})"
  | .missing => "M"

private def freshSpecId (pfx : String) : CommandElabM Ident :=
  mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple pfx)

private def requireSpecLibFn (ctx : SpecCtx) (stx : Syntax) (fnName : String) :
    CommandElabM Term := do
  let some ns := ctx.libNs?
    | throwErrorAt stx "spec primitive `{fnName}` requires `c_spec_lib <Namespace>` in scope"
  return mkIdent (ns ++ Name.mkSimple fnName)

private def specCtxArgIdent (ctx : SpecCtx) : String → Ident
  | "tags" => ctx.tagsId
  | "owned" => ctx.ownedId
  | "view" => ctx.viewId
  | "m" => ctx.mId
  | "m'" => ctx.m'Id
  | "view'" => ctx.view'Id
  | _ => ctx.retId

private def specCtxArgTerm (ctx : SpecCtx) (s : String) : Term :=
  specCtxArgIdent ctx s

private def wrapExist (reads : List ExistRead) (body : Term) : CommandElabM Term :=
  reads.foldrM (fun r acc =>
    let vId := r.varId
    let rd := r.readTerm
    `(term| ∃ $vId:ident, $rd = Option.some $vId ∧ ($acc))) body

private def wrapUniv (ctx : SpecCtx) (reads : List UnivRead) (body : Term) : CommandElabM Term :=
  reads.foldrM (fun r acc => match r with
    | .field _ readFn memId pTerm tag fld vId _ =>
      let tagLit := Syntax.mkStrLit tag
      let fldLit := Syntax.mkStrLit fld
      `(term| ∀ $vId:ident, $readFn $ctx.tagsId $memId $pTerm $tagLit $fldLit = Option.some $vId → ($acc))
    | .strlen _ memId pTerm bId oId lenId =>
      `(term| ∀ $bId:ident $oId:ident $lenId:ident, $pTerm = C99.Val.ptr $bId $oId → ($memId).strlenAt $bId $oId = Option.some $lenId → ($acc))) body

private partial def stripSpecParens (stx : Syntax) : Syntax :=
  if stx.getKind == ``cSpecParen then stripSpecParens stx[1]! else stx

private def varNameOfSpec? (stx : Syntax) : Option String :=
  let s := stripSpecParens stx
  if s.getKind == ``cSpecVar then some s[0]!.getId.toString else none

private partial def nullGuardPtr? (stx : Syntax) : Option String :=
  let s := stripSpecParens stx
  if s.getKind == ``cSpecEq then
    match varNameOfSpec? s[0]!, varNameOfSpec? s[2]! with
    | some p, some "NULL" => some p
    | some "NULL", some p => some p
    | _, _ => none
  else none

private partial def nonNullGuardPtrs (stx : Syntax) : List String :=
  let s := stripSpecParens stx
  if s.getKind == ``cSpecAnd then
    nonNullGuardPtrs s[0]! ++ nonNullGuardPtrs s[2]!
  else if s.getKind == ``cSpecNe then
    match varNameOfSpec? s[0]!, varNameOfSpec? s[2]! with
    | some p, some "NULL" => [p]
    | some "NULL", some p => [p]
    | _, _ => []
  else []

private def lookupTagFieldTy? (env : Environment) (tag fld : String) : Option CTy := do
  let flds ← match lookupTag? env tag with
    | some (.structDef flds) | some (.unionDef flds) => some flds
    | _ => none
  flds.lookup fld

private def resolveSpecArrowTarget (ctx : SpecCtx) (stx : Syntax) (pTy : SpecValTy) (fld : String) :
    CommandElabM (String × CTy) := do
  let .ptr inner := pTy
    | throwErrorAt stx "spec `->` expects pointer target before field `{fld}`"
  let tag ← match inner.unqual with
    | .structTy t | .unionTy t => pure t
    | _ => throwErrorAt stx "spec `->` requires struct/union pointer"
  let some fldTy := lookupTagFieldTy? ctx.env tag fld
    | throwErrorAt stx "unknown field `{fld}` on `struct {tag}`"
  return (tag, fldTy)

private def isPropLevelNode (stx : Syntax) : Bool :=
  let s := stripSpecParens stx
  let k := s.getKind
  k == ``cSpecAnd || k == ``cSpecOr || k == ``cSpecImp || k == ``cSpecForall ||
  k == ``cSpecForallIn || k == ``cSpecExists || k == ``cSpecLet || k == ``cSpecEq ||
  k == ``cSpecNe || k == ``cSpecLt || k == ``cSpecLe || k == ``cSpecGt || k == ``cSpecGe

mutual
private partial def elabSpecExpr (ctx : SpecCtx) (stx : Syntax) (st : SpecState) :
    CommandElabM ((Term × SpecValTy × Bool) × SpecState) := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cSpecLean then
    return ((⟨args[2]!⟩, .other, false), st)
  else if k == ``cSpecNum then
    return ((⟨args[0]!⟩, .lit, false), st)
  else if k == ``cSpecParen then
    let ((t, ty, bit), st1) ← elabSpecExpr ctx args[1]! st
    return (((← `(term| ($t))), ty, bit), st1)
  else if k == ``cSpecVar then
    let nm := args[0]!.getId.toString
    if nm == "NULL" then
      return (((← `(term| C99.Val.null)), .val, false), st)
    else if nm == "true" then
      return ((mkIdent ``Bool.true, .bool, false), st)
    else if nm == "false" then
      return ((mkIdent ``Bool.false, .bool, false), st)
    else if let some ty := ctx.varTys.lookup nm then
      return ((mkIdent (Name.mkSimple nm), ty, false), st)
    else if let some cname := lookupSpecConst? ctx.env nm then
      return ((mkIdent cname, .other, false), st)
    else if let some cval := lookupConst? ctx.env nm then
      let t ← if cval < 0 then
          let nLit := Syntax.mkNumLit (toString (-cval))
          `(term| -$nLit)
        else
          pure (Syntax.mkNumLit (toString cval))
      return ((t, .lit, false), st)
    else
      throwErrorAt stx "unknown identifier `{nm}` in C spec"
  else if k == ``cSpecCast then
    let expTy ← liftCoreM <| expandCMacros ctx.env [] 64 args[1]!
    let castTy ← elabTyExpanded ctx.env expTy
    let ((t, _, bit), st1) ← elabSpecExpr ctx args[3]! st
    return ((t, classifyCTy castTy, bit), st1)
  else if k == ``cSpecDeref then
    let pStx := args[1]!
    let ((pTerm, pTy, _), st1) ← elabSpecExpr ctx pStx st
    let .ptr inner := pTy
      | throwErrorAt stx "spec `*` requires a pointer operand"
    if inner.unqual != .int .u64 then
      throwErrorAt stx "spec `*` currently supports 64-bit integer pointers (`uint64`/`z_size_t`/`uLong`)"
    let readFn ← requireSpecLibFn ctx stx "readU64?"
    let key := "u64:" ++ stxShapeKey pTerm.raw
    match st1.existReads.find? (·.key == key) with
    | some er =>
      return ((mkIdent er.varId.getId, .nat, false), st1)
    | none =>
      let vId ← freshSpecId "__val"
      let readTerm ← `(term| $readFn $ctx.memId $pTerm)
      let er : ExistRead := { key, ptrName? := varNameOfSpec? pStx, readTerm, varId := vId }
      return ((mkIdent vId.getId, .nat, false), { st1 with existReads := st1.existReads.push er })
  else if k == ``cSpecArrow then
    let pStx := args[0]!
    let fld := args[2]!.getId.toString
    let ((pTerm, pTy, _), st1) ← elabSpecExpr ctx pStx st
    let (tag, fldTy) ← resolveSpecArrowTarget ctx stx pTy fld
    let isNat := fldTy.intKind?.isSome
    let resTy := if isNat then .nat else classifyCTy fldTy
    let key := s!"fld:{tag}.{fld}:{stxShapeKey pTerm.raw}"
    if let some (_, vId, ty) := ctx.boundUniv.find? (·.1 == key) then
      return ((mkIdent vId.getId, ty, false), st1)
    if let some ur := st1.univReads.find? (·.key == key) then
      let (_, vId, ty) := ur.boundEntry
      return ((mkIdent vId.getId, ty, false), st1)
    let readFn ← requireSpecLibFn ctx stx (if isNat then "readNatField?" else "readField?")
    let vId ← freshSpecId s!"__{fld}"
    let ur := UnivRead.field key readFn ctx.memId pTerm tag fld vId resTy
    return ((mkIdent vId.getId, resTy, false), { st1 with univReads := st1.univReads.push ur })
  else if k == ``cSpecField then
    let ((rTerm, _, _), st1) ← elabSpecExpr ctx args[0]! st
    let fldId := mkIdent (Name.mkSimple args[2]!.getId.toString)
    return (((← `(term| ($rTerm).$fldId)), .other, false), st1)
  else if k == ``cSpecApp then
    let fnStx := stripSpecParens args[0]!
    let argStxs := args[2]!.getSepArgs
    if fnStx.getKind == ``cSpecVar then
      let fnName := fnStx[0]!.getId.toString
      if fnName == "block" then
        if argStxs.size != 1 then throwErrorAt stx "`block(...)` takes 1 argument"
        let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
        let ptrBlkFn ← requireSpecLibFn ctx stx "PtrBlock"
        return (((← `(term| $ptrBlkFn $pT)), .other, false), st1)
      else if fnName == "strlen" then
        if argStxs.size != 1 then throwErrorAt stx "`strlen(...)` takes 1 argument"
        let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
        let key := "strlen:" ++ stxShapeKey pT.raw
        if let some (_, lenId, _) := ctx.boundUniv.find? (·.1 == key) then
          return ((mkIdent lenId.getId, .nat, false), st1)
        if let some ur := st1.univReads.find? (·.key == key) then
          let (_, lenId, _) := ur.boundEntry
          return ((mkIdent lenId.getId, .nat, false), st1)
        let bId ← freshSpecId "__b"
        let oId ← freshSpecId "__o"
        let lenId ← freshSpecId "__len"
        let ur := UnivRead.strlen key ctx.memId pT bId oId lenId
        return ((mkIdent lenId.getId, .nat, false), { st1 with univReads := st1.univReads.push ur })
      else if let some (ctxArgs, cName) := lookupSpecPred? ctx.env fnName then
        let mut curSt := st
        let mut argTerms : Array Term := ctxArgs.toArray.map (specCtxArgTerm ctx)
        for a in argStxs do
          let ((at_, _, _), nxt) ← elabSpecExpr ctx a curSt
          argTerms := argTerms.push at_
          curSt := nxt
        let fnId := mkIdent cName
        return (((← `(term| $fnId $argTerms*)), .other, false), curSt)
      else
        throwErrorAt stx "unknown function `{fnName}` in C spec expression"
    else if fnStx.getKind == ``cSpecField then
      let ((rT, _, _), st1) ← elabSpecExpr ctx fnStx[0]! st
      let methId := mkIdent (Name.mkSimple fnStx[2]!.getId.toString)
      let mut curSt := st1
      let mut argTerms : Array Term := #[]
      for a in argStxs do
        let ((at_, _, _), nxt) ← elabSpecExpr ctx a curSt
        argTerms := argTerms.push at_
        curSt := nxt
      return (((← `(term| ($rT).$methId $argTerms*)), .other, false), curSt)
    else
      throwErrorAt stx "unsupported call target in C spec expression"
  else if k == ``cSpecNeg then
    let ((t, ty, bit), st1) ← elabSpecExpr ctx args[1]! st
    return (((← `(term| -$t)), ty, bit), st1)
  else if k == ``cSpecBitNot then
    let ((t, ty, _), st1) ← elabSpecExpr ctx args[1]! st
    return (((← `(term| ~~~($t))), ty, true), st1)
  else if k == ``cSpecCond then
    let (cTerm, st1) ← elabSpecBool ctx args[0]! st
    let ((tTerm, tTy, tBit), st2) ← elabSpecExpr ctx args[2]! st1
    let ((fTerm, _, fBit), st3) ← elabSpecExpr ctx args[4]! st2
    return (((← `(term| (if $cTerm then $tTerm else $fTerm))), tTy, tBit || fBit), st3)
  else if k == ``cSpecMul || k == ``cSpecDiv || k == ``cSpecMod || k == ``cSpecAdd ||
          k == ``cSpecSub || k == ``cSpecShl || k == ``cSpecShr ||
          k == ``cSpecBitAnd || k == ``cSpecBitXor || k == ``cSpecBitOr then
    let ((lt, lTy, lBit), st1) ← elabSpecExpr ctx args[0]! st
    let ((rt, rTy, rBit), st2) ← elabSpecExpr ctx args[2]! st1
    let resTy := combineSpecArithTy lTy rTy
    let t ←
      if k == ``cSpecMul then `(term| ($lt * $rt))
      else if k == ``cSpecDiv then `(term| ($lt / $rt))
      else if k == ``cSpecMod then `(term| ($lt % $rt))
      else if k == ``cSpecAdd then `(term| ($lt + $rt))
      else if k == ``cSpecSub then `(term| ($lt - $rt))
      else if k == ``cSpecShl then `(term| ($lt <<< $rt))
      else if k == ``cSpecShr then `(term| ($lt >>> $rt))
      else if k == ``cSpecBitAnd then `(term| ($lt &&& $rt))
      else if k == ``cSpecBitXor then `(term| ($lt ^^^ $rt))
      else `(term| ($lt ||| $rt))
    let isBit := lBit || rBit || k == ``cSpecBitAnd || k == ``cSpecBitXor || k == ``cSpecBitOr
    return ((t, resTy, isBit), st2)
  else
    throwErrorAt stx "unsupported C spec expression `{k}`"

private partial def elabSpecNat (ctx : SpecCtx) (stx : Syntax) (st : SpecState) :
    CommandElabM (Term × SpecState) := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cSpecNum then
    return (⟨args[0]!⟩, st)
  else if k == ``cSpecParen then
    let (t, st1) ← elabSpecNat ctx args[1]! st
    return ((← `(term| ($t))), st1)
  else if k == ``cSpecMul || k == ``cSpecDiv || k == ``cSpecMod || k == ``cSpecAdd ||
          k == ``cSpecSub || k == ``cSpecShl || k == ``cSpecShr then
    let (lt, st1) ← elabSpecNat ctx args[0]! st
    let (rt, st2) ← elabSpecNat ctx args[2]! st1
    let t ←
      if k == ``cSpecMul then `(term| ($lt * $rt))
      else if k == ``cSpecDiv then `(term| ($lt / $rt))
      else if k == ``cSpecMod then `(term| ($lt % $rt))
      else if k == ``cSpecAdd then `(term| ($lt + $rt))
      else if k == ``cSpecSub then `(term| ($lt - $rt))
      else if k == ``cSpecShl then `(term| ($lt <<< $rt))
      else `(term| ($lt >>> $rt))
    return (t, st2)
  else
    let ((t, ty, _), st1) ← elabSpecExpr ctx stx st
    let natT ← match ty with
      | .nat | .lit => pure t
      | .uint _ => `(term| ($t).toNat)
      | .sint _ => `(term| ($t).toNatClampNeg)
      | _ => pure t
    return (natT, st1)

private partial def elabSpecCmp (ctx : SpecCtx) (isBool : Bool) (stx : Syntax) (st : SpecState) :
    CommandElabM (Term × SpecState) := do
  let k := stx.getKind
  let lStx := stx[0]!
  let rStx := stx[2]!
  let ((lt, lTy, lBit), stL) ← elabSpecExpr ctx lStx st
  let ((rt, rTy, rBit), stLR) ← elabSpecExpr ctx rStx stL
  let (lhs, rhs, stOut) ←
    if !lBit && !rBit && shouldUseNatCmp lTy rTy then
      let (ln, s1) ← elabSpecNat ctx lStx st
      let (rn, s2) ← elabSpecNat ctx rStx s1
      pure (ln, rn, s2)
    else
      pure (lt, rt, stLR)
  if isBool then
    let b ←
      if k == ``cSpecEq then `(term| ($lhs == $rhs))
      else if k == ``cSpecNe then `(term| ($lhs != $rhs))
      else if k == ``cSpecLt then `(term| decide ($lhs < $rhs))
      else if k == ``cSpecLe then `(term| decide ($lhs ≤ $rhs))
      else if k == ``cSpecGt then `(term| decide ($lhs > $rhs))
      else `(term| decide ($lhs ≥ $rhs))
    return (b, stOut)
  else
    let p ←
      if k == ``cSpecEq then `(term| $lhs = $rhs)
      else if k == ``cSpecNe then `(term| $lhs ≠ $rhs)
      else if k == ``cSpecLt then `(term| $lhs < $rhs)
      else if k == ``cSpecLe then `(term| $lhs ≤ $rhs)
      else if k == ``cSpecGt then `(term| $lhs > $rhs)
      else `(term| $lhs ≥ $rhs)
    return (p, stOut)

private partial def elabSpecBool (ctx : SpecCtx) (stx : Syntax) (st : SpecState) :
    CommandElabM (Term × SpecState) := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cSpecParen then
    elabSpecBool ctx args[1]! st
  else if k == ``cSpecVar then
    let nm := args[0]!.getId.toString
    if nm == "true" then return (mkIdent ``Bool.true, st)
    else if nm == "false" then return (mkIdent ``Bool.false, st)
    else
      let ((t, _, _), st1) ← elabSpecExpr ctx stx st
      return (t, st1)
  else if k == ``cSpecNot then
    let (t, st1) ← elabSpecBool ctx args[1]! st
    return ((← `(term| !$t)), st1)
  else if k == ``cSpecAnd then
    let (lt, st1) ← elabSpecBool ctx args[0]! st
    let (rt, st2) ← elabSpecBool ctx args[2]! st1
    return ((← `(term| ($lt && $rt))), st2)
  else if k == ``cSpecOr then
    let (lt, st1) ← elabSpecBool ctx args[0]! st
    let (rt, st2) ← elabSpecBool ctx args[2]! st1
    return ((← `(term| ($lt || $rt))), st2)
  else if k == ``cSpecEq || k == ``cSpecNe || k == ``cSpecLt ||
          k == ``cSpecLe || k == ``cSpecGt || k == ``cSpecGe then
    elabSpecCmp ctx true stx st
  else
    let ((t, _, _), st1) ← elabSpecExpr ctx stx st
    return (t, st1)

private partial def elabSpecAppProp (ctx : SpecCtx) (stx : Syntax) (st : SpecState) :
    CommandElabM (Term × SpecState) := do
  let fnStx := stripSpecParens stx[0]!
  let argStxs := stx[2]!.getSepArgs
  if fnStx.getKind == ``cSpecVar then
    let fnName := fnStx[0]!.getId.toString
    if fnName == "valid" || fnName == "valid_or_null" then
      if argStxs.size != 1 then throwErrorAt stx "`{fnName}(...)` takes 1 argument"
      let ((pT, pTy, _), st1) ← elabSpecExpr ctx argStxs[0]! st
      let .ptr inner := pTy
        | throwErrorAt stx "`{fnName}(...)` requires a pointer argument"
      let ctyT ← ctyToTerm inner
      let predFn ← requireSpecLibFn ctx stx (if fnName == "valid" then "TypedCell" else "OptTypedCell")
      return ((← `(term| $predFn $ctx.tagsId $ctx.memId $pT $ctyT)), st1)
    else if fnName == "readable" || fnName == "writable" ||
            fnName == "opt_readable" || fnName == "opt_writable" then
      if argStxs.size != 2 then throwErrorAt stx "`{fnName}(...)` takes 2 arguments"
      let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
      let (lenT, st2) ← elabSpecNat ctx argStxs[1]! st1
      let libFnName :=
        if fnName == "readable" then "Readable"
        else if fnName == "writable" then "Writable"
        else if fnName == "opt_readable" then "OptReadable"
        else "OptWritable"
      let predFn ← requireSpecLibFn ctx stx libFnName
      return ((← `(term| $predFn $ctx.memId $pT $lenT)), st2)
    else if fnName == "cstring" || fnName == "opt_cstring" || fnName == "safe_fmt" then
      if argStxs.size != 1 then throwErrorAt stx "`{fnName}(...)` takes 1 argument"
      let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
      let libFnName :=
        if fnName == "cstring" then "CString"
        else if fnName == "opt_cstring" then "OptCString"
        else "SafeFmtString"
      let predFn ← requireSpecLibFn ctx stx libFnName
      return ((← `(term| $predFn $ctx.memId $pT)), st1)
    else if fnName == "zero_ptr" then
      if argStxs.size != 1 then throwErrorAt stx "`zero_ptr(...)` takes 1 argument"
      let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
      let predFn ← requireSpecLibFn ctx stx "ZeroPtr"
      return ((← `(term| $predFn $pT)), st1)
    else if fnName == "fn_ptr" then
      if argStxs.size != 1 then throwErrorAt stx "`fn_ptr(...)` takes 1 argument"
      let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
      let fnSym ← freshSpecId "__fn"
      return ((← `(term| ∃ $fnSym:ident, $pT = C99.Val.fnPtr $fnSym)), st1)
    else if fnName == "ptr_or_null" then
      if argStxs.size != 1 then throwErrorAt stx "`ptr_or_null(...)` takes 1 argument"
      let ((pT, _, _), st1) ← elabSpecExpr ctx argStxs[0]! st
      let bId ← freshSpecId "__b"
      let oId ← freshSpecId "__off"
      return ((← `(term| $pT = C99.Val.null ∨ ∃ $bId:ident $oId:ident, $pT = C99.Val.ptr $bId $oId)), st1)
    else if fnName == "disjoint_owned" then
      if argStxs.size == 0 then throwErrorAt stx "`disjoint_owned(...)` expects at least 1 argument"
      let predFn ← requireSpecLibFn ctx stx "DisjointFrom"
      let mut curSt := st
      let mut ps : Array Term := #[]
      for a in argStxs do
        let ((pt, _, _), nxt) ← elabSpecExpr ctx a curSt
        ps := ps.push pt
        curSt := nxt
      let mut acc ← `(term| $predFn $(ps.back!) $ctx.ownedId)
      for i in [0 : ps.size - 1] do
        let pT := ps[ps.size - 2 - i]!
        acc ← `(term| $predFn $pT $ctx.ownedId ∧ ($acc))
      return (acc, curSt)
    else if fnName == "separated" then
      if argStxs.size < 2 then throwErrorAt stx "`separated(...)` expects at least 2 arguments"
      let predFn ← requireSpecLibFn ctx stx "PtrDisjoint"
      let mut curSt := st
      let mut ps : Array Term := #[]
      for a in argStxs do
        let ((pt, _, _), nxt) ← elabSpecExpr ctx a curSt
        ps := ps.push pt
        curSt := nxt
      let mut pairs : Array (Term × Term) := #[]
      for i in [:ps.size] do
        for j in [i + 1 : ps.size] do
          pairs := pairs.push (ps[i]!, ps[j]!)
      let last := pairs.back!
      let mut acc ← `(term| $predFn $(last.1) $(last.2))
      for idx in [0 : pairs.size - 1] do
        let pr := pairs[pairs.size - 2 - idx]!
        acc ← `(term| $predFn $(pr.1) $(pr.2) ∧ ($acc))
      return (acc, curSt)
    else if fnName == "initialized" then
      if argStxs.size != 1 then throwErrorAt stx "`initialized(...)` takes 1 argument"
      let target := stripSpecParens argStxs[0]!
      if target.getKind != ``cSpecArrow then
        throwErrorAt argStxs[0]! "`initialized(...)` expects a field access `p->fld`"
      let fld := target[2]!.getId.toString
      let ((pT, pTy, _), st1) ← elabSpecExpr ctx target[0]! st
      let (tag, fldTy) ← resolveSpecArrowTarget ctx target pTy fld
      let readFn ← requireSpecLibFn ctx stx (if fldTy.intKind?.isSome then "readNatField?" else "readField?")
      let vId ← freshSpecId s!"__{fld}"
      let tagLit := Syntax.mkStrLit tag
      let fldLit := Syntax.mkStrLit fld
      return ((← `(term| ∃ $vId:ident, $readFn $ctx.tagsId $ctx.memId $pT $tagLit $fldLit = Option.some $vId)), st1)
    else if let some (ctxArgs, cName) := lookupSpecPred? ctx.env fnName then
      let mut curSt := st
      let mut argTerms : Array Term := ctxArgs.toArray.map (specCtxArgTerm ctx)
      for a in argStxs do
        let ((at_, _, _), nxt) ← elabSpecExpr ctx a curSt
        argTerms := argTerms.push at_
        curSt := nxt
      let fnId := mkIdent cName
      return ((← `(term| $fnId $argTerms*)), curSt)
    else
      throwErrorAt stx "unknown predicate `{fnName}` in C spec"
  else if fnStx.getKind == ``cSpecField then
    let ((rT, _, _), st1) ← elabSpecExpr ctx fnStx[0]! st
    let methId := mkIdent (Name.mkSimple fnStx[2]!.getId.toString)
    let mut curSt := st1
    let mut argTerms : Array Term := #[]
    for a in argStxs do
      let ((at_, _, _), nxt) ← elabSpecExpr ctx a curSt
      argTerms := argTerms.push at_
      curSt := nxt
    return ((← `(term| ($rT).$methId $argTerms*)), curSt)
  else
    throwErrorAt stx "unsupported call target in C spec proposition"

private partial def elabSpecPropNode (ctx : SpecCtx) (dischargeUniv : Bool) (stx : Syntax)
    (st : SpecState) : CommandElabM (Term × SpecState) := do
  let k := stx.getKind
  let args := stx.getArgs
  if k == ``cSpecParen then
    elabSpecPropNode ctx dischargeUniv args[1]! st
  else if k == ``cSpecAnd then
    let (lt, st1) ← elabSpecPropNode ctx dischargeUniv args[0]! st
    let (rt, st2) ← elabSpecPropNode ctx dischargeUniv args[2]! st1
    return ((← `(term| ($lt) ∧ ($rt))), st2)
  else if k == ``cSpecOr then
    let (lt, st1) ← elabSpecPropNode ctx true args[0]! st
    match nullGuardPtr? args[0]! with
    | some guardPtr =>
      let preKeys := st1.existReads.map (·.key)
      let (rt, st2) ← elabSpecPropNode ctx true args[2]! { st1 with univReads := #[] }
      let newExist := st2.existReads.extract st1.existReads.size st2.existReads.size
      let (discharged, kept) := newExist.partition fun er =>
        !preKeys.contains er.key && er.ptrName? == some guardPtr
      let rtWrapped ← wrapExist discharged.toList rt
      return ((← `(term| ($lt) ∨ ($rtWrapped))),
        { existReads := st1.existReads ++ kept, univReads := st.univReads })
    | none =>
      let (rt, st2) ← elabSpecPropNode ctx true args[2]! { st1 with univReads := #[] }
      return ((← `(term| ($lt) ∨ ($rt))), { st2 with univReads := st.univReads })
  else if k == ``cSpecImp then
    let preKeys := st.existReads.map (·.key)
    let (lt, st1) ← elabSpecPropNode ctx false args[0]! { st with univReads := #[] }
    let lUniv := st1.univReads
    let newBound := lUniv.toList.map UnivRead.boundEntry
    let guardPtrs := nonNullGuardPtrs args[0]!
    let ctxR := { ctx with boundUniv := newBound ++ ctx.boundUniv }
    let (rt, st2) ← elabSpecPropNode ctxR true args[2]! { st1 with univReads := #[] }
    let newR := st2.existReads.extract st1.existReads.size st2.existReads.size
    let (dischargedR, keptR) := newR.partition fun er =>
      !preKeys.contains er.key && (er.ptrName?.map guardPtrs.contains |>.getD false)
    let rtWrapped ← wrapExist dischargedR.toList rt
    let impT ← `(term| ($lt) → ($rtWrapped))
    if dischargeUniv then
      return (← wrapUniv ctx lUniv.toList impT,
        { existReads := st1.existReads ++ keptR, univReads := st.univReads })
    else
      return (impT, { existReads := st1.existReads ++ keptR, univReads := st.univReads ++ lUniv })
  else if k == ``cSpecNot then
    let sub := args[1]!
    if isPropLevelNode sub || sub.getKind == ``cSpecApp then
      let (pt, st1) ← elabSpecPropNode ctx false sub { st with univReads := #[] }
      let negT ← `(term| ¬ ($pt))
      if dischargeUniv then
        return (← wrapUniv ctx st1.univReads.toList negT, { st1 with univReads := st.univReads })
      else
        return (negT, { st1 with univReads := st.univReads ++ st1.univReads })
    else
      let ((t, _, _), st1) ← elabSpecExpr ctx sub { st with univReads := #[] }
      let eqT ← `(term| $t = Bool.true → False)
      if dischargeUniv then
        return (← wrapUniv ctx st1.univReads.toList eqT, { st1 with univReads := st.univReads })
      else
        return (eqT, { st1 with univReads := st.univReads ++ st1.univReads })
  else if k == ``cSpecCond then
    let (ct, st1) ← elabSpecBool ctx args[0]! { st with univReads := #[] }
    let condUniv := st1.univReads
    let ctxBr := { ctx with boundUniv := condUniv.toList.map UnivRead.boundEntry ++ ctx.boundUniv }
    let (tt, st2) ← elabSpecPropNode ctxBr true args[2]! { st1 with univReads := #[] }
    let (ft, st3) ← elabSpecPropNode ctxBr true args[4]! { st2 with univReads := #[] }
    let iteT ← `(term| if $ct then ($tt) else ($ft))
    if dischargeUniv then
      return (← wrapUniv ctx condUniv.toList iteT, { st3 with univReads := st.univReads })
    else
      return (iteT, { st3 with univReads := st.univReads ++ condUniv })
  else if k == ``cSpecForall || k == ``cSpecExists then
    let isAll := k == ``cSpecForall
    let nm := args[2]!.getId.toString
    let vId := mkIdent (Name.mkSimple nm)
    let ctxB := { ctx with varTys := (nm, .other) :: ctx.varTys }
    let (bt, st1) ← elabSpecPropNode ctxB true args[4]! { existReads := st.existReads, univReads := #[] }
    let newEx := st1.existReads.extract st.existReads.size st1.existReads.size
    let bt' ← wrapExist newEx.toList bt
    let qT ← if isAll then `(term| ∀ $vId:ident, ($bt')) else `(term| ∃ $vId:ident, ($bt'))
    return (qT, st)
  else if k == ``cSpecForallIn then
    let nm := args[2]!.getId.toString
    let vId := mkIdent (Name.mkSimple nm)
    let ((colT, _, _), st1) ← elabSpecExpr ctx args[4]! { st with univReads := #[] }
    let ctxB := { ctx with varTys := (nm, .val) :: ctx.varTys }
    let (bt, st2) ← elabSpecPropNode ctxB true args[6]! { st1 with univReads := #[] }
    let newEx := st2.existReads.extract st1.existReads.size st2.existReads.size
    let bt' ← wrapExist newEx.toList bt
    let qT ← `(term| ∀ $vId:ident ∈ $colT, ($bt'))
    let outT ← if dischargeUniv then wrapUniv ctx st1.univReads.toList qT else pure qT
    return (outT, { st with existReads := st1.existReads, univReads := if dischargeUniv then st.univReads else st.univReads ++ st1.univReads })
  else if k == ``cSpecLet then
    let xName := args[1]!.getId.toString
    let xId := mkIdent (Name.mkSimple xName)
    let baseEx := st.existReads.size
    let ((eTerm, eTy, _), stE) ← elabSpecExpr ctx args[3]! { st with univReads := #[] }
    let newUniv := stE.univReads
    let newExist := stE.existReads.extract baseEx stE.existReads.size
    let preExist := stE.existReads.extract 0 baseEx
    let ctxB0 := { ctx with varTys := (xName, eTy) :: ctx.varTys }
    if newExist.isEmpty && newUniv.size == 1 && eTerm.raw.isIdent then
      let renamed? := match newUniv[0]! with
        | .field key rf memId pT tag fld vId _ =>
          if eTerm.raw.getId == vId.getId then
            some (UnivRead.field key rf memId pT tag fld xId eTy)
          else none
        | .strlen key memId pT bId oId lId =>
          if eTerm.raw.getId == lId.getId then
            some (UnivRead.strlen key memId pT bId oId xId)
          else none
      if let some ur := renamed? then
        let ctxB := { ctxB0 with boundUniv := ur.boundEntry :: ctxB0.boundUniv }
        let (bt, stB) ← elabSpecPropNode ctxB true args[5]! { existReads := preExist, univReads := #[] }
        return (← wrapUniv ctx [ur] bt, { existReads := stB.existReads, univReads := st.univReads })
    if newUniv.isEmpty && newExist.size == 1 && eTerm.raw.isIdent then
      let er := newExist[0]!
      if eTerm.raw.getId == er.varId.getId then
        let er' := { er with varId := xId }
        let (bt, stB) ← elabSpecPropNode ctxB0 true args[5]! { existReads := preExist.push er', univReads := #[] }
        return (bt, { existReads := stB.existReads, univReads := st.univReads })
    let (bt, stB) ← elabSpecPropNode { ctxB0 with boundUniv := newUniv.toList.map UnivRead.boundEntry ++ ctxB0.boundUniv }
      true args[5]! { existReads := stE.existReads, univReads := #[] }
    let letT ← `(term| let $xId := $eTerm; ($bt))
    return (← wrapUniv ctx newUniv.toList letT, { existReads := stB.existReads, univReads := st.univReads })
  else
    let baseUniv := st.univReads.size
    let (atomT, st1) ←
      if k == ``cSpecLean then
        pure ((⟨args[2]!⟩ : Term), st)
      else if k == ``cSpecVar then
        let nm := args[0]!.getId.toString
        if nm == "true" then pure (mkIdent ``True, st)
        else if nm == "false" then pure (mkIdent ``False, st)
        else
          let ((t, _, _), s1) ← elabSpecExpr ctx stx st
          pure (t, s1)
      else if k == ``cSpecEq || k == ``cSpecNe || k == ``cSpecLt ||
              k == ``cSpecLe || k == ``cSpecGt || k == ``cSpecGe then
        elabSpecCmp ctx false stx st
      else if k == ``cSpecApp then
        elabSpecAppProp ctx stx st
      else
        let ((t, _, _), s1) ← elabSpecExpr ctx stx st
        pure (t, s1)
    let localUniv := (st1.univReads.extract baseUniv st1.univReads.size).toList
    if dischargeUniv then
      return (← wrapUniv ctx localUniv atomT,
        { existReads := st1.existReads, univReads := st.univReads })
    else
      return (atomT, st1)
end

private def elabSpecClauseProp (ctx : SpecCtx) (stx : Syntax) : CommandElabM Term := do
  let (t, st) ← elabSpecPropNode ctx true stx {}
  wrapExist st.existReads.toList t

private def elabSpecMod (ctx : SpecCtx) (args : Array Syntax) (bScrut : Ident) :
    CommandElabM Term := do
  if args.size == 1 then
    let item := stripSpecParens args[0]!
    if item.getKind == ``cSpecVar && item[0]!.getId.toString == "nothing" then
      return ← `(term| False)
    else if item.getKind == ``cSpecLean then
      let t : Term := ⟨item[2]!⟩
      return ← `(term| ($t) $bScrut)
    else if item.getKind == ``cSpecApp then
      let fnStx := stripSpecParens item[0]!
      if fnStx.getKind == ``cSpecVar then
        let fnName := fnStx[0]!.getId.toString
        if let some (ctxArgs, cName) := lookupSpecPred? ctx.env fnName then
          let mut curSt : SpecState := {}
          let mut argTerms : Array Term := ctxArgs.toArray.map (specCtxArgTerm ctx)
          for a in item[2]!.getSepArgs do
            let ((at_, _, _), nxt) ← elabSpecExpr ctx a curSt
            argTerms := argTerms.push at_
            curSt := nxt
          let fnId := mkIdent cName
          return ← `(term| ($fnId $argTerms*) $bScrut)
  let writesFn ← requireSpecLibFn ctx args[0]! "writes"
  let mut curSt : SpecState := {}
  let mut ptrTerms : Array Term := #[]
  for a in args do
    let ((pt, _, _), nxt) ← elabSpecExpr ctx a curSt
    ptrTerms := ptrTerms.push pt
    curSt := nxt
  `(term| ($writesFn [$ptrTerms,*]) $bScrut)

private def initialSpecVarTys (ps : List Param) (variadic : Bool) (retTy : CTy) (inEnsures : Bool) :
    List (String × SpecValTy) :=
  let paramTys := ps.filterMap fun p =>
    if p.name == "" then none else some (p.name, classifyCTy p.ty)
  let retEntry := if inEnsures then
      [("ret", if retTy.isVoid then .other else classifyCTy retTy)]
    else []
  let vaEntry := if variadic then [("vaArgs", .other)] else []
  let ctxEntries := [("view", .other), ("view'", .other), ("m", .other), ("m'", .other), ("tags", .other), ("owned", .other)]
  paramTys ++ retEntry ++ vaEntry ++ ctxEntries

@[command_elab cFnCmd]
def elabCFn : CommandElab := fun stx => do
  let env ← getEnv
  let link := resolveLinkage env stx[1] stx[4]
  let ret := applyPtrMods env (← liftCoreM <| expandCMacros env [] 64 stx[3])
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
    let tagsId := mkIdent (Name.mkSimple "tags")
    let ownedId := mkIdent (Name.mkSimple "owned")
    let viewId := mkIdent (Name.mkSimple "view")
    let mId := mkIdent (Name.mkSimple "m")
    let m'Id := mkIdent (Name.mkSimple "m'")
    let view'Id := mkIdent (Name.mkSimple "view'")
    let retId := mkIdent (Name.mkSimple "ret")
    let argsScrut ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "args")
    let retScrut ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "retVal")
    let bScrut ← mkIdent <$> MonadQuotation.addMacroScope (Name.mkSimple "b")
    let baseCtx (inEnsures : Bool) : SpecCtx := {
      env := envAfter
      libNs? := lookupSpecLib? envAfter
      tagsId, ownedId, viewId, view'Id, mId, m'Id
      memId := if inEnsures then m'Id else mId
      retId
      varTys := initialSpecVarTys ps v ret inEnsures
    }
    let mut reqs : Array Term := #[]
    let mut mods : Array Term := #[]
    let mut enss : Array Term := #[]
    for cl in clauses do
      let ck := cl.getKind
      if ck == ``cSpecRequires then
        reqs := reqs.push (← elabSpecClauseProp (baseCtx false) cl[1]!)
      else if ck == ``cSpecModifies then
        mods := mods.push (← elabSpecMod (baseCtx false) cl[1]!.getSepArgs bScrut)
      else if ck == ``cSpecEnsures then
        enss := enss.push (← elabSpecClauseProp (baseCtx true) cl[1]!)
      else
        throwErrorAt cl "unsupported `c_fn` spec clause `{ck}`"
    let reqBody ← if reqs.size > 0 then
        let mut acc := reqs.back!
        for i in [0 : reqs.size - 1] do
          let idx := reqs.size - 2 - i
          let t := reqs[idx]!
          acc ← `(term| ($t) ∧ ($acc))
        pure acc
      else `(term| True)
    let modBody ← if mods.size > 0 then
        let mut acc := mods[0]!
        for i in [1 : mods.size] do
          let t := mods[i]!
          acc ← `(term| ($acc) ∨ ($t))
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
