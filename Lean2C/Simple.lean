import Lean
import Lean2C.ABI
import Lean2C.Headers
import ZlibF.Runtime.CAbi
import ZlibF.Runtime.ControlFlow
import ZlibF.Runtime.Address
import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables
import ZlibF.Zlib.«gzguts.h»
/-! Minimal, Zlib-agnostic `MetaM`-based Lean-`Expr` to C99 module compiler. -/
namespace Lean2C.Simple
open Lean Meta Lean2C.ABI
private abbrev VarEntry := String × String × String
private inductive Dest where
  | ret (isVoid : Bool)
  | vars (vs : List VarEntry)
  | unit
  | exitOnTrue (target : String)
  /-- A direct return to the outer mode dispatcher. Variables introduced in
      nested branches cannot be used at a shared case label. -/
  | modeTail (scope : LocalContext)
  | outTuple (outs : List (Nat × String × OutKind)) (isVoid : Bool)
  | loopStep (vs : List VarEntry) (retDest : Dest) (continueTo : Option String := none)
  | gotoStep (labelName : String) (stateVs : List VarEntry) (doneDest : Dest)
  | fwdStep (labelName : String) (stateVs : List VarEntry)
private structure State where
  vars : Std.HashMap FVarId (List VarEntry) := {}
  arrVars : Std.HashMap FVarId (List (String × String)) := {}
  stackArrays : Std.HashSet String := {}
  joinArrs : Std.HashMap FVarId (List (List (String × String))) := {}
  lastArrs : List (String × String) := []
  strLitVars : Std.HashMap FVarId String := {}
  structPtrs : Std.HashMap FVarId (String × Name) := {}
  immutableRecords : FVarIdSet := {}
  deflateIds : Std.HashMap FVarId String := {}
  stackFVars : FVarIdSet := {}
  letActions : Std.HashMap FVarId Expr := {}
  origOutFVars : List (FVarId × String × OutKind) := []
  joins : Std.HashMap FVarId (List (List VarEntry) × Bool) := {}
  joinGuards : Std.HashMap FVarId String := {}
  caseJoins : Std.HashMap FVarId String := {}
  sharedCases : Array (Expr × String) := #[]
  placedCases : Std.HashSet String := {}
  inInflateDispatch : Bool := false
  decoderReturn : Option (String × String) := none
  forwardDecoderReturn : Bool := false
  decoderFrame : Option (String × String) := none
  pointerCells : Std.HashMap FVarId String := {}
  decoderCursor : Option (FVarId × String) := none
  selectedRecord : Option FVarId := none
  breakVar? : Option String := none
  mutLocals : List (String × String) := []
  cdeclVars : Std.HashMap Name (List VarEntry) := {}
  fnRetDest : Dest := .unit
  varargs? : Option (FVarId × String) := none
  used : NameSet := {}
  optionDecls : List (String × String) := []
  rangeExit? : Option (String × Bool) := none
  nextSuffix : Std.HashMap String Nat := {}
  lines : Array String := #[]
  scopedLocals : Bool := false
  temporaries : Array String := #[]
  indent : Nat := 1
  staticsMap : List (String × Name) := []
  usedStatics : Array (String × Name) := #[]
  functionAddresses : Array Name := #[]
  localTbls : Array Name := #[]
  constCache : Std.HashMap Expr String := {}
  inCondFlag : String := ""
private abbrev M := StateRefT State MetaM
private def takeLast {α : Type} (xs : List α) (n : Nat) : List α := xs.drop (xs.length - n)
private def hasSubstr (h needle : String) : Bool := (h.splitOn needle).length > 1
private def stripZ (e : Expr) : Expr :=
  if e.isAppOfArity ``C.M 1 || e.isAppOfArity ``Zlib.GzFs.G 1 || e.isAppOfArity ``C.PointerLocalM 1 then
    e.getAppArgs.back!
  else e
private partial def stripMeta (e : Expr) : Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Eq 3 && e.getAppArgs.back!.isConstOf ``Bool.true then stripMeta e.getAppArgs[1]!
  else if e.isAppOfArity ``Decidable.decide 2 then stripMeta e.getAppArgs[0]!
  else if e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``liftM 5 then stripMeta e.getAppArgs.back! else e
private def natLitOf? : Expr → Option Nat | .lit (.natVal n) => some n | e => if e.isAppOfArity ``OfNat.ofNat 3 then match e.getAppArgs[1]! with | .lit (.natVal n) => some n | _ => none else none
private partial def unwrapOrder (t : Expr) (ord? : Option Nat := none) : Option Nat × Expr :=
  let i := stripZ t
  if i.isAppOfArity ``C.COrder 2 then unwrapOrder i.getAppArgs[1]! (ord?.orElse fun _ => natLitOf? i.getAppArgs[0]!)
  else if t.isAppOfArity ``C.COrder 2 then unwrapOrder t.getAppArgs[1]! (ord?.orElse fun _ => natLitOf? t.getAppArgs[0]!) else (ord?, t)
private def unwrapLinkage (t : Expr) : (Option (Linkage × Bool × Bool × Bool) × Expr) :=
  let t := stripZ (unwrapOrder t).2; let (n?, a) := (t.getAppFn.constName?, t.getAppArgs)
  let strOf (e : Expr) := match e with | .lit (.strVal s) => s | _ => ""
  if n? == some ``C.CExportAs && a.size == 2 then (some (.exportAs (strOf a[0]!), false, false, false), a[1]!)
  else if n? == some ``C.CHiddenAs && a.size == 2 then (some (.hiddenAs (strOf a[0]!), false, false, false), a[1]!)
  else if n? == some ``C.CStaticAs && a.size == 2 then (some (.staticAs (strOf a[0]!), false, false, false), a[1]!)
  else if a.size == 1 then match n?.bind (linkageTable.lookup ·) with | some info => (some info, a[0]!) | none => (none, t) else (none, t)
private def isRuntimeConst (n : Name) : Bool := [`C, `Zlib.GzFs, `Lean, `Init, `Std].any (·.isPrefixOf n)
private def isZlibModConst (env : Environment) (n : Name) : Bool := (env.getModuleIdxFor? n).any fun idx => let m := env.header.moduleNames[idx.toNat]!; (`ZlibF.Zlib).isPrefixOf m && m != `ZlibF.Zlib.gzfs
private def isLocalStruct (env : Environment) (sn : Name) : Bool := isStructure env sn && !isABIStruct sn && !isRuntimeConst sn && (cTypeHead? (mkConst sn)).isNone && isZlibModConst env sn
/-- Scalar and tuple payloads need a presence tag, including when the payload is zero. -/
private partial def optionShape? (ty : Expr) : MetaM (Option (String × List String)) := do
  if ty.isConstOf ``C.BPtr then return some ("bytes", ["unsigned char *"])
  let ty ← whnfR ty
  if ty.isAppOfArity ``C.Ptr 1 && ty.appArg!.isConstOf ``C.BRef then return some ("bytes", ["unsigned char *"])
  if ty.isConstOf ``UInt32 then return some ("u32", ["unsigned"])
  if ty.isConstOf ``Bool then return some ("bool", ["int"])
  if ty.isAppOfArity ``Prod 2 then
    let some (leftName, leftFields) ← optionShape? ty.getAppArgs[0]! | return none
    let some (rightName, rightFields) ← optionShape? ty.getAppArgs[1]! | return none
    return some ("pair_" ++ leftName ++ "_" ++ rightName, leftFields ++ rightFields)
  return none

private def taggedOption? (ty : Expr) : MetaM (Option (String × List String)) := do
  let ty ← whnfR ty
  unless ty.isAppOfArity ``Option 1 do return none
  let payload := ty.getAppArgs[0]!
  let head ← whnfR payload
  unless head.isAppOfArity ``Prod 2 || head.isConstOf ``UInt32 || head.isConstOf ``Bool do return none
  return (← optionShape? payload).map fun (name, fields) => ("lean_option_" ++ name, fields)

private def recordOption (shape : String × List String) : M Unit := do
  let (name, fields) := shape
  unless (← get).optionDecls.any (·.1 == name) do
    let decls := fields.zipIdx.map fun (ct, i) => s!"{ct} value{i};"
    let decl := "typedef struct { int present; " ++ String.intercalate " " decls ++ " } " ++ name ++ ";\n"
    modify fun st => { st with optionDecls := (name, decl) :: st.optionDecls }

private partial def cTypeWithOut? (t : Expr) : MetaM (Option (String × Option OutKind)) := do
  let (_, t) := unwrapLinkage t
  if let some r := cTypeHead? t then return some r
  let t ← whnfR t
  if let some r := cTypeHead? t then return some r
  if let some shape ← taggedOption? t then return some (shape.1, none)
  if let some ref := optPtrRefName? t then return some ((optPtrCType? ref).getD "void *", none)
  match t.getAppFn.constName? with
  | some ``Array =>
    if t.getAppArgs.size == 1 then if let some (et, _) ← cTypeWithOut? t.getAppArgs[0]! then return some (s!"const {et} *", none)
    return none
  | some ``C.Ptr => return some ((optPtrCType? (t.getAppArgs.back!.getAppFn.constName?.getD .anonymous)).getD "void *", none)
  | some sn => return if isLocalStruct (← getEnv) sn then some (cStructName sn, none) else none
  | _ => return none
private def cType? (t : Expr) : MetaM (Option String) := do return (← cTypeWithOut? t).map fun (ct, ok) => stripOutType ct ok
private def isArrTy (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  if ty.isConstOf ``C.ConstWTable then return false
  return ty.getAppFn.constName? == some ``Array
private def stackTypes : List (Name × String × String) :=
  [(``C.StackStream, "z_stream", "z_streamp"), (``C.StackScalar64, "unsigned long", "unsigned long *"),
   (``C.StackScalar32, "unsigned", "unsigned *"), (``C.StackByte, "unsigned char", "unsigned char *")]
private def isStackTy (t : Expr) (nm : Name) : Bool := t.getAppFn.isConstOf nm || (t.isAppOfArity ``C.M 1 && t.getAppArgs[0]!.getAppFn.isConstOf nm)
private partial def flattenType (t : Expr) (hint : Name) : MetaM (List (Name × String)) := do
  if t.isConstOf ``Unit then return []
  if let some (ct, ok) := cTypeHead? t then return [(hint, stripOutType ct ok)]
  let t ← whnfR t
  if t.isAppOfArity ``Array 1 then return []
  if t.isAppOfArity ``Prod 2 then return (← flattenType t.getAppArgs[0]! hint) ++ (← flattenType t.getAppArgs[1]! hint)
  if let some sn := t.getAppFn.constName? then if isLocalStruct (← getEnv) sn then
    let mut out : List (Name × String) := []; let env ← getEnv
    for f in getStructureFields env sn do if let some info := env.find? (sn ++ f) then
      out := out ++ (← forallTelescope info.type fun _ b => if b.getAppFn.constName? == some ``Array then pure [] else flattenType b f)
    if !out.isEmpty then return out
  return [(hint, (← cType? t).getD "unsigned long")]
private def analyzeFn? (name : Name) (type value : Expr) (line : Nat := 0) : MetaM (Option FnMeta) :=
  forallTelescope type fun xs bodyTy => do
    let (order?, bodyTy') := unwrapOrder bodyTy
    let (some (link, false, false, false), ret1) := unwrapLinkage bodyTy' | return none
    let mut v := value; let mut params : List (String × String × Option OutKind) := []; let mut idx := 0
    for x in xs do
      let decl ← x.fvarId!.getDecl; let vn := match v with | .lam vn' _ _ _ => vn' | _ => decl.userName
      let p0 := if !vn.isAnonymous && !vn.hasMacroScopes then cIdent vn else if !decl.userName.isAnonymous && !decl.userName.hasMacroScopes then cIdent decl.userName else s!"p{idx}"
      let some (ct, ok?) ← cTypeWithOut? decl.type | return none
      params := params ++ [(if params.any (·.1 == p0) then s!"{p0}_{idx}" else p0, ct, ok?)]
      v := match v with | .lam _ _ vb _ => vb | _ => v; idx := idx + 1
    if let some ellipsis := params.findIdx? (fun (_, ct, _) => ct == "...") then
      unless ellipsis > 0 && ellipsis + 1 == params.length do throwError m!"{name}: ellipsis must follow the last named parameter"
    let outCnt := params.countP (·.2.2.isSome); let cName := link.customCName?.getD (cIdent name)
    return some { leanName := name, cName, link, params, retCTy := (← cType? (if outCnt > 0 && ret1.isAppOfArity ``Prod 2 then ret1.getAppArgs[0]! else ret1)).getD "unsigned long", outCount := outCnt, order?, line }
private def emit (s : String) : M Unit := modify fun st => { st with lines := st.lines.push (String.ofList (List.replicate (st.indent * 4) ' ') ++ s) }
private def withBlock (header : String) (m : M α) : M α := do
  let savedMut := (← get).mutLocals; emit header; modify fun st => { st with indent := st.indent + 1 }
  let r ← m; modify fun st => { st with indent := st.indent - 1, mutLocals := savedMut }; emit "}"; return r
private partial def fresh (hint : Name) : M String := do
  let raw := cIdent hint
  let base := if raw.startsWith "__" || raw.isEmpty then "tmp" else raw
  let st ← get
  let mut index := st.nextSuffix[base]?.getD 0
  repeat
    let candidate := if index == 0 then base else s!"{base}_{index}"
    let name := Name.mkSimple candidate
    index := index + 1
    unless st.used.contains name do
      modify fun s => { s with used := s.used.insert name, nextSuffix := s.nextSuffix.insert base index }
      return candidate

private def emitTemporary (ct vn : String) (init? : Option String := none) : M Unit := do
  if (← get).scopedLocals then
    modify fun s => { s with temporaries := s.temporaries.push s!"    {ct} {vn};" }
    if let some rhs := init? then emit s!"{vn} = {rhs};"
  else
    let init := init?.map (fun rhs => s!" = {rhs}") |>.getD ""
    emit s!"{ct} {vn}{init};"

private def declMut (hint : Name) (ct : String) : M String := do
  let vn ← fresh hint
  emitTemporary ct vn
  modify fun s => { s with mutLocals := (vn, ct) :: s.mutLocals }
  return vn
private def allocVars (ty : Expr) (hint : Name) : M (List VarEntry) := do (← flattenType ty hint).mapM fun (nm, ct) => return (nm.toString, ← declMut nm ct, ct)
private def setVar (fv : FVarId) (vs : List VarEntry) (arrs : List (String × String) := []) : M Unit := modify fun s => { s with vars := s.vars.insert fv vs, arrVars := if arrs.isEmpty then s.arrVars else s.arrVars.insert fv arrs }
private def bindCont (cont : Expr) (f : FVarId → Expr → M α) : M α := lambdaBoundedTelescope cont 1 fun xs cb => f xs[0]!.fvarId! cb
private def withLetVar (nm : Name) (ty body : Expr) (vs : List VarEntry) (arrs : List (String × String) := []) (k : Expr → M α) : M α := withLocalDeclD nm ty fun fv => do setVar fv.fvarId! vs arrs; k (body.instantiate1 fv)
private partial def mentionsPosixOrRef (e : Expr) : Bool := match e with
  | .const n _ => (posixConst? n).isSome || n ∈ [``C.Ptr.ref, ``Zlib.GzFs.strLit, ``C.strLitRef, ``C.allocB, ``C.freeB]
  | .app f a => mentionsPosixOrRef f || mentionsPosixOrRef a | .letE _ _ v b _ => mentionsPosixOrRef v || mentionsPosixOrRef b
  | .lam _ _ b _ | .mdata _ b => mentionsPosixOrRef b | _ => false
/-- Keep symbolic platform constants in C, even inside an otherwise closed expression. -/
private partial def isIntegerConstant (e : Expr) : MetaM Bool := do
  let e := stripMeta e
  if let .lit (.natVal _) := e then return true
  if let .const n [] := e then
    if (posixConst? n).isSome then return false
    if let some v := ((← getEnv).find? n).bind (·.value?) then return ← isIntegerConstant v
    return false
  let some n := e.getAppFn.constName? | return false
  let a := e.getAppArgs
  if n == ``OfNat.ofNat && a.size == 3 then return (getRawNatValue? a[1]!).isSome
  if (n == ``Neg.neg || pureIntCasts.contains n) && !a.isEmpty then return ← isIntegerConstant a.back!
  if pureIntOps.contains n && a.size >= 2 then
    return (← isIntegerConstant a[a.size-2]!) && (← isIntegerConstant a.back!)
  return false

/-- Reduce at the expression's Lean type: unsigned subtraction wraps before a following
shift or cast. Converting operands to mathematical integers first loses that behavior. -/
private def evalPureInt? (e : Expr) : MetaM (Option Int) := do
  if let some v := getRawNatValue? e then return some v
  unless ← isIntegerConstant e do return none
  let ty := (← whnfR (← inferType e)).getAppFn.constName?
  let unsigned := [(``UInt8, ``UInt8.toNat), (``UInt16, ``UInt16.toNat),
                   (``UInt32, ``UInt32.toNat), (``UInt64, ``UInt64.toNat)]
  withTransparency .all do
    if let some cast := ty.bind (fun t => unsigned.lookup t) then
      return (getRawNatValue? (← whnf (mkApp (mkConst cast) e))).map Int.ofNat
    if ty == some ``Nat then return (getRawNatValue? (← whnf e)).map Int.ofNat
    let signed := [(``Int32, ``Int32.toInt), (``Int64, ``Int64.toInt)]
    let value ← if let some cast := ty.bind (fun t => signed.lookup t) then whnf (mkApp (mkConst cast) e)
                else if ty == some ``Int then whnf e else return none
    if value.isAppOfArity ``Int.ofNat 1 || value.isAppOfArity ``Int.negSucc 1 then
      let magnitude := getRawNatValue? (← whnf value.getAppArgs[0]!)
      return magnitude.map (if value.isAppOfArity ``Int.ofNat 1 then Int.ofNat else Int.negSucc)
    return none
private partial def evalPureBool? (e : Expr) : MetaM (Option Bool) := do
  let e := stripMeta e
  if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then return some (e.isConstOf ``Bool.true)
  let some n := e.getAppFn.constName? | return none
  let a := e.getAppArgs
  if (n == ``BEq.beq || n == ``Eq) && a.size >= 2 then if let (some l, some r) := (← evalPureInt? a[a.size-2]!, ← evalPureInt? a.back!) then return some (l == r)
  if (n == ``Bool.and || n == ``Bool.or) && a.size >= 2 then if let (some l, some r) := (← evalPureBool? a[a.size-2]!, ← evalPureBool? a.back!) then return some (if n == ``Bool.and then l && r else l || r)
  return none
private partial def evalPureString? (e : Expr) : MetaM (Option String) := do
  match stripMeta e with | .lit (.strVal s) => return some s | .const n [] => if let some v := ((← getEnv).find? n).bind (·.value?) then evalPureString? v else return none | _ => return none
private def evalScalar? (e : Expr) : M (Option String) := do
  if e.hasFVar || mentionsPosixOrRef e then return none
  if let some s := (← get).constCache.get? e then return some s
  let ty ← whnfR (← inferType e); let sMin (i : Int) (isMin : Bool) (minS sfx : String) := if isMin then minS else if i < 0 then s!"({i}{sfx})" else s!"{i}{sfx}"
  let res? ← match ty.getAppFn.constName? with
    | some ``String => Option.map ABI.cString <$> evalPureString? e
    | some ``Bool => Option.map (if · then "1" else "0") <$> evalPureBool? e
    | some tn => match ← evalPureInt? e with | none => pure none | some v => pure <| match tn with
        | ``UInt8 => some s!"{v.toNat % 256}" | ``UInt16 => some s!"{v.toNat % 65536}" | ``UInt32 => some s!"{v.toNat % (2^32)}U" | ``UInt64 => some s!"{v.toNat % (2^64)}UL"
        | ``Int32 => let i := Int32.ofInt v; some (sMin i.toInt (i == Int32.minValue) "(-2147483647 - 1)" "") | ``Int64 => let i := Int64.ofInt v; some (sMin i.toInt (i == Int64.minValue) "(-9223372036854775807L - 1L)" "L")
        | ``Nat => some s!"{v.toNat}" | _ => none
    | _ => pure none
  if let some r := res? then modify fun s => { s with constCache := s.constCache.insert e r }
  return res?
private def isUbTerm (e : Expr) : Bool := let e := stripMeta e; e.isAppOfArity ``C.ub 2 || e.isAppOfArity ``Zlib.GzFs.gub 2
private def treeCastType? : Name → Option String
  | ``Zlib.Trees.i2u => some "unsigned"
  | ``Zlib.Trees.u2i => some "int"
  | ``Zlib.Trees.i2ul => some "unsigned long"
  | ``Zlib.Trees.i2us => some "unsigned short"
  | _ => none
private def allocatorFieldType? (act : Expr) : Option String := do
  guard (act.isAppOfArity ``Bind.bind 6)
  let cont := act.getAppArgs[5]!
  let .lam _ _ body _ := cont | none
  let field := (stripMeta body).headBeta
  if field.isAppOf ``C.ZStream.zalloc then some "alloc_func"
  else if field.isAppOf ``C.ZStream.zfree then some "free_func"
  else none
private def inflateArrayField? : Name → Option String
  | `Zlib.Inflate.codesP => some "codes"
  | `Zlib.Inflate.lensP => some "lens"
  | `Zlib.Inflate.workP => some "work"
  | _ => none
private def shouldUnfoldHelper (n : Name) : MetaM Bool := do
  if n ∈ [`Zlib.Deflate.CompressFunc.call, `Zlib.Deflate.configuration_table, `Zlib.Deflate.config_at, `Zlib.Inflate.xwhile, `Zlib.Inflate.xwhileBrk, `Zlib.Inflate.xloopBrk, `Zlib.Inflate.xdoWhile,
      `Zlib.Inflate.LOAD, `Zlib.Inflate.RESTORE, `Zlib.Infback.backMatch, `Zlib.Infback.extendExtra, `Zlib.Infback.emitLiteral, `Zlib.Inflate.emitLiteral, `Zlib.Inflate.addExtra, `Zlib.Inflate.consumeCodeWidth, `Zlib.Inflate.countDictionaryInput, `Zlib.Inflate.storeHeaderWord, `Zlib.Inflate.updateHeader, `Zlib.Inflate.rejectsInput, `Zlib.Inflate.publishCounts, `Zlib.Inflate.invalidHeaderWord, `Zlib.Inflate.windowBitsFromHeader, `Zlib.Inflate.setWindowLimit, `Zlib.Inflate.resetHeaderCheck, `Zlib.Inflate.withMatchSource, `Zlib.Inflate.copyHeaderExtra, `Zlib.Inflate.accountCheckedOutput, `Zlib.Inflate.readHeaderString, `Zlib.Inflate.CRC2, `Zlib.Inflate.CRC4, `Zlib.Inflate.hcrcOn, `Zlib.Inflate.storeDictId, `Zlib.Inflate.startDataCheck, `Zlib.Inflate.repeatCodeLength, `Zlib.Inflate.appendCurrentCode, `Zlib.Infback.appendCurrentCode, `Zlib.Inflate.setPreviousLength, `Zlib.Infback.setPreviousLength, `Zlib.Inflate.setRepeatCount, `Zlib.Infback.setRepeatCount, `Zlib.Inflate.lookup1, `Zlib.Inflate.lookup2, `Zlib.Infback.lookup1, `Zlib.Infback.lookup2, `Zlib.Infback.runBackModesFrom, `Zlib.Inflate.startLengthTable, `Zlib.Inflate.storeOrderedLength, `Zlib.Infback.storeOrderedLength, `Zlib.Infback.copyStoredInput, `Zlib.Inflate.copyStoredInput, `Zlib.Infback.sharedCase, `Zlib.Infback.PULL, `Zlib.Infback.ROOM, `Zlib.Inflate.appendLength, `Zlib.Inflate.withLengthOrder, `Zlib.Inflate.BITS, `Zlib.Inflate.DROPBITS, `Zlib.Inflate.BYTEBITS, `Zlib.Inflate.copyMatchBytes, `Zlib.Inflate.absorbInputByte, `Zlib.Inflate.allocLocalB] || privateToUserName n == `Zlib.Infback.inDecoder then return false
  if (treeCastType? n).isSome || (inflateArrayField? n).isSome then return false
  if isRuntimeConst n || n == ``Zlib.Gzguts.memchrB || n == ``Zlib.Gzguts.loadNextPostInc then return false
  if n ∈ [`Zlib.Deflate.ZALLOC_words, `Zlib.Deflate.ZALLOC_bytes,
      `Zlib.Deflate.ishl, `Zlib.Deflate.ZFREE_words, `Zlib.Deflate.ZFREE_bytes, `Zlib.Deflate.ZFREE_state] then return false
  if n ∈ [`Zlib.Inflate.ZALLOCS, `Zlib.Inflate.ZFREES, `Zlib.Inflate.ZALLOCB, `Zlib.Inflate.ZFREEB] then return false
  if n ∈ [`Zlib.Trees.shlUs, `Zlib.Trees.shrUs] then return false
  if n ∈ [`Zlib.Trees.sid, `Zlib.Trees.getFc, `Zlib.Trees.getDl, `Zlib.Trees.setFc, `Zlib.Trees.setDl] then return false
  if n ∈ [``Zlib.Trees.heapPush, ``Zlib.Trees.heapSave, ``Zlib.Trees.heapReplaceRoot, ``Zlib.Trees.put_symbol_byte] then return false
  let env ← getEnv; if !isZlibModConst env n then return false
  return match env.find? n with | some d => d.hasValue && (unwrapLinkage d.type.getForallBody).1.isNone | none => false
private def localStructArgs? (e : Expr) : MetaM (Option (Name × List (Name × Expr))) := do
  let env ← getEnv
  let some n := (← inferType e).getAppFn.constName? | return none
  if isLocalStruct env n && !e.getAppArgs.isEmpty && e.getAppFn.constName?.any (·.getPrefix == n) then
    let flds := (getStructureFields env n).toList; return some (n, flds.zip (takeLast e.getAppArgs.toList flds.length))
  return none
private def pairVars (srcVars dstVars : List VarEntry) : List (VarEntry × VarEntry) :=
  if srcVars.length == dstVars.length then dstVars.zip srcVars
  else if dstVars.all (fun (fnm, _, _) => srcVars.any (·.1 == fnm)) then dstVars.filterMap fun d => (srcVars.find? (·.1 == d.1)).map (d, ·) else []
private def asBytePtrExpr (arg : Expr) (s : String) : M String := do
  if let .fvar fv := stripMeta arg then if let some [(_, _, ct)] := (← get).vars.get? fv then if !ct.isEmpty && !isBytePtrCType ct then return s!"((unsigned char *){s})"
  return s
private def lookupProj (inner : Expr) (fname : String) : M (Option String) := do
  if let .fvar fv := stripMeta inner then
    let st ← get
    if let some (ptrExpr, _) := st.structPtrs.get? fv then return some s!"{ptrExpr}->{fname}"
    if let some (_, vn, _) := (st.vars.get? fv).bind (·.find? (·.1 == fname)) then return some vn
    if let some aEntries := st.arrVars.get? fv then return (aEntries.find? (·.1 == fname)).map (·.2) |>.orElse fun _ => match aEntries with | [("", av)] => some av | _ => none
  return none
private partial def prodEntries? (e : Expr) : M (Option (List VarEntry)) := do
  let e := stripMeta e
  match e with
  | .fvar fv => return (← get).vars.get? fv
  | _ =>
    let slice (inner ty0 : Expr) (isFst : Bool) : M (Option (List VarEntry)) := do
      let some es ← prodEntries? inner | return none
      let k := (← flattenType ty0 `x).length; return some (if isFst then es.take k else es.drop k)
    match e with
    | .proj ``Prod idx inner => let ity ← whnfR (← inferType inner); if ity.isAppOfArity ``Prod 2 then slice inner ity.getAppArgs[0]! (idx == 0) else return none
    | _ => let fn := e.getAppFn; let a := e.getAppArgs; if (fn.isConstOf ``Prod.fst || fn.isConstOf ``Prod.snd) && a.size == 3 then slice a[2]! a[0]! (fn.isConstOf ``Prod.fst) else return none
private def asTypedPtrExpr (arg : Expr) (s wantCTy : String) : M String := do
  let st ← get; let isWant := match stripMeta arg with | .fvar fv => (match st.vars.get? fv with | some [(_, _, ct)] => ct == wantCTy | _ => false) | _ => false
  return if isWant then s else s!"(({wantCTy}){s})"
private def isNatLitVal (e : Expr) (k : Nat) : Bool := natLitOf? (stripMeta e) == some k
private def isDoWhileBrk (e : Expr) : Bool :=
  e.isAppOfArity ``C.cdoWhileBrk 4 || e.isAppOfArity ``Zlib.GzFs.gdoWhileBrk 4
private def memcpyLoadType? (e : Expr) : Option (String × Nat) :=
  if e.isAppOfArity ``C.memcpyLoad32 1 then some ("unsigned", 4)
  else if e.isAppOfArity ``C.memcpyLoad64 1 then some ("unsigned long", 8)
  else none
private def constructorProjection? (e : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let args := e.getAppArgs
  let some fn := e.getAppFn.constName? | return none
  let some info := env.getProjectionFnInfo? fn | return none
  unless info.ctorName ∈ [`Zlib.Infback.DecoderCtx.mk, `Zlib.Inflate.Ctx.mk, `Zlib.Inflate.IL.mk] && !args.isEmpty do return none
  let value ← whnf args[0]!
  unless value.isAppOf info.ctorName do return none
  return some (mkAppN value.getAppArgs[info.i]! (args.extract 1 args.size)).headBeta

private partial def unfoldStep (e : Expr) : MetaM Expr := do
  let e := stripMeta e
  if let some v ← constructorProjection? e then return ← unfoldStep v
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let a := e.getAppArgs; let arm (x : Expr) := if e.isAppOfArity ``dite 5 then x.beta #[mkConst ``Unit.unit] else x
    if isUbTerm a[3]! then return stripMeta (arm a[4]!) else if isUbTerm a[4]! then return stripMeta (arm a[3]!)
  if let some fn := e.getAppFn.constName? then if ← shouldUnfoldHelper fn then if let some e' ← Meta.unfoldDefinition? e then return ← unfoldStep e'.headBeta
  return e
mutual
private partial def lowerSnprintf (args : Array Expr) : M String := do
  let mut fmtArgs := [← lowerExpr args[0]!, ← lowerExpr args[1]!, ← lowerExpr args[2]!]; let mut cur := args[3]!
  while cur.isAppOfArity ``List.cons 3 do
    let hd := cur.getAppArgs[1]!
    if hd.isAppOfArity ``Zlib.GzFs.VaArg.str 1 then fmtArgs := fmtArgs ++ [s!"(const char *){← lowerExpr hd.getAppArgs[0]!}"]
    else if hd.isAppOfArity ``Zlib.GzFs.VaArg.int 1 then fmtArgs := fmtArgs ++ [← lowerExpr hd.getAppArgs[0]!]
    cur := cur.getAppArgs[2]!
  return s!"(void)snprintf({String.intercalate ", " fmtArgs})"
private partial def lowerBytePtr (arg : Expr) (force : Bool) : M String := do let s ← lowerExpr arg; if force then asBytePtrExpr arg s else pure s
private partial def lowerExpr (e : Expr) : M String := do
  let e := (stripMeta e).headBeta
  if e.isAppOfArity ``Option.some 2 || e.isAppOfArity ``Option.none 1 then
    if let some shape ← taggedOption? (← inferType e) then
      recordOption shape
      if e.isAppOf ``Option.none then return "(" ++ shape.1 ++ "){0}"
      let val := e.appArg!
      let values ← if let some entries ← prodEntries? val then pure (entries.map (·.2.1))
        else (← flattenExprsM val).mapM lowerExpr
      unless values.length == shape.2.length do throwError m!"optional payload width: {val}"
      return "(" ++ shape.1 ++ "){1, " ++ String.intercalate ", " values ++ "}"
  if e.isAppOf ``Option.isSome || e.isAppOf ``Option.isNone then
    if let some shape ← taggedOption? (← inferType e.appArg!) then
      recordOption shape
      let present := s!"({← lowerExpr e.appArg!}).present"
      return if e.isAppOf ``Option.isSome then present else s!"(!{present})"
  if let some v ← constructorProjection? e then return ← lowerExpr v
  if let .proj `Zlib.Inflate.IL idx base := e then
    let record ← whnf base
    if record.isAppOf `Zlib.Inflate.IL.mk then return ← lowerExpr record.getAppArgs[idx]!
  if e.isAppOfArity ``Inhabited.default 2 then
    let ty := e.getAppArgs[0]!
    if ty.isConstOf ``C.Code then
      let value ← withTransparency .all (whnf e)
      if value.isAppOf ``C.Code.mk then return ← lowerExpr value
    if [``UInt8, ``UInt16, ``UInt32, ``UInt64, ``Int32].any ty.isConstOf then
      if ← isDefEq e (← mkNumeral ty 0) then return "0"
  if e.isAppOfArity ``C.CtData.mk 2 then
    return "((ct_data){ .fc.freq = " ++ (← lowerExpr e.getAppArgs[0]!) ++ ", .dl.len = " ++ (← lowerExpr e.getAppArgs[1]!) ++ " })"
  if e.isAppOfArity ``C.CtData.fc 1 || e.isAppOfArity ``C.CtData.dl 1 then
    let field := if e.isAppOf ``C.CtData.fc then "fc.freq" else "dl.len"
    return "(" ++ (← lowerExpr e.appArg!) ++ ")." ++ field
  if e.isAppOf `Zlib.Inflate.IL.mk then
    let fields := getStructureFields (← getEnv) `Zlib.Inflate.IL
    let mut values := #[]
    for (field, value) in fields.zip e.getAppArgs do
      if field != `pointerLocals then
        values := values.push s!".{field} = {← lowerExpr value}"
    return "(" ++ cStructName `Zlib.Inflate.IL ++ "){ " ++ String.intercalate ", " values.toList ++ " }"
  match e with
  | .fvar fv =>
    let st ← get
    if st.varargs?.any (fun (args, _) => args == fv) then throwError "variadic arguments must be accessed through va_start"
    if let some s := st.strLitVars.get? fv then return s else if let some [(_, v, _)] := st.vars.get? fv then return v else if let some ((_, av) :: _) := st.arrVars.get? fv then return av else return "__fvar"
  | .lit (.natVal k) => return toString k | .lit (.strVal s) => return ABI.cString s
  | .proj sn idx inner =>
    if sn == ``C.CtData then
      let fields := #["fc.freq", "dl.len"]
      let some f := fields[idx]? | throwError m!"invalid ct_data member {idx}"
      return s!"({← lowerExpr inner}).{f}"
    if sn == ``Prod then
      if ← isArrTy e then if let (_, av) :: _ ← collectArrExprs e then return av
      if let some [(_, vn, _)] ← prodEntries? e then return vn
    let some fname := (getStructureFields (← getEnv) sn)[idx]? | throwError m!"bad proj {idx} on {sn}"
    if let some s ← lookupProj inner fname.toString then return s
    let s ← lowerExpr inner; return if !hasSubstr s " " then s!"{s}.{fname}" else s!"({s}).{fname}"
  | .letE nm ty val body _ => let v ← lowerExpr val; return ← withLetVar nm ty body [("", v, "")] (k := lowerExpr)
  | _ => pure ()
  if let some mApp ← Meta.matchMatcherApp? e then
    if mApp.discrs.size == 1 && mApp.alts.size == 2 then
      let discr := stripMeta mApp.discrs[0]!
      if discr.isAppOfArity ``GetElem?.getElem? 7 then if ← lambdaTelescope mApp.alts[1]! fun _ b => pure (isUbTerm b) then
        let elemExpr := s!"{← lowerExpr discr.getAppArgs[5]!}[{← lowerExpr discr.getAppArgs[6]!}]"
        return ← lambdaTelescope mApp.alts[0]! fun altFvs altBody => do
          if altFvs.size == 1 then
            let ct := (← cType? (← inferType altFvs[0]!)).getD ""
            setVar altFvs[0]!.fvarId! [("", elemExpr, ct)]
          lowerExpr altBody
  let fn := e.getAppFn; let a := e.getAppArgs
  if fn.isFVar then
    let some [(_, target, sig)] := (← get).vars.get? fn.fvarId!
      | throwError m!"indirect call has no C callback binding: {e}"
    unless (sig == "in_func" && a.size == 2) || (sig == "out_func" && a.size == 3) do
      throwError m!"indirect call requires a C callback signature and argument mapping: {e}"
    return s!"{target}({String.intercalate ", " (← a.toList.mapM lowerExpr)})"
  let some n := fn.constName? | throwError m!"unsupported expr {e}"
  if n == ``C.literalFirstByte && a.size == 1 then
    let some literal ← evalPureString? a[0]! | throwError m!"expected a C string literal: {a[0]!}"
    return s!"((unsigned char){ABI.cString literal}[0])"
  if n == ``C.BPtrCell.read then return s!"(*({← lowerExpr a[0]!}))"
  if n == ``C.BPtrCell.write then return s!"(*({← lowerExpr a[0]!}) = {← lowerExpr a[1]!})"
  if n == `Zlib.Deflate.config_at && a.size == 1 then
    return s!"configuration_table[{← lowerExpr a[0]!}]"
  if n == `Zlib.Deflate.CompressFunc.call && a.size == 3 then
    return s!"({← lowerExpr a[0]!})({← lowerExpr a[1]!}, {← lowerExpr a[2]!})"
  if let some field := inflateArrayField? n then
    let orig := stripMeta a[0]!
    let base := (← constructorProjection? orig).getD orig
    unless base.isFVar do throwError m!"array member address needs a bound inflate state: {base}"
    let ptr ← lowerExpr base
    if (← get).selectedRecord == base.fvarId? then return s!"({ptr})->{field}"
    return s!"(({ptr}) ? ({ptr})->{field} : 0)"
  if a.isEmpty then if let some p := posixConst? n then return p
  if n == ``OfNat.ofNat then
    -- A long literal also sets the width of shifts before assignment.
    if (← whnfR a[0]!).isConstOf ``Int64 then
      if let some value ← evalScalar? e then return value
    let .lit (.natVal k) := a[1]! | throwError "non-lit OfNat"
    let ty ← cType? a[0]!; return s!"{k}" ++ if ty == some "unsigned long" then "UL" else if ty == some "unsigned" then "U" else ""
  if n == ``Bool.true then return "1" else if n == ``Bool.false then return "0"
  if let some lit ← evalScalar? e then return lit
  if n == ``Zlib.Trees.bl_order then return "bl_order"
  if let some ty := treeCastType? n then return s!"(({ty})({← lowerExpr a[0]!}))"
  if n == `Zlib.Trees.getFc || n == `Zlib.Trees.getDl then
    let field := if n == `Zlib.Trees.getFc then "fc.freq" else "dl.len"
    return s!"{← lowerExpr a[0]!}[{← lowerExpr a[1]!}].{field}"
  if n.getPrefix == ``C.StaticTreeDescRef && (cIdent n).startsWith "st_" then
    return "&" ++ ((cIdent n).drop 3).toString
  if n.getPrefix == ``C.TreeDescRef && (cIdent n).startsWith "in_dstate_" then
    let some state := a[0]!.fvarId?.bind (← get).deflateIds.get? | throwError "tree descriptor needs its containing state"
    return s!"(&{state}->{((cIdent n).drop 10).toString})"
  if n == `Zlib.Trees.shlUs || n == `Zlib.Trees.shrUs then
    let op := if n == `Zlib.Trees.shlUs then "<<" else ">>"
    return s!"(((unsigned short)({← lowerExpr a[0]!})) {op} {← lowerExpr a[1]!})"
  if n == ``C.FnPtr.fn then
    let .lit (.strVal symbol) := a[0]! | throwError "function address requires a known C symbol"
    let target := Name.str `Zlib.Zutil symbol
    unless target ∈ [`Zlib.Zutil.zcalloc, `Zlib.Zutil.zcfree] && (← getEnv).contains target do
      throwError m!"unsupported allocator function address {symbol}"
    modify fun st => { st with functionAddresses := st.functionAddresses.push target }
    return symbol
  if n == `Zlib.Deflate.ishl && a.size == 2 then
    return s!"({← lowerExpr a[0]!} << {← lowerExpr a[1]!})"
  if n ∈ [`Zlib.Deflate.ZALLOC_words, `Zlib.Deflate.ZALLOC_bytes] then
    let p ← lowerExpr a[0]!
    let params ← if n == `Zlib.Deflate.ZALLOC_words then pure s!"{← lowerExpr a[1]!}, sizeof(unsigned short)"
      else pure s!"{← lowerExpr a[1]!}, {← lowerExpr a[2]!}"
    return s!"{p}->zalloc({p}->opaque, {params})"
  if n == `Zlib.Inflate.ZALLOCS || n == `Zlib.Inflate.ZALLOCB then
    let stream ← lowerExpr a[0]!
    let args ← if n == `Zlib.Inflate.ZALLOCS then pure "1, sizeof(struct inflate_state)"
      else pure s!"{← lowerExpr a[1]!}, {← lowerExpr a[2]!}"
    return s!"{stream}->zalloc({stream}->opaque, {args})"
  if n ∈ [`Zlib.Inflate.ZFREES, `Zlib.Inflate.ZFREEB, `Zlib.Deflate.ZFREE_words,
      `Zlib.Deflate.ZFREE_bytes, `Zlib.Deflate.ZFREE_state] then
    let stream ← lowerExpr a[0]!
    return s!"{stream}->zfree({stream}->opaque, {← lowerExpr a[1]!})"
  if n == ``Zlib.Gzguts.loadNextPostInc then return s!"(*({← lowerExpr a[0]!}->x.next)++)"
  if n == ``Zlib.Gzguts.memchrB then return s!"memchr({← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!})"
  if n == ``C.UInt32Cell.read then return s!"(*{← lowerExpr a[0]!})"
  if n == ``C.UInt32Cell.bytes then return s!"((unsigned *){← lowerExpr a[0]!})"
  if n == ``C.UInt32Cell.inflateHave then return s!"(&({← lowerExpr a[0]!})->have)"
  if n == ``C.UInt32Cell.gzHave then return s!"(&({← lowerExpr a[0]!})->x.have)"
  if n == ``Zlib.GzFs.vsnprintf then return s!"vsnprintf((char *){← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!}, {← lowerExpr a[3]!})"
  if n == ``Zlib.GzFs.fsWriteFrom then return s!"write({← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!})"
  if n == ``Zlib.GzFs.fsReadInto then return s!"read({← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!})"
  if n == ``C.firstByte32 && a.size == 1 then
    let word ← lowerExpr a[0]!
    if (← get).mutLocals.any (fun (v, _) => v == word) then
      return s!"(*(const unsigned char *)&{word})"
    return s!"((unsigned char)({word}))"
  if let some s := zeroOps.lookup n then return s
  if n == ``List.toArray && a.back!.isAppOfArity ``List.nil 1 then return "0"
  if n == ``Array.mk && a.back!.isAppOfArity ``List.nil 1 then return "0"
  if n == ``Option.some && a.size == 2 then return ← lowerExpr a[1]!
  if let some (p, s) := unaryExprOps.lookup n then if a.size >= 1 then return s!"{p}{← lowerExpr a.back!}{s}"
  if n == ``Option.map && a.size >= 4 then
    let src := stripMeta a[3]!; let srcS ← lowerExpr src
    match optPtrRefName? (← whnfR (← inferType src)), optPtrRefName? (← whnfR (← inferType e)) with
    | _, some ``C.GzStateRef => return s!"(gz_statep){srcS}" | _, some ``C.GzFileRef => return s!"(gzFile){srcS}" | some ``C.GzStateRef, some ``C.ZStreamRef => return s!"(&{srcS}->strm)" | _, _ => pure ()
  if n == ``C.stackAddr && a.size >= 5 then
    let .lit (.strVal fld) := a[3]! | throwError "stackAddr bad field"
    let b ← lowerExpr a[2]!; return s!"(unsigned char *)(&{if b.startsWith "(&" && b.endsWith ")" then (b.drop 2).dropEnd 1 |>.toString else if b.startsWith "&" then (b.drop 1).toString else b}.{fld})"
  if passThroughFns.contains n then return ← lowerExpr a.back!
  if let some ct := castMap.lookup n then return s!"(({ct})({← lowerExpr a.back!}))"
  if n == ``Bind.bind && a.size >= 6 then
    let act ← unfoldStep a[4]!
    if act.isAppOfArity ``Zlib.Trees.sid 1 then
      let state ← lowerExpr act.getAppArgs[0]!
      return ← bindCont a[5]! fun id body => do
        modify fun st => { st with deflateIds := st.deflateIds.insert id state }
        lowerExpr body
    if let some (false, sn) := act.getAppFn.constName?.bind structAct? then if act.getAppNumArgs == 1 then
      let p ← lowerExpr act.getAppArgs[0]!
      return ← bindCont a[5]! fun xId cb => do modify fun s => { s with structPtrs := s.structPtrs.insert xId (p, sn) }; lowerExpr cb
    let v ← lowerExpr act
    return ← bindCont a[5]! fun xId cb => do setVar xId [("", v, "")]; lowerExpr cb
  if n == ``C.Ptr.ref && a.size == 3 then
    let ref := a[1]!
    if let some constructor := ref.getAppFn.constName? then
      let name := cIdent constructor
      if name.startsWith "dstate_" && ref.getAppNumArgs == 1 then
        let some state := ref.getAppArgs[0]!.fvarId?.bind (← get).deflateIds.get? | throwError "array member needs its containing state"
        let member := s!"{state}->{(name.drop 7).toString}"
        if isNatLitVal a[2]! 0 then return member
        return s!"({member} + {← lowerExpr a[2]!})"
    if let some s := (a[1]!.getAppFn.constName?).bind fun cn => match cn with | .str _ x => if x.startsWith "st_" then some (x.drop 3).toString else none | _ => none then
      if let some (_, tbl) := (← get).staticsMap.find? (·.1 == s) then modify fun st => if st.usedStatics.any (·.1 == s) then st else { st with usedStatics := st.usedStatics.push (s, tbl) }
      let name := if s == "length_code" || s == "dist_code" then "_" ++ s else s
      if isNatLitVal a[2]! 0 then return name
      return s!"({name} + {← lowerExpr a[2]!})"
  if n == ``C.Ptr.add && a.size >= 3 then
    let ptrS ← lowerBytePtr a[a.size-2]! (a[0]!.isConstOf ``C.BRef)
    let off := stripMeta a.back!
    if off.isAppOfArity ``Neg.neg 3 then return s!"({ptrS} - {← lowerExpr off.getAppArgs.back!})"
    return s!"({ptrS} + {← lowerExpr a.back!})"
  if n == ``C.Ptr.diff && a.size >= 2 then return s!"({← lowerExpr a[a.size-2]!} - {← lowerExpr a.back!})"
  if n == ``C.Ptr.index || n == ``C.index8 then return s!"{← lowerBytePtr a[a.size-2]! (n == ``C.index8 || a[0]!.isConstOf ``C.BRef)}[{← lowerExpr a.back!}]"
  if n == ``Array.size then
    let array ← lowerExpr a.back!
    unless (← get).stackArrays.contains array do throwError m!"array size needs a complete local array: {e} ({array})"
    return s!"(sizeof({array}) / sizeof({array}[0]))"
  if n == ``GetElem?.getElem! && a.size == 8 then return s!"{← lowerExpr a[6]!}[{← lowerExpr a[7]!}]"
  if n == ``GetElem.getElem && a.size >= 7 then return s!"{← lowerExpr a[5]!}[{← lowerExpr a[6]!}]"
  if n == ``C.Code.mk && a.size == 3 then return s!"((code)\{{← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!}})"
  if n == ``ite && a.size == 5 then
    if isUbTerm a[3]! then return ← lowerExpr a[4]! else if isUbTerm a[4]! then return ← lowerExpr a[3]! else return s!"({← lowerExpr a[1]!} ? {← lowerExpr a[3]!} : {← lowerExpr a[4]!})"
  if n == ``dite && a.size == 5 then
    if isUbTerm a[3]! then return ← lowerExpr (a[4]!.beta #[mkConst ``Unit.unit]) else if isUbTerm a[4]! then return ← lowerExpr (a[3]!.beta #[mkConst ``Unit.unit])
  if let some op := binOps.lookup n then return s!"({← lowerExpr a[a.size-2]!} {op} {← lowerExpr a.back!})"
  if (n == ``Prod.fst || n == ``Prod.snd) && a.size == 3 then
    if ← isArrTy e then if let (_, av) :: _ ← collectArrExprs e then return av
    if let some [(_, vn, _)] ← prodEntries? e then return vn
  if (← getEnv).isProjectionFn n && a.size == 1 then
    let fname := cIdent n; if let some s ← lookupProj a[0]! fname then return s
    let s ← lowerExpr a[0]!; return if !hasSubstr s " " then s!"{s}.{fname}" else s!"({s}).{fname}"
  if a.isEmpty then
    if let some d := (← getEnv).find? n then if let (some (_, isStr, isArr, _), _) := unwrapLinkage d.type.getForallBody then if isStr || isArr then return cIdent n
    if (← whnfR (← inferType e)).isAppOfArity ``Array 1 then
      if let some (snm, _) := (← get).staticsMap.find? (·.2 == n) then return snm
      if !((← get).localTbls.contains n) then modify fun st => { st with localTbls := st.localTbls.push n }
      return cIdent n
  if ← shouldUnfoldHelper n then if let some e' ← Meta.unfoldDefinition? e then return ← lowerExpr e'.headBeta
  if n == ``Zlib.GzFs.BLOCKED then let ev ← lowerExpr a.back!; return s!"({ev} == EAGAIN || {ev} == EWOULDBLOCK)"
  if (n == ``C.freeB || n == ``C.freeGzState || n == ``C.freeZStream) && a.size >= 1 then
    let st ← get; let arg := stripMeta a.back!; if (match arg with | .fvar fv => st.stackFVars.contains fv | _ => false) then return "0" else return s!"free({← lowerExpr arg})"
  if let some want := ptrWidthType? n then if a.size >= 1 then return s!"(*{← asTypedPtrExpr a[0]! (← lowerExpr a[0]!) want})"
  if n == ``Zlib.GzFs.fsOpen && a.size >= 2 then return s!"open((const char *){← lowerExpr a[0]!}, {← lowerExpr a[1]!}, 0666)"
  if n == ``Zlib.GzFs.fsLseek && a.size >= 3 then return s!"LSEEK({← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!})"
  if n == ``Zlib.GzFs.snprintf && a.size >= 4 then return ← lowerSnprintf a
  if let some d := (← getEnv).find? n then if let (some (link, false, false, false), _) := unwrapLinkage d.type.getForallBody then
    return s!"{link.customCName?.getD (cIdent n)}({String.intercalate ", " (← a.toList.mapM lowerExpr)})"
  throwError m!"lowerExpr unsupported: {e}"
private partial def flattenExprsM (e : Expr) (keepUnit : Bool := false) : MetaM (List Expr) := do
  if !keepUnit && (← inferType e).isConstOf ``Unit then return []
  let e := stripMeta e
  if e.isAppOfArity ``Prod.mk 4 then return (← flattenExprsM e.getAppArgs[2]! keepUnit) ++ (← flattenExprsM e.getAppArgs[3]! keepUnit)
  if let some (n, fldArgs) ← localStructArgs? e then
    let env ← getEnv; let mut out : List Expr := []
    for (f, arg) in fldArgs do if let some info := env.find? (n ++ f) then if info.type.getForallBody.getAppFn.constName? != some ``Array then out := out ++ (← flattenExprsM arg keepUnit)
    return out
  return [e]
private partial def countArrTys (t : Expr) : MetaM Nat := do
  if t.isConstOf ``C.ConstWTable then return 0
  let t ← whnfR t
  if t.isAppOfArity ``Array 1 then return 1
  if t.isAppOfArity ``Prod 2 then return (← countArrTys t.getAppArgs[0]!) + (← countArrTys t.getAppArgs[1]!)
  if let some sn := t.getAppFn.constName? then
    if isLocalStruct (← getEnv) sn then
      let env ← getEnv; let mut n := 0
      for f in getStructureFields env sn do
        if let some info := env.find? (sn ++ f) then n := n + (← forallTelescope info.type fun _ b => countArrTys b)
      return n
  return 0
private partial def collectArrExprs (e : Expr) : M (List (String × String)) := do
  let e := stripMeta e
  if let .fvar fv := e then
    let st ← get
    if let some a := st.arrVars.get? fv then if !a.isEmpty then return a
    return if (st.vars.get? fv).any (·.length == 1) && (← isArrTy e) then [("", st.vars.get! fv |>.head!.2.1)] else []
  if e.isAppOfArity ``Prod.mk 4 then return (← collectArrExprs e.getAppArgs[2]!) ++ (← collectArrExprs e.getAppArgs[3]!)
  if let .proj ``Prod idx inner := e then
    let ity ← whnfR (← inferType inner)
    if ity.isAppOfArity ``Prod 2 then
      let k ← countArrTys ity.getAppArgs[0]!; let innerA ← collectArrExprs inner
      return if idx == 0 then innerA.take k else innerA.drop k
    return []
  if (e.getAppFn.isConstOf ``Prod.fst || e.getAppFn.isConstOf ``Prod.snd) && e.getAppArgs.size == 3 then
    let a := e.getAppArgs; let k ← countArrTys a[0]!; let innerA ← collectArrExprs a[2]!
    return if e.getAppFn.isConstOf ``Prod.fst then innerA.take k else innerA.drop k
  if let .proj sn idx inner := e then if ← isArrTy e then if let some fn := (getStructureFields (← getEnv) sn)[idx]? then if let some av ← lookupProj inner fn.toString then return [("", av)]
  if let some n := e.getAppFn.constName? then if (← getEnv).isProjectionFn n && e.getAppArgs.size == 1 then if ← isArrTy e then if let some av ← lookupProj e.getAppArgs[0]! (cIdent n) then return [("", av)]
  if ← isArrTy e then return [("", ← lowerExpr e)]
  if let some (_, fldArgs) ← localStructArgs? e then
    return ← fldArgs.foldlM (fun out (f, arg) => do if ← isArrTy arg then return out ++ [(f.toString, ((← collectArrExprs arg).head?.map (·.2)).getD (← lowerExpr arg))] else return out ++ (← collectArrExprs arg)) []
  return []
end
private partial def lowerValueToVars (e : Expr) (vars : List VarEntry) : M Unit := do
  let e := stripMeta e
  if e.isAppOfArity ``ite 5 && e.getAppArgs[0]!.isAppOfArity ``Prod 2 then
    let a := e.getAppArgs
    withBlock s!"if ({← lowerExpr a[1]!}) \{" (lowerValueToVars a[3]! vars)
    withBlock "else {" (lowerValueToVars a[4]! vars)
    return
  if let .letE nm ty val body _ := e then
    let st ← get
    let (es, aes) ← match stripMeta val with | .fvar fv => pure ((st.vars.get? fv).getD [], (st.arrVars.get? fv).getD []) | _ => pure ([], ← collectArrExprs val)
    let es ← if es.isEmpty then do pure [("", ← lowerExpr val, "")] else pure es
    withLetVar nm ty body es aes (k := (lowerValueToVars · vars)); return
  let curArrs ← collectArrExprs e; if !curArrs.isEmpty then modify fun st => { st with lastArrs := curArrs }
  if e.isAppOfArity ``Prod.mk 4 then
    let pa := e.getAppArgs; let k := (← flattenType (← inferType pa[2]!) `x).length
    if k <= vars.length then lowerValueToVars pa[2]! (vars.take k); lowerValueToVars pa[3]! (vars.drop k); return
  if let some srcVars ← prodEntries? e then
    let pairs := pairVars srcVars vars
    if srcVars.length == vars.length || !pairs.isEmpty then (for ((_, d, _), (_, s, _)) in pairs do if d != s && s != "__default" then emit s!"{d} = {s};"); return
  let curBrk := (← get).breakVar?; let isBreakLit (s : String) := let c := if s.endsWith "U" then (s.toSlice.dropEnd 1).toString else s; !c.isEmpty && c.all Char.isDigit && c != "0"
  let rec assignOne (d dt : String) (ve : Expr) : M Bool := do
    let ve := stripMeta ve
    if let .letE nm ty val body _ := ve then let v ← lowerExpr val; return ← withLetVar nm ty body [("", v, "")] (k := assignOne d dt)
    if ve.getAppFn.isConstOf ``Inhabited.default then return false
    if dt == "code" && ve.isAppOfArity ``C.Code.mk 3 then
      let ca := ve.getAppArgs; for (f, arg) in [("op", ca[0]!), ("bits", ca[1]!), ("val", ca[2]!)] do let v ← lowerExpr arg; if v != s!"{d}.{f}" then emit s!"{d}.{f} = {v};"
      return false
    let v ← lowerExpr ve; if v != d then emit s!"{d} = {v};"
    return (curBrk == some d && isBreakLit v)
  let filtered ← (← flattenExprsM e).filterM (fun vExpr => do return !(← isArrTy vExpr))
  if filtered.length == vars.length then
    let mut didBreak := false; for ((_, d, dt), vExpr) in vars.zip filtered do if ← assignOne d dt vExpr then didBreak := true
    if didBreak then emit "break;"
    return
  throwError m!"cannot assign {e} to {vars}"
private structure FieldStore where
  lhs : String
  rhs : String
  op : String
  stable : Bool

private partial def readsImmutableField (env : Environment) (immutable : FVarIdSet) (e : Expr) : Bool :=
  match stripMeta e with
  | .proj _ _ (.fvar id) => immutable.contains id
  | .app (.const name _) a =>
    if (castMap.lookup name).isSome || natIntCasts.contains name then readsImmutableField env immutable a
    else (env.getProjectionFnInfo? name).isSome && a.fvarId?.any immutable.contains
  | _ => false

/-- Preserve the ordering of successive pure record updates. Forward a projection
    of an intermediate constructor to its actual operand, including when a later
    field uses a value set by an earlier update. All operands still describe the
    value of the single final store. -/
private partial def recordOperands (env : Environment) (sn : Name) (fields : List Name) (record : Expr) :
    MetaM (List (Name × Expr)) := do
  let ctor := sn ++ `mk
  let values (e : Expr) := takeLast e.getAppArgs.toList fields.length
  let reorder (order : List Nat) (before after : List Expr) :=
    let (kept, changed) := order.partition fun i => before[i]? == after[i]?
    kept ++ changed
  let rec visit (e : Expr) (previous : Option (List Expr)) (order : List Nat) :
      MetaM (List (Name × Expr)) := do
    let e := (stripMeta e).headBeta
    if let .letE _ _ value body _ := e then
      let body := body.instantiate1 value
      unless value.isAppOf ctor do return ← visit body previous order
      let args := values value
      let body := body.replace fun proj =>
        match proj with
        | .proj name i src => if name == sn && src == value then args[i]? else none
        | .app f src => do
          guard (src == value)
          let info ← env.getProjectionFnInfo? (← f.constName?)
          guard (info.ctorName == ctor)
          args[info.i]?
        | _ => none
      return ← visit body (some args) (previous.map (reorder order · args) |>.getD order)
    unless e.isAppOf ctor do throwError m!"expected a {sn} constructor for a structure store, got {e}"
    let args := values e
    let final := previous.map (reorder order · args) |>.getD order
    return final.map fun i => (fields[i]!, args[i]!)
  visit record none (List.range fields.length)

private partial def structStores (ptrExpr sub : String) (sn : Name) (newRec : Expr) (oldFv? : Option FVarId := none) : M (Array FieldStore) := do
  let env ← getEnv; let st ← get; let fields := (getStructureFields env sn).toList; let pfx := if sub.isEmpty then s!"{ptrExpr}->" else s!"{ptrExpr}->{sub}."
  let sameFld (fv' : FVarId) := match oldFv? with
    | some fv => fv' == fv
    | none => (st.structPtrs.get? fv').any (·.1 == ptrExpr) ||
        (st.vars.get? fv').any (fun | [(_, v, _)] => v == s!"(*{ptrExpr})" | _ => false)
  let isField (fname : Name) (arg : Expr) := match arg with
    | .app f (.fvar fv) => f.isConstOf (sn ++ fname) && sameFld fv
    | .proj recName idx (.fvar fv) => recName == sn && fields[idx]? == some fname && sameFld fv
    | _ => false
  let mut stores := #[]
  let operands ← recordOperands env sn fields newRec
  -- A direct read of an untouched sibling field still yields the snapshot value
  -- after earlier stores. Reads through another pointer can alias a changed field.
  let untouched := if sub.isEmpty then operands.filterMap (fun (f, a) =>
    if isField f a then some f else none) else []
  for (fname, arg) in operands do
    if !isField fname arg then
      let rec recordValue (arg : Expr) : Expr :=
        match (stripMeta arg).headBeta with
        | .letE _ _ value body _ => recordValue (body.instantiate1 value)
        | value => value
      let argS := recordValue arg
      if let some innerSn := (← inferType argS).getAppFn.constName? then
        if (isLocalStruct env innerSn || (isABIStruct innerSn && (cTypeHead? (mkConst innerSn)).isNone)) && argS.getAppFn.constName?.any (·.getPrefix == innerSn) then
          let nested := if sub.isEmpty then fname.toString else s!"{sub}.{fname}"
          stores := stores ++ (← structStores ptrExpr nested innerSn argS oldFv?)
          continue
      let lhs := s!"{pfx}{fname}"
      -- The field store performs the final unsigned-short conversion in x |= bits.
      if argS.isAppOfArity ``UInt16.ofNat 1 then
        let bits := argS.getAppArgs[0]!
        if bits.isAppOfArity ``HOr.hOr 6 then
          let left := bits.getAppArgs[4]!
          if left.isAppOfArity ``UInt16.toNat 1 && isField fname left.getAppArgs[0]! then
            let mask := bits.getAppArgs[5]!
            stores := stores.push ⟨lhs, ← lowerExpr mask, "|=", ← isIntegerConstant mask⟩
            continue
      let rhs ← lowerExpr argS
      if rhs != lhs then
        -- Taking a member array's address reads the pointer, but none of the
        -- fields changed by these stores. Require the same bound C pointer.
        let plainPointer := !ptrExpr.isEmpty && ptrExpr.toList.all (fun c => c.isAlphanum || c == '_')
        let ownArray ← if argS.getAppFn.constName?.bind inflateArrayField? |>.isSome then
            pure (plainPointer && argS.getAppNumArgs == 1 && (← lowerExpr argS.appArg!) == ptrExpr)
          else if plainPointer && argS.isAppOfArity ``C.Ptr.ref 3 && isNatLitVal argS.getAppArgs[2]! 0 then
            let ref := argS.getAppArgs[1]!
            pure (ref.getAppFn.constName?.any (fun name => (cIdent name).startsWith "dstate_") &&
              ref.getAppNumArgs == 1 && ref.appArg!.fvarId?.bind st.deflateIds.get? == some ptrExpr)
          else pure false
        let stable := ownArray || untouched.any (fun f => isField f argS) ||
          readsImmutableField env st.immutableRecords argS || (← isIntegerConstant argS)
        stores := stores.push ⟨lhs, rhs, "=", stable⟩
  return stores

/-- A Lean record constructor reads every replacement field before the record is
    stored. In particular, a later operand can read a field through an alias. -/
private def emitStructDiff (ptrExpr sub : String) (sn : Name) (newRec : Expr) (oldFv? : Option FVarId := none) : M Unit := do
  let stores ← structStores ptrExpr sub sn newRec oldFv?
  let mut assignments := #[]
  for store in stores do
    let mut rhs := store.rhs
    if !assignments.isEmpty && !store.stable && rhs != "0" then
      let saved ← fresh `field_value
      emit s!"__typeof__({store.lhs}) {saved} = {rhs};"
      rhs := saved
    assignments := assignments.push s!"{store.lhs} {store.op} {rhs};"
  for assignment in assignments do emit assignment

private def handleMatch (e : Expr) (k : Expr → M α) (fallback : M α) : M α := do
  if let some mApp ← Meta.matchMatcherApp? e then
    if mApp.discrs.size == 1 && mApp.alts.size == 1 then if let .fvar srcFv := stripMeta mApp.discrs[0]! then
      let st ← get; let (srcVars, srcArrs) := ((st.vars.get? srcFv).getD [], (st.arrVars.get? srcFv).getD [])
      return ← lambdaTelescope mApp.alts[0]! fun altFvs altBody => do
        if !srcArrs.isEmpty && (← whnfR (← inferType mApp.discrs[0]!)).isAppOfArity ``Prod 2 then
          let mut vars := srcVars
          let mut arrays := srcArrs
          for fv in altFvs do
            let ty ← inferType fv
            let width := (← flattenType ty `x).length
            let arrayCount ← countArrTys ty
            setVar fv.fvarId! (vars.take width) (arrays.take arrayCount)
            vars := vars.drop width
            arrays := arrays.drop arrayCount
          return ← k altBody
        let mut sFvs : List FVarId := []; let mut aFvs : List FVarId := []
        for fv in altFvs do if ← isArrTy fv then aFvs := aFvs ++ [fv.fvarId!] else sFvs := sFvs ++ [fv.fvarId!]
        for (fvId, (_, av)) in aFvs.zip srcArrs do setVar fvId [] [("", av)]
        if sFvs.length == srcVars.length then
          for (fvId, entry) in sFvs.zip srcVars do setVar fvId [entry]
        else if sFvs.length > 0 then
          let lens ← sFvs.mapM fun fvId => do return (← flattenType (← fvId.getDecl).type `x).length
          if lens.foldl (· + ·) 0 == srcVars.length then
            let mut cur := srcVars
            for (fvId, len) in sFvs.zip lens do setVar fvId (cur.take len); cur := cur.drop len
          else if altFvs.size > 0 then setVar altFvs[0]!.fvarId! srcVars
        else if altFvs.size > 0 then setVar altFvs[0]!.fvarId! srcVars
        k altBody
    if mApp.discrs.size == 1 && mApp.alts.size == 2 then
      let discr := stripMeta mApp.discrs[0]!
      if discr.isAppOfArity ``GetElem?.getElem? 7 then if ← lambdaTelescope mApp.alts[1]! fun _ b => pure (isUbTerm b) then
        let elemExpr := s!"{← lowerExpr discr.getAppArgs[5]!}[{← lowerExpr discr.getAppArgs[6]!}]"
        return ← lambdaTelescope mApp.alts[0]! fun altFvs altBody => do
          if altFvs.size == 1 then
            let ct := (← cType? (← inferType altFvs[0]!)).getD ""
            if (← inferType altFvs[0]!).isConstOf ``String then modify fun s => { s with strLitVars := s.strLitVars.insert altFvs[0]!.fvarId! elemExpr } else setVar altFvs[0]!.fvarId! [("", elemExpr, ct)]
          k altBody
  fallback
private partial def extractLoopCond? (e : Expr) (selfFv : FVarId) : M (Option String) := do
  let e := e.consumeMData.headBeta
  handleMatch e (fun altBody => extractLoopCond? altBody selfFv) do
  let env ← getEnv; let st ← get
  let projFld? (x : Expr) : Option String := match stripMeta x with
    | .proj sn idx (.fvar fv) => if fv == selfFv then Option.map Name.toString (getStructureFields env sn)[idx]? else none
    | .app (.const fn _) (.fvar fv) => if fv == selfFv && env.isProjectionFn fn then some (cIdent fn) else none | _ => none
  let varOf (fld : String) := (st.vars.get? selfFv |>.getD []).find? (·.1 == fld) |>.map (·.2.1)
  let onlyUpdates (stExpr : Expr) (fld : String) (pred : Expr → Bool) : MetaM Bool := do
    let some (_, fldArgs) ← localStructArgs? (stripMeta stExpr) | return false
    return fldArgs.all fun (f, arg) => if f.toString == fld then pred (stripMeta arg) else projFld? arg == some f.toString
  if let .letE n t val body _ := e then
    if val.isAppOfArity ``HSub.hSub 6 && isNatLitVal val.getAppArgs[5]! 1 then if let some projFld := projFld? val.getAppArgs[4]! then if let some vn := varOf projFld then
      return ← withLocalDeclD n t fun fv => do
        setVar fv.fvarId! [("", s!"--{vn}", "")]
        let inner := stripMeta (body.instantiate1 fv)
        if inner.isAppOfArity ``Prod.mk 4 then
          let pred := stripMeta inner.getAppArgs[2]!
          if pred.isAppOfArity ``bne 4 && pred.getAppArgs[2]! == fv && isNatLitVal pred.getAppArgs[3]! 0 then
            if ← onlyUpdates inner.getAppArgs[3]! projFld (· == fv) then return some s!"--{vn}"
        return none
    return none
  if e.isAppOfArity ``ite 5 then
    let a := e.getAppArgs
    if (stripMeta a[3]!).isAppOfArity ``Prod.mk 4 && (stripMeta a[3]!).getAppArgs[2]!.isConstOf ``Bool.false then
      if let some r ← extractLoopCond? a[4]! selfFv then
        let lc := stripMeta a[1]!; let neg ← if lc.isAppOfArity ``BEq.beq 4 then pure s!"({← lowerExpr lc.getAppArgs[2]!} != {← lowerExpr lc.getAppArgs[3]!})" else pure s!"(!{← lowerExpr a[1]!})"
        return some s!"({neg} && {r})"
    if (stripMeta a[4]!).isAppOfArity ``Prod.mk 4 && (stripMeta a[4]!).getAppArgs[2]!.isConstOf ``Bool.false then
      if let some r ← extractLoopCond? a[3]! selfFv then
        return some s!"({← lowerExpr a[1]!} && {r})"
    return none
  if e.isAppOfArity ``Bind.bind 6 then
    let act ← unfoldStep e.getAppArgs[4]!
    if act.isAppOfArity ``C.cinline 2 || act.isAppOfArity ``Zlib.GzFs.ginline 2 ||
       act.isAppOfArity ``C.load8 1 || act.isAppOfArity ``C.Ptr.load 2 then
      let inner ← if act.isAppOfArity ``C.cinline 2 || act.isAppOfArity ``Zlib.GzFs.ginline 2 then unfoldStep act.getAppArgs[1]! else pure act
      let exprS ← lowerExpr inner
      return ← bindCont e.getAppArgs[5]! fun xId cb => do setVar xId [("", exprS, "")]; extractLoopCond? cb selfFv
    if act.isAppOfArity ``C.ByteAddress.address 1 then
      let addrExpr ← lowerExpr act
      return ← bindCont e.getAppArgs[5]! fun xId cb => do setVar xId [("", addrExpr, "unsigned long")]; extractLoopCond? cb selfFv
    if (act.getAppFn.isConstOf ``C.Ptr.lt || act.getAppFn.isConstOf ``C.Ptr.le) && act.getAppNumArgs >= 2 then
      let cmpExpr ← lowerExpr act
      return ← bindCont e.getAppArgs[5]! fun xId cb => do setVar xId [("", cmpExpr, "int")]; extractLoopCond? cb selfFv
    return none
  let rec nextScalarNames (ne : Expr) : M (List String) := do
    let ne := stripMeta ne
    if ne.isAppOfArity ``Prod.mk 4 then
      return (← nextScalarNames ne.getAppArgs[2]!) ++ (← nextScalarNames ne.getAppArgs[3]!)
    if ← isArrTy ne then return []
    if let .fvar fv := ne then
      if let some vs := (← get).vars.get? fv then
        if !vs.isEmpty then return vs.map (·.2.1)
    if let some (sn, fldArgs) ← localStructArgs? ne then
      let env ← getEnv; let mut out : List String := []
      for (f, arg) in fldArgs do
        if let some info := env.find? (sn ++ f) then
          if info.type.getForallBody.getAppFn.constName? != some ``Array then
            out := out ++ (← nextScalarNames arg)
      return out
    return [← lowerExpr ne]
  let s := stripMeta e
  if s.isAppOfArity ``Prod.mk 4 then
    let cond := stripMeta s.getAppArgs[2]!; let nextSt := stripMeta s.getAppArgs[3]!
    if nextSt == .fvar selfFv then return some (← lowerExpr cond)
    if let some loopVars := (← get).vars.get? selfFv then
      let nextNames ← nextScalarNames nextSt
      if nextNames == loopVars.map (·.2.1) then return some (← lowerExpr cond)
    if cond.isAppOfArity ``bne 4 && isNatLitVal cond.getAppArgs[3]! 0 then if let some fld := projFld? cond.getAppArgs[2]! then if let some vn := varOf fld then
      if ← onlyUpdates nextSt fld (fun x => x.isAppOfArity ``HSub.hSub 6 && isNatLitVal x.getAppArgs[5]! 1 && projFld? x.getAppArgs[4]! == some fld) then return some s!"{vn}--"
  return none
private partial def hasNonJpPath (e : Expr) (jpFv : FVarId) (breakIdx? : Option Nat := none)
    (innerJps : Std.HashMap FVarId Bool := {}) : MetaM Bool := do
  let e := stripMeta e.consumeMData.headBeta
  if isUbTerm e || e.getAppFn.fvarId? == some jpFv then return false
  if let some fv := e.getAppFn.fvarId? then
    if let some bad := innerJps.get? fv then return bad
  if e.getAppFn.constName? ∈ [some ``C.LoopStep.brk, some ``C.LoopStep.cont, some ``C.LoopStep.ret, some ``C.GotoStep.goto, some ``C.FwdStep.goto] then return false
  if e.isAppOfArity ``C.GotoStep.done 3 then return ← hasNonJpPath e.getAppArgs[2]! jpFv breakIdx? innerJps
  if let .letE n t v b _ := e then
    if v.isLambda then
      let innerBad ← lambdaTelescope v fun _ jpB => hasNonJpPath jpB jpFv breakIdx? innerJps
      return ← withLocalDeclD n t fun fv => hasNonJpPath (b.instantiate1 fv) jpFv breakIdx? (innerJps.insert fv.fvarId! innerBad)
    return ← withLocalDeclD n t fun fv => hasNonJpPath (b.instantiate1 fv) jpFv breakIdx? innerJps
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let a := e.getAppArgs; return (← hasNonJpPath a[3]! jpFv breakIdx? innerJps) || (← hasNonJpPath (if e.isAppOfArity ``dite 5 then a[4]!.beta #[mkConst ``Unit.unit] else a[4]!) jpFv breakIdx? innerJps)
  if let some mApp ← Meta.matchMatcherApp? e then return ← mApp.alts.anyM fun alt => lambdaTelescope alt fun _ b => hasNonJpPath b jpFv breakIdx? innerJps
  if e.isAppOfArity ``Bind.bind 6 then return ← lambdaBoundedTelescope e.getAppArgs[5]! 1 fun _ b => hasNonJpPath b jpFv breakIdx? innerJps
  if let some idx := breakIdx? then if ((← flattenExprsM e)[idx]?).any fun x => (stripMeta x).isConstOf ``Bool.true then return false
  return true
private def extractBreakLoop? (cond : String) (initExpr : Expr) (loopVars : List VarEntry) : M (Option (String × String)) := do
  let matchCond (vn : String) : Option (String × String) := Id.run do
    if cond ∈ [s!"(!{vn})", s!"({vn} == 0)", s!"({vn} == 0U)"] then return some (vn, "1")
    for pfx in [s!"((!{vn}) && ", s!"(({vn} == 0) && ", s!"(({vn} == 0U) && "] do
      if cond.startsWith pfx && cond.endsWith ")" then return some (vn, ((cond.drop pfx.length).dropEnd 1).toString)
    return none
  if let .fvar fv := stripMeta initExpr then
    let some srcVars := (← get).vars.get? fv | return none
    for ((_, vn, _), (_, s, _)) in pairVars srcVars loopVars do if s == "0" || s == "0U" then if let some r := matchCond vn then return some r
    return none
  let flatInit ← (← flattenExprsM initExpr).filterM (fun fe => do return !(← isArrTy fe))
  if flatInit.length != loopVars.length then return none
  for (iv, (_, vn, _)) in flatInit.zip loopVars do let ivS := stripMeta iv; if isNatLitVal ivS 0 || ivS.isConstOf ``Bool.false then if let some r := matchCond vn then return some r
  return none
private partial def hasCdeclType (ty : Expr) : M (Option (List VarEntry)) := do
  if let some sn := ty.getAppFn.constName? then
    if let some vs := (← get).cdeclVars.get? sn then return some vs
  let ty ← whnfR ty
  if ty.isAppOfArity ``Array 1 then return some []
  if ty.isAppOfArity ``Prod 2 then
    let some l ← hasCdeclType ty.getAppArgs[0]! | return none
    let some r ← hasCdeclType ty.getAppArgs[1]! | return none
    return some (l ++ r)
  return none
private def getLoopVars (ty init : Expr) (hint : Name) : M (List VarEntry × List (String × String)) := do
  let loopArrs ← collectArrExprs init
  if let some vs ← hasCdeclType ty then
    lowerValueToVars init vs
    return (vs, loopArrs)
  let vs ← allocVars ty hint
  lowerValueToVars init vs
  return (vs, loopArrs)
private def emitLabel (lbl : String) : M Unit := do
  let curIndent := (← get).indent
  let pfx := String.ofList (List.replicate ((if curIndent > 0 then curIndent - 1 else 0) * 4) ' ')
  modify fun st => { st with lines := st.lines.push s!"{pfx}{lbl}:" }
private def withStateFn {α} (stTy fnExpr : Expr) (vars : List VarEntry) (arrs : List (String × String)) (k : Expr → M α) : M α := do
  if fnExpr.isLambda then lambdaTelescope fnExpr fun xs body => do setVar xs[0]!.fvarId! vars arrs; k body
  else withLocalDeclD `s stTy fun fv => do setVar fv.fvarId! vars arrs; k (← unfoldStep (mkApp fnExpr fv)).headBeta
private partial def collectSwitch (scrut? : Option String) (cur : Expr) : M (String × List (String × Expr) × Expr) := do
  if cur.isAppOfArity ``ite 5 then
    let ca := cur.getAppArgs
    let test := stripMeta ca[1]!
    unless test.isAppOf ``BEq.beq || test.isAppOf ``Eq do return (scrut?.getD "", [], cur)
    let s ← lowerExpr test
    if s.startsWith "(" && s.endsWith ")" then
      let parts := (((s.drop 1).dropEnd 1).toString).splitOn " == "
      if parts.length == 2 then
        let lit := parts[1]!; let core := if lit.endsWith "UL" then (lit.toSlice.dropEnd 2).toString else if lit.endsWith "U" then (lit.toSlice.dropEnd 1).toString else lit
        if !core.isEmpty && core.all Char.isDigit && (scrut?.isNone || scrut? == some parts[0]!) then
          let (scOut, rest, defArm) ← collectSwitch (some parts[0]!) ca[4]!; return (scOut, (lit, ca[3]!) :: rest, defArm)
  return (scrut?.getD "", [], cur)
/-- Lower the same test and body in both statement and bound-result positions. A continue in
an expanded do-while must run the effectful condition before the next iteration. -/
private def lowerControlledLoop (lower : Expr → Dest → M Unit) (isDo : Bool) (ty cond body : Expr)
    (vs : List VarEntry) (arrs : List (String × String)) (retDest : Dest) : M Unit := do
  let runBody (label : Option String) := withStateFn ty body vs arrs fun b => lower b (.loopStep vs retDest label)
  let test? ← if cond.isLambda then lambdaTelescope cond fun xs b => do
      setVar xs[0]!.fvarId! vs arrs
      extractLoopCond? b xs[0]!.fvarId!
    else withLocalDeclD `s ty fun fv => do
      setVar fv.fvarId! vs arrs
      extractLoopCond? (← unfoldStep (mkApp cond fv)).headBeta fv.fvarId!
  if let some test := test? then
    if !isDo then withBlock s!"while ({test}) \{" (runBody none)
    else
      let saved := (← get).mutLocals
      emit "do {"
      modify fun s => { s with indent := s.indent + 1 }
      runBody none
      modify fun s => { s with indent := s.indent - 1, mutLocals := saved }
      emit s!"} while ({test});"
  else
    let tag ← fresh `loop_cond
    withBlock "for (;;) {" do
      emit s!"int {tag};"
      if isDo then
        let label ← fresh `loop_test
        runBody (some label)
        if (← get).lines.any (fun line => line.trimAscii == s!"goto {label};".toSlice) then emit s!"{label}: ;"
      withStateFn ty cond vs arrs fun b => lower b (.vars (("", tag, "int") :: vs))
      emit s!"if (!{tag}) break;"
      if !isDo then runBody none

/-- C passes its output registers by address. The Lean call takes their initial
    values and returns a product of the return code and the final values. -/
private def lowerOutCall? (act : Expr) (fieldRefs : Array (String × Bool) := #[]) (resultPlace : Option String := none) : M (Option (List VarEntry)) := do
  let some name := act.getAppFn.constName? | return none
  let some (.defnInfo decl) := (← getEnv).find? name | return none
  let (some _, retTy) := unwrapLinkage decl.type.getForallBody | return none
  unless retTy.isAppOfArity ``Prod 2 do return none
  let some fn ← analyzeFn? name decl.type decl.value | return none
  unless fn.outCount > 0 && fn.params.length == act.getAppNumArgs do return none
  let mut args := #[]
  let mut results := #[]
  unless fieldRefs.isEmpty || fieldRefs.size == fn.outCount do
    throwError m!"field address count does not match {name}"
  let mut reloads : Array (String × String × String) := #[]
  for ((param, ct, out), arg) in fn.params.zip act.getAppArgs.toList do
    if out.isSome then
      let localType := stripOutType ct out
      let tmp ← fresh (Name.mkSimple param)
      if let some (field, usedAfterCall) := fieldRefs[results.size]? then
        args := args.push ("&" ++ field)
        if usedAfterCall then reloads := reloads.push (localType, tmp, field)
      else
        emitTemporary localType tmp (some (← lowerExpr arg))
        args := args.push ("&" ++ tmp)
      results := results.push (param, tmp, localType)
    else
      args := args.push (← lowerExpr arg)
  let fields ← flattenType retTy `result
  let actualTypes := fn.retCTy :: results.toList.map (·.2.2)
  unless fields.map Prod.snd == actualTypes do
    throwError m!"output fields of {name} do not match its C ABI"
  let rc ← match resultPlace with | some place => pure place | none => fresh `rc
  let call := fn.cName ++ "(" ++ String.intercalate ", " args.toList ++ ")"
  if resultPlace.isSome then emit s!"{rc} = {call};" else emitTemporary fn.retCTy rc (some call)
  for (ct, tmp, field) in reloads do
    emitTemporary ct tmp (some field)
  return some (("", rc, fn.retCTy) :: results.toList)

private def bindParts? (e : Expr) : Option (Expr × Expr) := do
  let e := stripMeta e
  guard (e.isAppOfArity ``Bind.bind 6)
  let args := e.getAppArgs
  return (stripMeta args[4]!, args[5]!)

/-- Plain call operands can be read in either order before entering the called function. -/
private partial def plainCallOperand (env : Environment) (e : Expr) : Bool :=
  let e := stripMeta e
  if e.isFVar || (natLitOf? e).isSome then true
  else match e with
    | .proj _ _ base => plainCallOperand env base
    | .app (.const name _) base =>
      (name == ``UInt32.toNat || (env.getProjectionFnInfo? name).isSome) && plainCallOperand env base
    | _ => false

/-- Keep a checked address or allocation size at its sole use. Both computations
    preserve the heap on success. Their C pointer arithmetic and shift execute
    before the copy or allocator callback, including when the byte count is zero. -/
private def lowerCallOperand? (lower : Expr → Dest → M Unit) (act cont : Expr) (dest : Dest) : M Bool := do
  let shift := act.isAppOfArity `Zlib.Inflate.shl32 2
  unless shift || act.isAppOf ``C.Ptr.add do return false
  bindCont cont fun id body => do
    let (call, tail) := (bindParts? body).map (fun (c, k) => (c, some k)) |>.getD (body, none)
    let callee := if shift then `Zlib.Inflate.ZALLOCB else ``C.memcpyB
    unless call.isAppOfArity callee 3 do return false
    let args := call.getAppArgs
    unless args[1]!.fvarId? == some id && !args[0]!.containsFVar id && !args[2]!.containsFVar id &&
        !(tail.any (·.containsFVar id)) do return false
    let env ← getEnv
    unless plainCallOperand env args[0]! && plainCallOperand env args[2]! do return false
    let value ← lowerExpr (← unfoldStep act)
    let ct := if shift then "unsigned" else "unsigned char *"
    setVar id [("", value, ct)]
    lower body dest
    return true

/-- A field returned directly by a record load is read before the continuation
    resumes. A scalar or pointer projection does not need to copy the enclosing
    record (which may contain several large embedded arrays). -/
private def returnsScalarField (env : Environment) (record : FVarId) (sn : Name) (body : Expr) : Bool := Id.run do
  let field := match stripMeta body with
    | .proj name idx (.fvar id) =>
      if id == record && name == sn then (getStructureFields env sn)[idx]? else none
    | .app (.const fn _) (.fvar id) =>
      if id == record && fn.getPrefix == sn && env.isProjectionFn fn then some (Name.mkSimple (cIdent fn)) else none
    | _ => none
  return field.any fun f => !(sn == ``C.InflateState && f ∈ [`lens, `work, `codes])

/-- A read followed immediately by a store to the same record needs no copy
    when the old record is dead after that store. -/
private def immediatelyUpdates (body source : Expr) (sn : Name) (record : FVarId) : MetaM Bool := do
  let body := (stripMeta body).headBeta
  let store ← if let some (first, rest) := bindParts? body then do
    if rest.containsFVar record then return false
    pure first
  else pure body
  unless store.getAppFn.constName?.bind structAct? == some (true, sn) && store.getAppNumArgs == 2 do return false
  return ← isDefEq store.getAppArgs[0]! source

/-- Explicit record updates may alias this read even when the pointer expressions
    differ. If the old value occurs in the continuation, capture it before the update. -/
private partial def crossesRecordUpdate (e : Expr) (sn : Name) (id : FVarId) : Bool := Id.run do
  unless e.containsFVar id do return false
  let e := (stripMeta e).headBeta
  if let some (action, rest) := bindParts? e then
    let op := action.getAppFn.constName?
    let updates := op.bind structAct? == some (true, sn) ||
      (sn == ``C.InflateState && op == some `Zlib.Inflate.wrS) ||
      (sn == ``C.ZStream && op == some `Zlib.Inflate.wrZ)
    if updates && rest.containsFVar id then return true
    return crossesRecordUpdate action sn id || crossesRecordUpdate rest sn id
  match e with
  | .lam _ _ b _ => return crossesRecordUpdate b sn id
  | .letE _ _ v b _ => return crossesRecordUpdate v sn id || crossesRecordUpdate b sn id
  | .app f x => return crossesRecordUpdate f sn id || crossesRecordUpdate x sn id
  | _ => return false

/-- Recognize the declared C byte array's lifetime: the modeled body is followed
    by freeing this exact block and returning the body's result unchanged. -/
private def localBytesBody (body : Expr) (buffer : FVarId) : M Expr := do
  let some (computation, cleanup) := bindParts? body | throwError "missing automatic array body"
  bindCont cleanup fun result release => do
    let some (free, tail) := bindParts? release | throwError "missing automatic array cleanup"
    unless free.isAppOfArity ``C.freeB 1 && free.appArg!.fvarId? == some buffer do
      throwError "automatic array cleanup must release the declared array"
    bindCont tail fun _ returned => do
      let returned := returned.consumeMData.headBeta
      unless returned.isAppOfArity ``Pure.pure 4 && returned.appArg!.fvarId? == some result do
        throwError "automatic array cleanup must return the body's result"
      return computation

/-- Remove the writeback already performed through the C output pointers. Return the
    remaining computation abstracted over the three values produced by the call. -/
private def tableContinuation? (cont ptr : Expr) (width : Name) : MetaM (Option Expr) := do
  withLocalDeclD `rc (mkConst ``Int32) fun rc =>
    withLocalDeclD `next (mkConst ``C.CodePtr) fun next =>
      withLocalDeclD `bits (mkConst ``UInt32) fun bits => do
        let result ← mkAppM ``Prod.mk #[rc, ← mkAppM ``Prod.mk #[next, bits]]
        let .reduced body ← reduceMatcher? (cont.beta #[result]) | return none
        let some (store, tail) := bindParts? body | return none
        unless store.isAppOfArity `Zlib.Inflate.wrS 2 do return none
        let args := store.getAppArgs
        unless ← isDefEq args[0]! ptr do return none
        let exactWriteback ← withLocalDeclD `s (mkConst ``C.InflateState) fun s => do
          let fields := getStructureFields (← getEnv) ``C.InflateState
          let values := fields.map fun f =>
            if f == `next then next else if f == width then bits
            else mkApp (mkConst (``C.InflateState ++ f)) s
          isDefEq (mkApp args[1]! s) (mkAppN (mkConst ``C.InflateState.mk) values)
        unless exactWriteback do return none
        return some (← mkLambdaFVars #[rc, next, bits] (tail.beta #[mkConst ``Unit.unit]))

/-- Recognize the complete read/call/writeback sequence. Only the optional
    read-only address computation for the distance alphabet may intervene. -/
private def lowerTableFields? (lower : Expr → Dest → M Unit) (record : FVarId)
    (source : Expr) (p : String) (body : Expr) (dest : Dest) (live : Bool := false) : M Bool := do
  let some (first, cont) := bindParts? body | return false
  let fromState (e : Expr) (field : Name) : MetaM Bool := do
    unless (← getEnv).contains field do return false
    isDefEq e (mkApp (mkConst field) source)
  let project (f : Name) := mkApp (mkConst (``C.InflateState ++ f)) (mkFVar record)
  let compile (call tail : Expr) (offset : Option (FVarId × Expr)) : M Bool := do
    unless call.isAppOfArity `Zlib.Inftrees.inflate_table 6 do return false
    let xs := call.getAppArgs
    unless ← fromState xs[5]! `Zlib.Inflate.workP do return false
    if let some (id, _) := offset then
      unless xs[1]!.fvarId? == some id do return false
    else unless ← fromState xs[1]! `Zlib.Inflate.lensP do return false
    unless ← isDefEq xs[3]! (project `next) do return false
    let some width ← [`lenbits, `distbits].findM? (fun f => isDefEq xs[4]! (project f)) | return false
    let some after ← tableContinuation? tail source width | return false
    if live then
      if after.containsFVar record then return false
      modify fun st => { st with structPtrs := st.structPtrs.insert record (p, ``C.InflateState) }
    if let some (id, add) := offset then
      let rhs ← lowerExpr add
      if live && !after.containsFVar id then setVar id [("", rhs, "unsigned short *")]
      else
        let name ← fresh `lens
        emitTemporary "unsigned short *" name (some rhs)
        setVar id [("", name, "unsigned short *")]
    lambdaBoundedTelescope after 3 fun values rest => do
      let refs := #[`next, width].mapIdx fun i field =>
        (s!"({p})->{field}", rest.containsFVar values[i + 1]!.fvarId!)
      let fused ← (do
        if !live then return none
        let some (registers, _) := (← get).decoderFrame | return none
        let some (store, tail) := bindParts? rest | return none
        unless store.isAppOf ``modify && store.getAppArgs[0]!.isConstOf `Zlib.Inflate.IL do return none
        let exactStore ← withLocalDeclD `l (mkConst `Zlib.Inflate.IL) fun l => do
          let fields := getStructureFields (← getEnv) `Zlib.Inflate.IL
          let vals := fields.map fun fld => if fld == `ret then values[0]! else mkApp (mkConst (`Zlib.Inflate.IL ++ fld)) l
          isDefEq (mkApp store.appArg! l) (mkAppN (mkConst `Zlib.Inflate.IL.mk) vals)
        unless exactStore do return none
        let body := (tail.beta #[mkConst ``Unit.unit]).consumeMData.headBeta
        let id := values[0]!.fvarId!
        if body.containsFVar id then
          unless body.isAppOfArity ``ite 5 && !body.getAppArgs[3]!.containsFVar id && !body.getAppArgs[4]!.containsFVar id do return none
        return some (registers ++ ".ret", body) : M (Option (String × Expr)))
      let some entries ← lowerOutCall? call refs (fused.map Prod.fst) | throwError "missing inflate_table ABI"
      for (value, (_, name, ct)) in values.toList.zip entries do
        setVar value.fvarId! [("", name, ct)]
      lower ((fused.map Prod.snd).getD rest) dest
    return true
  if first.isAppOf `Zlib.Inftrees.inflate_table then return ← compile first cont none
  unless first.isAppOf ``C.Ptr.add do return false
  let args := first.getAppArgs
  unless args.size >= 3 && (← fromState args[args.size - 2]! `Zlib.Inflate.lensP) do return false
  bindCont cont fun id rest => do
    let some (call, tail) := bindParts? rest | return false
    compile call tail (some (id, first))

/-- Run the actual decoder and use its continuation to interpret each exit.
    Both exceptional exits jump out of any enclosing bit-reading loops. -/
private def lowerInflateRun? (lower : Expr → Dest → M Unit) (call cont : Expr) (dest : Dest) : M Bool := do
  unless call.isAppOfArity ``StateT.run 5 do return false
  let xs := call.getAppArgs
  let run := xs[3]!
  unless xs[0]!.isConstOf `Zlib.Inflate.IL && xs[1]!.isConstOf ``C.M &&
      run.isAppOfArity ``ExceptT.run 4 do return false
  let ys := run.getAppArgs
  let ex := mkConst `Zlib.Inflate.Ex
  let unit := mkConst ``Unit
  unless ys[0]! == ex && ys[2]! == unit do return false
  let regs ← fresh `registers
  let leave ← fresh `inf_leave
  let early ← fresh `early_return
  let value ← fresh `return_value
  let doneLabel ← fresh `finished
  let ty := cStructName `Zlib.Inflate.IL
  emit s!"{ty} {regs} = {← lowerExpr (← whnf xs[4]!)};"
  let branch (locals : Expr) (tag : Name) (arg : Expr) : M Expr := do
    let outcome ← mkAppOptM tag #[some ex, some unit, some arg]
    let frame ← mkAppM ``Prod.mk #[outcome, locals]
    let mut body := cont.beta #[frame]
    while let .reduced next ← reduceMatcher? body do body := next
    return body
  let forwarded ← match dest with
    | .ret false => withLocalDeclD `locals xs[0]! fun locals =>
        withLocalDeclD `code (mkConst ``Int32) fun code => do
          let ret ← mkAppM `Zlib.Inflate.Ex.ret #[code]
          let body ← branch locals ``Except.error ret
          let expected ← mkAppOptM ``Pure.pure #[some (mkConst ``C.M), none, some (mkConst ``Int32), some code]
          isDefEq body expected
    | _ => pure false
  unless forwarded do emit s!"int {value};"
  let outer := (← get).decoderFrame
  let outerRet := (← get).decoderReturn
  let outerForward := (← get).forwardDecoderReturn
  modify fun s => { s with
    decoderFrame := some (regs, leave), decoderReturn := some (value, early), forwardDecoderReturn := forwarded }
  lower ys[3]! .unit
  modify fun s => { s with decoderFrame := outer, decoderReturn := outerRet, forwardDecoderReturn := outerForward }
  withLocalDeclD `locals xs[0]! fun locals => do
    setVar locals.fvarId! [("", regs, ty)]
    modify fun st => { st with immutableRecords := st.immutableRecords.insert locals.fvarId! }
    let normal ← branch locals ``Except.ok (mkConst ``Unit.unit)
    let onLeave ← branch locals ``Except.error (mkConst `Zlib.Inflate.Ex.leave)
    unless ← isDefEq normal onLeave do
      withBlock "{" (lower normal dest)
      emit s!"goto {doneLabel};"
    withBlock (leave ++ ": {") (lower onLeave dest)
    emit s!"goto {doneLabel};"
    unless forwarded do
      withBlock (early ++ ": {") do
        withLocalDeclD `code (mkConst ``Int32) fun code => do
          setVar code.fvarId! [("", value, "int")]
          let ret ← mkAppM `Zlib.Inflate.Ex.ret #[code]
          lower (← branch locals ``Except.error ret) dest
  emit s!"{doneLabel}: ;"
  return true

/-- Recognize an unsigned literal match by the alternatives in its recursor
    type, including the variable-bound default branch. -/
private def literalAlts? (m : Meta.MatcherApp) : MetaM (Option (Array Nat)) := do
  let #[discr] := m.discrs | return none
  unless (← inferType discr).isConstOf ``UInt32 && m.params.isEmpty &&
      m.remaining.isEmpty && m.alts.size >= 2 do return none
  let type := (← getConstInfo m.matcherName).type
  forallTelescope type fun args _ => do
    unless args.size == m.alts.size + 2 do return none
    let motive := args[0]!
    let mut literals := #[]
    for i in [:m.alts.size] do
      let altType ← inferType args[i+2]!
      let .forallE _ dom body _ := altType | return none
      unless body.isApp && body.appFn! == motive do return none
      if i + 1 == m.alts.size then
        unless dom.isConstOf ``UInt32 && body.appArg! == .bvar 0 do return none
      else
        let some n := natLitOf? body.appArg! | return none
        unless dom.isConstOf ``Unit && !literals.contains n && n < 2^32 do return none
        literals := literals.push n
    return some literals

private def compressionTarget (tag state flush : Expr) : MetaM Name := do
  let info ← getConstInfo `Zlib.Deflate.CompressFunc.call
  let some dispatch := info.value? | throwError "missing compression dispatcher"
  let .reduced call ← reduceMatcher? (dispatch.beta #[tag, state, flush])
    | throwError m!"unknown compression strategy {tag}"
  unless call.getAppArgs == #[state, flush] do throwError m!"changed compression arguments for {tag}"
  let some target := call.getAppFn.constName? | throwError m!"expected a named function for {tag}"
  return target

/-- An indirect call through the table is valid when replacing the selected
    direct call in each Lean alternative gives the same continuation. -/
private def indirectCompressionCall (m : MatcherApp) (discr : Expr) : MetaM Expr := do
  let strategy ← getConstInfoInduct `Zlib.Deflate.CompressFunc
  withLocalDeclD `state (mkConst ``C.DeflateStatePtr) fun state =>
    withLocalDeclD `flush (mkConst ``Int32) fun flush => do
      let mut common := none
      for ctor in strategy.ctors do
        let tag := mkConst ctor
        let target ← compressionTarget tag state flush
        let selected := { m with discrs := #[tag] }
        let .reduced branch ← reduceMatcher? selected.toExpr
          | throwError m!"cannot specialize compression strategy {tag}"
        let branch := branch.headBeta
        let isCall (e : Expr) := e.isAppOfArity target 2
        unless (branch.find? isCall).isSome do throwError m!"missing call to {target}"
        let replaced := branch.replace fun e => if isCall e then
          some (mkApp3 (mkConst `Zlib.Deflate.CompressFunc.call) discr e.getAppArgs[0]! e.getAppArgs[1]!)
          else none
        if let some first := common then
          unless ← isDefEq first replaced do throwError "compression strategies have different continuations"
        else common := some replaced
      let some result := common | throwError "empty compression dispatcher"
      return result

/-- The deflate state allocator is modeled as a callback check immediately followed
    by a typed allocation or free. Only these exact pairs form the C callback. -/
private def lowerStateAllocator? (lower : Expr → Dest → M Unit) (action cont : Expr) (dest : Dest) : M Bool := do
  let allocate := action.isAppOfArity `Zlib.Deflate.zalloc_default 1
  unless allocate || action.isAppOfArity `Zlib.Deflate.zfree_default 1 do return false
  bindCont cont fun checked body => do
    if body.containsFVar checked then return false
    let some (mem, rest) := bindParts? body | return false
    let stream ← lowerExpr action.appArg!
    if allocate && mem.isConstOf ``C.allocDeflateState then
      return ← bindCont rest fun id tail => do
        let state ← fresh (← id.getDecl).userName
        emitTemporary "deflate_state *" state (some s!"{stream}->zalloc({stream}->opaque, 1, sizeof(deflate_state))")
        setVar id [("", state, "deflate_state *")]
        lower tail dest
        return true
    if !allocate && mem.isAppOfArity ``C.freeDeflateState 1 then
      return ← bindCont rest fun id tail => do
        if tail.containsFVar id then return false
        emit s!"{stream}->zfree({stream}->opaque, {← lowerExpr mem.appArg!});"
        lower tail dest
        return true
    return false

/-- Restrict cursor coalescing to a single dispatch followed directly by its exit.
    Ordinary uses of an addressed local must retain independent cell and register storage. -/
private partial def stripCursorLets (e : Expr) : Expr :=
  match e.consumeMData.headBeta with
  | .letE _ _ value body _ => stripCursorLets (body.instantiate1 value)
  | other => other

/-- For a one-field modification, a C member store preserves every sibling just as
    the Lean record constructor does. A general assignment still copies the record. -/
private def updateOneRegister? (id : FVarId) (record : Expr) (regs : String)
    (cursor : Option String) : M Bool := do
  let record := stripCursorLets record
  unless record.isAppOf `Zlib.Inflate.IL.mk do return false
  let fields := getStructureFields (← getEnv) `Zlib.Inflate.IL
  let mut changes := #[]
  for (field, arg) in fields.zip record.getAppArgs do
    let old := mkApp (mkConst (`Zlib.Inflate.IL ++ field)) (mkFVar id)
    unless ← isDefEq arg old do changes := changes.push (field, arg)
  if changes.size > 1 && !(changes.any (fun (field, _) => field == `pointerLocals)) &&
      (← changes.allM (fun (_, rhs) => isIntegerConstant rhs)) then
    for (field, rhs) in changes do
      let lhs := if field == `next then cursor.getD (regs ++ ".next") else s!"{regs}.{field}"
      emit s!"{lhs} = {← lowerExpr rhs};"
    return true
  let #[(field, rhs)] := changes | return false
  if field == `pointerLocals then return false
  if let some place := cursor then
    if rhs.containsFVar id then emit s!"{regs}.next = {place};"
  let lhs := if field == `next then cursor.getD (regs ++ ".next") else s!"{regs}.{field}"
  emit s!"{lhs} = {← lowerExpr rhs};"
  return true

/-- Capture a single used member at a register read. The occurrence test rejects
    whole-record uses and uses of any other projection in the continuation. -/
private def soleRegisterField? (env : Environment) (id : FVarId) (body : Expr) : Option Name := do
  let member? (e : Expr) : Option Name := do
    match e with
    | .proj `Zlib.Inflate.IL index (.fvar base) =>
      guard (base == id)
      (getStructureFields env `Zlib.Inflate.IL)[index]?
    | .app (.const fn _) (.fvar base) =>
      guard (base == id && fn.getPrefix == `Zlib.Inflate.IL && env.isProjectionFn fn)
      pure <| Name.mkSimple (cIdent fn)
    | _ => none
  let found ← body.find? fun e => (member? e).isSome
  let name ← member? found
  guard (name != `pointerLocals)
  let rest := body.replace fun e => if member? e == some name then some (mkConst ``Unit.unit) else none
  guard (!rest.containsFVar id)
  return name

/-- The register read can stay in the first guard or heap-record store when no
    continuation uses it after an intervening monadic action. -/
private partial def consumesRegisterNow (id : FVarId) (body : Expr) : Bool := Id.run do
  if !body.containsFVar id then return true
  let e := stripCursorLets body
  if e.isAppOfArity ``liftM 5 then return consumesRegisterNow id e.appArg!
  if let some (first, tail) := bindParts? e then
    return !tail.containsFVar id && consumesRegisterNow id first
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    let branch (x : Expr) := if x.isLambda then x.bindingBody! else x
    return consumesRegisterNow id (branch args[3]!) && consumesRegisterNow id (branch args[4]!)
  return e.isAppOfArity `Zlib.Inflate.wrS 2 || e.isAppOfArity `Zlib.Inflate.setMode 2 || e.isAppOfArity `Zlib.Inffast.inflate_fast 2

private def isAddressedDispatchScope (initial : Expr) (cell : FVarId) (body : Expr) : M Bool := do
  let body := stripCursorLets body
  unless body.isAppOfArity ``Bind.bind 6 do return false
  let run := stripCursorLets body.getAppArgs[4]!
  unless run.isAppOfArity `Zlib.Infback.runBackModesFrom 2 do return false
  let frame := stripCursorLets run.getAppArgs[0]!
  unless frame.getAppFn.constName?.map privateToUserName == some `Zlib.Infback.backRegisters &&
      frame.getAppNumArgs == 4 do return false
  unless ← isDefEq frame.getAppArgs[0]! initial do return false
  let dispatch := stripCursorLets run.getAppArgs[1]!
  unless dispatch.isAppOfArity `Zlib.Infback.back_dispatch 1 do return false
  let ctx := stripCursorLets dispatch.appArg!
  unless ctx.isAppOfArity `Zlib.Infback.addressedCtx 7 do return false
  let args := ctx.getAppArgs
  unless args[2]!.fvarId? == some cell do return false
  bindCont body.getAppArgs[5]! fun final tail => do
    let tail := stripCursorLets tail
    unless tail.isAppOfArity `Zlib.Infback.finishBack 6 do return false
    let exitArgs := tail.getAppArgs
    return exitArgs[2]!.fvarId? == some cell && exitArgs[5]!.fvarId? == some final &&
      exitArgs[0]! == args[0]! && exitArgs[1]! == args[1]! &&
      exitArgs[3]! == args[5]! && exitArgs[4]! == args[6]!

/-- The snapshot can be read through the live C pointer if every use is in an
    immediate pure expression or condition, before any call can mutate the record. -/
private partial def readsBeforeEffects (id : FVarId) (body : Expr) : Bool := Id.run do
  if !body.containsFVar id then return true
  let e := stripCursorLets body
  if e.isAppOfArity ``Pure.pure 4 then return true
  if e.isAppOfArity ``liftM 5 then return readsBeforeEffects id e.appArg!
  if let some (action, rest) := bindParts? e then
    if action.isAppOf ``MonadState.get && action.getAppArgs[0]!.isConstOf `Zlib.Inflate.IL &&
        rest.isLambda then
      return readsBeforeEffects id rest.bindingBody!
    return !rest.containsFVar id && readsBeforeEffects id action
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    let branch (x : Expr) := if x.isLambda then x.bindingBody! else x
    return readsBeforeEffects id (branch args[3]!) && readsBeforeEffects id (branch args[4]!)
  return false

/-- A decoder call in the base heap monad cannot mutate the unaddressed code registers. -/
private partial def preservesCodeMember (field : Name) (action : Expr) : M Bool := do
  let e := stripCursorLets action
  let name := e.getAppFn.constName?.getD .anonymous
  if name == ``liftM then return ← preservesCodeMember field e.appArg!
  if (← inferType e).isAppOf ``C.M then return true
  if name ∈ [``Pure.pure, ``MonadState.get, `Zlib.Inflate.consumeCodeWidth, `Zlib.Inflate.DROPBITS, `Zlib.Inflate.BITS,
      `Zlib.Inflate.NEEDBITS, `Zlib.Inflate.PULLBYTE, `Zlib.Infback.NEEDBITS, `Zlib.Infback.needExtra, `Zlib.Infback.PULLBYTE,
      `Zlib.Infback.ROOM, `Zlib.Infback.emitLiteral] then return true
  if name == ``modify && e.getAppArgs[0]!.isConstOf `Zlib.Inflate.IL then
    return ← bindCont e.appArg! fun id changed => do
      let read := mkConst (`Zlib.Inflate.IL ++ field)
      isDefEq (mkApp read changed) (mkApp read (mkFVar id))
  if let some (first, tail) := bindParts? e then
    unless ← preservesCodeMember field first do return false
    return ← bindCont tail fun _ body => preservesCodeMember field body
  return false

private partial def codeUsedWhileLive (id : FVarId) (field : Name) (body : Expr) : M Bool := do
  if !body.containsFVar id then return true
  let e := stripCursorLets body
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let args := e.getAppArgs
    let branch (a : Expr) := if a.isLambda then a.bindingBody! else a
    unless ← codeUsedWhileLive id field (branch args[3]!) do return false
    return ← codeUsedWhileLive id field (branch args[4]!)
  if let some (first, tail) := bindParts? e then
    unless ← codeUsedWhileLive id field first do return false
    if !tail.containsFVar id then return true
    unless ← preservesCodeMember field first do return false
    return ← bindCont tail fun _ rest => codeUsedWhileLive id field rest
  preservesCodeMember field e

private partial def modeSwitchOnly (id : FVarId) (e : Expr) (n : Nat) : Bool := Id.run do
  if e.isAppOfArity ``ite 5 then
    let a := e.getAppArgs
    let cmp := stripMeta a[1]!
    if (cmp.isAppOf ``BEq.beq || cmp.isAppOf ``Eq) && cmp.getAppNumArgs >= 2 &&
        cmp.getAppArgs[cmp.getAppNumArgs-2]!.fvarId? == some id &&
        !cmp.appArg!.containsFVar id && !a[3]!.containsFVar id then
      return modeSwitchOnly id a[4]! (n+1)
  return n >= 3 && !e.containsFVar id

private partial def lowerBindable (e : Expr) (dest : Dest) : M Unit := do
  let e0 := e.consumeMData.headBeta
  let annotated := e0.isAppOfArity `Zlib.Infback.sharedCase 1
  if let .modeTail scope := dest then
    let mode ← if (← get).decoderReturn.isSome && e0.getAppNumArgs == 1 &&
        e0.getAppFn.isConst then do
      let ret ← inferType e0
      pure (ret.isAppOfArity `Zlib.Inflate.X 1 && ret.appArg!.isConstOf ``Unit &&
        (← inferType e0.appArg!).isConstOf `Zlib.Inflate.Ctx)
    else pure false
    if annotated || mode then
      let target := if annotated then e0.appArg! else e0
      let branchLocal := target.find? (fun e => e.fvarId?.any fun id => (scope.find? id).isNone)
      if branchLocal.isNone then
        let cases := (← get).sharedCases
        let label ← match cases.find? (fun (other, _) => other == target) with
          | some (_, label) => pure label
          | none => do
            let label ← fresh `case_body
            modify fun st => { st with sharedCases := cases.push (target, label) }
            pure label
        emit s!"goto {label};"
        return
  if annotated then
    lowerBindable e0.appArg! dest
    return
  if let some value ← constructorProjection? e0 then
    lowerBindable value dest
    return
  if e0.isAppOfArity `Zlib.Inflate.publishCounts 2 then
    let args := e0.getAppArgs
    let ctx := stripMeta args[0]!
    let locals := stripMeta args[1]!
    if let .ret false := dest then
      if ctx.isAppOfArity `Zlib.Inflate.Ctx.mk 4 && locals.isFVar &&
          (← get).immutableRecords.contains locals.fvarId! then
        let strm := s!"({← lowerExpr ctx.getAppArgs[0]!})"
        let st := s!"({← lowerExpr ctx.getAppArgs[1]!})"
        let flush ← lowerExpr ctx.getAppArgs[3]!
        let regs ← lowerExpr locals
        emit s!"{regs}.in_ -= {strm}->avail_in;"
        emit s!"{regs}.out_ -= {strm}->avail_out;"
        emit s!"{strm}->total_in += {regs}.in_;"
        emit s!"{strm}->total_out += {regs}.out_;"
        emit s!"{st}->total += {regs}.out_;"
        withBlock s!"if (({st}->wrap & 4) && {regs}.out_) \{" do
          let args := s!"{st}->check, {strm}->next_out - {regs}.out_, {regs}.out_"
          emit s!"{strm}->adler = {st}->check = {st}->flags ? crc32({args}) : adler32({args});"
        emit s!"{strm}->data_type = (int){st}->bits + ({st}->last ? 64 : 0) + ({st}->mode == TYPE ? 128 : 0) + ({st}->mode == LEN_ || {st}->mode == COPY_ ? 256 : 0);"
        emit s!"if ((({regs}.in_ == 0 && {regs}.out_ == 0) || {flush} == 4) && {regs}.ret == 0) {regs}.ret = -5;"
        emit s!"return {regs}.ret;"
        return
    let some body ← unfoldDefinition? e0 | throwError "cannot unfold decoder count writeback"
    lowerBindable body.headBeta dest
    return
  if let some (regs, leave) := (← get).decoderFrame then
    if e0.isAppOfArity `Zlib.Inflate.repeatCodeLength 1 then
      let ptr := stripMeta e0.appArg!
      let base := (← constructorProjection? ptr).getD ptr
      if base.isFVar then
        let state ← lowerExpr base
        withBlock s!"while ({regs}.copy--) \{" do
          emit s!"({state})->lens[({state})->have++] = (unsigned short){regs}.len;"
      else
        let some body ← unfoldDefinition? e0 | throwError "cannot lower code-length repeat"
        lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.setRepeatCount 2 || e0.isAppOfArity `Zlib.Infback.setRepeatCount 2 then
      let args := e0.getAppArgs
      if let some width := natLitOf? (stripMeta args[1]!) then
        if width < 32 then
          emit s!"{regs}.copy = {← lowerExpr args[0]!} + ((unsigned){regs}.hold & ((1U << {width}U) - 1U));"
          return
      let some body ← unfoldDefinition? e0 | throwError "cannot lower repeat count"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.setPreviousLength 1 || e0.isAppOfArity `Zlib.Infback.setPreviousLength 1 then
      let ptr := stripMeta e0.appArg!
      let base := (← constructorProjection? ptr).getD ptr
      if base.isFVar then
        let state ← lowerExpr base
        emit s!"{regs}.len = (unsigned)({state})->lens[({state})->have - 1U];"
      else
        let some body ← unfoldDefinition? e0 | throwError "cannot lower previous code length"
        lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.appendCurrentCode 1 || e0.isAppOfArity `Zlib.Infback.appendCurrentCode 1 then
      let ptr := stripMeta e0.appArg!
      let base := (← constructorProjection? ptr).getD ptr
      if base.isFVar then
        let state ← lowerExpr base
        emit s!"({state})->lens[({state})->have++] = {regs}.here.val;"
      else
        let some body ← unfoldDefinition? e0 | throwError "cannot lower literal code length"
        lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.storeDictId 2 || e0.isAppOfArity `Zlib.Inflate.startDataCheck 3 then
      let args := e0.getAppArgs
      let z := stripMeta args[0]!
      let p := stripMeta args[1]!
      let z := (← constructorProjection? z).getD z
      let p := (← constructorProjection? p).getD p
      if z.isFVar && p.isFVar then
        let lhs := s!"({← lowerExpr z})->adler = ({← lowerExpr p})->check"
        if e0.isAppOfArity `Zlib.Inflate.storeDictId 2 then
          withLocalDeclD `hold (mkConst ``UInt64) fun hold => do
            setVar hold.fvarId! [("", s!"{regs}.hold", "unsigned long")]
            let value := mkApp (mkConst `Zlib.Inflate.ZSWAP32) hold
            emit s!"{lhs} = {← lowerExpr value};"
          return
        let gzip := stripMeta args[2]!
        if gzip.isConstOf ``Bool.true || gzip.isConstOf ``Bool.false then
          let checksum := if gzip.isConstOf ``Bool.true then "crc32" else "adler32"
          emit s!"{lhs} = {checksum}(0UL, 0, 0U);"
          return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold decoder checksum store"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.CRC2 1 || e0.isAppOfArity `Zlib.Inflate.CRC4 1 then
      let ctx := stripMeta e0.appArg!
      if ctx.isAppOfArity `Zlib.Inflate.Ctx.mk 4 then
        let args := ctx.getAppArgs
        if args[1]!.isFVar && args[2]!.isFVar then
          let st ← lowerExpr args[1]!
          let hbuf ← lowerExpr args[2]!
          let count := if e0.isAppOfArity `Zlib.Inflate.CRC4 1 then 4 else 2
          for i in [:count] do
            let word := if i == 0 then s!"{regs}.hold" else s!"({regs}.hold >> {8*i})"
            emit s!"{hbuf}[{i}] = (unsigned char){word};"
          emit s!"({st})->check = crc32(({st})->check, {hbuf}, {count});"
          return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold gzip header checksum"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.readHeaderString 2 then
      let args := e0.getAppArgs
      let ptr := stripMeta args[0]!
      let base := (← constructorProjection? ptr).getD ptr
      let kind := stripMeta args[1]!
      if base.isFVar && (kind.isConstOf ``Bool.true || kind.isConstOf ``Bool.false) then
        let state := s!"({← lowerExpr base})"
        let field := if kind.isConstOf ``Bool.true then "name" else "comment"
        let cap := if kind.isConstOf ``Bool.true then "name_max" else "comm_max"
        emit s!"if ({regs}.have_ == 0U) goto {leave};"
        emit s!"{regs}.copy = 0U;"
        emit "do {"
        emit s!"    {regs}.len = (unsigned){regs}.next[{regs}.copy++];"
        emit s!"    if ({state}->head != 0 && {state}->head->{field} != 0 && {state}->length < {state}->head->{cap})"
        emit s!"        {state}->head->{field}[{state}->length++] = (unsigned char){regs}.len;"
        emit ("} while (" ++ regs ++ ".len && " ++ regs ++ ".copy < " ++ regs ++ ".have_);")
        withBlock s!"if (({state}->flags & 0x0200) && ({state}->wrap & 4)) \{" do
          emit s!"{state}->check = crc32({state}->check, {regs}.next, {regs}.copy);"
        emit s!"{regs}.have_ -= {regs}.copy;"
        emit s!"{regs}.next += {regs}.copy;"
        emit s!"if ({regs}.len) goto {leave};"
        return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold gzip header string"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.accountCheckedOutput 2 then
      let args := e0.getAppArgs
      let z := stripMeta args[0]!
      let p := stripMeta args[1]!
      let z := (← constructorProjection? z).getD z
      let p := (← constructorProjection? p).getD p
      if z.isFVar && p.isFVar then
        let strm := s!"({← lowerExpr z})"
        let st := s!"({← lowerExpr p})"
        emit s!"{regs}.out_ -= {regs}.left;"
        emit s!"{strm}->total_out += {regs}.out_;"
        emit s!"{st}->total += {regs}.out_;"
        withBlock s!"if (({st}->wrap & 4) && {regs}.out_) \{" do
          let args := s!"{st}->check, {regs}.put - {regs}.out_, {regs}.out_"
          emit s!"{strm}->adler = {st}->check = {st}->flags ? crc32({args}) : adler32({args});"
        emit s!"{regs}.out_ = {regs}.left;"
        return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold decoder output accounting"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.copyHeaderExtra 1 then
      let st ← lowerExpr e0.appArg!
      let head := s!"({st})->head"
      emit s!"{regs}.copy = ({st})->length;"
      emit s!"if ({regs}.copy > {regs}.have_) {regs}.copy = {regs}.have_;"
      withBlock s!"if ({regs}.copy) \{" do
        withBlock s!"if ({head} != 0 && {head}->extra != 0 && ({regs}.len = {head}->extra_len - ({st})->length) < {head}->extra_max) \{" do
          let length := s!"{regs}.len + {regs}.copy > {head}->extra_max ? {head}->extra_max - {regs}.len : {regs}.copy"
          emit s!"memcpy({head}->extra + {regs}.len, {regs}.next, {length});"
        withBlock s!"if ((({st})->flags & 0x0200) && (({st})->wrap & 4)) \{" do
          emit s!"({st})->check = crc32(({st})->check, {regs}.next, {regs}.copy);"
        emit s!"{regs}.have_ -= {regs}.copy;"
        emit s!"{regs}.next += {regs}.copy;"
        emit s!"({st})->length -= {regs}.copy;"
      return
    if e0.isAppOfArity `Zlib.Inflate.withMatchSource 3 then
      let args := e0.getAppArgs
      let st := s!"({← lowerExpr args[0]!})"
      let count ← fresh `match_count
      let origin ← fresh `match_source
      let finish ← fresh `end_match
      emit s!"unsigned {count} = {regs}.out_ - {regs}.left;"
      emit s!"unsigned char *{origin};"
      withBlock s!"if ({st}->offset > {count}) \{" do
        emit s!"{count} = {st}->offset - {count};"
        withBlock s!"if ({count} > {st}->whave && {st}->sane) \{" do
          lowerBindable args[1]! dest
          emit s!"goto {finish};"
        withBlock s!"if ({count} > {st}->wnext) \{" do
          emit s!"{count} -= {st}->wnext;"
          emit s!"{origin} = {st}->window + ({st}->wsize - {count});"
        emit s!"else {origin} = {st}->window + ({st}->wnext - {count});"
        emit s!"if ({count} > {st}->length) {count} = {st}->length;"
      withBlock "else {" do
        emit s!"{origin} = {regs}.put - {st}->offset;"
        emit s!"{count} = {st}->length;"
      emit s!"if ({count} > {regs}.left) {count} = {regs}.left;"
      emit s!"{regs}.copy = {count};"
      emit s!"{regs}.from_ = {origin};"
      emit s!"{regs}.left -= {regs}.copy;"
      emit s!"{st}->length -= {regs}.copy;"
      lowerBindable args[2]! dest
      emit s!"{finish}: ;"
      return
    if e0.isConstOf `Zlib.Inflate.windowBitsFromHeader then
      emit s!"{regs}.len = ((unsigned){regs}.hold & ((1U << 4) - 1U)) + 8U;"
      return
    if e0.isAppOfArity `Zlib.Inflate.setWindowLimit 1 then
      emit s!"({← lowerExpr e0.appArg!})->dmax = 1U << {regs}.len;"
      return
    if e0.isAppOfArity `Zlib.Inflate.resetHeaderCheck 1 then
      emit s!"({← lowerExpr e0.appArg!})->check = crc32(0UL, 0, 0U);"
      return
    if e0.isAppOfArity `Zlib.Inflate.updateHeader 2 then
      let args := e0.getAppArgs
      let ptr := stripMeta args[0]!
      let base := (← constructorProjection? ptr).getD ptr
      if base.isFVar && args[1]!.isLambda then
        let state := s!"({← lowerExpr base})"
        let header := state ++ "->head"
        withBlock s!"if ({header} != 0) \{" do
          lambdaBoundedTelescope args[1]! 3 fun xs value => do
            unless xs.size == 3 do throwError "expected the register, state, and header operands"
            setVar xs[0]!.fvarId! [("", regs, "Zlib_Inflate_IL")]
            modify fun st => { st with
              immutableRecords := st.immutableRecords.insert xs[0]!.fvarId!
              structPtrs := (st.structPtrs.insert xs[1]!.fvarId! (state, ``C.InflateState)).insert
                xs[2]!.fvarId! (header, ``C.GzHeader) }
            emitStructDiff header "" ``C.GzHeader value (some xs[2]!.fvarId!)
        return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold header update"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.storeHeaderWord 2 then
      let args := e0.getAppArgs
      let ptr := stripMeta args[0]!
      let base := (← constructorProjection? ptr).getD ptr
      let os := stripMeta args[1]!
      if base.isFVar && (os.isConstOf ``Bool.true || os.isConstOf ``Bool.false) then
        let st ← lowerExpr base
        withBlock s!"if (({st})->head != 0) \{" do
          if os.isConstOf ``Bool.true then
            emit s!"({st})->head->xflags = (int)({regs}.hold & 0xff);"
            emit s!"({st})->head->os = (int)({regs}.hold >> 8);"
          else emit s!"({st})->head->time = {regs}.hold;"
        return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold gzip header word"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.countDictionaryInput 1 then
      let ptr := stripMeta e0.appArg!
      let base := (← constructorProjection? ptr).getD ptr
      if base.isFVar then
        let stream ← lowerExpr base
        emit s!"({stream})->total_in += {regs}.in_ - ({stream})->avail_in;"
      else
        let some body ← unfoldDefinition? e0 | throwError "cannot unfold input accounting"
        lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.consumeCodeWidth 2 then
      let args := e0.getAppArgs
      let kind := stripMeta args[1]!
      if kind.isConstOf ``Bool.true || kind.isConstOf ``Bool.false then
        let field := if kind.isConstOf ``Bool.true then "last" else "here"
        let width := s!"{regs}.{field}.bits"
        emit s!"{regs}.hold >>= {width};"
        emit s!"{regs}.bits -= (unsigned){width};"
        emit s!"({← lowerExpr args[0]!})->back += {width};"
        return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold decoder code width"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.addExtra 2 then
      let args := e0.getAppArgs
      let ptr := stripMeta args[0]!
      let base := (← constructorProjection? ptr).getD ptr
      let dist := stripMeta args[1]!
      if base.isFVar && (dist.isConstOf ``Bool.false || dist.isConstOf ``Bool.true) then
        let state ← lowerExpr base
        let field := if dist.isConstOf ``Bool.true then "offset" else "length"
        withBlock s!"if (({state})->extra != 0) \{" do
          withBlock s!"while ({regs}.bits < ({state})->extra) \{" do
            lowerBindable (mkConst `Zlib.Inflate.PULLBYTE) .unit
          emit s!"({state})->{field} += (unsigned){regs}.hold & ((1U << ({state})->extra) - 1U);"
          emit s!"{regs}.hold >>= ({state})->extra;"
          emit s!"{regs}.bits -= ({state})->extra;"
          emit s!"({state})->back += ({state})->extra;"
        return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold streaming decoder extra bits"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Infback.extendExtra 2 || e0.isAppOfArity `Zlib.Infback.backMatch 1 then
      let args := e0.getAppArgs
      let ctx := stripMeta args[0]!
      if (← get).decoderCursor.isSome && ctx.isAppOfArity `Zlib.Infback.addressedCtx 7 then
        let state ← lowerExpr ctx.getAppArgs[1]!
        if e0.isAppOfArity `Zlib.Infback.backMatch 1 then
          emit "do {"
          lowerBindable (mkApp (mkConst `Zlib.Infback.ROOM) args[0]!) .unit
          emit s!"{regs}.copy = ({state})->wsize - ({state})->offset;"
          withBlock s!"if ({regs}.copy < {regs}.left) \{" do
            emit s!"{regs}.from_ = {regs}.put + {regs}.copy;"
            emit s!"{regs}.copy = {regs}.left - {regs}.copy;"
          withBlock "else {" do
            emit s!"{regs}.from_ = {regs}.put - ({state})->offset;"
            emit s!"{regs}.copy = {regs}.left;"
          withBlock s!"if ({regs}.copy > ({state})->length) \{" do
            emit s!"{regs}.copy = ({state})->length;"
          emit s!"({state})->length -= {regs}.copy;"
          emit s!"{regs}.left -= {regs}.copy;"
          lowerBindable (mkConst `Zlib.Inflate.copyMatchBytes) .unit
          emit s!"} while (({state})->length != 0);"
          return
        let dist := stripMeta args[1]!
        if dist.isConstOf ``Bool.false || dist.isConstOf ``Bool.true then
          let field := if dist.isConstOf ``Bool.true then "offset" else "length"
          withBlock s!"if (({state})->extra != 0) \{" do
            withBlock s!"while ({regs}.bits < ({state})->extra) \{" do
              lowerBindable (mkApp (mkConst `Zlib.Infback.PULLBYTE) args[0]!) .unit
            emit s!"({state})->{field} += (unsigned){regs}.hold & ((1U << ({state})->extra) - 1U);"
            emit s!"{regs}.hold >>= ({state})->extra;"
            emit s!"{regs}.bits -= ({state})->extra;"
          return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold decoder match step"
      lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Infback.emitLiteral 1 || e0.isAppOfArity `Zlib.Inflate.emitLiteral 1 then
      let ptr := stripMeta e0.appArg!
      let base := (← constructorProjection? ptr).getD ptr
      if base.isFVar then
        let state ← lowerExpr base
        emit s!"*{regs}.put++ = (unsigned char)({state})->length;"
        emit s!"{regs}.left--;"
      else
        let some body ← unfoldDefinition? e0 | throwError "cannot unfold literal output"
        lowerBindable body.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Inflate.LOAD 2 || e0.isAppOfArity `Zlib.Inflate.RESTORE 2 then
      let args := e0.getAppArgs
      let streamArg := stripMeta args[0]!
      let stateArg := stripMeta args[1]!
      let streamArg := (← constructorProjection? streamArg).getD streamArg
      let stateArg := (← constructorProjection? stateArg).getD stateArg
      let cursor := ((← get).decoderCursor.map Prod.snd).getD (regs ++ ".next")
      if streamArg.isFVar && stateArg.isFVar then
          let stream ← lowerExpr streamArg
          let state ← lowerExpr stateArg
          for (localRegister, field) in [(s!"{regs}.put",s!"({stream})->next_out"),
              (s!"{regs}.left",s!"({stream})->avail_out"), (cursor,s!"({stream})->next_in"),
              (s!"{regs}.have_",s!"({stream})->avail_in"), (s!"{regs}.hold",s!"({state})->hold"),
              (s!"{regs}.bits",s!"({state})->bits")] do
            if e0.isAppOfArity `Zlib.Inflate.LOAD 2 then emit s!"{localRegister} = {field};"
            else emit s!"{field} = {localRegister};"
          return
      let some body ← unfoldDefinition? e0 | throwError "cannot unfold stream register transfer"
      lowerBindable body.headBeta dest
      return
    let callbackLookup := e0.isAppOfArity `Zlib.Infback.lookup1 2 || e0.isAppOfArity `Zlib.Infback.lookup2 2
    let ordinaryLookup := e0.isAppOfArity `Zlib.Inflate.lookup1 2 || e0.isAppOfArity `Zlib.Inflate.lookup2 2
    if ((← get).decoderCursor.isSome && callbackLookup) || ordinaryLookup then
      let args := e0.getAppArgs
      let ctx := stripMeta args[0]!
      let dist := stripMeta args[1]!
      let valid := (ordinaryLookup && ctx.isAppOfArity `Zlib.Inflate.Ctx.mk 4) ||
        (callbackLookup && ctx.isAppOfArity `Zlib.Infback.addressedCtx 7)
      if valid && (dist.isConstOf ``Bool.true || dist.isConstOf ``Bool.false) then
        let state ← lowerExpr ctx.getAppArgs[1]!
        let which := if dist.isConstOf ``Bool.true then "dist" else "len"
        let link := e0.isAppOfArity `Zlib.Infback.lookup2 2 || e0.isAppOfArity `Zlib.Inflate.lookup2 2
        let width := if link then s!"({regs}.last.bits + {regs}.last.op)" else s!"({state})->{which}bits"
        let mask := s!"((unsigned){regs}.hold & ((1U << ({width})) - 1U))"
        let index := if link then s!"{regs}.last.val + ({mask} >> {regs}.last.bits)" else mask
        let consumed := if link then s!"({regs}.last.bits + {regs}.here.bits)" else s!"{regs}.here.bits"
        withBlock "for (;;) {" do
          emit s!"{regs}.here = ({state})->{which}code[{index}];"
          emit s!"if ((unsigned){consumed} <= {regs}.bits) break;"
          let refill := if ordinaryLookup then mkConst `Zlib.Inflate.PULLBYTE
            else mkApp (mkConst `Zlib.Infback.PULLBYTE) args[0]!
          lowerBindable refill .unit
        return
    if e0.isAppOfArity `Zlib.Inflate.startLengthTable 1 then
      let state ← lowerExpr e0.appArg!
      emit s!"({state})->next = ({state})->codes;"
      emit s!"({state})->lencode = ({state})->distcode = (const code *)({state})->next;"
      emit s!"({state})->lenbits = 7U;"
      return
    if e0.isAppOfArity `Zlib.Infback.storeOrderedLength 2 || e0.isAppOfArity `Zlib.Inflate.storeOrderedLength 2 then
      let args := e0.getAppArgs
      let value := args[1]!.consumeMData.headBeta
      let rhs ← if value.isAppOfArity ``Pure.pure 4 && (natLitOf? (stripMeta value.appArg!)).isSome then
        some <$> lowerExpr value.appArg!
      else if let some (bits, cont) := bindParts? value then do
        if bits.isAppOfArity `Zlib.Inflate.BITS 1 && (natLitOf? (stripMeta bits.appArg!)).any (· < 32) then
          bindCont cont fun id body => do
            unless body.isAppOfArity ``Pure.pure 4 do return none
            let cast := mkApp (mkConst ``UInt32.toUInt16) (mkFVar id)
            unless ← isDefEq body.appArg! cast do return none
            let width ← lowerExpr bits.appArg!
            return some s!"(unsigned short)((unsigned){regs}.hold & ((1U << ({width})) - 1U))"
        else pure none
      else pure none
      if let some rhs := rhs then
        let state ← lowerExpr args[0]!
        let table ← lowerExpr (mkConst `Zlib.Inflate.order)
        emit s!"({state})->lens[{table}[({state})->have++]] = {rhs};"
        return
    if e0.isAppOfArity `Zlib.Inflate.withLengthOrder 3 then
      let args := e0.getAppArgs
      let state ← lowerExpr args[1]!
      let table ← lowerExpr (mkConst `Zlib.Inflate.order)
      bindCont args[2]! fun id body => do
        let index ← fresh (← id.getDecl).userName
        emitTemporary "unsigned short" index (some s!"{table}[({state})->have++]")
        setVar id [("", index, "unsigned short")]
        lowerBindable body dest
      return
    if e0.isAppOfArity `Zlib.Inflate.DROPBITS 1 || e0.isConstOf `Zlib.Inflate.BYTEBITS then
      let count ← if e0.isConstOf `Zlib.Inflate.BYTEBITS then pure s!"({regs}.bits & 7U)"
        else if (natLitOf? (stripMeta e0.appArg!)).isSome ||
            (e0.appArg!.isAppOfArity ``UInt8.toUInt32 1 && plainCallOperand (← getEnv) e0.appArg!.appArg!) then
          lowerExpr e0.appArg!
        else do
          let shift ← fresh `shift
          emitTemporary "unsigned" shift (some (← lowerExpr e0.appArg!))
          pure shift
      emit s!"{regs}.hold >>= {count};"
      emit s!"{regs}.bits -= {count};"
      return
    if e0.isAppOfArity `Zlib.Infback.copyStoredInput 1 || e0.isAppOfArity `Zlib.Inflate.copyStoredInput 1 then
      let state ← lowerExpr e0.appArg!
      let next := ((← get).decoderCursor.map Prod.snd).getD (regs ++ ".next")
      emit s!"if ({regs}.copy > {regs}.have_) {regs}.copy = {regs}.have_;"
      emit s!"if ({regs}.copy > {regs}.left) {regs}.copy = {regs}.left;"
      if e0.isAppOfArity `Zlib.Inflate.copyStoredInput 1 then
        emit s!"if ({regs}.copy == 0U) goto {leave};"
      emit s!"memcpy({regs}.put, {next}, {regs}.copy);"
      emit s!"{regs}.have_ -= {regs}.copy;"
      emit s!"{next} += {regs}.copy;"
      emit s!"{regs}.left -= {regs}.copy;"
      emit s!"{regs}.put += {regs}.copy;"
      emit s!"({state})->length -= {regs}.copy;"
      return
    if e0.isConstOf `Zlib.Inflate.copyMatchBytes then
      emit "do {"
      emit s!"    *{regs}.put++ = *{regs}.from_++;"
      emit s!"} while (--{regs}.copy);"
      return
    if e0.isAppOfArity `Zlib.Infback.ROOM 1 then
      let ctx := stripMeta e0.appArg!
      if ctx.isAppOfArity `Zlib.Infback.addressedCtx 7 then
        let args := ctx.getAppArgs
        if let some (cell, _) := (← get).decoderCursor then
          if args[2]!.fvarId? == some cell then
            let state ← lowerExpr args[1]!
            let outFn ← lowerExpr args[5]!
            let desc ← lowerExpr args[6]!
            withBlock s!"if ({regs}.left == 0) \{" do
              emit s!"{regs}.put = ({state})->window;"
              emit s!"{regs}.left = ({state})->wsize;"
              emit s!"({state})->whave = {regs}.left;"
              withBlock s!"if ({outFn}({desc}, {regs}.put, {regs}.left)) \{" do
                emit s!"{regs}.ret = {← lowerExpr (mkConst `C.Z_BUF_ERROR)};"
                emit s!"goto {leave};"
            return
      let some act ← unfoldDefinition? e0 | throwError "cannot lower output refill"
      lowerBindable act.headBeta dest
      return
    if e0.isAppOfArity `Zlib.Infback.PULL 1 then
      let ctx := stripMeta e0.appArg!
      if ctx.isAppOfArity `Zlib.Infback.addressedCtx 7 then
        let args := ctx.getAppArgs
        if let some (cell, place) := (← get).decoderCursor then
          if args[2]!.fvarId? == some cell then
            withBlock s!"if ({regs}.have_ == 0) \{" do
              emit s!"{regs}.have_ = {← lowerExpr args[3]!}({← lowerExpr args[4]!}, &{place});"
              withBlock s!"if ({regs}.have_ == 0) \{" do
                emit s!"{place} = 0;"
                emit s!"{regs}.ret = {← lowerExpr (mkConst `C.Z_BUF_ERROR)};"
                emit s!"goto {leave};"
            return
      let some act ← unfoldDefinition? e0 | throwError "cannot lower input refill"
      lowerBindable act.headBeta dest
      return
    if e0.isConstOf `Zlib.Inflate.absorbInputByte then
      let next := ((← get).decoderCursor.map Prod.snd).getD (regs ++ ".next")
      emit s!"{regs}.have_--;"
      emit s!"{regs}.hold += (unsigned long)(*{next}++) << {regs}.bits;"
      emit s!"{regs}.bits += 8U;"
      return
    if e0.isAppOfArity ``liftM 5 then
      lowerBindable e0.getAppArgs.back! dest
      return
    let action := stripMeta e0
    let fn := action.getAppFn.constName?.getD .anonymous
    let args := action.getAppArgs
    if privateToUserName fn == `Zlib.Infback.inDecoder then
      lowerBindable args.back! dest
      return
    if fn == ``MonadStateOf.set && args[0]!.isConstOf `Zlib.Inflate.IL then
      emit s!"{regs} = {← lowerExpr args.back!};"
      if let some (_, place) := (← get).decoderCursor then emit s!"{place} = {regs}.next;"
      return
    if fn == ``modify && args[0]!.isConstOf `Zlib.Inflate.IL then
      bindCont args.back! fun id body => do
        setVar id [("", regs, cStructName `Zlib.Inflate.IL)]
        if ← updateOneRegister? id body regs ((← get).decoderCursor.map Prod.snd) then return
        if let some (_, place) := (← get).decoderCursor then emit s!"{regs}.next = {place};"
        emit s!"{regs} = {← lowerExpr body};"
        if let some (_, place) := (← get).decoderCursor then emit s!"{place} = {regs}.next;"
      return
    if fn == ``MonadExcept.throw && args[0]!.isConstOf `Zlib.Inflate.Ex then
      if let some (value, early) := (← get).decoderReturn then
        if args.back!.isAppOfArity `Zlib.Inflate.Ex.ret 1 then
          if (← get).forwardDecoderReturn then emit s!"return {← lowerExpr args.back!.appArg!};"
          else
            emit s!"{value} = {← lowerExpr args.back!.appArg!};"
            emit s!"goto {early};"
          return
        unless args.back!.isConstOf `Zlib.Inflate.Ex.leave do throwError "unknown decoder exception"
      emit s!"goto {leave};"
      return
    if fn == `Zlib.Inflate.xwhileBrk then
      if let some (read, done) := bindParts? args[0]! then
        if read.isAppOfArity ``C.ldInflateState 1 then
          let direct ← bindCont done fun id action => do
            unless action.isAppOfArity ``Pure.pure 4 do return false
            let test := stripMeta action.appArg!
            unless test.isAppOfArity ``LT.lt 4 do return false
            let field (which : Name) := mkApp (mkConst (``C.InflateState ++ which)) (mkFVar id)
            unless ← isDefEq test.getAppArgs[2]! (field `«have») do return false
            let sum ← mkAppM ``HAdd.hAdd #[field `nlen, field `ndist]
            unless ← isDefEq test.getAppArgs[3]! sum do return false
            let state ← lowerExpr read.appArg!
            let leave ← fresh `finished_lengths
            withBlock s!"while (({state})->have < ({state})->nlen + ({state})->ndist) \{" do
              lowerBindable args[1]! (.exitOnTrue leave)
            emit s!"{leave}: ;"
            return true
          if direct then return
    if fn == `Zlib.Inflate.xwhile then
      if let some (read, done) := bindParts? args[0]! then
        if read.isAppOfArity ``C.ldInflateState 1 then
          let direct ← bindCont done fun id action => do
            unless action.isAppOfArity ``Pure.pure 4 do return false
            let test := stripMeta action.appArg!
            unless test.isAppOfArity ``LT.lt 4 do return false
            let operands := test.getAppArgs
            let field (which : Name) := mkApp (mkConst (``C.InflateState ++ which)) (mkFVar id)
            unless ← isDefEq operands[2]! (field `«have») do return false
            let state ← lowerExpr read.appArg!
            let bound ← if (natLitOf? (stripMeta operands[3]!)).isSome then some <$> lowerExpr operands[3]!
              else if ← isDefEq operands[3]! (field `ncode) then pure (some s!"({state})->ncode")
              else pure none
            let some bound := bound | return false
            withBlock s!"while (({state})->have < {bound}) \{" do lowerBindable args[1]! .unit
            return true
          if direct then return
        if read.isAppOfArity `Zlib.Inflate.rdS 3 then
          let direct ← bindCont done fun id tail => do
            let tail := tail.consumeMData.headBeta
            unless tail.isAppOfArity ``Pure.pure 4 do return false
            let test := tail.appArg!
            let zero ← mkNumeral (mkConst ``UInt32) 0
            let want ← mkAppM ``bne #[mkFVar id, zero]
            unless ← isDefEq test want do return false
            let field ← bindCont read.getAppArgs[2]! fun state projection => do
              let field := mkApp (mkConst ``C.InflateState.length) (mkFVar state)
              isDefEq projection field
            unless field do return false
            let ptr ← lowerExpr read.getAppArgs[1]!
            withBlock s!"while (({ptr})->length != 0) \{" do
              lowerBindable args[1]! .unit
            return true
          if direct then return
        if read.isAppOf ``MonadState.get && read.getAppArgs[0]!.isConstOf `Zlib.Inflate.IL then
          let direct ← bindCont done fun id result => do
            let result := result.consumeMData.headBeta
            unless result.isAppOfArity ``Pure.pure 4 do return false
            let lt := result.appArg!
            let test := stripMeta lt
            unless test.isAppOfArity ``LT.lt 4 do return false
            let bound := test.getAppArgs[3]!
            let limit := stripMeta bound
            let isComputed := limit.isAppOfArity ``HAdd.hAdd 6 &&
              (natLitOf? (stripMeta limit.appArg!)).isSome &&
              (limit.getAppArgs[4]!.find? (·.isConstOf ``C.Code.bits)).isSome
            unless (natLitOf? limit).isSome || isComputed do return false
            let bits := mkApp (mkConst `Zlib.Inflate.IL.bits) (mkFVar id)
            unless ← isDefEq test.getAppArgs[2]! bits do return false
            withBlock s!"while ({regs}.bits < {← lowerExpr bound}) \{" do
              lowerBindable args[1]! .unit
            return true
          if direct then return
    if fn ∈ [`Zlib.Inflate.xwhile, `Zlib.Inflate.xwhileBrk, `Zlib.Inflate.xloopBrk, `Zlib.Inflate.xdoWhile] then
      let condition (a : Expr) := do
        let test := stripCursorLets a
        if test.isAppOfArity ``Pure.pure 4 && test.appArg!.isConstOf ``Bool.true then return
        let v ← fresh `cond
        emit s!"int {v};"
        lowerBindable a (.vars [("", v, "int")])
        emit s!"if (!{v}) break;"
      let body (a : Expr) := do
        if fn ∈ [`Zlib.Inflate.xloopBrk, `Zlib.Inflate.xwhileBrk] then
          let v ← fresh `stop
          emit s!"int {v};"
          lowerBindable a (.vars [("", v, "int")])
          emit s!"if ({v}) break;"
        else lowerBindable a .unit
      withBlock "for (;;) {" do
        if fn == `Zlib.Inflate.xdoWhile then
          body args[0]!
          condition args[1]!
        else
          if fn != `Zlib.Inflate.xloopBrk then condition args[0]!
          if fn == `Zlib.Inflate.xwhile && args.back!.isAppOfArity `Zlib.Inflate.inflate_dispatch 1 then
            let scope ← getLCtx
            let saved ← get
            modify fun state => { state with sharedCases := #[], placedCases := {}, inInflateDispatch := true }
            let some dispatch ← unfoldDefinition? args.back! | throwError "cannot lower decoder dispatch"
            lowerBindable dispatch.headBeta (.modeTail scope)
            let mut i := 0
            let mut guarded := false
            while i < (← get).sharedCases.size do
              let (target, label) := (← get).sharedCases[i]!
              unless (← get).placedCases.contains label do
                unless guarded do
                  emit "continue;"
                  guarded := true
                let some block ← unfoldDefinition? target | throwError m!"cannot lower decoder case {target}"
                withBlock (label ++ ": {") do
                  lowerBindable block.headBeta (.modeTail scope)
                  emit "continue;"
              i := i+1
            modify fun state => { state with sharedCases := saved.sharedCases, placedCases := saved.placedCases, inInflateDispatch := saved.inInflateDispatch }
          else body args.back!
      return
  if e0.isAppOfArity `Zlib.Inflate.appendLength 5 then
    let args := e0.getAppArgs
    let state ← fresh `state
    let value ← fresh `lengthValue
    emitTemporary "struct inflate_state *" state (some (← lowerExpr args[3]!))
    emitTemporary "unsigned short" value (some (← lowerExpr args[4]!))
    emit s!"{state}->lens[{state}->have++] = {value};"
    return
  if e0.isAppOfArity ``C.withBPtrCell 3 then
    let args := e0.getAppArgs
    let init ← lowerExpr args[1]!
    withBlock "{" do
      bindCont args[2]! fun cell body => do
        let localName ← fresh (← cell.getDecl).userName
        emit s!"unsigned char *{localName} = {init};"
        setVar cell [("", s!"(&{localName})", "unsigned char **")]
        let outerCells := (← get).pointerCells
        if ← isAddressedDispatchScope args[1]! cell body then
          modify fun s => { s with pointerCells := outerCells.insert cell localName }
        lowerBindable body dest
        modify fun s => { s with pointerCells := outerCells }
    return
  let e ← match e0.getAppFn.constName? with | some fn => if ← shouldUnfoldHelper fn then unfoldStep e0 else pure e0 | none => pure e0
  if (← get).decoderFrame.isSome && e != e0 then
    lowerBindable e dest
    return
  if (stripMeta e).isAppOfArity ``ForInStep.done 2 then
    let some (label, _) := (← get).rangeExit? | throwError "for-in early exit outside a range"
    lowerBindable (stripMeta e).appArg! dest
    emit s!"goto {label};"
    modify fun st => { st with rangeExit? := some (label, true) }
    return
  let eYield := stripMeta e; if eYield.isAppOfArity ``ForInStep.yield 2 then lowerBindable eYield.getAppArgs[1]! dest; return
  if let some mApp ← Meta.matchMatcherApp? e then
    if let #[discr] := mApp.discrs then
      let ty ← whnfR (← inferType discr)
      if ty.isConstOf `Zlib.Deflate.CompressFunc then
        lowerBindable (← indirectCompressionCall mApp discr) dest
        return
      if ty.isAppOfArity ``Option 1 && ty.appArg!.isConstOf ``C.DeflateStateRef then
        let noneVal ← mkAppOptM ``Option.none #[some ty.appArg!]
        let noneMatcher := { mApp with discrs := #[noneVal] }
        if let .reduced invalid ← Meta.reduceMatcher? noneMatcher.toExpr then
          let invalid := invalid.headBeta
          if isUbTerm invalid || (bindParts? invalid).any (fun (first, _) => isUbTerm first) then
            let ptr ← lowerExpr discr
            withLocalDeclD `id (mkConst ``Nat) fun id => do
              let tag ← mkAppM ``C.DeflateStateRef.tab #[id]
              let someVal ← mkAppM ``Option.some #[tag]
              let validMatcher := { mApp with discrs := #[someVal] }
              let .reduced valid ← Meta.reduceMatcher? validMatcher.toExpr
                | throwError m!"cannot specialize state reference {mApp.matcherName}"
              withBlock s!"if (!{ptr}) \{" (emit "__builtin_unreachable();")
              modify fun st => { st with deflateIds := st.deflateIds.insert id.fvarId! ptr }
              lowerBindable valid.headBeta dest
            return
      if let some shape ← (if discr.isAppOfArity ``GetElem?.getElem? 7 then pure none else taggedOption? ty) then
        recordOption shape
        let localName ← fresh `optional
        emitTemporary shape.1 localName (some (← lowerExpr discr))
        let payload := ty.appArg!
        let select (value : Expr) : M Expr := do
          let matched := { mApp with discrs := #[value] }
          let .reduced body ← Meta.reduceMatcher? matched.toExpr
            | throwError m!"cannot specialize optional matcher {mApp.matcherName}"
          return body.headBeta
        withBlock s!"if ({localName}.present) \{" do
          withLocalDeclD `value payload fun fv => do
            let fields := shape.2.zipIdx.map fun (ct, i) => ("", s!"{localName}.value{i}", ct)
            setVar fv.fvarId! fields
            lowerBindable (← select (← mkAppM ``Option.some #[fv])) dest
        withBlock "else {" do
          lowerBindable (← select (← mkAppOptM ``Option.none #[some payload])) dest
        return
    let noBreak := (← get).breakVar?.isNone
    let switchOK := match dest with
      | .unit | .modeTail _ | .ret _ | .vars _ => noBreak
      | _ => false
    if let some lits ← (if switchOK && (← get).decoderFrame.isSome then literalAlts? mApp else pure none) then
      let discr := mApp.discrs[0]!
      withBlock s!"switch ({← lowerExpr discr}) \{" do
        for i in [:lits.size] do
          withBlock s!"case {lits[i]!}U: \{" do
            lowerBindable (mApp.alts[i]!.beta #[mkConst ``Unit.unit]) dest
            emit "break;"
        withBlock "default: {" do
          lowerBindable (mApp.alts.back!.beta #[discr]) dest
          emit "break;"
      return
    if let #[discr] := mApp.discrs then
      if mApp.alts.size == 1 && discr.isAppOfArity ``ite 5 && discr.getAppArgs[0]!.isAppOfArity ``Prod 2 then
        let ty := discr.getAppArgs[0]!
        let fields ← allocVars ty `part
        lowerValueToVars discr fields
        withLocalDeclD `parts ty fun fv => do
          setVar fv.fvarId! fields
          lowerBindable (e.replace fun x => if x == discr then some fv else none) dest
        return
  handleMatch e (fun altBody => lowerBindable altBody dest) do
  if let .letE jpName declaredTy jpVal body _ := e then
    if jpVal.isLambda then
      lambdaTelescope jpVal fun xs jpBody => do
        let firstTy ← inferType xs[0]!
        let hasUnit := firstTy.isConstOf ``Unit || firstTy.isConstOf ``PUnit
        let argFvs := if hasUnit then xs.toList.tail! else xs.toList
        let jpArgs ← argFvs.mapM fun fv => do
          let decl ← fv.fvarId!.getDecl
          if let some cVs ← hasCdeclType decl.type then
            return cVs
          (← flattenType decl.type decl.userName).mapM fun (fnm, ct) => do
            let name := cIdent fnm; let vn ← match (← get).mutLocals.find? (fun p => (p.1 == name || p.1.startsWith (name ++ "_")) && p.2 == ct) with | some (ex, _) => pure ex | none => declMut fnm ct
            return (name, vn, ct)
        withLocalDeclD jpName (mkConst ``Unit) fun jpFv => do
          let isRet := match dest with | .ret _ => true | _ => false
          let breakIdx? := match dest, (← get).breakVar? with | .vars vs, some bv => vs.findIdx? (·.2.1 == bv) | _, _ => none
          let body' := body.instantiate1 jpFv
          let guarded ← if isRet then pure false else hasNonJpPath body' jpFv.fvarId! breakIdx?
          let caseJoin ← match dest with
            | .modeTail _ =>
              if guarded && jpArgs.isEmpty then
                let enter ← fresh `resume_case
                let skip ← fresh `finish_case
                modify fun st => { st with caseJoins := st.caseJoins.insert jpFv.fvarId! enter }
                pure (some (enter, skip))
              else pure none
            | _ => pure none
          let guard? ← if guarded && caseJoin.isNone then do
            let flag ← fresh `jp_go
            emit s!"int {flag} = 0;"
            pure (some flag)
          else pure none
          modify fun st => { st with joins := st.joins.insert jpFv.fvarId! (jpArgs, hasUnit), joinGuards := match guard? with | some g => st.joinGuards.insert jpFv.fvarId! g | none => st.joinGuards }
          lowerBindable body' dest
          let jArrs := ((← get).joinArrs.get? jpFv.fvarId!).getD []
          for (fv, entries) in argFvs.zip jpArgs do modify fun st => { st with vars := st.vars.insert fv.fvarId! entries }
          for (fv, arrs) in argFvs.zip jArrs do modify fun st => { st with arrVars := st.arrVars.insert fv.fvarId! arrs }
          if let some (enter, skip) := caseJoin then
            emit s!"goto {skip};"
            emit s!"{enter}: ;"
            lowerBindable jpBody dest
            emit s!"{skip}: ;"
          else if let some g := guard? then withBlock s!"if ({g}) \{" do lowerBindable jpBody dest
          else lowerBindable jpBody dest
      return
    if jpVal.isAppOfArity ``C.ZStream.next_in 1 then
      let fused ← withLocalDeclD jpName declaredTy fun next => do
        let .letE countName countTy countVal scope _ := (body.instantiate1 next).consumeMData.headBeta | return false
        unless countTy.isConstOf ``UInt32 && countVal.isAppOfArity ``ite 5 do return false
        return ← withLocalDeclD countName countTy fun count => do
          let alloc := (scope.instantiate1 count).consumeMData.headBeta
          unless alloc.isAppOfArity ``C.withBPtrCell 3 && alloc.getAppArgs[1]! == next do return false
          bindCont alloc.appArg! fun cell computation => do
            unless ← isAddressedDispatchScope next cell computation do return false
            let computation := stripCursorLets computation
            let run := stripCursorLets computation.getAppArgs[4]!
            let frame := stripCursorLets run.getAppArgs[0]!
            unless frame.getAppArgs[0]! == next && frame.getAppArgs[1]! == count do return false
            let outside := computation.replace fun e => if e == frame then some (mkConst ``Unit.unit) else none
            if outside.containsFVar next.fvarId! || outside.containsFVar count.fvarId! then return false
            let initial ← lowerExpr jpVal
            let place ← fresh (← cell.getDecl).userName
            withBlock "{" do
              emit s!"unsigned char *{place} = {initial};"
              setVar cell [("", s!"(&{place})", "unsigned char **")]
              setVar next.fvarId! [("", place, "unsigned char *")]
              let countExpr ← lowerExpr countVal
              setVar count.fvarId! [("", countExpr, "unsigned")]
              let outer := (← get).pointerCells
              modify fun st => { st with pointerCells := outer.insert cell place }
              lowerBindable computation dest
              modify fun st => { st with pointerCells := outer }
            return true
      if fused then return
    let rhsTy := declaredTy
    if rhsTy.isConstOf `Zlib.Infback.DecoderCtx || rhsTy.isConstOf `Zlib.Inflate.Ctx then
      lowerBindable (body.instantiate1 jpVal) dest
      return
    if !body.hasLooseBVar 0 then lowerBindable (body.instantiate1 (mkFVar ⟨`__unused⟩)) dest; return
    if jpVal.isAppOfArity ``Array.replicate 3 then
      let vn ← fresh jpName; emit s!"{(← cType? jpVal.getAppArgs[0]!).getD "unsigned short"} {vn}[{← lowerExpr jpVal.getAppArgs[1]!}];"
      modify fun st => { st with stackArrays := st.stackArrays.insert vn }
      withLetVar jpName rhsTy body [] [("", vn)] (lowerBindable · dest); return
    if (rhsTy.isAppOfArity ``C.M 1 || rhsTy.isAppOfArity ``Zlib.GzFs.G 1 || rhsTy.isAppOfArity `Zlib.Inflate.X 1 || rhsTy.isAppOfArity ``C.PointerLocalM 1) && !stackTypes.any (fun (nm, _, _) => isStackTy rhsTy nm) then
      withLocalDeclD jpName rhsTy fun fv => do modify fun st => { st with letActions := st.letActions.insert fv.fvarId! jpVal }; lowerBindable (body.instantiate1 fv) dest
      return
    if ← isArrTy jpVal then
      let aes ← collectArrExprs jpVal
      if !aes.isEmpty then withLetVar jpName rhsTy body [] aes (lowerBindable · dest); return
    if (← cType? rhsTy).isNone || rhsTy.isAppOfArity ``Prod 2 || isLocalStruct (← getEnv) (rhsTy.getAppFn.constName?.getD .anonymous) then
      if let .fvar oldFv := stripMeta jpVal then
        let st ← get; if let some oldEntries := st.vars.get? oldFv then withLetVar jpName rhsTy body oldEntries ((st.arrVars.get? oldFv).getD []) (lowerBindable · dest); return
      if let some cEntries ← hasCdeclType rhsTy then
        lowerValueToVars jpVal cEntries
        withLetVar jpName rhsTy body cEntries (← collectArrExprs jpVal) (lowerBindable · dest); return
      if let some (_, fldArgs) ← localStructArgs? (stripMeta jpVal) then
        let mut entries : List VarEntry := []; let mut arrs : List (String × String) := []
        for (f, a) in fldArgs do
          if ← isArrTy a then arrs := arrs ++ [(f.toString, ((← collectArrExprs a).head?.map (·.2)).getD (← lowerExpr a))]
          else
            let mut v ← if (stripMeta a).getAppFn.isConstOf ``Inhabited.default then pure "__default" else lowerExpr a
            if v != "__default" && hasSubstr v " " then if let some ct ← cType? (← inferType a) then
              let vn ← fresh f; emitTemporary ct vn (some v); modify fun st => { st with mutLocals := (vn, ct) :: st.mutLocals }; v := vn
            entries := entries ++ [(f.toString, v, "")]
        withLetVar jpName rhsTy body entries arrs (lowerBindable · dest); return
    if (← whnfR rhsTy).isAppOfArity ``Prod 2 then
      let parts ← allocVars rhsTy jpName
      lowerValueToVars jpVal parts
      withLetVar jpName rhsTy body parts (k := (lowerBindable · dest))
      return
    let v ← lowerExpr jpVal
    let some ct ← cType? rhsTy | throwError m!"unsupported pure let type {rhsTy}"
    let nameHint := cIdent jpName
    let vn ← if (← get).mutLocals.any (· == (nameHint, ct)) then do
      if v != nameHint then emit s!"{nameHint} = {v};"
      pure nameHint
    else (do let vn ← fresh jpName; emitTemporary ct vn (some v); modify fun s => { s with mutLocals := (vn, ct) :: s.mutLocals }; pure vn)
    withLetVar jpName rhsTy body [(nameHint, vn, ct)] (k := (lowerBindable · dest)); return
  if e.getAppFn.isFVar then
    let fv := e.getAppFn.fvarId!
    if let some rhs := (← get).letActions.get? fv then lowerBindable (if e.getAppArgs.isEmpty then rhs else mkAppN rhs e.getAppArgs) dest; return
    if let some (jpArgs, hasUnit) := (← get).joins.get? fv then
      let args := if hasUnit then e.getAppArgs.toList.tail! else e.getAppArgs.toList
      let prev := ((← get).joinArrs.get? fv).getD (jpArgs.map fun _ => []); let mut merged : List (List (String × String)) := []
      for ((entries, arg), prevA) in (jpArgs.zip args).zip prev do
        lowerValueToVars arg entries; let cur ← collectArrExprs arg; merged := merged ++ [if prevA.isEmpty then cur else prevA]
      modify fun st => { st with joinArrs := st.joinArrs.insert fv merged }
      if let some label := (← get).caseJoins.get? fv then emit s!"goto {label};"
      if let some g := (← get).joinGuards.get? fv then emit s!"{g} = 1;"
      return
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let (scrut, cases, defArm) ← collectSwitch none e
    -- A synthesized switch would capture a break intended for the enclosing loop.
    let canSwitch := match dest with | .loopStep .. => false | _ => true
    if canSwitch && (← get).breakVar?.isNone && cases.length >= 3 then
      let lexicalBranches := (← get).inInflateDispatch
      if lexicalBranches then
        modify fun st => { st with inInflateDispatch := false }
        for (_, e) in cases do
          let arm := e.consumeMData.headBeta
          if arm.getAppNumArgs == 1 && arm.getAppFn.isConst &&
              (← inferType arm.appArg!).isConstOf `Zlib.Inflate.Ctx &&
              (← inferType arm).isAppOfArity `Zlib.Inflate.X 1 then
            unless (← get).sharedCases.any (fun (act, _) => act == arm) do
              let label ← fresh `case_body
              modify fun st => { st with sharedCases := st.sharedCases.push (arm, label) }
      withBlock s!"switch ({scrut}) \{" do
        modify fun st => { st with indent := st.indent - 1 }
        for (lit, arm) in cases do
          emit s!"case {lit}:"
          modify fun st => { st with indent := st.indent + 1 }
          let candidate := arm.consumeMData.headBeta
          let hereState ← get
          let existing := if lexicalBranches then hereState.sharedCases.find? (fun (a, _) => a == candidate)
            else if hereState.decoderCursor.isSome && candidate.isAppOfArity `Zlib.Infback.sharedCase 1 then
            hereState.sharedCases.find? (fun (body, _) => body == candidate.appArg!)
          else none
          if let some (body, label) := existing then
            if !(← get).placedCases.contains label then
              modify fun st => { st with placedCases := st.placedCases.insert label }
              withBlock (label ++ ": {") do
                if lexicalBranches then
                  let some action ← unfoldDefinition? body | throwError m!"cannot lower decoder case {body}"
                  lowerBindable action.headBeta dest
                else lowerBindable body .unit
            else emit s!"goto {label};"
          else lowerBindable arm dest
          let lastT := ((← get).lines.back?.map fun l => l.trimAsciiStart.toString).getD ""
          if !(lastT == "return;" || lastT.startsWith "return " || lastT == "break;" || lastT == "continue;" || lastT.startsWith "goto ") then emit "break;"
          modify fun st => { st with indent := st.indent - 1 }
        let nBefore := (← get).lines.size; emit "default:"; modify fun st => { st with indent := st.indent + 1 }; lowerBindable defArm dest
        modify fun st => { st with indent := st.indent - 1 }
        if (← get).lines.size == nBefore + 1 then modify fun st => { st with lines := st.lines.pop }
        modify fun st => { st with indent := st.indent + 1 }
      return
    let a := e.getAppArgs; let arm (x : Expr) := if e.isAppOfArity ``dite 5 then x.beta #[mkConst ``Unit.unit] else x
    if !a[1]!.hasFVar && !mentionsPosixOrRef a[1]! then if let some b ← evalPureBool? a[1]! then lowerBindable (arm (if b then a[3]! else a[4]!)) dest; return
    if isUbTerm a[3]! then lowerBindable (arm a[4]!) dest; return else if isUbTerm a[4]! then lowerBindable (arm a[3]!) dest; return
    let cond ← lowerExpr a[1]!; modify fun s => { s with inCondFlag := cond }; withBlock s!"if ({cond}) \{" do lowerBindable a[3]! dest
    let elseArm := stripMeta a[4]!; let joinsMap := (← get).joins
    if !(elseArm.isConstOf ``Unit.unit || match elseArm with | .fvar fv => (joinsMap.get? fv).any (·.1.all (·.isEmpty)) | _ => false) then
      let nBefore := (← get).lines.size; withBlock "else {" do lowerBindable a[4]! dest
      if (← get).lines.size == nBefore + 2 then modify fun st => { st with lines := st.lines.extract 0 nBefore }
    return
  let eFn := e.getAppFn.constName?
  if eFn == some ``C.Ptr.memcpy || eFn == some ``C.Ptr.fill then
    let a := e.getAppArgs
    let isByte := a[0]!.isConstOf ``C.BRef && a[1]!.isConstOf ``UInt8
    let isWord := a[0]!.isConstOf ``C.WRef && a[1]!.isConstOf ``UInt16
    unless isByte || isWord do
      throwError m!"array operation needs a C element representation: {a[0]!}, {a[1]!}"
    let dst ← lowerExpr a[a.size - 3]!
    let src := a[a.size - 2]!
    let count ← lowerExpr a.back!
    let byteCount := if isByte then count else s!"(({count}) * sizeof(unsigned short))"
    if eFn == some ``C.Ptr.memcpy then
      emit s!"memcpy({dst}, {← lowerExpr src}, {byteCount});"
    else
      unless isByte || isNatLitVal src 0 do
        throwError m!"word fill requires an element store for a nonzero value: {src}"
      emit s!"memset({dst}, {← lowerExpr src}, {byteCount});"
    return
  if eFn ∈ [some ``C.copyZStream, some ``C.copyInflateState, some ``C.copyDeflateState] then
    let args := e.getAppArgs
    let dst ← lowerExpr args[0]!
    emit s!"memcpy({dst}, {← lowerExpr args[1]!}, sizeof(*({dst})));"
    return
  let memCall := match eFn with
    | some ``C.memcpyB => some "memcpy"
    | some ``C.memmoveB => some "memmove"
    | some ``C.memsetB => some "memset"
    | _ => none
  if let some fn := memCall then
    let a := e.getAppArgs
    emit s!"{fn}({← lowerExpr a[a.size-3]!}, {← lowerExpr a[a.size-2]!}, {← lowerExpr a.back!});"
    return
  if e.isAppOfArity ``C.memcpyStore64 2 then
    let a' := e.getAppArgs; let dstS ← lowerExpr a'[0]!; let vS ← lowerExpr a'[1]!
    if !hasSubstr vS " " && !vS.startsWith "(" then emit s!"memcpy({dstS}, &{vS}, 8);"
    else do let tmp ← fresh `v; emit s!"unsigned long {tmp} = {vS};"; emit s!"memcpy({dstS}, &{tmp}, 8);"
    return
  if let some (true, sn) := eFn.bind structAct? then
    if e.getAppNumArgs == 2 then
      let dst ← lowerExpr e.getAppArgs[0]!
      let value := e.getAppArgs[1]!.headBeta
      if value.isConstOf ``C.InflateState.zeroed || value.isConstOf ``C.DeflateState.zeroed then
        emit s!"memset({dst}, 0, sizeof(*({dst})));"
      else
        emitStructDiff dst "" sn value
      return
  if eFn == some ``C.Ptr.store && e.getAppNumArgs >= 4 && e.getAppArgs[1]!.isConstOf ``C.Code then
    let a' := e.getAppArgs; let rhs := (stripMeta a'.back!).headBeta
    if rhs.isAppOfArity ``C.Code.mk 3 then emitStructDiff (← lowerExpr a'[a'.size-2]!) "" ``C.Code rhs
    else emit s!"*{← lowerExpr a'[a'.size-2]!} = {← lowerExpr a'.back!};"
    return
  if let some want := eFn.bind ptrWidthType? then
    if e.getAppNumArgs >= 2 then let a' := e.getAppArgs; emit s!"*{← asTypedPtrExpr a'[0]! (← lowerExpr a'[0]!) want} = {← lowerExpr a'[1]!};"; return
  if eFn == some ``C.Ptr.store || eFn == some ``C.store8 then
    let a' := e.getAppArgs; emit s!"*{← lowerBytePtr a'[a'.size-2]! (eFn == some ``C.store8 || (a'.size >= 1 && a'[0]!.isConstOf ``C.BRef))} = {← lowerExpr a'.back!};"; return
  if eFn == some ``C.UInt32Cell.write then
    emit s!"*{← lowerExpr e.getAppArgs[0]!} = {← lowerExpr e.getAppArgs[1]!};"
    return
  if eFn == some ``Zlib.Trees.heapPush || eFn == some ``Zlib.Trees.heapSave ||
      eFn == some ``Zlib.Trees.heapReplaceRoot || eFn == some ``Zlib.Trees.put_symbol_byte then
    let args := e.getAppArgs
    let argument (e : Expr) (ct : String) (hint : Name) : M String := do
      let text ← lowerExpr e
      if !text.isEmpty && text.toList.all (fun c => c.isAlphanum || c == '_') then return text
      let localName ← fresh hint
      emit s!"{ct} {localName} = {text};"
      return localName
    let state ← argument args[0]! "deflate_state *" `heap_state
    if eFn == some ``Zlib.Trees.put_symbol_byte then
      let value ← argument args[1]! "unsigned char" `symbol_byte
      emit s!"{state}->sym_buf[{state}->sym_next++] = {value};"
    else if eFn == some ``Zlib.Trees.heapReplaceRoot then
      emit s!"{state}->heap[1] = {state}->heap[{state}->heap_len--];"
    else
      let node ← argument args[1]! "int" `heap_node
      let index := if eFn == some ``Zlib.Trees.heapPush then s!"++{state}->heap_len" else s!"--{state}->heap_max"
      emit s!"{state}->heap[{index}] = {node};"
    return
  if eFn == some `Zlib.Trees.setFc || eFn == some `Zlib.Trees.setDl then
    let args := e.getAppArgs
    let field := if eFn == some `Zlib.Trees.setFc then "fc.freq" else "dl.len"
    emit s!"{← lowerExpr args[0]!}[{← lowerExpr args[1]!}].{field} = {← lowerExpr args[2]!};"
    return
  if eFn == some ``Zlib.GzFs.vaEnd then
    emit s!"va_end({← lowerExpr e.getAppArgs[0]!});"
    return
  if eFn == some ``Zlib.GzFs.setErrno then
    emit s!"errno = {← lowerExpr e.getAppArgs[0]!};"
    return
  if eFn == some ``Zlib.GzFs.fsFcntl then
    let fdv ← lowerExpr e.getAppArgs.back!
    emit (if hasSubstr (← get).inCondFlag "O_NONBLOCK" then s!"fcntl({fdv}, F_SETFL, fcntl({fdv}, F_GETFL) | O_NONBLOCK);" else s!"fcntl({fdv}, F_SETFD, fcntl({fdv}, F_GETFD) | FD_CLOEXEC);"); return
  if eFn == some ``Zlib.GzFs.snprintf then emit s!"{← lowerSnprintf e.getAppArgs};"; return
  if e.isAppOfArity ``ForIn.forIn 8 then
    let fa := e.getAppArgs; let range := stripMeta fa[5]!
    if range.isAppOfArity ``Std.Legacy.Range.mk 4 then
      let ra := range.getAppArgs; let stTy := fa[4]!
      let sVars : List VarEntry ← match dest with
        | .vars vs => if vs.isEmpty then pure [] else lowerValueToVars fa[6]! vs; pure vs
        | _ => if stTy.isConstOf ``PUnit || stTy.isConstOf ``Unit then pure [] else let vs ← allocVars stTy `v; lowerValueToVars fa[6]! vs; pure vs
      let idxVar ← fresh `i
      let label ← fresh `range_end
      let saved ← get
      modify fun st => { st with breakVar? := none, rangeExit? := some (label, false) }
      withBlock s!"for (unsigned long {idxVar} = {← lowerExpr ra[0]!}; {idxVar} < {← lowerExpr ra[1]!}; {idxVar} += {← lowerExpr ra[2]!}) \{" do
        lambdaBoundedTelescope fa[7]! 2 fun xs fBody => do
          let curSt ← get; set { curSt with vars := (curSt.vars.insert xs[0]!.fvarId! [("", idxVar, "unsigned long")]).insert xs[1]!.fvarId! sVars }
          lowerBindable fBody (if sVars.isEmpty then .unit else .vars sVars)
      if (← get).rangeExit?.any Prod.snd then emit s!"{label}: ;"
      modify fun st => { st with breakVar? := saved.breakVar?, rangeExit? := saved.rangeExit? }
      return
  if e.isAppOfArity ``C.cforEverRet 5 then
    let w := e.getAppArgs; let (loopVars, loopArrs) ← getLoopVars w[0]! w[3]! `s
    let retD := (← get).fnRetDest
    withBlock "for (;;) {" do
      withStateFn w[0]! (stripMeta w[2]!) loopVars loopArrs fun b => lowerBindable b (.loopStep loopVars retD)
    withStateFn w[0]! (stripMeta w[4]!) loopVars loopArrs fun b => lowerBindable b dest
    return
  if e.isAppOfArity ``C.cwhileRet 6 || e.isAppOfArity ``Zlib.GzFs.gwhileRet 6 || e.isAppOfArity ``Zlib.GzFs.gdoWhileRet 6 then
    let w := e.getAppArgs
    let isDo := e.isAppOfArity ``Zlib.GzFs.gdoWhileRet 6
    let (vs, arrs) ← getLoopVars w[0]! w[4]! `s
    lowerControlledLoop lowerBindable isDo w[0]! (stripMeta w[if isDo then 3 else 2]!)
      (stripMeta w[if isDo then 2 else 3]!) vs arrs (← get).fnRetDest
    withStateFn w[0]! (stripMeta w[5]!) vs arrs fun b => lowerBindable b dest
    return
  if e.isAppOfArity ``C.cwhileBrk 4 || e.isAppOfArity ``Zlib.GzFs.gwhileBrk 4 || isDoWhileBrk e then
    let w := e.getAppArgs
    let isDo := isDoWhileBrk e
    let (loopVars, loopArrs) ← getLoopVars w[0]! w[3]! `s
    lowerControlledLoop lowerBindable isDo w[0]! (stripMeta w[if isDo then 2 else 1]!)
      (stripMeta w[if isDo then 1 else 2]!) loopVars loopArrs (← get).fnRetDest
    match dest with
    | .unit | .modeTail _ => pure ()
    | .vars targetVs =>
      for ((_, d, _), (_, s, _)) in pairVars loopVars targetVs do if d != s && s != "__default" then emit s!"{d} = {s};"
    | _ => withLocalDeclD `result w[0]! fun fv => do
      setVar fv.fvarId! loopVars loopArrs
      lowerBindable fv dest
    modify fun st => { st with lastArrs := loopArrs }
    return
  if e.isAppOfArity ``C.clabel 5 then
    let w := e.getAppArgs
    let lbl := match stripMeta w[2]! with | .lit (.strVal s) => s | _ => "lbl"
    let (stateVars, stateArrs) ← getLoopVars w[0]! w[4]! `s
    emitLabel lbl
    withStateFn w[0]! (stripMeta w[3]!) stateVars stateArrs fun b => lowerBindable b (.gotoStep lbl stateVars dest)
    return
  if e.isAppOfArity ``C.cforwardLabel 6 then
    let w := e.getAppArgs
    let lbl := match stripMeta w[2]! with | .lit (.strVal s) => s | _ => "leave"
    let stateVars ← match ← hasCdeclType w[0]! with | some vs => pure vs | none => allocVars w[0]! `s
    lowerBindable w[3]! (.fwdStep lbl stateVars)
    withStateFn w[0]! (stripMeta w[4]!) stateVars [] fun b => lowerBindable b (.vars stateVars)
    emitLabel lbl
    withStateFn w[0]! (stripMeta w[5]!) stateVars [] fun b => lowerBindable b dest
    return
  if e.isAppOfArity ``Bind.bind 6 then
    let a := e.getAppArgs; let st ← get; let rawAct := stripMeta a[4]!
    let act0 := match rawAct.getAppFn with | .fvar fv => (match st.letActions.get? fv with | some rhs => if rawAct.getAppArgs.isEmpty then rhs else mkAppN rhs rawAct.getAppArgs | none => rawAct) | _ => rawAct
    let cont := a[5]!; let act0Ty ← inferType act0
    if act0.isAppOfArity `Zlib.Inflate.updatewindow 3 then
      let direct ← bindCont cont fun id body => do
        let e := stripCursorLets body
        unless e.isAppOfArity ``ite 5 && !e.getAppArgs[3]!.containsFVar id &&
            !e.getAppArgs[4]!.containsFVar id do return false
        let cond := stripMeta e.getAppArgs[1]!
        unless cond.isAppOfArity ``Eq 3 && cond.appArg!.isConstOf ``Bool.true do return false
        let compare := stripMeta cond.getAppArgs[1]!
        unless compare.isAppOf ``bne && compare.getAppNumArgs >= 2 &&
            compare.getAppArgs[compare.getAppNumArgs - 2]!.fvarId? == some id &&
            isNatLitVal compare.appArg! 0 do return false
        setVar id [("", ← lowerExpr act0, "int")]
        lowerBindable body dest
        return true
      if direct then return
    if act0.isAppOfArity `Zlib.Inflate.rejectsInput 1 then
      let ptr := stripMeta act0.appArg!
      if ptr.isFVar then
        let done ← bindCont cont fun id body => do
          let e := stripCursorLets body
          unless e.isAppOfArity ``ite 5 && !e.getAppArgs[3]!.containsFVar id &&
              !e.getAppArgs[4]!.containsFVar id do return false
          let test := stripMeta e.getAppArgs[1]!
          unless test.isAppOfArity ``Eq 3 && test.getAppArgs[1]!.fvarId? == some id &&
              test.appArg!.isConstOf ``Bool.true do return false
          let strm ← lowerExpr ptr
          let predicate := s!"(inflateStateCheck({strm}) || ({strm})->next_out == 0 || (({strm})->next_in == 0 && ({strm})->avail_in != 0))"
          setVar id [("", predicate, "int")]
          lowerBindable body dest
          return true
        if done then return
      let some expanded ← unfoldDefinition? act0 | throwError "cannot unfold public decoder guard"
      lowerBindable (mkAppN e.getAppFn (a.set! 4 expanded.headBeta)) dest
      return
    if let some (regs, _) := st.decoderFrame then
      if act0.isAppOfArity `Zlib.Inflate.invalidHeaderWord 1 then
        let state ← lowerExpr act0.appArg!
        let word := s!"((((unsigned){regs}.hold & ((1U << 8) - 1U)) << 8) + ({regs}.hold >> 8))"
        let value := s!"(!(({state})->wrap & 1) || {word} % 31)"
        let direct ← bindCont cont fun id body => do
          unless readsBeforeEffects id body do return false
          setVar id [("", value, "int")]
          lowerBindable body dest
          return true
        if direct then return
        let some expanded ← unfoldDefinition? act0 | throwError "cannot unfold header check"
        lowerBindable (mkAppN e.getAppFn (a.set! 4 expanded.headBeta)) dest
        return
      if act0.isAppOfArity `Zlib.Inflate.hcrcOn 1 then
        let ptr := stripMeta act0.appArg!
        let base := (← constructorProjection? ptr).getD ptr
        if base.isFVar then
          let done ← bindCont cont fun id body => do
            unless readsBeforeEffects id body do return false
            let state ← lowerExpr base
            setVar id [("", s!"((({state})->flags & 0x0200) && (({state})->wrap & 4))", "int")]
            lowerBindable body dest
            return true
          if done then return
        let some expanded ← unfoldDefinition? act0 | throwError "cannot unfold gzip checksum guard"
        lowerBindable (mkAppN e.getAppFn (a.set! 4 expanded.headBeta)) dest
        return
      if st.decoderCursor.isSome && act0.isAppOfArity `Zlib.Inflate.rdS 3 then
        let source := act0.getAppArgs
        let isWidth ← bindCont source[2]! fun id v => isDefEq v (mkApp (mkConst ``C.InflateState.wsize) (mkFVar id))
        if isWidth then
          let used ← bindCont cont fun id tail => do
            let (call, rest) := (bindParts? tail).map (fun (c,k) => (c,some k)) |>.getD (tail,none)
            let call := if call.isAppOfArity ``liftM 5 then call.appArg! else call
            unless call.isAppOfArity `Zlib.Inffast.inflate_fast 2 && call.appArg!.fvarId? == some id &&
                !(rest.any (·.containsFVar id)) do return false
            let ptr := stripMeta source[1]!
            let simple := (← constructorProjection? ptr).getD ptr
            unless simple.isFVar do return false
            setVar id [("", s!"({← lowerExpr simple})->wsize", "unsigned")]
            lowerBindable tail dest
            return true
          if used then return
      let guardAct := if act0.isAppOfArity ``liftM 5 then stripMeta act0.appArg! else act0
      if guardAct.isAppOfArity `Zlib.Inflate.rdS 3 || guardAct.isAppOf ``C.Ptr.index then
        let inGuard ← bindCont cont fun id body => do
          let e := stripCursorLets body
          unless e.isAppOfArity ``ite 5 do return false
          let args := e.getAppArgs
          let cond := stripMeta args[1]!
          let cond := if cond.isAppOfArity ``Eq 3 && cond.appArg!.isConstOf ``Bool.true then
            stripMeta cond.getAppArgs[1]! else cond
          unless (cond.isAppOf ``BEq.beq || cond.isAppOf ``Eq) && cond.getAppNumArgs >= 2 &&
              cond.getAppArgs[cond.getAppNumArgs - 2]!.fvarId? == some id &&
              !cond.appArg!.containsFVar id && !args[3]!.containsFVar id && !args[4]!.containsFVar id do return false
          let some ct ← cType? (← id.getDecl).type | return false
          let rhs ← if guardAct.isAppOf ``C.Ptr.index then some <$> lowerExpr guardAct
            else do
              let a := guardAct.getAppArgs
              let field ← bindCont a[2]! fun state value => do
                for field in [`mode, `«have», `havedict, `wrap, `last] do
                  if ← isDefEq value (mkApp (mkConst (``C.InflateState ++ field)) (mkFVar state)) then
                    return some field
                return none
              if let some field := field then pure (some s!"({← lowerExpr a[1]!})->{field}") else pure none
          let some rhs := rhs | return false
          setVar id [("", rhs, ct)]
          lowerBindable body dest
          return true
        if inGuard then return
      if (st.decoderCursor.isSome || st.inInflateDispatch) && act0.isAppOfArity `Zlib.Inflate.rdS 3 then
        let source := act0.getAppArgs
        let mode ← bindCont source[2]! fun id value =>
          isDefEq value (mkApp (mkConst ``C.InflateState.mode) (mkFVar id))
        if mode then
          let direct ← bindCont cont fun id body => do
            if !modeSwitchOnly id body 0 then return false
            let ptr ← lowerExpr source[1]!
            setVar id [("", s!"({ptr})->mode", "unsigned")]
            let old := (← get).selectedRecord
            let sourcePtr := stripMeta source[1]!
            let base := (← constructorProjection? sourcePtr).getD sourcePtr
            modify fun state => { state with selectedRecord := base.fvarId? }
            lowerBindable body dest
            modify fun state => { state with selectedRecord := old }
            return true
          if direct then return
      if act0.isAppOfArity `Zlib.Inflate.BITS 1 then
        let count ← lowerExpr act0.appArg!
        let value := s!"((unsigned){regs}.hold & ((1U << ({count})) - 1U))"
        bindCont cont fun id body => do
          let reduced := stripCursorLets body
          let parts := bindParts? reduced
          let immediateState := parts.any fun (call, tail) =>
            let call := if call.isAppOfArity ``liftM 5 then stripMeta call.appArg! else call
            call.isAppOfArity `Zlib.Inflate.wrS 2 && !call.getAppArgs[0]!.containsFVar id && !tail.containsFVar id
          let immediateGuard := (reduced.isAppOfArity ``ite 5 || reduced.isAppOfArity ``dite 5) &&
            !reduced.getAppArgs[3]!.containsFVar id && !reduced.getAppArgs[4]!.containsFVar id
          let immediateMatch := (← matchMatcherApp? reduced).any fun m =>
            m.discrs.size == 1 && m.discrs[0]!.fvarId? == some id && !m.alts.any (·.containsFVar id)
          let constant := natLitOf? (stripMeta act0.appArg!)
          let inlineWidth := constant.any (· < 32)
          if inlineWidth && (immediateGuard || immediateState || immediateMatch) then
            setVar id [("", value, "unsigned")]
            lowerBindable body dest
            return
          let name ← fresh (← id.getDecl).userName
          emitTemporary "unsigned" name (some value)
          setVar id [("", name, "unsigned")]
          lowerBindable body dest
        return
    if act0.isAppOfArity `Zlib.Inflate.appendLength 5 ||
        (st.decoderFrame.isSome && (act0.isConstOf `Zlib.Inflate.absorbInputByte ||
          act0.isAppOfArity `Zlib.Inflate.LOAD 2 || act0.isAppOfArity `Zlib.Inflate.RESTORE 2 || act0.isAppOfArity `Zlib.Inflate.setRepeatCount 2 || act0.isAppOfArity `Zlib.Infback.setRepeatCount 2 || act0.isAppOfArity `Zlib.Inflate.setPreviousLength 1 || act0.isAppOfArity `Zlib.Infback.setPreviousLength 1 || act0.isAppOfArity `Zlib.Inflate.appendCurrentCode 1 || act0.isAppOfArity `Zlib.Infback.appendCurrentCode 1 || act0.isAppOfArity `Zlib.Inflate.repeatCodeLength 1 || act0.isAppOfArity `Zlib.Infback.backMatch 1 || act0.isAppOfArity `Zlib.Infback.extendExtra 2 || act0.isAppOfArity `Zlib.Infback.emitLiteral 1 || act0.isAppOfArity `Zlib.Inflate.emitLiteral 1 || act0.isAppOfArity `Zlib.Inflate.consumeCodeWidth 2 || act0.isAppOfArity `Zlib.Inflate.addExtra 2 || act0.isAppOfArity `Zlib.Inflate.countDictionaryInput 1 || act0.isAppOfArity `Zlib.Inflate.readHeaderString 2 || act0.isAppOfArity `Zlib.Inflate.accountCheckedOutput 2 || act0.isAppOfArity `Zlib.Inflate.copyHeaderExtra 1 || act0.isConstOf `Zlib.Inflate.windowBitsFromHeader || act0.isAppOfArity `Zlib.Inflate.setWindowLimit 1 || act0.isAppOfArity `Zlib.Inflate.resetHeaderCheck 1 || act0.isAppOfArity `Zlib.Inflate.updateHeader 2 || act0.isAppOfArity `Zlib.Inflate.storeHeaderWord 2 || act0.isAppOfArity `Zlib.Inflate.CRC2 1 || act0.isAppOfArity `Zlib.Inflate.CRC4 1 || act0.isAppOfArity `Zlib.Inflate.storeDictId 2 || act0.isAppOfArity `Zlib.Inflate.startDataCheck 3 || act0.isAppOfArity `Zlib.Inflate.lookup1 2 || act0.isAppOfArity `Zlib.Inflate.lookup2 2 || act0.isAppOfArity `Zlib.Infback.lookup1 2 || act0.isAppOfArity `Zlib.Infback.lookup2 2 || act0.isAppOfArity `Zlib.Inflate.startLengthTable 1 || act0.isAppOfArity `Zlib.Inflate.storeOrderedLength 2 || act0.isAppOfArity `Zlib.Infback.storeOrderedLength 2 || act0.isAppOfArity `Zlib.Infback.copyStoredInput 1 || act0.isAppOfArity `Zlib.Inflate.copyStoredInput 1 || act0.isConstOf `Zlib.Inflate.copyMatchBytes || act0.isAppOfArity `Zlib.Inflate.DROPBITS 1 ||
          act0.isConstOf `Zlib.Inflate.BYTEBITS)) then
      lowerBindable act0 .unit
      bindCont cont fun id body => do
        setVar id []
        lowerBindable body dest
      return
    if ← lowerCallOperand? lowerBindable act0 cont dest then return
    if ← lowerStateAllocator? lowerBindable act0 cont dest then return
    if act0.isAppOfArity `Zlib.Inflate.allocLocalB 1 then
      let some count := natLitOf? act0.appArg! | throwError "expected a constant automatic array size"
      if count == 0 then throwError "C automatic byte array must have positive size"
      bindCont cont fun id body => do
        let computation ← localBytesBody body id
        withBlock "{" do
          let name ← fresh (← id.getDecl).userName
          emit s!"unsigned char {name}[{count}];"
          setVar id [("", name, "unsigned char *")]
          lowerBindable computation dest
      return
    if let some entries ← lowerOutCall? act0 then
      bindCont cont fun id body => do
        setVar id entries
        lowerBindable body dest
      return
    if ← lowerInflateRun? lowerBindable act0 cont dest then return
    if act0.isAppOfArity `Zlib.Infback.runBackModesFrom 2 then
      let args := act0.getAppArgs
      let regs ← fresh `registers
      let leave ← fresh `inf_leave
      let ty := cStructName `Zlib.Inflate.IL
      let initial ← whnf args[0]!
      let saved := (← get).decoderFrame
      let outerCases := (← get).sharedCases
      let outerReturn := (← get).decoderReturn
      let outerCursor := (← get).decoderCursor
      let mut cursor := none
      let action := stripMeta args[1]!
      if action.isAppOfArity `Zlib.Infback.back_dispatch 1 then
        let ctx := stripMeta action.appArg!
        if ctx.isAppOfArity `Zlib.Infback.addressedCtx 7 then
          if let some id := ctx.getAppArgs[2]!.fvarId? then
            if let some place := (← get).pointerCells.get? id then
              cursor := some (id, place)
      let seed := stripCursorLets args[0]!
      if let some (_, place) := cursor then
        unless seed.getAppFn.constName?.map privateToUserName == some `Zlib.Infback.backRegisters &&
            seed.getAppNumArgs == 4 do throwError "expected the initial back registers"
        let a := seed.getAppArgs
        let empty ← whnf (mkConst `Zlib.Inflate.IL.init)
        emit s!"{ty} {regs} = {← lowerExpr empty};"
        let next ← lowerExpr a[0]!
        if place != next then emit s!"{place} = {next};"
        emit s!"{regs}.have_ = {← lowerExpr a[1]!};"
        emit s!"{regs}.hold = 0;"
        emit s!"{regs}.bits = 0;"
        emit s!"{regs}.put = {← lowerExpr a[2]!};"
        emit s!"{regs}.left = {← lowerExpr a[3]!};"
      else
        emit s!"{ty} {regs} = {← lowerExpr initial};"
      modify fun st => { st with decoderFrame := some (regs, leave), decoderReturn := none, decoderCursor := cursor, sharedCases := #[] }
      withBlock "for (;;) {" do
        lowerBindable args[1]! (.modeTail (← getLCtx))
        let placed := (← get).placedCases
        let cases := (← get).sharedCases.filter (fun (_, lbl) => !placed.contains lbl)
        if !cases.isEmpty then
          emit "continue;"
          for (target, label) in cases do
            withBlock (label ++ ": {") do
              lowerBindable target .unit
              emit "continue;"
      modify fun st => { st with sharedCases := outerCases }
      emit s!"{leave}: ;"
      modify fun st => { st with decoderFrame := saved, decoderReturn := outerReturn, decoderCursor := outerCursor }
      bindCont cont fun id body => do
        if let some (cell, place) := cursor then
          let exit := stripCursorLets body
          if let .ret false := dest then
            if exit.isAppOfArity `Zlib.Infback.finishBack 6 then
              let finish := exit.getAppArgs
              if finish[2]!.fvarId? == some cell && finish[5]!.fvarId? == some id then
                let stream ← lowerExpr finish[0]!
                let state ← lowerExpr finish[1]!
                let deliver ← lowerExpr finish[3]!
                let desc ← lowerExpr finish[4]!
                let endCode ← lowerExpr (mkConst `C.Z_STREAM_END)
                let failCode ← lowerExpr (mkConst `C.Z_BUF_ERROR)
                withBlock s!"if ({regs}.left < ({state})->wsize) \{" do
                  withBlock s!"if ({deliver}({desc}, ({state})->window, ({state})->wsize - {regs}.left) && {regs}.ret == {endCode}) \{" do
                    emit s!"{regs}.ret = {failCode};"
                emit s!"({stream})->next_in = {place};"
                emit s!"({stream})->avail_in = {regs}.have_;"
                emit s!"return {regs}.ret;"
                return
          emit s!"{regs}.next = {place};"
        setVar id [("", regs, ty)]
        lowerBindable body dest
      return
    if let some (regs, _) := (← get).decoderFrame then
      if act0.isAppOf ``MonadState.get && act0.getAppArgs[0]!.isConstOf `Zlib.Inflate.IL then
        bindCont cont fun id body => do
          if consumesRegisterNow id body then
            let env ← getEnv
            let fields := getStructureFields env `Zlib.Inflate.IL
            let safe := #[`left, `have_, `bits, `hold, `copy, `len, `out_]
            let rest := body.replace fun sub =>
              let field := match sub with
                | .proj `Zlib.Inflate.IL idx (.fvar fv) => if fv == id then fields[idx]? else none
                | .app (.const fn _) (.fvar fv) =>
                  if fv == id && fn.getPrefix == `Zlib.Inflate.IL && env.isProjectionFn fn
                  then some (Name.mkSimple (cIdent fn)) else none
                | _ => none
              if field.any safe.contains then some (mkConst ``Unit.unit) else none
            if !rest.containsFVar id then
              setVar id [("", regs, cStructName `Zlib.Inflate.IL)]
              lowerBindable body dest
              return
          if let some field := soleRegisterField? (← getEnv) id body then
            let value := mkApp (mkConst (`Zlib.Inflate.IL ++ field)) (mkFVar id)
            if let some ct ← cType? (← inferType value) then
              let cursor := (← get).decoderCursor.map Prod.snd
              let rhs := if field == `next then cursor.getD (regs ++ ".next") else s!"{regs}.{field}"
              if field ∈ [`here, `last] then
                if ← codeUsedWhileLive id field body then
                  setVar id [(field.toString, rhs, ct)]
                  let body := match body.consumeMData.headBeta with
                    | .letE _ _ value rest _ =>
                      if value.containsFVar id && !value.isLambda then rest.instantiate1 value else body
                    | _ => body
                  lowerBindable body dest
                  return
              if field ∈ [`hold, `bits, `left, `have_, `len, `copy] && consumesRegisterNow id body then
                setVar id [(field.toString, rhs, ct)]
                lowerBindable body dest
                return
              let snapshot ← fresh field
              emitTemporary ct snapshot (some rhs)
              setVar id [(field.toString, snapshot, ct)]
              lowerBindable body dest
              return
          let vn ← fresh (← id.getDecl).userName
          let ty := cStructName `Zlib.Inflate.IL
          emit s!"{ty} {vn} = {regs};"
          if let some (_, place) := (← get).decoderCursor then emit s!"{vn}.next = {place};"
          setVar id [("", vn, ty)]
          modify fun st => { st with immutableRecords := st.immutableRecords.insert id }
          lowerBindable body dest
        return
    if let .gotoStep _ _ outerDone := dest then
      let isWrapDone ← bindCont cont fun xId cb => do
        let s := stripMeta cb
        return s.isAppOfArity ``C.GotoStep.done 3 && (stripMeta s.getAppArgs[2]!) == .fvar xId
      if isWrapDone then
        lowerBindable act0 outerDone
        return
    for (stkNm, cDecl, ptrTy) in stackTypes do
      if isStackTy act0Ty stkNm then
        bindCont cont fun xId cb => do let vn ← fresh (← xId.getDecl).userName; emit s!"{cDecl} {vn};"; setVar xId [("", s!"(&{vn})", ptrTy)]; modify fun s => { s with stackFVars := s.stackFVars.insert xId }; lowerBindable cb dest
        return
    if act0.getAppFn.isConstOf ``C.stackAddr && act0.getAppArgs.size >= 5 then
      let addrExpr ← lowerExpr act0; bindCont cont fun xId cb => do setVar xId [(cIdent (← xId.getDecl).userName, addrExpr, "unsigned char *")]; modify fun s => { s with stackFVars := s.stackFVars.insert xId }; lowerBindable cb dest
      return
    if act0.isAppOfArity ``Zlib.Trees.nextCodeBelow 2 then
      let args := act0.getAppArgs
      let code ← fresh `code
      let node ← fresh `node
      emit s!"int {code} = {← lowerExpr args[0]!};"
      emit s!"int {node} = {code} < {← lowerExpr args[1]!} ? ++{code} : 0;"
      bindCont cont fun xId cb => do
        setVar xId [("", code, "int"), ("", node, "int")]
        lowerBindable cb dest
      return
    if act0.isAppOfArity ``Zlib.Trees.cforIntLe 4 || act0.isAppOfArity ``Zlib.Trees.cforIntLt 4 ||
        act0.isAppOfArity ``Zlib.Trees.cforIntGe 3 then
      let args := act0.getAppArgs
      let initial := args.back!
      let stateTy ← inferType initial
      let bound ← fresh `limit
      emit s!"int {bound} = {← lowerExpr args[args.size - 3]!};"
      let (vars, arrays) ← getLoopVars stateTy initial `s
      let (_, index, "int") :: _ := vars | throwError "expected a signed int loop index"
      let (test, step) := if act0.isAppOfArity ``Zlib.Trees.cforIntGe 3 then (">=", "--")
        else if act0.isAppOfArity ``Zlib.Trees.cforIntLt 4 then ("<", "++") else ("<=", "++")
      withBlock s!"for (; {index} {test} {bound}; {index}{step}) \{" do
        withStateFn stateTy (stripMeta args[args.size - 2]!) vars arrays fun b => lowerBindable b (.vars vars)
      bindCont cont fun xId cb => do setVar xId vars arrays; lowerBindable cb dest
      return
    let act ← unfoldStep act0
    if act.isAppOfArity `Zlib.Deflate.config_at 1 then
      let index ← lowerExpr act.getAppArgs[0]!
      bindCont cont fun id body => do
        let row ← fresh `config_row
        let value ← fresh `config_value
        emit s!"const config *const {row} = &configuration_table[{index}];"
        -- Evaluate the array access at the bind even when the continuation discards it.
        -- Field projections can read the same immutable row later.
        emit s!"const config {value} = *{row};"
        emit s!"(void){value};"
        setVar id [("", value, "config")]
        modify fun st => { st with
          structPtrs := st.structPtrs.insert id (row, `Zlib.Deflate.Config)
          immutableRecords := st.immutableRecords.insert id }
        lowerBindable body dest
      return
    if act.isAppOfArity `Zlib.Trees.sid 1 then
      let state ← lowerExpr act.getAppArgs[0]!
      bindCont cont fun id body => do
        modify fun st => { st with deflateIds := st.deflateIds.insert id state }
        lowerBindable body dest
      return
    if act.isAppOfArity ``Zlib.GzFs.vaStart 1 then
      let some (args, last) := (← get).varargs? | throwError "va_start outside a variadic function"
      unless act.getAppArgs[0]!.fvarId? == some args do throwError "va_start requires this function's arguments"
      bindCont cont fun xId cb => do
        let name ← fresh (← xId.getDecl).userName
        emit s!"va_list {name};"
        emit s!"va_start({name}, {last});"
        setVar xId [("", name, "va_list")]
        lowerBindable cb dest
      return
    if act.isAppOfArity ``C.cinline 2 || act.isAppOfArity ``Zlib.GzFs.ginline 2 then
      let inner ← unfoldStep act.getAppArgs[1]!
      let exprS ← lowerExpr inner
      let ct := (← cType? act.getAppArgs[0]!).getD ""
      bindCont cont fun xId cb => do setVar xId [("", exprS, ct)]; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.cdecl 2 || act.isAppOfArity ``Zlib.GzFs.gdecl 2 then
      let stTy := act.getAppArgs[0]!; let initExpr := act.getAppArgs[1]!
      bindCont cont fun xId cb => do
        let flatTys ← flattenType stTy (← xId.getDecl).userName
        let flatRaw ← flattenExprsM initExpr
        let flatInits ← if stTy.getAppFn.constName?.any (isLocalStruct (← getEnv)) then pure flatRaw
          else flatRaw.filterM (fun fe => do return !(← isArrTy fe))
        if flatTys.length != flatInits.length then throwError m!"cdecl initializer length mismatch for {stTy}"
        let mut entries : List VarEntry := []
        for ((fnm, ct), iv) in flatTys.zip flatInits do
          let ivS := stripMeta iv; let nameHint := cIdent fnm
          let vn ← if (← get).mutLocals.any (· == (nameHint, ct)) then
            if !(ivS.getAppFn.isConstOf ``Inhabited.default) then
              let v ← lowerExpr ivS
              if v != nameHint then emit s!"{nameHint} = {v};"
            pure nameHint
          else
            let vvn ← fresh fnm
            if ivS.getAppFn.isConstOf ``Inhabited.default then emit s!"{ct} {vvn};"
            else emit s!"{ct} {vvn} = {← lowerExpr ivS};"
            modify fun st => { st with mutLocals := (vvn, ct) :: st.mutLocals }
            pure vvn
          entries := entries ++ [(fnm.toString, vn, ct)]
        if let some sn := stTy.getAppFn.constName? then
          if isLocalStruct (← getEnv) sn then modify fun st => { st with cdeclVars := st.cdeclVars.insert sn entries }
        setVar xId entries (← collectArrExprs initExpr)
        lowerBindable cb dest
      return
    if let some (false, sn) := act.getAppFn.constName?.bind structAct? then if act.getAppNumArgs == 1 then
      let p ← lowerExpr act.getAppArgs[0]!
      bindCont cont fun id body => do
        if (← get).decoderFrame.isSome && sn == ``C.InflateState then
          if ← lowerTableFields? lowerBindable id act.getAppArgs[0]! p body dest (live := true) then return
        let writesBack ← immediatelyUpdates body act.getAppArgs[0]! sn id
        let registerUse := (bindParts? body).any fun (use, rest) =>
          use.isAppOf ``modify && use.getAppArgs[0]!.isConstOf `Zlib.Inflate.IL && !rest.containsFVar id
        let immediate := (← get).decoderFrame.isSome && readsBeforeEffects id body
        let ptr ← if !writesBack && !registerUse && !immediate && sn ∈ [``C.InflateState, ``C.ZStream] &&
            !returnsScalarField (← getEnv) id sn body &&
            ((← get).decoderFrame.isSome || crossesRecordUpdate body sn id) then do
          let saved ← fresh `snapshot
          let ct := if sn == ``C.InflateState then "struct inflate_state" else "z_stream"
          emit s!"const {ct} {saved} = *({p});"
          pure s!"(&{saved})"
        else pure p
        modify fun st => { st with structPtrs := st.structPtrs.insert id (ptr, sn) }
        if sn == ``C.InflateState then
          if ← lowerTableFields? lowerBindable id act.getAppArgs[0]! p body dest then return
        lowerBindable body dest
      return
    if act.isAppOfArity ``C.cwhile 4 || act.isAppOfArity ``C.cdoWhile 4 || act.isAppOfArity ``Zlib.GzFs.gwhile 4 || act.isAppOfArity ``Zlib.GzFs.gdoWhile 4 then
      let w := act.getAppArgs; let isDo := act.isAppOfArity ``C.cdoWhile 4 || act.isAppOfArity ``Zlib.GzFs.gdoWhile 4
      let condFn := stripMeta w[if isDo then 2 else 1]!; let stepFn := stripMeta w[if isDo then 1 else 2]!
      let (loopVars, loopArrs) ← getLoopVars w[0]! w[3]! `s
      let withLoopFn {α} (fnExpr : Expr) (k : FVarId → Expr → M α) : M α := do
        if fnExpr.isLambda then lambdaTelescope fnExpr fun xs body => do setVar xs[0]!.fvarId! loopVars loopArrs; k xs[0]!.fvarId! body
        else withLocalDeclD `s w[0]! fun fv => do setVar fv.fvarId! loopVars loopArrs; k fv.fvarId! (← unfoldStep (mkApp fnExpr fv)).headBeta
      let savedBrk := (← get).breakVar?; let runStep (bv? : Option String) := do modify fun s => { s with breakVar? := bv? }; withLoopFn stepFn fun _ b => lowerBindable b (.vars loopVars); modify fun s => { s with breakVar? := savedBrk }
      if let some cTxt ← withLoopFn condFn fun fv cBody => extractLoopCond? cBody fv then
        let brkInfo? ← if !isDo then extractBreakLoop? cTxt w[3]! loopVars else pure none
        let (hdr, stepBrk?) := match brkInfo? with | some (bv, "1") => ("for (;;) {", some bv) | some (bv, nc) => (s!"while ({nc}) \{", some bv) | none => (s!"while ({cTxt}) \{", none)
        if !isDo then withBlock hdr (runStep stepBrk?) else
          let savedMut := (← get).mutLocals; emit "do {"; modify fun s => { s with indent := s.indent + 1 }; runStep none
          modify fun s => { s with indent := s.indent - 1, mutLocals := savedMut }; emit s!"} while ({cTxt});"
      else
        let tag ← fresh `loop_cond
        let runCond := withLoopFn condFn fun _ cBody =>
          lowerBindable cBody (.vars (("", tag, "int") :: loopVars))
        if isDo then
          emit s!"int {tag};"
          withBlock "do {" do
            runStep none
            runCond
          emit s!"while ({tag});"
        else
          withBlock "for (;;) {" do
            emit s!"int {tag};"
            runCond
            emit s!"if (!{tag}) break;"
            runStep none
      bindCont cont fun xId cb => do setVar xId loopVars loopArrs; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.cwhileBrk 4 || act.isAppOfArity ``Zlib.GzFs.gwhileBrk 4 || isDoWhileBrk act then
      let w := act.getAppArgs
      let isDo := isDoWhileBrk act
      let (loopVars, loopArrs) ← getLoopVars w[0]! w[3]! `s
      lowerControlledLoop lowerBindable isDo w[0]! (stripMeta w[if isDo then 2 else 1]!)
        (stripMeta w[if isDo then 1 else 2]!) loopVars loopArrs (← get).fnRetDest
      bindCont cont fun xId cb => do setVar xId loopVars loopArrs; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.clabel 5 then
      let w := act.getAppArgs; let lbl := match stripMeta w[2]! with | .lit (.strVal s) => s | _ => "lbl"
      let (stateVars, stateArrs) ← getLoopVars w[0]! w[4]! `s
      let resVars ← if w[1]! == w[0]! then pure stateVars else allocVars w[1]! `res
      emitLabel lbl
      withStateFn w[0]! (stripMeta w[3]!) stateVars stateArrs fun b => lowerBindable b (.gotoStep lbl stateVars (.vars resVars))
      bindCont cont fun xId cb => do setVar xId resVars stateArrs; lowerBindable cb dest
      return
    if let some (ct, bytes) := memcpyLoadType? act then
      let pS ← lowerExpr act.getAppArgs[0]!
      bindCont cont fun xId cb => do
        let nm := (← xId.getDecl).userName; let vn ← fresh nm
        emitTemporary ct vn; emit s!"memcpy(&{vn}, {pS}, {bytes});"
        setVar xId [(cIdent nm, vn, ct)]; modify fun st => { st with mutLocals := (vn, ct) :: st.mutLocals }
        lowerBindable cb dest
      return
    if act.isAppOfArity ``C.storePostIncCode 2 then
      let a' := act.getAppArgs; let pS ← lowerExpr a'[0]!; let vS ← lowerExpr a'[1]!
      emit s!"*{pS}++ = {vS};"
      bindCont cont fun xId cb => do setVar xId [(cIdent (← xId.getDecl).userName, pS, "code *")]; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.storeAtPostInc 4 then
      let a' := act.getAppArgs
      emit s!"{← lowerExpr a'[0]!}[{← lowerExpr a'[1]!}[{← lowerExpr a'[2]!}]++] = {← lowerExpr a'[3]!};"
      bindCont cont fun xId cb => do let avs ← collectArrExprs a'[1]!; if !avs.isEmpty then setVar xId [] avs; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.copyBytePostInc 2 then
      let a' := act.getAppArgs; let outS ← lowerExpr a'[0]!; let fromS ← lowerExpr a'[1]!
      emit s!"*{outS}++ = *{fromS}++;"
      bindCont cont fun xId cb => do setVar xId [("", outS, "unsigned char *"), ("", fromS, "unsigned char *")]; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.pullByte64 3 then
      let a' := act.getAppArgs; let inS ← lowerExpr a'[0]!; let holdS ← lowerExpr a'[1]!; let bitsS ← lowerExpr a'[2]!
      emit s!"{holdS} += (unsigned long)(*{inS}++) << {bitsS};"; emit s!"{bitsS} += 8;"
      bindCont cont fun xId cb => do setVar xId [("", inS, "unsigned char *"), ("", holdS, "unsigned long"), ("", bitsS, "unsigned")]; lowerBindable cb dest
      return
    let actFn := act.getAppFn.constName?
    if act.isAppOfArity ``Array.set! 4 then
      let a' := act.getAppArgs; emit s!"{← lowerExpr a'[1]!}[{← lowerExpr a'[2]!}] = {← lowerExpr a'[3]!};"
      bindCont cont fun xId cb => do let avs ← collectArrExprs a'[1]!; if !avs.isEmpty then setVar xId [] avs; lowerBindable cb dest
      return
    if actFn == some ``Zlib.GzFs.strLit || actFn == some ``C.strLitRef then
      let s ← lowerExpr act.getAppArgs.back!; bindCont cont fun xId cb => do modify fun st => { st with strLitVars := st.strLitVars.insert xId s }; lowerBindable cb dest
      return
    let lowerAct (result : Dest) : M Unit := do
      if let some callee := act0.getAppFn.constName? then
        if ← shouldUnfoldHelper callee then
          -- An inlined function owns its local bindings. Its parameters can still
          -- read their caller-supplied values through the free-variable map.
          let callerLocals := (← get).mutLocals
          modify fun st => { st with mutLocals := [] }
          lowerBindable act result
          modify fun st => { st with mutLocals := callerLocals }
          return
      lowerBindable act result
    bindCont cont fun xId cb => do
      let xTy := (← xId.getDecl).type
      if xTy.isConstOf ``Unit || xTy.isConstOf ``PUnit then lowerAct .unit; lowerBindable cb dest
      else if xTy.isConstOf ``C.FnPtr then
        let some ct := allocatorFieldType? act | throwError m!"cannot determine the allocator signature for {act}"
        let nm := (← xId.getDecl).userName
        let vars := [(cIdent nm, ← declMut nm ct, ct)]
        lowerAct (.vars vars)
        setVar xId vars
        lowerBindable cb dest
      else if xTy.isAppOfArity ``Array 1 then
        let aes ← collectArrExprs act
        if !aes.isEmpty then setVar xId [] aes
        lowerBindable cb dest
      else if act.isAppOfArity ``C.withBPtrCell 3 || act.isAppOfArity ``Bind.bind 6 || act.isLet || act.isAppOfArity ``ite 5 || act.isAppOfArity ``dite 5 ||
              act.isAppOfArity ``ForIn.forIn 8 || (← Meta.matchMatcherApp? act).isSome ||
              xTy.isAppOfArity ``Prod 2 || isLocalStruct (← getEnv) (xTy.getAppFn.constName?.getD .anonymous) then
        if let .fvar oldFv := act then
          let st ← get; if let some oldEntries := st.vars.get? oldFv then setVar xId oldEntries ((st.arrVars.get? oldFv).getD []); lowerBindable cb dest; return
        if let some cEntries ← hasCdeclType xTy then
          modify fun st => { st with lastArrs := [] }; lowerAct (.vars cEntries); setVar xId cEntries (← get).lastArrs; lowerBindable cb dest; return
        let xVars ← allocVars xTy (← xId.getDecl).userName; modify fun st => { st with lastArrs := [] }; lowerAct (.vars xVars); setVar xId xVars (← get).lastArrs; lowerBindable cb dest
      else
        let actCall ← lowerExpr act; let nm := (← xId.getDecl).userName; let ct := (← cType? xTy).getD "unsigned long"
        let contUnused := match stripMeta cont with | .lam _ _ b _ => !b.hasLooseBVar 0 | _ => false
        if contUnused && (actFn.isSome || act.isApp) then emit s!"{actCall};"; lowerBindable cb dest
        else let vn ← fresh nm; emitTemporary ct vn (some actCall); setVar xId [(cIdent nm, vn, ct)]; modify fun st => { st with mutLocals := (vn, ct) :: st.mutLocals }; lowerBindable cb dest
    return
  if let some (ct, bytes) := memcpyLoadType? e then
    let pS ← lowerExpr e.getAppArgs[0]!
    let vn ← fresh `v; emitTemporary ct vn; emit s!"memcpy(&{vn}, {pS}, {bytes});"
    match dest with
    | .ret false => emit s!"return {vn};"
    | .vars vs => if let [(_, d, _)] := vs then emit s!"{d} = {vn};"
    | _ => pure ()
    return
  if isUbTerm e then emit "__builtin_trap();"; return
  match dest with
  | .exitOnTrue target =>
    if e.isConstOf ``Bool.true then emit s!"goto {target};"
    else unless e.isConstOf ``Bool.false do emit s!"if ({← lowerExpr e}) goto {target};"
  | .unit | .modeTail _ => let s ← lowerExpr e; if s != "()" && s != "0" then emit s!"{s};"
  | .vars vs => lowerValueToVars e vs
  | .ret true => if e.isConstOf ``Unit.unit then emit "return;" else do let s ← lowerExpr e; if s != "()" && s != "0" then emit s!"{s};"
  | .ret false => emit s!"return {← lowerExpr e};"
  | .outTuple specs isVoid =>
    let flat ← flattenExprsM e (keepUnit := true); let origMap := (← get).origOutFVars
    for ((outIdx, pName, _), origPair) in specs.zip origMap do
      let valExpr := stripMeta flat[outIdx]!; if !(match valExpr with | .fvar fv => fv == origPair.1 | _ => false) then
        let rhsS ← lowerExpr valExpr
        if rhsS != s!"(*{pName})" then emit s!"*{pName} = {rhsS};"
    if isVoid then emit "return;" else emit s!"return {← lowerExpr flat[0]!};"
  | .loopStep vs retDest continueTo =>
    let es := stripMeta e
    if es.isAppOfArity ``C.LoopStep.next 3 then lowerValueToVars es.getAppArgs[2]! vs
    else if es.isAppOfArity ``C.LoopStep.cont 3 then
      lowerValueToVars es.getAppArgs[2]! vs
      emit (continueTo.map (fun label => s!"goto {label};") |>.getD "continue;")
    else if es.isAppOfArity ``C.LoopStep.brk 3 then lowerValueToVars es.getAppArgs[2]! vs; emit "break;"
    else if es.isAppOfArity ``C.LoopStep.ret 3 then lowerBindable es.getAppArgs[2]! retDest
    else throwError m!"unsupported LoopStep leaf {e}"
  | .gotoStep lbl vs doneDest =>
    let es := stripMeta e
    if es.isAppOfArity ``C.GotoStep.goto 3 then lowerValueToVars es.getAppArgs[2]! vs; emit s!"goto {lbl};"
    else if es.isAppOfArity ``C.GotoStep.done 3 then lowerBindable es.getAppArgs[2]! doneDest
    else throwError m!"unsupported GotoStep leaf {e}"
  | .fwdStep lbl vs =>
    let es := stripMeta e
    if es.isAppOfArity ``C.FwdStep.fall 2 then lowerValueToVars es.getAppArgs[1]! vs
    else if es.isAppOfArity ``C.FwdStep.goto 2 then lowerValueToVars es.getAppArgs[1]! vs; emit s!"goto {lbl};"
    else throwError m!"unsupported FwdStep leaf {e}"
private partial def collectExprDeps (e : Expr) (visited : NameSet) : MetaM (NameSet × List Name) := do
  let mut vis := visited; let mut fns : List Name := []
  for c in e.getUsedConstants do if !vis.contains c then
    vis := vis.insert c
    if let some info := (← getEnv).find? c then
      let modelHelper := c.getPrefix == `Zlib.Inflate && info.hasValue &&
        (unwrapLinkage info.type.getForallBody).1.isNone
      if modelHelper || (← shouldUnfoldHelper c) then
        if let some body := info.value? then
          let (seen, more) ← collectExprDeps body vis
          vis := seen
          fns := fns ++ more
      else fns := c :: fns
  return (vis, fns)
private def parseStaticsInit (env : Environment) (modConsts : Array Name) : List (String × Name) := Id.run do
  let rec findMk : Expr → List (String × Name) | .lam _ _ b _ => findMk b | e => if e.getAppFn.isConstOf ``C.Statics.mk then
    ((getStructureFields env ``C.Statics).toList.zip e.getAppArgs.toList).filterMap fun (fld, arg) => match stripMeta arg with | .const src [] => if src != (``C.Statics ++ fld) then some (fld.toString, src) else none | _ => none else []
  return modConsts.foldl (fun out n => if cIdent n == "initStatics" then match env.find? n with | some (.defnInfo d) => out ++ findMk d.value | _ => out else out) []
private def emitLocalStruct? (env : Environment) (sn : Name) : MetaM (Option String) := do
  if !isLocalStruct env sn then return none
  let mut flds := ""
  for f in getStructureFields env sn do if let some info := env.find? (sn ++ f) then
    if let some ct ← forallTelescope info.type (fun _ b => if b.getAppFn.constName? == some ``Array then pure none else cType? b) then flds := flds ++ s!"{ct}{if ct.endsWith "*" then "" else " "}{f.toString}; "
  return if flds.isEmpty then none else some ("typedef struct { " ++ flds ++ "} " ++ cStructName sn ++ ";\n")
private def arrElemCTy (ty : Expr) : String := if ty.isAppOfArity ``Array 1 && ty.getAppArgs[0]!.isConstOf ``C.Code then "code" else if ty.isAppOfArity ``Array 1 && ty.getAppArgs[0]!.isConstOf ``UInt16 then "unsigned short" else "unsigned"
/-- Render the configuration table from its Lean record array. The address for
    each enum value is obtained by reducing the same dispatch used by deflate. -/
private def configTable : MetaM (String × String) := do
  let table ← getConstInfo `Zlib.Deflate.configuration_table
  let some value := table.value? | throwError "missing configuration table"
  let some rows := extractListExprs value | throwError "configuration table must be a literal array"
  let fields := getStructureFields (← getEnv) `Zlib.Deflate.Config
  let mut members := #[]
  for name in fields do
    let field ← getConstInfo (`Zlib.Deflate.Config ++ name)
    let some (ct, _) := cTypeHead? field.type.getForallBody | throwError m!"unsupported config field {name}"
    members := members.push s!"    {ct} {name};"
  let types := "typedef unsigned (*compress_func)(deflate_state *, int);\ntypedef struct config_s {\n" ++
    String.intercalate "\n" members.toList ++ "\n} config;\n"
  withLocalDeclD `state (mkConst ``C.DeflateStatePtr) fun state =>
    withLocalDeclD `flush (mkConst ``Int32) fun flush => do
      let mut initializers := #[]
      for row in rows do
        unless row.isAppOfArity `Zlib.Deflate.Config.mk fields.size do throwError "unsupported config row"
        let mut values := #[]
        for arg in row.getAppArgs do
          if (← inferType arg).isConstOf `Zlib.Deflate.CompressFunc then
            let fn ← compressionTarget arg state flush
            let decl ← getConstInfo fn
            let some body := decl.value? | throwError m!"missing function body for {fn}"
            let some fm ← analyzeFn? fn decl.type body | throwError m!"missing C function for {fn}"
            unless fm.link.needsProto && fm.params.map (·.2.1) == ["deflate_state *", "int"] &&
                fm.retCTy == "unsigned" do
              throwError m!"invalid compression function signature or arguments for {fn}"
            values := values.push fm.cName
          else
            let some n ← evalPureInt? arg | throwError m!"nonconstant tuning parameter {arg}"
            values := values.push (toString n)
        initializers := initializers.push ("    {" ++ String.intercalate ", " values.toList ++ "}")
      let array := s!"static const config configuration_table[{rows.length}] = " ++ "{\n" ++
        String.intercalate ",\n" initializers.toList ++ "\n};\n"
      return (types, array)

def compileModule (modName : Name) (abiZStream abiInflate abiDeflate abiGz : String) (parts : List Name := []) : MetaM String := do
  let env ← getEnv
  let mut keyed : Array (Nat × Name) := #[]
  let mut offset := 0
  for part in modName :: parts do
    let some idx := env.getModuleIdx? part | throwError m!"module not loaded: {part}"
    let entries ← env.header.moduleData[idx.toNat]!.constNames.mapM fun n => do
      let line := ((← findDeclarationRanges? n).map (·.range.pos.line)).getD 0
      return (if line == 0 then 0 else offset + line, n)
    let sorted := entries.qsort (·.1 < ·.1)
    keyed := keyed ++ sorted
    if let some last := sorted.back? then offset := last.1
  let constNames := keyed.map (·.2); let staticsMap := parseStaticsInit env constNames; let mut fns : Array FnMeta := #[]; let mut globals := ""
  for (ln, n) in keyed do
    -- A source declaration may export a C name starting with an underscore.
    if n.isInternal && (ln == 0 || n.getPrefix.isInternal || env.contains n.getPrefix) then continue
    let some (.defnInfo d) := env.find? n | continue
    match (unwrapLinkage d.type.getForallBody).1 with
    | some (_, true, false, false) => globals := globals ++ "const char " ++ cIdent n ++ "[] = " ++ ABI.cString ((← evalPureString? d.value).getD "") ++ ";\n"
    | some (_, false, true, false) =>
      let some elems := extractListExprs d.value | throwError m!"bad str array {n}"
      globals := globals ++ "char * const " ++ cIdent n ++ "[] = {" ++ String.intercalate ", " (← elems.mapM fun x => return ABI.cString ((← evalPureString? x).getD "")) ++ "};\n"
    | some (_, false, false, false) =>
      if let some fm ← analyzeFn? n d.type d.value ln then
        if let some idx := fns.findIdx? (·.cName == fm.cName) then
          if fm.link.customCName?.isSome then
            let prev := fns[idx]!
            fns := fns.set! idx { fm with order? := fm.order?.orElse fun _ => prev.order?, line := if fm.order?.isNone then prev.line else fm.line }
        else fns := fns.push fm
    | _ => pure ()
  fns := fns.qsort fun a b => let ka := a.order?.getD a.line; let kb := b.order?.getD b.line; if ka != kb then ka < kb else a.line < b.line
  let mut usedAll : NameSet := {}; let mut usedConsts : List Name := []
  for fm in fns do if let some (.defnInfo d) := env.find? fm.leanName then let (v, cs) ← collectExprDeps d.value usedAll; usedAll := v; usedConsts := usedConsts ++ cs
  let mut pre := ""
  if fns.any (fun fm => fm.params.any (fun (_, ct, _) => ct == "va_list" || ct == "...")) then pre := pre ++ "#include <stdarg.h>\n"
  for (cs, hdr) in [([``C.allocB, ``C.freeB, ``C.allocGzState, ``C.freeGzState], "<stdlib.h>"), ([`Zlib.Infback.copyStoredInput, `Zlib.Inflate.copyStoredInput, ``C.copyZStream, ``C.copyDeflateState, ``C.copyInflateState, ``C.strlenB, ``C.memmoveB, ``C.memsetB, ``C.memcpyB, ``C.Ptr.memcpy, ``C.Ptr.fill, ``C.InflateState.zeroed, ``C.DeflateState.zeroed, ``C.memcpyLoad32, ``C.memcpyLoad64, ``C.memcpyStore64, ``Zlib.GzFs.zstrerror, ``Zlib.Gzguts.memchrB], "<string.h>"), ([``Zlib.GzFs.snprintf, ``Zlib.GzFs.vsnprintf], "<stdio.h>"), ([``Zlib.GzFs.fsOpen, ``Zlib.GzFs.fsFcntl], "<fcntl.h>"), ([``Zlib.GzFs.fsClose, ``Zlib.GzFs.fsLseek, ``Zlib.GzFs.fsReadInto, ``Zlib.GzFs.fsWriteFrom], "<unistd.h>")] do
    if cs.any usedAll.contains then
      pre := pre ++ s!"#include {hdr}\n"
      if hdr == "<unistd.h>" && usedAll.contains ``Zlib.GzFs.fsLseek then
        pre := pre ++ "#if defined(_LFS64_LARGEFILE) && _LFS64_LARGEFILE-0\n#  define LSEEK lseek64\n#else\n#  define LSEEK lseek\n#endif\n"
  if usedConsts.any (·.getPrefix == `Zlib.GzFs) then pre := pre ++ "#include <errno.h>\n"
  let hasP (ts : List String) := fns.any (·.params.any (·.2.1 ∈ ts)); let hasT (ts : List String) := fns.any (fun fm => fm.retCTy ∈ ts || fm.params.any (·.2.1 ∈ ts))
  if hasP ["in_func"] then pre := pre ++ "typedef unsigned (*in_func)(void *, unsigned char **);\n"
  if hasP ["out_func"] then pre := pre ++ "typedef int (*out_func)(void *, unsigned char *, unsigned);\n"
  pre := pre ++ if usedAll.contains ``C.GzState || usedAll.contains ``C.GzFile || hasP ["gzFile", "gz_statep"] then abiGz else if usedAll.contains `Zlib.Inflate.IL || usedAll.contains ``C.InflateState || usedAll.contains ``C.Code || hasP ["codetype", "code **"] then abiInflate else if usedAll.contains ``C.DeflateState || usedAll.contains ``C.CtData || usedAll.contains `Zlib.Deflate.config_at then abiDeflate else if usedAll.contains ``C.ZStream || hasP ["z_streamp"] then abiZStream else ""
  let usesOffsetCast := castMap.any fun (name, cType) => cType == "z_off64_t" && usedAll.contains name
  if hasT ["z_off_t", "z_off64_t"] || usesOffsetCast then pre := pre ++ "typedef long z_off_t;\ntypedef long z_off64_t;\n"
  if usedAll.contains ``C.CodeType || usedAll.contains `Zlib.Inftrees.inflate_table || hasP ["codetype"] then pre := pre ++ "typedef enum { CODES, LENS, DISTS } codetype;\n"
  if hasT ["z_crc_t", "z_word_t"] then pre := pre ++ "typedef unsigned z_crc_t;\ntypedef unsigned z_word_t;\n"
  let mut structDefs := ""; let mut emittedStructs : NameSet := {}; let mut structCands := usedConsts
  for fm in fns do if let some (.defnInfo d) := env.find? fm.leanName then structCands := structCands ++ (← forallTelescope d.type (fun xs _ => xs.toList.filterMapM fun x => return (← inferType x).getAppFn.constName?))
  for c in structCands do if !emittedStructs.contains c then emittedStructs := emittedStructs.insert c; if let some sd ← emitLocalStruct? env c then structDefs := structDefs ++ sd
  let mut externCandidates := usedConsts
  let mut optionDecls : List (String × String) := []
  let mut fnBodies := ""; let mut emittedStatics : NameSet := {}
  for fm in fns do
    let some (.defnInfo d) := env.find? fm.leanName | continue
    let st ← lambdaTelescope d.value fun xs body => do
      let scopedLocals := body.isAppOfArity ``C.withScopedLocals 2
      let body := if scopedLocals then body.getAppArgs[1]! else body
      let mut init : State := { staticsMap, scopedLocals }; let mut outSpec : List (Nat × String × OutKind) := []; let mut origOut : List (FVarId × String × OutKind) := []
      for (fv, (pName, ct, ok?)) in xs.toList.zip fm.params do
        init := { init with vars := init.vars.insert fv.fvarId! [(pName, pName, ct)], used := init.used.insert (.str .anonymous pName), mutLocals := (pName, ct) :: init.mutLocals }
        if ct == "..." then init := { init with varargs? := some (fv.fvarId!, fm.params[fm.params.length - 2]!.1) }
        if let some ok := ok? then outSpec := outSpec ++ [(outSpec.length + 1, pName, ok)]; origOut := origOut ++ [(fv.fvarId!, pName, ok)]; init := { init with vars := init.vars.insert fv.fvarId! [(pName, s!"(*{pName})", match ok with | .codePtr => "code *" | .uint32 => "unsigned")] }
      let retD := if outSpec.isEmpty then .ret (fm.retCTy == "void") else .outTuple outSpec (fm.retCTy == "void")
      init := { init with origOutFVars := origOut, fnRetDest := retD }
      try return (← (lowerBindable body retD).run init).2
      catch err => throwError m!"{fm.leanName}: {err.toMessageData}"
    for decl in st.optionDecls do
      unless optionDecls.any (·.1 == decl.1) do optionDecls := decl :: optionDecls
    let mut fnLocalTbls := ""; let mut preFnTbls := ""
    externCandidates := externCandidates ++ st.functionAddresses.toList
    for (tblName, sname, isLocOnly) in st.usedStatics.toList.map (fun (s, t) => (t, s, false)) ++ st.localTbls.toList.map (fun t => (t, cIdent t, true)) do
      if let some (.defnInfo td) := env.find? tblName then
        let (lk?, inner) := unwrapLinkage td.type.getForallBody; let isLocal := isLocOnly && (lk?.any (·.2.2.2))
        if isLocal || !emittedStatics.contains tblName then
          let decl ← emitStaticArray evalPureInt? sname (arrElemCTy (if isLocOnly then inner else td.type.getForallBody)) td.value
          if isLocal then fnLocalTbls := fnLocalTbls ++ "    " ++ decl else emittedStatics := emittedStatics.insert tblName; preFnTbls := preFnTbls ++ decl
    fnBodies := fnBodies ++ preFnTbls ++ fmtProto fm ++ " {\n" ++ fnLocalTbls ++ String.intercalate "\n" (st.temporaries ++ st.lines).toList ++ "\n}\n"
  let mut protos := ""
  let mut externs := ""; let mut emittedExt : NameSet := {}
  for c in externCandidates do
    if constNames.contains c || emittedExt.contains c then continue
    let some (.defnInfo cd) := env.find? c | continue
    let decl ← match (unwrapLinkage cd.type.getForallBody).1 with
      | some (_, true, false, false) => pure s!"extern const char {cIdent c}[];\n"
      | some (_, false, true, false) => pure s!"extern char * const {cIdent c}[];\n"
      | _ => do
        let some cm ← analyzeFn? c cd.type cd.value | pure ""
        let args := if cm.params.isEmpty then "void" else String.intercalate ", " (cm.params.map (·.2.1))
        pure s!"extern {hiddenVisibility cm.link}{cm.retCTy} {cm.cName}({args});\n"
    emittedExt := emittedExt.insert c
    externs := externs ++ decl
  for fm in fns do if fm.link.needsProto || fm.order?.isSome then protos := protos ++ fmtProto fm ++ ";\n"
  if modName == `ZlibF.Zlib.«trees.c» then
    match Headers.treeGlobals with
    | .ok data => pre := pre ++ data
    | .error err => throwError err
  for (ref, symbol) in [(``C.BRef.st_length_code, "_length_code"), (``C.BRef.st_dist_code, "_dist_code")] do
    if usedAll.contains ref && modName != `ZlibF.Zlib.«trees.c» then
      pre := pre ++ "extern const unsigned char __attribute__((visibility(\"hidden\"))) " ++ symbol ++ "[];\n"
  if usedAll.contains `Zlib.Deflate.config_at then
    let (types, table) ← configTable
    pre := pre ++ types
    protos := protos ++ table
  return pre ++ String.join (optionDecls.map (·.2)) ++ structDefs ++ globals ++ externs ++ protos ++ fnBodies
end Lean2C.Simple
