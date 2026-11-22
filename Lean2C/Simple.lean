import Lean
import Lean2C.ABI
import ZlibF.Runtime.CAbi
import ZlibF.Runtime.Address
import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables
import ZlibF.Zlib.gzfs
/-! Minimal, Zlib-agnostic `MetaM`-based Lean-`Expr` to C99 module compiler. -/
namespace Lean2C.Simple
open Lean Meta Lean2C.ABI
private abbrev VarEntry := String × String × String
private structure State where
  vars : Std.HashMap FVarId (List VarEntry) := {}
  arrVars : Std.HashMap FVarId (List (String × String)) := {}
  joinArrs : Std.HashMap FVarId (List (List (String × String))) := {}
  lastArrs : List (String × String) := []
  strLitVars : Std.HashMap FVarId String := {}
  structPtrs : Std.HashMap FVarId (String × Name) := {}
  stackFVars : FVarIdSet := {}
  letActions : Std.HashMap FVarId Expr := {}
  origOutFVars : List (FVarId × String × OutKind) := []
  joins : Std.HashMap FVarId (List (List VarEntry) × Bool) := {}
  joinGuards : Std.HashMap FVarId String := {}
  breakVar? : Option String := none
  mutLocals : List (String × String) := []
  used : NameSet := {}
  lines : Array String := #[]
  indent : Nat := 1
  staticsMap : List (String × Name) := []
  usedStatics : Array (String × Name) := #[]
  localTbls : Array Name := #[]
  constCache : Std.HashMap Expr String := {}
  inCondFlag : String := ""
private abbrev M := StateRefT State MetaM
private def takeLast {α : Type} (xs : List α) (n : Nat) : List α := xs.drop (xs.length - n)
private def hasSubstr (h needle : String) : Bool := (h.splitOn needle).length > 1
private def stripZ (e : Expr) : Expr := if e.isAppOfArity ``C.M 1 || e.isAppOfArity ``Zlib.GzFs.G 1 then e.getAppArgs.back! else e
private partial def stripMeta (e : Expr) : Expr :=
  let e := e.consumeMData
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
  if n? == some ``C.CExportAs && a.size == 2 then (some (.exportAs (match a[0]! with | .lit (.strVal s) => s | _ => ""), false, false, false), a[1]!)
  else if a.size == 1 then match n?.bind (linkageTable.lookup ·) with | some info => (some info, a[0]!) | none => (none, t) else (none, t)
private def isRuntimeConst (n : Name) : Bool := [`C, `Zlib.GzFs, `Lean, `Init, `Std].any (·.isPrefixOf n)
private def isZlibModConst (env : Environment) (n : Name) : Bool := (env.getModuleIdxFor? n).any fun idx => let m := env.header.moduleNames[idx.toNat]!; (`ZlibF.Zlib).isPrefixOf m && m != `ZlibF.Zlib.gzfs
private def isLocalStruct (env : Environment) (sn : Name) : Bool := isStructure env sn && !isABIStruct sn && !isRuntimeConst sn && (cTypeHead? (mkConst sn)).isNone && isZlibModConst env sn
private partial def cTypeWithOut? (t : Expr) : MetaM (Option (String × Option OutKind)) := do
  let (_, t) := unwrapLinkage t
  if let some r := cTypeHead? t then return some r
  let t ← whnfR t
  if let some r := cTypeHead? t then return some r
  if let some ref := optPtrRefName? t then return some ((optPtrCType? ref).getD "void *", none)
  match t.getAppFn.constName? with
  | some ``Array =>
    if t.getAppArgs.size == 1 then if let some (et, _) ← cTypeWithOut? t.getAppArgs[0]! then return some (s!"const {et} *", none)
    return none
  | some ``C.Ptr => return some ((optPtrCType? (t.getAppArgs.back!.getAppFn.constName?.getD .anonymous)).getD "void *", none)
  | some sn => return if isLocalStruct (← getEnv) sn then some (cStructName sn, none) else none
  | _ => return none
private def cType? (t : Expr) : MetaM (Option String) := do return (← cTypeWithOut? t).map fun (ct, ok) => stripOutType ct ok
private def isArrTy (e : Expr) : MetaM Bool := do return (← inferType e).getAppFn.constName? == some ``Array
private def isStackTy (t : Expr) (nm : Name) : Bool := t.getAppFn.isConstOf nm || (t.isAppOfArity ``C.M 1 && t.getAppArgs[0]!.getAppFn.isConstOf nm)
private partial def flattenType (t : Expr) (hint : Name) : MetaM (List (Name × String)) := do
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
    let outCnt := params.countP (·.2.2.isSome); let cName := match link with | .exportAs s => s | _ => cIdent name
    return some { leanName := name, cName, link, params, retCTy := (← cType? (if outCnt > 0 && ret1.isAppOfArity ``Prod 2 then ret1.getAppArgs[0]! else ret1)).getD "unsigned long", outCount := outCnt, order?, line }
private def emit (s : String) : M Unit := modify fun st => { st with lines := st.lines.push (String.ofList (List.replicate (st.indent * 4) ' ') ++ s) }
private def withBlock (header : String) (m : M α) : M α := do
  let savedMut := (← get).mutLocals; emit header; modify fun st => { st with indent := st.indent + 1 }
  let r ← m; modify fun st => { st with indent := st.indent - 1, mutLocals := savedMut }; emit "}"; return r
private def fresh (hint : Name) : M String := do
  let b0 := cIdent hint; let base := if b0.startsWith "__" || b0.isEmpty then "tmp" else b0; let used := (← get).used
  for cand in base :: (List.range 299).map fun i => s!"{base}_{i + 1}" do
    if !used.contains (.str .anonymous cand) then modify fun s => { s with used := s.used.insert (.str .anonymous cand) }; return cand
  return s!"{base}_x"
private def declMut (hint : Name) (ct : String) : M String := do let vn ← fresh hint; emit s!"{ct} {vn};"; modify fun s => { s with mutLocals := (vn, ct) :: s.mutLocals }; return vn
private def allocVars (ty : Expr) (hint : Name) : M (List VarEntry) := do (← flattenType ty hint).mapM fun (nm, ct) => return (nm.toString, ← declMut nm ct, ct)
private def setVar (fv : FVarId) (vs : List VarEntry) (arrs : List (String × String) := []) : M Unit := modify fun s => { s with vars := s.vars.insert fv vs, arrVars := if arrs.isEmpty then s.arrVars else s.arrVars.insert fv arrs }
private def bindCont (cont : Expr) (f : FVarId → Expr → M α) : M α := lambdaBoundedTelescope cont 1 fun xs cb => f xs[0]!.fvarId! cb
private def withLetVar (nm : Name) (ty body : Expr) (vs : List VarEntry) (arrs : List (String × String) := []) (k : Expr → M α) : M α := withLocalDeclD nm ty fun fv => do setVar fv.fvarId! vs arrs; k (body.instantiate1 fv)
private partial def mentionsPosixOrRef (e : Expr) : Bool := match e with
  | .const n _ => (posixConst? n).isSome || n ∈ [``C.Ptr.ref, ``Zlib.GzFs.strLit, ``C.strLitRef, ``C.allocB, ``C.freeB]
  | .app f a => mentionsPosixOrRef f || mentionsPosixOrRef a | .letE _ _ v b _ => mentionsPosixOrRef v || mentionsPosixOrRef b
  | .lam _ _ b _ | .mdata _ b => mentionsPosixOrRef b | _ => false
private partial def evalPureInt? (e : Expr) : MetaM (Option Int) := do
  let e := stripMeta e
  if let .lit (.natVal k) := e then return some k
  if let .const n [] := e then return ← if (posixConst? n).isSome then pure none else match ((← getEnv).find? n).bind (·.value?) with | some v => evalPureInt? v | none => pure none
  let some n := e.getAppFn.constName? | return none
  let a := e.getAppArgs
  if n == ``OfNat.ofNat && a.size == 3 then if let .lit (.natVal k) := a[1]! then return some k
  if n == ``Neg.neg && a.size >= 1 then return Option.map (- ·) (← evalPureInt? a.back!)
  if pureIntCasts.contains n && a.size >= 1 then return ← evalPureInt? a.back!
  if let some op := pureIntOps.lookup n then if a.size >= 2 then if let (some l, some r) := (← evalPureInt? a[a.size-2]!, ← evalPureInt? a.back!) then return some (op l r)
  if n == ``HDiv.hDiv && a.size >= 2 then if let (some l, some r) := (← evalPureInt? a[a.size-2]!, ← evalPureInt? a.back!) then if r != 0 then return some (l / r)
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
private def shouldUnfoldHelper (n : Name) : MetaM Bool := do
  if isRuntimeConst n then return false
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
  match e with
  | .fvar fv =>
    let st ← get
    if let some s := st.strLitVars.get? fv then return s else if let some [(_, v, _)] := st.vars.get? fv then return v else if let some ((_, av) :: _) := st.arrVars.get? fv then return av else return "__fvar"
  | .lit (.natVal k) => return toString k | .lit (.strVal s) => return ABI.cString s
  | .proj sn idx inner =>
    if sn == ``Prod then if let some [(_, vn, _)] ← prodEntries? e then return vn
    let some fname := (getStructureFields (← getEnv) sn)[idx]? | throwError m!"bad proj {idx} on {sn}"
    if let some s ← lookupProj inner fname.toString then return s
    let s ← lowerExpr inner; return if !hasSubstr s " " then s!"{s}.{fname}" else s!"({s}).{fname}"
  | .letE nm ty val body _ => let v ← lowerExpr val; return ← withLetVar nm ty body [("", v, "")] (k := lowerExpr)
  | _ => pure ()
  let fn := e.getAppFn; let a := e.getAppArgs
  if fn.isFVar then
    let st ← get; if let some s := st.strLitVars.get? fn.fvarId! then return s else if let some (h :: _) := st.vars.get? fn.fvarId! then return h.2.1 else throwError "unknown fvar fn"
  let some n := fn.constName? | throwError m!"unsupported expr {e}"
  if a.isEmpty then if let some p := posixConst? n then return p
  if n == ``OfNat.ofNat then
    let .lit (.natVal k) := a[1]! | throwError "non-lit OfNat"
    let ty ← cType? a[0]!; return s!"{k}" ++ if ty == some "unsigned long" then "UL" else if ty == some "unsigned" then "U" else ""
  if n == ``Bool.true then return "1" else if n == ``Bool.false then return "0"
  if let some lit ← evalScalar? e then return lit
  if let some s := zeroOps.lookup n then return s
  if n == ``List.toArray && a.back!.isAppOfArity ``List.nil 1 then return "0"
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
  if n == ``C.Ptr.ref && a.size >= 2 then
    if let some s := (a[1]!.getAppFn.constName?).bind fun cn => match cn with | .str _ x => if x.startsWith "st_" then some (x.drop 3).toString else none | _ => none then
      if let some (_, tbl) := (← get).staticsMap.find? (·.1 == s) then modify fun st => if st.usedStatics.any (·.1 == s) then st else { st with usedStatics := st.usedStatics.push (s, tbl) }
      return s
  if n == ``C.Ptr.add && a.size >= 3 then return s!"({← lowerBytePtr a[a.size-2]! (a[0]!.isConstOf ``C.BRef)} + {← lowerExpr a.back!})"
  if n == ``C.Ptr.diff && a.size >= 2 then return s!"({← lowerExpr a[a.size-2]!} - {← lowerExpr a.back!})"
  if n == ``C.Ptr.index || n == ``C.index8 then return s!"{← lowerBytePtr a[a.size-2]! (n == ``C.index8 || a[0]!.isConstOf ``C.BRef)}[{← lowerExpr a.back!}]"
  if n == ``GetElem.getElem && a.size >= 7 then return s!"{← lowerExpr a[5]!}[{← lowerExpr a[6]!}]"
  if n == ``C.Code.mk && a.size == 3 then return s!"((code)\{{← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!}})"
  if n == ``ite && a.size == 5 then
    if isUbTerm a[3]! then return ← lowerExpr a[4]! else if isUbTerm a[4]! then return ← lowerExpr a[3]! else return s!"({← lowerExpr a[1]!} ? {← lowerExpr a[3]!} : {← lowerExpr a[4]!})"
  if n == ``dite && a.size == 5 then
    if isUbTerm a[3]! then return ← lowerExpr (a[4]!.beta #[mkConst ``Unit.unit]) else if isUbTerm a[4]! then return ← lowerExpr (a[3]!.beta #[mkConst ``Unit.unit])
  if let some op := binOps.lookup n then return s!"({← lowerExpr a[a.size-2]!} {op} {← lowerExpr a.back!})"
  if (n == ``Prod.fst || n == ``Prod.snd) && a.size == 3 then if let some [(_, vn, _)] ← prodEntries? e then return vn
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
  if n == ``Zlib.GzFs.fsLseek && a.size >= 3 then return s!"lseek({← lowerExpr a[0]!}, {← lowerExpr a[1]!}, {← lowerExpr a[2]!})"
  if n == ``Zlib.GzFs.snprintf && a.size >= 4 then return ← lowerSnprintf a
  if let some d := (← getEnv).find? n then if let (some (link, false, false, false), _) := unwrapLinkage d.type.getForallBody then
    return s!"{match link with | .exportAs s => s | _ => cIdent n}({String.intercalate ", " (← a.toList.mapM lowerExpr)})"
  throwError m!"lowerExpr unsupported: {e}"
end
private partial def flattenExprsM (e : Expr) : MetaM (List Expr) := do
  let e := stripMeta e
  if e.isAppOfArity ``Prod.mk 4 then return (← flattenExprsM e.getAppArgs[2]!) ++ (← flattenExprsM e.getAppArgs[3]!)
  if let some (n, fldArgs) ← localStructArgs? e then
    let env ← getEnv; let mut out : List Expr := []
    for (f, arg) in fldArgs do if let some info := env.find? (n ++ f) then if info.type.getForallBody.getAppFn.constName? != some ``Array then out := out ++ (← flattenExprsM arg)
    return out
  return [e]
private partial def collectArrExprs (e : Expr) : M (List (String × String)) := do
  let e := stripMeta e
  if let .fvar fv := e then
    let st ← get
    if let some a := st.arrVars.get? fv then if !a.isEmpty then return a
    return if (st.vars.get? fv).any (·.length == 1) && (← isArrTy e) then [("", st.vars.get! fv |>.head!.2.1)] else []
  if e.isAppOfArity ``Prod.mk 4 then return (← collectArrExprs e.getAppArgs[2]!) ++ (← collectArrExprs e.getAppArgs[3]!)
  if let .proj sn idx inner := e then if let some fn := (getStructureFields (← getEnv) sn)[idx]? then if let some av ← lookupProj inner fn.toString then return [("", av)]
  if let some n := e.getAppFn.constName? then if (← getEnv).isProjectionFn n && e.getAppArgs.size == 1 then if let some av ← lookupProj e.getAppArgs[0]! (cIdent n) then return [("", av)]
  if ← isArrTy e then return [("", ← lowerExpr e)]
  if let some (_, fldArgs) ← localStructArgs? e then
    return ← fldArgs.foldlM (fun out (f, arg) => do if ← isArrTy arg then return out ++ [(f.toString, ((← collectArrExprs arg).head?.map (·.2)).getD (← lowerExpr arg))] else return out ++ (← collectArrExprs arg)) []
  return []
private partial def lowerValueToVars (e : Expr) (vars : List VarEntry) : M Unit := do
  let e := stripMeta e
  if let .letE nm ty val body _ := e then
    let st ← get
    let (es, aes) ← match stripMeta val with | .fvar fv => pure ((st.vars.get? fv).getD [], (st.arrVars.get? fv).getD []) | _ => pure ([], ← collectArrExprs val)
    let es ← if es.isEmpty then do pure [("", ← lowerExpr val, "")] else pure es
    withLetVar nm ty body es aes (k := (lowerValueToVars · vars)); return
  let curArrs ← collectArrExprs e; if !curArrs.isEmpty then modify fun st => { st with lastArrs := curArrs }
  if e.isAppOfArity ``Prod.mk 4 then
    let pa := e.getAppArgs; let k := (← flattenType (← inferType pa[2]!) `x).length
    if k <= vars.length then lowerValueToVars pa[2]! (vars.take k); lowerValueToVars pa[3]! (vars.drop k); return
  if let .fvar fv := e then if let some srcVars := (← get).vars.get? fv then
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
private partial def emitStructDiff (ptrExpr sub : String) (sn : Name) (newRec : Expr) (oldFv? : Option FVarId := none) : M Unit := do
  let env ← getEnv; let st ← get; let fields := (getStructureFields env sn).toList; let pfx := if sub.isEmpty then s!"{ptrExpr}->" else s!"{ptrExpr}->{sub}."
  let sameFld (fv' : FVarId) := match oldFv? with | some fv => fv' == fv | none => (st.structPtrs.get? fv').any (·.1 == ptrExpr)
  for (fname, arg) in fields.zip (takeLast (stripMeta newRec).getAppArgs.toList fields.length) do
    let same := match arg with | .app f (.fvar fv') => f.isConstOf (sn ++ fname) && sameFld fv' | .proj sn' idx (.fvar fv') => sn' == sn && (fields[idx]? == some fname || oldFv?.isSome) && sameFld fv' | _ => false
    if !same then
      let argS := (stripMeta arg).headBeta
      if let some innerSn := (← inferType argS).getAppFn.constName? then
        if (isLocalStruct env innerSn || (isABIStruct innerSn && (cTypeHead? (mkConst innerSn)).isNone)) && argS.getAppFn.constName?.any (·.getPrefix == innerSn) then
          emitStructDiff ptrExpr (if sub.isEmpty then fname.toString else s!"{sub}.{fname}") innerSn argS oldFv?; continue
      let lhs := s!"{pfx}{fname}"; let rhs ← lowerExpr argS; if rhs != lhs then emit s!"{lhs} = {rhs};"
private def handleMatch (e : Expr) (k : Expr → M α) (fallback : M α) : M α := do
  if let some mApp ← Meta.matchMatcherApp? e then
    if mApp.discrs.size == 1 && mApp.alts.size == 1 then if let .fvar srcFv := stripMeta mApp.discrs[0]! then
      let st ← get; let (srcVars, srcArrs) := ((st.vars.get? srcFv).getD [], (st.arrVars.get? srcFv).getD [])
      return ← lambdaTelescope mApp.alts[0]! fun altFvs altBody => do
        let mut sFvs : List FVarId := []; let mut aFvs : List FVarId := []
        for fv in altFvs do if ← isArrTy fv then aFvs := aFvs ++ [fv.fvarId!] else sFvs := sFvs ++ [fv.fvarId!]
        for (fvId, (_, av)) in aFvs.zip srcArrs do modify fun s => { s with arrVars := s.arrVars.insert fvId [("", av)] }
        if sFvs.length == srcVars.length then for (fvId, entry) in sFvs.zip srcVars do setVar fvId [entry] else if altFvs.size > 0 then setVar altFvs[0]!.fvarId! srcVars
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
private def isNatLitVal (e : Expr) (k : Nat) : Bool := natLitOf? (stripMeta e) == some k
private partial def unfoldStep (e : Expr) : MetaM Expr := do
  let e := stripMeta e
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let a := e.getAppArgs; let arm (x : Expr) := if e.isAppOfArity ``dite 5 then x.beta #[mkConst ``Unit.unit] else x
    if isUbTerm a[3]! then return stripMeta (arm a[4]!) else if isUbTerm a[4]! then return stripMeta (arm a[3]!)
  if let some fn := e.getAppFn.constName? then if ← shouldUnfoldHelper fn then if let some e' ← Meta.unfoldDefinition? e then return ← unfoldStep e'.headBeta
  return e
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
    return none
  if e.isAppOfArity ``Bind.bind 6 then
    let act ← unfoldStep e.getAppArgs[4]!
    if act.isAppOfArity ``C.ByteAddress.address 1 then
      let addrExpr ← lowerExpr act
      return ← bindCont e.getAppArgs[5]! fun xId cb => do setVar xId [("", addrExpr, "unsigned long")]; extractLoopCond? cb selfFv
    return none
  let s := stripMeta e
  if s.isAppOfArity ``Prod.mk 4 then
    let cond := stripMeta s.getAppArgs[2]!; let nextSt := stripMeta s.getAppArgs[3]!
    if nextSt == .fvar selfFv then return some (← lowerExpr cond)
    if let some loopVars := (← get).vars.get? selfFv then
      let nextScalars ← (← flattenExprsM nextSt).filterM (fun ne => do return !(← isArrTy ne))
      if nextScalars.length == loopVars.length && (← (nextScalars.zip loopVars).allM fun (ne, (_, vn, _)) => do return (← lowerExpr ne) == vn) then return some (← lowerExpr cond)
    if cond.isAppOfArity ``bne 4 && isNatLitVal cond.getAppArgs[3]! 0 then if let some fld := projFld? cond.getAppArgs[2]! then if let some vn := varOf fld then
      if ← onlyUpdates nextSt fld (fun x => x.isAppOfArity ``HSub.hSub 6 && isNatLitVal x.getAppArgs[5]! 1 && projFld? x.getAppArgs[4]! == some fld) then return some s!"{vn}--"
  return none
private partial def hasNonJpPath (e : Expr) (jpFv : FVarId) (breakIdx? : Option Nat := none) : MetaM Bool := do
  let e := stripMeta e.consumeMData.headBeta
  if isUbTerm e || e.getAppFn.fvarId? == some jpFv then return false
  if let .letE n t _ b _ := e then return ← withLocalDeclD n t fun fv => hasNonJpPath (b.instantiate1 fv) jpFv breakIdx?
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let a := e.getAppArgs; return (← hasNonJpPath a[3]! jpFv breakIdx?) || (← hasNonJpPath (if e.isAppOfArity ``dite 5 then a[4]!.beta #[mkConst ``Unit.unit] else a[4]!) jpFv breakIdx?)
  if let some mApp ← Meta.matchMatcherApp? e then return ← mApp.alts.anyM fun alt => lambdaTelescope alt fun _ b => hasNonJpPath b jpFv breakIdx?
  if e.isAppOfArity ``Bind.bind 6 then return ← lambdaBoundedTelescope e.getAppArgs[5]! 1 fun _ b => hasNonJpPath b jpFv breakIdx?
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
private inductive Dest where | ret (isVoid : Bool) | vars (vs : List VarEntry) | unit | outTuple (outs : List (Nat × String × OutKind)) (isVoid : Bool)
private partial def collectSwitch (scrut? : Option String) (cur : Expr) : M (String × List (String × Expr) × Expr) := do
  if cur.isAppOfArity ``ite 5 then
    let ca := cur.getAppArgs; let s ← lowerExpr ca[1]!
    if s.startsWith "(" && s.endsWith ")" then
      let parts := (((s.drop 1).dropEnd 1).toString).splitOn " == "
      if parts.length == 2 then
        let lit := parts[1]!; let core := if lit.endsWith "UL" then (lit.toSlice.dropEnd 2).toString else if lit.endsWith "U" then (lit.toSlice.dropEnd 1).toString else lit
        if !core.isEmpty && core.all Char.isDigit && (scrut?.isNone || scrut? == some parts[0]!) then
          let (scOut, rest, defArm) ← collectSwitch (some parts[0]!) ca[4]!; return (scOut, (lit, ca[3]!) :: rest, defArm)
  return (scrut?.getD "", [], cur)
private partial def lowerBindable (e : Expr) (dest : Dest) : M Unit := do
  let e0 := e.consumeMData.headBeta
  let e ← match e0.getAppFn.constName? with | some fn => if ← shouldUnfoldHelper fn then unfoldStep e0 else pure e0 | none => pure e0
  let eYield := stripMeta e; if eYield.isAppOfArity ``ForInStep.yield 2 then lowerBindable eYield.getAppArgs[1]! dest; return
  handleMatch e (fun altBody => lowerBindable altBody dest) do
  if let .letE jpName _ jpVal body _ := e then
    if jpVal.isLambda then
      lambdaTelescope jpVal fun xs jpBody => do
        let hasUnit := (← inferType xs[0]!).isConstOf ``Unit; let argFvs := if hasUnit then xs.toList.tail! else xs.toList
        let jpArgs ← argFvs.mapM fun fv => do
          let decl ← fv.fvarId!.getDecl
          (← flattenType decl.type decl.userName).mapM fun (fnm, ct) => do
            let name := cIdent fnm; let vn ← match (← get).mutLocals.find? (fun p => (p.1 == name || p.1.startsWith (name ++ "_")) && p.2 == ct) with | some (ex, _) => pure ex | none => declMut fnm ct
            return (name, vn, ct)
        withLocalDeclD jpName (mkConst ``Unit) fun jpFv => do
          let isRet := match dest with | .ret _ => true | _ => false
          let breakIdx? := match dest, (← get).breakVar? with | .vars vs, some bv => vs.findIdx? (·.2.1 == bv) | _, _ => none
          let body' := body.instantiate1 jpFv
          let guard? ← if !isRet && (← hasNonJpPath body' jpFv.fvarId! breakIdx?) then let g ← fresh `jp_go; emit s!"int {g} = 0;"; pure (some g) else pure none
          modify fun st => { st with joins := st.joins.insert jpFv.fvarId! (jpArgs, hasUnit), joinGuards := match guard? with | some g => st.joinGuards.insert jpFv.fvarId! g | none => st.joinGuards }
          lowerBindable body' dest
          let jArrs := ((← get).joinArrs.get? jpFv.fvarId!).getD []
          for (fv, entries) in argFvs.zip jpArgs do modify fun st => { st with vars := st.vars.insert fv.fvarId! entries }
          for (fv, arrs) in argFvs.zip jArrs do modify fun st => { st with arrVars := st.arrVars.insert fv.fvarId! arrs }
          if let some g := guard? then withBlock s!"if ({g}) \{" do lowerBindable jpBody dest else lowerBindable jpBody dest
      return
    let rhsTy ← inferType jpVal
    if !body.hasLooseBVar 0 then lowerBindable (body.instantiate1 (mkFVar ⟨`__unused⟩)) dest; return
    if jpVal.isAppOfArity ``Array.replicate 3 then
      let vn ← fresh jpName; emit s!"{(← cType? jpVal.getAppArgs[0]!).getD "unsigned short"} {vn}[{← lowerExpr jpVal.getAppArgs[1]!}];"
      withLetVar jpName rhsTy body [] [("", vn)] (lowerBindable · dest); return
    if (rhsTy.isAppOfArity ``C.M 1 || rhsTy.isAppOfArity ``Zlib.GzFs.G 1) && !isStackTy rhsTy ``C.StackStream && !isStackTy rhsTy ``C.StackScalar64 then
      withLocalDeclD jpName rhsTy fun fv => do modify fun st => { st with letActions := st.letActions.insert fv.fvarId! jpVal }; lowerBindable (body.instantiate1 fv) dest
      return
    if (← cType? rhsTy).isNone || rhsTy.isAppOfArity ``Prod 2 || isLocalStruct (← getEnv) (rhsTy.getAppFn.constName?.getD .anonymous) then
      if let .fvar oldFv := stripMeta jpVal then
        let st ← get; if let some oldEntries := st.vars.get? oldFv then withLetVar jpName rhsTy body oldEntries ((st.arrVars.get? oldFv).getD []) (lowerBindable · dest); return
      if let some (_, fldArgs) ← localStructArgs? (stripMeta jpVal) then
        let mut entries : List VarEntry := []; let mut arrs : List (String × String) := []
        for (f, a) in fldArgs do
          if ← isArrTy a then arrs := arrs ++ [(f.toString, ((← collectArrExprs a).head?.map (·.2)).getD (← lowerExpr a))]
          else
            let mut v ← if (stripMeta a).getAppFn.isConstOf ``Inhabited.default then pure "__default" else lowerExpr a
            if v != "__default" && hasSubstr v " " then if let some ct ← cType? (← inferType a) then
              let vn ← fresh f; emit s!"{ct} {vn} = {v};"; modify fun st => { st with mutLocals := (vn, ct) :: st.mutLocals }; v := vn
            entries := entries ++ [(f.toString, v, "")]
        withLetVar jpName rhsTy body entries arrs (lowerBindable · dest); return
    let v ← lowerExpr jpVal
    let some ct ← cType? rhsTy | throwError m!"unsupported pure let type {rhsTy}"
    let nameHint := cIdent jpName
    let vn ← if (← get).mutLocals.any (· == (nameHint, ct)) then do
      if v != nameHint then emit s!"{nameHint} = {v};"
      pure nameHint
    else (do let vn ← fresh jpName; emit s!"{ct} {vn} = {v};"; modify fun s => { s with mutLocals := (vn, ct) :: s.mutLocals }; pure vn)
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
      if let some g := (← get).joinGuards.get? fv then emit s!"{g} = 1;"
      return
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let (scrut, cases, defArm) ← collectSwitch none e
    if cases.length >= 3 then
      withBlock s!"switch ({scrut}) \{" do
        modify fun st => { st with indent := st.indent - 1 }
        for (lit, arm) in cases do
          emit s!"case {lit}:"; modify fun st => { st with indent := st.indent + 1 }; lowerBindable arm dest
          let lastT := ((← get).lines.back?.map fun l => l.trimAsciiStart.toString).getD ""
          if !(lastT.startsWith "return " || lastT == "break;") then emit "break;"
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
  if let some (true, sn) := eFn.bind structAct? then if e.getAppNumArgs == 2 then emitStructDiff (← lowerExpr e.getAppArgs[0]!) "" sn e.getAppArgs[1]!.headBeta; return
  if e.isAppOfArity ``C.Ptr.store 4 && e.getAppArgs[1]!.isConstOf ``C.Code then emitStructDiff (← lowerExpr e.getAppArgs[2]!) "" ``C.Code e.getAppArgs[3]!.headBeta; return
  if let some want := eFn.bind ptrWidthType? then
    if e.getAppNumArgs >= 2 then let a' := e.getAppArgs; emit s!"*{← asTypedPtrExpr a'[0]! (← lowerExpr a'[0]!) want} = {← lowerExpr a'[1]!};"; return
  if eFn == some ``C.Ptr.store || eFn == some ``C.store8 then
    let a' := e.getAppArgs; emit s!"*{← lowerBytePtr a'[a'.size-2]! (eFn == some ``C.store8 || (a'.size >= 1 && a'[0]!.isConstOf ``C.BRef))} = {← lowerExpr a'.back!};"; return
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
      let idxVar ← fresh `i; let savedBrk := (← get).breakVar?; modify fun st => { st with breakVar? := none }
      withBlock s!"for (unsigned long {idxVar} = {← lowerExpr ra[0]!}; {idxVar} < {← lowerExpr ra[1]!}; {idxVar} += {← lowerExpr ra[2]!}) \{" do
        lambdaBoundedTelescope fa[7]! 2 fun xs fBody => do
          let curSt ← get; set { curSt with vars := (curSt.vars.insert xs[0]!.fvarId! [("", idxVar, "unsigned long")]).insert xs[1]!.fvarId! sVars }
          lowerBindable fBody (if sVars.isEmpty then .unit else .vars sVars)
      modify fun st => { st with breakVar? := savedBrk }; return
  if e.isAppOfArity ``Bind.bind 6 then
    let a := e.getAppArgs; let st ← get; let rawAct := stripMeta a[4]!
    let act0 := match rawAct.getAppFn with | .fvar fv => (match st.letActions.get? fv with | some rhs => if rawAct.getAppArgs.isEmpty then rhs else mkAppN rhs rawAct.getAppArgs | none => rawAct) | _ => rawAct
    let cont := a[5]!; let act0Ty ← inferType act0
    for (stkNm, cDecl, ptrTy) in [(``C.StackStream, "z_stream", "z_streamp"), (``C.StackScalar64, "unsigned long", "unsigned long *")] do
      if isStackTy act0Ty stkNm then
        bindCont cont fun xId cb => do let vn ← fresh (← xId.getDecl).userName; emit s!"{cDecl} {vn};"; setVar xId [("", s!"(&{vn})", ptrTy)]; modify fun s => { s with stackFVars := s.stackFVars.insert xId }; lowerBindable cb dest
        return
    if act0.getAppFn.isConstOf ``C.stackAddr && act0.getAppArgs.size >= 5 then
      let addrExpr ← lowerExpr act0; bindCont cont fun xId cb => do setVar xId [(cIdent (← xId.getDecl).userName, addrExpr, "unsigned char *")]; modify fun s => { s with stackFVars := s.stackFVars.insert xId }; lowerBindable cb dest
      return
    let act ← unfoldStep act0
    if let some (false, sn) := act.getAppFn.constName?.bind structAct? then if act.getAppNumArgs == 1 then
      let p ← lowerExpr act.getAppArgs[0]!; bindCont cont fun xId cb => do modify fun s => { s with structPtrs := s.structPtrs.insert xId (p, sn) }; lowerBindable cb dest
      return
    if act.isAppOfArity ``C.cwhile 4 || act.isAppOfArity ``C.cdoWhile 4 || act.isAppOfArity ``Zlib.GzFs.gwhile 4 || act.isAppOfArity ``Zlib.GzFs.gdoWhile 4 then
      let w := act.getAppArgs; let isDo := act.isAppOfArity ``C.cdoWhile 4 || act.isAppOfArity ``Zlib.GzFs.gdoWhile 4
      let condFn := stripMeta w[if isDo then 2 else 1]!; let stepFn := stripMeta w[if isDo then 1 else 2]!
      let loopVars ← allocVars w[0]! `s; lowerValueToVars w[3]! loopVars; let loopArrs ← collectArrExprs w[3]!
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
        withBlock "for (;;) {" do
          emit s!"int {tag};"; let runCond := withLoopFn condFn fun _ cBody => lowerBindable cBody (.vars (("", tag, "int") :: loopVars))
          if isDo then runStep none; runCond; emit s!"if (!{tag}) break;" else runCond; emit s!"if (!{tag}) break;"; runStep none
      bindCont cont fun xId cb => do setVar xId loopVars loopArrs; lowerBindable cb dest
      return
    let actFn := act.getAppFn.constName?
    if act.isAppOfArity ``Array.set! 4 then
      let a' := act.getAppArgs; emit s!"{← lowerExpr a'[1]!}[{← lowerExpr a'[2]!}] = {← lowerExpr a'[3]!};"
      bindCont cont fun xId cb => do let avs ← collectArrExprs a'[1]!; if !avs.isEmpty then setVar xId [] avs; lowerBindable cb dest
      return
    if actFn == some ``Zlib.GzFs.strLit || actFn == some ``C.strLitRef then
      let s ← lowerExpr act.getAppArgs.back!; bindCont cont fun xId cb => do modify fun st => { st with strLitVars := st.strLitVars.insert xId s }; lowerBindable cb dest
      return
    bindCont cont fun xId cb => do
      let xTy := (← xId.getDecl).type
      if xTy.isConstOf ``Unit || xTy.isConstOf ``PUnit then lowerBindable act .unit; lowerBindable cb dest
      else if act.isAppOfArity ``Bind.bind 6 || act.isLet || act.isAppOfArity ``ite 5 || act.isAppOfArity ``dite 5 ||
              act.isAppOfArity ``ForIn.forIn 8 || (← Meta.matchMatcherApp? act).isSome ||
              xTy.isAppOfArity ``Prod 2 || isLocalStruct (← getEnv) (xTy.getAppFn.constName?.getD .anonymous) then
        if let .fvar oldFv := act then
          let st ← get; if let some oldEntries := st.vars.get? oldFv then setVar xId oldEntries ((st.arrVars.get? oldFv).getD []); lowerBindable cb dest; return
        let xVars ← allocVars xTy (← xId.getDecl).userName; modify fun st => { st with lastArrs := [] }; lowerBindable act (.vars xVars); setVar xId xVars (← get).lastArrs; lowerBindable cb dest
      else
        let actCall ← lowerExpr act; let nm := (← xId.getDecl).userName; let ct := (← cType? xTy).getD "unsigned long"
        let contUnused := match stripMeta cont with | .lam _ _ b _ => !b.hasLooseBVar 0 | _ => false
        if contUnused && (actFn.isSome || act.isApp) then emit s!"{actCall};"; lowerBindable cb dest
        else let vn ← fresh nm; emit s!"{ct} {vn} = {actCall};"; setVar xId [(cIdent nm, vn, ct)]; modify fun st => { st with mutLocals := (vn, ct) :: st.mutLocals }; lowerBindable cb dest
    return
  if isUbTerm e then emit "__builtin_trap();"; return
  match dest with
  | .unit => let s ← lowerExpr e; if s != "()" && s != "0" then emit s!"{s};"
  | .vars vs => lowerValueToVars e vs
  | .ret true => if e.isConstOf ``Unit.unit then emit "return;" else do let s ← lowerExpr e; if s != "()" && s != "0" then emit s!"{s};"
  | .ret false => emit s!"return {← lowerExpr e};"
  | .outTuple specs isVoid =>
    let flat ← flattenExprsM e; let origMap := (← get).origOutFVars
    for ((outIdx, pName, _), origPair) in specs.zip origMap do
      let valExpr := stripMeta flat[outIdx]!; if !(match valExpr with | .fvar fv => fv == origPair.1 | _ => false) then emit s!"*{pName} = {← lowerExpr valExpr};"
    if isVoid then emit "return;" else emit s!"return {← lowerExpr flat[0]!};"
private partial def collectExprDeps (e : Expr) (visited : NameSet) : MetaM (NameSet × List Name) := do
  let mut vis := visited; let mut fns : List Name := []
  for c in e.getUsedConstants do if !vis.contains c then
    vis := vis.insert c
    if let some info := (← getEnv).find? c then
      if ← shouldUnfoldHelper c then if let some v := info.value? then let (vis', fns') ← collectExprDeps v vis; vis := vis'; fns := fns ++ fns'
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
def compileModule (modName : Name) (abiZStream abiInflate abiDeflate abiGz : String) : MetaM String := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modName | throwError m!"module not loaded: {modName}"
  let keyed := (← env.header.moduleData[modIdx.toNat]!.constNames.mapM fun n => return (((← findDeclarationRanges? n).map (·.range.pos.line)).getD 0, n)).qsort (·.1 < ·.1)
  let constNames := keyed.map (·.2); let staticsMap := parseStaticsInit env constNames; let mut fns : Array FnMeta := #[]; let mut globals := ""
  for (ln, n) in keyed do
    if n.isInternal then continue
    let some (.defnInfo d) := env.find? n | continue
    match (unwrapLinkage d.type.getForallBody).1 with
    | some (_, true, false, false) => globals := globals ++ "const char " ++ cIdent n ++ "[] = " ++ ABI.cString ((← evalPureString? d.value).getD "") ++ ";\n"
    | some (_, false, true, false) =>
      let some elems := extractListExprs d.value | throwError m!"bad str array {n}"
      globals := globals ++ "char * const " ++ cIdent n ++ "[] = {" ++ String.intercalate ", " (← elems.mapM fun x => return ABI.cString ((← evalPureString? x).getD "")) ++ "};\n"
    | some (_, false, false, false) => if let some fm ← analyzeFn? n d.type d.value ln then fns := fns.push fm
    | _ => pure ()
  fns := fns.qsort fun a b => let ka := a.order?.getD a.line; let kb := b.order?.getD b.line; if ka != kb then ka < kb else a.line < b.line
  let mut usedAll : NameSet := {}; let mut usedConsts : List Name := []
  for fm in fns do if let some (.defnInfo d) := env.find? fm.leanName then let (v, cs) ← collectExprDeps d.value usedAll; usedAll := v; usedConsts := usedConsts ++ cs
  let mut pre := ""
  for (cs, hdr) in [([``C.allocB, ``C.freeB, ``C.allocGzState, ``C.freeGzState], "<stdlib.h>"), ([``C.strlenB], "<string.h>"), ([``Zlib.GzFs.snprintf], "<stdio.h>"), ([``Zlib.GzFs.fsOpen, ``Zlib.GzFs.fsFcntl], "<fcntl.h>"), ([``Zlib.GzFs.fsClose, ``Zlib.GzFs.fsLseek], "<unistd.h>")] do
    if cs.any usedAll.contains then pre := pre ++ s!"#include {hdr}\n"
  if usedConsts.any (·.getPrefix == `Zlib.GzFs) then pre := pre ++ "#include <errno.h>\n"
  let hasP (ts : List String) := fns.any (·.params.any (·.2.1 ∈ ts)); let hasT (ts : List String) := fns.any (fun fm => fm.retCTy ∈ ts || fm.params.any (·.2.1 ∈ ts))
  pre := pre ++ if usedAll.contains ``C.GzState || usedAll.contains ``C.GzFile || hasP ["gzFile", "gz_statep"] then abiGz else if usedAll.contains ``C.InflateState || usedAll.contains ``C.Code || hasP ["codetype", "code **"] then abiInflate else if usedAll.contains ``C.DeflateState || usedAll.contains ``C.CtData then abiDeflate else if usedAll.contains ``C.ZStream || hasP ["z_streamp"] then abiZStream else ""
  if hasT ["z_off_t", "z_off64_t"] then pre := pre ++ "typedef long z_off_t;\ntypedef long z_off64_t;\n"
  if usedAll.contains ``C.CodeType || hasP ["codetype"] then pre := pre ++ "typedef enum { CODES, LENS, DISTS } codetype;\n"
  if hasT ["z_crc_t", "z_word_t"] then pre := pre ++ "typedef unsigned z_crc_t;\ntypedef unsigned z_word_t;\n"
  let mut structDefs := ""; let mut emittedStructs : NameSet := {}; let mut structCands := usedConsts
  for fm in fns do if let some (.defnInfo d) := env.find? fm.leanName then structCands := structCands ++ (← forallTelescope d.type (fun xs _ => xs.toList.filterMapM fun x => return (← inferType x).getAppFn.constName?))
  for c in structCands do if !emittedStructs.contains c then emittedStructs := emittedStructs.insert c; if let some sd ← emitLocalStruct? env c then structDefs := structDefs ++ sd
  let mut externs := ""; let mut emittedExt : NameSet := {}
  for c in usedConsts do if !constNames.contains c && !emittedExt.contains c then if let some (.defnInfo cd) := env.find? c then if let some cm ← analyzeFn? c cd.type cd.value then
    emittedExt := emittedExt.insert c; externs := externs ++ s!"extern {cm.retCTy} {cm.cName}({if cm.params.isEmpty then "void" else String.intercalate ", " (cm.params.map (·.2.1))});\n"
  let mut fnBodies := ""; let mut emittedStatics : NameSet := {}; let mut fileTables := ""
  for fm in fns do
    let some (.defnInfo d) := env.find? fm.leanName | continue
    let st ← lambdaTelescope d.value fun xs body => do
      let mut init : State := { staticsMap }; let mut outSpec : List (Nat × String × OutKind) := []; let mut origOut : List (FVarId × String × OutKind) := []
      for (fv, (pName, ct, ok?)) in xs.toList.zip fm.params do
        init := { init with vars := init.vars.insert fv.fvarId! [(pName, pName, ct)], used := init.used.insert (.str .anonymous pName), mutLocals := (pName, ct) :: init.mutLocals }
        if let some ok := ok? then outSpec := outSpec ++ [(outSpec.length + 1, pName, ok)]; origOut := origOut ++ [(fv.fvarId!, pName, ok)]; init := { init with vars := init.vars.insert fv.fvarId! [(pName, s!"(*{pName})", match ok with | .codePtr => "code *" | .uint32 => "unsigned")] }
      init := { init with origOutFVars := origOut }
      return (← (lowerBindable body (if outSpec.isEmpty then .ret (fm.retCTy == "void") else .outTuple outSpec (fm.retCTy == "void"))).run init).2
    let mut fnLocalTbls := ""
    for (tblName, sname, isLocOnly) in st.usedStatics.toList.map (fun (s, t) => (t, s, false)) ++ st.localTbls.toList.map (fun t => (t, cIdent t, true)) do
      if let some (.defnInfo td) := env.find? tblName then
        let (lk?, inner) := unwrapLinkage td.type.getForallBody; let isLocal := isLocOnly && (lk?.any (·.2.2.2))
        if isLocal || !emittedStatics.contains tblName then
          let decl ← emitStaticArray evalPureInt? sname (arrElemCTy (if isLocOnly then inner else td.type.getForallBody)) td.value
          if isLocal then fnLocalTbls := fnLocalTbls ++ "    " ++ decl else emittedStatics := emittedStatics.insert tblName; fileTables := fileTables ++ decl
    fnBodies := fnBodies ++ fmtProto fm ++ " {\n" ++ fnLocalTbls ++ String.intercalate "\n" st.lines.toList ++ "\n}\n"
  let mut protos := ""
  for fm in fns do if [Linkage.static, .staticInline, .hidden].contains fm.link then protos := protos ++ fmtProto fm ++ ";\n"
  return pre ++ structDefs ++ globals ++ externs ++ protos ++ fileTables ++ fnBodies
end Lean2C.Simple
