import C99.Libc

/-!
# C99 LP64 Small-Step Operational Semantics (`C99.Semantics`)

Small-step continuation-based operational semantics directly on `C99.AST`,
over the flat byte-block memory model (`C99.Mem`) and safety-only `C99.Libc`.
Explicitly parameterizes the 2 documented pointer-arithmetic exceptions via `PointerConfig`.
-/

namespace C99

structure PointerConfig where
  allowAddZeroAny : Bool := true
  allowNullDiffNull : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Function prototype signature `(retTy, fixedParamTys, variadic)`. -/
abbrev FnSig := CTy × List CTy × Bool

/-- Environment mapping in-scope identifiers (globals, locals, `errno`) to `(BlockId, CTy)`. -/
abbrev Env := List (String × BlockId × CTy)

structure Prog where
  tags : TypeEnv
  globals : List (Linkage × VarDecl)
  globalEnv : Env := []
  fns : String → Option FnDef
  fnProtos : String → Option FnSig
  fnStatics : String → Env

abbrev ExtHandler := String → List Val → Mem → OSState → ExtOutcome → Prop

structure ModEntry where
  bid : BlockId
  off : Int64
  len : Nat
  deriving DecidableEq, Repr

abbrev ModSet := List ModEntry

def ModSet.conflicts (ms : ModSet) (b : BlockId) (o : Int64) (n : Nat) : Bool :=
  ms.any fun e => e.bid == b && !(e.off.toInt + e.len ≤ o.toInt || o.toInt + n ≤ e.off.toInt)

namespace Sem

/-! ## Pure Value Conversions, Arithmetic, and Memory Scalar/Aggregate Access -/

def isTruthy : Val → Option Bool
  | .int _ v => some (v.toNat != 0)
  | .ptr _ _ | .fnPtr _ => some true
  | .null => some false
  | _ => none

def valAsInt? : Val → Option (IntKind × Int)
  | .int k v => some (k, if k.signed then v.toInt else (v.toNat : Int))
  | _ => none

def ofIntExact (k : IntKind) (v : Int) : Option Val :=
  if k.signed then
    if k.inRange v then some (.int k (BitVec.ofInt k.bits v)) else none
  else some (.int k (BitVec.ofInt k.bits v))

def ofIntCast (k : IntKind) (v : Int) : Val := .int k (BitVec.ofInt k.bits v)

def cmpOrd : BinOp → Int → Int → Bool
  | .eq, a, b => decide (a == b)
  | .ne, a, b => decide (a != b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | _,   a, b => decide (a ≥ b)

def castVal (m : Mem) (target : CTy) (v : Val) : Option Val :=
  let ut := target.unqual
  if ut.isVoid then some .void
  else if let some k := ut.intKind? then
    match v with
    | .int k1 bv => some (ofIntCast k (if k1.signed then bv.toInt else (bv.toNat : Int)))
    | .null => some (.int k 0)
    | .ptr b off => (m.addrOf b off).map fun a => .int k (BitVec.ofNat k.bits a.toNat)
    | _ => none
  else match ut, v with
    | .ptr _, .null => some .null
    | .ptr _, .ptr b off => some (.ptr b off)
    | .ptr _, .int _ bv => if bv.toNat == 0 then some .null else none
    | .fnPtr _ _ _, .null => some .null
    | .fnPtr _ _ _, .fnPtr s => some (.fnPtr s)
    | .fnPtr _ _ _, .int _ bv => if bv.toNat == 0 then some .null else none
    | .vaList, .vaList true => some (.vaList true)
    | _, _ => none

def promoteVariadicArg : Val → Val
  | .int k bv =>
    let k' := k.promote
    if k' == k then .int k bv
    else .int k' (BitVec.ofInt k'.bits (if k.signed then bv.toInt else (bv.toNat : Int)))
  | v => v

def coerceCallArgs (m : Mem) (paramTys : List CTy) (variadic : Bool) (args : List (Val × CTy)) :
    Option (List Val) := do
  if variadic then
    guard (paramTys.length ≤ args.length)
    let fixed ← (paramTys.zip (args.take paramTys.length)).mapM fun (pty, (v, _)) => castVal m pty v
    return fixed ++ (args.drop paramTys.length).map fun (v, _) => promoteVariadicArg v
  else
    guard (args.length == paramTys.length)
    (paramTys.zip args).mapM fun (pty, (v, _)) => castVal m pty v

def evalUnary (op : UnOp) (v : Val) : Option (Val × CTy) :=
  match op with
  | .plus => do let (k, iv) ← valAsInt? v; return (← ofIntExact k.promote iv, .int k.promote)
  | .neg => do let (k, iv) ← valAsInt? v; return (← ofIntExact k.promote (-iv), .int k.promote)
  | .bitNot => match v with
    | .int k bv =>
      let k' := k.promote
      let iv := if k.signed then bv.toInt else (bv.toNat : Int)
      some (.int k' (~~~(BitVec.ofInt k'.bits iv)), .int k')
    | _ => none
  | .logNot => do let b ← isTruthy v; return (.int .i32 (if b then 0 else 1), .int .i32)

def evalPtrAdd (cfg : PointerConfig) (tags : TypeEnv) (m : Mem)
    (p : Val) (elemTy : CTy) (idx : Int) : Option Val :=
  if idx == 0 && cfg.allowAddZeroAny then
    match p with | .null | .ptr _ _ => some p | _ => none
  else match p with
    | .ptr b off => do
      let blk ← m.blocks b
      let newOff := off.toInt + idx * (max 1 (sizeofTy tags elemTy) : Int)
      guard (0 ≤ newOff && newOff ≤ (blk.size : Int))
      return .ptr b (Int64.ofInt newOff)
    | _ => none

def evalPtrDiff (cfg : PointerConfig) (tags : TypeEnv) (m : Mem)
    (p q : Val) (elemTy : CTy) : Option Val :=
  match p, q with
  | .null, .null => if cfg.allowNullDiffNull then some (.int .i64 0) else none
  | .ptr b1 o1, .ptr b2 o2 => do
    guard (b1 == b2)
    let blk ← m.blocks b1
    guard (0 ≤ o1.toInt && o1.toInt ≤ (blk.size : Int) && 0 ≤ o2.toInt && o2.toInt ≤ (blk.size : Int))
    let elemSz : Int := max 1 (sizeofTy tags elemTy)
    let diff := o1.toInt - o2.toInt
    guard (diff % elemSz == 0)
    ofIntExact .i64 (diff / elemSz)
  | _, _ => none

def evalPtrCmp (m : Mem) (op : BinOp) (p q : Val) : Option Val :=
  let isNull : Val → Bool | .null => true | .int _ bv => bv.toNat == 0 | _ => false
  match op with
  | .eq | .ne =>
    let eq? : Option Bool := match p, q with
      | .ptr b1 o1, .ptr b2 o2 => some (b1 == b2 && o1 == o2)
      | .fnPtr s1, .fnPtr s2 => some (s1 == s2)
      | .ptr _ _, _ | .fnPtr _, _ => if isNull q then some false else none
      | _, .ptr _ _ | _, .fnPtr _ => if isNull p then some false else none
      | _, _ => if isNull p && isNull q then some true else none
    eq?.map fun eq => .int .i32 (if (if op == .eq then eq else !eq) then 1 else 0)
  | .lt | .le | .gt | .ge => match p, q with
    | .ptr b1 o1, .ptr b2 o2 => do
      guard (b1 == b2)
      let blk ← m.blocks b1
      guard (0 ≤ o1.toInt && o1.toInt ≤ (blk.size : Int) && 0 ≤ o2.toInt && o2.toInt ≤ (blk.size : Int))
      return .int .i32 (if cmpOrd op o1.toInt o2.toInt then 1 else 0)
    | _, _ => none
  | _ => none

def evalIntBinary (op : BinOp) (v1 v2 : Val) : Option (Val × CTy) := do
  let (k1, i1) ← valAsInt? v1
  let (k2, i2) ← valAsInt? v2
  match op with
  | .shl | .shr =>
    let lk := k1.promote
    guard (0 ≤ i2 && i2 < (lk.bits : Int))
    let sh := i2.toNat
    if lk.signed then
      guard (0 ≤ i1)
      let raw := if op == .shl then i1 * (2 ^ sh : Int) else i1 / (2 ^ sh : Int)
      return (← ofIntExact lk raw, .int lk)
    else
      let bv := BitVec.ofInt lk.bits i1
      return (.int lk (if op == .shl then bv <<< sh else bv >>> sh), .int lk)
  | _ =>
    let ck := IntKind.usualArith k1 k2
    let (c1, c2) := (BitVec.ofInt ck.bits i1, BitVec.ofInt ck.bits i2)
    let n1 := if ck.signed then c1.toInt else (c1.toNat : Int)
    let n2 := if ck.signed then c2.toInt else (c2.toNat : Int)
    match op with
    | .eq | .ne | .lt | .le | .gt | .ge =>
      return (.int .i32 (if cmpOrd op n1 n2 then 1 else 0), .int .i32)
    | _ =>
      let res : Option Val := match op with
        | .add => ofIntExact ck (n1 + n2) | .sub => ofIntExact ck (n1 - n2)
        | .mul => ofIntExact ck (n1 * n2)
        | .div => if n2 == 0 then none else ofIntExact ck (Int.tdiv n1 n2)
        | .mod => if n2 == 0 then none else ofIntExact ck (Int.tmod n1 n2)
        | .bitAnd => some (.int ck (c1 &&& c2)) | .bitOr => some (.int ck (c1 ||| c2))
        | .bitXor => some (.int ck (c1 ^^^ c2)) | _ => none
      return (← res, .int ck)

def applyBinary (cfg : PointerConfig) (tags : TypeEnv) (m : Mem)
    (op : BinOp) (v1 : Val) (t1 : CTy) (v2 : Val) (t2 : CTy) : Option (Val × CTy) :=
  let isFn : CTy → Bool | t => match t.unqual with | .fnPtr .. => true | _ => false
  if t1.isPtr || t2.isPtr || isFn t1 || isFn t2 then
    match op with
    | .add =>
      if t1.isPtr then match t1.unqual, valAsInt? v2 with
        | .ptr el, some (_, idx) => (evalPtrAdd cfg tags m v1 el idx).map (·, t1.unqual) | _, _ => none
      else match t2.unqual, valAsInt? v1 with
        | .ptr el, some (_, idx) => (evalPtrAdd cfg tags m v2 el idx).map (·, t2.unqual) | _, _ => none
    | .sub =>
      if t1.isPtr && t2.isPtr then match t1.unqual with
        | .ptr el => (evalPtrDiff cfg tags m v1 v2 el).map (·, .int .i64) | _ => none
      else if t1.isPtr then match t1.unqual, valAsInt? v2 with
        | .ptr el, some (_, idx) => (evalPtrAdd cfg tags m v1 el (-idx)).map (·, t1.unqual) | _, _ => none
      else none
    | .eq | .ne | .lt | .le | .gt | .ge => (evalPtrCmp m op v1 v2).map (·, .int .i32)
    | _ => none
  else evalIntBinary op v1 v2

def readVal (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) : Option Val := do
  let ut := ty.unqual
  match ut with
  | .array _ _ => return .ptr b off
  | .int _ | .enumTy _ _ =>
    let k ← ut.intKind?
    let blk ← m.blocks b
    guard (Mem.isAligned blk off k.align)
    return .int k (← Mem.decodeInt k (← m.readBytes b off k.bytes))
  | .ptr _ =>
    let blk ← m.blocks b
    guard (Mem.isAligned blk off 8)
    match ← Mem.decodePtr (← m.readBytes b off 8) with
    | .null => return .null | .ptr pb poff => return .ptr pb poff | .fnPtr _ => none
  | .fnPtr _ _ _ =>
    let blk ← m.blocks b
    guard (Mem.isAligned blk off 8)
    match ← Mem.decodePtr (← m.readBytes b off 8) with
    | .null => return .null | .fnPtr s => return .fnPtr s | .ptr _ _ => none
  | .vaList =>
    let bs ← m.readBytes b off (sizeofTy tags ut)
    guard (bs.all (· == .byte 1))
    return .vaList true
  | _ => none

def writeVal (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) (v : Val) : Option Mem := do
  guard (!ty.isConst)
  let blk ← m.blocks b
  match ty.unqual with
  | .int _ | .enumTy _ _ =>
    let k ← ty.unqual.intKind?
    guard (Mem.isAligned blk off k.align)
    let (_, iv) ← valAsInt? v
    m.writeBytes b off (Mem.encodeInt k (BitVec.ofInt k.bits iv))
  | .ptr _ =>
    guard (Mem.isAligned blk off 8)
    match v with
    | .null => m.writeBytes b off Mem.encodeNull
    | .ptr pb poff => m.writeBytes b off (Mem.encodePtr pb poff)
    | .int _ bv => if bv.toNat == 0 then m.writeBytes b off Mem.encodeNull else none
    | _ => none
  | .fnPtr _ _ _ =>
    guard (Mem.isAligned blk off 8)
    match v with
    | .null => m.writeBytes b off Mem.encodeNull
    | .fnPtr s => m.writeBytes b off (Mem.encodeFnPtr s)
    | .int _ bv => if bv.toNat == 0 then m.writeBytes b off Mem.encodeNull else none
    | _ => none
  | .vaList =>
    match v with
    | .vaList true => m.writeBytes b off (List.replicate 24 (.byte 1))
    | _ => none
  | _ => none

/-! ## `sizeof(expr)`, Enum Lookup, Continuations, and Jump Unwinding -/

def enumConst? : TypeEnv → String → Option Int
  | [], _ => none
  | (_, .enumDef items _) :: rest, name =>
    let rec scan (nextVal : Int) : List (String × Option Int) → Option Int
      | [] => enumConst? rest name
      | (k, v?) :: tl => let v := v?.getD nextVal; if k == name then some v else scan (v + 1) tl
    scan 0 items
  | _ :: rest, name => enumConst? rest name

def exprType? (tags : TypeEnv) (env : Env) (fnProtos : String → Option FnSig) : CExpr → Option CTy
  | .paren e => exprType? tags env fnProtos e
  | .lit _ k _ _ _ => some (.int k)
  | .strLit s => some (.array (.const_ (.int .i8)) (some (s.utf8ByteSize + 1)))
  | .var x =>
    match env.lookup x with
    | some (_, ty) => some ty
    | none => if (enumConst? tags x).isSome then some (.int .i32)
              else (fnProtos x).map fun (r, ps, v) => .fnPtr r ps v
  | .sizeOfTy _ | .sizeOfExpr _ => some (.int .u64)
  | .cast ty _ => some ty
  | .unary op e =>
    if op == .logNot then some (.int .i32)
    else (exprType? tags env fnProtos e).bind fun t => t.intKind?.map fun k => .int k.promote
  | .addrOf e => (exprType? tags env fnProtos e).map .ptr
  | .deref e => do
    match (← exprType? tags env fnProtos e).decay.unqual with
    | .ptr el => return el
    | .fnPtr rt ps va => return .fnPtr rt ps va
    | _ => none
  | .index e _ => do
    let .ptr el := (← exprType? tags env fnProtos e).decay.unqual | none
    return el
  | .member b fld => (exprType? tags env fnProtos b).bind (fieldLayout? tags · fld) |>.map (·.2)
  | .arrow b fld => do
    let .ptr sty := (← exprType? tags env fnProtos b).decay.unqual | none
    return (← fieldLayout? tags sty fld).2
  | .binary op l r => do
    let lt ← (exprType? tags env fnProtos l).map CTy.decay
    let rt ← (exprType? tags env fnProtos r).map CTy.decay
    if lt.isPtr || rt.isPtr then match op with
      | .add => some (if lt.isPtr then lt.unqual else rt.unqual)
      | .sub => some (if lt.isPtr && rt.isPtr then .int .i64 else lt.unqual)
      | _ => some (.int .i32)
    else
      let lk ← lt.intKind?; let rk ← rt.intKind?
      match op with
      | .shl | .shr => some (.int lk.promote)
      | .eq | .ne | .lt | .le | .gt | .ge => some (.int .i32)
      | _ => some (.int (IntKind.usualArith lk rk))
  | .logAnd _ _ | .logOr _ _ => some (.int .i32)
  | .cond _ t _ => exprType? tags env fnProtos t
  | .comma _ r | .assign _ r _ | .incDec _ r => exprType? tags env fnProtos r
  | .call fn _ => do
    let .fnPtr rt _ _ := (← exprType? tags env fnProtos fn).decay.unqual | none
    return rt
  | .vaStart _ _ | .vaEnd _ => some .void

inductive Want where | rval | lval deriving DecidableEq

inductive ExprRes where
  | rval (v : Val) (ty : CTy)
  | lval (b : BlockId) (off : Int64) (ty : CTy)
  | structVal (bs : List MemByte) (ty : CTy)

inductive ExprFrame where
  | unaryF (op : UnOp)
  | binLhsF (op : BinOp) (r : CExpr)
  | binRhsF (op : BinOp) (v1 : Val) (t1 : CTy)
  | logAndF (r : CExpr) | logAndEndF | logOrF (r : CExpr) | logOrEndF
  | condF (t f : CExpr) | commaF (r : CExpr) | castF (ty : CTy)
  | derefF (want : Want) | addrOfF
  | indexBaseF (want : Want) (idx : CExpr) | indexIdxF (want : Want) (p : Val) (pty : CTy)
  | memberF (want : Want) (fld : String) | arrowF (want : Want) (fld : String)
  | assignLhsF (op : AssignOp) (rhs : CExpr)
  | assignRhsF (op : AssignOp) (b : BlockId) (off : Int64) (lty : CTy)
  | incDecF (op : IncDecOp) | callFnF (args : List CExpr)
  | callArgF (sym : String) (fnTy : CTy) (done : List (Val × CTy)) (todo : List CExpr)

inductive ExprState where
  | eval (want : Want) (e : CExpr) (frames : List ExprFrame)
  | ret (res : ExprRes) (frames : List ExprFrame)

inductive ExprCtx where
  | discard | returnVal | varInit (decl : VarDecl) (restDecls : List VarDecl)
  | branch (t f : CStmt) | whileCond (c : CExpr) (body : CStmt)
  | doWhileCond (body : CStmt) (c : CExpr)
  | forCond (c : CExpr) (step? : Option CExpr) (body : CStmt)
  | forStep (c? : Option CExpr) (step? : Option CExpr) (body : CStmt) | switchScrut (body : CStmt)

inductive Cont where
  | stop (retTy : CTy) | stmts (ss : List CStmt) (k : Cont)
  | blockEnd (savedEnv : Env) (stackBlks : List BlockId) (k : Cont)
  | loop (cond? : Option CExpr) (step? : Option CExpr) (body : CStmt) (isDo : Bool) (k : Cont)
  | switchCont (k : Cont)
  | callFrame (retEnv : Env) (retStackBlks : List BlockId) (retTy : CTy) (fnBody : CStmt)
      (frames : List ExprFrame) (ctx : ExprCtx) (k : Cont)

inductive Control where
  | stmt (s : CStmt)
  | expr (es : ExprState) (ctx : ExprCtx) (mods : ModSet)

inductive RunState where
  | running (ctrl : Control) (env : Env) (stackBlks : List BlockId) (m : Mem) (os : OSState) (k : Cont)
  | returned (v : Val) (m : Mem) (os : OSState)
  | ub

def RunState.isUB : RunState → Bool | .ub => true | _ => false

mutual
def findSwitchList (scrut : Int) (wantDef : Bool) : List CStmt → Option (List CStmt)
  | [] => none
  | hd :: tl => match findSwitchStmt scrut wantDef hd with
    | some found => some (found :: tl) | none => findSwitchList scrut wantDef tl

def findSwitchStmt (scrut : Int) (wantDef : Bool) : CStmt → Option CStmt
  | .caseStmt v body =>
    if !wantDef && v == scrut then some body else findSwitchStmt scrut wantDef body
  | .defaultStmt body => if wantDef then some body else findSwitchStmt scrut wantDef body
  | .labelStmt _ body => findSwitchStmt scrut wantDef body
  | .block ss => (findSwitchList scrut wantDef ss).map .block
  | .ifStmt _ t f? => match findSwitchStmt scrut wantDef t with
    | some s => some s | none => match f? with | some f => findSwitchStmt scrut wantDef f | none => none
  | _ => none
end

def findSwitchTarget (scrut : Int) (s : CStmt) : Option CStmt :=
  (findSwitchStmt scrut false s).orElse fun _ => findSwitchStmt scrut true s

mutual
def findInStmts (lbl : String) (env : Env) (blks : List BlockId) (kBlk : Cont) :
    List CStmt → Option (CStmt × Env × List BlockId × Cont)
  | [] => none
  | hd :: tl =>
    let k' := if tl.isEmpty then kBlk else .stmts tl kBlk
    match findInStmt lbl env blks hd k' with
    | some res => some res | none => findInStmts lbl env blks kBlk tl

def findInStmt (lbl : String) (env : Env) (blks : List BlockId) (s : CStmt) (k : Cont) :
    Option (CStmt × Env × List BlockId × Cont) :=
  match s with
  | .labelStmt l body => if l == lbl then some (body, env, blks, k) else findInStmt lbl env blks body k
  | .block ss => findInStmts lbl env [] (.blockEnd env blks k) ss
  | .ifStmt _ t f? => match findInStmt lbl env blks t k with
    | some res => some res | none => match f? with | some f => findInStmt lbl env blks f k | none => none
  | .whileStmt c body => findInStmt lbl env blks body (.loop (some c) none body false k)
  | .doWhileStmt body c => findInStmt lbl env blks body (.loop (some c) none body true k)
  | .forStmt _ c? stp? body => findInStmt lbl env blks body (.loop c? stp? body false k)
  | .switchStmt _ body => findInStmt lbl env blks body (.switchCont k)
  | .caseStmt _ body | .defaultStmt body => findInStmt lbl env blks body k
  | _ => none
end

def gotoInCont (lbl : String) (m : Mem) (env : Env) (blks : List BlockId) :
    Cont → Option (CStmt × Env × List BlockId × Mem × Cont)
  | .stop _ => none
  | .stmts ss rest => match findInStmts lbl env blks rest ss with
    | some (s', e', b', k') => some (s', e', b', m, k') | none => gotoInCont lbl m env blks rest
  | .blockEnd savedEnv savedBlks rest => gotoInCont lbl (m.freeStack blks) savedEnv savedBlks rest
  | .loop c? stp? body isDo rest =>
    match findInStmt lbl env blks body (.loop c? stp? body isDo rest) with
    | some (s', e', b', k') => some (s', e', b', m, k') | none => gotoInCont lbl m env blks rest
  | .switchCont rest => gotoInCont lbl m env blks rest
  | .callFrame re rb rt fnBody fs ctx rest =>
    match findInStmt lbl env blks fnBody (.callFrame re rb rt fnBody fs ctx rest) with
    | some (s', e', b', k') => some (s', e', b', m, k') | none => none

def unwindBreak (m : Mem) (env : Env) (blks : List BlockId) :
    Cont → Option (Env × List BlockId × Mem × Cont)
  | .stmts _ rest => unwindBreak m env blks rest
  | .blockEnd savedEnv savedBlks rest => unwindBreak (m.freeStack blks) savedEnv savedBlks rest
  | .loop _ _ _ _ rest | .switchCont rest => some (env, blks, m, rest)
  | _ => none

def unwindContinue (m : Mem) (env : Env) (blks : List BlockId) :
    Cont → Option (Option CExpr × Option CExpr × CStmt × Bool × Env × List BlockId × Mem × Cont)
  | .stmts _ rest | .switchCont rest => unwindContinue m env blks rest
  | .blockEnd savedEnv savedBlks rest => unwindContinue (m.freeStack blks) savedEnv savedBlks rest
  | .loop c? stp? body isDo rest => some (c?, stp?, body, isDo, env, blks, m, rest)
  | _ => none

def unwindReturn (m : Mem) (blks : List BlockId) :
    Cont → Option (Env × List BlockId × CTy × Mem × List ExprFrame × ExprCtx × Cont)
  | .stmts _ rest | .loop _ _ _ _ rest | .switchCont rest => unwindReturn m blks rest
  | .blockEnd _ savedBlks rest => unwindReturn (m.freeStack blks) savedBlks rest
  | .callFrame re rb rt _ fs ctx rest => some (re, rb, rt, m.freeStack blks, fs, ctx, rest)
  | .stop _ => none

def Cont.topRetTy : Cont → CTy
  | .stop rt => rt | .callFrame _ _ rt _ _ _ _ => rt
  | .stmts _ k | .blockEnd _ _ k | .loop _ _ _ _ k | .switchCont k => k.topRetTy

/-! ## Expression & Statement Transition Functions -/

def assignOpToBin? : AssignOp → Option BinOp
  | .eq => none | .addEq => some .add | .subEq => some .sub | .mulEq => some .mul
  | .divEq => some .div | .modEq => some .mod | .andEq => some .bitAnd
  | .orEq => some .bitOr | .xorEq => some .bitXor | .shlEq => some .shl | .shrEq => some .shr

def readPlace (tags : TypeEnv) (m : Mem) (mods : ModSet) (want : Want)
    (b : BlockId) (off : Int64) (ty : CTy) : Option ExprRes :=
  match want with
  | .lval => some (.lval b off ty)
  | .rval => match ty.unqual with
    | .array _ _ => some (.rval (.ptr b off) ty.decay)
    | .structTy _ | .unionTy _ | .anonStruct _ | .anonUnion _ => do
      let sz := sizeofTy tags ty; guard (!mods.conflicts b off sz)
      (m.readBytes b off sz).map (ExprRes.structVal · ty)
    | _ => do
      guard (!mods.conflicts b off (sizeofTy tags ty))
      (readVal tags m b off ty).map (ExprRes.rval · ty.decay)

def writePlace (tags : TypeEnv) (m : Mem) (b : BlockId) (off : Int64) (ty : CTy) (rv : ExprRes) :
    Option (ExprRes × Mem) :=
  match rv with
  | .structVal bs _ =>
    if bs.length == sizeofTy tags ty then (m.writeBytes b off bs).map (ExprRes.structVal bs ty, ·) else none
  | .rval v _ => do
    let cv ← match ty.unqual with
      | .int _ | .enumTy _ _ | .ptr _ | .fnPtr _ _ _ => castVal m ty v | _ => some v
    return (.rval cv ty, ← writeVal m b off ty cv)
  | .lval _ _ _ => none

def stepExprPure (prog : Prog) (cfg : PointerConfig) (env : Env) (m : Mem) (mods : ModSet) :
    ExprState → Option (ExprState × Mem × ModSet)
  | .eval w (.paren e) fs => some (.eval w e fs, m, mods)
  | .eval .rval (.lit v k _ _ _) fs => some (.ret (.rval (ofIntCast k v) (.int k)) fs, m, mods)
  | .eval .lval (.var x) fs => (env.lookup x).map fun (b, ty) => (.ret (.lval b 0 ty) fs, m, mods)
  | .eval .rval (.var x) fs => match env.lookup x with
    | some (b, ty) => (readPlace prog.tags m mods .rval b 0 ty).map fun r => (.ret r fs, m, mods)
    | none => match enumConst? prog.tags x with
      | some ev => some (.ret (.rval (ofIntCast .i32 ev) (.int .i32)) fs, m, mods)
      | none => (prog.fnProtos x).map fun (r, ps, v) => (.ret (.rval (.fnPtr x) (.fnPtr r ps v)) fs, m, mods)
  | .eval .rval (.sizeOfTy ty) fs =>
    some (.ret (.rval (.int .u64 (BitVec.ofNat 64 (sizeofTy prog.tags ty))) (.int .u64)) fs, m, mods)
  | .eval .rval (.sizeOfExpr e) fs => (exprType? prog.tags env prog.fnProtos e).map fun ty =>
    (.ret (.rval (.int .u64 (BitVec.ofNat 64 (sizeofTy prog.tags ty))) (.int .u64)) fs, m, mods)
  | .eval .rval (.unary op e) fs => some (.eval .rval e (.unaryF op :: fs), m, mods)
  | .eval .rval (.binary op l r) fs => some (.eval .rval l (.binLhsF op r :: fs), m, mods)
  | .eval .rval (.logAnd l r) fs => some (.eval .rval l (.logAndF r :: fs), m, mods)
  | .eval .rval (.logOr l r) fs => some (.eval .rval l (.logOrF r :: fs), m, mods)
  | .eval .rval (.cond c t f) fs => some (.eval .rval c (.condF t f :: fs), m, mods)
  | .eval .rval (.comma l r) fs => some (.eval .rval l (.commaF r :: fs), m, mods)
  | .eval .rval (.cast ty e) fs => some (.eval .rval e (.castF ty :: fs), m, mods)
  | .eval w (.deref e) fs => some (.eval .rval e (.derefF w :: fs), m, mods)
  | .eval .rval (.addrOf e) fs => some (.eval .lval e (.addrOfF :: fs), m, mods)
  | .eval w (.index b i) fs => some (.eval .rval b (.indexBaseF w i :: fs), m, mods)
  | .eval w (.member b f) fs => some (.eval .lval b (.memberF w f :: fs), m, mods)
  | .eval w (.arrow b f) fs => some (.eval .rval b (.arrowF w f :: fs), m, mods)
  | .eval .rval (.assign op l r) fs => some (.eval .lval l (.assignLhsF op r :: fs), m, mods)
  | .eval .rval (.incDec op l) fs => some (.eval .lval l (.incDecF op :: fs), m, mods)
  | .eval .rval (.call fn args) fs => some (.eval .rval fn (.callFnF args :: fs), m, mods)
  | .eval .rval (.vaStart ap _) fs => do
    let (b, ty) ← env.lookup ap; guard ty.isVaList
    let m' ← m.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) (.byte 1))
    return (.ret (.rval .void .void) fs, m', mods)
  | .eval .rval (.vaEnd ap) fs => do
    let (b, ty) ← env.lookup ap; guard ty.isVaList
    let m' ← m.writeBytes b 0 (List.replicate (sizeofTy prog.tags .vaList) .undef)
    return (.ret (.rval .void .void) fs, m', mods)
  | .ret (.rval v _) (.unaryF op :: fs) => (evalUnary op v).map fun (rv, rt) => (.ret (.rval rv rt) fs, m, mods)
  | .ret (.rval v1 t1) (.binLhsF op r :: fs) => some (.eval .rval r (.binRhsF op v1 t1 :: fs), m, mods)
  | .ret (.rval v2 t2) (.binRhsF op v1 t1 :: fs) =>
    (applyBinary cfg prog.tags m op v1 t1 v2 t2).map fun (rv, rt) => (.ret (.rval rv rt) fs, m, mods)
  | .ret (.rval v1 _) (.logAndF r :: fs) => do
    if !(← isTruthy v1) then return (.ret (.rval (.int .i32 0) (.int .i32)) fs, m, mods)
    else return (.eval .rval r (.logAndEndF :: fs), m, [])
  | .ret (.rval v2 _) (.logAndEndF :: fs) => do
    return (.ret (.rval (.int .i32 (if ← isTruthy v2 then 1 else 0)) (.int .i32)) fs, m, mods)
  | .ret (.rval v1 _) (.logOrF r :: fs) => do
    if (← isTruthy v1) then return (.ret (.rval (.int .i32 1) (.int .i32)) fs, m, mods)
    else return (.eval .rval r (.logOrEndF :: fs), m, [])
  | .ret (.rval v2 _) (.logOrEndF :: fs) => do
    return (.ret (.rval (.int .i32 (if ← isTruthy v2 then 1 else 0)) (.int .i32)) fs, m, mods)
  | .ret (.rval vc _) (.condF t f :: fs) => do
    return (.eval .rval (if ← isTruthy vc then t else f) fs, m, [])
  | .ret _ (.commaF r :: fs) => some (.eval .rval r fs, m, [])
  | .ret (.rval v _) (.castF ty :: fs) => (castVal m ty v).map fun cv => (.ret (.rval cv ty) fs, m, mods)
  | .ret (.rval p pty) (.derefF w :: fs) => do
    match pty.unqual with
    | .ptr el =>
      let (.ptr b off) := p | none
      return (.ret (← readPlace prog.tags m mods w b off el) fs, m, mods)
    | .fnPtr rt ps va =>
      guard (w == .rval)
      let (.fnPtr sym) := p | none
      return (.ret (.rval (.fnPtr sym) (.fnPtr rt ps va)) fs, m, mods)
    | _ => none
  | .ret (.lval b off ty) (.addrOfF :: fs) => some (.ret (.rval (.ptr b off) (.ptr ty)) fs, m, mods)
  | .ret (.rval p pty) (.indexBaseF w idx :: fs) => some (.eval .rval idx (.indexIdxF w p pty :: fs), m, mods)
  | .ret (.rval iv _) (.indexIdxF w p pty :: fs) => do
    let .ptr el := pty.unqual | none
    let (_, idx) ← valAsInt? iv
    let (.ptr b off) ← evalPtrAdd cfg prog.tags m p el idx | none
    return (.ret (← readPlace prog.tags m mods w b off el) fs, m, mods)
  | .ret (.lval b off ty) (.memberF w fld :: fs) => do
    let (foff, fty) ← fieldLayout? prog.tags ty fld
    return (.ret (← readPlace prog.tags m mods w b (Int64.ofInt (off.toInt + foff)) fty) fs, m, mods)
  | .ret (.rval p pty) (.arrowF w fld :: fs) => do
    let .ptr sty := pty.unqual | none
    let (.ptr b off) := p | none
    let (foff, fty) ← fieldLayout? prog.tags sty fld
    return (.ret (← readPlace prog.tags m mods w b (Int64.ofInt (off.toInt + foff)) fty) fs, m, mods)
  | .ret (.lval b off lty) (.assignLhsF op rhs :: fs) =>
    some (.eval .rval rhs (.assignRhsF op b off lty :: fs), m, mods)
  | .ret rv (.assignRhsF op b off lty :: fs) => do
    let sz := sizeofTy prog.tags lty; guard (!mods.conflicts b off sz)
    let rhsVal ← match assignOpToBin? op with
      | none => some rv
      | some bop => do
        let oldV ← readVal prog.tags m b off lty
        let (.rval rval rty) := rv | none
        let (nv, _) ← applyBinary cfg prog.tags m bop oldV lty rval rty
        pure (ExprRes.rval nv lty)
    let (res, m') ← writePlace prog.tags m b off lty rhsVal
    return (.ret res fs, m', ⟨b, off, sz⟩ :: mods)
  | .ret (.lval b off lty) (.incDecF op :: fs) => do
    let sz := sizeofTy prog.tags lty; guard (!mods.conflicts b off sz)
    let oldV ← readVal prog.tags m b off lty
    let d : Int := match op with | .preInc | .postInc => 1 | .preDec | .postDec => -1
    let (newV, _) ← applyBinary cfg prog.tags m .add oldV lty (.int .i32 (BitVec.ofInt 32 d)) (.int .i32)
    let m' ← writeVal m b off lty newV
    return (.ret (.rval (match op with | .preInc | .preDec => newV | _ => oldV) lty) fs, m', ⟨b, off, sz⟩ :: mods)
  | .ret (.rval (.fnPtr sym) fnTy) (.callFnF (arg :: rest) :: fs) =>
    some (.eval .rval arg (.callArgF sym fnTy [] rest :: fs), m, mods)
  | .ret (.rval v ty) (.callArgF sym fnTy done (arg :: rest) :: fs) =>
    some (.eval .rval arg (.callArgF sym fnTy (done ++ [(v, ty)]) rest :: fs), m, mods)
  | _ => none

def loopNext (c? stp? : Option CExpr) (body : CStmt) (isDo : Bool)
    (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont) : RunState :=
  match isDo, stp?, c? with
  | true, _, some c => .running (.expr (.eval .rval c []) (.doWhileCond body c) []) env blks m os k
  | true, _, none => .running (.stmt body) env blks m os (.loop none none body true k)
  | false, some stp, _ => .running (.expr (.eval .rval stp []) (.forStep c? stp? body) []) env blks m os k
  | false, none, some c => .running (.expr (.eval .rval c []) (.forCond c none body) []) env blks m os k
  | false, none, none => .running (.stmt body) env blks m os (.loop none none body false k)

inductive DetStep where
  | next (s : RunState)
  | allocStr (s : String) (fs : List ExprFrame) (ctx : ExprCtx) (mods : ModSet)
      (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont)
  | allocLocal (d : VarDecl) (initVal? : Option ExprRes) (rest : List VarDecl)
      (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont)
  | callFn (sym : String) (fnTy : CTy) (argVals : List (Val × CTy)) (fs : List ExprFrame)
      (ctx : ExprCtx) (env : Env) (blks : List BlockId) (m : Mem) (os : OSState) (k : Cont)

def stepDet (prog : Prog) (cfg : PointerConfig) : RunState → Option DetStep
  | .returned _ _ _ | .ub => none
  | .running (.expr (.eval .rval (.strLit s) fs) ctx mods) env blks m os k =>
    some (.allocStr s fs ctx mods env blks m os k)
  | .running (.expr (.ret (.rval (.fnPtr sym) fnTy) (.callFnF [] :: fs)) ctx _) env blks m os k =>
    some (.callFn sym fnTy [] fs ctx env blks m os k)
  | .running (.expr (.ret (.rval v ty) (.callArgF sym fnTy done [] :: fs)) ctx _) env blks m os k =>
    some (.callFn sym fnTy (done ++ [(v, ty)]) fs ctx env blks m os k)
  | .running (.expr (.ret rv []) ctx _) env blks m os k =>
    let doReturn (v : Val) : Option DetStep :=
      let rt := k.topRetTy
      if rt.isVoid then some (.next (match unwindReturn m blks k with
        | some (re, rb, _, m', fs, rctx, rk) => .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' os rk
        | none => .returned .void (m.freeStack blks) os))
      else (castVal m rt v).map fun cv => .next (match unwindReturn m blks k with
        | some (re, rb, _, m', fs, rctx, rk) => .running (.expr (.ret (.rval cv rt) fs) rctx []) re rb m' os rk
        | none => .returned cv (m.freeStack blks) os)
    let asRval? : Option Val := match rv with | .rval v _ => some v | _ => none
    match ctx with
    | .discard => some (.next (.running (.stmt .nop) env blks m os k))
    | .returnVal => asRval?.bind doReturn
    | .varInit d rest => some (.allocLocal d (some rv) rest env blks m os k)
    | .branch t f => asRval?.bind isTruthy |>.map fun b =>
      .next (.running (.stmt (if b then t else f)) env blks m os k)
    | .whileCond c body => asRval?.bind isTruthy |>.map fun b =>
      .next (if b then .running (.stmt body) env blks m os (.loop (some c) none body false k)
             else .running (.stmt .nop) env blks m os k)
    | .doWhileCond body c => asRval?.bind isTruthy |>.map fun b =>
      .next (if b then .running (.stmt body) env blks m os (.loop (some c) none body true k)
             else .running (.stmt .nop) env blks m os k)
    | .forCond c stp? body => asRval?.bind isTruthy |>.map fun b =>
      .next (if b then .running (.stmt body) env blks m os (.loop (some c) stp? body false k)
             else .running (.stmt .nop) env blks m os k)
    | .forStep c? stp? body => some (.next (match c? with
      | some c => .running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k
      | none => .running (.stmt body) env blks m os (.loop none stp? body false k)))
    | .switchScrut body => (asRval?.bind valAsInt?).map fun (_, iv) =>
      .next (match findSwitchTarget iv body with
        | some tgt => .running (.stmt tgt) env blks m os (.switchCont k)
        | none => .running (.stmt .nop) env blks m os k)
  | .running (.expr es ctx mods) env blks m os k =>
    (stepExprPure prog cfg env m mods es).map fun (es', m', mods') =>
      .next (.running (.expr es' ctx mods') env blks m' os k)
  | .running (.stmt .nop) env blks m os k => match k with
    | .stmts (s :: ss) rest => some (.next (.running (.stmt s) env blks m os (.stmts ss rest)))
    | .stmts [] rest | .switchCont rest => some (.next (.running (.stmt .nop) env blks m os rest))
    | .blockEnd savedEnv savedBlks rest =>
      some (.next (.running (.stmt .nop) savedEnv savedBlks (m.freeStack blks) os rest))
    | .loop c? stp? body isDo rest => some (.next (loopNext c? stp? body isDo env blks m os rest))
    | .stop rt => some (.next (.returned (if rt.isVoid then .void else .undef) (m.freeStack blks) os))
    | .callFrame re rb rt _ fs ctx rest =>
      let rv := if rt.isVoid then .void else .undef
      some (.next (.running (.expr (.ret (.rval rv rt) fs) ctx []) re rb (m.freeStack blks) os rest))
  | .running (.stmt s) env blks m os k => match s with
    | .nop => none
    | .expr e => some (.next (.running (.expr (.eval .rval e []) .discard []) env blks m os k))
    | .decl d => some (.next (.running (.stmt (.decls [d])) env blks m os k))
    | .decls [] => some (.next (.running (.stmt .nop) env blks m os k))
    | .decls (d :: rest) =>
      if d.isStatic then some (.next (.running (.stmt (.decls rest)) env blks m os k))
      else match d.init? with
        | none => some (.allocLocal d none rest env blks m os k)
        | some (.expr e) => some (.next (.running (.expr (.eval .rval e []) (.varInit d rest) []) env blks m os k))
        | some _ => none
    | .block [] => some (.next (.running (.stmt .nop) env blks m os k))
    | .block (hd :: tl) =>
      let kBlk := .blockEnd env blks k
      some (.next (.running (.stmt hd) env [] m os (if tl.isEmpty then kBlk else .stmts tl kBlk)))
    | .ifStmt c t f? => some (.next (.running (.expr (.eval .rval c []) (.branch t (f?.getD .nop)) []) env blks m os k))
    | .whileStmt c body => some (.next (.running (.expr (.eval .rval c []) (.whileCond c body) []) env blks m os k))
    | .doWhileStmt body c => some (.next (.running (.stmt body) env blks m os (.loop (some c) none body true k)))
    | .forStmt (some init) c? stp? body =>
      some (.next (.running (.expr (.eval .rval init []) (.forStep c? stp? body) []) env blks m os k))
    | .forStmt none (some c) stp? body =>
      some (.next (.running (.expr (.eval .rval c []) (.forCond c stp? body) []) env blks m os k))
    | .forStmt none none stp? body =>
      some (.next (.running (.stmt body) env blks m os (.loop none stp? body false k)))
    | .switchStmt scrut body => some (.next (.running (.expr (.eval .rval scrut []) (.switchScrut body) []) env blks m os k))
    | .caseStmt _ body | .defaultStmt body | .labelStmt _ body => some (.next (.running (.stmt body) env blks m os k))
    | .breakStmt => (unwindBreak m env blks k).map fun (e', b', m', k') => .next (.running (.stmt .nop) e' b' m' os k')
    | .continueStmt => (unwindContinue m env blks k).map fun (c?, stp?, b, d, e', b', m', k') =>
      .next (loopNext c? stp? b d e' b' m' os k')
    | .gotoStmt lbl => (gotoInCont lbl m env blks k).map fun (s', e', b', m', k') =>
      .next (.running (.stmt s') e' b' m' os k')
    | .returnStmt none =>
      if k.topRetTy.isVoid then some (.next (match unwindReturn m blks k with
        | some (re, rb, _, m', fs, rctx, rk) => .running (.expr (.ret (.rval .void .void) fs) rctx []) re rb m' os rk
        | none => .returned .void (m.freeStack blks) os))
      else none
    | .returnStmt (some e) => some (.next (.running (.expr (.eval .rval e []) .returnVal []) env blks m os k))

def pushCallParams (tags : TypeEnv) (m : Mem) (base : Nat → UInt64) :
    Nat → List (Param × Val) → Env → List BlockId → Option (Env × List BlockId × Mem)
  | _, [], env, blks => some (env, blks, m)
  | idx, (p, v) :: rest, env, blks =>
    let sz := max 1 (sizeofTy tags p.ty); let al := max 1 (alignofTy tags p.ty); let ba := base idx
    if hsz : sz < ptrDiffLimit then if hal : 0 < al then if hba : ba.toNat % al = 0 then
      let (bid, m1) := m.alloc sz al .rw .stack ba (fun _ => .undef) hsz hal hba
      (writeVal m1 bid 0 p.ty.stripConst v).bind fun m2 =>
        pushCallParams tags m2 base (idx + 1) rest ((p.name, bid, p.ty) :: env) (bid :: blks)
    else none else none else none

/-- Small-step operational relation `Step prog cfg ext s1 s2`. -/
inductive Step (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) :
    RunState → RunState → Prop where
  | det {s1 s2 : RunState} (h : stepDet prog cfg s1 = some (.next s2)) : Step prog cfg ext s1 s2
  | det_ub {ctrl env blks m os k}
      (h : stepDet prog cfg (.running ctrl env blks m os k) = none) :
      Step prog cfg ext (.running ctrl env blks m os k) .ub
  | strLit {s1 : RunState} {str : String} {fs ctx mods env blks base m m' bid os k}
      (hd : stepDet prog cfg s1 = some (.allocStr str fs ctx mods env blks m os k))
      (hsz : str.utf8ByteSize + 1 < ptrDiffLimit)
      (halloc : m.alloc (str.utf8ByteSize + 1) 1 .ro .global base
        (fun i => .byte ((str.toUTF8[i]?).getD 0)) hsz (by decide) (Nat.mod_one _) = (bid, m')) :
      Step prog cfg ext s1
        (.running (.expr (.ret (.rval (.ptr bid 0) (.ptr (.const_ (.int .i8)))) fs) ctx mods) env blks m' os k)
  | localDecl {s1 : RunState} {d init? rest env blks base m m1 m2 bid os k}
      (hd : stepDet prog cfg s1 = some (.allocLocal d init? rest env blks m os k))
      (hsz : max 1 (sizeofTy prog.tags d.ty) < ptrDiffLimit)
      (hal : 0 < max 1 (alignofTy prog.tags d.ty))
      (hba : base.toNat % max 1 (alignofTy prog.tags d.ty) = 0)
      (halloc : m.alloc (max 1 (sizeofTy prog.tags d.ty))
        (max 1 (alignofTy prog.tags d.ty)) .rw .stack base (fun _ => .undef) hsz hal hba = (bid, m1))
      (hwr : match init? with | none => m2 = m1 | some rv => ∃ r, writePlace prog.tags m1 bid 0 d.ty.stripConst rv = some (r, m2)) :
      Step prog cfg ext s1
        (.running (.stmt (.decls rest)) ((d.name, bid, d.ty) :: env) (bid :: blks) m2 os k)
  | localDecl_ub {s1 : RunState} {d init? rest env blks m os k}
      (hd : stepDet prog cfg s1 = some (.allocLocal d init? rest env blks m os k))
      (hbad : ∀ base m1 bid m2 hsz hal hba,
        m.alloc (max 1 (sizeofTy prog.tags d.ty)) (max 1 (alignofTy prog.tags d.ty)) .rw .stack base
          (fun _ => .undef) hsz hal hba = (bid, m1) →
        ¬ match init? with | none => m2 = m1 | some rv => ∃ r, writePlace prog.tags m1 bid 0 d.ty.stripConst rv = some (r, m2)) :
      Step prog cfg ext s1 .ub
  | call_internal {s1 : RunState} {sym fnTy fn argVals coerced fs ctx env callEnv blks callBlks base m m' os k}
      (hd : stepDet prog cfg s1 = some (.callFn sym fnTy argVals fs ctx env blks m os k))
      (hfn : prog.fns sym = some fn)
      (hcoerce : coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced)
      (hpush : pushCallParams prog.tags m base 0
        (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] =
          some (callEnv, callBlks, m')) :
      Step prog cfg ext s1
        (.running (.stmt fn.body) callEnv callBlks m' os (.callFrame env blks fn.retTy fn.body fs ctx k))
  | call_internal_ub {s1 : RunState} {sym fnTy fn argVals fs ctx env blks m os k}
      (hd : stepDet prog cfg s1 = some (.callFn sym fnTy argVals fs ctx env blks m os k))
      (hfn : prog.fns sym = some fn)
      (hbad : ∀ coerced base callEnv callBlks m',
        coerceCallArgs m (fn.params.map (·.ty)) fn.variadic argVals = some coerced →
        pushCallParams prog.tags m base 0
          (fn.params.zip (coerced.take fn.params.length)) ((prog.fnStatics sym) ++ prog.globalEnv) [] ≠
            some (callEnv, callBlks, m')) :
      Step prog cfg ext s1 .ub
  | call_ext {s1 : RunState} {sym fnTy retTy paramTys variadic argVals coerced fs ctx env blks m os out k}
      (hd : stepDet prog cfg s1 = some (.callFn sym fnTy argVals fs ctx env blks m os k))
      (hnfn : prog.fns sym = none)
      (hsig : fnTy.unqual = .fnPtr retTy paramTys variadic)
      (hcoerce : coerceCallArgs m paramTys variadic argVals = some coerced)
      (hext : ext sym coerced m os out) :
      Step prog cfg ext s1 (match out with
        | .ok ret m' os' => .running (.expr (.ret (.rval ret retTy) fs) ctx []) env blks m' os' k | .ub => .ub)
  | call_ext_ub {s1 : RunState} {sym fnTy argVals fs ctx env blks m os k}
      (hd : stepDet prog cfg s1 = some (.callFn sym fnTy argVals fs ctx env blks m os k))
      (hnfn : prog.fns sym = none)
      (hbad : ¬ ∃ retTy paramTys variadic coerced,
        fnTy.unqual = .fnPtr retTy paramTys variadic ∧ coerceCallArgs m paramTys variadic argVals = some coerced) :
      Step prog cfg ext s1 .ub

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Star R x x
  | tail {x y z : α} : Star R x y → R y z → Star R x z

def Safe (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) (s0 : RunState) : Prop :=
  ∀ s', Star (Step prog cfg ext) s0 s' → ¬ s'.isUB

def TerminatesSafely (prog : Prog) (cfg : PointerConfig) (ext : ExtHandler) (s0 : RunState) : Prop :=
  Safe prog cfg ext s0 ∧ ∃ v m os, Star (Step prog cfg ext) s0 (.returned v m os)

/-! ## Program Construction & Global/Static Initialization -/

def collectFnStatics : CStmt → List VarDecl
  | .decl d => if d.isStatic then [d] else []
  | .decls ds => ds.filter (·.isStatic)
  | .block ss => ss.flatMap collectFnStatics
  | .ifStmt _ t f? => collectFnStatics t ++ match f? with | some f => collectFnStatics f | none => []
  | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b | .switchStmt _ b
  | .caseStmt _ b | .defaultStmt b | .labelStmt _ b => collectFnStatics b
  | _ => []

def stdLibcProtos : List (String × FnSig) :=
  let (vp, cp, sp, csp) := (CTy.ptr .void, CTy.ptr (.const_ .void), CTy.ptr (.int .i8), CTy.ptr (.const_ (.int .i8)))
  [ ("malloc",   (vp, [.int .u64], false)), ("calloc", (vp, [.int .u64, .int .u64], false)),
    ("free",     (.void, [vp], false)), ("memcpy", (vp, [vp, cp, .int .u64], false)),
    ("memmove",  (vp, [vp, cp, .int .u64], false)), ("memset", (vp, [vp, .int .i32, .int .u64], false)),
    ("memcmp",   (.int .i32, [cp, cp, .int .u64], false)), ("strlen", (.int .u64, [csp], false)),
    ("memchr",   (vp, [cp, .int .i32, .int .u64], false)), ("open", (.int .i32, [csp, .int .i32], true)),
    ("close",    (.int .i32, [.int .i32], false)), ("fcntl", (.int .i32, [.int .i32, .int .i32], true)),
    ("lseek",    (.int .i64, [.int .i32, .int .i64, .int .i32], false)),
    ("lseek64",  (.int .i64, [.int .i32, .int .i64, .int .i32], false)),
    ("read",     (.int .i64, [.int .i32, vp, .int .u64], false)),
    ("write",    (.int .i64, [.int .i32, cp, .int .u64], false)),
    ("strerror", (sp, [.int .i32], false)),
    ("snprintf", (.int .i32, [sp, .int .u64, csp], true)),
    ("vsnprintf", (.int .i32, [sp, .int .u64, csp, .vaList], false)) ]

def progOfTUs (tus : List TU) : Prog :=
  let items := tus.flatMap (·.items)
  let tags := collectTagEnv items
  let globals := items.filterMap fun | .globalDecl l d => if l == .extern_ then none else some (l, d) | _ => none
  let fnDefs := items.filterMap fun | .fnDef f => some (f.name, f) | _ => none
  let protos := items.filterMap (fun
    | .fnDef f => some (f.name, (f.retTy, f.params.map (·.ty), f.variadic))
    | .fnProto _ r n ps v => some (n, (r, ps.map (·.ty), v)) | _ => none) ++ stdLibcProtos
  { tags, globals, fns := (List.lookup · fnDefs), fnProtos := (List.lookup · protos), fnStatics := fun _ => [] }

def resolveDeclTy (ty : CTy) (init? : Option InitVal) : CTy :=
  match ty, init? with
  | .array el none, some (.expr (.strLit s)) => .array el (some (s.utf8ByteSize + 1))
  | .array el none, some (.list xs) => .array el (some xs.length)
  | .array el none, some (.intSeq _ vals) => .array el (some (vals.size / max 1 el.flatElemCount))
  | .const_ t, _ => .const_ (resolveDeclTy t init?)
  | _, _ => ty

private def allocChecked (m : Mem) (sz al : Nat) (perm : Perm) (kind : AllocKind) (ba : UInt64)
    (init : Nat → MemByte) : Option (BlockId × Mem) :=
  if hsz : sz < ptrDiffLimit then if hal : 0 < al then if hba : ba.toNat % al = 0 then
    some (m.alloc sz al perm kind ba init hsz hal hba) else none else none else none

def evalConstExpr (prog : Prog) (env : Env) (m : Mem) (strBase : Nat → UInt64) (ns : Nat) :
    CExpr → Option (Val × CTy × Mem × Nat)
  | .paren e => evalConstExpr prog env m strBase ns e
  | .lit v k _ _ _ => some (ofIntCast k v, .int k, m, ns)
  | .strLit s => do
    let (bid, m') ← allocChecked m (s.utf8ByteSize + 1) 1 .ro .global (strBase ns)
      (fun i => .byte ((s.toUTF8[i]?).getD 0))
    return (.ptr bid 0, .ptr (.const_ (.int .i8)), m', ns + 1)
  | .var x => match env.lookup x with
    | some (b, ty) =>
      let resTy := match ty.unqual with | .array _ _ => ty.decay | _ => ty
      some (Val.ptr b 0, resTy, m, ns)
    | none => match enumConst? prog.tags x with
      | some ev => some (ofIntCast .i32 ev, .int .i32, m, ns)
      | none => (prog.fnProtos x).map fun (r, ps, v) => (.fnPtr x, .fnPtr r ps v, m, ns)
  | .addrOf (.var x) => (env.lookup x).map fun (b, ty) => (.ptr b 0, .ptr ty, m, ns)
  | .sizeOfTy ty => some (.int .u64 (BitVec.ofNat 64 (sizeofTy prog.tags ty)), .int .u64, m, ns)
  | .cast ty e => do let (v, _, m', ns') ← evalConstExpr prog env m strBase ns e; return (← castVal m' ty v, ty, m', ns')
  | .unary op e => do let (v, _, m', ns') ← evalConstExpr prog env m strBase ns e; let (rv, rt) ← evalUnary op v; return (rv, rt, m', ns')
  | .binary op l r => do
    let (v1, t1, m1, ns1) ← evalConstExpr prog env m strBase ns l
    let (v2, t2, m2, ns2) ← evalConstExpr prog env m1 strBase ns1 r
    let (rv, rt) ← applyBinary {} prog.tags m2 op v1 t1 v2 t2
    return (rv, rt, m2, ns2)
  | _ => none

mutual
def writeInitList (prog : Prog) (env : Env) (m : Mem) (strBase : Nat → UInt64)
    (b : BlockId) (off : Int64) (elem : CTy) (idx : Nat) : List InitVal → Nat → Option (Mem × Nat)
  | [], ns => some (m, ns)
  | iv :: rest, ns => do
    let esz := sizeofTy prog.tags elem
    let (m1, ns1) ← writeInitVal prog env m strBase b (Int64.ofInt (off.toInt + idx * esz)) elem iv ns
    writeInitList prog env m1 strBase b off elem (idx + 1) rest ns1

def writeInitFields (prog : Prog) (env : Env) (m : Mem) (strBase : Nat → UInt64)
    (b : BlockId) (baseOff offAcc : Nat) : List (String × CTy) → List InitVal → Nat → Option (Mem × Nat)
  | [], _, ns => some (m, ns) | _, [], ns => some (m, ns)
  | (_, fty) :: frest, iv :: irest, ns => do
    let foff := alignUp offAcc (max 1 (alignofTy prog.tags fty))
    let (m1, ns1) ← writeInitVal prog env m strBase b (Int64.ofNat (baseOff + foff)) fty iv ns
    writeInitFields prog env m1 strBase b baseOff (foff + sizeofTy prog.tags fty) frest irest ns1

def writeInitVal (prog : Prog) (env : Env) (m : Mem) (strBase : Nat → UInt64)
    (b : BlockId) (off : Int64) (ty : CTy) (iv : InitVal) (ns : Nat) : Option (Mem × Nat) :=
  match iv, ty.unqual with
  | .expr (.strLit s), .array _ _ =>
    let bs := (List.range s.utf8ByteSize).map (fun i => MemByte.byte ((s.toUTF8[i]?).getD 0)) ++ [.byte 0]
    (m.writeBytes b off bs).map (·, ns)
  | .expr e, _ => do
    let (v, _, m1, ns1) ← evalConstExpr prog env m strBase ns e
    (writeVal m1 b off ty.stripConst v).map (·, ns1)
  | .list xs, .array el _ => writeInitList prog env m strBase b off el 0 xs ns
  | .list xs, .anonStruct flds => writeInitFields prog env m strBase b off.toInt.toNat 0 flds xs ns
  | .list xs, .structTy tag => match prog.tags.lookup tag with
    | some (.structDef flds) => writeInitFields prog env m strBase b off.toInt.toNat 0 flds xs ns | _ => none
  | .list (x :: _), .anonUnion ((_, fty) :: _) => writeInitVal prog env m strBase b off fty x ns
  | .list [], .anonUnion _ => some (m, ns)
  | .list (x :: _), .unionTy tag => match prog.tags.lookup tag with
    | some (.unionDef ((_, fty) :: _)) => writeInitVal prog env m strBase b off fty x ns | _ => none
  | .list [], .unionTy _ => some (m, ns)
  | .intSeq _ vals, .array _ _ =>
    match ty.arrayLeafIntKind? with
    | some k =>
      let bs := vals.toList.flatMap fun v => Mem.encodeInt k (BitVec.ofInt k.bits v)
      (m.writeBytes b off bs).map (·, ns)
    | none => none
  | _, _ => none
end

def allocVarInit (prog : Prog) (env : Env) (m : Mem) (base strBase : Nat → UInt64)
    (idx ns : Nat) (d : VarDecl) : Option (BlockId × CTy × Mem × Nat) := do
  let ty := resolveDeclTy d.ty d.init?
  let sz := max 1 (sizeofTy prog.tags ty); let al := max 1 (alignofTy prog.tags ty)
  let (bid, m1) ← allocChecked m sz al .rw .global (base idx) (fun _ => .byte 0)
  let (m2, ns') ← match d.init? with
    | none => some (m1, ns) | some iv => writeInitVal prog env m1 strBase bid 0 ty iv ns
  let isRo := ty.isReadOnly
  let m3 : Mem := if isRo then
    { m2 with
      blocks := fun x => if x == bid then (m2.blocks bid).map ({ · with perm := .ro }) else m2.blocks x
      fresh := fun x hx => by
        by_cases hxb : x == bid
        · have heq : x = bid := beq_iff_eq.mp hxb
          subst heq
          simp [m2.fresh x hx]
        · simp [hxb, m2.fresh x hx] }
    else m2
  return (bid, ty, m3, ns')

def initProg (tus : List TU) (globBase staticBase strBase : Nat → UInt64) (errnoBase : UInt64) :
    Option (Prog × Env × Mem × OSState) := do
  let prog0 := progOfTUs tus
  let (eBid, m0) ← allocChecked Mem.empty 4 4 .rw .global errnoBase (fun _ => .byte 0)
  let rec initGlobs (idx ns : Nat) (env : Env) (m : Mem) : List (Linkage × VarDecl) → Option (Env × Mem × Nat)
    | [] => some (env, m, ns)
    | (_, d) :: rest =>
      if (env.lookup d.name).isSome then initGlobs idx ns env m rest
      else do
        let (bid, ty, m', ns') ← allocVarInit prog0 env m globBase strBase idx ns d
        initGlobs (idx + 1) ns' ((d.name, bid, ty) :: env) m' rest
  let (gEnv, m1, ns1) ← initGlobs 0 0 [("errno", eBid, .int .i32)] m0 prog0.globals
  let fnDefs := (tus.flatMap (·.items)).filterMap fun | .fnDef f => some f | _ => none
  let rec initStatics (idx ns : Nat) (m : Mem) (fnAcc : List (String × Env)) :
      List FnDef → Option (List (String × Env) × Mem)
    | [] => some (fnAcc, m)
    | f :: frest => do
      let ds := collectFnStatics f.body
      let (sEnv, m', idx', ns') ← ds.foldlM (fun (sE, mA, iA, nA) d => do
        let (bid, ty, mB, nB) ← allocVarInit prog0 gEnv mA staticBase strBase iA nA d
        return ((d.name, bid, ty) :: sE, mB, iA + 1, nB)) ([], m, idx, ns)
      initStatics idx' ns' m' ((f.name, sEnv) :: fnAcc) frest
  let (fnStaticList, m2) ← initStatics 0 ns1 m1 [] fnDefs
  let prog := { prog0 with globalEnv := gEnv, fnStatics := fun s => (fnStaticList.lookup s).getD [] }
  return (prog, gEnv, m2, { errnoBlk := eBid })

end Sem
end C99
