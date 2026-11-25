/-!
# C99 Core AST and LP64 Layout

Zlib-agnostic C99 abstract syntax tree targeting x86-64 LP64 (`char` = 1, `short` = 2,
`int` = 4, `long` = 8, pointers = 8). Both the operational semantics (`C99.Semantics`)
and the 1-to-1 C printer (`C99.EmitC`) operate directly on this single representation.
-/

namespace C99

/-- Fixed-width integer kinds on LP64. -/
inductive IntKind where
  | i8 | u8 | i16 | u16 | i32 | u32 | i64 | u64
  deriving DecidableEq, Repr, Inhabited

namespace IntKind

def bits : IntKind → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 => 32
  | .i64 | .u64 => 64

def bytes (k : IntKind) : Nat := k.bits / 8

def signed : IntKind → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | .u8 | .u16 | .u32 | .u64 => false

def align (k : IntKind) : Nat := k.bytes

def minVal (k : IntKind) : Int :=
  if k.signed then -(2 ^ (k.bits - 1) : Int) else 0

def maxVal (k : IntKind) : Int :=
  if k.signed then (2 ^ (k.bits - 1) : Int) - 1 else (2 ^ k.bits : Int) - 1

def inRange (k : IntKind) (v : Int) : Bool :=
  k.minVal ≤ v && v ≤ k.maxVal

def rank : IntKind → Nat
  | .i8 | .u8 => 1
  | .i16 | .u16 => 2
  | .i32 | .u32 => 3
  | .i64 | .u64 => 4

/-- C99 §6.3.1.1 integer promotions (on LP64 all sub-int types fit in `int`). -/
def promote (k : IntKind) : IntKind :=
  if k.rank < 3 then .i32 else k

/-- C99 §6.3.1.8 usual arithmetic conversions after integer promotions. -/
def usualArith (a b : IntKind) : IntKind :=
  let a := a.promote
  let b := b.promote
  if a == b then a
  else if a.signed == b.signed then
    if a.rank ≥ b.rank then a else b
  else
    let (u, s) := if !a.signed then (a, b) else (b, a)
    if u.rank ≥ s.rank then u
    else if s.bits > u.bits then s
    else match s with
      | .i32 => .u32
      | .i64 => .u64
      | _ => u

def render : IntKind → String
  | .i8 => "char"
  | .u8 => "unsigned char"
  | .i16 => "short"
  | .u16 => "unsigned short"
  | .i32 => "int"
  | .u32 => "unsigned"
  | .i64 => "long"
  | .u64 => "unsigned long"

end IntKind

/-- C99 types, preserving typedef and qualifier spelling for 1-to-1 emission. -/
inductive CTy where
  | void
  | int (k : IntKind)
  | const_ (to : CTy)
  | ptr (to : CTy)
  | array (elem : CTy) (len : Option Nat)
  | structTy (tag : String)
  | unionTy (tag : String)
  | anonStruct (fields : List (String × CTy))
  | anonUnion (fields : List (String × CTy))
  | enumTy (tag : String) (isUnsigned : Bool := true)
  | fnPtr (ret : CTy) (params : List CTy) (variadic : Bool := false)
  | vaList
  | typedef (name : String) (underlying : CTy)
  deriving BEq, Inhabited

/-- Definition of a named struct, union, or enum tag in `TypeEnv`. -/
inductive TagDef where
  | structDef (fields : List (String × CTy))
  | unionDef (fields : List (String × CTy))
  | enumDef (items : List (String × Option Int)) (isUnsigned : Bool := true)
  deriving BEq, Inhabited

abbrev TypeEnv := List (String × TagDef)

namespace CTy

/-- Strip top-level `const` qualifiers and `typedef` aliases. -/
def unqual : CTy → CTy
  | .const_ t => t.unqual
  | .typedef _ t => t.unqual
  | t => t

def isConst : CTy → Bool
  | .const_ _ => true
  | .typedef _ t => t.isConst
  | _ => false

def stripConst : CTy → CTy
  | .const_ t => t.stripConst
  | .typedef n t => .typedef n t.stripConst
  | t => t

def isVoid (t : CTy) : Bool :=
  match t.unqual with | .void => true | _ => false

def isVaList (t : CTy) : Bool :=
  match t.unqual with | .vaList => true | _ => false

def isPtr (t : CTy) : Bool :=
  match t.unqual with
  | .ptr _ => true
  | _ => false

def isArray (t : CTy) : Bool :=
  match t.unqual with
  | .array _ _ => true
  | _ => false

def isIntLike (t : CTy) : Bool :=
  match t.unqual with
  | .int _ | .enumTy _ _ => true
  | _ => false

def intKind? (t : CTy) : Option IntKind :=
  match t.unqual with
  | .int k => some k
  | .enumTy _ isU => some (if isU then .u32 else .i32)
  | _ => none

/-- Array-to-pointer decay for expression typing. -/
def decay : CTy → CTy
  | .const_ t => t.decay
  | .typedef _ t => t.decay
  | .array elem _ => .ptr elem
  | t => t

end CTy

/-! ## LP64 Type Layout (`sizeof`, `alignof`, `offsetof`) -/

def alignUp (off align : Nat) : Nat :=
  if align ≤ 1 then off else ((off + align - 1) / align) * align

mutual
def alignofAux (env : TypeEnv) : Nat → CTy → Nat
  | _, .void => 1
  | _, .int k => k.align
  | fuel, .const_ t => alignofAux env fuel t
  | _, .ptr _ => 8
  | fuel, .array elem _ => alignofAux env fuel elem
  | fuel, .anonStruct flds => alignofFields env fuel flds 1
  | fuel, .anonUnion flds => alignofFields env fuel flds 1
  | 0, .structTy _ => 1
  | n + 1, .structTy tag =>
    match env.lookup tag with
    | some (.structDef flds) => alignofFields env n flds 1
    | _ => 1
  | 0, .unionTy _ => 1
  | n + 1, .unionTy tag =>
    match env.lookup tag with
    | some (.unionDef flds) => alignofFields env n flds 1
    | _ => 1
  | _, .enumTy _ _ => 4
  | _, .fnPtr _ _ _ => 8
  | _, .vaList => 8
  | fuel, .typedef _ t => alignofAux env fuel t

def alignofFields (env : TypeEnv) (fuel : Nat) : List (String × CTy) → Nat → Nat
  | [], acc => acc
  | (_, fty) :: rest, acc => alignofFields env fuel rest (max acc (alignofAux env fuel fty))

def sizeofAux (env : TypeEnv) : Nat → CTy → Nat
  | _, .void => 0
  | _, .int k => k.bytes
  | fuel, .const_ t => sizeofAux env fuel t
  | _, .ptr _ => 8
  | fuel, .array elem (some n) => n * sizeofAux env fuel elem
  | _, .array _ none => 0
  | fuel, .anonStruct flds => sizeofStructFields env fuel 0 1 flds
  | fuel, .anonUnion flds => sizeofUnionFields env fuel 0 1 flds
  | 0, .structTy _ => 0
  | n + 1, .structTy tag =>
    match env.lookup tag with
    | some (.structDef flds) => sizeofStructFields env n 0 1 flds
    | _ => 0
  | 0, .unionTy _ => 0
  | n + 1, .unionTy tag =>
    match env.lookup tag with
    | some (.unionDef flds) => sizeofUnionFields env n 0 1 flds
    | _ => 0
  | _, .enumTy _ _ => 4
  | _, .fnPtr _ _ _ => 8
  | _, .vaList => 24
  | fuel, .typedef _ t => sizeofAux env fuel t

def sizeofStructFields (env : TypeEnv) (fuel sz align : Nat) : List (String × CTy) → Nat
  | [] => alignUp sz align
  | (_, fty) :: rest =>
    let fa := max 1 (alignofAux env fuel fty)
    let off := alignUp sz fa
    sizeofStructFields env fuel (off + sizeofAux env fuel fty) (max align fa) rest

def sizeofUnionFields (env : TypeEnv) (fuel sz align : Nat) : List (String × CTy) → Nat
  | [] => alignUp sz align
  | (_, fty) :: rest =>
    sizeofUnionFields env fuel (max sz (sizeofAux env fuel fty)) (max align (alignofAux env fuel fty)) rest
end

def alignofTy (env : TypeEnv) (ty : CTy) : Nat :=
  alignofAux env (env.length + 1) ty

def sizeofTy (env : TypeEnv) (ty : CTy) : Nat :=
  sizeofAux env (env.length + 1) ty

private def findStructField (env : TypeEnv) (off : Nat) (target : String) :
    List (String × CTy) → Option (Nat × CTy)
  | [] => none
  | (fname, fty) :: rest =>
    let fa := max 1 (alignofTy env fty)
    let foff := alignUp off fa
    if fname == target then some (foff, fty)
    else findStructField env (foff + sizeofTy env fty) target rest

private def findUnionField (target : String) : List (String × CTy) → Option (Nat × CTy)
  | [] => none
  | (fname, fty) :: rest =>
    if fname == target then some (0, fty) else findUnionField target rest

/-- Offset and field type for a member access on `ty`. -/
def fieldLayout? (env : TypeEnv) (ty : CTy) (field : String) : Option (Nat × CTy) :=
  match ty.unqual with
  | .anonStruct flds => findStructField env 0 field flds
  | .anonUnion flds => findUnionField field flds
  | .structTy tag =>
    match env.lookup tag with
    | some (.structDef flds) => findStructField env 0 field flds
    | _ => none
  | .unionTy tag =>
    match env.lookup tag with
    | some (.unionDef flds) => findUnionField field flds
    | _ => none
  | _ => none

/-! ## Expressions, Initializers, Statements, and Translation Units -/

inductive LitRadix where | dec | hex | oct | char
  deriving DecidableEq, Repr, Inhabited

inductive LitSuffix where | none | U | L | UL | LL | ULL
  deriving DecidableEq, Repr, Inhabited

inductive UnOp where | neg | bitNot | logNot | plus
  deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | mod
  | bitAnd | bitOr | bitXor | shl | shr
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

inductive AssignOp where
  | eq | addEq | subEq | mulEq | divEq | modEq | andEq | orEq | xorEq | shlEq | shrEq
  deriving DecidableEq, Repr, Inhabited

inductive IncDecOp where
  | preInc | preDec | postInc | postDec
  deriving DecidableEq, Repr, Inhabited

/-- C99 expressions. -/
inductive CExpr where
  | lit (val : Int) (ty : IntKind := .i32) (suffix : LitSuffix := .none) (radix : LitRadix := .dec)
      (sym? : Option String := none)
  | strLit (s : String)
  | var (name : String)
  | sizeOfTy (ty : CTy)
  | sizeOfExpr (e : CExpr)
  | unary (op : UnOp) (e : CExpr)
  | binary (op : BinOp) (l r : CExpr)
  | logAnd (l r : CExpr)
  | logOr (l r : CExpr)
  | cond (c t f : CExpr)
  | comma (l r : CExpr)
  | cast (ty : CTy) (e : CExpr)
  | deref (e : CExpr)
  | addrOf (e : CExpr)
  | index (base idx : CExpr)
  | member (base : CExpr) (field : String)
  | arrow (base : CExpr) (field : String)
  | assign (op : AssignOp) (lhs rhs : CExpr)
  | incDec (op : IncDecOp) (lhs : CExpr)
  | call (fn : CExpr) (args : List CExpr)
  | vaStart (ap lastParam : String)
  | vaEnd (ap : String)
  | paren (e : CExpr)
  deriving BEq, Inhabited

/-- Declaration initializers, including bulk numeric/table arrays for fast elaboration. -/
inductive InitVal where
  | expr (e : CExpr)
  | list (xs : List InitVal)
  | intArray (k : IntKind) (radix : LitRadix) (vals : Array Int)
  | intArray2D (k : IntKind) (radix : LitRadix) (rows : Array (Array Int))
  | tupleArray (nestedBraces : Bool) (rows : Array (Array Int))
  deriving BEq, Inhabited

structure VarDecl where
  name : String
  ty : CTy
  isStatic : Bool := false
  isConst : Bool := false
  init? : Option InitVal := none
  deriving BEq, Inhabited

/-- C99 statements (including `switch` fallthrough, `goto`, and block-scoped `decl`). -/
inductive CStmt where
  | nop
  | expr (e : CExpr)
  | decl (d : VarDecl)
  | decls (ds : List VarDecl)
  | block (ss : List CStmt)
  | ifStmt (c : CExpr) (t : CStmt) (f? : Option CStmt)
  | whileStmt (c : CExpr) (body : CStmt)
  | doWhileStmt (body : CStmt) (c : CExpr)
  | forStmt (init? : Option CExpr) (cond? : Option CExpr) (step? : Option CExpr) (body : CStmt)
  | switchStmt (scrut : CExpr) (body : CStmt)
  | caseStmt (val : Int) (body : CStmt)
  | defaultStmt (body : CStmt)
  | breakStmt
  | continueStmt
  | returnStmt (val? : Option CExpr)
  | labelStmt (lbl : String) (body : CStmt)
  | gotoStmt (lbl : String)
  deriving BEq, Inhabited

inductive Linkage where
  | export_
  | hidden
  | static_
  | staticInline
  | extern_
  deriving DecidableEq, Repr, Inhabited

structure Param where
  name : String
  ty : CTy
  deriving BEq, Inhabited

structure FnDef where
  linkage : Linkage := .export_
  retTy : CTy
  name : String
  params : List Param
  variadic : Bool := false
  body : CStmt
  deriving BEq, Inhabited

/-- Top-level items inside a C translation unit or header. -/
inductive TopItem where
  | includeSys (path : String)
  | includeLocal (path : String)
  | ppRaw (text : String)
  | typedefDecl (name : String) (ty : CTy)
  | fwdTag (isUnion : Bool := false) (tag : String)
  | tagDecl (isUnion : Bool := false) (tag? : Option String) (typedefName? : Option String)
      (fields : List (String × CTy))
  | enumDecl (tag? : Option String) (typedefName? : Option String)
      (items : List (String × Option Int))
  | globalDecl (linkage : Linkage) (decl : VarDecl)
  | fnProto (linkage : Linkage) (retTy : CTy) (name : String)
      (params : List Param) (variadic : Bool := false)
  | fnDef (fn : FnDef)
  deriving BEq, Inhabited

structure TU where
  fileName : String
  items : List TopItem
  deriving BEq, Inhabited

/-- Extract tag definitions in declaration order. -/
def collectTagEnv (items : List TopItem) : TypeEnv :=
  items.filterMap fun
    | .tagDecl isUnion tag? td? flds =>
      let defn := if isUnion then TagDef.unionDef flds else TagDef.structDef flds
      (tag?.orElse (fun _ => td?)).map (·, defn)
    | .enumDecl tag? td? items =>
      let isU := items.all fun (_, v?) => match v? with | some v => v ≥ 0 | none => true
      (tag?.orElse (fun _ => td?)).map (·, TagDef.enumDef items isU)
    | _ => none

end C99
