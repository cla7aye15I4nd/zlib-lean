import Lean
import ZlibF.Runtime.Schema
import ZlibF.Runtime.CAbi
import ZlibF.Runtime.Address
import ZlibF.Runtime.Alloc
import ZlibF.Zlib.gzfs

/-! Shared C ABI struct layouts, type/operator tables, and table formatters.
Covers all 10 C structs across zlib (`z_stream`, `gz_header`, `ct_data`, `static_tree_desc`,
`tree_desc`, `deflate_state`, `code`, `inflate_state`, `gzFile_s`, `gz_state`). -/
namespace Lean2C.ABI
open Lean Elab Term

def cString (s : String) : String := Id.run do
  let mut out := "\""
  for b in s.toUTF8 do
    let c := Char.ofNat b.toNat
    out := if b >= 32 && b < 127 && c != '\\' && c != '"' then out.push c
      else out ++ "\\" ++ toString (b.toNat / 64) ++ toString (b.toNat / 8 % 8) ++ toString (b.toNat % 8)
  return out ++ "\""

private def basicFieldCTys : List (Name × String) :=
  [(``UInt8, "unsigned char"), (``UInt16, "unsigned short"), (``UInt64, "unsigned long"), (``Int32, "int"), (``Int64, "long"),
   (``C.GzFile, "struct gzFile_s"), (``C.ZStream, "struct z_stream_s"), (``C.TreeDesc, "struct tree_desc_s"),
   (``C.WPtr, "unsigned short *"), (``C.IPtr, "const int *")]

private def optFieldCTys : List (Name × String) :=
  [(``C.StateRef, "struct internal_state *"), (``C.ZStreamRef, "z_streamp"), (``C.GzHeaderRef, "gz_headerp"), (``C.StaticTreeDescRef, "const static_tree_desc *")]

private def fieldDecl? (record field : Name) (type : Expr) : TermElabM (String × String) := do
  let body := type.getForallBody; let n? := body.getAppFn.constName?
  if let some ct := n?.bind (fun n => basicFieldCTys.lookup n) then return (ct, "")
  if n? == some ``UInt32 then return (if record == ``C.InflateState && field == `mode then "inflate_mode" else "unsigned", "")
  if n? == some ``C.BPtr then return (if field == `opaque then "void *" else if field == `msg || field == `path then "char *" else "unsigned char *", "")
  if n? == some ``C.CtDataPtr then return (if field == `static_tree then "const struct ct_data_s *" else "struct ct_data_s *", "")
  if n? == some ``C.CodePtr then return (if field == `lencode || field == `distcode then "const code *" else "code *", "")
  if body.isAppOfArity ``Option 1 then
    if let some ct := (body.getAppArgs.back!.getAppFn.constName?).bind (fun n => optFieldCTys.lookup n) then return (ct, "")
  if n? == some ``C.FnPtr then if field == `zalloc then return ("alloc_func", "") else if field == `zfree then return ("free_func", "")
  if n? == some ``Array then
    let arrDecls : List (Name × Name × String × Nat) :=
      [(``C.InflateState, `lens, "unsigned short", C.InflateState.zeroed.lens.size), (``C.InflateState, `work, "unsigned short", C.InflateState.zeroed.work.size),
       (``C.InflateState, `codes, "code", C.InflateState.zeroed.codes.size), (``C.DeflateState, `dyn_ltree, "struct ct_data_s", C.DeflateState.zeroed.dyn_ltree.size),
       (``C.DeflateState, `dyn_dtree, "struct ct_data_s", C.DeflateState.zeroed.dyn_dtree.size), (``C.DeflateState, `bl_tree, "struct ct_data_s", C.DeflateState.zeroed.bl_tree.size),
       (``C.DeflateState, `bl_count, "unsigned short", C.DeflateState.zeroed.bl_count.size), (``C.DeflateState, `heap, "int", C.DeflateState.zeroed.heap.size),
       (``C.DeflateState, `depth, "unsigned char", C.DeflateState.zeroed.depth.size)]
    if let some (_, _, et, sz) := arrDecls.find? (fun e => e.1 == record && e.2.1 == field) then return (et, s!"[{sz}]")
  throwError m!"unsupported ABI field {record}.{field} of type {type}"

private def structDecl (env : Environment) (record : Name) (header : String) : TermElabM String := do
  let mut fields := ""
  for field in getStructureFields env record do
    let some info := env.find? (record ++ field) | throwError m!"missing {record}.{field}"
    if record == ``C.CtData then
      fields := fields ++ s!"    union \{ {if field == `fc then "unsigned short freq, code;" else "unsigned short dad, len;"} } {field.toString};\n"
    else
      let (ty, suffix) ← fieldDecl? record field info.type
      fields := fields ++ "    " ++ ty ++ (if ty.endsWith "*" then "" else " ") ++ field.toString ++ suffix ++ ";\n"
  return header ++ " {\n" ++ fields ++ "}"

private def inflateModeDecl : String :=
  let modes : List (String × UInt32) :=
    [("HEAD", C.HEAD), ("FLAGS", C.FLAGS), ("TIME", C.TIME), ("OS", C.OS), ("EXLEN", C.EXLEN), ("EXTRA", C.EXTRA), ("NAME", C.NAME),
     ("COMMENT", C.COMMENT), ("HCRC", C.HCRC), ("DICTID", C.DICTID), ("DICT", C.DICT), ("TYPE", C.TYPE), ("TYPEDO", C.TYPEDO),
     ("STORED", C.STORED), ("COPY_", C.COPY_), ("COPY", C.COPY), ("TABLE", C.TABLE), ("LENLENS", C.LENLENS), ("CODELENS", C.CODELENS),
     ("LEN_", C.LEN_), ("LEN", C.LEN), ("LENEXT", C.LENEXT), ("DIST", C.DIST), ("DISTEXT", C.DISTEXT), ("MATCH", C.MATCH),
     ("LIT", C.LIT), ("CHECK", C.CHECK), ("LENGTH", C.LENGTH), ("DONE", C.DONE), ("BAD", C.BAD), ("MEM", C.MEM), ("SYNC", C.SYNC)]
  "typedef enum { " ++ String.intercalate ", " (modes.map fun (n, v) => s!"{n} = {v}") ++ " } inflate_mode;\n"

private def commonPrelude (env : Environment) : TermElabM String := do
  let stream ← structDecl env ``C.ZStream "struct z_stream_s"; let hdr ← structDecl env ``C.GzHeader "struct gz_header_s"
  return "typedef void *(*alloc_func)(void *, unsigned, unsigned);\ntypedef void (*free_func)(void *, void *);\nstruct internal_state;\n" ++
    stream ++ ";\ntypedef struct z_stream_s z_stream;\ntypedef z_stream *z_streamp;\n" ++
    hdr ++ ";\ntypedef struct gz_header_s gz_header;\ntypedef gz_header *gz_headerp;\n"

private def inflatePart (env : Environment) : TermElabM String := do
  return (← structDecl env ``C.Code "typedef struct") ++ " code;\n" ++ inflateModeDecl ++ (← structDecl env ``C.InflateState "struct inflate_state") ++ ";\n"

private def deflatePart (env : Environment) : TermElabM String := do
  let ct ← structDecl env ``C.CtData "typedef struct ct_data_s"; let std ← structDecl env ``C.StaticTreeDesc "struct static_tree_desc_s"
  let td ← structDecl env ``C.TreeDesc "typedef struct tree_desc_s"; let dstate ← structDecl env ``C.DeflateState "struct internal_state"
  return ct ++ " ct_data;\ntypedef struct static_tree_desc_s static_tree_desc;\n" ++ std ++ ";\n" ++ td ++ " tree_desc;\n" ++ dstate ++ ";\ntypedef struct internal_state deflate_state;\n"

private def gzPart (env : Environment) : TermElabM String := do
  return (← structDecl env ``C.GzFile "struct gzFile_s") ++ ";\ntypedef struct gzFile_s *gzFile;\n" ++ (← structDecl env ``C.GzState "typedef struct") ++ " gz_state;\ntypedef gz_state *gz_statep;\n"

elab "abiZStream%" : term => do return toExpr (← commonPrelude (← getEnv))
elab "abiInflateLayouts%" : term => do let env ← getEnv; return toExpr ((← commonPrelude env) ++ (← inflatePart env))
elab "abiDeflateLayouts%" : term => do let env ← getEnv; return toExpr ((← commonPrelude env) ++ (← deflatePart env))
elab "abiGzLayouts%" : term => do let env ← getEnv; return toExpr ((← commonPrelude env) ++ (← gzPart env))
elab "abiAllLayouts%" : term => do let env ← getEnv; return toExpr ((← commonPrelude env) ++ (← inflatePart env) ++ (← deflatePart env) ++ (← gzPart env))

def arrayDecl (ty name : String) (vals : List String) : String :=
  s!"static const {ty} {name}[{vals.length}] = \{\n    " ++ String.intercalate ", " vals ++ "\n};\n"

inductive Linkage where | «export» | exportAs (cname : String) | hidden | «static» | staticInline deriving Inhabited, BEq
inductive OutKind where | codePtr | uint32 deriving Inhabited, BEq
structure FnMeta where
  leanName : Name
  cName : String
  link : Linkage
  params : List (String × String × Option OutKind)
  retCTy : String
  outCount : Nat
  order? : Option Nat := none
  line : Nat := 0
  deriving Inhabited

def cIdent : Name → String | .str _ s => s.map fun c => if c.isAlphanum || c == '_' then c else '_' | _ => "v"
def cStructName (n : Name) : String := String.intercalate "_" (n.components.map cIdent)
def isABIStruct (n : Name) : Bool := n ∈ [``C.ZStream, ``C.GzHeader, ``C.CtData, ``C.TreeDesc, ``C.StaticTreeDesc, ``C.DeflateState, ``C.Code, ``C.InflateState, ``C.GzFile, ``C.GzState]
def isBytePtrCType (ct : String) : Bool := ct ∈ ["unsigned char *", "const unsigned char *", "char *", "const char *"]
def stripOutType (ct : String) : Option OutKind → String | some .codePtr => "code *" | some .uint32 => "unsigned" | none => ct

private def cTypeHeadTable : List (Name × String × Option OutKind) :=
  [(``C.ConstBPtr, "const unsigned char *", none), (``C.CStr, "char *", none), (``C.ConstCStr, "const char *", none),
   (``C.VoidPtr, "void *", none), (``C.ConstVoidPtr, "const void *", none), (``C.ConstWPtr, "const unsigned short *", none),
   (``C.ConstCodePtr, "const code *", none), (``C.ConstUPtr, "const unsigned *", none), (``C.PtrU64, "unsigned long *", none),
   (``C.OutCodePtr, "code **", some .codePtr), (``C.OutUInt32, "unsigned *", some .uint32), (``C.OutInt32, "int *", none),
   (``C.ZOffT, "z_off_t", none), (``C.ZOff64T, "z_off64_t", none), (``C.CodeType, "codetype", none), (``C.ZCrcT, "z_crc_t", none),
   (``C.ZWordT, "z_word_t", none), (``C.StackStream, "z_streamp", none), (``C.StackScalar64, "unsigned long *", none),
   (``UInt8, "unsigned char", none), (``UInt16, "unsigned short", none), (``UInt32, "unsigned", none), (``UInt64, "unsigned long", none),
   (``Int32, "int", none), (``Int64, "long", none), (``Bool, "int", none), (``Unit, "void", none), (``PUnit, "void", none),
   (``C.BPtr, "unsigned char *", none), (``C.WPtr, "unsigned short *", none), (``C.IPtr, "const int *", none), (``C.UPtr, "const unsigned *", none),
   (``C.CodePtr, "code *", none), (``C.GzFilePtr, "gzFile", none), (``C.GzStatePtr, "gz_statep", none), (``C.ZStreamPtr, "z_streamp", none),
   (``C.InflateStatePtr, "struct inflate_state *", none), (``C.DeflateStatePtr, "deflate_state *", none),
   (``C.Code, "code", none), (``C.CtData, "ct_data", none), (``C.ZStream, "z_stream", none)]
def cTypeHead? (t : Expr) : Option (String × Option OutKind) := t.getAppFn.constName?.bind fun n => cTypeHeadTable.lookup n
def optPtrRefName? (t : Expr) : Option Name :=
  if t.isAppOfArity ``Option 1 then let i := t.getAppArgs[0]!; (if i.isAppOfArity ``C.Ptr 1 then i.getAppArgs[0]! else i).getAppFn.constName? else none
private def optPtrTable : List (Name × String) :=
  [(``C.BRef, "unsigned char *"), (``C.WRef, "unsigned short *"), (``C.IRef, "const int *"), (``C.URef, "const unsigned *"), (``C.CodeRef, "code *"),
   (``C.GzFileRef, "gzFile"), (``C.GzStateRef, "gz_statep"), (``C.ZStreamRef, "z_streamp"), (``C.InflateStateRef, "struct inflate_state *"), (``C.DeflateStateRef, "deflate_state *")]
def optPtrCType? (n : Name) : Option String := optPtrTable.lookup n

private def posixNames : List String :=
  ["SEEK_SET", "SEEK_CUR", "SEEK_END", "O_WRONLY", "O_CREAT", "O_EXCL", "O_TRUNC", "O_APPEND", "O_NONBLOCK", "O_CLOEXEC",
   "ENOENT", "EBADF", "EEXIST", "EISDIR", "EINVAL", "EFBIG", "ENOSPC", "EOVERFLOW", "EAGAIN", "EINTR", "EIO", "EACCES", "ESPIPE", "EMFILE"]
def posixConst? : Name → Option String
  | .str (.str (.str .anonymous "Zlib") "GzFs") s => if s == "O_LARGEFILE" then some "0" else if posixNames.contains s then some s else none | _ => none

def linkageTable : List (Name × Linkage × Bool × Bool × Bool) :=
  [(``C.CExport, .«export», false, false, false), (``C.CHidden, .hidden, false, false, false), (``C.CStatic, .«static», false, false, false),
   (``C.CStaticInline, .staticInline, false, false, false), (``C.CGlobalConstStr, .«export», true, false, false),
   (``C.CGlobalConstStrArray, .«export», false, true, false), (``C.CLocalConst, .«static», false, false, true)]
def natIntCasts : List Name := [``UInt8.toNat, ``UInt16.toNat, ``UInt32.toNat, ``UInt64.toNat, ``Int.toNat, ``Int32.toInt, ``Int64.toInt, ``Int32.ofInt, ``Int64.ofInt, ``Int64.ofNat]
def pureIntCasts : List Name := natIntCasts ++ [``UInt8.toUInt32, ``UInt16.toUInt32, ``UInt32.toUInt64, ``UInt8.toUInt64, ``UInt16.toUInt64, ``Int64.toUInt64]
def pureIntOps : List (Name × (Int → Int → Int)) := [(``HAdd.hAdd, (· + ·)), (``HSub.hSub, (· - ·)), (``HMul.hMul, (· * ·)), (``HShiftLeft.hShiftLeft, fun l r => l.toNat <<< r.toNat)]
def castMap : List (Name × String) :=
  [(``UInt16.toUInt8, "unsigned char"), (``UInt32.toUInt8, "unsigned char"), (``UInt64.toUInt8, "unsigned char"), (``UInt8.toUInt16, "unsigned short"),
   (``UInt32.toUInt16, "unsigned short"), (``UInt64.toUInt16, "unsigned short"), (``Int32.toUInt32, "unsigned"), (``UInt64.toUInt32, "unsigned"),
   (``UInt8.toUInt32, "unsigned"), (``UInt16.toUInt32, "unsigned"), (``UInt8.toInt8, "signed char"), (``Int8.toInt32, "int"), (``Int64.toInt32, "int"),
   (``UInt32.toInt32, "int"), (``Int32.toInt64, "z_off64_t"), (``UInt32.toUInt64, "unsigned long"), (``UInt8.toUInt64, "unsigned long"),
   (``Int64.toUInt64, "unsigned long"), (``UInt16.toUInt64, "unsigned long"), (``Nat.toUInt8, "unsigned char"), (``Nat.toUInt16, "unsigned short"),
   (``Nat.toUInt32, "unsigned"), (``Nat.toUInt64, "unsigned long"), (``Nat.toInt32, "int"), (``Nat.toInt64, "z_off64_t"), (``C.ByteAddress.address, "unsigned long")]
def passThroughFns : List Name := natIntCasts ++ [``Nat.cast, ``Zlib.GzFs.strLit, ``Zlib.GzFs.cstring, ``C.strLitRef, ``ForInStep.yield, ``ForInStep.done]
def binOps : List (Name × String) :=
  [(``HAdd.hAdd, "+"), (``HSub.hSub, "-"), (``HMul.hMul, "*"), (``HDiv.hDiv, "/"), (``HMod.hMod, "%"), (``HAnd.hAnd, "&"), (``HOr.hOr, "|"),
   (``HXor.hXor, "^"), (``HShiftLeft.hShiftLeft, "<<"), (``HShiftRight.hShiftRight, ">>"), (``LT.lt, "<"), (``LE.le, "<="), (``GT.gt, ">"),
   (``GE.ge, ">="), (``BEq.beq, "=="), (``Eq, "=="), (``bne, "!="), (``Bool.and, "&&"), (``Bool.or, "||")]
def zeroOps : List (Name × String) :=
  [(``Inhabited.default, "{0}"), (``Array.empty, "0"), (``Array.emptyWithCapacity, "0"), (``Array.mkEmpty, "0"), (``C.Ptr.null, "0"),
   (``C.FnPtr.null, "0"), (``Option.none, "0"), (``Unit.unit, "0"), (``PUnit.unit, "0"), (``Zlib.GzFs.zstrerror, "strerror(errno)"),
   (``C.allocGzState, "(gz_statep)malloc(sizeof(gz_state))")]
def unaryExprOps : List (Name × String × String) :=
  [(``Bool.not, "(!", ")"), (``Not, "(!", ")"), (``Complement.complement, "(~", ")"), (``Neg.neg, "(-", ")"),
   (``Option.isNone, "(", " == 0)"), (``Option.isSome, "(", " != 0)"), (``C.Ptr.load, "(*", ")"), (``C.load8, "(*", ")"),
   (``C.allocB, "malloc(", ")"), (``C.ByteAddress.address, "((unsigned long)(", "))"), (``C.strlenB, "strlen((const char *)", ")"),
   (``Zlib.GzFs.fsClose, "close(", ")")]
def ptrWidthType? : Name → Option String | ``C.load64 | ``C.store64 => some "unsigned long *" | ``C.load32 | ``C.store32 => some "int *" | _ => none
def structAct? : Name → Option (Bool × Name)
  | ``C.stGzState => some (true, ``C.GzState) | ``C.stZStream => some (true, ``C.ZStream) | ``C.stInflateState => some (true, ``C.InflateState)
  | ``C.ldGzState => some (false, ``C.GzState) | ``C.ldZStream => some (false, ``C.ZStream) | ``C.ldInflateState => some (false, ``C.InflateState) | _ => none

def fmtProto (fn : FnMeta) : String :=
  let link := match fn.link with | .static => "static " | .staticInline => "static inline " | .hidden => "__attribute__((visibility(\"hidden\"))) " | _ => ""
  let ps := if fn.params.isEmpty then "void" else String.intercalate ", " (fn.params.map fun (p, ct, _) => if ct.endsWith "*" then s!"{ct}{p}" else s!"{ct} {p}")
  s!"{link}{fn.retCTy} {fn.cName}({ps})"

partial def extractListExprs (e : Expr) : Option (List Expr) := match e.consumeMData with
  | .letE _ _ v body _ => extractListExprs (body.instantiate1 v)
  | e => if e.isAppOfArity ``Array.mk 2 || e.isAppOfArity ``List.toArray 2 then extractListExprs e.getAppArgs[1]!
    else if e.isAppOfArity ``List.nil 1 then some [] else if e.isAppOfArity ``List.cons 3 then return e.getAppArgs[1]! :: (← extractListExprs e.getAppArgs[2]!) else none

def emitStaticArray (evalInt : Expr → MetaM (Option Int)) (name cTy : String) (valExpr : Expr) : MetaM String := do
  let ty ← Meta.whnfR (← Meta.inferType valExpr)
  if ty.isAppOfArity ``Array 1 then
    let elemTy ← Meta.whnfR ty.getAppArgs[0]!
    let some elems := extractListExprs valExpr | throwError m!"non-literal array {name}"
    if elemTy.isConstOf ``UInt16 then return arrayDecl cTy name (← elems.mapM fun x => return toString ((← evalInt x).getD 0).toNat)
    if elemTy.isConstOf ``UInt32 then return arrayDecl cTy name (← elems.mapM fun x => return s!"{((← evalInt x).getD 0).toNat % (2^32)}U")
    if elemTy.isConstOf ``C.Code then
      return arrayDecl "code" name (← elems.mapM fun x => do
        let mut e := x.consumeMData; while e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``liftM 5 do e := e.getAppArgs.back!.consumeMData
        let ca := e.getAppArgs; return "{" ++ s!"{(← evalInt ca[0]!).getD 0},{(← evalInt ca[1]!).getD 0},{(← evalInt ca[2]!).getD 0}" ++ "}")
    if elemTy.isAppOfArity ``Array 1 then
      let rows ← elems.mapM fun r => do
        let some cs := extractListExprs r | throwError "bad 2d array row"
        return "{" ++ String.intercalate ", " (← cs.mapM fun x => return s!"{((← evalInt x).getD 0).toNat % (2^32)}U") ++ "}"
      let cols := match rows.head? with | some h => (h.splitOn ",").length | none => 0
      return s!"static const {cTy} {name}[{rows.length}][{cols}] = " ++ "{\n    " ++ String.intercalate ",\n    " rows ++ "\n};\n"
  throwError m!"unsupported static array table {name} of type {ty}"

end Lean2C.ABI
