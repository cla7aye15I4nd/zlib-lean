import C99.Semantics

/-!
# Pure 1-to-1 Structural C99 Pretty-Printer (`C99.EmitC`)

Translates `C99.AST` translation units directly into standard C99 text.
100% zlib-agnostic with zero metaprogramming or proof-state inspection.
-/

namespace C99.EmitC

private def indentStr (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

private def oct3 (b : UInt8) : String :=
  let v := b.toNat
  let d0 := v / 64
  let d1 := (v / 8) % 8
  let d2 := v % 8
  s!"\\{d0}{d1}{d2}"

private def escapeByte (inStr : Bool) (b : UInt8) : String :=
  match b with
  | 0 => "\\0"
  | 9 => "\\t"
  | 10 => "\\n"
  | 13 => "\\r"
  | 34 => if inStr then "\\\"" else "\""
  | 39 => if inStr then "'" else "\\'"
  | 92 => "\\\\"
  | _ =>
    if 32 ≤ b.toNat && b.toNat ≤ 126 then
      String.singleton (Char.ofNat b.toNat)
    else oct3 b

def emitStrLit (s : String) : String :=
  let body := String.join (s.toUTF8.toList.map (escapeByte true))
  s!"\"{body}\""

private def toRadix (base : Nat) (n : Nat) : String :=
  if h : 1 < base then
    let rec go (k : Nat) (acc : List Char) : List Char :=
      if hk : k == 0 then acc
      else
        let d := k % base
        let ch := Char.ofNat (if d < 10 then '0'.toNat + d else 'a'.toNat + (d - 10))
        have : k / base < k := Nat.div_lt_self (Nat.pos_of_ne_zero (by simpa using hk)) h
        go (k / base) (ch :: acc)
      termination_by k
    if n == 0 then "0" else String.ofList (go n [])
  else toString n

def emitSuffix : LitSuffix → String
  | .none => "" | .U => "U" | .L => "L" | .UL => "UL" | .LL => "LL" | .ULL => "ULL"

def emitIntLit (v : Int) (_k : IntKind) (suf : LitSuffix) (rad : LitRadix) (sym? : Option String := none) :
    String :=
  match sym? with
  | some sym => sym
  | none =>
    let s := emitSuffix suf
    match rad with
    | .char =>
      let b := UInt8.ofNat (v.toNat % 256)
      s!"'{escapeByte false b}'"
    | .hex =>
      if v < 0 then s!"-0x{toRadix 16 (-v).toNat}{s}" else s!"0x{toRadix 16 v.toNat}{s}"
    | .oct =>
      if v < 0 then s!"-0{toRadix 8 (-v).toNat}{s}" else s!"0{toRadix 8 v.toNat}{s}"
    | .dec => s!"{v}{s}"

mutual
partial def emitDecl (name : String) (ty : CTy) : String :=
  emitDeclarator name false ty

partial def emitDeclarator (inner : String) (isPtrInner : Bool) (ty : CTy) : String :=
  let sp (s : String) := if s == "" then "" else " " ++ s
  match ty with
  | .void => "void" ++ sp inner
  | .int k => k.render ++ sp inner
  | .typedef n _ => n ++ sp inner
  | .structTy tag => s!"struct {tag}" ++ sp inner
  | .unionTy tag => s!"union {tag}" ++ sp inner
  | .enumTy tag _ => s!"enum {tag}" ++ sp inner
  | .vaList => "va_list" ++ sp inner
  | .anonStruct flds =>
    let fs := String.intercalate " " (flds.map fun (n, t) => emitDecl n t ++ ";")
    s!"struct \{ {fs} }" ++ sp inner
  | .anonUnion flds =>
    let fs := String.intercalate " " (flds.map fun (n, t) => emitDecl n t ++ ";")
    s!"union \{ {fs} }" ++ sp inner
  | .const_ (.ptr to) =>
    let m := if inner == "" then "const" else "const " ++ inner
    emitDeclarator m isPtrInner (.ptr to)
  | .const_ (.fnPtr ret ps v) =>
    let m := if inner == "" then "const" else "const " ++ inner
    emitDeclarator m isPtrInner (.fnPtr ret ps v)
  | .const_ (.array el len?) =>
    emitDeclarator inner isPtrInner (.array (.const_ el) len?)
  | .const_ t => "const " ++ emitDeclarator inner isPtrInner t
  | .ptr to => emitDeclarator ("*" ++ inner) true to
  | .array el len? =>
    let base := if isPtrInner then s!"({inner})" else inner
    let suf := match len? with | some n => s!"[{n}]" | none => "[]"
    emitDeclarator (base ++ suf) false el
  | .fnPtr ret params variadic =>
    let pstr :=
      if params.isEmpty then (if variadic then "..." else "void")
      else String.intercalate ", " (params.map (emitDecl "")) ++ (if variadic then ", ..." else "")
    let mid := s!"(*{inner})({pstr})"
    emitDeclarator mid false ret
end

def emitUnOp : UnOp → String
  | .neg => "-" | .bitNot => "~" | .logNot => "!" | .plus => "+"

def emitBinOp : BinOp → String × Nat
  | .mul => ("*", 13) | .div => ("/", 13) | .mod => ("%", 13)
  | .add => ("+", 12) | .sub => ("-", 12)
  | .shl => ("<<", 11) | .shr => (">>", 11)
  | .lt => ("<", 10) | .le => ("<=", 10) | .gt => (">", 10) | .ge => (">=", 10)
  | .eq => ("==", 9) | .ne => ("!=", 9)
  | .bitAnd => ("&", 8) | .bitXor => ("^", 7) | .bitOr => ("|", 6)

def emitAssignOp : AssignOp → String
  | .eq => "=" | .addEq => "+=" | .subEq => "-=" | .mulEq => "*=" | .divEq => "/="
  | .modEq => "%=" | .andEq => "&=" | .orEq => "|=" | .xorEq => "^=" | .shlEq => "<<=" | .shrEq => ">>="

def exprPrec : CExpr → Nat
  | .comma _ _ => 1
  | .assign _ _ _ => 2
  | .cond _ _ _ => 3
  | .logOr _ _ => 4
  | .logAnd _ _ => 5
  | .binary op _ _ => (emitBinOp op).2
  | .cast _ _ | .unary _ _ | .deref _ | .addrOf _ | .sizeOfTy _ | .sizeOfExpr _ => 14
  | .incDec .preInc _ | .incDec .preDec _ => 14
  | _ => 15

mutual
partial def emitExprP (minPrec : Nat) (e : CExpr) : String :=
  let s := emitExpr e
  if exprPrec e < minPrec then s!"({s})" else s

partial def emitExpr : CExpr → String
  | .lit v k suf rad sym? => emitIntLit v k suf rad sym?
  | .strLit s => emitStrLit s
  | .var name => name
  | .sizeOfTy ty => s!"sizeof({emitDecl "" ty})"
  | .sizeOfExpr e => s!"sizeof({emitExpr e})"
  | .unary op e => s!"{emitUnOp op}{emitExprP 14 e}"
  | .binary op l r =>
    let (opStr, p) := emitBinOp op
    s!"{emitExprP p l} {opStr} {emitExprP (p + 1) r}"
  | .logAnd l r => s!"{emitExprP 5 l} && {emitExprP 6 r}"
  | .logOr l r => s!"{emitExprP 4 l} || {emitExprP 5 r}"
  | .cond c t f => s!"{emitExprP 4 c} ? {emitExprP 3 t} : {emitExprP 3 f}"
  | .comma l r => s!"{emitExprP 1 l}, {emitExprP 2 r}"
  | .cast ty e => s!"({emitDecl "" ty}){emitExprP 14 e}"
  | .deref e => s!"*{emitExprP 14 e}"
  | .addrOf e => s!"&{emitExprP 14 e}"
  | .index b i => s!"{emitExprP 15 b}[{emitExpr i}]"
  | .member b fld => s!"{emitExprP 15 b}.{fld}"
  | .arrow b fld => s!"{emitExprP 15 b}->{fld}"
  | .assign op l r => s!"{emitExprP 14 l} {emitAssignOp op} {emitExprP 2 r}"
  | .incDec .preInc l => s!"++{emitExprP 14 l}"
  | .incDec .preDec l => s!"--{emitExprP 14 l}"
  | .incDec .postInc l => s!"{emitExprP 15 l}++"
  | .incDec .postDec l => s!"{emitExprP 15 l}--"
  | .call fn args =>
    let argStr := String.intercalate ", " (args.map emitExpr)
    s!"{emitExprP 15 fn}({argStr})"
  | .vaStart ap last => s!"va_start({ap}, {last})"
  | .vaEnd ap => s!"va_end({ap})"
  | .paren e => s!"({emitExpr e})"
end

private def chunkLines (ind : String) (items : List String) (perLine : Nat := 8) : String :=
  let lim := max 1 perLine
  let rec go (cur : List String) (cnt : Nat) : List String → List String
    | [] => if cur.isEmpty then [] else [ind ++ String.intercalate ", " cur.reverse]
    | x :: xs =>
      let cur' := x :: cur
      if cnt + 1 ≥ lim then
        (ind ++ String.intercalate ", " cur'.reverse) :: go [] 0 xs
      else
        go cur' (cnt + 1) xs
  String.intercalate ",\n" (go [] 0 items)

private def fmtArrayInt (k : IntKind) (rad : LitRadix) (v : Int) : String :=
  let suf := match k, rad with
    | .u64, _ => LitSuffix.ULL
    | .i64, _ => LitSuffix.LL
    | .u32, .hex => LitSuffix.U
    | .u32, _ => if v ≥ 2147483648 then LitSuffix.U else LitSuffix.none
    | _, _ => LitSuffix.none
  emitIntLit v k suf rad

partial def emitInit (ind : Nat) : InitVal → String
  | .expr e => emitExpr e
  | .list xs =>
    if xs.isEmpty then "{ 0 }"
    else "{ " ++ String.intercalate ", " (xs.map (emitInit ind)) ++ " }"
  | .intArray k rad vals =>
    if vals.isEmpty then "{ 0 }"
    else
      let items := vals.toList.map (fmtArrayInt k rad)
      "{\n" ++ chunkLines (indentStr (ind + 1)) items ++ "\n" ++ indentStr ind ++ "}"
  | .intArray2D k rad rows =>
    let rowStrs := rows.toList.map fun r =>
      let items := r.toList.map (fmtArrayInt k rad)
      indentStr (ind + 1) ++ "{\n" ++ chunkLines (indentStr (ind + 2)) items ++ "\n" ++ indentStr (ind + 1) ++ "}"
    "{\n" ++ String.intercalate ",\n" rowStrs ++ "\n" ++ indentStr ind ++ "}"
  | .tupleArray nestedBraces rows =>
    let rowStrs := rows.toList.map fun r =>
      let elems := r.toList.map toString
      if nestedBraces then "{" ++ String.intercalate ", " (elems.map fun s => s!"\{{s}}") ++ "}"
      else "{" ++ String.intercalate ", " elems ++ "}"
    "{\n" ++ chunkLines (indentStr (ind + 1)) rowStrs 6 ++ "\n" ++ indentStr ind ++ "}"

def emitVarDecl (ind : Nat) (d : VarDecl) (skipStatic : Bool := false) : String :=
  let statPfx := if d.isStatic && !skipStatic then "static " else ""
  let constPfx := if d.isConst && !d.ty.isConst then "const " else ""
  let lhs := statPfx ++ constPfx ++ emitDecl d.name d.ty
  match d.init? with
  | none => lhs
  | some iv => s!"{lhs} = {emitInit ind iv}"

private def emitArm (ind : Nat) (pfx : String) (body : CStmt) (emitS : Nat → CStmt → String) : String :=
  match body with
  | .caseStmt _ _ | .defaultStmt _ | .labelStmt _ _ => s!"{indentStr ind}{pfx}\n{emitS ind body}"
  | .nop => s!"{indentStr ind}{pfx} ;"
  | .block _ => s!"{indentStr ind}{pfx}\n{emitS ind body}"
  | _ => s!"{indentStr ind}{pfx}\n{emitS (ind + 1) body}"

partial def emitStmt (ind : Nat) : CStmt → String
  | .nop => indentStr ind ++ ";"
  | .expr e => indentStr ind ++ emitExpr e ++ ";"
  | .decl d => indentStr ind ++ emitVarDecl ind d ++ ";"
  | .decls ds => String.intercalate "\n" (ds.map fun d => indentStr ind ++ emitVarDecl ind d ++ ";")
  | .block ss =>
    let body := String.intercalate "\n" (ss.map (emitStmt (ind + 1)))
    if ss.isEmpty then indentStr ind ++ "{}"
    else indentStr ind ++ "{\n" ++ body ++ "\n" ++ indentStr ind ++ "}"
  | .ifStmt c t f? =>
    let emitBranch (s : CStmt) := match s with
      | .block _ => "\n" ++ emitStmt ind s
      | _ => "\n" ++ emitStmt (ind + 1) s
    let head := s!"{indentStr ind}if ({emitExpr c}){emitBranch t}"
    match f? with
    | none => head
    | some els@(.ifStmt _ _ _) => s!"{head}\n{indentStr ind}else {((emitStmt ind els).trimAsciiStart).toString}"
    | some f => s!"{head}\n{indentStr ind}else{emitBranch f}"
  | .whileStmt c b =>
    let bstr := match b with | .block _ => "\n" ++ emitStmt ind b | _ => "\n" ++ emitStmt (ind + 1) b
    s!"{indentStr ind}while ({emitExpr c}){bstr}"
  | .doWhileStmt b c =>
    let bstr := match b with
      | .block _ => (emitStmt ind b).trimAsciiStart.toString
      | _ => "\n" ++ emitStmt (ind + 1) b ++ "\n" ++ indentStr ind
    s!"{indentStr ind}do {bstr} while ({emitExpr c});"
  | .forStmt i? c? stp? b =>
    let istr := i?.map emitExpr |>.getD ""
    let cstr := c?.map emitExpr |>.getD ""
    let sstr := stp?.map emitExpr |>.getD ""
    let bstr := match b with | .block _ => "\n" ++ emitStmt ind b | _ => "\n" ++ emitStmt (ind + 1) b
    s!"{indentStr ind}for ({istr}; {cstr}; {sstr}){bstr}"
  | .switchStmt scrut b =>
    let bstr := match b with | .block _ => "\n" ++ emitStmt ind b | _ => "\n" ++ emitStmt (ind + 1) b
    s!"{indentStr ind}switch ({emitExpr scrut}){bstr}"
  | .caseStmt v b => emitArm ind s!"case {v}:" b emitStmt
  | .defaultStmt b => emitArm ind "default:" b emitStmt
  | .labelStmt l b =>
    let lblInd := if ind > 0 then ind - 1 else 0
    emitArm lblInd s!"{l}:" b emitStmt
  | .breakStmt => indentStr ind ++ "break;"
  | .continueStmt => indentStr ind ++ "continue;"
  | .gotoStmt l => indentStr ind ++ s!"goto {l};"
  | .returnStmt none => indentStr ind ++ "return;"
  | .returnStmt (some e) => indentStr ind ++ s!"return {emitExpr e};"

def emitLinkage : Linkage → String
  | .export_ => ""
  | .hidden => "C99_HIDDEN "
  | .static_ => "static "
  | .staticInline => "static inline "
  | .extern_ => "extern "

private def emitFnSig (name : String) (ret : CTy) (params : List Param) (variadic : Bool) : String :=
  let pstr :=
    if params.isEmpty then (if variadic then "..." else "void")
    else String.intercalate ", " (params.map fun p => emitDecl p.name p.ty) ++ (if variadic then ", ..." else "")
  emitDecl s!"{name}({pstr})" ret

def emitTopItem : TopItem → String
  | .includeSys p => s!"#include <{p}>"
  | .includeLocal p => s!"#include \"{p}\""
  | .ppRaw txt => txt
  | .typedefDecl name ty => s!"typedef {emitDecl name ty};"
  | .fwdTag isUnion tag => s!"{if isUnion then "union" else "struct"} {tag};"
  | .tagDecl isUnion tag? td? flds =>
    let kw := if isUnion then "union" else "struct"
    let tagPart := tag?.map (" " ++ ·) |>.getD ""
    let body := String.intercalate "\n" (flds.map fun (n, t) => s!"  {emitDecl n t};")
    let core := s!"{kw}{tagPart} \{\n{body}\n}"
    match td? with | some td => s!"typedef {core} {td};" | none => s!"{core};"
  | .enumDecl tag? td? items =>
    let tagPart := tag?.map (" " ++ ·) |>.getD ""
    let body := String.intercalate ",\n" (items.map fun (n, v?) => match v? with
      | some v => s!"  {n} = {v}" | none => s!"  {n}")
    let core := s!"enum{tagPart} \{\n{body}\n}"
    match td? with | some td => s!"typedef {core} {td};" | none => s!"{core};"
  | .globalDecl link d =>
    let skipStatic := link == .static_ || link == .extern_
    s!"{emitLinkage link}{emitVarDecl 0 d skipStatic};"
  | .fnProto link ret name ps v => s!"{emitLinkage link}{emitFnSig name ret ps v};"
  | .fnDef fn =>
    let head := s!"{emitLinkage fn.linkage}{emitFnSig fn.name fn.retTy fn.params fn.variadic}"
    let body := match fn.body with | .block _ => emitStmt 0 fn.body | s => "{\n" ++ emitStmt 1 s ++ "\n}"
    s!"{head}\n{body}"

private def usesHidden (tu : TU) : Bool :=
  tu.items.any fun
    | .globalDecl l _ | .fnProto l _ _ _ _ => l == .hidden
    | .fnDef f => f.linkage == .hidden
    | _ => false

private def hiddenPrelude : String :=
  "#ifndef C99_HIDDEN\n#  ifdef HAVE_HIDDEN\n#    define C99_HIDDEN __attribute__((visibility(\"hidden\")))\n#  else\n#    define C99_HIDDEN\n#  endif\n#endif\n\n"

def emitTU (tu : TU) : String :=
  (if usesHidden tu then hiddenPrelude else "") ++
  String.intercalate "\n\n" (tu.items.map emitTopItem) ++ "\n"

end C99.EmitC
