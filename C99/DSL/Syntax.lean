import C99.DSL.Env

/-!
# C-Like Surface Syntax (`C99.DSL.Syntax`)

Defines the Lean 4 syntax categories for C99 types, expressions, initializers, statements,
macros, and top-level `c_*` commands.
-/

namespace C99.DSL

open Lean Parser

private def cReservedWords : List String :=
  [ "auto", "break", "case", "char", "const", "continue", "default", "do", "double",
    "else", "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long",
    "register", "restrict", "return", "short", "signed", "sizeof", "static", "struct",
    "switch", "typedef", "union", "unsigned", "void", "volatile", "while",
    "va_list", "va_start", "va_end" ]

def isCReserved (s : String) : Bool :=
  cReservedWords.contains s

private partial def scanCIdentEnd (allowPrime : Bool) (c : InputContext) (p : String.Pos.Raw) : String.Pos.Raw :=
  if c.atEnd p then p
  else
    let ch := c.get p
    if ch.isAlphanum || ch == '_' || (allowPrime && ch == '\'') then
      scanCIdentEnd allowPrime c (c.next p)
    else p

private def scanIdentToken (ok : Environment → String → Bool) (err : String)
    (allowPrime : Bool := false) : ParserFn := fun c s =>
  let iniPos := s.pos
  if c.atEnd iniPos then s.mkError err
  else
    let ch := c.get iniPos
    if !(ch.isAlpha || ch == '_') then s.mkError err
    else
      let stopPos := scanCIdentEnd allowPrime c (c.next iniPos)
      let val := c.extract iniPos stopPos
      if !ok c.env val then s.mkError err
      else
        let s := s.setPos stopPos
        let s := whitespace c s
        let info := SourceInfo.original "".toRawSubstring iniPos (c.substring stopPos s.pos) stopPos
        s.pushSyntax (Syntax.ident info (c.substring iniPos stopPos) (Name.mkSimple val) [])

private def isCAliasOrReserved (env : Environment) (val : String) : Bool :=
  isCReserved val || (lookupQualAlias? env val).isSome || (lookupLinkAlias? env val).isSome

def cRawIdentFn : ParserFn :=
  scanIdentToken (fun _ _ => true) "expected C identifier"

def cRawIdent : Parser := { fn := cRawIdentFn }
@[combinator_formatter cRawIdent] def cRawIdent.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cRawIdent] def cRawIdent.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

def cIdentFn : ParserFn :=
  scanIdentToken (fun env val => !isCAliasOrReserved env val) "expected C identifier"

def cIdent : Parser := { fn := cIdentFn }
@[combinator_formatter cIdent] def cIdent.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cIdent] def cIdent.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

private def specReservedWords : List String := ["forall", "exists", "let", "lean"]

def cSpecIdentFn : ParserFn :=
  scanIdentToken (fun _ val => !specReservedWords.contains val)
    "expected C spec identifier" (allowPrime := true)

def cSpecIdent : Parser := { fn := cSpecIdentFn }
@[combinator_formatter cSpecIdent] def cSpecIdent.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cSpecIdent] def cSpecIdent.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

def cTypedefNameFn : ParserFn :=
  scanIdentToken (fun env val => !isCAliasOrReserved env val && (lookupTypedef? env val).isSome)
    "expected registered C typedef name"

def cTypedefName : Parser := { fn := cTypedefNameFn }
@[combinator_formatter cTypedefName] def cTypedefName.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cTypedefName] def cTypedefName.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

def cQualAliasNameFn : ParserFn :=
  scanIdentToken (fun env val => (lookupQualAlias? env val).isSome) "expected C qualifier alias"

def cQualAliasName : Parser := { fn := cQualAliasNameFn }
@[combinator_formatter cQualAliasName] def cQualAliasName.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cQualAliasName] def cQualAliasName.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

def cLinkAliasNameFn : ParserFn :=
  scanIdentToken (fun env val => (lookupLinkAlias? env val).isSome) "expected C linkage alias"

def cLinkAliasName : Parser := { fn := cLinkAliasNameFn }
@[combinator_formatter cLinkAliasName] def cLinkAliasName.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cLinkAliasName] def cLinkAliasName.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

private def litSuffixes : List String :=
  ["U", "L", "UL", "LL", "ULL", "u", "l", "ul", "ll", "ull"]

def cLitSuffixFn : ParserFn := fun c s =>
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := identFn c s
  if s.hasError then s
  else
    let val := s.stxStack.back.getId.toString
    if litSuffixes.contains val then s
    else ((s.setPos iniPos).shrinkStack iniSz).mkError "expected integer literal suffix"

def cLitSuffix : Parser := { fn := cLitSuffixFn }
@[combinator_formatter cLitSuffix] def cLitSuffix.formatter : PrettyPrinter.Formatter := fun _ => pure ()
@[combinator_parenthesizer cLitSuffix] def cLitSuffix.parenthesizer : PrettyPrinter.Parenthesizer := fun _ => pure ()

/-! ## C99 Syntax Categories -/

declare_syntax_cat c_qual
declare_syntax_cat c_sign_rest
declare_syntax_cat c_ty_base
declare_syntax_cat c_ty_spec
declare_syntax_cat c_ptr_mod
declare_syntax_cat c_ty
declare_syntax_cat c_param
declare_syntax_cat c_expr
declare_syntax_cat c_init
declare_syntax_cat c_init_decl
declare_syntax_cat c_decl
declare_syntax_cat c_field_decl
declare_syntax_cat c_stmt
declare_syntax_cat c_link_pre
declare_syntax_cat c_link_mid
declare_syntax_cat c_enum_item

syntax (name := cQualConst) "const" : c_qual
syntax (name := cQualAlias) cQualAliasName : c_qual
syntax (name := cQualVolatile) "volatile" : c_qual

syntax (name := cSignChar) "char" : c_sign_rest
syntax (name := cSignShort) "short" ("int")? : c_sign_rest
syntax (name := cSignLLong) atomic("long" "long") ("int")? : c_sign_rest
syntax (name := cSignLong) "long" ("int")? : c_sign_rest
syntax (name := cSignInt) "int" : c_sign_rest

syntax (name := cBaseVoid) "void" : c_ty_base
syntax (name := cBaseVaList) "va_list" : c_ty_base
syntax (name := cBaseChar) "char" : c_ty_base
syntax (name := cBaseInt) "int" : c_ty_base
syntax (name := cBaseShort) "short" ("int")? : c_ty_base
syntax (name := cBaseLong) "long" ("long")? ("int")? : c_ty_base
syntax (name := cBaseUnsigned) "unsigned" (c_sign_rest)? : c_ty_base
syntax (name := cBaseSigned) "signed" (c_sign_rest)? : c_ty_base
syntax (name := cBaseAnonStruct) atomic("struct" "{") (c_field_decl ";")* "}" : c_ty_base
syntax (name := cBaseAnonUnion) atomic("union" "{") (c_field_decl ";")* "}" : c_ty_base
syntax (name := cBaseStruct) "struct" cIdent : c_ty_base
syntax (name := cBaseUnion) "union" cIdent : c_ty_base
syntax (name := cBaseEnum) "enum" cIdent : c_ty_base
syntax (name := cBaseTypedef) cTypedefName : c_ty_base

syntax (name := cTySpec) c_qual* c_ty_base c_qual* : c_ty_spec
syntax (name := cPtrMod) "*" c_qual* : c_ptr_mod

syntax (name := cTySimple) c_ty_spec c_ptr_mod* ("[" (c_expr)? "]")* : c_ty
syntax (name := cTyFnPtr) atomic(c_ty_spec c_ptr_mod* "(" "*" ")") "(" c_param,* ")" : c_ty

syntax (name := cParamEllipsis) "..." : c_param
syntax (name := cParamFnPtr) atomic(c_ty_spec c_ptr_mod* "(" "*" (cIdent)? ")") "(" c_param,* ")" : c_param
syntax (name := cParamSimple) c_ty_spec c_ptr_mod* (cIdent)? ("[" (c_expr)? "]")* : c_param

syntax (name := cFieldDecl) c_ty_spec c_init_decl,+ : c_field_decl

-- Expressions (prec 95 postfix down to 10 comma)
syntax:max (name := cLitExpr) num (noWs cLitSuffix)? : c_expr
syntax:max (name := cCharExpr) charLit : c_expr
syntax:max (name := cStrExpr) str+ : c_expr
syntax:max (name := cVaStart) "va_start" "(" cIdent "," cIdent ")" : c_expr
syntax:max (name := cVaEnd) "va_end" "(" cIdent ")" : c_expr
syntax:max (name := cVarExpr) cIdent : c_expr
syntax:max (name := cSizeofTy) (priority := high) atomic("sizeof" "(" c_ty ")") : c_expr
syntax:max (name := cParenExpr) "(" c_expr ")" : c_expr

syntax:95 (name := cIndex) c_expr:95 "[" c_expr "]" : c_expr
syntax:95 (name := cCall) c_expr:95 "(" c_expr:15,* ")" : c_expr
syntax:95 (name := cMember) c_expr:95 "." cIdent : c_expr
syntax:95 (name := cArrow) c_expr:95 "->" cIdent : c_expr
syntax:95 (name := cPostInc) c_expr:95 "++" : c_expr
syntax:95 (name := cPostDec) c_expr:95 ".-" : c_expr

syntax:85 (name := cCast) (priority := high) atomic("(" c_ty ")") c_expr:85 : c_expr
syntax:85 (name := cPreInc) "++" c_expr:85 : c_expr
syntax:85 (name := cPreDec) ".-" c_expr:85 : c_expr
syntax:85 (name := cUnPlus) "+" c_expr:85 : c_expr
syntax:85 (name := cUnNeg) "-" c_expr:85 : c_expr
syntax:85 (name := cBitNot) "~" c_expr:85 : c_expr
syntax:85 (name := cLogNot) "!" c_expr:85 : c_expr
syntax:85 (name := cDeref) "*" c_expr:85 : c_expr
syntax:85 (name := cAddrOf) "&" c_expr:85 : c_expr
syntax:85 (name := cSizeofEx) "sizeof" c_expr:85 : c_expr

syntax:75 (name := cMul) c_expr:75 " * " c_expr:76 : c_expr
syntax:75 (name := cDiv) c_expr:75 " / " c_expr:76 : c_expr
syntax:75 (name := cMod) c_expr:75 " % " c_expr:76 : c_expr
syntax:70 (name := cAdd) c_expr:70 " + " c_expr:71 : c_expr
syntax:70 (name := cSub) c_expr:70 " - " c_expr:71 : c_expr
syntax:65 (name := cShl) c_expr:65 " << " c_expr:66 : c_expr
syntax:65 (name := cShr) c_expr:65 " >> " c_expr:66 : c_expr
syntax:60 (name := cLt)  c_expr:60 " < " c_expr:61 : c_expr
syntax:60 (name := cLe)  c_expr:60 " <= " c_expr:61 : c_expr
syntax:60 (name := cGt)  c_expr:60 " > " c_expr:61 : c_expr
syntax:60 (name := cGe)  c_expr:60 " >= " c_expr:61 : c_expr
syntax:55 (name := cEq)  c_expr:55 " == " c_expr:56 : c_expr
syntax:55 (name := cNe)  c_expr:55 " != " c_expr:56 : c_expr
syntax:50 (name := cBitAnd) c_expr:50 " & " c_expr:51 : c_expr
syntax:45 (name := cBitXor) c_expr:45 " ^ " c_expr:46 : c_expr
syntax:40 (name := cBitOr)  c_expr:40 " | " c_expr:41 : c_expr
syntax:35 (name := cLogAnd) c_expr:35 " && " c_expr:36 : c_expr
syntax:30 (name := cLogOr)  c_expr:30 " || " c_expr:31 : c_expr

syntax:25 (name := cCond) c_expr:30 "?" c_expr:15 ":" c_expr:25 : c_expr
syntax:20 (name := cAssignEq)  c_expr:85 " = " c_expr:20 : c_expr
syntax:20 (name := cAssignAdd) c_expr:85 " += " c_expr:20 : c_expr
syntax:20 (name := cAssignSub) c_expr:85 " -= " c_expr:20 : c_expr
syntax:20 (name := cAssignMul) c_expr:85 " *= " c_expr:20 : c_expr
syntax:20 (name := cAssignDiv) c_expr:85 " /= " c_expr:20 : c_expr
syntax:20 (name := cAssignMod) c_expr:85 " %= " c_expr:20 : c_expr
syntax:20 (name := cAssignAnd) c_expr:85 " &= " c_expr:20 : c_expr
syntax:20 (name := cAssignOr)  c_expr:85 " |= " c_expr:20 : c_expr
syntax:20 (name := cAssignXor) c_expr:85 " ^= " c_expr:20 : c_expr
syntax:20 (name := cAssignShl) c_expr:85 " <<= " c_expr:20 : c_expr
syntax:20 (name := cAssignShr) c_expr:85 " >>= " c_expr:20 : c_expr
syntax:10 (name := cComma) c_expr:10 "," c_expr:15 : c_expr

-- Initializers and declarations
syntax (name := cInitList) "{" c_init,*,? "}" : c_init
syntax (name := cInitExpr) c_expr:15 : c_init

syntax (name := cDeclFnPtr) atomic(c_ptr_mod* "(" "*" cIdent ")") "(" c_param,* ")" ("=" c_init)? : c_init_decl
syntax (name := cDeclVar) c_ptr_mod* cIdent ("[" (c_expr)? "]")* ("=" c_init)? : c_init_decl
syntax (name := cDecl) ("static")? c_ty_spec c_init_decl,+ : c_decl

-- Statements
syntax (name := cStmtNop) ";" : c_stmt
syntax (name := cStmtDecl) (priority := high) atomic(c_decl ";") : c_stmt
syntax (name := cStmtBlock) "{" c_stmt* "}" : c_stmt
syntax (name := cStmtIf) "if" "(" c_expr ")" c_stmt ("else" c_stmt)? : c_stmt
syntax (name := cStmtWhile) "while" "(" c_expr ")" c_stmt : c_stmt
syntax (name := cStmtDoWhile) "do" c_stmt "while" "(" c_expr ")" ";" : c_stmt
syntax (name := cStmtFor) "for" "(" (c_expr)? ";" (c_expr)? ";" (c_expr)? ")" c_stmt : c_stmt
syntax (name := cStmtSwitch) "switch" "(" c_expr ")" c_stmt : c_stmt
syntax (name := cStmtCase) "case" c_expr ":" : c_stmt
syntax (name := cStmtDefault) "default" ":" : c_stmt
syntax (name := cStmtBreak) "break" ";" : c_stmt
syntax (name := cStmtContinue) "continue" ";" : c_stmt
syntax (name := cStmtGoto) "goto" cIdent ";" : c_stmt
syntax (name := cStmtReturn) "return" (c_expr)? ";" : c_stmt
syntax (name := cStmtLabel) atomic(cIdent ":") : c_stmt
syntax (name := cStmtExpr) c_expr ";" : c_stmt

-- Linkage and top-level `c_*` commands
syntax (name := cLinkPreAlias) cLinkAliasName : c_link_pre
syntax (name := cLinkStatic) "static" : c_link_pre
syntax (name := cLinkStaticInline) "static" "inline" : c_link_pre
syntax (name := cLinkExtern) "extern" : c_link_pre
syntax (name := cLinkMidAlias) cLinkAliasName : c_link_mid
syntax (name := cEnumItem) cIdent ("=" c_expr:15)? : c_enum_item

syntax (name := cTuBegin) "c_tu_begin" ident str : command
syntax (name := cTuEnd) "c_tu_end" ident : command
syntax (name := cHeaderBegin) "c_header_begin" ident str : command
syntax (name := cHeaderEnd) "c_header_end" ident : command
syntax (name := cIncludeStr) "c_include" str : command
syntax (name := cIncludeLocal) "c_include_local" str : command
syntax (name := cPpRaw) "c_pp" str : command
syntax (name := cIncludeTuCmd) "c_include_tu" term : command
syntax (name := cQualAliasCmd) "c_qual_alias" cRawIdent ":=" cRawIdent : command
syntax (name := cLinkAliasCmd) "c_link_alias" cRawIdent ":=" cRawIdent : command
syntax (name := cDefineConst) "c_define_const" cIdent ":=" c_expr : command
syntax (name := cDefineExpr) "c_define" cIdent ":=" c_expr : command
syntax (name := cDefineField) "c_define_field" cIdent ":=" cIdent,+ : command
syntax (name := cMacroFn) "c_macro" cIdent "(" cIdent,* ")" ":=" c_expr : command
syntax (name := cMacroStmt) "c_stmt_macro" cIdent "(" cIdent,* ")" ":=" c_stmt : command
syntax (name := cTypedefStructCmd) (priority := high) atomic("c_typedef" "struct" (cIdent)? "{") (c_field_decl ";")* "}" cIdent ";" : command
syntax (name := cTypedefUnionCmd) (priority := high) atomic("c_typedef" "union" (cIdent)? "{") (c_field_decl ";")* "}" cIdent ";" : command
syntax (name := cTypedefEnumCmd) (priority := high) atomic("c_typedef" "enum" (cIdent)? "{") c_enum_item,*,? "}" cIdent ";" : command
syntax (name := cTypedefCmd) "c_typedef" c_ty_spec c_init_decl,+ ";" : command
syntax (name := cFwdTag) "c_fwd" ("struct" <|> "union") cIdent ";" : command
syntax (name := cStructCmd) "c_struct" cIdent "{" (c_field_decl ";")* "}" ";" : command
syntax (name := cUnionCmd) "c_union" cIdent "{" (c_field_decl ";")* "}" ";" : command
syntax (name := cEnumCmd) "c_enum" (cIdent)? "{" c_enum_item,*,? "}" ";" : command
syntax (name := cGlobalCmd) "c_global" (c_link_pre)? c_ty_spec (c_link_mid)? c_init_decl,+ ";" : command
syntax (name := cProtoCmd) "c_proto" (c_link_pre)? c_ty_spec c_ptr_mod* (c_link_mid)? cIdent "(" c_param,* ")" ";" : command
declare_syntax_cat c_spec
syntax:max (name := cSpecLean) "lean" "(" term ")" : c_spec
syntax:max (name := cSpecForallIn) (priority := high) atomic("forall" "(" cSpecIdent "in") c_spec:20 "," c_spec ")" : c_spec
syntax:max (name := cSpecForall) "forall" "(" cSpecIdent "," c_spec ")" : c_spec
syntax:max (name := cSpecExists) "exists" "(" cSpecIdent "," c_spec ")" : c_spec
syntax:max (name := cSpecNum) num : c_spec
syntax:max (name := cSpecVar) cSpecIdent : c_spec
syntax:max (name := cSpecParen) "(" c_spec ")" : c_spec

syntax:95 (name := cSpecArrow) c_spec:95 "->" cSpecIdent : c_spec
syntax:95 (name := cSpecField) c_spec:95 "." cSpecIdent : c_spec
syntax:95 (name := cSpecApp)   c_spec:95 "(" c_spec:20,* ")" : c_spec

syntax:85 (name := cSpecCast)   (priority := high) atomic("(" c_ty ")") c_spec:85 : c_spec
syntax:85 (name := cSpecNeg)    "-" c_spec:85 : c_spec
syntax:85 (name := cSpecBitNot) "~" c_spec:85 : c_spec
syntax:85 (name := cSpecNot)    "!" c_spec:85 : c_spec
syntax:85 (name := cSpecDeref)  "*" c_spec:85 : c_spec

syntax:75 (name := cSpecMul)    c_spec:75 " * " c_spec:76 : c_spec
syntax:75 (name := cSpecDiv)    c_spec:75 " / " c_spec:76 : c_spec
syntax:75 (name := cSpecMod)    c_spec:75 " % " c_spec:76 : c_spec
syntax:70 (name := cSpecAdd)    c_spec:70 " + " c_spec:71 : c_spec
syntax:70 (name := cSpecSub)    c_spec:70 " - " c_spec:71 : c_spec
syntax:65 (name := cSpecShl)    c_spec:65 " << " c_spec:66 : c_spec
syntax:65 (name := cSpecShr)    c_spec:65 " >> " c_spec:66 : c_spec
syntax:60 (name := cSpecLt)     c_spec:61 " < " c_spec:61 : c_spec
syntax:60 (name := cSpecLe)     c_spec:61 " <= " c_spec:61 : c_spec
syntax:60 (name := cSpecGt)     c_spec:61 " > " c_spec:61 : c_spec
syntax:60 (name := cSpecGe)     c_spec:61 " >= " c_spec:61 : c_spec
syntax:55 (name := cSpecEq)     c_spec:56 " == " c_spec:56 : c_spec
syntax:55 (name := cSpecNe)     c_spec:56 " != " c_spec:56 : c_spec
syntax:50 (name := cSpecBitAnd) c_spec:50 " & " c_spec:51 : c_spec
syntax:45 (name := cSpecBitXor) c_spec:45 " ^ " c_spec:46 : c_spec
syntax:40 (name := cSpecBitOr)  c_spec:40 " | " c_spec:41 : c_spec
syntax:35 (name := cSpecAnd)    c_spec:36 " && " c_spec:35 : c_spec
syntax:30 (name := cSpecOr)     c_spec:31 " || " c_spec:30 : c_spec
syntax:25 (name := cSpecCond)   c_spec:30 "?" c_spec:15 ":" c_spec:25 : c_spec
syntax:20 (name := cSpecImp)    c_spec:21 " ==> " c_spec:15 : c_spec
syntax:15 (name := cSpecLet)    "let" cSpecIdent "=" c_spec:25 "," c_spec:15 : c_spec

declare_syntax_cat c_spec_clause
syntax (name := cSpecRequires) "requires" c_spec ";" : c_spec_clause
syntax (name := cSpecModifies) "modifies" c_spec:20,+ ";" : c_spec_clause
syntax (name := cSpecEnsures)  "ensures"  c_spec ";" : c_spec_clause
syntax (name := cSpecViewCmd)  "c_spec_view" ident : command
syntax (name := cSpecLibCmd)   "c_spec_lib" ident : command
syntax (name := cSpecPredCmd)  "c_spec_pred" cSpecIdent "[" cSpecIdent,* "]" ":=" ident : command
syntax (name := cSpecConstCmd) "c_spec_const" cSpecIdent ":=" ident : command

syntax (name := cFnCmd) "c_fn" (c_link_pre)? c_ty_spec c_ptr_mod* (c_link_mid)? cIdent "(" c_param,* ")" c_spec_clause* c_stmt : command

end C99.DSL
