import C99.DSL.Syntax

/-!
# Unhygienic C99 Preprocessor Macro Expander (`C99.DSL.Macro`)

Syntax-level unhygienic macro expansion for `c_define`, `c_define_field`,
`c_macro`, and `c_stmt_macro`, faithfully preserving variable capture and
nested macro chains with explicit fuel termination.
-/

namespace C99.DSL

open Lean

private def isSimpleAtomExpr (k : SyntaxNodeKind) : Bool :=
  k == ``cVarExpr || k == ``cLitExpr || k == ``cCharExpr || k == ``cStrExpr ||
  k == ``cParenExpr || k == ``cMember || k == ``cArrow || k == ``cIndex ||
  k == ``cCall

private def wrapParenIfNeeded (stx : Syntax) : Syntax :=
  if isSimpleAtomExpr stx.getKind then stx
  else Syntax.node .none ``cParenExpr #[Syntax.atom .none "(", stx, Syntax.atom .none ")"]

private def mkMember (base : Syntax) (fld : String) : Syntax :=
  Syntax.node .none ``cMember #[base, Syntax.atom .none ".", mkIdent (Name.mkSimple fld)]

private def chainFields (base : Syntax) : List String → Syntax
  | [] => base
  | fld :: rest => chainFields (mkMember base fld) rest

private def mkArrow (base : Syntax) (fld : String) : Syntax :=
  Syntax.node .none ``cArrow #[base, Syntax.atom .none "->", mkIdent (Name.mkSimple fld)]

/-- Recursively expand C macros in any C syntax tree (`c_expr`, `c_stmt`, `c_init`, `c_ty`). -/
partial def expandCMacros (env : Environment) (subst : List (String × Syntax))
    (fuel : Nat) (stx : Syntax) : CoreM Syntax := do
  if fuel == 0 then
    throwErrorAt stx "C macro expansion exceeded recursion limit (possible cyclic macro)"
  match stx with
  | .atom _ _ | .ident .. | .missing => return stx
  | .node info kind args =>
    if kind == ``cVarExpr then
      let id := args[0]!.getId.toString
      if let some rep := subst.lookup id then
        return wrapParenIfNeeded rep
      else if let some mk := lookupMacro? env id then
        match mk with
        | .objExpr body => expandCMacros env [] (fuel - 1) body
        | _ => return stx
      else
        return stx
    else if kind == ``cMember then
      let base' ← expandCMacros env subst fuel args[0]!
      let fld := args[2]!.getId.toString
      match lookupMacro? env fld with
      | some (.fieldAlias (hd :: rest)) =>
        return chainFields (mkMember base' hd) rest
      | _ => return .node info kind #[base', args[1]!, args[2]!]
    else if kind == ``cArrow then
      let base' ← expandCMacros env subst fuel args[0]!
      let fld := args[2]!.getId.toString
      match lookupMacro? env fld with
      | some (.fieldAlias (hd :: rest)) =>
        return chainFields (mkArrow base' hd) rest
      | _ => return .node info kind #[base', args[1]!, args[2]!]
    else if kind == ``cCall then
      let fnStx := args[0]!
      let argsSep := args[2]!
      let rawArgs := argsSep.getSepArgs
      if fnStx.getKind == ``cVarExpr then
        let fnName := fnStx.getArgs[0]!.getId.toString
        if let some (.fnExpr params body) := lookupMacro? env fnName then
          if rawArgs.size != params.length then
            throwErrorAt stx "C macro `{fnName}` expects {params.length} argument(s), got {rawArgs.size}"
          let expArgs ← rawArgs.mapM (expandCMacros env subst (fuel - 1))
          let newSubst := params.zip expArgs.toList
          return ← expandCMacros env newSubst (fuel - 1) body
      let fn' ← expandCMacros env subst fuel fnStx
      let argsSep' ← expandCMacros env subst fuel argsSep
      return .node info kind #[fn', args[1]!, argsSep', args[3]!]
    else if kind == ``cStmtExpr then
      let exprStx := args[0]!
      if exprStx.getKind == ``cCall then
        let fnStx := exprStx.getArgs[0]!
        let rawArgs := exprStx.getArgs[2]!.getSepArgs
        if fnStx.getKind == ``cVarExpr then
          let fnName := fnStx.getArgs[0]!.getId.toString
          if let some (.fnStmt params body) := lookupMacro? env fnName then
            if rawArgs.size != params.length then
              throwErrorAt stx "C statement macro `{fnName}` expects {params.length} argument(s), got {rawArgs.size}"
            let expArgs ← rawArgs.mapM (expandCMacros env subst (fuel - 1))
            let newSubst := params.zip expArgs.toList
            return ← expandCMacros env newSubst (fuel - 1) body
      let expr' ← expandCMacros env subst fuel exprStx
      return .node info kind #[expr', args[1]!]
    else
      let args' ← args.mapM (expandCMacros env subst fuel)
      return .node info kind args'

end C99.DSL
