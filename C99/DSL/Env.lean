import Lean
import C99.AST

/-!
# Scoped Environment State for the C99 DSL (`C99.DSL.Env`)

Separates `[init]` persistent/transient environment extensions into a base module so
`C99.DSL.Syntax` and downstream modules can safely evaluate them during parsing and
elaboration without hitting Lean 4's same-module `[init]` restriction.
-/

namespace C99.DSL

open Lean

inductive CMacroKind where
  | constExpr (val : Int) (ty : IntKind) (suf : LitSuffix) (rad : LitRadix) (sym : String)
  | objExpr (stx : Syntax)
  | fnExpr (params : List String) (stx : Syntax)
  | fnStmt (params : List String) (stx : Syntax)
  | fieldAlias (path : List String)
  deriving Inhabited

structure CScopeData where
  typedefs : List (String × CTy) := []
  tags : List (String × TagDef) := []
  consts : List (String × Int) := []
  macros : List (String × CMacroKind) := []
  qualAliases : List (String × Bool) := []
  linkAliases : List (String × Linkage) := []
  specView : Option Name := none
  deriving Inhabited

def mergeScopeData (a b : CScopeData) : CScopeData :=
  { typedefs := b.typedefs ++ a.typedefs
    tags := b.tags ++ a.tags
    consts := b.consts ++ a.consts
    macros := b.macros ++ a.macros
    qualAliases := b.qualAliases ++ a.qualAliases
    linkAliases := b.linkAliases ++ a.linkAliases
    specView := b.specView.orElse fun _ => a.specView }

/-- Persisted across module imports (used inside `c_header_begin` .. `c_header_end`). -/
initialize persistedScopeExt : SimplePersistentEnvExtension CScopeData CScopeData ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries =>
      entries.foldl (fun acc arr => arr.foldl mergeScopeData acc) {}
    addEntryFn := fun s e => mergeScopeData s e
  }

/-- Transient within the active file / translation unit (`c_tu_begin` .. `c_tu_end`). -/
initialize localScopeExt : EnvExtension CScopeData ←
  registerEnvExtension (pure {})

structure ActiveTU where
  leanName : Name
  fileName : String
  itemChunks : Array Expr := #[]
  contractNames : Array Name := #[]
  isHeader : Bool := false
  deriving Inhabited

initialize activeTUExt : EnvExtension (Option ActiveTU) ←
  registerEnvExtension (pure none)

def getScopeData (env : Environment) : CScopeData :=
  mergeScopeData (persistedScopeExt.getState env) (localScopeExt.getState env)

def lookupTypedef? (env : Environment) (s : String) : Option CTy :=
  ((localScopeExt.getState env).typedefs.lookup s).orElse fun _ =>
    (persistedScopeExt.getState env).typedefs.lookup s

def lookupMacro? (env : Environment) (s : String) : Option CMacroKind :=
  ((localScopeExt.getState env).macros.lookup s).orElse fun _ =>
    (persistedScopeExt.getState env).macros.lookup s

def lookupConst? (env : Environment) (s : String) : Option Int :=
  ((localScopeExt.getState env).consts.lookup s).orElse fun _ =>
    (persistedScopeExt.getState env).consts.lookup s

def lookupTag? (env : Environment) (s : String) : Option TagDef :=
  ((localScopeExt.getState env).tags.lookup s).orElse fun _ =>
    (persistedScopeExt.getState env).tags.lookup s

def lookupQualAlias? (env : Environment) (s : String) : Option Bool :=
  ((localScopeExt.getState env).qualAliases.lookup s).orElse fun _ =>
    (persistedScopeExt.getState env).qualAliases.lookup s

def lookupLinkAlias? (env : Environment) (s : String) : Option Linkage :=
  ((localScopeExt.getState env).linkAliases.lookup s).orElse fun _ =>
    (persistedScopeExt.getState env).linkAliases.lookup s

def lookupSpecView? (env : Environment) : Option Name :=
  ((localScopeExt.getState env).specView).orElse fun _ =>
    (persistedScopeExt.getState env).specView

def pushScopeData (env : Environment) (d : CScopeData) : Environment :=
  let persist := match activeTUExt.getState env with
    | some atu => atu.isHeader
    | none => true
  if persist then persistedScopeExt.addEntry env d
  else localScopeExt.modifyState env (mergeScopeData · d)

end C99.DSL
