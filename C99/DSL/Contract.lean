import C99.Semantics

/-!
# Verus-Style Function Contracts for C99 Functions (`C99.DSL.Contract`)

Zlib-agnostic contract record attached to `c_fn` declarations inside the DSL.
Contracts live strictly in Lean `Prop` space and are completely erased from
`C99.FnDef`, `C99.TU`, `C99.Semantics`, and `C99.EmitC`.
-/

namespace C99

structure FnContract (View : Type) where
  fnName : String
  paramTys : List CTy
  variadic : Bool
  retTy : CTy
  pre : TypeEnv → (BlockId → Prop) → View → Mem → List Val → Prop
  modSet : TypeEnv → (BlockId → Prop) → View → Mem → List Val → BlockId → Prop
  post : TypeEnv → (BlockId → Prop) → View → Mem → List Val → Val → Mem → View → Prop

end C99
