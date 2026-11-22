import Lean

/-!
# The check of the registry of results

`ZlibF/Results.lean` runs `checkWith` on its lists over the whole library. The check imports nothing of
the library, so `tests/results-check/` runs the same function on small fixture modules.

A *goal* is a definition whose name has a component `Goal` and whose type is `Prop` after its binders
(`Goal.x : Prop`, or `Goal.x (A : HeapApi) : Prop`). The check fails unless:

- no goal is listed twice, and every listed name is a goal without universe parameters;
- the theorem paired with a goal has exactly the goal as its type: `Goal.x`, or
  `∀ a₁ … aₙ, Goal.x a₁ … aₙ` for a goal with binders (syntactic equality of expressions);
- each paired theorem depends on no axiom other than `propext`, `Classical.choice` and `Quot.sound`
  (`Lean.collectAxioms`, the facility behind `#print axioms`; it follows every dependency);
- every required goal is proved;
- every goal in scope is listed, and the number of goals in scope equals the number listed;
- every declaration in scope whose name has a component `Goal` is a goal, or belongs to one: a name
  `….Goal.x` must be a goal, and a longer name `….Goal.x.y` (an equation lemma, an auxiliary) needs
  `….Goal.x` to be one. So a goal cannot hide behind a type that is `Prop` only after unfolding, a
  `structure`, an `axiom` or a `theorem` named like a goal.
-/

namespace ZlibF.Results
open Lean Elab Command

/-- The axioms a proof may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The type of a goal: `Prop` after its binders. -/
def isGoalType : Expr → Bool
  | .forallE _ _ body _ => isGoalType body
  | .sort .zero => true
  | _ => false

/-- The type a theorem proving the goal `g` of type `ty` must have: `g`, or `∀ a₁ … aₙ, g a₁ … aₙ`. -/
def expectedType (g : Name) (ty : Expr) : Expr :=
  go ty 0
where
  go : Expr → Nat → Expr
    | .forallE n t body bi, k => .forallE n t (go body (k + 1)) bi
    | _, k => mkAppN (.const g []) ((List.range k).reverse.map Expr.bvar).toArray

/-- A definition that is a goal: `Prop` after its binders by syntax, no universe parameters. -/
def isGoal (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo d) => isGoalType d.type && d.levelParams.isEmpty
  | _ => false

/-- For a name with a component `Goal`, the name up to the component after the first `Goal`
(`A.Goal.x` for `A.Goal.x.eq_1`); `none` if `Goal` is the last component or absent. -/
def goalHead (n : Name) : Option Name :=
  let cs := n.components
  match cs.findIdx? (· == `Goal) with
  | some i => if i + 1 < cs.length then some ((cs.take (i + 2)).foldl (fun acc c => acc ++ c) .anonymous) else none
  | none => none

/-- The check. `inScope` says which constants of the environment are searched for goals. -/
def checkWith (proved : List (Name × Name)) (notDone required : List Name)
    (inScope : Environment → Name → Bool) : CommandElabM Unit := do
  let env ← getEnv
  let provedGoals := proved.map (·.1)
  let listed := provedGoals ++ notDone
  if listed.eraseDups.length != listed.length then throwError "a goal is listed twice"
  for g in listed do
    let some (.defnInfo d) := env.find? g | throwError m!"{g} is not a definition"
    unless isGoalType d.type && d.levelParams.isEmpty && g.components.contains `Goal do
      throwError m!"{g} is not a goal (a definition named …Goal.… of type Prop after its binders)"
  for (g, t) in proved do
    let some (.defnInfo d) := env.find? g | throwError m!"{g} is not a definition"
    let some (.thmInfo ti) := env.find? t | throwError m!"{t} is not a theorem"
    unless ti.levelParams.isEmpty && ti.type == expectedType g d.type do
      throwError m!"the type of {t} is not exactly {g}"
    let bad := (← collectAxioms t).filter (!allowedAxioms.contains ·)
    unless bad.isEmpty do throwError m!"{t} depends on {bad}"
  for g in required do
    unless provedGoals.contains g do throwError m!"required goal {g} is not proved"
  let mut defined := 0
  for (n, _) in env.constants.toList do
    unless n.components.contains `Goal && inScope env n do continue
    match goalHead n with
    | none => throwError m!"{n} is named like a goal but has no goal name after `Goal`"
    | some h =>
      unless isGoal env h do
        throwError m!"{n} is named like a goal, but {h} is not a definition of type Prop after its binders"
      if h == n then
        defined := defined + 1
        unless listed.contains n do throwError m!"goal {n} is neither proved nor listed as not done"
  logInfo m!"{defined} goals defined, {listed.length} listed: {provedGoals.length} proved, \
    {notDone.length} not done; {required.length} required"
  unless defined == listed.length do
    throwError m!"{defined} goals defined, {listed.length} listed"

/-- The constants of the library: those of a module whose name starts with `ZlibF`, and those of the
module being checked (`ZlibF/Results.lean` itself, whose constants have no module index yet). -/
def inLibrary (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i]!.getRoot == `ZlibF
  | none => true

end ZlibF.Results
