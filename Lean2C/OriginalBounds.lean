import Lean2C.Soundness

/-! Source-level certificates for the two LP64 length bounds in compress.c.
`tools/source_bounds.py` checks the typed functions below against Clang on both C inputs. -/
namespace Lean2C.OriginalBounds
open CSource Semantics Soundness

private def boundSum (countTy : Ty) (extra : Value) : Value :=
  let n := Value.var .u64 "sourceLen"
  let shift := fun k => Value.op .u64 ">>" n (.num countTy k)
  .op .u64 "+" (.op .u64 "+" (.op .u64 "+" (.op .u64 "+" n (shift 12)) (shift 14)) (shift 25)) extra

/-- The two source casts spell the all-ones value as `(z_size_t)-1` or `(uLong)-1`. -/
private def minusOneCast : Value := .cast .u64 (.op .i32 "-" (.num .i32 0) (.num .i32 1))

def original_compressBound_z : List (String × Ty) × List Stmt :=
  ([("sourceLen", .u64)],
   [.decl .u64 "bound" (some (boundSum .i32 (.cast .u64 (.num .i32 13)))),
    .ret (.choose (.op .i32 "<" (.var .u64 "bound") (.var .u64 "sourceLen"))
      minusOneCast (.var .u64 "bound"))])

def original_compressBound : List (String × Ty) × List Stmt :=
  ([("sourceLen", .u64)],
   [.decl .u64 "bound" (some (.call .u64 "compressBound_z" [.var .u64 "sourceLen"])),
    .ret (.choose (.op .i32 "!=" (.var .u64 "bound") (.var .u64 "bound"))
      minusOneCast (.var .u64 "bound"))])

def standalone_compressBound_z : List (String × Ty) × List Stmt :=
  ([("sourceLen", .u64)],
   [.decl .u64 "bound" (some (boundSum .u64 (.num .u64 13))),
    .branch (.op .i32 "<" (.var .u64 "bound") (.var .u64 "sourceLen"))
      [.ret (.num .u64 18446744073709551615)] [.ret (.var .u64 "bound")]])

theorem source_bound_z (f : FnTable) (g : CEnv) (fuel : Nat) (x : UInt64) (h : C.Heap) :
    runCFn f g fuel original_compressBound_z [.u64 x] h = .ret (.u64 (Zlib.Compress.compressBound_z x)) h := by
  let e : CEnv := [("sourceLen", .u64 x)]
  let b := x + (x >>> 12) + (x >>> 14) + (x >>> 25) + 13
  have literal13 : evalCast .u64 (.i32 13) = .ok (.u64 13) := rfl
  have minusOne (env : CEnv) : evalValue f g fuel env h minusOneCast =
      .ok (.u64 18446744073709551615, env, h) := by
    simp only [minusOneCast, evalValue]
    rfl
  have val : evalValue f g fuel e h (boundSum .i32 (.cast .u64 (.num .i32 13))) = .ok (.u64 b, e, h) := by
    simp [boundSum, evalValue, e, CEnv.lookup, evalNum, evalBinOp, evalShiftOp, bitWidth?, CVal.toInt?, literal13,
      Bind.bind, Except.bind, Pure.pure, Except.pure, b]
  have entry : bindParams [("sourceLen", Ty.u64)] [.u64 x] = .ok e := by
    simp [bindParams, e, Bind.bind, Except.bind, Pure.pure, Except.pure]
  unfold runCFn
  rw [show bindParams original_compressBound_z.1 [.u64 x] = .ok e from entry]
  dsimp only [original_compressBound_z]
  rw [execStmts, execStmt, val]
  have castSelf : evalCast .u64 (.u64 b) = .ok (.u64 b) := by simp
  simp only [castSelf]
  change _ = StmtOutcome.ret (.u64 (if b < x then 0xffffffffffffffff else b)) h
  by_cases less : b < x <;>
    simp [execStmts, execStmt, evalValue, evalBinOp, evalRelOp, e, CEnv.set, CEnv.lookup, CVal.toInt?,
      minusOne, CVal.toBool?, less, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem linkedCall (f : FnTable) (g : CEnv) (n : Nat) (x : UInt64) (h : C.Heap)
    (body : List Stmt)
    (linked : f "compressBound_z" = some ([("sourceLen", .u64)], body))
    (sound : runCFn f g n ([("sourceLen", .u64)], body) [.u64 x] h =
      .ret (.u64 (Zlib.Compress.compressBound_z x)) h) :
    evalValue f g (n + 1) [("sourceLen", .u64 x)] h (.call .u64 "compressBound_z" [.var .u64 "sourceLen"]) =
      .ok (.u64 (Zlib.Compress.compressBound_z x), [("sourceLen", .u64 x)], h) := by
  let e : CEnv := [("sourceLen", .u64 x)]
  have castSelf (v : UInt64) : evalCast .u64 (.u64 v) = .ok (.u64 v) := by simp
  unfold runCFn at sound
  simp only [bindParams, castSelf, Bind.bind, Except.bind, Pure.pure, Except.pure] at sound
  have hargs : evalArgs f g (n + 1) e h [.var .u64 "sourceLen"] = .ok ([.u64 x], e, h) := by
    simp [evalArgs, evalValue, e, CEnv.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure]
  change evalValue f g (n + 1) e h _ = _
  rw [evalValue, hargs]
  simp only [linked, List.length_cons, List.length_nil, ne_eq,
      not_true_eq_false, ite_false, bindParams, castSelf, Bind.bind, Except.bind, Pure.pure, Except.pure, sound]
  rfl

theorem source_bound (f : FnTable) (g : CEnv) (fuel : Nat)
    (linked : f "compressBound_z" = some original_compressBound_z)
    (budget : 1 ≤ fuel) (x : UInt64) (h : C.Heap) :
    runCFn f g fuel original_compressBound [.u64 x] h = .ret (.u64 (Zlib.Compress.compressBound x)) h := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  have castSelf (v : UInt64) : evalCast .u64 (.u64 v) = .ok (.u64 v) := by simp
  have call := linkedCall f g n x h original_compressBound_z.2 linked (source_bound_z f g n x h)
  unfold runCFn original_compressBound minusOneCast Zlib.Compress.compressBound
  simp only [bindParams, castSelf, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [execStmts, execStmt, show evalValue f g (n + 1) [("sourceLen", .u64 x)] h _ = _ from call]
  simp [execStmts, execStmt, evalValue, CEnv.set, CEnv.lookup, evalBinOp, evalRelOp, CVal.toInt?,
    CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The standalone emitter uses unsigned-long shift counts. Clang represents the comparison
    result as int. Both details are retained in the imported C tree. -/
theorem standalone_bound_z (f : FnTable) (g : CEnv) (fuel : Nat) (x : UInt64) (h : C.Heap) :
    runCFn f g fuel standalone_compressBound_z [.u64 x] h = .ret (.u64 (Zlib.Compress.compressBound_z x)) h := by
  let e : CEnv := [("sourceLen", .u64 x)]
  let b := x + (x >>> 12) + (x >>> 14) + (x >>> 25) + 13
  have val : evalValue f g fuel e h (boundSum .u64 (.num .u64 13)) = .ok (.u64 b, e, h) := by
    simp [boundSum, evalValue, e, CEnv.lookup, evalNum, evalBinOp, evalShiftOp, bitWidth?, CVal.toInt?,
      Bind.bind, Except.bind, Pure.pure, Except.pure, b]
  have entry : bindParams [("sourceLen", Ty.u64)] [.u64 x] = .ok e := by
    simp [bindParams, e, Bind.bind, Except.bind, Pure.pure, Except.pure]
  unfold runCFn
  rw [show bindParams standalone_compressBound_z.1 [.u64 x] = .ok e from entry]
  dsimp only [standalone_compressBound_z]
  rw [execStmts, execStmt, val]
  have castSelf : evalCast .u64 (.u64 b) = .ok (.u64 b) := by simp
  simp only [castSelf]
  change _ = StmtOutcome.ret (.u64 (if b < x then 0xffffffffffffffff else b)) h
  by_cases less : b < x <;>
    simp [execStmts, execStmt, evalValue, evalNum, evalBinOp, evalRelOp, e, CEnv.set, CEnv.lookup, CVal.toInt?,
      CVal.toBool?, less, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem standalone_bound (f : FnTable) (g : CEnv) (fuel : Nat)
    (linked : f "compressBound_z" = some standalone_compressBound_z)
    (budget : 1 ≤ fuel) (x : UInt64) (h : C.Heap) :
    runCFn f g fuel compressBound_c [.u64 x] h = .ret (.u64 (Zlib.Compress.compressBound x)) h := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  have call := linkedCall f g n x h standalone_compressBound_z.2 linked (standalone_bound_z f g n x h)
  unfold runCFn compressBound_c Zlib.Compress.compressBound
  have castSelf : evalCast .u64 (.u64 x) = .ok (.u64 x) := by simp
  simp only [bindParams, castSelf, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [execStmts, execStmt, call]

/-- The two C inputs agree on the full outcome, including the heap, for every LP64 length. -/
theorem same_bound_z (reference generated : FnTable) (g : CEnv) (fuel : Nat) (x : UInt64) (h : C.Heap) :
    runCFn reference g fuel original_compressBound_z [.u64 x] h =
      runCFn generated g fuel standalone_compressBound_z [.u64 x] h := by
  rw [source_bound_z, standalone_bound_z]

/-- Each wrapper calls the definition from its own translation unit. -/
theorem same_bound (reference generated : FnTable) (g : CEnv) (fuel : Nat)
    (refLink : reference "compressBound_z" = some original_compressBound_z)
    (genLink : generated "compressBound_z" = some standalone_compressBound_z)
    (budget : 1 ≤ fuel) (x : UInt64) (h : C.Heap) :
    runCFn reference g fuel original_compressBound [.u64 x] h =
      runCFn generated g fuel compressBound_c [.u64 x] h := by
  rw [source_bound _ _ _ refLink budget, standalone_bound _ _ _ genLink budget]

#print axioms same_bound_z
#print axioms same_bound
end Lean2C.OriginalBounds
