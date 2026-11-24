import Lean2C.CompressWrapper

/-! The original and emitted buffer refills inside the do-while of compress2_z. -/
namespace Lean2C.OriginalCompressLoop
open C CSource Semantics Zlib.Deflate
set_option autoImplicit false

private def streamName (generated : Bool) := if generated then "strm" else "stream"
private def countName (input : Bool) := if input then "avail_in" else "avail_out"
private def lengthName (input : Bool) := if input then "sourceLen" else "left"
private def savedName (input : Bool) := if input then "v_2" else "v_1"
private def chunkName (input : Bool) := if input then "ai" else "ao"

private def chunkExpr (length : Value) : Value :=
  let max := Value.var .u32 "max"
  .choose (.op .i32 ">" length (.cast .u64 max)) max (.cast .u32 length)

/-- Both forms select the same chunk. The original reloads the stream field
after writing it. The emitted form converts the assigned local to size_t. -/
def refillCode (generated input : Bool) : List Stmt :=
  let length := Value.var .u64 (lengthName input)
  let field := Value.field .u32 (.var (.named "z_stream") (streamName generated)) (countName input)
  let update := fun (from_ : Value) => Stmt.assign length (.op .u64 "-" length (.cast .u64 from_))
  if generated then
    let saved := Value.var .u32 (savedName input)
    let chunk := Value.var .u32 (chunkName input)
    [.decl .u32 (savedName input) none, .assign saved field,
     .branch (.op .i32 "==" saved (.num .u32 0))
       [.decl .u32 (chunkName input) (some (chunkExpr length)), .assign field chunk, update chunk] []]
  else
    [.branch (.op .i32 "==" field (.cast .u32 (.num .i32 0)))
      [.assign field (chunkExpr length), update field] []]

private def copyLocal (ty : Ty) (toName fromName : String) : Stmt :=
  .assign (.var ty toName) (.var ty fromName)

def entryLocals (generated : Bool) : List Stmt :=
  if generated then [.decl .i32 "s" none, .decl .u64 "s_1" none, .decl .u64 "s_2" none,
    copyLocal .i32 "s" "err", copyLocal .u64 "s_1" "left", copyLocal .u64 "s_2" "sourceLen"] else []

def copyResult (generated : Bool) : List Stmt :=
  if generated then [copyLocal .i32 "err" "s"] else []

def restoreLocals (generated : Bool) : List Stmt :=
  if generated then [copyLocal .u64 "left" "s_1", copyLocal .u64 "sourceLen" "s_2"] else []

def saveLocals (generated : Bool) : List Stmt :=
  if generated then [copyLocal .i32 "s" "err_1", copyLocal .u64 "s_1" "left",
    copyLocal .u64 "s_2" "sourceLen"] else []

def flushArgument (generated : Bool) : Value :=
  let n := Value.var .u64 "sourceLen"
  .choose (if generated then .op .i32 "!=" n (.num .u64 0) else n) (.num .i32 0) (.num .i32 4)

def whileCondition (generated : Bool) : Value :=
  .op .i32 "==" (.var .i32 (if generated then "s" else "err")) (.num .i32 0)

private def count (input : Bool) (z : ZStream) := if input then z.avail_in else z.avail_out
private def changeCount (input : Bool) (z : ZStream) (n : UInt32) : ZStream :=
  if input then {z with avail_in := n} else {z with avail_out := n}

private theorem zero (x : UInt32) (h : Heap) : evalBinOp .i32 "==" (.u32 x) (.u32 0) h = .ok (.bool (x == 0)) := rfl
private theorem greater (x y : UInt64) (h : Heap) : evalBinOp .i32 ">" (.u64 x) (.u64 y) h = .ok (.bool (decide (x > y))) := rfl
private theorem subtract (x y : UInt64) (h : Heap) :
    evalBinOp .u64 "-" (.u64 x) (.u64 y) h = .ok (.u64 (x - y)) := by
  unfold evalBinOp
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem zeroCast : evalCast .u32 (.i32 0) = .ok (.u32 0) := rfl

/-- Exact environment and heap after a refill. The nonzero case just observes
the stream. Generated temporaries are retained here to compose later statements. -/
def refillResult (generated input : Bool) (env : CEnv) (h : Heap) (r : ZStreamRef)
    (z : ZStream) (n : UInt64) : StmtOutcome :=
  let env := if generated then ((env.set (savedName input) .void).set (savedName input) (.u32 (count input z))) else env
  if count input z == 0 then
    let chunk : UInt32 := if n > (0xffffffff : UInt32).toUInt64 then 0xffffffff else n.toUInt32
    let env := if generated then env.set (chunkName input) (.u32 chunk) else env
    .next (env.set (lengthName input) (.u64 (n - chunk.toUInt64))) (r.put h (changeCount input z chunk))
  else .next env h

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem refill_run (generated input : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (r : ZStreamRef) (z : ZStream) (n : UInt64)
    (stream : env.lookup (streamName generated) = some (.streamLocal r))
    (length : env.lookup (lengthName input) = some (.u64 n)) (max : env.lookup "max" = some (.u32 0xffffffff))
    (live : r.get h = some z) :
    execStmts f g fuel env h (refillCode generated input) = refillResult generated input env h r z n := by
  have writable : r.isRo = false := by cases r <;> rfl
  have get (v) := Zlib.Deflate.Proofs.ZStreamRef.get_put_same live v
  cases empty : count input z == 0 <;> by_cases large : (4294967295 : UInt64) < n <;>
    cases generated <;> cases input <;>
    simp only [streamName, lengthName, count, Bool.false_eq_true, ↓reduceIte] at stream length empty
  all_goals
      simp [refillCode, refillResult, chunkExpr, streamName, countName, lengthName, chunkName, savedName,
        count, changeCount, execStmts, execStmt, evalValue, readStreamCount, writeStreamCount, ldZStream,
        stZStream, stream, length, max, live, writable, get, empty, large, CEnv.lookup_set_ne,
        pointerElement, Value.type, evalNum, zeroCast, zero, greater, subtract, CVal.toBool?, Bind.bind,
        Except.bind, Pure.pure, Except.pure, C.bind_app, C.pure_app]

/-- Read the observable remaining length, preserving the fault and the whole heap. -/
private def remaining (name : String) : StmtOutcome → Except Fault (UInt64 × Heap)
  | .next env h =>
    match env.lookup name with
    | some (.u64 n) => .ok (n, h)
    | _ => .error (.ub "missing loop length")
  | .fault e => .error e
  | _ => .error (.ub "unexpected control transfer in refill")

set_option linter.unusedSimpArgs false in
/-- Projecting a Clang-imported refill gives the ABI loop operation, for
arbitrary heaps, and for both the input and output half of the iteration. -/
theorem refill_matches (generated input : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (r : ZStreamRef) (h : Heap) (n : UInt64)
    (stream : env.lookup (streamName generated) = some (.streamLocal r))
    (length : env.lookup (lengthName input) = some (.u64 n)) (max : env.lookup "max" = some (.u32 0xffffffff)) :
    remaining (lengthName input) (execStmts f g fuel env h (refillCode generated input)) =
      CompressWrapper.refill (some r) n (!generated) (count input) (changeCount input) h := by
  cases live : r.get h with
  | none =>
    cases generated <;> cases input <;> simp only [streamName, Bool.false_eq_true, ↓reduceIte] at stream
    all_goals
      simp [remaining, refillCode, streamName, lengthName, countName, savedName, chunkName, CompressWrapper.refill,
        execStmts, execStmt, evalValue, CEnv.lookup_set_ne, stream, readStreamCount, zrd, ldZStream, live,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some z =>
    rw [refill_run generated input f g env fuel h r z n stream length max live]
    have writable : r.isRo = false := by cases r <;> rfl
    have get (v) := Zlib.Deflate.Proofs.ZStreamRef.get_put_same live v
    by_cases empty : count input z = 0 <;> cases input <;> cases generated <;>
      simp only [count, lengthName, Bool.false_eq_true, ↓reduceIte] at length empty
    all_goals
      simp [remaining, refillResult, CompressWrapper.refill, count, changeCount, countName, lengthName,
        chunkName, savedName, CEnv.lookup_set_ne, length, zrd, zwr, ldZStream, stZStream, live, writable,
        get, empty, bne, Bool.not_eq_true']

theorem entry_locals_run (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32) (left n : UInt64)
    (init : env.lookup "err" = some (.i32 err)) (room : env.lookup "left" = some (.u64 left))
    (source : env.lookup "sourceLen" = some (.u64 n)) :
    execStmts f g fuel env h (entryLocals true) = .next
      ((((((env.set "s" .void).set "s_1" .void).set "s_2" .void).set "s" (.i32 err)).set "s_1" (.u64 left)).set "s_2" (.u64 n)) h := by
  simp [entryLocals, copyLocal, execStmts, execStmt, evalValue, CEnv.lookup_set_ne, init, room, source]

theorem copy_result_run (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32)
    (saved : env.lookup "s" = some (.i32 err)) :
    execStmts f g fuel env h (copyResult true) = .next (env.set "err" (.i32 err)) h := by
  simp [copyResult, copyLocal, execStmts, execStmt, evalValue, saved]

theorem restore_run (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (remaining room : UInt64)
    (left : env.lookup "s_1" = some (.u64 room)) (source : env.lookup "s_2" = some (.u64 remaining)) :
    execStmts f g fuel env h (restoreLocals true) =
      .next ((env.set "left" (.u64 room)).set "sourceLen" (.u64 remaining)) h := by
  simp [restoreLocals, copyLocal, execStmts, execStmt, evalValue, CEnv.lookup_set_ne, left, source]

theorem save_run (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32) (remaining room : UInt64)
    (ret : env.lookup "err_1" = some (.i32 err)) (left : env.lookup "left" = some (.u64 room))
    (source : env.lookup "sourceLen" = some (.u64 remaining)) :
    execStmts f g fuel env h (saveLocals true) =
      .next (((env.set "s" (.i32 err)).set "s_1" (.u64 room)).set "s_2" (.u64 remaining)) h := by
  simp [saveLocals, copyLocal, execStmts, execStmt, evalValue, CEnv.lookup_set_ne, ret, left, source]

set_option linter.unusedSimpArgs false in
theorem flush_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (n : UInt64)
    (length : env.lookup "sourceLen" = some (.u64 n)) :
    evalValue f g fuel env h (flushArgument generated) =
      .ok (.i32 (if n != 0 then Z_NO_FLUSH else Z_FINISH), env, h) := by
  have cmp : evalBinOp .i32 "!=" (.u64 n) (.u64 0) h .u8 = .ok (.bool (n != 0)) := rfl
  cases generated <;> cases e : n != 0 <;>
    simp [flushArgument, evalValue, length, cmp, pointerElement, Value.type, evalNum, CVal.toBool?,
      Z_NO_FLUSH, Z_FINISH, e, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem condition_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32)
    (saved : env.lookup (if generated then "s" else "err") = some (.i32 err)) :
    evalValue f g fuel env h (whileCondition generated) = .ok (.bool (err == Z_OK), env, h) := by
  have cmp : evalBinOp .i32 "==" (.i32 err) (.i32 0) h .u8 = .ok (.bool (err == 0)) := rfl
  simp [whileCondition, evalValue, saved, cmp, pointerElement, Value.type, evalNum, Z_OK,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private def sourceRefill (generated input : Bool) (r : ZStreamRef) (n : UInt64) : M UInt64 := fun h =>
  let env : CEnv := [(streamName generated, .streamLocal r), (lengthName input, .u64 n), ("max", .u32 0xffffffff)]
  remaining (lengthName input) (execStmts (fun _ => none) [] 0 env h (refillCode generated input))

private theorem sourceRefill_eq (generated input : Bool) (r : ZStreamRef) (n : UInt64) :
    sourceRefill generated input r n = CompressWrapper.refill (some r) n (!generated) (count input) (changeCount input) := by
  funext h
  apply refill_matches
  · apply CEnv.lookup_cons_same
  · cases generated <;> cases input <;> rfl
  · cases generated <;> cases input <;> rfl

private def sourceFlush (generated : Bool) (n : UInt64) : M Int32 := fun h => do
  let (.i32 flush, _, after) ← evalValue (fun _ => none) [] 0 [("sourceLen", .u64 n)] h (flushArgument generated)
    | .error (.ub "expected int flush")
  return (flush, after)

private theorem sourceFlush_eq (generated : Bool) (n : UInt64) :
    sourceFlush generated n = pure (if n != 0 then Z_NO_FLUSH else Z_FINISH) := by
  funext h
  unfold sourceFlush
  rw [flush_run generated _ _ _ _ _ _ (by rfl)]
  rfl

/-- One iteration using the checked C syntax for both refills and the call
argument. The returned registers are exactly those stored by `saveLocals`.
The call to deflate has the same heap and stream object as the ABI wrapper. -/
def sourceBody (generated : Bool) (r : ZStreamRef) (st : Int32 × UInt64 × UInt64) :
    M (Int32 × UInt64 × UInt64) := do
  let left ← sourceRefill generated false r st.2.1
  let n ← sourceRefill generated true r st.2.2
  let flush ← sourceFlush generated n
  let err ← deflate (some r) flush
  return (err, left, n)

def sourceCond (generated : Bool) (st : Int32 × UInt64 × UInt64) : M (Bool × (Int32 × UInt64 × UInt64)) :=
  fun h => do
    let (.bool again, _, after) ← evalValue (fun _ => none) [] 0
      [(if generated then "s" else "err", .i32 st.1)] h (whileCondition generated)
      | .error (.ub "expected loop test")
    return ((again, st), after)

private theorem sourceCond_eq (generated : Bool) (st : Int32 × UInt64 × UInt64) :
    sourceCond generated st = pure (st.1 == Z_OK, st) := by
  funext h
  unfold sourceCond
  rw [condition_run generated _ _ _ _ _ _ (CEnv.lookup_cons_same ..)]
  rfl

theorem body_eq (generated : Bool) (r : ZStreamRef) :
    sourceBody generated r = CompressWrapper.iteration (some r) false := by
  have native : sourceBody generated r = CompressWrapper.iteration (some r) (!generated) := by
    funext st
    simp only [sourceBody, sourceRefill_eq, sourceFlush_eq, CompressWrapper.iteration]
    rfl
  rw [native]
  cases generated
  · exact CompressWrapper.loop_body (some r)
  · rfl

/-- Equality of the entire compression loop when both sides call the modeled
deflate function. This includes every iteration, final registers, heap and faults. -/
theorem loop_eq (generated : Bool) (r : ZStreamRef) (st : Int32 × UInt64 × UInt64) :
    cdoWhile (sourceBody generated r) (sourceCond generated) st =
      cdoWhile (CompressWrapper.iteration (some r) false) (fun x => pure (x.1 == Z_OK, x)) st := by
  rw [body_eq, funext (sourceCond_eq generated)]

#print axioms loop_eq
#print axioms refill_run
#print axioms flush_run
#print axioms condition_run

end Lean2C.OriginalCompressLoop
