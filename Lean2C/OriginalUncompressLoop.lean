import Lean2C.OriginalUncompressLengths

/-! Stream refills and the fixed flush argument in both LP64 uncompress2_z loops. -/
namespace Lean2C.OriginalUncompressLoop
open C CSource Semantics Zlib.Uncompr Zlib.Gzguts Zlib.Inflate Zlib.Deflate
set_option autoImplicit false

private def lengthName (generated input : Bool) :=
  if generated then (if input then "len_1" else "left_1") else if input then "len" else "left"
private def fieldName (input : Bool) := if input then "avail_in" else "avail_out"
private def fieldCount (input : Bool) (z : ZStream) := if input then z.avail_in else z.avail_out
private def setCount (input : Bool) (z : ZStream) (n : UInt32) :=
  if input then {z with avail_in := n} else {z with avail_out := n}

def refillCode (generated input : Bool) : List Stmt :=
  let length := Value.var .u64 (lengthName generated input)
  let field := Value.field .u32 (.var (.named "z_stream") "stream") (fieldName input)
  let max := Value.var .u32 "max"
  let amount := Value.choose (.op .i32 ">" length (.cast .u64 max)) max (.cast .u32 length)
  let zero := if generated then Value.num .u32 0 else .cast .u32 (.num .i32 0)
  let less := fun v => Value.op .u64 "-" length (.cast .u64 v)
  let statements := if generated then
    let a := if input then "a_1" else "a"
    let saved := if input then "len_2" else "left_2"
    [.decl .u32 a (some amount), .assign field (.var .u32 a), .decl .u64 saved (some (less (.var .u32 a))),
     .assign length (.var .u64 saved)]
  else [.assign field amount, .assign length (less field)]
  [.branch (.op .i32 "==" field zero) statements []]

def flush : Value := .num .i32 0

def loopTest (generated : Bool) : Value :=
  .op .i32 "==" (.var .i32 (if generated then "err_1" else "err")) (.num .i32 0)

def entryLocals (generated : Bool) : List Stmt :=
  if generated then [.decl .i32 "err_1" none, .decl .u64 "len_1" none, .decl .u64 "left_1" none,
    .assign (.var .i32 "err_1") (.var .i32 "err"), .assign (.var .u64 "len_1") (.var .u64 "len"),
    .assign (.var .u64 "left_1") (.var .u64 "left")] else []

def saveResult (generated : Bool) : List Stmt :=
  if generated then [.assign (.var .i32 "err_1") (.var .i32 "err_2")] else []

theorem entry_run (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32) (n cap : UInt64)
    (e : env.lookup "err" = some (.i32 err)) (l : env.lookup "len" = some (.u64 n))
    (c : env.lookup "left" = some (.u64 cap)) :
    execStmts f g fuel env h (entryLocals true) =
      .next ((((((env.set "err_1" .void).set "len_1" .void).set "left_1" .void).set "err_1" (.i32 err)).set
        "len_1" (.u64 n)).set "left_1" (.u64 cap)) h := by
  simp [entryLocals, execStmts, execStmt, evalValue, e, l, c, CEnv.lookup_set_ne]

theorem save_run (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32)
    (e : env.lookup "err_2" = some (.i32 err)) :
    execStmts f g fuel env h (saveResult true) = .next (env.set "err_1" (.i32 err)) h := by
  simp [saveResult, execStmts, execStmt, evalValue, e]

private def projectLength (name : String) : StmtOutcome → Except Fault (UInt64 × Heap)
  | .next env h => match env.lookup name with
    | some (.u64 n) => .ok (n, h) | _ => .error (.ub "missing uncompress length")
  | .fault e => .error e
  | _ => .error (.ub "unexpected uncompress control flow")

private theorem eqZero (n : UInt32) (h : Heap) (el : Ty) :
    evalBinOp .i32 "==" (.u32 n) (.u32 0) h el = .ok (.bool (n == 0)) := rfl
private theorem larger (x y : UInt64) (h : Heap) (el : Ty) :
    evalBinOp .i32 ">" (.u64 x) (.u64 y) h el = .ok (.bool (decide (x > y))) := rfl
private theorem sub64 (x y : UInt64) (h : Heap) (el : Ty) :
    evalBinOp .u64 "-" (.u64 x) (.u64 y) h el = .ok (.u64 (x-y)) := by
  unfold evalBinOp
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
private theorem zeroCast : evalCast .u32 (.i32 0) = .ok (.u32 0) := rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1500000 in
theorem refill_run (generated input : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap)
    (r : ZStreamRef) (n : UInt64) (obj : env.lookup "stream" = some (.streamLocal r))
    (localN : env.lookup (lengthName generated input) = some (.u64 n)) (max : env.lookup "max" = some (.u32 0xffffffff)) :
    projectLength (lengthName generated input) (execStmts f g fuel env h (refillCode generated input)) =
      CompressWrapper.refill (some r) n false (fieldCount input) (setCount input) h := by
  cases live : r.get h with
  | none =>
    cases generated <;> cases input <;>
      simp [refillCode, execStmts, execStmt, evalValue, fieldName, obj, readStreamCount, ldZStream, live,
        projectLength, CompressWrapper.refill, zrd, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some z =>
    have writable : r.isRo = false := by cases r <;> rfl
    have get (v) := Zlib.Deflate.Proofs.ZStreamRef.get_put_same live v
    by_cases empty : fieldCount input z = 0 <;> by_cases big : (4294967295 : UInt64) < n <;>
      cases generated <;> cases input <;> simp only [lengthName, fieldCount, Bool.false_eq_true, ↓reduceIte] at localN empty
    all_goals
      simp [projectLength, lengthName, refillCode, execStmts, execStmt, evalValue, fieldName, obj, localN, max,
        readStreamCount, writeStreamCount, CompressWrapper.refill, fieldCount, setCount, zrd, zwr, ldZStream,
        stZStream, writable, get, live, empty, big, eqZero, larger, sub64, zeroCast, evalNum, CEnv.lookup_set_ne,
        CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure] <;>
        simp [beq_false_of_ne empty, localN]

private def sourceRefill (generated input : Bool) (r : ZStreamRef) (n : UInt64) : M UInt64 := fun h =>
  let len := lengthName generated input
  let env : CEnv := [("stream", .streamLocal r), (len, .u64 n), ("max", .u32 0xffffffff)]
  projectLength len (execStmts (fun _ => none) [] 0 env h (refillCode generated input))

private theorem sourceRefill_eq (generated input : Bool) (r : ZStreamRef) (n : UInt64) :
    sourceRefill generated input r n = CompressWrapper.refill (some r) n false (fieldCount input) (setCount input) := by
  funext h
  apply refill_run
  · apply CEnv.lookup_cons_same
  · cases generated <;> cases input <;> rfl
  · cases generated <;> cases input <;> rfl

private def sourceFlush : M Int32 := fun h => do
  let (.i32 how, _, after) ← evalValue (fun _ => none) [] 0 [] h flush
    | .error (.ub "expected an integer flush argument")
  return (how, after)

private theorem sourceFlush_eq : sourceFlush = pure Z_NO_FLUSH := by
  funext h
  simp [sourceFlush, flush, evalValue, evalNum, Z_NO_FLUSH, Bind.bind, Except.bind, Pure.pure, Except.pure]

def sourceBody (generated : Bool) (r : ZStreamRef) (st : UncLoop) : M UncLoop := do
  let left ← sourceRefill generated false r st.left
  let n ← sourceRefill generated true r st.len
  let how ← sourceFlush
  let code ← inflate (some r) how
  return { err := code, len := n, left }

def abiBody (stream : ZStreamPtr) (st : UncLoop) : M UncLoop := do
  let mut l := st
  if (← ldZ stream).avail_out == 0 then
    let a : UInt32 := if l.left > (0xffffffff : UInt32).toUInt64 then 0xffffffff else l.left.toUInt32
    updZ stream fun z => { z with avail_out := a }
    l := { l with left := l.left - a.toUInt64 }
  if (← ldZ stream).avail_in == 0 then
    let a : UInt32 := if l.len > (0xffffffff : UInt32).toUInt64 then 0xffffffff else l.len.toUInt32
    updZ stream fun z => { z with avail_in := a }
    l := { l with len := l.len - a.toUInt64 }
  let err ← inflate stream Z_NO_FLUSH
  return { l with err }

def sourceCond (generated : Bool) (st : UncLoop) : M (Bool × UncLoop) := fun h => do
  let (.bool again, _, after) ← evalValue (fun _ => none) [] 0
    [(if generated then "err_1" else "err", .i32 st.err)] h (loopTest generated)
    | .error (.ub "expected integer loop condition")
  return ((again, st), after)

theorem condition_run (generated : Bool) (st : UncLoop) :
    sourceCond generated st = pure (st.err == Z_OK, st) := by
  funext h
  have eq : evalBinOp .i32 "==" (.i32 st.err) (.i32 0) h .u8 = .ok (.bool (st.err == 0)) := rfl
  simp [sourceCond, loopTest, evalValue, evalNum, eq, pointerElement, Value.type, Z_OK,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem body_eq (generated : Bool) (r : ZStreamRef) : sourceBody generated r = abiBody (some r) := by
  funext st h
  simp only [sourceBody, sourceRefill_eq, sourceFlush_eq, M_pure_bind]
  cases live : r.get h with
  | none => simp [abiBody, CompressWrapper.refill, fieldCount, zrd, ldZ, ldZStream, live]
  | some z =>
    have writable : r.isRo = false := by cases r <;> rfl
    by_cases ho : z.avail_out = 0 <;> by_cases hi : z.avail_in = 0 <;>
      simp [abiBody, CompressWrapper.refill, fieldCount, setCount, ldZ, updZ, zrd, zwr, ldZStream, stZStream,
        live, writable, ho, hi]

theorem loop_eq (generated : Bool) (r : ZStreamRef) (st : UncLoop) :
    cdoWhile (sourceBody generated r) (sourceCond generated) st =
      cdoWhile (abiBody (some r)) (fun l => pure (l.err == Z_OK, l)) st := by
  rw [body_eq, funext (condition_run generated)]

#print axioms loop_eq
end Lean2C.OriginalUncompressLoop
