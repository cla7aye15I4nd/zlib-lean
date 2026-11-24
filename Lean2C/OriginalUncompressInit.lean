import Lean2C.OriginalUncompressLoop
import Lean2C.OriginalCompressInit

/-! Stream arguments, field writes and error return around inflateInit_. -/
namespace Lean2C.OriginalUncompressInit
open C CSource Semantics Zlib.Gzguts Zlib.Deflate
set_option autoImplicit false

private def buffer (generated input : Bool) : List Stmt :=
  let stream := Value.var (.named "z_stream") "stream"
  let ptr := Ty.ptr .u8
  let operand := if input then Value.cast ptr (.var ptr "source") else Value.var ptr "dest"
  let zero := if generated then Value.num .u32 0 else .cast .u32 (.num .i32 0)
  [.assign (.field ptr stream (if input then "next_in" else "next_out")) operand,
   .assign (.field .u32 stream (if input then "avail_in" else "avail_out")) zero]

def inputFields (generated : Bool) : List Stmt := buffer generated true ++ OriginalCompressInit.allocators false
def outputFields (generated : Bool) : List Stmt := buffer generated false

def initArgs (generated : Bool) : String × Value := (OriginalCompressInit.initArgs generated).2
def initCheck : List Stmt := OriginalCompressLengths.initResult

theorem args_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) :
    (initArgs generated).1 = ZLIB_VERSION ∧
    evalValue f g fuel env h (initArgs generated).2 = .ok (.i32 sizeof_z_stream, env, h) := by
  refine ⟨rfl, ?_⟩
  cases generated <;> simp only [initArgs, OriginalCompressInit.initArgs, Bool.false_eq_true, ↓reduceIte, evalValue] <;> rfl

private def fieldsOutcome (r : ZStreamRef) (h : Heap) (env : CEnv) (f : ZStream → ZStream) : StmtOutcome :=
  match r.get h with
  | none => .fault (.ub "access through a dangling pointer (z_stream)")
  | some z => .next env (r.put h (f z))

def setInput (p : BPtr) (z : ZStream) : ZStream :=
  {z with next_in := p, avail_in := 0, zalloc := .null, zfree := .null, «opaque» := .null}
def setOutput (p : BPtr) (z : ZStream) : ZStream := {z with next_out := p, avail_out := 0}

private theorem ptrCast (ty : Ty) (p : BPtr) : evalCast (.ptr ty) (.ptr p) = .ok (.ptr p) := rfl
private theorem ptrZero : evalCast (.ptr .void) (.i32 0) = .ok (.ptr .null) := rfl
private theorem zeroCast : evalCast .u32 (.i32 0) = .ok (.u32 0) := rfl
private theorem allocNull : evalCast (.named "alloc_func") (.i32 0) = .ok (.functionPtr .null) := rfl
private theorem freeNull : evalCast (.named "free_func") (.i32 0) = .ok (.functionPtr .null) := rfl
private theorem allocCast : evalCast (.named "alloc_func") (.functionPtr .null) = .ok (.functionPtr .null) := rfl
private theorem freeCast : evalCast (.named "free_func") (.functionPtr .null) = .ok (.functionPtr .null) := rfl

set_option linter.unusedSimpArgs false in
theorem fields_run (generated input : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap)
    (r : ZStreamRef) (p : BPtr) (stream : env.lookup "stream" = some (.streamLocal r))
    (arg : env.lookup (if input then "source" else "dest") = some (.ptr p)) :
    execStmts f g fuel env h (if input then inputFields generated else outputFields generated) =
      fieldsOutcome r h env (if input then setInput p else setOutput p) := by
  have writable : r.isRo = false := by cases r <;> rfl
  cases live : r.get h with
  | none =>
    cases input <;> cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte] at arg ⊢ <;>
      simp [inputFields, outputFields, buffer, fieldsOutcome, execStmts, execStmt, evalValue, stream, arg,
        ptrCast, writeStreamField, ldZStream, live, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some z =>
    have get (z') := Zlib.Deflate.Proofs.ZStreamRef.get_put_same live z'
    cases input <;> cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte] at arg ⊢
    all_goals
      simp [inputFields, outputFields, buffer, fieldsOutcome, setInput, setOutput,
        OriginalCompressInit.allocators, OriginalCompressInit.field, OriginalCompressInit.streamName, execStmts, execStmt, evalValue, stream, arg, writeStreamField,
        ptrCast, ptrZero, zeroCast, allocNull, freeNull, allocCast, freeCast, evalNum, ldZStream, stZStream, writeStreamCount,
        writable, live, get, Bind.bind, Except.bind, Pure.pure, Except.pure]

def sourceFields (generated input : Bool) (r : ZStreamRef) (p : BPtr) : M Unit := fun h =>
  let env : CEnv := [("stream", .streamLocal r), (if input then "source" else "dest", .ptr p)]
  match execStmts (fun _ => none) [] 0 env h (if input then inputFields generated else outputFields generated) with
  | .next _ after => .ok ((), after)
  | .fault e => .error e
  | _ => .error (.ub "unexpected return during stream initialization")

theorem sourceFields_eq (generated input : Bool) (r : ZStreamRef) (p : BPtr) :
    sourceFields generated input r p = updZ (some r) (if input then setInput p else setOutput p) := by
  funext h
  unfold sourceFields
  dsimp only
  rw [fields_run generated input _ _ _ _ _ _ p (CEnv.lookup_cons_same ..) (by cases input <;> rfl)]
  have writable : r.isRo = false := by cases r <;> rfl
  cases live : r.get h <;> simp [fieldsOutcome, updZ, ldZStream, stZStream, writable, live]

#print axioms sourceFields_eq
end Lean2C.OriginalUncompressInit
