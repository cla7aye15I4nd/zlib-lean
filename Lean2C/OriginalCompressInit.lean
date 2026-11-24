import Lean2C.OriginalCompressLoop

/-! Stream initialization and call arguments of the two LP64 compression wrappers. -/
namespace Lean2C.OriginalCompressInit
open C CSource Semantics Zlib.Deflate
set_option autoImplicit false

def streamName (generated : Bool) := if generated then "strm" else "stream"
def field (generated : Bool) (ty : Ty) (member : String) : Value :=
  .field ty (.var (.named "z_stream") (streamName generated)) member

def allocators (generated : Bool) : List Stmt :=
  let clear (ty : Ty) (member : String) := Stmt.assign (field generated ty member) (.cast ty (.num .i32 0))
  [clear (.named "alloc_func") "zalloc", clear (.named "free_func") "zfree", clear (.ptr .void) "opaque"]

def buffers (generated : Bool) : List Stmt :=
  let ptr := Ty.ptr .u8
  let src := Value.var ptr "source"
  let zero := if generated then Value.num .u32 0 else .cast .u32 (.num .i32 0)
  [.assign (field generated ptr "next_out") (.var ptr "dest"), .assign (field generated .u32 "avail_out") zero,
   .assign (field generated ptr "next_in") (.cast ptr src),
   .assign (field generated .u32 "avail_in") zero]

/-- The imported level expression, literal content and size argument. The
importer asks the target compiler to check sizeof(z_stream) before translating
that sizeof expression. -/
def initArgs (generated : Bool) : Value × String × Value :=
  (.var .i32 "level", "1.4.0.1-motley",
    if generated then .num .i32 112 else .cast .i32 (.num .u64 112))

private theorem ptr_cast (ty : Ty) (p : BPtr) : evalCast (.ptr ty) (.ptr p) = .ok (.ptr p) := rfl
private theorem castZero : evalCast .u32 (.i32 0) = .ok (.u32 0) := rfl
private theorem ptrZero : evalCast (.ptr .void) (.i32 0) = .ok (.ptr .null) := rfl
private theorem allocatorNull : evalCast (.named "alloc_func") (.i32 0) = .ok (.functionPtr .null) := rfl
private theorem freeNull : evalCast (.named "free_func") (.i32 0) = .ok (.functionPtr .null) := rfl

private theorem allocatorCast (p : FnPtr) : evalCast (.named "alloc_func") (.functionPtr p) = .ok (.functionPtr p) := rfl
private theorem freeCast (p : FnPtr) : evalCast (.named "free_func") (.functionPtr p) = .ok (.functionPtr p) := rfl

set_option linter.unusedSimpArgs false in
theorem allocators_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap)
    (r : ZStreamRef) (z : ZStream) (obj : env.lookup (streamName generated) = some (.streamLocal r))
    (live : r.get h = some z) :
    execStmts f g fuel env h (allocators generated) =
      .next env (r.put h {z with zalloc := .null, zfree := .null, «opaque» := .null}) := by
  have writable : r.isRo = false := by cases r <;> rfl
  cases generated <;> simp only [streamName, Bool.false_eq_true, ↓reduceIte] at obj
  all_goals
    simp [allocators, field, streamName, execStmts, execStmt, evalValue, obj, live, writable, ldZStream,
      stZStream, writeStreamField, evalNum, allocatorNull, freeNull, ptrZero, ptr_cast, allocatorCast, freeCast,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option linter.unusedSimpArgs false in
theorem buffers_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap)
    (r : ZStreamRef) (z : ZStream) (dest source : BPtr) (obj : env.lookup (streamName generated) = some (.streamLocal r))
    (dst : env.lookup "dest" = some (.ptr dest)) (src : env.lookup "source" = some (.ptr source))
    (live : r.get h = some z) :
    execStmts f g fuel env h (buffers generated) =
      .next env (r.put h {z with next_out := dest, avail_out := 0, next_in := source, avail_in := 0}) := by
  have writable : r.isRo = false := by cases r <;> rfl
  cases generated <;> simp only [streamName, Bool.false_eq_true, ↓reduceIte] at obj
  all_goals
    simp [buffers, field, streamName, execStmts, execStmt, evalValue, obj, dst, src, live, writable, ldZStream,
      stZStream, writeStreamField, writeStreamCount, evalNum, castZero, ptr_cast, Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option linter.unusedSimpArgs false in
theorem fields_dangling (generated alloc : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (r : ZStreamRef) (dest : BPtr) (obj : env.lookup (streamName generated) = some (.streamLocal r))
    (dst : env.lookup "dest" = some (.ptr dest)) (gone : r.get h = none) :
    execStmts f g fuel env h (if alloc then allocators generated else buffers generated) =
      .fault (.ub "access through a dangling pointer (z_stream)") := by
  cases generated <;> cases alloc <;> simp only [streamName, Bool.false_eq_true, ↓reduceIte] at obj ⊢
  all_goals
    simp [allocators, buffers, field, streamName, execStmts, execStmt, evalValue, obj, dst, gone,
      ldZStream, writeStreamField, allocatorNull, allocatorCast, ptr_cast, evalNum,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem init_args_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (level : Int32)
    (lv : env.lookup "level" = some (.i32 level)) :
    evalValue f g fuel env h (initArgs generated).1 = .ok (.i32 level, env, h) ∧
    (initArgs generated).2.1 = ZLIB_VERSION ∧
    evalValue f g fuel env h (initArgs generated).2.2 = .ok (.i32 sizeof_z_stream, env, h) := by
  refine ⟨?_, rfl, ?_⟩
  · simp [initArgs, evalValue, lv]
  · cases generated <;> simp only [initArgs, Bool.false_eq_true, ↓reduceIte, evalValue] <;> rfl

end Lean2C.OriginalCompressInit
