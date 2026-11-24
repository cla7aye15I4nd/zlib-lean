import Lean2C.LengthAccess

/-! Argument guards of the two LP64 utility functions. The importer checks
the control flow up to the first validated length read in the accepted
continuation. References to parameters, scalar temporaries, and their types
are checked against Clang in each translation unit. -/
namespace Lean2C.OriginalLengthGuards
open C CSource Semantics
set_option autoImplicit false

private def ptr (ty : Ty) (name : String) : Value := .var (.ptr ty) name
private def word (name : String) : Value := .load .u64 (ptr .u64 name)
private def isNull (ty : Ty) (name : String) : Value :=
  .op .i32 "==" (ptr ty name) (.cast (.ptr ty) (.num .i32 0))
private def missing (n : Value) (zero : Value) (p : String) : Value :=
  .op .i32 "&&" (.op .i32 ">" n zero) (isNull .u8 p)
private def disj (a b : Value) : Value := .op .i32 "||" a b
private def reject : Stmt :=
  .ret (.op .i32 "-" (.num .i32 0) (.num .i32 2))
private def originalZero : Value := .cast .u64 (.num .i32 0)

def originalCompress : List Stmt :=
  [.branch (disj (disj (missing (.var .u64 "sourceLen") originalZero "source") (isNull .u64 "destLen"))
    (missing (word "destLen") originalZero "dest")) [reject] []]

def originalUncompress : List Stmt :=
  [.branch (disj (disj (disj (isNull .u64 "sourceLen") (missing (word "sourceLen") originalZero "source"))
    (isNull .u64 "destLen")) (missing (word "destLen") originalZero "dest")) [reject] []]

private def mark : List Stmt := [.assign (.var .i32 "bad") (.num .i32 1)]
private def destCheck (tmp : String) : Stmt :=
  .branch (isNull .u64 "destLen") mark
    [.decl .u64 tmp (some (word "destLen")), .branch (missing (.var .u64 tmp) (.num .u64 0) "dest") mark []]
private def initBad : Stmt := .decl .i32 "bad" (some (.num .i32 0))
private def checkBad : Stmt := .branch (.var .i32 "bad") [reject] []

def standaloneCompress : List Stmt :=
  [initBad, .branch (missing (.var .u64 "sourceLen") (.num .u64 0) "source") mark [destCheck "v"], checkBad]

def standaloneUncompress : List Stmt :=
  [initBad, .branch (isNull .u64 "sourceLen") mark
    [.decl .u64 "v" (some (word "sourceLen")),
     .branch (missing (.var .u64 "v") (.num .u64 0) "source") mark [destCheck "v_1"]], checkBad]

/-- Only local scalar temporaries differ at the accepted continuation. Keep
the entire heap, the return value or fault, and any unexpected control exit. -/
def observe : StmtOutcome → StmtOutcome
  | .next _ h => .next [] h
  | other => other

private def readLength (h : Heap) (p : BPtr) : Except Fault UInt64 := do
  if ByteAddress.value h p % 8 != 0 then throw (.ub "misaligned unsigned long load")
  let (value, _) ← load64 p h
  return value

private theorem read_word (h : Heap) (p : BPtr) :
    readHeap .u64 p h = (readLength h p).map CVal.u64 := by
  unfold readHeap readLength
  by_cases aligned : ByteAddress.value h p % 8 = 0
  · cases load64 p h with
    | error e => simp [aligned, Bind.bind, Except.bind]; rfl
    | ok pair => obtain ⟨v, g⟩ := pair; simp [aligned, Bind.bind, Except.bind]; rfl
  · simp [aligned, Bind.bind, Except.bind]; rfl

private def stopped (h : Heap) : StmtOutcome := .ret (.i32 (-2)) h
private def continued (h : Heap) : StmtOutcome := .next [] h

private def checkDest (h : Heap) (dest destLen : BPtr) : StmtOutcome :=
  if destLen == .null then stopped h else
  match readLength h destLen with
  | .error e => .fault e
  | .ok n => if n > 0 && dest == .null then stopped h else continued h

def compressResult (h : Heap) (dest destLen source : BPtr) (n : UInt64) : StmtOutcome :=
  if n > 0 && source == .null then stopped h else checkDest h dest destLen

def uncompressResult (h : Heap) (dest destLen source sourceLen : BPtr) : StmtOutcome :=
  if sourceLen == .null then stopped h else
  match readLength h sourceLen with
  | .error e => .fault e
  | .ok n => if n > 0 && source == .null then stopped h else checkDest h dest destLen

def acceptedDest (h : Heap) (dest : BPtr) : Except Fault UInt64 → StmtOutcome
  | .error e => .fault e
  | .ok cap => if cap > 0 && dest == .null then .ret (.i32 (-2)) h else .next [] h

/-- Expose the exact typed read at the final compression guard, including its fault. -/
theorem compressResult_typed (h : Heap) (d dl s : BPtr) (n : UInt64)
    (read : Except Fault UInt64) (spec : readHeap .u64 dl h = read.map CVal.u64) :
    compressResult h d dl s n = (if n > 0 && s == .null then .ret (.i32 (-2)) h
      else if dl == .null then .ret (.i32 (-2)) h else acceptedDest h d read) := by
  have same : readLength h dl = read := by
    rw [read_word] at spec
    cases a : readLength h dl <;> cases b : read <;> simp_all [Except.map]
  simp only [compressResult, checkDest, same, stopped, continued]
  cases read <;> rfl

def acceptedInput (h : Heap) (d dl s : BPtr) : Except Fault UInt64 → StmtOutcome
  | .error e => .fault e
  | .ok n => compressResult h d dl s n

/-- The input length read can fault before the output length is examined. -/
theorem uncompressResult_typed (h : Heap) (d dl s sl : BPtr)
    (input : Except Fault UInt64) (spec : readHeap .u64 sl h = input.map CVal.u64) :
    uncompressResult h d dl s sl = (if sl == .null then .ret (.i32 (-2)) h else
      acceptedInput h d dl s input) := by
  have same : readLength h sl = input := by
    rw [read_word] at spec
    cases a : readLength h sl <;> cases b : input <;> simp_all [Except.map]
  cases input <;> simp [acceptedInput, uncompressResult, same, stopped, compressResult]

private theorem compareZero (n : UInt64) (h : Heap) (t : Ty) :
    evalBinOp .i32 ">" (.u64 n) (.u64 0) h t = .ok (.bool (0 < n)) := rfl

private theorem pointerNull (p : BPtr) (h : Heap) (t : Ty) :
    evalBinOp .i32 "==" (.ptr p) (.ptr .null) h t = .ok (.bool (p == .null)) := rfl

private theorem rcMinusTwo (h : Heap) (t : Ty) :
    evalBinOp .i32 "-" (.i32 0) (.i32 2) h t = .ok (.i32 (-2)) := rfl

private theorem nullCast (t : Ty) : evalCast (.ptr t) (.i32 0) = .ok (.ptr .null) := rfl
private theorem zeroCast : evalCast .u64 (.i32 0) = .ok (.u64 0) := rfl

local macro "guard_eval" : tactic => `(tactic|
  simp [*, originalCompress, originalUncompress, standaloneCompress, standaloneUncompress,
    disj, missing, isNull, word, ptr, originalZero, reject, initBad, checkBad, mark, destCheck,
    CEnv.lookup_set_ne, execStmts, execStmt, evalValue, CEnv.lookup, CEnv.set, evalNum, zeroCast, nullCast,
    compareZero, pointerNull, rcMinusTwo, CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure,
    read_word, Except.map, observe, compressResult, uncompressResult, stopped, continued, checkDest])

set_option linter.unusedSimpArgs false in
/-- In both compiled compression prefixes, every input heap yields the same
acceptance, stream error, or typed memory fault. Locals outside the guard
can have arbitrary values. -/
theorem compress_guard (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (d dl s : BPtr) (n : UInt64)
    (dest : env.lookup "dest" = some (.ptr d)) (capacity : env.lookup "destLen" = some (.ptr dl))
    (source : env.lookup "source" = some (.ptr s)) (length : env.lookup "sourceLen" = some (.u64 n)) :
    observe (execStmts f g fuel env h originalCompress) = compressResult h d dl s n ∧
    observe (execStmts f g fuel env h standaloneCompress) = compressResult h d dl s n := by
  constructor <;> cases n0 : decide (0 < n) <;> cases ns : s == .null <;> cases ndl : dl == .null
  all_goals first
    | solve | guard_eval
    | cases rd : readLength h dl with
      | error fault => guard_eval
      | ok v => cases v0 : decide (0 < v) <;> cases nd : d == .null <;> guard_eval

set_option linter.unusedSimpArgs false in
/-- The decoder checks its source-length pointer first. A rejection at that
step can bypass even a faulty destination-length read. -/
theorem uncompress_guard (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (d dl s sl : BPtr)
    (dest : env.lookup "dest" = some (.ptr d)) (capacity : env.lookup "destLen" = some (.ptr dl))
    (source : env.lookup "source" = some (.ptr s)) (length : env.lookup "sourceLen" = some (.ptr sl)) :
    observe (execStmts f g fuel env h originalUncompress) = uncompressResult h d dl s sl ∧
    observe (execStmts f g fuel env h standaloneUncompress) = uncompressResult h d dl s sl := by
  constructor <;> cases nsl : sl == .null
  all_goals first
    | solve | guard_eval
    | cases rs : readLength h sl with
      | error fault => guard_eval
      | ok n =>
        cases n0 : decide (0 < n) <;> cases ns : s == .null <;> cases ndl : dl == .null
        all_goals first
          | solve | guard_eval
          | cases rd : readLength h dl with
            | error fault => guard_eval
            | ok v => cases v0 : decide (0 < v) <;> cases nd : d == .null <;> guard_eval

private theorem read_valid {h : Heap} {p : BPtr} {n : UInt64}
    (cell : ZlibF.Spec.Public.LengthCell h p n) (aligned : ByteAddress.value h p % 8 = 0) :
    readLength h p = .ok n := by
  have value := (Lean2C.LengthAccess.read_cell_iff cell).2 aligned
  rw [read_word] at value
  cases result : readLength h p with
  | error fault => simp [result, Except.map] at value
  | ok v => simpa [result, Except.map] using value

/-- A non-null public length pointer supplies its little-endian scalar value
and the alignment required by these C lvalues. -/
def LengthArgument (h : Heap) (p : BPtr) (value : UInt64) : Prop :=
  p ≠ .null → ZlibF.Spec.Public.LengthCell h p value ∧ ByteAddress.value h p % 8 = 0

private theorem dest_valid (h : Heap) (d dl : BPtr) (capacity : UInt64)
    (valid : LengthArgument h dl capacity) :
    checkDest h d dl =
      (if dl == .null || (capacity > 0 && d == .null) then stopped h else continued h) := by
  by_cases absent : dl = .null
  · simp [checkDest, absent]
  · obtain ⟨cell, aligned⟩ := valid absent
    simp [checkDest, absent, read_valid cell aligned]

/-- On the aligned domain, the two compression guards reject precisely the
invalid buffer combinations or pass control with the entire original heap. -/
theorem compress_domain (h : Heap) (d dl s : BPtr) (n capacity : UInt64)
    (valid : LengthArgument h dl capacity) :
    compressResult h d dl s n = (if n > 0 && s == .null || dl == .null || (capacity > 0 && d == .null)
      then .ret (.i32 (-2)) h else .next [] h) := by
  unfold compressResult
  rw [dest_valid h d dl capacity valid]
  cases decide (n > 0) <;> cases s == .null <;> cases dl == .null <;> rfl

/-- A null source-length pointer returns the stream error immediately.
Otherwise both typed length reads have the values in the caller contract. -/
theorem uncompress_domain (h : Heap) (d dl s sl : BPtr) (n capacity : UInt64)
    (src : LengthArgument h sl n) (dst : LengthArgument h dl capacity) :
    uncompressResult h d dl s sl = (if sl == .null || (n > 0 && s == .null) ||
      dl == .null || (capacity > 0 && d == .null) then .ret (.i32 (-2)) h else .next [] h) := by
  by_cases absent : sl = .null
  · simp [uncompressResult, absent, stopped]
  · obtain ⟨cell, aligned⟩ := src absent
    simp only [uncompressResult, beq_false_of_ne absent, Bool.false_eq_true, ↓reduceIte, Bool.false_or,
      read_valid cell aligned, dest_valid h d dl capacity dst]
    cases decide (n > 0) <;> cases s == .null <;> cases dl == .null <;> rfl

#print axioms compress_guard
#print axioms uncompress_guard
#print axioms compress_domain
#print axioms uncompress_domain

end Lean2C.OriginalLengthGuards
