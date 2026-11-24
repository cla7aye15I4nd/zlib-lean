import Lean2C.OriginalLengthGuards
import ZlibF.Zlib.«compress.c»

/-! Scalar length accesses after the argument guard of LP64 `compress2_z`. -/
namespace Lean2C.OriginalCompressLengths
open C CSource Semantics ZlibF.Spec.Public
set_option autoImplicit false

private def capacity : Value := .load .u64 (.var (.ptr .u64) "destLen")
private def output : Value := .var (.ptr .u8) "dest"
private def cursor (stream : String) : Value :=
  .field (.ptr .u8) (.var (.named "z_stream") stream) "next_out"

def originalStart : List Stmt :=
  [.assign (.var .u64 "left") capacity, .assign capacity (.cast .u64 (.num .i32 0))]

def standaloneStart : List Stmt :=
  [.decl .u64 "left" (some capacity), .assign capacity (.num .u64 0)]

def originalWriteback : List Stmt :=
  [.assign capacity (.cast .u64 (.op .i64 "-" (cursor "stream") output))]

def standaloneWriteback : List Stmt :=
  [.decl (.ptr .u8) "no" none, .assign (.var (.ptr .u8) "no") (cursor "strm"),
   .decl .i64 "n" (some (.op .i64 "-" (.var (.ptr .u8) "no") output)),
   .assign capacity (.cast .u64 (.var .i64 "n"))]

def resultCode : List Stmt :=
  [.ret (.choose (.op .i32 "==" (.var .i32 "err") (.num .i32 1)) (.num .i32 0) (.var .i32 "err"))]

def initResult : List Stmt :=
  [.branch (.op .i32 "!=" (.var .i32 "err") (.num .i32 0)) [.ret (.var .i32 "err")] []]

private theorem lookup_other (env : CEnv) (n k : String) (v : CVal) (diff : n ≠ k) :
    (env.set k v).lookup n = env.lookup n := CEnv.lookup_set_ne env diff v

private theorem cast_ptr (p : BPtr) : evalCast (.ptr .u8) (.ptr p) = .ok (.ptr p) := rfl

private theorem castZero : evalCast .u64 (.i32 0) = .ok (.u64 0) := rfl

private theorem cast_signed (n : Int64) : evalCast .u64 (.i64 n) = .ok (.u64 n.toUInt64) := by
  change Except.ok (.u64 (UInt64.ofInt n.toInt)) = (.ok (.u64 n.toUInt64) : Except Fault CVal)
  congr 2
  apply UInt64.toNat_inj.mp
  change (n.toBitVec.toInt % (2 ^ 64 : Int)).toNat % 2 ^ 64 = n.toBitVec.toNat
  rw [BitVec.toInt_emod_two_pow, Int.toNat_natCast, Nat.mod_eq_of_lt n.toBitVec.isLt]

/-- Both accepted branches save the old capacity in `left` and clear exactly the
length cell. This write precedes initialization, including a failed initialization. -/
theorem read_clear (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (p : BPtr) (n : UInt64)
    (arg : env.lookup "destLen" = some (.ptr p)) (cell : LengthCell h p n)
    (aligned : ByteAddress.value h p % 8 = 0) :
    ∃ after, Store h p (lengthBytes 0) after ∧
      execStmts f g fuel env h originalStart = .next (env.set "left" (.u64 n)) after ∧
      execStmts f g fuel env h standaloneStart = .next (env.set "left" (.u64 n)) after := by
  have load := (LengthAccess.read_cell_iff cell).2 aligned
  obtain ⟨after, write, stored⟩ := (LengthAccess.write_cell_iff 0 cell.2).2 aligned
  refine ⟨after, stored, ?_, ?_⟩ <;>
    simp [originalStart, standaloneStart, capacity, execStmts, execStmt, evalValue, arg, load,
      lookup_other, evalNum, castZero, write, Bind.bind, Except.bind, Pure.pure, Except.pure]

def startResult (env : CEnv) (h : Heap) (p : BPtr) : Except Fault UInt64 → StmtOutcome
  | .error e => .fault e
  | .ok n =>
    match writeHeap .u64 p (.u64 0) h with
    | .error e => .fault e
    | .ok after => .next (env.set "left" (.u64 n)) after

/-- Evaluate both accepted length instructions before initialization, also
when access fails. The result includes the complete local environment. -/
theorem start_outcome (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap)
    (p : BPtr) (arg : env.lookup "destLen" = some (.ptr p))
    (read : Except Fault UInt64) (typed : readHeap .u64 p h = read.map CVal.u64) :
    execStmts f g fuel env h (if generated then standaloneStart else originalStart) =
      startResult env h p read := by
  cases read with
  | error fault =>
    cases generated <;> simp [originalStart, standaloneStart, capacity, execStmts, execStmt, evalValue,
      arg, typed, startResult, Except.map, Bind.bind, Except.bind]
  | ok n =>
    cases generated <;> cases w : writeHeap .u64 p (.u64 0) h <;>
      simp [originalStart, standaloneStart, capacity, execStmts, execStmt, evalValue, arg, typed,
        lookup_other, evalNum, castZero, w, startResult, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem byte_sub (h : Heap) (p q : BPtr) (e : Ty) :
    evalBinOp .i64 "-" (.ptr p) (.ptr q) h e =
      (elementDifference e p q h).map (fun pair => CVal.i64 pair.1) := by
  cases r : elementDifference e p q h with
  | error fault => simp [evalBinOp, evalPtrOp, r, Except.map, Bind.bind, Except.bind]
  | ok v => rcases v with ⟨k, h'⟩; simp [evalBinOp, evalPtrOp, r, Except.map, Bind.bind, Except.bind]; rfl

/-- The observed result keeps all memory changes and faults. Only the emitted
automatic scalar temporaries are outside the observation. -/
def writebackResult (ref : ZStreamRef) (p dest : BPtr) (h : Heap) : StmtOutcome :=
  match ldZStream (some ref) h with
  | .error fault => .fault fault
  | .ok (z, h1) =>
    match elementDifference .u8 z.next_out dest h1 with
    | .error fault => .fault fault
    | .ok (n, _) =>
      match writeHeap .u64 p (.u64 n.toUInt64) h1 with
      | .error fault => .fault fault
      | .ok after => .next [] after

set_option linter.unusedSimpArgs false in
/-- The two source blocks agree for all modeled heaps, including dangling
stream objects, invalid pointer differences, and invalid output stores. -/
theorem writeback (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (ref : ZStreamRef) (p dest : BPtr)
    (generated : Bool) (lenArg : env.lookup "destLen" = some (.ptr p)) (destArg : env.lookup "dest" = some (.ptr dest))
    (localStream : env.lookup (if generated then "strm" else "stream") = some (.streamLocal ref)) :
    OriginalLengthGuards.observe (execStmts f g fuel env h
      (if generated then standaloneWriteback else originalWriteback)) = writebackResult ref p dest h := by
  cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte] at localStream ⊢ <;> cases live : ldZStream (some ref) h with
  | error fault =>
    simp [*, originalWriteback, standaloneWriteback, capacity, output, cursor, writebackResult,
      OriginalLengthGuards.observe, execStmts, execStmt, evalValue, lookup_other, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  | ok pair =>
    obtain ⟨z, h1⟩ := pair
    cases delta : elementDifference .u8 z.next_out dest h1 with
    | error fault =>
      simp [*, originalWriteback, standaloneWriteback, capacity, output, cursor, writebackResult,
        OriginalLengthGuards.observe, execStmts, execStmt, evalValue, lookup_other, byte_sub, pointerElement,
        Value.type, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure, evalCast]
    | ok pair =>
      obtain ⟨n, h2⟩ := pair
      cases write : writeHeap .u64 p (.u64 n.toUInt64) h1 <;>
        simp [*, originalWriteback, standaloneWriteback, capacity, output, cursor, writebackResult,
          OriginalLengthGuards.observe, execStmts, execStmt, evalValue, lookup_other, byte_sub, pointerElement,
          Value.type, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure, cast_signed, cast_ptr]

/-- The operations of the emitted Lean entry between its loop and deflateEnd. -/
def abiWriteback (stream : ZStreamPtr) (p dest : BPtr) : M Unit := do
  let no ← Zlib.Deflate.zrd stream (·.next_out)
  let n ← Ptr.diff no dest
  store64 p n.toUInt64

/-- On two positions of the same live byte array (including one-past), both
source blocks and the ABI operations write precisely the converted distance. -/
theorem writeback_domain {h : Heap} {ref : ZStreamRef} {z : ZStream} {p : BPtr}
    {r : BRef} {i j : Nat} {bytes : Array UInt8}
    (stream : ref.get h = some z) (out : z.next_out = .ref r i)
    (buffer : Space.get h r = some bytes) (hi : i ≤ bytes.size) (hj : j ≤ bytes.size)
    (range : -(2 ^ 63 : Int) ≤ (i : Int) - (j : Int) ∧ (i : Int) - (j : Int) < 2 ^ 63)
    (region : Writable h p 8) (aligned : ByteAddress.value h p % 8 = 0) :
    ∃ after, writebackResult ref p (.ref r j) h = .next [] after ∧
      abiWriteback (some ref) p (.ref r j) h = .ok ((), after) ∧
      Store h p (lengthBytes (Int64.ofInt ((i : Int) - j)).toUInt64) after := by
  let n := Int64.ofInt ((i : Int) - j)
  have diff : elementDifference .u8 (.ref r i) (.ref r j) h = .ok (n, h) := by
    simp [elementDifference, elementBytes, buffer, Nat.not_lt.mpr hi, Nat.not_lt.mpr hj,
      inSignedRange, n, Pure.pure, Except.pure]
    exact range
  have raw := Ptr.diff_ok buffer hi hj range
  obtain ⟨after, wr, stored⟩ := ZlibF.Spec.Public.Proofs.Uncompress.store64_writable n.toUInt64 region
  have typed : writeHeap .u64 p (.u64 n.toUInt64) h = .ok after := by
    simp [writeHeap, aligned, wr, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨after, ?_, ?_, stored⟩
  · simp [writebackResult, ldZStream, stream, out, diff, typed]
  · simp only [abiWriteback, Zlib.Deflate.zrd, bind_app, ldZStream, stream, pure_app, out]
    rw [show Ptr.diff (Ptr.ref r i) (.ref r j) h = .ok (n, h) from raw]
    exact wr

/-- At the final subtraction the strict source evaluator faults for two null
operands. The ABI runtime's documented null-minus-null rule instead stores zero. -/
theorem writeback_null {h : Heap} {ref : ZStreamRef} {z : ZStream} (p : BPtr)
    (stream : ref.get h = some z) (out : z.next_out = .null) :
    writebackResult ref p .null h = .fault (.ub "subtraction of a null pointer") ∧
    abiWriteback (some ref) p .null h = store64 p 0 h := by
  constructor
  · simp [writebackResult, ldZStream, stream, out, elementDifference, elementBytes]
  · simp [abiWriteback, Zlib.Deflate.zrd, ldZStream, stream, out, Ptr.diff_null_null]
    rfl

theorem result_code (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32)
    (saved : env.lookup "err" = some (.i32 err)) :
    execStmts f g fuel env h resultCode = .ret (.i32 (if err == 1 then 0 else err)) h := by
  have cmp : evalBinOp .i32 "==" (.i32 err) (.i32 1) h .u8 = .ok (.bool (err == 1)) := rfl
  cases e : err == 1 <;>
    simp [resultCode, execStmts, execStmt, evalValue, saved, evalNum, pointerElement, Value.type,
      cmp, e, CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem init_result (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap) (err : Int32)
    (saved : env.lookup "err" = some (.i32 err)) :
    execStmts f g fuel env h initResult = (if err != 0 then .ret (.i32 err) h else .next env h) := by
  have cmp : evalBinOp .i32 "!=" (.i32 err) (.i32 0) h .u8 = .ok (.bool (err != 0)) := rfl
  cases e : err != 0 <;>
    simp [initResult, execStmts, execStmt, evalValue, saved, evalNum, pointerElement, Value.type,
      cmp, e, CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure]

end Lean2C.OriginalCompressLengths
