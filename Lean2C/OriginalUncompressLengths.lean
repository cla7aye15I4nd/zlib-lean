import Lean2C.CompressWrapper
import ZlibF.Zlib.«uncompr.c»
import ZlibF.Proof.LibcScalar

/-! Typed length accesses in the pinned LP64 uncompress2_z source and emitted wrapper. -/
namespace Lean2C.OriginalUncompressLengths
open C CSource Semantics Std.WP Lean.Order
open scoped C.HeapWP
set_option autoImplicit false

private def cell (name : String) : Value := .load .u64 (.var (.ptr .u64) name)

def readLengths (generated : Bool) : List Stmt :=
  let read := fun name p => if generated then Stmt.decl .u64 name (some (cell p))
    else Stmt.assign (.var .u64 name) (cell p)
  [read "len" "sourceLen", read "left" "destLen"]

def unusedCounts (generated : Bool) : List Stmt :=
  let accumulate := fun name saved field =>
    let count := Value.field .u32 (.var (.named "z_stream") "stream") field
    Stmt.assign (.var .u64 name) (.op .u64 "+" (.var .u64 (if generated then saved else name)) (.cast .u64 count))
  [accumulate "len" "len_1" "avail_in", accumulate "left" "left_1" "avail_out"]

private def updateCell (generated : Bool) (p n temp : String) : List Stmt :=
  let old := if generated then Value.var .u64 temp else cell p
  let store := Stmt.assign (cell p) (.op .u64 "-" old (.var .u64 n))
  if generated then [.decl .u64 temp (some (cell p)), store] else [store]

def writeLengths (generated : Bool) : List Stmt :=
  updateCell generated "sourceLen" "len" "v_2" ++ updateCell generated "destLen" "left" "v_3"

private def zeroSize (generated : Bool) : Value :=
  if generated then .num .u64 0 else .cast .u64 (.num .i32 0)

def selectDest (generated : Bool) : List Stmt :=
  let dest := Value.var (.ptr .u8) "dest"
  let zero := Value.op .i32 "==" (.var .u64 "left") (zeroSize generated)
  let null := Value.op .i32 "==" dest (.cast (.ptr .u8) (.num .i32 0))
  let cond := Value.op .i32 "&&" zero null
  let addr := Value.cast (.ptr .u8) (.addr (.field .u64 (.var (.named "z_stream") "stream") "reserved"))
  if generated then [.assign dest (.choose cond addr dest)] else [.branch cond [.assign dest addr] []]

def returnResult (generated : Bool) : List Stmt :=
  let err := Value.var .i32 "err"
  let negative := fun n => Value.op .i32 "-" (.num .i32 0) (.num .i32 n)
  let code := fun v => Value.op .i32 "==" err v
  let empty := Value.op .i32 "==" (.var .u64 "len") (zeroSize generated)
  let needInput := Value.op .i32 "&&" (code (negative 5)) empty
  let dataError := negative 3
  let result := Value.choose (code (.num .i32 1)) (.num .i32 0)
    (.choose (code (.num .i32 2)) dataError (.choose needInput dataError err))
  if generated then [.assign err (.var .i32 "err_1"), .decl .i32 "r" (some result), .ret (.var .i32 "r")]
  else [.ret result]

private theorem sizeEq (x y : UInt64) (h : Heap) (el : Ty) :
    evalBinOp .i32 "==" (.u64 x) (.u64 y) h el = .ok (.bool (x == y)) := rfl

private theorem intEq (x y : Int32) (h : Heap) (el : Ty) :
    evalBinOp .i32 "==" (.i32 x) (.i32 y) h el = .ok (.bool (x == y)) := rfl

private theorem nullEq (x : BPtr) (h : Heap) (el : Ty) :
    evalBinOp .i32 "==" (.ptr x) (.ptr .null) h el = .ok (.bool (x == .null)) := rfl

private theorem negThree (h : Heap) (el : Ty) :
    evalBinOp .i32 "-" (.i32 0) (.i32 3) h el = .ok (.i32 (-3)) := by rfl

private theorem negFive (h : Heap) (el : Ty) :
    evalBinOp .i32 "-" (.i32 0) (.i32 5) h el = .ok (.i32 (-5)) := by rfl

private theorem ptrZero : evalCast (.ptr .u8) (.i32 0) = .ok (.ptr .null) := rfl
private theorem ptrCast (p : BPtr) : evalCast (.ptr .u8) (.ptr p) = .ok (.ptr p) := rfl
private theorem castZero : evalCast .u64 (.i32 0) = .ok (.u64 0) := rfl

set_option linter.unusedSimpArgs false in
/-- The reserved member address is consulted only for zero output capacity
and a null destination. The address is supplied by the representation of the
stack object; this theorem does not identify it with any separate allocation. -/
theorem select_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (r : ZStreamRef) (dest : BPtr) (cap : UInt64) (addr : Option BPtr)
    (st : env.lookup "stream" = some (match addr with
      | none => .streamLocal r | some p => .streamWithReserved r p))
    (out : env.lookup "dest" = some (.ptr dest)) (left : env.lookup "left" = some (.u64 cap)) :
    execStmts f g fuel env h (selectDest generated) =
      (if cap == 0 && dest == .null then
        match addr with
        | some p => .next (env.set "dest" (.ptr p)) h
        | none => .fault (.ub "missing address for z_stream.reserved")
      else .next (if generated then env.set "dest" (.ptr dest) else env) h) := by
  cases generated <;> cases addr <;> cases a : cap == 0 <;> cases b : dest == .null <;>
    simp [selectDest, zeroSize, execStmts, execStmt, evalValue, st, out, left, sizeEq, nullEq,
      ptrZero, ptrCast, castZero, evalNum, a, b, CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option linter.unusedSimpArgs false in
theorem result_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat) (h : Heap)
    (err : Int32) (n : UInt64) (code : env.lookup (if generated then "err_1" else "err") = some (.i32 err))
    (len : env.lookup "len" = some (.u64 n)) :
    execStmts f g fuel env h (returnResult generated) =
      .ret (.i32 (if err == Z_STREAM_END then Z_OK else if err == Z_NEED_DICT then Z_DATA_ERROR
        else if err == Z_BUF_ERROR && n == 0 then Z_DATA_ERROR else err)) h := by
  cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte] at code ⊢ <;>
    cases a : err == 1 <;> cases b : err == 2 <;> cases c : err == (-5) <;> cases d : n == 0 <;>
    simp [returnResult, zeroSize, execStmts, execStmt, evalValue, CEnv.lookup_set_ne, code, len,
      intEq, sizeEq, negThree, negFive, castZero, evalNum, Z_STREAM_END, Z_OK, Z_NEED_DICT, Z_DATA_ERROR,
      Z_BUF_ERROR, a, b, c, d, CVal.toBool?, Bind.bind, Except.bind, Pure.pure, Except.pure]

def readWord (p : BPtr) (h : Heap) : Except Fault UInt64 := (CompressWrapper.readLength p h).map Prod.fst

theorem typedWord (p : BPtr) (h : Heap) :
    readHeap .u64 p h = (readWord p h).map CVal.u64 := by
  rw [CompressWrapper.read_typed]
  unfold readWord
  cases CompressWrapper.readLength p h <;> rfl

def observed (run : Except Fault Heap) : StmtOutcome :=
  match run with
  | .ok h => .next [] h
  | .error fault => .fault fault

def readsResult (env : CEnv) (h : Heap) (src dst : BPtr) : StmtOutcome :=
  match readWord src h with
  | .error e => .fault e
  | .ok n =>
    match readWord dst h with
    | .error e => .fault e
    | .ok cap => .next ((env.set "len" (.u64 n)).set "left" (.u64 cap)) h

set_option linter.unusedSimpArgs false in
theorem reads_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (src dst : BPtr) (s : env.lookup "sourceLen" = some (.ptr src))
    (d : env.lookup "destLen" = some (.ptr dst)) :
    execStmts f g fuel env h (readLengths generated) = readsResult env h src dst := by
  cases a : readWord src h <;> cases b : readWord dst h <;> cases generated <;>
    simp [readLengths, readsResult, cell, execStmts, execStmt, evalValue, s, d, CEnv.lookup_set_ne,
      typedWord, a, b, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem add64 (a b : UInt64) (h : Heap) (el : Ty) :
    evalBinOp .u64 "+" (.u64 a) (.u64 b) h el = .ok (.u64 (a+b)) := by
  unfold evalBinOp
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem sub64 (a b : UInt64) (h : Heap) (el : Ty) :
    evalBinOp .u64 "-" (.u64 a) (.u64 b) h el = .ok (.u64 (a-b)) := by
  unfold evalBinOp
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

set_option linter.unusedSimpArgs false in
theorem counts_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (r : ZStreamRef) (z : ZStream) (n cap : UInt64)
    (st : env.lookup "stream" = some (.streamLocal r))
    (len : env.lookup (if generated then "len_1" else "len") = some (.u64 n))
    (left : env.lookup (if generated then "left_1" else "left") = some (.u64 cap))
    (live : r.get h = some z) :
    execStmts f g fuel env h (unusedCounts generated) =
      .next ((env.set "len" (.u64 (n+z.avail_in.toUInt64))).set "left" (.u64 (cap+z.avail_out.toUInt64))) h := by
  cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte] at len left ⊢ <;>
    simp [unusedCounts, execStmts, execStmt, evalValue, st, len, left, CEnv.lookup_set_ne,
      readStreamCount, ldZStream, live, add64, Bind.bind, Except.bind, Pure.pure, Except.pure]

private def update (p : BPtr) (n : UInt64) (h : Heap) : Except Fault Heap := do
  let old ← readWord p h
  writeHeap .u64 p (.u64 (old-n)) h

/-- Both writebacks run in C sequence. The second load observes the first
store's heap even when the two length pointers designate the same cell. -/
def updateLengths (src dst : BPtr) (n cap : UInt64) (h : Heap) : Except Fault Heap := do
  let after ← update src n h
  update dst cap after

set_option linter.unusedSimpArgs false in
theorem writes_run (generated : Bool) (f : FnTable) (g env : CEnv) (fuel : Nat)
    (h : Heap) (src dst : BPtr) (n cap : UInt64)
    (s : env.lookup "sourceLen" = some (.ptr src)) (d : env.lookup "destLen" = some (.ptr dst))
    (len : env.lookup "len" = some (.u64 n)) (room : env.lookup "left" = some (.u64 cap)) :
    OriginalLengthGuards.observe (execStmts f g fuel env h (writeLengths generated)) =
      observed (updateLengths src dst n cap h) := by
  cases srcRead : readWord src h with
  | error e =>
    cases generated <;> simp [writeLengths, updateCell, cell, execStmts, execStmt, evalValue,
      s, typedWord, srcRead, updateLengths, update, observed, OriginalLengthGuards.observe,
      Except.map, Bind.bind, Except.bind]
  | ok old =>
    cases srcWrite : writeHeap .u64 src (.u64 (old-n)) h with
    | error e =>
      cases generated <;> simp [writeLengths, updateCell, cell, execStmts, execStmt, evalValue,
        s, len, CEnv.lookup_set_ne, typedWord, srcRead, srcWrite, sub64, updateLengths, update,
        observed, OriginalLengthGuards.observe, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
    | ok after =>
      cases dstRead : readWord dst after with
      | error e =>
        cases generated <;> simp [writeLengths, updateCell, cell, execStmts, execStmt, evalValue,
          s, d, len, room, CEnv.lookup_set_ne, typedWord, srcRead, srcWrite, dstRead, sub64, updateLengths, update,
          observed, OriginalLengthGuards.observe, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
      | ok avail =>
        cases dstWrite : writeHeap .u64 dst (.u64 (avail-cap)) after <;> cases generated <;>
          simp [writeLengths, updateCell, cell, execStmts, execStmt, evalValue, s, d, len, room,
            CEnv.lookup_set_ne, typedWord, srcRead, srcWrite, dstRead, dstWrite, sub64, updateLengths, update,
            observed, OriginalLengthGuards.observe, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Exact length-update sequence used by the emitted Lean uncompress2_z. -/
def abiUpdates (src dst : BPtr) (n cap : UInt64) : M Unit := do
  store64 src ((← load64 src) - n)
  store64 dst ((← load64 dst) - cap)

private theorem update_raw (h : Heap) (b off : Nat) (n : UInt64) (aligned : UInt64.ofNat off % 8 = 0) :
    update (.ref (.blk b) off) n h =
      ((do store64 (.ref (.blk b) off) ((← load64 (.ref (.blk b) off)) - n) : M Unit) h).map Prod.snd := by
  unfold update readWord
  simp only [CompressWrapper.readLength, ByteAddress.value, aligned, ↓reduceIte]
  cases ld : load64 (.ref (.blk b) off) h with
  | error e => simp [ld, Except.map, Bind.bind, Except.bind]
  | ok pair =>
    obtain ⟨v, after⟩ := pair
    obtain rfl := CompressWrapper.load64_heap _ h v after ld
    simp [ld, Except.map, Bind.bind, Except.bind, CompressWrapper.write_typed,
      CompressWrapper.writeLength, ByteAddress.value, aligned]

/-- Equality with the ABI writebacks on aligned raw cells. Source and
destination may have identical block numbers and offsets. -/
theorem writes_abi (h : Heap) (sb so db doff : Nat) (n cap : UInt64)
    (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0) :
    updateLengths (.ref (.blk sb) so) (.ref (.blk db) doff) n cap h =
      (abiUpdates (.ref (.blk sb) so) (.ref (.blk db) doff) n cap h).map Prod.snd := by
  let single := fun p amt => (do store64 p ((← load64 p) - amt) : M Unit)
  have seq : abiUpdates (.ref (.blk sb) so) (.ref (.blk db) doff) n cap =
      (single (.ref (.blk sb) so) n >>= fun _ => single (.ref (.blk db) doff) cap) := by
    simp [abiUpdates, single]
  rw [seq]
  unfold updateLengths
  rw [update_raw h sb so n sa]
  change (do
    let after ← (single (.ref (.blk sb) so) n h).map Prod.snd
    update (.ref (.blk db) doff) cap after) = _
  rw [bind_app]
  cases first : single (.ref (.blk sb) so) n h with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    exact update_raw after db doff cap da

private theorem store_readback (h : Heap) (b off : Nat) (a : Array UInt8) (v : UInt64)
    (live : h.bytes b = some a) (w : h.ro b = false) (fit : off + 8 ≤ a.size) :
    let p : BPtr := .ref (.blk b) off
    let after := { h with bytes := upd h.bytes b (some (writeLE64 a off v)) }
    load64 p after = .ok (v, after) := by
  let p : BPtr := .ref (.blk b) off
  let after := { h with bytes := upd h.bytes b (some (writeLE64 a off v)) }
  have readback := (store64_load64_spec b (b+1) off a v (fun _ => True) (by omega) fit).le_wp h ⟨live, w, trivial⟩
  rw [wp_run, bind_app, store64_ok (v := v) live w fit] at readback
  dsimp only at readback
  change load64 p after = .ok (v, after)
  cases ld : load64 p after with
  | error e =>
    rw [ld] at readback
    simp at readback
  | ok pair =>
    obtain ⟨v', h'⟩ := pair
    rw [ld] at readback
    obtain rfl := CompressWrapper.load64_heap p after v' h' ld
    rw [readback.1]

/-- When both parameters point to the same aligned length cell, the second
subtraction uses the result of the first. Both subtractions use unsigned arithmetic. -/
theorem writes_alias (h : Heap) (b off : Nat) (a : Array UInt8) (initial n cap : UInt64)
    (live : h.bytes b = some a) (w : h.ro b = false) (fit : off + 8 ≤ a.size)
    (aligned : UInt64.ofNat off % 8 = 0) (initialRead : load64 (.ref (.blk b) off) h = .ok (initial, h)) :
    ∃ after, updateLengths (.ref (.blk b) off) (.ref (.blk b) off) n cap h = .ok after ∧
      load64 (.ref (.blk b) off) after = .ok ((initial-n)-cap, after) := by
  let a' := writeLE64 a off (initial-n)
  let h' := { h with bytes := upd h.bytes b (some a') }
  have g : h'.bytes b = some a' := by simp [h']
  have fit' : off + 8 ≤ a'.size := by simpa [a', size_writeLE64] using fit
  have first := store_readback h b off a (initial-n) live w fit
  have second := store_readback h' b off a' ((initial-n)-cap) g w fit'
  refine ⟨_, ?_, second⟩
  rw [writes_abi h b off b off n cap aligned aligned]
  simp only [abiUpdates, bind_app, initialRead, store64_ok (v := initial-n) live w fit]
  rw [first]
  dsimp only
  rw [store64_ok (v := (initial-n)-cap) g w fit']
  rfl

#print axioms select_run
#print axioms result_run
#print axioms writes_alias
#print axioms reads_run
#print axioms counts_run
#print axioms writes_run
#print axioms writes_abi
end Lean2C.OriginalUncompressLengths
