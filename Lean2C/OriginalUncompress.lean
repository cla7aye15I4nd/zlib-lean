import Lean2C.OriginalUncompressInit
import Lean2C.OriginalCompress

/-! Composition of the pinned uncompress2_z wrapper under the modeled inflate calls. -/
namespace Lean2C.OriginalUncompress
open C CSource Semantics OriginalUncompressLengths OriginalUncompressLoop OriginalUncompressInit
open Zlib.Uncompr Zlib.Gzguts Zlib.GzFs Zlib.Inflate
open CompressWrapper (readLength)
set_option autoImplicit false

private def noFns : FnTable := fun _ => none
private def argEnv (d dl s sl : BPtr) : CEnv :=
  [("dest", .ptr d), ("destLen", .ptr dl), ("source", .ptr s), ("sourceLen", .ptr sl)]

def sourceGuard (generated : Bool) (d dl s sl : BPtr) : M Bool := fun h =>
  OriginalCompress.rejected (execStmts noFns [] 0 (argEnv d dl s sl) h
    (if generated then OriginalLengthGuards.standaloneUncompress else OriginalLengthGuards.originalUncompress))

theorem guard_eq (generated : Bool) (d dl s sl : BPtr) :
    sourceGuard generated d dl s sl = (do
      if sl == .null then return true
      OriginalCompress.checkedGuard d dl s (← readLength sl)) := by
  funext h
  have cert := OriginalLengthGuards.uncompress_guard noFns [] (argEnv d dl s sl) 0 h d dl s sl rfl rfl rfl rfl
  have result := OriginalLengthGuards.uncompressResult_typed h d dl s sl _ (typedWord sl h)
  unfold sourceGuard
  rw [← OriginalCompress.rejected_observe]
  cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte, cert.1, cert.2, result]
  all_goals cases missing : sl == .null <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_app, bind_app]
  all_goals first | rfl | skip
  all_goals unfold readWord
  all_goals
    cases run : readLength sl h with
    | error e => rfl
    | ok pair =>
      obtain ⟨n, g⟩ := pair
      obtain rfl := CompressWrapper.readLength_heap sl h n g run
      exact OriginalCompress.rejected_result d dl s n h

private def lengthsIn (env : CEnv) : Except Fault (UInt64 × UInt64) := do
  let some (.u64 n) := env.lookup "len" | .error (.ub "missing input length")
  let some (.u64 cap) := env.lookup "left" | .error (.ub "missing output capacity")
  return (n, cap)

private def lengthValues : StmtOutcome → Except Fault ((UInt64 × UInt64) × Heap)
  | .next env h => (lengthsIn env).map (fun counts => (counts, h))
  | .fault e => .error e
  | _ => .error (.ub "unexpected control flow in length computation")

def sourceStart (generated : Bool) (dl sl : BPtr) : M (UInt64 × UInt64) := fun h =>
  lengthValues (execStmts noFns [] 0 (argEnv .null dl .null sl) h (readLengths generated))

theorem start_eq (generated : Bool) (dl sl : BPtr) :
    sourceStart generated dl sl = (do let n ← readLength sl; let cap ← readLength dl; return (n, cap)) := by
  funext h
  unfold sourceStart
  rw [reads_run generated _ _ _ _ _ sl dl rfl rfl]
  unfold readsResult readWord
  cases rs : readLength sl h with
  | error e => simp [lengthValues, bind_app, rs, Except.map]
  | ok pair =>
    obtain ⟨n, g⟩ := pair
    obtain rfl := CompressWrapper.readLength_heap sl h n g rs
    cases rd : readLength dl h with
    | error e => simp [lengthValues, bind_app, rs, rd, Except.map]
    | ok pair =>
      obtain ⟨cap, after⟩ := pair
      obtain rfl := CompressWrapper.readLength_heap dl h cap after rd
      simp only [bind_app, rs, rd, pure_app]
      simp [lengthValues, lengthsIn, CEnv.lookup_set_ne, Except.map, Pure.pure, Except.pure]

def sourceDest (generated : Bool) (r : ZStreamRef) (dest reserved : BPtr) (cap : UInt64) : M BPtr := fun h =>
  let env : CEnv := [("stream", .streamWithReserved r reserved), ("dest", .ptr dest), ("left", .u64 cap)]
  match execStmts noFns [] 0 env h (selectDest generated) with
  | .next out after => match out.lookup "dest" with
    | some (.ptr p) => .ok (p, after) | _ => .error (.ub "missing selected destination")
  | .fault e => .error e
  | _ => .error (.ub "unexpected control flow selecting destination")

theorem dest_eq (generated : Bool) (r : ZStreamRef) (dest reserved : BPtr) (cap : UInt64) :
    sourceDest generated r dest reserved cap = pure (if cap == 0 && dest == .null then reserved else dest) := by
  funext h
  unfold sourceDest
  dsimp only
  rw [select_run generated _ _ _ _ _ r dest cap (some reserved) rfl rfl rfl]
  cases generated <;> cases cond : (cap == 0 && dest == .null) <;> simp [pure_app]

def sourceCounts (generated : Bool) (r : ZStreamRef) (st : UncLoop) : M (UInt64 × UInt64) := fun h =>
  let env : CEnv := [("stream", .streamLocal r), (if generated then "len_1" else "len", .u64 st.len),
    (if generated then "left_1" else "left", .u64 st.left)]
  lengthValues (execStmts noFns [] 0 env h (unusedCounts generated))

theorem counts_eq (generated : Bool) (r : ZStreamRef) (st : UncLoop) :
    sourceCounts generated r st = (do
      let z ← ldZ (some r)
      return (st.len + z.avail_in.toUInt64, st.left + z.avail_out.toUInt64)) := by
  funext h
  unfold sourceCounts
  dsimp only
  cases live : r.get h with
  | none =>
    cases generated <;> simp [unusedCounts, execStmts, execStmt, evalValue, CEnv.lookup, readStreamCount,
      lengthValues, ldZ, ldZStream, live, Bind.bind, Except.bind]
  | some z =>
    rw [counts_run generated _ _ _ _ _ r z st.len st.left rfl (by cases generated <;> rfl) (by cases generated <;> rfl) live]
    simp only [bind_app, ldZ, ldZStream, live, pure_app]
    simp [lengthValues, lengthsIn, CEnv.lookup_set_ne, Except.map, Pure.pure, Except.pure]

private def unitOutcome : StmtOutcome → Except Fault (Unit × Heap)
  | .next _ after => .ok ((), after)
  | .fault e => .error e
  | _ => .error (.ub "unexpected control flow during writeback")

def sourceWrites (generated : Bool) (sl dl : BPtr) (n cap : UInt64) : M Unit := fun h =>
  let env : CEnv := [("sourceLen", .ptr sl), ("destLen", .ptr dl), ("len", .u64 n), ("left", .u64 cap)]
  unitOutcome (OriginalLengthGuards.observe (execStmts noFns [] 0 env h (writeLengths generated)))

theorem writes_eq (generated : Bool) (sl dl : BPtr) (n cap : UInt64) :
    sourceWrites generated sl dl n cap = fun h => (updateLengths sl dl n cap h).map (fun after => ((), after)) := by
  funext h
  unfold sourceWrites
  dsimp only
  rw [writes_run generated _ _ _ _ _ sl dl n cap rfl rfl rfl rfl]
  cases updateLengths sl dl n cap h <;> rfl

private def codeOutcome : StmtOutcome → Except Fault (Int32 × Heap)
  | .ret (.i32 code) after => .ok (code, after)
  | .fault e => .error e
  | _ => .error (.ub "missing decompression return")

def sourceReturn (generated : Bool) (err : Int32) (n : UInt64) : M Int32 := fun h =>
  let env : CEnv := [(if generated then "err_1" else "err", .i32 err), ("len", .u64 n)]
  codeOutcome (execStmts noFns [] 0 env h (returnResult generated))

theorem return_eq (generated : Bool) (err : Int32) (n : UInt64) :
    sourceReturn generated err n = pure (if err == Z_STREAM_END then Z_OK else if err == Z_NEED_DICT then Z_DATA_ERROR
      else if err == Z_BUF_ERROR && n == 0 then Z_DATA_ERROR else err) := by
  funext h
  unfold sourceReturn
  dsimp only
  rw [result_run generated _ _ _ _ _ err n (CEnv.lookup_cons_same ..) (by cases generated <;> rfl)]
  rfl

private def sourceInit (generated : Bool) (stream : ZStreamPtr) : M Int32 := fun h => do
  let (version, g) ← strLitRef (initArgs generated).1 h
  let (.i32 size, _, after) ← evalValue noFns [] 0 [] g (initArgs generated).2 | .error (.ub "expected stream size")
  inflateInit_ stream version size after

private theorem init_eq (generated : Bool) (stream : ZStreamPtr) :
    sourceInit generated stream = (do let version ← strLit ZLIB_VERSION; inflateInit_ stream version 112) := by
  funext h
  have args := fun g => args_run generated noFns [] [] 0 g
  unfold sourceInit
  simp only [(args h).1, strLit, Bind.bind, Except.bind]
  cases rd : strLitRef ZLIB_VERSION h with
  | error e => rfl
  | ok pair =>
    obtain ⟨v, g⟩ := pair
    dsimp only
    rw [(args g).2]
    rfl

private def cleanup (stream : ZStreamPtr) (storage : BPtr) : M Unit := do
  freeB storage
  freeZStream stream

/-- Execute the C blocks for a live automatic stream. The parameter
`member` is the byte address used for &stream.reserved. The cleanup action
belongs to the chosen representation of the automatic object. -/
def sourceAt (generated : Bool) (r : ZStreamRef) (member dest dl src sl : BPtr) (leave : M Unit) : M Int32 := do
  if ← sourceGuard generated dest dl src sl then
    leave
    return Z_STREAM_ERROR
  let (n, cap) ← sourceStart generated dl sl
  let out ← sourceDest generated r dest member cap
  sourceFields generated true r src
  let err ← sourceInit generated (some r)
  if ← OriginalCompress.failedInit err then
    leave
    return err
  sourceFields generated false r out
  let st ← cdoWhile (sourceBody generated r) (sourceCond generated) ({ err, len := n, left := cap } : UncLoop)
  let (unused, room) ← sourceCounts generated r st
  sourceWrites generated sl dl unused room
  let _ ← inflateEnd (some r)
  leave
  sourceReturn generated st.err unused

def guardWith (read : BPtr → M UInt64) (d dl s sl : BPtr) : M Bool := do
  if sl == .null then return true
  if (← read sl) > 0 && s == .null then return true
  if dl == .null then return true
  return (← read dl) > 0 && d == .null

def wrapperAt (stream : ZStreamPtr) (member d dl s sl : BPtr) (leave : M Unit)
    (read : BPtr → M UInt64) (writes : UInt64 → UInt64 → M Unit) : M Int32 := do
  if ← guardWith read d dl s sl then
    leave
    return Z_STREAM_ERROR
  let n ← read sl
  let cap ← read dl
  let out := if cap == 0 && d == .null then member else d
  updZ stream (setInput s)
  let version ← strLit ZLIB_VERSION
  let err ← inflateInit_ stream version 112
  if err != Z_OK then
    leave
    return err
  updZ stream (setOutput out)
  let st ← cdoWhile (abiBody stream) (fun l => pure (l.err == Z_OK, l)) ({ err, len := n, left := cap } : UncLoop)
  let z ← ldZ stream
  let unused := st.len + z.avail_in.toUInt64
  writes unused (st.left + z.avail_out.toUInt64)
  let _ ← inflateEnd stream
  leave
  return if st.err == Z_STREAM_END then Z_OK else if st.err == Z_NEED_DICT then Z_DATA_ERROR
      else if st.err == Z_BUF_ERROR && unused == 0 then Z_DATA_ERROR else st.err

private def typedWrites (sl dl : BPtr) (unused room : UInt64) : M Unit := fun h =>
  (updateLengths sl dl unused room h).map (fun after => ((), after))

theorem at_eq (generated : Bool) (r : ZStreamRef) (member d dl s sl : BPtr) (leave : M Unit) :
    sourceAt generated r member d dl s sl leave =
      wrapperAt (some r) member d dl s sl leave readLength (typedWrites sl dl) := by
  unfold sourceAt wrapperAt
  simp only [guard_eq, OriginalCompress.checkedGuard, guardWith, start_eq, dest_eq, sourceFields_eq, init_eq,
    OriginalCompress.failedInit_eq, Bool.false_eq_true, ↓reduceIte, loop_eq, counts_eq, writes_eq,
    return_eq, M_bind_assoc, M_pure_bind]
  cases sl == .null <;> rfl

private theorem aligned_accesses (sb so db doff : Nat)
    (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0) :
    let sl := Ptr.ref (BRef.blk sb) so
    let dl := Ptr.ref (BRef.blk db) doff
    readLength sl = load64 sl ∧ readLength dl = load64 dl ∧ typedWrites sl dl = abiUpdates sl dl := by
  let sl : BPtr := .ref (.blk sb) so
  let dl : BPtr := .ref (.blk db) doff
  have wr : typedWrites sl dl = abiUpdates sl dl := by
    funext n cap h
    unfold typedWrites
    rw [writes_abi h sb so db doff n cap sa da]
    cases abiUpdates sl dl n cap h with
    | error e => rfl
    | ok pair => obtain ⟨u, after⟩ := pair; rfl
  have src : readLength sl = load64 sl := by funext h; simp [readLength, sl, ByteAddress.value, sa]
  have dst : readLength dl = load64 dl := by funext h; simp [readLength, dl, ByteAddress.value, da]
  exact ⟨src, dst, wr⟩

/-- Run the imported blocks directly on a caller-chosen representation of the
automatic member. Both length accesses use the ABI byte operations on aligned
raw cells, even if the cells overlap. -/
theorem at_abi_raw (generated : Bool) (r : ZStreamRef) (member d s : BPtr) (sb so db doff : Nat)
    (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0) (leave : M Unit) :
    let sl := Ptr.ref (BRef.blk sb) so
    let dl := Ptr.ref (BRef.blk db) doff
    sourceAt generated r member d dl s sl leave =
      wrapperAt (some r) member d dl s sl leave load64 (abiUpdates sl dl) := by
  obtain ⟨src, dst, wr⟩ := aligned_accesses sb so db doff sa da
  dsimp only
  rw [at_eq, wr]
  simp only [wrapperAt, guardWith, src, dst]

/-- A non-null output pointer makes the backing address for reserved
unobservable by this wrapper, with the same cleanup action. -/
theorem member_unused (generated : Bool) (r : ZStreamRef) (first second d dl s sl : BPtr)
    (leave : M Unit) (nonnull : d ≠ .null) :
    sourceAt generated r first d dl s sl leave = sourceAt generated r second d dl s sl leave := by
  rw [at_eq, at_eq]
  simp only [wrapperAt, beq_false_of_ne nonnull, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Equality of the two source computations from entry to cleanup, using the
same concrete member address and inflate callees. Includes all modeled faults. -/
theorem same_sources (r : ZStreamRef) (member d dl s sl : BPtr) (leave : M Unit) :
    sourceAt false r member d dl s sl leave = sourceAt true r member d dl s sl leave :=
  (at_eq ..).trans (at_eq ..).symm

private def wrapper (d dl s sl : BPtr) (read : BPtr → M UInt64) (write : UInt64 → UInt64 → M Unit) : M Int32 := do
  let stream ← allocLocalZ
  let storage ← stackAddr stream "reserved" (allocLocal 8)
  wrapperAt stream storage d dl s sl (cleanup stream storage) read write

private theorem bind_branch {α β : Type} (test : Prop) [Decidable test] (yes no : M α) (k : α → M β) :
    ((if test then yes else no) >>= k) = (if test then yes >>= k else no >>= k) := by split <;> rfl

private theorem wrapper_abi (d dl s sl : BPtr) :
    wrapper d dl s sl load64 (abiUpdates sl dl) = uncompress2_z d dl s sl := by
  unfold wrapper wrapperAt uncompress2_z
  simp only [guardWith, cleanup, abiUpdates, M_bind_assoc, bind_branch, M_pure_bind, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Automatic storage is represented by the stream record and its separately
allocated byte view in the Lean ABI. -/
def source (generated : Bool) (d dl s sl : BPtr) : M Int32 := do
  let some r ← allocLocalZ | ub "missing automatic stream"
  let storage ← stackAddr (some r) "reserved" (allocLocal 8)
  sourceAt generated r storage d dl s sl (cleanup (some r) storage)

private theorem allocated_some (h : Heap) (g : Heap) : allocLocalZ h ≠ .ok (none, g) := by
  intro run
  unfold allocLocalZ allocZStream at run
  simp only [↓reduceIte] at run
  cases occupied : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk <;> simp [occupied] at run

theorem source_checked (generated : Bool) (d dl s sl : BPtr) :
    source generated d dl s sl = wrapper d dl s sl readLength (typedWrites sl dl) := by
  funext h
  unfold source wrapper
  simp only [bind_app]
  cases allocation : allocLocalZ h with
  | error e => rfl
  | ok pair =>
    obtain ⟨stream, g⟩ := pair
    cases stream with
    | none => exact (allocated_some h g allocation).elim
    | some r =>
      simp only [bind_app, stackAddr]
      cases storage : allocLocal 8 g with
      | error e => rfl
      | ok pair =>
        obtain ⟨p, after⟩ := pair
        exact congrFun (at_eq generated r p d dl s sl _) after

/-- The checked wrapper agrees with the ABI for aligned raw length arguments,
including aliasing. The theorem uses the ABI representation of stack storage. -/
theorem source_abi (generated : Bool) (d s : BPtr) (sb so db doff : Nat)
    (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0) :
    source generated d (.ref (.blk db) doff) s (.ref (.blk sb) so) =
      uncompress2_z d (.ref (.blk db) doff) s (.ref (.blk sb) so) := by
  obtain ⟨src, dst, wr⟩ := aligned_accesses sb so db doff sa da
  rw [source_checked, ← wrapper_abi, wr]
  simp only [wrapper, wrapperAt, guardWith, src, dst]

#print axioms source_abi
#print axioms same_sources
end Lean2C.OriginalUncompress
