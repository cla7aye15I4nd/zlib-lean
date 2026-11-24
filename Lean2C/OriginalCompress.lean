import Lean2C.OriginalCompressInit

/-! Compose the LP64 compress2_z source blocks using the modeled external calls. -/
namespace Lean2C.OriginalCompress
open C CSource Semantics OriginalCompressLengths OriginalCompressInit OriginalCompressLoop
open CompressWrapper (readLength writeLength)
open Zlib.Deflate Zlib.Compress
set_option autoImplicit false

private def emptyFns : FnTable := fun _ => none

private def guardEnv (d dl s : BPtr) (n : UInt64) : CEnv :=
  [("dest", .ptr d), ("destLen", .ptr dl), ("source", .ptr s), ("sourceLen", .u64 n)]

def rejected (out : StmtOutcome) : Except Fault (Bool × Heap) :=
  match out with
  | .next _ h => .ok (false, h)
  | .ret (.i32 code) h => if code == (-2) then .ok (true, h) else .error (.ub "unexpected refusal code")
  | .fault e => .error e
  | _ => .error (.ub "unexpected compression guard exit")

theorem rejected_observe (out : StmtOutcome) :
    rejected (OriginalLengthGuards.observe out) = rejected out := by cases out <;> rfl

def sourceGuard (generated : Bool) (d dl s : BPtr) (n : UInt64) : M Bool := fun h =>
  rejected (execStmts emptyFns [] 0 (guardEnv d dl s n) h
    (if generated then OriginalLengthGuards.standaloneCompress else OriginalLengthGuards.originalCompress))

def checkedGuard (d dl s : BPtr) (n : UInt64) : M Bool := do
  if n > 0 && s == .null then return true
  if dl == .null then return true
  return (← readLength dl) > 0 && d == .null

theorem rejected_result (d dl s : BPtr) (n : UInt64) (h : Heap) :
    rejected (OriginalLengthGuards.compressResult h d dl s n) = checkedGuard d dl s n h := by
  have scalar := CompressWrapper.read_typed dl h
  have result := OriginalLengthGuards.compressResult_typed h d dl s n ((readLength dl h).map Prod.fst) (by
    rw [scalar]; cases readLength dl h <;> rfl)
  rw [result]
  all_goals
    cases bad : (n > 0 && s == .null) <;> cases nullLen : dl == .null <;>
      simp only [checkedGuard, bad, nullLen, Bool.false_eq_true, ↓reduceIte, rejected, beq_self_eq_true, ↓reduceIte, pure_app, bind_app]
  all_goals
    cases read : readLength dl h with
    | error e => rfl
    | ok pair =>
      obtain ⟨cap, g⟩ := pair
      obtain rfl := CompressWrapper.readLength_heap dl h cap g read
      cases test : (cap > 0 && d == .null) <;> simp [OriginalLengthGuards.acceptedDest, test, Except.map]

theorem guard_eq (generated : Bool) (d dl s : BPtr) (n : UInt64) :
    sourceGuard generated d dl s n = checkedGuard d dl s n := by
  funext h
  have cert := OriginalLengthGuards.compress_guard emptyFns [] (guardEnv d dl s n) 0 h d dl s n rfl rfl rfl rfl
  unfold sourceGuard
  rw [← rejected_observe]
  cases generated <;> simp only [Bool.false_eq_true, ↓reduceIte, cert.1, cert.2, rejected_result]

private def savedCapacity (out : StmtOutcome) : Except Fault (UInt64 × Heap) :=
  match out with
  | .next env h => match env.lookup "left" with
    | some (.u64 n) => .ok (n, h)
    | _ => .error (.ub "missing saved capacity")
  | .fault e => .error e
  | _ => .error (.ub "unexpected length initializer exit")

def sourceStart (generated : Bool) (dl : BPtr) : M UInt64 := fun h =>
  savedCapacity (execStmts emptyFns [] 0 [("destLen", .ptr dl)] h (if generated then standaloneStart else originalStart))

theorem start_eq (generated : Bool) (dl : BPtr) :
    sourceStart generated dl = (do let n ← readLength dl; writeLength dl 0; pure n) := by
  funext h
  unfold sourceStart
  have scalar := CompressWrapper.read_typed dl h
  rw [start_outcome generated _ _ _ _ _ _ (by rfl) ((readLength dl h).map Prod.fst) (by
    rw [scalar]; cases readLength dl h <;> rfl)]
  simp only [bind_app]
  cases rd : readLength dl h with
  | error fault => rfl
  | ok pair =>
    obtain ⟨n, h1⟩ := pair
    obtain rfl := CompressWrapper.readLength_heap dl h n h1 rd
    simp only [Except.map, startResult]
    rw [CompressWrapper.write_typed]
    cases wr : writeLength dl 0 h with
    | error fault => rfl
    | ok p => obtain ⟨u, g⟩ := p; rfl

private def nextUnit : StmtOutcome → Except Fault (Unit × Heap)
  | .next _ h => .ok ((), h)
  | .fault e => .error e
  | _ => .error (.ub "unexpected control transfer")

private def localEnv (generated : Bool) (r : ZStreamRef) (d dl s : BPtr) : CEnv :=
  [(if generated then "strm" else "stream", .streamLocal r), ("dest", .ptr d), ("destLen", .ptr dl), ("source", .ptr s)]

def sourceFields (generated alloc : Bool) (r : ZStreamRef) (dest source : BPtr) : M Unit := fun h =>
  nextUnit (execStmts emptyFns [] 0 (localEnv generated r dest .null source) h
    (if alloc then allocators generated else buffers generated))

theorem fields_eq (generated alloc : Bool) (r : ZStreamRef) (dest source : BPtr) :
    sourceFields generated alloc r dest source =
      (if alloc then zwr (some r) (fun z => {z with zalloc := .null, zfree := .null, «opaque» := .null}) else do
        zwr (some r) (fun z => {z with next_out := dest, avail_out := 0})
        zwr (some r) (fun z => {z with next_in := source, avail_in := 0})) := by
  funext h
  let env := localEnv generated r dest .null source
  have obj : env.lookup (if generated then "strm" else "stream") = some (.streamLocal r) := CEnv.lookup_cons_same ..
  have dst : env.lookup "dest" = some (.ptr dest) := by cases generated <;> rfl
  have src : env.lookup "source" = some (.ptr source) := by cases generated <;> rfl
  unfold sourceFields
  cases live : r.get h with
  | none =>
    rw [fields_dangling generated alloc _ _ env _ _ r dest obj dst live]
    cases alloc <;> simp [nextUnit, zwr, ldZStream, live]
  | some z =>
    cases alloc with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [buffers_run generated _ _ env _ _ _ _ dest source obj dst src live]
      simp [nextUnit, Zlib.Deflate.Proofs.zwr_eq, live]
    | true =>
      simp only [↓reduceIte]
      rw [allocators_run generated _ _ env _ _ _ _ obj live]
      simp [nextUnit, Zlib.Deflate.Proofs.zwr_eq, live]

def sourceFinish (generated : Bool) (r : ZStreamRef) (dest p : BPtr) : M Unit := fun h =>
  nextUnit (OriginalLengthGuards.observe (execStmts emptyFns [] 0 (localEnv generated r dest p .null) h
    (if generated then standaloneWriteback else originalWriteback)))

private theorem diff_heap (p q : BPtr) : Preserves Eq (elementDifference .u8 p q) := by
  intro h n after run
  unfold elementDifference at run
  simp only [elementBytes] at run
  cases p <;> cases q <;>
    simp only [reduceCtorEq, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  all_goals repeat' split at run
  all_goals cases run <;> rfl

theorem finish_eq (generated : Bool) (r : ZStreamRef) (dest p : BPtr) :
    sourceFinish generated r dest p = (do
      let no ← zrd (some r) (·.next_out)
      let n ← elementDifference .u8 no dest
      writeLength p n.toUInt64) := by
  funext h
  let env := localEnv generated r dest p .null
  have lenArg : env.lookup "destLen" = some (.ptr p) := by cases generated <;> rfl
  have destArg : env.lookup "dest" = some (.ptr dest) := by cases generated <;> rfl
  unfold sourceFinish
  rw [writeback _ _ env _ _ r p dest generated lenArg destArg (CEnv.lookup_cons_same ..)]
  cases live : r.get h with
  | none => simp [writebackResult, nextUnit, zrd, ldZStream, live]
  | some z =>
    simp only [writebackResult, zrd, bind_app, ldZStream, live, pure_app]
    cases diff : elementDifference .u8 z.next_out dest h with
    | error fault => rfl
    | ok pair =>
      obtain ⟨n, g⟩ := pair
      obtain rfl := diff_heap _ _ h n g diff
      dsimp only
      rw [CompressWrapper.write_typed]
      cases wr : writeLength p n.toUInt64 h with
      | error fault => rfl
      | ok pair => obtain ⟨u, after⟩ := pair; rfl

private def initCall (generated : Bool) (r : ZStreamRef) (level : Int32) : M Int32 := fun h => do
  let env : CEnv := [("level", .i32 level)]
  let (.i32 lv, _, h1) ← evalValue emptyFns [] 0 env h (initArgs generated).1 | .error (.ub "expected int level")
  let (version, h2) ← strLitRef (initArgs generated).2.1 h1
  let (.i32 size, _, h3) ← evalValue emptyFns [] 0 env h2 (initArgs generated).2.2 | .error (.ub "expected int size")
  deflateInit_ (some r) lv version size h3

private theorem initCall_eq (generated : Bool) (r : ZStreamRef) (level : Int32) :
    initCall generated r level = (do
      let version ← Zlib.GzFs.strLit ZLIB_VERSION
      deflateInit_ (some r) level version sizeof_z_stream) := by
  funext h
  let args := fun g => init_args_run generated emptyFns [] [("level", .i32 level)] 0 g level rfl
  unfold initCall
  simp only [(args h).1, (args h).2.1, Bind.bind, Except.bind, Zlib.GzFs.strLit]
  cases result : strLitRef ZLIB_VERSION h with
  | error e => rfl
  | ok pair =>
    obtain ⟨version, h2⟩ := pair
    dsimp only
    rw [(args h2).2.2]

def failedInit (code : Int32) : M Bool := fun h =>
  match execStmts emptyFns [] 0 [("err", .i32 code)] h initResult with
  | .next _ after => .ok (false, after)
  | .ret (.i32 _) after => .ok (true, after)
  | .fault e => .error e
  | _ => .error (.ub "unexpected initialization exit")

theorem failedInit_eq (err : Int32) : failedInit err = pure (err != Z_OK) := by
  funext h
  unfold failedInit
  rw [init_result _ _ _ _ _ err rfl]
  cases e : err != 0 <;> simp only [e, Z_OK, pure_app, Bool.false_eq_true, ↓reduceIte]

private def returnCode (code : Int32) : M Int32 := fun h =>
  match execStmts emptyFns [] 0 [("err", .i32 code)] h resultCode with
  | .ret (.i32 result) after => .ok (result, after)
  | .fault e => .error e
  | _ => .error (.ub "missing compression return")

private theorem returnCode_eq (err : Int32) : returnCode err = pure (if err == Z_STREAM_END then Z_OK else err) := by
  funext h
  unfold returnCode
  rw [result_code _ _ _ _ _ err rfl]
  rfl

/-- Execute the imported source blocks, with zlib calls interpreted by the
pinned model. The stream has automatic duration and is released on every
return. A fault aborts the computation. -/
def sourceAt (generated : Bool) (r : ZStreamRef) (dest dl src : BPtr) (n : UInt64) (level : Int32) : M Int32 := do
  if ← sourceGuard generated dest dl src n then
    freeZStream (some r)
    return Z_STREAM_ERROR
  let left ← sourceStart generated dl
  sourceFields generated true r dest src
  let err ← initCall generated r level
  if ← failedInit err then
    freeZStream (some r)
    return err
  sourceFields generated false r dest src
  let st ← cdoWhile (sourceBody generated r) (sourceCond generated) (err, left, n)
  sourceFinish generated r dest dl
  let _ ← deflateEnd (some r)
  freeZStream (some r)
  returnCode st.1

def source (generated : Bool) (dest dl src : BPtr) (n : UInt64) (level : Int32) : M Int32 := do
  let some r ← allocLocalZ | ub "missing automatic stream"
  sourceAt generated r dest dl src n level

set_option maxHeartbeats 800000 in
private theorem at_eq (generated : Bool) (r : ZStreamRef) (d dl s : BPtr) (n : UInt64) (level : Int32) :
    sourceAt generated r d dl s n level =
      CompressWrapper.wrapperAt (some r) d dl s n level true (readLength dl) (writeLength dl)
        (fun no => elementDifference .u8 no d) := by
  unfold sourceAt CompressWrapper.wrapperAt
  simp only [guard_eq, start_eq, fields_eq, Bool.false_eq_true, ↓reduceIte, initCall_eq, failedInit_eq,
    returnCode_eq, finish_eq, loop_eq, CompressWrapper.loop_body, M_bind_assoc, M_pure_bind, checkedGuard]
  cases (n > 0 && s == .null) <;> cases dl == .null <;>
    simp only [Bool.false_eq_true, ↓reduceIte, M_pure_bind, M_bind_assoc]

theorem source_checked (generated : Bool) (d dl s : BPtr) (n : UInt64) (level : Int32) :
    source generated d dl s n level = CompressWrapper.checked d dl s n level := by
  funext h
  unfold source CompressWrapper.checked CompressWrapper.wrapper
  simp only [bind_app]
  cases run : allocLocalZ h with
  | error e => rfl
  | ok pair =>
    obtain ⟨p, g⟩ := pair
    cases p with
    | some r => exact congrFun (at_eq generated r d dl s n level) g
    | none =>
      unfold allocLocalZ allocZStream at run
      simp only [↓reduceIte] at run
      cases occupied : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk <;>
        simp [occupied] at run

/-- On an aligned raw length cell with a non-null destination, executing either
C source through the modeled calls gives the exact emitted Lean computation. -/
theorem source_abi (generated : Bool) (dest src : BPtr) (blk offset : Nat) (n : UInt64) (level : Int32)
    (aligned : UInt64.ofNat offset % 8 = 0) (nonnull : dest ≠ .null) :
    source generated dest (.ref (.blk blk) offset) src n level =
      compress2_z_c dest (.ref (.blk blk) offset) src n level :=
  (source_checked ..).trans (CompressWrapper.checked_raw _ _ _ _ _ _ aligned nonnull)

theorem source_early (generated : Bool) (dest dl src : BPtr) (n : UInt64) (level : Int32)
    (early : (n > 0 && src == .null) = true ∨ dl = .null) :
    source generated dest dl src n level = compress2_z_c dest dl src n level :=
  (source_checked ..).trans (CompressWrapper.checked_early dest dl src n level early)

/-- The two source representations agree even on paths that encounter a
strict typed fault or bail out before dereferencing a length pointer. -/
theorem same_sources (d dl s : BPtr) (n : UInt64) (level : Int32) :
    source false d dl s n level = source true d dl s n level :=
  (source_checked ..).trans (source_checked ..).symm

#print axioms source_checked
#print axioms source_abi
#print axioms same_sources

end Lean2C.OriginalCompress
