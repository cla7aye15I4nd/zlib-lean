import Lean2C.OriginalCompressLengths
import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.ControlFlowFrame
import ZlibF.Proof.«trees.c.monad»

/-! Relate the full exported Lean wrapper to the typed length accesses. -/
namespace Lean2C.CompressWrapper
open C Zlib.Compress Zlib.Deflate
set_option autoImplicit false

/-- The original loop uses the stream counter it just wrote as the amount
consumed from the remaining length. The emitted loop uses the local value. -/
def refill (stream : ZStreamPtr) (len : UInt64) (readBack : Bool)
    (field : ZStream → UInt32) (update : ZStream → UInt32 → ZStream) : M UInt64 := do
  if (← zrd stream field) != 0 then return len
  let count : UInt32 := if len > (0xffffffff : UInt32).toUInt64 then 0xffffffff else len.toUInt32
  zwr stream (fun z => update z count)
  let used ← if readBack then zrd stream field else pure count
  return len - used.toUInt64

def iteration (stream : ZStreamPtr) (readBack : Bool) (st : Int32 × UInt64 × UInt64) :
    M (Int32 × UInt64 × UInt64) := do
  let left ← refill stream st.2.1 readBack (·.avail_out) (fun z n => {z with avail_out := n})
  let remaining ← refill stream st.2.2 readBack (·.avail_in) (fun z n => {z with avail_in := n})
  let err ← deflate stream (if remaining != 0 then Z_NO_FLUSH else Z_FINISH)
  return (err, left, remaining)

private theorem refill_readback (stream : ZStreamPtr) (len : UInt64)
    (field : ZStream → UInt32) (update : ZStream → UInt32 → ZStream)
    (get_set : ∀ z n, field (update z n) = n) :
    refill stream len true field update = refill stream len false field update := by
  funext h
  cases stream with
  | none => rfl
  | some r =>
    cases live : r.get h with
    | none => simp [refill, zrd, ldZStream, live]
    | some z =>
      have get (v) := Zlib.Deflate.Proofs.ZStreamRef.get_put_same live v
      have writable : r.isRo = false := by cases r <;> rfl
      by_cases empty : field z = 0 <;>
        simp [refill, zrd, zwr, ldZStream, stZStream, live, empty, writable, get, get_set]

theorem loop_body (stream : ZStreamPtr) :
    iteration stream true = iteration stream false := by
  funext st
  unfold iteration
  rw [refill_readback stream st.2.1 (·.avail_out) _ (by intros; rfl),
      refill_readback stream st.2.2 (·.avail_in) _ (by intros; rfl)]

/-- Execution with either representation of the two refills. The selected
length operations are called only at their original control-flow locations. -/
def wrapperAt (strm : ZStreamPtr) (dest destLen source : BPtr) (sourceLen : UInt64) (level : Int32) (readBack : Bool)
    (read : M UInt64) (write : UInt64 → M Unit) (difference : BPtr → M Int64) : M Int32 := do
  let mut bad := false
  if sourceLen > 0 && source == .null then bad := true
  else if destLen == .null then bad := true
  else if (← read) > 0 && dest == .null then bad := true
  if bad then
    freeZStream strm
    return Z_STREAM_ERROR
  let left ← read
  write 0
  zwr strm (fun z => {z with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null})
  let ver ← Zlib.GzFs.strLit ZLIB_VERSION
  let err ← deflateInit_ strm level ver sizeof_z_stream
  if err != Z_OK then
    freeZStream strm
    return err
  zwr strm (fun z => {z with next_out := dest, avail_out := 0})
  zwr strm (fun z => {z with next_in := source, avail_in := 0})
  let st ← cdoWhile (iteration strm readBack) (fun st => pure (st.1 == Z_OK, st)) (err, left, sourceLen)
  let no ← zrd strm (·.next_out)
  let n ← difference no
  write n.toUInt64
  let _ ← deflateEnd strm
  freeZStream strm
  return if st.1 == Z_STREAM_END then Z_OK else st.1

def wrapper (dest destLen source : BPtr) (sourceLen : UInt64) (level : Int32) (readBack : Bool)
    (read : M UInt64) (write : UInt64 → M Unit) (difference : BPtr → M Int64) : M Int32 := do
  let strm ← allocLocalZ
  wrapperAt strm dest destLen source sourceLen level readBack read write difference

private theorem emitted_iteration (stream : ZStreamPtr) : iteration stream false =
    (fun ((_, left, sourceLen) : Int32 × UInt64 × UInt64) => do
      let mut left := left
      let mut sourceLen := sourceLen
      if (← zrd stream (·.avail_out)) == 0 then
        let ao : UInt32 := if left > (0xffffffff : UInt32).toUInt64 then 0xffffffff else left.toUInt32
        zwr stream (fun z => { z with avail_out := ao })
        left := left - ao.toUInt64
      if (← zrd stream (·.avail_in)) == 0 then
        let ai : UInt32 := if sourceLen > (0xffffffff : UInt32).toUInt64 then 0xffffffff else sourceLen.toUInt32
        zwr stream (fun z => { z with avail_in := ai })
        sourceLen := sourceLen - ai.toUInt64
      let err ← deflate stream (if sourceLen != 0 then Z_NO_FLUSH else Z_FINISH)
      pure (err, left, sourceLen)) := by
  funext st h
  obtain ⟨err, left, n⟩ := st
  cases stream with
  | none => rfl
  | some r =>
    cases live : r.get h with
    | none => simp [iteration, refill, zrd, ldZStream, live]
    | some z =>
      have writable : r.isRo = false := by cases r <;> rfl
      by_cases ho : z.avail_out = 0 <;> by_cases hi : z.avail_in = 0 <;>
        simp [iteration, refill, zrd, zwr, ldZStream, stZStream, live, writable, ho, hi]

/-- With the actual ABI primitives, this is the computation consumed by the
C generator, including early returns and the heap after cleanup. -/
theorem wrapper_abi (dest destLen source : BPtr) (sourceLen : UInt64) (level : Int32) :
    wrapper dest destLen source sourceLen level true (load64 destLen) (store64 destLen) (fun no => Ptr.diff no dest) =
      compress2_z_c dest destLen source sourceLen level := by
  unfold wrapper wrapperAt compress2_z_c
  simp only [loop_body, emitted_iteration]

private theorem byteRead (p : BPtr) (i : Int) : Preserves Eq (index8 p i) := by
  apply Preserves.bind (@Eq.trans Heap)
  · intro h v after run
    unfold Ptr.add at run
    repeat' split at run
    all_goals cases run <;> rfl
  · intro q h v after run
    unfold Ptr.load at run
    repeat' split at run
    all_goals cases run <;> rfl
private theorem pureRead {α : Type} (v : α) : Preserves Eq (pure v : M α) := by
  intro h x after run
  cases run; rfl

theorem load64_heap (p : BPtr) : Preserves Eq (load64 p) := by
  unfold load64
  simp only [forIn, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size]
  rw [show List.range' 0 ((8 - 0 + 1 - 1) / 1) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.forIn'_cons, List.forIn'_nil, M_bind_assoc, M_pure_bind]
  repeat' first
    | exact pureRead _
    | apply Preserves.bind (@Eq.trans Heap) (byteRead _ _); intro x

/-- Reached typed accesses use the current heap's address residue. -/
def readLength (p : BPtr) : M UInt64 := fun h =>
  if ByteAddress.value h p % 8 = 0 then load64 p h else .error (.ub "misaligned unsigned long load")

def writeLength (p : BPtr) (n : UInt64) : M Unit := fun h =>
  if ByteAddress.value h p % 8 = 0 then store64 p n h else .error (.ub "misaligned unsigned long store")

theorem read_typed (p : BPtr) (h : Heap) : Semantics.readHeap .u64 p h =
    (readLength p h).map (fun a => Semantics.CVal.u64 a.1) := by
  by_cases a : ByteAddress.value h p % 8 = 0
  · cases v : load64 p h with
    | error fault => simp [Semantics.readHeap, readLength, a, v, Bind.bind, Except.bind, Except.map]
    | ok pair => rcases pair with ⟨n, g⟩; simp [Semantics.readHeap, readLength, a, v, Bind.bind, Except.bind, Except.map]; rfl
  · simp [Semantics.readHeap, readLength, a, Bind.bind, Except.bind, Except.map]

theorem readLength_heap (p : BPtr) : Preserves Eq (readLength p) := by
  intro h n after run
  unfold readLength at run
  split at run
  · exact load64_heap p h n after run
  · cases run

theorem write_typed (p : BPtr) (n : UInt64) (h : Heap) : Semantics.writeHeap .u64 p (.u64 n) h =
    (writeLength p n h).map Prod.snd := by
  by_cases a : ByteAddress.value h p % 8 = 0
  · cases v : store64 p n h with
    | error fault => simp [Semantics.writeHeap, writeLength, a, v, Bind.bind, Except.bind, Except.map]
    | ok pair => rcases pair with ⟨u, g⟩; simp [Semantics.writeHeap, writeLength, a, v, Bind.bind, Except.bind, Except.map]; rfl
  · simp [Semantics.writeHeap, writeLength, a, Bind.bind, Except.bind, Except.map]

private theorem diff_nonnull (dest : BPtr) (nonNull : dest ≠ .null) (no : BPtr) :
    Semantics.elementDifference .u8 no dest = Ptr.diff no dest := by
  funext h
  cases dest with
  | null => exact (nonNull rfl).elim
  | ref r j =>
    cases no with
    | null => rfl
    | ref q i =>
      by_cases same : q = r
      · subst q
        cases live : Space.get h r with
        | none => simp [Semantics.elementDifference, Semantics.elementBytes, Ptr.diff, live]
        | some bytes =>
          by_cases hi : i ≤ bytes.size <;> by_cases hj : j ≤ bytes.size <;>
            simp (disch := omega) [Semantics.elementDifference, Semantics.elementBytes, Ptr.diff, Semantics.inSignedRange,
              live, hi, hj, Bind.bind, Except.bind, Pure.pure, Except.pure]
          intro outside
          omega
      · simp [Semantics.elementDifference, Semantics.elementBytes, Ptr.diff, same, Bind.bind, Except.bind]

/-- Full wrapper with checked LP64 length accesses and strict pointer subtraction. -/
def checked (dest destLen source : BPtr) (sourceLen : UInt64) (level : Int32) : M Int32 :=
  wrapper dest destLen source sourceLen level true (readLength destLen) (writeLength destLen)
    (fun no => Semantics.elementDifference .u8 no dest)

/-- Every reached read, clear and final store is checked. An aligned raw
length-cell offset has the same residue on every heap, including after calls
to deflate. A non-null destination excludes the null-minus-null exception. -/
theorem checked_raw (dest source : BPtr) (blk offset : Nat) (n : UInt64) (level : Int32)
    (aligned : UInt64.ofNat offset % 8 = 0) (out : dest ≠ .null) :
    checked dest (.ref (.blk blk) offset) source n level =
      compress2_z_c dest (.ref (.blk blk) offset) source n level := by
  unfold checked
  simp only [diff_nonnull dest out]
  have rd : readLength (.ref (.blk blk) offset) = load64 (.ref (.blk blk) offset) := by
    funext h
    simp [readLength, ByteAddress.value, aligned]
  have wr : writeLength (.ref (.blk blk) offset) = store64 (.ref (.blk blk) offset) := by
    funext v h
    simp [writeLength, ByteAddress.value, aligned]
  rw [rd, wr, wrapper_abi]

/-- The first two refusal paths bypass every length access. They agree on
arbitrary heaps and pointer values, including an unaligned destination length. -/
theorem checked_early (dest dl src : BPtr) (n : UInt64) (level : Int32)
    (early : (n > 0 && src == .null) = true ∨ dl = .null) :
    checked dest dl src n level = compress2_z_c dest dl src n level := by
  rw [← wrapper_abi]
  unfold checked wrapper wrapperAt
  rcases early with badSource | rfl
  · simp only [badSource, ↓reduceIte]
  · cases (n > 0 && src == .null) <;>
      simp only [Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]

#print axioms wrapper_abi
#print axioms checked_raw
#print axioms checked_early

end Lean2C.CompressWrapper
