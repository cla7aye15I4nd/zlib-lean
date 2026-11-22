import ZlibF.Proof.«deflate.c.engine.call-size-data»
import ZlibF.Proof.«deflate.c.engine.valid-pending-entry»
import ZlibF.Proof.«deflate.c.engine.valid-flush-entry»
import ZlibF.Proof.«deflate.c.engine.public-pending-checksum»
import ZlibF.Proof.«deflate.c.engine.stream-control»
import ZlibF.Proof.«deflate.c.engine.pending-buffered»
import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»
import ZlibF.Proof.«deflate.c.engine.strategy-no-flush-loop»

/-! # The size of a whole `BUSY_STATE` call

A `deflate` call with `Z_NO_FLUSH` or `Z_FINISH` from a `BUSY_STATE` boundary with room: with
nothing pending, the duplicate-request refusal (nothing changes) or the data part; with pending
output, the pending flush, then (when room is left) the data part. Delivered pending bytes leave
the held bytes, so the ledger outcome of the data part carries over.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- An outcome after delivering `first` pending bytes first. -/
theorem BusySizeOutcome.prepend {after : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream}
    {result : DeflateState} {flush rc : Int32} {start base held heldM first produced : Nat}
    (outcome : BusySizeOutcome after r ds z' result flush rc start base heldM produced)
    (moved : first + heldM = held) :
    BusySizeOutcome after r ds z' result flush rc start base held (first + produced) := by
  rcases outcome with ⟨status, input', origin', base', xs', boundary, endpoint, companion, size⟩ |
      ⟨status, size, ended, entry⟩
  · exact Or.inl ⟨status, input', origin', base', xs', boundary, endpoint, companion, by omega⟩
  · exact Or.inr ⟨status, by omega, ended, entry⟩

/-- **The size of a `BUSY_STATE` call.** -/
theorem busy_call_size {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {flush rc : Int32}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (bits : config.windowBits = 15)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (lower : -2 ≤ d.last_flush.toInt) (upper : d.last_flush.toInt ≤ 5)
    (companion : SizeCompanion d xs) (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    ∃ used produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      StreamAccounting z z' used produced ∧
      (flush = Z_FINISH → rc = Z_OK → z'.avail_out = 0) ∧
      BusySizeOutcome after r ds z' result flush rc (origin + fillEnd d + used) base (heldBytes d) produced := by
  have flagLo : 0 ≤ flush.toInt := by rcases clean with rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ 5 := by rcases clean with rfl | rfl <;> decide
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; cases output
  have boundary0 := last_flush_buffered_boundary boundary flush
  have buffers0 := last_flush_buffers boundary.good buffers flush
  by_cases queued : d.pending = 0
  · have publish0 : PublishReady { d with last_flush := flush } :=
      ⟨queued, boundary.empty_cursor queued, boundary.bits⟩
    obtain ⟨current, old, _currentRank, _oldRank, source⟩ := public_busy_valid_entry_choice boundary.good
      status queued nonnull positive inputValid lower upper flush flagLo flagHi
    by_cases duplicate : (z.avail_in == 0 && decide (current ≤ old) && flush != Z_FINISH) = true
    · rw [ite_eq_left duplicate] at source
      obtain ⟨message, refused⟩ := err_return_run boundary0.good.live.hz Z_BUF_ERROR
      let z' := {z with msg := message}
      have goodA := stream_control_good (z' := z') boundary0.good rfl boundary.good.live.zalloc
        boundary.good.live.zfree
      have stateA := stream_control_buffered boundary0 goodA
      obtain ⟨rcs, heaps⟩ := Prod.mk.inj (Except.ok.inj ((source.trans refused).symm.trans run))
      subst heaps
      refine ⟨0, 0, z', { d with last_flush := flush }, goodA.live.hz, goodA.live.hs, stream_accounting_zero z,
        fun _ ok => absurd (rcs.trans ok) (by decide), Or.inl ⟨status, input, origin, base, xs, stateA.toContentBoundary, rfl, companion, ?_⟩⟩
      change 0 + heldBytes d + base + 5 * (base / 16383) ≤ heldBytes d + base + 5 * (base / 16383)
      omega
    · rw [ite_eq_right duplicate] at source
      exact busy_data_tail_size (d := { d with last_flush := flush }) boundary0 buffers0 status level strategy
        pointer memory wrap bits publish0 inputValid companion clean (source.symm.trans run)
  · obtain ⟨before, pendingBits⟩ := good_pending_bits boundary.good
    by_cases enough : z.avail_out.toNat ≤ d.pending.toNat
    · obtain ⟨_pb, other, z', result, _written, _remaining, _base, tested, stateA, _buffersA, accountA,
          _sizes, _storage, emptyA, _last, count, _low, frame, _bytes, _pendingA, _wire, _adler⟩ :=
        public_pending_buffered_exhausted_adler flush boundary buffers pointer inputValid flagLo flagHi
          (by intro finished; rw [status] at finished; cases finished) output enough pendingBits
      obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run))
      subst heaps
      refine ⟨0, z.avail_out.toNat, z', result, stateA.good.live.hz, stateA.good.live.hs, accountA,
        fun _ _ => emptyA, Or.inl ⟨?_, input, origin, base, xs, stateA.toContentBoundary, ?_, ?_, ?_⟩⟩
      · rw [frame]; exact status
      · rw [frame]; rfl
      · rw [frame]; exact companion
      · have bitsEq : result.bi_valid = d.bi_valid := by rw [frame]
        unfold heldBytes
        rw [bitsEq]
        omega
    · have pending0 := last_flush_pending_bits boundary.good pendingBits flush
      obtain ⟨_pb, produced, middle, zm, dm, _written, _remaining, _base, flushRun, stateM, buffersM,
          accountM, _sizesM, _storageM, amount, pendingCount, fields, readyM, _bytesM, _pendingM, _bitsM⟩ :=
        flush_pending_buffered_boundary boundary0 buffers0 pointer pending0
      have statusM : dm.status = BUSY_STATE := by rw [fields]; exact status
      have levelM : dm.level = 6 := by rw [fields]; exact level
      have strategyM : dm.strategy = 0 := by rw [fields]; exact strategy
      have left : 0 < zm.avail_out.toNat := by
        have balance := accountM.2.2.2.1
        change produced = min d.pending.toNat z.avail_out.toNat at amount
        rw [Nat.min_eq_left (by omega)] at amount
        omega
      have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
        rw [accountM.2.2.2.2.2.1, pointer]; rfl
      have entry := public_pending_valid_continue boundary.good stateM.good status nonnull positive inputValid
        queued flush flagLo flagHi flushRun (by intro zero; rw [zero] at left; contradiction)
        (by intro finished; rw [statusM] at finished; cases finished)
      rw [entry, public_busy_header_skip_next stateM.good statusM] at run
      have companionM : SizeCompanion dm xs := by rw [fields]; exact companion
      obtain ⟨used, laterProduced, z', result, getA, stateA, accountA, roomA, outcome⟩ :=
        busy_data_tail_size stateM buffersM statusM levelM strategyM pointerM memory wrap bits (readyM left)
          (input_valid_accounting_output inputValid accountM) companionM clean run
      have fillM : fillEnd dm = fillEnd d := by rw [fields]; rfl
      have moved : produced + heldBytes dm = heldBytes d := by
        have bitsEq : dm.bi_valid = d.bi_valid := by rw [fields]
        unfold heldBytes
        rw [bitsEq]
        change dm.pending.toNat + produced = d.pending.toNat at pendingCount
        omega
      rw [fillM] at outcome
      refine ⟨0 + used, produced + laterProduced, z', result, getA, stateA,
        stream_accounting_trans accountM accountA, roomA, ?_⟩
      rw [Nat.zero_add]
      exact outcome.prepend moved

end Zlib.Deflate.Engine.Proofs
