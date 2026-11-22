import ZlibF.Proof.«deflate.c.engine.call-size-first»
import ZlibF.Proof.«deflate.c.engine.call-size-finishing-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered-joint-next»
import ZlibF.Proof.«deflate.c.engine.public-dispatch»

/-! # The size of the first call into a foreign output pointer

The twin of `first_call_size` for a caller output pointer into another deflate state's `depth`
array. The header is written by `publicZlibHeader` for either flush; when it is all delivered the
data part follows.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of the first call into a foreign output pointer.** -/
theorem foreign_first_call_size {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig} {flush rc : Int32}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input origin base [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (output : 0 < z.avail_out.toNat)
    (memory : config.memory.toNat = 16384) (bits : config.windowBits = 15)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (companion : SizeCompanion d [])
    (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    ∃ used produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      StreamAccounting z z' used produced ∧
      (flush = Z_FINISH → rc = Z_OK → z'.avail_out = 0) ∧
      BusySizeOutcome after r ds z' result flush rc (origin + fillEnd d + used) base 2 produced := by
  have nonnull : z.next_out ≠ .null := by rw [pointer]; intro eq; cases eq
  have positive : z.avail_out ≠ 0 := by intro zero; rw [zero] at output; cases output
  have entry : deflate (some r) flush h =
      publicZlibHeader (some r) (some (.tab ds)) (publicDataTail (some r) (some (.tab ds)) flush)
        (setD h ds { d with last_flush := flush }) := by
    rcases clean with noFlush | finish
    · subst noFlush
      exact public_default_entry initial nonnull positive valid
    · subst finish
      exact public_default_finish_initial_entry initial nonnull positive valid
  obtain ⟨oldD, pb, buf, trees⟩ := initial.good.trees
  have sameD : oldD = d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have wrapConfig : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have strategyConfig : d.strategy = 0 := initial.strategy
  have bits0 : d.bi_valid.toInt = 0 := by rw [initial.bits]; rfl
  obtain ⟨produced, after1, z1, d1, _written, _remaining, header, state1, good1, buffers1, account1, _sizes,
      amount, left, status1, bits1, _last1, frame1, _rest⟩ :=
    foreign_zlib_header_buffered_joint_next (d := { d with last_flush := flush })
      (last_flush_buffered_boundary boundary flush) (last_flush_trees trees flush)
      (last_flush_buffers initial.good buffers flush) pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut bits0
      (publicDataTail (some r) (some (.tab ds)) flush)
  rw [entry, header] at run
  have companion1 : SizeCompanion d1 [] := by rw [frame1]; exact companion
  have fill1 : fillEnd d1 = fillEnd d := by rw [frame1]; rfl
  have held1 : heldBytes d1 = d1.pending.toNat := by
    unfold heldBytes
    rw [bits1]
    rfl
  by_cases queued : (d1.pending != 0) = true
  · rw [ite_eq_left queued] at run
    obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj run)
    subst heaps
    have room1 : z1.avail_out = 0 := by
      have pendingPos : 0 < d1.pending.toNat := by
        have nonzero : d1.pending ≠ 0 := by simpa using queued
        have ne : d1.pending.toNat ≠ 0 := fun eq => nonzero (UInt64.toNat_inj.mp eq)
        omega
      have balance := account1.2.2.2.1
      apply UInt32.toNat_inj.mp
      change z1.avail_out.toNat = 0
      omega
    refine ⟨0, produced, z1, d1, good1.live.hz, good1.live.hs, account1, fun _ _ => room1,
      Or.inl ⟨status1, input, origin, base, [], state1.toContentBoundary, ?_, companion1, ?_⟩⟩
    · rw [fill1]; rfl
    · rw [held1]
      omega
  · rw [ite_eq_right queued] at run
    have none : d1.pending = 0 := by simpa using queued
    have publish1 : PublishReady d1 :=
      ⟨none, state1.empty_cursor none, by rw [bits1]; decide⟩
    have level1 : d1.level = 6 := by rw [frame1]; exact level
    have strategy1 : d1.strategy = 0 := by rw [frame1]; exact strategyConfig
    have pointer1 : z1.next_out = .ref (.dstate_depth owner) (oo + produced) := by
      rw [account1.2.2.2.2.2.1, pointer]
      rfl
    obtain ⟨used, laterProduced, z', result, getA, stateA, accountA, roomA, outcome⟩ :=
      foreign_busy_data_tail_size state1 buffers1 status1 level1 strategy1 pointer1 memory wrapConfig bits
        publish1 (input_valid_accounting_output valid account1) companion1 clean run
    have moved : produced + heldBytes d1 = 2 := by
      rw [held1]
      omega
    rw [fill1] at outcome
    refine ⟨0 + used, produced + laterProduced, z', result, getA, stateA,
      stream_accounting_trans account1 accountA, roomA, ?_⟩
    rw [Nat.zero_add]
    exact outcome.prepend moved

end Zlib.Deflate.Engine.Proofs
