import ZlibF.Proof.«deflate.c.engine.call-size-tail»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-publication»

/-! # The size of the trailer into a foreign output pointer

The twin of `trailer_run_size` for a caller output pointer into another deflate state's `depth`
array.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of the trailer.** An established `publicFinishTail` run with the trailer owed and
nothing pending or held delivers `produced` bytes and holds `heldBytes result` after it, 4 in all,
and the trailer is written. -/
theorem foreign_trailer_run_size {h after : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {rc : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0)
    (run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after)) :
    ∃ produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      produced + heldBytes result = 4 ∧ result.wrap = -1 ∧ result.status = d.status ∧
      rc = (if result.pending != 0 then Z_OK else Z_STREAM_END) ∧ (rc = Z_OK → z'.avail_out = 0) := by
  let next := zlibTrailerBuffer buf z.adler
  let emitted := { d with pending := 4 }
  obtain ⟨write, goodE, treesE, buffersE, _sizesE, _storageE, _values⟩ :=
    zlib_trailer_write (ob := pb) good trees buffers pending cursor
  obtain ⟨produced, middle, z', result, _written, _remaining, flush, goodM, _buffersM, account, _sizesM,
    amount, left, fields, _bytesM, _pendingM, _outputM, _frameM⟩ :=
    flush_pending_low_foreign_caller_bits_frame goodE treesE buffersE (by change d.bi_valid.toInt < 8; omega)
      cursor pointer
  have wrapM : result.wrap = 1 := by rw [fields]; exact wrap
  have bitsM : result.bi_valid.toInt = 0 := by rw [fields]; exact bits
  have statusM : result.status = d.status := by rw [fields]
  let final := setD middle ds { result with wrap := -1 }
  have goodF := trailer_wrap_good goodM wrapM
  have tested : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
      .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), final) := by
    have getW : rd (some (.tab ds)) (·.wrap) h = .ok (1, h) := by
      simp only [rdD_eq, good.live.hs, wrap]
    have getWM : rd (some (.tab ds)) (·.wrap) middle = .ok (1, middle) := by
      simp only [rdD_eq, goodM.live.hs, wrapM]
    have negative : ineg (1 : Int32) = pure (-1) := by rfl
    unfold publicFinishTail
    simp only [bind_app, pure_app, show (Z_FINISH != Z_FINISH) = false from rfl,
      Bool.false_eq_true, ite_false, getW,
      show ¬ (1 : Int32) ≤ 0 from by decide, show ((1 : Int32) == 2) = false from rfl,
      write, flush, getWM, show (1 : Int32) > 0 from by decide,
      ite_true, negative, wrD_eq, goodM.live.hs]
    simp only [rdD_eq, setD_dstates_same]
    rfl
  obtain ⟨rcs, heaps⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run))
  subst heaps
  have roomF : rc = Z_OK → z'.avail_out = 0 := by
    intro ok
    have queued : result.pending ≠ 0 := by
      intro zero
      rw [← rcs, zero] at ok
      cases ok
    have positive : 0 < result.pending.toNat := by
      have nonzero : result.pending.toNat ≠ 0 := fun eq => queued (UInt64.toNat_inj.mp eq)
      omega
    have count : result.pending.toNat + produced = 4 := left
    change produced = min 4 z.avail_out.toNat at amount
    have balance := account.2.2.2.1
    apply UInt32.toNat_inj.mp
    change z'.avail_out.toNat = 0
    omega
  refine ⟨produced, z', { result with wrap := -1 }, goodF.live.hz, goodF.live.hs, goodF, account, ?_, rfl, statusM,
    rcs.symm, roomF⟩
  have count : result.pending.toNat + produced = 4 := left
  unfold heldBytes
  change produced + (result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8) = 4
  rw [bitsM]
  simp only [Int.toNat_zero, Nat.zero_add, Nat.reduceDiv, Nat.add_zero]
  omega

end Zlib.Deflate.Engine.Proofs
