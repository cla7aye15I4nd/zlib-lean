import ZlibF.Proof.«deflate.c.engine.call-size»
import ZlibF.Proof.«deflate.c.engine.trailer-counters»

/-! # The size of the trailer and of the pending flush

`publicFinishTail` with the trailer still owed queues the 4 trailer bytes and publishes what fits:
the delivered bytes and the pending bytes after it are 4, and the trailer is no longer owed.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `M` runs split at a bind. -/
theorem size_bind_split {α β : Type} {m : M α} {f : α → M β} {h H : Heap} {v : β}
    (e : (m >>= f) h = .ok (v, H)) : ∃ a h1, m h = .ok (a, h1) ∧ f a h1 = .ok (v, H) := by
  rw [bind_app] at e
  cases hm : m h with
  | error err => rw [hm] at e; cases e
  | ok p => obtain ⟨a, h1⟩ := p; rw [hm] at e; exact ⟨a, h1, rfl, e⟩

/-- **The size of the trailer.** An established `publicFinishTail` run with the trailer owed and
nothing pending or held delivers `produced` bytes and holds `heldBytes result` after it, 4 in all,
and the trailer is written. -/
theorem trailer_run_size {h after : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {rc : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0)
    (run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h = .ok (rc, after)) :
    ∃ produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      produced + heldBytes result = 4 ∧ result.wrap = -1 ∧ result.status = d.status ∧
      rc = (if result.pending != 0 then Z_OK else Z_STREAM_END) ∧ (rc = Z_OK → z'.avail_out = 0) := by
  let next := zlibTrailerBuffer buf z.adler
  let emitted := { d with pending := 4 }
  obtain ⟨write, goodE, treesE, buffersE, _sizesE, _storageE, _values⟩ :=
    zlib_trailer_write (ob := ob) good trees buffers pending cursor
  obtain ⟨output, getOutput, writable, outputBound, outside⟩ := caller_raw_output goodE buffersE pointer
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr treesE.base.pbuf))))
  obtain ⟨produced, middle, z', result, _written, _remaining, flush, goodM, account, _sizesM,
    amount, left, fields, _bytesM, _pendingM, _outputM, _storageM⟩ :=
    flush_pending_low_raw_bits_storage goodE treesE (by change d.bi_valid.toInt < 8; omega)
      cursor pointer getOutput writable separate outputBound
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
