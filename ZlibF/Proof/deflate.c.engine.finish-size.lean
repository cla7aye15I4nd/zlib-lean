import ZlibF.Proof.«deflate.c.engine.loop-size»
import ZlibF.Proof.«deflate.c.engine.finish-tail-counters»

/-! # The size of the final block of `deflate_slow`

After the loop breaks on `Z_FINISH`, `deflate_slow` settles a pending literal, records `insert`
and flushes the final block. The block covers the rest of the window. With the stored fallback it
costs at most its bytes plus 5; without it (after a slide) the block covers at least 32506 bytes in
at most 16383 symbols of level-6 quality, and the fixed code costs at most its bytes.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The final block in bytes.** The bytes a block flush produces, plus what it holds after, are
at most what it held before plus the block's bytes plus 5. -/
theorem final_block_cost {ys : List Symbol} {source : Prop} {bits body produced held : Nat}
    (size : produced + held = (bits + 3 + body + 7) / 8)
    (nullCost : source → 3 + body ≤ 8 * ((fixedCost ys + 10) / 8))
    (storedCost : ¬ source → (bits + 3 + body + 7) / 8 ≤ (bits + 7) / 8 + represented ys + 5)
    (valid : ∀ s ∈ ys, s.Valid)
    (quality : ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (symbols : ys.length ≤ 16383) (large : source → 32506 ≤ represented ys) :
    produced + held ≤ (bits + 7) / 8 + represented ys + 5 := by
  by_cases present : source
  · have cheap := slid_fixed_cost valid quality symbols (large present)
    have bound := nullCost present
    omega
  · have bound := storedCost present
    omega

/-- **The size of the `Z_FINISH` tail of `deflate_slow`.** From the strategy boundary where the
loop broke (empty lookahead, nothing pending, a 32 KiB window, the companion), an established run
of the tail delivers `produced` bytes and holds `heldBytes result` after, at most the held bytes
before plus the uncovered bytes plus 5. -/
theorem slow_eof_finish_size {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (wrap : d.wrap = 1)
    (window : d.w_size.toNat = 32768) (companion : SizeCompanion d xs)
    (run : slowEofTail (some (.tab ds)) Z_FINISH h = .ok (ret, after)) :
    ∃ produced z' result, r.get after = some z' ∧ after.dstates ds = some result ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧
      ((ret = finish_started ∧ z'.avail_out = 0) ∨ (ret = finish_done ∧ 0 < z'.avail_out.toNat)) ∧
      result.bi_valid.toInt = 0 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      result.wrap = d.wrap ∧
      base ≤ origin + fillEnd d ∧
      produced + heldBytes result + base ≤ heldBytes d + (origin + fillEnd d) + 5 := by
  obtain ⟨quality, _candidate, floor⟩ := companion
  obtain ⟨settledHeap, settled, ys, settleRun, settledBoundary, settledFrontier, settledBuffers,
      settledFlag, settledLook, settledStart, settledCount, settledClear, settledConfig, settledFrame, shape⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  obtain ⟨insertRun, insertedBoundary, _insertedFrontier, insertedConfig⟩ :=
    eof_insert_content_boundary settledBoundary settledFrontier settledLook
  have owned := stream_owned_keys settledBoundary.good insertedBoundary.good rfl rfl rfl rfl
  have insertedBuffers := stream_buffers_private_read settledBoundary.good.live.hz insertedBoundary.good.live.hz
    settledBuffers (byte_frame_setD settledHeap ds (eofInsert settled))
    (fun k equal => (stream_owned_deflate settledBoundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  have configI : ConfigFrame d (eofInsert settled) := settledConfig.trans insertedConfig
  have clearI : BlockInit.BlockClear (eofInsert settled) := ⟨settledClear.bl, settledClear.opt, settledClear.fixed⟩
  have bitFrame : settled.bi_valid = d.bi_valid := by rw [settledFrame]
  have startFrame : settled.block_start = d.block_start := by rw [settledFrame]
  have bitsI : (eofInsert settled).bi_valid.toInt ≤ 7 := by
    change settled.bi_valid.toInt ≤ 7
    rw [bitFrame]
    have low := boundary.bits
    omega
  have cursorI : (eofInsert settled).pending_out = (eofInsert settled).pending_buf := by
    change settled.pending_out = settled.pending_buf; rw [settledFrame]; exact cursor
  have pendingI : (eofInsert settled).pending = 0 := by
    change settled.pending = 0; rw [settledFrame]; exact pending
  have memoryI : (eofInsert settled).lit_bufsize.toNat = 16384 := by rw [configI.memory]; exact memory
  have positiveI : 0 < (eofInsert settled).level.toInt := by rw [configI.level]; exact positive
  have wrapI : (eofInsert settled).wrap = 1 := by rw [configI.wrap]; exact wrap
  obtain ⟨amount, other, otherZ, otherD, controlRun, boundaryA, buffersA, accountA, _clearA, frameA, _lowA, phaseA⟩ :=
    flush_final_loop_boundary insertedBoundary insertedBuffers positiveI pointer cursorI memoryI pendingI
      bitsI clearI settledFlag wrapI
  have tailRun : finish_tail (some (.tab ds)) Z_FINISH (setD settledHeap ds (eofInsert settled)) =
      .ok ((if otherZ.avail_out == 0 then finish_started else finish_done), other) := by
    unfold finish_tail
    simp only [beq_self_eq_true, ite_true, bind_app, controlRun]
    by_cases emptyOut : (otherZ.avail_out == 0) = true <;> simp [emptyOut, pure_app]
  have actualRun : slowEofTail (some (.tab ds)) Z_FINISH h =
      .ok ((if otherZ.avail_out == 0 then finish_started else finish_done), other) := by
    unfold slowEofTail
    rw [bind_app, settleRun]
    simp only []
    rw [bind_app, insertRun]
    exact tailRun
  obtain ⟨rets, heaps⟩ := Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))
  subst heaps
  have returns : (ret = finish_started ∧ otherZ.avail_out = 0) ∨
      (ret = finish_done ∧ 0 < otherZ.avail_out.toNat) := by
    rw [← rets]
    by_cases emptyOut : otherZ.avail_out = 0
    · exact Or.inl ⟨by simp [emptyOut], emptyOut⟩
    · refine Or.inr ⟨by simp [emptyOut], ?_⟩
      have nonzero : otherZ.avail_out.toNat ≠ 0 := fun zero => emptyOut (UInt32.toNat_inj.mp zero)
      omega
  obtain ⟨w, body, _startA, _keep, _emptied, size, nullCost, storedCost, final⟩ :=
    flush_control_run_size_effects insertedBoundary insertedBuffers positiveI pointer cursorI memoryI pendingI
      bitsI clearI settledFlag true controlRun boundaryA.good.live.hz boundaryA.good.live.hs accountA
  obtain ⟨_pbI, _bufI, treesI, ledgerI, _balanceI⟩ := insertedBoundary.symbols
  have countI := ledgerI.count
  have endI := treesI.base.sym_end
  have symbols : ys.length ≤ 16383 := by
    have bound : (eofInsert settled).sym_next.toNat ≤ (eofInsert settled).sym_end.toNat := settledCount
    omega
  have qualityY : ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096 := by
    rcases shape with same | ⟨wa, extended⟩
    · rw [same]; exact quality
    · rw [extended]
      intro s member
      rcases List.mem_append.mp member with old | new
      · exact quality s old
      · rw [List.mem_singleton] at new
        rw [new]
        intro nonzero
        exact absurd rfl nonzero
  have accountedI : base + represented ys = origin + (eofInsert settled).strstart.toNat := by
    have flagI : (eofInsert settled).match_available = 0 := settledFlag
    have acc := insertedBoundary.accounted
    simp only [pendingCredit, flagI, ↓reduceIte, Nat.add_zero] at acc
    omega
  have strstartI : (eofInsert settled).strstart = d.strstart := settledStart
  have baseEq := content_base_eq insertedBoundary
  have startI : (eofInsert settled).block_start = d.block_start := startFrame
  have large : defaultStoredSource (eofInsert settled) w = .null → 32506 ≤ represented ys := by
    intro present
    have negative : (eofInsert settled).block_start.toInt < 0 := by
      unfold defaultStoredSource at present
      by_cases nonneg : 0 ≤ (eofInsert settled).block_start.toInt
      · simp [nonneg] at present
      · omega
    rw [startI] at negative baseEq
    have high := floor negative
    rw [window] at high
    rw [strstartI] at accountedI
    omega
  have bitsEq : (eofInsert settled).bi_valid = d.bi_valid := bitFrame
  rw [bitsEq] at size storedCost
  have cost := final_block_cost (source := defaultStoredSource (eofInsert settled) w = .null) size nullCost storedCost
    ledgerI.valid qualityY symbols large
  have fill : fillEnd d = d.strstart.toNat := by
    simp only [fillEnd, empty, show (0 : UInt32).toNat = 0 from rfl, Nat.add_zero]
  have wrapA : otherD.wrap = d.wrap := by
    rw [frameA]
    change settled.wrap = d.wrap
    rw [settledFrame]
  refine ⟨amount, otherZ, otherD, boundaryA.good.live.hz, boundaryA.good.live.hs, boundaryA.good, buffersA,
    accountA, returns, final rfl, phaseA, wrapA, ?_, ?_⟩
  · rw [fill]
    rw [strstartI] at accountedI
    omega
  unfold heldBytes
  rw [pending, fill]
  rw [strstartI] at accountedI
  omega

end Zlib.Deflate.Engine.Proofs
