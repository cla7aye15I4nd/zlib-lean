import ZlibF.Proof.«deflate.c.engine.flush-loop-phase»
import ZlibF.Proof.«deflate.c.engine.flush-default-cost»
import ZlibF.Proof.«deflate.c.engine.counter-effects»

/-! # The size of a block flush, in bytes

`FLUSH_BLOCK_ONLY` runs `_tr_flush_block`, moves `block_start` and publishes pending bytes. At a
flush with no pending byte, the bytes delivered by the publication, the bytes still pending and the
held bits rounded up make exactly the held bits before the flush, the block tag and the body,
rounded up. With `flush_default_cost` this is the per-block step of the size ledger.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt natBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of `FLUSH_BLOCK_ONLY`.** Under the hypotheses of `flush_macro_loop_execution`, the
macro delivers `produced` bytes, and `produced`, the pending bytes and the held bits after it,
rounded up, are the held bits before, the tag and the body, rounded up; the body is bounded as in
`flush_default_cost`. -/
theorem flush_macro_size {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (after : Heap) (z' : ZStream) (result : DeflateState) (produced : Nat) (body : List Bool),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamAccounting z z' 0 produced ∧
      result.block_start = d.strstart.toUInt64.toInt64 ∧
      (result.match_length = d.match_length ∧ result.match_start = d.match_start ∧ result.strstart = d.strstart) ∧
      result.sym_next = 0 ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 =
        (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ∧
      (defaultStoredSource d w = .null → 3 + body.length ≤ 8 * ((fixedCost xs + 10) / 8)) ∧
      (defaultStoredSource d w ≠ .null →
        (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ≤
          (d.bi_valid.toInt.toNat + 7) / 8 + represented xs + 5) ∧
      (last = true → result.bi_valid.toInt = 0) := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, _kind, _body, _padding, run, goodE, treesE, buffersE,
    accountE, _sizesE, _storageE, ledgerE, _clearE, sizeE, _boundE, cursorE, _finalE, _kindBound,
    _padBound, _padNone, _storedPad, _outputE, _grammar⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  obtain ⟨zc, afterC, resultC, nextC, kind, body, padding, runC, goodC, _treesC, _kindC, padBound, padNone,
    outputC, nullCost, storedCost⟩ :=
    flush_default_cost (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  -- the two runs are one run
  have sameHeap : afterC = ready := (Prod.mk.inj (Except.ok.inj (runC.symm.trans run))).2
  subst sameHeap
  have sameState : resultC = emitted := Option.some.inj (goodC.live.hs.symm.trans goodE.live.hs)
  subst sameState
  -- the bits after the block
  have lengths := congrArg List.length outputC
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append, Zlib.Trees.Proofs.Out.natBits_length,
    pending, UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at lengths
  have held := Zlib.Trees.Proofs.Out.outBits_length
  have final : last = true → resultC.bi_valid.toInt = 0 := _finalE
  have frame := flush_default_run_frame (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
    win get range balance accounted view last run goodE.live.hs
  let updated : DeflateState := { resultC with block_start := resultC.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, _sizesU, _storageU⟩ :=
    flush_block_start_engine (ob := ob) goodE treesE buffersE
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * resultC.pending.toNat + resultC.bi_valid.toInt.toNat ≤ 524288
    omega
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, _buffersA, accountA,
    _sizesA, _storageA, _copied, published, _low, validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
    flush_pending_raw_bits goodU treesU buffersU pointerE cursorE roomU
  have startStr : resultC.strstart = d.strstart := by rw [frame]
  have startA : result.block_start = d.strstart.toUInt64.toInt64 := by
    rw [fieldsA]
    change resultC.strstart.toUInt64.toInt64 = _
    rw [startStr]
  have keep : result.match_length = d.match_length ∧ result.match_start = d.match_start ∧
      result.strstart = d.strstart := by
    rw [fieldsA]
    change resultC.match_length = d.match_length ∧ resultC.match_start = d.match_start ∧
      resultC.strstart = d.strstart
    rw [frame]
    exact ⟨rfl, rfl, rfl⟩
  have emptied : result.sym_next = 0 := by
    rw [fieldsA]
    change resultC.sym_next = 0
    have count := ledgerE.count
    simp only [List.length_nil, Nat.mul_zero] at count
    exact UInt32.toNat_inj.mp count
  refine ⟨after, z', result, produced, body, ?_, goodA, ?_, startA, keep, emptied, ?_, nullCost, storedCost, ?_⟩
  · have streamRead : rd (some (.tab ds)) (·.strm) (setD afterC ds updated) =
        .ok (some r, setD afterC ds updated) := by
      simp only [rdD_eq, setD_dstates_same]
      rw [show updated.strm = some r from goodE.live.back]
    rw [flush_block_only_arguments_source, bind_app, arguments]
    simp only [bind_app, run, updateRun]
    change (rd (some (.tab ds)) (·.strm) >>= fun strm => flush_pending strm)
      (setD afterC ds updated) = .ok ((), after)
    rw [bind_app, streamRead]
    exact flush
  · simpa only [Nat.zero_add, Nat.add_zero] using stream_accounting_trans accountE accountA
  · change result.pending.toNat + produced = resultC.pending.toNat + resultC.bi_valid.toInt.toNat / 8 at published
    change result.bi_valid.toInt.toNat = resultC.bi_valid.toInt.toNat % 8 at validA
    cases last with
    | false =>
      have empty := padNone rfl
      subst empty
      simp only [List.length_nil, Nat.add_zero] at lengths
      omega
    | true =>
      have aligned := final rfl
      have zero : resultC.bi_valid.toInt.toNat = 0 := by rw [aligned]; rfl
      rw [zero] at lengths validA published
      omega
  · intro isLast
    have aligned := final isLast
    have zero : resultC.bi_valid.toInt.toNat = 0 := by rw [aligned]; rfl
    change result.bi_valid.toInt.toNat = resultC.bi_valid.toInt.toNat % 8 at validA
    rw [zero] at validA
    have nonneg := goodA.inv.bits.1
    omega

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **The size of an established `FLUSH_BLOCK` run** from a content boundary with no pending byte:
the delivered bytes, the pending bytes and the held bits after it (rounded up) are the held bits
before, the tag and a body bounded as in `flush_default_cost`. -/
theorem flush_control_run_size_effects {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z z' : ZStream} {d d' : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool)
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (ret, after))
    (live : r.get after = some z') (state : after.dstates ds = some d')
    (account : StreamAccounting z z' 0 produced) :
    ∃ (w : Nat) (body : List Bool),
      d'.block_start = d.strstart.toUInt64.toInt64 ∧
      (d'.match_length = d.match_length ∧ d'.match_start = d.match_start ∧ d'.strstart = d.strstart) ∧
      d'.sym_next = 0 ∧
      produced + d'.pending.toNat + (d'.bi_valid.toInt.toNat + 7) / 8 =
        (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ∧
      (defaultStoredSource d w = .null → 3 + body.length ≤ 8 * ((fixedCost xs + 10) / 8)) ∧
      (defaultStoredSource d w ≠ .null →
        (d.bi_valid.toInt.toNat + 3 + body.length + 7) / 8 ≤
          (d.bi_valid.toInt.toNat + 7) / 8 + represented xs + 5) ∧
      (last = true → d'.bi_valid.toInt = 0) := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨other, otherZ, otherD, amount, body, macroRun, goodA, accountA, startA, keep, emptied, size, nullCost, storedCost, final⟩ :=
    flush_macro_size boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 accounted0 view last
  let control : Option block_state :=
    if otherZ.avail_out == 0 then
      if last then
        if otherD.pending != 0 || otherD.wrap != 0 then some finish_started else none
      else some need_more
    else none
  have controlRun : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (control, other) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, macroRun, ldDeflateState_tab goodA.live.hs, goodA.live.back, zrd_eq, goodA.live.hz]
    by_cases empty : (otherZ.avail_out == 0) = true <;>
      by_cases queued : (otherD.pending != 0 || otherD.wrap != 0) = true <;>
      cases last <;> simp [control, empty, queued, pure_app]
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (controlRun.symm.trans run))).2
  subst heaps
  have sameZ : otherZ = z' := Option.some.inj (goodA.live.hz.symm.trans live)
  subst sameZ
  have sameD : otherD = d' := Option.some.inj (goodA.live.hs.symm.trans state)
  subst sameD
  have count : produced = amount := (stream_accounting_counts_unique account accountA).2
  subst count
  exact ⟨w, body, startA, keep, emptied, size, nullCost, storedCost, final⟩

end Zlib.Deflate.Engine.Proofs
