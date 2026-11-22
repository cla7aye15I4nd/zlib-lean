import ZlibF.Proof.«deflate.c.universal-call-stageframe»
import ZlibF.Proof.«deflate.c.universal-call-lift»
import ZlibF.Proof.«deflate.c.engine.pending-bits»
import ZlibF.Proof.«deflate.c.engine.pending-resume»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-resume»

/-!
# deflate.c: the entry flush with an advanced pending cursor

At a call boundary with bytes pending, the previous call stopped on a full output, so
`pending_out` may lie past `pending_buf`. The flush lemmas of the header and trailer phases assume
the base cursor. Here `flush_pending` from `DInv` is proved for any cursor that `DBlocks.pout`
allows, for a raw and for a foreign output view: the invariant holds afterwards, the call is a
stage (`StageFrame`), and it copies `min pending avail_out` bytes, at least one. Between calls at
most seven bits are held (`Shape.biValid`), so `_tr_flush_bits` writes nothing. The copy rests on
the cursor-general resume lemmas (`flush_pending_resume_raw_bits`,
`flush_pending_resume_foreign_bits`).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The pending bits of a state, read at its cursor. -/
theorem pending_bits_of_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) : ∃ bits, PendingBits h d bits := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  exact ⟨_, pending_bits_slice cursor get (by rw [size, ← blocks.psize]; exact bound)⟩

/-- **A low-bit `flush_pending` at any cursor** is a stage (`StageFrame.of_flush` without the base
cursor). -/
theorem StageFrame.of_flush_low {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream}
    {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0) (low : d.bi_valid.toInt < 8) (out : z.next_out ≠ .null)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    StageFrame h after r ds pb d z z' produced := by
  obtain ⟨before, bits⟩ := pending_bits_of_good good
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨output, outGet, _, _, _⟩ := caller_raw_output good buffers ptr
    obtain ⟨pb', _, after', _, _, _, _, base, run', _, _, _, sizes, storage, _⟩ :=
      flush_pending_resume_raw_bits good buffers ptr low bits
    have key : pb' = pb := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using base.symm
    subst pb'
    have same : after' = after := (Prod.mk.inj (Except.ok.inj (run'.symm.trans run))).2
    subst same
    have totals := flush_pending_low_run_counter_effects good buffers ptr low run live account
    obtain ⟨next, getN, sizeN, keep⟩ :=
      flush_pending_low_run_output_interval good buffers ptr low run live account outGet
    have frame : Frame h after' (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b = ob) := by
      apply full_frame_weaken (storage.private_frame pbuf)
      intro b changed
      rcases changed with root | owned | output
      · exact Or.inl (Or.inl root)
      · exact Or.inl (Or.inr owned)
      · exact Or.inr output
    have buffer : BufferFrame h after' (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
        [⟨z.next_out, produced⟩] := by
      rw [ptr]
      exact raw_buffer_frame_of_interval frame storage.shape good.uniq outGet getN (sizes.ro (.blk ob)) sizeN keep
    refine ⟨⟨⟨account, by simpa using totals.1, totals.2, buffer, full_shape_live_change storage.shape,
      storage.nalloc⟩, storage.shape⟩, fun ob' root => ?_⟩
    rw [ptr] at root
    change ob' = ob at root
    subst root
    exact storage
  · have storage := low_foreign_pending_run_storage good buffers pbuf ptr low run
    obtain ⟨_, produced2, after', z2, _, _, _, _, run', good2, _, account2, _, _, _, _, _, _, _, _, _, _, bufferA⟩ :=
      flush_pending_resume_foreign_bits good buffers ptr low bits
    have same : after = after' := (Prod.mk.inj (Except.ok.inj (run.symm.trans run'))).2
    subst same
    have sameZ : z2 = z' := Option.some.inj (good2.live.hz.symm.trans live)
    subst sameZ
    have sameP : produced = produced2 := by
      have a1 := account.2.2.2.1; have a2 := account2.2.2.2.1; omega
    subst sameP
    have scalars := flush_pending_low_foreign_run_scalar_effects good buffers ptr low run live account
    have buffer : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
        [⟨z.next_out, produced⟩] := by
      refine ⟨full_frame_weaken bufferA.1 ?_, bufferA.2⟩
      intro b changed
      rcases changed with root | same
      · exact Or.inl root
      · exact Or.inr (Or.inl same)
    refine ⟨⟨⟨account, by simpa using scalars.2.1, scalars.2.2.1, buffer, full_shape_live_change storage.shape,
      storage.nalloc⟩, storage.shape⟩, fun ob' root => ?_⟩
    rw [ptr] at root
    change ob' = ob at root
    subst root
    exact storage

/-- The run of a low-bit `flush_pending` that copies `n ≠ 0` bytes from the cursor `po`: its state
is `pendingState` (the cursor advanced by `n`, or reset when nothing is left). -/
theorem flush_cursor_state {h after : Heap} {r : ZStreamRef} {ds pb po : Nat} {z z' : ZStream}
    {d d' : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pbuf : d.pending_buf = .ref (.blk pb) 0) (cursor : d.pending_out = .ref (.blk pb) po)
    (low : d.bi_valid.toInt < 8) (out : z.next_out ≠ .null)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0)
    (run : flush_pending (some r) h = .ok ((), after)) (goodA : DGood after r ds z' d') :
    d' = pendingState d (.ref (.blk pb) (po + (pendingLen d.pending z.avail_out).toNat))
      (pendingLen d.pending z.avail_out) := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have key : b = pb := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po', cursor', bound⟩ := blocks.pout
  have samePo : po' = po := by simpa only [cursor, Ptr.ref.injEq, true_and] using cursor'.symm
  subst po'
  have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers ptr
    have separate : ob ≠ pb := by
      intro e; subst e; exact outside (Or.inr (Or.inr (Or.inr (Or.inr pbuf))))
    have run0 := flush_pending_low_raw good.live.hz good.live.zst good.live.hs low ptr cursor outGet get writable
      separate outBound sourceBound nonzero
    have heaps := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have state := goodA.live.hs
    rw [← heaps] at state
    simp only [setD_dstates_same, Option.some.injEq] at state
    exact state.symm
  · obtain ⟨foreign, outGet, outBound, different, _, _⟩ := caller_foreign_output good buffers ptr
    have run0 := flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low ptr cursor outGet get
      (Ne.symm different) outBound sourceBound nonzero
    have heaps := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have state := goodA.live.hs
    rw [← heaps] at state
    simp only [setD_dstates_same, Option.some.injEq] at state
    exact state.symm

/-- The output result of a low-bit `flush_pending` at any cursor, for a raw or a foreign output:
the run, the new representation, the caller buffers and the counts. -/
theorem flush_cursor_run {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (low : d.bi_valid.toInt < 8)
    (out : z.next_out ≠ .null) :
    ∃ produced after z' d', flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' d' ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      produced = min d.pending.toNat z.avail_out.toNat := by
  obtain ⟨before, bits⟩ := pending_bits_of_good good
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good buffers out
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · obtain ⟨_, produced, after, z', d', _, _, _, run, goodA, buffersA, account, _, _, count, _⟩ :=
      flush_pending_resume_raw_bits good buffers ptr low bits
    exact ⟨produced, after, z', d', run, goodA, buffersA, account, count⟩
  · obtain ⟨_, produced, after, z', d', _, _, _, run, goodA, buffersA, account, _, _, count, _⟩ :=
      flush_pending_resume_foreign_bits good buffers ptr low bits
    exact ⟨produced, after, z', d', run, goodA, buffersA, account, count⟩

end Zlib.Deflate.Universal.Call
