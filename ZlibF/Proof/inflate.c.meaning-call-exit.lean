import ZlibF.Proof.«inflate.c.meaning-call-entry»
import ZlibF.Proof.«inflate.c.meaning-leave»
import ZlibF.Proof.«inflate.c.meaning-format»
import ZlibF.Proof.«inflate.c.meaning-rebuffer»
import ZlibF.Proof.«inflate.c.call-default»
import ZlibF.Proof.«inflate.c.caller-buffers»
import ZlibF.Proof.«inflate.c.stream-frame-run»
import ZlibF.Proof.«inflate.c.leave-finalize»

/-!
# inflate.c: the exit row of one `inflate` call (`CallExit`)

After the mode loop of an accepted call ends (`LoopExit`), the rest of `inflate()` runs:
`inf_leave` for a leave exit, or the direct `return Z_NEED_DICT` from `DICT`, then
`free(hbuf)`. `call_exit` gives `ParseMeaning` of the history after the call.

* `callExit_split`: the actual call is the loop run, then `inflate_leave` or the direct return,
  then the release of the local buffer (`freeWin` of the block `h.nextBlk`).
* `callExit_after`: the safety proof of the call (`inflate_default_origin_public_memory_contract`)
  gives the invariant of the heap after the call, the stream accounting and the modes of the
  return codes. The run is deterministic, so these are facts of the observed call.
* `callExit_stage`: the common end of a leave with `LoopMatches` and of the dictionary request:
  the input read is `used` bytes, the output is the call's output `callOut`, and the stage
  clause moves to the heap after the call (`SameRefs`).
* `callExit_bad`: the common end of the `BAD` exit: the input read is doomed.
* `callExit_leave`, `callExit_leaveBad`, `callExit_needDict`: the three exits of the loop.
* A call refused at entry with a `NULL` output pointer is `call_refused`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-! ## Small facts -/

/-- `free` of the start of a byte block is `freeWin`. -/
theorem callExit_freeB {H H' : Heap} {n : Nat} {u : Unit}
    (run : freeB (.ref (.blk n) 0) H = .ok (u, H')) : H' = freeWin H (.ref (.blk n) 0) := by
  simp only [freeB] at run
  split at run
  · split at run
    · cases run
    · cases run
      rfl
  · cases run

/-- A byte view after freeing a block is the view before. -/
theorem callExit_freeWin_view {H : Heap} {n : Nat} {ref : BRef} {a : Array UInt8}
    (get : (Space.get (freeWin H (.ref (.blk n) 0)) ref : Option (Array UInt8)) = some a) :
    (Space.get H ref : Option (Array UInt8)) = some a := by
  cases ref with
  | blk b =>
    by_cases e : b = n
    · subst e
      change (upd H.bytes b none) b = some a at get
      rw [upd_same] at get
      cases get
    · change (upd H.bytes n none) b = some a at get
      rw [upd_ne _ _ _ _ e] at get
      exact get
  | _ => exact get

theorem callExit_get_freeWin (H : Heap) (n : Nat) (r : ZStreamRef) :
    r.get (freeWin H (.ref (.blk n) 0)) = r.get H := by
  cases r <;> rfl

/-- Freeing a block other than the window keeps the tables and the window of the state. -/
theorem callExit_sameRefs {H : Heap} {n : Nat} {s : InflateState}
    (win : WinInv (freeWin H (.ref (.blk n) 0)) s) : SameRefs H (freeWin H (.ref (.blk n) 0)) s := by
  constructor
  · intro ref _ _
    cases ref <;> rfl
  · intro ref off ptr
    rcases win.block with nullW | ⟨w, a, weq, wget, _⟩
    · rw [nullW] at ptr
      cases ptr
    · rw [weq] at ptr
      cases ptr
      have g : (Space.get (freeWin H (.ref (.blk n) 0)) (BRef.blk w) : Option (Array UInt8)) =
          some a := wget
      rw [g, callExit_freeWin_view g]

/-- Two readings of one range agree when the second heap's views are views of the first. -/
theorem callExit_bytes_eq {A B : Heap} {p : BPtr} {n : Nat} {xs ys : List UInt8}
    (one : Bytes A p n xs) (two : Bytes B p n ys)
    (views : ∀ (ref : BRef) (a : Array UInt8),
      (Space.get B ref : Option (Array UInt8)) = some a → Space.get A ref = some a) : ys = xs := by
  rcases one with ⟨null, _, empty⟩ | ⟨ref, off, array, pointer, get, _, values⟩
  · rcases two with ⟨_, _, empty2⟩ | ⟨_, _, _, pointer, _⟩
    · exact empty2.trans empty.symm
    · rw [null] at pointer
      cases pointer
  · subst pointer
    rcases two with ⟨null, _⟩ | ⟨ref2, off2, array2, pointer, get2, _, values2⟩
    · cases null
    · cases pointer
      have same : array2 = array := Option.some.inj ((views _ _ get2).symm.trans get)
      subst same
      exact values2.trans values.symm

/-- The bytes used by the call are those the loop read. -/
theorem callExit_used {used : Nat} {z z' : ZStream} {input : List UInt8} {l : IL}
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat) (inLen : input.length = z.avail_in.toNat)
    (availIn : z'.avail_in = l.have_) (inEq : l.in_.toNat = input.length) : used = loopRead l := by
  unfold loopRead
  rw [usedEq, availIn, ← inLen, ← inEq]

/-- A stage stands for a decoder outside `BAD`, `MEM` and `SYNC`. -/
theorem callExit_stage_ordinary {h : Heap} {s : InflateState} {wrap : Api.Wrap} {dict : List UInt8}
    {stage : WrapStage} (sm : StageMatches h s wrap dict stage) :
    s.mode ≠ BAD ∧ s.mode ≠ MEM ∧ s.mode ≠ SYNC := by
  have low : s.mode ≤ DONE := by
    cases stage with
    | header bytes => exact UInt32.le_trans sm.2 (by decide)
    | needDict header =>
      have m : s.mode = DICT := sm
      rw [m]
      decide
    | body header pos =>
      exact UInt32.le_trans (MeaningTrailer.body_mode_range sm.1).2 (by decide)
    | trailer header out bytes => rcases sm.1 with m | m <;> rw [m] <;> decide
    | done out =>
      have m : s.mode = DONE := sm
      rw [m]
      decide
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> rw [e] at low <;> exact absurd low (by decide)

/-! ## The call around the loop -/

/-- The actual call of an accepted call: the loop run, then `inf_leave` or the direct return,
then `free(hbuf)`. -/
theorem callExit_split {h after h1 : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} {flush rc : Int32} {exit : Ex} {regs : IL}
    (inv : InflateInv h r i z s) (nonnull : z.next_out ≠ .null)
    (inputOk : z.next_in = .null → z.avail_in = 0)
    (run : C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after))
    (erun : runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) =
      .ok ((.error exit, regs), h1)) :
    ∃ h2, ((exit = .leave ∧ inflate_leave (callCtx h r i flush) regs h1 = .ok (rc, h2)) ∨
      (∃ v, exit = .ret v ∧ rc = v ∧ h2 = h1)) ∧ after = freeWin h2 (.ref (.blk h.nextBlk) 0) := by
  have live' := Live.syncAlloc inv.good.live
  have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
    cases e1 : (z.next_out == .null) with
    | true => exact absurd (by simpa using e1) nonnull
    | false =>
      cases e2 : (z.next_in == .null) with
      | false => simp
      | true =>
        have zero := inputOk (by simpa using e2)
        simp [zero]
  unfold C.run Zlib.Inflate.inflate at run
  obtain ⟨hbuf, hA, ealloc, runA⟩ := KeepProofs.bind_ok run
  rw [allocLocalB_run h inv.good.fresh] at ealloc
  cases ealloc
  obtain ⟨res, hB, ebody, runB⟩ := KeepProofs.bind_ok runA
  obtain ⟨u, hC, efree, runC⟩ := KeepProofs.bind_ok runB
  cases runC
  simp only [bind_app, stateCheck_live live', bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok live'.hz, accepted, live'.zst, castI] at ebody
  generalize hR : (ExceptT.run (inflate_run
    { strm := some r, st := some (InflateStateRef.tab i), hbuf := syncBuf h, flush := flush })).run
      IL.init (syncAlloc h) = R at ebody
  have eR : R = .ok ((.error exit, regs), h1) := hR.symm.trans erun
  subst eR
  have freed := callExit_freeB efree
  cases exit with
  | leave =>
    dsimp only at ebody
    exact ⟨_, Or.inl ⟨rfl, ebody⟩, freed⟩
  | ret v =>
    simp only [pure_app] at ebody
    cases ebody
    exact ⟨_, Or.inr ⟨_, rfl, rfl, rfl⟩, freed⟩

/-- The heap after the call: the invariant, the stream accounting and the modes of the return
codes, from the safety proof of the same (deterministic) run. -/
theorem callExit_after {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} {flush rc : Int32} (inv : InflateInv h r i z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r)
    (run : C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after)) :
    ∃ (z' : ZStream) (s' : InflateState) (used out : Nat), InflateInv after r i z' s' ∧ StreamAccounting z z' used out ∧
      ReturnedModes rc s' := by
  obtain ⟨rc', after', stream, state, used, out, run', next, finalAllocator, _, accounting,
    _, _, _, _, _, modes, _⟩ :=
    inflate_default_origin_public_memory_contract (inv.to_origin fit) inv.alloc buffers
      (ActiveHeader.entry active inv.good.live) (ActiveHeader.record active inv.good.live) flush
  have same := Except.ok.inj (run'.symm.trans run)
  cases same
  exact ⟨stream, state, used, out.length, InflateInv.of_origin next finalAllocator, accounting,
    modes⟩

/-! ## The common ends -/

/-- The end of a call whose loop stands at a stage: a leave with `LoopMatches` (after
`leave_meaning`) or the dictionary request. `Hx` is the heap holding the call's output before the
release of the local buffer; the decoder after the call is in `MEM`, or matches the stage. -/
theorem callExit_stage {wb : Int32} {r : ZStreamRef} {after Hx : Heap} {log : DataLog}
    {wrap : Api.Wrap} {configured : Nat} {rc : Int32} {input output : List UInt8}
    {used i u0 o0 : Nat} {z z' : ZStream} {s' : InflateState} {l : IL} {callOut : List UInt8}
    {consumed held : List Bool} {stage : WrapStage}
    (wbits : Api.inflWbits wb.toInt = some (wrap, configured))
    (inv' : InflateInv after r i z' s') (modes : ReturnedModes rc s')
    (nonnull : z.next_out ≠ .null) (accounting : StreamAccounting z z' u0 o0)
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (outBytes : Bytes after z.next_out (z.avail_out.toNat - z'.avail_out.toNat) output)
    (inLen : input.length = z.avail_in.toNat)
    (availIn : z'.avail_in = l.have_) (nextOut : z'.next_out = l.put)
    (inEq : l.in_.toNat = input.length)
    (putEq : l.put = inputAdvance z.next_out callOut.length)
    (callBytes : Bytes Hx z.next_out callOut.length callOut)
    (views : ∀ (ref : BRef) (a : Array UInt8),
      (Space.get after ref : Option (Array UInt8)) = some a → Space.get Hx ref = some a)
    (bitsEq : bytesToBits (log.input ++ input.take (loopRead l)) = consumed ++ held)
    (parsed : WrapParsed wrap configured log.dictionary consumed stage)
    (outputEq : stage.output = log.output ++ callOut)
    (config : ConfigMatches s' wrap configured) (heldBits : HeldBits s' held)
    (ends : s'.mode = MEM ∨
      (s'.mode ≠ BAD ∧ s'.mode ≠ MEM ∧ s'.mode ≠ SYNC ∧
        StageMatches after s' wrap log.dictionary stage ∧
        WrapMatches after s' wrap configured log.dictionary stage ∧
        ((rc == Z_NEED_DICT) = true → ∃ header, stage = .needDict header ∧ s'.havedict = 0))) :
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT) := by
  have usedRead := callExit_used usedEq inLen availIn inEq
  have outLen : z.avail_out.toNat - z'.avail_out.toNat = callOut.length := by
    obtain ⟨_, _, _, availO, _, nextO, _⟩ := accounting
    obtain ⟨ref, off, hp⟩ : ∃ ref off, z.next_out = .ref ref off := by
      cases hq : z.next_out with
      | null => exact absurd hq nonnull
      | ref ref off => exact ⟨ref, off, rfl⟩
    have e := nextO.symm.trans (nextOut.trans putEq)
    rw [hp] at e
    simp [advance, inputAdvance] at e
    omega
  have outEq : output = callOut := by
    rw [outLen] at outBytes
    exact callExit_bytes_eq callBytes outBytes views
  refine ⟨wrap, configured, i, z', s', wbits, inv', config, fun e => Or.inl (modes.2.2.1 e),
    fun e => Or.inl (modes.1 e), ?_, ?_, ?_⟩
  · intro _ bad
    rcases ends with mem | ⟨nb, _⟩
    · rw [mem] at bad
      exact absurd bad (by decide)
    · exact absurd bad nb
  · intro _ mem
    refine ⟨fun e => absurd ((modes.1 e).symm.trans mem) (by decide),
      fun source decoded valid full started => ?_⟩
    have started' : log.input ++ input.take (loopRead l) <+: source := by
      rw [← usedRead]
      exact started
    obtain ⟨pre, _⟩ := wrapParsed_prefix parsed bitsEq valid started'
    refine ⟨?_, fun e => absurd ((modes.2.2.1 e).symm.trans mem) (by decide),
      fun e => absurd ((modes.1 e).symm.trans mem) (by decide)⟩
    show log.output ++ output <+: decoded
    rw [outEq, ← outputEq]
    exact pre
  · intro _ _ nm _
    rcases ends with mem | ⟨_, _, _, sm, wm, request⟩
    · exact absurd mem nm
    · refine ⟨consumed, held, stage, ?_, heldBits, parsed, sm, wm, ?_, request⟩
      · show bytesToBits (log.input ++ input.take used) = _
        rw [usedRead]
        exact bitsEq
      · show log.output ++ output = _
        rw [outEq, outputEq]

/-- The end of a call from `BAD`: the decoder is in `BAD` (or `MEM` after a window allocation
failure) and the input read has no valid completion. -/
theorem callExit_bad {wb : Int32} {r : ZStreamRef} {after : Heap} {log : DataLog}
    {wrap : Api.Wrap} {configured : Nat} {rc : Int32} {input output : List UInt8}
    {used i : Nat} {z z' : ZStream} {s' : InflateState} {l : IL} {pending : Bool}
    (wbits : Api.inflWbits wb.toInt = some (wrap, configured))
    (inv' : InflateInv after r i z' s') (modes : ReturnedModes rc s')
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (inLen : input.length = z.avail_in.toNat)
    (availIn : z'.avail_in = l.have_) (inEq : l.in_.toNat = input.length)
    (config : ConfigMatches s' wrap configured)
    (doomed : ∀ source decoded, Api.Layer.Decodes wrap configured log.dictionary source decoded →
      Api.FullWindow wrap configured source → ¬ (log.input ++ input.take (loopRead l)) <+: source)
    (mode : s'.mode = BAD ∨ s'.mode = MEM) :
    ParseMeaning wb r after (logAfterCall log rc input output used) pending := by
  have usedRead := callExit_used usedEq inLen availIn inEq
  refine ⟨wrap, configured, i, z', s', wbits, inv', config, fun e => Or.inl (modes.2.2.1 e),
    fun e => Or.inl (modes.1 e), ?_, ?_, ?_⟩
  · intro _ _ source decoded valid full started
    exact doomed source decoded valid full (by rw [← usedRead]; exact started)
  · intro _ _
    refine ⟨fun e => ?_, fun source decoded valid full started => ?_⟩
    · exfalso
      rcases mode with m | m <;> exact absurd ((modes.1 e).symm.trans m) (by decide)
    · exact (doomed source decoded valid full (by rw [← usedRead]; exact started)).elim
  · intro _ nb nm _
    rcases mode with m | m
    · exact absurd m nb
    · exact absurd m nm

/-! ## The exits of the loop -/

/-- The safety facts at the exit give the side premises of `inf_leave`. -/
theorem callExit_leave_side {h h1 : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} {flush : Int32} {exit : Ex} {regs : IL}
    (inv : InflateInv h r i z s)
    (erun : runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) =
      .ok ((.error exit, regs), h1))
    (side : CallSide (callCtx h r i flush) r regs h1) :
    ∃ z1, r.get h1 = some z1 ∧ z1.zalloc = .fn "zcalloc" ∧ Zlib.Crc32.Proofs.StaticsOK h1 ∧
      (∀ zs s, (callCtx h r i flush).st = some (.tab zs) → h1.istates zs = some s →
        Good h1 r zs z1 s ∧ DataPendingInvariant s ∧
        ∀ w ref off, s.window = .ref (.blk w) 0 → regs.put = .ref ref off → ref ≠ .blk w) ∧
      (∃ bs, BitInv h1 regs bs) ∧ regs.bits.toNat ≤ 39 ∧ LeaveOutputView h1 regs := by
  obtain ⟨zs1, z1, s1, _, st, j, ⟨bs, buf⟩, _, bits, _⟩ := side
  have hz0 : r.get (syncAlloc h) = some z := by
    rw [ZStreamRef.get_syncAlloc]
    exact inv.good.live.hz
  have frame := streamFrameX_inflate_run r (callCtx h r i flush) rfl IL.init (syncAlloc h) _ regs h1
    erun
  have allocator := (frame.allocator hz0 j.good.live.hz inv.alloc).1
  have statics : Zlib.Crc32.Proofs.StaticsOK h1 := by
    have globals := j.globals
    unfold LibraryGlobals at globals
    rw [Zlib.Crc32.Proofs.StaticsOK, globals]
    exact ⟨rfl, rfl⟩
  refine ⟨z1, j.good.live.hz, allocator, statics, ?_, ⟨bs, buf.bits⟩, bits,
    leaveOutputView_of_cursor j.good buf.output⟩
  intro zs' s' st' hs'
  have e : zs' = zs1 := by
    have e := st'.symm.trans st
    simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
    exact e
  rw [e] at hs'
  have se : s' = s1 := Option.some.inj (hs'.symm.trans j.good.live.hs)
  rw [e, se]
  exact ⟨j.good, j.pending, fun w ref off win put =>
    callerRange_private_window j.good buf.output.range put w win⟩

/-- A leave with `LoopMatches`, with the return register `ret` (`Z_OK` for input or output
exhausted or a `Z_BLOCK` stop, `Z_STREAM_END` from `DONE`): `leave_meaning`, then the release of
the local buffer. -/
theorem callExit_leave {wb : Int32} {r : ZStreamRef} {h after h1 h2 : Heap} {log : DataLog}
    {wrap : Api.Wrap} {configured : Nat} {flush rc ret : Int32} {input output : List UInt8}
    {used i u0 o0 : Nat} {z z' : ZStream} {s sF : InflateState} {regs : IL}
    (wbits : Api.inflWbits wb.toInt = some (wrap, configured))
    (inv : InflateInv h r i z s) (invF : InflateInv after r i z' sF) (modes : ReturnedModes rc sF)
    (accounting : StreamAccounting z z' u0 o0)
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (outBytes : Bytes after z.next_out (z.avail_out.toNat - z'.avail_out.toNat) output)
    (inLen : input.length = z.avail_in.toNat) (nonnull : z.next_out ≠ .null)
    (erun : runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) =
      .ok ((.error .leave, regs), h1))
    (side : CallSide (callCtx h r i flush) r regs h1)
    (retCase : ret = Z_OK ∨ ret = Z_STREAM_END) (retEq : regs.ret = ret)
    (loop : LoopMatches (callCtx h r i flush) (callFrame wrap configured log z input) h1
      { regs with ret := Z_OK })
    (leaveRun : inflate_leave (callCtx h r i flush) regs h1 = .ok (rc, h2))
    (afterEq : after = freeWin h2 (.ref (.blk h.nextBlk) 0)) :
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT) := by
  obtain ⟨z1, hz1, allocator, statics, sideFn, _, bits, _⟩ := callExit_leave_side inv erun side
  have regsEq : ({ ({ regs with ret := Z_OK } : IL) with ret := ret } : IL) = regs := by
    rw [← retEq]
  have leaveM := leave_meaning (ret := ret) loop rfl hz1 sideFn bits allocator statics nonnull
    (by rw [regsEq]; exact leaveRun)
  obtain ⟨zs', s0, s', z2, callOut, consumed, held, stage, st', hs', hz2, _, aIn, nOut, _, _, inEq,
    putEq, outB, bitsEq, parsed, outputEq, config, _, heldB, rest⟩ := leaveM
  have zsI : zs' = i := by
    have e : (some (InflateStateRef.tab i) : InflateStatePtr) = some (.tab zs') := st'
    simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
    exact e.symm
  rw [zsI] at hs'
  subst afterEq
  have zEq : z2 = z' := by
    have g := invF.good.live.hz
    rw [callExit_get_freeWin] at g
    exact Option.some.inj (hz2.symm.trans g)
  have sEq : s' = sF := Option.some.inj (hs'.symm.trans invF.good.live.hs)
  subst zEq sEq
  refine callExit_stage wbits invF modes nonnull accounting usedEq outBytes inLen aIn nOut inEq
    putEq outB (fun _ _ g => callExit_freeWin_view g) bitsEq parsed outputEq config heldB ?_
  rcases rest with ⟨_, mem⟩ | ⟨rcCase, _, sm, wm⟩
  · exact Or.inl mem
  · obtain ⟨nb, nm, ns⟩ := callExit_stage_ordinary sm
    refine Or.inr ⟨nb, nm, ns, sm.frameRefs (callExit_sameRefs invF.good.inv.win),
      wm.frameRefs (callExit_sameRefs invF.good.inv.win), fun e => ?_⟩
    exfalso
    have e' : rc = Z_NEED_DICT := beq_iff_eq.mp e
    rcases rcCase with r1 | ⟨r1, _⟩
    · rw [r1] at e'
      rcases retCase with r2 | r2 <;> rw [r2] at e' <;> exact absurd e' (by decide)
    · rw [r1] at e'
      exact absurd e' (by decide)

/-- The `BAD` exit (`case BAD:` set `Z_DATA_ERROR`): `leave_meaning_bad`, then the release of the
local buffer. -/
theorem callExit_leaveBad {wb : Int32} {r : ZStreamRef} {h after h1 h2 : Heap} {log : DataLog}
    {wrap : Api.Wrap} {configured : Nat} {flush rc : Int32} {input output : List UInt8}
    {used i : Nat} {z z' : ZStream} {s sF : InflateState} {regs : IL} {pending : Bool}
    (wbits : Api.inflWbits wb.toInt = some (wrap, configured))
    (inv : InflateInv h r i z s) (invF : InflateInv after r i z' sF) (modes : ReturnedModes rc sF)
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (inLen : input.length = z.avail_in.toNat)
    (erun : runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) =
      .ok ((.error .leave, regs), h1))
    (side : CallSide (callCtx h r i flush) r regs h1) (retEq : regs.ret = Z_DATA_ERROR)
    (bad : LoopBad (callCtx h r i flush) (callFrame wrap configured log z input) h1
      { regs with ret := Z_OK })
    (leaveRun : inflate_leave (callCtx h r i flush) regs h1 = .ok (rc, h2))
    (afterEq : after = freeWin h2 (.ref (.blk h.nextBlk) 0)) :
    ParseMeaning wb r after (logAfterCall log rc input output used) pending := by
  obtain ⟨z1, hz1, allocator, statics, sideFn, ⟨bs, binv⟩, bits, view⟩ :=
    callExit_leave_side inv erun side
  have regsEq : ({ ({ regs with ret := Z_OK } : IL) with ret := Z_DATA_ERROR } : IL) = regs := by
    rw [← retEq]
  have leaveB := leave_meaning_bad bad rfl hz1 sideFn ⟨bs, ⟨binv.have_eq, binv.next, binv.hold_lt⟩⟩
    bits allocator statics view (by rw [regsEq]; exact leaveRun)
  obtain ⟨zs', s', z2, st', hs', hz2, _, aIn, _, _, _, inEq, config, doomed, codes⟩ := leaveB
  have zsI : zs' = i := by
    have e : (some (InflateStateRef.tab i) : InflateStatePtr) = some (.tab zs') := st'
    simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
    exact e.symm
  rw [zsI] at hs'
  subst afterEq
  have zEq : z2 = z' := by
    have g := invF.good.live.hz
    rw [callExit_get_freeWin] at g
    exact Option.some.inj (hz2.symm.trans g)
  have sEq : s' = sF := Option.some.inj (hs'.symm.trans invF.good.live.hs)
  subst zEq sEq
  exact callExit_bad wbits invF modes usedEq inLen aIn inEq config doomed
    (codes.imp And.right And.right)

/-- The dictionary request (`NeedDictExit`): `RESTORE()` wrote the registers, `DICT` returned
`Z_NEED_DICT` directly, and the local buffer was released. The stage is the dictionary request
with no dictionary installed. -/
theorem callExit_needDict {wb : Int32} {r : ZStreamRef} {h after mid : Heap} {log : DataLog}
    {wrap : Api.Wrap} {configured : Nat} {flush rc : Int32} {input output : List UInt8}
    {used i u0 o0 zs : Nat} {z z' z0 : ZStream} {sD sF : InflateState} {regs : IL}
    (wbits : Api.inflWbits wb.toInt = some (wrap, configured))
    (invF : InflateInv after r i z' sF) (modes : ReturnedModes rc sF)
    (accounting : StreamAccounting z z' u0 o0)
    (usedEq : used = z.avail_in.toNat - z'.avail_in.toNat)
    (outBytes : Bytes after z.next_out (z.avail_out.toNat - z'.avail_out.toNat) output)
    (inLen : input.length = z.avail_in.toNat) (nonnull : z.next_out ≠ .null)
    (st : (callCtx h r i flush).st = some (.tab zs))
    (hz0 : r.get mid = some z0) (hsD : mid.istates zs = some sD) (mode : sD.mode = DICT)
    (noDict : sD.havedict = 0)
    (loop : LoopMatches (callCtx h r i flush) (callFrame wrap configured log z input) mid regs)
    (afterEq : after = freeWin (setI (r.put mid (dictWaitStream z0 regs)) zs (leaveState sD regs))
      (.ref (.blk h.nextBlk) 0)) :
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT) := by
  have zsI : zs = i := by
    have e : (some (InflateStateRef.tab i) : InflateStatePtr) = some (.tab zs) := st
    simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
    exact e.symm
  rw [zsI] at hsD afterEq
  obtain ⟨zs2, s2, callOut, consumed, held, stage, st2, hs2, _, config, _, inEq, _, _, _, putEq,
    outB, _, _, _, _, bitsEq, heldB, parsed, stageM, wrapM, outputEq⟩ := loop
  have zs2I : zs2 = i := by
    have e : (some (InflateStateRef.tab i) : InflateStatePtr) = some (.tab zs2) := st2
    simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
    exact e.symm
  rw [zs2I] at hs2
  have sEq : sD = s2 := Option.some.inj (hsD.symm.trans hs2)
  rw [sEq] at mode noDict afterEq
  subst afterEq
  have hsA : (freeWin (setI (r.put mid (dictWaitStream z0 regs)) i (leaveState s2 regs))
      (.ref (.blk h.nextBlk) 0)).istates i = some (leaveState s2 regs) := setI_istates_same _ _ _
  have sFEq : sF = leaveState s2 regs := Option.some.inj (invF.good.live.hs.symm.trans hsA)
  have hzA : r.get (freeWin (setI (r.put mid (dictWaitStream z0 regs)) i (leaveState s2 regs))
      (.ref (.blk h.nextBlk) 0)) = some (dictWaitStream z0 regs) := by
    rw [callExit_get_freeWin]
    simp [hz0]
  have zEq : z' = dictWaitStream z0 regs := Option.some.inj (invF.good.live.hz.symm.trans hzA)
  subst sFEq zEq
  have modeL : (loopState s2 regs).mode = DICT := mode
  obtain ⟨header, rfl⟩ : ∃ header, stage = .needDict header := by
    cases stage with
    | header b =>
      have hi := stageM.2
      rw [modeL] at hi
      exact absurd hi (by decide)
    | needDict b => exact ⟨b, rfl⟩
    | body b pos =>
      have lo := (MeaningTrailer.body_mode_range stageM.1).1
      rw [modeL] at lo
      exact absurd lo (by decide)
    | trailer b o t =>
      rcases stageM.1 with m | m <;> rw [modeL] at m <;> exact absurd m (by decide)
    | done o =>
      have m : (loopState s2 regs).mode = DONE := stageM
      rw [modeL] at m
      exact absurd m (by decide)
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, _⟩ := wrapM
  have m : (leaveState s2 regs).mode = DICT := mode
  refine callExit_stage wbits invF modes nonnull accounting usedEq outBytes inLen rfl rfl inEq
    putEq outB (fun _ _ g => by
      have g' := callExit_freeWin_view g
      rwa [byte_view_get_setI, byte_view_get_stream_put] at g')
    bitsEq parsed outputEq config heldB (Or.inr ⟨?_, ?_, ?_, m, ⟨w1, w2, w3, w4, w5, w6, w7,
      fun hd => absurd noDict hd⟩, fun _ => ⟨header, rfl, noDict⟩⟩)
  · intro e
    exact absurd (m.symm.trans e) (by decide)
  · intro e
    exact absurd (m.symm.trans e) (by decide)
  · intro e
    exact absurd (m.symm.trans e) (by decide)

/-! ## The row -/

/-- `CallExit`: from a loop exit through `inf_leave` or the `Z_NEED_DICT` return and the release
of the local buffer to `ParseMeaning` of the history after the call. A call refused at entry
(`next_out` `NULL`) never ran the loop; it is `call_refused`. -/
theorem call_exit : CallExit := by
  intro wb r h after log pending wrap configured flush rc input output used i z s exit regs h1
    meaning _ wbits fit inv step bytes erun side ends
  have step0 := step
  obtain ⟨z0, z', get, get', buffers, active, _, usedEq, outBytes, run⟩ := step0
  have zEq : z0 = z := Option.some.inj (get.symm.trans inv.good.live.hz)
  rw [zEq] at usedEq outBytes
  have inLen : input.length = z.avail_in.toNat := callEntry_bytes_length bytes
  by_cases null : z.next_out = .null
  · exact call_refused wb r h after log pending flush rc input output used i z s meaning fit step
      inv.good (Or.inl null)
  have inputOk : z.next_in = .null → z.avail_in = 0 := by
    intro e
    rcases bytes with ⟨_, n0, _⟩ | ⟨_, _, _, p, _⟩
    · exact UInt32.toNat_inj.mp (by rw [n0]; rfl)
    · rw [e] at p
      cases p
  obtain ⟨zF, sF, u0, o0, invF, accounting, modes⟩ := callExit_after inv fit buffers active run
  have zF' : z' = zF := Option.some.inj (get'.symm.trans invF.good.live.hz)
  rw [zF'] at usedEq outBytes
  obtain ⟨h2, how, afterEq⟩ := callExit_split inv null inputOk run erun
  rcases ends with ⟨exitEq, loopCases⟩ | needDict
  · subst exitEq
    obtain ⟨_, leaveRun⟩ : _ ∧ _ := by
      rcases how with p | ⟨_, e, _, _⟩
      · exact p
      · cases e
    rcases loopCases with loop | ⟨retEq, loop⟩ | ⟨retEq, bad⟩
    · have loop0 := loop
      obtain ⟨_, _, _, _, _, _, _, _, ret0, _⟩ := loop0
      have eq : ({ regs with ret := Z_OK } : IL) = regs := by rw [← ret0]
      exact callExit_leave wbits inv invF modes accounting usedEq outBytes inLen null erun side
        (Or.inl rfl) ret0 (by rw [eq]; exact loop) leaveRun afterEq
    · exact callExit_leave wbits inv invF modes accounting usedEq outBytes inLen null erun side
        (Or.inr rfl) retEq loop leaveRun afterEq
    · exact callExit_leaveBad wbits inv invF modes usedEq inLen erun side retEq bad leaveRun afterEq
  · obtain ⟨exitEq, r', z0', zs, sD, mid, strm, st, hz0, hsD, mode, noDict, loop, h1Eq⟩ := needDict
    have rEq : r' = r := by
      have e : (some r : Option ZStreamRef) = some r' := strm
      exact (Option.some.inj e).symm
    subst rEq
    have exitEq' : exit = .ret Z_NEED_DICT := by cases exitEq; rfl
    subst exitEq'
    rcases how with ⟨e, _⟩ | ⟨_, _, _, h2Eq⟩
    · cases e
    subst h2Eq h1Eq
    exact callExit_needDict wbits invF modes accounting usedEq outBytes inLen null st hz0 hsD mode
      noDict loop afterEq

#print axioms call_exit

end Zlib.Inflate.Proofs
