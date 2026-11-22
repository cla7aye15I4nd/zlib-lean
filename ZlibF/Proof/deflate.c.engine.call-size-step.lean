import ZlibF.Proof.«deflate.c.engine.call-size-first»
import ZlibF.Proof.«deflate.c.engine.refusal-counters»
import ZlibF.Proof.«deflate.c.engine.encoding-observations»

/-! # The size ledger across one call

Every clean call (`Z_NO_FLUSH` or `Z_FINISH`) with a raw output pointer keeps `SizeLedger`, for the
encoding state the call reaches: refusals change nothing, the first call and `BUSY_STATE` calls
give a ledger outcome, and `FINISH_STATE` calls conserve delivered, held and owed bytes.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- **A ledger outcome gives the ledger.** -/
theorem ledger_of_outcome {after : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {result : DeflateState}
    {config : EngineConfig} {accepted observed : List UInt8} {flush rc : Int32} {start base held produced : Nat}
    (outcome : BusySizeOutcome after r ds z' result flush rc start base held produced)
    (startEq : start = accepted.length)
    (before : observed.length + held ≤ base + 2 + 5 * (base / 16383))
    (window : config.windowBits = 15) {output : List UInt8} (outLen : output.length = produced) :
    SizeLedger after r ds z' result config accepted (observed ++ output) := by
  rcases outcome with ⟨status, input', origin', base', xs', known, endpoint, companion, size⟩ |
      ⟨status, size, _ended⟩
  · refine ⟨fun init => absurd (status.symm.trans init) (by decide), ?_,
      fun finish => absurd (status.symm.trans finish) (by decide), window⟩
    exact busy_clause_of_data known (endpoint.trans startEq) companion
      (by simp only [List.length_append]; omega)
  · refine ⟨fun init => absurd (status.symm.trans init) (by decide),
      fun _ _ _ _ _ busy => absurd (status.symm.trans busy) (by decide), fun _ => ?_, window⟩
    simp only [List.length_append]
    rw [← startEq]
    omega

/-- **Entering `FINISH_STATE`**: an outcome in `FINISH_STATE` came from `Z_FINISH` and left no input. -/
theorem BusySizeOutcome.finish_entry {after : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream}
    {result : DeflateState} {flush rc : Int32} {start base held produced : Nat}
    (outcome : BusySizeOutcome after r ds z' result flush rc start base held produced)
    (status : result.status = FINISH_STATE) : flush = Z_FINISH ∧ z'.avail_in = 0 := by
  rcases outcome with ⟨busy, _⟩ | ⟨_, _, _, entry⟩
  · exact absurd (status.symm.trans busy) (by decide)
  · exact entry

/-- **A conserving `FINISH_STATE` call gives the ledger.** -/
theorem ledger_of_finishing {after : Heap} {r : ZStreamRef} {ds : Nat} {z' : ZStream} {d result : DeflateState}
    {config : EngineConfig} {accepted observed output : List UInt8} {produced : Nat}
    (status : result.status = FINISH_STATE)
    (size : produced + heldBytes result + owedTrailer result = heldBytes d + owedTrailer d)
    (before : observed.length + heldBytes d + owedTrailer d ≤
      accepted.length + 11 + 5 * (accepted.length / 16383))
    (window : config.windowBits = 15) (outLen : output.length = produced) :
    SizeLedger after r ds z' result config accepted (observed ++ output) := by
  refine ⟨fun init => absurd (status.symm.trans init) (by decide),
    fun _ _ _ _ _ busy => absurd (status.symm.trans busy) (by decide), fun _ => ?_, window⟩
  simp only [List.length_append]
  omega

/-- **A refusal keeps the ledger**: only the stream record changes. -/
theorem SizeLedger.refused {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {accepted observed : List UInt8} {message : BPtr}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (ledger : SizeLedger h r ds z d config accepted observed) :
    SizeLedger (r.put h { z with msg := message }) r ds { z with msg := message } d config accepted
      (observed ++ []) := by
  rw [List.append_nil]
  have goodA := stream_control_good (z' := { z with msg := message }) state.protocol.good rfl
    state.protocol.good.live.zalloc state.protocol.good.live.zfree
  refine ⟨ledger.init, ?_, ledger.finishing, ledger.window⟩
  intro input origin base xs boundary status prefixEq
  obtain ⟨input0, origin0, base0, xs0, boundary0, prefix0⟩ := state.busy_data status
  obtain ⟨companion, size⟩ := ledger.busy input0 origin0 base0 xs0 boundary0 status prefix0
  have boundaryA := stream_control_buffered boundary0 goodA
  have length := congrArg List.length prefix0
  rw [input_prefix_length] at length
  exact busy_clause_of_data (config := config) boundaryA.toContentBoundary length companion size
    input origin base xs boundary status prefixEq

/-- **The ledger across one clean call** with a raw output pointer. -/
theorem SizeLedger.step_raw {h after : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream}
    {d result : DeflateState} {config : EngineConfig} {accepted observed input output : List UInt8}
    {flush rc : Int32} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted observed)
    (ledger : SizeLedger h r ds z d config accepted observed)
    (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (step : DataStep .deflate h after r flush rc input output used)
    (getA : r.get after = some z') (stateA : after.dstates ds = some result) :
    SizeLedger after r ds z' result config (accepted ++ input.take used) (observed ++ output) ∧
      (flush = Z_FINISH → rc = Z_OK → z'.avail_out = 0) ∧
      (d.status ≠ FINISH_STATE → result.status = FINISH_STATE → flush = Z_FINISH ∧ z'.avail_in = 0) := by
  obtain ⟨z0, z1, get0, get1, buffers, _header, snapshot, usedEq, bytesOut, run⟩ := step
  have same0 : z0 = z := Option.some.inj (get0.symm.trans state.protocol.good.live.hz)
  subst same0
  have same1 : z1 = z' := Option.some.inj (get1.symm.trans getA)
  subst same1
  have run' : deflate (some r) flush h = .ok (rc, after) := run
  have outLen := public_bytes_length bytesOut
  have inLen := public_bytes_length snapshot
  have identify : ∀ usedS producedS zS resultS, r.get after = some zS → after.dstates ds = some resultS →
      StreamAccounting z0 zS usedS producedS →
      zS = z1 ∧ resultS = result ∧ used = usedS ∧ output.length = producedS := by
    intro usedS producedS zS resultS gS sS account
    have e1 : zS = z1 := Option.some.inj (gS.symm.trans getA)
    have e2 : resultS = result := Option.some.inj (sS.symm.trans stateA)
    subst e1 e2
    have a1 := account.2.2.1
    have a2 := account.2.2.2.1
    exact ⟨rfl, rfl, by omega, by omega⟩
  have acceptedLen : (accepted ++ input.take used).length = accepted.length + used := by
    simp only [List.length_append, List.length_take]
    omega
  have flagLo : 0 ≤ flush.toInt := by rcases clean with rfl | rfl <;> decide
  have flagHi : flush.toInt ≤ Z_BLOCK.toInt := by rcases clean with rfl | rfl <;> decide
  have options := state.protocol.configuration
  by_cases refused : z0.next_out = .null ∨ (z0.avail_in ≠ 0 ∧ z0.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) ∨ z0.avail_out = 0
  · have source : deflate (some r) flush h = ERR_RETURN (some r) Z_STREAM_ERROR h ∨
        deflate (some r) flush h = ERR_RETURN (some r) Z_BUF_ERROR h := by
      by_cases streamBad : z0.next_out = .null ∨ (z0.avail_in ≠ 0 ∧ z0.next_in = .null) ∨
          (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)
      · exact Or.inl (public_stream_guard_refusal state.protocol.good flush flagLo flagHi streamBad)
      · have out : z0.next_out ≠ .null := fun eq => streamBad (Or.inl eq)
        have valid : z0.avail_in ≠ 0 → z0.next_in ≠ .null := fun count eq => streamBad (Or.inr (Or.inl ⟨count, eq⟩))
        have finish : d.status = FINISH_STATE → flush = Z_FINISH := by
          intro status
          by_cases flag : flush = Z_FINISH
          · exact flag
          · exact False.elim (streamBad (Or.inr (Or.inr ⟨status, flag⟩)))
        have empty : z0.avail_out = 0 := by
          rcases refused with bad | bad | bad | empty
          · exact False.elim (out bad)
          · exact False.elim (valid bad.1 bad.2)
          · exact False.elim (bad.2 (finish bad.1))
          · exact empty
        exact Or.inr (public_zero_output_refusal state.protocol.good flush flagLo flagHi out valid finish empty)
    have refusedRun : ∃ message, (rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
        deflate (some r) flush h = .ok (rc, r.put h { z0 with msg := message }) := by
      rcases source with stream | buffer
      · obtain ⟨message, err⟩ := err_return_run state.protocol.good.live.hz Z_STREAM_ERROR
        have tested := stream.trans err
        obtain ⟨rcs, _⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run'))
        exact ⟨message, Or.inl rcs.symm, rcs ▸ tested⟩
      · obtain ⟨message, err⟩ := err_return_run state.protocol.good.live.hz Z_BUF_ERROR
        have tested := buffer.trans err
        obtain ⟨rcs, _⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run'))
        exact ⟨message, Or.inr rcs.symm, rcs ▸ tested⟩
    obtain ⟨message, codes, tested⟩ := refusedRun
    obtain ⟨_, heaps⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run'))
    subst heaps
    have keep := state.protocol.good
    have goodA := stream_control_good (z' := { z0 with msg := message }) keep rfl keep.live.zalloc keep.live.zfree
    obtain ⟨zEq, dEq, usedZero, outZero⟩ := identify 0 0 _ _ goodA.live.hz goodA.live.hs (stream_accounting_zero z0)
    subst zEq dEq usedZero
    have nil : output = [] := List.eq_nil_of_length_eq_zero outZero
    subst nil
    refine ⟨by simpa only [List.take_zero, List.append_nil] using ledger.refused (message := message) state, ?_,
      fun notFinished finished => absurd finished notFinished⟩
    intro _ ok
    rcases codes with c | c
    · exact absurd (ok.symm.trans c) (by decide)
    · exact absurd (ok.symm.trans c) (by decide)
  · have out : z0.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z0.avail_in ≠ 0 → z0.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have output0 : 0 < z0.avail_out.toNat := by
      have nonzero : z0.avail_out.toNat ≠ 0 := fun zero =>
        refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp zero))))
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z0.next_out = .ref (.blk ob) oo := raw.resolve_left out
    have busyCase : ∀ input0 origin base xs, BufferedBoundary h r ds z0 d input0 origin base xs config →
        d.status = BUSY_STATE → inputPrefix input0 (origin + fillEnd d) = accepted →
        SizeLedger after r ds z1 result config (accepted ++ input.take used) (observed ++ output) ∧
          (flush = Z_FINISH → rc = Z_OK → z1.avail_out = 0) ∧
          (d.status ≠ FINISH_STATE → result.status = FINISH_STATE → flush = Z_FINISH ∧ z1.avail_in = 0) := by
      intro input0 origin base xs boundary status inputEq
      have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans options.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy boundary.configuration).trans options.strategy
      obtain ⟨companion, size⟩ := ledger.busy input0 origin base xs boundary status inputEq
      obtain ⟨usedS, producedS, zS, resultS, gS, sS, account, roomS, outcome⟩ :=
        busy_call_size boundary buffers status level strategy pointer output0 options.memory options.wrap
          ledger.window valid state.protocol.lower state.protocol.upper companion clean run'
      obtain ⟨zEq, dEq, usedS', outS⟩ := identify usedS producedS zS resultS gS sS account
      subst zEq dEq usedS'
      have length := congrArg List.length inputEq
      rw [input_prefix_length] at length
      refine ⟨ledger_of_outcome outcome ?_ size ledger.window outS, roomS, fun _ finished => outcome.finish_entry finished⟩
      rw [acceptedLen, length]
    rcases state.phase with ⟨emptyInput, emptyOutput, input0, start, boundary⟩ |
        ⟨_, _, _, _, status, _⟩ |
        ⟨_, _, _, _, _, _, _, status, _, _⟩ |
        ⟨_published, _outputEq, phase, _encoding⟩
    · -- the first call
      subst emptyInput emptyOutput
      have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans options.level
      obtain ⟨_, _, companion⟩ := ledger.init start.status
      obtain ⟨usedS, producedS, zS, resultS, gS, sS, account, roomS, outcome⟩ :=
        first_call_size start level boundary buffers pointer output0 options.memory ledger.window valid
          companion clean run'
      obtain ⟨zEq, dEq, usedS', outS⟩ := identify usedS producedS zS resultS gS sS account
      subst zEq dEq usedS'
      have fill : fillEnd d = 0 := by
        simp only [fillEnd, start.start, start.lookahead, UInt32.toNat_zero, Nat.add_zero]
      refine ⟨ledger_of_outcome outcome ?_ (by simp) ledger.window outS, roomS, fun _ finished => outcome.finish_entry finished⟩
      rw [acceptedLen, fill]
      simp
    · obtain ⟨input0, origin, base, xs, boundary, inputEq⟩ := state.busy_data status
      exact busyCase input0 origin base xs boundary status inputEq
    · obtain ⟨input0, origin, base, xs, boundary, inputEq⟩ := state.busy_data status
      exact busyCase input0 origin base xs boundary status inputEq
    · -- FINISH_STATE
      have finish : flush = Z_FINISH := by
        by_cases flag : flush = Z_FINISH
        · exact flag
        · exact False.elim (refused (Or.inr (Or.inr (Or.inl ⟨phase.status, flag⟩))))
      subst finish
      have finishing := ledger.finishing phase.status
      by_cases empty : z0.avail_in = 0
      · obtain ⟨producedS, rcE, other, zS, resultS, tested, goodS, account, roomS, statusS, sizeS⟩ :=
          public_finishing_size_execution state.protocol.good buffers phase pointer empty output0
            state.protocol.lower state.protocol.upper
        obtain ⟨rcs, heaps⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run'))
        subst heaps
        obtain ⟨zEq, dEq, usedS', outS⟩ := identify 0 producedS zS resultS goodS.live.hz goodS.live.hs account
        subst zEq dEq usedS'
        have fin := ledger_of_finishing (after := other) (r := r) (ds := ds) (z' := zS) (config := config)
          (accepted := accepted) (observed := observed) statusS sizeS finishing ledger.window outS
        refine ⟨by simpa only [List.take_zero, List.append_nil] using fin, ?_,
          fun notFinished _ => absurd phase.status notFinished⟩
        intro _ ok
        exact roomS (rcs.trans ok)
      · obtain ⟨producedS, rcE, other, zS, resultS, tested, goodS, account, roomS, statusS, sizeS⟩ :=
          public_finishing_new_input_size_execution state.protocol.good buffers phase pointer valid empty output0
            state.protocol.lower state.protocol.upper
        obtain ⟨rcs, heaps⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run'))
        subst heaps
        obtain ⟨zEq, dEq, usedS', outS⟩ := identify 0 producedS zS resultS goodS.live.hz goodS.live.hs account
        subst zEq dEq usedS'
        have fin := ledger_of_finishing (after := other) (r := r) (ds := ds) (z' := zS) (config := config)
          (accepted := accepted) (observed := observed) statusS sizeS finishing ledger.window outS
        refine ⟨by simpa only [List.take_zero, List.append_nil] using fin, ?_,
          fun notFinished _ => absurd phase.status notFinished⟩
        intro _ ok
        exact roomS (rcs.trans ok)

/-- **The first output is strictly inside the ledger.** A `Z_FINISH` call with a raw output
pointer from a stream that has written nothing, returning `Z_OK`, writes at most
`n + 10 + 5 * (n / 16383)` bytes for the `n` bytes it accepts: it stops owing or holding output. -/
theorem first_ok_raw {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {config : EngineConfig} {accepted input output : List UInt8} {used : Nat}
    (state : DefaultEncodingState h r ds z d config accepted [])
    (ledger : SizeLedger h r ds z d config accepted [])
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (step : DataStep .deflate h after r Z_FINISH Z_OK input output used) :
    output.length + 1 ≤ (accepted ++ input.take used).length + 11 +
      5 * ((accepted ++ input.take used).length / 16383) := by
  obtain ⟨z0, z1, get0, getA, buffers, _header, snapshot, usedEq, bytesOut, run⟩ := step
  have same0 : z0 = z := Option.some.inj (get0.symm.trans state.protocol.good.live.hz)
  subst same0
  have run' : deflate (some r) Z_FINISH h = .ok (Z_OK, after) := run
  have outLen := public_bytes_length bytesOut
  have inLen := public_bytes_length snapshot
  have options := state.protocol.configuration
  rcases state.phase with ⟨emptyInput, _emptyOutput, input0, start, boundary⟩ | ⟨_, impossible, _⟩ |
      ⟨_, _, _, _, _, impossible, _⟩ | ⟨_, impossible, _⟩
  rotate_left
  · cases impossible
  · simp at impossible
  · simp at impossible
  subst emptyInput
  have acceptedLen : ([] ++ input.take used).length = used := by
    simp only [List.nil_append, List.length_take]
    omega
  rw [acceptedLen]
  by_cases refused : z0.next_out = .null ∨ (z0.avail_in ≠ 0 ∧ z0.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_FINISH ≠ Z_FINISH) ∨ z0.avail_out = 0
  · exfalso
    have flagLo : 0 ≤ Z_FINISH.toInt := by decide
    have flagHi : Z_FINISH.toInt ≤ Z_BLOCK.toInt := by decide
    by_cases streamBad : z0.next_out = .null ∨ (z0.avail_in ≠ 0 ∧ z0.next_in = .null) ∨
        (d.status = FINISH_STATE ∧ Z_FINISH ≠ Z_FINISH)
    · have source := public_stream_guard_refusal state.protocol.good Z_FINISH flagLo flagHi streamBad
      obtain ⟨message, err⟩ := err_return_run state.protocol.good.live.hz Z_STREAM_ERROR
      obtain ⟨rcs, _⟩ := Prod.mk.inj (Except.ok.inj ((source.trans err).symm.trans run'))
      exact absurd rcs (by decide)
    · have out : z0.next_out ≠ .null := fun eq => streamBad (Or.inl eq)
      have valid : z0.avail_in ≠ 0 → z0.next_in ≠ .null := fun count eq => streamBad (Or.inr (Or.inl ⟨count, eq⟩))
      have empty : z0.avail_out = 0 := by
        rcases refused with bad | bad | bad | empty
        · exact False.elim (out bad)
        · exact False.elim (valid bad.1 bad.2)
        · exact False.elim (bad.2 rfl)
        · exact empty
      have source := public_zero_output_refusal state.protocol.good Z_FINISH flagLo flagHi out valid (fun _ => rfl) empty
      obtain ⟨message, err⟩ := err_return_run state.protocol.good.live.hz Z_BUF_ERROR
      obtain ⟨rcs, _⟩ := Prod.mk.inj (Except.ok.inj ((source.trans err).symm.trans run'))
      exact absurd rcs (by decide)
  · have out : z0.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z0.avail_in ≠ 0 → z0.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have output0 : 0 < z0.avail_out.toNat := by
      have nonzero : z0.avail_out.toNat ≠ 0 := fun zero =>
        refused (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp zero))))
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z0.next_out = .ref (.blk ob) oo := raw.resolve_left out
    have level : d.level = 6 := (congrArg EngineConfig.level boundary.configuration).trans options.level
    obtain ⟨_, _, companion⟩ := ledger.init start.status
    obtain ⟨usedS, producedS, zS, resultS, gS, _sS, account, _roomS, outcome⟩ :=
      first_call_size start level boundary buffers pointer output0 options.memory ledger.window valid
        companion (Or.inr rfl) run'
    have zEq : zS = z1 := Option.some.inj (gS.symm.trans getA)
    subst zEq
    have usedS' : used = usedS := by have a := account.2.2.1; omega
    have outS : output.length = producedS := by have a := account.2.2.2.1; omega
    subst usedS'
    have fill : fillEnd d = 0 := by
      simp only [fillEnd, start.start, start.lookahead, UInt32.toNat_zero, Nat.add_zero]
    rw [fill] at outcome
    rcases outcome with ⟨_status, input', origin', base', xs', known, endpoint, _companion, size⟩ |
        ⟨_status, size, ended, _⟩
    · have covered := content_base_le known
      have grow : base' / 16383 ≤ used / 16383 := Nat.div_le_div_right (by omega)
      omega
    · have owing : 0 < heldBytes resultS + owedTrailer resultS := by
        by_cases none : heldBytes resultS + owedTrailer resultS = 0
        · have done := ended (by omega) (by omega)
          exact absurd done (by decide)
        · omega
      omega

end Zlib.Deflate.Engine.Proofs
