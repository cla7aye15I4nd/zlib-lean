import ZlibF.Proof.«inflate.c.meaning-trip»
import ZlibF.Proof.«inflate.c.completes-meaning»
import ZlibF.Proof.«inflate.c.completes-blocked»

/-!
# inflate.c: one `inflate` call keeps the format meaning (`MeaningStep`)

`MeaningStep` (`inflate.c.completes-interface`) is the step of `ParseMeaning` over one call of a
protocol history. One call takes the local buffer, checks its arguments, runs `inflate_run` (the
`TYPE`-to-`TYPEDO` skip, `LOAD()` and the mode loop), then `inf_leave` or a direct return, and
frees the local buffer. The call-level rows are named propositions:

* `CallRefused`: a refusal at entry (a `NULL` output or input pointer with input, `MEM`, `SYNC`);
* `CallEntry`: from `ParseMeaning` to the loop start with `CallSide` and `LoopMatches` or `LoopBad`;
* `CallExit`: from a loop exit through `inf_leave` or the `Z_NEED_DICT` return to `ParseMeaning`;
* `CallUnstaged`: a history with more than one raw dictionary (no stage clause).

`call_meaning` assembles one call of a configuration from `CallRows` and the trips
(`loop_meaning_side`). `meaning_of_protocol_plain` is the induction over a protocol history for
`wb ≥ 0`, where every history has a single dictionary; `meaning_of_protocol_zlib` is the zlib
case, from `ZlibTripRows` and `CallRows`; `meaning_step_of_rows` is the universal `MeaningStep`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.KeepProofs
set_option autoImplicit false

/-- The context of an `inflate` call on stream `r` with decoder record `i` from heap `h`. -/
def callCtx (h : Heap) (r : ZStreamRef) (i : Nat) (flush : Int32) : Ctx :=
  ⟨some r, some (.tab i), syncBuf h, flush⟩

/-- What the call keeps fixed: the configuration, the history before it, the offered input and
the output start. -/
def callFrame (wrap : Api.Wrap) (configured : Nat) (log : DataLog) (z : ZStream)
    (input : List UInt8) : LoopFrame :=
  ⟨wrap, configured, log.dictionary, log.input, log.output, input, z.next_out⟩

/-- The history after a call, as `InflateProtocolTrace.step` records it. -/
def logAfterCall (log : DataLog) (rc : Int32) (input output : List UInt8) (used : Nat) :
    DataLog :=
  { log with
    input := log.input ++ input.take used, output := log.output ++ output
    result := rc, finished := log.finished || rc == Z_STREAM_END }

/-- `MeaningStep` for one configuration and a single-dictionary history. -/
def MeaningStepSingle (wb : Int32) : Prop :=
  ∀ (r : ZStreamRef) (h after : Heap) (log : DataLog) (pending : Bool)
    (flush rc : Int32) (input output : List UInt8) (used : Nat),
    log.singleDictionary = true →
    ParseMeaning wb r h log pending → ZlibF.PlatformMemory.ByteObjectsFit h →
    DataStep .inflate h after r flush rc input output used →
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT)

/-- The loop rule for every call of a configuration. -/
def TripsFor (wb : Int32) : Prop :=
  ∀ wrap configured, Api.inflWbits wb.toInt = some (wrap, configured) →
    ∀ (c : Ctx) (f : LoopFrame) (r : ZStreamRef), f.wrap = wrap → f.configured = configured →
      TripMeaning c f (CallSide c r) ∧ RawCheckTrip c f (CallSide c r)

/-! ## Rows -/

/-- A refused call: `next_out` is `NULL`, `next_in` is `NULL` with input, or the decoder is in
`MEM` (returns `Z_MEM_ERROR`) or `SYNC` (returns `Z_STREAM_ERROR`). Only the local buffer is taken
and released; the stream and the decoder are unchanged, no input is used and no output made. -/
def CallRefused : Prop :=
  ∀ (wb : Int32) (r : ZStreamRef) (h after : Heap) (log : DataLog) (pending : Bool)
    (flush rc : Int32) (input output : List UInt8) (used i : Nat) (z : ZStream) (s : InflateState),
    ParseMeaning wb r h log pending → ZlibF.PlatformMemory.ByteObjectsFit h →
    DataStep .inflate h after r flush rc input output used → Good h r i z s →
    (z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = MEM ∨ s.mode = SYNC) →
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT)

/-- A history with more than one raw dictionary: `ParseMeaning` after the call needs only the
invariant, the configuration and the result clauses. Not needed by the zlib round trip. -/
def CallUnstaged : Prop :=
  ∀ (wb : Int32) (r : ZStreamRef) (h after : Heap) (log : DataLog) (pending : Bool)
    (flush rc : Int32) (input output : List UInt8) (used : Nat),
    ParseMeaning wb r h log pending → log.singleDictionary = false →
    ZlibF.PlatformMemory.ByteObjectsFit h → DataStep .inflate h after r flush rc input output used →
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT)

/-- Entry of an accepted call: after the local buffer, the `TYPE`-to-`TYPEDO` skip and `LOAD()`,
the loop starts with the safety facts and with `LoopMatches` (the stage of `ParseMeaning`, nothing
read or written yet), or with `LoopBad` from a decoder in `BAD`. -/
def CallEntry : Prop :=
  ∀ (wb : Int32) (r : ZStreamRef) (h : Heap) (log : DataLog) (pending : Bool)
    (wrap : Api.Wrap) (configured : Nat) (flush : Int32) (i : Nat) (z : ZStream)
    (s : InflateState) (input : List UInt8),
    ParseMeaning wb r h log pending → log.singleDictionary = true →
    Api.inflWbits wb.toInt = some (wrap, configured) →
    ZlibF.PlatformMemory.ByteObjectsFit h → InflateInv h r i z s →
    StreamBuffers h r → ActiveHeader h r → Bytes h z.next_in z.avail_in.toNat input →
    z.next_out ≠ .null → (z.next_in = .null → z.avail_in = 0) → s.mode ≠ MEM → s.mode ≠ SYNC →
    ∃ l0 h0,
      runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) =
        runX (xwhile (pure true) (inflate_dispatch (callCtx h r i flush))) l0 h0 ∧
      CallSide (callCtx h r i flush) r l0 h0 ∧
      (LoopMatches (callCtx h r i flush) (callFrame wrap configured log z input) h0 l0 ∨
       LoopBad (callCtx h r i flush) (callFrame wrap configured log z input) h0 l0)

/-- Exit of an accepted call: from a loop exit, `inf_leave` (`leave_meaning`, `leave_meaning_bad`,
the window-allocation failure to `MEM`) or the `Z_NEED_DICT` return, then the release of the local
buffer, give `ParseMeaning` of the history after the call with the request token. -/
def CallExit : Prop :=
  ∀ (wb : Int32) (r : ZStreamRef) (h after : Heap) (log : DataLog) (pending : Bool)
    (wrap : Api.Wrap) (configured : Nat) (flush rc : Int32) (input output : List UInt8)
    (used i : Nat) (z : ZStream) (s : InflateState) (exit : Ex) (regs : IL) (h1 : Heap),
    ParseMeaning wb r h log pending → log.singleDictionary = true →
    Api.inflWbits wb.toInt = some (wrap, configured) →
    ZlibF.PlatformMemory.ByteObjectsFit h → InflateInv h r i z s →
    DataStep .inflate h after r flush rc input output used →
    Bytes h z.next_in z.avail_in.toNat input →
    runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) =
      .ok ((.error exit, regs), h1) →
    CallSide (callCtx h r i flush) r regs h1 →
    LoopExit (callCtx h r i flush) (callFrame wrap configured log z input) exit h1 regs →
    ParseMeaning wb r after (logAfterCall log rc input output used) (rc == Z_NEED_DICT)

/-- The call rows of a single-dictionary history. -/
structure CallRows : Prop where
  refused : CallRefused
  entry : CallEntry
  exit : CallExit

/-! ## The loop with the side facts at its exit -/

/-- `CallSide` holds after every end of a dispatch, also an exit. -/
theorem side_kept_all (c : Ctx) (r : ZStreamRef) :
    ∀ l h outcome l' h', CallSide c r l h →
      runX (inflate_dispatch c) l h = .ok ((outcome, l'), h') → CallSide c r l' h' := by
  intro l h outcome l' h' side run
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, loc, bits, apart⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  obtain ⟨outcome', regs, after, stream, state, used, _, _, run', j', ⟨rest, _, buf'⟩, _, next,
    count, _, _, bits', loc', _⟩ := inflate_dispatch_default_view_state_rank E j buf loc bits
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨⟨_, hl⟩, hh⟩ := same
  subst hl hh
  exact ⟨zs, stream, state, strm, st, j', ⟨rest, buf'⟩, loc', bits', apart.advance next count⟩

/-- `loop_meaning_from` with the side facts at the exit. -/
theorem loop_meaning_side {c : Ctx} {f : LoopFrame} {r : ZStreamRef}
    (trip : TripMeaning c f (CallSide c r)) (rawTrip : RawCheckTrip c f (CallSide c r))
    (strm : c.strm = some r)
    {l regs : IL} {h after : Heap} {outcome : Except Ex Unit}
    (side : CallSide c r l h) (start : LoopMatches c f h l ∨ LoopBad c f h l)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((outcome, regs), after)) :
    ∃ exit, outcome = .error exit ∧ LoopExit c f exit after regs ∧ CallSide c r regs after := by
  cases outcome with
  | ok u => exact absurd run (fun run => xwhile_true_not_ok run)
  | error exit =>
    refine ⟨exit, rfl, ?_⟩
    let P : IL → Heap → Prop := fun l h =>
      CallSide c r l h ∧ ((LoopMatches c f h l ∨ LoopBad c f h l) ∨ RawCheck c f h l)
    let Q : Ex → IL → Heap → Prop := fun e l h => LoopExit c f e h l ∧ CallSide c r l h
    have step : ∀ l h outcome regs after, P l h →
        runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) →
        match outcome with
        | .ok () => P regs after
        | .error exit => Q exit regs after := by
      intro l h outcome regs after ⟨side, current⟩ source
      have sideAfter := side_kept_all c r l h outcome regs after side source
      rcases current with (loop | bad) | raw
      · obtain ⟨result, l', h', run', outcome'⟩ := trip h l side loop
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases outcome' with tripOut | needDict | ⟨rfl, raw'⟩
        · rcases tripOut with ⟨rfl, cont⟩ | ⟨rfl, leave⟩
          · exact ⟨sideAfter, Or.inl cont⟩
          · exact ⟨Or.inl ⟨rfl, leave⟩, sideAfter⟩
        · have exitEq := needDict.1
          cases exitEq
          exact ⟨Or.inr needDict, sideAfter⟩
        · exact ⟨sideAfter, Or.inr raw'⟩
      · obtain ⟨z, hz⟩ := side.record
        obtain ⟨run', tripOut⟩ := bad_trip bad strm hz
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases tripOut with ⟨eq, _⟩ | ⟨_, leave⟩
        · cases eq
        · exact ⟨Or.inl ⟨rfl, leave⟩, sideAfter⟩
      · obtain ⟨result, l', h', run', tripOut⟩ := rawTrip h l side raw
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases tripOut with ⟨rfl, cont⟩ | ⟨rfl, leave⟩
        · exact ⟨sideAfter, Or.inl cont⟩
        · exact ⟨Or.inl ⟨rfl, leave⟩, sideAfter⟩
    exact xwhile_success_control_post P Q step ⟨side, Or.inl start⟩ run

/-! ## Assembly -/

/-- One call of a configuration, from the call rows and the trips. -/
theorem call_meaning (rows : CallRows) (wb : Int32) (trips : TripsFor wb) :
    MeaningStepSingle wb := by
  intro r h after log pending flush rc input output used single meaning fit step
  have meaning0 := meaning
  obtain ⟨wrap, configured, i, z, s, wbits, inv, _⟩ := meaning0
  have step0 := step
  obtain ⟨z1, _, get, _, buffers, active, bytes, _, _, run⟩ := step0
  have zEq : z1 = z := Option.some.inj (get.symm.trans inv.good.live.hz)
  subst zEq
  by_cases refused : z1.next_out = .null ∨ (z1.next_in = .null ∧ z1.avail_in ≠ 0) ∨
      s.mode = MEM ∨ s.mode = SYNC
  · exact rows.refused wb r h after log pending flush rc input output used i z1 s meaning fit step
      inv.good refused
  have nonnull : z1.next_out ≠ .null := fun e => refused (Or.inl e)
  have inputOk : z1.next_in = .null → z1.avail_in = 0 := fun e => by
    apply Classical.byContradiction
    intro nz
    exact refused (Or.inr (Or.inl ⟨e, nz⟩))
  have notMem : s.mode ≠ MEM := fun e => refused (Or.inr (Or.inr (Or.inl e)))
  have notSync : s.mode ≠ SYNC := fun e => refused (Or.inr (Or.inr (Or.inr e)))
  obtain ⟨l0, h0, eq0, side0, start0⟩ := rows.entry wb r h log pending wrap configured flush i z1 s
    input meaning single wbits fit inv buffers active bytes nonnull inputOk notMem notSync
  -- the run of `inflate_run` inside the call
  have live' := Live.syncAlloc inv.good.live
  have accepted : (z1.next_out == .null || (z1.next_in == .null && z1.avail_in != 0)) = false := by
    cases e1 : (z1.next_out == .null) with
    | true => exact absurd (by simpa using e1) nonnull
    | false =>
      cases e2 : (z1.next_in == .null) with
      | false => simp
      | true =>
        have zero := inputOk (by simpa using e2)
        simp [zero]
  have run1 := run
  unfold C.run Zlib.Inflate.inflate at run1
  obtain ⟨hbuf, hA, ealloc, runA⟩ := KeepProofs.bind_ok run1
  rw [allocLocalB_run h inv.good.fresh] at ealloc
  cases ealloc
  obtain ⟨res, hB, ebody, _⟩ := KeepProofs.bind_ok runA
  simp only [bind_app, stateCheck_live live', bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok live'.hz, accepted, live'.zst, castI] at ebody
  generalize hR : (ExceptT.run (inflate_run
    { strm := some r, st := some (InflateStateRef.tab i), hbuf := syncBuf h, flush := flush })).run
      IL.init (syncAlloc h) = R at ebody
  have erun : runX (inflate_run (callCtx h r i flush)) IL.init (syncAlloc h) = R := hR
  cases R with
  | error fault => cases ebody
  | ok triple =>
    obtain ⟨⟨outcome, regs⟩, h1⟩ := triple
    rw [eq0] at erun
    obtain ⟨trip, rawTrip⟩ := trips wrap configured wbits (callCtx h r i flush)
      (callFrame wrap configured log z1 input) r rfl rfl
    obtain ⟨exit, rfl, ends, side1⟩ := loop_meaning_side trip rawTrip rfl side0 start0 erun
    rw [← eq0] at erun
    exact rows.exit wb r h after log pending wrap configured flush rc input output used i z1 s exit
      regs h1 meaning single wbits fit inv step bytes erun side1 ends

/-! ## Results -/

/-- The trips of every configuration. -/
theorem trips_all (rows : TripRows) (wb : Int32) : TripsFor wb :=
  fun _ _ _ c f r _ _ => ⟨trip_meaning rows c f r, rows.rawCheck c f r⟩

/-- The trips of a zlib configuration, without the gzip header rows and the raw rows. -/
theorem trips_zlib (rows : ZlibTripRows) {wb : Int32} {bits : Nat}
    (zlib : Api.inflWbits wb.toInt = some (.zlib, bits)) : TripsFor wb := by
  intro wrap configured wbits c f r fwrap _
  rw [zlib] at wbits
  have same : Api.Wrap.zlib = wrap := (Prod.mk.inj (Option.some.inj wbits)).1
  have zlibF : f.wrap = .zlib := fwrap.trans same.symm
  exact ⟨trip_meaning_zlib rows c f r zlibF, raw_check_trip_zlib zlibF⟩

/-- The universal `MeaningStep`, from the rows. -/
theorem meaning_step_of_rows (trips : TripRows) (calls : CallRows) (unstaged : CallUnstaged) :
    MeaningStep := by
  intro wb r h after log pending flush rc input output used meaning fit step
  rcases Bool.eq_false_or_eq_true log.singleDictionary with single | single
  · exact call_meaning calls wb (trips_all trips wb) r h after log pending flush rc input output
      used single meaning fit step
  · exact unstaged wb r h after log pending flush rc input output used meaning single fit step

/-- The format meaning after every protocol history of a configuration with `wb ≥ 0`, from the
step of that configuration; every such history has a single dictionary. -/
theorem meaning_of_protocol_plain {wb : Int32} (step : MeaningStepSingle wb) (plain : 0 ≤ wb.toInt)
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) :
    ParseMeaning wb r h log pending ∧ log.singleDictionary = true := by
  induction trace with
  | init domain run => exact ⟨meaning_init domain run, rfl⟩
  | caller _ edit _ ih => exact ⟨meaning_rebuffer ih.1 edit, ih.2⟩
  | step _ fit observation ih =>
    exact ⟨step _ _ _ _ _ _ _ _ _ _ ih.2 ih.1 fit observation, ih.2⟩
  | dictionary _ _ arguments read run admitted ih =>
    refine ⟨meaning_dictionary ih.1 arguments read run admitted, ?_⟩
    have notNeg : ¬ wb.toInt < 0 := by omega
    simp [ih.2, notNeg]

/-- `ParseMeaning` after every zlib protocol history, from the zlib trip rows and the call rows. -/
theorem meaning_of_protocol_zlib (trips : ZlibTripRows) (calls : CallRows) {wb : Int32} {bits : Nat}
    (zlib : Api.inflWbits wb.toInt = some (.zlib, bits))
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace wb r h log pending) :
    ParseMeaning wb r h log pending ∧ log.singleDictionary = true := by
  have plain : 0 ≤ wb.toInt := by
    refine Classical.byContradiction fun negative => ?_
    have neg : wb.toInt < 0 := by omega
    simp only [Api.inflWbits, neg, ite_true] at zlib
    split at zlib
    · cases zlib
    · split at zlib
      · cases zlib
      · cases zlib
  exact meaning_of_protocol_plain (call_meaning calls wb (trips_zlib trips zlib)) plain trace

#print axioms call_meaning
#print axioms meaning_of_protocol_zlib
#print axioms meaning_step_of_rows

end Zlib.Inflate.Proofs
