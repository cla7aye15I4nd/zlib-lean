import ZlibF.Proof.«inflate.c.meaning-call»
import ZlibF.Proof.«inflate.c.call-refused»
import ZlibF.Proof.«inflate.c.stuck-no-output»
import ZlibF.Proof.«inflate.c.default-view-run»
import ZlibF.Proof.«inflate.c.default-error-clauses»

/-!
# inflate.c: the entry rows of one `inflate` call (`CallRefused`, `CallEntry`)

* `call_refused`: a call refused at entry (`next_out` `NULL`, `next_in` `NULL` with input, the
  decoder in `MEM` or `SYNC`) runs to `Z_STREAM_ERROR` or `Z_MEM_ERROR` on the heap with the local
  buffer made and freed (`tmpFreed`). The stream and the decoder are unchanged, no input is used
  and no output made. `ParseMeaning` is re-established with the new result: the result clauses
  hold since the result is neither `Z_DATA_ERROR` nor `Z_STREAM_END`, the `MEM` clause keeps its
  output prefix, and the stage clause moves to the new heap (`SameRefs`).
* `call_entry`: an accepted call runs the `TYPE`-to-`TYPEDO` skip and `LOAD()` before the mode
  loop. The safety facts at the loop start (`CallSide`) are those of the safety proof
  (`inflate_run_default_view_entry`, `inflate_run_entry_local`), with the unread input apart
  from the fresh local buffer (`HbufInputApart`). The meaning at the loop start is
  the stage of `ParseMeaning` with nothing read or written (`LoopMatches`), or the doom of the
  input so far for a decoder in `BAD` (`LoopBad`). The skip writes `TYPEDO` only in a block
  boundary, where `BodyMatches` admits both modes.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Small facts -/

theorem callEntry_bytes_length {h : Heap} {p : BPtr} {n : Nat} {xs : List UInt8}
    (bytes : Bytes h p n xs) : xs.length = n := by
  rcases bytes with ⟨_, rfl, rfl⟩ | ⟨ref, off, a, _, _, bound, rfl⟩
  · rfl
  · simp only [List.length_take, List.length_drop, Array.length_toList]
    omega

theorem callEntry_separate_symm {p q : BPtr} {n m : Nat} (separate : Separate p n q m) :
    Separate q m p n := by
  rcases separate with empty | empty | apart
  · exact Or.inr (Or.inl empty)
  · exact Or.inl empty
  · right
    right
    cases p with
    | null => cases q <;> trivial
    | ref r i =>
      cases q with
      | null => trivial
      | ref s j =>
        rcases apart with different | before | after
        · exact Or.inl (Ne.symm different)
        · exact Or.inr (Or.inr before)
        · exact Or.inr (Or.inl after)

/-- Making and freeing the local buffer keeps the tables and the window of the state. -/
theorem sameRefs_tmpFreed {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r i z s) : SameRefs h (tmpFreed h) s := by
  constructor
  · intro ref _ _
    cases ref <;> first | rfl | simp [Space.get, tmpFreed, freeWin, syncBuf, syncAlloc]
  · intro ref _ _
    exact byte_view_tmpFreed good.fresh ref

/-- The local buffer and a state write that keeps the code array keep the tables and the
window of the state. -/
theorem sameRefs_entry {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r i z s) (state0 : InflateState) (codesEq : state0.codes = s.codes) :
    SameRefs h (setI (syncAlloc h) i state0) s := by
  constructor
  · intro ref _ _
    cases ref with
    | istate_codes id =>
      by_cases e : id = i
      · subst e
        simp [Space.get, setI, good.live.hs, codesEq]
      · simp [Space.get, setI, upd_ne _ _ _ _ e]
    | st_lenfix => rfl
    | st_distfix => rfl
  · intro ref offset pointer
    rw [byte_view_get_setI]
    rcases good.inv.win.block with null | ⟨w, a, windowEq, get, _, _⟩
    · rw [null] at pointer
      cases pointer
    · rw [windowEq] at pointer
      cases pointer
      exact (byte_view_syncAlloc (ref := .blk w) good.fresh get).1.trans get.symm

/-- `MEM` past the entry checks: `return Z_MEM_ERROR;` with the local buffer made and freed. -/
theorem inflate_mem_run {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r i z s) (flush : Int32)
    (accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false)
    (mem : s.mode = MEM) :
    C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (Z_MEM_ERROR, tmpFreed h) := by
  have allocated := current.sync_alloc
  unfold C.run Zlib.Inflate.inflate
  rw [bind_app, allocLocalB_run h current.good.fresh]
  simp only []
  rw [bind_app]
  let c : Ctx := ⟨some r, some (.tab i), syncBuf h, flush⟩
  have env : Env c (syncAlloc h) r i z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have loop := stuck_inflate_run_MEM env mem
  simp only [bind_app, stateCheck_live allocated.good.live,
    bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
  unfold runX at loop
  dsimp only [c] at loop
  erw [loop]
  simp only []
  change (do freeB (syncBuf h); pure Z_MEM_ERROR) (syncAlloc h) = .ok (Z_MEM_ERROR, tmpFreed h)
  rw [bind_app]
  dsimp only [syncBuf]
  rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
  rfl

/-! ## The refused call -/

theorem call_refused : CallRefused := by
  intro wb r h after log pending flush rc input output used i z s meaning _ step good refused
  obtain ⟨wrap, configured, i', z', s', wbits, inv', config, _, _, bad, memory, stageClause⟩ :=
    meaning
  have zEq : z = z' := Option.some.inj (good.live.hz.symm.trans inv'.good.live.hz)
  subst zEq
  have iEq : i = i' := by
    have e := good.live.zst.symm.trans inv'.good.live.zst
    cases e
    rfl
  subst iEq
  have sEq : s = s' := Option.some.inj (good.live.hs.symm.trans inv'.good.live.hs)
  subst sEq
  obtain ⟨code, run0, codeFacts⟩ : ∃ code,
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (code, tmpFreed h) ∧
      (code = Z_STREAM_ERROR ∨ code = Z_MEM_ERROR) := by
    by_cases early : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC
    · exact ⟨_, inflate_refused_run inv' flush early, Or.inl rfl⟩
    · have mem : s.mode = MEM := by
        rcases refused with a | b | c | d
        · exact absurd (Or.inl a) early
        · exact absurd (Or.inr (Or.inl b)) early
        · exact c
        · exact absurd (Or.inr (Or.inr d)) early
      have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
        cases e1 : (z.next_out == .null) with
        | true => exact absurd (Or.inl (by simpa using e1)) early
        | false =>
          cases e2 : (z.next_in == .null) with
          | false => simp
          | true =>
            cases e3 : (z.avail_in != 0) with
            | false => simp
            | true =>
              exact absurd (Or.inr (Or.inl ⟨by simpa using e2, by simpa using e3⟩)) early
      exact ⟨_, inflate_mem_run inv' flush accepted mem, Or.inr rfl⟩
  obtain ⟨z1, z2, get1, get2, _, _, _, usedEq, outBytes, run⟩ := step
  have same := run.symm.trans run0
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨rcEq, afterEq⟩ := same
  subst rcEq afterEq
  have next : InflateInv (tmpFreed h) r i z s :=
    inv'.sync_alloc.free_local (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn])
  have z1Eq : z1 = z := Option.some.inj (get1.symm.trans inv'.good.live.hz)
  have z2Eq : z2 = z := Option.some.inj (get2.symm.trans next.good.live.hz)
  have usedZero : used = 0 := by rw [usedEq, z1Eq, z2Eq, Nat.sub_self]
  have outNil : output = [] := by
    have length := callEntry_bytes_length outBytes
    rw [z1Eq, z2Eq, Nat.sub_self] at length
    exact List.eq_nil_of_length_eq_zero length
  subst usedZero outNil
  have rcNotData : rc ≠ Z_DATA_ERROR := by
    rcases codeFacts with e | e <;> rw [e] <;> decide
  have rcNotEnd : rc ≠ Z_STREAM_END := by
    rcases codeFacts with e | e <;> rw [e] <;> decide
  have rcNotDict : (rc == Z_NEED_DICT) = false := by
    rcases codeFacts with e | e <;> rw [e] <;> decide
  have sameRefs := sameRefs_tmpFreed inv'.good
  have logEq : logAfterCall log rc input [] 0 =
      { log with result := rc, finished := log.finished || rc == Z_STREAM_END } := by
    simp [logAfterCall]
  rw [logEq, rcNotDict]
  refine ⟨wrap, configured, i, z, s, wbits, next, config, fun e => absurd e rcNotData,
    fun e => absurd e rcNotEnd, bad, ?_, ?_⟩
  · intro single isMem
    obtain ⟨_, prefixes⟩ := memory single isMem
    refine ⟨fun e => absurd e rcNotEnd, ?_⟩
    intro source decoded valid full pre
    obtain ⟨outPre, _, _⟩ := prefixes source decoded valid full pre
    exact ⟨outPre, rcNotData, fun e => absurd e rcNotEnd⟩
  · intro single notBad notMem notSync
    obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageM, wrapM, outputEq, _⟩ :=
      stageClause single notBad notMem notSync
    exact ⟨consumed, held, stage, inputBits, heldBits, parsed, stageM.frameRefs sameRefs,
      wrapM.frameRefs sameRefs, outputEq, fun e => absurd e (by decide)⟩

/-! ## The entry of an accepted call -/

/-- The stage facts of `ParseMeaning` as the loop facts with nothing written in the call. -/
theorem loopStage_of_stage {h : Heap} {s : InflateState} {f : LoopFrame} {stage : WrapStage}
    (m : StageMatches h s f.wrap f.dict stage) (out : stage.output = f.logOut) :
    LoopStageMatches h s f f.logOut stage := by
  cases stage with
  | header _ => exact m
  | needDict _ => exact m
  | body header pos =>
    obtain ⟨body, window, check⟩ := m
    change pos.out = f.logOut at out
    rw [out] at window check
    exact ⟨body, window, check⟩
  | trailer header o bytes =>
    obtain ⟨modes, check⟩ := m
    change o = f.logOut at out
    rw [← out]
    exact ⟨modes, check⟩
  | done _ => exact m

/-- The `TYPE`-to-`TYPEDO` skip keeps the loop stage facts: in `TYPE` the stage is a block
boundary or the end of the last block, where both modes are admitted. -/
theorem loopStage_typedo {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} {wrap : Api.Wrap} {configured : Nat} {dict : List UInt8}
    (type : s.mode = TYPE) (m : LoopStageMatches h s f checked stage)
    (w : WrapMatches h s wrap configured dict stage) :
    LoopStageMatches h { s with mode := TYPEDO } f checked stage ∧
      WrapMatches h { s with mode := TYPEDO } wrap configured dict stage := by
  cases stage with
  | header _ =>
    obtain ⟨_, high⟩ := m
    rw [type] at high
    exact absurd high (by decide)
  | needDict _ =>
    have e : s.mode = DICT := m
    exact absurd (type.symm.trans e) (by decide)
  | body header pos =>
    obtain ⟨out, final, st⟩ := pos
    obtain ⟨body, window, check⟩ := m
    cases st with
    | boundary =>
      obtain ⟨_, rest⟩ := body
      exact ⟨⟨⟨Or.inr rfl, rest⟩, window, check⟩, w⟩
    | finished =>
      obtain ⟨_, rest⟩ := body
      exact ⟨⟨⟨Or.inr rfl, rest⟩, window, check⟩, w⟩
    | storedHeader =>
      obtain ⟨e, _⟩ := body
      exact absurd (type.symm.trans e) (by decide)
    | stored remaining =>
      obtain ⟨e | e, _⟩ := body <;> exact absurd (type.symm.trans e) (by decide)
    | dynamicHeader header =>
      obtain ⟨dynamic, _⟩ := body
      rcases dynamic with ⟨e, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨e, _⟩ | ⟨e, _⟩⟩ <;>
        exact absurd (type.symm.trans e) (by decide)
    | codes L D pending =>
      obtain ⟨_, _, _, modes⟩ := body
      cases pending with
      | none =>
        obtain ⟨e | e, _⟩ := modes <;> exact absurd (type.symm.trans e) (by decide)
      | lengthExtra _ =>
        obtain ⟨e, _⟩ := modes
        exact absurd (type.symm.trans e) (by decide)
      | distance _ =>
        obtain ⟨e, _⟩ := modes
        exact absurd (type.symm.trans e) (by decide)
      | distanceExtra _ _ =>
        obtain ⟨e, _⟩ := modes
        exact absurd (type.symm.trans e) (by decide)
      | copy _ _ =>
        obtain ⟨e, _⟩ := modes
        exact absurd (type.symm.trans e) (by decide)
      | literal _ =>
        obtain ⟨e, _⟩ := modes
        exact absurd (type.symm.trans e) (by decide)
  | trailer _ _ _ =>
    obtain ⟨e | e, _⟩ := m <;> exact absurd (type.symm.trans e) (by decide)
  | done _ =>
    have e : s.mode = DONE := m
    exact absurd (type.symm.trans e) (by decide)

theorem call_entry : CallEntry := by
  intro wb r h log pending wrap configured flush i z s input meaning single wbits fit inv buffers
    active bytes nonnull inputValid notMem notSync
  obtain ⟨wrap', configured', i', z', s', wbits', inv', config, _, _, bad, _, stageClause⟩ :=
    meaning
  have zEq : z = z' := Option.some.inj (inv.good.live.hz.symm.trans inv'.good.live.hz)
  subst zEq
  have iEq : i = i' := by
    have e := inv.good.live.zst.symm.trans inv'.good.live.zst
    cases e
    rfl
  subst iEq
  have sEq : s = s' := Option.some.inj (inv.good.live.hs.symm.trans inv'.good.live.hs)
  subst sEq
  have wEq := wbits.symm.trans wbits'
  simp only [Option.some.injEq, Prod.mk.injEq] at wEq
  obtain ⟨wrapEq, configuredEq⟩ := wEq
  subst wrapEq configuredEq
  -- the safety facts at the loop start
  have fresh := inv.good.fresh
  have invariant : DefaultStateJ h r i z s := (inv.to_origin fit).toDefaultStateJ
  have allocated := default_state_syncAlloc invariant
  have env : Env (callCtx h r i flush) (syncAlloc h) r i z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have local_ : HeaderLocal (callCtx h r i flush) (syncAlloc h) r s (dispatchRegs z s) :=
    entry_header_local fresh (ActiveHeader.entry active inv.good.live) flush
  obtain ⟨h0, state0, bs, entryRun, currentJ, currentEnv, packet, bits, sizes, frame, heapEq,
    stateEq⟩ :=
    inflate_run_default_view_entry env allocated (streamBuffers_syncAlloc fresh buffers) nonnull
      inputValid
  have entryLocal := inflate_run_entry_local allocated currentJ sizes frame heapEq stateEq local_
  -- the unread input lies in a block of `h`, never in the fresh local buffer
  have apart : HbufInputApart (callCtx h r i flush) (dispatchRegs z state0) := by
    intro nonzero b o ref off hb hn
    have hbEq := hb
    dsimp only [callCtx, syncBuf] at hbEq
    cases hbEq
    change z.next_in = .ref ref off at hn
    intro sameRef
    subst sameRef
    rcases bytes with ⟨nullIn, _, _⟩ | ⟨ref', off', a, pointer, get, _, _⟩
    · rw [hn] at nullIn
      cases nullIn
    · rw [hn] at pointer
      cases pointer
      have absent := (fresh_dead inv.good.fresh (Nat.le_refl h.nextBlk)).1
      have present : h.bytes h.nextBlk = some a := get
      rw [present] at absent
      cases absent
  refine ⟨dispatchRegs z state0, h0, entryRun,
    ⟨i, z, state0, rfl, rfl, currentJ, ⟨bs, packet⟩, entryLocal, bits, apart⟩, ?_⟩
  -- nothing read or written yet
  have regsRead : loopRead (dispatchRegs z state0) = 0 := by simp [loopRead, dispatchRegs]
  have regsPending : loopPending (dispatchRegs z state0) = 0 := by
    simp [loopPending, dispatchRegs]
  have inputLen : input.length = z.avail_in.toNat := callEntry_bytes_length bytes
  have notType : s.mode = BAD → state0 = s := by
    intro isBad
    rw [stateEq, ite_eq_right (by rw [isBad]; decide)]
  by_cases isBad : s.mode = BAD
  · -- a decoder in `BAD`: the input so far has no valid completion
    right
    have st0 := notType isBad
    refine ⟨i, state0, rfl, currentEnv.hs, by rw [st0]; exact isBad, ?_, Nat.le_refl _,
      inputLen.symm, ?_⟩
    · show ConfigMatches state0 wrap configured
      rw [st0]
      exact config
    · intro source decoded valid full pre
      change (log.input ++ input.take (loopRead (dispatchRegs z state0))) <+: source at pre
      rw [regsRead, List.take_zero, List.append_nil] at pre
      exact bad single isBad source decoded valid full pre
  · left
    obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageM, wrapM, outputEq, _⟩ :=
      stageClause single isBad notMem notSync
    have codesEq : state0.codes = s.codes := by
      rw [stateEq]
      split <;> rfl
    have sameRefs := sameRefs_entry inv.good state0 codesEq
    have stage0 : StageMatches h0 s wrap log.dictionary stage := by
      rw [heapEq]
      exact stageM.frameRefs sameRefs
    have wrap0 : WrapMatches h0 s wrap configured log.dictionary stage := by
      rw [heapEq]
      exact wrapM.frameRefs sameRefs
    have loopStage : LoopStageMatches h0 s (callFrame wrap configured log z input) log.output
        stage :=
      loopStage_of_stage (f := callFrame wrap configured log z input) stage0 outputEq.symm
    have final : LoopStageMatches h0 state0 (callFrame wrap configured log z input) log.output
          stage ∧ WrapMatches h0 state0 wrap configured log.dictionary stage ∧
        HeldBits state0 held ∧ ConfigMatches state0 wrap configured := by
      by_cases type : s.mode = TYPE
      · rw [stateEq, ite_eq_left type]
        obtain ⟨stageNext, wrapNext⟩ := loopStage_typedo type loopStage wrap0
        refine ⟨stageNext, wrapNext, heldBits, ?_⟩
        obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
        exact ⟨c1, c2, c3, c4, c5, by show TYPEDO ≠ SYNC; decide⟩
      · rw [stateEq, ite_eq_right type]
        exact ⟨loopStage, wrap0, heldBits, config⟩
    -- the output room
    obtain ⟨_, writable, unowned⟩ : (∃ xs, Bytes h0 z.next_out z.avail_out.toNat xs) ∧
        (true = true → Writable h0 z.next_out z.avail_out.toNat) ∧
        ∀ b, ByteRoot z.next_out b → ¬ StreamOwned h0 r b := by
      rcases packet.output.range with nullOut | range
      · exact absurd nullOut packet.output.nonnull
      · exact range
    have room := writable rfl
    have sepWin : Separate z.next_out z.avail_out.toNat state0.window state0.wsize.toNat := by
      rcases currentJ.good.inv.win.block with null | ⟨w, a, windowEq, _, _, _⟩
      · rw [null]
        cases z.next_out <;> exact Or.inr (Or.inr trivial)
      · rw [windowEq]
        cases pointer : z.next_out with
        | null => exact Or.inr (Or.inr trivial)
        | ref ref off =>
          refine Or.inr (Or.inr (Or.inl ?_))
          intro sameRef
          subst sameRef
          have owned : StreamOwned h0 r w :=
            (currentJ.good.streamOwned_iff w).mpr (Or.inr windowEq)
          have root : ByteRoot z.next_out w := by
            rw [pointer]
            exact rfl
          exact unowned w root owned
    have outBytes : Bytes h0 z.next_out 0 [] := by
      rcases room with ⟨nullOut, _⟩ | ⟨ref, off, a, pointer, get, _, bound⟩
      · exact absurd nullOut nonnull
      · exact Or.inr ⟨ref, off, a, pointer, get, by omega, by simp⟩
    have bitInv : BitInv h0 (dispatchRegs z state0) input := by
      refine ⟨inputLen.symm, ?_, packet.bits.hold_lt⟩
      rcases bytes with ⟨_, _, rfl⟩ | ⟨ref, off, a, pointer, get, bound, values⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨ref, a, off, pointer, ?_, by omega, ?_⟩
        · rw [heapEq, byte_view_get_setI]
          exact (byte_view_syncAlloc fresh get).1
        · rw [inputLen]
          exact values
    have checked : (log.output ++ ([] : List UInt8)).take
        ((log.output ++ ([] : List UInt8)).length - loopPending (dispatchRegs z state0)) =
          log.output := by
      rw [regsPending]
      simp
    refine ⟨i, state0, [], consumed, held, stage, rfl, currentEnv.hs, rfl, final.2.2.2,
      Nat.le_refl _, inputLen.symm, ?_, Nat.le_refl _, ?_, (inputAdvance_zero _).symm, outBytes,
      room, callEntry_separate_symm packet.separate, sepWin, Or.inl rfl, ?_, final.2.2.1, parsed,
      ?_, final.2.1, ?_⟩
    · change BitInv h0 (dispatchRegs z state0) (input.drop (loopRead (dispatchRegs z state0)))
      rw [regsRead, List.drop_zero]
      exact bitInv
    · rw [regsPending]
      exact ⟨Nat.le_refl _, fun _ _ _ => rfl⟩
    · change bytesToBits (log.input ++ input.take (loopRead (dispatchRegs z state0))) =
        consumed ++ held
      rw [regsRead, List.take_zero, List.append_nil]
      exact inputBits
    · change LoopStageMatches h0 state0 (callFrame wrap configured log z input)
        ((log.output ++ ([] : List UInt8)).take
          ((log.output ++ ([] : List UInt8)).length - loopPending (dispatchRegs z state0))) stage
      rw [checked]
      exact final.1
    · change stage.output = log.output ++ []
      rw [List.append_nil]
      exact outputEq.symm

#print axioms call_refused
#print axioms call_entry

end Zlib.Inflate.Proofs
