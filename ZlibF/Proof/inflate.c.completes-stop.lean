import ZlibF.Proof.«inflate.c.completes-cause-zlib»
import ZlibF.Proof.«inflate.c.meaning-stop-short»
import ZlibF.Proof.«inflate.c.meaning-zlib»
import ZlibF.Proof.«inflate.c.meaning-call-exit»
import ZlibF.Proof.«inflate.c.completes-stops»
import ZlibF.Proof.«public-inflate»
import ZlibF.Spec.Functional.InflateCompletion

/-!
# inflate.c: a call that returns `Z_OK` or `Z_BUF_ERROR` has not read a whole zlib stream

The cause of the leave that ends the call (`loop_cause`, `zlib_cause_rows`) excludes it:
* a leave short of the field its mode waits for (`LoopMatches.starved_not_end`);
* a leave in `LEN_` with fewer than 8 bits held: the rest of the stream still holds an
  end-of-block symbol and the trailer (`lenstart_not_end`);
* a leave for want of output room holds output that is still due, so the output is shorter than
  the decoding.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open HeldWithinBounds MeaningDistance MeaningLit MeaningTypeFinal
set_option autoImplicit false

/-- A stage in `LEN_` is a Huffman-code position before a symbol. -/
theorem stage_of_len_start {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (mode : s.mode = LEN_) :
    ∃ header out final L D, stage = .body header ⟨out, final, .codes L D .none⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [mode] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · exact ⟨header, out, final, L, D, rfl⟩
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [mode] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [mode] at m
    exact absurd m (by decide)

/-- A leave in `LEN_` holding fewer than 8 bits has not read a whole wrapped stream. -/
theorem lenstart_not_end {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    (loop : LoopMatches c f h l)
    (len : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LEN_)
    (small : l.bits.toNat < 8) (wrapped : f.wrap ≠ .raw) {S decoded : List UInt8}
    (valid : Api.Layer.Decodes f.wrap f.configured f.dict S decoded)
    (whole : f.logIn ++ f.inp.take (loopRead l) = S) : False := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have mode : (loopState s l).mode = LEN_ := len zs s st hs
  obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len_start stageM mode
  obtain ⟨bodyDict, dbits, wh, consumedEq, dparsed⟩ := parsed
  rw [whole, consumedEq] at bitsEq
  obtain ⟨more, tail, aligned, srcEq, blocks, trailer⟩ :=
    body_on_source wh valid (List.prefix_refl S) (rest := held) (by rw [bitsEq])
  have moreEq : more = held := by
    rw [srcEq, List.append_assoc] at bitsEq
    exact List.append_cancel_left (List.append_cancel_left bitsEq)
  subst moreEq
  have resid := deflateParsed_resid dparsed more tail decoded aligned blocks
  obtain ⟨_, _, r, h', symbols, cont⟩ := resid
  have l1 := symbols_length symbols
  have l2 := cont_length cont
  have nonempty := wrapTrailer_ne_nil wrapped header decoded
  have trailerLen : 8 ≤ tail.length := by
    have e := congrArg List.length trailer
    rw [List.length_drop, bytesToBits_length'] at e
    have pos : 0 < (WrapTrailer f.wrap header decoded).length := by
      cases eq : WrapTrailer f.wrap header decoded with
      | nil => exact absurd eq.symm nonempty
      | cons _ _ => simp
    omega
  have heldLen : more.length = l.bits.toNat := heldBits.1
  omega

theorem params15' : Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) := by decide

theorem layer_of_zlib' {S D : List UInt8} (valid : Zlib.Decodes [] S D) :
    Api.Layer.Decodes .zlib 15 [] S D ∧ Api.FullWindow .zlib 15 S := by
  refine ⟨⟨valid, ?_⟩, Or.inl rfl⟩
  obtain ⟨cmf, flg, pre, s, rfl, ⟨_, ci, _⟩, _⟩ := valid
  exact Or.inr ⟨cmf, rfl, by omega⟩

/-- A call of a zlib protocol history (window 15, no dictionary) that returns `Z_OK` or
`Z_BUF_ERROR` after reading a whole valid stream: it filled the output and output is still due.
The other causes of its last leave are impossible (`StopShort` for the default stream). -/
theorem call_stop {r : ZStreamRef} {h after : Heap} {log : DataLog} {pending : Bool}
    {S D input output : List UInt8} {flush rc : Int32} {used : Nat} {z' : ZStream}
    (history : InflateProtocolTrace 15 r h log pending) (dictEmpty : log.dictionary = [])
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (notMemAll : ∀ i z s, Zlib.Inflate.Spec.Good h r i z s → s.mode ≠ MEM)
    (valid : Zlib.Decodes [] S D) (flushes : OrdinaryFlush flush)
    (step : DataStep .inflate h after r flush rc input output used) (hz' : r.get after = some z')
    (codes : rc = Z_OK ∨ rc = Z_BUF_ERROR) (all : log.input ++ input.take used = S) :
    z'.avail_out = 0 ∧ (log.output ++ output).length < D.length := by
  obtain ⟨meaning, single⟩ := meaning_zlib params15' history
  have meaning0 := meaning
  obtain ⟨wrap, configured, i, z, s, wbits, inv, config0, _⟩ := meaning0
  rw [params15'] at wbits
  obtain ⟨rfl, rfl⟩ : Api.Wrap.zlib = wrap ∧ 15 = configured := by
    cases wbits; exact ⟨rfl, rfl⟩
  have step0 := step
  obtain ⟨z1, z2, get, get2, buffers, active, bytes, usedEq, outBytes, run⟩ := step0
  have zEq : z1 = z := Option.some.inj (get.symm.trans inv.good.live.hz)
  subst zEq
  have z2Eq : z2 = z' := Option.some.inj (get2.symm.trans hz')
  subst z2Eq
  clear hz'
  have inLen : input.length = z1.avail_in.toNat := callEntry_bytes_length bytes
  have notBlock : flush ≠ Z_BLOCK := by
    rcases flushes with f | f | f | f | f <;> rw [f] <;> decide
  have notTrees : flush ≠ Z_TREES := by
    rcases flushes with f | f | f | f | f <;> rw [f] <;> decide
  have reach := InflateProtocolTrace.reachable history
  -- the refused calls return `Z_STREAM_ERROR`
  obtain ⟨rc', after', _, _, _, _, run', _, _, _, _, _, sErr, _⟩ :=
    inflate_public h r i z1 s flush reach inv.good fit inv.alloc buffers active
  have same' : (rc, after) = (rc', after') := Except.ok.inj (run.symm.trans run')
  cases same'
  have notStreamErr : rc ≠ Z_STREAM_ERROR := by
    rcases codes with e | e <;> rw [e] <;> decide
  have nonnull : z1.next_out ≠ .null := fun e => notStreamErr (sErr.2 (Or.inl e))
  have inputOk : z1.next_in = .null → z1.avail_in = 0 := by
    intro e
    rcases bytes with ⟨_, n0, _⟩ | ⟨_, _, _, p, _⟩
    · exact UInt32.toNat_inj.mp (by rw [n0]; rfl)
    · rw [e] at p
      cases p
  have notSync : s.mode ≠ SYNC := fun e => notStreamErr (sErr.2 (Or.inr (Or.inr e)))
  have notMem : s.mode ≠ MEM := notMemAll i z1 s inv.good
  obtain ⟨l0, h0, eq0, side0, start0⟩ := call_entry 15 r h log pending .zlib 15 flush i z1 s input
    meaning single params15' fit inv buffers active bytes nonnull inputOk notMem notSync
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
    have erun0 := erun
    rw [eq0] at erun
    let c := callCtx h r i flush
    let f := callFrame .zlib 15 log z1 input
    obtain ⟨trip, rawTrip⟩ := trips_zlib zlib_trip_rows params15' .zlib 15 params15' c f r rfl rfl
    obtain ⟨exit, rfl, ends, side1⟩ := loop_meaning_side trip rawTrip rfl side0 start0 erun
    obtain ⟨h2, how, afterEq⟩ := callExit_split inv nonnull inputOk run erun0
    rcases ends with ⟨exitEq, loopCases⟩ | needDict
    · subst exitEq
      obtain ⟨_, leaveRun⟩ : _ ∧ _ := by
        rcases how with p | ⟨_, e, _, _⟩
        · exact p
        · cases e
      have retCode := inflate_leave_ret c regs h1 rc h2 leaveRun
      rcases loopCases with loop | ⟨retEq, _⟩ | ⟨retEq, _⟩
      · -- an ordinary leave: its cause
        have loop0 := loop
        obtain ⟨_, _, _, _, _, _, _, _, ret0, _⟩ := loop0
        obtain ⟨l0', cause, _⟩ := loop_cause trip rawTrip
          (cause_zlib zlib_cause_rows c f r rfl) (show Api.Wrap.zlib ≠ .raw by decide) rfl side0 start0 erun
        obtain ⟨zc, hzc, allocator, statics, sideFn, _, bits, _⟩ := callExit_leave_side inv erun0 side1
        have regsEq : ({ regs with ret := Z_OK } : IL) = regs := by rw [← ret0]
        have leaveM := leave_meaning (ret := Z_OK) loop rfl hzc sideFn bits allocator statics nonnull
          (by rw [regsEq]; exact leaveRun)
        obtain ⟨zs', s0', sA, zA, callOut, consumed, held, stage, st', hsA, hzA, _, aIn, nOut, aOut, _,
          inEq, putEqL, callBytes, bitsEqL, parsedL, outputEqL, _, _, _, restL⟩ := leaveM
        subst afterEq
        have zAEq : zA = z2 := by
          have g := get2
          rw [callExit_get_freeWin] at g
          exact Option.some.inj (hzA.symm.trans g)
        subst zAEq
        have usedRead : used = loopRead regs :=
          callExit_used usedEq inLen aIn inEq
        have whole : f.logIn ++ f.inp.take (loopRead regs) = S := by
          rw [← usedRead]; exact all
        obtain ⟨lay, full⟩ := layer_of_zlib' valid
        have valid' : Api.Layer.Decodes f.wrap f.configured f.dict S D := by
          show Api.Layer.Decodes .zlib 15 log.dictionary S D
          rw [dictEmpty]; exact lay
        rcases cause with retNe | block | trees | ⟨left0, holds⟩ | short | ⟨lenMode, small⟩
        · exact absurd ret0 retNe
        · exact absurd block notBlock
        · exact absurd trees notTrees
        · -- no output room, holding output that is due
          refine ⟨by rw [aOut]; exact left0, ?_⟩
          have zsI : zs' = i := by
            have e : (some (InflateStateRef.tab i) : InflateStatePtr) = some (.tab zs') := st'
            simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
            exact e.symm
          have hsA' : h2.istates i = some sA := zsI ▸ hsA
          -- the call's output is the loop's
          obtain ⟨zF, sF, u0, o0, invF, accounting, _⟩ := callExit_after inv fit buffers active run
          have zFEq : zF = zA := Option.some.inj (invF.good.live.hz.symm.trans get2)
          subst zFEq
          have outLen : z1.avail_out.toNat - zF.avail_out.toNat = callOut.length := by
            obtain ⟨_, _, _, availO, _, nextO, _⟩ := accounting
            obtain ⟨ref, off, hp⟩ : ∃ ref off, z1.next_out = .ref ref off := by
              cases hq : z1.next_out with
              | null => exact absurd hq nonnull
              | ref ref off => exact ⟨ref, off, rfl⟩
            have e := nextO.symm.trans (nOut.trans putEqL)
            have fs : f.start = z1.next_out := rfl
            rw [fs, hp] at e
            simp [advance, inputAdvance] at e
            omega
          have outEq : output = callOut := by
            rw [outLen] at outBytes
            exact callExit_bytes_eq callBytes outBytes (fun _ _ g => callExit_freeWin_view g)
          -- `inf_leave` keeps the mode and the length of the decoder record
          have notMemRc : rc ≠ Z_MEM_ERROR := by rcases codes with e | e <;> rw [e] <;> decide
          have frame := ModeLen.rcFrame_inflate_leave r c rfl regs h1 rc h2 leaveRun notMemRc
          unfold ModeLen.WindowFrame ModeLen.decoderWindows at frame
          have atI := congrFun frame i
          obtain ⟨zs1, _, s1, _, st1, j1, _⟩ := side1
          have e1 : zs1 = i := by
            have e : (some (InflateStateRef.tab i) : InflateStatePtr) = some (.tab zs1) := st1
            simp only [Option.some.injEq, InflateStateRef.tab.injEq] at e
            exact e.symm
          have hs1 : h1.istates i = some s1 := e1 ▸ j1.good.live.hs
          rw [hsA', hs1] at atI
          simp only [Option.map_some, Option.some.injEq, ModeLen.counts, Prod.mk.injEq] at atI
          have holding1 := holds i s1 rfl hs1
          have holdingA : sA.mode = LIT ∨ sA.mode = MATCH ∨ (sA.mode = COPY ∧ sA.length ≠ 0) := by
            rw [atI.1, atI.2]
            exact holding1
          rcases restL with ⟨rcMem, _⟩ | ⟨_, _, smA, _⟩
          · exact absurd rcMem notMemRc
          have copies : ∀ header out final L D remaining dist,
              stage = .body header ⟨out, final, .codes L D (.copy remaining dist)⟩ → 0 < remaining := by
            intro header out final L D remaining dist e
            subst e
            obtain ⟨_, _, _, _, dparsed⟩ := parsedL
            exact copy_remaining_pos dparsed
          obtain ⟨header, pos, rfl, due⟩ := due_of_mode smA copies holdingA
          have bitsS : bytesToBits S = consumed ++ held := by rw [← whole]; exact bitsEqL
          have shorter := wrapParsed_due parsedL due bitsS valid' (List.prefix_refl S)
          have lengths := congrArg List.length outputEqL
          simp only [List.length_append, WrapStage.output] at lengths
          rw [outEq, List.length_append]
          have logOut : f.logOut = log.output := rfl
          rw [logOut] at lengths
          omega
        · exact (LoopMatches.starved_not_end loop short.2 valid' whole).elim
        · exact (lenstart_not_end loop lenMode small (show Api.Wrap.zlib ≠ .raw by decide) valid' whole).elim
      · exfalso
        rw [retEq] at retCode
        rcases retCode with e | e | ⟨_, e⟩
        · rcases codes with c' | c' <;> rw [c'] at e <;> exact absurd e (by decide)
        · rcases codes with c' | c' <;> rw [c'] at e <;> exact absurd e (by decide)
        · exact absurd e (by decide)
      · exfalso
        rw [retEq] at retCode
        rcases retCode with e | e | ⟨_, e⟩
        · rcases codes with c' | c' <;> rw [c'] at e <;> exact absurd e (by decide)
        · rcases codes with c' | c' <;> rw [c'] at e <;> exact absurd e (by decide)
        · exact absurd e (by decide)
    · exfalso
      obtain ⟨exitEq, _⟩ := needDict
      cases exitEq
      rcases how with ⟨e, _⟩ | ⟨v, e, rcEq, _⟩
      · cases e
      · cases e
        rcases codes with c' | c' <;> rw [c'] at rcEq <;> exact absurd rcEq (by decide)

end Zlib.Inflate.Proofs
