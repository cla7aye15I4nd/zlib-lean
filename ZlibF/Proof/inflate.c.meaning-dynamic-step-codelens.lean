import ZlibF.Proof.«inflate.c.meaning-dynamic-step-common»

/-! `case CODELENS` of `inflate.c.meaning-dynamic-steps`. -/

namespace Zlib.Inflate.Proofs.MeaningDynamicSteps
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningDynamic
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-! ## `CODELENS` -/

section CodeLens
open Zlib.Inflate.Proofs.MeaningCodeLens Zlib.Inflate.Proofs.MeaningDynamicTables

/-- The bits read in a call after the held bits. -/
theorem read_take {f : LoopFrame} {l : IL} {used : Nat} {consumed : List Bool}
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ natBits l.bits.toNat l.hold.toNat)
    (ub : used ≤ (f.inp.drop (loopRead l)).length) :
    bytesToBits (f.logIn ++ f.inp.take (loopRead l + used)) =
      consumed ++ (stream l (f.inp.drop (loopRead l))).take (l.bits.toNat + 8 * used) := by
  rw [bits_take bitsEq]
  congr 1
  have split : bytesBits (f.inp.drop (loopRead l)) =
      bytesBits ((f.inp.drop (loopRead l)).take used) ++ bytesBits ((f.inp.drop (loopRead l)).drop used) := by
    rw [← bytesBits_append, List.take_append_drop]
  unfold stream
  rw [split, ← List.append_assoc]
  exact (List.take_left' (by rw [List.length_append, natBits_length, bytesBits_length, List.length_take]; omega)).symm

theorem trace_empty {cl : List Nat} {T : Nat} {before after : List Nat} {X : List Bool}
    (zero : ∀ k, cl.getD k 0 = 0) (lt : after.length < T) :
    ZlibF.Math.CodeLengthPrefix.Trace cl T before X after := by
  intro future rest lens p
  exact (codeLens_none p lt (dec_none_zero zero _)).elim

set_option maxHeartbeats 16000000 in
/-- `case CODELENS` keeps the format meaning. It reads the code lengths
across calls, an item at a time (`DeflateParsed.dynamicBits` with the items
read). Without input it leaves (`have = 0`) with the parse of the lengths
read so far in both directions and the held-bit bound. A repeat that runs
past the total or has no previous length goes to `BAD`: by the converse of
the parse no completion of the header passes through it. With all lengths
read, a missing end-of-block length or an unacceptable literal/length or
distance code goes to `BAD`: the parse of the header is complete and is not
a `DynamicHeader`. Otherwise both tables are installed with `Inv` and
`StableQuery` (`DeflateParsed.dynamicDone`), and the call leaves for
`Z_TREES` (in `LEN_`, fewer than 8 bits held) or, for another flush, falls through to `LEN_` with fewer than 8
held bits.

The safety invariant of the decoder state supplies `wf` (array sizes) and
`lengths` (`CodeLengthInvariant`: the table is the state's `codes`, the
counts, the initialized lengths). The installed table's content
classification comes from `LoopMatches` (`DynamicMatches`). -/
theorem codelens_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (codelensMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = CODELENS)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed)
    (lengths : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → CodeLengthInvariant zs s) :
    (∃ result l' h', runX (inflate_CODELENS c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ ((l'.have_ = 0 ∧ LeaveShort c h' l') ∨
          (c.flush = Z_TREES ∧ (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = LEN_) ∧
            l'.bits.toNat < 8)) ∧
          LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
         LoopRefuted f l'))) ∨
    (c.flush ≠ Z_TREES ∧ ∃ l' h', runX (inflate_CODELENS c) l h = runX (inflate_LEN_ c) l' h' ∧
      loopRead l ≤ loopRead l' ∧
      (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = LEN_) ∧
      LoopMatches c f h' l') := by
  obtain ⟨zs, s, callOut, consumedP, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have mode : s.mode = CODELENS := codelensMode zs s st hs
  have wfS := wf zs s st hs
  have invS := lengths zs s st hs
  obtain ⟨pointer, table, nlenB, ndistB, haveB, initialized⟩ := invS mode
  obtain ⟨header, out, final, hdr, rfl⟩ := stage_of_dynamic stageM (Or.inr (Or.inr mode))
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨dyn, last⟩, window, check⟩ := stageM
  obtain ⟨hlit, hdist, hclen, r1, r2, r3, read1, read2, read3, counts, nlenEq, ndistEq, ncodeEq,
      cl, r4, ref, offset, codes, readCL, lencodeEq, getCodes, meaning0, haveLt, trace, conv, emptyF, heldB⟩ :
      ∃ (hlit hdist hclen : Nat) (r1 r2 r3 : List Bool),
        readBits 5 hdr = some (hlit, r1) ∧ readBits 5 r1 = some (hdist, r2) ∧
        readBits 4 r2 = some (hclen, r3) ∧ DynamicCountsOK hlit hdist ∧
        s.nlen.toNat = hlit + 257 ∧ s.ndist.toNat = hdist + 1 ∧ s.ncode.toNat = hclen + 4 ∧
        ∃ (cl : List Nat) (r4 : List Bool) (ref : CodeRef) (offset : Nat) (codes : Array Code),
          readCodeLenLens (hclen + 4) r3 = some (cl, r4) ∧
          s.lencode = .ref ref offset ∧ Space.get h ref = some codes ∧
          Zlib.Inftrees.Proofs.CodeLengthContents codes offset s.lenbits.toNat cl ∧
          s.«have».toNat < hlit + 257 + (hdist + 1) ∧
          ZlibF.Math.CodeLengthPrefix.Trace cl (hlit + 257 + (hdist + 1)) [] r4 (lensPrefix s) ∧
          (∀ future rest lens, CodeLens cl (hlit + 257 + (hdist + 1)) [] (r4 ++ future) rest lens →
            CodeLens cl (hlit + 257 + (hdist + 1)) (lensPrefix s) future rest lens) ∧
          ((∀ k, cl.getD k 0 = 0) →
            (∀ i, i < 2 ^ s.lenbits.toNat → codes[offset + i]? = some ⟨64, 1, 0⟩) ∧
            ∀ k, k < s.«have».toNat → s.lens.getD k 0 = 0) ∧
          (l.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧ ¬ CodeLenItem cl (heldShort (loopState s l)))) := by
    rcases dyn with ⟨m, _, _⟩ | ⟨hlit, hdist, hclen, r1, r2, r3, read1, read2, read3, counts, e1, e2, e3,
      ⟨m, _⟩ | ⟨_, rest⟩⟩
    · exact absurd (mode.symm.trans m) (by decide)
    · exact absurd (mode.symm.trans m) (by decide)
    · exact ⟨hlit, hdist, hclen, r1, r2, r3, read1, read2, read3, counts, e1, e2, e3, rest⟩
  rw [pointer] at lencodeEq
  obtain ⟨rfl, rfl⟩ := Ptr.ref.inj lencodeEq
  rw [CodeRef.get_istate_codes hs] at getCodes
  cases getCodes
  have Ttot : s.nlen.toNat + s.ndist.toNat = hlit + 257 + (hdist + 1) := by omega
  have lensPrefixEq : lensPrefix s = actualLengthPrefix s := rfl
  rw [← Ttot, lensPrefixEq] at trace conv
  have acc := meaning0.acceptable
  -- the table cells
  have emptyCells : (∀ k, cl.getD k 0 = 0) → ∀ i, i < 2 ^ s.lenbits.toNat →
      s.codes[0 + i]? = some ⟨64, 1, 0⟩ := fun e => (emptyF e).1
  have ordinary : (¬ ∀ k, cl.getD k 0 = 0) → ∀ i, i < 2 ^ s.lenbits.toNat →
      ∃ e, s.codes[i]? = some e ∧ e.op = 0 := by
    intro ne
    have cont := meaning0
    rcases cont.layout with ⟨root1, _, c0, c1⟩ | ord
    · exfalso
      obtain ⟨k, nzk⟩ := Classical.not_forall.mp ne
      obtain ⟨value, suffix, entry, rd, cellGet, op, _⟩ :=
        meaning0.forward _ _ _ (dec_word acc nzk (List.replicate 15 false))
      have vb := (rb_split rd).2
      rw [root1] at vb
      have : value = 0 ∨ value = 1 := by omega
      rcases this with rfl | rfl
      · rw [c0] at cellGet; cases cellGet; exact absurd op (by decide)
      · rw [c1] at cellGet; cases cellGet; exact absurd op (by decide)
    · intro i inside
      obtain ⟨e, get, op⟩ := ord i inside
      exact ⟨e, by simpa using get, op⟩
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have bound : l.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
      ¬ CodeLenItem cl (natBits (l.bits.toNat - 8) l.hold.toNat)) := by
    have e := MeaningDistance.heldShort_eq (loopState s l)
    rw [e] at heldB
    exact heldB
  have more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat := by omega
  obtain ⟨result, regs, after, lensA, haveA, used, consumed, runL, ub, keep, nxt, szA, hbA, valsA, res⟩ :=
    cl_loop strm st hz hs wfS.1 mode invS meaning0.toCodeLengthMeaning ordinary emptyCells more (fun e => (emptyF e).2) binv bound
  have haveOld := binv.have_eq
  simp only [List.length_drop] at haveOld
  have ub' : used ≤ (f.inp.drop (loopRead l)).length := ub
  simp only [List.length_drop] at ub
  have rb := read_take bitsEq ub'
  have sLen := tcStream_length binv
  have readOf : ∀ (hx : Heap), BitInv hx regs ((f.inp.drop (loopRead l)).drop used) →
      loopRead regs = loopRead l + used ∧ regs.have_.toNat + used = l.have_.toNat := by
    intro hx inv
    have a := inv.have_eq
    simp only [List.length_drop] at a
    constructor
    · simp only [loopRead, keep.1]
      simp only [loopRead] at ub
      omega
    · simp only [loopRead] at ub
      omega
  have heldOf : ∀ (hx : Heap), BitInv hx regs ((f.inp.drop (loopRead l)).drop used) →
      stream l (f.inp.drop (loopRead l)) = consumed ++ stream regs ((f.inp.drop (loopRead l)).drop used) →
      (stream l (f.inp.drop (loopRead l))).take (l.bits.toNat + 8 * used) =
        consumed ++ natBits regs.bits.toNat regs.hold.toNat := by
    intro hx inv source
    have a := congrArg List.length source
    rw [List.length_append, sLen, tcStream_length inv] at a
    simp only [List.length_drop] at a
    rw [show l.bits.toNat + 8 * used = consumed.length + regs.bits.toNat by omega, take_split source]
    congr 1
    unfold stream
    exact List.take_left' (natBits_length _ _)
  have window' := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  have hz' : ∀ s' : InflateState, r.get (setI h zs s') = some z := fun s' => by simpa using hz
  have lenSt : ∀ (lensX : Array UInt16) (haveX : UInt32),
      (actualLengthPrefix { s with lens := lensX, «have» := haveX }).length = haveX.toNat :=
    fun _ _ => Zlib.Inftrees.Proofs.lensOf_length _ _
  rcases res with ⟨rfl, afterEq, invA, have0, ltA, source, ltrace, zerosA, bndA, fullA⟩ |
    ⟨rfl, ⟨sB, getB, modeB⟩, badAll, invB, doom⟩ |
    ⟨rfl, afterEq, invC, doneA, source, ltrace, zerosA, small⟩
  · -- waiting for input
    left
    subst afterEq
    obtain ⟨readEq, usedEq⟩ := readOf _ invA
    have runW : runX (inflate_CODELENS c) l h =
        .ok ((.error Ex.leave, regs), setI h zs { s with lens := lensA, «have» := haveA }) := by
      rw [inflate_CODELENS_eq, runX_bind, runL]
    have binvR : BitInv h regs (f.inp.drop (loopRead regs)) := by
      rw [readEq, ← List.drop_drop]; exact MeaningLength.bitInv_unsetI invA
    have bitsR : bytesToBits (f.logIn ++ f.inp.take (loopRead regs)) =
        (consumedP ++ consumed) ++ natBits regs.bits.toNat regs.hold.toNat := by
      rw [readEq, rb, heldOf _ invA source, List.append_assoc]
    obtain ⟨a1, a2, a3⟩ := counts_append (more := consumed) read1 read2 read3
    have readCL' := ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ consumed readCL
    have moved := loop_move (s' := { s with lens := lensA, «have» := haveA }) (l' := regs) (j := used)
      (pos := ⟨out, final, .dynamicHeader (hdr ++ consumed)⟩) st retOk config
      haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep usedEq nxt binvR bitsR
      (HeldBits.of_natBits (s := loopState { s with lens := lensA, «have» := haveA } regs) binvR.hold_lt)
      wrapHeader (by rw [consumedEq, List.append_assoc]) (DeflateParsed.dynamicBits consumed deflate)
      ⟨Or.inr ⟨hlit, hdist, hclen, r1 ++ consumed, r2 ++ consumed, r3 ++ consumed, a1, a2, a3, counts,
          nlenEq, ndistEq, ncodeEq,
          Or.inr ⟨mode, cl, r4 ++ consumed, .istate_codes zs, 0, ({ s with lens := lensA, «have» := haveA } : InflateState).codes, readCL', pointer,
            CodeRef.get_istate_codes (setI_istates_same h zs ({ s with lens := lensA, «have» := haveA } : InflateState)), meaning0,
            by show haveA.toNat < _; omega,
            by
              rw [← Ttot]
              show ZlibF.Math.CodeLengthPrefix.Trace cl _ [] (r4 ++ consumed)
                (actualLengthPrefix { s with lens := lensA, «have» := haveA })
              by_cases empty : ∀ k, cl.getD k 0 = 0
              · exact trace_empty empty (by rw [lenSt]; exact ltA)
              · exact trace.trans (ltrace empty).1,
            by
              rw [← Ttot]
              intro fut rest lens p
              show CodeLens cl _ (actualLengthPrefix { s with lens := lensA, «have» := haveA }) fut rest lens
              by_cases empty : ∀ k, cl.getD k 0 = 0
              · exact (codeLens_none p (by simp only [List.length_nil]; omega) (dec_none_zero empty _)).elim
              · rw [List.append_assoc] at p
                exact (ltrace empty).2 _ _ _ (conv _ _ _ p),
            fun empty => ⟨emptyCells empty, zerosA empty⟩,
            by
              rw [MeaningDistance.heldShort_eq]
              exact bndA⟩⟩, last⟩
      (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
    have short : LeaveShort c (setI h zs { s with lens := lensA, «have» := haveA }) regs := by
      refine LeaveShort.of_state st (setI_istates_same h zs _) (ShortAt.codelens mode ?_)
      intro ref' offset' codes' cl' ptr' get' m' item
      have ptr'' : s.lencode = .ref ref' offset' := ptr'
      rw [pointer] at ptr''
      obtain ⟨rfl, rfl⟩ := Ptr.ref.inj ptr''
      rw [CodeRef.get_istate_codes (setI_istates_same h zs _)] at get'
      cases get'
      exact fullA (codeLenItem_meaning meaning0.toCodeLengthMeaning m' item)
    exact ⟨_, _, _, runW, Or.inl ⟨rfl, Or.inl ⟨have0, short⟩, moved⟩⟩
  · -- a bad repeat
    left
    obtain ⟨readEq, _⟩ := readOf _ invB
    have tailB : runX (clTail c) regs after = .ok ((.ok (), regs), after) := by
      unfold clTail
      rw [st]
      simp [runX_bind, runX_lift, rdI_eq, getB, modeB, runX_pure]
    have runB : runX (inflate_CODELENS c) l h = .ok ((.ok (), regs), after) := by
      rw [inflate_CODELENS_eq, runX_bind, runL]
      exact tailB
    refine ⟨.ok (), regs, after, runB, Or.inr ⟨rfl, by omega, badAll, ?_⟩⟩
    apply refuted_of_aligned (rest := (stream l (f.inp.drop (loopRead l))).take (l.bits.toNat + 8 * used))
      wrapHeader deflate
    · rw [readEq, rb, consumedEq]
    · intro more tail outF _ resid
      obtain ⟨_, _, body, _⟩ := resid
      cases body with
      | dynamic q1 q2 q3 _ q5 _ q7 =>
        obtain ⟨a1, a2, a3⟩ := counts_append
          (more := (stream l (f.inp.drop (loopRead l))).take (l.bits.toNat + 8 * used) ++ more) read1 read2 read3
        rw [a1] at q1
        simp only [Option.some.injEq, Prod.mk.injEq] at q1
        obtain ⟨rfl, rfl⟩ := q1
        rw [a2] at q2
        simp only [Option.some.injEq, Prod.mk.injEq] at q2
        obtain ⟨rfl, rfl⟩ := q2
        rw [a3] at q3
        simp only [Option.some.injEq, Prod.mk.injEq] at q3
        obtain ⟨rfl, rfl⟩ := q3
        rw [ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ _ readCL] at q5
        simp only [Option.some.injEq, Prod.mk.injEq] at q5
        obtain ⟨rfl, rfl⟩ := q5
        rw [← Ttot] at q7
        exact doom more _ _ (conv _ _ _ q7)
  · -- all lengths read
    subst afterEq
    obtain ⟨readEq, usedEq⟩ := readOf _ invC
    have hsSt : (setI h zs { s with lens := lensA, «have» := haveA }).istates zs =
        some { s with lens := lensA, «have» := haveA } := setI_istates_same _ _ _
    have invSt : CodeLengthInvariant zs { s with lens := lensA, «have» := haveA } :=
      fun _ => ⟨pointer, table, nlenB, ndistB, by show haveA.toNat ≤ _; omega, valsA⟩
    have wfSt : ({ s with lens := lensA, «have» := haveA } : InflateState).WellFormed := ⟨szA, wfS.2.1, wfS.2.2⟩
    have runC : runX (inflate_CODELENS c) l h =
        runX (clTail c) regs (setI h zs { s with lens := lensA, «have» := haveA }) := by
      rw [inflate_CODELENS_eq, runX_bind, runL]
    have lenFinal : (actualLengthPrefix { s with lens := lensA, «have» := haveA }).length =
        s.nlen.toNat + s.ndist.toNat := by
      rw [lenSt]; exact doneA
    have traceAll : (¬ ∀ k, cl.getD k 0 = 0) →
        ZlibF.Math.CodeLengthPrefix.Trace cl (s.nlen.toNat + s.ndist.toNat) [] (r4 ++ consumed)
          (actualLengthPrefix { s with lens := lensA, «have» := haveA }) :=
      fun ne => trace.trans (ltrace ne).1
    have readCL' := ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ consumed readCL
    obtain ⟨a1, a2, a3⟩ := counts_append (more := consumed) read1 read2 read3
    have binvR : BitInv h regs (f.inp.drop (loopRead regs)) := by
      rw [readEq, ← List.drop_drop]; exact MeaningLength.bitInv_unsetI invC
    have bitsR : bytesToBits (f.logIn ++ f.inp.take (loopRead regs)) =
        (consumedP ++ consumed) ++ natBits regs.bits.toNat regs.hold.toNat := by
      rw [readEq, rb, heldOf _ invC source, List.append_assoc]
    by_cases valid : HasEndOfBlock ((actualLengthPrefix { s with lens := lensA, «have» := haveA }).take s.nlen.toNat) ∧
        Acceptable .litLen ((actualLengthPrefix { s with lens := lensA, «have» := haveA }).take s.nlen.toNat) ∧
        Acceptable .dist ((actualLengthPrefix { s with lens := lensA, «have» := haveA }).drop s.nlen.toNat)
    · -- both tables built
      have ne : ¬ ∀ k, cl.getD k 0 = 0 := by
        intro empty
        apply valid.1
        have slices := Zlib.Inflate.Proofs.PayloadTables.actualLengthPrefix_payload_slices
          { s with lens := lensA, «have» := haveA } doneA
        rw [slices.1, Zlib.Inftrees.Proofs.lensOf_getD _ (show 256 < s.nlen.toNat by omega)]
        change (lensA.getD 256 0).toNat = 0
        rw [zerosA empty 256 (by omega)]
        rfl
      obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD, offsetD, lcEq, dcEq, ⟨uL, invL⟩, stL,
        ⟨uD, invD⟩, stD, tailRun⟩ :=
        clTail_valid_tables (l := regs) st hsSt wfSt mode invSt doneA valid.1 valid.2.1 valid.2.2
      let state' : InflateState := { clDistResult (clLensResult zs { s with lens := lensA, «have» := haveA }
        nextL bitsL workL codesL) nextD bitsD workD codesD with mode := LEN_ }
      have dh := dynamic_header_of_trace a1 a2 a3 counts readCL' acc (by rw [← Ttot]; exact traceAll ne)
        (by rw [lenFinal, Ttot]) (by rw [← nlenEq]; exact valid.1) (by rw [← nlenEq]; exact valid.2.1)
        (by rw [← nlenEq]; exact valid.2.2)
      have parsedDone := DeflateParsed.dynamicDone (DeflateParsed.dynamicBits consumed deflate) dh
      rw [nlenEq] at invL invD
      have moved := loop_move (s' := state') (l' := { regs with ret := 0 }) (j := used)
        (pos := ⟨out, final, .codes
          ((actualLengthPrefix { s with lens := lensA, «have» := haveA }).take (hlit + 257))
          ((actualLengthPrefix { s with lens := lensA, «have» := haveA }).drop (hlit + 257)) .none⟩) st retOk
        ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LEN_ ≠ SYNC by decide⟩
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
        ⟨keep.1, keep.2.1, keep.2.2.1, keep.2.2.2.1, by show (0 : Int32) = l.ret; rw [retOk]; rfl⟩
        usedEq nxt ⟨binvR.have_eq, binvR.next, binvR.hold_lt⟩ bitsR
        (HeldBits.of_natBits (s := loopState state' { regs with ret := 0 }) binvR.hold_lt)
        wrapHeader (by rw [consumedEq, List.append_assoc]) parsedDone
        ⟨last, ⟨.istate_codes zs, 0, state'.codes, uL, lcEq, CodeRef.get_istate_codes (setI_istates_same h zs state'),
            invL, stL⟩,
          ⟨.istate_codes zs, offsetD, state'.codes, uD, dcEq, CodeRef.get_istate_codes (setI_istates_same h zs state'),
            invD, stD⟩, Or.inl rfl, Or.inl small⟩
        (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
      by_cases trees : c.flush = Z_TREES
      · left
        refine ⟨.error Ex.leave, { regs with ret := 0 }, setI h zs state', ?_, Or.inl ⟨rfl, Or.inr ⟨trees, fun zs' s' st' hs' => by rw [setI_state state' st zs' s' st' hs'], small⟩, moved⟩⟩
        rw [runC, tailRun, ite_eq_left trees, setI_setI]
      · right
        refine ⟨trees, { regs with ret := 0 }, setI h zs state', ?_, by show loopRead l ≤ loopRead regs; omega,
          fun zs' s' st' hs' => by rw [setI_state state' st zs' s' st' hs'], moved⟩
        rw [runC, tailRun, ite_eq_right trees, setI_setI]
    · -- a header that the format rejects
      left
      obtain ⟨l'', h'', tailRun, in'', have'', badAll⟩ :=
        clTail_invalid (l := regs) strm st (hz' _) hsSt wfSt mode invSt doneA (by show 257 ≤ s.nlen.toNat; omega)
          valid
      have readL : loopRead l'' = loopRead regs := by simp only [loopRead, in'', have'']
      refine ⟨.ok (), l'', h'', runC.trans tailRun, Or.inr ⟨rfl, by rw [readL]; omega, badAll, ?_⟩⟩
      apply refuted_of_aligned (rest := consumed ++ natBits regs.bits.toNat regs.hold.toNat) wrapHeader deflate
      · rw [readL, bitsR, consumedEq]
        simp only [List.append_assoc]
      · intro more tail outF _ resid
        obtain ⟨_, _, body, _⟩ := resid
        cases body with
        | dynamic q1 q2 q3 _ q5 _ q7 q8 q9 q10 =>
          obtain ⟨b1, b2, b3⟩ := counts_append
            (more := (consumed ++ natBits regs.bits.toNat regs.hold.toNat) ++ more) read1 read2 read3
          rw [b1] at q1
          simp only [Option.some.injEq, Prod.mk.injEq] at q1
          obtain ⟨rfl, rfl⟩ := q1
          rw [b2] at q2
          simp only [Option.some.injEq, Prod.mk.injEq] at q2
          obtain ⟨rfl, rfl⟩ := q2
          rw [b3] at q3
          simp only [Option.some.injEq, Prod.mk.injEq] at q3
          obtain ⟨rfl, rfl⟩ := q3
          rw [ZlibF.Spec.Proofs.readCodeLenLens_append _ _ _ _ _ readCL] at q5
          simp only [Option.some.injEq, Prod.mk.injEq] at q5
          obtain ⟨rfl, rfl⟩ := q5
          rw [← Ttot] at q7
          by_cases empty : ∀ k, cl.getD k 0 = 0
          · exact codeLens_none q7 (by simp only [List.length_nil]; omega) (dec_none_zero empty _)
          · have complete := (traceAll empty).complete (future := natBits regs.bits.toNat regs.hold.toNat ++ more)
              lenFinal
            simp only [List.append_assoc] at complete q7
            obtain ⟨_, rfl⟩ := CodeLens.det q7 complete
            rw [← nlenEq] at q8 q9 q10
            exact valid ⟨q8, q9, q10⟩

#print axioms codelens_step

end CodeLens

end Zlib.Inflate.Proofs.MeaningDynamicSteps
