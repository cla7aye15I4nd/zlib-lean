import ZlibF.Proof.«inffast.c.body-token-reject»
import ZlibF.Proof.«inffast.c.fast64-loop»

/-!
# inffast.c: token refinement for the 64-bit fast loop (`Fast64Trace`)

Bridges `Dolen8Event`, `Body8Trace`, and `Fast64Trace` to the independent
DEFLATE token semantics (`ZlibF.Spec.Token.Step` / `Token.Rejected`):
- `writtenBytes_eq_of_prefix`: output-slice extensionality up to the write cursor.
- `dolen8_event_refines_token`: each single `Dolen8Event` refines `Token.Step`
  (literal, match copy, or end-of-block) or `Token.Rejected` (invalid length,
  invalid distance, or distance too far) on the bit stream `Origin.initial e`.
- `body8_trace_refines_tokens` / `fast64_trace_refines_tokens`: lifts any
  nonterminal-token-closed invariant `Q` across `Body8Trace` and `Fast64Trace`
  into the exact `LoopEnd` token disjunction.
-/

set_option autoImplicit false

namespace Zlib.Inffast.Proofs.Fast64Tokens
open C Zlib.Inffast Zlib.Inffast.Spec Zlib.Inffast.Proofs ZlibF.Spec ZlibF.Spec.Proofs
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs ZlibF.Math.LZ77Copy
open Zlib.Inffast.Spec.BodyToken Zlib.Inffast.Proofs.BodyTokenProof
open Zlib.Inffast.Proofs.BodyTokenReject
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inffast.Spec.Origin

theorem writtenBytes_eq_of_prefix (A B : Array UInt8) (offset count : Nat)
    (hc : count ≤ offset) (hpre : ∀ j, j < offset → A[j]? = B[j]?) :
    writtenBytes A offset count = writtenBytes B offset count := by
  apply List.ext_getElem?
  intro i
  rw [written_get, written_get]
  by_cases hi : i < count
  · simp only [hi, ite_true]
    exact hpre (offset - count + i) (by omega)
  · simp only [hi, ite_false]

private theorem readBits_nil_length : ∀ (n v : Nat) (w : List Bool),
    readBits n w = some (v, []) → w.length = n
  | 0, _, [], _ => rfl
  | 0, _, _ :: _, h => by simp [readBits] at h
  | _ + 1, _, [], h => by simp [readBits] at h
  | n + 1, _, _ :: w, h => by
    cases hr : readBits n w with
    | none => simp [readBits, hr] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [readBits, hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hr'⟩ := h
      subst hr'
      have ih := readBits_nil_length n v' w hr
      simp [ih]

private theorem drop_drop_add (l : List Bool) (a b : Nat) :
    (l.drop a).drop b = l.drop (a + b) := by
  rw [List.drop_drop, Nat.add_comm]

private theorem dist_base_fields (sym : Nat) (entry : Code)
    (hlo : sym ≤ 29) (hmeaning : DecodeSemantics.SymbolEntry DISTS sym entry) :
    (entry.op &&& 15).toNat = distExtras.getD sym 0 ∧
    entry.val.toNat = distBases.getD sym 0 := by
  have hFields : entry.op.toNat = 16 + distExtras.getD sym 0 ∧
      entry.val.toNat = distBases.getD sym 0 := by
    have hne : DISTS ≠ LENS := by decide
    simpa [DecodeSemantics.SymbolEntry, hne, hlo] using hmeaning
  have hDistEx : ∀ k : Fin 30, distExtras.getD k.val 0 ≤ 13 := by decide +kernel
  have hd : distExtras.getD sym 0 ≤ 13 := hDistEx ⟨sym, by omega⟩
  have hMask : ∀ k : Fin 14, ((UInt8.ofNat (16 + k.val)) &&& 15).toNat = k.val := by
    decide +kernel
  have hOp : entry.op = UInt8.ofNat (16 + distExtras.getD sym 0) := by
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change entry.op.toNat = (UInt8.ofNat (16 + distExtras.getD sym 0)).toNat
    rw [hFields.1, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : 16 + distExtras.getD sym 0 < 256)]
  refine ⟨?_, hFields.2⟩
  simpa [hOp] using hMask ⟨distExtras.getD sym 0, by omega⟩

theorem dolen8_event_refines_token (e : Env) (LL DD : List Nat)
    (tables : BodyToken.Tables e LL DD)
    (lenPrefix : PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat)
    {m : UInt32} {A A' : Array UInt8} {o u o' u' : Nat} {broke : Bool} {m' : UInt32}
    (ev : Dolen8Event e m A o u A' o' u' broke m')
    (hbg : e.bg ≤ o) (ho' : o' ≤ A.size) :
    let hist := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff
    let src := Origin.initial e
    u ≤ u' ∧
    ((broke = false ∧ m' = m ∧
        Token.Step LL DD hist (writtenBytes A o (o - e.bg))
          (src.drop u) (src.drop u') (writtenBytes A' o' (o' - e.bg)) false) ∨
     (broke = true ∧ m' = TYPE ∧ A' = A ∧ o' = o ∧
        Token.Step LL DD hist (writtenBytes A o (o - e.bg))
          (src.drop u) (src.drop u') (writtenBytes A' o' (o' - e.bg)) true) ∨
     (broke = true ∧ m' = BAD ∧ A' = A ∧ o' = o ∧
        ∀ more, Token.Rejected LL DD hist (writtenBytes A o (o - e.bg))
          ((src.drop u).take (u' - u) ++ more))) := by
  dsimp only
  obtain ⟨usedL, invL⟩ := tables.lengthTable
  obtain ⟨usedD, invD⟩ := tables.distanceTable
  have extL : Ext LL := ext_acceptable invL.acceptable
  have extD : Ext DD := ext_acceptable invD.acceptable
  cases ev with
  | lit hold bits i entry cb h15 hhold hsg hcb hlook hop =>
    refine ⟨by omega, Or.inl ⟨rfl, rfl, ?_⟩⟩
    obtain ⟨_, _, _, _, sem⟩ := length_lookup_matches_format e hold bits i usedL LL entry cb
      invL tables.lengthStable tables.lengthFlags hhold h15 hlook
    rcases sem with ⟨hnot, _⟩ | ⟨_, sym, hsym285, hmeaning, _, hdec, _⟩
    · exact False.elim (hnot (Or.inl hop))
    · have hlit := literal_symbol sym entry hsym285 hmeaning hop
      rw [hsg] at hdec
      have hu8 : entry.val.toUInt8 = sym.toUInt8 := by
        apply UInt8.eq_of_toBitVec_eq
        apply BitVec.eq_of_toNat_eq
        change entry.val.toUInt8.toNat = sym.toUInt8.toNat
        rw [UInt16.toNat_toUInt8, Nat.toUInt8, UInt8.toNat_ofNat', hlit.2]
      rw [show o + 1 - e.bg = (o - e.bg) + 1 by omega, hu8,
        written_set_append A o (o - e.bg) sym.toUInt8 (Nat.sub_le _ _) (by omega)]
      rw [drop_drop_add] at hdec
      exact Token.Step.literal hdec hlit.1
  | copy holdL bitsL iL entryL cL xL extraL holdD bitsD iD entryD cD xD extraD dist _
      hbL hholdLLt hsgL hcL hlkL hEnz hE16 hxL hxL5 hval3 hval259 hreadL
      hbD hholdDLt hsgD hcD hlkD hD16 hxD hxD13 hDval1 hreadD hdistEq hnotToo hAsz' hpre =>
    refine ⟨by omega, Or.inl ⟨rfl, rfl, ?_⟩⟩
    obtain ⟨_, _, _, _, semL⟩ := length_lookup_matches_format e holdL bitsL iL usedL LL entryL cL
      invL tables.lengthStable tables.lengthFlags hholdLLt hbL hlkL
    rcases semL with ⟨hnotL, _⟩ | ⟨_, symL, hsymL285, hmeaningL, _, hdecL, _⟩
    · exact False.elim (hnotL (Or.inr (Or.inl hE16)))
    · have hsymL257 := base_symbol symL entryL hsymL285 hmeaningL hE16
      obtain ⟨_, hxLEq, hvalLEq⟩ := length_base_fields symL entryL hsymL257 hsymL285 hmeaningL
      rw [hsgL, drop_drop_add] at hdecL
      obtain ⟨_, _, _, _, semD⟩ := distance_lookup_matches_format e holdD bitsD iD usedD DD entryD cD
        invD tables.distanceStable tables.distanceFlags hholdDLt hbD hlkD
      rcases semD with ⟨hbadD, _⟩ | ⟨_, symD, hsymD29, hmeaningD, _, hdecD, _⟩
      · exact False.elim (hD16 hbadD)
      · obtain ⟨hxDEq, hvalDEq⟩ := dist_base_fields symD entryD hsymD29 hmeaningD
        rw [hsgD, drop_drop_add] at hdecD
        have hlenHist : (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
            e.s0.whave.toNat e.woff).length = e.s0.whave.toNat := by
          simp [MatchHistory.saved]
        have hlenCur : (writtenBytes A o (o - e.bg)).length = o - e.bg :=
          written_length A o (o - e.bg) (Nat.sub_le _ _) (by omega)
        have hdistBound : distBases.getD symD 0 + extraD ≤
            (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
              e.s0.whave.toNat e.woff ++ writtenBytes A o (o - e.bg)).length := by
          rw [List.length_append, hlenHist, hlenCur]
          omega
        have hEqMatch : writtenBytes A' (o + (entryL.val.toNat + extraL))
            (o + (entryL.val.toNat + extraL) - e.bg) =
            writtenBytes (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist
              (entryL.val.toNat + extraL) A)
              (o + (entryL.val.toNat + extraL))
              (o - e.bg + (entryL.val.toNat + extraL)) := by
          rw [show o + (entryL.val.toNat + extraL) - e.bg =
            (o - e.bg) + (entryL.val.toNat + extraL) by omega]
          exact writtenBytes_eq_of_prefix A' _ (o + (entryL.val.toNat + extraL))
            ((o - e.bg) + (entryL.val.toNat + extraL)) (by omega) hpre
        have hRef : writtenBytes (matchArr e.s0.wsize.toNat e.s0.wnext.toNat e.woff e.W e.bg o dist
            (entryL.val.toNat + extraL) A)
            (o + (entryL.val.toNat + extraL))
            (o - e.bg + (entryL.val.toNat + extraL)) =
            copyBack (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
              e.s0.whave.toNat e.woff) dist (entryL.val.toNat + extraL)
              (writtenBytes A o (o - e.bg)) := by
          apply fast_match_array_refines_lz77 e.W A e.s0.wsize.toNat e.s0.wnext.toNat
            e.s0.whave.toNat e.woff e.bg o dist (entryL.val.toNat + extraL) e.hwh e.hwn
          · intro hwh
            have hne : e.s0.whave ≠ 0 := fun hz => hwh (by simp [hz])
            exact (e.hwin hne).2.2.2
          · exact hbg
          · exact ho'
          · omega
          · omega
        rw [hEqMatch, hRef, hdistEq, hvalDEq, hvalLEq]
        have hreadL' : readBits (lengthExtras.getD (symL - 257) 0)
            ((Origin.initial e).drop (u + cL)) =
            some (extraL, (Origin.initial e).drop (u + cL + xL)) := by
          simpa [hxL, hxLEq] using hreadL
        have hreadD' : readBits (distExtras.getD symD 0)
            ((Origin.initial e).drop (u + cL + xL + cD)) =
            some (extraD, (Origin.initial e).drop (u + cL + xL + cD + xD)) := by
          simpa [hxD, hxDEq] using hreadD
        exact Token.Step.copy hdecL hsymL257 hsymL285 hreadL' hdecD hsymD29 hreadD' hdistBound
  | eob hold bits i entry cb h15 hhold hsg hcb hlook hnz hn16 _ h32 =>
    refine ⟨by omega, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, ?_⟩)⟩
    obtain ⟨_, _, _, _, sem⟩ := length_lookup_matches_format e hold bits i usedL LL entry cb
      invL tables.lengthStable tables.lengthFlags hhold h15 hlook
    rcases sem with ⟨hnot, _⟩ | ⟨_, sym, hsym285, hmeaning, _, hdec, _⟩
    · exact False.elim (hnot (Or.inr (Or.inr ⟨‹_›, h32⟩)))
    · have heob := eob_symbol sym entry hsym285 hmeaning hnz hn16
      subst heob
      rw [hsg, drop_drop_add] at hdec
      exact Token.Step.eob hdec
  | badLen hold bits i entry cb h15 hhold hsg hcb hlook hnz hn16 _ h32 =>
    refine ⟨by omega, Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, ?_⟩)⟩
    obtain ⟨hquery, _, _, _, sem⟩ := length_lookup_matches_format e hold bits i usedL LL entry cb
      invL tables.lengthStable tables.lengthFlags hhold h15 hlook
    rcases sem with ⟨_, hfuture⟩ | ⟨hfa, _⟩
    · have hlong : 15 ≤ ((Origin.initial e).drop u).length := by
        rw [← hsg]
        exact Nat.le_trans h15 (Sg_long e hold bits i)
      rw [hsg] at hquery hfuture
      have hrej := table_rejected (fun _ => lensValid) invL tables.lengthStable lenPrefix
        hlong hquery hcb hfuture
      intro more
      rw [show (u + cb) - u = cb by omega]
      exact Token.Rejected.length (fun more2 => by
        rw [List.append_assoc]
        exact hrej (more ++ more2))
    · exfalso
      rcases hfa with h0 | h16 | ⟨_, h32'⟩
      · exact hnz h0
      · exact h16 hn16
      · exact h32' h32
  | badDist holdL bitsL iL entryL cL xL extraL holdD bitsD iD entryD cD
      hbL hholdLLt hsgL hcL hlkL _ hE16 hxL _ _ _ hreadL
      hbD hholdDLt hsgD hcD hlkD hD16 =>
    refine ⟨by omega, Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, ?_⟩)⟩
    obtain ⟨_, _, _, _, semL⟩ := length_lookup_matches_format e holdL bitsL iL usedL LL entryL cL
      invL tables.lengthStable tables.lengthFlags hholdLLt hbL hlkL
    rcases semL with ⟨hnotL, _⟩ | ⟨_, symL, hsymL285, hmeaningL, _, hdecL, _⟩
    · exact False.elim (hnotL (Or.inr (Or.inl hE16)))
    · have hsymL257 := base_symbol symL entryL hsymL285 hmeaningL hE16
      obtain ⟨_, hxLEq, _⟩ := length_base_fields symL entryL hsymL257 hsymL285 hmeaningL
      rw [hsgL, drop_drop_add] at hdecL
      obtain ⟨hqueryD, _, _, _, semD⟩ := distance_lookup_matches_format e holdD bitsD iD
        usedD DD entryD cD invD tables.distanceStable tables.distanceFlags hholdDLt hbD hlkD
      rcases semD with ⟨_, hfutureD⟩ | ⟨hfaD, _⟩
      · have hlongL : 15 ≤ ((Origin.initial e).drop u).length := by
          rw [← hsgL]
          exact Nat.le_trans hbL (Sg_long e holdL bitsL iL)
        have hlongD : 15 ≤ ((Origin.initial e).drop (u + cL + xL)).length := by
          rw [← hsgD]
          exact Nat.le_trans hbD (Sg_long e holdD bitsD iD)
        rw [hsgD] at hqueryD hfutureD
        have hrejD := table_rejected (fun _ => distsValid) invD tables.distanceStable distPrefix
          hlongD hqueryD hcD hfutureD
        obtain ⟨wL, hwLSplit, hwLDec⟩ := decodeSym_word hdecL
        obtain ⟨wX, hwXSplit, hwXRead⟩ := readBits_word hreadL
        rw [List.length_drop] at hlongL
        have hwLLen : wL.length = cL := by
          have := congrArg List.length hwLSplit
          rw [List.length_append, List.length_drop, List.length_drop] at this
          omega
        have hwXLen : wX.length = xL := readBits_nil_length xL extraL wX hwXRead
        have hsplit : (Origin.initial e).drop u =
            (wL ++ wX) ++ (Origin.initial e).drop (u + cL + xL) := by
          rw [List.append_assoc, ← hwXSplit, ← hwLSplit]
        have htake : ((Origin.initial e).drop u).take (u + cL + xL + cD - u) =
            (wL ++ wX) ++ ((Origin.initial e).drop (u + cL + xL)).take cD := by
          have hlenWX : (wL ++ wX).length = cL + xL := by simp [hwLLen, hwXLen]
          rw [show u + cL + xL + cD - u = (wL ++ wX).length + cD by omega, hsplit]
          exact take_front (wL ++ wX) ((Origin.initial e).drop (u + cL + xL)) cD
        intro more
        rw [htake, List.append_assoc, List.append_assoc]
        have hDec1 : decodeSym LL (wL ++ (wX ++
            (((Origin.initial e).drop (u + cL + xL)).take cD ++ more))) =
            some (symL, wX ++ (((Origin.initial e).drop (u + cL + xL)).take cD ++ more)) := by
          simpa using extL wL symL []
            (wX ++ (((Origin.initial e).drop (u + cL + xL)).take cD ++ more)) hwLDec
        have hRead1 : readBits (lengthExtras.getD (symL - 257) 0)
            (wX ++ (((Origin.initial e).drop (u + cL + xL)).take cD ++ more)) =
            some (extraL, ((Origin.initial e).drop (u + cL + xL)).take cD ++ more) := by
          rw [← hxLEq, ← hxL]
          simpa using readBits_append xL wX extraL []
            (((Origin.initial e).drop (u + cL + xL)).take cD ++ more) hwXRead
        refine Token.Rejected.distance hDec1 hsymL257 hsymL285 hRead1 (fun more2 => ?_)
        rw [List.append_assoc]
        exact hrejD (more ++ more2)
      · exact False.elim (hfaD hD16)
  | badTooFar holdL bitsL iL entryL cL xL extraL holdD bitsD iD entryD cD xD extraD dist
      hbL hholdLLt hsgL hcL hlkL _ hE16 hxL _ _ _ hreadL
      hbD hholdDLt hsgD hcD hlkD hD16 hxD _ _ hreadD hdistEq htoo =>
    refine ⟨by omega, Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, ?_⟩)⟩
    obtain ⟨_, _, _, _, semL⟩ := length_lookup_matches_format e holdL bitsL iL usedL LL entryL cL
      invL tables.lengthStable tables.lengthFlags hholdLLt hbL hlkL
    rcases semL with ⟨hnotL, _⟩ | ⟨_, symL, hsymL285, hmeaningL, _, hdecL, _⟩
    · exact False.elim (hnotL (Or.inr (Or.inl hE16)))
    · have hsymL257 := base_symbol symL entryL hsymL285 hmeaningL hE16
      obtain ⟨_, hxLEq, _⟩ := length_base_fields symL entryL hsymL257 hsymL285 hmeaningL
      rw [hsgL, drop_drop_add] at hdecL
      obtain ⟨_, _, _, _, semD⟩ := distance_lookup_matches_format e holdD bitsD iD
        usedD DD entryD cD invD tables.distanceStable tables.distanceFlags hholdDLt hbD hlkD
      rcases semD with ⟨hbadD, _⟩ | ⟨_, symD, hsymD29, hmeaningD, _, hdecD, _⟩
      · exact False.elim (hD16 hbadD)
      · obtain ⟨hxDEq, hvalDEq⟩ := dist_base_fields symD entryD hsymD29 hmeaningD
        rw [hsgD, drop_drop_add] at hdecD
        have hlongL : 15 ≤ ((Origin.initial e).drop u).length := by
          rw [← hsgL]; exact Nat.le_trans hbL (Sg_long e holdL bitsL iL)
        have hlongD : 15 ≤ ((Origin.initial e).drop (u + cL + xL)).length := by
          rw [← hsgD]; exact Nat.le_trans hbD (Sg_long e holdD bitsD iD)
        obtain ⟨wL, hwLSplit, hwLDec⟩ := decodeSym_word hdecL
        obtain ⟨wXL, hwXLSplit, hwXLRead⟩ := readBits_word hreadL
        obtain ⟨wD, hwDSplit, hwDDec⟩ := decodeSym_word hdecD
        obtain ⟨wXD, hwXDSplit, hwXDRead⟩ := readBits_word hreadD
        rw [List.length_drop] at hlongL hlongD
        have hwLLen : wL.length = cL := by
          have := congrArg List.length hwLSplit
          rw [List.length_append, List.length_drop, List.length_drop] at this
          omega
        have hwXLLen : wXL.length = xL := readBits_nil_length xL extraL wXL hwXLRead
        have hwDLen : wD.length = cD := by
          have := congrArg List.length hwDSplit
          rw [List.length_append, List.length_drop, List.length_drop] at this
          omega
        have hwXDLen : wXD.length = xD := readBits_nil_length xD extraD wXD hwXDRead
        have hsplit : (Origin.initial e).drop u =
            (wL ++ wXL ++ wD ++ wXD) ++ (Origin.initial e).drop (u + cL + xL + cD + xD) := by
          simp only [List.append_assoc]
          rw [← hwXDSplit, ← hwDSplit, ← hwXLSplit, ← hwLSplit]
        have hwLen : (wL ++ wXL ++ wD ++ wXD).length = u + cL + xL + cD + xD - u := by
          simp only [List.length_append, hwLLen, hwXLLen, hwDLen, hwXDLen]; omega
        have htake : ((Origin.initial e).drop u).take (u + cL + xL + cD + xD - u) =
            wL ++ wXL ++ wD ++ wXD := by
          rw [← hwLen, hsplit, List.take_left]
        have hlenHist : (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
            e.s0.whave.toNat e.woff).length = e.s0.whave.toNat := by
          simp [MatchHistory.saved]
        have hlenCur : (writtenBytes A o (o - e.bg)).length = o - e.bg :=
          written_length A o (o - e.bg) (Nat.sub_le _ _) (by omega)
        have hfar : (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat
            e.s0.whave.toNat e.woff ++ writtenBytes A o (o - e.bg)).length <
            distBases.getD symD 0 + extraD := by
          rw [List.length_append, hlenHist, hlenCur]
          omega
        intro more
        rw [htake, List.append_assoc, List.append_assoc, List.append_assoc]
        have hDec1 := extL wL symL [] (wXL ++ (wD ++ (wXD ++ more))) hwLDec
        simp only [List.nil_append] at hDec1
        have hRead1 : readBits (lengthExtras.getD (symL - 257) 0)
            (wXL ++ (wD ++ (wXD ++ more))) =
            some (extraL, wD ++ (wXD ++ more)) := by
          rw [← hxLEq, ← hxL]
          simpa using readBits_append xL wXL extraL [] (wD ++ (wXD ++ more)) hwXLRead
        have hDec2 := extD wD symD [] (wXD ++ more) hwDDec
        simp only [List.nil_append] at hDec2
        have hRead2 : readBits (distExtras.getD symD 0) (wXD ++ more) = some (extraD, more) := by
          rw [← hxDEq, ← hxD]
          simpa using readBits_append xD wXD extraD [] more hwXDRead
        exact Token.Rejected.tooFar hDec1 hsymL257 hsymL285 hRead1 hDec2 hsymD29 hRead2 hfar

theorem body8_trace_refines_tokens (e : Env) (LL DD : List Nat)
    (tables : BodyToken.Tables e LL DD)
    (lenPrefix : PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat)
    (Q : Nat → List UInt8 → Prop)
    (step : ∀ u u' current next, u ≤ u' → Q u current →
      Token.Step LL DD
        (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff)
        current ((Origin.initial e).drop u) ((Origin.initial e).drop u') next false →
      Q u' next)
    {m : UInt32} {A A' : Array UInt8} {o u o' u' : Nat} {broke : Bool} {m' : UInt32}
    (tr : Body8Trace e m A o u A' o' u' broke m')
    (hbg : e.bg ≤ o) (ho' : o' ≤ A'.size) (hq : Q u (writtenBytes A o (o - e.bg))) :
    let hist := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff
    let src := Origin.initial e
    u ≤ u' ∧
    ((broke = false ∧ m' = m ∧ Q u' (writtenBytes A' o' (o' - e.bg))) ∨
     (broke = true ∧ m' = TYPE ∧ ∃ u0, u0 ≤ u' ∧ Q u0 (writtenBytes A' o' (o' - e.bg)) ∧
        Token.Step LL DD hist (writtenBytes A' o' (o' - e.bg))
          (src.drop u0) (src.drop u') (writtenBytes A' o' (o' - e.bg)) true) ∨
     (broke = true ∧ m' = BAD ∧ ∃ u0, u0 ≤ u' ∧ Q u0 (writtenBytes A' o' (o' - e.bg)) ∧
        ∀ more, Token.Rejected LL DD hist (writtenBytes A' o' (o' - e.bg))
          ((src.drop u0).take (u' - u0) ++ more))) := by
  induction tr with
  | base ev =>
    have hbd := (Body8Trace.base ev).output_bounds
    obtain ⟨hu, hres⟩ := dolen8_event_refines_token e LL DD tables lenPrefix distPrefix ev hbg
      (by omega)
    refine ⟨hu, ?_⟩
    rcases hres with ⟨hb, hm, htok⟩ | ⟨hb, hm, hA, ho, htok⟩ | ⟨hb, hm, hA, ho, hrej⟩
    · exact Or.inl ⟨hb, hm, step _ _ _ _ hu hq htok⟩
    · rcases hA with rfl; rcases ho with rfl
      exact Or.inr (Or.inl ⟨hb, hm, _, hu, hq, htok⟩)
    · rcases hA with rfl; rcases ho with rfl
      exact Or.inr (Or.inr ⟨hb, hm, _, hu, hq, hrej⟩)
  | @step A0 o0 u0 A1 o1 u1 A2 o2 u2 br2 m2 ev rest ih =>
    have hbd1 := (Body8Trace.base ev).output_bounds
    have hbd2 := rest.output_bounds
    obtain ⟨hu1, hres1⟩ := dolen8_event_refines_token e LL DD tables lenPrefix distPrefix ev hbg
      (by omega)
    have hq1 : Q u1 (writtenBytes A1 o1 (o1 - e.bg)) := by
      rcases hres1 with ⟨_, _, htok⟩ | ⟨hb, _, _⟩ | ⟨hb, _, _⟩
      · exact step _ _ _ _ hu1 hq htok
      · cases hb
      · cases hb
    obtain ⟨hu2, hres2⟩ := ih (by omega) ho' hq1
    exact ⟨Nat.le_trans hu1 hu2, hres2⟩

theorem fast64_trace_refines_tokens (e : Env) (LL DD : List Nat)
    (tables : BodyToken.Tables e LL DD)
    (lenPrefix : PrefixQuery LENS e.LCA e.ol e.s0.lenbits.toNat)
    (distPrefix : PrefixQuery DISTS e.DCA e.od e.s0.distbits.toNat)
    (Q : Nat → List UInt8 → Prop)
    (step : ∀ u u' current next, u ≤ u' → Q u current →
      Token.Step LL DD
        (MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff)
        current ((Origin.initial e).drop u) ((Origin.initial e).drop u') next false →
      Q u' next)
    {m : UInt32} {A A' : Array UInt8} {o u o' u' : Nat} {broke : Bool} {m' : UInt32}
    (tr : Fast64Trace e m A o u A' o' u' broke m')
    (hbg : e.bg ≤ o) (ho' : o' ≤ A'.size) (hq : Q u (writtenBytes A o (o - e.bg))) :
    let hist := MatchHistory.saved e.W e.s0.wsize.toNat e.s0.wnext.toNat e.s0.whave.toNat e.woff
    let src := Origin.initial e
    u ≤ u' ∧
    ((broke = false ∧ m' = m ∧ Q u' (writtenBytes A' o' (o' - e.bg))) ∨
     (broke = true ∧ m' = TYPE ∧ ∃ u0, u0 ≤ u' ∧ Q u0 (writtenBytes A' o' (o' - e.bg)) ∧
        Token.Step LL DD hist (writtenBytes A' o' (o' - e.bg))
          (src.drop u0) (src.drop u') (writtenBytes A' o' (o' - e.bg)) true) ∨
     (broke = true ∧ m' = BAD ∧ ∃ u0, u0 ≤ u' ∧ Q u0 (writtenBytes A' o' (o' - e.bg)) ∧
        ∀ more, Token.Rejected LL DD hist (writtenBytes A' o' (o' - e.bg))
          ((src.drop u0).take (u' - u0) ++ more))) := by
  induction tr with
  | single b =>
    exact body8_trace_refines_tokens e LL DD tables lenPrefix distPrefix Q step b hbg ho' hq
  | @cons A0 o0 u0 A1 o1 u1 A2 o2 u2 br2 m2 b rest ih =>
    have hbd1 := b.output_bounds
    have hbd2 := rest.output_bounds
    obtain ⟨hu1, hres1⟩ := body8_trace_refines_tokens e LL DD tables lenPrefix distPrefix Q step b
      hbg (by omega) hq
    have hq1 : Q u1 (writtenBytes A1 o1 (o1 - e.bg)) := by
      rcases hres1 with ⟨_, _, h⟩ | ⟨hb, _⟩ | ⟨hb, _⟩
      · exact h
      · cases hb
      · cases hb
    obtain ⟨hu2, hres2⟩ := ih (by omega) ho' hq1
    exact ⟨Nat.le_trans hu1 hu2, hres2⟩

end Zlib.Inffast.Proofs.Fast64Tokens
