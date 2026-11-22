import ZlibF.Proof.«inflate.c.meaning-trip-trailer»
import ZlibF.Proof.«inflate.c.meaning-block»
import ZlibF.Proof.«inflate.c.block-type»

/-!
# inflate.c: the trip row `TYPE`/`TYPEDO` after the last block, with a wrapper

```
case TYPE:
    if (flush == Z_BLOCK || flush == Z_TREES) goto inf_leave;
case TYPEDO:
    if (state->last) { BYTEBITS(); state->mode = CHECK; break; }
```

A `TYPE` or `TYPEDO` state with `last` set stands for the finished body
(`BodyMatches .finished`): fewer than 8 bits are held, and the consumed bits
and the held bits together end on a byte boundary. `TYPE` with `Z_BLOCK` or
`Z_TREES` leaves with nothing changed. Otherwise `BYTEBITS()` drops the held
bits, which are exactly the padding of the last byte of the body, and the
stage moves to the trailer with no trailer byte read.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningBits
set_option autoImplicit false

namespace MeaningTypeFinal

/-- The only stage a `TYPE` or `TYPEDO` state after the final block can stand for. -/
theorem stage_of_final {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0) :
    ∃ header out, stage = .body header ⟨out, true, .finished⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rcases mode with m | m <;> rw [m] at lo hi <;> exact absurd hi (by decide)
  · have this := stageFacts
    simp only [LoopStageMatches] at this
    rcases mode with m | m <;> rw [m] at this <;> exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨_, _, zero, _⟩ := body
      exact absurd zero last
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m' | m' | m' <;> rcases mode with m | m <;>
        (rw [m] at m'; exact absurd m' (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
    · obtain ⟨_, fin, _, _⟩ := body
      subst fin
      exact ⟨header, out, rfl⟩
  · obtain ⟨m', _⟩ := stageFacts
    rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)

/-- The trailer of a wrapped stream is not empty. -/
theorem wrapTrailer_ne_nil {wrap : Api.Wrap} (wrapped : wrap ≠ .raw) (header out : List UInt8) :
    ([] : List UInt8) ≠ WrapTrailer wrap header out := by
  cases wrap with
  | raw => exact absurd rfl wrapped
  | zlib => simp [WrapTrailer, be32]
  | gzip => simp [WrapTrailer, le32]
  | auto =>
    simp only [WrapTrailer]
    split <;> simp [le32, be32]

/-- `BYTEBITS(); state->mode = CHECK;` at the finished body: the loop meaning
holds at the trailer stage with no trailer byte read. -/
theorem final_loop {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    (loop : LoopMatches c f h l) (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (mode : s.mode = TYPE ∨ s.mode = TYPEDO) (last : s.last ≠ 0) (wrapped : f.wrap ≠ .raw) :
    LoopMatches c f (setI h zs { s with mode := CHECK }) (bytebits l) := by
  obtain ⟨zs0, s0, callOut, consumed, held, stage, st0, hs0, retOk, config, haveLe, inLen, binv,
    leftLe, pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  rw [st] at st0
  cases st0
  rw [hs] at hs0
  cases hs0
  obtain ⟨header, out, rfl⟩ := stage_of_final stageM mode last
  obtain ⟨⟨_, _, _, bitsLt⟩, _, check⟩ := stageM
  have bitsLt' : l.bits.toNat < 8 := bitsLt
  obtain ⟨flagsM, widthM, _⟩ := wrapM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  -- the registers after `BYTEBITS()`
  obtain ⟨binv', _, _⟩ := BYTEBITS_inv binv
  have bitsZero : (bytebits l).bits.toNat = 0 := by
    show (l.bits - (l.bits &&& 7)).toNat = 0
    rw [UInt32.toNat_sub_of_le l.bits (l.bits &&& 7) (UInt32.le_iff_toNat_le.mpr (and7_le l)),
      and7_toNat]
    omega
  have readSame : loopRead (bytebits l) = loopRead l := rfl
  have pendSame : loopPending (bytebits l) = loopPending l := rfl
  have heldNil : HeldBits (loopState { s with mode := CHECK } (bytebits l)) [] := by
    have small : (loopState { s with mode := CHECK } (bytebits l)).hold.toNat <
        2 ^ (loopState { s with mode := CHECK } (bytebits l)).bits.toNat := binv'.hold_lt
    have := HeldBits.of_natBits small
    have zero : (loopState { s with mode := CHECK } (bytebits l)).bits.toNat = 0 := bitsZero
    rw [zero] at this
    exact this
  -- the held bits are the padding of the last body byte
  have heldLen : held.length = l.bits.toNat := heldBits.1
  have padLen : held.length = (8 - bitsP.length % 8) % 8 := by
    have lengths := congrArg List.length bitsEq
    rw [consumedEq] at lengths
    simp only [List.length_append, bytesToBits_length'] at lengths
    omega
  refine ⟨zs, { s with mode := CHECK }, callOut, consumed ++ held, [],
    .trailer header out [], st, setI_istates_same _ _ _, retOk,
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1,
      show CHECK ≠ SYNC by decide⟩,
    haveLe, inLen, bitInv_setI binv', leftLe,
    ⟨by rw [pendSame]; exact pendLe.1, fun _ _ e => by cases e⟩, putEq, bytes_setI outBytes,
    MeaningTrailer.writable_setI writable, sepIn, sepWin, sepOutIn,
    by rw [readSame, List.append_nil, bitsEq], heldNil, ?_, ?_, ?_, outputEq⟩
  · refine ⟨bodyDict, bitsP, held, wrapHeader, deflate, wrapped, padLen, List.nil_prefix,
      wrapTrailer_ne_nil wrapped header out, ?_⟩
    rw [consumedEq]
    simp [bytesToBits]
  · rw [pendSame]
    exact ⟨Or.inl rfl, check⟩
  · exact ⟨flagsM, widthM, fun _ => rfl, fun m => absurd (show CHECK = LENGTH from m) (by decide),
      by show (bytebits l).bits.toNat ≤ 32; omega⟩

end MeaningTypeFinal

open MeaningTypeFinal in
/-- `TYPE`/`TYPEDO` after the last block, with a wrapper: `TYPE` with `Z_BLOCK`
or `Z_TREES` leaves with nothing changed; otherwise `BYTEBITS()` and on to
`CHECK`, the stage moving from the finished body to the trailer. -/
theorem trip_type_final : TripTypeFinal := by
  intro c f r wrapped h l side loop modeAt
  obtain ⟨zs, z, s, E, _⟩ := side.env
  obtain ⟨mode, last⟩ := modeAt zs s E.st E.hs
  have dispatch := inflate_dispatch_block_type E l mode
  have typedo : runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h →
      ∃ result l' h', runX (inflate_dispatch c) l h = .ok ((result, l'), h') ∧
        (TripOutcome c f result h' l' ∨ MeaningDictid.NeedDictExit c f result h' l' ∨
          (result = .ok () ∧ RawCheck c f h' l')) := by
    intro run
    refine ⟨_, _, _, run.trans (inflate_TYPEDO_last E l last), Or.inl (Or.inl ⟨rfl, Or.inl ?_⟩)⟩
    exact final_loop loop E.st E.hs mode last wrapped
  by_cases isType : s.mode = TYPE
  · rw [ite_eq_left_of_eq_true _ _ (eq_true isType)] at dispatch
    by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
    · exact ⟨_, _, _, dispatch.trans (inflate_TYPE_leave c l h flush),
        Or.inl (Or.inr ⟨rfl, Or.inl loop⟩)⟩
    · have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
        ⟨fun e => flush (Or.inl e), fun e => flush (Or.inr e)⟩
      exact typedo (dispatch.trans (inflate_TYPE_go c l h go))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false isType)] at dispatch
    exact typedo dispatch

#print axioms trip_type_final

end Zlib.Inflate.Proofs
