import ZlibF.Proof.«infback.c.safety-fast»
import ZlibF.Proof.«public-infback-end»
import ZlibF.Proof.«public-infback-init»
import ZlibF.Proof.«infback.c.back»
import ZlibF.Proof.«public-init-safety»
import ZlibF.Spec.Safety.Back

/-!
# Callback decoder: the per-function safety goals

`Goal.inflateBack_safety` and `Goal.inflateBackEnd_safety` are clauses of
`Goal.inflate_back_sequence_safety`, with the refusals of `inflateBack_nostate` and
`back_end_public`. `Goal.inflateBackInit__safety` follows from the functional init theorem
`back_init_public`: its refusal clauses leave the heap unchanged, its allocation failure keeps the
same objects up to the prepared stream, and its success gives a valid state.
-/

namespace ZlibF.Spec.Public.BackSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `Goal.inflateBack_safety`: clauses 1 and 3 of `Goal.inflate_back_sequence_safety`, and the
refusal of a `NULL` state by `inflateBack_nostate`. -/
theorem inflateBack_safety : Goal.inflateBack_safety :=
  ⟨Zlib.Infback.Safety.inflate_back_sequence_safety.1,
   fun _ _ _ input inDesc output outDesc hz hno =>
     Zlib.Infback.Proofs.inflateBack_nostate hz hno input inDesc output outDesc,
   Zlib.Infback.Safety.inflate_back_sequence_safety.2.2.1⟩

/-- `Goal.inflateBackEnd_safety`: the refusal clauses of `back_end_public` and clause 4 of
`Goal.inflate_back_sequence_safety`. -/
theorem inflateBackEnd_safety : Goal.inflateBackEnd_safety :=
  ⟨ZlibF.Spec.Public.InflateBackEndProof.back_end_public.1,
   ZlibF.Spec.Public.InflateBackEndProof.back_end_public.2.1,
   Zlib.Infback.Safety.inflate_back_sequence_safety.2.2.2⟩

/-- The heap unchanged is a frame of the stream record with no live change. -/
theorem unchanged (h : Heap) (r : ZStreamRef) :
    Frame h h (StreamRoot r) ∧ LiveChange h h (fun _ => False) (fun _ => False) :=
  ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
   fun b => by simp⟩

/-- `Goal.inflateBackInit__safety`: `inflateBackInit_` is safe on every call `zlib.h` allows; from
`back_init_public`. A version or stream-size mismatch, a `NULL` stream, a `NULL` window and window
bits out of range are refused with the heap unchanged; an allocation failure changes only the stream
record; `Z_OK` gives a valid state over the window with only the state block new. -/
theorem inflateBackInit__safety : Goal.inflateBackInit__safety := by
  intro h strm version size wb window ⟨hf, hu, hg, ⟨head, hv⟩, hrec⟩ hwrite
  obtain ⟨hversion, hrefuse, hmain⟩ := ZlibF.Spec.Public.InflateBackInitProof.back_init_public
  by_cases hgood : head = some 49 ∧ size = 112
  · obtain ⟨rfl, rfl⟩ := hgood
    cases strm with
    | none =>
      exact ⟨Z_STREAM_ERROR, h, hrefuse h none wb window version hv (Or.inl rfl), Or.inr rfl, rfl⟩
    | some r =>
      obtain ⟨z, hz, hd⟩ := hrec r rfl
      by_cases hin : window ≠ .null ∧ 8 ≤ wb.toInt ∧ wb.toInt ≤ 15
      · obtain ⟨hwin, hlo, hhi⟩ := hin
        obtain ⟨rc, after, hrun, -, hbr⟩ :=
          hmain h r z wb window version hf hu hg hz hd hv hlo hhi hwin (hwrite hwin hlo hhi)
        refine ⟨rc, after, hrun, ?_⟩
        by_cases ha : h.allocOk h.nalloc = false
        · rw [ite_eq_left ha] at hbr
          obtain ⟨hrc, hsame⟩ := hbr
          obtain ⟨hfr, hl⟩ := InitSafetyProof.frame_of_same hz (InitSafetyProof.upToShape_of_same hsame)
          exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
        · rw [ite_eq_right ha] at hbr
          dsimp only at hbr
          obtain ⟨hrc, hvalid, hfr, hl⟩ := hbr
          exact ⟨hfr, Or.inl ⟨hrc, ⟨_, _, hvalid, rfl⟩, hl⟩⟩
      · have hcase : (some r = none ∨ window = .null ∨ wb.toInt < 8 ∨ 15 < wb.toInt) := by
          right
          by_cases hw : window = .null
          · exact Or.inl hw
          · right
            by_cases hl : 8 ≤ wb.toInt
            · by_cases hh : wb.toInt ≤ 15
              · exact absurd ⟨hw, hl, hh⟩ hin
              · exact Or.inr (by omega)
            · exact Or.inl (by omega)
        refine ⟨Z_STREAM_ERROR, h, hrefuse h (some r) wb window version hv hcase, ?_⟩
        exact ⟨(unchanged h r).1, Or.inr ⟨by decide, (unchanged h r).2⟩⟩
  · have hbad : head ≠ some 49 ∨ size ≠ 112 := by
      by_cases hh : head = some 49
      · exact Or.inr (fun hs => hgood ⟨hh, hs⟩)
      · exact Or.inl hh
    refine ⟨Z_VERSION_ERROR, h, hversion h strm wb window version head size hv hbad, ?_⟩
    cases strm with
    | none => exact ⟨Or.inl rfl, rfl⟩
    | some r => exact ⟨(unchanged h r).1, Or.inr ⟨by decide, (unchanged h r).2⟩⟩

end ZlibF.Spec.Public.BackSafetyProof
