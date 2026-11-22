import ZlibF.Proof.«inflate.c.meaning-trip»
import ZlibF.Proof.«inflate.c.meaning-trailer»

/-!
# inflate.c: the mode range of a trip (`LoopModeCases`, `GzipFieldsAbsent`)

`LoopModeCases`: the stage of `LoopMatches` places the decoder mode in one of the row groups of
`inflate.c.meaning-trip`. `GzipFieldsAbsent`: in a zlib or raw configuration the gzip header
field modes do not occur, since the safety invariant admits them only under a gzip wrapper code
and `ConfigMatches` fixes the code.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem u32_eq_iff {a b : UInt32} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun e => congrArg UInt32.toNat e, fun e => UInt32.toNat_inj.mp e⟩

/-- `LoopModeCases`, from the stage of `LoopMatches`. -/
theorem loop_mode_cases : LoopModeCases := by
  intro c f h l loop
  obtain ⟨zs, s, _, _, _, stage, st, hs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stageM,
    _, _⟩ := loop
  refine ⟨zs, s, st, hs, ?_⟩
  have range : (HEAD ≤ s.mode ∧ s.mode ≤ DICTID) ∨ s.mode = DICT ∨ (TYPE ≤ s.mode ∧ s.mode ≤ LIT) ∨
      s.mode = CHECK ∨ s.mode = LENGTH ∨ s.mode = DONE := by
    rcases stage with b | b | ⟨b, pos⟩ | ⟨header, out, bytes⟩ | out
    · exact Or.inl stageM
    · exact Or.inr (Or.inl stageM)
    · exact Or.inr (Or.inr (Or.inl (MeaningTrailer.body_mode_range (s := loopState s l) stageM.1)))
    · rcases stageM.1 with x | x
      · exact Or.inr (Or.inr (Or.inr (Or.inl x)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl x))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr stageM))))
  have k : HEAD.toNat = 16180 ∧ FLAGS.toNat = 16181 ∧ HCRC.toNat = 16188 ∧ DICTID.toNat = 16189 ∧
      DICT.toNat = 16190 ∧ TYPE.toNat = 16191 ∧ TYPEDO.toNat = 16192 ∧ STORED.toNat = 16193 ∧
      COPY_.toNat = 16194 ∧ COPY.toNat = 16195 ∧ TABLE.toNat = 16196 ∧ LENLENS.toNat = 16197 ∧
      CODELENS.toNat = 16198 ∧ LEN_.toNat = 16199 ∧ LIT.toNat = 16205 ∧ CHECK.toNat = 16206 ∧
      LENGTH.toNat = 16207 ∧ DONE.toNat = 16208 ∧ (0 : UInt32).toNat = 0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19⟩ := k
  by_cases hl : s.last = 0
  · simp only [hl, ne_eq, not_true_eq_false, and_true, and_false]
    simp only [UInt32.le_iff_toNat_le, u32_eq_iff, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10,
      k11, k12, k13, k14, k15, k16, k17, k18] at range ⊢
    omega
  · simp only [hl, ne_eq, not_false_eq_true, and_true, and_false, false_or]
    simp only [UInt32.le_iff_toNat_le, u32_eq_iff, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10,
      k11, k12, k13, k14, k15, k16, k17, k18] at range ⊢
    omega

/-- `GzipFieldsAbsent`, from `DefaultStateJ.modes` and `ConfigMatches`. -/
theorem gzip_fields_absent : GzipFieldsAbsent := by
  intro c f r h l side loop plain zs s st hs range
  obtain ⟨zs', z', s', _, st', j, _⟩ := side
  have e : zs' = zs := by
    rw [st] at st'
    cases st'
    rfl
  subst e
  have e2 : s' = s := Option.some.inj (j.good.live.hs.symm.trans hs)
  subst e2
  obtain ⟨zs2, s2, _, _, _, _, st2, hs2, _, config, _⟩ := loop
  have e3 : zs2 = zs' := by
    rw [st] at st2
    cases st2
    rfl
  subst e3
  have e4 : s2 = s' := Option.some.inj (hs2.symm.trans hs)
  subst e4
  have wrapEq : s2.wrap = wrapCode f.wrap := config.1
  rcases j.modes with m | m | g
  · rw [m] at range
    exact absurd range.1 (by decide)
  · exact absurd (UInt32.le_trans m.1 range.2) (by decide)
  · obtain ⟨_, _, allowed, _⟩ := g
    rw [wrapEq] at allowed
    rcases plain with p | p <;> rw [p] at allowed <;> unfold GzipAllowed wrapCode at allowed <;>
      revert allowed <;> decide

#print axioms loop_mode_cases
#print axioms gzip_fields_absent

end Zlib.Inflate.Proofs
