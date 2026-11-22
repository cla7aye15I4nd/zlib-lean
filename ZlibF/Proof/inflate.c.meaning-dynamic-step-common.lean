import ZlibF.Proof.«inflate.c.meaning-length»
import ZlibF.Proof.«inflate.c.meaning-dynamic»
import ZlibF.Proof.«inflate.c.table-fields-meaning»
import ZlibF.Proof.«inflate.c.header-chunks»
import ZlibF.Proof.«inflate.c.lenlens-input»
import ZlibF.Proof.«inflate.c.code-length-install»
import ZlibF.Proof.«inflate.c.lenlens-code-length-meaning»
import ZlibF.Proof.«inflate.c.meaning-codelens-items»
import ZlibF.Proof.«inflate.c.meaning-dynamic-tables»

/-! The definitions and lemmas that the `TABLE`, `LENLENS` and `CODELENS` steps of
`inflate.c.meaning-dynamic-steps` share. -/

namespace Zlib.Inflate.Proofs.MeaningDynamicSteps
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningDynamic
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-! ## Stages and bits -/

/-- The only stage a `TABLE`, `LENLENS` or `CODELENS` state can stand for. -/
theorem stage_of_dynamic {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ header out final hdr, stage = .body header ⟨out, final, .dynamicHeader hdr⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rcases mode with m | m | m <;> rw [m] at lo hi <;> exact absurd hi (by decide)
  · have this := stageFacts
    simp only [LoopStageMatches] at this
    rcases mode with m | m | m <;> rw [m] at this <;> exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | hdr | ⟨L, D, pending⟩ | _
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · exact ⟨header, out, final, hdr, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      all_goals (rcases mode with m | m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide))
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · obtain ⟨m', _⟩ := stageFacts
    rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rcases mode with m | m | m <;> rw [m] at m' <;> exact absurd m' (by decide)

/-- The state record after a `BAD` exit has mode `BAD`. -/
theorem bad_heap_mode {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {i : Nat} (st : c.st = some (.tab zs)) :
    ∀ zs' s', c.st = some (.tab zs') → (tcBadHeap h r zs z s i).istates zs' = some s' →
      s'.mode = BAD := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  simp only [tcBadHeap, setI_istates_same, Option.some.injEq] at hs'
  rw [← hs']

/-- The state record after `setI` is the one stored. -/
theorem setI_state {c : Ctx} {h : Heap} {zs : Nat} (s2 : InflateState) (st : c.st = some (.tab zs)) :
    ∀ zs' s', c.st = some (.tab zs') → (setI h zs s2).istates zs' = some s' → s' = s2 := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  rw [setI_istates_same] at hs'
  cases hs'
  rfl

/-- The three count fields read from the low 14 held bits. -/
theorem counts_bits (v : Nat) :
    readBits 5 (natBits 14 v) = some (v % 32, natBits 9 (v / 32)) ∧
    readBits 5 (natBits 9 (v / 32)) = some (v / 32 % 32, natBits 4 (v / 32 / 32)) ∧
    readBits 4 (natBits 4 (v / 32 / 32)) = some (v / 32 / 32 % 16, []) := by
  have s14 : natBits 14 v = natBits 5 v ++ natBits 9 (v / 32) := natBits_add 5 9 v
  have s9 : natBits 9 (v / 32) = natBits 5 (v / 32) ++ natBits 4 (v / 32 / 32) :=
    natBits_add 5 4 (v / 32)
  refine ⟨?_, ?_, ?_⟩
  · rw [s14, readBits_natBits]
  · rw [s9, readBits_natBits]
  · have := readBits_natBits 4 (v / 32 / 32) []
    rwa [List.append_nil] at this

/-- Bytes read after the held bits join them. -/
theorem bits_take {f : LoopFrame} {l : IL} {j : Nat} {consumed held : List Bool}
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held) :
    bytesToBits (f.logIn ++ f.inp.take (loopRead l + j)) =
      consumed ++ (held ++ bytesBits ((f.inp.drop (loopRead l)).take j)) := by
  rw [List.take_add, ← List.append_assoc, bytesToBits_append', bitsEq, bytesBits_eq_bytesToBits,
    List.append_assoc]

end Zlib.Inflate.Proofs.MeaningDynamicSteps
