import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«deflate.c.universal-call-keep-base»
import Init.Data.Range.Lemmas
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»

/-! The checksum read loops are in `KeepRel` (`deflate.c.universal-call-keep-base`). Port of
`deflate.c.universal-params-checksum`. -/
set_option maxRecDepth 10000
namespace Zlib.Deflate.Universal.Keep
open C


theorem KeepM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (stable : ∀ value member state, KeepM (body value member state))
    (initial : β) : KeepM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact KeepM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply KeepM.bind (stable head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact KeepM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => stable value (by simp [member]) state) next

macro "keep_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact KeepM.pure _
    | exact KeepM.ub _
    | with_reducible exact keep_load8 _
    | with_reducible exact keep_index8 _ _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible exact keep_ptr_index _ _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.cdoWhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | intro x
    | dsimp only)

open Zlib.Adler32 in
theorem keep_adler_do1 (s : Locals) (i : Int) : KeepM (do1 s i) := by
  unfold do1
  keep_steps

open Zlib.Adler32 in
theorem keep_adler_do16 (s : Locals) : KeepM (do16 s) := by
  unfold do16
  repeat' first | with_reducible exact keep_adler_do1 _ _ | with_reducible apply KeepM.bind | intro x

open Zlib.Adler32 in
theorem keep_adler_stepByte (s : Locals) : KeepM (stepByte s) := by
  unfold stepByte
  keep_steps

open Zlib.Adler32 in
theorem keep_adler32_z (v : UInt64) (p : BPtr) (n : UInt64) : KeepM (adler32_z v p n) := by
  unfold adler32_z
  repeat' first
    | with_reducible exact keep_adler_do16 _
    | with_reducible exact keep_adler_stepByte _
    | (unfold lenPostDec; exact KeepM.pure _)
    | with_reducible exact KeepM.pure _
    | with_reducible exact keep_index8 _ _
    | with_reducible exact keep_ptr_add _ _
    | with_reducible apply KeepM.cwhile
    | with_reducible apply KeepM.cdoWhile
    | with_reducible apply KeepM.ite
    | with_reducible apply KeepM.bind
    | intro x
    | dsimp only

open Zlib.Adler32 in
theorem keep_adler32 (v : UInt64) (p : BPtr) (n : UInt32) : KeepM (adler32 v p n) :=
  keep_adler32_z _ _ _

open Zlib.Crc32 in
theorem keep_crc32_z (v : UInt64) (p : BPtr) (n : UInt64) : KeepM (crc32_z v p n) := by
  intro h val after hr
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged v p n h val after hr
  exact KeepRel.refl h

open Zlib.Crc32 in
theorem keep_crc32 (v : UInt64) (p : BPtr) (n : UInt32) : KeepM (crc32 v p n) :=
  keep_crc32_z _ _ _

end Zlib.Deflate.Universal.Keep
