import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«deflate.c.universal-params-prims»
import Init.Data.Range.Lemmas
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»

/-! The checksum read loops keep every parameter. -/
set_option maxRecDepth 10000
namespace Zlib.Deflate.Universal.Params
open C


theorem ExactM.list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (stable : ∀ value member state, ExactM (body value member state))
    (initial : β) : ExactM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact ExactM.pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    apply ExactM.bind (stable head (by simp) initial)
    intro decision
    cases decision with
    | done value => exact ExactM.pure _
    | yield next =>
      exact ih (fun value member state => body value (by simp [member]) state)
        (fun value member state => stable value (by simp [member]) state) next

macro "exact_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact ExactM.pure _
    | exact ExactM.ub _
    | with_reducible exact exact_load8 _
    | with_reducible exact exact_index8 _ _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible exact exact_ptr_index _ _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.cdoWhile
    | with_reducible apply ExactM.ite
    | with_reducible apply ExactM.bind
    | intro x
    | dsimp only)

open Zlib.Adler32 in
theorem exact_adler_do1 (s : Locals) (i : Int) : ExactM (do1 s i) := by
  unfold do1
  exact_steps

open Zlib.Adler32 in
theorem exact_adler_do16 (s : Locals) : ExactM (do16 s) := by
  unfold do16
  repeat' first | with_reducible exact exact_adler_do1 _ _ | with_reducible apply ExactM.bind | intro x

open Zlib.Adler32 in
theorem exact_adler_stepByte (s : Locals) : ExactM (stepByte s) := by
  unfold stepByte
  exact_steps

open Zlib.Adler32 in
theorem exact_adler32_z (v : UInt64) (p : BPtr) (n : UInt64) : ExactM (adler32_z v p n) := by
  unfold adler32_z
  repeat' first
    | with_reducible exact exact_adler_do16 _
    | with_reducible exact exact_adler_stepByte _
    | (unfold lenPostDec; exact ExactM.pure _)
    | with_reducible exact ExactM.pure _
    | with_reducible exact exact_index8 _ _
    | with_reducible exact exact_ptr_add _ _
    | with_reducible apply ExactM.cwhile
    | with_reducible apply ExactM.cdoWhile
    | with_reducible apply ExactM.ite
    | with_reducible apply ExactM.bind
    | intro x
    | dsimp only

open Zlib.Adler32 in
theorem exact_adler32 (v : UInt64) (p : BPtr) (n : UInt32) : ExactM (adler32 v p n) :=
  exact_adler32_z _ _ _

open Zlib.Crc32 in
theorem exact_crc32_z (v : UInt64) (p : BPtr) (n : UInt64) : ExactM (crc32_z v p n) := by
  intro h val after hr
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged v p n h val after hr
  exact ExactRel.refl h

open Zlib.Crc32 in
theorem exact_crc32 (v : UInt64) (p : BPtr) (n : UInt32) : ExactM (crc32 v p n) :=
  exact_crc32_z _ _ _

end Zlib.Deflate.Universal.Params
