import ZlibF.Proof.«public-gz-sequence-safety»
import ZlibF.Spec.Safety.GzCalls

/-!
# gz file interface: the per-function safety goals

Each goal of `ZlibF/Spec/Safety/GzCalls.lean` is a clause of `Goal.gz_sequence_safety` restricted to
one function, so each proof applies `gz_sequence_safety_public`. The `NULL` refusal of a call on a handle
holds by evaluation, as in `Goal.gz_refusal`.
-/

namespace ZlibF.Spec.Public.GzCallSafetyProof
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- A clause-2 restriction holds by clause 2 of `Goal.gz_sequence_safety`. -/
theorem call_safety (selects : Call → Prop) : GzCallSafety selects :=
  fun h fs i s call hist hs _ op args => ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.1 h fs i s call hist hs op args

/-- A clause-5 restriction holds by clause 5 of `Goal.gz_sequence_safety`. -/
theorem close_safety (selects : Call → Prop) : GzCloseCallSafety selects :=
  fun h fs i s call hist hs _ close => ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.2.2.2.1 h fs i s call hist hs close

/-- `Goal.gzbuffer_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzbuffer`. -/
theorem gzbuffer_safety : Goal.gzbuffer_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzclearerr_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzclearerr`. -/
theorem gzclearerr_safety : Goal.gzclearerr_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzdirect_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzdirect`. -/
theorem gzdirect_safety : Goal.gzdirect_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzeof_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzeof`. -/
theorem gzeof_safety : Goal.gzeof_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzflush_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzflush`. -/
theorem gzflush_safety : Goal.gzflush_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzfread_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzfread`. -/
theorem gzfread_safety : Goal.gzfread_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzfwrite_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzfwrite`. -/
theorem gzfwrite_safety : Goal.gzfwrite_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzgetc__safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzgetc_`. -/
theorem gzgetc__safety : Goal.gzgetc__safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzgets_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzgets`. -/
theorem gzgets_safety : Goal.gzgets_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzoffset_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzoffset`. -/
theorem gzoffset_safety : Goal.gzoffset_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzoffset64_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzoffset64`. -/
theorem gzoffset64_safety : Goal.gzoffset64_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzprintf_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzprintf`. -/
theorem gzprintf_safety : Goal.gzprintf_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzvprintf_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzvprintf`. -/
theorem gzvprintf_safety : Goal.gzvprintf_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzputc_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzputc`. -/
theorem gzputc_safety : Goal.gzputc_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzputs_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzputs`. -/
theorem gzputs_safety : Goal.gzputs_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzread_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzread`. -/
theorem gzread_safety : Goal.gzread_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzrewind_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzrewind`. -/
theorem gzrewind_safety : Goal.gzrewind_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzseek_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzseek`. -/
theorem gzseek_safety : Goal.gzseek_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzseek64_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzseek64`. -/
theorem gzseek64_safety : Goal.gzseek64_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzsetparams_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzsetparams`. -/
theorem gzsetparams_safety : Goal.gzsetparams_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gztell_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gztell`. -/
theorem gztell_safety : Goal.gztell_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gztell64_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gztell64`. -/
theorem gztell64_safety : Goal.gztell64_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzungetc_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzungetc`. -/
theorem gzungetc_safety : Goal.gzungetc_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzwrite_safety`: the `NULL` refusal by evaluation, and clause 2 of
`Goal.gz_sequence_safety` for the calls of `gzwrite`. -/
theorem gzwrite_safety : Goal.gzwrite_safety := ⟨by intros; rfl, call_safety _⟩

/-- `Goal.gzgetc_safety`: the `NULL` refusal by evaluation, and clauses 2 and 3 of
`Goal.gz_sequence_safety` (the function and the macro). -/
theorem gzgetc_safety : Goal.gzgetc_safety := ⟨by intros; rfl, call_safety _, ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.2.1⟩

/-- `Goal.gzerror_safety`: the `NULL` refusal by evaluation, and clauses 2 and 4 of
`Goal.gz_sequence_safety` (the call and its string). -/
theorem gzerror_safety : Goal.gzerror_safety := ⟨by intros; rfl, call_safety _, ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.2.2.1⟩

/-- `Goal.gzclose_safety`: the `NULL` refusal by evaluation, and clause 5 of
`Goal.gz_sequence_safety` for `gzclose`. -/
theorem gzclose_safety : Goal.gzclose_safety := ⟨by intros; rfl, close_safety _⟩

/-- `Goal.gzclose_r_safety`: the `NULL` refusal by evaluation, and clause 5 of
`Goal.gz_sequence_safety` for `gzclose_r`. -/
theorem gzclose_r_safety : Goal.gzclose_r_safety := ⟨by intros; rfl, close_safety _⟩

/-- `Goal.gzclose_w_safety`: the `NULL` refusal by evaluation, and clause 5 of
`Goal.gz_sequence_safety` for `gzclose_w`. -/
theorem gzclose_w_safety : Goal.gzclose_w_safety := ⟨by intros; rfl, close_safety _⟩

/-- `Goal.gzopen_safety`: the `gzopen` clause of `Goal.gz_sequence_safety`. -/
theorem gzopen_safety : Goal.gzopen_safety := ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.2.2.2.2.1

/-- `Goal.gzopen64_safety`: the `gzopen64` clause of `Goal.gz_sequence_safety`. -/
theorem gzopen64_safety : Goal.gzopen64_safety := ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.2.2.2.2.2.1

/-- `Goal.gzdopen_safety`: the `gzdopen` clause of `Goal.gz_sequence_safety`. -/
theorem gzdopen_safety : Goal.gzdopen_safety := ZlibF.Spec.Public.Proofs.gz_sequence_safety_public.2.2.2.2.2.2.2

end ZlibF.Spec.Public.GzCallSafetyProof
