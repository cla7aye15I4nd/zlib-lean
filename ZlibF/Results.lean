import ZlibF
import ZlibF.ResultsCheck

/-!
# Results

The safety-only registry of results, checked by Lean when the library is built.

`proved` pairs each proved safety goal with the theorem that proves it. `notDone` is empty (`[]`).
`required` lists the 99 required safety goals: the safety goal of every documented function of
`zlib.h`, the safety goals of sequences and refusals, and the non-vacuity goals. Functional and
round-trip goals outside the maintained safety scope have been excluded from the registry.

The command at the end of this file (`checkWith`, in `ZlibF/ResultsCheck.lean`) fails the build
unless each theorem's type is exactly its goal, each theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`, every required goal is proved, and every goal in safety
scope (`ZlibF.Spec.Safety.*`, `compressBound`, `compressBound_z`) is listed. It prints the counts.
-/

namespace ZlibF.Results
open Lean Elab Command

/-- Each proved safety goal, and the theorem whose type is exactly that goal. -/
def proved : List (Name × Name) := [
  -- Safety of each stream function
  (``ZlibF.Spec.Public.Goal.deflateBound_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_safety),
  (``ZlibF.Spec.Public.Goal.deflateBound_z_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateBound_z_safety),
  (``ZlibF.Spec.Public.Goal.deflateEnd_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateEnd_safety),
  (``ZlibF.Spec.Public.Goal.deflateGetDictionary_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateGetDictionary_safety),
  (``ZlibF.Spec.Public.Goal.deflateParams_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateParams_safety),
  (``ZlibF.Spec.Public.Goal.deflatePending_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflatePending_safety),
  (``ZlibF.Spec.Public.Goal.deflatePrime_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflatePrime_safety),
  (``ZlibF.Spec.Public.Goal.deflateReset_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateReset_safety),
  (``ZlibF.Spec.Public.Goal.deflateSetDictionary_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetDictionary_safety),
  (``ZlibF.Spec.Public.Goal.deflateSetHeader_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateSetHeader_safety),
  (``ZlibF.Spec.Public.Goal.deflateTune_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateTune_safety),
  (``ZlibF.Spec.Public.Goal.deflateUsed_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflateUsed_safety),
  (``ZlibF.Spec.Public.Goal.deflate_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.deflate_safety),
  (``ZlibF.Spec.Public.Goal.inflateEnd_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateEnd_safety),
  (``ZlibF.Spec.Public.Goal.inflateGetDictionary_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateGetDictionary_safety),
  (``ZlibF.Spec.Public.Goal.inflateGetHeader_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateGetHeader_safety),
  (``ZlibF.Spec.Public.Goal.inflateMark_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateMark_safety),
  (``ZlibF.Spec.Public.Goal.inflatePrime_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflatePrime_safety),
  (``ZlibF.Spec.Public.Goal.inflateReset2_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateReset2_safety),
  (``ZlibF.Spec.Public.Goal.inflateReset_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateReset_safety),
  (``ZlibF.Spec.Public.Goal.inflateSetDictionary_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateSetDictionary_safety),
  (``ZlibF.Spec.Public.Goal.inflateSync_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflateSync_safety),
  (``ZlibF.Spec.Public.Goal.inflate_safety, ``ZlibF.Spec.Public.StreamCallSafetyProof.inflate_safety),
  -- Safety of the initialisation functions
  (``ZlibF.Spec.Public.Goal.deflateInit2__safety, ``ZlibF.Spec.Public.InitSafetyProof.deflateInit2__safety),
  (``ZlibF.Spec.Public.Goal.deflateInit__safety, ``ZlibF.Spec.Public.InitSafetyProof.deflateInit__safety),
  (``ZlibF.Spec.Public.Goal.inflateInit2__safety, ``ZlibF.Spec.Public.InitSafetyProof.inflateInit2__safety),
  (``ZlibF.Spec.Public.Goal.inflateInit__safety, ``ZlibF.Spec.Public.InitSafetyProof.inflateInit__safety),
  -- Safety of the copy functions
  (``ZlibF.Spec.Public.Goal.deflateCopy_safety, ``Zlib.Deflate.Universal.deflate_copy_safety),
  (``ZlibF.Spec.Public.Goal.inflateCopy_safety, ``ZlibF.Spec.Public.InflateCopySafetyProof.inflateCopy_safety),
  -- Safety of the query functions
  (``ZlibF.Spec.Public.Goal.zlibCompileFlags_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.zlibCompileFlags_safety),
  (``ZlibF.Spec.Public.Goal.zlibVersion_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.zlibVersion_safety),
  (``ZlibF.Spec.Public.Goal.compressBound, ``ZlibF.Spec.Public.Proofs.compressBound),
  (``ZlibF.Spec.Public.Goal.compressBound_z, ``ZlibF.Spec.Public.Proofs.compressBound_z),
  -- Safety of the checksum functions
  (``ZlibF.Spec.Public.Goal.adler32_combine64_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine64_safety),
  (``ZlibF.Spec.Public.Goal.adler32_combine_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.adler32_combine_safety),
  (``ZlibF.Spec.Public.Goal.adler32_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.adler32_safety),
  (``ZlibF.Spec.Public.Goal.adler32_z_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.adler32_z_safety),
  (``ZlibF.Spec.Public.Goal.crc32_combine64_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine64_safety),
  (``ZlibF.Spec.Public.Goal.crc32_combine_gen64_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_gen64_safety),
  (``ZlibF.Spec.Public.Goal.crc32_combine_gen_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_gen_safety),
  (``ZlibF.Spec.Public.Goal.crc32_combine_op_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_op_safety),
  (``ZlibF.Spec.Public.Goal.crc32_combine_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_combine_safety),
  (``ZlibF.Spec.Public.Goal.crc32_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_safety),
  (``ZlibF.Spec.Public.Goal.crc32_z_safety, ``ZlibF.Spec.Public.StatelessSafetyProof.crc32_z_safety),
  -- Safety of compress and uncompress
  (``ZlibF.Spec.Public.Goal.compress2_safety, ``ZlibF.Spec.Public.Proofs.Compress.compress2_safety),
  (``ZlibF.Spec.Public.Goal.compress2_z_safety, ``ZlibF.Spec.Public.Proofs.Compress.compress2_z_safety),
  (``ZlibF.Spec.Public.Goal.compress_safety, ``ZlibF.Spec.Public.Proofs.Compress.compress_safety),
  (``ZlibF.Spec.Public.Goal.compress_z_safety, ``ZlibF.Spec.Public.Proofs.Compress.compress_z_safety),
  (``ZlibF.Spec.Public.Goal.uncompress2_safe, ``ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_safe),
  (``ZlibF.Spec.Public.Goal.uncompress2_z_safe, ``ZlibF.Spec.Public.Proofs.Uncompress.uncompress2_z_safe),
  (``ZlibF.Spec.Public.Goal.uncompress_safe, ``ZlibF.Spec.Public.Proofs.Uncompress.uncompress_safe),
  (``ZlibF.Spec.Public.Goal.uncompress_z_safe, ``ZlibF.Spec.Public.Proofs.Uncompress.uncompress_z_safe),
  -- Safety of the callback decoder (inflateBack)
  (``ZlibF.Spec.Public.Goal.inflateBackEnd_safety, ``ZlibF.Spec.Public.BackSafetyProof.inflateBackEnd_safety),
  (``ZlibF.Spec.Public.Goal.inflateBackInit__safety, ``ZlibF.Spec.Public.BackSafetyProof.inflateBackInit__safety),
  (``ZlibF.Spec.Public.Goal.inflateBack_safety, ``ZlibF.Spec.Public.BackSafetyProof.inflateBack_safety),
  -- Safety of each gzip file function
  (``ZlibF.Spec.Public.Goal.gzbuffer_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzbuffer_safety),
  (``ZlibF.Spec.Public.Goal.gzclearerr_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzclearerr_safety),
  (``ZlibF.Spec.Public.Goal.gzclose_r_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzclose_r_safety),
  (``ZlibF.Spec.Public.Goal.gzclose_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzclose_safety),
  (``ZlibF.Spec.Public.Goal.gzclose_w_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzclose_w_safety),
  (``ZlibF.Spec.Public.Goal.gzdirect_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzdirect_safety),
  (``ZlibF.Spec.Public.Goal.gzdopen_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzdopen_safety),
  (``ZlibF.Spec.Public.Goal.gzeof_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzeof_safety),
  (``ZlibF.Spec.Public.Goal.gzerror_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzerror_safety),
  (``ZlibF.Spec.Public.Goal.gzflush_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzflush_safety),
  (``ZlibF.Spec.Public.Goal.gzfread_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzfread_safety),
  (``ZlibF.Spec.Public.Goal.gzfwrite_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzfwrite_safety),
  (``ZlibF.Spec.Public.Goal.gzgetc__safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzgetc__safety),
  (``ZlibF.Spec.Public.Goal.gzgetc_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzgetc_safety),
  (``ZlibF.Spec.Public.Goal.gzgets_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzgets_safety),
  (``ZlibF.Spec.Public.Goal.gzoffset64_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzoffset64_safety),
  (``ZlibF.Spec.Public.Goal.gzoffset_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzoffset_safety),
  (``ZlibF.Spec.Public.Goal.gzopen64_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzopen64_safety),
  (``ZlibF.Spec.Public.Goal.gzopen_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzopen_safety),
  (``ZlibF.Spec.Public.Goal.gzprintf_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzprintf_safety),
  (``ZlibF.Spec.Public.Goal.gzvprintf_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzvprintf_safety),
  (``ZlibF.Spec.Public.Goal.gzputc_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzputc_safety),
  (``ZlibF.Spec.Public.Goal.gzputs_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzputs_safety),
  (``ZlibF.Spec.Public.Goal.gzread_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzread_safety),
  (``ZlibF.Spec.Public.Goal.gzrewind_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzrewind_safety),
  (``ZlibF.Spec.Public.Goal.gzseek64_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzseek64_safety),
  (``ZlibF.Spec.Public.Goal.gzseek_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzseek_safety),
  (``ZlibF.Spec.Public.Goal.gzsetparams_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzsetparams_safety),
  (``ZlibF.Spec.Public.Goal.gztell64_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gztell64_safety),
  (``ZlibF.Spec.Public.Goal.gztell_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gztell_safety),
  (``ZlibF.Spec.Public.Goal.gzungetc_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzungetc_safety),
  (``ZlibF.Spec.Public.Goal.gzwrite_safety, ``ZlibF.Spec.Public.GzCallSafetyProof.gzwrite_safety),
  -- Safety of every gzip file history, and its non-vacuity
  (``ZlibF.Spec.Public.Goal.gz_sequence_nonvacuity, ``ZlibF.Spec.Public.Proofs.GzNonvacuity.gz_sequence_nonvacuity_public),
  (``ZlibF.Spec.Public.Goal.gz_sequence_safety, ``ZlibF.Spec.Public.Proofs.gz_sequence_safety_public),
  -- Safety of call sequences
  (``ZlibF.Spec.Public.Goal.deflate_sequence_safety, ``Zlib.Deflate.Universal.deflate_sequence_safety),
  (``ZlibF.Spec.Public.Goal.inflate_back_sequence_safety, ``Zlib.Infback.Safety.inflate_back_sequence_safety),
  (``ZlibF.Spec.Public.Goal.inflate_sequence_safety, ``Zlib.Inflate.Proofs.inflate_sequence_safety_public),
  -- Refusals of the stream functions
  (``ZlibF.Spec.Public.Goal.deflate_refusal, ``ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal),
  (``ZlibF.Spec.Public.Goal.inflate_refusal, ``ZlibF.Spec.Public.RefusalProof.inflate_refusal),
  -- Refusals of the gzip file functions
  (``ZlibF.Spec.Public.Goal.gz_refusal, ``ZlibF.Spec.Public.GzRefusalProof.gz_refusal),
  -- Non-vacuity of the initialisation domains
  (``ZlibF.Spec.Public.Goal.deflate_initialisation_domain, ``ZlibF.Spec.Public.Proofs.DeflateInitDomain.deflate_initialisation_domain_public),
  (``ZlibF.Spec.Public.Goal.inflate_back_initialisation_domain, ``ZlibF.Spec.Public.InflateBackInitProof.back_init_domain_public),
  (``ZlibF.Spec.Public.Goal.inflateBack_call_domain, ``ZlibF.Spec.Public.BackCallDomainProof.inflateBack_call_domain),
  (``ZlibF.Spec.Public.Goal.inflate_initialisation_domain, ``ZlibF.Spec.Public.Proofs.InflateInit.inflate_initialisation_domain_public),
  -- Safety lemmas stated as goals: byte addresses
  (``C.ByteAddress.Spec.Goal.address_read_is_pure, ``C.ByteAddress.Proofs.address_read_is_pure),
  (``C.ByteAddress.Spec.Goal.byte_modifies_preserve_bases, ``C.ByteAddress.Proofs.byte_modifies_preserve_bases),
  (``C.ByteAddress.Spec.Goal.byte_stores_preserve_bases, ``C.ByteAddress.Proofs.byte_stores_preserve_bases),
  (``C.ByteAddress.Spec.Goal.every_existing_heap_accepts_layout, ``C.ByteAddress.Proofs.every_existing_heap_accepts_layout),
  (``C.ByteAddress.Spec.Goal.every_layout_is_representable, ``C.ByteAddress.Proofs.every_layout_is_representable),
  (``C.ByteAddress.Spec.Goal.first_aligned_offset, ``C.ByteAddress.Proofs.first_aligned_offset),
  (``C.ByteAddress.Spec.Goal.mask_refines_base_plus_offset, ``C.ByteAddress.Proofs.mask_refines_base_plus_offset),
  (``C.ByteAddress.Spec.Goal.pointer_advance_preserves_low_bits, ``C.ByteAddress.Proofs.pointer_advance_preserves_low_bits),
  (``C.ByteAddress.Spec.Goal.raw_block_unchanged, ``C.ByteAddress.Proofs.raw_block_unchanged),
  -- Safety lemmas stated as goals: the fast decoder
  (``Zlib.Inffast.Spec.Goal.fast_safe, ``Zlib.Inffast.Proofs.inflate_fast_safe),
  (``Zlib.Inffast.Spec.Goal.step_safe, ``Zlib.Inffast.Proofs.inflate_fast_body_step_safe),
  -- Safety lemmas stated as goals: the fast decoder's distances
  (``Zlib.Inffast.Spec.BodyOrigin.Goal.actual_body_preserves_origin, ``Zlib.Inffast.Proofs.actual_body_preserves_origin),
  (``Zlib.Inffast.Spec.CallOrigin.Goal.actual_fast_preserves_origin, ``ZlibF.Proof.Registration.fast_call_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.actual_drop_preserves_origin, ``Zlib.Inffast.Proofs.actual_drop_preserves_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.actual_pull_preserves_origin, ``Zlib.Inffast.Proofs.actual_pull_preserves_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.actual_rollback_preserves_origin, ``Zlib.Inffast.Proofs.actual_rollback_preserves_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.drop_preserves_origin, ``Zlib.Inffast.Proofs.drop_preserves_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.initial_origin, ``Zlib.Inffast.Proofs.initial_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.pull_preserves_origin, ``Zlib.Inffast.Proofs.pull_preserves_origin),
  (``Zlib.Inffast.Spec.Origin.Goal.rollback_preserves_origin, ``Zlib.Inffast.Proofs.rollback_preserves_origin),
  -- Safety lemmas stated as goals: the decoding tables
  (``Zlib.Inftrees.Spec.Goal.inflate_table_content, ``Zlib.Inftrees.Proofs.inflate_table_content),
  (``Zlib.Inftrees.Spec.Goal.inflate_table_decoder_safe, ``Zlib.Inftrees.Proofs.inflate_table_decoder_safe),
  (``Zlib.Inftrees.Spec.Goal.inflate_table_read_extent, ``Zlib.Inftrees.Proofs.inflate_table_read_extent),
  (``Zlib.Inftrees.Spec.RootTable.Goal.constructor_root_bits, ``Zlib.Inftrees.Proofs.constructor_root_bits),
  (``Zlib.Inftrees.Spec.Subtable.Goal.constructor_subtable_bits, ``Zlib.Inftrees.Proofs.constructor_subtable_bits)
]

/-- No unproved safety goals remain. -/
def notDone : List Name := []

/-- The required safety goals: the safety goal of every documented function of `zlib.h`, the
safety goals of sequences and refusals, and the non-vacuity goals. -/
def required : List Name := [
  ``ZlibF.Spec.Public.Goal.adler32_safety,
  ``ZlibF.Spec.Public.Goal.adler32_combine_safety,
  ``ZlibF.Spec.Public.Goal.adler32_combine64_safety,
  ``ZlibF.Spec.Public.Goal.adler32_z_safety,
  ``ZlibF.Spec.Public.Goal.compress_safety,
  ``ZlibF.Spec.Public.Goal.compress2_safety,
  ``ZlibF.Spec.Public.Goal.compress2_z_safety,
  ``ZlibF.Spec.Public.Goal.compressBound,
  ``ZlibF.Spec.Public.Goal.compressBound_z,
  ``ZlibF.Spec.Public.Goal.compress_z_safety,
  ``ZlibF.Spec.Public.Goal.crc32_safety,
  ``ZlibF.Spec.Public.Goal.crc32_combine_safety,
  ``ZlibF.Spec.Public.Goal.crc32_combine64_safety,
  ``ZlibF.Spec.Public.Goal.crc32_combine_gen_safety,
  ``ZlibF.Spec.Public.Goal.crc32_combine_gen64_safety,
  ``ZlibF.Spec.Public.Goal.crc32_combine_op_safety,
  ``ZlibF.Spec.Public.Goal.crc32_z_safety,
  ``ZlibF.Spec.Public.Goal.deflate_safety,
  ``ZlibF.Spec.Public.Goal.deflateBound_safety,
  ``ZlibF.Spec.Public.Goal.deflateBound_z_safety,
  ``ZlibF.Spec.Public.Goal.deflateCopy_safety,
  ``ZlibF.Spec.Public.Goal.deflateEnd_safety,
  ``ZlibF.Spec.Public.Goal.deflateGetDictionary_safety,
  ``ZlibF.Spec.Public.Goal.deflateInit2__safety,
  ``ZlibF.Spec.Public.Goal.deflateInit__safety,
  ``ZlibF.Spec.Public.Goal.deflateParams_safety,
  ``ZlibF.Spec.Public.Goal.deflatePending_safety,
  ``ZlibF.Spec.Public.Goal.deflatePrime_safety,
  ``ZlibF.Spec.Public.Goal.deflateReset_safety,
  ``ZlibF.Spec.Public.Goal.deflateSetDictionary_safety,
  ``ZlibF.Spec.Public.Goal.deflateSetHeader_safety,
  ``ZlibF.Spec.Public.Goal.deflateTune_safety,
  ``ZlibF.Spec.Public.Goal.deflateUsed_safety,
  ``ZlibF.Spec.Public.Goal.gzbuffer_safety,
  ``ZlibF.Spec.Public.Goal.gzclearerr_safety,
  ``ZlibF.Spec.Public.Goal.gzclose_safety,
  ``ZlibF.Spec.Public.Goal.gzclose_r_safety,
  ``ZlibF.Spec.Public.Goal.gzclose_w_safety,
  ``ZlibF.Spec.Public.Goal.gzdirect_safety,
  ``ZlibF.Spec.Public.Goal.gzdopen_safety,
  ``ZlibF.Spec.Public.Goal.gzeof_safety,
  ``ZlibF.Spec.Public.Goal.gzerror_safety,
  ``ZlibF.Spec.Public.Goal.gzflush_safety,
  ``ZlibF.Spec.Public.Goal.gzfread_safety,
  ``ZlibF.Spec.Public.Goal.gzfwrite_safety,
  ``ZlibF.Spec.Public.Goal.gzgetc_safety,
  ``ZlibF.Spec.Public.Goal.gzgetc__safety,
  ``ZlibF.Spec.Public.Goal.gzgets_safety,
  ``ZlibF.Spec.Public.Goal.gzoffset_safety,
  ``ZlibF.Spec.Public.Goal.gzoffset64_safety,
  ``ZlibF.Spec.Public.Goal.gzopen_safety,
  ``ZlibF.Spec.Public.Goal.gzopen64_safety,
  ``ZlibF.Spec.Public.Goal.gzprintf_safety,
  ``ZlibF.Spec.Public.Goal.gzputc_safety,
  ``ZlibF.Spec.Public.Goal.gzputs_safety,
  ``ZlibF.Spec.Public.Goal.gzread_safety,
  ``ZlibF.Spec.Public.Goal.gzrewind_safety,
  ``ZlibF.Spec.Public.Goal.gzseek_safety,
  ``ZlibF.Spec.Public.Goal.gzseek64_safety,
  ``ZlibF.Spec.Public.Goal.gzsetparams_safety,
  ``ZlibF.Spec.Public.Goal.gztell_safety,
  ``ZlibF.Spec.Public.Goal.gztell64_safety,
  ``ZlibF.Spec.Public.Goal.gzungetc_safety,
  ``ZlibF.Spec.Public.Goal.gzwrite_safety,
  ``ZlibF.Spec.Public.Goal.inflate_safety,
  ``ZlibF.Spec.Public.Goal.inflateBack_safety,
  ``ZlibF.Spec.Public.Goal.inflateBackEnd_safety,
  ``ZlibF.Spec.Public.Goal.inflateBackInit__safety,
  ``ZlibF.Spec.Public.Goal.inflateCopy_safety,
  ``ZlibF.Spec.Public.Goal.inflateEnd_safety,
  ``ZlibF.Spec.Public.Goal.inflateGetDictionary_safety,
  ``ZlibF.Spec.Public.Goal.inflateGetHeader_safety,
  ``ZlibF.Spec.Public.Goal.inflateInit2__safety,
  ``ZlibF.Spec.Public.Goal.inflateInit__safety,
  ``ZlibF.Spec.Public.Goal.inflateMark_safety,
  ``ZlibF.Spec.Public.Goal.inflatePrime_safety,
  ``ZlibF.Spec.Public.Goal.inflateReset_safety,
  ``ZlibF.Spec.Public.Goal.inflateReset2_safety,
  ``ZlibF.Spec.Public.Goal.inflateSetDictionary_safety,
  ``ZlibF.Spec.Public.Goal.inflateSync_safety,
  ``ZlibF.Spec.Public.Goal.uncompress_safe,
  ``ZlibF.Spec.Public.Goal.uncompress2_safe,
  ``ZlibF.Spec.Public.Goal.uncompress2_z_safe,
  ``ZlibF.Spec.Public.Goal.uncompress_z_safe,
  ``ZlibF.Spec.Public.Goal.zlibCompileFlags_safety,
  ``ZlibF.Spec.Public.Goal.zlibVersion_safety,
  ``ZlibF.Spec.Public.Goal.inflate_sequence_safety,
  ``ZlibF.Spec.Public.Goal.deflate_sequence_safety,
  ``ZlibF.Spec.Public.Goal.inflate_back_sequence_safety,
  ``ZlibF.Spec.Public.Goal.inflate_refusal,
  ``ZlibF.Spec.Public.Goal.deflate_refusal,
  ``ZlibF.Spec.Public.Goal.gz_sequence_safety,
  ``ZlibF.Spec.Public.Goal.gz_refusal,
  ``ZlibF.Spec.Public.Goal.gzvprintf_safety,
  ``ZlibF.Spec.Public.Goal.inflate_initialisation_domain,
  ``ZlibF.Spec.Public.Goal.deflate_initialisation_domain,
  ``ZlibF.Spec.Public.Goal.inflate_back_initialisation_domain,
  ``ZlibF.Spec.Public.Goal.inflateBack_call_domain,
  ``ZlibF.Spec.Public.Goal.gz_sequence_nonvacuity
]

/-- Restrict registry discovery to the safety specifications (`ZlibF.Spec.Safety.*`) and the two
pure bound queries (`compressBound`, `compressBound_z`) that serve as their own safety goals. -/
def inSafetyScope (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    let m := env.header.moduleNames[i]!
    (`ZlibF.Spec.Safety).isPrefixOf m ||
      goalHead n == some ``ZlibF.Spec.Public.Goal.compressBound ||
      goalHead n == some ``ZlibF.Spec.Public.Goal.compressBound_z
  | none => true

#eval checkWith proved notDone required inSafetyScope

end ZlibF.Results
