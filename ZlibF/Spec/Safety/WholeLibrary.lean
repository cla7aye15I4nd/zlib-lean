import ZlibF.Spec.Functional.Queries
import ZlibF.Spec.Safety.Back
import ZlibF.Spec.Safety.Checksums
import ZlibF.Spec.Safety.Copy
import ZlibF.Spec.Safety.GzCalls
import ZlibF.Spec.Safety.Initialisation
import ZlibF.Spec.Safety.Queries
import ZlibF.Spec.Safety.Sequences
import ZlibF.Spec.Safety.Streams
import ZlibF.Spec.Safety.Utilities

namespace ZlibF.Spec.Public

/-- The documented entry points of the pinned Linux library. An entry's index is its
original contract, including every caller premise and fault alternative. The two pure
compression-bound queries use their total result equations. -/
inductive PublicEntry : Prop → Type where
  | adler32 : PublicEntry Goal.adler32_safety
  | adler32_combine : PublicEntry Goal.adler32_combine_safety
  | adler32_combine64 : PublicEntry Goal.adler32_combine64_safety
  | adler32_z : PublicEntry Goal.adler32_z_safety
  | compress : PublicEntry Goal.compress_safety
  | compress2 : PublicEntry Goal.compress2_safety
  | compress2_z : PublicEntry Goal.compress2_z_safety
  | compressBound : PublicEntry Goal.compressBound
  | compressBound_z : PublicEntry Goal.compressBound_z
  | compress_z : PublicEntry Goal.compress_z_safety
  | crc32 : PublicEntry Goal.crc32_safety
  | crc32_combine : PublicEntry Goal.crc32_combine_safety
  | crc32_combine64 : PublicEntry Goal.crc32_combine64_safety
  | crc32_combine_gen : PublicEntry Goal.crc32_combine_gen_safety
  | crc32_combine_gen64 : PublicEntry Goal.crc32_combine_gen64_safety
  | crc32_combine_op : PublicEntry Goal.crc32_combine_op_safety
  | crc32_z : PublicEntry Goal.crc32_z_safety
  | deflate : PublicEntry Goal.deflate_safety
  | deflateBound : PublicEntry Goal.deflateBound_safety
  | deflateBound_z : PublicEntry Goal.deflateBound_z_safety
  | deflateCopy : PublicEntry Goal.deflateCopy_safety
  | deflateEnd : PublicEntry Goal.deflateEnd_safety
  | deflateGetDictionary : PublicEntry Goal.deflateGetDictionary_safety
  | deflateInit2_ : PublicEntry Goal.deflateInit2__safety
  | deflateInit_ : PublicEntry Goal.deflateInit__safety
  | deflateParams : PublicEntry Goal.deflateParams_safety
  | deflatePending : PublicEntry Goal.deflatePending_safety
  | deflatePrime : PublicEntry Goal.deflatePrime_safety
  | deflateReset : PublicEntry Goal.deflateReset_safety
  | deflateSetDictionary : PublicEntry Goal.deflateSetDictionary_safety
  | deflateSetHeader : PublicEntry Goal.deflateSetHeader_safety
  | deflateTune : PublicEntry Goal.deflateTune_safety
  | deflateUsed : PublicEntry Goal.deflateUsed_safety
  | gzbuffer : PublicEntry Goal.gzbuffer_safety
  | gzclearerr : PublicEntry Goal.gzclearerr_safety
  | gzclose : PublicEntry Goal.gzclose_safety
  | gzclose_r : PublicEntry Goal.gzclose_r_safety
  | gzclose_w : PublicEntry Goal.gzclose_w_safety
  | gzdirect : PublicEntry Goal.gzdirect_safety
  | gzdopen : PublicEntry Goal.gzdopen_safety
  | gzeof : PublicEntry Goal.gzeof_safety
  | gzerror : PublicEntry Goal.gzerror_safety
  | gzflush : PublicEntry Goal.gzflush_safety
  | gzfread : PublicEntry Goal.gzfread_safety
  | gzfwrite : PublicEntry Goal.gzfwrite_safety
  | gzgetc : PublicEntry Goal.gzgetc_safety
  | gzgetc_ : PublicEntry Goal.gzgetc__safety
  | gzgets : PublicEntry Goal.gzgets_safety
  | gzoffset : PublicEntry Goal.gzoffset_safety
  | gzoffset64 : PublicEntry Goal.gzoffset64_safety
  | gzopen : PublicEntry Goal.gzopen_safety
  | gzopen64 : PublicEntry Goal.gzopen64_safety
  | gzprintf : PublicEntry Goal.gzprintf_safety
  | gzputc : PublicEntry Goal.gzputc_safety
  | gzputs : PublicEntry Goal.gzputs_safety
  | gzread : PublicEntry Goal.gzread_safety
  | gzrewind : PublicEntry Goal.gzrewind_safety
  | gzseek : PublicEntry Goal.gzseek_safety
  | gzseek64 : PublicEntry Goal.gzseek64_safety
  | gzsetparams : PublicEntry Goal.gzsetparams_safety
  | gztell : PublicEntry Goal.gztell_safety
  | gztell64 : PublicEntry Goal.gztell64_safety
  | gzungetc : PublicEntry Goal.gzungetc_safety
  | gzwrite : PublicEntry Goal.gzwrite_safety
  | inflate : PublicEntry Goal.inflate_safety
  | inflateBack : PublicEntry Goal.inflateBack_safety
  | inflateBackEnd : PublicEntry Goal.inflateBackEnd_safety
  | inflateBackInit_ : PublicEntry Goal.inflateBackInit__safety
  | inflateCopy : PublicEntry Goal.inflateCopy_safety
  | inflateEnd : PublicEntry Goal.inflateEnd_safety
  | inflateGetDictionary : PublicEntry Goal.inflateGetDictionary_safety
  | inflateGetHeader : PublicEntry Goal.inflateGetHeader_safety
  | inflateInit2_ : PublicEntry Goal.inflateInit2__safety
  | inflateInit_ : PublicEntry Goal.inflateInit__safety
  | inflateMark : PublicEntry Goal.inflateMark_safety
  | inflatePrime : PublicEntry Goal.inflatePrime_safety
  | inflateReset : PublicEntry Goal.inflateReset_safety
  | inflateReset2 : PublicEntry Goal.inflateReset2_safety
  | inflateSetDictionary : PublicEntry Goal.inflateSetDictionary_safety
  | inflateSync : PublicEntry Goal.inflateSync_safety
  | uncompress : PublicEntry Goal.uncompress_safe
  | uncompress2 : PublicEntry Goal.uncompress2_safe
  | uncompress2_z : PublicEntry Goal.uncompress2_z_safe
  | uncompress_z : PublicEntry Goal.uncompress_z_safe
  | zlibCompileFlags : PublicEntry Goal.zlibCompileFlags_safety
  | zlibVersion : PublicEntry Goal.zlibVersion_safety

/-- The four supported single-stream or single-handle histories. -/
inductive StreamProtocol : Prop → Type where
  | deflate : StreamProtocol Goal.deflate_sequence_safety
  | inflate : StreamProtocol Goal.inflate_sequence_safety
  | inflateBack : StreamProtocol Goal.inflate_back_sequence_safety
  | gzip : StreamProtocol Goal.gz_sequence_safety

/-- Select a documented operation or a permitted stream protocol to recover its full
safety contract. Each protocol retains its own reachability, frame and ownership rules. -/
def Goal.whole_library_safety : Prop :=
  (∀ {contract : Prop}, PublicEntry contract → contract) ∧
  (∀ {contract : Prop}, StreamProtocol contract → contract)

end ZlibF.Spec.Public
