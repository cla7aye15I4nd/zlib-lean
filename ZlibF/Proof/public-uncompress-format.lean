import ZlibF.Proof.«inflate.c.completes-meaning»
import ZlibF.Proof.«inflate.c.meaning-held-within»
import ZlibF.Spec.Functional.Streams
import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.«inflate.c.meaning-init»
import ZlibF.Proof.Format.Huffman
import ZlibF.Proof.Format.Api
import ZlibF.Proof.Api.InflateCausality
import ZlibF.Proof.«inflate.c.completes-stops»
import ZlibF.Proof.«inflate.c.completes-blocked»
import ZlibF.Proof.«inflate.c.completes-gzip-fields»
import ZlibF.Proof.Api.Examples
import ZlibF.Spec.Functional.Sequences
import ZlibF.Spec.Functional.Utilities

/-!
# uncompr.c: the data relation from the last decoder call

After the call loop of `uncompress2_z`, the actual history of its local stream
is a protocol history with window bits 15 and no dictionary. From the decoder
facts and the last call, the returned code, the output and the consumed source
satisfy `Api.Uncompress2`.
-/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The return code of `uncompress2_z` from the last `inflate` result and the
unused source length (`len` after the loop). -/
def finalCode (err : Int32) (rest : UInt64) : Int32 :=
  if err == Z_STREAM_END then Z_OK
  else if err == Z_NEED_DICT then Z_DATA_ERROR
  else if err == Z_BUF_ERROR && rest == 0 then Z_DATA_ERROR
  else err

theorem zlib_decodes_long {d s o : List UInt8} (h : Zlib.Decodes d s o) : 2 ≤ s.length := by
  obtain ⟨cmf, flg, pre, rest, rfl, -⟩ := h
  simp

end ZlibF.Spec.Public.Proofs.Uncompress
