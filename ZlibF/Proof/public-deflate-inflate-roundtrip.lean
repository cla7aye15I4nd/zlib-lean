import ZlibF.Proof.«deflate.c.generic-observed-decoding»
import ZlibF.Spec.Functional.Sequences
import ZlibF.Proof.«inflate.c.meaning-zlib»
import ZlibF.Proof.«inflate.c.default-success-decoding»

/-! Direct default zlib stream round trip, using actual execution traces.
It is restricted to completed fresh epochs. Completion with sufficient buffers remains separate. -/

namespace ZlibF.Spec.Public.Proofs.DirectRoundtrip
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- A fresh default inflate epoch with legal buffer edits and actual calls.
There are no dictionary, reset or advanced-operation constructors. -/
inductive InflateTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Inflate.inflateInit2_ (some r) 15 version 112) h = .ok (Z_OK, after) →
      InflateTrace r after {}
  | caller {h after log} : InflateTrace r h log → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → InflateTrace r after log
  | step {h after log flush rc input output used} : InflateTrace r h log →
      ZlibF.PlatformMemory.ByteObjectsFit h →
      DataStep .inflate h after r flush rc input output used →
      InflateTrace r after
        { log with input := log.input ++ input.take used
                   output := log.output ++ output
                   result := rc
                   finished := log.finished || rc == Z_STREAM_END }

theorem InflateTrace.dictionary_empty {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : InflateTrace r h log) :
    log.dictionary = [] ∧ log.singleDictionary = true := by
  induction trace with
  | init => exact ⟨rfl, rfl⟩
  | caller _ _ _ ih => exact ih
  | step _ _ _ ih => exact ih

theorem InflateTrace.protocol {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : InflateTrace r h log) :
    ∃ pending, InflateProtocolTrace 15 r h log pending := by
  induction trace with
  | init domain actual => exact ⟨false, .init domain actual⟩
  | caller _ edit platform ih =>
      obtain ⟨pending, history⟩ := ih
      exact ⟨pending, .caller history edit platform⟩
  | step _ platform actual ih =>
      obtain ⟨pending, history⟩ := ih
      exact ⟨_, .step history platform actual⟩

/-- The decoder side of the round trip: a completed zlib epoch decodes its consumed input to its
output. From `ParseMeaning` after the history (`meaning_zlib`) and the completed-meaning
decoding. -/
theorem completed_inflate_decodes
    {r : ZStreamRef} {h : Heap} {log : DataLog}
    (trace : InflateTrace r h log) (ended : log.result = Z_STREAM_END) :
    Zlib.Decodes [] log.input log.output := by
  obtain ⟨pending, history⟩ := trace.protocol
  have zlib : Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) := by decide
  obtain ⟨meaning, _⟩ := Zlib.Inflate.Proofs.meaning_zlib zlib history
  obtain ⟨empty, single⟩ := trace.dictionary_empty
  exact Zlib.Inflate.Proofs.default_completed_meaning_decodes meaning empty single ended

/-- Completed direct default zlib epochs round-trip when the decoder input
is the consumed prefix of the emitted encoder bytes. Arbitrary chunking is
recorded by actual caller edits and data steps. -/
theorem deflate_inflate_roundtrip
    {rd ri : ZStreamRef} {hd hi : Heap} {encoded decoded : DataLog}
    (encoder : GenericDefaultDataTrace rd hd encoded)
    (decoder : InflateTrace ri hi decoded)
    (encoderEnded : encoded.result = Z_STREAM_END)
    (decoderEnded : decoded.result = Z_STREAM_END)
    (sameBytes : ∃ trailing, encoded.output = decoded.input ++ trailing) :
    decoded.output = encoded.input := by
  have source := encoder.exact_decodes encoderEnded
  have output := completed_inflate_decodes decoder decoderEnded
  obtain ⟨trailing, bytes⟩ := sameBytes
  rw [bytes] at source
  exact (Zlib.ext output source).2

#print axioms deflate_inflate_roundtrip

end ZlibF.Spec.Public.Proofs.DirectRoundtrip
