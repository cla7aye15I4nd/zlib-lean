import ZlibF.Proof.«public-inflate-sequence-safety»
import ZlibF.Proof.«public-deflate-goals»
import ZlibF.Proof.«public-stream-refusal»
import ZlibF.Proof.«public-inflate-prime»
import ZlibF.Proof.«public-inflate-mark»
import ZlibF.Proof.«inflate.c.sync2»
import ZlibF.Proof.«inflate.c.hdr»
import ZlibF.Proof.«deflate.c.life.end»
import ZlibF.Proof.«deflate.c.life.reset»
import ZlibF.Proof.«deflate.c.prime»
import ZlibF.Proof.«deflate.c.life.bound»
import ZlibF.Spec.Safety.Streams

/-!
# Per-function safety of the inflate and deflate functions

Each theorem proves one goal of `ZlibF/Spec/Safety/Streams.lean` as a corollary of the sequence
safety theorems `Zlib.Inflate.Proofs.inflate_sequence_safety_public` (clauses 2 and 3 of
`StreamSequenceSafety .inflate`) and `Zlib.Deflate.Universal.deflate_sequence_safety`. The refusal
clause of each goal is a corollary of a theorem: `Goal.inflate_refusal`,
`Goal.deflate_refusal`, the `CheckedInflate`/`CheckedDeflate` clause of the function's own goal, or
the function's refusal lemma (`inflateSync_check`, `inflateGetHeader_check`, `deflateEnd_reject`,
`deflateReset_reject`, `deflatePrime_refused`, `deflateBound_nostate`, `deflateBound_z_nostate`),
with `refused_dom` and `refused_not_initialised` (and their deflate forms) for the lemmas stated on
`StreamDom`.
-/

namespace ZlibF.Spec.Public.StreamCallSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

/-- `inflateSync` refuses a refused stream: it makes and frees its local array, so the heap ends with
no live change and a frame of nothing; from `inflateSync_check`, as for `inflate` in
`Goal.inflate_refusal`. -/
theorem inflateSync_refused (h : Heap) (p : ZStreamPtr) (fresh : Fresh h) (hr : RefusedInflate h p) :
    ∃ after, C.run (Zlib.Inflate.inflateSync p) h = .ok (Z_STREAM_ERROR, after) ∧
      Frame h after (fun _ => False) ∧ LiveChange h after (fun _ => False) (fun _ => False) := by
  refine ⟨Zlib.Inflate.Spec.tmpFreed h,
    Zlib.Inflate.Proofs.inflateSync_check fresh (ZlibF.Spec.Public.InflateQueryProof.refused_dom hr) (ZlibF.Spec.Public.InflateQueryProof.refused_not_initialised hr), ?_, ?_⟩
  · have frame := (Zlib.Inflate.Proofs.tmp_freed_buffer_frame fresh (fun _ => False) []).1
    simpa [ZlibF.Spec.Public.restoreRegions] using frame
  · intro b
    have := (Zlib.Inflate.Proofs.sync_tmp_freed_shape fresh).live b
    simp only [and_true, or_false, not_false_eq_true]
    exact this

/-- `deflateBound` (and `deflateBound_z`) on a refused stream returns the value it returns on a `NULL`
stream and changes nothing; from `deflateBound_nostate`. -/
theorem deflateBound_refused (h : Heap) (p : ZStreamPtr) (n : UInt64) (hr : RefusedDeflate h p) :
    ∃ v, C.run (Zlib.Deflate.deflateBound p n) h = .ok (v, h) ∧
      C.run (Zlib.Deflate.deflateBound none n) h = .ok (v, h) :=
  have hn : RefusedDeflate h none := Or.inl rfl
  ⟨_, Zlib.Deflate.Proofs.deflateBound_nostate (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_dom hr) (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_not_init hr) n,
    Zlib.Deflate.Proofs.deflateBound_nostate (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_dom hn)
      (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_not_init hn) n⟩

theorem deflateBound_z_refused (h : Heap) (p : ZStreamPtr) (n : UInt64) (hr : RefusedDeflate h p) :
    ∃ v, C.run (Zlib.Deflate.deflateBound_z p n) h = .ok (v, h) ∧
      C.run (Zlib.Deflate.deflateBound_z none n) h = .ok (v, h) :=
  have hn : RefusedDeflate h none := Or.inl rfl
  ⟨_, Zlib.Deflate.Proofs.deflateBound_z_nostate (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_dom hr) (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_not_init hr) n,
    Zlib.Deflate.Proofs.deflateBound_z_nostate (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_dom hn)
      (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_not_init hn) n⟩

/-- `Goal.inflate_safety`: one call of `inflate` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflate_safety : Goal.inflate_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.inflate_refusal.1,
   fun h r _flush d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateSetDictionary_safety`: one call of `inflateSetDictionary` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateSetDictionary_safety : Goal.inflateSetDictionary_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.inflate_refusal.2.2.2.2.2.1,
   fun h r _dictionary _dictLength d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateGetDictionary_safety`: one call of `inflateGetDictionary` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateGetDictionary_safety : Goal.inflateGetDictionary_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.inflate_refusal.2.2.2.2.1,
   fun h r _dictionary _dictLength d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateSync_safety`: one call of `inflateSync` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateSync_safety : Goal.inflateSync_safety :=
  ⟨inflateSync_refused,
   fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateReset_safety`: one call of `inflateReset` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateReset_safety : Goal.inflateReset_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.inflate_refusal.2.2.1,
   fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateReset2_safety`: one call of `inflateReset2` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateReset2_safety : Goal.inflateReset2_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.inflate_refusal.2.2.2.1,
   fun h r _windowBits d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflatePrime_safety`: one call of `inflatePrime` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflatePrime_safety : Goal.inflatePrime_safety :=
  ⟨fun h p bits value hr => (ZlibF.Spec.Public.InflatePrimeProof.prime_public bits value).1 h p hr,
   fun h r _bits _value d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateMark_safety`: one call of `inflateMark` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateMark_safety : Goal.inflateMark_safety :=
  ⟨ZlibF.Spec.Public.InflateMarkProof.mark_public.1,
   fun h r d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateGetHeader_safety`: one call of `inflateGetHeader` on a stream that holds the inflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Inflate.Proofs.inflate_sequence_safety_public` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateGetHeader_safety : Goal.inflateGetHeader_safety :=
  ⟨fun _h _p head hr => Zlib.Inflate.Proofs.inflateGetHeader_check head
    (ZlibF.Spec.Public.InflateQueryProof.refused_dom hr) (ZlibF.Spec.Public.InflateQueryProof.refused_not_initialised hr),
   fun h r _head d => Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflate_safety`: one call of `deflate` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflate_safety : Goal.deflate_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal.1,
   fun h r _flush d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateSetDictionary_safety`: one call of `deflateSetDictionary` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateSetDictionary_safety : Goal.deflateSetDictionary_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal.2.1,
   fun h r _dictionary _dictLength d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateGetDictionary_safety`: one call of `deflateGetDictionary` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateGetDictionary_safety : Goal.deflateGetDictionary_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal.2.2.2.1,
   fun h r _dictionary _hasDictLength d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateReset_safety`: one call of `deflateReset` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateReset_safety : Goal.deflateReset_safety :=
  ⟨fun _h _p hr => Zlib.Deflate.Proofs.deflateReset_reject
    (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_dom hr) (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_not_init hr),
   fun h r d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateParams_safety`: one call of `deflateParams` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateParams_safety : Goal.deflateParams_safety :=
  ⟨ZlibF.Spec.Public.RefusalProof.Deflate.deflate_refusal.2.2.1,
   fun h r _level _strategy d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateTune_safety`: one call of `deflateTune` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateTune_safety : Goal.deflateTune_safety :=
  ⟨fun h p good lazy nice chain hr => (ZlibF.Spec.Public.DeflateQueryProof.tune_public good lazy nice chain).1 h p hr,
   fun h r _good_length _max_lazy _nice_length _max_chain d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateBound_safety`: one call of `deflateBound` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateBound_safety : Goal.deflateBound_safety :=
  ⟨deflateBound_refused,
   fun h r _sourceLen d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateBound_z_safety`: one call of `deflateBound_z` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateBound_z_safety : Goal.deflateBound_z_safety :=
  ⟨deflateBound_z_refused,
   fun h r _sourceLen d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflatePending_safety`: one call of `deflatePending` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflatePending_safety : Goal.deflatePending_safety :=
  ⟨fun h p pending bits hr => (ZlibF.Spec.Public.DeflateQueryProof.pending_public pending bits).1 h p hr,
   fun h r _hasPending _hasBits d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateUsed_safety`: one call of `deflateUsed` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateUsed_safety : Goal.deflateUsed_safety :=
  ⟨fun h p bits hr => (ZlibF.Spec.Public.DeflateQueryProof.used_public bits).1 h p hr,
   fun h r _hasBits d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflatePrime_safety`: one call of `deflatePrime` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflatePrime_safety : Goal.deflatePrime_safety :=
  ⟨fun _h _p bits value hr => Zlib.Deflate.Proofs.deflatePrime_refused hr bits value,
   fun h r _bits _value d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.deflateSetHeader_safety`: one call of `deflateSetHeader` on a stream that holds the deflate sequence invariant is safe and keeps it; clause 2 of `Zlib.Deflate.Universal.deflate_sequence_safety` for this call. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateSetHeader_safety : Goal.deflateSetHeader_safety :=
  ⟨fun h p head hr => (ZlibF.Spec.Public.DeflateQueryProof.header_public head).1 h p hr,
   fun h r _head d => Zlib.Deflate.Universal.deflate_sequence_safety.2.1 h r _ d.1 d.2.1 ⟨rfl, rfl⟩ d.2.2⟩

/-- `Goal.inflateEnd_safety`: `inflateEnd` is safe on a stream that holds the inflate sequence invariant; clause 3 (End) of the inflate sequence theorem. The refusal clause is a corollary of a refusal theorem. -/
theorem inflateEnd_safety : Goal.inflateEnd_safety := by
  refine ⟨ZlibF.Spec.Public.RefusalProof.inflate_refusal.2.1, ?_⟩
  intro h r hr
  obtain ⟨rc, after, z, hrun, hrc, hz, hs, hf, hl⟩ :=
    Zlib.Inflate.Proofs.inflate_sequence_safety_public.2.2 h r hr
  refine ⟨rc, after, z, hrun, ?_, hz, hs, hf, hl⟩
  rcases hrc with hrc | ⟨hk, _⟩
  · exact hrc
  · cases hk

/-- `Goal.deflateEnd_safety`: `deflateEnd` is safe on a stream that holds the deflate sequence invariant; clause 3 (End) of the deflate sequence theorem. The refusal clause is a corollary of a refusal theorem. -/
theorem deflateEnd_safety : Goal.deflateEnd_safety := by
  refine ⟨fun h p hr => Zlib.Deflate.Proofs.deflateEnd_reject
      (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_dom hr) (ZlibF.Spec.Public.DeflateQueryProof.refused_deflate_not_init hr), ?_⟩
  intro h r hr
  obtain ⟨rc, after, z, hrun, hrc, hz, hs, hf, hl⟩ :=
    Zlib.Deflate.Universal.deflate_sequence_safety.2.2 h r hr
  refine ⟨rc, after, z, hrun, ?_, hz, hs, hf, hl⟩
  rcases hrc with hrc | ⟨_, hrc⟩
  · exact Or.inl hrc
  · exact Or.inr hrc

end ZlibF.Spec.Public.StreamCallSafetyProof
