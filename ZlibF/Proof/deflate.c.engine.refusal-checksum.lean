import ZlibF.Proof.«deflate.c.engine.public-header-resume-checksum»
import ZlibF.Proof.«deflate.c.engine.public-entry-refusals»

/-! # Actual early refusals retain encoded input and checksum meaning -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Updating a stream record does not change the private pending bit view. -/
theorem pending_bits_put_stream {h : Heap} {d : DeflateState} {bits : List Bool}
    (pending : PendingBits h d bits) (r : ZStreamRef) (z' : ZStream) :
    PendingBits (r.put h z') d bits := by
  obtain ⟨bytes, data, value⟩ := pending
  refine ⟨bytes, ?_, value⟩
  rcases data with null | ⟨ref, offset, array, pointer, get, bound, slice⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref, offset, array, pointer, (byte_get_stream_put h r z' ref).trans get, bound, slice⟩

/-- A stream-only message store retains the raw encoded prefix. -/
theorem RawPrefix.put_stream {h : Heap} {d : DeflateState} {input : Nat → UInt8}
    {base : Nat} {published : List UInt8} (encoding : RawPrefix h d input base published)
    (r : ZStreamRef) (z' : ZStream) : RawPrefix (r.put h z') d input base published := by
  obtain ⟨remaining, encoded, pending, wire, meaning⟩ := encoding
  exact ⟨remaining, encoded, pending_bits_put_stream pending r z', wire, meaning⟩

/-- A stream-only message store retains pending initial header bytes. -/
theorem HeaderPending.put_stream {h : Heap} {d : DeflateState} {published : List UInt8}
    (encoding : HeaderPending h d published) (r : ZStreamRef) (z' : ZStream) :
    HeaderPending (r.put h z') d published := by
  obtain ⟨remaining, pending, wire, bits, start, look⟩ := encoding
  exact ⟨remaining, pending_bits_put_stream pending r z', wire, bits, start, look⟩

/-- A stream-only scalar store with the same checksum preserves the
source-established initial engine state, including its hash frontier. -/
theorem EngineStart.put_stream {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d : DeflateState} (initial : EngineStart h r ds z d)
    (goodA : DGood (r.put h z') r ds z' d) (adler : z'.adler = z.adler) :
    EngineStart (r.put h z') r ds z' d := by
  have chains : HeapChains (r.put h z') d 0 := control_heap_chains initial.chains (fun _ _ => by simp only [ZStreamRef.put_bytes])
    (by simp only [ZStreamRef.put_words]) rfl
  exact { initial with good := goodA, chains := chains, adler := adler.trans initial.adler }

/-- Every admitted caller output has the exact zero-length slice. -/
theorem caller_output_zero_slice {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    Bytes h z.next_out 0 [] := by
  obtain ⟨other, get, _input, output, _separate⟩ := buffers
  have same : other = z := Option.some.inj (get.symm.trans good.live.hz)
  subst other
  rcases output with null | ⟨⟨bytes, data⟩, _writable, _outside⟩
  · exact Or.inl ⟨null, rfl, rfl⟩
  · rcases data with null | ⟨ref, offset, array, pointer, get, bound, _slice⟩
    · exact Or.inl ⟨null.1, rfl, rfl⟩
    · exact Or.inr ⟨ref, offset, array, pointer, get, by omega, by simp⟩

end Zlib.Deflate.Engine.Proofs
