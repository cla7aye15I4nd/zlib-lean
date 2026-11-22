import ZlibF.Proof.«deflate.c.engine.fill-checksum»
import ZlibF.Proof.«deflate.c.engine.decision-checksum»
import ZlibF.Proof.«deflate.c.engine.body-counters»

/-! # Complete ordinary bodies checksum exactly their accepted caller bytes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The zero-length slice is readable at every admitted caller input. -/
theorem caller_input_zero_slice {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    Bytes h z.next_in 0 [] := by
  cases pointer : z.next_in with
  | null => exact Or.inl ⟨rfl, rfl, rfl⟩
  | ref ref io =>
    obtain ⟨array, get, bound⟩ := caller_input_array good buffers pointer
    exact Or.inr ⟨ref, io, array, rfl, get, by omega, by simp⟩

end Zlib.Deflate.Engine.Proofs
