import ZlibF.Proof.«inflate.c.meaning-format»
import ZlibF.Proof.«public-inflate»
import ZlibF.Proof.«inflate.c.meaning-leave»
import ZlibF.Spec.Functional.Api.InflateAccepted

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- With no installed dictionary, the configured-window acceptance relation
coincides with independent zlib decoding for every configured window. -/
theorem no_dictionary_accepted_decodes {bits : Nat} {source output : List UInt8}
    (accepted : Api.Layer.InflateAccepted .zlib bits [] source output) :
    Zlib.Decodes [] source output := by
  have decoded : Zlib.DecodesWithWindow bits [] source output := accepted.1
  simpa [Zlib.DecodesWithWindow, Zlib.Decodes] using decoded

/-- A completed default decoder format state supplies exactly the successful
stream-decoding fact needed by the whole-buffer utility. This lemma does not
establish that actual calls preserve ParseMeaning. -/
theorem default_completed_meaning_decodes
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (meaning : ParseMeaning 15 r h log pending)
    (dictionary : log.dictionary = []) (single : log.singleDictionary = true)
    (ended : log.result = Z_STREAM_END) :
    Zlib.Decodes [] log.input log.output := by
  have accepted := meaning_accepted
    (wrap := Api.Wrap.zlib) (bits := 15) (by decide +kernel) meaning single ended
  rw [dictionary] at accepted
  exact no_dictionary_accepted_decodes accepted

/-- A successful inf_leave result with its proved format relation and DONE
state decodes the exact consumed input to the exact accumulated output.
The actual-call loop must still establish LeaveMeaning and DONE. -/
theorem successful_leave_decodes
    {c : Ctx} {f : LoopFrame} {r : ZStreamRef} {l : IL} {ret : Int32}
    {after : Heap}
    (leave : LeaveMeaning c f r l ret Z_STREAM_END after)
    (wrap : f.wrap = Api.Wrap.zlib) (dictionary : f.dict = [])
    (done : ∀ zs state, c.st = some (.tab zs) →
      after.istates zs = some state → state.mode = DONE) :
    ∃ callOut, Bytes after f.start callOut.length callOut ∧
      Zlib.Decodes [] (f.logIn ++ f.inp.take (loopRead l)) (f.logOut ++ callOut) := by
  obtain ⟨zs, state, finalState, stream, callOut, consumed, held, stage,
    _st, hs, _get, _nextIn, _availIn, _nextOut, _availOut, _inLe, _inLen,
    _put, bytes, inputBits, parsed, outputEq, _config, _dictionary,
    heldBits, exit⟩ := leave
  rcases exit with ⟨impossible, _⟩ | ⟨_code, _mode, stageMatch, wrapper⟩
  · exact False.elim ((by decide : Z_STREAM_END ≠ Z_MEM_ERROR) impossible)
  · obtain ⟨output, stageEq⟩ := stage_done_of_mode stageMatch (done zs finalState _st hs)
    subst stage
    have empty := held_empty_of_done wrapper heldBits
    subst held
    have accepted := wrapParsed_accepted parsed (by simpa using inputBits)
    rw [wrap, dictionary] at accepted
    have decoded := no_dictionary_accepted_decodes accepted
    refine ⟨callOut, bytes, ?_⟩
    rw [← outputEq]
    exact decoded

/-- The actual successful inflate run establishes DONE for its returned
decoder. This invokes the proved public call theorem, not a caller contract. -/
theorem actual_success_done
    {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {state returned : InflateState} {flush : Int32}
    (reach : StreamReachable .inflate h r)
    (good : Zlib.Inflate.Spec.Good h r i z state)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocator : Zlib.Inflate.Spec.DefAlloc z)
    (buffers : StreamBuffers h r) (header : ActiveHeader h r)
    (actual : C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after))
    (get : after.istates i = some returned) : returned.mode = DONE := by
  obtain ⟨rc, heap, stream, finalState, _used, _out, run, goodA,
    _account, _bytes, _codes, _progress, _streamError, _streamEq,
    _bufferError, _moving, ended, _rest⟩ :=
    inflate_public h r i z state flush reach good platform allocator buffers header
  have equality := Prod.mk.inj (Except.ok.inj (run.symm.trans actual))
  have codeEq : rc = Z_STREAM_END := equality.1
  have heapEq : heap = after := equality.2
  subst rc heap
  have sameState : finalState = returned :=
    Option.some.inj (goodA.live.hs.symm.trans get)
  rw [sameState] at ended
  exact ended rfl

/-- A real completed inflate call discharges the DONE premise of the
return-stage decoding bridge. LeaveMeaning remains the format obligation. -/
theorem actual_successful_leave_decodes
    {h after : Heap} {c : Ctx} {f : LoopFrame} {r : ZStreamRef}
    {i : Nat} {z : ZStream} {state : InflateState} {flush ret : Int32} {l : IL}
    (reach : StreamReachable .inflate h r)
    (good : Zlib.Inflate.Spec.Good h r i z state)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (allocator : Zlib.Inflate.Spec.DefAlloc z)
    (buffers : StreamBuffers h r) (header : ActiveHeader h r)
    (actual : C.run (inflate (some r) flush) h = .ok (Z_STREAM_END, after))
    (context : c.st = some (.tab i))
    (leave : LeaveMeaning c f r l ret Z_STREAM_END after)
    (wrap : f.wrap = Api.Wrap.zlib) (dictionary : f.dict = []) :
    ∃ callOut, Bytes after f.start callOut.length callOut ∧
      Zlib.Decodes [] (f.logIn ++ f.inp.take (loopRead l)) (f.logOut ++ callOut) := by
  apply successful_leave_decodes leave wrap dictionary
  intro zs returned tag get
  have index : zs = i := by
    have equality := context.symm.trans tag
    cases equality
    rfl
  subst zs
  exact actual_success_done reach good platform allocator buffers header actual get

#print axioms actual_success_done
#print axioms actual_successful_leave_decodes

end Zlib.Inflate.Proofs
