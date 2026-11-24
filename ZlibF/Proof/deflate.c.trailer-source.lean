import ZlibF.Proof.ControlFlowFrame
import ZlibF.Proof.«trees.c.monad»
import ZlibF.Zlib.«deflate.c»

/-! # Stream reads while writing the deflate header and trailer -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate

private abbrev PreservesStream (r : ZStreamRef) (op : M α) : Prop :=
  Preserves (fun h after => r.get after = r.get h) op

private theorem preserve_bind {r : ZStreamRef} {op : M α} {next : α → M β}
    (a : PreservesStream r op) (b : ∀ x, PreservesStream r (next x)) :
    PreservesStream r (op >>= next) :=
  Preserves.bind (R := fun h after => r.get after = r.get h) (fun x y => y.trans x) a b

private theorem preserve_ld (r : ZStreamRef) (s : DeflateStatePtr) :
    PreservesStream r (ldDeflateState s) := by
  intro h v after run
  unfold ldDeflateState at run
  split at run <;> try contradiction
  split at run <;> cases run <;> rfl

private theorem preserve_add (r : ZStreamRef) (p : BPtr) (k : Int) :
    PreservesStream r (p.add k) := by
  intro h v after run
  unfold Ptr.add at run
  repeat' first | split at run | contradiction | (cases run; rfl)

private theorem preserve_update (r : ZStreamRef) (s : DeflateStatePtr) (v : DeflateState) :
    PreservesStream r (stDeflateState s v) := by
  intro h result after run
  cases s with
  | none => cases run
  | some d =>
    cases d with
    | tab i =>
      cases get : h.dstates i <;> simp [stDeflateState, DeflateStateRef.get,
        DeflateStateRef.isRo, get] at run
      obtain ⟨rfl, rfl⟩ := run
      rw [DeflateStateRef.put_tab get]
      cases r <;> rfl

private theorem preserve_byte (r : ZStreamRef) (p : BPtr) (v : UInt8) :
    PreservesStream r (store8 p v) := by
  have frame (h : Heap) (b : BRef) (f : Array UInt8 → Array UInt8) :
      r.get (Space.modify h b f) = r.get h := by cases b <;> cases r <;> rfl
  intro h result after run
  unfold store8 Ptr.store at run
  repeat' first | split at run | contradiction | (cases run; exact frame _ _ _)

private theorem put_byte_stream (r : ZStreamRef) (s : DeflateStatePtr) (v : UInt8) :
    PreservesStream r (put_byte s v) := by
  unfold put_byte Zlib.Trees.put_byte
  simp only [cdecl_eq, C.M_pure_bind]
  apply preserve_bind (preserve_ld r s)
  intro d
  apply preserve_bind (preserve_add r _ _)
  intro p
  apply preserve_bind (preserve_bind (preserve_ld r s) (fun _ => preserve_update r s _))
  exact fun _ => preserve_byte r p _

private theorem putShortMSB_stream (r : ZStreamRef) (s : DeflateStatePtr) (v : UInt32) :
    PreservesStream r (putShortMSB s v) :=
  preserve_bind (put_byte_stream r s _) (fun _ => put_byte_stream r s _)

private theorem reread {α β γ : Type} (strm : ZStreamPtr) (field : ZStream → α)
    (write : α → M β) (frame : ∀ r a, PreservesStream r (write a)) (k : α → β → M γ) :
    (do let a ← zrd strm field
        let b ← write a
        let a' ← zrd strm field
        k a' b) =
    (do let a ← zrd strm field
        let b ← write a
        k a b) := by
  funext h
  cases strm with
  | none => rfl
  | some r =>
    cases stream : r.get h with
    | none => simp [zrd, ldZStream, bind_app, stream]
    | some z =>
      simp only [zrd, ldZStream, bind_app, stream, pure_app]
      cases wrote : write (field z) h with
      | error e => rfl
      | ok result =>
        obtain ⟨b, after⟩ := result
        simp only
        rw [frame r _ _ _ _ wrote, stream]

/-- Reading the dictionary checksum again after its high half has been written gives the
same execution as the single read in the earlier header proof, on every model heap. -/
theorem dictionary_header_reread_eq (strm : ZStreamPtr) (s : DeflateStatePtr) :
    (do let a ← zrd strm (·.adler)
        putShortMSB s (a >>> 16).toUInt32
        let low ← zrd strm (·.adler)
        putShortMSB s (low &&& 0xffff).toUInt32 : M Unit) =
    (do let a ← zrd strm (·.adler)
        putShortMSB s (a >>> 16).toUInt32
        putShortMSB s (a &&& 0xffff).toUInt32 : M Unit) :=
  reread strm (·.adler) (fun a => putShortMSB s (a >>> 16).toUInt32)
    (fun r _ => putShortMSB_stream r s _) (fun a _ => putShortMSB s (a &&& 0xffff).toUInt32)


theorem dictionary_header_reread_then (strm : ZStreamPtr) (s : DeflateStatePtr) (tail : M α) :
    (do let a ← zrd strm (·.adler)
        putShortMSB s (a >>> 16).toUInt32
        let a ← zrd strm (·.adler)
        putShortMSB s (a &&& 0xffff).toUInt32
        tail) =
    (do let a ← zrd strm (·.adler)
        putShortMSB s (a >>> 16).toUInt32
        putShortMSB s (a &&& 0xffff).toUInt32
        tail) :=
  reread strm (·.adler) (fun a => putShortMSB s (a >>> 16).toUInt32)
    (fun r _ => putShortMSB_stream r s _) (fun a _ => do
      putShortMSB s (a &&& 0xffff).toUInt32
      tail)

/-- Writing the first gzip header CRC byte preserves the stream checksum read for the second. -/
theorem hcrc_reread_then (strm : ZStreamPtr) (s : DeflateStatePtr) (tail : M α) :
    (do let a ← zrd strm (·.adler)
        put_byte s (a &&& 0xff).toUInt8
        let a ← zrd strm (·.adler)
        put_byte s ((a >>> 8) &&& 0xff).toUInt8
        tail) =
    (do let a ← zrd strm (·.adler)
        put_byte s (a &&& 0xff).toUInt8
        put_byte s ((a >>> 8) &&& 0xff).toUInt8
        tail) :=
  reread strm (·.adler) (fun a => put_byte s (a &&& 0xff).toUInt8)
    (fun r _ => put_byte_stream r s _) (fun a _ => do
      put_byte s ((a >>> 8) &&& 0xff).toUInt8
      tail)

private theorem fourReads (strm : ZStreamPtr) (s : DeflateStatePtr) (field : ZStream → UInt64)
    (tail : M α) :
    (do let a ← zrd strm field
        put_byte s (a &&& 0xff).toUInt8
        let a ← zrd strm field
        put_byte s ((a >>> 8) &&& 0xff).toUInt8
        let a ← zrd strm field
        put_byte s ((a >>> 16) &&& 0xff).toUInt8
        let a ← zrd strm field
        put_byte s ((a >>> 24) &&& 0xff).toUInt8
        tail) =
    (do let a ← zrd strm field
        put_byte s (a &&& 0xff).toUInt8
        put_byte s ((a >>> 8) &&& 0xff).toUInt8
        put_byte s ((a >>> 16) &&& 0xff).toUInt8
        put_byte s ((a >>> 24) &&& 0xff).toUInt8
        tail) := by
  funext h
  cases strm with
  | none => rfl
  | some r =>
    cases stream : r.get h with
    | none => simp [zrd, ldZStream, bind_app, stream]
    | some z =>
      simp only [zrd, ldZStream, bind_app, pure_app, stream]
      have advance {before after : Heap} {v : UInt8} {u : Unit}
          (live : r.get before = some z) (wrote : put_byte s v before = .ok (u, after)) :
          r.get after = some z := (put_byte_stream r s v _ _ _ wrote).trans live
      cases w0 : put_byte s ((field z) &&& 0xff).toUInt8 h with
      | error e => rfl
      | ok pair =>
        obtain ⟨u, h₁⟩ := pair
        have r₁ := advance stream w0
        simp only [r₁]
        cases w1 : put_byte s (((field z) >>> 8) &&& 0xff).toUInt8 h₁ with
        | error e => rfl
        | ok pair =>
          obtain ⟨u, h₂⟩ := pair
          have r₂ := advance r₁ w1
          simp only [r₂]
          cases w2 : put_byte s (((field z) >>> 16) &&& 0xff).toUInt8 h₂ with
          | error e => rfl
          | ok pair =>
            obtain ⟨u, h₃⟩ := pair
            simp only [advance r₂ w2]

/-- The two writes with a single checksum read, as used in the trailer-buffer proof. -/
def zlibTrailer (strm : ZStreamPtr) (s : DeflateStatePtr) : M Unit := do
  let a ← zrd strm (·.adler)
  putShortMSB s (a >>> 16).toUInt32
  putShortMSB s (a &&& 0xffff).toUInt32


/-- The final source statements as used by the existing public compression proofs. -/
def publicFinishTail (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) : M Int32 := do
  -- if (flush != Z_FINISH) return Z_OK; if (s->wrap <= 0) return Z_STREAM_END;
  if flush != Z_FINISH then return Z_OK
  if (← rd s (·.wrap)) ≤ 0 then return Z_STREAM_END
  -- Write the trailer
  if (← rd s (·.wrap)) == 2 then
    let a ← zrd strm (·.adler)
    put_byte s (a &&& 0xff).toUInt8
    put_byte s ((a >>> 8) &&& 0xff).toUInt8
    put_byte s ((a >>> 16) &&& 0xff).toUInt8
    put_byte s ((a >>> 24) &&& 0xff).toUInt8
    let t ← zrd strm (·.total_in)
    put_byte s (t &&& 0xff).toUInt8
    put_byte s ((t >>> 8) &&& 0xff).toUInt8
    put_byte s ((t >>> 16) &&& 0xff).toUInt8
    put_byte s ((t >>> 24) &&& 0xff).toUInt8
  else
    zlibTrailer strm s
  flush_pending strm
  -- if (s->wrap > 0) s->wrap = -s->wrap; /* write the trailer only once! */
  let w ← rd s (·.wrap)
  if w > 0 then
    let nw ← ineg w
    wr s (fun d => { d with wrap := nw })
  -- return s->pending != 0 ? Z_OK : Z_STREAM_END;
  return if (← rd s (·.pending)) != 0 then Z_OK else Z_STREAM_END


set_option maxHeartbeats 3000000 in
/-- The emitted trailer and the earlier safety-proof cut point agree on the entire result,
including faults from any of the byte stores or the final flush. -/
theorem trailerPhase_eq_publicFinishTail (strm : ZStreamPtr) (s : DeflateStatePtr) (flush : Int32) :
    Phases.trailerPhase strm s flush = publicFinishTail strm s flush := by
  unfold Phases.trailerPhase publicFinishTail zlibTrailer
  simp only [C.M_bind_assoc, fourReads, dictionary_header_reread_then]

end Zlib.Deflate.Engine.Proofs
