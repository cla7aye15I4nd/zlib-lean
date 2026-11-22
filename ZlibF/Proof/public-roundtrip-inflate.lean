import ZlibF.Proof.«public-roundtrip-deflate»
import ZlibF.Proof.«public-inflate-completes»
import ZlibF.Proof.«inflate.c.window-public-call-history»

/-! # The default decoder on a default stream

* `default_no_dictionary_request`: a default deflate stream does not ask for a preset dictionary.
* `Goal.inflate_completes_default`: from `DefaultCompletes.completes`.
* `Goal.inflate_chain_ends`: from `DefaultCompletes.progress`; the rest of the stream plus the
  rest of the decoding falls by at least one at every unfinished call.
-/

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-! ## The dictionary flag -/

/-- **A default stream does not ask for a preset dictionary**: the output of every default
deflate history is empty, `[120]`, or starts with `[120, 156]`, and `156` has `FDICT` clear. -/
theorem default_no_dictionary_request {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultDeflateHistory r h log) : ¬ AsksDictionary log.output := by
  obtain ⟨_ds, _z, _d, _config, state, _ended⟩ := (history_generic history).exact_encoding
  rintro ⟨cmf, flg, tail, shape, flag⟩
  rcases state.phase with ⟨_, empty, _⟩ | ⟨_, header, _⟩ | ⟨_, _, _, _, published, outputEq, _⟩ |
      ⟨published, outputEq, _⟩
  · rw [empty] at shape; cases shape
  · rw [header] at shape; cases shape
  · rw [outputEq] at shape
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at shape
    obtain ⟨_, second, _⟩ := shape
    subst second
    exact absurd flag (by decide)
  · rw [outputEq] at shape
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at shape
    obtain ⟨_, second, _⟩ := shape
    subst second
    exact absurd flag (by decide)

/-- The encoder's output of an ended default history decodes to its input. -/
theorem ended_decodes {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultDeflateHistory r h log) (ended : log.result = Z_STREAM_END) :
    Zlib.Decodes [] log.output log.input :=
  (history_generic history).exact_decodes ended

/-- `Goal.inflate_completes_default` from `DefaultCompletes.completes`, with the dictionary
case excluded by `default_no_dictionary_request`. -/
theorem inflate_completes_default : Goal.inflate_completes_default := by
  intro rd hd encoded ri hi decoded z flush encoder ended decoder unfinished prefixIn get buffers output
    fit alloc snapshot room ordinary
  have valid := ended_decodes encoder ended
  obtain ⟨rc, after, out, used, step, outcome⟩ :=
    Zlib.Inflate.Proofs.DefaultCompletes.completes ri hi decoded encoded.output encoded.input z flush
      decoder unfinished valid prefixIn fit alloc buffers get output snapshot room ordinary
  rcases outcome with ⟨isEnd, _used, outputs⟩ | ⟨_, asks, _⟩
  · subst isEnd
    obtain ⟨z0, z1, get0, _get1, _buffers, _header, _snapshot, _usedEq, bytes, run⟩ := step
    have same : z0 = z := Option.some.inj (get0.symm.trans get)
    subst same
    refine ⟨after, run, ?_⟩
    have length := congrArg List.length outputs
    simp only [List.length_append] at length
    have outEq : out = encoded.input.drop decoded.output.length := by
      rw [← outputs]; simp
    have bytesLen := public_bytes_length bytes
    rw [outEq] at bytes
    have count : z0.avail_out.toNat - z1.avail_out.toNat = encoded.input.length - decoded.output.length := by
      rw [outEq] at bytesLen; simp at bytesLen; omega
    rw [count] at bytes
    exact bytes
  · exact absurd asks (default_no_dictionary_request encoder)

/-- Two observed inflate steps from one heap and flush are the same step. -/
theorem inflate_step_unique {h a1 a2 : Heap} {r : ZStreamRef} {flush rc1 rc2 : Int32}
    {i1 i2 o1 o2 : List UInt8} {u1 u2 : Nat}
    (one : DataStep .inflate h a1 r flush rc1 i1 o1 u1)
    (two : DataStep .inflate h a2 r flush rc2 i2 o2 u2) :
    a1 = a2 ∧ rc1 = rc2 ∧ u1 = u2 ∧ o1 = o2 := by
  obtain ⟨z1, z1', g1, g1', _, _, _, used1, bytes1, run1⟩ := one
  obtain ⟨z2, z2', g2, g2', _, _, _, used2, bytes2, run2⟩ := two
  obtain ⟨rcs, heaps⟩ := Prod.mk.inj (Except.ok.inj (run1.symm.trans run2))
  subst heaps rcs
  have s : z1 = z2 := Option.some.inj (g1.symm.trans g2)
  have s' : z1' = z2' := Option.some.inj (g1'.symm.trans g2')
  subst s s'
  exact ⟨rfl, rfl, used1.trans used2.symm,
    Zlib.Inflate.Proofs.WindowHistory.bytes_unique bytes1 bytes2⟩

/-- `Goal.inflate_chain_ends` from `DefaultCompletes.progress`: the rest of the stream plus the
rest of the decoding falls by at least one at every unfinished call. -/
theorem inflate_chain_ends : Goal.inflate_chain_ends := by
  intro rd hd encoded ri hi decoded encoder ended decoder unfinished prefixIn
  have valid := ended_decodes encoder ended
  let S := encoded.output
  let D := encoded.input
  let Φ : DataLog → Nat := fun log => (S.length - log.input.length) + (D.length - log.output.length)
  have invariant : ∀ k after final,
      DefaultInflateChain ri S D k hi decoded after final →
      DefaultInflateTrace ri after final ∧ final.input <+: S ∧
        (final.finished = false → k + Φ final ≤ Φ decoded) ∧
        (final.finished = true → final.input = S ∧ final.output = D) := by
    intro k after final chain
    induction chain with
    | refl => exact ⟨decoder, prefixIn, fun _ => by omega, fun f => by rw [unfinished] at f; cases f⟩
    | caller _ edit fit ih =>
        obtain ⟨trace, pre, bound, done⟩ := ih decoder unfinished prefixIn
        exact ⟨.caller trace edit fit, pre, bound, done⟩
    | @step k start initial h log after z flush rc input output used _ notDone fit alloc get out room
        snapshot pre nonempty ordinary observed ih =>
        obtain ⟨trace, _pre, bound, _done⟩ := ih decoder unfinished prefixIn
        have original := observed
        obtain ⟨z0, z1, g0, _g1, buffers, _header, _snap, usedEq, _bytes, _run⟩ := original
        have same : z0 = z := Option.some.inj (g0.symm.trans get)
        obtain ⟨rc', after', output', used', step', outcome⟩ :=
          Zlib.Inflate.Proofs.DefaultCompletes.progress ri h log S D input z flush trace notDone valid
            (List.IsPrefix.trans (List.prefix_append _ _) pre) fit alloc buffers get out room snapshot pre
            nonempty ordinary
        obtain ⟨heaps, rcs, useds, outputs⟩ := inflate_step_unique step' observed
        subst heaps rcs useds outputs
        have trace' : DefaultInflateTrace ri after' (inflateLogStep log rc' input output' used') :=
          .step trace fit alloc observed
        have inLen := public_bytes_length snapshot
        rcases outcome with ⟨isEnd, inputs, outputs⟩ | ⟨codes, moved, preIn, preOut⟩ | ⟨_, asks, _⟩
        · subst isEnd
          refine ⟨trace', by simp only [inflateLogStep]; rw [inputs]; exact List.prefix_refl _, fun f => ?_, fun _ => ?_⟩
          · simp [inflateLogStep] at f
          · exact ⟨inputs, outputs⟩
        · have notEnd : rc' ≠ Z_STREAM_END := by
            rcases codes with ok | ⟨buf, _⟩ <;> subst_vars <;> decide
          have finishedNew : (inflateLogStep log rc' input output' used').finished = false := by
            simp only [inflateLogStep, notDone, Bool.false_or]
            simpa using notEnd
          refine ⟨trace', preIn, fun _ => ?_, fun f => by rw [finishedNew] at f; cases f⟩
          have b := bound notDone
          have usedLe : used' ≤ input.length := by
            rw [usedEq, inLen, ← same]
            omega
          have lin := preIn.length_le
          have lout := preOut.length_le
          simp only [List.length_append, List.length_take, Nat.min_eq_left usedLe] at lin lout
          simp only [Φ, inflateLogStep, List.length_append, List.length_take, Nat.min_eq_left usedLe] at b ⊢
          rcases moved with u | o
          · omega
          · have pos : output'.length ≥ 1 := by
              cases output' with
              | nil => exact absurd rfl o
              | cons _ _ => simp
            omega
        · exact absurd asks (default_no_dictionary_request encoder)
  refine ⟨Φ decoded, fun k after final chain => ?_⟩
  obtain ⟨_, _, bound, done⟩ := invariant k after final chain
  exact ⟨fun f => by have := bound f; omega, done⟩

end ZlibF.Spec.Public.Proofs.RoundTrip
