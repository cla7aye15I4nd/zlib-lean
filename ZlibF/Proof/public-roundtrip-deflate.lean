import ZlibF.Spec.Functional.RoundTrip
import ZlibF.Proof.«public-deflate-inflate-roundtrip»
import ZlibF.Proof.«public-roundtrip-bound»
import ZlibF.Proof.«deflate.c.engine.call-size-step-foreign»
import ZlibF.Proof.«deflate.c.engine.generic-ordinary-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-stream-end-control»
import ZlibF.Proof.«deflate.c.default-core-finish»
import ZlibF.Proof.«deflate.c.engine.default-bound-value»

/-! # Completion of the default deflate stream from the bound, and the conditional round trip

* `Goal.stream_roundtrip`: from `deflate_inflate_roundtrip`.
* `Goal.deflate_completes_default`: a `Z_FINISH` call with room for more than the rest of the
  unsaturated bound of the whole input ends. The size ledger (`clean_size_ledger`) bounds the
  output of every clean history by that bound (`output_le_bound`), and a `Z_FINISH` call that
  returns `Z_OK` has used all its room (`finish_ok_fills`).
* `Goal.deflate_bound_default`: one call from a fresh stream with `deflateBound` room ends.
  Before any output `deflateBound` is `compressBound` (`bound_value_default`), and a `Z_OK` call
  from a stream with no output stops owing output (`first_ok_output_lt`).
-/

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-! ## The conditional round trip -/

theorem history_generic {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultDeflateHistory r h log) : GenericDefaultDataTrace r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ actual ih =>
    have observed := actual
    obtain ⟨z, _, get, _⟩ := observed
    exact .step ih get actual

theorem clean_generic {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultCleanHistory r h log) : GenericDefaultDataTrace r h log :=
  history_generic history.toDefault

theorem inflate_history_trace {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultInflateHistory r h log) : DirectRoundtrip.InflateTrace r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit fit ih => exact .caller ih edit fit
  | step _ fit actual ih => exact .step ih fit actual

/-- The conditional stream round trip (`Goal.stream_roundtrip`), from `deflate_inflate_roundtrip`. -/
theorem stream_roundtrip : Goal.stream_roundtrip := by
  intro rd ri hd hi encoded decoded encoder decoder encEnd decEnd same
  exact DirectRoundtrip.deflate_inflate_roundtrip (history_generic encoder)
    (inflate_history_trace decoder) encEnd decEnd same

/-! ## Deflate completion from the bound -/

/-- The encoding state of a clean history. -/
theorem clean_encoding {r : ZStreamRef} {h : Heap} {log : DataLog} (history : DefaultCleanHistory r h log) :
    ∃ ds z d config, DefaultEncodingState h r ds z d config log.input log.output :=
  let ⟨ds, z, d, config, state, _⟩ := (clean_generic history).exact_encoding
  ⟨ds, z, d, config, state⟩

/-- **The header clause of a default history.** A default stream has no gzip header
(`DefaultFinishBoundary.no_header`), so `ActiveHeader` holds after every default history. -/
theorem default_active_header {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultDeflateHistory r h log) : ActiveHeader h r := by
  obtain ⟨_ds, _z, _d, _config, state, _⟩ := (history_generic history).exact_encoding
  exact default_finish_active_header state.protocol.good state.protocol.no_header

theorem clean_active_header {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultCleanHistory r h log) : ActiveHeader h r :=
  default_active_header history.toDefault

/-- A `Z_FINISH` call on a clean unfinished history is observed and returns `Z_OK` or
`Z_STREAM_END`. -/
theorem finish_call_outcome {r : ZStreamRef} {h : Heap} {log : DataLog} {z : ZStream}
    {input : List UInt8}
    (history : DefaultCleanHistory r h log) (_unfinished : log.finished = false)
    (get : r.get h = some z) (buffers : StreamBuffers h r) (header : ActiveHeader h r)
    (output : z.next_out ≠ .null) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (protocol : ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = [])
    (room : 0 < z.avail_out.toNat) :
    ∃ after rc out used, DataStep .deflate h after r Z_FINISH rc input out used ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END) := by
  obtain ⟨ds, z0, d, config, state⟩ := clean_encoding history
  have same : z0 = z := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
  subst same
  obtain ⟨used, rc, after, z', _result, written, run, stateA, _buffersA, account, bytes, _ended⟩ :=
    state.generic_scalar_encoding_request buffers Z_FINISH snapshot
  have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
  have accepted : d.status = FINISH_STATE → z0.avail_in = 0 := by
    intro status
    have empty := protocol ds d state.protocol.good.live.zst state.protocol.good.live.hs status
    subst empty
    have length := public_bytes_length snapshot
    exact UInt32.toNat_inj.mp (by simpa using length.symm)
  have codes : rc = Z_OK ∨ rc = Z_STREAM_END := by
    rcases caller_output_storage_cases state.protocol.good buffers with null | ⟨ob, oo, pointer⟩ |
        ⟨owner, oo, pointer⟩
    · exact absurd null output
    · obtain ⟨_u, _p, rcF, _a, _z, _r, runF, _s, _b, _acc, allowed, _e⟩ :=
        state.protocol.finish buffers pointer room valid accepted
      obtain ⟨rcs, _⟩ := Prod.mk.inj (Except.ok.inj (runF.symm.trans run))
      rw [← rcs]; exact allowed
    · obtain ⟨_u, _p, rcF, _a, _z, _r, runF, _s, _b, _acc, allowed, _e⟩ :=
        state.protocol.foreign_finish buffers pointer room valid accepted
      obtain ⟨rcs, _⟩ := Prod.mk.inj (Except.ok.inj (runF.symm.trans run))
      rw [← rcs]; exact allowed
  refine ⟨after, rc, written, used, ⟨z0, z', get, stateA.protocol.good.live.hz, buffers, header, snapshot,
    ?_, ?_, run⟩, codes⟩
  · have count := account.2.2.1
    omega
  · have count := account.2.2.2.1
    have length : z0.avail_out.toNat - z'.avail_out.toNat = written.length := by omega
    rw [length]
    exact bytes

/-- A call that returns `Z_STREAM_END` accepted all offered input. -/
theorem stream_end_consumes {r : ZStreamRef} {h after : Heap} {log : DataLog}
    {input out : List UInt8} {used : Nat} {flush : Int32}
    (history : DefaultCleanHistory r h log)
    (step : DataStep .deflate h after r flush Z_STREAM_END input out used) :
    used = input.length := by
  obtain ⟨ds, z, d, config, state⟩ := clean_encoding history
  have original := step
  obtain ⟨z0, z1, get0, get1, buffers, _header, snapshot, usedEq, _bytes, run⟩ := original
  have same : z0 = z := Option.some.inj (get0.symm.trans state.protocol.good.live.hz)
  subst same
  obtain ⟨z', result, stateA, _ended⟩ := state.generic_scalar_observed step
  have sameA : z1 = z' := Option.some.inj (get1.symm.trans stateA.protocol.good.live.hz)
  subst sameA
  obtain ⟨_finish, _status, drained, _pending, _bits⟩ :=
    state.protocol.generic_stream_end_run_control buffers run stateA.protocol.good
  have length := public_bytes_length snapshot
  rw [drained] at usedEq
  simp only [UInt32.toNat_zero, Nat.sub_zero] at usedEq
  omega

/-- **The ledger along a clean default history**, beside the encoding state. -/
theorem clean_size_ledger {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultCleanHistory r h log) :
    ∃ ds z d config, DefaultEncodingState h r ds z d config log.input log.output ∧
      SizeLedger h r ds z d config log.input log.output := by
  induction history with
  | init domain actual =>
      obtain ⟨hf, hu, hg, hv, z, hz, ha, _null⟩ := domain
      obtain ⟨zf, sf, state⟩ := observed_default_init_encoding_state hf hu hg hz ha hv actual
      exact ⟨_, zf, sf, engineConfig sf, state, state.size_ledger_init⟩
  | caller _ edit ih =>
      obtain ⟨ds, z, d, config, state, ledger⟩ := ih
      obtain ⟨zg, getG, stateG⟩ := state.rebuffer edit
      exact ⟨ds, zg, d, config, stateG, ledger.rebuffer state edit getG⟩
  | step _ clean observed ih =>
      obtain ⟨ds, oldZ, d, config, state, ledger⟩ := ih
      have original := observed
      obtain ⟨z0, _z1, get0, _get1, buffers, _rest⟩ := original
      have sameZ : oldZ = z0 := Option.some.inj (state.protocol.good.live.hz.symm.trans get0)
      subst oldZ
      obtain ⟨z', result, stateA, _ended⟩ := state.generic_scalar_observed observed
      have getA := stateA.protocol.good.live.hz
      have dA := stateA.protocol.good.live.hs
      refine ⟨ds, z', result, config, stateA, ?_⟩
      rcases caller_output_storage_cases state.protocol.good buffers with null | raw | ⟨owner, oo, pointer⟩
      · exact (ledger.step_raw state clean (Or.inl null) observed getA dA).1
      · exact (ledger.step_raw state clean (Or.inr raw) observed getA dA).1
      · exact (ledger.step_foreign state clean pointer observed getA dA).1

/-- A `Z_FINISH` call that returns `Z_OK` used all of its output room. -/
theorem finish_ok_fills {r : ZStreamRef} {h after : Heap} {log : DataLog} {z : ZStream}
    {input out : List UInt8} {used : Nat}
    (history : DefaultCleanHistory r h log) (get : r.get h = some z)
    (step : DataStep .deflate h after r Z_FINISH Z_OK input out used) :
    out.length = z.avail_out.toNat := by
  obtain ⟨_ds, z0, _d, _config, state, ledger⟩ := clean_size_ledger history
  have same : z0 = z := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
  subst same
  have original := step
  obtain ⟨z1, z', get1, getA, buffers, _header, _snapshot, _usedEq, bytes, _run⟩ := original
  have same1 : z1 = z0 := Option.some.inj (get1.symm.trans get)
  subst same1
  obtain ⟨zA, result, stateA, _ended⟩ := state.generic_scalar_observed step
  have sameA : zA = z' := Option.some.inj (stateA.protocol.good.live.hz.symm.trans getA)
  subst sameA
  have dA := stateA.protocol.good.live.hs
  have room : zA.avail_out = 0 := by
    rcases caller_output_storage_cases state.protocol.good buffers with null | raw | ⟨owner, oo, pointer⟩
    · exact (ledger.step_raw state (Or.inr rfl) (Or.inl null) step getA dA).2.1 rfl rfl
    · exact (ledger.step_raw state (Or.inr rfl) (Or.inr raw) step getA dA).2.1 rfl rfl
    · exact (ledger.step_foreign state (Or.inr rfl) pointer step getA dA).2.1 rfl rfl
  have length := public_bytes_length bytes
  rw [room] at length
  simpa using length

/-- **The bound ledger.** A clean default history has written at most the unsaturated
`compressBound` sum of the input it accepted. Equality is reachable. -/
theorem output_le_bound {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultCleanHistory r h log) :
    log.output.length ≤ unsaturatedBound log.input.length := by
  obtain ⟨_ds, _z, _d, _config, state, ledger⟩ := clean_size_ledger history
  have le := ledger.output_le state
  have budget := ZlibF.Math.DeflateBound.counted_blocks_to_default_bound log.input.length
  unfold unsaturatedBound
  omega

/-- **The strict ledger for the first output.** A `Z_FINISH` call after a clean history with no
output yet that returns `Z_OK` has written fewer bytes than the bound of what it accepted: no
pending output is delivered at its entry, so it stops with output still owed (pending bytes, the
final block or the trailer). -/
theorem first_ok_output_lt {r : ZStreamRef} {h after : Heap} {log : DataLog}
    {input out : List UInt8} {used : Nat}
    (history : DefaultCleanHistory r h log) (empty : log.output = [])
    (step : DataStep .deflate h after r Z_FINISH Z_OK input out used) :
    out.length < unsaturatedBound (log.input.length + (input.take used).length) := by
  obtain ⟨_ds, z, _d, _config, state, ledger⟩ := clean_size_ledger history
  rw [empty] at state ledger
  have original := step
  obtain ⟨z0, _z1, get0, _get1, buffers, _rest⟩ := original
  have sameZ : z = z0 := Option.some.inj (state.protocol.good.live.hz.symm.trans get0)
  subst sameZ
  have bound : out.length + 1 ≤ (log.input ++ input.take used).length + 11 +
      5 * ((log.input ++ input.take used).length / 16383) := by
    rcases caller_output_storage_cases state.protocol.good buffers with null | raw | ⟨owner, oo, pointer⟩
    · exact first_ok_raw state ledger (Or.inl null) step
    · exact first_ok_raw state ledger (Or.inr raw) step
    · exact first_ok_foreign state ledger pointer step
  have budget := ZlibF.Math.DeflateBound.counted_blocks_to_default_bound
    (log.input.length + (input.take used).length)
  simp only [List.length_append] at bound
  unfold unsaturatedBound
  omega

theorem unsaturatedBound_mono {a b : Nat} (le : a ≤ b) : unsaturatedBound a ≤ unsaturatedBound b := by
  unfold unsaturatedBound
  have h1 : a / 4096 ≤ b / 4096 := Nat.div_le_div_right le
  have h2 : a / 16384 ≤ b / 16384 := Nat.div_le_div_right le
  have h3 : a / 33554432 ≤ b / 33554432 := Nat.div_le_div_right le
  omega

/-- A `Z_FINISH` call that cannot return `Z_OK` ends the stream. -/
theorem finish_completes_of {r : ZStreamRef} {h : Heap} {log : DataLog} {z : ZStream}
    {input : List UInt8}
    (history : DefaultCleanHistory r h log) (unfinished : log.finished = false)
    (get : r.get h = some z) (buffers : StreamBuffers h r) (header : ActiveHeader h r)
    (output : z.next_out ≠ .null) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (protocol : ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = [])
    (room : 0 < z.avail_out.toNat)
    (short : ∀ after out used, DataStep .deflate h after r Z_FINISH Z_OK input out used →
      out.length < z.avail_out.toNat) :
    ∃ after output, DataStep .deflate h after r Z_FINISH Z_STREAM_END input output input.length ∧
      Zlib.Decodes [] (log.output ++ output) (log.input ++ input) := by
  obtain ⟨after, rc, out, used, step, outcome⟩ :=
    finish_call_outcome history unfinished get buffers header output snapshot protocol room
  have next : DefaultCleanHistory r after (deflateLogStep log Z_FINISH rc input out used) :=
    .step history (Or.inr rfl) step
  rcases outcome with ok | ended
  · subst ok
    exfalso
    have fills := finish_ok_fills history get step
    have lt := short after out used step
    omega
  · subst ended
    have all := stream_end_consumes history step
    subst all
    refine ⟨after, out, step, ?_⟩
    have decodes := (clean_generic next).exact_decodes (by simp [deflateLogStep])
    simpa [deflateLogStep, List.take_length] using decodes

/-- After a clean default history, a `Z_FINISH` call with room for more than the rest of the bound ends the stream (`Goal.deflate_completes_default`). -/
theorem deflate_completes_default : Goal.deflate_completes_default := by
  intro r h log z input history unfinished get buffers output snapshot protocol room enough
  have header := clean_active_header history
  refine finish_completes_of history unfinished get buffers header output snapshot protocol room ?_
  intro after out used step
  have next : DefaultCleanHistory r after (deflateLogStep log Z_FINISH Z_OK input out used) :=
    .step history (Or.inr rfl) step
  have le := output_le_bound next
  have taken : (input.take used).length ≤ input.length := List.length_take_le' _ _
  have mono := unsaturatedBound_mono (a := log.input.length + (input.take used).length)
    (b := log.input.length + input.length) (by omega)
  simp only [deflateLogStep, List.length_append] at le
  omega

/-- Before any output, `deflateBound(strm, n)` is `compressBound(n)`. -/
theorem bound_value_default {r : ZStreamRef} {h : Heap} {log : DataLog} {n b : UInt64}
    (history : DefaultCleanHistory r h log) (empty : log.output = [])
    (bound : C.run (Zlib.Deflate.deflateBound (some r) n) h = .ok (b, h)) :
    b.toNat = Api.compressBound n.toNat := by
  obtain ⟨_ds, _z, _d, _config, state⟩ := clean_encoding history
  rw [empty] at state
  rcases state.phase with ⟨_, _, _, start, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, _, _, _, impossible, _⟩ |
      ⟨_, impossible, _⟩
  · exact default_initial_bound_value start bound
  · cases impossible
  · simp at impossible
  · simp at impossible

/-- Before any output, the status is not `FINISH_STATE`. -/
theorem no_output_not_finishing {r : ZStreamRef} {h : Heap} {log : DataLog} {z : ZStream}
    (history : DefaultCleanHistory r h log) (empty : log.output = []) (get : r.get h = some z) :
    ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d → d.status ≠ FINISH_STATE := by
  intro ds d kind live
  obtain ⟨ds0, z0, d0, config, state⟩ := clean_encoding history
  have same : z0 = z := Option.some.inj (state.protocol.good.live.hz.symm.trans get)
  subst same
  have ids : ds0 = ds := by
    simpa only [state.protocol.good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using kind
  subst ids
  have states : d0 = d := Option.some.inj (state.protocol.good.live.hs.symm.trans live)
  subst states
  rw [empty] at state
  rcases state.phase with ⟨_, _, _, start, _⟩ | ⟨_, impossible, _⟩ | ⟨_, _, _, _, _, impossible, _⟩ |
      ⟨_, impossible, _⟩
  · rw [start.status]; decide
  · cases impossible
  · simp at impossible
  · simp at impossible

theorem unsaturatedBound_pos (n : Nat) : 0 < unsaturatedBound n := by
  unfold unsaturatedBound
  omega

/-- A `compressBound` value that fits the room is the unsaturated sum. -/
theorem unsaturated_le_of_compressBound_le {n room : Nat} (fits : room < 4294967296)
    (le : Api.compressBound n ≤ room) : unsaturatedBound n ≤ room := by
  by_cases small : unsaturatedBound n < 18446744073709551616
  · rw [compressBound_eq_unsaturated n small] at le
    exact le
  · have unfolded : Api.compressBound n =
        if unsaturatedBound n ≥ 18446744073709551616 then 18446744073709551615 else unsaturatedBound n := by
      unfold Api.compressBound unsaturatedBound
      rfl
    rw [unfolded, ite_eq_left (by omega : unsaturatedBound n ≥ 18446744073709551616)] at le
    omega

/-- One `deflate(Z_FINISH)` call from a fresh default stream with `deflateBound` room ends the stream (`Goal.deflate_bound_default`). -/
theorem deflate_bound_default : Goal.deflate_bound_default := by
  intro r h log z input n b history noInput noOutput unfinished bound get buffers output
    snapshot length room
  have header := clean_active_header history
  have value := bound_value_default history noOutput bound
  have protocol : ∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = [] := by
    intro ds d zs hs status
    exact absurd status (no_output_not_finishing history noOutput get ds d zs hs)
  have fits := unsaturated_le_of_compressBound_le (UInt32.toNat_lt z.avail_out) (value ▸ room)
  have positive : 0 < z.avail_out.toNat := by
    have := unsaturatedBound_pos n.toNat
    omega
  obtain ⟨after, out, step, decodes⟩ :=
    finish_completes_of history unfinished get buffers header output snapshot protocol positive (by
      intro after out used step
      have lt := first_ok_output_lt history noOutput step
      have taken : (input.take used).length ≤ input.length := List.length_take_le' _ _
      have mono := unsaturatedBound_mono (a := log.input.length + (input.take used).length)
        (b := n.toNat) (by rw [noInput, ← length]; simp only [List.length_nil, Nat.zero_add]; exact taken)
      omega)
  refine ⟨after, out, step, ?_⟩
  simpa [noInput, noOutput] using decodes

end ZlibF.Spec.Public.Proofs.RoundTrip
