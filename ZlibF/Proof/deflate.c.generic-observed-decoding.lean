import ZlibF.Proof.«deflate.c.engine.generic-default-data-trace»
import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual observed default histories retain encoding of the same byte log,
for every caller output representation admitted by DataStep. -/
theorem GenericDefaultDataTrace.exact_encoding {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) :
    ∃ ds z d config, DefaultEncodingState h r ds z d config log.input log.output ∧
      (log.result = Z_STREAM_END → ZlibF.Spec.Zlib.Valid log.input log.output) := by
  induction history with
  | init domain actual =>
      obtain ⟨hf, hu, hg, hv, z, hz, ha, _null⟩ := domain
      obtain ⟨zf, sf, state⟩ := observed_default_init_encoding_state hf hu hg hz ha hv actual
      refine ⟨_, zf, sf, engineConfig sf, state, ?_⟩
      intro impossible
      exact False.elim ((by decide : Z_OK ≠ Z_STREAM_END) impossible)
  | caller _ edit ih =>
      obtain ⟨ds, z, d, config, state, ended⟩ := ih
      obtain ⟨zg, _getG, stateG⟩ := state.rebuffer edit
      exact ⟨ds, zg, d, config, stateG, ended⟩
  | step _ getZ observed ih =>
      obtain ⟨ds, oldZ, d, config, state, _previousEnd⟩ := ih
      have sameZ : oldZ = _ := Option.some.inj (state.protocol.good.live.hz.symm.trans getZ)
      subst oldZ
      obtain ⟨z', result, stateA, endedA⟩ := state.generic_scalar_observed observed
      exact ⟨ds, z', result, config, stateA, endedA⟩

/-- A completed actual observed default trace decodes to its exact input log. -/
theorem GenericDefaultDataTrace.exact_decodes {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) (ended : log.result = Z_STREAM_END) :
    ZlibF.Spec.Zlib.Decodes [] log.output log.input := by
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := history.exact_encoding
  exact valid ended

end Zlib.Deflate.Engine.Proofs
