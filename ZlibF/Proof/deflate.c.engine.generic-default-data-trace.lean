import ZlibF.Proof.«deflate.c.engine.encoding-init-observed»
import ZlibF.Proof.«deflate.c.engine.encoded-state-finish»
import ZlibF.Proof.«deflate.c.engine.encoded-state-ordinary-request»
import ZlibF.Spec.Functional.Sequences
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual default data trace admits every signed flush and every caller output
reference allowed by DataStep. Its constructors record initialization, caller edits,
actual execution and byte observations, with no invariant or callee-contract field.
Existing raw/default trace declarations are preserved. -/
inductive GenericDefaultDataTrace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h = .ok (Z_OK, after) →
      GenericDefaultDataTrace r after {}
  | caller {h after log} : GenericDefaultDataTrace r h log → Rebuffer h after r →
      GenericDefaultDataTrace r after log
  | step {h after log z flush rc input output used} : GenericDefaultDataTrace r h log →
      r.get h = some z →
      DataStep .deflate h after r flush rc input output used →
      GenericDefaultDataTrace r after
        { log with
          input := log.input ++ input.take used, output := log.output ++ output
          result := rc, finished := log.finished || rc == Z_STREAM_END
          boundEligible := log.boundEligible && flush == Z_FINISH }

/-- This default data epoch never records a dictionary. This is derived
from its actual constructors rather than supplied as an invariant. -/
theorem GenericDefaultDataTrace.dictionary_empty {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) : log.dictionary = [] ∧ log.singleDictionary = true := by
  induction history with
  | init => exact ⟨rfl, rfl⟩
  | caller _ _ ih => exact ih
  | step _ _ _ ih => exact ih

end Zlib.Deflate.Engine.Proofs
