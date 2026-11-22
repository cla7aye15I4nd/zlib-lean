import ZlibF.Proof.«deflate.c.universal-call-header-fact»
import ZlibF.Proof.«deflate.c.universal-deflate-proof»
import ZlibF.Spec.Functional.Streams
import ZlibF.Spec.Safety.Sequences

/-!
# `Goal.deflate` and `Goal.deflate_sequence_safety` under `TinyOverlay`

Every field of `SequenceFacts` is a theorem under `TinyOverlay` (`sequence_facts_of`), so the two
deflate goals hold under that one hypothesis. `TinyOverlay` is the dynamic-block room of
`memLevel` 1 and 2 (`lit_bufsize < 512`); it is proved by `tinyOverlay`
(`deflate.c.engine.overlay-header-ref`). The goals themselves, as theorems of exactly their type,
are `deflate_safety` and `deflate_sequence_safety` (`public-deflate-goals`).
-/

namespace Zlib.Deflate.Universal
open ZlibF.Spec.Public
set_option autoImplicit false

/-- **`Goal.deflate`** under `TinyOverlay` (`memLevel` 1 and 2; proved by `tinyOverlay`). -/
theorem deflate_safety_of_tiny (tiny : Block.TinyOverlay) : Goal.deflate :=
  deflate_proof_of (Call.sequence_facts_of tiny)

/-- **`Goal.deflate_sequence_safety`** under `TinyOverlay` (`memLevel` 1 and 2; proved by
`tinyOverlay`). -/
theorem deflate_sequence_safety_of_tiny (tiny : Block.TinyOverlay) : Goal.deflate_sequence_safety :=
  deflate_sequence_safety_of (Call.sequence_facts_of tiny)

end Zlib.Deflate.Universal
