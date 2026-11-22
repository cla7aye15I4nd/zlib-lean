import ZlibF.Proof.«public-compress-safe»
import ZlibF.Proof.«public-compress-finished»
import ZlibF.Proof.«public-deflate-safety»
import ZlibF.Spec.Functional.Streams
import ZlibF.Spec.Safety.Sequences
import ZlibF.Spec.Safety.Utilities

/-!
# The deflate goals from the overlay room of the two small buffer sizes

`TinyOverlay` holds as soon as the dynamic-block room holds for `lit_bufsize = 128` and
`lit_bufsize = 256` (`memLevel` 1 and 2): a valid state's symbol buffer has `2 ^ (memLevel + 6)`
entries (`tinyOverlay_of_two`). So `Goal.deflate`, `Goal.deflate_sequence_safety` and the four
`compress*` safety goals hold from `TinyOverlayAt 128 ∧ TinyOverlayAt 256`. Both are theorems
(`tinyOverlayAt_128`, `tinyOverlayAt_256`, `deflate.c.engine.overlay-header-ref`), and
`public-deflate-goals` applies them.
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open ZlibF.Spec.Public Zlib.Deflate.Universal
set_option autoImplicit false

/-- **`Goal.deflate`** from the room at `lit_bufsize` 128 and 256. -/
theorem deflate_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.deflate :=
  deflate_safety_of_tiny (Block.tinyOverlay_of_two t128 t256)

/-- **`Goal.deflate_sequence_safety`** from the room at `lit_bufsize` 128 and 256. -/
theorem deflate_sequence_safety_two (t128 : Block.TinyOverlayAt 128) (t256 : Block.TinyOverlayAt 256) :
    Goal.deflate_sequence_safety :=
  deflate_sequence_safety_of_tiny (Block.tinyOverlay_of_two t128 t256)

end ZlibF.Spec.Public.Proofs.Compress
