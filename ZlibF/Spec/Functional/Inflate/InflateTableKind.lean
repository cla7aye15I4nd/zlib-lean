import ZlibF.Zlib.«inftrees.c»
import ZlibF.Spec.Functional.Format.Huffman

/-!
# inftrees.c: the kind of code of each table type

`kindOf` names the code of the format model that `inflate_table` builds for `CODES`, `LENS` and `DISTS`. The lemmas
about it are in the proof modules `ZlibF/Proof/inftrees.c.*.lean`.
-/

namespace Zlib.Inftrees.Spec
open C

/-- The kind of code that `inflate_table` builds for each table type: `CODES` is the code-length code, `LENS` the
literal/length code, `DISTS` the distance code. -/
def kindOf (type : UInt32) : ZlibF.Spec.CodeKind :=
  if type = CODES then .codeLength else if type = LENS then .litLen else .dist

end Zlib.Inftrees.Spec
