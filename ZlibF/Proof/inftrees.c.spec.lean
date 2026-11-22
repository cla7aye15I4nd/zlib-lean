import ZlibF.Spec.Functional.Inflate.InflateTableKind
import ZlibF.Zlib.«inftrees.c»
import ZlibF.Spec.Functional.Format.Huffman

/-!
# inftrees.c: what the theorems about `inflate_table` say

`capOf` is the room the caller gives the table (`inftrees.h`: `ENOUGH_LENS`, `ENOUGH_DISTS`; 128 entries for
`CODES`, where the code-length code has at most 7 bits). `Result` is what every exit of `inflate_table` does to
the heap and to the returned values.
-/

namespace Zlib.Inftrees.Spec
open C

/-- The first `n` code lengths of `lens` (the array `la` read from offset `ol`), as the specification sees them. -/
def lensList (la : Array UInt16) (ol n : Nat) : List Nat := (List.range n).map (fun k => (la.getD (ol + k) 0).toNat)

end Zlib.Inftrees.Spec
