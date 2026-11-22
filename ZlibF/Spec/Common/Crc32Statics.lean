import ZlibF.Zlib.«crc32.c»

/-!
# crc32.c: the static tables

`StaticsOK h` is the premise of the CRC goals. The lemmas about it are in `ZlibF/Proof/crc32.c.lean`.
-/

namespace Zlib.Crc32.Proofs
open C

/-- `StaticsOK h`: the static tables `crc_table` and `x2n_table` of the heap hold the contents `crc32.h` gives them
(`Zlib.Crc32.initStatics`). -/
def StaticsOK (h : Heap) : Prop :=
  h.static.crc_table = Crc32H.crc_table ∧ h.static.x2n_table = Crc32H.x2n_table

end Zlib.Crc32.Proofs
