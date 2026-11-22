import ZlibF.Proof.«deflate.c.engine.fill-initial»
import ZlibF.Proof.«deflate.c.engine.fill-read»
import ZlibF.Spec.Functional.Checksums

/-! # Complete first fill_window call with input

The first read consumes min(avail_in, 65536). If lookahead is still below
262, that read exhausted the input, so the source loop stops immediately.
The actual padding write and all hash priming statements are retained.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem setD_bytes_commute (h : Heap) (ds : Nat) (d : DeflateState)
    (bytes : Tbl (Option (Array UInt8))) :
    { setD h ds d with bytes } = setD { h with bytes } ds d := rfl

end Zlib.Deflate.Engine.Proofs
