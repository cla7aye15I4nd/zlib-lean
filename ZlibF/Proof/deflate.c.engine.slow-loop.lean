import ZlibF.Proof.«deflate.c.engine.loop-accounting»

/-! # The actual non-flushing slow loop before block output

The byte budget describes the source path that cannot fill its symbol
buffer. It is not a restriction on the public compressor target.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

end Zlib.Deflate.Engine.Proofs
