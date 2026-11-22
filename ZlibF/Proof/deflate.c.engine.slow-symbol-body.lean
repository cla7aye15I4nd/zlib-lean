import ZlibF.Proof.«deflate.c.engine.slow-body»
import ZlibF.Proof.«deflate.c.engine.slow-symbols»

/-! # The full slow body preserves the initialized symbol boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

def retainedMatchSymbol (d : DeflateState) : Symbol :=
  ⟨(d.strstart - 1 - d.match_start).toNat, (d.match_length - MIN_MATCH_u).toNat⟩

end Zlib.Deflate.Engine.Proofs
