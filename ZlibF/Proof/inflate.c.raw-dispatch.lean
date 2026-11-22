import ZlibF.Proof.«inflate.c.fast-buffers»
import ZlibF.Proof.«inflate.c.pending-dispatch»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The current fast-callee interface admits separate raw byte blocks.
This internal branch condition does not replace the public caller domain. -/
def RawFastIO (l : IL) : Prop :=
  ∃ ib io ob oo, l.next = .ref (.blk ib) io ∧ l.put = .ref (.blk ob) oo ∧ ib ≠ ob

end Zlib.Inflate.Proofs
