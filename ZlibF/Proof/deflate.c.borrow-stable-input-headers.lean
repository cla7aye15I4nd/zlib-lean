import ZlibF.Proof.«deflate.c.borrow-stable-base»
import ZlibF.Proof.«deflate.c.engine.header-buffered»
import ZlibF.Proof.«deflate.c.engine.common-first-header»
import ZlibF.Proof.«deflate.c.engine.header-boundary»
import ZlibF.Proof.«deflate.c.engine.common-header»

/-! # Actual header heap updates retain borrowed libc text -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The exact default header heap changes byte and stream/state records only. -/
theorem header_complete_borrow_eq (h : Heap) (r : ZStreamRef) (ds pb ob oo : Nat)
    (z : ZStream) (d : DeflateState) (buf output : Array UInt8) :
    (headerCompleteHeap h r ds pb ob oo z d buf output).libcErrorBorrow = h.libcErrorBorrow := by
  change (r.put (headerCompleteBytes h pb ob oo buf output) (headerCompleteStream z ob oo)).libcErrorBorrow = _
  rw [Zlib.Deflate.BorrowProofs.stream_put_borrow]
  rfl

end Zlib.Deflate.Engine.Proofs
