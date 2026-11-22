import ZlibF.Proof.«inflate.c.table-mode»
import ZlibF.Proof.«inflate.c.fast-default-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Advancing cursors retains the internal distinct-raw fast interface. -/
theorem RawFastIO.advance {l regs : IL} {used made : Nat} (raw : RawFastIO l)
    (input : regs.next = inputAdvance l.next used) (output : regs.put = inputAdvance l.put made) :
    RawFastIO regs := by
  obtain ⟨ib, io, ob, oo, next, put, different⟩ := raw
  exact ⟨ib, io + used, ob, oo + made, by rw [input, next]; rfl,
    by rw [output, put]; rfl, different⟩

end Zlib.Inflate.Proofs
