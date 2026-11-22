import ZlibF.Spec.Common.Inflate.InflateCodeLengthInvariant
import ZlibF.Proof.«inflate.c.main.table6»
import ZlibF.Proof.«inflate.c.codelens-install»
import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Proof.«inflate.c.table-rebuffer»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual LENLENS result already retains the table predicate used
here. With the mode's count bounds, its installed state establishes every
CODELENS boundary clause; have is zero, so no unwritten lens cell is used. -/
theorem llOkSt_codeLengthInvariant (state : Nat) (s : InflateState) (used : Nat)
    (root : UInt32) (work : Array UInt16) (codes : Array Code)
    (table : Zlib.Inftrees.Spec.CodeLengthTableSafe codes 0 root.toNat)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30) :
    CodeLengthInvariant state (llOkSt state s used root work codes) := by
  intro _
  refine ⟨rfl, table, nlen, ndist, ?_, ?_⟩
  · change 0 ≤ _
    omega
  · intro k bound
    change k < 0 at bound
    omega

end Zlib.Inflate.Proofs
