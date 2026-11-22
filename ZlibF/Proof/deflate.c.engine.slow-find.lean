import ZlibF.Proof.«deflate.c.engine.slow-source»
import ZlibF.Proof.«deflate.c.engine.caller-frame»

/-! # The slow strategy's actual conditional match search -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def matchState (d : DeflateState) (pos len : UInt32) : DeflateState :=
  { d with match_start := pos, match_length := len }

theorem matchState_good {h : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top) (pos len : UInt32) :
    DGood (setD h ds (matchState d pos len)) r ds z (matchState d pos len) ∧
      HeapChains (setD h ds (matchState d pos len)) (matchState d pos len) top := by
  have inv : DStInv h ds (matchState d pos len) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact ⟨good.setD' rfl good.live.status inv (by trkeep), by simpa only [HeapChains, matchState, setD] using chains⟩

def rejectShort (d : DeflateState) : Bool :=
  d.match_length ≤ 5 && (d.strategy == Z_FILTERED ||
    (d.match_length == MIN_MATCH_u && d.strstart - d.match_start > TOO_FAR))

/-- The source guard's unsigned distance has its mathematical meaning
once the actual old-head proof has established candidate < strstart. -/
theorem machine_distance {d : DeflateState} {candidate : UInt32}
    (older : candidate.toNat < d.strstart.toNat) (window : 262 ≤ d.w_size.toNat)
    (guard : d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u) :
    d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262 := by
  rw [UInt32.le_iff_toNat_le,
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega),
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact window)] at guard
  exact guard

/-- A failed search may retain its input match. A search that does not
improve the previous lazy length may retain a stale position. A selected
improvement has a real matching-byte witness. The short filter may reduce
the length below MIN_MATCH.
-/
def SearchEvidence (d : DeflateState) (wa : Array UInt8) (pos len : UInt32) : Prop :=
  (len = d.match_length ∧ pos = d.match_start) ∨
    len.toNat ≤ d.prev_length.toNat ∨ len.toNat < 3 ∨
      GoodMatch wa d.strstart.toNat d.w_size.toNat pos.toNat len.toNat

end Zlib.Deflate.Engine.Proofs
