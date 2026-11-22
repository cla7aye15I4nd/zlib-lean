import ZlibF.Proof.«deflate.c.engine.match-endpoint»
import ZlibF.Proof.«deflate.c.engine.match-advance»

/-! # Complete selected-match consumption without a long-input premise -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The last source increment rejoins the ordinary window-data endpoint. -/
theorem finish_match_good_at {h : Heap} {r : ZStreamRef} {ds w validEnd : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d)
    (chains : HeapChainsAt h d (d.strstart.toNat + 1) validEnd)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (endpoint : validEnd = d.strstart.toNat + 1 + d.lookahead.toNat) :
    (finishMatch d).strstart.toNat = d.strstart.toNat + 1 ∧
      DGood (setD h ds (finishMatch d)) r ds z (finishMatch d) ∧
      HeapChains (setD h ds (finishMatch d)) (finishMatch d) (finishMatch d).strstart.toNat ∧
      (finishMatch d).strstart.toNat + (finishMatch d).lookahead.toNat ≤ (finishMatch d).window_size.toNat := by
  have bumped := bump_start_good_at good chains win get room
  have inv : DStInv h ds (finishMatch d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have ss : (finishMatch d).strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have saved : HeapChainsAt (setD h ds (finishMatch d)) (finishMatch d)
      (d.strstart.toNat + 1) validEnd := chains.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨ss, good.setD' (d' := finishMatch d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · rw [ss]
    exact saved.collapse (by change validEnd = (finishMatch d).strstart.toNat + d.lookahead.toNat; rw [ss]; exact endpoint)
  · change (finishMatch d).strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
    rw [ss]; exact room

theorem max_insert_nat_bounded {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (nonempty : 3 ≤ d.strstart.toNat + d.lookahead.toNat) :
    (d.strstart + d.lookahead - MIN_MATCH_u).toNat = d.strstart.toNat + d.lookahead.toNat - 3 := by
  have extent := window_extent good win get
  have sum : (d.strstart + d.lookahead).toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, sum]; change 3 ≤ _; omega), sum]
  rfl

end Zlib.Deflate.Engine.Proofs
