import ZlibF.Proof.«deflate.c.engine.slow-find»

/-! # The actual slow strategy's insertion and match-search prefix -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def lazyPrepare (d : DeflateState) : DeflateState :=
  { d with prev_length := d.match_length, prev_match := d.match_start, match_length := 2 }

theorem initial_match_length : (MIN_MATCH_u - 1 : UInt32) = 2 := by decide

theorem lazy_prepare_inv {h : Heap} {ds : Nat} {d : DeflateState} (inv : DStInv h ds d) :
    DStInv h ds (lazyPrepare d) := by
  exact { inv with blocks := inv.blocks_keys (d' := lazyPrepare d) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }

theorem lazy_prepare_chains {h : Heap} {ds top : Nat} {d : DeflateState} (chains : HeapChains h d top) :
    HeapChains (setD h ds (lazyPrepare d)) (lazyPrepare d) top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

theorem lazy_prepare_good {h : Heap} {r : ZStreamRef} {ds top : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top) :
    DGood (setD h ds (lazyPrepare d)) r ds z (lazyPrepare d) ∧
      HeapChains (setD h ds (lazyPrepare d)) (lazyPrepare d) top := by
  exact ⟨good.setD' (d' := lazyPrepare d) rfl good.live.status (lazy_prepare_inv good.inv) (by trkeep),
    lazy_prepare_chains chains⟩

theorem slow_search_composes {h after : Heap} {ds p q : Nat} {d : DeflateState}
    {pa qa : Array UInt16} {key : UInt32}
    (state : h.dstates ds = some d) (ready : d.lookahead ≥ MIN_MATCH_u)
    (inserted : INSERT_STRING (some (.tab ds)) d.strstart h =
      .ok ((wfn qa key.toNat).toUInt32, insertedHeap h ds p q d pa qa key))
    (findRun : slowFind (some (.tab ds)) (wfn qa key.toNat).toUInt32
      (setD (insertedHeap h ds p q d pa qa key) ds (lazyPrepare { d with ins_h := key })) = .ok ((), after)) :
    slowSearch (some (.tab ds)) h = .ok ((wfn qa key.toNat).toUInt32, after) := by
  let hi := insertedHeap h ds p q d pa qa key
  let hm := setD hi ds (lazyPrepare { d with ins_h := key })
  have write : wr (some (.tab ds)) lazyPrepare hi = .ok ((), hm) := by
    simp [wrD_eq, hi, insertedHeap, hm]
  unfold slowSearch
  simp only [bind_app, rdD_eq, state, ready, ite_true, inserted, initial_match_length]
  change (do
    wr (some (.tab ds)) lazyPrepare
    slowFind (some (.tab ds)) (wfn qa key.toNat).toUInt32
    pure (wfn qa key.toNat).toUInt32) hi = _
  rw [bind_app, write]
  simp only []
  rw [bind_app, findRun]
  rfl

end Zlib.Deflate.Engine.Proofs
