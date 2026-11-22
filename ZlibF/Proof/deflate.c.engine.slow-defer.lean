import ZlibF.Proof.«deflate.c.engine.slow-search»
import ZlibF.Proof.«deflate.c.engine.advance»
import ZlibF.Proof.«deflate.c.engine.fill-resume-empty»

/-! # The slow strategy's first deferred byte

The first search has no previous match or deferred literal. Its decision
therefore consumes one byte without writing a symbol or flushing a block.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def deferOne (d : DeflateState) : DeflateState :=
  { advanceOne d with match_available := 1 }

theorem defer_one_good {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (positive : 1 ≤ d.lookahead.toNat) :
    DGood (setD h ds (deferOne d)) r ds z (deferOne d) ∧
      HeapChains (setD h ds (deferOne d)) (deferOne d) top ∧
      (deferOne d).strstart.toNat + (deferOne d).lookahead.toNat ≤ (deferOne d).window_size.toNat := by
  have advanced := advance_one_good good chains range positive
  have inv : DStInv h ds (deferOne d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := deferOne d) rfl good.live.status inv (by trkeep), ?_, advanced.2.2⟩
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := advanced.2.1
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

theorem slow_defer_branch {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available = 0) (flush : Int32) (st : LoopS) (candidate : UInt32) :
    slowDecision (some (.tab ds)) flush st candidate h =
      .ok ({ st with hash_head := candidate, bflush := false }, setD h ds (deferOne d)) := by
  unfold slowDecision
  simp only [bind_app, ldDeflateState_tab state, branch, Bool.false_eq_true, ite_false, available]
  change (wr (some (.tab ds)) deferOne >>= fun _ =>
    pure { st with hash_head := candidate, bflush := false }) h = _
  simp [wrD_eq, state, deferOne, advanceOne]

end Zlib.Deflate.Engine.Proofs
