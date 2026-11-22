import ZlibF.Proof.«deflate.c.engine.insert-chains»
import ZlibF.Proof.«deflate.c.engine.lmmain»

/-! # Actual hash tables supply the matcher's chain environment

Candidate order is retained from the old head returned by insertion.
It is not inferred from the new NIL head at position zero.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem heap_chains_arrays {h : Heap} {d : DeflateState} {top w p q : Nat}
    {wa : Array UInt8} {pa qa : Array UInt16} (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (hq : h.words q = some qa) :
    HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (d.strstart.toNat + d.lookahead.toNat) := by
  obtain ⟨w0, p0, q0, wa0, pa0, qa0, win0, prev0, head0, hw0, hp0, hq0, H⟩ := chains
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using win0.symm
  have pe : p0 = p := by simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using prev0.symm
  have qe : q0 = q := by simpa only [head, Ptr.ref.injEq, WRef.blk.injEq, and_true] using head0.symm
  subst w0 p0 q0
  have wbytes : wa0 = wa := Option.some.inj (hw0.symm.trans hw)
  have pwords : pa0 = pa := Option.some.inj (hp0.symm.trans hp)
  have qwords : qa0 = qa := Option.some.inj (hq0.symm.trans hq)
  subst wa0 pa0 qa0
  exact H

def insertedHeap (h : Heap) (ds p q : Nat) (d : DeflateState) (pa qa : Array UInt16) (key : UInt32) : Heap :=
  { h with
    dstates := upd h.dstates ds (some { d with ins_h := key }),
    words := upd (upd h.words p
      (some (pa.set! (d.strstart &&& d.w_mask).toNat (wfn qa key.toNat))))
      q (some (qa.set! key.toNat d.strstart.toUInt16)) }

theorem match_environment_published {h : Heap} {r : ZStreamRef} {ds w p q : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa : Array UInt16}
    {key : Nat} {candidate : UInt32}
    (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) (prev : d.prev = .ref (.blk p) 0)
    (_head : d.head = .ref (.blk q) 0)
    (hw : h.bytes w = some wa) (hp : h.words p = some pa) (_hq : h.words q = some qa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (d.strstart.toNat + 1) (d.strstart.toNat + d.lookahead.toNat))
    (hash : (hkey d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat).toNat = key)
    (keyBound : key < d.hash_size.toNat) (published : (wfn qa key).toNat = d.strstart.toNat)
    (link : (wfn pa (d.strstart.toNat &&& (d.w_size.toNat - 1))).toNat = candidate.toNat)
    (nonzero : 1 ≤ candidate.toNat) (older : candidate.toNat < d.strstart.toNat)
    (distance : d.strstart.toNat - candidate.toNat ≤ d.w_size.toNat - 262)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (lookahead : 262 ≤ d.lookahead.toNat) (previous : d.prev_length.toNat ≤ 258) :
    LMEnv h ds d w p wa pa candidate := by
  obtain ⟨w0, p0, q0, b, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pe : p0 = p := by simpa only [prev, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.prev.symm
  subst w0 p0
  obtain ⟨wa0, getW, sizeW⟩ := blocks.wa
  obtain ⟨pa0, getP, sizeP⟩ := blocks.pa
  have eqW : wa0 = wa := Option.some.inj (getW.symm.trans hw)
  have eqP : pa0 = pa := Option.some.inj (getP.symm.trans hp)
  subst wa0 pa0
  have window : d.strstart.toNat + d.lookahead.toNat ≤ 2 * d.w_size.toNat := by
    simpa only [good.inv.wsz] using range
  refine ⟨good.live.hs, win, hw, prev, hp,
    ⟨d.w_bits.toNat, good.inv.wsize, good.inv.wbits_lo, good.inv.wbits_hi⟩, ?_,
    by omega, by omega, by omega, by omega, previous, nonzero, older, distance, ?_⟩
  · apply UInt32.toNat_inj.mp
    rw [good.inv.wmask]
    have positive : 1 ≤ d.w_size.toNat := by
      rw [good.inv.wsize]
      have := Nat.two_pow_pos d.w_bits.toNat
      omega
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simpa using positive)]
    rfl
  · exact chain_ok_of_chains (hash_parameters good.inv) chains hash keyBound published link nonzero older distance

end Zlib.Deflate.Engine.Proofs
