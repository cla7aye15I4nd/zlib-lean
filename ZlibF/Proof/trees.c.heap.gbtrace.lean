import ZlibF.Proof.«trees.c.heap.gbtop»
import ZlibF.Proof.«trees.c.heap.gbfix-model»

/-! # Actual bit-length construction retains its first-pass and repair data -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Zlib.Trees.Proofs.GB
set_option autoImplicit false

/-- Data from the actual source stages, on their actual returned states.
The no-overflow branch retains the exact clamped first pass. The overflow
branch retains the precise initial histogram, number of repair rounds,
model count vector and source reassignment result. Rank-wise monotonicity
of the reassigned leaf lengths is a separate execution obligation. -/
def GBStageTrace (tk : TK) (d : DeflateState) (hm J elems maxc L : Nat)
    (xb : Nat → Nat) (slOpt : Option (Nat → Nat)) (result : DeflateState) : Prop :=
  (ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 0 ∧
    P1State tk d hm J elems maxc L xb slOpt (2 * J) result) ∨
  ∃ (R : Nat) (ov : Int32) (first repaired : DeflateState) (hc : Nat),
    ovP (Hn d) hm elems L (clK (Hn d) hm elems L (2 * J)) (2 * J) = 2 * (R + 1) ∧
    P1State tk d hm J elems maxc L xb slOpt (2 * J) first ∧
    FixInvX L (nLeaves (Hn d) hm J maxc) 0 ov
      (HuffmanAbstract.repairIter L (R + 1)
        (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b)) first repaired ∧
    ReSt tk repaired hm J maxc L xb
      (HuffmanAbstract.repairIter L (R + 1)
        (fun b => blC (Hn d) hm J maxc (clK (Hn d) hm elems L (2 * J)) b)) d.opt_len hc 0 0 result

end Zlib.Trees.Proofs
