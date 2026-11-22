import ZlibF.Proof.«deflate.c.engine.fill-prime»
import ZlibF.Proof.«deflate.c.engine.read-zlib»
import ZlibF.Spec.Functional.Checksums

/-! # First fill_window input read and hash priming -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem rbLen_nat (avail size : UInt32) : (rbLen avail size).toNat = min avail.toNat size.toNat := by
  unfold rbLen
  split
  · rename_i big
    change size < avail at big
    rw [UInt32.lt_iff_toNat_lt] at big
    exact (Nat.min_eq_right (by omega)).symm
  · rename_i small
    change ¬ size < avail at small
    rw [UInt32.lt_iff_toNat_lt] at small
    exact (Nat.min_eq_left (by omega)).symm

def firstRead (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in 65536
  let copied := copyRange wa ia 0 io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  setD (r.put { h with bytes := upd h.bytes w (some copied) } z') ds
    (primeState { d with lookahead := n } copied)

end Zlib.Deflate.Engine.Proofs
