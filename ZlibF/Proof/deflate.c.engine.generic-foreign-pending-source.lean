import ZlibF.Proof.«deflate.c.engine.generic-foreign-output-base»

/-! Pending publication into a state's embedded byte array after a low-bit flush. -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem flush_pending_low_foreign {h : Heap} {r : ZStreamRef} {ds pb owner po oo : Nat}
    {z : ZStream} {d foreign : DeflateState} {pending : Array UInt8}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (outPtr : z.next_out = .ref (.dstate_depth owner) oo) (pendingPtr : d.pending_out = .ref (.blk pb) po)
    (outGet : h.dstates owner = some foreign) (pendingGet : h.bytes pb = some pending)
    (different : ds ≠ owner)
    (outBound : oo + z.avail_out.toNat ≤ foreign.depth.size)
    (pendingBound : po + d.pending.toNat ≤ pending.size)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0) :
    let n := pendingLen d.pending z.avail_out
    let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
    flush_pending (some r) h = .ok ((),
      setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
        (pendingState d (.ref (.blk pb) (po + n.toNat)) n)) := by
  simpa only [different, ite_false] using flush_pending_low_depth hz state hd bits outPtr
    pendingPtr outGet pendingGet outBound pendingBound nonzero


end Zlib.Deflate.Engine.Proofs
