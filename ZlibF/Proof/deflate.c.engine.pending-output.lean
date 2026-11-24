import ZlibF.Proof.«deflate.c.engine.read-zlib»
import ZlibF.Proof.«trees.c.align»

/-! # Actual pending-prefix transfer for the default wrapper header

These internal execution results cover fewer than eight buffered bits
and distinct raw output/pending allocations. They do not replace the
public buffer domain or the general bit-flush obligation.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The source's unsigned length selection, without a truncation premise. -/
def pendingLen (pending : UInt64) (available : UInt32) : UInt32 :=
  if pending > available.toUInt64 then available else pending.toUInt32

theorem pendingLen_value (pending : UInt64) (available : UInt32) :
    (pendingLen pending available).toNat = min pending.toNat available.toNat := by
  unfold pendingLen
  split
  · rename_i larger
    change available.toUInt64 < pending at larger
    rw [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64] at larger
    omega
  · rename_i smaller
    have bound : pending.toNat ≤ available.toNat := by
      change ¬ available.toUInt64 < pending at smaller
      rw [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64] at smaller
      omega
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by have size := available.toNat_lt; omega)]
    omega

def pendingStream (z : ZStream) (out : BPtr) (n : UInt32) : ZStream :=
  { z with next_out := out, total_out := z.total_out + n.toUInt64, avail_out := z.avail_out - n }

def pendingState (d : DeflateState) (out : BPtr) (n : UInt32) : DeflateState :=
  { d with
    pending_out := if d.pending - n.toUInt64 == 0 then d.pending_buf else out,
    pending := d.pending - n.toUInt64 }

/-- Updating the stream record preserves the array bounds used by byte pointer arithmetic. -/
private theorem padd_after_stream_write {p q : BPtr} {n : Nat} {h : Heap}
    (r : ZStreamRef) (z : ZStream) (advance : padd p n h = .ok (q, h)) :
    padd p n (r.put h z) = .ok (q, r.put h z) := by
  have same (b : BRef) : Space.get (r.put h z) b = Space.get h b := by
    cases r <;> cases b <;> simp [ZStreamRef.put] <;> (try split) <;> rfl
  unfold padd Ptr.add at advance ⊢
  split at advance <;> rename_i k
  · simp [k] at advance ⊢
    exact advance
  · simp only [k, ite_false]
    cases p with
    | null => cases advance
    | ref b off =>
      simp only [same] at *
      cases a : Space.get h b <;> simp [a] at advance ⊢
      split at advance <;> simp_all

/-- Compute the six field updates after a successful copy, starting from the current records. -/
theorem advance_pending_eq {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {n : UInt32} {out pending : BPtr} (hz : r.get h = some z) (hd : h.dstates ds = some d)
    (outAdd : padd z.next_out n.toNat h = .ok (out, h))
    (pendingAdd : padd d.pending_out n.toNat h = .ok (pending, h)) :
    advance_pending (some r) (some (.tab ds)) n h =
      .ok ((), setD (r.put h (pendingStream z out n)) ds (pendingState d pending n)) := by
  have advance := padd_after_stream_write r { z with next_out := out } pendingAdd
  simp only [advance_pending, bind_app, zrd_eq, zwr_eq, rdD_eq, wrD_eq, hz, hd, outAdd,
    advance, ZStreamRef.put_dstates, ZStreamRef.get_setD, ZStreamRef.get_put, Option.map_some,
    ZStreamRef.put_setD, ZStreamRef.put_put, setD_dstates_same, setD_setD]
  split <;> rename_i exhausted <;>
    simp [exhausted, pendingStream, pendingState, wrD_eq, pure_app]

/-- `local void flush_pending(z_streamp strm)`.
With fewer than eight buffered bits and zero selected bytes, the actual
call leaves the heap unchanged. It does not dereference caller output. -/
theorem flush_pending_low_zero {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (zero : pendingLen d.pending z.avail_out = 0) :
    flush_pending (some r) h = .ok ((), h) := by
  have flushBits := Zlib.Trees.Proofs.Out.bi_flush_low hd bits
  unfold pendingLen at zero
  simp only [flush_pending, zrd_eq, hz, bind_app, state, castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq, flushBits, ldDeflateState_tab hd,
    ldZStream_ok hz, zero, BEq.rfl, ite_true]
  rfl

/-- `local void flush_pending(z_streamp strm)`.
The aligned raw-output path copies exactly the selected pending prefix,
advances both cursors, updates the wrapping output total and resets the
pending cursor only after all pending bytes have been consumed. Caller
output and pending storage are distinct raw allocations. -/
theorem flush_pending_low_raw {h : Heap} {r : ZStreamRef} {ds pb ob po oo : Nat}
    {z : ZStream} {d : DeflateState} {pending output : Array UInt8}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (outPtr : z.next_out = .ref (.blk ob) oo) (pendingPtr : d.pending_out = .ref (.blk pb) po)
    (outGet : h.bytes ob = some output) (pendingGet : h.bytes pb = some pending)
    (writable : h.ro ob = false) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size)
    (pendingBound : po + d.pending.toNat ≤ pending.size)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0) :
    let n := pendingLen d.pending z.avail_out
    let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
    flush_pending (some r) h = .ok ((),
      setD (r.put copied (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)) ds
        (pendingState d (.ref (.blk pb) (po + n.toNat)) n)) := by
  let n := pendingLen d.pending z.avail_out
  let copied := { h with bytes := upd h.bytes ob (some (copyRange output pending oo po n.toNat)) }
  change flush_pending (some r) h = .ok ((),
    setD (r.put copied (pendingStream z (.ref (.blk ob) (oo + n.toNat)) n)) ds
      (pendingState d (.ref (.blk pb) (po + n.toNat)) n))
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have copy : memcpyB z.next_out d.pending_out n.toNat h = .ok ((), copied) := by
    rw [outPtr, pendingPtr]
    exact memcpyB_blk_ok outGet pendingGet writable separate (by omega) (by omega)
  have outAfter : copied.bytes ob = some (copyRange output pending oo po n.toNat) := by simp [copied]
  have pendingAfter : copied.bytes pb = some pending := by
    simpa only [copied, upd_ne _ _ _ _ (Ne.symm separate)] using pendingGet
  have advanceOut : padd z.next_out n.toNat copied = .ok (.ref (.blk ob) (oo + n.toNat), copied) := by
    rw [outPtr]
    exact padd_ok' outAfter (by rw [size_copyRange]; omega)
  have advancePending : padd d.pending_out n.toNat copied = .ok (.ref (.blk pb) (po + n.toNat), copied) := by
    rw [pendingPtr]
    exact padd_ok' pendingAfter (by omega)
  have getZ : r.get copied = some z := by simpa only [copied, stream_get_bytes] using hz
  have getD : copied.dstates ds = some d := hd
  have flushBits := Zlib.Trees.Proofs.Out.bi_flush_low hd bits
  have test : (n == 0) = false := by simpa only [n, beq_eq_false_iff_ne] using nonzero
  have selected : (if d.pending > z.avail_out.toUInt64 then z.avail_out else d.pending.toUInt32) = n := rfl
  simp only [flush_pending, zrd_eq, hz, bind_app, state, castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq, flushBits, ldDeflateState_tab hd,
    ldZStream_ok hz, selected, test, Bool.false_eq_true, ite_false, copy]
  exact advance_pending_eq getZ getD advanceOut advancePending

/-- Copying into an embedded depth array also preserves the bytes when the array belongs
    to the same state whose pending cursor is being advanced. -/
theorem flush_pending_low_depth {h : Heap} {r : ZStreamRef} {ds pb owner po oo : Nat}
    {z : ZStream} {d foreign : DeflateState} {pending : Array UInt8}
    (hz : r.get h = some z) (state : z.state = some (.deflate ds))
    (hd : h.dstates ds = some d) (bits : d.bi_valid.toInt < 8)
    (outPtr : z.next_out = .ref (.dstate_depth owner) oo) (pendingPtr : d.pending_out = .ref (.blk pb) po)
    (outGet : h.dstates owner = some foreign) (pendingGet : h.bytes pb = some pending)
    (outBound : oo + z.avail_out.toNat ≤ foreign.depth.size)
    (pendingBound : po + d.pending.toNat ≤ pending.size)
    (nonzero : pendingLen d.pending z.avail_out ≠ 0) :
    let n := pendingLen d.pending z.avail_out
    let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
    let current := if ds = owner then { d with depth := copyRange foreign.depth pending oo po n.toNat } else d
    flush_pending (some r) h = .ok ((),
      setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
        (pendingState current (.ref (.blk pb) (po + n.toNat)) n)) := by
  let n := pendingLen d.pending z.avail_out
  let copied := setD h owner { foreign with depth := copyRange foreign.depth pending oo po n.toNat }
  let current := if ds = owner then { d with depth := copyRange foreign.depth pending oo po n.toNat } else d
  change flush_pending (some r) h = .ok ((),
    setD (r.put copied (pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n)) ds
      (pendingState current (.ref (.blk pb) (po + n.toNat)) n))
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have copy : memcpyB z.next_out d.pending_out n.toNat h = .ok ((), copied) := by
    rw [outPtr, pendingPtr]
    have run := Ptr.memcpy_ok (rd := BRef.dstate_depth owner) (rs := BRef.blk pb)
      (od := oo) (os := po) (n := n.toNat) (BRef.get_dstate_depth outGet) pendingGet
      (by rfl) (by omega) (by omega) (Or.inl (by intro bad; cases bad))
    have store (next : Array UInt8) : Space.put h (.dstate_depth owner : BRef) next =
        setD h owner { foreign with depth := next } := BRef.put_dstate_depth outGet next
    simpa only [memcpyB, store, copied] using run
  have outAfter : Space.get copied (BRef.dstate_depth owner) =
      some (copyRange foreign.depth pending oo po n.toNat) := by
    exact BRef.get_dstate_depth (s := { foreign with depth := copyRange foreign.depth pending oo po n.toNat }) (by simp [copied])
  have pendingAfter : copied.bytes pb = some pending := pendingGet
  have advanceOut : padd z.next_out n.toNat copied = .ok (.ref (.dstate_depth owner) (oo + n.toNat), copied) := by
    rw [outPtr]
    exact padd_ok' outAfter (by rw [size_copyRange]; omega)
  have advancePending : padd d.pending_out n.toNat copied = .ok (.ref (.blk pb) (po + n.toNat), copied) := by
    rw [pendingPtr]
    exact padd_ok' pendingAfter (by omega)
  have getZ : r.get copied = some z := by simpa only [copied, ZStreamRef.get_setD] using hz
  have getD : copied.dstates ds = some current := by
    by_cases same : ds = owner
    · subst owner
      have records := hd.symm.trans outGet
      cases records
      simp [copied, current]
    · simpa only [copied, current, same, ite_false, setD_dstates_ne _ _ _ _ same] using hd
  have cursor : current.pending_out = d.pending_out := by dsimp only [current]; split <;> rfl
  have flushBits := Zlib.Trees.Proofs.Out.bi_flush_low hd bits
  have test : (n == 0) = false := by simpa only [n, beq_eq_false_iff_ne] using nonzero
  have selected : (if d.pending > z.avail_out.toUInt64 then z.avail_out else d.pending.toUInt32) = n := rfl
  simp only [flush_pending, zrd_eq, hz, bind_app, state, castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq, flushBits, ldDeflateState_tab hd,
    ldZStream_ok hz, selected, test, Bool.false_eq_true, ite_false, copy]
  exact advance_pending_eq getZ getD advanceOut (by simpa only [cursor] using advancePending)

end Zlib.Deflate.Engine.Proofs
