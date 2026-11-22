import ZlibF.Proof.«inflate.c.lenlens-mode»
import ZlibF.Proof.«inflate.c.no-return»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual four-bit HCLEN field always gives at most nineteen entries. -/
theorem tableCounts_ncode_bound (s : InflateState) (hold : UInt64) :
    (tableCounts s hold).ncode.toNat ≤ 19 := by
  have mask : (((hold >>> 5 >>> 5).toUInt32 &&& 15).toNat) ≤ 15 := by
    rw [UInt32.toNat_and]
    exact Nat.and_le_right
  change (((hold >>> 5 >>> 5).toUInt32 &&& 15) + 4).toNat ≤ 19
  rw [UInt32.toNat_add]
  change (_ + 4) % 2 ^ 32 ≤ 19
  omega

/-- Scalar fields written while reading the dynamic alphabet counts. -/
def TableCountsFrame (before after : InflateState) : Prop :=
  after = { before with nlen := after.nlen, ndist := after.ndist, ncode := after.ncode, «have» := after.«have», mode := after.mode }

/-- Actual count writes retain J once the real validity check has supplied
its guarded LENLENS clause. BAD activates no construction precondition. -/
theorem DefaultDecodeJ.counts_update {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultDecodeJ h r zs z s)
    (frame : TableCountsFrame s state) (streamFrame : stream = { z with msg := stream.msg })
    (modes : state.mode = BAD ∨ state.mode = LENLENS) (lengths : LengthHeaderInvariant state) :
    DefaultDecodeJ (setI (r.put h stream) zs state) r zs stream state := by
  have bounds : HEAD ≤ state.mode ∧ state.mode ≤ SYNC := by
    rcases modes with selected | selected <;> rw [selected] <;> decide
  have inv : StInv h zs state := by
    apply invariant.good.inv.of_fields
    all_goals rw [frame]
    exact invariant.good.inv.bits
  have current : Good (setI (r.put h stream) zs state) r zs stream state :=
    invariant.good.setZI (by rw [streamFrame]) (by rw [streamFrame]; exact invariant.good.live.zalloc)
      (by rw [streamFrame]; exact invariant.good.live.zfree) (by rw [frame]) bounds inv
  refine ⟨current, ?_, ?_, ?_, lengths, ?_, ?_, ?_, ?_, ?_, ?_,
    (by simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals),
    (invariant.platform.put_stream r stream).with_istates _⟩
  · apply dataTableInvariant_inactive
    rcases modes with selected | selected <;> rw [selected] <;> unfold DataTableMode <;> decide
  · apply dataPendingInvariant_idle (by rw [frame]; exact invariant.pending.sane)
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · intro active
    rcases modes with selected | selected <;> rw [selected] at active <;> contradiction
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · rw [frame]
    exact invariant.header
  · right; left
    rcases modes with selected | selected <;> rw [selected] <;> decide
  · rintro (active | active) <;>
      rcases modes with selected | selected <;> rw [selected] at active <;> contradiction

/-- The accepted dynamic count check initializes the exact LENLENS guard.
No lens entry is constrained before it has been written. -/
theorem tableCounts_header_invariant (s : InflateState) (hold : UInt64)
    (valid : ¬ ((tableCounts s hold).nlen > 286 ∨ (tableCounts s hold).ndist > 30)) :
    LengthHeaderInvariant { tableCounts s hold with «have» := 0, mode := LENLENS } := by
  intro _
  have nlen := (not_or.mp valid).1
  have ndist := (not_or.mp valid).2
  rw [gt_iff_lt, UInt32.lt_iff_toNat_lt] at nlen ndist
  refine ⟨tableCounts_ncode_bound s hold, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ _
    omega
  · change (tableCounts s hold).nlen.toNat ≤ 286
    change ¬ 286 < (tableCounts s hold).nlen.toNat at nlen
    omega
  · change (tableCounts s hold).ndist.toNat ≤ 30
    change ¬ 30 < (tableCounts s hold).ndist.toNat at ndist
    omega
  · intro k inside
    change k < 0 at inside
    omega


/-- Exact metadata writes preserve all public byte views and transport
an already checked input trace without changing the output interval. -/
theorem DispatchBuffers.metadata_advance {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} {l regs : IL} {bs : List UInt8} {used : Nat}
    (buffers : DispatchBuffers h r l bs) (before : Good h r zs z s)
    (current : Good (setI (r.put h stream) zs state) r zs stream state)
    (window : state.window = s.window) (inv : BitInv h regs (bs.drop used))
    (cursor : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat)
    (put : regs.put = l.put) (left : regs.left = l.left) (total : regs.out_ = l.out_) :
    DispatchBuffers (setI (r.put h stream) zs state) r regs (bs.drop used) ∧
      ByteViewSizes h (setI (r.put h stream) zs state) := by
  have views : ∀ ref : BRef, Space.get (setI (r.put h stream) zs state) ref = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) := by intro ref; rw [views]
  have readonly : ∀ ref : BRef, Space.ro (setI (r.put h stream) zs state) ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  exact ⟨buffers.advance_both before current window sizes readonly cursor count (made := 0)
    (by rw [inputAdvance_zero]; exact put) (by rw [left]; rfl) total (inv.byte_views views), sizes⟩

/-- The real switch selects the TABLE construction mode. -/
theorem inflate_dispatch_TABLE {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = TABLE) :
    runX (inflate_dispatch c) l h = runX (inflate_TABLE c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE]

/-- The real switch selects the LENLENS construction mode. -/
theorem inflate_dispatch_LENLENS {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = LENLENS) :
    runX (inflate_dispatch c) l h = runX (inflate_LENLENS c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS]

/-- The real switch selects the CODELENS construction mode. -/
theorem inflate_dispatch_CODELENS {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = CODELENS) :
    runX (inflate_dispatch c) l h = runX (inflate_CODELENS c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS]

/-- The construction cases of the actual switch cannot invent a direct
API return. The result follows from the translated mode bodies. -/
theorem inflate_dispatch_construction_outcomes {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l regs : IL} {after : Heap} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
    (run : runX (inflate_dispatch c) l h = .ok ((outcome, regs), after)) :
    outcome = .error Ex.leave ∨ outcome = .ok () := by
  rcases mode with table | lengths | codes
  · exact (noRet_inflate_TABLE c).outcomes ((inflate_dispatch_TABLE E l table).symm.trans run)
  · exact (noRet_inflate_LENLENS c).outcomes ((inflate_dispatch_LENLENS E l lengths).symm.trans run)
  · exact (noRet_inflate_CODELENS c).outcomes ((inflate_dispatch_CODELENS E l codes).symm.trans run)

end Zlib.Inflate.Proofs
