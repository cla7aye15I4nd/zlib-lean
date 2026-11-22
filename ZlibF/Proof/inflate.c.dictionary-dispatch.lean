import ZlibF.Proof.«inflate.c.block-type»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The direct dictionary request restores cursors and accounts only for
input. This return bypasses the ordinary inf_leave suffix in the source. -/
def dictWaitStream (z : ZStream) (l : IL) : ZStream :=
  { leaveStream z l with total_in := z.total_in + (l.in_ - l.have_).toUInt64 }

/-- The exact real Z_NEED_DICT path, including its input accounting. -/
theorem inflate_DICT_wait_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (missing : s.havedict = 0) :
    runX (inflate_DICT c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), l),
      setI (r.put h (dictWaitStream z l)) zs (leaveState s l)) := by
  have restored : Env c (setI (r.put h (leaveStream z l)) zs (leaveState s l)) r zs
      (leaveStream z l) (leaveState s l) :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _, by simp⟩
  unfold inflate_DICT
  rw [runX_bind, runX_rdS E]
  simp only [missing, beq_self_eq_true, ↓reduceIte]
  rw [runX_bind, RESTORE_pending_run E]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  have write : wrZ c.strm (fun stream => { stream with total_in := stream.total_in + (l.in_ - stream.avail_in).toUInt64 })
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) =
      .ok ((), setI (r.put h (dictWaitStream z l)) zs (leaveState s l)) := by
    simp only [E.strm, wrZ_eq, restored.hz, ZStreamRef.put_setI, ZStreamRef.put_put]
    rfl
  rw [runX_bind, runX_lift_ok write]
  rfl

/-- A dictionary request retains the common packet and writes back the
normalized local bits. It changes no caller bytes and preserves the exact
heap shape; the actual public return is Z_NEED_DICT. -/
theorem inflate_DICT_wait_boundary {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = DICT)
    (missing : s.havedict = 0) (bitsBound : l.bits.toNat ≤ 39) :
    let stream := dictWaitStream z l
    let state := leaveState s l
    let after := setI (r.put h stream) zs state
    runX (inflate_DICT c) l h = .ok ((.error (Ex.ret Z_NEED_DICT), l), after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      DispatchBuffers after r l bs ∧ ByteViewSizes h after ∧ after.static = h.static ∧
      state.hold.toNat < 2 ^ state.bits.toNat ∧
      stream.total_out = z.total_out ∧ state.total = s.total := by
  dsimp only
  let stream := dictWaitStream z l
  let state := leaveState s l
  let after := setI (r.put h stream) zs state
  have nextGood : Good after r zs stream state :=
    good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode
      (good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl bitsBound rfl rfl rfl)
  have views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  have nextPending : DataPendingInvariant state :=
    ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩
  exact ⟨inflate_DICT_wait_run E l missing, nextGood,
    dataTableInvariant_inactive (by change ¬ DataTableMode s.mode; rw [mode]; unfold DataTableMode; decide),
    nextPending, buffers.byte_views good nextGood rfl views readonly,
    by intro ref; rw [views], by simp only [setI, ZStreamRef.put_static], buffers.bits.hold_lt, rfl, rfl⟩

/-- Once a dictionary exists, the source initializes the checksum and
continues through the actual TYPE mode. The continuation is the already
proved block-type program, rather than an assumed contract. -/
theorem inflate_DICT_ready_cut {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (present : s.havedict ≠ 0) :
    runX (inflate_DICT c) l h = runX (inflate_TYPE c) l
      (setI (r.put h { z with adler := 1 }) zs { s with check := 1, mode := TYPE }) := by
  unfold inflate_DICT
  rw [runX_bind, runX_rdS E]
  simp only [beq_iff_eq, present, ↓reduceIte]
  rw [runX_bind, runX_lift_ok (adler32_init h)]
  simp only []
  rw [runX_bind, runX_wrS E]
  simp only []
  have E1 : Env c (setI h zs { s with check := 1 }) r zs z { s with check := 1 } :=
    ⟨E.strm, E.st, by simpa only [ZStreamRef.get_setI] using E.hz, by simp⟩
  have write : wrZ c.strm (fun z => { z with adler := 1 }) (setI h zs { s with check := 1 }) =
      .ok ((), setI (r.put h { z with adler := 1 }) zs { s with check := 1 }) := by
    simp only [E.strm, wrZ_eq, E1.hz, ZStreamRef.put_setI]
  rw [runX_bind, runX_lift_ok write]
  simp only []
  have E2 : Env c (setI (r.put h { z with adler := 1 }) zs { s with check := 1 }) r zs
      { z with adler := 1 } { s with check := 1 } :=
    ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _, by simp⟩
  rw [runX_bind, runX_setMode E2, setI_setI]

end Zlib.Inflate.Proofs
