import Lean2C.OriginalUncompress
import ZlibF.Proof.«inflate.c.leave-finalize»
import ZlibF.Proof.«inflate.c.dispatch-entry»

/-! Zero-output paths of the inflate call made by uncompress2_z. -/
namespace Lean2C.OriginalUncompress
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false

/-- On exit the stream records the selected pointer. With no window and no
output this is its only use. This includes the byte pointer into the automatic
stream, regardless of the contents of the reserved field. -/
theorem zero_output_leave {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (window : s.wsize = 0) (noOutput : l.out_ = l.left) (bits : l.bits.toNat ≤ 39) :
    ∃ dt : Int32, chkI32 ((u2i l.bits).toInt + (if s.last != 0 then 64 else 0) +
      (if s.mode == TYPE then 128 else 0) + (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)) = pure dt ∧
      ∀ p : BPtr,
      let regs := {l with put := p}
      let stream := {leaveStream z regs with total_in := z.total_in + (l.in_ - l.have_).toUInt64, data_type := dt}
      let ret := if ((l.in_ - l.have_ == 0 || c.flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret
      inflate_leave c regs (r.put h {z with next_out := p}) =
        .ok (ret, setI (r.put h stream) zs (leaveState s l)) := by
  let state := leaveState s l
  obtain ⟨dt, cast⟩ := leave_data_type_safe state bits
  refine ⟨dt, cast, fun p => ?_⟩
  let regs := {l with put := p}
  let old := {z with next_out := p}
  let saved := leaveStream old regs
  let heap0 := setI (r.put (r.put h old) saved) zs state
  let counted := leaveCountStream saved saved regs
  let heap1 := setI (r.put heap0 counted) zs state
  have E0 : Env c heap0 r zs saved state :=
    ⟨E.strm, E.st, by simp [heap0, ZStreamRef.get_put_same E.hz], upd_same ..⟩
  have E1 : Env c heap1 r zs counted state :=
    ⟨E.strm, E.st, by simp [heap1, ZStreamRef.get_put_same E0.hz], upd_same ..⟩
  have zero : regs.out_ - saved.avail_out = 0 := by change l.out_ - l.left = 0; rw [noOutput, UInt32.sub_self]
  have skip : (state.wsize != 0 || (regs.out_ != saved.avail_out && state.mode < BAD &&
      (state.mode < CHECK || c.flush != Z_FINISH))) = false := by
    change (s.wsize != 0 || (l.out_ != l.left && _ && _)) = false
    simp [window, noOutput]
  have countState : leaveCountState state saved regs = state := by simp [leaveCountState, zero]
  have count : leaveCounters c regs saved heap0 = .ok ((), heap1) := by
    simpa only [countState] using (leaveCounters_run (z := saved) E0 (l := regs))
  have noCheck : leaveChecksum c regs saved heap1 = .ok ((), heap1) := by
    unfold leaveChecksum
    simp [bind_app, E.st, ldInflateState_tab E1.hs, zero, pure_app]
  obtain ⟨dt', cast', ret⟩ := leaveReturn_run (z := saved) (l := regs) E1 bits
  have same : dt' = dt := by
    rw [cast] at cast'
    exact (congrArg Prod.fst (Except.ok.inj (congrFun cast' h))).symm
  subst dt'
  change inflate_leave c regs (r.put h old) = _
  rw [inflate_leave_restore_cut (E.put old)]
  change leaveAfterRestore c regs heap0 = _
  rw [leaveAfterRestore_no_window E0 skip, leaveFinalize_split]
  simp only [bind_app, count, noCheck, ret]
  simp only [zero, beq_self_eq_true, Bool.and_true, ZStreamRef.put_setI, ZStreamRef.put_put, setI_setI,
    heap1, heap0, counted, leaveCountStream, show (0 : UInt32).toUInt64 = 0 from rfl, UInt64.add_zero]
  rfl

/-- A call starting in HEAD with no input leaves the dispatch loop before
touching the selected output pointer. -/
theorem empty_input_dispatch {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (head : s.mode = HEAD) (wrapped : s.wrap ≠ 0) (short : s.bits < 16) (empty : z.avail_in = 0) :
    runX (inflate_run c) IL.init h = .ok ((.error Ex.leave, dispatchRegs z s), h) := by
  let l := dispatchRegs z s
  let test : X Bool := do return (← get).bits < (16 : UInt32)
  have guard : runX test l h = .ok ((.ok true, l), h) := by
    rw [show runX test l h = _ from runX_cond_lt 16 l h]
    simp [l, dispatchRegs, short]
  have wait : runX (NEEDBITS 16) l h = .ok ((.error Ex.leave, l), h) := by
    obtain ⟨res, regs, H, run, rfl, rfl, rfl⟩ := xwhileBrk_run (cond := test)
      (body := do PULLBYTE; pure false) (fun k regs H => k = 1 ∧ regs = l ∧ H = h)
      (fun res regs H => res = .error Ex.leave ∧ regs = l ∧ H = h)
      (by rintro k regs H ⟨_, rfl, rfl⟩
          exact ⟨_, _, guard, .error Ex.leave, _, _, by rw [runX_bind, PULLBYTE_zero (show l.have_ = 0 from empty)], rfl, rfl, rfl⟩)
      (by rintro _ _ ⟨bad, _⟩; cases bad)
      (k := 1) (l := l) (h := h) ⟨rfl, rfl, rfl⟩ (by decide)
    exact run
  have dispatch : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l), h) := by
    unfold inflate_dispatch
    rw [runX_bind, runX_rdS E]
    simp only [head, beq_self_eq_true, ↓reduceIte]
    unfold inflate_HEAD
    simp only [runX_bind, runX_rdS E, beq_false_of_ne wrapped, Bool.false_eq_true, ↓reduceIte, wait]
  have stop := xwhile_run_chain (inflate_dispatch c) (fun _ => l) (fun _ => h) 0 (by decide)
    Ex.leave l h (by intro j hj; omega) dispatch
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  simp only [head]
  change runX (do
    LOAD c.strm c.st
    modify fun regs => {regs with in_ := regs.have_, out_ := regs.left, ret := Z_OK}
    xwhile (pure true) (inflate_dispatch c)) IL.init h = _
  rw [runX_bind, LOAD_run E]
  dsimp only
  rw [runX_bind, runX_modify]
  exact stop

/-- A fresh, wrapped decoder with empty input returns Z_BUF_ERROR before
using any output bytes. Its only caller-visible record write is data_type.
The result includes allocation and release of inflate's four-byte local. -/
theorem empty_input_inflate {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (fresh : Fresh h) (live : Live h r zs z s) (head : s.mode = HEAD) (wrapped : s.wrap ≠ 0)
    (window : s.wsize = 0) (bits : s.bits = 0) (last : s.last = 0)
    (empty : z.avail_in = 0) (nonnul : z.next_out ≠ .null) :
    inflate (some r) Z_NO_FLUSH h = .ok (Z_BUF_ERROR, r.put (tmpFreed h) {z with data_type := 0}) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, Z_NO_FLUSH⟩
  let regs := dispatchRegs z s
  let H := syncAlloc h
  have E : Env c H r zs z s := ⟨rfl, rfl, by simpa [H] using live.hz, live.hs⟩
  have active : Live H r zs z s := {live with hz := E.hz, hs := E.hs}
  have short : s.bits < 16 := by rw [bits]; decide
  have run := empty_input_dispatch E head wrapped short empty
  obtain ⟨dt, cast, result⟩ := zero_output_leave (l := regs) E window rfl (by change s.bits.toNat ≤ 39; rw [bits]; decide)
  have code : chkI32 ((u2i regs.bits).toInt + (if s.last != 0 then 64 else 0) +
      (if s.mode == TYPE then 128 else 0) + (if s.mode == LEN_ || s.mode == COPY_ then 256 else 0)) = pure 0 := by
    change chkI32 ((u2i s.bits).toInt + _ + _ + _) = _
    rw [bits, last, head]; rfl
  rw [code] at cast
  have val : dt = 0 := (congrArg Prod.fst (Except.ok.inj (congrFun cast h))).symm
  subst dt
  have leave := result z.next_out
  have fix : r.put H {z with next_out := z.next_out} = H := ZStreamRef.put_self E.hz
  have state : setI (r.put H {z with data_type := 0}) zs s = r.put H {z with data_type := 0} := by
    unfold setI
    rw [upd_self _ _ _ (show (r.put H {z with data_type := 0}).istates zs = some s by simpa using E.hs)]
  have left : inflate_leave c regs H = .ok (Z_BUF_ERROR, r.put H {z with data_type := 0}) := by
    simpa only [regs, dispatchRegs, leaveStream, leaveState, fix, UInt32.sub_self, beq_self_eq_true,
      Bool.true_or, Bool.true_and, show (0 : UInt32).toUInt64 = 0 from rfl, UInt64.add_zero, state, ↓reduceIte] using leave
  have cleared := freeBuf_run (show (r.put H {z with data_type := 0}).bytes h.nextBlk = some (syncJunk h) by
    simpa [H] using syncAlloc_bytes_buf h) (show (r.put H {z with data_type := 0}).ro h.nextBlk = false by
      simpa [H] using syncAlloc_ro_buf h)
  have check : inflateStateCheck (some r) (syncAlloc h) = .ok (0, syncAlloc h) := stateCheck_live active
  have loop : (ExceptT.run (inflate_run c)).run IL.init H = .ok ((.error Ex.leave, regs), H) := run
  have record : ldZStream (some r) (syncAlloc h) = .ok (z, syncAlloc h) := ldZStream_ok E.hz
  have castState : castInflateState z.state (syncAlloc h) = .ok (some (.tab zs), syncAlloc h) := by
    rw [live.zst]; rfl
  dsimp only [H, c, regs, syncBuf] at loop left cleared
  have input : (z.next_in == .null && z.avail_in != 0) = false := by simp [empty]
  unfold inflate
  simp only [bind_app, allocLocalB_run h fresh, check, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, record,
    beq_false_of_ne nonnul, input, Bool.or_self, pure_app, castState, syncBuf, loop, left, cleared]
  change Except.ok (Z_BUF_ERROR, freeWin (r.put (syncAlloc h) {z with data_type := 0}) (syncBuf h)) = _
  rw [← ZStreamRef.put_freeWin]
  rfl

/-- Both imported wrapper loops refill the zero counts, execute one actual
inflate call on the selected address and stop with its buffer error. -/
theorem empty_input_loop (generated : Bool) {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (fresh : Fresh h) (live : Live h r zs z s) (head : s.mode = HEAD) (wrapped : s.wrap ≠ 0)
    (window : s.wsize = 0) (bits : s.bits = 0) (last : s.last = 0)
    (empty : z.avail_in = 0) (full : z.avail_out = 0) (nonnull : z.next_out ≠ .null) :
    cdoWhile (OriginalUncompressLoop.sourceBody generated r) (OriginalUncompressLoop.sourceCond generated)
      ⟨Z_OK, 0, 0⟩ h = .ok (⟨Z_BUF_ERROR, 0, 0⟩, r.put (tmpFreed h) {z with data_type := 0}) := by
  let init : Zlib.Uncompr.UncLoop := ⟨Z_OK, 0, 0⟩
  let done_ : Zlib.Uncompr.UncLoop := ⟨Z_BUF_ERROR, 0, 0⟩
  let H := r.put (tmpFreed h) {z with data_type := 0}
  have call := empty_input_inflate fresh live head wrapped window bits last empty nonnull
  have read : Zlib.Gzguts.ldZ (some r) h = .ok (z, h) := ldZStream_ok live.hz
  have write (f : ZStream → ZStream) (same : f z = z) :
      Zlib.Gzguts.updZ (some r) f h = .ok ((), h) := by
    unfold Zlib.Gzguts.updZ
    rw [bind_app, ldZStream_ok live.hz]
    change stZStream (some r) (f z) h = _
    rw [same, stZStream_ok live.hz (by cases r <;> rfl), ZStreamRef.put_self live.hz]
  have noOut := write (fun cur => {cur with avail_out := 0}) (by rw [←full])
  have noIn := write (fun cur => {cur with avail_in := 0}) (by rw [←empty])
  have body : OriginalUncompressLoop.abiBody (some r) init h = .ok (done_, H) := by
    unfold OriginalUncompressLoop.abiBody
    dsimp only [H, done_]
    simp only [init, bind_app, read, full, empty, beq_self_eq_true, ↓reduceIte,
      show ¬ (0 : UInt64) > (0xffffffff : UInt32).toUInt64 by decide,
      show (0 : UInt64).toUInt32 = 0 from rfl, noOut, noIn, call, pure_app]
    rfl
  rw [OriginalUncompressLoop.loop_eq]
  change cdoWhile.go _ _ (18446744073709551615 + 1) init h = _
  rw [cdoWhile.go, bind_app, body]
  rfl

#print axioms empty_input_loop
#print axioms empty_input_inflate
#print axioms empty_input_dispatch
#print axioms zero_output_leave
end Lean2C.OriginalUncompress
