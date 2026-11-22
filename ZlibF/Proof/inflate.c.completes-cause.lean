import ZlibF.Proof.«inflate.c.meaning-trip-body»
import ZlibF.Proof.«inflate.c.meaning-trip-codes»
import ZlibF.Proof.«inflate.c.meaning-trip-trailer»
import ZlibF.Proof.«inflate.c.meaning-stop-short»
import ZlibF.Proof.«inflate.c.meaning-trip-modes»

/-!
# inflate.c: why a trip of the mode loop leaves (zlib rows)

`TripMeaning` keeps the format meaning at a leave (`LoopMatches`) and drops its cause. The cause
is what `StopShort` needs: a leave for want of input holds bits that do not complete the field
its mode waits for (`LeaveShort`), so a trip that left that way has not read a whole valid stream
(`LoopMatches.starved_not_end`). `TripLeaveCause` names the causes: a code other than `Z_OK` in `ret`
(`DONE` sets `Z_STREAM_END`), a `Z_BLOCK` or `Z_TREES` stop, no output room at the start of the
trip, or no input with `LeaveShort`. `CauseAt` is the cause row of a group of modes, for every
trip from `LoopMatches` that leaves.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The cause of a leave from the trip start registers `l` to the leave registers `l'`, heap `h'`.
The room cause (`left = 0`, holding output) is stated in the leave registers. -/
def TripLeaveCause (c : Ctx) (h' : Heap) (_l l' : IL) : Prop :=
  l'.ret ≠ Z_OK ∨ c.flush = Z_BLOCK ∨ c.flush = Z_TREES ∨ (l'.left = 0 ∧ HoldsOutput c h') ∨
    (l'.have_ = 0 ∧ LeaveShort c h' l') ∨
    ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = LEN_) ∧ l'.bits.toNat < 8)

/-- A leave for want of input, short of the field the mode waits for. -/
theorem TripLeaveCause.short {c : Ctx} {h' : Heap} {l l' : IL}
    (short : l'.have_ = 0 ∧ LeaveShort c h' l') : TripLeaveCause c h' l l' :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl short))))

/-- A leave in `LEN_` with fewer than 8 bits held: the dynamic header is complete (the `Z_TREES`
stop of `CODELENS`). -/
theorem TripLeaveCause.lenStart {c : Ctx} {h' : Heap} {l l' : IL}
    (len : (∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = LEN_) ∧
      l'.bits.toNat < 8) :
    TripLeaveCause c h' l l' :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr len))))

/-- Every trip from a state with `P` that leaves states its cause. -/
def CauseAt (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (P : InflateState → Prop) : Prop :=
  ∀ h l, CallSide c r l h → LoopMatches c f h l →
    (∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → P s) →
    ∀ l' h', runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h') → TripLeaveCause c h' l l'

/-- No room at the trip start leaves no room at its end. -/
theorem left_zero_of_le {l l' : IL} (le : l'.left.toNat ≤ l.left.toNat) (zero : l.left = 0) :
    l'.left = 0 := by
  apply UInt32.toNat_inj.mp
  rw [zero] at le
  simp only [UInt32.toNat_zero] at le ⊢
  omega

theorem TripLeaveCause.of_step {c : Ctx} {h' : Heap} {l l' : IL}
    (step : (l'.have_ = 0 ∧ LeaveShort c h' l') ∨ c.flush = Z_TREES ∨ (l.left = 0 ∧ HoldsOutput c h'))
    (le : l'.left.toNat ≤ l.left.toNat) :
    TripLeaveCause c h' l l' := by
  rcases step with s | s | s
  · exact TripLeaveCause.short s
  · exact Or.inr (Or.inr (Or.inl s))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨left_zero_of_le le s.1, s.2⟩)))

theorem TripLeaveCause.of_short {c : Ctx} {h' : Heap} {l l' : IL}
    (step : (l'.have_ = 0 ∧ LeaveShort c h' l') ∨ (l.left = 0 ∧ HoldsOutput c h'))
    (le : l'.left.toNat ≤ l.left.toNat) :
    TripLeaveCause c h' l l' := by
  rcases step with s | s
  · exact TripLeaveCause.short s
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨left_zero_of_le le s.1, s.2⟩)))

/-- A run that is equal to a known one ends the same way. -/
theorem same_leave {p : X Unit} {l l' l1 : IL} {h h' h1 : Heap} {result : Except Ex Unit}
    (run : runX p l h = .ok ((.error Ex.leave, l'), h')) (run1 : runX p l h = .ok ((result, l1), h1)) :
    result = .error Ex.leave ∧ l1 = l' ∧ h1 = h' := by
  have same := run1.symm.trans run
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  exact ⟨same.1.1, same.1.2, same.2⟩

/-- `left` only decreases in a trip. -/
theorem trip_left_le {c : Ctx} {r : ZStreamRef} {l l' : IL} {h h' : Heap} {outcome : Except Ex Unit}
    (side : CallSide c r l h) (run : runX (inflate_dispatch c) l h = .ok ((outcome, l'), h')) :
    l'.left.toNat ≤ l.left.toNat := by
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, loc, bits, _⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  obtain ⟨outcome2, regs, after, _, _, _, made, _, run2, _, _, _, _, _, _, leftEq, _⟩ :=
    inflate_dispatch_default_view_state_rank E j buf loc bits
  have same := run.symm.trans run2
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨⟨_, rfl⟩, rfl⟩ := same
  omega

/-- Stored blocks (`STORED`, `COPY_`, `COPY`). -/
theorem cause_stored (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) := by
  intro h l side loop mode l' h' run
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) E.st E.hs
    (window_bounds j.good.inv.win)
  rcases mode zs s E.st E.hs with m | m | m
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningBlock.stored_step loop E.strm E.hz (at_state (P := fun s => s.mode = STORED) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_STORED E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · exact TripLeaveCause.of_step cause (trip_left_le side run)
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningCopy.copy_start_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY_) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_COPY_start E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · exact TripLeaveCause.of_short cause (trip_left_le side run)
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ :=
      MeaningCopy.copy_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY) E.st E.hs m)
        bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_COPY E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · exact TripLeaveCause.of_short cause (trip_left_le side run)
    · rw [e] at e'; cases e'

/-- `TYPE`/`TYPEDO` before the last block. -/
theorem cause_type_open (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) := by
  intro h l side loop mode l' h' run
  obtain ⟨zs, z, s, E, j⟩ := side.env
  obtain ⟨m, _⟩ := mode zs s E.st E.hs
  rcases m with m | m
  · obtain ⟨result, l1, h1, run1, ends⟩ := MeaningBlock.type_step loop E.strm E.hz j.globals mode
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_TYPE E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s | s
      · exact TripLeaveCause.short s
      · exact Or.inr (Or.inl s)
      · exact Or.inr (Or.inr (Or.inl s))
    · rw [e] at e'; cases e'
  · obtain ⟨result, l1, h1, run1, ends⟩ := MeaningBlock.typedo_step loop E.strm E.hz j.globals mode
    obtain ⟨e, rfl, rfl⟩ := same_leave run ((inflate_dispatch_TYPEDO E l m).trans run1)
    rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
    · rcases cause with s | s
      · exact TripLeaveCause.short s
      · exact Or.inr (Or.inr (Or.inl s))
    · rw [e] at e'; cases e'

/-- `DONE`: `Z_STREAM_END` in `ret`. -/
theorem cause_done (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = DONE) := by
  intro h l side _ mode l' h' run
  obtain ⟨zs, z, s, E, _⟩ := side.env
  have run1 := (inflate_dispatch_DONE E l (mode zs s E.st E.hs)).trans (inflate_DONE_run c l h)
  obtain ⟨_, rfl, rfl⟩ := same_leave run run1
  exact Or.inl (show Z_STREAM_END ≠ Z_OK by decide)

/-- The cause from the ends of a decode step. -/
theorem cause_of_ends {c : Ctx} {f : LoopFrame} {h' : Heap} {l l' : IL} {result : Except Ex Unit}
    {B : Prop}
    (ends : (result = .error Ex.leave ∧ ((l'.have_ = 0 ∧ LeaveShort c h' l') ∨ (l.left = 0 ∧ HoldsOutput c h')) ∧
        LoopMatches c f h' l') ∨
      (result = .ok () ∧ B)) (leave : result = .error Ex.leave) (le : l'.left.toNat ≤ l.left.toNat) :
    TripLeaveCause c h' l l' := by
  rcases ends with ⟨_, cause, _⟩ | ⟨e, _⟩
  · exact TripLeaveCause.of_short cause le
  · rw [leave] at e; cases e

open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningMatch
open Zlib.Inflate.Proofs.MeaningDistance Zlib.Inflate.Proofs.MeaningLength in
/-- The Huffman codes (`LEN_` to `LIT`). -/
theorem cause_codes (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => LEN_ ≤ s.mode ∧ s.mode ≤ LIT) := by
  intro h l side loop mode l' h' leaveRun
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, _, _⟩ := id side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  have m0 := mode zs s st E.hs
  have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) st E.hs
    (window_bounds j.good.inv.win)
  have sane := at_state (P := fun s => s.sane ≠ 0) st E.hs (by rw [j.pending.sane]; decide)
  have wsizeBits := at_state (P := fun s => s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    st E.hs (code_wsize_bits j.good.inv.win)
  have ring := at_state (P := fun s => s.whave < s.wsize → s.wnext = s.whave) st E.hs
    (code_ring j.good.inv.win)
  have privateWindow := at_state
    (P := fun s => ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d) st E.hs
    (code_private_window j.good buf)
  have rawWidth := code_raw_width j st E.hs loop
  have binv : BitInv h l (f.inp.drop (loopRead l)) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, binv, _⟩ := loop
    exact binv
  have buffers : DispatchBuffers h r l (f.inp.drop (loopRead l)) :=
    ⟨buf.input, buf.output, buf.separate, binv⟩
  have tablesAt : DataTableMode s.mode → ∀ zs' s', c.st = some (.tab zs') →
      h.istates zs' = some s' → DataTablesSafe h s' :=
    fun dm => at_state (P := fun s => DataTablesSafe h s) st E.hs (j.tables dm)
  rcases code_mode_cases m0 with m | m | m | m | m | m | m
  · -- LEN_
    by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
    · obtain ⟨l1, h1, run, _⟩ := len_start_fast loop E j buffers m fast rawWidth
      obtain ⟨e, _, _⟩ := same_leave leaveRun ((inflate_dispatch_LEN_start E l m).trans run)
      cases e
    · obtain ⟨result, l1, h1, run, ends⟩ := len__step loop E.strm E.hz fast
        (at_state (P := fun s => s.mode = LEN_) st E.hs m)
        (tablesAt (by rw [m]; unfold DataTableMode; decide))
        bounds sane wsizeBits ring privateWindow rawWidth
      obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LEN_start E l m).trans run)
      exact cause_of_ends ends e (trip_left_le side leaveRun)
  · -- LEN
    by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
    · obtain ⟨l1, h1, run, _, _⟩ := fast_len_meaning _ _ _ _ _ _ loop E.strm E.hz fast
        (at_state_id (P := fun zs s => s.mode = LEN ∧ Good h r zs z s ∧ DataTablesSafe h s ∧
          DataPendingInvariant s) st E.hs
          ⟨m, j.good, j.tables (by rw [m]; unfold DataTableMode; decide), j.pending⟩)
        j.platform buffers rawWidth
      obtain ⟨e, _, _⟩ := same_leave leaveRun ((inflate_dispatch_LEN E l m).trans run)
      cases e
    · obtain ⟨result, l1, h1, run, ends⟩ := len_slow_step loop E.strm E.hz fast
        (at_state (P := fun s => s.mode = LEN ∨ s.mode = LEN_) st E.hs (Or.inl m))
        (tablesAt (by rw [m]; unfold DataTableMode; decide))
        bounds sane wsizeBits ring privateWindow rawWidth
      obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LEN E l m).trans run)
      exact cause_of_ends ends e (trip_left_le side leaveRun)
  · -- LENEXT
    obtain ⟨result, l1, h1, run, ends⟩ := lenext_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = LENEXT) st E.hs m)
      (tablesAt (by rw [m]; unfold DataTableMode; decide))
      (at_state (P := fun s => BackBound s 15) st E.hs (j.pending.lenext m).2.2.2)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LENEXT E l m).trans run)
    exact cause_of_ends ends e (trip_left_le side leaveRun)
  · -- DIST
    obtain ⟨result, l1, h1, run, ends⟩ := dist_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = DIST) st E.hs m)
      (tablesAt (by rw [m]; unfold DataTableMode; decide))
      (at_state (P := fun s => BackBound s 20) st E.hs (j.pending.dist m).2)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_DIST E l m).trans run)
    exact cause_of_ends ends e (trip_left_le side leaveRun)
  · -- DISTEXT
    obtain ⟨result, l1, h1, run, ends⟩ := distext_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = DISTEXT) st E.hs m)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_DISTEXT E l m).trans run)
    exact cause_of_ends ends e (trip_left_le side leaveRun)
  · -- MATCH
    obtain ⟨result, l1, h1, run, ends⟩ := match_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = MATCH) st E.hs m)
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_MATCH E l m).trans run)
    rcases ends with ⟨_, left, rfl, rfl⟩ | ⟨e', _⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨left, HoldsOutput.of_state st E.hs (Or.inr (Or.inl m))⟩)))
    · rw [e] at e'; cases e'
  · -- LIT
    obtain ⟨result, l1, h1, run, ends⟩ := lit_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = LIT) st E.hs m) bounds
    obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun ((inflate_dispatch_LIT E l m).trans run)
    rcases ends with ⟨_, left, rfl, rfl⟩ | ⟨e', _⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨left, HoldsOutput.of_state st E.hs (Or.inl m)⟩)))
    · rw [e] at e'; cases e'

open MeaningCheck MeaningTrailer in
/-- `CHECK` of a zlib stream: the only leave with `ret = Z_OK` is its `NEEDBITS(32)`; past it
`LENGTH` (no length field: `flags = 0`) ends the stream with `Z_STREAM_END`. -/
theorem cause_check_zlib (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (zlib : f.wrap = .zlib) :
    CauseAt c f r (fun s => s.mode = CHECK) := by
  intro h l side loop check l' h' leaveRun
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    have globals := j.globals
    unfold LibraryGlobals at globals
    rw [Zlib.Crc32.Proofs.StaticsOK, globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨zs0, s0, callOut0, consumed0, held0, stage0, st, hs, _, config0, _, _, binv0, leftLe0, pend0,
    putEq0, outBytes0, _, _, _, _, bitsEq0, heldBits0, parsed0, stageM0, wrapM0, _⟩ := loop
  have e0 : zs0 = zs := by rw [E.st] at st; cases st; rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs.symm.trans E.hs)
  subst e1
  have mode : s0.mode = CHECK := check zs0 s0 st hs
  obtain ⟨header0, out0, bytes0, rfl⟩ := stage_of_check stageM0 mode
  obtain ⟨flagsM, _, ⟨checkFacts0, _, _⟩⟩ := wrapM0
  have wrapped : f.wrap ≠ .raw := by rw [zlib]; decide
  have wrapNZ : s0.wrap ≠ 0 := fun zero => wrapped (wrapCode_zero (config0.1.symm.trans zero))
  have notGzip : ¬ IsGzipHeader header0 := by
    obtain ⟨_, _, _, wh, _⟩ := parsed0
    rw [zlib] at wh
    obtain ⟨window, zh, _⟩ := wh
    exact zlibHeader_not_gzip zh
  have flags0 : s0.flags = 0 := by
    unfold FlagsMatch at flagsM
    rw [zlib] at flagsM
    simpa [notGzip, loopState] using flagsM
  have outNat : (l.out_ - l.left).toNat = loopPending l :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr leftLe0)
  have putAt : chkCond s0 (l.out_ - l.left) = true → ∃ ref off array, l.put = .ref ref off ∧
      Space.get h ref = some array ∧ (l.out_ - l.left).toNat ≤ off ∧ off ≤ array.size := by
    intro cond
    have nonzero : (l.out_ - l.left) ≠ 0 := by
      simp only [chkCond, Bool.and_eq_true, bne_iff_ne, ne_eq] at cond
      exact cond.2
    have pos : 0 < (l.out_ - l.left).toNat :=
      Nat.pos_of_ne_zero (fun zero => nonzero (UInt32.toNat_inj.mp (by simpa using zero)))
    rcases outBytes0 with ⟨_, len0, _⟩ | ⟨r0, i0, a0, ptr0, get0, fit0, _⟩
    · have := pend0.1
      omega
    · refine ⟨r0, i0 + callOut0.length, a0, by rw [putEq0, ptr0]; rfl, get0, ?_, fit0⟩
      have := pend0.1
      omega
  obtain ⟨rr, l1, _, needRun, _, _, _, leaveRun1, okRun⟩ :=
    inflate_CHECK_value_run (l.out_ - l.left) rfl E.strm st E.hz hs wrapNZ binv0 statics putAt
  have rrKinds : rr = .ok () ∨ rr = .error Ex.leave := by
    obtain ⟨result, l2, _, run2, _, _, _, _, _, _, _, _, _, kinds, _⟩ :=
      NEEDBITS_run_cursor binv0 32 (by decide)
    have same := needRun.symm.trans run2
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    rw [same.1.1]
    exact kinds
  have dispatchEq := inflate_dispatch_CHECK E l mode
  cases rr with
  | error x =>
    cases x with
    | leave =>
      obtain ⟨have0, _, bits32, run1⟩ := leaveRun1 rfl
      obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun (dispatchEq.trans run1)
      refine TripLeaveCause.short ⟨have0, LeaveShort.of_state st hs ?_⟩
      have len : (natBits l1.bits.toNat l1.hold.toNat).length < 32 := by
        rw [natBits_length]; exact bits32
      unfold ShortAt
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨mode, wrapNZ, len⟩)))))))))))))
    | ret v => rcases rrKinds with e | e <;> cases e
  | ok u =>
    obtain ⟨_, v, _, badRun, matchRun⟩ := okRun rfl
    by_cases bad : (s0.wrap &&& 4) ≠ 0 ∧
        (if s0.flags ≠ 0 then l1.hold else ZSWAP32 l1.hold) ≠ (chkS s0 (l.out_ - l.left) v).check
    · obtain ⟨i, _, run1⟩ := badRun bad.1 bad.2
      obtain ⟨e, _, _⟩ := same_leave leaveRun (dispatchEq.trans run1)
      cases e
    · have run1 := matchRun bad
      have skip := inflate_LENGTH_skip (c := c)
        (l := { l1 with out_ := l.left, hold := 0, bits := 0 }) st
        (s := { chkS s0 (l.out_ - l.left) v with mode := LENGTH })
        (h := setI (chkH h r zs0 z s0 (l.out_ - l.left) v) zs0
          { chkS s0 (l.out_ - l.left) v with mode := LENGTH })
        (setI_istates_same _ _ _) (Or.inr (by simp [chkS, flags0]))
      obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun ((dispatchEq.trans run1).trans skip)
      exact Or.inl (show Z_STREAM_END ≠ Z_OK by decide)

/-- The leave that ends the mode loop of a wrapped stream has a cause in the trip it ends. -/
theorem loop_cause {c : Ctx} {f : LoopFrame} {r : ZStreamRef}
    (trip : TripMeaning c f (CallSide c r)) (_rawTrip : RawCheckTrip c f (CallSide c r))
    (cause : ∀ h l, CallSide c r l h → LoopMatches c f h l →
      ∀ l' h', runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h') → TripLeaveCause c h' l l')
    (wrapped : f.wrap ≠ .raw) (strm : c.strm = some r)
    {l regs : IL} {h after : Heap}
    (side : CallSide c r l h) (start : LoopMatches c f h l ∨ LoopBad c f h l)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave, regs), after)) :
    ∃ l0, TripLeaveCause c after l0 regs ∧ regs.left.toNat ≤ l0.left.toNat := by
  let P : IL → Heap → Prop := fun l h =>
    CallSide c r l h ∧ ((LoopMatches c f h l ∨ LoopBad c f h l) ∨ RawCheck c f h l)
  let Q : Ex → IL → Heap → Prop := fun e regs after =>
    e = .leave → ∃ l0, TripLeaveCause c after l0 regs ∧ regs.left.toNat ≤ l0.left.toNat
  have kept := side_kept c r
  have step : ∀ l h outcome regs after, P l h →
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) →
      match outcome with
      | .ok () => P regs after
      | .error exit => Q exit regs after := by
    intro l h outcome regs after ⟨side, current⟩ source
    have leftLe := trip_left_le side source
    rcases current with (loop | bad) | raw
    · obtain ⟨result, l', h', run', outcome'⟩ := trip h l side loop
      have same := source.symm.trans run'
      simp only [Except.ok.injEq, Prod.mk.injEq] at same
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
      cases outcome with
      | ok u =>
        cases u
        rcases outcome' with tripOut | needDict | ⟨_, raw'⟩
        · rcases tripOut with ⟨_, cont⟩ | ⟨e, _⟩
          · exact ⟨kept l h regs after side source, Or.inl cont⟩
          · cases e
        · obtain ⟨e, _⟩ := needDict
          cases e
        · exact ⟨kept l h regs after side source, Or.inr raw'⟩
      | error exit =>
        intro e
        subst e
        exact ⟨l, cause h l side loop regs after source, leftLe⟩
    · obtain ⟨z, hz⟩ := side.record
      obtain ⟨run', _⟩ := bad_trip bad strm hz
      have same := source.symm.trans run'
      simp only [Except.ok.injEq, Prod.mk.injEq] at same
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
      intro _
      exact ⟨l, Or.inl (show Z_DATA_ERROR ≠ Z_OK by decide), leftLe⟩
    · exact absurd raw.1 wrapped
  exact xwhile_success_control_post P Q step ⟨side, Or.inl start⟩ run rfl

/-- The cause rows of a zlib call that `cause_zlib` takes as premises (`zlib_cause_rows`,
`inflate.c.completes-cause-zlib`, proves them): the header rows (`HEAD`,
`DICTID`, `DICT`), the boundary after the last block, the dynamic header and `LENGTH`. -/
structure ZlibCauseRows : Prop where
  head : ∀ c f r, f.wrap = .zlib → CauseAt c f r (fun s => s.mode = HEAD)
  dictid : ∀ c f r, f.wrap = .zlib → CauseAt c f r (fun s => s.mode = DICTID)
  dict : ∀ c f r, f.wrap = .zlib → CauseAt c f r (fun s => s.mode = DICT)
  typeFinal : ∀ c f r, f.wrap = .zlib →
    CauseAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0)
  dynamic : ∀ c f r, CauseAt c f r (fun s => s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)
  length : ∀ c f r, f.wrap = .zlib → CauseAt c f r (fun s => s.mode = LENGTH)

/-- Every trip of a zlib call that leaves states its cause. -/
theorem cause_zlib (rows : ZlibCauseRows) (c : Ctx) (f : LoopFrame) (r : ZStreamRef)
    (zlib : f.wrap = .zlib) :
    ∀ h l, CallSide c r l h → LoopMatches c f h l →
      ∀ l' h', runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h') →
        TripLeaveCause c h' l l' := by
  intro h l side loop
  obtain ⟨zs, s, st, hs, mode⟩ := loop_mode_cases c f h l loop
  rcases mode with m | m | m | m | m | m | m | m | m | m | m | m
  · exact rows.head c f r zlib h l side loop (at_state (P := fun s => s.mode = HEAD) st hs m)
  · exact absurd m (gzip_fields_absent c f r h l side loop (Or.inl zlib) zs s st hs)
  · exact rows.dictid c f r zlib h l side loop (at_state (P := fun s => s.mode = DICTID) st hs m)
  · exact rows.dict c f r zlib h l side loop (at_state (P := fun s => s.mode = DICT) st hs m)
  · exact cause_type_open c f r h l side loop
      (at_state (P := fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) st hs m)
  · exact rows.typeFinal c f r zlib h l side loop
      (at_state (P := fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0) st hs m)
  · exact cause_stored c f r h l side loop
      (at_state (P := fun s => s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) st hs m)
  · exact rows.dynamic c f r h l side loop
      (at_state (P := fun s => s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) st hs m)
  · exact cause_codes c f r h l side loop
      (at_state (P := fun s => LEN_ ≤ s.mode ∧ s.mode ≤ LIT) st hs m)
  · exact cause_check_zlib c f r zlib h l side loop (at_state (P := fun s => s.mode = CHECK) st hs m)
  · exact rows.length c f r zlib h l side loop (at_state (P := fun s => s.mode = LENGTH) st hs m)
  · exact cause_done c f r h l side loop (at_state (P := fun s => s.mode = DONE) st hs m)

end Zlib.Inflate.Proofs
