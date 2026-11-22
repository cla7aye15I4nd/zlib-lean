import ZlibF.Proof.«inflate.c.meaning-trip-body»
import ZlibF.Proof.«inflate.c.meaning-fast»
import ZlibF.Proof.«inflate.c.pending-dispatch»
import ZlibF.Proof.«inflate.c.fast-view-caller-start»
import ZlibF.Proof.«inflate.c.meaning-trip-dynamic»

/-!
# inflate.c: the code modes `LEN_`..`LIT` (`TripCodes`) and the fast `LEN` step on byte views

Each code mode is its per-mode step behind its dispatch equation: `len__step` and
`len_slow_step` (slow `LEN_`, `LEN`), `fast_call_meaning` (fast `LEN`), `lenext_step`,
`dist_step`, `distext_step`, `match_step` and `lit_step`. `body_outcome` turns the ends into a
`TripOutcome`. The premises of the steps come from `CallSide` and `LoopMatches`. The fast call
takes input and output in any byte view the dispatch packet admits (`DispatchBuffers.fast_views`).
That fast step is `fast_len_meaning : FastLenMeaning`; it also closes the dynamic header row
(`trip_dynamic`, through `trip_dynamic_of`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningMatch
open Zlib.Inflate.Proofs.MeaningDistance Zlib.Inflate.Proofs.MeaningLength
set_option autoImplicit false

/-- The fast `case LEN` call: `fast_call_meaning` on the byte views of the dispatch packet. -/
theorem fast_len {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (state : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.mode = LEN ∧ Good h r zs z s ∧ DataTablesSafe h s ∧ DataPendingInvariant s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (buffers : DispatchBuffers h r l (f.inp.drop (loopRead l)))
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ l' h', runX (inflate_LEN c) l h = .ok ((.ok (), l'), h') ∧ loopRead l ≤ loopRead l' ∧
      (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l')) := by
  obtain ⟨zs, s, _, _, _, _, st, hs, _⟩ := id loop
  have good := (state zs s st hs).2.1
  obtain ⟨inRef, outRef, _, _, io, oo, input, _, _, _, _, output, _⟩ := buffers.fast_views good fit fast
  exact MeaningFast.fast_call_meaning loop strm hz fast state fit buffers input output rawWidth

/-- `FastLenMeaning`: the fast `case LEN` call keeps the format meaning for every caller byte
view of input and output. -/
theorem fast_len_meaning : MeaningLenEntry.FastLenMeaning :=
  fun _ _ _ _ _ _ loop strm hz fast state fit buffers rawWidth =>
    fast_len loop strm hz fast state fit buffers rawWidth

/-! ## Premises of the steps -/

/-- `at_state` for a fact that also names the state's record number. -/
theorem at_state_id {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {P : Nat → InflateState → Prop}
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s) (p : P zs s) :
    ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' → P zs' s' := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  rw [hs] at hs'
  cases hs'
  exact p

theorem code_wsize_bits {h : Heap} {s : InflateState} (w : WinInv h s) :
    s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat := by
  intro ne
  rcases w.ws with zero | e
  · exact absurd (UInt32.toNat_inj.mp (by rw [zero]; rfl)) ne
  · exact e

theorem code_ring {h : Heap} {s : InflateState} (w : WinInv h s) :
    s.whave < s.wsize → s.wnext = s.whave := by
  intro lt
  exact UInt32.toNat_inj.mp (w.eq (UInt32.lt_iff_toNat_lt.mp lt))

/-- The window is a stream-owned block; the caller's output range has no stream-owned root. -/
theorem code_private_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l : IL} {bs : List UInt8}
    (good : Good h r zs z s) (buf : DispatchBuffers h r l bs) :
    ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d := by
  intro w o d i win put same
  rcases good.inv.win.block with null | ⟨b, a, win', _, _, _⟩
  · rw [win] at null
    cases null
  · rw [win] at win'
    cases win'
    exact callerRange_private_window good buf.output.range put b win same.symm

/-- A raw configuration has a nonzero width: the wrapper code is 0, the requested wrapper is the
wrapper, and a raw request has a nonzero requested width (`RequestedBitsOK`). -/
theorem code_raw_width {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (j : DefaultStateJ h r zs z s)
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s) (loop : LoopMatches c f h l) :
    f.wrap = .raw → f.configured ≠ 0 := by
  intro raw
  obtain ⟨zs0, s0, _, _, _, _, st0, hs0, _, config, _⟩ := loop
  have e0 : zs0 = zs := by
    rw [st] at st0
    cases st0
    rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs0.symm.trans hs)
  subst e1
  obtain ⟨c1, c2, _, c4, _, _⟩ := config
  have wrap0 : s0.wrap = 0 := by
    have w := c1
    rw [raw] at w
    exact w
  have req : s0.reqwrap = 0 := c2.trans wrap0
  have bits := j.requestedBits.2 req
  intro zero
  apply bits
  apply UInt32.toNat_inj.mp
  have e : s0.reqbits.toNat = f.configured := c4
  rw [e, zero]
  rfl

/-- The seven code modes. -/
theorem code_mode_cases {m : UInt32} (range : LEN_ ≤ m ∧ m ≤ LIT) :
    m = LEN_ ∨ m = LEN ∨ m = LENEXT ∨ m = DIST ∨ m = DISTEXT ∨ m = MATCH ∨ m = LIT := by
  have lo := UInt32.le_iff_toNat_le.mp range.1
  have hi := UInt32.le_iff_toNat_le.mp range.2
  have lo' : LEN_.toNat = 16199 := rfl
  have hi' : LIT.toNat = 16205 := rfl
  have cases : m.toNat = 16199 ∨ m.toNat = 16200 ∨ m.toNat = 16201 ∨ m.toNat = 16202 ∨
      m.toNat = 16203 ∨ m.toNat = 16204 ∨ m.toNat = 16205 := by omega
  rcases cases with k | k | k | k | k | k | k
  · exact Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))
  · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))
  · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by rw [k]; rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by rw [k]; rfl)))))))

/-! ## End shapes -/

/-- The end of a decoding step (`LEN`, `LENEXT`, `DIST`, `DISTEXT`) in the form of `body_outcome`. -/
theorem decode_ends {c : Ctx} {f : LoopFrame} {h' : Heap} {l' : IL} {result : Except Ex Unit}
    {A B : Prop}
    (ends : (result = .error Ex.leave ∧ A ∧ LoopMatches c f h' l') ∨
      (result = .ok () ∧ B ∧ (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l')))) :
    (result = .error Ex.leave ∧ LoopMatches c f h' l') ∨
      (result = .ok () ∧ (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l'))) := by
  rcases ends with ⟨e, _, m⟩ | ⟨e, _, rest⟩
  · exact Or.inl ⟨e, m⟩
  · exact Or.inr ⟨e, rest⟩

/-- The end of `MATCH` in the form of `body_outcome`: the leave keeps the start. -/
theorem match_ends {c : Ctx} {f : LoopFrame} {h h' : Heap} {l l' : IL} {result : Except Ex Unit}
    {B : Prop} (loop : LoopMatches c f h l)
    (ends : (result = .error Ex.leave ∧ l.left = 0 ∧ l' = l ∧ h' = h) ∨
      (result = .ok () ∧ B ∧ (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l')))) :
    (result = .error Ex.leave ∧ LoopMatches c f h' l') ∨
      (result = .ok () ∧ (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l'))) := by
  rcases ends with ⟨e, _, rfl, rfl⟩ | ⟨e, _, rest⟩
  · exact Or.inl ⟨e, loop⟩
  · exact Or.inr ⟨e, rest⟩

/-! ## `LEN_` on the fast branch -/

/-- `case LEN_` sets `LEN`: the loop facts carry over (as in `len__step`). -/
theorem loop_len_start {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat}
    {s : InflateState} (loop : LoopMatches c f h l) (st : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (mode : s.mode = LEN_) :
    LoopMatches c f (setI h zs { s with mode := LEN }) l := by
  obtain ⟨zs0, s0, callOut, consumed, held, stage, st0, hs0, retOk, config, haveLe, inLen, binv,
    leftLe, pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  have e0 : zs0 = zs := by
    rw [st] at st0
    cases st0
    rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs0.symm.trans hs)
  subst e1
  obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len stageM (Or.inr mode)
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _, p7⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  exact loop_move (s' := { s0 with mode := LEN }) (l' := l) (j := 0)
    (pos := ⟨out, final, .codes L D .none⟩) st retOk
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LEN ≠ SYNC by decide⟩
    haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
    ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) (inputAdvance_zero l.next).symm binv bitsEq
    (HeldBits.of_natBits (s := loopState { s0 with mode := LEN } l) binv.hold_lt) wrapHeader
    consumedEq deflate
    ⟨last, table_setI (s' := { s0 with mode := LEN }) hs rfl lenTable,
      table_setI (s' := { s0 with mode := LEN }) hs rfl distTable, Or.inr rfl, p7⟩
    (window_transfer (s := loopState s0 l) (s' := loopState { s0 with mode := LEN } l) rfl rfl rfl rfl
      (fun q => byte_view_get_setI h zs0 _ q) window) check wrapM outputEq

/-- `case LEN_` on the fast branch: set `LEN`, then the fast call. The decoder invariant after
the mode write is that of `inflate_LEN_start_fast_view_state_run`. -/
theorem len_start_fast {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l (f.inp.drop (loopRead l))) (mode : s.mode = LEN_)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ l' h', runX (inflate_LEN_ c) l h = .ok ((.ok (), l'), h') ∧
      (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l')) := by
  let current := { s with mode := LEN }
  let heap := setI h zs current
  have frame : DecodeStateFrame s current := rfl
  have good := invariant.good.decode_update frame
    (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
  have oldMode : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
  have tables := (invariant.tables oldMode).decode_update invariant.good.live.hs frame
  have pending : DataPendingInvariant current := by
    apply dataPendingInvariant_idle (s := current) invariant.pending.sane
    change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
    decide
  have decoded := invariant.toDefaultDecodeJ.decode_update good (fun _ => tables)
    pending frame
    (by change DataExitMode LEN; exact Or.inl (by unfold DataTableMode; decide))
    (byte_view_sizes_setI h zs current) rfl
  have currentJ : DefaultStateJ heap r zs z current :=
    ⟨decoded, invariant.requestedBits, invariant.requestedWrap,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (invariant.data_format oldMode)))))⟩
  have packet : DispatchBuffers heap r l (f.inp.drop (loopRead l)) :=
    buffers.byte_views invariant.good good rfl
      (byte_view_get_setI h zs current) (byte_view_ro_setI h zs current)
  have loop1 : LoopMatches c f heap l := loop_len_start loop E.st E.hs mode
  obtain ⟨l', h', run, _, rest⟩ := fast_len_meaning _ _ _ _ _ _ loop1 E.strm currentJ.good.live.hz fast
    (at_state_id (P := fun zs s => s.mode = LEN ∧ Good heap r zs z s ∧ DataTablesSafe heap s ∧
      DataPendingInvariant s) E.st (setI_istates_same h zs current)
      ⟨rfl, currentJ.good, currentJ.tables (by change DataTableMode LEN; unfold DataTableMode; decide),
        currentJ.pending⟩)
    currentJ.platform packet rawWidth
  exact ⟨l', h', (len__run E l).trans run, rest⟩

/-! ## The row -/

/-- The code modes keep the format meaning. -/
theorem trip_codes : TripCodes := by
  intro c f r h l side loop mode
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
  have body := at_state (P := fun s => TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨
    s.mode = LENGTH) st E.hs
    (Or.inl ⟨UInt32.le_iff_toNat_le.mpr (Nat.le_trans (by decide) (UInt32.le_iff_toNat_le.mp m0.1)),
      m0.2⟩)
  have tablesAt : DataTableMode s.mode → ∀ zs' s', c.st = some (.tab zs') →
      h.istates zs' = some s' → DataTablesSafe h s' :=
    fun dm => at_state (P := fun s => DataTablesSafe h s) st E.hs (j.tables dm)
  rcases code_mode_cases m0 with m | m | m | m | m | m | m
  · -- LEN_
    by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
    · obtain ⟨l', h', run, rest⟩ := len_start_fast loop E j buffers m fast rawWidth
      have run' := (inflate_dispatch_LEN_start E l m).trans run
      exact ⟨_, l', h', run', Or.inl (body_outcome side loop body run' (Or.inr ⟨rfl, rest⟩))⟩
    · obtain ⟨result, l', h', run, ends⟩ := len__step loop E.strm E.hz fast
        (at_state (P := fun s => s.mode = LEN_) st E.hs m)
        (tablesAt (by rw [m]; unfold DataTableMode; decide))
        bounds sane wsizeBits ring privateWindow rawWidth
      have run' := (inflate_dispatch_LEN_start E l m).trans run
      exact ⟨result, l', h', run', Or.inl (body_outcome side loop body run' (decode_ends ends))⟩
  · -- LEN
    by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
    · obtain ⟨l', h', run, _, rest⟩ := fast_len_meaning _ _ _ _ _ _ loop E.strm E.hz fast
        (at_state_id (P := fun zs s => s.mode = LEN ∧ Good h r zs z s ∧ DataTablesSafe h s ∧
          DataPendingInvariant s) st E.hs
          ⟨m, j.good, j.tables (by rw [m]; unfold DataTableMode; decide), j.pending⟩)
        j.platform buffers rawWidth
      have run' := (inflate_dispatch_LEN E l m).trans run
      exact ⟨_, l', h', run', Or.inl (body_outcome side loop body run' (Or.inr ⟨rfl, rest⟩))⟩
    · obtain ⟨result, l', h', run, ends⟩ := len_slow_step loop E.strm E.hz fast
        (at_state (P := fun s => s.mode = LEN ∨ s.mode = LEN_) st E.hs (Or.inl m))
        (tablesAt (by rw [m]; unfold DataTableMode; decide))
        bounds sane wsizeBits ring privateWindow rawWidth
      have run' := (inflate_dispatch_LEN E l m).trans run
      exact ⟨result, l', h', run', Or.inl (body_outcome side loop body run' (decode_ends ends))⟩
  · -- LENEXT
    obtain ⟨result, l', h', run, ends⟩ := lenext_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = LENEXT) st E.hs m)
      (tablesAt (by rw [m]; unfold DataTableMode; decide))
      (at_state (P := fun s => BackBound s 15) st E.hs (j.pending.lenext m).2.2.2)
      bounds sane wsizeBits ring privateWindow rawWidth
    have run' := (inflate_dispatch_LENEXT E l m).trans run
    exact ⟨result, l', h', run', Or.inl (body_outcome side loop body run' (decode_ends ends))⟩
  · -- DIST
    obtain ⟨result, l', h', run, ends⟩ := dist_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = DIST) st E.hs m)
      (tablesAt (by rw [m]; unfold DataTableMode; decide))
      (at_state (P := fun s => BackBound s 20) st E.hs (j.pending.dist m).2)
      bounds sane wsizeBits ring privateWindow rawWidth
    have run' := (inflate_dispatch_DIST E l m).trans run
    exact ⟨result, l', h', run', Or.inl (body_outcome side loop body run' (decode_ends ends))⟩
  · -- DISTEXT
    obtain ⟨result, l', h', run, ends⟩ := distext_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = DISTEXT) st E.hs m)
      bounds sane wsizeBits ring privateWindow rawWidth
    have run' := (inflate_dispatch_DISTEXT E l m).trans run
    exact ⟨result, l', h', run', Or.inl (body_outcome side loop body run' (decode_ends ends))⟩
  · -- MATCH
    obtain ⟨result, l', h', run, ends⟩ := match_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = MATCH) st E.hs m)
      bounds sane wsizeBits ring privateWindow rawWidth
    have run' := (inflate_dispatch_MATCH E l m).trans run
    exact ⟨result, l', h', run', Or.inl (body_outcome side loop body run' (match_ends loop ends))⟩
  · -- LIT
    obtain ⟨result, l', h', run, ends⟩ := lit_step loop E.strm E.hz
      (at_state (P := fun s => s.mode = LIT) st E.hs m) bounds
    have run' := (inflate_dispatch_LIT E l m).trans run
    refine ⟨result, l', h', run', Or.inl (body_outcome side loop body run' ?_)⟩
    rcases ends with ⟨e, _, rfl, rfl⟩ | ⟨e, _, m'⟩
    · exact Or.inl ⟨e, loop⟩
    · exact Or.inr ⟨e, Or.inl m'⟩

/-- The dynamic header row, from the fast `case LEN` call on every byte view. -/
theorem trip_dynamic : TripDynamic := MeaningTripDynamic.trip_dynamic_of fast_len_meaning

#print axioms fast_len_meaning
#print axioms len_start_fast
#print axioms trip_codes
#print axioms trip_dynamic

end Zlib.Inflate.Proofs
