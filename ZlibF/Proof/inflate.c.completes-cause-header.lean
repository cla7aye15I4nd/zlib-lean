import ZlibF.Proof.«inflate.c.completes-cause»
import ZlibF.Proof.«inflate.c.meaning-head-zlib»
import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.dictid-dispatch»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»
import ZlibF.Proof.«inflate.c.meaning-dict-trip»
import ZlibF.Proof.«inflate.c.meaning-type-final»

/-!
# inflate.c: why the header trips of a zlib call leave

The cause rows of `ZlibCauseRows` for the zlib header, from the run of the actual header code:
`HEAD` leaves only in its `NEEDBITS(16)`, short of the two header bytes; after them the header
checks end the trip normally (`headDefaultCheck_default_state`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningHeadZlib
set_option autoImplicit false

/-- `HEAD` of a zlib stream. -/
theorem cause_head_zlib (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (zlib : f.wrap = .zlib) :
    CauseAt c f r (fun s => s.mode = HEAD) := by
  intro h l side loop head l' h' leaveRun
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, _, _, _⟩ := id side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  have mode : s.mode = HEAD := head zs s st E.hs
  obtain ⟨wrap5, headNone, _, _⟩ := zlib_head_entry loop st E.hs mode zlib
  obtain ⟨rr, l1, used, needRun, usedLe, binv1, _, _, shape, _, _, okEnough, leaveFacts, kinds, nextEq⟩ :=
    NEEDBITS_run_cursor buf.bits 16 (by decide)
  have dispatch := inflate_dispatch_HEAD E l mode
  rcases kinds with rfl | rfl
  · have run1 := dispatch.trans (zlib_head_run_ok E wrap5 headNone needRun)
    have shape' : SymbolRegShape l l1 := by
      unfold SymbolRegShape
      rw [shape]
    have packet : DispatchBuffers h r l1 (bs.drop used) :=
      buf.consume j.good j.good rfl (fun _ => rfl) (fun _ => rfl) shape' nextEq usedLe binv1
    obtain ⟨_, _, _, _, run2, _⟩ := headDefaultCheck_default_state E j packet (okEnough rfl)
    obtain ⟨e, _, _⟩ := same_leave leaveRun (run1.trans run2)
    cases e
  · obtain ⟨_, have0, below⟩ := leaveFacts rfl
    have run1 := dispatch.trans (zlib_head_run_leave E wrap5 needRun)
    obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun run1
    refine TripLeaveCause.short ⟨have0, LeaveShort.of_state st E.hs ?_⟩
    have len : (natBits l1.bits.toNat l1.hold.toNat).length < 16 := by
      rw [natBits_length]; exact below
    have wrapNZ : s.wrap ≠ 0 := by rw [wrap5]; decide
    unfold ShortAt
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨mode, wrapNZ, len⟩))))))))))

open MeaningDictid in
/-- `DICTID`: it leaves only in its `NEEDBITS(32)`, short of the identifier; after it `DICT`
returns `Z_NEED_DICT`, since no dictionary is installed yet. -/
theorem cause_dictid (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = DICTID) := by
  intro h l side loop dictid l' h' leaveRun
  obtain ⟨zs, z, s, E, _⟩ := side.env
  have loop0 := loop
  obtain ⟨zs0, s0, _, _, _, stage0, st, hs, _, _, _, _, binv0, _, _, _, _, _, _, _, _, _,
    _, _, stageM0, wrapM0, _⟩ := loop
  have e0 : zs0 = zs := by rw [E.st] at st; cases st; rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs.symm.trans E.hs)
  subst e1
  have mode : s0.mode = DICTID := dictid zs0 s0 st hs
  have high : (loopState s0 l).mode ≤ DICTID := by
    show s0.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨bytes0, rfl⟩ := stage_of_header stageM0 high
  obtain ⟨⟨rawHead0, _, _, _, _, wrappedC0, _, _, _⟩, _, _⟩ := wrapM0
  have wrapped : f.wrap ≠ .raw := by
    intro raw
    have headMode : s0.mode = HEAD := rawHead0 raw
    rw [mode] at headMode
    exact absurd headMode (by decide)
  have havedict0 : s0.havedict = 0 := (wrappedC0 wrapped).1
  obtain ⟨rr, l1, _, needRun, _, _, _, _, _, _, _, _, leaveFacts, kinds, _⟩ :=
    NEEDBITS_run_cursor binv0 32 (by decide)
  have dispatch := inflate_dispatch_DICTID E l mode
  rcases kinds with rfl | rfl
  · have cut := inflate_DICTID_parsed_cut E l l1 needRun
    have E2 : Env c (setI (r.put h { z with adler := ZSWAP32 l1.hold }) zs0
        { s0 with check := ZSWAP32 l1.hold, mode := DICT }) r zs0 { z with adler := ZSWAP32 l1.hold }
        { s0 with check := ZSWAP32 l1.hold, mode := DICT } :=
      ⟨E.strm, st, by rw [ZStreamRef.get_setI]; exact ZStreamRef.get_put_same E.hz _,
        setI_istates_same _ _ _⟩
    have wait := inflate_DICT_wait_run E2 { l1 with hold := 0, bits := 0 } havedict0
    obtain ⟨e, _, _⟩ := same_leave leaveRun ((dispatch.trans cut).trans wait)
    cases e
  · obtain ⟨_, have0, below⟩ := leaveFacts rfl
    obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun (dispatch.trans (inflate_DICTID_wait needRun))
    refine TripLeaveCause.short ⟨have0, LeaveShort.of_state st hs ?_⟩
    have len : (natBits l1.bits.toNat l1.hold.toNat).length < 32 := by
      rw [natBits_length]; exact below
    unfold ShortAt
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨Or.inr mode, len⟩))))))))))))

open MeaningDictTrip MeaningBlock in
/-- `DICT`: without a dictionary it returns `Z_NEED_DICT`; with one it goes on to `TYPE` in the
same dispatch (`type_step`). -/
theorem cause_dict (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = DICT) := by
  intro h l side loop dict l' h' leaveRun
  have side0 := side
  obtain ⟨zs, z, s, strm, st, j, _, _, _⟩ := side0
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  have mode : s.mode = DICT := dict zs s st E.hs
  have dispatch := inflate_dispatch_DICT E l mode
  by_cases present : s.havedict = 0
  · obtain ⟨e, _, _⟩ := same_leave leaveRun (dispatch.trans (inflate_DICT_wait_run E l present))
    cases e
  let z1 : ZStream := { z with adler := 1 }
  let s1 : InflateState := { s with check := 1, mode := TYPE }
  let h1 := setI (r.put h z1) zs s1
  have hz1 : r.get h1 = some z1 := by
    simp only [h1, ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have loop1 : LoopMatches c f h1 l := dict_ready_loop loop E mode present
  have globals : LibraryGlobals h1 := by
    have g := j.globals
    unfold LibraryGlobals at g ⊢
    simp only [h1, setI, ZStreamRef.put_static]
    exact g
  have last0 : s.last = 0 := by
    obtain ⟨_, s', _, _, _, stage, st', hs', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      stageM, wrapM, _⟩ := loop
    rw [st] at st'
    cases st'
    rw [E.hs] at hs'
    cases hs'
    obtain ⟨header, rfl⟩ := stage_of_dict stageM mode
    exact wrapM.2.2.2.2.1
  have boundary : ∀ zs' s', c.st = some (.tab zs') → h1.istates zs' = some s' →
      (s'.mode = TYPE ∨ s'.mode = TYPEDO) ∧ s'.last = 0 :=
    at_state (P := fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) st
      (setI_istates_same _ _ _) ⟨Or.inl rfl, last0⟩
  have cut := dispatch.trans (inflate_DICT_ready_cut E l present)
  obtain ⟨result, l1, h2, run, ends⟩ := type_step loop1 strm hz1 globals boundary
  obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun (cut.trans run)
  rcases ends with ⟨_, cause, _⟩ | ⟨e', _⟩
  · rcases cause with s | s | s
    · exact TripLeaveCause.short s
    · exact Or.inr (Or.inl s)
    · exact Or.inr (Or.inr (Or.inl s))
  · rw [e] at e'; cases e'

/-- `TYPE`/`TYPEDO` after the last block: it leaves only at a `Z_BLOCK`/`Z_TREES` stop in `TYPE`;
`TYPEDO` goes on to `CHECK`. -/
theorem cause_type_final (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0) := by
  intro h l side _ modeAt l' h' leaveRun
  obtain ⟨zs, z, s, E, _⟩ := side.env
  obtain ⟨mode, last⟩ := modeAt zs s E.st E.hs
  have dispatch := inflate_dispatch_block_type E l mode
  have typedo : runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h → False := by
    intro run
    obtain ⟨e, _, _⟩ := same_leave leaveRun (run.trans (inflate_TYPEDO_last E l last))
    cases e
  by_cases isType : s.mode = TYPE
  · rw [ite_eq_left_of_eq_true _ _ (eq_true isType)] at dispatch
    by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
    · rcases flush with b | t
      · exact Or.inr (Or.inl b)
      · exact Or.inr (Or.inr (Or.inl t))
    · have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
        ⟨fun e => flush (Or.inl e), fun e => flush (Or.inr e)⟩
      exact (typedo (dispatch.trans (inflate_TYPE_go c l h go))).elim
  · rw [ite_eq_right_of_eq_false _ _ (eq_false isType)] at dispatch
    exact (typedo dispatch).elim

open MeaningTrailer in
/-- `LENGTH` of a zlib stream: no length field (`flags = 0`), so `DONE` with `Z_STREAM_END`. -/
theorem cause_length_zlib (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (zlib : f.wrap = .zlib) :
    CauseAt c f r (fun s => s.mode = LENGTH) := by
  intro h l side loop length l' h' leaveRun
  obtain ⟨zs, z, s, E, _⟩ := side.env
  obtain ⟨zs0, s0, _, _, _, stage0, st, hs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    parsed0, stageM0, wrapM0, _⟩ := loop
  have e0 : zs0 = zs := by rw [E.st] at st; cases st; rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs.symm.trans E.hs)
  subst e1
  have mode : s0.mode = LENGTH := length zs0 s0 st hs
  obtain ⟨header0, out0, bytes0, rfl⟩ : ∃ header out bytes, stage0 = .trailer header out bytes := by
    rcases stage0 with b | b | ⟨b, pos⟩ | ⟨header, out, bytes⟩ | out
    · have hi : s0.mode ≤ DICTID := stageM0.2
      rw [mode] at hi; exact absurd hi (by decide)
    · have m : s0.mode = DICT := stageM0; rw [mode] at m; exact absurd m (by decide)
    · have range := MeaningTrailer.body_mode_range (s := loopState s0 l) stageM0.1
      have m : (loopState s0 l).mode = LENGTH := mode
      rw [m] at range
      exact absurd range (by decide)
    · exact ⟨header, out, bytes, rfl⟩
    · have m : s0.mode = DONE := stageM0; rw [mode] at m; exact absurd m (by decide)
  obtain ⟨flagsM, _, _⟩ := wrapM0
  have notGzip : ¬ IsGzipHeader header0 := by
    obtain ⟨_, _, _, wh, _⟩ := parsed0
    rw [zlib] at wh
    obtain ⟨window, zh, _⟩ := wh
    exact zlibHeader_not_gzip zh
  have flags0 : s0.flags = 0 := by
    unfold FlagsMatch at flagsM
    rw [zlib] at flagsM
    simpa [notGzip, loopState] using flagsM
  have run1 := (inflate_dispatch_LENGTH E l mode).trans (inflate_LENGTH_skip st hs (Or.inr flags0))
  obtain ⟨_, rfl, rfl⟩ := same_leave leaveRun run1
  exact Or.inl (show Z_STREAM_END ≠ Z_OK by decide)

end Zlib.Inflate.Proofs
