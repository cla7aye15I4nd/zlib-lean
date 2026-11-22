import ZlibF.Proof.«inflate.c.meaning-trip»
import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.meaning-block»
import ZlibF.Proof.«inflate.c.meaning-head-zlib»
import ZlibF.Proof.«inflate.c.meaning-wrap-steps»
import ZlibF.Proof.«inflate.c.check-dispatch»
import ZlibF.Proof.«inflate.c.dictionary-dispatch»
import ZlibF.Proof.«inflate.c.held-bound»

/-!
# inflate.c: the trip row `DICT` (`TripDict`)

`case DICT:` in the loop. The parse stands at the dictionary request (`.needDict header`).

* No dictionary (`havedict = 0`): `RESTORE()`, the input count and `return Z_NEED_DICT`. This is
  `NeedDictExit` with the request state itself as `mid` (`inflate_DICT_wait_run`).
* A dictionary (`havedict ≠ 0`): `inflateSetDictionary` checked its Adler-32 against the
  identifier and installed it in the window (`WrapMatches .needDict`). `check` becomes
  `adler32 [] = 1` and the mode `TYPE`; the parse is then at the first block boundary of the body
  (`wrapParsed_dictionary_body`). The same dispatch falls through into `case TYPE:`
  (`inflate_DICT_ready_cut`), which is `type_step` on that state. Its ends are mapped to
  `TripOutcome`; for the rejection of block type 3 the configuration of the `BAD` state comes from
  `type_frame`: `TYPE`/`TYPEDO` change no configuration field and no register but the input
  cursor and the bit buffer.
-/

namespace Zlib.Inflate.Proofs.MeaningDictTrip
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningDictid Zlib.Inflate.Proofs.MeaningBlock
set_option autoImplicit false

/-- The configuration fields of the decoder state and the registers that `TYPE` keeps. -/
def TypeKeeps (s s' : InflateState) (l l' : IL) : Prop :=
  s'.wrap = s.wrap ∧ s'.reqwrap = s.reqwrap ∧ s'.head = s.head ∧ s'.reqbits = s.reqbits ∧
    s'.wbits = s.wbits ∧ RegsKeep l l' ∧ l'.have_.toNat ≤ l.have_.toNat

/-- `case TYPE` and `case TYPEDO` before the final block change no configuration field, and no
register but the input cursor and the bit buffer. -/
theorem type_frame {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l : IL} {bs : List UInt8} (E : Env c h r zs z s) (last : s.last = 0)
    (binv : BitInv h l bs) {result : Except Ex Unit} {l' : IL} {h' : Heap} {s' : InflateState}
    (run : runX (inflate_TYPE c) l h = .ok ((result, l'), h')) (hs' : h'.istates zs = some s') :
    TypeKeeps s s' l l' := by
  by_cases flush : c.flush = Z_BLOCK ∨ c.flush = Z_TREES
  · obtain ⟨_, rfl, rfl⟩ := runX_same run (inflate_TYPE_leave c l h flush)
    rw [E.hs] at hs'
    cases hs'
    exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, Nat.le_refl _⟩
  have go : c.flush ≠ Z_BLOCK ∧ c.flush ≠ Z_TREES :=
    ⟨fun e => flush (Or.inl e), fun e => flush (Or.inr e)⟩
  rw [inflate_TYPE_go c l h go] at run
  obtain ⟨res1, l1, j, pull, jle, binv1, _, _, shape, _, _, _, _, kinds, _⟩ :=
    NEEDBITS_run_cursor binv 3 (by decide)
  have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape
  have have1 : l1.have_.toNat ≤ l.have_.toNat := by
    have a := binv.have_eq
    have b := binv1.have_eq
    simp only [List.length_drop] at b
    omega
  rcases kinds with rfl | rfl
  · have runHead := inflate_TYPEDO_head E l l1 last pull
    let s1 : InflateState := { s with last := u2i (l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1)) }
    let l2 : IL := { l1 with hold := l1.hold >>> 1, bits := l1.bits - 1 }
    have E1 : Env c (setI h zs s1) r zs z s1 := ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
    have keep2 : RegsKeep l { l2 with hold := l2.hold >>> 2, bits := l2.bits - 2 } :=
      keep1.trans ⟨rfl, rfl, rfl, rfl, rfl⟩
    have have2 : ({ l2 with hold := l2.hold >>> 2, bits := l2.bits - 2 } : IL).have_.toNat ≤
        l.have_.toNat := have1
    have cases4 : l2.hold.toNat % 4 = 0 ∨ l2.hold.toNat % 4 = 1 ∨ l2.hold.toNat % 4 = 2 ∨
        l2.hold.toNat % 4 = 3 := by omega
    rcases cases4 with t | t | t | t
    · obtain ⟨_, rfl, rfl⟩ := runX_same run (runHead.trans (typedoTail_stored E1 l2 t))
      simp only [setI_istates_same, Option.some.injEq] at hs'
      subst hs'
      exact ⟨rfl, rfl, rfl, rfl, rfl, keep2, have2⟩
    · by_cases trees : c.flush = Z_TREES
      · obtain ⟨_, rfl, rfl⟩ := runX_same run (runHead.trans (typedoTail_fixed_trees E1 l2 t trees))
        simp only [setI_istates_same, Option.some.injEq] at hs'
        subst hs'
        exact ⟨rfl, rfl, rfl, rfl, rfl, keep2, have2⟩
      · obtain ⟨_, rfl, rfl⟩ := runX_same run (runHead.trans (typedoTail_fixed E1 l2 t trees))
        simp only [setI_istates_same, Option.some.injEq] at hs'
        subst hs'
        exact ⟨rfl, rfl, rfl, rfl, rfl, keep2, have2⟩
    · obtain ⟨_, rfl, rfl⟩ := runX_same run (runHead.trans (typedoTail_table E1 l2 t))
      simp only [setI_istates_same, Option.some.injEq] at hs'
      subst hs'
      exact ⟨rfl, rfl, rfl, rfl, rfl, keep2, have2⟩
    · obtain ⟨i, _, runBad⟩ := typedoTail_bad E1 l2 t
      obtain ⟨_, rfl, rfl⟩ := runX_same run (runHead.trans runBad)
      simp only [badHeap, setI_istates_same, Option.some.injEq] at hs'
      subst hs'
      exact ⟨rfl, rfl, rfl, rfl, rfl, keep2, have2⟩
  · obtain ⟨_, rfl, rfl⟩ := runX_same run (inflate_TYPEDO_wait E l l1 last _ pull)
    rw [E.hs] at hs'
    cases hs'
    exact ⟨rfl, rfl, rfl, rfl, rfl, keep1, have1⟩

/-- The only stage a `DICT` state can stand for. -/
theorem stage_of_dict {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageM : LoopStageMatches h s f checked stage) (mode : s.mode = DICT) :
    ∃ header, stage = .needDict header := by
  rcases stage with b | header | ⟨header, pos⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨_, hi⟩ := stageM
    rw [mode] at hi
    exact absurd hi (by decide)
  · exact ⟨header, rfl⟩
  · have range := MeaningTrailer.body_mode_range stageM.1
    rw [mode] at range
    exact absurd range.1 (by decide)
  · rcases stageM.1 with m | m <;> rw [mode] at m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageM
    rw [mode] at m
    exact absurd m (by decide)

/-- After the dictionary: `check = 1`, mode `TYPE`, and the parse at the first block boundary of
the body. -/
theorem dict_ready_loop {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef}
    {z : ZStream} {zs : Nat} {s : InflateState}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (mode : s.mode = DICT)
    (present : s.havedict ≠ 0) :
    LoopMatches c f (setI (r.put h { z with adler := 1 }) zs { s with check := 1, mode := TYPE }) l := by
  obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk, config, haveLe, inLen, binv,
    leftLe, pend, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    have st := E.st
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (E.hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨header, rfl⟩ := stage_of_dict stageM mode
  obtain ⟨check0, flags0, bits0, width, last0, total0, _, dictC⟩ := wrapM
  obtain ⟨identifier, windowM⟩ := dictC present
  have needed := parsed
  obtain ⟨consumedEq, zlibLike, cmf, flg, dictid, rfl, _, ok, _, _⟩ := parsed
  have outNil : f.logOut ++ callOut = [] := outputEq.symm
  obtain ⟨logNil, callNil⟩ := List.append_eq_nil_iff.mp outNil
  subst callNil
  have pend0 : loopPending l = 0 := by
    have := pend.1
    simp only [List.length_nil] at this
    omega
  have notGzip : ¬ IsGzipHeader ([cmf, flg] ++ dictid) := by
    intro magic
    apply MeaningHeadZlib.zlib_head_not_gzip ok
    unfold IsGzipHeader at magic ⊢
    simpa using magic
  have views := sameViews_put h r { z with adler := 1 } zs { s with check := 1, mode := TYPE }
  have binv2 := binv.byte_views (fun ref => (views ref).1)
  have bitsL : l.bits = 0 := bits0
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  refine ⟨zs, { s with check := 1, mode := TYPE }, [], consumed, held,
    .body ([cmf, flg] ++ dictid) ⟨[], false, .boundary⟩, E.st, setI_istates_same _ _ _, retOk,
    ⟨c1, c2, c3, c4, c5, show TYPE ≠ SYNC by decide⟩, haveLe, inLen,
    ⟨binv2.have_eq, binv2.next, binv2.hold_lt⟩, leftLe,
    ⟨Nat.le_of_eq pend0, fun _ _ _ => pend0⟩, putEq, views.bytes outBytes,
    views.writable writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits,
    wrapParsed_dictionary_body needed identifier, ⟨?_, ?_, ?_⟩, ⟨?_, width, ?_⟩, outputEq⟩
  · refine ⟨Or.inl rfl, rfl, last0, ?_⟩
    show l.bits.toNat < 8
    rw [bitsL]
    decide
  · rw [logNil]
    exact MeaningCopy.window_transfer rfl rfl rfl rfl (fun q => (views q).1) windowM
  · refine ⟨?_, fun _ => ?_⟩
    · rw [logNil]
      simp only [List.append_nil, List.take_nil, List.length_nil]
      exact total0
    · show (1 : UInt64) = _
      rw [logNil]
      have notG : ¬ (f.wrap = .gzip ∨ (f.wrap = .auto ∧ ([cmf, flg] ++ dictid).take 2 = [31, 139])) := by
        rintro (g | ⟨_, g⟩)
        · rcases zlibLike with w | w <;> rw [w] at g <;> cases g
        · exact notGzip g
      rw [ite_eq_right notG]
      simp only [List.append_nil, List.take_nil]
      decide
  · show FlagsMatch _ f.wrap _
    have notRaw : f.wrap ≠ .raw := by rcases zlibLike with w | w <;> rw [w] <;> decide
    unfold FlagsMatch
    rw [ite_eq_right notRaw, ite_eq_right notGzip]
    exact flags0
  · exact Or.inr (Or.inr (by simp; omega))

end Zlib.Inflate.Proofs.MeaningDictTrip

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningDictid Zlib.Inflate.Proofs.MeaningBlock
  Zlib.Inflate.Proofs.MeaningDictTrip
set_option autoImplicit false

/-- `DICT`: with no dictionary the request exit (`NeedDictExit`); with one, `check = 1`, mode
`TYPE`, and the fall-through into `case TYPE:` (`type_step`). -/
theorem trip_dict : TripDict := by
  intro c f r h l side loop dict
  have side0 := side
  obtain ⟨zs, z, s, strm, st, j, _, _, _⟩ := side0
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  have mode : s.mode = DICT := dict zs s st E.hs
  have dispatch := inflate_dispatch_DICT E l mode
  by_cases present : s.havedict = 0
  · exact ⟨_, _, _, dispatch.trans (inflate_DICT_wait_run E l present),
      Or.inr (Or.inl ⟨rfl, r, z, zs, s, h, strm, st, E.hz, E.hs, mode, present, loop, rfl⟩)⟩
  -- the dictionary is installed: on to `TYPE` in the same dispatch
  let z1 : ZStream := { z with adler := 1 }
  let s1 : InflateState := { s with check := 1, mode := TYPE }
  let h1 := setI (r.put h z1) zs s1
  have hz1 : r.get h1 = some z1 := by
    simp only [h1, ZStreamRef.get_setI]
    exact ZStreamRef.get_put_same E.hz _
  have E1 : Env c h1 r zs z1 s1 := ⟨strm, st, hz1, setI_istates_same _ _ _⟩
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
  obtain ⟨result, l', h', run, ends⟩ := type_step loop1 strm hz1 globals boundary
  refine ⟨result, l', h', cut.trans run, Or.inl ?_⟩
  rcases ends with ⟨rfl, _, moved⟩ | ⟨rfl, _, moved | ⟨bad, refuted⟩⟩
  · exact Or.inr ⟨rfl, Or.inl moved⟩
  · exact Or.inl ⟨rfl, Or.inl moved⟩
  · -- block type 3: `BAD`, the configuration kept by `type_frame`
    obtain ⟨zs2, s2, _, _, _, _, st2, hs2, _, config, haveLe, inLen, binv, _⟩ := loop1
    rw [st] at st2
    cases st2
    simp only [h1, setI_istates_same, Option.some.injEq] at hs2
    subst hs2
    obtain ⟨zs3, _, s', _, st3, j', _⟩ := side_kept c r l h l' h' side (cut.trans run)
    rw [st] at st3
    cases st3
    have hs' := j'.good.live.hs
    obtain ⟨w, rw', hd, rb, wb, keep, haveL⟩ := type_frame E1 last0 binv run hs'
    obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
    refine Or.inl ⟨rfl, Or.inr ⟨zs, s', st, hs', bad zs s' st hs', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
      LoopRefuted.doomed refuted⟩⟩
    · show s'.wrap = _
      rw [w]
      exact c1
    · show s'.reqwrap = s'.wrap
      rw [rw', w]
      exact c2
    · show s'.head = none
      rw [hd]
      exact c3
    · show s'.reqbits.toNat = _
      rw [rb]
      exact c4
    · intro nz
      show s'.wbits.toNat = _
      rw [wb]
      exact c5 nz
    · show s'.mode ≠ SYNC
      rw [bad zs s' st hs']
      decide
    · rw [keep.1]
      omega
    · rw [keep.1]
      exact inLen

#print axioms trip_dict

end Zlib.Inflate.Proofs
