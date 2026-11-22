import ZlibF.Proof.«inflate.c.meaning-trip-trailer»
import ZlibF.Proof.«inflate.c.body-dispatch-frame»
import ZlibF.Proof.«inflate.c.meaning-block»
import ZlibF.Proof.«inflate.c.meaning-copy»
import ZlibF.Proof.«inflate.c.stored-dispatch»

/-!
# inflate.c: body trips (adapters; `TripStored`, `TripTypeOpen`)

The body steps of `inflate.c.meaning-*` end a trip in `LoopMatches`, at a leave with
`LoopMatches`, or in `BAD` with the input read so far refuted (`LoopRefuted`). `body_outcome`
turns these ends into a `TripOutcome`. The `BAD` end becomes `LoopBad` with the frame of the
dispatch (`body_dispatch_frame`: `in_` and the configuration fields are kept) and the input
count of the safety step (`have` only decreases).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The window cursors of the safety invariant, as the body steps ask for them. -/
theorem window_bounds {h : Heap} {s : InflateState} (w : WinInv h s) :
    s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize := by
  rw [UInt32.le_iff_toNat_le, UInt32.le_iff_toNat_le]
  have hv := w.hv
  have wn := w.wn
  have eq := w.eq
  refine ⟨?_, hv⟩
  by_cases lt : s.whave.toNat < s.wsize.toNat
  · have := eq lt
    omega
  · omega

/-- The `BAD` end of a body trip is `LoopBad`. -/
theorem loopBad_of_refuted {c : Ctx} {f : LoopFrame} {r : ZStreamRef} {h h' : Heap} {l l' : IL}
    (side : CallSide c r l h) (loop : LoopMatches c f h l)
    (body : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨ s.mode = LENGTH)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), l'), h'))
    (bad : ∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD)
    (refuted : LoopRefuted f l') : LoopBad c f h' l' := by
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, loc, bits, _⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  obtain ⟨inEq, s', hs', ew, erw, ehd, erb, ewb⟩ :=
    body_dispatch_frame st E.hs (body zs s st E.hs) run
  obtain ⟨outcome, regs, after, _, _, used, _, _, run', _, _, _, _, haveEq, _, _, _, _, _⟩ :=
    inflate_dispatch_default_view_state_rank E j buf loc bits
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨⟨_, hl⟩, hh⟩ := same
  subst hl hh
  obtain ⟨zs0, s0, _, _, _, _, st0, hs0, _, config, haveLe, inLen, _⟩ := loop
  have e0 : zs0 = zs := by
    rw [st] at st0
    cases st0
    rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs0.symm.trans E.hs)
  subst e1
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  have modeBad := bad zs0 s' st hs'
  refine ⟨zs0, s', st, hs', modeBad, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, refuted.doomed⟩
  · show s'.wrap = _
    rw [ew]
    exact c1
  · show s'.reqwrap = s'.wrap
    rw [erw, ew]
    exact c2
  · show s'.head = none
    rw [ehd]
    exact c3
  · show s'.reqbits.toNat = _
    rw [erb]
    exact c4
  · intro nz
    show s'.wbits.toNat = _
    rw [ewb]
    exact c5 nz
  · show s'.mode ≠ SYNC
    rw [modeBad]
    decide
  · rw [inEq]
    omega
  · rw [inEq]
    exact inLen

/-- The ends of a body step, as a `TripOutcome`. -/
theorem body_outcome {c : Ctx} {f : LoopFrame} {r : ZStreamRef} {h h' : Heap} {l l' : IL}
    {result : Except Ex Unit}
    (side : CallSide c r l h) (loop : LoopMatches c f h l)
    (body : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨ s.mode = LENGTH)
    (run : runX (inflate_dispatch c) l h = .ok ((result, l'), h'))
    (ends : (result = .error Ex.leave ∧ LoopMatches c f h' l') ∨
      (result = .ok () ∧ (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l')))) :
    TripOutcome c f result h' l' := by
  rcases ends with ⟨rfl, m⟩ | ⟨rfl, m | ⟨bad, ref⟩⟩
  · exact Or.inr ⟨rfl, Or.inl m⟩
  · exact Or.inl ⟨rfl, Or.inl m⟩
  · exact Or.inl ⟨rfl, Or.inr (loopBad_of_refuted side loop body run bad ref)⟩

/-- The real switch selects the TYPE branch. -/
theorem inflate_dispatch_TYPE {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = TYPE) :
    runX (inflate_dispatch c) l h = runX (inflate_TYPE c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE,
    ]

/-- The real switch selects the TYPEDO branch. -/
theorem inflate_dispatch_TYPEDO {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = TYPEDO) :
    runX (inflate_dispatch c) l h = runX (inflate_TYPEDO c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO,
    ]

/-- Stored blocks: `stored_step`, `copy_start_step`, `copy_step`. -/
theorem trip_stored : TripStored := by
  intro c f r h l side loop mode
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) E.st E.hs
    (window_bounds j.good.inv.win)
  rcases mode zs s E.st E.hs with m | m | m
  · have body := at_state (P := fun s => TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨
      s.mode = LENGTH) E.st E.hs (Or.inl (by rw [m]; decide))
    obtain ⟨result, l', h', run, ends⟩ :=
      MeaningBlock.stored_step loop E.strm E.hz (at_state (P := fun s => s.mode = STORED) E.st E.hs m)
        bounds
    have run' := (inflate_dispatch_STORED E l m).trans run
    refine ⟨result, l', h', run', Or.inl (body_outcome side loop body run' ?_)⟩
    rcases ends with ⟨e, _, m'⟩ | ⟨e, _, rest⟩
    · exact Or.inl ⟨e, m'⟩
    · exact Or.inr ⟨e, rest⟩
  · obtain ⟨result, l', h', run, ends⟩ :=
      MeaningCopy.copy_start_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY_) E.st E.hs m)
        bounds
    have run' := (inflate_dispatch_COPY_start E l m).trans run
    refine ⟨result, l', h', run', Or.inl ?_⟩
    rcases ends with ⟨e, _, m'⟩ | ⟨e, _, m'⟩
    · exact Or.inr ⟨e, Or.inl m'⟩
    · exact Or.inl ⟨e, Or.inl m'⟩
  · obtain ⟨result, l', h', run, ends⟩ :=
      MeaningCopy.copy_step loop E.strm E.hz (at_state (P := fun s => s.mode = COPY) E.st E.hs m)
        bounds
    have run' := (inflate_dispatch_COPY E l m).trans run
    refine ⟨result, l', h', run', Or.inl ?_⟩
    rcases ends with ⟨e, _, m'⟩ | ⟨e, _, m'⟩
    · exact Or.inr ⟨e, Or.inl m'⟩
    · exact Or.inl ⟨e, Or.inl m'⟩

/-- `TYPE`/`TYPEDO` before the last block: `type_step` and `typedo_step`. -/
theorem trip_type_open : TripTypeOpen := by
  intro c f r h l side loop mode
  obtain ⟨zs, z, s, E, j⟩ := side.env
  obtain ⟨m, _⟩ := mode zs s E.st E.hs
  have body := at_state (P := fun s => TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨
    s.mode = LENGTH) E.st E.hs (Or.inl (by rcases m with m | m <;> rw [m] <;> decide))
  rcases m with m | m
  · obtain ⟨result, l', h', run, ends⟩ := MeaningBlock.type_step loop E.strm E.hz j.globals mode
    have run' := (inflate_dispatch_TYPE E l m).trans run
    refine ⟨result, l', h', run', Or.inl (body_outcome side loop body run' ?_)⟩
    rcases ends with ⟨e, _, m'⟩ | ⟨e, _, rest⟩
    · exact Or.inl ⟨e, m'⟩
    · exact Or.inr ⟨e, rest⟩
  · obtain ⟨result, l', h', run, ends⟩ := MeaningBlock.typedo_step loop E.strm E.hz j.globals mode
    have run' := (inflate_dispatch_TYPEDO E l m).trans run
    refine ⟨result, l', h', run', Or.inl (body_outcome side loop body run' ?_)⟩
    rcases ends with ⟨e, _, m'⟩ | ⟨e, _, rest⟩
    · exact Or.inl ⟨e, m'⟩
    · exact Or.inr ⟨e, rest⟩

#print axioms loopBad_of_refuted
#print axioms trip_stored
#print axioms trip_type_open

end Zlib.Inflate.Proofs
