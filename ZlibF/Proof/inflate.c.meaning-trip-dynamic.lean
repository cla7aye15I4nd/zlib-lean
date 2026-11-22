import ZlibF.Proof.«inflate.c.meaning-len-entry»
import ZlibF.Proof.«inflate.c.meaning-dynamic-steps»
import ZlibF.Proof.«inflate.c.construction-default-state»
import ZlibF.Proof.«inflate.c.table-mode»

/-!
# inflate.c: the dynamic header trip (`TripDynamic`)

A trip that starts in `TABLE`, `LENLENS` or `CODELENS` runs the dynamic header steps
(`table_step`, `lenlens_step`, `codelens_step`), which fall through into one another. After the
tables are installed, `CODELENS` sets `LEN_` and, unless `flush == Z_TREES`, falls through into
`case LEN_`. That point is inside the dispatch, so the safety facts there do not come from
`CallSide`.

They come from the safety boundary lemmas (`inflate_*_default_state_boundary`), which run the same
code. The meaning steps and the safety lemmas each name the continuation point only up to the run
equation `runX (M c) l h = runX (inflate_LEN_ c) L H`, which does not fix `(L, H)`. Both are
therefore used for the context `treesCtx c`, with `flush = Z_TREES`: then the continuation is a
leave, `runX (M (treesCtx c)) l h = .ok ((.error .leave, L), H)`, and the two results name the same
`(L, H)`. `Agree` relates the runs of `M c` and `M (treesCtx c)`: the code before the `Z_TREES`
test does not read `flush`, so the two runs are equal, or both reach the test at the same `(L, H)`
with the state in `LEN_`.

The row is proved from the fast path of `LEN_` on any caller byte view, `FastLenMeaning`:
`trip_dynamic_of`. `FastLenMeaning` is proved as `fast_len_meaning` (`inflate.c.meaning-trip-codes`),
which closes the row.
-/

namespace Zlib.Inflate.Proofs.MeaningTripDynamic
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLenEntry
set_option autoImplicit false

/-! ## The same call with `flush = Z_TREES` -/

/-- The context of the call with the flush argument `Z_TREES`. -/
abbrev treesCtx (c : Ctx) : Ctx := { c with flush := Z_TREES }

/-- The code after `state->mode = LEN_;` at the end of `CODELENS`. -/
abbrev finTail (c : Ctx) : X Unit := do
  if c.flush == Z_TREES then throw Ex.leave
  inflate_LEN_ c

/-- The state record of the call is in `LEN_`. -/
def LenMode (c : Ctx) (h : Heap) : Prop :=
  ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LEN_

/-- `p` (with the call's flush) and `q` (with `Z_TREES`) run alike up to the `Z_TREES` test. -/
def Agree (c : Ctx) (p q : X Unit) : Prop :=
  ∀ l h, runX p l h = runX q l h ∨
    ∃ L H, LenMode c H ∧ runX p l h = runX (finTail c) L H ∧ runX q l h = runX (finTail (treesCtx c)) L H

theorem agree_refl {c : Ctx} (p : X Unit) : Agree c p p := fun _ _ => Or.inl rfl

theorem agree_bind {c : Ctx} {α : Type} (m m' : X α) (f g : α → X Unit) (e : m = m')
    (next : ∀ a, Agree c (f a) (g a)) : Agree c (m >>= f) (m' >>= g) := by
  subst e
  intro l h
  rw [runX_bind, runX_bind]
  rcases runX m l h with e | ⟨⟨res, l1⟩, h1⟩
  · exact Or.inl rfl
  · rcases res with e | a
    · exact Or.inl rfl
    · exact next a l1 h1

theorem agree_bind3 {c : Ctx} {α β γ : Type} (m m' : X (α × β × γ)) (f g : α × β × γ → X Unit)
    (e : m = m') (next : ∀ a b d, Agree c (f (a, b, d)) (g (a, b, d))) : Agree c (m >>= f) (m' >>= g) :=
  agree_bind m m' f g e (fun ⟨a, b, d⟩ => next a b d)

theorem agree_ite {c : Ctx} {b : Prop} [Decidable b] {p1 p2 q1 q2 : X Unit}
    (h1 : Agree c p1 q1) (h2 : Agree c p2 q2) :
    Agree c (if b then p1 else p2) (if b then q1 else q2) := by
  by_cases hb : b
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact h1
  · rw [ite_eq_right hb, ite_eq_right hb]
    exact h2

/-- The `Z_TREES` test itself. -/
theorem agree_base (c : Ctx) :
    Agree c (do setMode c.st LEN_; finTail c) (do setMode (treesCtx c).st LEN_; finTail (treesCtx c)) := by
  intro l h
  rw [runX_bind, runX_bind]
  rcases hm : runX (monadLift (setMode c.st LEN_) : X Unit) l h with e | ⟨⟨res, l1⟩, h1⟩
  · exact Or.inl rfl
  · rcases res with e | u
    · exact Or.inl rfl
    · refine Or.inr ⟨l1, h1, ?_, rfl, rfl⟩
      intro zs s st hs
      cases hh : h.istates zs with
      | none =>
        rw [runX_lift, st] at hm
        unfold setMode at hm
        rw [wrI_eq, hh] at hm
        simp at hm
      | some v =>
        have key : runX (monadLift (setMode c.st LEN_) : X Unit) l h =
            .ok ((.ok (), l), setI h zs { v with mode := LEN_ }) :=
          runX_lift_ok (by rw [st]; exact setMode_tab hh LEN_) l
        rw [key] at hm
        simp only [Except.ok.injEq, Prod.mk.injEq] at hm
        obtain ⟨⟨_, _⟩, rfl⟩ := hm
        rw [setI_istates_same] at hs
        cases hs
        rfl

theorem finTail_leave {c : Ctx} (trees : c.flush = Z_TREES) (L : IL) (H : Heap) :
    runX (finTail c) L H = .ok ((.error Ex.leave, L), H) := by
  have cond : (c.flush == Z_TREES) = true := by rw [trees]; decide
  simp only [finTail, runX_bind, ite_eq_left cond, runX_throw]

theorem finTail_run {c : Ctx} (trees : c.flush ≠ Z_TREES) (L : IL) (H : Heap) :
    runX (finTail c) L H = runX (inflate_LEN_ c) L H := by
  have cond : ¬ (c.flush == Z_TREES) = true := by
    intro e
    exact trees (by simpa using e)
  simp only [finTail, ite_eq_right cond]

/-- One step of the walk over two copies of a mode body. -/
macro "agree_step" : tactic => `(tactic| first
  | with_reducible exact agree_refl _
  | with_reducible exact agree_base _
  | with_reducible refine agree_ite ?_ ?_
  | ((with_reducible refine agree_bind3 _ _ _ _ ?e (fun _ _ _ => ?_)); case e => rfl)
  | ((with_reducible refine agree_bind _ _ _ _ ?e (fun _ => ?_)); case e => rfl))

theorem agree_CODELENS (c : Ctx) : Agree c (inflate_CODELENS c) (inflate_CODELENS (treesCtx c)) := by
  unfold inflate_CODELENS
  repeat agree_step

theorem agree_LENLENS (c : Ctx) : Agree c (inflate_LENLENS c) (inflate_LENLENS (treesCtx c)) := by
  unfold inflate_LENLENS
  repeat (first | with_reducible exact agree_CODELENS _ | agree_step)

theorem agree_TABLE (c : Ctx) : Agree c (inflate_TABLE c) (inflate_TABLE (treesCtx c)) := by
  unfold inflate_TABLE
  repeat (first | with_reducible exact agree_LENLENS _ | agree_step)

/-! ## The meaning steps with `Z_TREES`: the whole header -/

theorem codelens_end {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (trees : c.flush = Z_TREES) (loop : LoopMatches c f h l) (strm : c.strm = some r)
    (hz : r.get h = some z)
    (mode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = CODELENS)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed)
    (lengths : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → CodeLengthInvariant zs s) :
    ∃ res L H, runX (inflate_CODELENS c) l h = .ok ((res, L), H) ∧ BodyEnds c f res H L := by
  rcases MeaningDynamicSteps.codelens_step loop strm hz mode wf lengths with
    ⟨res, L, H, run, ends⟩ | ⟨other, _⟩
  · refine ⟨res, L, H, run, ?_⟩
    rcases ends with ⟨e, _, m⟩ | ⟨e, _, bad, refuted⟩
    · exact Or.inl ⟨e, m⟩
    · exact Or.inr ⟨e, Or.inr ⟨bad, refuted⟩⟩
  · exact absurd trees other

theorem lenlens_end {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (trees : c.flush = Z_TREES) (loop : LoopMatches c f h l) (strm : c.strm = some r)
    (hz : r.get h = some z)
    (mode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LENLENS)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed) :
    ∃ res L H, runX (inflate_LENLENS c) l h = .ok ((res, L), H) ∧ BodyEnds c f res H L := by
  rcases MeaningDynamicSteps.lenlens_step loop strm hz mode wf with
    ⟨res, L, H, run, ends⟩ | ⟨L1, H1, run1, _, mode1, hz1, facts1, loop1⟩
  · refine ⟨res, L, H, run, ?_⟩
    rcases ends with ⟨e, _, _, m⟩ | ⟨e, _, bad, refuted⟩
    · exact Or.inl ⟨e, m⟩
    · exact Or.inr ⟨e, Or.inr ⟨bad, refuted⟩⟩
  · obtain ⟨res, L, H, run2, ends⟩ := codelens_end trees loop1 strm hz1 mode1
      (fun zs s st hs => (facts1 zs s st hs).1) (fun zs s st hs => (facts1 zs s st hs).2)
    exact ⟨res, L, H, run1.trans run2, ends⟩

theorem table_end {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (trees : c.flush = Z_TREES) (loop : LoopMatches c f h l) (strm : c.strm = some r)
    (hz : r.get h = some z)
    (mode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = TABLE)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed) :
    ∃ res L H, runX (inflate_TABLE c) l h = .ok ((res, L), H) ∧ BodyEnds c f res H L := by
  rcases MeaningDynamicSteps.table_step loop strm hz mode with
    ⟨res, L, H, run, ends⟩ | ⟨L1, H1, run1, _, mode1, hz1, wf1, loop1⟩
  · refine ⟨res, L, H, run, ?_⟩
    rcases ends with ⟨e, _, _, m⟩ | ⟨e, _, bad, refuted⟩
    · exact Or.inl ⟨e, m⟩
    · exact Or.inr ⟨e, Or.inr ⟨bad, refuted⟩⟩
  · obtain ⟨res, L, H, run2, ends⟩ := lenlens_end trees loop1 strm hz1 mode1 (wf1 wf)
    exact ⟨res, L, H, run1.trans run2, ends⟩

/-! ## The safety facts at the `Z_TREES` leave -/

/-- The conclusion of the safety boundary lemmas of the three header modes. -/
def ConstructionBoundary (c : Ctx) (M : X Unit) (h : Heap) (r : ZStreamRef) (zs : Nat)
    (s : InflateState) (l : IL) (bs : List UInt8) : Prop :=
  ∃ regs after stream state used, used ≤ bs.length ∧ DefaultStateJ after r zs stream state ∧
    DefaultConfigFrame s state ∧
    DispatchBuffers after r regs (bs.drop used) ∧ ByteViewSizes h after ∧
    regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
    regs.put = l.put ∧ regs.left = l.left ∧ regs.out_ = l.out_ ∧
    regs.bits.toNat ≤ max l.bits.toNat 21 ∧ regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧
    ((∃ outcome, runX M l h = .ok ((outcome, regs), after) ∧
        (outcome ≠ .ok () ∨ state.mode = BAD)) ∨
     (state.mode = LEN_ ∧ runX M l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, regs), after)
        else runX (inflate_LEN_ c) regs after))

theorem boundary_at_leave {c : Ctx} {M : X Unit} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {s : InflateState} {l L : IL} {bs : List UInt8} {H : Heap}
    (b : ConstructionBoundary c M h r zs s l bs) (trees : c.flush = Z_TREES)
    (run : runX M l h = .ok ((.error Ex.leave, L), H)) :
    ∃ stream state bs', DefaultStateJ H r zs stream state ∧ DispatchBuffers H r L bs' := by
  obtain ⟨regs, after, stream, state, used, _, J, _, buf, _, _, _, _, _, _, _, _, kinds⟩ := b
  rcases kinds with ⟨outcome, r1, _⟩ | ⟨_, r2⟩
  · have e := run.symm.trans r1
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨_, rfl⟩, rfl⟩ := e
    exact ⟨stream, state, _, J, buf⟩
  · rw [ite_eq_left trees] at r2
    have e := run.symm.trans r2
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨_, rfl⟩, rfl⟩ := e
    exact ⟨stream, state, _, J, buf⟩

/-! ## The trip -/

theorem dyn_trip_core {c : Ctx} {f : LoopFrame} {r : ZStreamRef} {h : Heap} {l : IL} {zs : Nat}
    {s : InflateState} {bs : List UInt8} {M : Ctx → X Unit}
    (fastRow : FastLenMeaning) (side : CallSide c r l h) (loop : LoopMatches c f h l)
    (strm : c.strm = some r) (st : c.st = some (.tab zs))
    (dispatchEq : runX (inflate_dispatch c) l h = runX (M c) l h)
    (agree : Agree c (M c) (M (treesCtx c)))
    (meaning : ∃ res L H, runX (M (treesCtx c)) l h = .ok ((res, L), H) ∧ BodyEnds c f res H L)
    (boundary : ConstructionBoundary (treesCtx c) (M (treesCtx c)) h r zs s l bs)
    (body : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨ s.mode = LENGTH) :
    ∃ result l' h', runX (inflate_dispatch c) l h = .ok ((result, l'), h') ∧
      (TripOutcome c f result h' l' ∨ MeaningDictid.NeedDictExit c f result h' l' ∨
        (result = .ok () ∧ RawCheck c f h' l')) := by
  obtain ⟨res, L, H, runT, ends⟩ := meaning
  rcases agree l h with same | ⟨L0, H0, lenMode, runC, runT0⟩
  · have run : runX (inflate_dispatch c) l h = .ok ((res, L), H) := dispatchEq.trans (same.trans runT)
    exact ⟨res, L, H, run, Or.inl (body_outcome side loop body run ends)⟩
  · have runLeave : runX (M (treesCtx c)) l h = .ok ((.error Ex.leave, L0), H0) :=
      runT0.trans (finTail_leave (c := treesCtx c) rfl L0 H0)
    have e := runT.symm.trans runLeave
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨eRes, eL⟩, eH⟩ := e
    have loop0 : LoopMatches c f H0 L0 := by
      rw [← eL, ← eH]
      rcases ends with ⟨_, m⟩ | ⟨e', _⟩
      · exact m
      · rw [eRes] at e'
        cases e'
    by_cases trees : c.flush = Z_TREES
    · have run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, L0), H0) :=
        dispatchEq.trans (runC.trans (finTail_leave trees L0 H0))
      exact ⟨_, _, _, run, Or.inl (body_outcome side loop body run (Or.inl ⟨rfl, loop0⟩))⟩
    · obtain ⟨stream, state, bs', J, buf⟩ := boundary_at_leave boundary rfl runLeave
      have E : Env c H0 r zs stream state := ⟨strm, st, J.good.live.hz, J.good.live.hs⟩
      have mode : state.mode = LEN_ := lenMode zs state st J.good.live.hs
      obtain ⟨result, l', h', runL, endsL⟩ := len_entry_step loop0 E J buf mode (fun _ => Or.inr fastRow)
      have run : runX (inflate_dispatch c) l h = .ok ((result, l'), h') :=
        dispatchEq.trans (runC.trans ((finTail_run trees L0 H0).trans runL))
      exact ⟨result, l', h', run, Or.inl (body_outcome side loop body run endsL)⟩

/-- The dynamic header row, from the fast `LEN` step on any caller byte views. -/
theorem trip_dynamic_of (fastRow : FastLenMeaning) : TripDynamic := by
  intro c f r h l side loop modes
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, _⟩ := id side
  have hz := j.good.live.hz
  have hs := j.good.live.hs
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have E' : Env (treesCtx c) h r zs z s := ⟨strm, st, hz, hs⟩
  have wf := at_state (P := fun s => s.WellFormed) st hs j.good.inv.wf
  have lengths : ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' →
      CodeLengthInvariant zs' s' := by
    intro zs' s' st' hs'
    rw [st] at st'
    cases st'
    rw [hs] at hs'
    cases hs'
    exact j.lengths
  have body : ∀ m, (m = TABLE ∨ m = LENLENS ∨ m = CODELENS) → s.mode = m →
      ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
        TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨ s.mode = LENGTH := by
    intro m which mode
    apply at_state (P := fun s => TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨ s.mode = LENGTH) st hs
    left
    rw [mode]
    rcases which with rfl | rfl | rfl <;> decide
  rcases modes zs s st hs with m | m | m
  · exact dyn_trip_core (M := inflate_TABLE) fastRow side loop strm st (inflate_dispatch_TABLE E l m)
      (agree_TABLE c)
      (table_end (c := treesCtx c) rfl loop strm hz (at_state (P := fun s => s.mode = TABLE) st hs m) wf)
      (inflate_TABLE_default_state_boundary E' j buf m) (body TABLE (Or.inl rfl) m)
  · exact dyn_trip_core (M := inflate_LENLENS) fastRow side loop strm st (inflate_dispatch_LENLENS E l m)
      (agree_LENLENS c)
      (lenlens_end (c := treesCtx c) rfl loop strm hz (at_state (P := fun s => s.mode = LENLENS) st hs m) wf)
      (inflate_LENLENS_default_state_boundary E' j buf m) (body LENLENS (Or.inr (Or.inl rfl)) m)
  · exact dyn_trip_core (M := inflate_CODELENS) fastRow side loop strm st (inflate_dispatch_CODELENS E l m)
      (agree_CODELENS c)
      (codelens_end (c := treesCtx c) rfl loop strm hz (at_state (P := fun s => s.mode = CODELENS) st hs m)
        wf lengths)
      (inflate_CODELENS_default_state_boundary E' j buf m) (body CODELENS (Or.inr (Or.inr rfl)) m)

#print axioms trip_dynamic_of

end Zlib.Inflate.Proofs.MeaningTripDynamic
