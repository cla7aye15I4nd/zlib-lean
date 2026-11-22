import ZlibF.Proof.«inflate.c.completes-cause»
import ZlibF.Proof.«inflate.c.meaning-trip-dynamic»

/-!
# inflate.c: why a trip from the dynamic header leaves

The trip from `TABLE`, `LENLENS` or `CODELENS` runs the header and, at its end, either stops
(`Z_TREES`, in `LEN_`) or goes on into `LEN_`. As in `trip_dynamic_of`, the header is run in the
`Z_TREES` context (`treesCtx`), whose steps state the cause of each leave; `Agree` relates that run
to the call's own run. A leave inside the header is short of its field; at the end of the header
the call's own flush decides: `Z_TREES` (the cause), or the trip goes on into `LEN_`
(`cause_len_start`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLength Zlib.Inflate.Proofs.MeaningTripDynamic
set_option autoImplicit false

/-- A run of `case LEN_` from a state with the loop facts and the safety invariant that leaves
has a cause (the leave registers are compared with `left` at the start). -/
theorem cause_len_start {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (j : DefaultStateJ h r zs z s)
    (buf : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    {L : IL} {H : Heap}
    (run : runX (inflate_LEN_ c) l h = .ok ((.error Ex.leave, L), H))
    (le : L.left.toNat ≤ l.left.toNat) : TripLeaveCause c H l L := by
  have st := E.st
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
  have tables : ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' → DataTablesSafe h s' :=
    at_state (P := fun s => DataTablesSafe h s) st E.hs (j.tables (by rw [mode]; unfold DataTableMode; decide))
  by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨l1, h1, run1, _⟩ := len_start_fast loop E j buffers mode fast rawWidth
    obtain ⟨e, _, _⟩ := same_leave run run1
    cases e
  · obtain ⟨result, l1, h1, run1, ends⟩ := len__step loop E.strm E.hz fast
      (at_state (P := fun s => s.mode = LEN_) st E.hs mode) tables
      bounds sane wsizeBits ring privateWindow rawWidth
    obtain ⟨e, rfl, rfl⟩ := same_leave run run1
    exact cause_of_ends ends e le

/-- The cause of a leave of the header run in the `Z_TREES` context. -/
def TreesCause (c : Ctx) (f : LoopFrame) (res : Except Ex Unit) (H : Heap) (L : IL) : Prop :=
  res = .error Ex.leave → LoopMatches c f H L ∧
    ((L.have_ = 0 ∧ LeaveShort c H L) ∨ (LenMode c H ∧ L.bits.toNat < 8))

theorem codelens_cause {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (trees : c.flush = Z_TREES) (loop : LoopMatches c f h l) (strm : c.strm = some r)
    (hz : r.get h = some z)
    (mode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = CODELENS)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed)
    (lengths : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → CodeLengthInvariant zs s) :
    ∃ res L H, runX (inflate_CODELENS c) l h = .ok ((res, L), H) ∧ TreesCause c f res H L := by
  rcases MeaningDynamicSteps.codelens_step loop strm hz mode wf lengths with
    ⟨res, L, H, run, ends⟩ | ⟨other, _⟩
  · refine ⟨res, L, H, run, fun leave => ?_⟩
    rcases ends with ⟨_, cause, m⟩ | ⟨e, _⟩
    · refine ⟨m, ?_⟩
      rcases cause with s | ⟨_, len, small⟩
      · exact Or.inl s
      · exact Or.inr ⟨len, small⟩
    · rw [leave] at e; cases e
  · exact absurd trees other

theorem lenlens_cause {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (trees : c.flush = Z_TREES) (loop : LoopMatches c f h l) (strm : c.strm = some r)
    (hz : r.get h = some z)
    (mode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LENLENS)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed) :
    ∃ res L H, runX (inflate_LENLENS c) l h = .ok ((res, L), H) ∧ TreesCause c f res H L := by
  rcases MeaningDynamicSteps.lenlens_step loop strm hz mode wf with
    ⟨res, L, H, run, ends⟩ | ⟨L1, H1, run1, _, mode1, hz1, facts1, loop1⟩
  · refine ⟨res, L, H, run, fun leave => ?_⟩
    rcases ends with ⟨_, have0, short, m⟩ | ⟨e, _⟩
    · exact ⟨m, Or.inl ⟨have0, short⟩⟩
    · rw [leave] at e; cases e
  · obtain ⟨res, L, H, run2, cause⟩ := codelens_cause trees loop1 strm hz1 mode1
      (fun zs s st hs => (facts1 zs s st hs).1) (fun zs s st hs => (facts1 zs s st hs).2)
    exact ⟨res, L, H, run1.trans run2, cause⟩

theorem table_cause {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (trees : c.flush = Z_TREES) (loop : LoopMatches c f h l) (strm : c.strm = some r)
    (hz : r.get h = some z)
    (mode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = TABLE)
    (wf : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.WellFormed) :
    ∃ res L H, runX (inflate_TABLE c) l h = .ok ((res, L), H) ∧ TreesCause c f res H L := by
  rcases MeaningDynamicSteps.table_step loop strm hz mode with
    ⟨res, L, H, run, ends⟩ | ⟨L1, H1, run1, _, mode1, hz1, wf1, loop1⟩
  · refine ⟨res, L, H, run, fun leave => ?_⟩
    rcases ends with ⟨_, have0, short, m⟩ | ⟨e, _⟩
    · exact ⟨m, Or.inl ⟨have0, short⟩⟩
    · rw [leave] at e; cases e
  · obtain ⟨res, L, H, run2, cause⟩ := lenlens_cause trees loop1 strm hz1 mode1 (wf1 wf)
    exact ⟨res, L, H, run1.trans run2, cause⟩

/-- The cause of a trip from the dynamic header, from the header run in the `Z_TREES` context. -/
theorem dyn_cause_core {c : Ctx} {f : LoopFrame} {r : ZStreamRef} {h : Heap} {l : IL} {zs : Nat}
    {s : InflateState} {bs : List UInt8} {M : Ctx → X Unit}
    (side : CallSide c r l h) (strm : c.strm = some r) (st : c.st = some (.tab zs))
    (dispatchEq : runX (inflate_dispatch c) l h = runX (M c) l h)
    (agree : Agree c (M c) (M (treesCtx c)))
    (cause : ∃ res L H, runX (M (treesCtx c)) l h = .ok ((res, L), H) ∧ TreesCause c f res H L)
    (boundary : ConstructionBoundary (treesCtx c) (M (treesCtx c)) h r zs s l bs)
    {l' : IL} {h' : Heap}
    (leaveRun : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, l'), h')) :
    TripLeaveCause c h' l l' := by
  obtain ⟨res, L, H, runT, causeT⟩ := cause
  rcases agree l h with same | ⟨L0, H0, lenMode, runC, runT0⟩
  · obtain ⟨e, rfl, rfl⟩ := same_leave leaveRun (dispatchEq.trans (same.trans runT))
    obtain ⟨_, c1 | c2⟩ := causeT e
    · exact TripLeaveCause.short c1
    · exact TripLeaveCause.lenStart c2
  · have runLeave : runX (M (treesCtx c)) l h = .ok ((.error Ex.leave, L0), H0) :=
      runT0.trans (finTail_leave (c := treesCtx c) rfl L0 H0)
    obtain ⟨eRes, rfl, rfl⟩ := same_leave runLeave runT
    obtain ⟨loop0, _⟩ := causeT eRes
    by_cases trees : c.flush = Z_TREES
    · exact Or.inr (Or.inr (Or.inl trees))
    · obtain ⟨regs, after, stream, state, used, _, J, _, buf, _, _, _, _, leftEq, _, _, _, kinds⟩ :=
        boundary
      have same : regs = L ∧ after = H := by
        rcases kinds with ⟨outcome, r1, _⟩ | ⟨_, r2⟩
        · have e := runLeave.symm.trans r1
          simp only [Except.ok.injEq, Prod.mk.injEq] at e
          exact ⟨e.1.2.symm, e.2.symm⟩
        · rw [ite_eq_left (show (treesCtx c).flush = Z_TREES from rfl)] at r2
          have e := runLeave.symm.trans r2
          simp only [Except.ok.injEq, Prod.mk.injEq] at e
          exact ⟨e.1.2.symm, e.2.symm⟩
      obtain ⟨rfl, rfl⟩ := same
      have E : Env c after r zs stream state := ⟨strm, st, J.good.live.hz, J.good.live.hs⟩
      have mode : state.mode = LEN_ := lenMode zs state st J.good.live.hs
      have runL : runX (inflate_LEN_ c) regs after = .ok ((.error Ex.leave, l'), h') :=
        ((dispatchEq.trans runC).trans (finTail_run trees regs after)).symm.trans leaveRun
      have le : l'.left.toNat ≤ regs.left.toNat := by
        rw [leftEq]
        exact trip_left_le side leaveRun
      exact cause_len_start loop0 E J buf mode runL le

/-- The dynamic header (`TABLE`, `LENLENS`, `CODELENS`). -/
theorem cause_dynamic (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    CauseAt c f r (fun s => s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) := by
  intro h l side loop modes l' h' leaveRun
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
  rcases modes zs s st hs with m | m | m
  · exact dyn_cause_core (M := inflate_TABLE) side strm st (inflate_dispatch_TABLE E l m)
      (agree_TABLE c)
      (table_cause (c := treesCtx c) rfl loop strm hz (at_state (P := fun s => s.mode = TABLE) st hs m) wf)
      (inflate_TABLE_default_state_boundary E' j buf m) leaveRun
  · exact dyn_cause_core (M := inflate_LENLENS) side strm st (inflate_dispatch_LENLENS E l m)
      (agree_LENLENS c)
      (lenlens_cause (c := treesCtx c) rfl loop strm hz (at_state (P := fun s => s.mode = LENLENS) st hs m) wf)
      (inflate_LENLENS_default_state_boundary E' j buf m) leaveRun
  · exact dyn_cause_core (M := inflate_CODELENS) side strm st (inflate_dispatch_CODELENS E l m)
      (agree_CODELENS c)
      (codelens_cause (c := treesCtx c) rfl loop strm hz (at_state (P := fun s => s.mode = CODELENS) st hs m)
        wf lengths)
      (inflate_CODELENS_default_state_boundary E' j buf m) leaveRun

end Zlib.Inflate.Proofs
