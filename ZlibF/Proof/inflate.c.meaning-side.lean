import ZlibF.Proof.«inflate.c.meaning-run»
import ZlibF.Proof.«inflate.c.default-view-dispatch-rank»
import ZlibF.Proof.«inflate.c.sync2»

/-!
# inflate.c: the safety facts that the mode loop of one call keeps (`Side` of `loop_meaning`)

`loop_meaning` (`inflate.c.meaning-run`) takes a predicate `Side` on the registers and the heap
that every normal end of a dispatch keeps. The safety proof of `inflate` already carries one:
`DefaultViewLoopInv` (`inflate.c.default-view-loop`), kept by
`inflate_dispatch_default_view_state_rank`. `CallSide` is its part that does not count the
progress of the call: the decoder invariant `DefaultStateJ` (which includes `Good`, the table,
pending-field and code-length invariants, the library globals and the object-size limit), the
buffer facts `DispatchBuffers`, the header facts `HeaderLocal` and at most 39 held bits.

`loop_meaning_from` is `loop_meaning` entered from `LoopMatches` or `LoopBad`: a call that starts
in `BAD` goes straight to `case BAD:`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The local buffer `hbuf` of the call (`unsigned char hbuf[4]`, a local of `inflate()`) is not
the block of the unread input. The gzip header modes write it (`CRC2`, `CRC4`); in C a local
cannot alias the caller's input. In the model the buffer is the fresh block of the call. -/
def HbufInputApart (c : Ctx) (l : IL) : Prop :=
  l.have_ ≠ 0 → ∀ (b o : Nat) (ref : BRef) (off : Nat), c.hbuf = .ref (.blk b) o →
    l.next = .ref ref off → ref ≠ .blk b

/-- The safety facts at a trip of the mode loop of the call with context `c` on stream `r`. -/
def CallSide (c : Ctx) (r : ZStreamRef) (l : IL) (h : Heap) : Prop :=
  ∃ (zs : Nat) (z : ZStream) (s : InflateState), c.strm = some r ∧ c.st = some (.tab zs) ∧
    DefaultStateJ h r zs z s ∧ (∃ bs, DispatchBuffers h r l bs) ∧ HeaderLocal c h r s l ∧
    l.bits.toNat ≤ 39 ∧ HbufInputApart c l

/-- The input cursor only advances within its block and `have` only decreases, so a dispatch keeps
`HbufInputApart`. -/
theorem HbufInputApart.advance {c : Ctx} {l regs : IL} {used : Nat} (apart : HbufInputApart c l)
    (next : regs.next = inputAdvance l.next used) (count : regs.have_.toNat + used = l.have_.toNat) :
    HbufInputApart c regs := by
  intro nonzero b o ref off hb hn
  have before : l.have_ ≠ 0 := by
    intro zero
    apply nonzero
    apply UInt32.toNat_inj.mp
    rw [zero] at count
    simp only [UInt32.toNat_zero] at count ⊢
    omega
  cases hnext : l.next with
  | null =>
    rw [hnext] at next
    rw [next] at hn
    cases hn
  | ref ref0 off0 =>
    rw [hnext] at next
    rw [next] at hn
    cases hn
    exact apart before b o _ _ hb hnext


/-- The side facts name a live stream record. -/
theorem CallSide.record {c : Ctx} {r : ZStreamRef} {l : IL} {h : Heap} (side : CallSide c r l h) :
    ∃ z, r.get h = some z := by
  obtain ⟨_, z, _, _, _, j, _⟩ := side
  exact ⟨z, j.good.live.hz⟩

/-- `SideKept` for `CallSide`, from the safety step of one dispatch. -/
theorem side_kept (c : Ctx) (r : ZStreamRef) : SideKept c (CallSide c r) := by
  intro l h l' h' side run
  obtain ⟨zs, z, s, strm, st, j, ⟨bs, buf⟩, loc, bits, apart⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, j.good.live.hz, j.good.live.hs⟩
  obtain ⟨outcome, regs, after, stream, state, used, _, _, run', j', ⟨rest, _, buf'⟩, _, next, count,
    _, _, bits', loc', _⟩ := inflate_dispatch_default_view_state_rank E j buf loc bits
  have same := run.symm.trans run'
  simp only [Except.ok.injEq, Prod.mk.injEq] at same
  obtain ⟨⟨_, hl⟩, hh⟩ := same
  subst hl hh
  exact ⟨zs, stream, state, strm, st, j', ⟨rest, buf'⟩, loc', bits', apart.advance next count⟩

/-- `loop_meaning` entered from `LoopMatches` or from `LoopBad`: the proof of `loop_meaning`, whose
loop predicate already admits `LoopBad`, with the start relaxed. -/
theorem loop_meaning_from {c : Ctx} {f : LoopFrame} {Side : IL → Heap → Prop} {r : ZStreamRef}
    (trip : TripMeaning c f Side) (rawTrip : RawCheckTrip c f Side) (kept : SideKept c Side)
    (strm : c.strm = some r)
    (record : ∀ l h, Side l h → ∃ z, r.get h = some z)
    {l regs : IL} {h after : Heap} {outcome : Except Ex Unit}
    (side : Side l h) (start : LoopMatches c f h l ∨ LoopBad c f h l)
    (run : runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((outcome, regs), after)) :
    ∃ exit, outcome = .error exit ∧ LoopExit c f exit after regs := by
  cases outcome with
  | ok u => exact absurd run (fun run => xwhile_true_not_ok run)
  | error exit =>
    refine ⟨exit, rfl, ?_⟩
    let P : IL → Heap → Prop := fun l h =>
      Side l h ∧ ((LoopMatches c f h l ∨ LoopBad c f h l) ∨ RawCheck c f h l)
    let Q : Ex → IL → Heap → Prop := fun e l h => LoopExit c f e h l
    have step : ∀ l h outcome regs after, P l h →
        runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) →
        match outcome with
        | .ok () => P regs after
        | .error exit => Q exit regs after := by
      intro l h outcome regs after ⟨side, current⟩ source
      rcases current with (loop | bad) | raw
      · obtain ⟨result, l', h', run', outcome'⟩ := trip h l side loop
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases outcome' with tripOut | needDict | ⟨rfl, raw'⟩
        · rcases tripOut with ⟨rfl, cont⟩ | ⟨rfl, leave⟩
          · exact ⟨kept l h regs after side source, Or.inl cont⟩
          · exact Or.inl ⟨rfl, leave⟩
        · have exitEq := needDict.1
          cases exitEq
          exact Or.inr needDict
        · exact ⟨kept l h regs after side source, Or.inr raw'⟩
      · obtain ⟨z, hz⟩ := record l h side
        obtain ⟨run', tripOut⟩ := bad_trip bad strm hz
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases tripOut with ⟨eq, _⟩ | ⟨_, leave⟩
        · cases eq
        · exact Or.inl ⟨rfl, leave⟩
      · obtain ⟨result, l', h', run', tripOut⟩ := rawTrip h l side raw
        have same := source.symm.trans run'
        simp only [Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        rcases tripOut with ⟨rfl, cont⟩ | ⟨rfl, leave⟩
        · exact ⟨kept l h regs after side source, Or.inl cont⟩
        · exact Or.inl ⟨rfl, leave⟩
    exact xwhile_success_control_post P Q step ⟨side, Or.inl start⟩ run

end Zlib.Inflate.Proofs
