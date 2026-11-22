import ZlibF.Proof.«inflate.c.fast-buffers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- LOAD and the TYPE back write retain actual fast-call output progress.
This companion has the same explicit internal raw-buffer scope as the
proved caller bridge; it does not narrow the public inflate target. -/
theorem inflate_LEN_fast_raw_progress_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (mode : s.mode = LEN)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after state, runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      after.istates zs = some state ∧
      (state.mode = TYPE ∨ state.mode = BAD ∨ regs.left.toNat < l.left.toNat) := by
  obtain ⟨entry, heap1, cut, _, _, _, refEq, idEq, _, streamEq, _, _, progress⟩ :=
    inflate_LEN_fast_raw_cut_progress E good fit tables buffers pending mode input output different fast
  obtain ⟨stream1, state1, streamGet, stateGet, advancing⟩ := progress
  change entry.r.get heap1 = some stream1 at streamGet
  change heap1.istates entry.stid = some state1 at stateGet
  rw [refEq] at streamGet
  rw [idEq] at stateGet
  have E1 : Env c heap1 r zs stream1 state1 := ⟨E.strm, E.st, streamGet, stateGet⟩
  let regs := { l with put := stream1.next_out, left := stream1.avail_out, next := stream1.next_in, have_ := stream1.avail_in, hold := state1.hold, bits := state1.bits }
  by_cases type : state1.mode = TYPE
  · refine ⟨regs, setI heap1 zs { state1 with back := -1 }, { state1 with back := -1 }, ?_, by simp, Or.inl type⟩
    rw [cut, inflateAfterFast_run E1]
    simp only [type, ↓reduceIte]
    rfl
  · have kinds : state1.mode = TYPE ∨ state1.mode = BAD ∨ regs.left.toNat < l.left.toNat := by
      by_cases bad : state1.mode = BAD
      · exact Or.inr (Or.inl bad)
      · have delta := advancing type bad
        change stream1.avail_out.toNat < entry.sm0.avail_out.toNat at delta
        rw [streamEq] at delta
        exact Or.inr (Or.inr delta)
    refine ⟨regs, heap1, state1, ?_, stateGet, kinds⟩
    rw [cut, inflateAfterFast_run E1]
    simp only [type, ↓reduceIte]
    rfl

/-- The complete raw fast LEN branch retains the caller packet and proves actual nonterminal progress. -/
theorem inflate_LEN_fast_raw_buffers_progress {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} {ib io ob oo : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (mode : s.mode = LEN)
    (input : l.next = .ref (.blk ib) io) (output : l.put = .ref (.blk ob) oo)
    (different : ib ≠ ob) (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ used made regs after stream state, used ≤ bs.length ∧
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧ Good after r zs stream state ∧
      DataTableInvariant after state ∧ DataPendingInvariant state ∧ DispatchBuffers after r regs (bs.drop used) ∧
      ByteViewSizes h after ∧ regs.next = inputAdvance l.next used ∧ regs.have_.toNat + used = l.have_.toNat ∧
      regs.put = inputAdvance l.put made ∧ regs.left.toNat + made = l.left.toNat ∧ regs.bits.toNat < 8 ∧ (state.mode = TYPE ∨ state.mode = BAD ∨ 0 < made) := by
  obtain ⟨used, made, regs, after, stream, state, bound, run, current, data, nextPending,
    packet, sizes, next, haveCount, put, left, bits⟩ :=
    inflate_LEN_fast_raw_buffers E good fit tables buffers pending mode input output different fast
  obtain ⟨regs2, after2, state2, progressRun, stateGet, progress⟩ :=
    inflate_LEN_fast_raw_progress_run E good fit tables buffers pending mode input output different fast
  obtain ⟨localEq, heapEq⟩ := Prod.mk.inj (Except.ok.inj (run.symm.trans progressRun))
  have regsEq : regs2 = regs := (congrArg Prod.snd localEq).symm
  subst regs2
  subst after2
  have stateEq : state2 = state := Option.some.inj (stateGet.symm.trans current.live.hs)
  subst state2
  have kinds : state.mode = TYPE ∨ state.mode = BAD ∨ 0 < made := by
    rcases progress with type | bad | delta
    · exact Or.inl type
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (by omega))
  exact ⟨used, made, regs, after, stream, state, bound, run, current, data, nextPending,
    packet, sizes, next, haveCount, put, left, bits, kinds⟩

end Zlib.Inflate.Proofs
