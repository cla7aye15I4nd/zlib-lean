import ZlibF.Proof.«inflate.c.origin-fields-memory-contract»
import ZlibF.Proof.«inflate.c.default-origin-state»
import ZlibF.Proof.«inflate.c.default-readonly-controls»
import ZlibF.Proof.«public-inflate-setdict»
import ZlibF.Spec.Common.Sequences
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every good window has a chronological dictionary view. -/
theorem good_dictionary_view {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) :
    ∃ old, InflateDictionary h s old := by
  rcases good.inv.win.block with null | ⟨w, a, window, get, _, size⟩
  · refine ⟨[], Or.inl ⟨?_, rfl⟩⟩
    have ws := good.inv.win.nullws null
    have hv := good.inv.win.hv
    rw [ws] at hv
    exact UInt32.toNat_inj.mp (by simpa using hv)
  · exact ⟨_, (inflateDictionary_eq_ring good window get size).mpr rfl⟩

/-- The actual successful window update retains each old owned block. -/
theorem updatewindow_owned_retained {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {ref : BRef} {off : Nat} {a : Array UInt8} {len : UInt32}
    (good : Good h r zs z s) (get : Space.get h ref = some a)
    (room : off + len.toNat ≤ a.size)
    (separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat))
    (run : updatewindow (some r) (.ref ref (off + len.toNat)) len h = .ok (0, after))
    (stateGet : after.istates zs = some state) :
    ∀ b, InflateOwned zs s b → InflateOwned zs state b := by
  rcases good.inv.win.block with null | ⟨w, bytes, window, bytesGet, ro, size⟩
  · intro b owned
    rcases owned with same | impossible
    · exact Or.inl same
    · rw [null] at impossible
      cases impossible
  · have sep : Separate (.ref ref ((off + len.toNat) - len.toNat)) len.toNat
        s.window (2 ^ s.wbits.toNat) := by simpa using separate
    obtain ⟨computed, result, actual, _, _, next, windowEq, _, _, _, _, _⟩ :=
      uw_post_public (copy := len) (eo := off + len.toNat) good window bytesGet ro size get
        (by omega) room sep
    have heapEq : after = computed := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    have sameState : state = result := Option.some.inj (stateGet.symm.trans (heapEq ▸ next.live.hs))
    subst state
    intro b owned
    simpa only [InflateOwned, windowEq] using owned

/-- The setter neither relinquishes its existing window nor changes its
state block. This observes the actual translated branches. -/
theorem inflateSetDictionary_owned_retained {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {source : BPtr} {len : UInt32} {rc : Int32}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r source len.toNat false)
    (current : Good after r zs z state)
    (run : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after)) :
    ∀ b, InflateOwned zs s b → InflateOwned zs state b := by
  have unchanged (same : after = h) : ∀ b, InflateOwned zs s b → InflateOwned zs state b := by
    have stateEq : state = s := Option.some.inj (current.live.hs.symm.trans (same ▸ before.good.live.hs))
    simpa only [stateEq] using (fun b (owned : InflateOwned zs s b) => owned)
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · have actual := inflateSetDictionary_refused_any before.good.live source len refused
    exact unchanged (congrArg Prod.snd (Except.ok.inj (run.symm.trans actual)))
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      apply Classical.byContradiction
      intro wrong
      exact refused (Or.inr ⟨raw, wrong⟩)
  obtain ⟨xs, readable⟩ := range.resolve_left nonnull |>.1
  rcases readable with null | ⟨ref, off, array, pointer, get, room, _⟩
  · exact (nonnull null.1).elim
  subst source
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · have actual := inflateSetDictionary_dataerr_any before.good.live get room mismatch.1 mismatch.2
    exact unchanged (congrArg Prod.snd (Except.ok.inj (run.symm.trans actual)))
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    apply Classical.byContradiction
    intro wrong
    exact mismatch ⟨dict, wrong⟩
  have unowned := callerRange_private_window before.good range rfl
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases before.good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, _frame, _source, _codes, outcome⟩ :=
    updatewindow_decoder_boundary before.good allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room unowned
  have actual := inflateSetDictionary_window_cut before.good.live get room allowed checked windowRun good1.live.hs
  rcases outcome with success | ⟨failure, _null, sameState, _heap⟩
  · subst wr
    simp only [ite_true] at actual
    have heapEq := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    dsimp only at heapEq
    have stateEq : state = { state1 with havedict := 1 } := by
      apply Option.some.inj
      rw [← current.live.hs, heapEq]
      simp [setI]
    have retained := updatewindow_owned_retained before.good get room separate windowRun good1.live.hs
    simpa only [stateEq, InflateOwned] using retained
  · subst wr
    subst state1
    simp only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] at actual
    have heapEq := congrArg Prod.snd (Except.ok.inj (run.symm.trans actual))
    dsimp only at heapEq
    have stateEq : state = { s with mode := MEM } := by
      apply Option.some.inj
      rw [← current.live.hs, heapEq]
      simp [setI]
    simpa only [stateEq, InflateOwned] using (fun b (owned : InflateOwned zs s b) => owned)

#print axioms good_dictionary_view
#print axioms updatewindow_owned_retained
#print axioms inflateSetDictionary_owned_retained
end Zlib.Inflate.Proofs
