import ZlibF.Proof.«deflate.c.engine.fill-slide-pending»
import ZlibF.Math.DeflateStreamBudget

/-! # Full refill preservation from the initialized pending boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Only fields written by the slide, read, priming and padding fragments
can change in the source state record. -/
def FillRecordFrame (before after : DeflateState) : Prop :=
  after = { before with
    strstart := after.strstart, match_start := after.match_start, block_start := after.block_start,
    insert := after.insert, slid := after.slid, lookahead := after.lookahead,
    ins_h := after.ins_h, high_water := after.high_water }

/-- What a refill keeps of the size ledger's two state clauses: a three-byte lazy candidate within
`TOO_FAR` of the next position, and a block start below zero only after a slide, which leaves the
position at least `w_size - 262`. A slide moves the position and the candidate by the same amount. -/
def FillCompanion (d result : DeflateState) : Prop :=
  ((d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR) →
    (result.match_length = 3 → result.strstart - 1 - result.match_start ≤ TOO_FAR)) ∧
  ((d.block_start.toInt < 0 → d.w_size.toNat - 262 ≤ d.strstart.toNat) →
    (result.block_start.toInt < 0 → result.w_size.toNat - 262 ≤ result.strstart.toNat))

theorem fill_companion_same {d result : DeflateState}
    (ml : result.match_length = d.match_length) (ss : result.strstart = d.strstart)
    (ms : result.match_start = d.match_start) (bs : result.block_start = d.block_start)
    (ws : result.w_size = d.w_size) : FillCompanion d result := by
  refine ⟨fun q => ?_, fun f => ?_⟩
  · rw [ml, ss, ms]; exact q
  · rw [bs, ws, ss]; exact f

theorem fill_companion_slide {d result : DeflateState}
    (ml : result.match_length = d.match_length) (ss : result.strstart.toNat = d.strstart.toNat - d.w_size.toNat)
    (ssU : result.strstart = d.strstart - d.w_size)
    (ms : result.match_start = d.match_start - d.w_size) (ws : result.w_size = d.w_size)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (small : d.w_size.toNat ≤ 32768)
    (large : 512 ≤ d.w_size.toNat) : FillCompanion d result := by
  refine ⟨fun q short => ?_, fun _ _ => ?_⟩
  · rw [ml] at short
    rw [ssU, ms, ZlibF.Math.DeflateBound.shifted_short_distance]
    exact q short
  · rw [ws, ss]
    have bound := UInt32.le_iff_toNat_le.mp taken
    have lookahead : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 262 ≤ d.w_size.toNat; omega)]
      rfl
    rw [UInt32.toNat_add, lookahead] at bound
    rw [Nat.mod_eq_of_lt (by omega)] at bound
    omega

/-- An internal call after the public null-input refusal. Empty input,
pending insertions and both sides of the slide test are covered. The
caller supplies public buffer storage, not an intermediate heap contract.
-/
theorem fill_window_pending_boundary_all_frame {h : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      PendingBoundary after r ds z' result extended nextOrigin xs ∧ StreamAccounting z z' used 0 ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.wrap = 1 ∧
      (nextOrigin = origin ∨ nextOrigin = origin + d.w_size.toNat) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result ∧
      FillCompanion d result := by
  obtain ⟨w, wa, win, get, _, _⟩ := boundary.data
  have sizes := slide_window_sizes boundary.good
  have accounting : StreamAccounting z z 0 0 := by
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · cases z.next_in <;> rfl
    · cases z.next_out <;> rfl
  by_cases empty : z.avail_in = 0
  · by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨after, run, boundaryA⟩ := fill_window_slide_empty_pending_boundary boundary empty taken
      have geometry := fill_slide_counts boundary.good win get boundary.range taken
      refine ⟨0, after, z, paddedState (slideState d), input, origin + d.w_size.toNat,
        run, boundaryA, accounting, ?_, by simp [paddedState, slideState, slideBeforeHash], wrap,
        Or.inr rfl, fun _ _ => rfl, Or.inr empty, rfl, ?_⟩
      · change origin + d.w_size.toNat + (slideState d).strstart.toNat = _
        rw [geometry.2.2.2.2.1]
        have start := geometry.1
        omega
      · exact fill_companion_slide rfl geometry.2.2.2.2.1 rfl rfl rfl taken sizes.2 sizes.1
    · obtain ⟨after, run, boundaryA⟩ := fill_window_empty_pending_boundary boundary empty taken
      exact ⟨0, after, z, paddedState d, input, origin, run, boundaryA, accounting, rfl,
        by simp [paddedState], wrap, Or.inl rfl, fun _ _ => rfl, Or.inr empty, rfl,
        fill_companion_same rfl rfl rfl rfl rfl⟩
  · obtain ⟨ref, io, pointer⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases pointer : z.next_in with
      | null => exact False.elim (inputValid empty pointer)
      | ref ref io => exact ⟨ref, io, rfl⟩
    by_cases taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)
    · obtain ⟨used, after, z', result, extended, run, boundaryA, account, start, look, _, wrapA, prefixA, stop, fields⟩ :=
        fill_window_slide_pending_boundary boundary short taken wrap buffers pointer empty
      have geometry := fill_slide_counts boundary.good win get boundary.range taken
      refine ⟨used, after, z', result, extended, origin + d.w_size.toNat, run, boundaryA, account,
        ?_, look, wrapA, Or.inr rfl, prefixA, stop, by rw [fields]; rfl, ?_⟩
      · rw [start]
        have before := geometry.1
        omega
      · exact fill_companion_slide (by rw [fields]; rfl) start (by rw [fields]; rfl) (by rw [fields]; rfl)
          (by rw [fields]; rfl) taken sizes.2 sizes.1
    · obtain ⟨used, after, z', result, extended, run, boundaryA, account, start, look, _, wrapA, prefixA, stop, fields⟩ :=
        fill_window_pending_boundary boundary short taken wrap buffers pointer empty
      exact ⟨used, after, z', result, extended, origin, run, boundaryA, account,
        by rw [start], look, wrapA, Or.inl rfl, prefixA, stop, by rw [fields]; rfl,
        fill_companion_same (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields])⟩

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- An established refill keeps the size ledger's two state clauses (`FillCompanion`). -/
theorem fill_run_companion {h after : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : fill_window (some (.tab ds)) h = .ok ((), after)) (state : after.dstates ds = some result) :
    FillCompanion d result := by
  obtain ⟨_used, other, _z', otherD, _extended, _nextOrigin, otherRun, boundaryA, _account,
      _start, _look, _wrapA, _originA, _prefixA, _stopped, _frame, companion⟩ :=
    fill_window_pending_boundary_all_frame boundary short wrap buffers inputValid
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst heaps
  have same : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans state)
  subst same
  exact companion

end Zlib.Deflate.Engine.Proofs
