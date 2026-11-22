import ZlibF.Proof.«deflate.c.engine.symbol-content»

/-! # Initialization, refill and the real slow body preserve symbol content -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Successful default entry establishes the empty content trace on its
actual allocated heap. No universal Init2 contract is assumed. -/
theorem default_initialization_content_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ ContentBoundary after r h.nextBlk zf sf input 0 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_pending_boundary hf hu hg hz ha hv params alloc input
  refine ⟨after, zf, sf, run, start, ⟨boundary, .empty, ?_⟩, initial, reachable⟩
  simp [pendingCredit, represented, start.start, start.matchAvailable]

/-- Caller edits preserve the private symbols and their logical meaning. -/
theorem rebuffer_content_boundary {h g : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ ContentBoundary g r ds z' d input origin base xs := by
  obtain ⟨z', getZ, next⟩ := rebuffer_pending_boundary boundary.toPendingBoundary edit header
  exact ⟨z', getZ, next, boundary.trace, boundary.accounted⟩

/-- The actual fill extends input only beyond the previously accepted
prefix. The stored symbols and their cumulative positions retain their
meaning through sliding, pending insertions and every padding branch. -/
theorem fill_window_content_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (short : d.lookahead.toNat < 262) (wrap : d.wrap = 1) (buffers : StreamBuffers h r)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used after z' result extended nextOrigin,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧
      ContentBoundary after r ds z' result extended nextOrigin base xs ∧ StreamAccounting z z' used 0 ∧
      nextOrigin + result.strstart.toNat = origin + d.strstart.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat + used ∧ result.wrap = 1 ∧
      (nextOrigin = origin ∨ nextOrigin = origin + d.w_size.toNat) ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) ∧ FillRecordFrame d result := by
  obtain ⟨used, after, z', result, extended, nextOrigin, run, pending, account,
      start, look, wrapA, originA, agrees, stopped, frame, _companion⟩ :=
    fill_window_pending_boundary_all_frame boundary.toPendingBoundary short wrap buffers inputValid
  have accounted := boundary.accounted
  have credit : pendingCredit result = pendingCredit d := by
    have available : result.match_available = d.match_available := congrArg (·.match_available) frame
    unfold pendingCredit
    rw [available]
  have traceA : Trace extended base xs := boundary.trace.extend (by dsimp only [fillEnd]; omega) agrees
  exact ⟨used, after, z', result, extended, nextOrigin, run, ⟨pending, traceA, by omega⟩,
    account, start, look, wrapA, originA, agrees, stopped, frame⟩

/-- The buffered symbols expand under the format's copyBack to the real
input prefix, ending immediately before any deferred byte. -/
theorem ContentBoundary.expands {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) :
    expandSymbols xs (inputPrefix input base) =
      inputPrefix input (origin + d.strstart.toNat - pendingCredit d) := by
  have position := boundary.accounted
  have endpoint : base + represented xs = origin + d.strstart.toNat - pendingCredit d := by omega
  rw [← endpoint]
  exact boundary.trace.expands

end Zlib.Deflate.Engine.Proofs
