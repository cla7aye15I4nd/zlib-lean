import ZlibF.Proof.«deflate.c.engine.slow-boundary»
import ZlibF.Proof.«deflate.c.engine.fill-pending-call»

/-! # Pending positions retain their earlier hash-chain frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

structure PendingBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin : Nat) (xs : List Symbol) : Prop extends SlowBoundary h r ds z d input origin xs where
  insert_le : d.insert.toNat ≤ d.strstart.toNat
  frontier : HeapChains h d (d.strstart.toNat - d.insert.toNat)
  ready : 3 ≤ d.lookahead.toNat → d.insert = 0

theorem heap_chains_raise {h : Heap} {d : DeflateState} {top next : Nat}
    (chains : HeapChains h d top) (ordered : top ≤ next) : HeapChains h d next := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, chains_mono H ordered (Nat.le_refl _)⟩

/-- Actual default initialization establishes both frontiers, with insert=0. -/
theorem default_initialization_pending_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ PendingBoundary after r h.nextBlk zf sf input 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, boundary, initial, reachable⟩ :=
    default_initialization_slow_boundary hf hu hg hz ha hv params alloc input
  refine ⟨after, zf, sf, run, start, ⟨boundary, ?_, ?_, fun _ => start.insert⟩, initial, reachable⟩
  · simp [start.insert]
  · simpa only [start.insert, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using boundary.chains

end Zlib.Deflate.Engine.Proofs
