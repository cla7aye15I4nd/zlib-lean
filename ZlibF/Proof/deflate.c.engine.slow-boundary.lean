import ZlibF.Proof.«deflate.c.engine.slow-symbol-body»
import ZlibF.Proof.«deflate.c.engine.fill-read-resume»

/-! # An initialized and preserved boundary for the slow strategy

This is an internal representation boundary. It is not an assumption
that a translated callee obeys a specification.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

structure SlowBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin : Nat) (xs : List Symbol) : Prop where
  good : DGood h r ds z d
  chains : HeapChains h d d.strstart.toNat
  range : fillEnd d ≤ d.window_size.toNat
  history : LazyHistory input origin d
  deferred : DeferredByte d
  symbols : SymbolBoundary h ds d xs
  data : ∃ w wa, d.window = .ref (.blk w) 0 ∧ h.bytes w = some wa ∧
    (∀ i, i < fillEnd d → bfn wa i = input (origin + i)) ∧
    (3 ≤ d.lookahead.toNat → InsHForm d.hash_shift d.hash_mask (bfn wa) d.strstart.toNat d.ins_h)

/-- Successful actual default initialization supplies this boundary.
The input view starts empty, so fresh window bytes remain arbitrary. -/
theorem default_initialization_slow_boundary {h : Heap} {r : ZStreamRef} {z : ZStream}
    {version : BPtr} {level : Int32} {p : ZlibF.Spec.Api.DeflParams}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (hv : VersionValue h version (some 49))
    (params : ZlibF.Spec.Api.deflInit? level.toInt 8 15 8 0 = some p)
    (alloc : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) (input : Nat → UInt8) :
    ∃ after zf sf,
      C.run (deflateInit_ (some r) level version 112) h = .ok (Z_OK, after) ∧
      EngineStart after r h.nextBlk zf sf ∧ SlowBoundary after r h.nextBlk zf sf input 0 [] ∧
      DeflateInitial h after r p ∧ StreamReachable .deflate after r := by
  obtain ⟨after, zf, sf, run, start, initial, reachable, symbol⟩ :=
    default_initialization_symbol_boundary hf hu hg hz ha hv params alloc
  refine ⟨after, zf, sf, run, start, ?_, initial, reachable⟩
  refine ⟨start.good, ?_, start.window_range, logical_history_initial start.matchLength input 0,
    initialized_deferred_byte start, symbol, ?_⟩
  · simpa only [start.start, show (0 : UInt32).toNat = 0 from rfl] using start.chains
  · obtain ⟨w, p0, q, b, blocks⟩ := start.good.inv.blocks
    obtain ⟨wa, get, _⟩ := blocks.wa
    refine ⟨w, wa, blocks.win, get, ?_, ?_⟩
    · intro i bound
      simp [fillEnd, start.start, start.lookahead] at bound
    · intro large
      simp [start.lookahead] at large

end Zlib.Deflate.Engine.Proofs
