import ZlibF.Proof.«deflate.c.engine.fill-pending-complete»
import ZlibF.Proof.«deflate.c.engine.rebuffer»

/-! # Caller buffer replacement retains both initialized hash frontiers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Arbitrary legal changes to unowned storage preserve the stronger
boundary. The header-free condition holds at the default entry. -/
theorem rebuffer_pending_boundary {h g : Heap} {r : ZStreamRef} {ds origin : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (boundary : PendingBoundary h r ds z d input origin xs)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ PendingBoundary g r ds z' d input origin xs := by
  obtain ⟨z', getZ, _, good⟩ := rebuffer_good_no_header boundary.good edit header
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
  have window := rebuffer_owned boundary.good edit (x := w) (Or.inr (Or.inl win))
  have pending := rebuffer_owned boundary.good edit (x := b)
    (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have symbols := symbol_boundary_of_ledger good trees.base.pbuf (pending.1.trans trees.base.bytes) ledger balance
  refine ⟨z', getZ, ⟨good, rebuffer_chains boundary.good edit boundary.chains,
    boundary.range, boundary.history, boundary.deferred, symbols,
    w, wa, win, window.1.trans get, view, form⟩,
    boundary.insert_le, rebuffer_chains boundary.good edit boundary.frontier, boundary.ready⟩

end Zlib.Deflate.Engine.Proofs
