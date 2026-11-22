import ZlibF.Proof.«deflate.c.engine.fill-slide-call»
import ZlibF.Spec.Functional.Checksums

/-! # A complete sliding fill call from public caller buffers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesBase)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem window_pending_separate {h : Heap} {r : ZStreamRef} {ds w b : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (win : d.window = .ref (.blk w) 0) (pending : d.pending_buf = .ref (.blk b) 0) : w ≠ b := by
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have windowId : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have pendingId : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  exact blocks.wb

end Zlib.Deflate.Engine.Proofs
