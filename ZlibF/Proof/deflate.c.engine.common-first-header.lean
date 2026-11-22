import ZlibF.Proof.«deflate.c.engine.public-first-finish-all»
import ZlibF.Proof.«deflate.c.engine.common-header»

/-! # The actual first split header at every compression level -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual header's staged bytes, BUSY store and checksum reset leave
a valid representation and caller ranges before its pending copy. -/
theorem common_header_ready_good_buffers {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf) :
    DGood (levelHeaderReady h r ds pb z d buf) r ds { z with adler := 1 } (levelHeaderState d) ∧
    StreamBuffers (levelHeaderReady h r ds pb z d buf) r := by
  let hb := { h with bytes := upd h.bytes pb (some (levelHeaderBytes d.level buf)) }
  have size : (levelHeaderBytes d.level buf).size = buf.size := by simp [levelHeaderBytes]
  have goodB : DGood hb r ds z d := good.bytes_set pb (levelHeaderBytes d.level buf) buf trees.base.bytes size
  obtain ⟨w, p, q, b, blocks⟩ := goodB.inv.blocks
  have room : 2 ≤ d.pending_buf_size.toNat := by
    rw [trees.base.psize]
    have lower := trees.base.lit_lo
    have extent := trees.base.size
    omega
  have blocksA : DBlocks hb (levelHeaderState d) w p q b :=
    { blocks with pout := ⟨0, by change d.pending_out = .ref (.blk b) 0; rw [cursor]; exact blocks.pbuf,
        by change 0 + 2 ≤ d.pending_buf_size.toNat; omega⟩ }
  have inv : DStInv hb ds (levelHeaderState d) :=
    { goodB.inv with blocks := ⟨w, p, q, b, blocksA⟩ }
  have goodA : DGood (levelHeaderReady h r ds pb z d buf) r ds { z with adler := 1 } (levelHeaderState d) :=
    goodB.setZD rfl good.live.zalloc good.live.zfree rfl (by simp [GoodStatus, levelHeaderState]) inv (by trkeep)
  have view : ∀ ref : BRef, Space.get (levelHeaderReady h r ds pb z d buf) ref = Space.get hb ref := by
    intro ref
    rw [levelHeaderReady, byte_view_setD_depth (d := d) (result := levelHeaderState d)
      (by simpa only [hb, ZStreamRef.put_dstates] using goodB.live.hs) rfl, byte_get_stream_put]
  have sizes : ByteSizes h (levelHeaderReady h r ds pb z d buf) := by
    refine ⟨?_, ?_⟩
    · intro ref a getA
      obtain ⟨next, getN, sizeN⟩ := byte_view_write_size getA trees.base.bytes size
      exact ⟨next, (view ref).trans getN, sizeN⟩
    · intro ref
      cases ref <;> simp [Space.ro, levelHeaderReady]
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have account : StreamAccounting z { z with adler := 1 } 0 0 := stream_accounting_zero z
  exact ⟨goodA, stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account⟩

end Zlib.Deflate.Engine.Proofs
