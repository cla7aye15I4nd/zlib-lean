import ZlibF.Proof.«deflate.c.engine.fill-source»
import ZlibF.Proof.«deflate.c.engine.insert-chains»

/-! # The first fill_window call

The execution boundary allows every good status. Header output may have
changed INIT_STATE to BUSY_STATE before the strategy reaches this call.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem EngineStart.window_size {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) : d.window_size = 65536 := by
  apply UInt64.toNat_inj.mp
  rw [start.good.inv.wsz, start.good.inv.wsize, start.windowBits]
  rfl

theorem EngineStart.w_size {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (start : EngineStart h r ds z d) : d.w_size = 32768 := by
  apply UInt32.toNat_inj.mp
  rw [start.good.inv.wsize, start.windowBits]
  rfl

theorem do_once {α : Type} {body : α → M α} {cond : α → M (Bool × α)}
    {h g j : Heap} {a b c : α} (hb : body a h = .ok (b, g))
    (hc : cond b g = .ok ((false, c), j)) : cdoWhile body cond a h = .ok (c, j) := by
  unfold cdoWhile
  change cdoWhile.go body cond (18446744073709551615 + 1) a h = _
  rw [cdoWhile.go, bind_app, hb]
  simp only []
  rw [bind_app, hc]
  rfl

theorem fill_cond_break (s : DeflateStatePtr) (h : Heap) :
    fillCond s true h = .ok ((false, true), h) := rfl

end Zlib.Deflate.Engine.Proofs
