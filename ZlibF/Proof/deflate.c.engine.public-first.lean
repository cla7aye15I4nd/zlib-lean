import ZlibF.Proof.«deflate.c.engine.header-caller»

/-! # The first actual default public compressor call before block output

This supporting path emits the wrapper header and executes the selected
strategy on the same heap. The full public target is unchanged.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem stream_accounting_trans {a b c : ZStream} {used1 used2 produced1 produced2 : Nat}
    (one : StreamAccounting a b used1 produced1) (two : StreamAccounting b c used2 produced2) :
    StreamAccounting a c (used1 + used2) (produced1 + produced2) := by
  rcases one with ⟨boundIn1, boundOut1, input1, output1, inPtr1, outPtr1, state1, alloc1, free1, opaque1, reserved1⟩
  rcases two with ⟨boundIn2, boundOut2, input2, output2, inPtr2, outPtr2, state2, alloc2, free2, opaque2, reserved2⟩
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, state2.trans state1,
    alloc2.trans alloc1, free2.trans free1, opaque2.trans opaque1, reserved2.trans reserved1⟩
  · rw [inPtr2, inPtr1, advance_add]
  · rw [outPtr2, outPtr1, advance_add]

theorem caller_raw_output {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) :
    ∃ output, h.bytes ob = some output ∧ h.ro ob = false ∧ oo + z.avail_out.toNat ≤ output.size ∧
      ¬ DeflateOwned ds d ob := by
  obtain ⟨old, getter, _input, output, _separate⟩ := buffers
  have equal : old = z := Option.some.inj (getter.symm.trans good.live.hz)
  subst old
  rw [pointer] at output
  rcases output with null | ⟨_bytes, writable, outside⟩
  · cases null
  · rcases writable rfl with ⟨null, _⟩ | ⟨ref, off, array, ptr, get, ro, bound⟩
    · cases null
    · have same : ref = .blk ob ∧ off = oo := by simpa only [Ptr.ref.injEq] using ptr.symm
      rcases same with ⟨refEq, offEq⟩
      subst ref off
      exact ⟨array, get, ro, bound, fun mine => outside ob rfl ((stream_owned_deflate good ob).mpr mine)⟩

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (empty data tail).
After a complete zlib header, empty input and lookahead return Z_OK
without executing a strategy or emitting block bits on Z_NO_FLUSH. -/
theorem public_default_empty_data {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (status : d.status = BUSY_STATE) (empty : z.avail_in = 0)
    (look : d.lookahead = 0) :
    publicDataTail (some r) (some (.tab ds)) Z_NO_FLUSH h = .ok (Z_OK, h) := by
  unfold publicDataTail
  simp only [bind_app, pure_app, rdD_eq, good.live.hs, status,
    show (BUSY_STATE == GZIP_STATE) = false from by decide,
    show (BUSY_STATE == EXTRA_STATE) = false from by decide,
    show (BUSY_STATE == NAME_STATE) = false from by decide,
    show (BUSY_STATE == COMMENT_STATE) = false from by decide,
    show (BUSY_STATE == HCRC_STATE) = false from by decide,
    Bool.false_eq_true, ite_false, ldDeflateState_tab good.live.hs, zrd_eq, good.live.hz,
    empty, look, show ((0 : UInt32) != 0) = false from rfl,
    show (Z_NO_FLUSH != Z_NO_FLUSH) = false from rfl, Bool.false_and, Bool.false_or,
    show (Z_NO_FLUSH != Z_FINISH) = true from rfl, ite_true]

end Zlib.Deflate.Engine.Proofs
