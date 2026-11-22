import ZlibF.Proof.LibcMemory
import ZlibF.Proof.«inflate.c.copy-window-failure»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The second actual allocator call returns a fresh byte block of the
window size after the state record has been allocated and zeroed. -/
theorem inflateCopy_window_allocation_success
    {h : Heap} {source : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (allocator : DefAlloc z)
    (second : h.allocOk (h.nalloc + 1) = true) :
    let zeroed := allocIstHeap h InflateState.zeroed
    let bytes := 2 ^ s.wbits.toNat
    ZALLOCB (some source) ((1 : UInt32) <<< s.wbits) 1 zeroed =
      .ok (.ref (.blk zeroed.nextBlk) 0,
        Zlib.Zutil.Proofs.allocHeap zeroed bytes) := by
  dsimp only
  let zeroed := allocIstHeap h InflateState.zeroed
  have sourceZero : source.get zeroed = some z := by
    rw [ZStreamRef.get_allocIst]
    exact good.live.hz
  have freshZero : Fresh zeroed := fresh_allocIst good.fresh InflateState.zeroed
  have secondZero : zeroed.allocOk zeroed.nalloc = true := by
    simpa [zeroed, allocIstHeap] using second
  have size : ((1 : UInt32) <<< s.wbits).toNat = 2 ^ s.wbits.toNat :=
    shl_toNat_aux good.inv.win.wbits
  rw [zallocb_run sourceZero allocator.1]
  simpa [Zlib.Zutil.zcalloc, size, zeroed, allocIstHeap] using
    Zlib.Zutil.Proofs.zcalloc_ok_run zeroed z.«opaque»
      ((1 : UInt32) <<< s.wbits) 1 secondZero freshZero

open Std.WP in
open scoped C.HeapWP in
/-- Record and stream updates between allocation and copying preserve the byte table.
At the actual copy point the original window survives, and the fresh window retains
its allocator-provided contents outside the populated prefix. -/
theorem inflateCopy_window_memcpy_framed
    {h before : Heap} {source : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s) (window : s.window ≠ .null)
    (sameBytes : before.bytes = (Zlib.Zutil.Proofs.allocHeap
      (allocIstHeap h InflateState.zeroed) (2 ^ s.wbits.toNat)).bytes)
    (writable : before.ro (h.nextBlk + 1) = false) :
    let zeroed := allocIstHeap h InflateState.zeroed
    let fresh : Array UInt8 := Array.ofFn (n := 2 ^ s.wbits.toNat)
      (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
    ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
      let after := { before with
        bytes := upd before.bytes zeroed.nextBlk (some (copyRange fresh a 0 0 s.whave.toNat)) }
      memcpyB (.ref (.blk zeroed.nextBlk) 0) s.window s.whave.toNat before = .ok ((), after) ∧
      after.bytes w = some a ∧
      ∀ i, s.whave.toNat ≤ i → (after.bytes zeroed.nextBlk).bind (·[i]?) = fresh[i]? := by
  dsimp only
  rcases good.inv.win.block with empty | ⟨w, a, ptr, get, ro, size⟩
  · exact False.elim (window empty)
  let zeroed := allocIstHeap h InflateState.zeroed
  let n := 2 ^ s.wbits.toNat
  let fresh : Array UInt8 := Array.ofFn (n := n)
    (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
  have sourceLive : h.live w := by simp [Heap.live, get]
  have wBound : w < h.nextBlk := by
    by_cases bound : w < h.nextBlk
    · exact bound
    · exact False.elim (good.fresh w (by omega) sourceLive)
  have different : zeroed.nextBlk ≠ w := by
    simp [zeroed, allocIstHeap]
    omega
  have destination : before.bytes zeroed.nextBlk = some fresh := by
    rw [sameBytes]
    simp [zeroed, n, Zlib.Zutil.Proofs.allocHeap, fresh]
  have sourceGet : before.bytes w = some a := by
    rw [sameBytes]
    change (upd h.bytes (h.nextBlk + 1)
      (some (Array.ofFn (n := n)
        (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))))).get w = some a
    rw [upd_ne _ _ _ _ (by omega)]
    exact get
  have count : s.whave.toNat ≤ n := by
    rcases good.inv.win.ws with small | full
    · have hv := good.inv.win.hv
      omega
    · have hv := good.inv.win.hv
      omega
  have destinationRoom : 0 + s.whave.toNat ≤ fresh.size := by
    simpa [fresh, n] using count
  have sourceRoom : 0 + s.whave.toNat ≤ a.size := by omega
  have run := memcpyB_blk_ok destination sourceGet writable different destinationRoom sourceRoom
  have post := (memcpyB_range_frame zeroed.nextBlk w w 0 0 s.whave.toNat fresh a (· = some a)
    different.symm (Or.inl different) destinationRoom sourceRoom).le_wp before
    ⟨destination, sourceGet, writable, sourceGet⟩
  rw [wp_run, run] at post
  refine ⟨w, a, ptr, get, ?_, post.2.1, ?_⟩
  · simpa only [ptr] using run
  · intro i hi
    exact post.2.2 i (Or.inr (by omega))

/-- The actual window copy reads exactly `whave` source bytes and writes
them into the fresh allocation; the remaining bytes retain allocator
garbage, as in the translated `malloc` model. -/
theorem inflateCopy_window_memcpy_success
    {h : Heap} {source : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (good : Good h source zs z s)
    (window : s.window ≠ .null) :
    let zeroed := allocIstHeap h InflateState.zeroed
    let size := 2 ^ s.wbits.toNat
    let allocated := Zlib.Zutil.Proofs.allocHeap zeroed size
    let fresh : Array UInt8 := Array.ofFn (n := size)
      (fun i => Junk.of (zeroed.garbage zeroed.nalloc i.val))
    ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
      C.run (memcpyB (.ref (.blk zeroed.nextBlk) 0) s.window s.whave.toNat)
        allocated =
        .ok ((), { allocated with bytes := upd allocated.bytes zeroed.nextBlk (some (copyRange fresh a 0 0 s.whave.toNat)) }) := by
  let zeroed := allocIstHeap h InflateState.zeroed
  let allocated := Zlib.Zutil.Proofs.allocHeap zeroed (2 ^ s.wbits.toNat)
  obtain ⟨w, a, ptr, live, run, _⟩ := inflateCopy_window_memcpy_framed (before := allocated)
    good window rfl (by simp [allocated, zeroed, Zlib.Zutil.Proofs.allocHeap, allocIstHeap])
  exact ⟨w, a, ptr, live, run⟩

#print axioms inflateCopy_window_allocation_success
#print axioms inflateCopy_window_memcpy_framed
#print axioms inflateCopy_window_memcpy_success
end Zlib.Inflate.Proofs
