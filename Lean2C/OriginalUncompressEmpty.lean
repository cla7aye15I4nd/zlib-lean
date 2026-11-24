import Lean2C.OriginalUncompressMember
import ZlibF.Proof.«public-uncompress2-z»

/-! The null-destination, empty-input path through the two imported wrappers. -/
namespace Lean2C.OriginalUncompress
open C ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Public.Proofs.Uncompress Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Gzguts Zlib.Uncompr OriginalUncompressLoop OriginalUncompressLengths
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 350000

def initializedDecoder (h : Heap) : InflateState :=
  resetKeepState (h.nextBlk + 2) (resetPre (reset2Pre 5 15 (initState (.tab h.nextBlk))))

private def emptyPost (h : Heap) (src member : BPtr) : Heap :=
  let H := tmpFreed (initHeap h src)
  {H with streams := upd H.streams h.nextBlk (some {boundStream h src member with data_type := 0})}

private theorem empty_post_stream (h : Heap) (src p : BPtr) :
    (ZStreamRef.tab h.nextBlk).get (emptyPost h src p) = some {boundStream h src p with data_type := 0} := by
  simp only [ZStreamRef.get, emptyPost, upd_same]

theorem init_decoder_good {h : Heap} (fresh : Fresh h) (uniq : Uniq h) (src : BPtr)
    (alloc : h.allocOk h.nalloc = true) :
    Good (initHeap h src) (.tab h.nextBlk) (h.nextBlk + 2) (initStreamRec h src) (initializedDecoder h) := by
  obtain ⟨_, _, rfl, good, _⟩ := inflateInit2_ok (preHeap_uniq fresh uniq src) (preHeap_fresh fresh src)
    (preHeap_stream h src) alloc (Or.inl rfl) (Or.inl rfl) (by simp) (version_byte _) params15
  exact good

private theorem empty_bound_loop {H : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    (fresh : Fresh H) (live : Live H (.tab k) i z s)
    (head : s.mode = HEAD) (wrap : s.wrap ≠ 0) (window : s.wsize = 0) (bits : s.bits = 0)
    (last : s.last = 0) (noInput : z.avail_in = 0) (p : BPtr) (nz : p ≠ .null) :
    let bound := {z with next_out := p, avail_out := 0}
    let start := (ZStreamRef.tab k).put H bound
    cdoWhile (abiBody (some (.tab k))) (fun l => pure (l.err == Z_OK, l)) ⟨Z_OK, 0, 0⟩ start =
      .ok (⟨Z_BUF_ERROR, 0, 0⟩, {tmpFreed H with streams := upd H.streams k (some {bound with data_type := 0})}) := by
  dsimp only
  let bound := {z with next_out := p, avail_out := 0}
  let G : Heap := {H with streams := upd H.streams k (some bound)}
  rw [put_tab_eq (H := H) (k := k) live.hz]
  have active : Live G (.tab k) i bound s :=
    ⟨upd_same H.streams k (some bound), live.hs, live.zst, live.back, live.mode, live.zalloc, live.zfree⟩
  have hf : Fresh G := fresh_put_tab live.hz bound fresh
  have loop := empty_input_loop false hf active head wrap window bits last noInput rfl nz
  have present : (tmpFreed G).streams k = some bound := active.hz
  rw [loop_eq, put_tab_eq (H := tmpFreed G) (k := k) present] at loop
  simpa only [G, tmpFreed, syncBuf, syncAlloc, freeWin, upd_upd] using loop

private theorem empty_start_loop {h : Heap} (fresh : Fresh h) (uniq : Uniq h) (src member : BPtr)
    (nz : member ≠ .null) (alloc : h.allocOk h.nalloc = true) :
    cdoWhile (abiBody (some (.tab h.nextBlk))) (fun l => pure (l.err == Z_OK, l))
      ⟨Z_OK, 0, 0⟩ (startHeap h src member) = .ok (⟨Z_BUF_ERROR, 0, 0⟩, emptyPost h src member) := by
  have good := init_decoder_good fresh uniq src alloc
  have run := empty_bound_loop (H := initHeap h src) (k := h.nextBlk) (i := h.nextBlk + 2)
    (z := initStreamRec h src) (s := initializedDecoder h) good.fresh good.live rfl
    (by change (5 : Int32) ≠ 0; decide) rfl rfl rfl (initStreamRec_fields h src).2 member nz
  have tables (H : Heap) : (tmpFreed H).streams = H.streams := rfl
  simpa only [startHeap, boundStream, emptyPost, tables] using run

private theorem empty_end {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (l : Live h r i z s) (window : s.window = .null) (release : z.zfree = .fn "zcfree") :
    inflateEnd (some r) h = .ok (Z_OK, r.put (freeIst h i) {z with state := none}) := by
  unfold inflateEnd
  isimp [stateCheck_live l, l.zst, l.hz, l.hs, window, zfrees_run l.hz release l.hs]

private theorem store_unchanged {h : Heap} {p : BPtr} {v : UInt64} (cell : LengthCell h p v) :
    store64 p v h = .ok ((), h) := by
  obtain ⟨g, run, st⟩ := store64_writable v cell.2
  have ne : lengthBytes v ≠ [] := by intro eq; have := congrArg List.length eq; simp [lengthBytes_length] at this
  rwa [store_eq_writeOut st ne, cell_self_write cell] at run

private theorem zero_writes {h : Heap} {sl dl : BPtr} (sc : LengthCell h sl 0) (dc : LengthCell h dl 0) :
    abiUpdates sl dl 0 0 h = .ok ((), h) := by
  simp only [abiUpdates, bind_app, load64_cell sc, load64_cell dc, UInt64.sub_zero,
    store_unchanged sc, store_unchanged dc]

private theorem init_next (h : Heap) (src : BPtr) : (initHeap h src).nextBlk = h.nextBlk + 2 + 1 := by
  simp only [initHeap, initOkHeap, reset2Heap_null _ _ _ (by rfl : (initState (.tab h.nextBlk)).window = .null),
    setI_nextBlk, ZStreamRef.put_nextBlk, allocIstHeap, preHeap, localHeap]

private theorem kept_after_empty {h : Heap} (fresh : Fresh h) (src p : BPtr) :
    ByteViewsKept h (emptyPost h src p) where
  bytes b live := by
    have a : b < h.nextBlk := Nat.lt_of_not_ge (fun ge => fresh b ge (Or.inl live))
    have n3 : b ≠ h.nextBlk + 2 + 1 := by omega
    have nb := init_next h src
    obtain ⟨g, ro, _⟩ := initHeap_get h src (.blk b)
    change (initHeap h src).bytes b = (localHeap h).bytes b at g
    change (initHeap h src).ro b = (localHeap h).ro b at ro
    obtain ⟨old, write⟩ := (localHeap_kept fresh).bytes b live
    simp only [emptyPost, tmpFreed, syncAlloc, syncBuf, freeWin, nb, upd_ne _ _ _ _ n3]
    exact ⟨g.trans old, ro.trans write⟩
  dstates := by simp only [emptyPost, tmpFreed, syncAlloc, syncBuf, freeWin, initHeap, initOkHeap,
    reset2Heap_null _ _ _ (by rfl : (initState (.tab h.nextBlk)).window = .null), setI, ZStreamRef.put_dstates, allocIstHeap, preHeap, localHeap, streamHeap]
  static := by simp only [emptyPost, tmpFreed, syncAlloc, syncBuf, freeWin, initHeap, initOkHeap,
    reset2Heap_null _ _ _ (by rfl : (initState (.tab h.nextBlk)).window = .null), setI, ZStreamRef.put_static, allocIstHeap, preHeap, localHeap, streamHeap]
  borrow := by
    simpa only [emptyPost, tmpFreed, syncBuf, syncAlloc, freeWin, preHeap, localHeap, streamHeap] using (initHeap_get h src (.blk 0)).2.2

def releaseLocals (k : Nat) : M Unit := do
  freeB (.ref (.blk (k + 1)) 0)
  freeZStream (some (.tab k))

theorem release_locals {h : Heap} {k : Nat} {a : Array UInt8} {z : ZStream}
    (bytes : h.bytes (k + 1) = some a) (rw_ : h.ro (k + 1) = false) (stream : h.streams k = some z) :
    releaseLocals k h = .ok ((), freedHeap h k) := by
  have free := freeZStream_local_run (H := reservedFreed h k) stream
  simp only [releaseLocals, bind_app, freeB_reserved_run bytes rw_, free, freedHeap]

theorem release_ended {H : Heap} {k i : Nat} {z : ZStream} {s : InflateState} {a : Array UInt8}
    (live : Live {H with streams := upd H.streams k (some z)} (.tab k) i z s)
    (window : s.window = .null) (release : z.zfree = .fn "zcfree")
    (raw : H.bytes (k + 1) = some a) (ro : H.ro (k + 1) = false) :
    ∃ after, inflateEnd (some (.tab k)) {H with streams := upd H.streams k (some z)} = .ok (Z_OK, after) ∧
      releaseLocals k after = .ok ((), freedHeap (freeIst H i) k) := by
  let G : Heap := {H with streams := upd H.streams k (some z)}
  have old : (freeIst G i).streams k = some z := upd_same H.streams k (some z)
  obtain fin := empty_end live window release
  rw [put_tab_eq (H := freeIst G i) (k := k) old] at fin
  let F : Heap := {freeIst G i with streams := upd G.streams k (some {z with state := none})}
  refine ⟨F, fin, ?_⟩
  have ss : F.streams k = some {z with state := none} := upd_same G.streams k _
  rw [release_locals (h := F) raw ro ss]
  simp only [F, G, freedHeap, reservedFreed, freeIst, upd_upd]

private theorem empty_epilogue {h : Heap} (fresh : Fresh h) (uniq : Uniq h) (src p : BPtr)
    (alloc : h.allocOk h.nalloc = true) :
    ∃ after, inflateEnd (some (.tab h.nextBlk)) (emptyPost h src p) = .ok (Z_OK, after) ∧
      releaseLocals h.nextBlk after = .ok ((), freedHeap (freeIst (tmpFreed (initHeap h src)) (h.nextBlk + 2)) h.nextBlk) := by
  let z := {boundStream h src p with data_type := 0}
  let r := ZStreamRef.tab h.nextBlk
  let i := h.nextBlk + 2
  let H := emptyPost h src p
  have good := init_decoder_good fresh uniq src alloc
  have l : Live H r i z (initializedDecoder h) := by
    refine ⟨empty_post_stream h src p, ?_, good.live.zst, good.live.back, good.live.mode, good.live.zalloc, good.live.zfree⟩
    simpa only [H, emptyPost, tmpFreed, syncBuf, syncAlloc, freeWin] using good.live.hs
  have nb := init_next h src
  have apart : h.nextBlk + 1 ≠ h.nextBlk + 2 + 1 := by omega
  obtain ⟨raw, write, _⟩ := initHeap_get h src (.blk (h.nextBlk + 1))
  change (initHeap h src).bytes (h.nextBlk + 1) = (localHeap h).bytes (h.nextBlk + 1) at raw
  change (initHeap h src).ro (h.nextBlk + 1) = (localHeap h).ro (h.nextBlk + 1) at write
  obtain ⟨b, ro⟩ := localHeap_reserved h
  have raw' : (tmpFreed (initHeap h src)).bytes (h.nextBlk + 1) = some (reservedBytes h) := by
    simp only [tmpFreed, syncAlloc, syncBuf, freeWin, nb, upd_ne _ _ _ _ apart]
    exact raw.trans b
  have ro' : (tmpFreed (initHeap h src)).ro (h.nextBlk + 1) = false := by
    simp only [tmpFreed, syncAlloc, syncBuf, freeWin, nb, upd_ne _ _ _ _ apart]
    exact write.trans ro
  exact release_ended (H := tmpFreed (initHeap h src)) (z := z) l rfl rfl raw' ro'

/-- With a null destination and both caller lengths zero, the source programs
return the same status and final heap for every nonnull choice of the member
address. Both length cells can name the same bytes. The shared automatic frame
and its cleanup are those of the Lean ABI. -/
theorem empty_input_wrapper {h : Heap} (fresh : Fresh h) (uniq : Uniq h) (src : BPtr)
    {sb so db doff : Nat} (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0)
    (sourceCell : LengthCell h (.ref (.blk sb) so) 0) (destCell : LengthCell h (.ref (.blk db) doff) 0) :
    ∃ after, ∀ (generated : Bool) (p : BPtr), p ≠ .null →
      sourceAt generated (.tab h.nextBlk) p .null (.ref (.blk db) doff) src (.ref (.blk sb) so)
        (do freeB (.ref (.blk (h.nextBlk + 1)) 0); freeZStream (some (.tab h.nextBlk))) (localHeap h) =
      .ok (if h.allocOk h.nalloc then Z_DATA_ERROR else Z_MEM_ERROR, after) := by
  let r := ZStreamRef.tab h.nextBlk
  let sl := Ptr.ref (BRef.blk sb) so
  let dl := Ptr.ref (BRef.blk db) doff
  have lsc := load64_cell ((localHeap_kept fresh).cell_of sourceCell)
  have ldc := load64_cell ((localHeap_kept fresh).cell_of destCell)
  have guard : guardWith load64 .null dl src sl (localHeap h) = .ok (false, localHeap h) := by
    simp [guardWith, sl, dl, bind_app, lsc, ldc]
  have prepare := prepare_run h src
  change updZ (some r) (OriginalUncompressInit.setInput src) (localHeap h) = _ at prepare
  have ver := version_run (preHeap h src)
  by_cases alloc : h.allocOk h.nalloc = true
  · refine ⟨freedHeap (freeIst (tmpFreed (initHeap h src)) (h.nextBlk + 2)) h.nextBlk, ?_⟩
    intro generated p nz
    have entered := bind_run h src p
    change updZ (some r) (OriginalUncompressInit.setOutput p) (initHeap h src) = _ at entered
    have loop := empty_start_loop fresh uniq src p nz alloc
    let z := {boundStream h src p with data_type := 0}
    have read : ldZ (some r) (emptyPost h src p) = .ok (z, emptyPost h src p) :=
      ldZStream_ok (empty_post_stream h src p)
    have kept := kept_after_empty fresh src p
    have write := zero_writes (kept.cell_of sourceCell) (kept.cell_of destCell)
    obtain ⟨endH, endRun, release⟩ := empty_epilogue fresh uniq src p alloc
    rw [at_abi_raw generated r p .null src sb so db doff sa da]
    change wrapperAt (some r) p .null dl src sl (releaseLocals h.nextBlk) _ _ (localHeap h) = _
    have countIn : z.avail_in = 0 := (initStreamRec_fields h src).2
    have countOut : z.avail_out = 0 := rfl
    simp only [wrapperAt, bind_app, guard, Bool.false_eq_true, ↓reduceIte, sl, dl, lsc, ldc,
      beq_self_eq_true, Bool.and_true, prepare, ver, init_ok_run fresh src alloc,
      bne_self_eq_false, entered, loop, read, countIn, countOut, UInt64.zero_add, show (0 : UInt32).toUInt64 = 0 from rfl,
      write, endRun, release, pure_app, alloc, r]
    rfl
  · refine ⟨freedHeap (memHeap h src) h.nextBlk, ?_⟩
    intro generated p _
    obtain ⟨raw, ro⟩ := memHeap_reserved h src
    have freed := release_locals raw ro (memHeap_stream h src)
    have fail := init_fail_run fresh src alloc
    change inflateInit_ _ _ _ _ = .ok (Z_MEM_ERROR, memHeap h src) at fail
    rw [at_abi_raw generated r p .null src sb so db doff sa da]
    change wrapperAt (some r) p .null dl src sl (releaseLocals h.nextBlk) _ _ (localHeap h) = _
    simp only [wrapperAt, bind_app, guard, Bool.false_eq_true, ↓reduceIte, sl, dl, lsc, ldc,
      prepare, ver, fail, show (Z_MEM_ERROR != Z_OK) = true by decide, freed, pure_app, alloc, r]

/-- The reference selector uses offset 104 in the automatic stream block.
The Lean ABI selector allocates its byte view separately. In the shared
frame, these two choices give the exact same return and heap when both
lengths are zero, including refusal of the decoder allocation. -/
theorem empty_member_abi {h : Heap} (fresh : Fresh h) (uniq : Uniq h) (src : BPtr)
    {sb so db doff : Nat} (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0)
    (sourceCell : LengthCell h (.ref (.blk sb) so) 0) (destCell : LengthCell h (.ref (.blk db) doff) 0) :
    let dl := Ptr.ref (BRef.blk db) doff
    let sl := Ptr.ref (BRef.blk sb) so
    sourceAt false (.tab h.nextBlk) (.ref (.blk h.nextBlk) 104) .null dl src sl
      (do freeB (.ref (.blk (h.nextBlk + 1)) 0); freeZStream (some (.tab h.nextBlk))) (localHeap h) =
      uncompress2_z .null dl src sl h := by
  dsimp only
  obtain ⟨_, eq⟩ := empty_input_wrapper fresh uniq src sa da sourceCell destCell
  rw [← source_abi true .null src sb so db doff sa da]
  unfold source
  simp only [bind_app, allocLocalZ_run fresh, stackAddr, allocLocal_run fresh]
  exact (eq false (.ref (.blk h.nextBlk) 104) (by simp)).trans
    (eq true (.ref (.blk (h.nextBlk + 1)) 0) (by simp)).symm

#print axioms empty_member_abi
#print axioms empty_input_wrapper
end Lean2C.OriginalUncompress
