import Lean2C.OriginalUncompressZero
import Lean2C.OriginalUncompressEmpty

/-! Returning from uncompress2_z with a null destination and zero capacity. -/
namespace Lean2C.OriginalUncompress
open C ZlibF.Spec ZlibF.Spec.Public ZlibF.Spec.Public.Proofs.Uncompress
open Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Uncompr Zlib.Gzguts
open OriginalUncompressLoop OriginalUncompressLengths
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 8192

private def finish (k : Nat) (sl dl : BPtr) (l : UncLoop) : M Int32 := do
  let z ← ldZ (some (.tab k))
  let unused := l.len + z.avail_in.toUInt64
  abiUpdates sl dl unused (l.left + z.avail_out.toUInt64)
  let _ ← inflateEnd (some (.tab k))
  releaseLocals k
  return finalCode l.err unused

private theorem raw_range {H : Heap} {b off : Nat} (w : Writable H (.ref (.blk b) off) 8) :
    ∃ a, H.bytes b = some a ∧ H.ro b = false ∧ off + 8 ≤ a.size := by
  rcases w with ⟨no, _⟩ | ⟨r, i, a, eq, get, ro, fit⟩
  · cases no
  · cases eq; exact ⟨a, get, ro, fit⟩

private def putRaw (H : Heap) (b : Nat) (a : Array UInt8) := Space.put H (BRef.blk b) a

private theorem raw_after {H : Heap} {b d : Nat} {a u : Array UInt8} (v : Array UInt8)
    (old : H.bytes b = some a) (get : H.bytes d = some u) (size : v.size = a.size) :
    ∃ w, (putRaw H b v).bytes d = some w ∧ w.size = u.size := by
  by_cases eq : d = b
  · subst d; cases Option.some.inj (old.symm.trans get)
    exact ⟨v, upd_same .., size⟩
  · exact ⟨u, (upd_ne H.bytes b _ d eq).trans get, rfl⟩

private def subtractRaw (b off : Nat) (n : UInt64) : M Unit := do
  let ptr : BPtr := .ref (.blk b) off
  store64 ptr ((← load64 ptr) - n)

private theorem raw_step {H : Heap} {b off : Nat} {a : Array UInt8}
    (get : H.bytes b = some a) (ro : H.ro b = false) (fit : off + 8 ≤ a.size) (unused : UInt64) :
    ∃ v, v.size = a.size ∧ ∀ k p, subtractRaw b off unused (Refill.heap k p H) =
      .ok ((), Refill.heap k p (putRaw H b v)) := by
  refine ⟨store64Array a off (le64 a off - unused), by simp [store64Array], ?_⟩
  intro k p
  have read := load64_ref (h := Refill.heap k p H) (r := .blk b) (i := off) get fit
  have write := store64_ref (h := Refill.heap k p H) (r := .blk b) (i := off)
    (v := le64 a off - unused) get ro fit
  simp only [subtractRaw, bind_app, read, write]
  rfl

/-- Execute both read/modify/writes, including a second read from the same
cell, then discard the only differing stream record during cleanup. -/
private theorem finish_pair {H : Heap} {k i sb so db doff : Nat} {z : ZStream} {s : InflateState}
    {a : Array UInt8} (l : UncLoop) (live : Live H (.tab k) i z s) (window : s.window = .null)
    (release : z.zfree = .fn "zcfree") (sw : Writable H (.ref (.blk sb) so) 8)
    (dw : Writable H (.ref (.blk db) doff) 8) (raw : H.bytes (k + 1) = some a) (ro : H.ro (k + 1) = false) :
    ∃ rc after, ∀ p, finish k (.ref (.blk sb) so) (.ref (.blk db) doff) l (Refill.heap k p H) =
      .ok (rc, after) := by
  obtain ⟨sa, sg, sr, sf⟩ := raw_range sw
  obtain ⟨da, dg, dr, df⟩ := raw_range dw
  let unused := l.len + z.avail_in.toUInt64
  let room := l.left + z.avail_out.toUInt64
  obtain ⟨v, size, one⟩ := raw_step sg sr sf unused
  obtain ⟨d, g1, ds⟩ := raw_after v sg dg size
  let H1 := putRaw H sb v
  obtain ⟨w, size', two⟩ := raw_step (H := H1) g1 dr (ds ▸ df) room
  let H2 := putRaw H1 db w
  obtain ⟨a1, get1, _⟩ := raw_after v sg raw size
  obtain ⟨a2, get2, _⟩ := raw_after w g1 get1 size'
  refine ⟨finalCode l.err unused, freedHeap (freeIst H2 i) k, ?_⟩
  intro p
  let zp := {z with next_out := p}
  have hz : (ZStreamRef.tab k).get (Refill.heap k p H) = some zp := by
    rw [Refill.heap_eq_put live.hz]; exact ZStreamRef.get_put_same live.hz _
  have reb : Refill.heap k p H2 = {H2 with streams := upd H2.streams k (some zp)} := by
    have get : H2.streams k = some z := live.hz
    simp only [Refill.heap, get, zp]
  have final : Live {H2 with streams := upd H2.streams k (some zp)} (.tab k) i zp s :=
    {live with hz := upd_same .., hs := live.hs}
  obtain ⟨endH, endRun, freed⟩ := release_ended final window release get2 ro
  have updates : abiUpdates (.ref (.blk sb) so) (.ref (.blk db) doff) unused room (Refill.heap k p H) =
      .ok ((), Refill.heap k p H2) := by
    have seq : abiUpdates (.ref (.blk sb) so) (.ref (.blk db) doff) unused room =
        (subtractRaw sb so unused >>= fun _ => subtractRaw db doff room) := by
      simp [abiUpdates, subtractRaw, C.M_bind_assoc]
    rw [seq, bind_app, one k p]; exact two k p
  rw [← reb] at endRun
  have up : abiUpdates (.ref (.blk sb) so) (.ref (.blk db) doff)
      (l.len + zp.avail_in.toUInt64) (l.left + zp.avail_out.toUInt64) (Refill.heap k p H) =
      .ok ((), Refill.heap k p H2) := updates
  simp only [finish, bind_app, ldZ, ldZStream_ok hz, up, endRun, freed, pure_app]
  rfl

private def afterInit (k : Nat) (sl dl : BPtr) (n : UInt64) : M Int32 := do
  let l ← cdoWhile (abiBody (some (.tab k))) (fun l => pure (l.err == Z_OK, l)) ⟨Z_OK, n, 0⟩
  finish k sl dl l

private theorem same_start (h : Heap) (src base p : BPtr) :
    startHeap h src p = Refill.heap h.nextBlk p (startHeap h src base) := by
  have live := initHeap_stream h src
  have get : (startHeap h src base).streams h.nextBlk = some (boundStream h src base) :=
    (ZStreamRef.get_put_same (r := .tab h.nextBlk) live (boundStream h src base))
  rw [Refill.heap_eq_put get, startHeap, startHeap, ZStreamRef.put_put]
  rfl

private theorem start_pair {h : Heap} {src : BPtr} {sb so db doff : Nat} {n : UInt64}
    {input : List UInt8} (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (bytes : Bytes h src n.toNat input)
    (sourceCell : LengthCell h (.ref (.blk sb) so) n) (destCell : LengthCell h (.ref (.blk db) doff) 0)
    (alloc : h.allocOk h.nalloc = true) (p : BPtr) (address : p ≠ .null) :
    let run := afterInit h.nextBlk (.ref (.blk sb) so) (.ref (.blk db) doff) n
    run (startHeap h src p) = run (startHeap h src (.ref (.blk (h.nextBlk + 1)) 0)) := by
  let out : BPtr := .ref (.blk (h.nextBlk + 1)) 0
  let e : Proofs.Uncompress.Env := ⟨h, src, out, input, n.toNat, 0⟩
  have ok : EnvOK e := ⟨fresh, bytes, bytes_length bytes, Or.inl ⟨rfl, rfl⟩, by simp [e, out],
    Or.inr (Or.inl rfl), bytes_bound bytes fit, by change 0 < 2 ^ 63; decide⟩
  obtain ⟨s, start⟩ := start_state ok uniq globals fit alloc n 0 rfl rfl
  have initial := init_decoder_good fresh uniq src alloc
  have found : (startHeap h src out).istates (h.nextBlk + 2) = some (initializedDecoder h) := by
    simpa only [startHeap, ZStreamRef.put_istates] using initial.live.hs
  have same := Option.some.inj (start.good.live.hs.symm.trans found)
  subst s
  have mode : Refill.WrapperMode (initializedDecoder h) := Or.inl ⟨rfl, Or.inr rfl⟩
  obtain ⟨l, H, t, loops, ended, state, window⟩ :=
    zero_output_loop ok rfl start.toSafeState mode rfl p address
  obtain ⟨left, right⟩ := loops false
  rw [loop_eq] at left right
  obtain ⟨_, _, _, _, _, _, z, _, s, fin⟩ := ended
  obtain rfl := Option.some.inj (fin.good.live.hs.symm.trans state)
  obtain ⟨written, _, len, agree⟩ := fin.agree
  have empty : written = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp len)
  rw [empty, writeOut_nil] at agree
  have dst := agree.cell destCell (cell_blocks destCell)
  have srcC := agree.cell sourceCell (cell_blocks sourceCell)
  obtain ⟨rc, after, finishRun⟩ := finish_pair l fin.good.live window fin.alloc.2 srcC.2 dst.2
    fin.reservedBytes fin.reservedRo
  have id : Refill.heap e.k z.next_out H = H := by
    have live : H.streams e.k = some z := fin.good.live.hz
    rw [Refill.heap_eq_put live]
    exact put_self_tab fin.good.live.hz
  have baseline := finishRun z.next_out
  change finish e.k _ _ l (Refill.heap e.k z.next_out H) = _ at baseline
  rw [id] at baseline
  dsimp only
  rw [same_start h src out p]
  change (afterInit e.k _ _ n) (Refill.heap e.k p (startHeap e.h₀ e.source e.out0)) =
    (afterInit e.k _ _ n) (startHeap e.h₀ e.source e.out0)
  have base : cdoWhile (abiBody (some (.tab e.k))) (fun l => pure (l.err == Z_OK, l)) ⟨Z_OK, n, 0⟩
      (startHeap e.h₀ e.source e.out0) = .ok (l, H) := left
  have alt : cdoWhile (abiBody (some (.tab e.k))) (fun l => pure (l.err == Z_OK, l)) ⟨Z_OK, n, 0⟩
      (Refill.heap e.k p (startHeap e.h₀ e.source e.out0)) = .ok (l, Refill.heap e.k p H) := right
  simp only [afterInit, bind_app, base, alt]
  exact (finishRun p).trans baseline.symm

/-- With zero capacity, the pinned member address and the ABI byte view
have the same observable result on arbitrary valid input in the common
automatic frame. No separation between the raw length cells is required. -/
theorem zero_member_abi {h : Heap} {src : BPtr} {sb so db doff : Nat} {n : UInt64}
    {input : List UInt8} (generated : Bool) (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (bytes : Bytes h src n.toNat input)
    (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0)
    (sourceCell : LengthCell h (.ref (.blk sb) so) n) (destCell : LengthCell h (.ref (.blk db) doff) 0) :
    let sl := Ptr.ref (BRef.blk sb) so
    let dl := Ptr.ref (BRef.blk db) doff
    sourceAt generated (.tab h.nextBlk) (.ref (.blk h.nextBlk) 104) .null dl src sl
      (releaseLocals h.nextBlk) (localHeap h) = uncompress2_z .null dl src sl h := by
  let r := ZStreamRef.tab h.nextBlk
  let sl : BPtr := .ref (.blk sb) so
  let dl : BPtr := .ref (.blk db) doff
  let member : BPtr := .ref (.blk h.nextBlk) 104
  let view : BPtr := .ref (.blk (h.nextBlk + 1)) 0
  have ln := load64_cell ((localHeap_kept fresh).cell_of sourceCell)
  have ld := load64_cell ((localHeap_kept fresh).cell_of destCell)
  have valid : (decide (n > 0) && src == Ptr.null) = false := by
    by_cases empty : src = .null
    · rcases bytes with ⟨_, zero, _⟩ | ⟨_, _, _, eq, _⟩
      · have z : n = 0 := UInt64.toNat_inj.mp zero
        simp [z]
      · rw [empty] at eq; cases eq
    · simp [empty]
  have no : ¬ (0 < n ∧ src = Ptr.null) := by simpa using valid
  have guard : guardWith load64 .null dl src sl (localHeap h) = .ok (false, localHeap h) := by
    simp [guardWith, sl, dl, ln, ld, no]
  have prepare := prepare_run h src
  change updZ (some r) (OriginalUncompressInit.setInput src) (localHeap h) = _ at prepare
  have ver := version_run (preHeap h src)
  have readS : load64 sl (localHeap h) = .ok (n, localHeap h) := ln
  have readD : load64 dl (localHeap h) = .ok (0, localHeap h) := ld
  dsimp only
  rw [← source_abi true .null src sb so db doff sa da]
  unfold source
  simp only [bind_app, allocLocalZ_run fresh, stackAddr, allocLocal_run fresh]
  rw [at_abi_raw generated r member .null src sb so db doff sa da,
    at_abi_raw true r view .null src sb so db doff sa da]
  · change wrapperAt (some r) member .null dl src sl (releaseLocals h.nextBlk) _ _ (localHeap h) =
      wrapperAt (some r) view .null dl src sl (releaseLocals h.nextBlk) _ _ (localHeap h)
    by_cases alloc : h.allocOk h.nalloc = true
    · have cut (p : BPtr) : wrapperAt (some r) p .null dl src sl (releaseLocals h.nextBlk) load64
          (abiUpdates sl dl) (localHeap h) = afterInit h.nextBlk sl dl n (startHeap h src p) := by
        have entered := bind_run h src p
        change updZ (some r) (OriginalUncompressInit.setOutput p) (initHeap h src) = _ at entered
        have initialized : inflateInit_ (some r) (.ref (.str 57) 0) 112 (preHeap h src) =
            .ok (Z_OK, initHeap h src) := init_ok_run fresh src alloc
        simp only [wrapperAt, bind_app, guard, Bool.false_eq_true, ↓reduceIte, readS, readD, beq_self_eq_true,
          Bool.and_true, prepare, ver, initialized, bne_self_eq_false, entered]
        simp only [afterInit, finish, finalCode, bind_app, r]
      rw [cut, cut]
      exact start_pair fresh uniq globals fit bytes sourceCell destCell alloc member (by simp [member])
    · have fail := init_fail_run fresh src alloc
      change inflateInit_ (some r) _ _ _ = .ok (Z_MEM_ERROR, memHeap h src) at fail
      simp only [wrapperAt, bind_app, guard, Bool.false_eq_true, ↓reduceIte, readS, readD, prepare, ver,
        fail, show (Z_MEM_ERROR != Z_OK) = true by decide]


/-- The selector uses the actual LP64 member offset inside the shared frame.
Together the null and non-null branches cover every accepted destination. -/
theorem member_abi {h : Heap} {dest src : BPtr} {sb so db doff : Nat} {n cap : UInt64}
    {input : List UInt8} (generated : Bool) (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (bytes : Bytes h src n.toNat input)
    (valid : dest = .null → cap = 0) (sa : UInt64.ofNat so % 8 = 0) (da : UInt64.ofNat doff % 8 = 0)
    (sourceCell : LengthCell h (.ref (.blk sb) so) n) (destCell : LengthCell h (.ref (.blk db) doff) cap) :
    let sl := Ptr.ref (BRef.blk sb) so
    let dl := Ptr.ref (BRef.blk db) doff
    sourceAt generated (.tab h.nextBlk) (.ref (.blk h.nextBlk) 104) dest dl src sl
      (releaseLocals h.nextBlk) (localHeap h) = uncompress2_z dest dl src sl h := by
  by_cases missing : dest = .null
  · subst dest; obtain rfl := valid rfl
    exact zero_member_abi generated fresh uniq globals fit bytes sa da sourceCell destCell
  · dsimp only
    rw [← source_abi generated dest src sb so db doff sa da]
    unfold source
    simp only [bind_app, allocLocalZ_run fresh, stackAddr, allocLocal_run fresh]
    exact congrFun (member_unused generated (.tab h.nextBlk) (.ref (.blk h.nextBlk) 104)
      (.ref (.blk (h.nextBlk + 1)) 0) dest _ src _ (releaseLocals h.nextBlk) missing) _

#print axioms zero_member_abi
#print axioms member_abi
end Lean2C.OriginalUncompress
