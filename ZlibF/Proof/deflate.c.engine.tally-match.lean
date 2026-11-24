import ZlibF.Proof.«deflate.c.engine.tally-distance»

/-! # The actual inline match-symbol tally -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees (length_code_tab)
open Zlib.Trees.Proofs.Out (TreesBase TreesStatic bumpFc dcodeN)
set_option autoImplicit false

def matchBytes (buf : Array UInt8) (d : DeflateState) (dist : UInt16) (len : UInt8) : Array UInt8 :=
  ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) dist.toUInt8).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) (dist >>> 8).toUInt8).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) len

def matchFrequencies (d : DeflateState) (dist : UInt16) (len : UInt8) : DeflateState :=
  { d with
    dyn_ltree := bumpFc d.dyn_ltree (length_code_tab[len.toNat]!.toNat + 256 + 1)
    dyn_dtree := bumpFc d.dyn_dtree (dcodeN (dist - 1).toNat) }

def matchTallyTail (s : DeflateStatePtr) (dist : UInt16) (len : UInt8) : M Bool := do
  let dist := dist - 1
  match s with
  | none => ub "null deflate_state"
  | some (.tab id) =>
    let lc ← index8 (.ref BRef.st_length_code 0) len.toNat
    freq_inc (.dstate_dyn_ltree id) (lc.toNat + 256 + 1)
    let dc ← Zlib.Deflate.d_code dist
    freq_inc (.dstate_dyn_dtree id) dc.toNat
    let d ← ldDeflateState s
    return d.sym_next == d.sym_end

theorem tally_distance_source (s : DeflateStatePtr) (distance length : UInt32) :
    tally_dist s distance length = (do
      Zlib.Trees.put_symbol_byte s distance.toUInt16.toUInt8
      Zlib.Trees.put_symbol_byte s (distance.toUInt16 >>> 8).toUInt8
      Zlib.Trees.put_symbol_byte s length.toUInt8
      matchTallyTail s distance.toUInt16 length.toUInt8) := by
  rfl

theorem match_tally_tail_run {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (wf : d.WellFormed) (static : TreesStatic h.static)
    (dist : UInt16) (len : UInt8) (bound : (dist - 1).toNat < 32768) :
    matchTallyTail (some (.tab ds)) dist len h =
      .ok (d.sym_next == d.sym_end, setD h ds (matchFrequencies d dist len)) := by
  let lc := length_code_tab[len.toNat]!
  let dl := { d with dyn_ltree := bumpFc d.dyn_ltree (lc.toNat + 256 + 1) }
  let hl := setD h ds dl
  have fit : len.toNat < length_code_tab.size := by
    rw [Zlib.Trees.Proofs.Out.length_code_tab_size]
    exact len.toNat_lt
  have get : Space.get h BRef.st_length_code = some length_code_tab := by
    simp [Space.get, static.length_code]
  have read : index8 (.ref BRef.st_length_code 0) len.toNat h = .ok (lc, h) := by
    simpa [OkOn, fit, lc] using Ptr.index_ok (off := 0) (i := len.toNat) get (by omega)
  have lcBound : lc.toNat ≤ 28 := by
    simpa [lc, fit] using Zlib.Trees.Proofs.Out.length_code_le len.toNat len.toNat_lt
  have incL := increment_literal_frequency state
    (show lc.toNat + 256 + 1 < d.dyn_ltree.size by rw [wf.1]; omega)
  obtain ⟨dc, code, codeNat, codeBound⟩ := distance_code_run (h := hl)
    (by simpa [hl] using static) (dist - 1) bound
  have incD := increment_distance_frequency (h := hl) (ds := ds) (d := dl) (i := dc.toNat)
    (by simp [hl]) (by change dc.toNat < d.dyn_dtree.size; rw [wf.2.1]; omega)
  unfold matchTallyTail
  simp only []
  rw [bind_app, read]
  simp only []
  rw [bind_app, incL]
  change (do
    let dc ← Zlib.Deflate.d_code (dist - 1)
    freq_inc (.dstate_dyn_dtree ds) dc.toNat
    let d ← ldDeflateState (some (.tab ds))
    pure (d.sym_next == d.sym_end)) hl = _
  rw [bind_app, code]
  simp only []
  rw [bind_app, incD]
  simp only [bind_app, ldDeflateState_tab (setD_dstates_same _ _ _)]
  simp only [hl, dl, setD_setD, matchFrequencies, codeNat, lc]
  rfl


/-- `_tr_tally_dist(s, distance, length, flush)`.
The actual inline macro packs the distance and length, updates both
frequencies and returns the exact full flag. It does not increment the
matches field: that write belongs to the separate _tr_tally function.
-/
theorem tally_match_run {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (base : TreesBase h ds d b buf) (distance length : UInt32)
    (positive : 1 ≤ distance.toNat) (distanceBound : distance.toNat ≤ 32768)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    tally_dist (some (.tab ds)) distance length h =
      .ok (d.sym_next + 3 == d.sym_end,
        setD (Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)) ds
          (matchFrequencies { d with sym_next := d.sym_next + 3 } distance.toUInt16 length.toUInt8)) := by
  let dist := distance.toUInt16
  let len := length.toUInt8
  let hb := Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d dist len)
  let dn := { d with sym_next := d.sym_next + 3 }
  let hn := setD hb ds dn
  have tail := match_tally_tail_run (h := hn) (ds := ds) (d := dn) (by simp [hn]) base.wf
    (by simpa [hn, hb] using base.static) dist len (match_distance_index distance positive distanceBound).2.2
  have packed := put_three_symbol_bytes_run base room dist.toUInt8 (dist >>> 8).toUInt8 len
  have source : tally_dist (some (.tab ds)) distance length = (do
      Zlib.Trees.put_symbol_byte (some (.tab ds)) dist.toUInt8
      Zlib.Trees.put_symbol_byte (some (.tab ds)) (dist >>> 8).toUInt8
      Zlib.Trees.put_symbol_byte (some (.tab ds)) len) >>= fun _ =>
        matchTallyTail (some (.tab ds)) dist len := by
    simp only [tally_distance_source, M_bind_assoc, dist, len]
  rw [source, bind_app, packed]
  change matchTallyTail (some (.tab ds)) dist len hn = _
  rw [tail]
  simp only [hn, setD_setD]
  rfl


def matchSymbolState (d : DeflateState) (distance length : UInt32) : DeflateState :=
  matchFrequencies { d with sym_next := d.sym_next + 3 } distance.toUInt16 length.toUInt8

theorem match_bytes_view (buf : Array UInt8) (d : DeflateState) (dist : UInt16) (len : UInt8)
    (fit : d.lit_bufsize.toNat + d.sym_next.toNat + 2 < buf.size) (i : Nat) :
    bfn (matchBytes buf d dist len) i =
      if i = d.lit_bufsize.toNat + d.sym_next.toNat + 2 then len
      else if i = d.lit_bufsize.toNat + d.sym_next.toNat + 1 then (dist >>> 8).toUInt8
      else if i = d.lit_bufsize.toNat + d.sym_next.toNat then dist.toUInt8
      else bfn buf i := by
  unfold matchBytes
  rw [bfn_set _ _ _ (by simp; omega)]
  rw [bfn_set _ _ _ (by simp; omega)]
  rw [bfn_set _ _ _ (by omega)]
  simp only [Nat.add_assoc]

theorem tally_match_trees {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d b buf) (distance length : UInt32)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    Zlib.Trees.Proofs.Out.TreesInvAt
      (setD (Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)) ds
        (matchSymbolState d distance length))
      ds (matchSymbolState d distance length) b (matchBytes buf d distance.toUInt16 length.toUInt8) := by
  have wf : (matchSymbolState d distance length).WellFormed := by
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := trees.base.wf
    exact ⟨by simpa [matchSymbolState, matchFrequencies] using w1,
      by simpa [matchSymbolState, matchFrequencies] using w2, w3, w4, w5, w6⟩
  have base := trees.base.step (matchBytes buf d distance.toUInt16 length.toUInt8)
    (by simp [matchBytes]) (matchSymbolState d distance length) wf rfl rfl rfl rfl rfl trees.base.pending_le
  have count : (matchSymbolState d distance length).sym_next.toNat = d.sym_next.toNat + 3 :=
    literal_count trees.base room 0
  have run : Zlib.Trees.Proofs.Out.TreesRun ds (matchSymbolState d distance length) := by
    have old := trees.run
    refine ⟨old.ldyn, old.lstat, old.ddyn, old.dstat, old.bldyn, old.blstat,
      old.bi_lo, old.bi_hi, old.bi_buf, ?_, ?_⟩
    · change (matchSymbolState d distance length).sym_next.toNat ≤ d.sym_end.toNat
      rw [count]
      exact room
    · rw [count]
      have mod := old.sym_next_mod
      omega
  exact ⟨base, run⟩

theorem match_good_after {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} (good : DGood h r ds z d)
    (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d b buf) (distance length : UInt32)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    DGood
      (setD (Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)) ds
        (matchSymbolState d distance length))
      r ds z (matchSymbolState d distance length) := by
  have treeResult := tally_match_trees trees distance length room
  let hb := Zlib.Trees.Proofs.Out.setB h b (matchBytes buf d distance.toUInt16 length.toUInt8)
  let dt := matchSymbolState d distance length
  have goodB : DGood hb r ds z d := good.bytes_set b _ buf trees.base.bytes (by simp [matchBytes])
  have inv : DStInv hb ds dt :=
    { goodB.inv with
      wf := treeResult.base.wf
      blocks := goodB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sym := ⟨goodB.inv.sym.1, goodB.inv.sym.2.1, treeResult.run.sym_next_le, treeResult.run.sym_next_mod⟩ }
  have shape := shape_setD goodB.live.hs dt
  refine ⟨?_, DStInv.congr (h := hb) (h' := setD hb ds dt) rfl rfl rfl rfl inv,
    shape.uniq goodB.uniq, shape.fresh rfl goodB.fresh,
    ⟨dt, b, matchBytes buf d distance.toUInt16 length.toUInt8, treeResult⟩⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp, good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

end Zlib.Deflate.Engine.Proofs
