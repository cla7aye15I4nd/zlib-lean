import ZlibF.Proof.«deflate.c.engine.lminner»
import ZlibF.Proof.«deflate.c.engine.initial»
import ZlibF.Proof.«trees.c.tally»

/-! # The actual inline literal tally used by the strategies

This proves tally_lit itself. The inline macro and `_tr_tally` share the post-increment byte store.
The arithmetic and tree updates of the macro are proved here.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Trees.Proofs.Out (TreesBase TreesInvAt TreesRun bumpFc)
set_option autoImplicit false

def literalBytes (buf : Array UInt8) (d : DeflateState) (c : UInt8) : Array UInt8 :=
  ((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) 0).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) 0).set!
    (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) c

def literalState (d : DeflateState) (c : UInt8) : DeflateState :=
  { d with sym_next := d.sym_next + 3, dyn_ltree := bumpFc d.dyn_ltree c.toNat }

/-- Exact symbol contents and the unchanged prefix/suffix. This is the
byte-level input required later by the payload encoder's overlay proof. -/
theorem literal_bytes_view (buf : Array UInt8) (d : DeflateState) (c : UInt8)
    (fit : d.lit_bufsize.toNat + d.sym_next.toNat + 2 < buf.size) (i : Nat) :
    bfn (literalBytes buf d c) i =
      if i = d.lit_bufsize.toNat + d.sym_next.toNat + 2 then c
      else if i = d.lit_bufsize.toNat + d.sym_next.toNat + 1 then 0
      else if i = d.lit_bufsize.toNat + d.sym_next.toNat then 0
      else bfn buf i := by
  unfold literalBytes
  rw [bfn_set _ _ _ (by simp; omega)]
  rw [bfn_set _ _ _ (by simp; omega)]
  rw [bfn_set _ _ _ (by omega)]
  simp only [Nat.add_assoc]

theorem store_symbol_byte {h : Heap} {b off i : Nat} {buf : Array UInt8} (v : UInt8)
    (get : h.bytes b = some buf) (rw : h.ro b = false) (bound : off + i < buf.size) :
    store_at (.ref (.blk b) off) i v h =
      .ok ((), Zlib.Trees.Proofs.Out.setB h b (buf.set! (off + i) v)) := by
  have add : padd (.ref (.blk b) off : BPtr) i h = .ok (.ref (.blk b) (off + i), h) :=
    Ptr.add_nat_ok (off := off) (n := i) (show Space.get h (BRef.blk b) = some buf from get) (by omega)
  have put := Ptr.store_ok (r := BRef.blk b) (T := UInt8) (a := buf) (off := off + i) (v := v)
    get rw bound
  unfold store_at
  rw [bind_app, add]
  exact put

theorem put_symbol_byte_run {h : Heap} {ds b off : Nat} {d : DeflateState} {buf : Array UInt8}
    (v : UInt8) (state : h.dstates ds = some d) (sym : d.sym_buf = .ref (.blk b) off)
    (get : h.bytes b = some buf) (writeable : h.ro b = false) (fit : off + d.sym_next.toNat < buf.size) :
    Zlib.Trees.put_symbol_byte (some (.tab ds)) v h =
      .ok ((), Zlib.Trees.Proofs.Out.setD (Zlib.Trees.Proofs.Out.setB h b (buf.set! (off + d.sym_next.toNat) v)) ds {d with sym_next := d.sym_next + 1}) := by
  let d' := {d with sym_next := d.sym_next + 1}
  have add : Ptr.add (.ref (.blk b) off : BPtr) d.sym_next.toNat h = .ok (.ref (.blk b) (off + d.sym_next.toNat), h) := Ptr.add_nat_ok (off := off) (n := d.sym_next.toNat)
    (show Space.get h (BRef.blk b) = some buf from get) (by omega)
  have store := Ptr.store_ok (T := UInt8) (r := BRef.blk b) (h := Zlib.Trees.Proofs.Out.setD h ds d')
    (off := off + d.sym_next.toNat) (v := v) (a := buf) get writeable fit
  have address : Ptr.add d.sym_buf d.sym_next.toNat h = .ok (.ref (.blk b) (off + d.sym_next.toNat), h) := by rw [sym]; exact add
  unfold Zlib.Trees.put_symbol_byte
  simp only [bind_app, Zlib.Trees.Proofs.Out.rd_run state, address, Zlib.Trees.Proofs.Out.md_run state]
  exact store


/-- Under the actual strategy's bounds, the three post-increments pack exactly three
bytes and preserve every other heap entry. -/
theorem put_three_symbol_bytes_run {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (base : TreesBase h ds d b buf) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat)
    (v0 v1 v2 : UInt8) :
    (do Zlib.Trees.put_symbol_byte (some (.tab ds)) v0
        Zlib.Trees.put_symbol_byte (some (.tab ds)) v1
        Zlib.Trees.put_symbol_byte (some (.tab ds)) v2) h =
      .ok ((), Zlib.Trees.Proofs.Out.setD (Zlib.Trees.Proofs.Out.setB h b (((buf.set! (d.lit_bufsize.toNat + d.sym_next.toNat) v0).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 1)) v1).set!
        (d.lit_bufsize.toNat + (d.sym_next.toNat + 2)) v2)) ds {d with sym_next := d.sym_next + 3}) := by
  let off := d.lit_bufsize.toNat
  let n := d.sym_next.toNat
  let a1 := buf.set! (off + n) v0
  let a2 := a1.set! (off + (n+1)) v1
  let d1 := {d with sym_next := d.sym_next + 1}
  let d2 := {d with sym_next := d.sym_next + 1 + 1}
  let h1 := Zlib.Trees.Proofs.Out.setD (Zlib.Trees.Proofs.Out.setB h b a1) ds d1
  let h2 := Zlib.Trees.Proofs.Out.setD (Zlib.Trees.Proofs.Out.setB h b a2) ds d2
  have cap := base.size
  have end_ := base.sym_end
  have lim := base.lit_hi
  have one : d1.sym_next.toNat = n + 1 := by
    exact Zlib.Trees.Proofs.Out.toNat_add_one_u32 (by omega)
  have two : d2.sym_next.toNat = n + 2 := by
    change (d1.sym_next + 1).toNat = n + 2
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u32 (by omega), one]
  have step0 : Zlib.Trees.put_symbol_byte (some (.tab ds)) v0 h = .ok ((), h1) :=
    put_symbol_byte_run v0 base.dstate base.sym base.bytes base.rw (by omega)
  have step1 := put_symbol_byte_run (h := h1) (ds := ds) (d := d1) (off := off) (buf := a1) v1
    (Zlib.Trees.Proofs.Out.setD_dstates_same _ _ _) base.sym (by simp [h1]) (by simpa [h1] using base.rw)
    (by rw [one]; simp [a1, off, n]; omega)
  have step1' : Zlib.Trees.put_symbol_byte (some (.tab ds)) v1 h1 = .ok ((), h2) := by
    simpa only [one, h1, h2, a2, Zlib.Trees.Proofs.Out.setB_setD,
      Zlib.Trees.Proofs.Out.setB_setB, Zlib.Trees.Proofs.Out.setD_setD] using step1
  have step2 := put_symbol_byte_run (h := h2) (ds := ds) (d := d2) (off := off) (buf := a2) v2
    (Zlib.Trees.Proofs.Out.setD_dstates_same _ _ _) base.sym (by simp [h2]) (by simpa [h2] using base.rw)
    (by rw [two]; simp [a2, a1, off, n]; omega)
  rw [two] at step2
  simp only [bind_app, step0, step1']
  simpa only [h2, Zlib.Trees.Proofs.Out.setB_setD, Zlib.Trees.Proofs.Out.setB_setB,
    Zlib.Trees.Proofs.Out.setD_setD, d2, UInt32.add_assoc, UInt32.reduceAdd] using step2

theorem increment_literal_frequency {h : Heap} {ds : Nat} {d : DeflateState} {i : Nat}
    (state : h.dstates ds = some d) (bound : i < d.dyn_ltree.size) :
    freq_inc (.dstate_dyn_ltree ds) i h =
      .ok ((), setD h ds { d with dyn_ltree := bumpFc d.dyn_ltree i }) := by
  have get := CtDataRef.get_dstate_dyn_ltree state
  have add : padd (.ref (.dstate_dyn_ltree ds) 0 : CtDataPtr) i h =
      .ok (.ref (.dstate_dyn_ltree ds) i, h) := by
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := i) get (by omega)
  have load := Ptr.load_ok (off := i) get bound
  have put := Ptr.store_ok (off := i) (v := { d.dyn_ltree[i] with fc := d.dyn_ltree[i].fc + 1 })
    get (by rfl) bound
  unfold freq_inc
  rw [bind_app, add]
  simp only
  rw [bind_app, load]
  simp only []
  rw [put, CtDataRef.put_dstate_dyn_ltree state]
  simp [setD, bumpFc, bound]

/-- `_tr_tally_lit(s, c, flush)`.
The actual inline macro writes the three symbol bytes, increments sym_next
after selecting each byte address, increments the literal frequency and returns the full flag.
Room follows from the strategy's strict symbol-count invariant. -/
theorem tally_literal_run {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (base : TreesBase h ds d b buf) (c : UInt8)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end,
      setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c)) := by
  let hb := Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)
  let dn := { d with sym_next := d.sym_next + 3 }
  let hn := setD hb ds dn
  have inc := increment_literal_frequency (h := hn) (ds := ds) (d := dn) (i := c.toNat)
    (by simp [hn]) (by change c.toNat < d.dyn_ltree.size; rw [base.wf.1]; have := c.toNat_lt; omega)
  have packed := put_three_symbol_bytes_run base room 0 0 c
  let tail : Unit → M Bool := fun _ => do
    freq_inc (.dstate_dyn_ltree ds) c.toNat
    let state ← ldDeflateState (some (.tab ds))
    return state.sym_next == state.sym_end
  have source : tally_lit (some (.tab ds)) c = (do
      Zlib.Trees.put_symbol_byte (some (.tab ds)) 0
      Zlib.Trees.put_symbol_byte (some (.tab ds)) 0
      Zlib.Trees.put_symbol_byte (some (.tab ds)) c) >>= tail := by
    simp only [tally_lit, tail, M_bind_assoc]
  rw [source, bind_app, packed]
  change tail () hn = _
  simp only [tail, bind_app, inc, ldDeflateState_tab (setD_dstates_same _ _ _)]
  simp [hn, hb, dn, literalState, setD_setD]


theorem literalState_tally (d : DeflateState) (c : UInt8) :
    literalState d c = Zlib.Trees.Proofs.Out.tallyRec d 0 c.toUInt32 := by
  have three : d.sym_next + 1 + 1 + 1 = d.sym_next + 3 := by
    rw [UInt32.add_assoc, UInt32.add_assoc]
    rfl
  simp only [literalState, Zlib.Trees.Proofs.Out.tallyRec, ite_true, three, UInt8.toNat_toUInt32]

/-- The strategy's strict, aligned symbol count supplies room for the
three actual stores. It does not assume output space for tree emission. -/
theorem literal_room {h : Heap} {ds : Nat} {d : DeflateState}
    (inv : DStInv h ds d) (strict : d.sym_next.toNat < d.sym_end.toNat) :
    d.sym_next.toNat + 3 ≤ d.sym_end.toNat := by
  have aligned := inv.sym.2.2.2
  have endAligned : d.sym_end.toNat % 3 = 0 := by rw [inv.sym.2.1]; omega
  omega

/-- The inline literal tally establishes its updated tree invariant on
the actual returned heap. This uses the proved mathematical tree-field
update, not an assumed call to _tr_tally. -/
theorem tally_literal_trees {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d b buf) (c : UInt8)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
      ds (literalState d c) b (literalBytes buf d c) := by
  have wf : (literalState d c).WellFormed := by
    rw [literalState_tally]
    exact Zlib.Trees.Proofs.Out.tallyRec_wf trees.base.wf _ _
  have base := trees.base.step (literalBytes buf d c) (by simp [literalBytes]) (literalState d c)
    wf rfl rfl rfl rfl rfl trees.base.pending_le
  have run : TreesRun ds (literalState d c) := by
    rw [literalState_tally]
    apply Zlib.Trees.Proofs.Out.tallyRec_run trees.run room trees.run.sym_next_mod
    have end_ := trees.base.sym_end
    have cap := trees.base.lit_hi
    omega
  exact ⟨base, run⟩

/-- `_tr_tally_lit(s, c, flush)` preserves DGood as well as the actual
tree invariant. A source-returned true flag marks exactly the full buffer. -/
theorem literal_good_after {h : Heap} {r : ZStreamRef} {ds b : Nat} {z : ZStream}
    {d : DeflateState} {buf : Array UInt8} (good : DGood h r ds z d)
    (trees : TreesInvAt h ds d b buf) (c : UInt8) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) :
    DGood (setD (Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)) ds (literalState d c))
      r ds z (literalState d c) := by
  have treeResult := tally_literal_trees trees c room
  let hb := Zlib.Trees.Proofs.Out.setB h b (literalBytes buf d c)
  let dt := literalState d c
  have goodB : DGood hb r ds z d := good.bytes_set b (literalBytes buf d c) buf trees.base.bytes
    (by simp [literalBytes])
  have inv : DStInv hb ds dt :=
    { goodB.inv with
      wf := treeResult.base.wf
      blocks := goodB.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sym := ⟨goodB.inv.sym.1, goodB.inv.sym.2.1, treeResult.run.sym_next_le, treeResult.run.sym_next_mod⟩ }
  have shape := shape_setD goodB.live.hs dt
  refine ⟨?_, DStInv.congr (h := hb) (h' := setD hb ds dt) rfl rfl rfl rfl inv,
    shape.uniq goodB.uniq, shape.fresh rfl goodB.fresh, ⟨dt, b, literalBytes buf d c, treeResult⟩⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp, good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

theorem pending_write_chains {h : Heap} {r : ZStreamRef} {ds top b : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (chains : HeapChains h d top)
    (pending : d.pending_buf = .ref (.blk b) 0) (buf : Array UInt8) (c : UInt8) :
    HeapChains (setD (Zlib.Trees.Proofs.Out.setB h b buf) ds (literalState d c)) (literalState d c) top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
  have we : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have be : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  exact ⟨w, p, q, wa, pa, qa, win, prev, head,
    by simpa [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb] using hw,
    hp, hq, H⟩

theorem pending_window_frame {h : Heap} {r : ZStreamRef} {ds w b : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (pending : d.pending_buf = .ref (.blk b) 0) (get : h.bytes w = some wa)
    (buf : Array UInt8) (state : DeflateState) :
    (setD (Zlib.Trees.Proofs.Out.setB h b buf) ds state).bytes w = some wa := by
  obtain ⟨w0, p, q, b0, blocks⟩ := good.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  have bid : b0 = b := by simpa only [pending, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst w0 b0
  simpa [Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb] using get

theorem literal_count {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (base : TreesBase h ds d b buf) (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat) (c : UInt8) :
    (literalState d c).sym_next.toNat = d.sym_next.toNat + 3 := by
  have end_ := base.sym_end
  have cap := base.lit_hi
  change (d.sym_next + 3).toNat = _
  rw [UInt32.toNat_add]
  simp only [show (3 : UInt32).toNat = 3 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

/-- A false full flag gives the strict symbol-count invariant needed by
the next actual tally. The true branch still needs real block emission. -/
theorem literal_not_full {h : Heap} {ds b : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d b buf) (c : UInt8)
    (room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat)
    (flag : (d.sym_next + 3 == d.sym_end) = false) :
    (literalState d c).sym_next.toNat < (literalState d c).sym_end.toNat := by
  have next := literal_count trees.base room c
  have neq : d.sym_next + 3 ≠ d.sym_end := by simpa using flag
  have ne : (literalState d c).sym_next.toNat ≠ d.sym_end.toNat := by
    intro eq
    apply neq
    exact UInt32.toNat_inj.mp eq
  change (literalState d c).sym_next.toNat < d.sym_end.toNat
  omega

end Zlib.Deflate.Engine.Proofs
