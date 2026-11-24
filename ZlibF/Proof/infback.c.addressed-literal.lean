import ZlibF.Proof.«infback.c.addressed-huffman»

/-! Output, end-of-block and invalid literal/length symbols with a live input cursor. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety Zlib.Infback.AddressedStored
set_option autoImplicit false

private theorem emit_byte {owner w off cap : Nat} {cell : BPtrCell} {s : InflateState} {l : IL} {h : Heap}
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (space : l.left ≠ 0) :
    ∃ before after regs H, h.bytes w = some before ∧ after.size = before.size ∧
      (∀ j, j < off ∨ off + cap ≤ j → after[j]? = before[j]?) ∧
      runX (Zlib.Infback.emitLiteral (some (.tab owner))) l h = .ok ((.ok (), regs), H) ∧
      H = {h with bytes := upd h.bytes w (some after)} ∧ Buffers cell w off cap s regs H ∧
      regs.pointerLocals = l.pointerLocals ∧ regs.bits = l.bits ∧ regs.hold = l.hold ∧
      regs.have_ = l.have_ ∧ regs.left.toNat + 1 = l.left.toNat ∧
      after[off + (cap - l.left.toNat)]? = some s.length.toUInt8 := by
  obtain ⟨a, get, fits⟩ := buf.window.storage
  let j := off + (cap - l.left.toNat)
  let data := a.set! j s.length.toUInt8
  let H := {h with bytes := upd h.bytes w (some data)}
  let regs := {l with put := .ref (.blk w) (j + 1), left := l.left - 1}
  have ne : l.left.toNat ≠ 0 := fun eq => space (UInt32.toNat_inj.mp eq)
  have bound := buf.left
  have pos : j < off + cap := by dsimp only [j]; omega
  have inside : j < a.size := by omega
  have size : data.size = a.size := by simp [data]
  have wrote : store8 l.put s.length.toUInt8 h = .ok ((), H) := by
    rw [buf.put]
    exact Ptr.store_ok (r := BRef.blk w) (show Space.get h (.blk w : BRef) = some a from get)
      buf.window.writable inside
  have getW : Space.get H (.blk w : BRef) = some data := upd_same ..
  have add : l.put.add 1 H = .ok (regs.put, H) := by
    rw [buf.put]
    exact Ptr.add_nat_ok (n := 1) getW (by change j + 1 ≤ data.size; omega)
  have run : runX (Zlib.Infback.emitLiteral (some (.tab owner))) l h = .ok ((.ok (), regs), H) := by
    simp only [Zlib.Infback.emitLiteral, runX_bind, runX_get, runX_lift_ok (ldInflateState_tab state),
      runX_lift_ok wrote, runX_lift_ok add, runX_set]
    rfl
  have left : regs.left.toNat + 1 = l.left.toNat := by
    change (l.left - 1).toNat + 1 = _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by change 1 ≤ l.left.toNat; omega))]
    change l.left.toNat - 1 + 1 = _; omega
  refine ⟨a, data, regs, H, get, size, ?_, run, rfl, ?_, rfl, rfl, rfl, rfl, left, ?_⟩
  · intro k apart
    apply array_set!_getElem?_ne
    dsimp only [j]; omega
  · refine ⟨buf.live, ⟨⟨data, getW, by omega⟩, buf.window.writable⟩, buf.address, buf.size, buf.positive,
      by omega, ?_, ?_⟩
    · change Ptr.ref (BRef.blk w) (j + 1) = .ref _ (off + (cap - regs.left.toNat))
      congr 1; dsimp only [j]; omega
    · intro has
      obtain ⟨b, ix, src, ptr, gb, room, disjoint⟩ := buf.input has
      by_cases same : b = w
      · subst b; cases Option.some.inj (get.symm.trans gb)
        exact ⟨w, ix, data, ptr, getW, by change ix + l.have_.toNat ≤ data.size; omega, disjoint⟩
      · exact ⟨b, ix, src, ptr, (upd_ne h.bytes w _ b same).trans gb, room, disjoint⟩
  · simp [data, j, inside]

/-- After a literal leaf, a failed output callback exits with Z_BUF_ERROR.
On success exactly one window byte is written. The input cursor remains
the one selected by ROOM, including when it ran the output callback. -/
theorem literal_output {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (lit : l.here.op = 0) (small : l.here.bits.toNat ≤ 15) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    let drop := dropR l l.here.bits.toUInt32
    ∃ status regs H t, runX (lenSym c) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some t ∧
      regs.bits = drop.bits ∧ regs.hold = drop.hold ∧ regs.have_ = l.have_ ∧
      (t = {s with length := t.length, whave := t.whave, mode := t.mode} ∧ (t.whave = s.whave ∨ t.whave = s.wsize)) ∧
      (∀ err, status = .error err → err = Ex.leave ∧ regs.ret = Z_BUF_ERROR) ∧
      (status = .ok () → t.mode = LEN ∧ ∃ a, H.bytes w = some a ∧
        a[off + (cap - (regs.left.toNat + 1))]? = some l.here.val.toUInt32.toUInt8) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let d := dropR l l.here.bits.toUInt32
  let marked := {s with length := l.here.val.toUInt32}
  let ready := setI h owner marked
  have st : ready.istates owner = some marked := upd_same ..
  have good : Buffers cell w off cap marked d ready :=
    {buf with window := ⟨buf.window.storage, buf.window.writable⟩}
  have wr : wrS c.st (fun t => {t with length := l.here.val.toUInt32}) h = .ok ((), ready) := wrS_tab state _
  have drop : runX (DROPBITS l.here.bits.toUInt32) l h = .ok ((.ok (), d), h) :=
    DROPBITS_run _ _ _ (by rw [UInt8.toNat_toUInt32]; omega)
  obtain ⟨status, r, g, t, room, good', ok, live, len, _, count, ⟨bits, hold, history⟩, has, err⟩ :=
    room_safe (strm := strm) cb st good (edit _ _ _ allowed)
  have fields : t = {s with length := t.length, whave := t.whave, mode := t.mode} ∧
      (t.whave = s.whave ∨ t.whave = s.wsize) := by
    rcases history with rfl | rfl
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  dsimp only
  change runX (ROOM c) d ready = _ at room
  cases status with
  | error e =>
    refine ⟨.error e, r, g, t, ?_, good', ok, live, bits, hold, count, fields, err, nofun⟩
    change runX (lenSym c) l h = _
    unfold lenSym
    simp only [runX_bind, runX_get, drop, runX_lift_ok wr, lit, beq_self_eq_true, ↓reduceIte, room]
  | ok u =>
    cases u
    obtain ⟨a, b, regs, H, get, size, outside, emit, eq, buf', cs, bit', hold', count', left, value⟩ :=
      emit_byte live good' (has rfl)
    subst H
    let H := {g with bytes := upd g.bytes w (some b)}
    have st' : H.istates owner = some t := live
    have allowedH : admitted r.pointerLocals H := by
      have kept := cb.copy _ _ _ _ _ t.length ok live get size outside
      change admitted r.pointerLocals (setI H owner t) at kept
      have self : setI H owner t = H := by simp [setI, upd_self _ _ _ st']
      rw [self] at kept
      exact kept
    let endState := {t with mode := LEN}
    have set : setMode c.st LEN H = .ok ((), setI H owner endState) := setMode_tab st' LEN
    change runX (Zlib.Infback.emitLiteral c.st) r g = .ok ((.ok (), regs), H) at emit
    have tail : runX (do Zlib.Infback.emitLiteral c.st; setMode c.st LEN; pure () : X Unit) r g =
        .ok ((.ok (), regs), setI H owner endState) := by
      simp only [runX_bind, emit, runX_lift_ok set, runX_pure]
    refine ⟨.ok (), regs, setI H owner endState, endState, ?_,
      {buf' with window := ⟨buf'.window.storage, buf'.window.writable⟩}, (by rw [cs]; exact edit _ _ _ allowedH),
      upd_same .., bit'.trans bits, hold'.trans hold, count'.trans count, ⟨?_, fields.2⟩, (fun _ f => nomatch f), ?_⟩
    · change runX (lenSym c) l h = _
      unfold lenSym
      simp only [runX_bind, runX_get, drop, runX_lift_ok wr, lit, beq_self_eq_true, ↓reduceIte, room]
      simpa only [Zlib.Infback.emitLiteral, x_bind_assoc, runX_bind, runX_get] using tail
    · change {t with mode := LEN} = _
      conv => lhs; rw [fields.1]
    · intro _
      exact ⟨rfl, b, upd_same .., by rw [left]; rw [len] at value; exact value⟩

/-- The end-of-block flag has priority over the invalid-code flag. Both
branches consume the leaf width and save its value before setting the mode. -/
theorem len_terminal (c : DecoderCtx) {r : ZStreamRef} {i : Nat} {s : InflateState}
    {l : IL} {h : Heap} {z : ZStream} (stream : c.strm = some r) (owner : c.st = some (.tab i))
    (live : r.get h = some z) (state : h.istates i = some s) (small : l.here.bits.toNat ≤ 15)
    (notLit : l.here.op ≠ 0) (flags : l.here.op &&& 32 ≠ 0 ∨ l.here.op &&& 64 ≠ 0) :
    let d := dropR l l.here.bits.toUInt32
    let t := {s with length := l.here.val.toUInt32}
    if l.here.op &&& 32 != 0 then
      runX (lenSym c) l h = .ok ((.ok (), d), setI h i {t with mode := TYPE})
    else ∃ j, strTable[j]? = some "invalid literal/length code" ∧
      runX (lenSym c) l h = .ok ((.ok (), d),
        setI (r.put (setI h i t) {z with msg := .ref (.str j) 0}) i {t with mode := BAD}) := by
  let t := {s with length := l.here.val.toUInt32}
  let d := dropR l l.here.bits.toUInt32
  have drop : runX (DROPBITS l.here.bits.toUInt32) l h = .ok ((.ok (), d), h) :=
    DROPBITS_run _ _ _ (by rw [UInt8.toNat_toUInt32]; omega)
  have get : (setI h i t).istates i = some t := upd_same ..
  have save : wrS c.st (fun s => {s with length := l.here.val.toUInt32}) h = .ok ((), setI h i t) :=
    owner ▸ wrS_tab state _
  dsimp only
  by_cases done : l.here.op &&& 32 ≠ 0
  · have set : setMode c.st TYPE (setI h i t) = .ok ((), setI (setI h i t) i {t with mode := TYPE}) :=
      owner ▸ setMode_tab get TYPE
    simp only [bne_iff_ne.mpr done, ↓reduceIte, lenSym, runX_bind, runX_get, drop, runX_lift_ok save,
      beq_false_of_ne notLit, Bool.false_eq_true, runX_lift_ok set, runX_pure, setI_setI]
    rfl
  · have zero : l.here.op &&& 32 = 0 := Classical.byContradiction done
    have bad := flags.resolve_left done
    have live' : r.get (setI h i t) = some z := by simpa using live
    obtain ⟨j, msg, set⟩ := badMode_ctx_literal c stream owner live' get _ lit_len_code
    simp only [show (l.here.op &&& 32 != 0) = false by simp [zero], Bool.false_eq_true, ↓reduceIte]
    exact ⟨j, msg, by simp only [lenSym, runX_bind, runX_get, drop, runX_lift_ok save, beq_false_of_ne notLit,
      Bool.false_eq_true, ↓reduceIte, zero, bne_self_eq_false,
      bne_iff_ne.mpr bad, runX_lift_ok set, runX_pure]; rfl⟩

/-- An invalid distance symbol publishes the source error string and enters
BAD immediately after dropping its bits. -/
theorem dist_invalid (c : DecoderCtx) {r : ZStreamRef} {i : Nat} {s : InflateState}
    {l : IL} {h : Heap} {z : ZStream} (stream : c.strm = some r) (owner : c.st = some (.tab i))
    (live : r.get h = some z) (state : h.istates i = some s) (small : l.here.bits.toNat ≤ 15)
    (bad : l.here.op &&& 64 ≠ 0) :
    ∃ j, strTable[j]? = some "invalid distance code" ∧
      runX (distSym c) l h = .ok ((.ok (), dropR l l.here.bits.toUInt32),
        setI (r.put h {z with msg := .ref (.str j) 0}) i {s with mode := BAD}) := by
  obtain ⟨j, msg, set⟩ := badMode_ctx_literal c stream owner live state _ lit_dist_code
  have small' : l.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  refine ⟨j, msg, ?_⟩
  simp only [distSym, runX_bind, runX_get, DROPBITS_run _ _ _ small', bne_iff_ne.mpr bad, ↓reduceIte,
    runX_lift_ok set, runX_pure]
  rfl

#print axioms literal_output
#print axioms len_terminal
#print axioms dist_invalid
end Zlib.Infback.AddressedTable
