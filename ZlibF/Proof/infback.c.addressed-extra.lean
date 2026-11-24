import ZlibF.Proof.«infback.c.addressed-huffman»

/-! Extra bits for an addressed length or distance read, including the live C loop guard. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored
set_option autoImplicit false

section
variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)

include cb

/-- Every condition evaluation reads the current decoder's extra field. Each
callback preserves the decoder and may install a different unread buffer. -/
theorem extra_refill {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (width : s.extra.toNat < 32) (short : l.bits.toNat < 8) (clean : l.hold.toNat < 2 ^ l.bits.toNat) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H, runX (needExtra c) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → s.extra.toNat ≤ regs.bits.toNat ∧ regs.bits.toNat < s.extra.toNat + 8 ∧
        regs.hold.toNat < 2 ^ regs.bits.toNat) ∧ (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let valid := fun (r : IL) (H : Heap) => Buffers cell w off cap s r H ∧ admitted r.pointerLocals H ∧
    H.istates owner = some s ∧ r.bits.toNat < s.extra.toNat + 8 ∧ r.hold.toNat < 2 ^ r.bits.toNat
  let post := fun (status : Except Ex Unit) (r : IL) (H : Heap) => Buffers cell w off cap s r H ∧
    admitted r.pointerLocals H ∧ H.istates owner = some s ∧
    (status = .ok () → s.extra.toNat ≤ r.bits.toNat ∧ r.bits.toNat < s.extra.toNat + 8 ∧ r.hold.toNat < 2 ^ r.bits.toNat) ∧
    (∀ e, status = .error e → e = Ex.leave ∧ r.ret = Z_BUF_ERROR)
  apply xwhileBrk_wf (cond := do return (← get).bits < (← rdS c.st (·.extra)))
    (body := do Zlib.Infback.PULLBYTE c; pure false) valid post (fun r _ => s.extra.toNat - r.bits.toNat)
    _ (show valid l h from ⟨buf, allowed, state, by omega, clean⟩)
  · unfold fuel; omega
  · intro r H ⟨v, ok, st, maxBits, held⟩
    have read : rdS c.st (·.extra) H = .ok (s.extra, H) := by
      rw [show c.st = some (.tab owner) from rfl, rdI_eq]; simp [st]
    refine ⟨r, H, decide (r.bits < s.extra), by simp only [runX_bind, runX_get, runX_lift_ok read, runX_pure], ?_, ?_⟩
    · intro guard
      have lt := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true guard)
      have room : r.bits.toNat < 32 := by omega
      obtain ⟨status, r', H', run, v', ok', st', appended, err⟩ := pullByte_step (strm := strm) cb st v ok room
      cases status with
      | error e => exact ⟨.error e, r', H', by rw [runX_bind, run], v', ok', st', nofun, err⟩
      | ok u =>
        have step := appended rfl
        have inc := step.count
        exact ⟨.ok false, r', H', by rw [runX_bind, run]; rfl,
          ⟨v', ok', st', by omega, (step.held room held).2⟩, by omega⟩
    · intro guard
      have enough := Nat.le_of_not_gt fun lt => (of_decide_eq_false guard) (UInt32.lt_iff_toNat_lt.mpr lt)
      exact ⟨v, ok, st, fun _ => ⟨enough, maxBits, held⟩, fun _ eq => nomatch eq⟩

/-- The actual C extension adds the low bits to either the match distance or
the match length. Arithmetic here is the unsigned arithmetic of the decoder. -/
def addExtra (dist : Bool) (s : InflateState) (b : UInt32) : InflateState :=
  if dist then {s with offset := s.offset + b} else {s with length := s.length + b}

theorem extra_value (dist : Bool) (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (width : s.extra.toNat < 32) (short : l.bits.toNat < 8) (clean : l.hold.toNat < 2 ^ l.bits.toNat) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H t, runX (extendExtra c dist) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some t ∧
      (status = .ok () → ∃ b, b.toNat < 2 ^ s.extra.toNat ∧ t = addExtra dist s b ∧
        regs.bits.toNat < 8 ∧ regs.hold.toNat < 2 ^ regs.bits.toNat) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR ∧ t = s) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  have read {H : Heap} {t : InflateState} (st : H.istates owner = some t) :
      rdS c.st (·.extra) H = .ok (t.extra, H) := by
    rw [show c.st = some (.tab owner) from rfl, rdI_eq]; simp [st]
  by_cases zero : s.extra = 0
  · refine ⟨.ok (), l, h, s, ?_, buf, allowed, state,
      fun _ => ⟨0, Nat.two_pow_pos _, by cases dist <;> simp [addExtra], short, clean⟩, fun _ eq => nomatch eq⟩
    change runX (extendExtra c dist) l h = _
    simp only [extendExtra, runX_bind, runX_lift_ok (read state), zero, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte, runX_pure]
  · obtain ⟨status, r, H, run, valid, ok, st, complete, err⟩ := extra_refill (strm := strm) cb state buf allowed width short clean
    change runX (needExtra c) l h = _ at run
    cases status with
    | error e =>
      refine ⟨.error e, r, H, s, ?_, valid, ok, st, nofun, fun e eq => ⟨(err e eq).1, (err e eq).2, rfl⟩⟩
      change runX (extendExtra c dist) l h = _
      simp only [extendExtra, runX_bind, runX_lift_ok (read state), bne_iff_ne.mpr zero, ↓reduceIte, run]
    | ok u =>
      cases u
      obtain ⟨enough, maxBits, held⟩ := complete rfl
      let b := bitsV r s.extra
      let t := addExtra dist s b
      let regs := dropR r s.extra
      let G := setI H owner t
      have gt : G.istates owner = some t := upd_same ..
      have ex : t.extra = s.extra := by cases dist <;> rfl
      have after : rdS c.st (·.extra) G = .ok (s.extra, G) := ex ▸ read gt
      have bits : runX (BITS s.extra) r H = .ok ((.ok b, r), H) := BITS_run _ _ _ width
      have drop : runX (DROPBITS s.extra) r G = .ok ((.ok (), regs), G) := DROPBITS_run _ _ _ (by omega)
      refine ⟨.ok (), regs, G, t, ?_, ?_, edit _ _ _ ok, gt, fun _ => ⟨b, bitsV_lt _ width, rfl, ?_,
        dropR_clean (by omega) enough held⟩, fun _ eq => nomatch eq⟩
      · change runX (extendExtra c dist) l h = _
        cases dist with
        | false =>
          have wr : wrS c.st (fun s => {s with length := s.length + b}) H = .ok ((), G) := wrS_tab st _
          simp only [extendExtra, runX_bind, runX_lift_ok (read state), bne_iff_ne.mpr zero, ↓reduceIte,
            run, runX_lift_ok (read st), bits, Bool.false_eq_true, runX_lift_ok wr, runX_lift_ok after, drop]
        | true =>
          have wr : wrS c.st (fun s => {s with offset := s.offset + b}) H = .ok ((), G) := wrS_tab st _
          simp only [extendExtra, runX_bind, runX_lift_ok (read state), bne_iff_ne.mpr zero, ↓reduceIte,
            run, runX_lift_ok (read st), bits, runX_lift_ok wr, runX_lift_ok after, drop]
      · cases dist <;> exact {valid with window := ⟨valid.window.storage, valid.window.writable⟩}
      · change (dropR r s.extra).bits.toNat < 8
        rw [dropR_bits enough]; omega

/-- The two match-base entries installed by the literal/length and distance
handlers before the extra-bit loop. -/
def matchBase (dist : Bool) (s : InflateState) (e : Code) : InflateState :=
  let extra := e.op.toUInt32 &&& 15
  if dist then {s with offset := e.val.toUInt32, extra}
  else {s with length := e.val.toUInt32, extra}

omit cb in
private theorem match_cut (c : DecoderCtx) {owner : Nat} {s : InflateState} {l : IL} {h : Heap}
    (ownerEq : c.st = some (.tab owner)) (state : h.istates owner = some s) (dist : Bool)
    (small : l.here.bits.toNat ≤ 15) (normal : l.here.op &&& 64 = 0)
    (len : dist = false → l.here.op ≠ 0 ∧ l.here.op &&& 32 = 0) :
    let d := dropR l l.here.bits.toUInt32
    let H := setI h owner (matchBase dist s l.here)
    runX (if dist then distSym c else lenSym c) l h =
      runX (do extendExtra c dist; if dist then lenCopy c else lenDist c) d H := by
  let d := dropR l l.here.bits.toUInt32
  let t := matchBase dist s l.here
  let H := setI h owner t
  let ex := l.here.op.toUInt32 &&& 15
  have drop : runX (DROPBITS l.here.bits.toUInt32) l h = .ok ((.ok (), d), h) :=
    DROPBITS_run _ _ _ (by rw [UInt8.toNat_toUInt32]; omega)
  have live : H.istates owner = some t := upd_same ..
  have read : rdS c.st (·.extra) H = .ok (ex, H) := by
    rw [ownerEq, rdI_eq]; simp only [live]; cases dist <;> rfl
  dsimp only
  cases dist with
  | true =>
    have save : wrS c.st (fun s => {s with offset := l.here.val.toUInt32, extra := ex}) h = .ok ((), H) :=
      ownerEq ▸ wrS_tab state _
    change runX (distSym c) l h = runX (do extendExtra c true; lenCopy c) d H
    unfold distSym extendExtra
    by_cases need : ex != 0 <;>
      simp only [runX_bind, runX_get, drop, normal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        runX_lift_ok save, runX_lift_ok read, ← show ex = l.here.op.toUInt32 &&& 15 from rfl,
        need, runX_pure, x_bind_assoc] <;> rfl
  | false =>
    let mid := {s with length := l.here.val.toUInt32}
    have st : (setI h owner mid).istates owner = some mid := upd_same ..
    have save : wrS c.st (fun s => {s with length := l.here.val.toUInt32}) h = .ok ((), setI h owner mid) :=
      ownerEq ▸ wrS_tab state _
    have extra : wrS c.st (fun s => {s with extra := ex}) (setI h owner mid) = .ok ((), H) := by
      rw [ownerEq, wrS_tab st, setI_setI]; rfl
    obtain ⟨base, noEnd⟩ := len rfl
    change runX (lenSym c) l h = runX (do extendExtra c false; lenDist c) d H
    unfold lenSym extendExtra
    by_cases need : ex != 0 <;>
      simp only [runX_bind, runX_get, drop, runX_lift_ok save, beq_false_of_ne base, noEnd, normal,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, runX_lift_ok extra, runX_lift_ok read,
        ← show ex = l.here.op.toUInt32 &&& 15 from rfl, need, runX_pure, x_bind_assoc] <;> rfl

/-- From a match-base leaf, the next distance lookup or copy sees the base
plus the decoded extra bits, with a clean partial byte. -/
theorem match_base_read (dist : Bool) (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (small : l.here.bits.toNat ≤ 15) (fits : l.here.bits.toNat ≤ l.bits.toNat)
    (short : l.bits.toNat - l.here.bits.toNat < 8) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    (normal : l.here.op &&& 64 = 0) (len : dist = false → l.here.op ≠ 0 ∧ l.here.op &&& 32 = 0) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    let step := if dist then distSym c else lenSym c
    let base := matchBase dist s l.here
    (∃ regs H, runX step l h = .ok ((.error Ex.leave, regs), H) ∧ regs.ret = Z_BUF_ERROR ∧
      Buffers cell w off cap base regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some base) ∨
    (∃ b regs H, b.toNat < 2 ^ base.extra.toNat ∧
      H.istates owner = some (addExtra dist base b) ∧ Buffers cell w off cap (addExtra dist base b) regs H ∧
      admitted regs.pointerLocals H ∧ regs.bits.toNat < 8 ∧ regs.hold.toNat < 2 ^ regs.bits.toNat ∧
      runX step l h = runX (if dist then lenCopy c else lenDist c) regs H) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let t := matchBase dist s l.here
  let d := dropR l l.here.bits.toUInt32
  let H := setI h owner t
  have cut := match_cut c rfl state dist small normal len
  have st : H.istates owner = some t := upd_same ..
  have valid : Buffers cell w off cap t d H := by
    cases dist <;> exact {buf with window := ⟨buf.window.storage, buf.window.writable⟩}
  have fit : l.here.bits.toUInt32.toNat ≤ l.bits.toNat := by simpa only [UInt8.toNat_toUInt32] using fits
  have ex : t.extra = l.here.op.toUInt32 &&& 15 := by cases dist <;> rfl
  have width : t.extra.toNat < 32 := by
    rw [ex, Zlib.Inffast.Proofs.mask15]
    have := Nat.and_le_right (n := l.here.op.toNat) (m := 15)
    change l.here.op.toNat &&& 15 < 32
    omega
  have near : d.bits.toNat < 8 := by rw [show d.bits.toNat = _ from dropR_bits fit, UInt8.toNat_toUInt32]; exact short
  obtain ⟨res, regs, g, u, run, valid', ok', get, good, err⟩ := extra_value (strm := strm) cb dist edit st valid
    (edit _ _ _ allowed) width near (dropR_clean (by rw [UInt8.toNat_toUInt32]; omega) fit clean)
  dsimp only
  change runX (extendExtra c dist) d H = _ at run
  change runX _ l h = runX (do extendExtra c dist; if dist then lenCopy c else lenDist c) d H at cut
  cases res with
  | error e =>
    obtain ⟨rfl, ret, rfl⟩ := err e rfl
    exact Or.inl ⟨regs, g, cut.trans (by rw [runX_bind, run]), ret, valid', ok', get⟩
  | ok u =>
    cases u
    obtain ⟨b, bound, rfl, low, held⟩ := good rfl
    exact Or.inr ⟨b, regs, g, bound, get, valid', ok', low, held, cut.trans (by rw [runX_bind, run])⟩

end
#print axioms extra_refill
#print axioms match_base_read
end Zlib.Infback.AddressedTable
