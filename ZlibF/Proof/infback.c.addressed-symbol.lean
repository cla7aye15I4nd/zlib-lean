import ZlibF.Proof.«infback.c.addressed-repeat»

/-! Reading the three repeat codes from the addressed decoder's bit stream. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

private def countThenCopy (c : DecoderCtx) (width base value : UInt32) : X Bool := do
  let b ← BITS width
  modify fun l => {l with len := value, copy := base + b}
  DROPBITS width
  trTail c

private def previousThenCopy (c : DecoderCtx) : X Bool := do
  let s ← ldInflateState c.st
  if s.«have» == 0 then
    badMode c "invalid bit length repeat"
    return true
  let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
  countThenCopy c 2 3 v.toUInt32

private def refillSymbol (c : DecoderCtx) (here : Code) (extra : UInt32) (k : X Bool) : X Bool := do
  Zlib.Infback.NEEDBITS c (here.bits.toUInt32 + extra)
  DROPBITS here.bits.toUInt32
  k

private theorem rep_eq (c : DecoderCtx) (here : Code) :
    trRep c here = if here.val == 16 then refillSymbol c here 2 (previousThenCopy c)
      else if here.val == 17 then refillSymbol c here 3 (countThenCopy c 3 3 0)
      else refillSymbol c here 7 (countThenCopy c 7 11 0) := by
  unfold trRep
  split
  · rfl
  · split <;> rfl

section
variable {owner w off cap : Nat} {cell : BPtrCell} {admitted : PointerLocals → Heap → Prop}
  (write : ∀ cs H t v, admitted cs H → H.istates owner = some t →
    t.«have».toNat < t.nlen.toNat + t.ndist.toNat → v.toNat ≤ 15 → admitted cs (setI H owner (rdSet t v)))
  {r : ZStreamRef} (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)

include write stream

private theorem count_safe (c : DecoderCtx) (hr : c.strm = some r) (hc : c.st = some (.tab owner))
    {s : InflateState} {l : IL} {h : Heap} (d : Reading owner w off cap cell admitted s l h)
    (width base value : UInt32) (small : width.toNat ≤ 7) (len : value.toNat ≤ 15)
    (lo : 3 ≤ base.toNat) (hi : base.toNat + 2^width.toNat ≤ 139) :
    ∃ stop regs H, runX (countThenCopy c width base value) l h = .ok ((.ok stop, regs), H) ∧
      SymbolResult owner w off cap cell r admitted s.«have».toNat stop regs H ∧
      (stop = false → ReadyBits (dropR l width) → ReadyBits regs) := by
  let n := base + bitsV l width
  let saved := dropR {l with len := value, copy := n} width
  have bound := bitsV_lt l (k := width) (by omega)
  have add : n.toNat = base.toNat + (bitsV l width).toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have ready : Reading owner w off cap cell admitted s saved h := {d with buffers := {d.buffers with}}
  obtain ⟨stop,regs,H,run,out,kept⟩ := repeat_tail_safe write c hr hc stream ready len
    (show 3 ≤ n.toNat by omega) (show n.toNat ≤ 138 by omega)
  refine ⟨stop, regs, H, ?_, out, fun _ => kept⟩
  unfold countThenCopy
  simp only [runX_bind, BITS_run _ _ width (by omega), runX_modify, DROPBITS_run _ _ width (by omega)]
  exact run

private theorem previous_safe (c : DecoderCtx) (hr : c.strm = some r) (hc : c.st = some (.tab owner))
    {s : InflateState} {l : IL} {h : Heap} (d : Reading owner w off cap cell admitted s l h) :
    ∃ stop regs H, runX (previousThenCopy c) l h = .ok ((.ok stop, regs), H) ∧
      SymbolResult owner w off cap cell r admitted s.«have».toNat stop regs H ∧
      (stop = false → ReadyBits (dropR l 2) → ReadyBits regs) := by
  have ld : ldInflateState c.st h = .ok (s,h) := by rw [hc]; exact ldInflateState_tab d.state
  unfold previousThenCopy
  rw [runX_bind, runX_lift_ok ld]
  by_cases zero : (s.«have» == 0) = true
  · obtain ⟨z, alive⟩ := stream _ _ d.allowed
    obtain ⟨key, bad⟩ := badMode_ctx_run c hr hc alive d.state _ lit_bit_length_repeat
    have wb := d.buffers.putStream r {z with msg := .ref (.str key) 0}
    refine ⟨true, l, setI (r.put h {z with msg := .ref (.str key) 0}) owner {s with mode := BAD}, ?_,
      ⟨{s with mode := BAD}, Or.inl ⟨rfl, upd_same .., rfl,upd_same ..,{wb with window := ⟨wb.window.storage,wb.window.writable⟩},
        .state (.message (.caller d.allowed) alive _) _⟩⟩, nofun⟩
    simp only [zero, ↓reduceIte, runX_bind, runX_lift_ok bad]; rfl
  · have nz : s.«have» ≠ 0 := by simpa using zero
    have pos : 0 < s.«have».toNat := Nat.pos_of_ne_zero (fun eq => nz (UInt32.toNat_inj.mp eq))
    have sub : (s.«have»-1).toNat = s.«have».toNat - 1 := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr pos)
    have limit : 0 + (s.«have»-1).toNat < s.lens.size := by
      rw [d.wf.1,sub]; have := d.decoded.le; have := d.decoded.tab.nlen; have := d.decoded.tab.ndist; omega
    have read := Ptr.index_ok (off := 0) (i := (s.«have»-1).toNat) (WRef.get_istate_lens d.state) limit
    let v := s.lens[0 + (s.«have»-1).toNat]
    have val : v.toNat ≤ 15 := by
      have bound := d.decoded.rl (0 + (s.«have»-1).toNat) (by omega)
      simpa only [v, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem limit, Option.getD_some] using bound
    obtain ⟨stop,regs,H,run,out⟩ := count_safe write stream c hr hc d 2 3 v.toUInt32
      (by decide) (by simpa using val) (by decide) (by decide)
    refine ⟨stop, regs, H, ?_, out⟩
    simp only [zero, Bool.false_eq_true, ↓reduceIte, hc, lensP, runX_bind, runX_lift_ok read]
    exact run

end

section
variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
  {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop}
  (cb : Callbacks owner w off cap cell input i output o admitted)
  {r : ZStreamRef}
  (write : ∀ cs H t v, admitted cs H → H.istates owner = some t →
    t.«have».toNat < t.nlen.toNat + t.ndist.toNat → v.toNat ≤ 15 → admitted cs (setI H owner (rdSet t v)))
  (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)

private abbrev ctx (r : ZStreamRef) (owner : Nat) (cell : BPtrCell) (input : CInCb) (i : VoidPtr)
    (output : COutCb) (o : VoidPtr) := addressedCtx (some r) (some (.tab owner)) cell input i output o

def RoundResult (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef) (admitted : PointerLocals → Heap → Prop)
    (start : Nat) (res : Except Ex Bool) (l : IL) (h : Heap) : Prop :=
  match res with
  | .ok stop => SymbolResult owner w off cap cell r admitted start stop l h
  | .error e => e = Ex.leave ∧ l.ret = Z_BUF_ERROR ∧ ∃ t, AtExit owner w off cap cell r admitted t l h

include cb in
private theorem refill_safe {s : InflateState} {l : IL} {h : Heap}
    (d : Reading owner w off cap cell admitted s l h) (here : Code) (width : here.bits.toNat ≤ 7)
    {guard : Prop} (before : guard → l.hold.toNat < 2 ^ l.bits.toNat ∧ l.bits.toNat - here.bits.toNat < 8)
    (extra : UInt32) (small : extra.toNat ≤ 7) (k : X Bool)
    (done : ∀ regs H, Reading owner w off cap cell admitted s regs H →
      ∃ stop regs' H', runX k regs H = .ok ((.ok stop, regs'), H') ∧
        SymbolResult owner w off cap cell r admitted s.«have».toNat stop regs' H' ∧
        (stop = false → ReadyBits (dropR regs extra) → ReadyBits regs')) :
    ∃ res regs H, runX (refillSymbol (ctx r owner cell input i output o) here extra k) l h =
      .ok ((res, regs), H) ∧ RoundResult owner w off cap cell r admitted s.«have».toNat res regs H ∧
      (res = .ok false → guard → ReadyBits regs) := by
  have sum : (here.bits.toUInt32 + extra).toNat ≤ 32 := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32]; omega
  obtain ⟨res, regs, H, need, buffers, allowed, state, filled, err⟩ :=
    needBits_safe (strm := some r) cb _ sum d.state d.buffers d.allowed
  unfold refillSymbol
  rw [runX_bind, need]
  cases res with
  | error e => exact ⟨.error e, regs, H, rfl, ⟨(err e rfl).1,(err e rfl).2,s,state,buffers,.caller allowed⟩, nofun⟩
  | ok u =>
    have narrow : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    obtain ⟨stop,regs',H',run,out,kept⟩ := done (dropR regs here.bits.toUInt32) H
      ⟨state, d.wf, d.decoded, {buffers with}, allowed⟩
    have keep (cont : stop = false) (g : guard) : ReadyBits regs' := by
      apply kept cont
      obtain ⟨clean, near⟩ := before g
      obtain ⟨lo, hi, preserve⟩ := filled rfl
      have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32]; exact Nat.mod_eq_of_lt (by omega)
      rw [total] at lo hi
      have f₁ : here.bits.toUInt32.toNat ≤ regs.bits.toNat := by rw [UInt8.toNat_toUInt32]; omega
      have remaining := dropR_bits f₁
      rw [UInt8.toNat_toUInt32] at remaining
      have f₂ : extra.toNat ≤ (dropR regs here.bits.toUInt32).bits.toNat := by omega
      exact ⟨by rw [dropR_bits f₂, remaining]; omega,
        dropR_clean (by omega) f₂ (dropR_clean narrow f₁ (preserve clean))⟩
    refine ⟨.ok stop, regs', H', ?_, out, fun eq => keep (Except.ok.inj eq)⟩
    change runX (do DROPBITS here.bits.toUInt32; k) regs H = _
    rw [runX_bind, DROPBITS_run _ _ _ narrow]
    exact run

include cb write stream in
/-- One full iteration of the literal/distance code-length loop, including
repeated callback refills, all three repeat codes, and both rejection guards. -/
theorem symbol_safe {s : InflateState} {l : IL} {h : Heap}
    (d : Reading owner w off cap cell admitted s l h) (lt : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    ∃ res regs H, runX (do Zlib.Infback.lookup1 c false; trAfter c) l h = .ok ((res, regs), H) ∧
      RoundResult owner w off cap cell r admitted s.«have».toNat res regs H ∧
      (res = .ok false → ReadyBits l → ReadyBits regs) := by
  let c := ctx r owner cell input i output o
  change ∃ res regs H, runX (do Zlib.Infback.lookup1 c false; trAfter c) l h = .ok ((res, regs), H) ∧ _
  obtain ⟨status, regs, H, lookup, valid, allowed, state, found, err⟩ :=
    code_lookup_safe cb (some r) d.decoded.rd d.state d.buffers d.allowed
  rw [runX_bind, lookup]
  cases status with
  | error e => exact ⟨.error e, regs, H, rfl, ⟨(err e rfl).1,(err e rfl).2,s,state,valid,.caller allowed⟩, nofun⟩
  | ok u =>
    change ∃ res regs' H', runX (trAfter c) regs H = .ok ((res, regs'), H') ∧ _
    have dt : Reading owner w off cap cell admitted s regs H := ⟨state, d.wf, d.decoded, valid, allowed⟩
    obtain ⟨_, fit, width, held⟩ := found rfl
    unfold trAfter
    rw [runX_bind, runX_get]
    by_cases lit : regs.here.val < 16
    · simp only [lit, ↓reduceIte]
      obtain ⟨run,out⟩ := literal_safe (r := r) write c rfl dt lt regs.here (UInt16.lt_iff_toNat_lt.mp lit) width
      refine ⟨.ok false, _, _, run, out, fun _ ready => ?_⟩
      obtain ⟨clean, near⟩ := held ready
      have enough : regs.here.bits.toUInt32.toNat ≤ regs.bits.toNat := by simpa using fit
      exact ⟨by rw [dropR_bits enough, UInt8.toNat_toUInt32]; exact near,
        dropR_clean (by rw [UInt8.toNat_toUInt32]; omega) enough clean⟩
    · simp only [lit, ↓reduceIte, rep_eq]
      split
      · exact refill_safe cb dt regs.here width held 2 (by decide) _ fun _ _ d' => previous_safe write stream c rfl rfl d'
      · split
        · exact refill_safe cb dt regs.here width held 3 (by decide) _ fun _ _ d' =>
            count_safe write stream c rfl rfl d' 3 3 0 (by decide) (by decide) (by decide) (by decide)
        · exact refill_safe cb dt regs.here width held 7 (by decide) _ fun _ _ d' =>
            count_safe write stream c rfl rfl d' 7 11 0 (by decide) (by decide) (by decide) (by decide)

include cb write stream in
/-- Read every literal and distance code width. Each successful nonterminal
symbol increases the state index, which cannot exceed 316. -/
theorem read_all_safe {s : InflateState} {l : IL} {h : Heap}
    (d : Reading owner w off cap cell admitted s l h) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    ∃ res regs H, runX (tabRead c) l h = .ok ((res, regs), H) ∧
      match res with
      | .error e => e = Ex.leave ∧ regs.ret = Z_BUF_ERROR ∧ ∃ t, AtExit owner w off cap cell r admitted t regs H
      | .ok _ => ∃ t, (H.istates owner = some t ∧ t.mode = BAD ∧ AtExit owner w off cap cell r admitted t regs H) ∨
          (Reading owner w off cap cell admitted t regs H ∧ t.«have».toNat = t.nlen.toNat + t.ndist.toNat ∧ (ReadyBits l → ReadyBits regs)) := by
  let c := ctx r owner cell input i output o
  let inv := fun regs H => ∃ t, Reading owner w off cap cell admitted t regs H ∧ (ReadyBits l → ReadyBits regs)
  let post := fun (res : Except Ex Unit) (regs : IL) (H : Heap) =>
    match res with
    | .error e => e = Ex.leave ∧ regs.ret = Z_BUF_ERROR ∧ ∃ t, AtExit owner w off cap cell r admitted t regs H
    | .ok _ => ∃ t, (H.istates owner = some t ∧ t.mode = BAD ∧ AtExit owner w off cap cell r admitted t regs H) ∨
        (Reading owner w off cap cell admitted t regs H ∧ t.«have».toNat = t.nlen.toNat + t.ndist.toNat ∧ (ReadyBits l → ReadyBits regs))
  change ∃ res regs H, runX (tabRead c) l h = .ok ((res, regs), H) ∧ post res regs H
  rw [tabRead_eq]
  apply xwhileBrk_wf inv post (fun _ H => tabGap owner (fun _ => 316) H) _ ⟨s,d,id⟩
  · rw [tabGap_of d.state]; unfold fuel; omega
  · intro regs H ⟨t,dt,kept⟩
    have nl := dt.decoded.tab.nlen
    have nd := dt.decoded.tab.ndist
    have sum : (t.nlen + t.ndist).toNat = t.nlen.toNat + t.ndist.toNat := by rw [UInt32.toNat_add]; omega
    have cond : runX (trCond c) regs H = .ok ((.ok (decide (t.«have» < t.nlen + t.ndist)), regs), H) := by
      unfold trCond
      rw [show c.st = some (.tab owner) from rfl, runX_bind, runX_lift_ok (ldInflateState_tab dt.state)]
      rfl
    refine ⟨regs, H, _, cond, fun more => ?_, fun done => ?_⟩
    · have lt := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true more)
      obtain ⟨res, regs', H', run, out, clean⟩ := symbol_safe cb write stream dt (by omega)
      refine ⟨res, regs', H', run, ?_⟩
      cases res with
      | error e => exact out
      | ok stop =>
        obtain ⟨t', ⟨rfl,st,bad,access⟩ | ⟨rfl,dt',grow⟩⟩ := out
        · exact ⟨t', Or.inl ⟨st,bad,access⟩⟩
        · refine ⟨⟨t', dt', clean rfl ∘ kept⟩, ?_⟩
          rw [tabGap_of dt.state, tabGap_of dt'.state]
          omega
    · have ge := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp (of_decide_eq_false done))
      exact ⟨t, Or.inr ⟨dt, by have := dt.decoded.le; omega, kept⟩⟩

end
#print axioms symbol_safe
#print axioms read_all_safe
end Zlib.Infback.AddressedTable
