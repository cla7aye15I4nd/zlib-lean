import ZlibF.Proof.«infback.c.addressed-codes»
import ZlibF.Proof.«infback.c.safety-table-read»

/-! The code-length repeat loop on the ABI callback decoder. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

structure Reading (owner w off cap : Nat) (cell : BPtrCell) (admitted : PointerLocals → Heap → Prop)
    (s : InflateState) (l : IL) (h : Heap) : Prop where
  state : h.istates owner = some s
  wf : s.WellFormed
  decoded : RdSt owner s
  buffers : Buffers cell w off cap s l h
  allowed : admitted l.pointerLocals h

section
variable {owner w off cap : Nat} {cell : BPtrCell} {admitted : PointerLocals → Heap → Prop}
  (write : ∀ cs H t v, admitted cs H → H.istates owner = some t →
    t.«have».toNat < t.nlen.toNat + t.ndist.toNat → v.toNat ≤ 15 → admitted cs (setI H owner (rdSet t v)))

include write

private theorem appended {s : InflateState} {l : IL} {h : Heap} (d : Reading owner w off cap cell admitted s l h)
    (lt : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) {v : UInt16} (small : v.toNat ≤ 15) :
    Reading owner w off cap cell admitted (rdSet s v) l (setI h owner (rdSet s v)) :=
  ⟨upd_same .., ⟨by simp [rdSet, d.wf.1], d.wf.2⟩, rdSet_st d.decoded lt d.wf.1 small,
    {d.buffers with window := ⟨d.buffers.window.storage, d.buffers.window.writable⟩},
    write _ _ _ _ d.allowed d.state lt small⟩

/-- All copies fit in the 320-entry lengths array. The final zero test also
decrements the unsigned C counter, leaving it at UINT_MAX. -/
theorem repeat_safe (c : DecoderCtx) (hc : c.st = some (.tab owner)) {s : InflateState} {l : IL} {h : Heap}
    (d : Reading owner w off cap cell admitted s l h)
    (fit : s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat) (small : l.len.toNat ≤ 15) :
    ∃ H t, runX (xwhile trCopyCond (trCopyBody c)) l h = .ok ((.ok (), {l with copy := 0 - 1}), H) ∧
      Reading owner w off cap cell admitted t l H ∧ t.«have».toNat = s.«have».toNat + l.copy.toNat := by
  have v15 : l.len.toUInt16.toNat ≤ 15 := by rw [UInt32.toNat_toUInt16]; omega
  let inv := fun (regs : IL) (H : Heap) => ∃ x t, regs = {l with copy := x} ∧
    Reading owner w off cap cell admitted t l H ∧ t.nlen = s.nlen ∧ t.ndist = s.ndist ∧
    t.«have».toNat + x.toNat = s.«have».toNat + l.copy.toNat
  let post := fun (res : Except Ex Unit) (regs : IL) H => res = .ok () ∧ regs = {l with copy := 0 - 1} ∧
    ∃ t, Reading owner w off cap cell admitted t l H ∧ t.«have».toNat = s.«have».toNat + l.copy.toNat
  have loop := xwhileBrk_wf (cond := trCopyCond) (body := do trCopyBody c; pure false) inv post
    (fun regs _ => regs.copy.toNat) (l := l) (h := h) (fun regs H ⟨x,t,eq,dt,nl,nd,total⟩ => by
      subst regs
      have cond : runX trCopyCond {l with copy := x} H = .ok ((.ok (x != 0), {l with copy := x-1}), H) := by
        unfold trCopyCond; simp only [runX_bind, runX_get, runX_set]; rfl
      refine ⟨_, H, _, cond, fun test => ?_, fun test => ?_⟩
      · have nz : x ≠ 0 := by simpa using test
        have pos : 0 < x.toNat := Nat.pos_of_ne_zero (fun eq => nz (UInt32.toNat_inj.mp eq))
        have lt : t.«have».toNat < t.nlen.toNat + t.ndist.toNat := by rw [nl,nd]; omega
        have bound : t.«have».toNat < 320 := by have := dt.decoded.tab.nlen; have := dt.decoded.tab.ndist; omega
        have run := trCopyBody_run c hc dt.state bound dt.wf.1 {l with copy := x-1}
        have sub : (x-1).toNat = x.toNat-1 := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr pos)
        refine ⟨.ok false, _, _, by rw [runX_bind, run]; rfl, ⟨x-1, rdSet t l.len.toUInt16, rfl,
          appended write dt lt v15, nl, nd, ?_⟩, ?_⟩
        · rw [rdSet_have bound, sub]; omega
        · change (x-1).toNat < x.toNat; omega
      · have zero : x = 0 := by simpa using test
        subst x
        exact ⟨rfl, rfl, t, dt, by simpa using total⟩)
    ⟨l.copy, s, rfl, d, rfl, rfl, rfl⟩ (by have := UInt32.toNat_lt l.copy; unfold fuel; omega)
  obtain ⟨res, regs, H, run, rfl, rfl, t, dt, count⟩ := loop
  exact ⟨H, t, run, dt, count⟩

/-- A completed symbol either marks the block bad or advances the number of
decoded lengths while preserving the next iteration's preconditions. -/
def SymbolResult (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef) (admitted : PointerLocals → Heap → Prop)
    (start : Nat) (stop : Bool) (l : IL) (h : Heap) : Prop :=
  ∃ t, (stop = true ∧ h.istates owner = some t ∧ t.mode = BAD ∧ AtExit owner w off cap cell r admitted t l h) ∨
    (stop = false ∧ Reading owner w off cap cell admitted t l h ∧ start < t.«have».toNat)

theorem repeat_tail_safe (c : DecoderCtx) {r : ZStreamRef} (hr : c.strm = some r) (hc : c.st = some (.tab owner))
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z) {s : InflateState} {l : IL} {h : Heap}
    (d : Reading owner w off cap cell admitted s l h) (len : l.len.toNat ≤ 15)
    (least : 3 ≤ l.copy.toNat) (most : l.copy.toNat ≤ 138) :
    ∃ stop regs H, runX (trTail c) l h = .ok ((.ok stop, regs), H) ∧
      SymbolResult owner w off cap cell r admitted s.«have».toNat stop regs H ∧ (ReadyBits l → ReadyBits regs) := by
  have ld : ldInflateState c.st h = .ok (s,h) := hc ▸ ldInflateState_tab d.state
  have nl := d.decoded.tab.nlen
  have nd := d.decoded.tab.ndist
  have used := d.decoded.le
  have sum : (s.«have» + l.copy).toNat = s.«have».toNat + l.copy.toNat := by rw [UInt32.toNat_add]; omega
  have total : (s.nlen + s.ndist).toNat = s.nlen.toNat + s.ndist.toNat := by rw [UInt32.toNat_add]; omega
  by_cases over : s.«have» + l.copy > s.nlen + s.ndist
  · obtain ⟨z, alive⟩ := stream _ _ d.allowed
    obtain ⟨key, bad⟩ := badMode_ctx_run c hr hc alive d.state _ lit_bit_length_repeat
    have wb := d.buffers.putStream r {z with msg := .ref (.str key) 0}
    refine ⟨true, l, setI (r.put h {z with msg := .ref (.str key) 0}) owner {s with mode := BAD}, ?_,
      ⟨{s with mode := BAD}, Or.inl ⟨rfl, upd_same .., rfl,upd_same ..,{wb with window := ⟨wb.window.storage,wb.window.writable⟩},
        .state (.message (.caller d.allowed) alive _) _⟩⟩, id⟩
    unfold trTail
    simp only [runX_bind, runX_lift_ok ld, runX_get, over, ↓reduceIte, runX_lift_ok bad]
    rfl
  · have fit := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp over)
    obtain ⟨H,t,run,dt,count⟩ := repeat_safe write c hc d (by omega) len
    refine ⟨false, {l with copy := 0 - 1}, H, ?_, ⟨t,
      Or.inr ⟨rfl, {dt with buffers := {dt.buffers with}}, by omega⟩⟩, id⟩
    unfold trTail
    simp only [runX_bind, runX_lift_ok ld, runX_get, over, ↓reduceIte, run]
    rfl

theorem literal_safe {r : ZStreamRef} (c : DecoderCtx) (hc : c.st = some (.tab owner)) {s : InflateState} {l : IL} {h : Heap}
    (d : Reading owner w off cap cell admitted s l h) (lt : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (here : Code) (val : here.val.toNat < 16) (width : here.bits.toNat ≤ 7) :
    runX (trLit c here) l h = .ok ((.ok false, dropR l here.bits.toUInt32), setI h owner (rdSet s here.val)) ∧
    SymbolResult owner w off cap cell r admitted s.«have».toNat false (dropR l here.bits.toUInt32)
      (setI h owner (rdSet s here.val)) := by
  have bound : s.«have».toNat < 320 := by have := d.decoded.tab.nlen; have := d.decoded.tab.ndist; omega
  have narrow : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  obtain ⟨add, store⟩ := lens_at d.state bound d.wf.1 here.val
  have ld := ldInflateState_tab d.state
  have present : (setI h owner {s with lens := s.lens.set! s.«have».toNat here.val}).istates owner =
      some {s with lens := s.lens.set! s.«have».toNat here.val} := upd_same ..
  have inc := wrS_tab present (fun t => {t with «have» := t.«have» + 1})
  have dt := appended write d lt (show here.val.toNat ≤ 15 by omega)
  refine ⟨?_, rdSet s here.val, Or.inr ⟨rfl, {dt with buffers := {dt.buffers with}}, by rw [rdSet_have bound]; omega⟩⟩
  unfold trLit
  rw [hc]
  simp only [runX_bind, DROPBITS_run _ _ _ narrow, runX_lift_ok ld, lensP, runX_lift_ok add,
    runX_lift_ok store, runX_lift_ok inc, setI_setI]
  rfl

end
#print axioms repeat_safe
#print axioms repeat_tail_safe
#print axioms literal_safe
end Zlib.Infback.AddressedTable
