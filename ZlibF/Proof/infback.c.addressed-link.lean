import ZlibF.Proof.«infback.c.addressed-lookup»
import ZlibF.Proof.«infback.c.safety-lookup2»

/-! Root and second-level Huffman lookups, including the bits retained across
each addressed input callback. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored
open Zlib.Inffast.Spec (LinkOK)

private def PulledFor (needed : Nat → Nat) (l regs : IL) : Prop :=
  (regs.bits = l.bits ∧ regs.hold = l.hold) ∨
  ∃ bits hold, l.bits.toNat ≤ bits ∧ hold < 2 ^ bits ∧ bits < needed hold ∧
    regs.bits.toNat = bits + 8 ∧ regs.hold.toNat % 2 ^ bits = hold

variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    {s : InflateState} {l : IL} {h : Heap}

include cb

private theorem read_safe (body : X Bool) (entry : Nat → Code) (needed : Nat → Nat)
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (clean : l.hold.toNat < 2 ^ l.bits.toNat) (width : ∀ hold, needed hold ≤ 15)
    (read : ∀ (regs : IL) H, admitted regs.pointerLocals H → H.istates owner = some s → regs.last = l.last →
      let next := {regs with here := entry regs.hold.toNat}
      runX body regs H = if needed regs.hold.toNat ≤ regs.bits.toNat then .ok ((.ok true, next), H)
        else runX (do Zlib.Infback.PULLBYTE (addressedCtx strm (some (.tab owner)) cell input i output o); pure false : X Bool) next H) :
    ∃ status regs H, runX (xloopBrk body) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → regs.last = l.last ∧ regs.here = entry regs.hold.toNat ∧ needed regs.hold.toNat ≤ regs.bits.toNat ∧
        regs.hold.toNat < 2 ^ regs.bits.toNat ∧ Ext l regs ∧ PulledFor needed l regs) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let inv := fun (regs : IL) H => Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧
    H.istates owner = some s ∧ regs.last = l.last ∧ regs.hold.toNat < 2 ^ regs.bits.toNat ∧ Ext l regs ∧ PulledFor needed l regs
  let post := fun (status : Except Ex Unit) (regs : IL) H =>
    Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
    (status = .ok () → regs.last = l.last ∧ regs.here = entry regs.hold.toNat ∧ needed regs.hold.toNat ≤ regs.bits.toNat ∧
      regs.hold.toNat < 2 ^ regs.bits.toNat ∧ Ext l regs ∧ PulledFor needed l regs) ∧
    (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR)
  apply xwhileBrk_wf (cond := pure true) (body := body) inv post (fun regs _ => 15 - regs.bits.toNat) _
    (show inv l h from ⟨buf, allowed, state, rfl, clean, ⟨Nat.le_refl _, Nat.mod_eq_of_lt clean⟩, Or.inl ⟨rfl, rfl⟩⟩)
  · unfold fuel; omega
  · intro regs H ⟨valid, ok, st, saved, held, ext, history⟩
    refine ⟨regs, H, true, rfl, fun _ => ?_, nofun⟩
    let ready := {regs with here := entry regs.hold.toNat}
    have call := read regs H ok st saved
    dsimp only at call
    have valid' : Buffers cell w off cap s ready H := {valid with}
    by_cases fit : needed regs.hold.toNat ≤ regs.bits.toNat
    · rw [ite_eq_left fit] at call
      exact ⟨.ok true, ready, H, call, valid', ok, st, fun _ => ⟨saved, rfl, fit, held, ext, history⟩, nofun⟩
    · rw [ite_eq_right fit] at call
      have small := width regs.hold.toNat
      have room : ready.bits.toNat < 32 := by change regs.bits.toNat < 32; omega
      obtain ⟨status, after, heap, pull, valid'', ok', st', appended, err⟩ :=
        pullByte_step (strm := strm) cb st valid' ok room
      cases status with
      | error e =>
        exact ⟨.error e, after, heap, by rw [call, runX_bind, pull], valid'', ok', st', nofun, err⟩
      | ok u =>
        have added := appended rfl
        have count : after.bits.toNat = regs.bits.toNat + 8 := added.count
        have ⟨low, clean'⟩ := added.held room held
        change after.hold.toNat % 2 ^ regs.bits.toNat = regs.hold.toNat at low
        obtain ⟨le, prev⟩ := ext
        have ext' : Ext l after := ⟨by omega, by
          rw [←prev, ←low, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 le)]⟩
        exact ⟨.ok false, after, heap, by rw [call, runX_bind, pull]; rfl,
          ⟨valid'', ok', st', added.last.trans saved, clean', ext',
           Or.inr ⟨_, _, le, held, Nat.lt_of_not_ge fit, count, low⟩⟩, by omega⟩

/-- The entire root lookup, including the bit prefix used by a subsequent link. -/
theorem root_history_safe (dist : Bool) (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    {ref : CodeRef} {base : Nat} {ca : Array Code} {nb : UInt32}
    (tab : (if dist then s.distcode else s.lencode) = .ref ref base)
    (bits : (if dist then s.distbits else s.lenbits) = nb)
    (storage : ∀ cs H, admitted cs H → H.istates owner = some s → Space.get H ref = some ca)
    (root : nb.toNat ≤ 15) (size : base + 2 ^ nb.toNat ≤ ca.size)
    (entries : ∀ j, j < 2 ^ nb.toNat → (ca.getD (base + j) default).bits.toNat ≤ 15) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H, runX (Zlib.Infback.lookup1 c dist) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → regs.here = ca.getD (base + regs.hold.toNat % 2 ^ nb.toNat) default ∧
        regs.here.bits.toNat ≤ regs.bits.toNat ∧ regs.hold.toNat < 2 ^ regs.bits.toNat ∧
        Ext l regs ∧ Pulled ca base nb.toNat l regs) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let entry := fun n : Nat => ca.getD (base + n % 2 ^ nb.toNat) default
  obtain ⟨status, regs, H, run, valid, ok, st, success, err⟩ := read_safe (strm := strm) cb
    (lkBody c dist) entry (fun n => (entry n).bits.toNat) state buf allowed clean
    (fun n => entries _ (Nat.mod_lt n (Nat.two_pow_pos _))) (by
      intro regs H ok st _
      have call := lkBody_run c dist regs rfl st tab bits (storage _ _ ok st) root size
      simpa only [UInt32.le_iff_toNat_le, UInt8.toNat_toUInt32] using call)
  refine ⟨status, regs, H, run, valid, ok, st, fun done => ?_, err⟩
  obtain ⟨_, here, fit, held, ext, hist⟩ := success done
  exact ⟨here, by rw [here]; exact fit, held, ext, hist⟩

/-- A refilling second-level lookup retains its root link, even when the input
callback redirects the cursor between two reads of the same table. -/
theorem link_safe (dist : Bool) (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    {ref : CodeRef} {base : Nat} {ca : Array Code} {P : Nat → Code → Prop}
    (tab : (if dist then s.distcode else s.lencode) = .ref ref base)
    (storage : ∀ cs H, admitted cs H → H.istates owner = some s → Space.get H ref = some ca)
    (link : LinkOK P ca base l.last)
    (sub15 : ∀ j, j < 2 ^ l.last.op.toNat →
      l.last.bits.toNat + (ca.getD (base + l.last.val.toNat + j) default).bits.toNat ≤ 15) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H, runX (Zlib.Infback.lookup2 c dist) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → regs.last = l.last ∧ regs.here = subVal ca base l.last regs.hold.toNat ∧
        l.last.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat ∧ regs.hold.toNat < 2 ^ regs.bits.toNat ∧
        Ext l regs ∧ Pulled2 ca base l.last l regs) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let entry := subVal ca base l.last
  let needed := fun n => l.last.bits.toNat + (entry n).bits.toNat
  have width : ∀ n, needed n ≤ 15 := fun n => sub15 _ (ZlibF.Math.InflateLookup.slice_lt n _ _)
  obtain ⟨status, regs, H, run, valid, ok, st, success, err⟩ := read_safe (strm := strm) cb
    (lk2Body c dist) entry needed state buf allowed clean width (by
      intro regs H ok st saved
      have call := lk2Body_run c dist regs rfl st tab (storage _ _ ok st) (by rw [saved]; exact link)
      rw [saved] at call
      have sum : (l.last.bits.toUInt32 + (entry regs.hold.toNat).bits.toUInt32).toNat = needed regs.hold.toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32]
        exact Nat.mod_eq_of_lt (by have := width regs.hold.toNat; dsimp [needed] at this; omega)
      dsimp only [entry] at sum
      simpa only [UInt32.le_iff_toNat_le, sum, saved] using call)
  refine ⟨status, regs, H, run, valid, ok, st, fun done => ?_, err⟩
  obtain ⟨last, here, fit, held, ext, hist⟩ := success done
  exact ⟨last, here, by rw [here]; exact fit, held, ext, hist⟩

#print axioms root_history_safe
#print axioms link_safe
end Zlib.Infback.AddressedTable
