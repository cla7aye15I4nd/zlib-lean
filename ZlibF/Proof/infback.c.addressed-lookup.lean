import ZlibF.Proof.«infback.c.addressed-stored»
import ZlibF.Proof.«infback.c.safety-lookup»

/-! A root-table read can refill repeatedly through an address-retaining callback.
For a table embedded in the decoder, preserving the owner record also preserves
the lookup table. Static tables can use the caller's heap invariant. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

theorem root_safe {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (strm : ZStreamPtr) (dist : Bool) {s : InflateState} {l : IL} {h : Heap}
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    {ref : CodeRef} {base : Nat} {ca : Array Code} {nb : UInt32}
    (tab : (if dist then s.distcode else s.lencode) = .ref ref base)
    (width : (if dist then s.distbits else s.lenbits) = nb)
    (storage : ∀ cs H, admitted cs H → H.istates owner = some s → Space.get H ref = some ca)
    (root : nb.toNat ≤ 15) (size : base + 2 ^ nb.toNat ≤ ca.size)
    (entries : ∀ j, j < 2 ^ nb.toNat → (ca.getD (base + j) default).bits.toNat ≤ 15) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H, runX (Zlib.Infback.lookup1 c dist) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → regs.here = ca.getD (base + regs.hold.toNat % 2 ^ nb.toNat) default ∧
        regs.here.bits.toNat ≤ regs.bits.toNat ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let inv := fun (regs : IL) H => Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧
    H.istates owner = some s ∧ regs.bits.toNat ≤ max l.bits.toNat 22
  let post := fun (status : Except Ex Unit) (regs : IL) H =>
    Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
    (status = .ok () → regs.here = ca.getD (base + regs.hold.toNat % 2 ^ nb.toNat) default ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∧
    (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR)
  apply xwhileBrk_wf (cond := pure true) (body := lkBody c dist) inv post
    (fun regs _ => 15 - regs.bits.toNat) _ (show inv l h from ⟨buf, allowed, state, by omega⟩)
  · unfold fuel; omega
  · intro regs H ⟨valid, ok, st, mx⟩
    refine ⟨regs, H, true, rfl, fun _ => ?_, nofun⟩
    let here := ca.getD (base + regs.hold.toNat % 2 ^ nb.toNat) default
    let ready := {regs with here}
    have call := lkBody_run c dist regs rfl st tab width (storage _ _ ok st) root size
    have bound := entries _ (Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos nb.toNat))
    have valid' : Buffers cell w off cap s ready H := {valid with}
    by_cases fit : here.bits.toUInt32 ≤ regs.bits
    · rw [ite_eq_left fit] at call
      have count := UInt32.le_iff_toNat_le.mp fit
      exact ⟨.ok true, ready, H, call, valid', ok, st, fun _ => ⟨rfl, by simpa [ready] using count, mx⟩,
        fun _ eq => nomatch eq⟩
    · rw [ite_eq_right fit] at call
      have small : regs.bits.toNat < here.bits.toNat := by
        have bad := mt UInt32.le_iff_toNat_le.mpr fit
        simp only [UInt8.toNat_toUInt32] at bad
        omega
      change here.bits.toNat ≤ 15 at bound
      obtain ⟨status, regs', H', pull, valid'', ok', st', inc, err⟩ :=
        pullByte_safe (strm := strm) cb st valid' ok (show regs.bits.toNat < 32 by omega)
      cases status with
      | error e => exact ⟨.error e, regs', H', by rw [call, runX_bind, pull], valid'', ok', st', nofun, err⟩
      | ok u =>
        have delta : regs'.bits.toNat = regs.bits.toNat + 8 := inc rfl
        exact ⟨.ok false, regs', H', by rw [call, runX_bind, pull]; rfl, ⟨valid'', ok', st', by omega⟩, by omega⟩

#print axioms root_safe
end Zlib.Infback.AddressedTable
