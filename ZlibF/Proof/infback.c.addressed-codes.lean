import ZlibF.Proof.«infback.c.addressed-table»
import ZlibF.Proof.«infback.c.addressed-link»
import ZlibF.Proof.«infback.c.safety-table-codes»

/-! The first dynamic table build and the transition to reading length and
distance symbols with address-retaining input callbacks. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

/-- From the start of the dynamic block through the first table build. On
success the next decoder step starts at index zero with a safe prefix table. -/
theorem build_codes_safe {owner w off cap : Nat} {cell : BPtrCell} {inCb : CInCb} {i : VoidPtr}
    {outCb : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop}
    (cb : Callbacks owner w off cap cell inCb i outCb o admitted)
    (write : ∀ cells H t v, admitted cells H → H.istates owner = some t → t.«have».toNat < 19 →
      v.toNat ≤ 7 → admitted cells (setI H owner (clSet t v)))
    {r : ZStreamRef} {s : InflateState} {l : IL} {h : Heap}
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (accept : ∀ cs H t nl nd nc, admitted cs H → H.istates owner = some t →
      nl ≤ (286 : UInt32) → nd ≤ (30 : UInt32) → nc.toNat ≤ 19 →
      admitted cs (setI H owner {t with nlen := nl, ndist := nd, ncode := nc, «have» := 0}))
    (install : ∀ cs H t wa ca nx lb, admitted cs H → H.istates owner = some t →
      let done := cdSt owner t wa ca nx lb
      done.WellFormed → RdTab owner done → admitted cs (setI H owner {done with «have» := 0}))
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (mode : s.mode = TABLE) (wf : s.WellFormed) :
    let c := addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o
    (∃ regs H, regs.ret = Z_BUF_ERROR ∧ runX (back_TABLE c) l h = .ok ((.error Ex.leave, regs), H) ∧
      ∃ t, AtExit owner w off cap cell r admitted t regs H) ∨
    (∃ regs H t, H.istates owner = some t ∧ t.mode = BAD ∧ runX (back_TABLE c) l h = .ok ((.ok (), regs), H) ∧
      AtExit owner w off cap cell r admitted t regs H) ∨
    (∃ regs H t, H.istates owner = some t ∧ t.WellFormed ∧ TabSt t ∧ RdTab owner t ∧ t.«have» = 0 ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧ (ReadyBits l → ReadyBits regs) ∧
      runX (back_TABLE c) l h = runX (do tabRead c; tabC c) regs H) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o
  rcases header_safe cb write stream accept state buf allowed wf.1 with stop | bad | next
  · exact Or.inl stop
  · exact Or.inr (Or.inl bad)
  obtain ⟨regs, H, t, present, _, nl, nd, nc, widths, oldMode, well, buffers, ok, clean, enter⟩ := next
  obtain ⟨ret, nx, lb, wa, ca, valid, call, -, table⟩ := tabB_run c rfl present (well wf) widths regs
  let built := cdSt owner t wa ca nx lb
  have live : (setI H owner built).istates owner = some built := upd_same ..
  have cut : runX (back_TABLE c) l h = runX (tabBTail c ret) {regs with ret} (setI H owner built) := enter.trans call
  by_cases success : ret = 0
  · subst ret
    let done := {built with «have» := 0}
    let after := setI H owner done
    let nextRegs := {regs with ret := 0}
    have set : wrS c.st (fun t => {t with «have» := 0}) (setI H owner built) = .ok ((),after) := by
      rw [show c.st = some (.tab owner) from rfl, wrS_tab live, setI_setI]
    have out : runX (back_TABLE c) l h = runX (do tabRead c; tabC c) nextRegs after := by
      rw [cut]
      simp only [tabBTail, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, runX_bind, runX_lift_ok set]
      rfl
    refine Or.inr (Or.inr ⟨nextRegs, after, done, upd_same .., valid, ?_, table rfl, rfl, ?_,
      install _ _ _ _ _ _ _ ok present valid (table rfl), clean, out⟩)
    · exact ⟨oldMode.trans mode, UInt32.le_iff_toNat_le.mp nl, UInt32.le_iff_toNat_le.mp nd, UInt32.le_iff_toNat_le.mp nc⟩
    · exact {buffers with window := ⟨buffers.window.storage, buffers.window.writable⟩}
  · obtain ⟨z, alive⟩ := stream _ _ ok
    have still : r.get (setI H owner built) = some z := by simpa using alive
    obtain ⟨k, fail⟩ := badMode_ctx_run c rfl rfl still live "invalid code lengths set" lit_code_lengths
    let z' := {z with msg := .ref (.str k) 0}
    let failed := {built with mode := BAD}
    refine Or.inr (Or.inl ⟨{regs with ret}, setI (r.put (setI H owner built) z') owner failed,
      failed, upd_same .., rfl, ?_, ?_⟩)
    · rw [cut]
      have nonzero : (ret != 0) = true := by simpa using success
      simp only [tabBTail, nonzero, ↓reduceIte, runX_bind, runX_lift_ok fail]
      rfl
    have prev : Buffers cell w off cap built regs (setI H owner built) :=
      {buffers with window := ⟨buffers.window.storage,buffers.window.writable⟩}
    have b := prev.putStream r z'
    exact ⟨upd_same ..,{b with window := ⟨b.window.storage,b.window.writable⟩},
      .state (.message (.state (.caller ok) built) still _) _⟩

#print axioms build_codes_safe

/-- Each successful code-length lookup selects the entry for the current held
bits, even if the input callback changed the address between lookup attempts. -/
theorem code_lookup_safe {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (strm : ZStreamPtr) {s : InflateState} {l : IL} {h : Heap} (tab : RdTab owner s)
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H, runX (Zlib.Infback.lookup1 c false) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → regs.here = s.codes.getD (regs.hold.toNat % 2 ^ s.lenbits.toNat) default ∧
        regs.here.bits.toNat ≤ regs.bits.toNat ∧ regs.here.bits.toNat ≤ 7 ∧
        (ReadyBits l → regs.hold.toNat < 2 ^ regs.bits.toNat ∧ regs.bits.toNat - regs.here.bits.toNat < 8)) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  obtain ⟨ptr, safe, alpha, contents⟩ := tab
  have seven := safe.2.1
  obtain ⟨status, regs, H, run, valid, ok, present, found, err⟩ :=
    root_safe cb strm false state buf allowed (ca := s.codes) (nb := s.lenbits) ptr rfl
      (fun _ _ _ owned => CodeRef.get_istate_codes owned) (by omega) safe.2.2.1
      (fun j lt => by have := (safe.2.2.2 j lt).2.1; omega)
  refine ⟨status, regs, H, run, valid, ok, present, ?_, err⟩
  intro accept
  obtain ⟨eq, fit, _⟩ := found accept
  have small := (safe.2.2.2 _ (Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.lenbits.toNat))).2.1
  refine ⟨by simpa using eq, fit, by rw [eq]; omega, ?_⟩
  rintro ⟨short, clean⟩
  obtain ⟨status', regs', H', run', _, _, _, result, _⟩ :=
    root_history_safe (strm := strm) cb false state buf allowed clean (ca := s.codes) (nb := s.lenbits) ptr rfl
      (fun _ _ _ owned => CodeRef.get_istate_codes owned) (by omega) safe.2.2.1
      (fun j lt => by have := (safe.2.2.2 j lt).2.1; omega)
  cases Except.ok.inj (run.symm.trans run')
  obtain ⟨found, _, held, _, history⟩ := result accept
  exact ⟨held, by rw [found]; exact bits_after_cl contents short held (found ▸ fit) history⟩

#print axioms code_lookup_safe
end Zlib.Infback.AddressedTable
