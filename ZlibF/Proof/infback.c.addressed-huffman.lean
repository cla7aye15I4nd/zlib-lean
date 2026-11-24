import ZlibF.Proof.«infback.c.addressed-link»
import ZlibF.Proof.«infback.c.safety-len»

/-! Decoding one literal/length or distance symbol with a retained input cursor. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety Zlib.Infback.AddressedStored
open Zlib.Inftrees.Spec.DecodeTableStability (StableQuery)
open Zlib.Inftrees.Proofs (PrefixQuery)
open Zlib.Inffast.Spec (TableSafe)

/-- The read either exits when the input callback is exhausted or enters the
symbol handler at a permitted leaf of the decoder's current table. -/
def ReadsSymbol (owner w off cap : Nat) (cell : BPtrCell) (admitted : PointerLocals → Heap → Prop)
    (s : InflateState) (l : IL) (h : Heap) (step k : X Unit) (leaf : Nat → Code → Prop) : Prop :=
  (∃ regs H, runX step l h = .ok ((.error Ex.leave, regs), H) ∧ regs.ret = Z_BUF_ERROR ∧
    Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s) ∨
  (∃ regs H d, runX step l h = runX k regs H ∧ Buffers cell w off cap s regs H ∧
    admitted regs.pointerLocals H ∧ H.istates owner = some s ∧ leaf d regs.here ∧
    1 ≤ d + regs.here.bits.toNat ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
    regs.bits.toNat - regs.here.bits.toNat < 8 ∧ regs.hold.toNat < 2 ^ regs.bits.toNat)

/-- Both lookup levels select a leaf and leave fewer than eight bits after
its code is consumed. The continuation sees all callback updates. -/
theorem huffman_safe {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (dist : Bool) (isLink : Code → Bool) (k : X Unit) {s : InflateState} {l : IL} {h : Heap}
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (clean : l.hold.toNat < 2 ^ l.bits.toNat) (short : l.bits.toNat < 8)
    {type : UInt32} {ref : CodeRef} {base used : Nat} {ca : Array Code} {nb : UInt32} {lens : List Nat}
    (tab : (if dist then s.distcode else s.lencode) = .ref ref base)
    (width : (if dist then s.distbits else s.lenbits) = nb)
    (storage : ∀ cs H, admitted cs H → H.istates owner = some s → Space.get H ref = some ca)
    {P : Nat → Code → Prop} {L : Code → Prop} [DecidablePred L] (safe : TableSafe P L ca base nb.toNat)
    (P15 : ∀ d e, P d e → e.bits.toNat + d ≤ 15)
    (linkEq : ∀ e, isLink e = Zlib.Inftrees.Spec.Subtable.IsLink type e)
    (codeL : ∀ e, isLink e = true → L e) (Lcode : ∀ e, L e → e.op.toNat ≤ 15 → isLink e = true)
    (inv : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv type ca base nb.toNat used lens)
    (stable : StableQuery type ca base nb.toNat) (pfx : PrefixQuery type ca base nb.toNat) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ReadsSymbol owner w off cap cell admitted s l h (symLook c dist isLink k) k P := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  obtain ⟨root, room, cells⟩ := safe
  have bounded : ∀ j, j < 2 ^ nb.toNat → (ca.getD (base + j) default).bits.toNat ≤ 15 := by
    intro j hj
    have value := cells j hj
    split at value
    · exact value.1
    · have := P15 _ _ value; omega
  obtain ⟨status, first, H, read, valid, ok, st, success, err⟩ :=
    root_history_safe (strm := strm) cb dist state buf allowed clean tab width storage root room bounded
  change runX (Zlib.Infback.lookup1 c dist) l h = .ok ((status, first), H) at read
  cases status with
  | error e =>
    obtain ⟨rfl, ret⟩ := err _ rfl
    exact Or.inl ⟨first, H, by unfold symLook; rw [runX_bind, read], ret, valid, ok, st⟩
  | ok u =>
    obtain ⟨here, fit, held, _, history⟩ := success rfl
    have idx := Nat.mod_lt first.hold.toNat (Nat.two_pow_pos nb.toNat)
    have actual : ca[base + first.hold.toNat % 2 ^ nb.toNat]? = some first.here := by
      rw [here, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]; rfl
    obtain ⟨e, found, pos, _⟩ := inv.rootTable.2.2.2 _ idx
    rw [actual] at found
    cases found
    have cellValue := cells _ idx
    rw [← here] at cellValue
    by_cases linked : isLink first.here = true
    · rw [ite_eq_left (codeL _ linked)] at cellValue
      have selected := (linkEq first.here).symm.trans linked
      obtain ⟨rootBits, _⟩ := inv.subtables _ _ idx actual selected
      let saved := {first with last := first.here}
      have valid' : Buffers cell w off cap s saved H := {valid with}
      have sub15 : ∀ j, j < 2 ^ first.here.op.toNat →
          first.here.bits.toNat + (ca.getD (base + first.here.val.toNat + j) default).bits.toNat ≤ 15 := by
        intro j hj; have := P15 _ _ (cellValue.2.2.2.2 j hj); omega
      obtain ⟨res, second, H', read2, valid2, ok2, st2, success2, err2⟩ :=
        link_safe (strm := strm) (l := saved) cb dist st valid' ok held tab storage cellValue sub15
      change runX (Zlib.Infback.lookup2 c dist) saved H = .ok ((res, second), H') at read2
      have pre : runX (symLook c dist isLink k) l h =
          runX (do Zlib.Infback.lookup2 c dist; DROPBITS (← get).last.bits.toUInt32; k) saved H := by
        unfold symLook
        simp only [runX_bind, read, runX_get, linked, ↓reduceIte, runX_modify]
        rfl
      cases res with
      | error e =>
        obtain ⟨rfl, ret⟩ := err2 _ rfl
        exact Or.inl ⟨second, H', by rw [pre, runX_bind, read2], ret, valid2, ok2, st2⟩
      | ok v =>
        obtain ⟨last, here2, fit2, clean2, ext, hist2⟩ := success2 rfl
        change second.last = first.here at last
        change second.here = subVal ca base first.here second.hold.toNat at here2
        change first.here.bits.toNat + second.here.bits.toNat ≤ second.bits.toNat at fit2
        have room64 : first.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := cellValue.1; omega
        have within : first.here.bits.toUInt32.toNat ≤ second.bits.toNat := by rw [UInt8.toNat_toUInt32]; omega
        let regs := dropR second first.here.bits.toUInt32
        have count : regs.bits.toNat = second.bits.toNat - first.here.bits.toNat := by rw [dropR_bits within, UInt8.toNat_toUInt32]
        have kept : regs.hold.toNat < 2 ^ regs.bits.toNat := by
          rw [count]
          change (second.hold >>> first.here.bits.toUInt32.toUInt64).toNat < _
          rw [shr64_toNat _ _ room64, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), UInt8.toNat_toUInt32,
            ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
          exact clean2
        have short2 : second.bits.toNat - (first.here.bits.toNat + second.here.bits.toNat) < 8 := by
          rw [here2, here]
          apply bits_after_link inv stable pfx short clean2
          · rw [← here]; exact selected
          · rw [← rootBits]; exact fit
          · exact ext
          · rw [← here, ← here2]; exact fit2
          · exact history
          · rw [← here]; exact hist2
        refine Or.inr ⟨regs, H', first.here.bits.toNat, ?_, {valid2 with}, ok2, st2, ?_, ?_, ?_, ?_, kept⟩
        · rw [pre, runX_bind, read2]
          simp only [runX_bind, runX_get]
          rw [last, DROPBITS_run _ _ _ room64]; rfl
        · change P _ second.here
          rw [here2]; exact cellValue.2.2.2.2 _ (ZlibF.Math.InflateLookup.slice_lt _ _ _)
        · change 1 ≤ first.here.bits.toNat + second.here.bits.toNat; omega
        · change second.here.bits.toNat ≤ regs.bits.toNat; omega
        · change regs.bits.toNat - second.here.bits.toNat < 8; omega
    · have leaf : ¬ L first.here := fun yes => by
        rw [ite_eq_left yes] at cellValue
        exact linked (Lcode _ yes cellValue.2.2.1)
      rw [ite_eq_right leaf] at cellValue
      have noLink : isLink first.here = false := by simpa using linked
      have remaining : first.bits.toNat - first.here.bits.toNat < 8 := by
        rw [here]
        apply bits_after_root inv stable pfx short held
        · rw [← here, ← linkEq]; exact noLink
        · rw [← here]; exact fit
        · exact history
      exact Or.inr ⟨first, H, 0, by unfold symLook; rw [runX_bind, read]; simp only [runX_bind, runX_get, noLink, Bool.false_eq_true, ↓reduceIte],
        valid, ok, st, cellValue, by omega, fit, remaining, held⟩

open ZlibF.Spec.Public Zlib.Inffast.Spec in
/-- From the actual slow LEN branch, a retained input cursor leads to the
literal/length handler. The decoder's installed tables may be fixed or dynamic. -/
theorem slow_len_read {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s) (tabs : TablesOk owner s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (globals : ∀ cs H, admitted cs H → LibraryGlobals H) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    (short : l.bits.toNat < 8) (slow : (l.have_ >= 6 && l.left >= 258) = false) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ReadsSymbol owner w off cap cell admitted s l h (back_LEN c) (lenSym c) LenLeaf := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  obtain ⟨ref, base, ca, used, lens, tab, refOk, get, safe, inv, stable, pfx⟩ := lenTab state tabs (globals _ _ allowed)
  have store cs H (ok : admitted cs H) (st : H.istates owner = some s) : Space.get H ref = some ca :=
    (refOk.get_eq (st.trans state.symm) ((globals _ _ ok).trans (globals _ _ allowed).symm)).trans get
  have pre : runX (back_LEN c) l h = runX (symLook c false lenIsLink (lenSym c)) l h := by
    rw [back_LEN_eq']
    simp only [runX_bind, runX_get, slow, Bool.false_eq_true, ↓reduceIte]
  change ReadsSymbol _ _ _ _ _ _ _ _ _ (back_LEN c) (lenSym c) _
  unfold ReadsSymbol
  rw [pre]
  exact huffman_safe cb false lenIsLink (lenSym c) state buf allowed clean short tab rfl store safe
    (fun _ _ x => x.1) lenIsLink_eq (fun e x => lenLink_of_code e.op x)
    (fun e x y => code_of_lenLink e.op x.1 x.2.1 x.2.2 y) inv stable pfx

open ZlibF.Spec.Public Zlib.Inffast.Spec in
/-- The distance-symbol code uses the second installed table and its distinct
link test, including when callbacks redirect the input cursor on a refill. -/
theorem distance_read {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {strm : ZStreamPtr}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s) (tabs : TablesOk owner s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (globals : ∀ cs H, admitted cs H → LibraryGlobals H) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    (short : l.bits.toNat < 8) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ReadsSymbol owner w off cap cell admitted s l h (lenDist c) (distSym c) DistLeaf := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  obtain ⟨ref, base, ca, used, lens, tab, refOk, get, safe, inv, stable, pfx⟩ := distTab state tabs (globals _ _ allowed)
  have store cs H (ok : admitted cs H) (st : H.istates owner = some s) : Space.get H ref = some ca :=
    (refOk.get_eq (st.trans state.symm) ((globals _ _ ok).trans (globals _ _ allowed).symm)).trans get
  change ReadsSymbol _ _ _ _ _ _ _ _ _ (lenDist c) (distSym c) _
  rw [lenDist_eq]
  exact huffman_safe cb true distIsLink (distSym c) state buf allowed clean short tab rfl store safe
    (fun _ _ x => x.1) distIsLink_eq (fun e x => distLink_of_code e.op x)
    (fun e _ x => code_of_distLink e.op x) inv stable pfx

#print axioms slow_len_read
#print axioms distance_read
#print axioms huffman_safe
end Zlib.Infback.AddressedTable
