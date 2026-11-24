import ZlibF.Proof.«infback.c.addressed-symbol»
import ZlibF.Proof.«infback.c.safety-table-lens»

/-! The addressed decoder's dynamic-block header, from the first input bits
through all three table constructions and the fallthrough to LEN. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

/-- The two table builds update these members of the decoder record. -/
def TablesOnly (s t : InflateState) : Prop :=
  t = {s with
    next := t.next, lencode := t.lencode, distcode := t.distcode, lenbits := t.lenbits
    distbits := t.distbits, work := t.work, codes := t.codes, mode := t.mode}

private theorem build_pair (c : DecoderCtx) {owner w off cap : Nat} {cell : BPtrCell} {A : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (hr : c.strm = some r) (hc : c.st = some (.tab owner)) {h : Heap} {s : InflateState} {z : ZStream}
    (stream : r.get h = some z) (state : h.istates owner = some s) (wf : s.WellFormed)
    (st : TabSt s) (full : s.«have».toNat = s.nlen.toNat + s.ndist.toNat) (widths : RL s) (l : IL)
    (buf : Buffers cell w off cap s l h) (ok : A l.pointerLocals h) :
    (∃ regs H t, H.istates owner = some t ∧ t.mode = BAD ∧ runX (tabLens c) l h = .ok ((.ok (), regs), H) ∧
      AtExit owner w off cap cell r A t regs H) ∨
    (∃ t, TablesOnly s t ∧ t.mode = LEN ∧ t.WellFormed ∧ TablesOk owner t ∧
      runX (tabLens c) l h = runX (back_LEN c) {l with ret := 0} (setI h owner t)) := by
  obtain ⟨a,nx,lb,wa,ca,well,first,-,built⟩ := literal_build c hc state wf st full widths l
  let lit := lnSt owner s nx lb wa ca
  let hL := setI h owner lit
  have live : hL.istates owner = some lit := upd_same ..
  have alive : r.get hL = some z := by simpa [hL] using stream
  change runX (tabLens c) l h = runX (tabLensTail1 c a) {l with ret := a} hL at first
  by_cases accepted : a = 0
  · subst a
    have lengths (k : Nat) (lt : k < lit.ndist.toNat) : (lit.lens.getD (lit.nlen.toNat+k) 0).toNat ≤ 15 :=
      widths _ (by change k < s.ndist.toNat at lt; change s.nlen.toNat+k < s.«have».toNat; omega)
    obtain ⟨b,last,db,work,codes,wfD,second,-,both⟩ :=
      distance_build c hc live well st.nlen st.ndist lengths (built rfl) {l with ret := 0}
    let dist := dsSt lit last db work codes
    let hD := setI h owner dist
    have read : hD.istates owner = some dist := upd_same ..
    have same : setI hL owner dist = hD := setI_setI ..
    change runX (tabLensTail1 c 0) {l with ret := 0} hL =
      runX (tabLensTail2 c b) {l with ret := b} (setI hL owner dist) at second
    rw [same] at second
    by_cases accept : b = 0
    · subst b
      let t := {dist with mode := LEN}
      refine Or.inr ⟨t,rfl,rfl,wfD,both rfl,?_⟩
      rw [first, second]
      have set : setMode c.st LEN hD = .ok ((), setI h owner t) := by
        rw [hc, setMode_tab read, show setI hD owner t = setI h owner t from setI_setI ..]
      simp only [tabLensTail2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, runX_bind, runX_lift_ok set]
    · have nz : (b != 0) = true := by simpa using accept
      have liveZ : r.get hD = some z := by simpa [hD] using stream
      obtain ⟨key,bad⟩ := badMode_ctx_run c hr hc liveZ read _ lit_distances
      refine Or.inl ⟨{l with ret := b}, setI (r.put hD {z with msg := .ref (.str key) 0}) owner {dist with mode := BAD},
        {dist with mode := BAD}, upd_same .., rfl, ?_, ?_⟩
      · rw [first,second]
        simp only [tabLensTail2,nz,↓reduceIte,runX_bind,runX_lift_ok bad]; rfl
      have pre : Buffers cell w off cap dist l hD :=
        {buf with window := ⟨buf.window.storage,buf.window.writable⟩}
      have b' := pre.putStream r {z with msg := .ref (.str key) 0}
      exact ⟨upd_same ..,{b' with window := ⟨b'.window.storage,b'.window.writable⟩},
        .state (.message (.state (.caller ok) dist) liveZ _) _⟩
  · have nz : (a != 0) = true := by simpa using accepted
    obtain ⟨key,bad⟩ := badMode_ctx_run c hr hc alive live _ lit_literal_lengths
    refine Or.inl ⟨{l with ret := a}, setI (r.put hL {z with msg := .ref (.str key) 0}) owner {lit with mode := BAD},
      {lit with mode := BAD}, upd_same .., rfl, ?_, ?_⟩
    · rw [first]
      simp only [tabLensTail1,tabLensTail1With,nz,↓reduceIte,runX_bind,runX_lift_ok bad]; rfl
    have pre : Buffers cell w off cap lit l hL :=
      {buf with window := ⟨buf.window.storage,buf.window.writable⟩}
    have b' := pre.putStream r {z with msg := .ref (.str key) 0}
    exact ⟨upd_same ..,{b' with window := ⟨b'.window.storage,b'.window.writable⟩},
      .state (.message (.state (.caller ok) lit) alive _) _⟩

/-- The caller assertion is preserved by the decoder's private writes between
callbacks. Each field describes the concrete writes of one stage. -/
structure DynamicFrame (owner : Nat) (r : ZStreamRef) (admitted : PointerLocals → Heap → Prop) : Prop where
  stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z
  counts : ∀ cs H t nl nd nc, admitted cs H → H.istates owner = some t →
    nl ≤ (286 : UInt32) → nd ≤ (30 : UInt32) → nc.toNat ≤ 19 →
    admitted cs (setI H owner {t with nlen := nl, ndist := nd, ncode := nc, «have» := 0})
  ordered : ∀ cs H t v, admitted cs H → H.istates owner = some t →
    t.«have».toNat < 19 → v.toNat ≤ 7 → admitted cs (setI H owner (clSet t v))
  codes : ∀ cs H t wa ca nx lb, admitted cs H → H.istates owner = some t →
    let done := cdSt owner t wa ca nx lb
    done.WellFormed → RdTab owner done → admitted cs (setI H owner {done with «have» := 0})
  lengths : ∀ cs H t v, admitted cs H → H.istates owner = some t →
    t.«have».toNat < t.nlen.toNat + t.ndist.toNat → v.toNat ≤ 15 → admitted cs (setI H owner (rdSet t v))
  tables : ∀ cs H s t, admitted cs H → H.istates owner = some s → TablesOnly s t →
    t.mode = LEN → t.WellFormed → TablesOk owner t → admitted cs (setI H owner t)

/-- A caller assertion that only observes its own objects satisfies all five
decoder-write clauses by a single frame rule. -/
theorem DynamicFrame.of_private {owner : Nat} {r : ZStreamRef} {admitted : PointerLocals → Heap → Prop}
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (privateState : ∀ cs H s, admitted cs H → admitted cs (setI H owner s)) : DynamicFrame owner r admitted :=
  ⟨stream, fun _ _ _ _ _ _ ok _ _ _ _ => privateState _ _ _ ok,
    fun _ _ _ _ ok _ _ _ => privateState _ _ _ ok, fun _ _ _ _ _ _ _ ok _ _ _ => privateState _ _ _ ok,
    fun _ _ _ _ ok _ _ _ => privateState _ _ _ ok, fun _ _ _ _ ok _ _ _ _ _ => privateState _ _ _ ok⟩

private def keptState (before now : InflateState) : Prop := now.last = before.last ∧ (StOk before → StOk now)

private theorem DynamicFrame.keep {owner : Nat} {r : ZStreamRef} {A : PointerLocals → Heap → Prop}
    (frame : DynamicFrame owner r A) (s : InflateState) :
    DynamicFrame owner r (WithDecoder owner (keptState s) A) := by
  refine ⟨fun cs H ok => frame.stream cs H ok.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro cs H t nl nd nc ok st lim₁ lim₂ lim₃
    exact .intro (frame.counts cs H t nl nd nc ok.1 st lim₁ lim₂ lim₃) (upd_same ..) (ok.2 t st)
  · intro cs H t v ok st bound width
    exact .intro (frame.ordered cs H t v ok.1 st bound width) (upd_same ..) (ok.2 t st)
  · intro cs H t wa ca nx lb ok st _ wf table
    exact .intro (frame.codes cs H t wa ca nx lb ok.1 st wf table) (upd_same ..) (ok.2 t st)
  · intro cs H t v ok st bound width
    exact .intro (frame.lengths cs H t v ok.1 st bound width) (upd_same ..) (ok.2 t st)
  · intro cs H t u ok st fields mode wf tables
    refine .intro (frame.tables cs H t u ok.1 st fields mode wf tables) (upd_same ..) ?_
    change keptState s u
    rw [show u = _ from fields]
    exact ok.2 t st

/-- The dynamic block can leave on input exhaustion, set BAD, or fall through
to LEN with both tables ready to read. -/
theorem dynamic_safe {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted) (frame : DynamicFrame owner r admitted)
    {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (mode : s.mode = TABLE)
    (wf : s.WellFormed) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    (∃ regs H, regs.ret = Z_BUF_ERROR ∧ runX (back_TABLE c) l h = .ok ((.error Ex.leave, regs), H) ∧
      ∃ t, AtExit owner w off cap cell r admitted t regs H) ∨
    (∃ regs H t, H.istates owner = some t ∧ t.mode = BAD ∧ runX (back_TABLE c) l h = .ok ((.ok (), regs), H) ∧
      AtExit owner w off cap cell r admitted t regs H) ∨
    (∃ regs H t, H.istates owner = some t ∧ t.mode = LEN ∧ t.WellFormed ∧ TablesOk owner t ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧ (ReadyBits l → ReadyBits regs) ∧
      (t.last = s.last ∧ (StOk s → StOk t)) ∧
      runX (back_TABLE c) l h = runX (back_LEN c) regs H) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have readMode {H : Heap} {t : InflateState} (present : H.istates owner = some t) :
      rdS c.st (·.mode) H = .ok (t.mode,H) := by
    rw [show c.st = some (.tab owner) from rfl, rdI_eq]; simp [present]
  have guard := cb.withDecoder (keptState s) (fun _ _ valid => valid)
    (fun _ valid => ⟨valid.1, fun ok => ⟨(valid.2 ok).1, (valid.2 ok).2.1, Nat.le_refl _⟩⟩)
  have guarded := frame.keep s
  have initial : WithDecoder owner (keptState s) admitted l.pointerLocals h :=
    .intro allowed state ⟨rfl, id⟩
  rcases build_codes_safe guard guarded.ordered guarded.stream guarded.counts guarded.codes state buf initial mode wf
    with empty | bad | next
  · obtain ⟨regs,H,ret,run,t,access⟩ := empty
    exact Or.inl ⟨regs,H,ret,run,t,access.map (fun _ _ a => a.1)⟩
  · obtain ⟨regs,H,t,live,target,run,access⟩ := bad
    exact Or.inr (Or.inl ⟨regs,H,t,live,target,run,access.map (fun _ _ a => a.1)⟩)
  obtain ⟨regs,H,t,st,well,counts,table,zero,buffers,ok,headerBits,cut⟩ := next
  have d : Reading owner w off cap cell (WithDecoder owner (keptState s) admitted) t regs H := ⟨st, well,
    ⟨counts, table, by simp [zero], by intro k lt; simp [zero] at lt⟩, buffers, ok⟩
  obtain ⟨res,regs',H',run,out⟩ := read_all_safe guard guarded.lengths guarded.stream d
  rw [runX_bind,run] at cut
  cases res with
  | error e =>
    obtain ⟨rfl,ret,t,access⟩ := out
    exact Or.inl ⟨regs',H',ret,cut,t,access.map (fun _ _ a => a.1)⟩
  | ok u =>
    change runX (back_TABLE c) l h = runX (tabC c) regs' H' at cut
    obtain ⟨s', ⟨present,bad,access⟩ | ⟨d',full,readBits⟩⟩ := out
    · refine Or.inr (Or.inl ⟨regs',H',s',present,bad,?_,access.map (fun _ _ a => a.1)⟩)
      have rdm := readMode present
      rw [cut]; unfold tabC
      simp only [runX_bind,runX_lift_ok rdm,bad,beq_self_eq_true,↓reduceIte]; rfl
    · have rdm := readMode d'.state
      have nb : (s'.mode == BAD) = false := by rw [d'.decoded.tab.mode]; decide
      have lens : lensP c.st = .ref (.istate_lens owner) 0 := rfl
      have read : OkOn H' (Ptr.index (Ptr.ref (WRef.istate_lens owner) 0) (256 : Int))
          (s'.lens[0+256]'(by rw [d'.wf.1]; decide)) :=
        Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens d'.state) (by rw [d'.wf.1]; decide)
      obtain ⟨z, live⟩ := guarded.stream _ _ d'.allowed
      unfold tabC at cut
      simp only [runX_bind,runX_lift_ok rdm,nb,Bool.false_eq_true,↓reduceIte,lens,runX_lift_ok read] at cut
      by_cases missing : (s'.lens[0+256]'(by rw [d'.wf.1]; decide) == 0) = true
      · obtain ⟨k,fail⟩ := badMode_ctx_run c rfl rfl live d'.state _ lit_missing_eob
        have wb := d'.buffers.putStream r {z with msg := .ref (.str k) 0}
        refine Or.inr (Or.inl ⟨regs',setI (r.put H' {z with msg := .ref (.str k) 0}) owner {s' with mode := BAD},
          {s' with mode := BAD},upd_same ..,rfl,?_,upd_same ..,
          {wb with window := ⟨wb.window.storage,wb.window.writable⟩},.state (.message (.caller d'.allowed.1) live _) _⟩)
        rw [cut]
        simp only [missing,↓reduceIte,runX_bind,runX_lift_ok fail]; rfl
      · simp only [missing,Bool.false_eq_true,↓reduceIte] at cut
        rcases build_pair c rfl rfl live d'.state d'.wf d'.decoded.tab full d'.decoded.rl regs' d'.buffers d'.allowed with bad | next
        · obtain ⟨regs'',H'',t',present,mode',endRun,access⟩ := bad
          exact Or.inr (Or.inl ⟨regs'',H'',t',present,mode',cut.trans endRun,access.map (fun _ _ a => a.1)⟩)
        · obtain ⟨t',fields,mode',wf',tables,endRun⟩ := next
          have win := congrArg InflateState.window fields
          have size := congrArg InflateState.wsize fields
          exact Or.inr (Or.inr ⟨{regs' with ret := 0},setI H' owner t',t',upd_same ..,mode',wf',tables,
            {d'.buffers with
              window := ⟨d'.buffers.window.storage,d'.buffers.window.writable⟩
              address := win.trans d'.buffers.address
              size := (congrArg UInt32.toNat size).trans d'.buffers.size},
            (guarded.tables _ _ _ _ d'.allowed d'.state fields mode' wf' tables).1, readBits ∘ headerBits,
            (guarded.tables _ _ _ _ d'.allowed d'.state fields mode' wf' tables).2 _ (upd_same ..), cut.trans endRun⟩)

#print axioms dynamic_safe
end Zlib.Infback.AddressedTable
