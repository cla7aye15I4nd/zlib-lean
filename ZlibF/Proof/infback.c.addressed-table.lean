import ZlibF.Proof.«infback.c.addressed-stored»
import ZlibF.Proof.«infback.c.safety-table-read»

/-! The two loops of the addressed decoder that construct the 19 code-length
code lengths. The input callback can change the cursor on each refill. -/

namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs
open Zlib.Infback.Safety Zlib.Infback.AddressedStored

/-- Only the permutation index and the length array change while the table is filled. -/
structure Entry (owner w off cap : Nat) (cell : BPtrCell) (admitted : PointerLocals → Heap → Prop)
    (base s : InflateState) (l : IL) (h : Heap) : Prop where
  state : h.istates owner = some s
  buffers : Buffers cell w off cap s l h
  allowed : admitted l.pointerLocals h
  fields : s = {base with «have» := s.«have», lens := s.lens}
  size : s.lens.size = 320
  recorded : CLInv s

private def limit (encoded : Bool) (s : InflateState) : UInt32 := if encoded then s.ncode else 19

section
variable {owner w off cap : Nat} {cell : BPtrCell} {inCb : CInCb} {i : VoidPtr}
  {outCb : COutCb} {o : VoidPtr} {strm : ZStreamPtr} {admitted : PointerLocals → Heap → Prop}
  (cb : Callbacks owner w off cap cell inCb i outCb o admitted)
  (write : ∀ cells H s v, admitted cells H → H.istates owner = some s → s.«have».toNat < 19 →
    v.toNat ≤ 7 → admitted cells (setI H owner (clSet s v)))

include write in
private theorem afterStore {base s : InflateState} {l : IL} {h : Heap} {v : UInt16}
    (entry : Entry owner w off cap cell admitted base s l h) (inside : s.«have».toNat < 19)
    (width : v.toNat ≤ 7) :
    Entry owner w off cap cell admitted base (clSet s v) l (setI h owner (clSet s v)) := by
  refine ⟨upd_same .., {entry.buffers with window := ⟨entry.buffers.window.storage, entry.buffers.window.writable⟩},
    write _ _ _ _ entry.allowed entry.state inside width, ?_, by simp [clSet, entry.size],
    clSet_inv entry.recorded inside entry.size width⟩
  conv => lhs; unfold clSet; rw [entry.fields]
  rfl

include cb write in
private theorem trip (encoded : Bool) {base s : InflateState} {l : IL} {h : Heap}
    (entry : Entry owner w off cap cell admitted base s l h) (inside : s.«have».toNat < 19) :
    let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
    ∃ status regs H s', runX (if encoded then tl1Body c else tl2Body c) l h = .ok ((status, regs), H) ∧
      Entry owner w off cap cell admitted base s' regs H ∧
      (status = .ok () → s'.«have».toNat = s.«have».toNat + 1 ∧ (ReadyBits l → ReadyBits regs)) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
  cases encoded with
  | false =>
    exact ⟨.ok (), l, _, _, tl2Body_run c rfl entry.state inside entry.size l,
      afterStore write entry inside (v := 0) (by decide), fun _ => ⟨clSet_have inside 0, id⟩, fun _ eq => nomatch eq⟩
  | true =>
    obtain ⟨status, regs, H, run, buf, ok, st, bits, err⟩ :=
      needBits_safe (strm := strm) cb 3 (by decide) entry.state entry.buffers entry.allowed
    change ∃ _ _ _ _, runX (tl1Body c) l h = _ ∧ _
    rw [tl1Body_eq, runX_bind, run]
    have filled : Entry owner w off cap cell admitted base s regs H := {entry with state := st, buffers := buf, allowed := ok}
    cases status with
    | error e => exact ⟨.error e, regs, H, s, rfl, filled, nofun, err⟩
    | ok u =>
      let v := (regs.hold.toUInt32 &&& ((1 : UInt32) <<< 3 - 1)).toUInt16
      have done := afterStore write filled inside (v := v) v3_le
      refine ⟨.ok (), _, _, _, tl1Rest_run c rfl st inside entry.size regs,
        {done with buffers := {done.buffers with}}, fun _ => ⟨clSet_have inside v, ?_⟩, fun _ eq => nomatch eq⟩
      rintro ⟨low, held⟩
      obtain ⟨enough, bound, clean⟩ := bits rfl
      change regs.bits.toNat ≤ max l.bits.toNat (3 + 7) at bound
      change ReadyBits (dropR regs 3)
      exact ⟨by rw [dropR_bits enough]; change regs.bits.toNat - 3 < 8; omega, dropR_clean (by decide) enough (clean held)⟩

include cb write in
/-- The transmitted loop stops at ncode and the zero-fill loop at 19. At each
successful store the index increases by one and all lengths installed so far fit in three bits. -/
private theorem loop_safe (encoded : Bool) {base s : InflateState} {l : IL} {h : Heap}
    (entry : Entry owner w off cap cell admitted base s l h)
    (haveBound : s.«have».toNat ≤ (limit encoded base).toNat) (bound : (limit encoded base).toNat ≤ 19) :
    let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
    ∃ status regs H s', runX (if encoded then tabLoop1 c else tabLoop2 c) l h = .ok ((status, regs), H) ∧
      Entry owner w off cap cell admitted base s' regs H ∧
      (status = .ok () → s'.«have» = limit encoded base ∧ (ReadyBits l → ReadyBits regs)) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
  let cond := if encoded then tl1Cond c else tl2Cond c
  let body := if encoded then tl1Body c else tl2Body c
  let target := limit encoded base
  change target.toNat ≤ 19 at bound
  let inv := fun (regs : IL) (H : Heap) => ∃ t, Entry owner w off cap cell admitted base t regs H ∧ t.«have».toNat ≤ target.toNat ∧ (ReadyBits l → ReadyBits regs)
  let post := fun (res : Except Ex Unit) (regs : IL) (H : Heap) => ∃ t, Entry owner w off cap cell admitted base t regs H ∧
    (res = .ok () → t.«have» = target ∧ (ReadyBits l → ReadyBits regs)) ∧ (∀ e, res = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR)
  have eq : (if encoded then tabLoop1 c else tabLoop2 c) = xwhile cond body := by cases encoded <;> rfl
  change ∃ _ _ _ _, runX (if encoded then tabLoop1 c else tabLoop2 c) l h = _ ∧ _
  rw [eq]
  suffices ends : ∃ res regs H, runX (xwhile cond body) l h = .ok ((res, regs), H) ∧ post res regs H by
    obtain ⟨res, regs, H, run, t, endState⟩ := ends
    exact ⟨res, regs, H, t, run, endState⟩
  apply xwhileBrk_wf (cond := cond) (body := do body; pure false) inv post
    (fun _ H => tabGap owner (fun _ => target.toNat) H) _ (show inv l h from ⟨s, entry, haveBound, id⟩)
  · rw [tabGap_of entry.state]; unfold fuel; omega
  · intro regs H ⟨t, valid, before, clean⟩
    have same : t.ncode = base.ncode := by
      have eq := congrArg InflateState.ncode valid.fields
      exact eq
    have test : runX cond regs H = .ok ((.ok (decide (t.«have» < target)), regs), H) := by
      have rd : ldInflateState c.st H = .ok (t, H) := ldInflateState_tab valid.state
      cases encoded <;> simp [cond, target, limit, tl1Cond, tl2Cond, runX_bind, runX_lift_ok rd, same, runX_pure]
    refine ⟨regs, H, decide (t.«have» < target), test, ?_, ?_⟩
    · intro more
      have lt := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true more)
      have hi : t.«have».toNat < 19 := Nat.lt_of_lt_of_le lt bound
      obtain ⟨res, regs', H', t', run, after, advance, err⟩ := trip (strm := strm) cb write encoded valid hi
      change runX body regs H = _ at run
      cases res with
      | error e => exact ⟨.error e, regs', H', by rw [runX_bind, run], t', after, nofun, err⟩
      | ok u =>
        obtain ⟨inc, kept⟩ := advance rfl
        exact ⟨.ok false, regs', H', by rw [runX_bind, run]; rfl, ⟨t', after, by omega, kept ∘ clean⟩,
          by rw [tabGap_of after.state, tabGap_of valid.state]; omega⟩
    · intro done
      have ge := Nat.le_of_not_lt (fun lt => of_decide_eq_false done (UInt32.lt_iff_toNat_lt.mpr lt))
      exact ⟨t, valid, fun _ => ⟨UInt32.toNat_inj.mp (Nat.le_antisymm before ge), clean⟩, fun _ eq => nomatch eq⟩

include cb write in
/-- Reach the table builder with all 19 lengths bounded, or leave with a refill error.
The continuation reads exactly the state returned by the zero-fill loop. -/
theorem lengths_safe {base : InflateState} {l : IL} {h : Heap}
    (entry : Entry owner w off cap cell admitted base base l h)
    (start : base.«have» = 0) (count : base.ncode.toNat ≤ 19) :
    let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
    ∃ status regs H t, runX (do tabLoop1 c; tabLoop2 c) l h = .ok ((status, regs), H) ∧
      Entry owner w off cap cell admitted base t regs H ∧
      (status = .ok () → t.«have» = 19 ∧ (ReadyBits l → ReadyBits regs) ∧ ∀ j, j < 19 → (t.lens.getD j 0).toNat ≤ 7) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
  obtain ⟨res₁, l₁, H₁, s₁, run₁, entry₁, full₁, fail₁⟩ :=
    loop_safe (strm := strm) cb write true entry (by rw [start]; exact Nat.zero_le _) count
  change runX (tabLoop1 c) l h = _ at run₁
  change ∃ _ _ _ _, runX (do tabLoop1 c; tabLoop2 c) l h = _ ∧ _
  rw [runX_bind, run₁]
  cases res₁ with
  | error e => exact ⟨.error e, l₁, H₁, s₁, rfl, entry₁, nofun, fail₁⟩
  | ok u =>
    have atCount : s₁.«have» = base.ncode := (full₁ rfl).1
    obtain ⟨res₂, l₂, H₂, s₂, run₂, entry₂, full₂, fail₂⟩ :=
      loop_safe (strm := strm) cb write false entry₁ (by rw [atCount]; exact count) (Nat.le_refl 19)
    refine ⟨res₂, l₂, H₂, s₂, run₂, entry₂, ?_, fail₂⟩
    intro success
    have full : s₂.«have» = 19 := (full₂ success).1
    exact ⟨full, (full₂ success).2 ∘ (full₁ rfl).2, entry₂.recorded.all (by rw [full]; rfl)⟩

include cb write in
/-- At the end of the header, the actual decoder enters the table builder on
the checked state. A short input leaves the case before the builder is called. -/
theorem tabA_run {base : InflateState} {l : IL} {h : Heap}
    (entry : Entry owner w off cap cell admitted base base l h)
    (start : base.«have» = 0) (count : base.ncode.toNat ≤ 19) :
    let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
    ∃ regs H t, Entry owner w off cap cell admitted base t regs H ∧
      ((regs.ret = Z_BUF_ERROR ∧ runX (tabA c) l h = .ok ((.error Ex.leave, regs), H)) ∨
       (t.«have» = 19 ∧ (ReadyBits l → ReadyBits regs) ∧ (∀ j, j < 19 → (t.lens.getD j 0).toNat ≤ 7) ∧
        runX (tabA c) l h = runX (tabB c) regs H)) := by
  let c := addressedCtx strm (some (.tab owner)) cell inCb i outCb o
  obtain ⟨res, regs, H, t, run, valid, full, fail⟩ := lengths_safe (strm := strm) cb write entry start count
  have cut : tabA c = ((do tabLoop1 c; tabLoop2 c : X Unit) >>= fun _ => tabB c) := by
    simp only [tabA, x_bind_assoc]
  change runX (do tabLoop1 c; tabLoop2 c) l h = _ at run
  change ∃ _ _ _, _ ∧ (_ ∨ (_ ∧ _ ∧ _ ∧ runX (tabA c) l h = _))
  refine ⟨regs, H, t, valid, ?_⟩
  rw [cut, runX_bind, run]
  cases res with
  | ok u => exact Or.inr ⟨(full rfl).1, (full rfl).2.1, (full rfl).2.2, rfl⟩
  | error e =>
    obtain ⟨rfl, ret⟩ := fail e rfl
    exact Or.inl ⟨ret, rfl⟩

private def lowBits (l : IL) (width : UInt32) := l.hold.toUInt32 &&& ((1 : UInt32) <<< width - 1)
private def discard (l : IL) (width : UInt32) : IL :=
  { l with hold := l.hold >>> width.toUInt64, bits := l.bits - width }

private def headerCounts (s : InflateState) (l : IL) : InflateState :=
  { s with nlen := lowBits l 5 + 257, ndist := lowBits (discard l 5) 5 + 1,
           ncode := lowBits (discard (discard l 5) 5) 4 + 4 }

/-- Evaluate the 14-bit header after refill. This includes every count write and the
subsequent read of the state record before the validation branch. -/
private theorem counts_run {r : ZStreamRef} {s : InflateState} {l regs : IL} {h H : Heap}
    (state : H.istates owner = some s)
    (read : runX (Zlib.Infback.NEEDBITS (addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o) 14)
      l h = .ok ((.ok (), regs), H)) :
    let c := addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o
    let counts := headerCounts s regs
    runX (back_TABLE c) l h = runX (if counts.nlen > 286 || counts.ndist > 30 then do
      badMode c "too many length or distance symbols"; pure ()
    else do
      wrS c.st fun t => {t with «have» := 0}; tabA c)
      (discard (discard (discard regs 5) 5) 4) (setI H owner counts) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o
  let first := {s with nlen := lowBits regs 5 + 257}
  let second := {first with ndist := lowBits (discard regs 5) 5 + 1}
  let count := headerCounts s regs
  have getBits (l : IL) (h : Heap) (n : UInt32) (room : n.toNat < 32) :
      runX (BITS n) l h = .ok ((.ok (lowBits l n), l), h) := BITS_run l h n room
  have drop (l : IL) (h : Heap) (n : UInt32) (room : n.toNat < 64) :
      runX (DROPBITS n) l h = .ok ((.ok (), discard l n), h) := DROPBITS_run l h n room
  have wa : wrS c.st (fun t => {t with nlen := lowBits regs 5 + 257}) H = .ok ((), setI H owner first) :=
    wrS_tab state _
  have wb : wrS c.st (fun t => {t with ndist := lowBits (discard regs 5) 5 + 1}) (setI H owner first) =
      .ok ((), setI H owner second) := by
    have live : (setI H owner first).istates owner = some first := upd_same ..
    rw [show c.st = some (.tab owner) from rfl, wrS_tab live, setI_setI]
  have wc : wrS c.st (fun t => {t with ncode := lowBits (discard (discard regs 5) 5) 4 + 4}) (setI H owner second) =
      .ok ((), setI H owner count) := by
    have live : (setI H owner second).istates owner = some second := upd_same ..
    rw [show c.st = some (.tab owner) from rfl, wrS_tab live, setI_setI]
    rfl
  have ld : ldInflateState c.st (setI H owner count) = .ok (count, setI H owner count) :=
    ldInflateState_tab (upd_same ..)
  change runX (back_TABLE c) l h = _
  rw [back_TABLE_ctx_eq c (fun n code => CodeFrame.need_addressed _ _ _ _ _ _ _ code n)]
  change runX (Zlib.Infback.NEEDBITS c 14) l h = _ at read
  simp only [runX_bind, read, getBits _ _ 5 (by decide), getBits _ _ 4 (by decide),
    drop _ _ 5 (by decide), drop _ _ 4 (by decide), runX_lift_ok wa, runX_lift_ok wb, runX_lift_ok wc, runX_lift_ok ld]
  rfl

include cb write in
/-- The actual TABLE case reaches the code-length table builder with 19 checked
entries, or stops on input exhaustion or an oversized alphabet. -/
theorem header_safe {r : ZStreamRef} {s : InflateState} {l : IL} {h : Heap}
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (accept : ∀ cs H t nl nd nc, admitted cs H → H.istates owner = some t →
      nl ≤ (286 : UInt32) → nd ≤ (30 : UInt32) → nc.toNat ≤ 19 →
      admitted cs (setI H owner {t with nlen := nl, ndist := nd, ncode := nc, «have» := 0}))
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h)
    (size : s.lens.size = 320) :
    let c := addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o
    (∃ regs H, regs.ret = Z_BUF_ERROR ∧ runX (back_TABLE c) l h = .ok ((.error Ex.leave, regs), H) ∧
      ∃ t, AtExit owner w off cap cell r admitted t regs H) ∨
    (∃ regs H t, H.istates owner = some t ∧ t.mode = BAD ∧ runX (back_TABLE c) l h = .ok ((.ok (), regs), H) ∧
      AtExit owner w off cap cell r admitted t regs H) ∨
    (∃ regs H t, H.istates owner = some t ∧ t.«have» = 19 ∧ t.nlen ≤ 286 ∧ t.ndist ≤ 30 ∧ t.ncode ≤ 19 ∧
      (∀ j, j < 19 → (t.lens.getD j 0).toNat ≤ 7) ∧ t.mode = s.mode ∧ (s.WellFormed → t.WellFormed) ∧
      Buffers cell w off cap t regs H ∧ admitted regs.pointerLocals H ∧ (ReadyBits l → ReadyBits regs) ∧
      runX (back_TABLE c) l h = runX (tabB c) regs H) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell inCb i outCb o
  obtain ⟨status, regs, H, header, valid, ok, st, filled, err⟩ :=
    needBits_safe (strm := some r) cb 14 (by decide) state buf allowed
  cases status with
  | error e =>
    obtain ⟨rfl, ret⟩ := err e rfl
    left
    refine ⟨regs, H, ret, ?_,s,st,valid,.caller ok⟩
    change runX (back_TABLE c) l h = _
    rw [back_TABLE_ctx_eq c (fun n code => CodeFrame.need_addressed _ _ _ _ _ _ _ code n), runX_bind, header]
  | ok u =>
    let counts := headerCounts s regs
    let stripped := discard (discard (discard regs 5) 5) 4
    let heap := setI H owner counts
    have cut := counts_run st header
    change runX (back_TABLE c) l h = runX (if counts.nlen > 286 || counts.ndist > 30 then do
      badMode c "too many length or distance symbols"; pure ()
    else do wrS c.st fun t => {t with «have» := 0}; tabA c) stripped heap at cut
    have owned : heap.istates owner = some counts := upd_same ..
    by_cases invalid : (counts.nlen > 286 || counts.ndist > 30) = true
    · obtain ⟨z, present⟩ := stream _ _ ok
      have live : r.get heap = some z := by simpa [heap] using present
      obtain ⟨k, bad⟩ := badMode_ctx_run c rfl rfl live owned _ lit_many_symbols
      right; left
      refine ⟨stripped, setI (r.put heap {z with msg := .ref (.str k) 0}) owner {counts with mode := BAD}, {counts with mode := BAD}, upd_same .., rfl, ?_, ?_⟩
      · rw [cut]
        change runX (if (counts.nlen > 286 || counts.ndist > 30) then _ else _) stripped heap = _
        simp only [invalid, ↓reduceIte, runX_bind, runX_lift_ok bad]; rfl
      have mid : Buffers cell w off cap counts stripped heap :=
        {valid with window := ⟨valid.window.storage,valid.window.writable⟩}
      have wb := mid.putStream r {z with msg := .ref (.str k) 0}
      exact ⟨upd_same ..,{wb with window := ⟨wb.window.storage,wb.window.writable⟩},
        .state (.message (.state (.caller ok) counts) live _) _⟩
    · have nl : counts.nlen ≤ 286 := UInt32.not_lt.mp (fun gt => by simp [gt] at invalid)
      have nd : counts.ndist ≤ 30 := UInt32.not_lt.mp (fun gt => by simp [gt] at invalid)
      have nc : counts.ncode.toNat ≤ 19 := by
        change (lowBits (discard (discard regs 5) 5) 4 + 4).toNat ≤ 19
        rw [UInt32.toNat_add]
        have bound : (lowBits (discard (discard regs 5) 5) 4).toNat < 16 := by
          rw [lowBits, BITS_toNat _ 4 (by decide)]; exact Nat.mod_lt _ (by decide)
        change (_ + 4) % 2^32 ≤ 19; omega
      let base := {counts with «have» := 0}
      let ready := setI H owner base
      have zero : wrS c.st (fun t => {t with «have» := 0}) heap = .ok ((), ready) := by
        rw [show c.st = some (.tab owner) from rfl, wrS_tab owned]; simp only [heap, ready, base, setI_setI]
      have enter : runX (back_TABLE c) l h = runX (tabA c) stripped ready := by
        rw [cut]
        change runX (if (counts.nlen > 286 || counts.ndist > 30) then _ else _) stripped heap = _
        simp only [invalid, Bool.false_eq_true, ↓reduceIte, runX_bind, runX_lift_ok zero]
      have entry : Entry owner w off cap cell admitted base base stripped ready := by
        refine ⟨upd_same .., {valid with window := ⟨valid.window.storage, valid.window.writable⟩},
          accept _ H s counts.nlen counts.ndist counts.ncode ok st nl nd nc, rfl, size, ?_⟩
        rintro j _ ⟨k, small, _⟩
        exact (Nat.not_lt_zero k small).elim
      obtain ⟨loc, H', t, final, stop | next⟩ := tabA_run (strm := some r) cb write entry rfl nc
      · exact Or.inl ⟨loc, H', stop.1, enter.trans stop.2,t,final.state,final.buffers,.caller final.allowed⟩
      · obtain ⟨full, kept, widths, run⟩ := next
        have lens := congrArg InflateState.nlen final.fields
        have dist := congrArg InflateState.ndist final.fields
        have codes := congrArg InflateState.ncode final.fields
        have mode := congrArg InflateState.mode final.fields
        have wf (old : s.WellFormed) : t.WellFormed := by
          have wk := congrArg (fun v : InflateState => v.work.size) final.fields
          have cd := congrArg (fun v : InflateState => v.codes.size) final.fields
          exact ⟨final.size, wk.trans old.2.1, cd.trans old.2.2⟩
        refine Or.inr (Or.inr ⟨loc, H', t, final.state, full, lens ▸ nl, dist ▸ nd,
          codes ▸ UInt32.le_iff_toNat_le.mpr nc, widths, mode, wf, final.buffers, final.allowed, ?_, enter.trans run⟩)
        rintro ⟨low, held⟩
        apply kept
        obtain ⟨enough, high, clean⟩ := filled rfl
        change 14 ≤ regs.bits.toNat at enough
        change regs.bits.toNat ≤ max l.bits.toNat (14 + 7) at high
        have f₁ : (5 : UInt32).toNat ≤ regs.bits.toNat := by change 5 ≤ _; omega
        have n₁ : (dropR regs 5).bits.toNat = regs.bits.toNat - 5 := dropR_bits f₁
        have f₂ : (5 : UInt32).toNat ≤ (dropR regs 5).bits.toNat := by change 5 ≤ _; omega
        have n₂ : (dropR (dropR regs 5) 5).bits.toNat = (dropR regs 5).bits.toNat - 5 := dropR_bits f₂
        have f₃ : (4 : UInt32).toNat ≤ (dropR (dropR regs 5) 5).bits.toNat := by change 4 ≤ _; omega
        change ReadyBits (dropR (dropR (dropR regs 5) 5) 4)
        exact ⟨by rw [dropR_bits f₃, n₂, n₁]; change regs.bits.toNat - 5 - 5 - 4 < 8; omega,
          dropR_clean (by decide) f₃ (dropR_clean (by decide) f₂ (dropR_clean (by decide) f₁ (clean held)))⟩

end
#print axioms lengths_safe
#print axioms header_safe
end Zlib.Infback.AddressedTable
