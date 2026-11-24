import Lean2C.OriginalUncompressDecode
import ZlibF.Proof.«inflate.c.need-dict-sourcecut»
import ZlibF.Proof.«inflate.c.origin-fields-head»
import ZlibF.Proof.«inflate.c.window-pointer-run»
import ZlibF.Proof.«inflate.c.default-view-public»

/-! Rebinding the zero-capacity destination throughout the actual inflate dispatch loop. -/
namespace Lean2C.OriginalUncompress.Refill
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- uncompress2_z initializes a zlib-only decoder. After the header, the
block and trailer modes can never return to gzip header processing. -/
def WrapperMode (s : InflateState) : Prop :=
  (s.mode = HEAD ∧ (s.wrap = 1 ∨ s.wrap = 5)) ∨ DICTID ≤ s.mode

private def Running (c : Ctx) (k i : Nat) (l : IL) (h : Heap) : Prop :=
  ∃ z s bs, DefaultStateJ h (.tab k) i z s ∧ DispatchBuffers h (.tab k) l bs ∧
    HeaderLocal c h (.tab k) s l ∧ l.bits.toNat ≤ 39 ∧ WrapperMode s ∧ NoRoom l

theorem heap_eq_put {k : Nat} {h : Heap} {z : ZStream} (live : h.streams k = some z) (p : BPtr) :
    heap k p h = (ZStreamRef.tab k).put h {z with next_out := p} := by
  simp only [heap, ZStreamRef.put, live]

private theorem stepMode {c : Ctx} {h after : Heap} {k i : Nat} {z stream : ZStream} {s t : InflateState}
    {bs : List UInt8} {l regs : IL} {v : Except Ex Unit} (E : Env c h (.tab k) i z s)
    (current : DefaultStateJ h (.tab k) i z s) (buffer : DispatchBuffers h (.tab k) l bs)
    (bits : l.bits.toNat ≤ 39) (mode : WrapperMode s)
    (run : runX (inflate_dispatch c) l h = .ok ((v, regs), after))
    (final : DefaultStateJ after (.tab k) i stream t) : WrapperMode t := by
  obtain ⟨head, wrap⟩ | high := mode
  · have noGzip : ¬ GzipAllowed s.wrap := by unfold GzipAllowed; rcases wrap with e | e <;> rw [e] <;> decide
    obtain ⟨seen, get, _, _, _, held⟩ := inflate_dispatch_HEAD_origin_record E current buffer head noGzip run
    have same := Option.some.inj (get.symm.trans final.good.live.hs)
    subst seen
    have wrapped : t.wrap = 1 ∨ t.wrap = 5 := held ▸ wrap
    rcases final.modes with m | ⟨m, _⟩ | m
    · exact Or.inl ⟨m, wrapped⟩
    · exact Or.inr m
    · exact False.elim (noGzip (held ▸ m.2.2.1))
  · right
    by_cases d : s.mode = DICTID ∨ s.mode = DICT
    · exact inflate_dispatch_dictionary_mode_floor E current buffer d bits run final.good.live.hs
    · have large : DICT < s.mode := by
        change 16189 ≤ s.mode.toNat at high
        change 16190 < s.mode.toNat
        have h1 : s.mode.toNat ≠ 16189 := fun a => d (Or.inl (UInt32.toNat_inj.mp a))
        have h2 : s.mode.toNat ≠ 16190 := fun a => d (Or.inr (UInt32.toNat_inj.mp a))
        omega
      exact UInt32.le_trans (by decide : DICTID ≤ DICT)
        (UInt32.le_of_lt (ActiveSourceCut.dispatch_above_dictionary E current buffer bits large run final.good.live.hs))

private theorem dispatchStep {c : Ctx} {k i : Nat} (p : BPtr) (root : c.strm = some (.tab k))
    (state : c.st = some (.tab i)) (l : IL) (h : Heap) (before : Running c k i l h) :
    runX (inflate_dispatch c) (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX (inflate_dispatch c) l h) ∧
    ∀ v regs after, runX (inflate_dispatch c) l h = .ok ((v, regs), after) → Running c k i regs after := by
  obtain ⟨z, s, bs, valid, buffer, local_, bits, mode, zero⟩ := before
  have E : Env c h (.tab k) i z s := ⟨root, state, valid.good.live.hz, valid.good.live.hs⟩
  have compared : runX (inflate_dispatch c) (registers p l) (heap k p h) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX (inflate_dispatch c) l h) ∧
      ∀ v regs after, runX (inflate_dispatch c) l h = .ok ((v, regs), after) → NoRoom regs := by
    obtain ⟨head, wrap⟩ | high := mode
    · have changed : Env c (heap k p h) (.tab k) i {z with next_out := p} s := by
        rw [heap_eq_put E.hz]; exact E.put _
      rw [inflate_dispatch_HEAD E l head, inflate_dispatch_HEAD changed (registers p l) head]
      exact header p E buffer.bits wrap (valid.head_none wrap) zero
    · exact dispatch_after_header p l E high zero
  refine ⟨compared.1, ?_⟩
  intro v regs after run
  obtain ⟨v', regs', after', stream, t, _, _, _, source, final, ⟨rest, _, resumed⟩, _, _, _, _, _, bitBound, headLocal, _⟩ :=
    inflate_dispatch_default_view_state_rank E valid buffer local_ bits
  cases Except.ok.inj (source.symm.trans run)
  exact ⟨stream, t, rest, final, resumed, headLocal, bitBound, stepMode E valid buffer bits mode run final,
    compared.2 _ _ _ run⟩

/-- Follow the real endless-condition loop until its exit. The alternate
destination need not denote a model byte allocation. Only the baseline
execution supplies a valid input packet and ordinary stream invariant. -/
theorem dispatch_loop {c : Ctx} {k i : Nat} {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8} {h : Heap}
    (p : BPtr) (E : Env c h (.tab k) i z s) (valid : DefaultStateJ h (.tab k) i z s)
    (buffer : DispatchBuffers h (.tab k) l bs) (local_ : HeaderLocal c h (.tab k) s l)
    (bits : l.bits.toNat ≤ 39) (mode : WrapperMode s) (zero : NoRoom l) :
    ∃ e regs after stream t,
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error e, regs), after) ∧
      runX (xwhile (pure true) (inflate_dispatch c)) (registers p l) (heap k p h) =
        .ok ((.error e, registers p regs), heap k p after) ∧
      DefaultStateJ after (.tab k) i stream t ∧ regs.bits.toNat ≤ 39 ∧ WrapperMode t ∧ NoRoom regs := by
  let I := Running c k i
  have start : I l h := ⟨z, s, bs, valid, buffer, local_, bits, mode, zero⟩
  let body : X Bool := do inflate_dispatch c; pure false
  have mapBody : ∀ a g, I a g → runX body (registers p a) (heap k p g) =
      mapped (fun (v, regs) => (v, registers p regs)) (heap k p) (runX body a g) := by
    intro a g inv
    simp only [body, runX_bind, (dispatchStep p E.strm E.st a g inv).1]
    rcases runX (inflate_dispatch c) a g with err | ⟨⟨v, b⟩, G⟩
    · rfl
    · cases v <;> rfl
  have keepBody : ∀ a g v regs after, I a g → runX body a g = .ok ((v, regs), after) → I regs after := by
    intro a g v regs after inv run
    simp only [body, runX_bind] at run
    rcases result : runX (inflate_dispatch c) a g with err | ⟨⟨res, b⟩, G⟩ <;> rw [result] at run
    · cases run
    · have holds := (dispatchStep p E.strm E.st a g inv).2 _ _ _ result
      cases res <;> cases run <;> exact holds
  have same := xloop_on (cond := pure true) I (fun _ _ _ => rfl) mapBody
    (by intros; cases ‹runX (pure true) _ _ = _›; assumption) keepBody l h start
  obtain ⟨exit, regs, after, _, _, _, _, _, run, _⟩ := inflate_default_view_loop E valid buffer local_ bits
  change runX (xwhile (pure true) (inflate_dispatch c)) _ _ = mapped _ _ (runX (xwhile (pure true) (inflate_dispatch c)) l h) at same
  rw [run] at same
  have endInv : I regs after := by
    apply xwhile_success_control_post I (fun _ => I) _ start run
    intro a g res b G inv source
    have holds := (dispatchStep p E.strm E.st a g inv).2 _ _ _ source
    cases res <;> exact holds
  obtain ⟨stream, t, _, final, _, _, bitBound, eligibility, counts⟩ := endInv
  exact ⟨exit, regs, after, stream, t, run, same, final, bitBound, eligibility, counts⟩

private theorem entryCut {c : Ctx} {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (E : Env c h r i z s) :
    let t := if s.mode = TYPE then {s with mode := TYPEDO} else s
    runX (inflate_run c) IL.init h = runX (xwhile (pure true) (inflate_dispatch c)) (dispatchRegs z t) (setI h i t) := by
  dsimp only
  unfold inflate_run
  rw [runX_bind, runX_rdS E]
  by_cases type : s.mode = TYPE
  · let t := {s with mode := TYPEDO}
    have env : Env c (setI h i t) r i z t := ⟨E.strm, E.st, by simpa using E.hz, upd_same ..⟩
    have loaded := LOAD_run env IL.init
    dsimp only [t] at loaded
    simp only [type, beq_self_eq_true, ↓reduceIte, runX_bind, runX_setMode E, loaded, runX_modify]
    rfl
  · simp only [beq_false_of_ne type, Bool.false_eq_true, ↓reduceIte, type, runX_bind, LOAD_run E, runX_modify]
    have self : setI h i s = h := by simp only [setI, upd_self _ _ _ E.hs]
    rw [self]
    rfl

/-- The real TYPE normalization, register load and dispatch loop agree for
the whole call, including the exit kind and every consumed input byte. -/
theorem decoder_run {c : Ctx} {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    (p : BPtr) (E : Env c h (.tab k) i z s) (valid : DefaultStateJ h (.tab k) i z s)
    (buffers : StreamBuffers h (.tab k)) (nonnull : z.next_out ≠ .null)
    (input : z.next_in = .null → z.avail_in = 0) (local_ : HeaderLocal c h (.tab k) s (dispatchRegs z s))
    (mode : WrapperMode s) (full : z.avail_out = 0) :
    ∃ e regs after stream t, runX (inflate_run c) IL.init h = .ok ((.error e, regs), after) ∧
      runX (inflate_run c) IL.init (heap k p h) = .ok ((.error e, registers p regs), heap k p after) ∧
      DefaultStateJ after (.tab k) i stream t ∧ regs.bits.toNat ≤ 39 ∧ WrapperMode t ∧ NoRoom regs ∧ t.window = s.window := by
  obtain ⟨entry, t, bs, cut, start, env, packet, bound, sizes, frame, heapEq, stateEq⟩ :=
    inflate_run_default_view_entry E valid buffers nonnull input
  have entryLocal := inflate_run_entry_local valid start sizes frame heapEq stateEq local_
  have selected : WrapperMode t := by
    rw [stateEq]; split
    · exact Or.inr (by decide : DICTID ≤ TYPEDO)
    · exact mode
  have initial : NoRoom (dispatchRegs z t) := ⟨full, full⟩
  obtain ⟨e, regs, after, stream, returned, loop, other, final, bits, eligible, zero⟩ :=
    dispatch_loop p env start packet entryLocal bound selected initial
  have source := cut.trans loop
  have changed : Env c (heap k p h) (.tab k) i {z with next_out := p} s := by
    rw [heap_eq_put E.hz]; exact E.put _
  have alternate := entryCut changed
  dsimp only at alternate
  rw [← stateEq] at alternate
  rw [heapEq] at other
  refine ⟨e, regs, after, stream, returned, source, alternate.trans other, final, bits, eligible, zero, ?_⟩
  exact inflate_run_window_unchanged E.strm E.hs final.good.live.hs source

private theorem leave_pair {c : Ctx} {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (p : BPtr) (E : Env c h (.tab k) i z s) (empty : s.wsize = 0) (zero : NoRoom l) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after, inflate_leave c l h = .ok (rc, after) ∧
      inflate_leave c (registers p l) (heap k p h) = .ok (rc, heap k p after) ∧
      after.istates i = some (leaveState s l) := by
  let r := ZStreamRef.tab k
  obtain ⟨dt, _, run⟩ := zero_output_leave (l := l) E empty (zero.2.trans zero.1.symm) bits
  let saved (q : BPtr) := {leaveStream z (registers q l) with
    total_in := z.total_in + (l.in_ - l.have_).toUInt64, data_type := dt}
  let after (q : BPtr) := setI (r.put h (saved q)) i (leaveState s l)
  let rc := if ((l.in_ - l.have_ == 0 || c.flush == Z_FINISH) && l.ret == Z_OK) then Z_BUF_ERROR else l.ret
  have base : inflate_leave c l (r.put h {z with next_out := l.put}) = .ok (rc, after l.put) := run l.put
  have reset : inflate_leave c l h = inflate_leave c l (r.put h {z with next_out := l.put}) := by
    rw [inflate_leave_restore_cut E, inflate_leave_restore_cut (E.put {z with next_out := l.put}), ZStreamRef.put_put]
    rfl
  have result : heap k p (after l.put) = after p := by
    have live : h.streams k = some z := E.hz
    simp only [after, r, heap, setI, ZStreamRef.put, live, upd_same, upd_upd]
    rfl
  refine ⟨rc, after l.put, reset.trans base, ?_, upd_same ..⟩
  rw [heap_eq_put E.hz, result]
  exact run p

private def decodeBody (c : Ctx) : M Int32 := do
  let (v, l) ← runX (inflate_run c) IL.init
  match v with
  | .error (.ret rc) => return rc
  | _ => inflate_leave c l

private theorem body_pair {c : Ctx} {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    (p : BPtr) (E : Env c h (.tab k) i z s) (valid : DefaultStateJ h (.tab k) i z s)
    (buffers : StreamBuffers h (.tab k)) (nonnull : z.next_out ≠ .null)
    (input : z.next_in = .null → z.avail_in = 0) (local_ : HeaderLocal c h (.tab k) s (dispatchRegs z s))
    (mode : WrapperMode s) (window : s.window = .null) (full : z.avail_out = 0) :
    ∃ rc g t, decodeBody c h = .ok (rc, g) ∧ decodeBody c (heap k p h) = .ok (rc, heap k p g) ∧
      g.istates i = some t ∧ WrapperMode t ∧ t.window = .null := by
  obtain ⟨e, regs, after, stream, t, run, other, final, bits, eligible, zero, windowEq⟩ :=
    decoder_run p E valid buffers nonnull input local_ mode full
  have null := windowEq.trans window
  unfold decodeBody
  simp only [bind_app, run, other]
  cases e with
  | ret rc => exact ⟨rc, after, t, rfl, rfl, final.good.live.hs, eligible, null⟩
  | leave =>
    have env : Env c after (.tab k) i stream t := ⟨E.strm, E.st, final.good.live.hz, final.good.live.hs⟩
    obtain ⟨rc, H, left, right, get⟩ := leave_pair p env (final.good.inv.win.nullws null) zero bits
    exact ⟨rc, H, leaveState t regs, left, right, get, eligible, null⟩

private theorem publicEntry {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    (fresh : Fresh h) (live : Live h (.tab k) i z s) (nonnull : z.next_out ≠ .null)
    (input : z.next_in = .null → z.avail_in = 0) (flush : Int32) :
    let c : Ctx := ⟨some (.tab k), some (.tab i), syncBuf h, flush⟩
    inflate (some (.tab k)) flush h =
      (do let rc ← decodeBody c; freeB (syncBuf h); return rc : M Int32) (syncAlloc h) := by
  have ok : (z.next_in == .null && z.avail_in != 0) = false := by
    by_cases empty : z.next_in = .null <;> simp [empty, input]
  have here : Live (syncAlloc h) (.tab k) i z s := { live with hz := live.hz, hs := live.hs }
  dsimp only
  unfold inflate
  simp only [bind_app, allocLocalB_run h fresh, stateCheck_live here, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, ldZStream_ok here.hz, beq_false_of_ne nonnull, ok, Bool.or_self,
    pure_app, here.zst, castI]
  rfl

/-- One complete public inflate called by uncompress2_z, on arbitrary
compressed input and zero output capacity. Only the original cursor must
satisfy the model's byte-range premise. The replacement may designate the
automatic stream member. Both calls free their own four-byte local. -/
theorem inflate_call {h : Heap} {k i : Nat} {z : ZStream} {s : InflateState}
    (p : BPtr) (address : p ≠ .null) (valid : DefaultStateJ h (.tab k) i z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h (.tab k)) (nonnull : z.next_out ≠ .null)
    (input : z.next_in = .null → z.avail_in = 0) (mode : WrapperMode s)
    (window : s.window = .null) (full : z.avail_out = 0) (flush : Int32) :
    ∃ rc after t, inflate (some (.tab k)) flush h = .ok (rc, after) ∧
      inflate (some (.tab k)) flush (heap k p h) = .ok (rc, heap k p after) ∧
      after.istates i = some t ∧ WrapperMode t ∧ t.window = .null := by
  let r := ZStreamRef.tab k
  let c : Ctx := ⟨some r, some (.tab i), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc valid
  have E : Env c (syncAlloc h) r i z s := ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have entry : EntryHeaderFacts h r s z := by
    obtain ⟨_, wrapped⟩ | high := mode
    · exact EntryHeaderFacts.of_none (valid.head_none wrapped)
    · exact EntryHeaderFacts.of_mode high
  have local_ : HeaderLocal c (syncAlloc h) r s (dispatchRegs z s) := entry_header_local valid.good.fresh entry flush
  have ranges := streamBuffers_syncAlloc valid.good.fresh buffers
  obtain ⟨rc, g, t, base, other, state, eligible, null⟩ :=
    body_pair p E allocated ranges nonnull input local_ mode window full
  obtain ⟨_, _, _, _, a, body, _, _, bytes, _, ro⟩ :=
    inflate_default_view_local_state_return E allocated allocator ranges nonnull input local_
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  change decodeBody c (syncAlloc h) = _ at body
  cases Except.ok.inj (base.symm.trans body)
  have fresh : Fresh (heap k p h) := by
    rw [heap_eq_put valid.good.live.hz]
    exact (shape_put valid.good.live.hz _).fresh (by simp) valid.good.fresh
  have live : Live (heap k p h) r i {z with next_out := p} s :=
    {valid.good.live with hz := by rw [heap_eq_put valid.good.live.hz]; exact ZStreamRef.get_put_same valid.good.live.hz _, hs := valid.good.live.hs}
  have required := publicEntry valid.good.fresh valid.good.live nonnull input flush
  have alternate := publicEntry fresh live address input flush
  have free := freeBuf_run bytes ro
  have free' := freeBuf_run (H := heap k p g) (show (heap k p g).bytes h.nextBlk = some a from bytes)
    (show (heap k p g).ro h.nextBlk = false from ro)
  change inflate _ _ h = (decodeBody c >>= fun res => freeB (syncBuf h) >>= fun _ => pure res) (syncAlloc h) at required
  change inflate _ _ (heap k p h) = (decodeBody c >>= fun res => freeB (syncBuf h) >>= fun _ => pure res)
    (heap k p (syncAlloc h)) at alternate
  refine ⟨rc, freeWin g (syncBuf h), t, ?_, ?_, state, eligible, null⟩
  · rw [required, bind_app, base]
    simp only [bind_app, syncBuf, free, pure_app]
  · rw [alternate, bind_app, other]
    simp only [bind_app, syncBuf, free', pure_app]
    rfl

#print axioms inflate_call
#print axioms decoder_run
#print axioms dispatch_loop
end Lean2C.OriginalUncompress.Refill
