import ZlibF.Proof.«infback.c.back»
import ZlibF.Proof.«infback.c.safety-stored»

/-! The stored-block copy of the addressed callback decoder. The output callback may
change the input address while bytes remain. Its replacement must support precisely
that unread range, including when it shares the output allocation. -/

namespace Zlib.Infback.AddressedStored
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec
open Zlib.Infback Zlib.Infback.Proofs Zlib.Infback.Safety

/-- The two C comparisons clamp the saved length before copying and advancing both cursors. -/
theorem copy_source (st : InflateStatePtr) : copyStoredInput st = (do
    let l ← get
    let k := if l.copy > l.have_ then l.have_ else l.copy
    let n := if k > l.left then l.left else k
    memcpyB l.put l.next n.toNat
    let nx ← l.next.add (n.toNat : Int)
    let pt ← l.put.add (n.toNat : Int)
    set {l with copy := n, have_ := l.have_ - n, next := nx, left := l.left - n, put := pt}
    wrS st fun s => {s with length := s.length - n}) := by
  funext l h
  change runX (copyStoredInput st) l h = runX _ l h
  unfold copyStoredInput
  rw [runX_bind, runX_get]
  conv => rhs; rw [runX_bind, runX_get]
  by_cases input : l.copy > l.have_
  · by_cases room : l.have_ > l.left <;> simp only [input, room, ↓reduceIte]
  · by_cases room : l.copy > l.left <;> simp only [input, room, ↓reduceIte]

/-- The unread range may move to a different offset or allocation at a callback.
Its bytes must fit and be separate from the decoder's writable window slice. -/
def InputRange (w off cap : Nat) (h : Heap) (p : BPtr) (n : UInt32) : Prop :=
  n ≠ 0 → ∃ b pos a, p = .ref (.blk b) pos ∧ h.bytes b = some a ∧
    pos + n.toNat ≤ a.size ∧ (b ≠ w ∨ pos + n.toNat ≤ off ∨ off + cap ≤ pos)

structure Window (w off cap : Nat) (h : Heap) : Prop where
  storage : ∃ a, h.bytes w = some a ∧ off + cap ≤ a.size
  writable : h.ro w = false

structure Buffers (cell : BPtrCell) (w off cap : Nat) (s : InflateState) (l : IL) (h : Heap) : Prop where
  live : (l.pointerLocals.live.lookup cell).isSome = true
  window : Window w off cap h
  address : s.window = .ref (.blk w) off
  size : s.wsize.toNat = cap
  positive : 0 < cap
  left : l.left.toNat ≤ cap
  put : l.put = .ref (.blk w) (off + (cap - l.left.toNat))
  input : InputRange w off cap h l.next l.have_

/-- A completed field leaves at most seven live bits, all in the low part of hold. -/
def ReadyBits (l : IL) : Prop := l.bits.toNat < 8 ∧ l.hold.toNat < 2 ^ l.bits.toNat

theorem Buffers.putStream {cell : BPtrCell} {w off cap : Nat} {s : InflateState} {l : IL} {h : Heap}
    (buf : Buffers cell w off cap s l h) (r : ZStreamRef) (z : ZStream) : Buffers cell w off cap s l (r.put h z) :=
  {buf with window := ⟨by simpa using buf.window.storage, by simpa using buf.window.writable⟩,
            input := by simpa only [InputRange, ZStreamRef.put_bytes] using buf.input}

/-- Heaps reachable from the caller's assertion by the decoder's private
state writes and error-message writeback. -/
inductive ExitFrame (owner : Nat) (r : ZStreamRef) (A : PointerLocals → Heap → Prop) (cs : PointerLocals) : Heap → Prop
  | caller {h} : A cs h → ExitFrame owner r A cs h
  | state {h} (previous : ExitFrame owner r A cs h) (s : InflateState) : ExitFrame owner r A cs (setI h owner s)
  | message {h z} (previous : ExitFrame owner r A cs h) (live : r.get h = some z) (msg : BPtr) :
      ExitFrame owner r A cs (r.put h {z with msg})

theorem ExitFrame.implies {owner r A cs h} {B : PointerLocals → Heap → Prop}
    (frame : ExitFrame owner r A cs h) (start : ∀ H, A cs H → B cs H)
    (edit : ∀ H t, B cs H → B cs (setI H owner t))
    (message : ∀ H z msg, B cs H → r.get H = some z → B cs (r.put H {z with msg})) : B cs h := by
  induction frame with
  | caller a => exact start _ a
  | state _ s ih => exact edit _ s ih
  | message _ atZ msg ih => exact message _ _ msg ih atZ

/-- Live storage and caller state that the exit label can still use. -/
structure AtExit (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef) (A : PointerLocals → Heap → Prop)
    (s : InflateState) (l : IL) (h : Heap) : Prop where
  state : h.istates owner = some s
  buffers : Buffers cell w off cap s l h
  frame : ExitFrame owner r A l.pointerLocals h

theorem AtExit.map {owner w off cap cell r A B s l h} (x : AtExit owner w off cap cell r A s l h)
    (imp : ∀ cs H, A cs H → B cs H) : AtExit owner w off cap cell r B s l h :=
  ⟨x.state,x.buffers,x.frame.implies (fun _ a => .caller (imp _ _ a))
    (fun _ t f => .state f t) (fun _ _ msg f live => .message f live msg)⟩

/-- The two caller functions terminate on admitted heaps. Either may call another decoder,
modify other live pointer cells, or change its own storage. The output callback chooses
the cursor for the remaining input. The supplied count stays in the decoder. -/
structure Callbacks (owner w off cap : Nat) (cell : BPtrCell) (input : CInCb) (i : VoidPtr)
    (output : COutCb) (o : VoidPtr) (admitted : PointerLocals → Heap → Prop) : Prop where
  refill : ∀ cells h s next, admitted cells h → h.istates owner = some s →
    Window w off cap h → (cells.live.lookup cell).isSome = true →
    ∃ n p cs H, (input i cell).run (cells.assign cell next) h = .ok ((n, cs), H) ∧
      cs.live.lookup cell = some p ∧ H.istates owner = some s ∧ Window w off cap H ∧
      InputRange w off cap H p n ∧ admitted cs H
  flush : ∀ cells h s next n, admitted cells h → h.istates owner = some s →
    Window w off cap h → (cells.live.lookup cell).isSome = true → InputRange w off cap h next n →
    ∃ rc p cs H, (output o (.ref (.blk w) off) s.wsize).run (cells.assign cell next) h = .ok ((rc, cs), H) ∧
      cs.live.lookup cell = some p ∧ H.istates owner = some s ∧ Window w off cap H ∧
      InputRange w off cap H p n ∧ admitted cs H
  copy : ∀ cells h (before after : Array UInt8) (s : InflateState) (len : UInt32), admitted cells h → h.istates owner = some s →
    h.bytes w = some before → after.size = before.size →
    (∀ j, j < off ∨ off + cap ≤ j → after[j]? = before[j]?) →
    admitted cells (setI {h with bytes := upd h.bytes w (some after)} owner {s with length := len})
  publish : ∀ cells h s, admitted cells h → h.istates owner = some s →
    admitted cells (setI h owner {s with whave := s.wsize})

/-- A caller assertion accompanied by a property of the current decoder record. -/
def WithDecoder (owner : Nat) (P : InflateState → Prop) (A : PointerLocals → Heap → Prop)
    (cs : PointerLocals) (h : Heap) : Prop := A cs h ∧ ∀ t, h.istates owner = some t → P t

theorem WithDecoder.intro {owner : Nat} {P : InflateState → Prop} {A : PointerLocals → Heap → Prop}
    {cs : PointerLocals} {h : Heap} {s : InflateState} (ok : A cs h)
    (live : h.istates owner = some s) (valid : P s) : WithDecoder owner P A cs h :=
  ⟨ok, fun _ st => (Option.some.inj (live.symm.trans st)) ▸ valid⟩

theorem Callbacks.withDecoder {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {A : PointerLocals → Heap → Prop} (P : InflateState → Prop)
    (cb : Callbacks owner w off cap cell input i output o A)
    (length : ∀ s n, P s → P {s with length := n}) (full : ∀ s, P s → P {s with whave := s.wsize}) :
    Callbacks owner w off cap cell input i output o (WithDecoder owner P A) := by
  constructor
  · intro cs h s next ok st win cellLive
    obtain ⟨n, p, cs', H, run, ptr, live, window, range, kept⟩ := cb.refill cs h s next ok.1 st win cellLive
    exact ⟨n, p, cs', H, run, ptr, live, window, range, .intro kept live (ok.2 s st)⟩
  · intro cs h s next n ok st win cellLive span
    obtain ⟨rc, p, cs', H, run, ptr, live, window, range, kept⟩ := cb.flush cs h s next n ok.1 st win cellLive span
    exact ⟨rc, p, cs', H, run, ptr, live, window, range, .intro kept live (ok.2 s st)⟩
  · intro cs h a b s n ok st get size frame
    exact .intro (cb.copy cs h a b s n ok.1 st get size frame) (upd_same ..) (length s n (ok.2 s st))
  · intro cs h s ok st
    exact .intro (cb.publish cs h s ok.1 st) (upd_same ..) (full s (ok.2 s st))

/-- In particular the copy uses the cursor after the output callback, even if
the previous input callback returned another pointer. -/
theorem copy_safe {owner w off cap : Nat} {cell : BPtrCell} {s : InflateState} {l : IL} {h : Heap}
    (buf : Buffers cell w off cap s l h) (state : h.istates owner = some s)
    (saved : l.copy = s.length) (len : s.length ≠ 0) (hasInput : l.have_ ≠ 0) (hasRoom : l.left ≠ 0) :
    ∃ l' h' s' a', runX (copyStoredInput (some (.tab owner))) l h = .ok ((.ok (), l'), h') ∧
      h' = setI {h with bytes := upd h.bytes w (some a')} owner s' ∧
      h'.istates owner = some s' ∧ s'.length.toNat < s.length.toNat ∧
      Buffers cell w off cap s' l' h' ∧ l'.pointerLocals = l.pointerLocals ∧
      s' = {s with length := s'.length} ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧ ∃ before, h.bytes w = some before ∧ a'.size = before.size ∧
        ∀ j, j < off ∨ off + cap ≤ j → a'[j]? = before[j]? := by
  obtain ⟨b, pos, src, cursor, srcGet, srcFit, apart⟩ := buf.input hasInput
  obtain ⟨dst, dstGet, dstFit⟩ := buf.window.storage
  let k := clampCopy l.copy l.have_ l.left
  have ⟨lenBound, inBound, outBound⟩ := clampCopy_le l.copy l.have_ l.left
  change k.toNat ≤ l.copy.toNat at lenBound
  change k.toNat ≤ l.have_.toNat at inBound
  change k.toNat ≤ l.left.toNat at outBound
  have posK : 0 < k.toNat :=
    Nat.pos_of_ne_zero (fun e => clampCopy_pos _ _ _ (saved ▸ len) hasInput hasRoom
      (UInt32.toNat_inj.mp (by change k.toNat = 0; exact e)))
  let dest := off + (cap - l.left.toNat)
  let bytes := copyRange dst src dest pos k.toNat
  let copied := {h with bytes := upd h.bytes w (some bytes)}
  let s' := {s with length := s.length - k}
  let H := setI copied owner s'
  have leftBound := buf.left
  have dstSpan : dest + k.toNat ≤ dst.size := by dsimp only [dest]; omega
  have dis : BRef.blk w ≠ .blk b ∨ dest + k.toNat ≤ pos ∨ pos + k.toNat ≤ dest := by
    rcases apart with ne | sep | sep
    · exact Or.inl (fun e => ne (BRef.blk.inj e).symm)
    · right; right; dsimp only [dest]; omega
    · right; left; dsimp only [dest]; omega
  have mc : memcpyB l.put l.next k.toNat h = .ok ((), copied) := by
    rw [buf.put, cursor]
    exact Ptr.memcpy_ok (rd := .blk w) (rs := BRef.blk b) dstGet srcGet buf.window.writable
      dstSpan (by omega) dis
  have sizeBytes : bytes.size = dst.size := size_copyRange ..
  obtain ⟨src', srcGet', sz⟩ := get_after_put (a' := bytes) dstGet sizeBytes
    (show Space.get h (BRef.blk b) = some src from srcGet)
  have getDst : Space.get copied (BRef.blk w) = some bytes := upd_same ..
  have next : OkOn copied (l.next.add (k.toNat : Int)) (.ref (.blk b) (pos + k.toNat)) := by
    rw [cursor]; exact Ptr.add_nat_ok srcGet' (by omega)
  have put : OkOn copied (l.put.add (k.toNat : Int)) (.ref (.blk w) (dest + k.toNat)) := by
    rw [buf.put]; exact Ptr.add_nat_ok getDst (by omega)
  have write := wrS_tab (show copied.istates owner = some s from state) (fun x => {x with length := x.length - k})
  have run := copyStoredInput_run (some (.tab owner)) k rfl mc next put write
  have subIn : (l.have_ - k).toNat = l.have_.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr inBound)
  have subOut : (l.left - k).toNat = l.left.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr outBound)
  rw [saved] at lenBound
  have subLen : s'.length.toNat = s.length.toNat - k.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr lenBound)
  refine ⟨_, H, s', bytes, run, rfl, upd_same .., by omega, ?_, rfl, rfl, rfl, rfl, dst, dstGet, sizeBytes, ?_⟩
  rotate_left
  · intro j outside
    exact copyRange_getElem?_outside dst src dest pos k.toNat j (by dsimp only [dest]; omega)
  refine ⟨buf.live, ⟨⟨bytes, getDst, by omega⟩, buf.window.writable⟩, buf.address, buf.size, buf.positive,
    by change (l.left - k).toNat ≤ cap; omega, ?_, ?_⟩
  · change Ptr.ref (BRef.blk w) (dest + k.toNat) = .ref _ (off + (cap - (l.left - k).toNat))
    congr 1; dsimp only [dest]; omega
  · intro _
    refine ⟨b, pos + k.toNat, src', rfl, srcGet', by change pos + k.toNat + (l.have_ - k).toNat ≤ src'.size; omega, ?_⟩
    change b ≠ w ∨ pos + k.toNat + (l.have_ - k).toNat ≤ off ∨ off + cap ≤ pos + k.toNat
    omega


section
variable {owner w off cap : Nat} {strm : ZStreamPtr} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop}
    (cb : Callbacks owner w off cap cell input i output o admitted)

include cb

private theorem pull_safe {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    ∃ status l' h', runX (PULL (addressedCtx strm (some (.tab owner)) cell input i output o)) l h =
        .ok ((status, l'), h') ∧ Buffers cell w off cap s l' h' ∧ admitted l'.pointerLocals h' ∧
        h'.istates owner = some s ∧ l'.copy = l.copy ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧ l'.last = l.last ∧
        (status = .ok () → l'.have_ ≠ 0) ∧ (∀ e, status = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  rw [addressedPull_run _ _ _ _ _ _ _ _ _ buf.live]
  by_cases empty : l.have_ = 0
  · obtain ⟨n, p, cs, H, run, ptr, st, win, span, ok⟩ :=
      cb.refill l.pointerLocals h s l.next allowed state buf.window buf.live
    simp only [empty, ite_true, run, ptr]
    have live : (cs.live.lookup cell).isSome = true := by simp [ptr]
    by_cases zero : n = 0
    · subst n
      exact ⟨.error Ex.leave, _, _, rfl, {buf with live, window := win, input := fun nz => (nz rfl).elim}, ok,
        st, rfl, rfl, rfl, rfl, nofun, fun _ eq => ⟨(Except.error.inj eq).symm, rfl⟩⟩
    · simp only [zero, ite_false]
      exact ⟨.ok (), _, _, rfl, {buf with live, window := win, input := span}, ok, st, rfl, rfl, rfl, rfl, fun _ => zero, fun _ eq => nomatch eq⟩
  · exact ⟨.ok (), l, h, by simp [empty], buf, allowed, state, rfl, rfl, rfl, rfl, fun _ => empty, fun _ eq => nomatch eq⟩

/-- A refill can redirect the byte cursor. It appends one byte above the
previously held bits and leaves the saved table link in its own register. -/
structure InputByte (before after : IL) : Prop where
  count : after.bits.toNat = before.bits.toNat + 8
  last : after.last = before.last
  value : ∃ b : UInt8, after.hold = before.hold + (b.toUInt64 <<< before.bits.toUInt64)

omit cb in
theorem InputByte.held {before after : IL} (step : InputByte before after)
    (room : before.bits.toNat < 32) (clean : before.hold.toNat < 2 ^ before.bits.toNat) :
    after.hold.toNat % 2 ^ before.bits.toNat = before.hold.toNat ∧ after.hold.toNat < 2 ^ after.bits.toNat := by
  obtain ⟨b, value⟩ := step.value
  obtain ⟨sum, bound⟩ := pull_hold before.hold b before.bits (by omega) clean
  rw [value, sum, step.count, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt clean]
  exact ⟨rfl, bound⟩

/-- Consume precisely the byte at the cursor returned by the callback. -/
theorem pullByte_step {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (bits : l.bits.toNat < 32) :
    ∃ status regs H, runX (Zlib.Infback.PULLBYTE (addressedCtx strm (some (.tab owner)) cell input i output o)) l h =
        .ok ((status, regs), H) ∧ Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧
        H.istates owner = some s ∧ (status = .ok () → InputByte l regs) ∧
        (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  obtain ⟨status, regs, H, pull, valid, ok, st, _, sameBits, sameHold, sameLast, has, err⟩ :=
    pull_safe (strm := strm) cb state buf allowed
  unfold Zlib.Infback.PULLBYTE
  rw [runX_bind, pull]
  cases status with
  | error e => exact ⟨.error e, regs, H, rfl, valid, ok, st, nofun, err⟩
  | ok u =>
    cases u
    have nonempty := has rfl
    obtain ⟨b, pos, a, ptr, storage, span, apart⟩ := valid.input nonempty
    have positive : 0 < regs.have_.toNat := Nat.pos_of_ne_zero (fun eq => nonempty (UInt32.toNat_inj.mp eq))
    have inside : pos < a.size := by omega
    let byte := a[pos]
    let nx := Ptr.ref (BRef.blk b) (pos + 1)
    have read : OkOn H (load8 regs.next) byte := by
      rw [ptr]; exact Ptr.load_ok (r := BRef.blk b) storage inside
    have advance : OkOn H (regs.next.add 1) nx := by
      rw [ptr]; exact Ptr.add_nat_ok (n := 1) storage (by omega)
    have shift := congrFun (shl64_run byte.toUInt64 regs.bits (by rw [sameBits]; omega)) H
    have direct : runX absorbInputByte regs H = .ok ((.ok (), pulled regs byte nx), H) := by
      unfold absorbInputByte
      simp only [runX_bind, runX_get, runX_lift_ok read, runX_lift_ok advance, runX_lift_ok shift, runX_set]
      rfl
    have sub : (regs.have_ - 1).toNat = regs.have_.toNat - 1 :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr positive)
    refine ⟨.ok (), pulled regs byte nx, H, direct, ?_, ok, st, ?_, fun _ eq => nomatch eq⟩
    · refine {valid with input := ?_}
      intro _
      refine ⟨b, pos + 1, a, rfl, storage, ?_, ?_⟩
      · change pos + 1 + (regs.have_ - 1).toNat ≤ a.size
        omega
      · change b ≠ w ∨ pos + 1 + (regs.have_ - 1).toNat ≤ off ∨ off + cap ≤ pos + 1
        omega
    · intro _
      refine ⟨?_, sameLast, byte, ?_⟩
      · change (regs.bits + 8).toNat = l.bits.toNat + 8
        rw [sameBits, UInt32.toNat_add]
        exact Nat.mod_eq_of_lt (by change l.bits.toNat + 8 < 2^32; omega)
      · change regs.hold + (byte.toUInt64 <<< regs.bits.toUInt64) = _
        rw [sameHold, sameBits]

theorem pullByte_safe {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (bits : l.bits.toNat < 32) :
    ∃ status regs H, runX (Zlib.Infback.PULLBYTE (addressedCtx strm (some (.tab owner)) cell input i output o)) l h =
        .ok ((status, regs), H) ∧ Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧
        H.istates owner = some s ∧ (status = .ok () → regs.bits.toNat = l.bits.toNat + 8) ∧
        (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  obtain ⟨status, regs, H, run, valid, ok, st, step, err⟩ := pullByte_step (strm := strm) cb state buf allowed bits
  exact ⟨status, regs, H, run, valid, ok, st, fun success => (step success).count, err⟩

/-- Refill until the requested number of bits is available, including early EOF.
Every successful iteration advances the bit count even when a callback replaces the cursor. -/
theorem needBits_safe {s : InflateState} {l : IL} {h : Heap} (k : UInt32) (bound : k.toNat ≤ 32)
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ status regs H, runX (Zlib.Infback.NEEDBITS c k) l h = .ok ((status, regs), H) ∧
      Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
      (status = .ok () → k.toNat ≤ regs.bits.toNat ∧ regs.bits.toNat ≤ max l.bits.toNat (k.toNat + 7) ∧
      (l.hold.toNat < 2 ^ l.bits.toNat → regs.hold.toNat < 2 ^ regs.bits.toNat)) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let valid := fun (regs : IL) (H : Heap) => Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧
    H.istates owner = some s ∧ regs.bits.toNat ≤ max l.bits.toNat (k.toNat + 7) ∧
    (l.hold.toNat < 2 ^ l.bits.toNat → regs.hold.toNat < 2 ^ regs.bits.toNat)
  let post := fun (status : Except Ex Unit) (regs : IL) (H : Heap) =>
    Buffers cell w off cap s regs H ∧ admitted regs.pointerLocals H ∧ H.istates owner = some s ∧
    (status = .ok () → k.toNat ≤ regs.bits.toNat ∧ regs.bits.toNat ≤ max l.bits.toNat (k.toNat + 7) ∧
      (l.hold.toNat < 2 ^ l.bits.toNat → regs.hold.toNat < 2 ^ regs.bits.toNat)) ∧
    (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR)
  apply xwhileBrk_wf (cond := do return (← get).bits < k) (body := do Zlib.Infback.PULLBYTE c; pure false)
    valid post (fun regs _ => k.toNat - regs.bits.toNat) _ (show valid l h from ⟨buf, allowed, state, by omega, id⟩)
  · unfold fuel; omega
  · intro regs H ⟨v, ok, st, mx, clean⟩
    refine ⟨regs, H, decide (regs.bits < k), by simp [runX_bind, runX_get, runX_pure], ?_, ?_⟩
    · intro guard
      have lt := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true guard)
      obtain ⟨status, regs', H', run, v', ok', st', inc, err⟩ := pullByte_step (strm := strm) cb st v ok (by omega)
      cases status with
      | error e => exact ⟨.error e, regs', H', by rw [runX_bind, run], v', ok', st', nofun, err⟩
      | ok u =>
        have step := inc rfl
        have delta := step.count
        exact ⟨.ok false, regs', H', by rw [runX_bind, run]; rfl, ⟨v', ok', st', by omega, fun start => (step.held (by omega) (clean start)).2⟩, by omega⟩
    · intro guard
      have ge : k.toNat ≤ regs.bits.toNat := Nat.le_of_not_lt (fun lt =>
        (of_decide_eq_false guard) (UInt32.lt_iff_toNat_lt.mpr lt))
      exact ⟨v, ok, st, fun _ => ⟨ge, mx, clean⟩, fun _ eq => nomatch eq⟩

theorem room_safe {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    ∃ status l' h' s', runX (ROOM (addressedCtx strm (some (.tab owner)) cell input i output o)) l h =
        .ok ((status, l'), h') ∧ Buffers cell w off cap s' l' h' ∧ admitted l'.pointerLocals h' ∧
        h'.istates owner = some s' ∧ s'.length = s.length ∧ l'.copy = l.copy ∧ l'.have_ = l.have_ ∧
        (l'.bits = l.bits ∧ l'.hold = l.hold ∧ (s' = s ∨ s' = {s with whave := s.wsize})) ∧
        (status = .ok () → l'.left ≠ 0) ∧ (∀ e, status = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  rw [addressedRoom_run _ _ _ _ _ _ _ _ _ buf.live]
  by_cases full : l.left = 0
  · let s' := {s with whave := s.wsize}
    let ready := setI h owner s'
    have st : ready.istates owner = some s' := upd_same ..
    have win : Window w off cap ready := ⟨buf.window.storage, buf.window.writable⟩
    have span : InputRange w off cap ready l.next l.have_ := buf.input
    obtain ⟨rc, p, cs, H, run, ptr, state', window', input', ok⟩ :=
      cb.flush l.pointerLocals ready s' l.next l.have_ (cb.publish _ _ _ allowed state) st win buf.live span
    have call : (output o s.window s.wsize).run (l.pointerLocals.assign cell l.next) ready = .ok ((rc, cs), H) := by
      rw [buf.address]; exact run
    have live : (cs.live.lookup cell).isSome = true := by simp [ptr]
    have sz : s.wsize ≠ 0 := by intro zero; have := buf.size; have := buf.positive; rw [zero] at *; simp_all
    have position : s.window = .ref (.blk w) (off + (cap - s.wsize.toNat)) := by simp [buf.size, buf.address]
    have wr := wrS_tab state (fun t => {t with whave := s.wsize})
    dsimp only [ready, s'] at call
    have bindOK {α β : Type} (a : α) (f : α → Except Fault β) :
        (Except.ok a >>= f) = f a := rfl
    let regs := {l with next := p, put := s.window, left := s.wsize, pointerLocals := cs}
    have valid : Buffers cell w off cap s' regs H := ⟨live, window', buf.address, buf.size, buf.positive,
      Nat.le_of_eq buf.size, position, input'⟩
    simp only [full, bne_self_eq_false, Bool.false_eq_true, ite_false, ldInflateState_tab state,
      bindOK, wr, call, ptr]
    by_cases fail : rc ≠ 0
    · refine ⟨.error Ex.leave, {regs with ret := Z_BUF_ERROR}, H, s', ?_,
        {valid with}, ok, state', rfl, rfl, rfl, ⟨rfl, rfl, Or.inr rfl⟩, nofun, fun _ eq => ⟨(Except.error.inj eq).symm, rfl⟩⟩
      simp [fail]; rfl
    · refine ⟨.ok (), regs, H, s', ?_, valid, ok, state', rfl, rfl, rfl, ⟨rfl, rfl, Or.inr rfl⟩, fun _ => sz, fun _ eq => nomatch eq⟩
      simp [fail]; rfl
  · exact ⟨.ok (), l, h, s, by simp [full]; rfl, buf, allowed, state, rfl, rfl, rfl, ⟨rfl, rfl, Or.inl rfl⟩, fun _ => full, fun _ eq => nomatch eq⟩

def storedTrip (c : DecoderCtx) : X Unit := do
  let s ← ldInflateState c.st
  modify fun l => {l with copy := s.length}
  PULL c
  ROOM c
  copyStoredInput c.st

def moreStored (st : InflateStatePtr) : X Bool := do return (← rdS st (·.length)) != 0

omit cb in
/-- The ABI decoder enters this loop when the stored header passes. -/
theorem back_STORED_loop (c : DecoderCtx) : back_STORED c = (do
    BYTEBITS
    Zlib.Infback.NEEDBITS c 32
    let l ← get
    if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
      badMode c "invalid stored block lengths"
      return
    wrS c.st fun s => {s with length := l.hold.toUInt32 &&& 0xffff}
    INITBITS
    xwhile (moreStored c.st) (storedTrip c)
    setMode c.st TYPE) := rfl

/-- Copying stored bytes can change the remaining length and mark a
full window as available history. The decoder's other fields are preserved. -/
def StoredFields (s t : InflateState) : Prop :=
  t = {s with length := t.length} ∨ t = {s with length := t.length, whave := s.wsize}

omit cb in
private theorem StoredFields.trans {s t u : InflateState} (a : StoredFields s t) (b : StoredFields t u) :
    StoredFields s u := by
  rcases a with a | a <;> rcases b with b | b
  · left; conv => lhs; rw [b, a]
  · right; conv => lhs; rw [b, a]
  · right; conv => lhs; rw [b, a]
  · right; conv => lhs; rw [b, a]

private theorem trip_safe {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) (len : s.length ≠ 0) :
    ∃ result l' h' s', runX (storedTrip (addressedCtx strm (some (.tab owner)) cell input i output o)) l h =
        .ok ((result, l'), h') ∧ Buffers cell w off cap s' l' h' ∧ admitted l'.pointerLocals h' ∧
        h'.istates owner = some s' ∧ StoredFields s s' ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧ (result = .ok () → s'.length.toNat < s.length.toNat) ∧
        (∀ e, result = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let saved := {l with copy := s.length}
  have buf0 : Buffers cell w off cap s saved h := {buf with}
  have start : runX (storedTrip c) l h =
      runX (do PULL c; ROOM c; copyStoredInput c.st) saved h := by
    unfold storedTrip
    have ld : ldInflateState c.st h = .ok (s, h) := ldInflateState_tab state
    rw [runX_bind, runX_lift_ok ld]
    dsimp only
    rw [runX_bind, runX_modify]
  change ∃ _ _ _ _, runX (storedTrip c) l h = _ ∧ _
  rw [start]
  obtain ⟨status, l₁, h₁, pull, b₁, ok₁, st₁, saved₁, bits₁, hold₁, _, has, err⟩ :=
    pull_safe (strm := strm) cb state buf0 allowed
  cases status with
  | error e =>
    exact ⟨.error e, l₁, h₁, s, by rw [runX_bind, pull], b₁, ok₁, st₁, Or.inl rfl, bits₁, hold₁, nofun, err⟩
  | ok u =>
    cases u
    rw [runX_bind, pull]
    dsimp only
    obtain ⟨status, l₂, h₂, s₂, room, b₂, ok₂, st₂, len₂, saved₂, have₂, ⟨bits₂, hold₂, frame₂⟩, space, err₂⟩ :=
      room_safe (strm := strm) cb st₁ b₁ ok₁
    have fields₂ : StoredFields s s₂ := by
      rcases frame₂ with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr rfl
    cases status with
    | error e =>
      exact ⟨.error e, l₂, h₂, s₂, by rw [runX_bind, room], b₂, ok₂, st₂, fields₂, bits₂.trans bits₁, hold₂.trans hold₁, nofun, err₂⟩
    | ok u =>
      cases u
      rw [runX_bind, room]
      dsimp only
      obtain ⟨regs, after, result, bytes, run, heap, record, smaller, valid, cs, fields, bits₃, hold₃, before, db, size, unchanged⟩ :=
        copy_safe b₂ st₂ (saved₂.trans (saved₁.trans len₂.symm)) (by rw [len₂]; exact len) (by rw [have₂]; exact has rfl) (space rfl)
      exact ⟨.ok (), regs, after, result, run, valid, by
        rw [cs, heap]
        have step := cb.copy _ _ _ _ _ result.length ok₂ st₂ db size unchanged
        rw [← fields] at step
        exact step,
        record, fields₂.trans (Or.inl fields), bits₃.trans (bits₂.trans bits₁), hold₃.trans (hold₂.trans hold₁),
        fun _ => by simpa only [len₂] using smaller, fun _ eq => nomatch eq⟩

/-- The entire stored-block copy loop returns with zero bytes still to copy, or leaves
with the callback decoder's buffer error. For each continuing iteration the state's
remaining length decreases even if an output callback redirects the input. -/
theorem storedLoop_safe {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    let c := addressedCtx strm (some (.tab owner)) cell input i output o
    ∃ result regs H s', runX (xwhile (moreStored c.st) (storedTrip c)) l h = .ok ((result, regs), H) ∧
      H.istates owner = some s' ∧ Buffers cell w off cap s' regs H ∧ admitted regs.pointerLocals H ∧
      StoredFields s s' ∧ regs.bits = l.bits ∧ regs.hold = l.hold ∧
      (result = .ok () → s'.length = 0) ∧ (∀ e, result = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) := by
  let c := addressedCtx strm (some (.tab owner)) cell input i output o
  let valid := fun (regs : IL) (H : Heap) =>
    ∃ current, H.istates owner = some current ∧ Buffers cell w off cap current regs H ∧ admitted regs.pointerLocals H ∧
      StoredFields s current ∧ regs.bits = l.bits ∧ regs.hold = l.hold
  let post := fun (result : Except Ex Unit) (regs : IL) (H : Heap) =>
    ∃ s', H.istates owner = some s' ∧ Buffers cell w off cap s' regs H ∧ admitted regs.pointerLocals H ∧
      StoredFields s s' ∧ regs.bits = l.bits ∧ regs.hold = l.hold ∧
      (result = .ok () → s'.length = 0) ∧ (∀ e, result = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR)
  suffices verified : ∃ result regs H, runX (xwhile (moreStored c.st) (storedTrip c)) l h =
      .ok ((result, regs), H) ∧ post result regs H by
    obtain ⟨result, regs, H, run, current, body⟩ := verified
    exact ⟨result, regs, H, current, run, body⟩
  unfold xwhile
  apply xwhileBrk_wf (cond := moreStored c.st) (body := do storedTrip c; pure false)
    valid post (fun _ H => stLen owner H) _ (show valid l h from ⟨s, state, buf, allowed, Or.inl rfl, rfl, rfl⟩)
  · rw [stLen_of state]; have := s.length.toNat_lt; unfold fuel; omega
  · intro regs H admitted'
    obtain ⟨s₁, state₁, buf₁, ok₁, fields₁, bits₁, hold₁⟩ := admitted'
    have read : rdS c.st (·.length) H = .ok (s₁.length, H) := by
      change rdS (some (.tab owner)) _ H = _
      simp [rdI_eq, state₁]
    refine ⟨regs, H, s₁.length != 0, by unfold moreStored; rw [runX_bind, runX_lift_ok read]; rfl, ?_, ?_⟩
    · intro more
      obtain ⟨result, regs', H', s', run, buf', ok', st', fields', bits', hold', progress, err⟩ :=
        trip_safe (strm := strm) cb state₁ buf₁ ok₁ (by simpa using more)
      cases result with
      | ok value =>
        cases value
        refine ⟨.ok false, regs', H', by rw [runX_bind, run]; rfl, ⟨s', st', buf', ok', fields₁.trans fields', bits'.trans bits₁, hold'.trans hold₁⟩, ?_⟩
        rw [stLen_of state₁, stLen_of st']; exact progress rfl
      | error e => exact ⟨.error e, regs', H', by rw [runX_bind, run], s', st', buf', ok', fields₁.trans fields', bits'.trans bits₁, hold'.trans hold₁, nofun, err⟩
    · intro done
      exact ⟨s₁, state₁, buf₁, ok₁, fields₁, bits₁, hold₁, fun _ => by simpa using done, fun _ eq => nomatch eq⟩

/-- The full stored-block case, from byte alignment and header refill to its next
mode. A malformed header publishes its error on the live stream. -/
theorem stored_safe {r : ZStreamRef} {s : InflateState} {l : IL} {h : Heap}
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (state : h.istates owner = some s) (buf : Buffers cell w off cap s l h) (allowed : admitted l.pointerLocals h) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    ∃ status regs H s', runX (back_STORED c) l h = .ok ((status, regs), H) ∧
      H.istates owner = some s' ∧ Buffers cell w off cap s' regs H ∧
      (status = .ok () → s'.mode = BAD ∨ s'.mode = TYPE ∧ s'.length = 0) ∧
      (∀ e, status = .error e → e = Ex.leave ∧ regs.ret = Z_BUF_ERROR) ∧
      s' = {s with mode := s'.mode, whave := s'.whave, length := s'.length} ∧
      (s'.whave = s.whave ∨ s'.whave = s.wsize) ∧
      (status = .ok () → s'.mode = TYPE → regs.bits = 0 ∧ regs.hold = 0) ∧
      ((∀ cs G t, admitted cs G → admitted cs (setI G owner t)) →
        (∀ cs G z msg, admitted cs G → r.get G = some z → admitted cs (r.put G {z with msg := msg})) →
        admitted regs.pointerLocals H) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  have start : Buffers cell w off cap s (bytebits l) h := {buf with}
  obtain ⟨status, regs, H, header, valid, ok, st, _, err⟩ :=
    needBits_safe (strm := some r) cb 32 (by decide) state start allowed
  change ∃ _ _ _ _, runX (back_STORED c) l h = _ ∧ _
  rw [back_STORED_loop, runX_bind, BYTEBITS_run]
  dsimp only
  rw [runX_bind, header]
  cases status with
  | error e => exact ⟨.error e, regs, H, s, rfl, st, valid, nofun, err, rfl, Or.inl rfl, nofun, fun _ _ => ok⟩
  | ok u =>
    cases u
    simp only [runX_bind, runX_get]
    by_cases invalid : ((regs.hold &&& (0xffff : UInt64)) != ((regs.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨z, hz⟩ := stream _ _ ok
      obtain ⟨k, bad⟩ := badMode_ctx_run c rfl rfl hz st _ lit_invalid_stored
      let marked := r.put H {z with msg := .ref (.str k) 0}
      let failed := {s with mode := BAD}
      have win : Window w off cap (setI marked owner failed) :=
        ⟨by simpa [marked, setI] using valid.window.storage, by simpa [marked, setI] using valid.window.writable⟩
      have span : InputRange w off cap (setI marked owner failed) regs.next regs.have_ := by
        simpa [InputRange, marked, setI] using valid.input
      exact ⟨.ok (), regs, setI marked owner failed, failed, by simp only [invalid, ↓reduceIte, runX_bind, runX_lift_ok bad]; rfl,
        upd_same .., {valid with window := win, input := span}, fun _ => Or.inl rfl, (fun _ eq => nomatch eq),
        rfl, Or.inl rfl, (fun _ impossible => False.elim ((by decide : BAD ≠ TYPE) impossible)),
        fun edit message => edit _ _ _ (message _ _ _ _ ok hz)⟩
    · let len := regs.hold.toUInt32 &&& 0xffff
      let saved := {s with length := len}
      let ready := setI H owner saved
      let reset := {regs with hold := 0, bits := 0}
      obtain ⟨a, storage, _⟩ := valid.window.storage
      have ok' := cb.copy regs.pointerLocals H a a s len ok st storage rfl (fun _ _ => rfl)
      rw [upd_self _ _ _ storage] at ok'
      have st' : ready.istates owner = some saved := upd_same ..
      have valid' : Buffers cell w off cap saved reset ready := {valid with window := ⟨valid.window.storage, valid.window.writable⟩}
      obtain ⟨res, loc, H', final, loop, last, kept, accepted, fields, bits, hold, success, fail⟩ :=
        storedLoop_safe (strm := some r) cb st' valid' ok'
      have write : wrS c.st (fun t => {t with length := regs.hold.toUInt32 &&& 0xffff}) H = .ok ((), ready) :=
        wrS_tab st _
      change runX (xwhile (moreStored c.st) (storedTrip c)) {regs with hold := 0, bits := 0} ready = .ok ((res, loc), H') at loop
      simp only [invalid, Bool.false_eq_true, ↓reduceIte, runX_bind, runX_lift_ok write, runX_INITBITS, loop]
      have frame : final = {s with mode := final.mode, whave := final.whave, length := final.length} := by
        rcases fields with eq | eq
        · have m : final.mode = s.mode := by have e := congrArg InflateState.mode eq; exact e
          have win : final.whave = s.whave := by have e := congrArg InflateState.whave eq; exact e
          rw [m, win]; exact eq
        · have m : final.mode = s.mode := by have e := congrArg InflateState.mode eq; exact e
          have win : final.whave = s.wsize := by have e := congrArg InflateState.whave eq; exact e
          rw [m, win]; exact eq
      have hist : final.whave = s.whave ∨ final.whave = s.wsize := by
        rcases fields with eq | eq <;> rw [eq]
        · exact Or.inl rfl
        · exact Or.inr rfl
      cases res with
      | error e => exact ⟨.error e, loc, H', final, rfl, last, kept, nofun, fail, frame, hist, nofun, fun _ _ => accepted⟩
      | ok u =>
        have typeMode : setMode c.st TYPE H' = .ok ((), setI H' owner {final with mode := TYPE}) := setMode_tab last TYPE
        exact ⟨.ok (), loc, setI H' owner {final with mode := TYPE}, {final with mode := TYPE}, runX_lift_ok typeMode loc, upd_same ..,
          {kept with window := ⟨kept.window.storage, kept.window.writable⟩},
          fun _ => Or.inr ⟨rfl, success rfl⟩, (fun _ eq => nomatch eq),
          congrArg (fun (v : InflateState) => {v with mode := TYPE}) frame, hist, fun _ _ => ⟨bits, hold⟩,
          fun edit _ => edit _ _ _ accepted⟩

end
#print axioms needBits_safe
#print axioms storedLoop_safe
#print axioms stored_safe
end Zlib.Infback.AddressedStored
