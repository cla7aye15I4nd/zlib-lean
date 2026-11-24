import ZlibF.Proof.«infback.c.addressed-slow»
import ZlibF.Proof.«infback.c.safety-fast»
import ZlibF.Proof.«inffast.c.abi»

/-! The fast path of LEN uses the cursor currently held by the addressed
decoder, including an input range previously replaced by an output callback. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem fast_env_from_buffers {w off cap owner : Nat} {cell : BPtrCell} {r : ZStreamRef}
    {c : DecoderCtx} {z : ZStream} {s : InflateState} {h : Heap} {l : IL}
    (stream : c.strm = some r) (live : r.get h = some z) (index : z.state = some (.inflate owner))
    (buf : Buffers cell w off cap s l h) (mode : s.mode = LEN) (tabs : TablesOk owner s)
    (globals : LibraryGlobals h) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (state : StOk s) (winSize : s.wsize.toNat ≤ 32768)
    (short : l.bits.toNat < 8) (held : l.hold.toNat < 2 ^ l.bits.toNat)
    (fast : (l.have_ >= 6 && l.left >= 258) = true) :
    ∃ e : Zlib.Inffast.Proofs.EnvG true,
      e.h0 = setI (r.put h {z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_}) owner
        {s with hold := l.hold, bits := l.bits} ∧ e.strm = c.strm ∧ e.start = s.wsize ∧ e.r = r ∧ e.stid = owner ∧
      e.sm0 = {z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_} ∧
      e.s0 = {s with hold := l.hold, bits := l.bits} ∧ e.ob = .blk w ∧ e.o0 = off + (cap - l.left.toNat) ∧
      l.next = .ref e.ib e.i0 ∧ LenLeavesPositive e.LCA e.ol e.s0.lenbits.toNat := by
  have margins : 6 ≤ l.have_ ∧ 258 ≤ l.left := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have inputRoom : 6 ≤ l.have_.toNat := UInt32.le_iff_toNat_le.mp margins.1
  have outputRoom : 258 ≤ l.left.toNat := UInt32.le_iff_toNat_le.mp margins.2
  have nonzero : l.have_ ≠ 0 := fun eq => by rw [eq] at inputRoom; contradiction
  obtain ⟨b, pos, a, ptr, get, room, apart⟩ := buf.input nonzero
  obtain ⟨wa, wget, fits⟩ := buf.window.storage
  apply fast_range_env c stream live index mode tabs globals state winSize buf.address buf.size buf.left
    buf.put ptr get wget buf.window.writable room fits (fit (.blk b) a get) (fit (.blk w) wa wget)
    inputRoom outputRoom _ short held
  by_cases same : b = w
  · refine Or.inr ⟨same, ?_⟩
    have := buf.left
    rcases apart with n | low | high
    · exact absurd same n
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · exact Or.inl same

/-- RESTORE, the output bytes actually written, and the final public stream fields. -/
def FastWrites (r : ZStreamRef) (owner w off cap : Nat) (z : ZStream) (t : InflateState)
    (before after : Heap) (l regs : IL) : Prop :=
  ∃ (original written : Array UInt8) (msg : BPtr), before.bytes w = some original ∧
    written.size = original.size ∧ (∀ j, j < off ∨ off + cap ≤ j → written[j]? = original[j]?) ∧
    after = r.put (winHeap (setI (r.put before
      {z with next_in := l.next, avail_in := l.have_, next_out := l.put, avail_out := l.left}) owner t) w written)
      {z with next_in := regs.next, avail_in := regs.have_, next_out := regs.put, avail_out := regs.left, msg}

theorem FastWrites.admitted {w off cap owner : Nat} {cell : BPtrCell} {r : ZStreamRef}
    {input : CInCb} {i : VoidPtr} {output : COutCb} {o : VoidPtr}
    {A : PointerLocals → Heap → Prop}
    (cb : Callbacks owner w off cap cell input i output o A)
    (edit : ∀ cs H t, A cs H → A cs (setI H owner t))
    (publishStream : ∀ cs H z next haveIn put left msg, r.get H = some z → A cs H →
      A cs (r.put H {z with next_in := next, avail_in := haveIn, next_out := put, avail_out := left, msg}))
    {h after : Heap} {s t : InflateState} {z : ZStream} {l regs : IL}
    (writes : FastWrites r owner w off cap z t h after l regs)
    (get : h.istates owner = some s) (live : r.get h = some z)
    (ok : A l.pointerLocals h) (same : regs.pointerLocals = l.pointerLocals) : A regs.pointerLocals after := by
  obtain ⟨before, written, msg, data, size, frame, heap⟩ := writes
  let restored := {z with next_in := l.next, avail_in := l.have_, next_out := l.put, avail_out := l.left}
  let H := r.put h restored
  have first : A l.pointerLocals H := publishStream _ _ _ _ _ _ _ z.msg live ok
  have updated := cb.copy _ H before written s s.length first
    (by simpa only [H, ZStreamRef.put_istates] using get)
    (by simpa only [H, ZStreamRef.put_bytes] using data) size frame
  have stored := edit _ _ t updated
  rw [setI_setI] at stored
  have current : r.get (winHeap (setI H owner t) w written) = some restored := by
    rw [rget_winHeap, rget_setI]
    exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same live restored
  rw [heap, same]
  exact publishStream _ _ restored regs.next regs.have_ regs.put regs.left msg current stored

/-- RESTORE publishes the current registers before the fast call. LOAD
takes its counters and bits from that same call's resulting heap and keeps
the caller's live pointer-cell table. -/
theorem fast_case {w off cap owner : Nat} {cell : BPtrCell} {r : ZStreamRef}
    {c : DecoderCtx} {z : ZStream} {s : InflateState} {h : Heap} {l : IL}
    (stream : c.strm = some r) (decoder : c.st = some (.tab owner))
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (get : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (mode : s.mode = LEN) (tabs : TablesOk owner s)
    (globals : LibraryGlobals h) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (state : StOk s) (winSize : s.wsize.toNat ≤ 32768)
    (short : l.bits.toNat < 8) (held : l.hold.toNat < 2 ^ l.bits.toNat)
    (fast : (l.have_ >= 6 && l.left >= 258) = true) :
    ∃ regs after t, runX (back_LEN c) l h = .ok ((.ok (), regs), after) ∧
      after.istates owner = some t ∧ regs.pointerLocals = l.pointerLocals ∧ regs.bits.toNat < 8 ∧
      regs.hold.toNat < 2 ^ regs.bits.toNat ∧ (t.mode = LEN ∨ t.mode = TYPE ∨ t.mode = BAD) ∧
      Buffers cell w off cap t regs after ∧
      t = {s with mode := t.mode, bits := regs.bits, hold := regs.hold} ∧
      FastWrites r owner w off cap z t h after l regs ∧
      ∃ e : Zlib.Inffast.Proofs.EnvG true, e.strm = c.strm ∧ e.start = s.wsize ∧
        e.h0 = setI (r.put h {z with next_out := l.put, avail_out := l.left, next_in := l.next, avail_in := l.have_}) owner
          {s with hold := l.hold, bits := l.bits} ∧
        Zlib.Inffast.inflate_fast c.strm s.wsize e.h0 = .ok ((), after) ∧
        C.run (Zlib.Inffast.inflate_fast_c c.strm s.wsize) e.h0 = .ok ((), after) ∧ FastPost e after := by
  obtain ⟨e, entered, es, start, er, ei, ez, et, ob, origin, cursor, pos⟩ :=
    fast_env_from_buffers stream live index buf mode tabs globals fit state winSize short held fast
  obtain ⟨after, call, post, _, _⟩ := Zlib.Inffast.Proofs.fast_consumes e pos
  have execute : Zlib.Inffast.inflate_fast c.strm s.wsize e.h0 = .ok ((), after) := es ▸ start ▸ call
  have restore : runX (RESTORE c.strm c.st) l h = .ok ((.ok (), l), e.h0) := by
    rw [entered]; exact RESTORE_back_run stream decoder live get l
  have present : e.h0.istates owner = some e.s0 := ei ▸ e.hs0
  have ws : rdS c.st (·.wsize) e.h0 = .ok (s.wsize, e.h0) := by
    rw [decoder, rdI_eq, present, et]
  have result := post
  obtain ⟨used, made, saved, bytes, msg, m, bits, hold, usedLe, _, madeLe, sameSize, low, clean, heap, frame, cls, _⟩ := post
  let t := {e.s0 with mode := m, bits, hold}
  let z' := {e.sm0 with
    next_in := .ref e.ib (e.i0 + used)
    next_out := .ref e.ob (e.o0 + made)
    avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - used)
    avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - made)
    msg := msg}
  let H := winHeap (setI e.h0 owner t) w bytes
  have hi : after = r.put H z' := by dsimp only [z']; rw [heap, er, ei, ob]; rfl
  have hz : r.get H = some e.sm0 := by
    rw [show r.get H = r.get e.h0 by unfold H; rw [rget_winHeap, rget_setI]]
    exact er ▸ e.hsm
  have zAfter : r.get after = some z' := hi ▸ Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz z'
  have tAfter : after.istates owner = some t := by rw [hi, ZStreamRef.put_istates]; exact upd_same ..
  have load := LOAD_back_run stream decoder zAfter tAfter l
  let regs := {l with
    next := z'.next_in
    put := z'.next_out
    have_ := z'.avail_in
    left := z'.avail_out
    hold := t.hold
    bits := t.bits}
  have windowAt : h.bytes w = some e.A0 := by
    have before := e.hA0
    rw [entered, ob] at before
    change (r.put h _).bytes w = some e.A0 at before
    simpa only [ZStreamRef.put_bytes] using before
  refine ⟨regs, after, t, ?_, tAfter, rfl, low, clean, ?_, ?_, ?_, ?_, e, es, start, entered, execute, ?_, ?_⟩
  · rw [back_LEN_eq']
    simp only [runX_bind, runX_get, fast, ↓reduceIte, restore, runX_lift_ok ws, runX_lift_ok execute, load, runX_pure, regs]
  · rcases cls with ⟨same, _⟩ | ⟨type, _⟩ | bad
    · exact Or.inl (same.trans (et ▸ mode))
    · exact Or.inr (Or.inl type)
    · exact Or.inr (Or.inr bad)
  · have inCount : e.sm0.avail_in = l.have_ := by rw [ez]
    have outCount : e.sm0.avail_out = l.left := by rw [ez]
    rw [inCount] at usedLe
    rw [outCount] at madeLe
    have remIn : regs.have_.toNat = l.have_.toNat - used := by
      change (UInt32.ofNat (e.sm0.avail_in.toNat - used)).toNat = _
      rw [inCount]; exact UInt32.toNat_ofNat_of_lt' (by have := l.have_.toNat_lt; unfold UInt32.size; omega)
    have remOut : regs.left.toNat = l.left.toNat - made := by
      change (UInt32.ofNat (e.sm0.avail_out.toNat - made)).toNat = _
      rw [outCount]; exact UInt32.toNat_ofNat_of_lt' (by have := l.left.toNat_lt; unfold UInt32.size; omega)
    have outBytes : after.bytes = upd h.bytes w (some bytes) := by
      simp only [hi, ZStreamRef.put_bytes, H, winHeap, setI, entered]
    have writeable : after.ro w = false := by
      simpa only [hi, ZStreamRef.put_ro, H, winHeap, setI, entered] using buf.window.writable
    obtain ⟨a, wa, room⟩ := buf.window.storage
    cases Option.some.inj (windowAt.symm.trans wa)
    have capRoom := buf.left
    refine ⟨buf.live, ⟨⟨bytes, by rw [outBytes]; exact upd_same .., by omega⟩, writeable⟩,
      ?_, ?_, buf.positive, by omega, ?_, ?_⟩
    · change e.s0.window = _; rw [et]; exact buf.address
    · change e.s0.wsize.toNat = _; rw [et]; exact buf.size
    · change Ptr.ref e.ob (e.o0 + made) = _
      rw [ob, origin, remOut]; congr 1; omega
    · intro nonzero
      have before : l.have_ ≠ 0 := fun zero => by
        have nz : regs.have_.toNat ≠ 0 := fun e => nonzero (UInt32.toNat_inj.mp e)
        rw [zero] at remIn; simp_all
      obtain ⟨b, first, src, ptr, data, fits, apart⟩ := buf.input before
      have same := Ptr.ref.inj (cursor.symm.trans ptr)
      have now : regs.next = .ref (.blk b) (first + used) := by
        change Ptr.ref e.ib (e.i0 + used) = _; rw [same.1,same.2]
      have dis : b ≠ w ∨ first + used + regs.have_.toNat ≤ off ∨ off + cap ≤ first + used := by omega
      by_cases eq : b = w
      · subst b
        cases Option.some.inj (windowAt.symm.trans data)
        exact ⟨w, first+used, bytes, now, by rw [outBytes]; exact upd_same .., by omega, dis⟩
      · exact ⟨b, first+used, src, now, by rw [outBytes]; exact (upd_ne _ _ _ _ eq).trans data, by omega, dis⟩
  · dsimp only [t, regs]; rw [et]
  · refine ⟨e.A0, bytes, msg, windowAt, sameSize, ?_, ?_⟩
    · intro j outside
      apply frame j
      have := buf.left
      rw [ez] at madeLe
      change made ≤ l.left.toNat at madeLe
      simp only [origin, ↓reduceIte]
      omega
    · simp only [hi, H, entered, setI_setI, regs, z', ez]
  · exact ZlibF.Proof.StandaloneCAbi.inflate_fast_c_of_ok c.strm s.wsize execute
  · exact result

/-- One dispatch of the literal/length mode with an address-retaining input
callback. The number of available input and output bytes selects the path. -/
theorem len_case {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (globals : ∀ cs H, admitted cs H → LibraryGlobals H)
    {s : InflateState} {l : IL} {h : Heap} {z : ZStream}
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (get : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (ok : admitted l.pointerLocals h)
    (mode : s.mode = LEN) (tabs : TablesOk owner s) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (state : StOk s) (winSize : s.wsize.toNat ≤ 32768)
    (short : l.bits.toNat < 8) (held : l.hold.toNat < 2 ^ l.bits.toNat) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenResult owner (runX (back_LEN c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  cases guard : l.have_ >= 6 && l.left >= 258 with
  | false => exact slow_case cb edit stream globals get mode tabs buf ok short held guard
  | true =>
    obtain ⟨regs, H, t, run, present, _, _, _, target, _⟩ :=
      fast_case (c := c) rfl rfl live index get buf mode tabs (globals _ _ ok) fit state winSize short held guard
    exact Or.inr ⟨regs, H, t, run, present, target⟩

/-- A complete LEN switch preserves the frame, buffer ranges, decoder state and
the clean bit accumulator needed by its successor. -/
theorem len_round {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
    {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
    (cb : Callbacks owner w off cap cell input i output o admitted)
    (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
    (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
    (publishStream : ∀ cs H z next haveIn put left msg, r.get H = some z → admitted cs H →
      admitted cs (r.put H {z with next_in := next, avail_in := haveIn, next_out := put, avail_out := left, msg}))
    (globals : ∀ cs H, admitted cs H → LibraryGlobals H)
    {s : InflateState} {l : IL} {h : Heap} {z : ZStream}
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (get : h.istates owner = some s)
    (buf : Buffers cell w off cap s l h) (ok : admitted l.pointerLocals h)
    (mode : s.mode = LEN) (tabs : TablesOk owner s) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (state : StOk s) (winSize : s.wsize.toNat ≤ 32768)
    (short : l.bits.toNat < 8) (held : l.hold.toNat < 2 ^ l.bits.toNat) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenRound owner w off cap cell r admitted s (runX (back_LEN c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  cases guard : l.have_ >= 6 && l.left >= 258 with
  | false => exact slow_round cb edit stream globals get mode tabs buf ok short held guard
  | true =>
    obtain ⟨regs, H, t, run, present, same, low, clean, target, valid, shape, writes, _⟩ :=
      fast_case (c := c) rfl rfl live index get buf mode tabs (globals _ _ ok) fit state winSize short held guard
    exact ⟨_,regs,H,t,run,present,valid,fun _ => writes.admitted cb edit publishStream get live ok same,
      by rw [show t = _ from shape]; exact LenState.same owner s, ⟨low,clean⟩,target⟩

#print axioms len_round
#print axioms len_case
#print axioms fast_case
end Zlib.Infback.AddressedTable
