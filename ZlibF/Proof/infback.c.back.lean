import ZlibF.Proof.«infback.c.end»
import ZlibF.Proof.«inflate.c.exit-codes»
import ZlibF.Proof.«inflate.c.main.table2»
import ZlibF.Zlib.«crc32.c»
import ZlibF.Zlib.«trees.c»

/-!
# inflateBack entry, refill and exit

The entry lemmas cover invalid streams and an empty first input. The ABI lemmas track
the address of the input cursor across refills, nested callbacks and the final writeback.
`addressedOrderAt_after_refill` establishes the code-length subscript bound when the
input callback preserves the decoder record and keeps the cursor live. The value-callback
protocol's whole-loop safety theorem is `inflate_back_sequence_safety` in `infback.c.safety-fast`.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem read_released_cursor (cell : BPtrCell) (cells : PointerLocals) (h : Heap) :
    cell.read.run (cells.release cell) h = .error (.ub "read of an expired pointer variable") := by
  have absent : (cells.release cell).live.lookup cell = none := by
    apply List.lookup_eq_none_iff.mpr
    intro p hp
    have ne : p.1 ≠ cell := by simpa using (List.mem_filter.mp hp).2
    simp [Ne.symm ne]
  simp [BPtrCell.read, StateT.run, absent]

theorem nested_cursors (initial outerValue innerValue : BPtr) (h : Heap) :
    ((withBPtrCell initial fun outer => do
        let inside ← withBPtrCell initial fun inner => do
          outer.write outerValue
          inner.write innerValue
          inner.read
        return (← outer.read, inside)).run {}) h =
      .ok (((outerValue, innerValue), { nextId := 2, live := [] }), h) := rfl

theorem inflateBack_c_nullstream (input : CInCb) (output : COutCb)
    (i o : BPtr) (cells : PointerLocals) (h : Heap) :
    (inflateBack_c none input i output o).run cells h =
      .ok ((Z_STREAM_ERROR, cells), h) := rfl

theorem lookup_assigned (cells : PointerLocals) (cell : BPtrCell) (p : BPtr)
    (live : (cells.live.lookup cell).isSome = true) :
    (cells.assign cell p).live.lookup cell = some p := by
  rcases cells with ⟨_, entries⟩
  change (entries.lookup cell).isSome = true at live
  unfold PointerLocals.assign
  induction entries with
  | nil => simp at live
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases e : key = cell
    · subst key; simp
    · simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm e)] at live
      simpa [List.lookup_cons, e, beq_eq_false_iff_ne.mpr (Ne.symm e)] using ih live

/-- An arbitrary C callback sees the current input pointer in the live local.
    A returning callback may change the heap and any live cursors. The decoder
    resumes with the pointer left in its own cell and preserves those changes. -/
theorem callWithNext_run (cell : BPtrCell) (next : BPtr) (callback : PointerLocalM α)
    (cells : PointerLocals) (h : Heap) (live : (cells.live.lookup cell).isSome = true) :
    (callWithNext cell next callback).run cells h =
      match callback.run (cells.assign cell next) h with
      | .error e => .error e
      | .ok ((value, afterCells), afterHeap) =>
        match afterCells.live.lookup cell with
        | none => .error (.ub "read of an expired pointer variable")
        | some cursor => .ok (((value, cursor), afterCells), afterHeap) := by
  cases ran : callback.run (cells.assign cell next) h with
  | error e =>
    simp [callWithNext, BPtrCell.write, StateT.run, bind, StateT.bind, live, StateT.run] at ran ⊢
    rw [ran]
  | ok pair =>
    obtain ⟨⟨value, afterCells⟩, afterHeap⟩ := pair
    cases cursor : afterCells.live.lookup cell <;>
      simp [callWithNext, BPtrCell.write, BPtrCell.read, StateT.run, bind, StateT.bind,
        pure, StateT.pure, live, StateT.run] at ran ⊢ <;> rw [ran] <;> simp [cursor]

/-- The direct C call starts with the same cursor in its addressed local.
    The result includes callback faults and all changes to other live variables. -/
theorem callWithNext_eq_direct (cell : BPtrCell) (next : BPtr) (callback : PointerLocalM α)
    (cells : PointerLocals) (h : Heap) (live : (cells.live.lookup cell).isSome = true) :
    (callWithNext cell next callback).run cells h =
      (do let value ← callback; return (value, ← cell.read) : PointerLocalM (α × BPtr)).run
        (cells.assign cell next) h := by
  simp [callWithNext, BPtrCell.write, StateT.run, bind, StateT.bind, live]

theorem release_assigned (cells : PointerLocals) (cell : BPtrCell) (next : BPtr) :
    (cells.assign cell next).release cell = cells.release cell := by
  cases cells with
  | mk nextId entries =>
    unfold PointerLocals.assign PointerLocals.release
    apply congrArg (PointerLocals.mk nextId)
    induction entries with
    | nil => rfl
    | cons e tail ih =>
      obtain ⟨key, value⟩ := e
      by_cases eq : key = cell <;> simpa [eq] using ih

theorem runX_inDecoder (action : PointerLocalM α) (l : IL) (h : Heap) :
    runX (inDecoder action) l h =
      match action.run l.pointerLocals h with
      | .error e => .error e
      | .ok ((v, cells), after) => .ok ((.ok v, { l with pointerLocals := cells }), after) := by
  unfold inDecoder
  simp only [runX_bind, runX_get, runX_lift, runX_set, runX_pure]
  cases run : action.run l.pointerLocals h with
  | error => rfl
  | ok p => obtain ⟨⟨_, _⟩, _⟩ := p; rfl

/-- The input refill in the ABI decoder, with the actual callback and the address
of the current invocation's cursor. A zero count clears the decoder cursor. -/
theorem addressedPull_run (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (input : CInCb) (desc : VoidPtr) (output : COutCb) (outDesc : VoidPtr) (l : IL) (h : Heap)
    (live : (l.pointerLocals.live.lookup cell).isSome = true) :
    runX (PULL (addressedCtx strm st cell input desc output outDesc)) l h =
      if l.have_ = 0 then
        match (input desc cell).run (l.pointerLocals.assign cell l.next) h with
        | .error e => .error e
        | .ok ((n, cells), after) =>
          match cells.live.lookup cell with
          | none => .error (.ub "read of an expired pointer variable")
          | some p =>
            if n = 0 then
              .ok ((.error Ex.leave, { l with pointerLocals := cells, have_ := n, next := .null, ret := Z_BUF_ERROR }), after)
            else
              .ok ((.ok (), { l with pointerLocals := cells, have_ := n, next := p }), after)
      else .ok ((.ok (), l), h) := by
  by_cases empty : l.have_ = 0
  · simp only [PULL, runX_bind, runX_get, empty, beq_self_eq_true, ↓reduceIte, addressedCtx, runX_inDecoder,
      callWithNext_run cell l.next _ l.pointerLocals h live]
    cases run : (input desc cell).run (l.pointerLocals.assign cell l.next) h with
    | error => rfl
    | ok p =>
      obtain ⟨⟨n, cells⟩, after⟩ := p
      simp only
      cases cursor : cells.live.lookup cell with
      | none => rfl
      | some p =>
        by_cases zero : n = 0 <;> simp [zero, runX_bind, runX_set, runX_throw, runX_pure]
  · simp [PULL, runX_bind, runX_get, runX_pure, empty]

/-- Direct input refill on a single addressed C local. The byte count and return
code live in the decoder registers, and the callback receives the cursor address. -/
def directPull (cell : BPtrCell) (input : CInCb) (desc : VoidPtr) (l : IL) :
    PointerLocalM (Except Ex Unit × IL) := do
  if l.have_ == 0 then
    let count ← input desc cell
    if count == 0 then
      cell.write .null
      return (.error Ex.leave, { l with have_ := 0, next := ← cell.read, ret := Z_BUF_ERROR })
    return (.ok (), { l with have_ := count, next := ← cell.read })
  return (.ok (), l)

/-- With a live automatic input pointer, PULL agrees with calling in(desc, &next)
directly. Compare the current cursor in the registers and every other pointer
variable separately; a nested call can change any of them. A returning callback
keeps the address of its caller's automatic variable live. -/
theorem addressedPull_eq_direct (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (input : CInCb) (desc : VoidPtr) (output : COutCb) (outDesc : VoidPtr) (l : IL) (h : Heap)
    (live : (l.pointerLocals.live.lookup cell).isSome = true)
    (returnsLive : ∀ count cells after,
      (input desc cell).run (l.pointerLocals.assign cell l.next) h = .ok ((count, cells), after) →
      (cells.live.lookup cell).isSome = true) :
    (runX (PULL (addressedCtx strm st cell input desc output outDesc)) l h).map
      (fun ((status, r), heap) => ((status, { r with pointerLocals := r.pointerLocals.release cell }), heap)) =
    ((directPull cell input desc l).run (l.pointerLocals.assign cell l.next) h).map
      (fun (((status, r), cells), heap) => ((status, { r with pointerLocals := cells.release cell }), heap)) := by
  rw [addressedPull_run strm st cell input desc output outDesc l h live]
  by_cases empty : l.have_ = 0
  · simp only [empty, ↓reduceIte]
    cases run : (input desc cell).run (l.pointerLocals.assign cell l.next) h with
    | error e =>
      simp [directPull, empty, bind, StateT.run, StateT.bind] at run ⊢
      rw [run]
      rfl
    | ok pair =>
      obtain ⟨⟨n, cells⟩, after⟩ := pair
      obtain ⟨p, cursor⟩ := Option.isSome_iff_exists.mp (returnsLive n cells after run)
      simp [directPull, empty, StateT.run, bind, StateT.bind, pure] at run ⊢
      rw [run]
      by_cases zero : n = 0
      · subst n
        have cleared := lookup_assigned cells cell .null (by simp [cursor])
        simp [StateT.bind, StateT.pure, bind, pure, BPtrCell.write, BPtrCell.read, cursor, cleared,
          release_assigned, Except.map]
      · simp [zero, StateT.bind, StateT.pure, bind, pure, BPtrCell.read, cursor, Except.map]
  · simp [directPull, empty, StateT.run, pure, StateT.pure, Except.map, release_assigned]

private theorem lift_local (m : M α) (s : PointerLocals) (h : Heap) :
    (monadLift m : PointerLocalM α) s h =
      match m h with | .ok (a, after) => .ok ((a, s), after) | .error e => .error e := rfl

/-- The three exit arms change only the return register before jumping to
    `inf_leave`. This holds for the ABI context with arbitrary callbacks. -/
theorem back_dispatch_exit (c : DecoderCtx) (l : IL) (h : Heap) (mode : UInt32)
    (read : rdS c.st (·.mode) h = .ok (mode, h))
    (notType : mode ≠ TYPE) (notStored : mode ≠ STORED)
    (notTable : mode ≠ TABLE) (notLen : mode ≠ LEN) :
    runX (back_dispatch c) l h = .ok ((.error Ex.leave, { l with ret :=
      if mode = DONE then Z_STREAM_END else if mode = BAD then Z_DATA_ERROR else Z_STREAM_ERROR }), h) := by
  have fetch := runX_lift_ok read l
  simp only [back_dispatch, runX_bind, fetch, beq_iff_eq, notType, notStored, notTable, notLen, ↓reduceIte]
  split
  · simp [runX_bind, runX_modify, runX_throw]
  · split <;> simp [runX_bind, runX_modify, runX_throw]

/-- Compare the actual ABI exit with the direct C operations on the addressed
    cursor. After its scope ends, both executions have the same result, heap
    and surviving locals, even if the last callback redirects the cursor. -/
theorem finishBack_eq_direct (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (output : COutCb) (outDesc : VoidPtr) (l : IL) (cells : PointerLocals) (h : Heap)
    (live : (cells.live.lookup cell).isSome = true) :
    ((finishBack strm st cell output outDesc l).run cells h).map
      (fun ((rc, locals), heap) => ((rc, locals.release cell), heap)) =
      ((do
          let s ← ldInflateState st
          let mut ret := l.ret
          if l.left < s.wsize then
            let rc ← output outDesc s.window (s.wsize - l.left)
            if rc != 0 && ret == Z_STREAM_END then ret := Z_BUF_ERROR
          let next ← cell.read
          wrZ strm fun z => { z with next_in := next, avail_in := l.have_ }
          return ret : PointerLocalM Int32).run (cells.assign cell l.next) h).map
        (fun ((rc, locals), heap) => ((rc, locals.release cell), heap)) := by
  have bindRun {α β : Type} (m : PointerLocalM α) (f : α → PointerLocalM β)
      (locals : PointerLocals) (heap : Heap) :
      (m >>= f).run locals heap =
        match m.run locals heap with
        | .error e => .error e
        | .ok ((a, locals'), heap') => (f a).run locals' heap' := by
    cases result : m.run locals heap with
    | error e => simp [StateT.run, bind, StateT.bind] at result ⊢; rw [result]
    | ok pair =>
      obtain ⟨⟨a, locals'⟩, heap'⟩ := pair
      simp [StateT.run, bind, StateT.bind] at result ⊢; rw [result]
  have liftRun {α : Type} (m : M α) (locals : PointerLocals) (heap : Heap) :
      (liftM m : PointerLocalM α).run locals heap =
        match m heap with | .ok (a, h') => .ok ((a, locals), h') | .error e => .error e :=
    lift_local m locals heap
  cases state : ldInflateState st h with
  | error e => simp only [finishBack, bindRun, liftRun, state]
  | ok pair =>
    obtain ⟨s, h₁⟩ := pair
    simp only [finishBack, bindRun, liftRun, state]
    by_cases pending : l.left < s.wsize
    · simp only [pending, ↓reduceIte, bindRun]
      rw [callWithNext_eq_direct cell l.next _ cells h₁ live]
      simp only [bindRun]
      cases result : (output outDesc s.window (s.wsize - l.left)).run (cells.assign cell l.next) h₁ with
      | error e => rfl
      | ok pair =>
        obtain ⟨⟨rc, after⟩, h₂⟩ := pair
        cases cursor : after.live.lookup cell <;>
          by_cases failed : (rc != 0 && l.ret == Z_STREAM_END) = true <;>
          simp [BPtrCell.read, bind, StateT.bind, StateT.run, pure, StateT.pure, cursor, failed]
    · have published := lookup_assigned cells cell l.next live
      simp only [pending, ↓reduceIte, bindRun, liftRun]
      cases written : wrZ strm (fun z => { z with next_in := l.next, avail_in := l.have_ }) h₁ with
      | error e => simp [BPtrCell.read, StateT.run, published, written, Except.map]
      | ok pair =>
        obtain ⟨_, after⟩ := pair
        simp [BPtrCell.read, StateT.run, pure, StateT.pure, published, written, Except.map, release_assigned]

/-- The ABI decoder's output hook reads the value left in the addressed input cursor,
including when the caller redirects it while writing output. -/
theorem addressedOutput_run (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (input : CInCb) (desc : VoidPtr) (output : COutCb) (outDesc buf : BPtr) (len : UInt32)
    (l : IL) (h : Heap) (live : (l.pointerLocals.live.lookup cell).isSome = true) :
    runX ((addressedCtx strm st cell input desc output outDesc).output buf len) l h =
      match (output outDesc buf len).run (l.pointerLocals.assign cell l.next) h with
      | .error e => .error e
      | .ok ((rc, cells), after) =>
        match cells.live.lookup cell with
        | none => .error (.ub "read of an expired pointer variable")
        | some cursor => .ok ((.ok rc, { l with next := cursor, pointerLocals := cells }), after) := by
  simp only [addressedCtx, runX_bind, runX_get, runX_inDecoder,
    callWithNext_run cell l.next _ l.pointerLocals h live]
  cases ran : (output outDesc buf len).run (l.pointerLocals.assign cell l.next) h with
  | error => rfl
  | ok pair =>
    obtain ⟨⟨value, cells⟩, after⟩ := pair
    simp only
    cases cursor : cells.live.lookup cell with
    | none => rfl
    | some ptr => rfl

/-- When the window is full, ROOM resets its output registers, publishes the
window size, and invokes the output callback with the current input cursor live. -/
theorem addressedRoom_run (strm : ZStreamPtr) (st : InflateStatePtr) (cell : BPtrCell)
    (input : CInCb) (desc : VoidPtr) (output : COutCb) (outDesc : BPtr) (l : IL) (h : Heap)
    (live : (l.pointerLocals.live.lookup cell).isSome = true) :
    runX (ROOM (addressedCtx strm st cell input desc output outDesc)) l h =
      (do
        if l.left != 0 then return ((.ok (), l), h)
        let (state, heap) ← ldInflateState st h
        let (_, ready) ← wrS st (fun s => { s with whave := state.wsize }) heap
        let ((rc, cells), after) ← (output outDesc state.window state.wsize).run
          (l.pointerLocals.assign cell l.next) ready
        let some next := cells.live.lookup cell | throw (.ub "read of an expired pointer variable")
        let regs := { l with next, put := state.window, left := state.wsize, pointerLocals := cells }
        if rc != 0 then return ((.error Ex.leave, { regs with ret := Z_BUF_ERROR }), after)
        return ((.ok (), regs), after)) := by
  have bindOK {α β : Type} (a : α) (k : α → Except Fault β) :
      (Except.ok a >>= k) = k a := rfl
  have bindErr {α β : Type} (e : Fault) (k : α → Except Fault β) :
      (Except.error e >>= k) = .error e := rfl
  by_cases full : l.left = 0
  · simp only [ROOM, runX_bind, runX_get, full, bne_self_eq_false, beq_self_eq_true, ↓reduceIte,
      runX_lift, Bool.false_eq_true,
      show (addressedCtx strm st cell input desc output outDesc).st = st from rfl]
    cases sread : ldInflateState st h with
    | error => rfl
    | ok pair =>
      obtain ⟨s, heap⟩ := pair
      have separate : wrS st (fun t => { t with whave := t.wsize }) heap =
          wrS st (fun t => { t with whave := s.wsize }) heap := by
        unfold wrS
        cases st with
        | none => rfl
        | some ref =>
          cases read : ref.get h with
          | none => simp [ldInflateState, read] at sread
          | some v =>
            simp [ldInflateState, read] at sread
            obtain ⟨rfl, rfl⟩ := sread
            simp [bind_app, ldInflateState, read]
      simp only [bindOK, runX_set]
      rw [separate]
      cases write : wrS st (fun t => { t with whave := s.wsize }) heap with
      | error => simp only [bindErr]
      | ok pair =>
        obtain ⟨_, ready⟩ := pair
        simp only [bindOK]
        rw [addressedOutput_run strm st cell input desc output outDesc s.window s.wsize
          { l with put := s.window, left := s.wsize } ready live]
        cases ran : (output outDesc s.window s.wsize).run (l.pointerLocals.assign cell l.next) ready with
        | error => rfl
        | ok pair =>
          obtain ⟨⟨rc, cells⟩, after⟩ := pair
          simp only [bindOK]
          cases cursor : cells.live.lookup cell with
          | none => rfl
          | some next =>
            by_cases ok : rc = 0 <;> simp [ok, runX_bind, runX_modify, runX_throw, runX_pure] <;> rfl
  · simp [ROOM, runX_bind, runX_get, full, runX_pure]; rfl

private theorem absorbInputByte_frame {l l' : IL} {h h' : Heap} {r : Except Ex Unit}
    (run : runX absorbInputByte l h = .ok ((r, l'), h')) :
    h' = h ∧ l'.pointerLocals = l.pointerLocals := by
  simp only [absorbInputByte, runX_bind, runX_get, runX_set, runX_lift] at run
  cases read : load8 l.next h with
  | error e => simp [read] at run
  | ok pair =>
    obtain ⟨byte, h1⟩ := pair
    have e : h1 = h := by
      change Ptr.load l.next h = _ at read
      unfold Ptr.load at read
      repeat' first | split at read | (cases read <;> rfl)
    subst h1
    simp only [read] at run
    cases advance : l.next.add 1 h with
    | error e => simp [advance] at run
    | ok pair =>
      obtain ⟨p, h2⟩ := pair
      have e : h2 = h := by
        unfold Ptr.add at advance
        repeat' first | split at advance | (cases advance <;> rfl)
      subst h2
      by_cases bound : l.bits < 64 <;> simp only [advance, shl64, bound, ↓reduceIte, pure_app, C.ub] at run <;> cases run
      exact ⟨rfl, rfl⟩

section
variable (strm : ZStreamPtr) (owner : Nat) (cell : BPtrCell)
    (input : CInCb) (desc : VoidPtr) (output : COutCb) (outDesc : VoidPtr)
    (preserves : ∀ (before : PointerLocals) (heap : Heap) n (cells : PointerLocals) (after : Heap),
      (before.live.lookup cell).isSome = true → (input desc cell).run before heap = .ok ((n, cells), after) →
      after.istates owner = heap.istates owner ∧ (cells.live.lookup cell).isSome = true)

include preserves

/-- Input may redirect this cursor, run another decoder or modify other objects.
Given a live cursor and a callback that preserves it and the selected decoder record,
each completed NEEDBITS preserves both, including early decoder exits. -/
theorem addressedNeedBits_frame
    (count : UInt32) (l : IL) (h : Heap) (live : (l.pointerLocals.live.lookup cell).isSome = true)
    {r : Except Ex Unit} {regs : IL} {after : Heap}
    (run : runX (Zlib.Infback.NEEDBITS (addressedCtx strm (some (.tab owner)) cell input desc output outDesc) count)
      l h = .ok ((r, regs), after)) :
    after.istates owner = h.istates owner ∧ (regs.pointerLocals.live.lookup cell).isSome = true := by
  let ctx := addressedCtx strm (some (.tab owner)) cell input desc output outDesc
  let I := fun (s : IL × Stop) (heap : Heap) =>
    heap.istates owner = h.istates owner ∧ (s.1.pointerLocals.live.lookup cell).isSome = true
  have refill (l1 : IL) (h1 : Heap) (ok : I (l1, .go) h1)
      (r1 : Except Ex Unit) (l2 : IL) (h2 : Heap)
      (step : runX (PULL ctx) l1 h1 = .ok ((r1, l2), h2)) : I (l2, .go) h2 := by
    rw [addressedPull_run _ _ _ _ _ _ _ _ _ ok.2] at step
    split at step
    · cases cb : (input desc cell).run (l1.pointerLocals.assign cell l1.next) h1 with
      | error e => simp [cb] at step
      | ok pair =>
        obtain ⟨⟨n, cells⟩, heap⟩ := pair
        have live' : ((l1.pointerLocals.assign cell l1.next).live.lookup cell).isSome = true := by
          rw [lookup_assigned _ _ _ ok.2]; rfl
        obtain ⟨same, holds⟩ := preserves _ _ _ _ _ live' cb
        cases cursor : cells.live.lookup cell with
        | none => simp [cursor] at holds
        | some p =>
          simp only [cb, cursor] at step
          split at step <;> cases step <;> exact ⟨same.trans ok.1, holds⟩
    · cases step; exact ok
  let cond : IL × Stop → M (Bool × (IL × Stop)) := fun (s : IL × Stop) => match s.2 with
    | .go => pure (decide (s.1.bits < count), (s.1, Stop.go)) | stop => pure (false, (s.1, stop))
  let body : IL × Stop → M (IL × Stop) := fun s => do
    let (res, loc) ← runX (do Zlib.Infback.PULLBYTE ctx; pure false : X Bool) s.1
    pure (match res with | .ok b => (loc, if b then Stop.brk else Stop.go) | .error e => (loc, Stop.ex e))
  have byteFrame (l1 : IL) (h1 : Heap) (ok : I (l1, .go) h1) (r1 : Except Ex Unit)
      (l2 : IL) (h2 : Heap) (byte : runX (Zlib.Infback.PULLBYTE ctx) l1 h1 = .ok ((r1, l2), h2)) :
      I (l2, .go) h2 := by
    unfold Zlib.Infback.PULLBYTE at byte
    rw [runX_bind] at byte
    cases step : runX (PULL ctx) l1 h1 with
    | error e => simp [step] at byte
    | ok pair =>
      obtain ⟨⟨res, middle⟩, mid⟩ := pair
      have ok2 := refill l1 h1 ok res middle mid step
      cases res with
      | error e => simp only [step] at byte; cases byte; exact ok2
      | ok u =>
        simp only [step] at byte
        obtain ⟨rfl, cells⟩ := absorbInputByte_frame byte
        exact ⟨ok2.1, cells ▸ ok2.2⟩
  have bodyInv : ∀ s h1 next h2, I s h1 → body s h1 = .ok (next, h2) → I next h2 := by
    intro ⟨l1, stop⟩ h1 next h2 ok executed
    change (do let (r1, l2) ← runX (do Zlib.Infback.PULLBYTE ctx; pure false : X Bool) l1
               pure (match r1 with | .ok b => (l2, if b then Stop.brk else Stop.go) | .error e => (l2, Stop.ex e))) h1 = _ at executed
    rw [bind_app, runX_bind] at executed
    cases step : runX (Zlib.Infback.PULLBYTE ctx) l1 h1 with
    | error e => simp [step] at executed
    | ok pair =>
      obtain ⟨⟨res, l2⟩, mid⟩ := pair
      have ok2 := byteFrame l1 h1 ok res l2 mid step
      cases res <;> simp only [step, runX_pure, pure_app] at executed <;> cases executed <;> exact ok2
  change (do let (loc, stop) ← cwhile cond body (l, Stop.go)
             pure (match stop with | .ex e => (Except.error e, loc) | _ => (Except.ok (), loc))) h = _ at run
  rw [bind_app] at run
  cases loop : cwhile cond body (l, Stop.go) h with
  | error e => simp [loop] at run
  | ok pair =>
    obtain ⟨⟨loc, stop⟩, last⟩ := pair
    have final := cwhile_success_invariant I (fun ⟨_, stop⟩ _ _ _ _ ok executed => by
      cases stop <;> cases executed <;> exact ok) bodyInv (show I (l, .go) h from ⟨rfl, live⟩) loop
    cases stop <;> simp only [loop, pure_app] at run <;> cases run <;> exact final

/-- At the code-length loop's subscript, the actual ABI refill leaves the same
decoder record. The loop guard and the header bound justify the direct C read. -/
theorem addressedOrderAt_after_refill {l regs : IL} {h after : Heap} {s : InflateState}
    (live : (l.pointerLocals.live.lookup cell).isSome = true) (state : h.istates owner = some s)
    (guard : s.«have» < s.ncode) (limit : s.ncode.toNat ≤ 19)
    (run : runX (Zlib.Infback.NEEDBITS (addressedCtx strm (some (.tab owner)) cell input desc output outDesc) 3)
      l h = .ok ((.ok (), regs), after)) :
    after.istates owner = some s ∧ s.«have».toNat < 19 ∧
      orderAt s.«have» after = .ok (order[s.«have».toNat]!, after) := by
  have frame := addressedNeedBits_frame strm owner cell input desc output outDesc preserves 3 l h live run
  have bound := Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp guard) limit
  exact ⟨frame.1.trans state, bound, orderAt_run after s.«have» bound⟩
end

/-- For every heap and live cursor, adapting an old input callback preserves its
    count, new input pointer, heap effects, and any fault. -/
theorem adaptInput_observations (cell : BPtrCell) (cells : PointerLocals) (h : Heap)
    (live : (cells.live.lookup cell).isSome = true) (input : InCb) (desc next : BPtr) :
    ((callWithNext cell next (adaptInput input desc cell)).run cells h).map
      (fun ((result, _), after) => (result, after)) = input desc next h := by
  have exposed := lookup_assigned cells cell next live
  cases ran : input desc next h with
  | error e => simp [callWithNext, adaptInput, StateT.run, BPtrCell.read, BPtrCell.write,
                     bind, StateT.bind, liftM, lift_local, Except.map, live, exposed, ran]
  | ok pair =>
    obtain ⟨⟨n, p⟩, after⟩ := pair
    have assigned := lookup_assigned (cells.assign cell next) cell p (by simp [exposed])
    simp [callWithNext, adaptInput, StateT.run, BPtrCell.read, BPtrCell.write, bind,
          StateT.bind, liftM, lift_local, pure, StateT.pure, Except.map, live, exposed, assigned, ran]

/-- The output adapter preserves the old callback result and heap and leaves
    the input cursor at the value published by the decoder. -/
theorem adaptOutput_observations (cell : BPtrCell) (cells : PointerLocals) (h : Heap)
    (live : (cells.live.lookup cell).isSome = true) (output : OutCb) (desc buf next : BPtr) (n : UInt32) :
    ((callWithNext cell next (adaptOutput output desc buf n)).run cells h).map
      (fun ((result, _), after) => (result, after)) =
    (output desc buf n h).map (fun (rc, after) => ((rc, next), after)) := by
  have exposed := lookup_assigned cells cell next live
  cases ran : output desc buf n h with
  | error e =>
    simp [callWithNext, adaptOutput, StateT.run, BPtrCell.write,
          bind, StateT.bind, liftM, lift_local, Except.map, live, ran]
  | ok pair =>
    obtain ⟨rc, after⟩ := pair
    simp [callWithNext, adaptOutput, StateT.run, BPtrCell.write, BPtrCell.read,
          bind, StateT.bind, liftM, lift_local, pure, StateT.pure, Except.map, live, exposed, ran]

/-! ### Running the monad `X` -/

theorem xrun_bind {α β : Type} (m : X α) (f : α → X β) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (m >>= f)) l h =
      match StateT.run (ExceptT.run m) l h with
      | .ok ((.ok a, l'), h') => StateT.run (ExceptT.run (f a)) l' h'
      | .ok ((.error e, l'), h') => .ok ((.error e, l'), h')
      | .error e => .error e := by
  cases hm : StateT.run (ExceptT.run m) l h with
  | error e => simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, ExceptT.run, ExceptT.mk, StateT.run] at hm ⊢; simp [hm]
  | ok p =>
    obtain ⟨⟨r, l'⟩, h'⟩ := p
    cases r <;> simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, ExceptT.run, ExceptT.mk, StateT.run,
      pure] at hm ⊢ <;> simp [hm, StateT.pure]

theorem xrun_get (l : IL) (h : Heap) : StateT.run (ExceptT.run (get : X IL)) l h = .ok ((.ok l, l), h) := rfl
theorem xrun_set (l l0 : IL) (h : Heap) : StateT.run (ExceptT.run (set l0 : X PUnit)) l h = .ok ((.ok ⟨⟩, l0), h) := rfl
theorem xrun_lift {α : Type} (m : M α) (l : IL) (h : Heap) :
    StateT.run (ExceptT.run (liftM m : X α)) l h =
      match m h with | .ok (a, h') => .ok ((.ok a, l), h') | .error e => .error e := by
  cases hm : m h <;> simp [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, StateT.lift, ExceptT.run, ExceptT.mk,
    StateT.run, bind, pure, Functor.map, StateT.map, hm]

theorem PULL_eof {c : BCtx} {l : IL} {h h3 : Heap} {nx : BPtr} (h0 : l.have_ = 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h3)) :
    StateT.run (ExceptT.run (PULL c)) l h =
      .ok ((Except.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h3) := by
  simp [PULL, xrun_bind, xrun_get, xrun_set, xrun_lift, hin, h0]

/-- A null stream: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBack_nullstream (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) (h : Heap) :
    inflateBack none inCb inDesc outCb outDesc h = .ok (Z_STREAM_ERROR, h) := by
  simp [inflateBack, withBackStream]

/-- No state: `Z_STREAM_ERROR`, nothing changes. -/
theorem inflateBack_nostate {h : Heap} {r : ZStreamRef} {z : ZStream} (hz : r.get h = some z) (hno : z.state = none)
    (inCb : InCb) (inDesc : BPtr) (outCb : OutCb) (outDesc : BPtr) :
    inflateBack (some r) inCb inDesc outCb outDesc h = .ok (Z_STREAM_ERROR, h) := by
  isimp [inflateBack, withBackStream, hz, hno]

end Zlib.Infback.Proofs
