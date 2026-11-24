import ZlibF.Proof.«infback.c.addressed-loop»

/-! The addressed callback decoder, including its automatic cursor and final output call. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored ZlibF.Spec.Public
set_option autoImplicit false

/-- The final call may request any positive prefix of the window. Like the
full-window call, it may replace the input cursor before the public writeback. -/
structure CallFrame (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef)
    (input : CInCb) (i : VoidPtr) (output : COutCb) (o : VoidPtr) (A : PointerLocals → Heap → Prop) : Prop
    extends Callbacks owner w off cap cell input i output o A where
  edit : ∀ cs H t, A cs H → A cs (setI H owner t)
  stream : ∀ cs H, A cs H → ∃ z, r.get H = some z ∧ z.state = some (.inflate owner)
  publishStream : ∀ cs H z next haveIn put left msg, r.get H = some z → A cs H →
    A cs (r.put H {z with next_in := next, avail_in := haveIn, next_out := put, avail_out := left, msg})
  globals : ∀ cs H, A cs H → LibraryGlobals H
  fit : ∀ cs H, A cs H → ZlibF.PlatformMemory.ByteObjectsFit H
  finalOutput : ∀ cs H s next haveIn used, A cs H → H.istates owner = some s →
    Window w off cap H → (cs.live.lookup cell).isSome = true → InputRange w off cap H next haveIn →
    0 < used.toNat → used.toNat ≤ cap →
    ∃ rc p after G, (output o (.ref (.blk w) off) used).run (cs.assign cell next) H = .ok ((rc,after),G) ∧
      after.live.lookup cell = some p ∧ A after G

theorem localBind {α β : Type} (m : PointerLocalM α) (f : α → PointerLocalM β) (cs : PointerLocals) (h : Heap) :
    (m >>= f).run cs h = match m.run cs h with
      | .error e => .error e
      | .ok ((a,after),H) => (f a).run after H := by
  cases run : m.run cs h with
  | error e => simp [StateT.run,bind,StateT.bind] at run ⊢; rw [run]
  | ok p => obtain ⟨⟨a,after⟩,H⟩ := p; simp [StateT.run,bind,StateT.bind] at run ⊢; rw [run]

theorem localLift {α : Type} (m : M α) (cs : PointerLocals) (h : Heap) :
    (liftM m : PointerLocalM α).run cs h = match m h with
      | .ok (a,H) => .ok ((a,cs),H)
      | .error e => .error e := rfl

theorem localPure {α : Type} (a : α) (cs : PointerLocals) (h : Heap) :
    (pure a : PointerLocalM α).run cs h = .ok ((a,cs),h) := rfl

def BackStatus (rc : Int32) : Prop := rc = Z_BUF_ERROR ∨ rc = Z_DATA_ERROR ∨ rc = Z_STREAM_END

section
variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
  {output : COutCb} {o : VoidPtr} {A : PointerLocals → Heap → Prop} {r : ZStreamRef}
  (frame : CallFrame owner w off cap cell r input i output o A)
include frame

/-- Finish with the cursor observed after the last callback and the decoder's
remaining count. A refusal replaces a successful end code with Z_BUF_ERROR. -/
theorem finish_safe {l : IL} {h : Heap} (exited : ExitPost owner w off cap cell r A l h) :
    ∃ rc cs H base z p, (finishBack (some r) (some (.tab owner)) cell output o l).run l.pointerLocals h =
        .ok ((rc,cs),H) ∧ BackStatus rc ∧ A cs H ∧ r.get base = some z ∧
        H = r.put base {z with next_in := p, avail_in := l.have_} := by
  obtain ⟨code,s,info⟩ := exited
  have allowed := info.frame.implies (B := A) (fun _ a => a) (frame.edit l.pointerLocals)
    (fun G z msg a atZ => frame.publishStream _ G z z.next_in z.avail_in z.next_out z.avail_out msg atZ a)
  have ld := ldInflateState_tab info.state
  have write {cs : PointerLocals} {G : Heap} (a : A cs G) (p : BPtr) :
      ∃ z, r.get G = some z ∧ wrZ (some r) (fun z => {z with next_in := p, avail_in := l.have_}) G =
        .ok ((), r.put G {z with next_in := p, avail_in := l.have_}) ∧
        A cs (r.put G {z with next_in := p, avail_in := l.have_}) := by
    obtain ⟨z,live,_⟩ := frame.stream _ _ a
    exact ⟨z, live, by rw [wrZ_eq,live], frame.publishStream _ _ _ p l.have_ z.next_out z.avail_out z.msg live a⟩
  unfold finishBack
  simp only [localBind,localLift,ld]
  by_cases pending : l.left < s.wsize
  · let used := s.wsize - l.left
    have left := UInt32.lt_iff_toNat_lt.mp pending
    have sub : used.toNat = s.wsize.toNat - l.left.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt pending)
    obtain ⟨result,p,cs,G,call,ptr,admit⟩ := frame.finalOutput l.pointerLocals h s l.next l.have_ used allowed
      info.state info.buffers.window info.buffers.live info.buffers.input (by omega) (by have := info.buffers.size; omega)
    rw [← info.buffers.address] at call
    obtain ⟨z,live,put,done_⟩ := write admit p
    let rc := if result != 0 && l.ret == Z_STREAM_END then Z_BUF_ERROR else l.ret
    refine ⟨rc,cs,_,G,z,p,?_,?_,done_,live,rfl⟩
    · simp only [pending,↓reduceIte,localBind,callWithNext_run _ _ _ _ _ info.buffers.live,call,ptr,rc,used]
      split <;> simp only [localBind,localLift,put,localPure]
    · unfold rc; split
      · exact Or.inl rfl
      · exact code
  · obtain ⟨z,live,put,done_⟩ := write allowed l.next
    exact ⟨l.ret,l.pointerLocals,_,h,z,l.next,by simp only [pending,↓reduceIte,localBind,localPure,localLift,put],
      code,done_,live,rfl⟩

omit frame in
theorem modes_run (init : IL) (body : X Unit) (cs : PointerLocals) (h : Heap) :
    (runBackModesFrom init body).run cs h =
      match runX (xwhile (pure true) body) {init with pointerLocals := cs} h with
      | .error e => .error e
      | .ok ((_,regs),H) => .ok ((regs,regs.pointerLocals),H) := by
  have getRun : (get : PointerLocalM PointerLocals).run cs h = .ok ((cs,cs),h) := rfl
  unfold runBackModesFrom
  simp only [localBind,getRun,localLift]
  cases eq : runX (xwhile (pure true) body) {init with pointerLocals := cs} h with
  | error e => unfold runX at eq; rw [eq]
  | ok p => obtain ⟨⟨_,regs⟩,H⟩ := p; unfold runX at eq; rw [eq]; rfl

/-- Run the switch and inf_leave on the same live automatic variable. -/
theorem modes_finish {init : IL} {cs : PointerLocals} {h : Heap}
    (start : AtSwitch owner w off cap cell r A {init with pointerLocals := cs} h) (size : cap ≤ 32768) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    let action : PointerLocalM Int32 := do
      let l ← runBackModesFrom init (back_dispatch c)
      finishBack (some r) (some (.tab owner)) cell output o l
    action.run cs h = .error .outOfFuel ∨ ∃ rc after H, action.run cs h = .ok ((rc,after),H) ∧ BackStatus rc ∧ A after H := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  rcases dispatch_loop frame.toCallbacks frame.edit frame.stream frame.publishStream frame.globals frame.fit size start
    with fuel | ⟨regs,G,loop,exited⟩
  · exact Or.inl (by rw [localBind,modes_run,fuel])
  · obtain ⟨rc,after,H,_,_,_,endRun,status,kept,_,_⟩ := finish_safe frame exited
    exact Or.inr ⟨rc,after,H,by rw [localBind,modes_run,loop]; exact endRun,status,kept⟩
end
theorem valid_entry {r : ZStreamRef} {owner : Nat} {s : InflateState} {z : ZStream} {h : Heap}
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (st : h.istates owner = some s)
    (cs : PointerLocals) (body : InflateStatePtr → BPtr → UInt32 → BPtr → UInt32 → PointerLocalM Int32) :
    (withBackStream (some r) Z_STREAM_ERROR body).run cs h =
      (body (some (.tab owner)) z.next_in (if z.next_in != .null then z.avail_in else 0) s.window s.wsize).run cs
        (setI (r.put h {z with msg := .null}) owner {s with mode := TYPE,last := 0,whave := 0}) := by
  let z' := {z with msg := .null}
  let s' := {s with mode := TYPE,last := 0,whave := 0}
  let h₁ := r.put h z'
  let entered := setI h₁ owner s'
  have read : ldZStream (some r) h = .ok (z,h) := by rw [ldZ_eq,live]
  have clearMsg : wrZ (some r) (fun t => {t with msg := .null}) h = .ok ((),h₁) := by rw [wrZ_eq,live]
  have atS : h₁.istates owner = some s := by simpa only [h₁,ZStreamRef.put_istates] using st
  have clearState : wrS (some (.tab owner)) (fun t => {t with mode := TYPE,last := 0,whave := 0}) h₁ = .ok ((),entered) :=
    wrS_tab atS _
  have atZ : r.get entered = some z' := by rw [rget_setI]; exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same live _
  have again : ldZStream (some r) entered = .ok (z',entered) := by rw [ldZ_eq,atZ]
  have reset : ldInflateState (some (.tab owner)) entered = .ok (s',entered) := ldInflateState_tab (upd_same ..)
  conv => lhs; simp only [withBackStream,reduceCtorEq,beq_iff_eq,↓reduceIte,localBind,localLift,read,index,
    castInflateState_ok,clearMsg,clearState,again,reset]

theorem scope_run {α : Type} (next : BPtr) (body : BPtrCell → PointerLocalM α) (cs : PointerLocals) (h : Heap)
    (fresh : cs.live.lookup ⟨cs.nextId⟩ = none) :
    let cell : BPtrCell := ⟨cs.nextId⟩
    let opened : PointerLocals := ⟨cs.nextId+1,(cell,next)::cs.live⟩
    (withBPtrCell next body).run cs h =
      ((body cell).run opened h).map (fun ((rc,after),H) => ((rc,after.release cell),H)) := by
  let cell : BPtrCell := ⟨cs.nextId⟩
  let opened : PointerLocals := ⟨cs.nextId+1,(cell,next)::cs.live⟩
  have getRun : (get : PointerLocalM PointerLocals).run cs h = .ok ((cs,cs),h) := rfl
  have setRun : (set opened : PointerLocalM PUnit).run cs h = .ok ((⟨⟩,opened),h) := rfl
  simp only [withBPtrCell,localBind,getRun,fresh,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  erw [setRun]
  dsimp only
  cases run : (body cell).run opened h with
  | error e => rfl
  | ok p => obtain ⟨⟨rc,after⟩,H⟩ := p; rfl

/-- A stream with a null state is refused before opening a cursor cell. -/
theorem null_state {r : ZStreamRef} {z : ZStream} {h : Heap} (stream : r.get h = some z) (empty : z.state = none)
    (input : CInCb) (i : VoidPtr) (output : COutCb) (o : VoidPtr) (cs : PointerLocals) :
    (inflateBack_c (some r) input i output o).run cs h = .ok ((Z_STREAM_ERROR,cs),h) := by
  have read : ldZStream (some r) h = .ok (z,h) := by rw [ldZ_eq,stream]
  simp only [inflateBack_c,withBackStream,beq_iff_eq,reduceCtorEq,↓reduceIte,localBind,localLift,read,empty,localPure]

/-- Whole accepted ABI call. The output callback may use the cursor address
saved by the input callback. On return only this activation's cell is released. -/
theorem addressed_call {owner w off cap : Nat} {r : ZStreamRef} {z : ZStream} {s : InflateState}
    {h : Heap} {cs : PointerLocals} {input : CInCb} {i : VoidPtr} {output : COutCb} {o : VoidPtr}
    {A : PointerLocals → Heap → Prop}
    (frame : CallFrame owner w off cap ⟨cs.nextId⟩ r input i output o A)
    (fresh : cs.live.lookup ⟨cs.nextId⟩ = none)
    (allowed : A ⟨cs.nextId+1,(⟨cs.nextId⟩,z.next_in)::cs.live⟩ h)
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (st : h.istates owner = some s)
    (wf : s.WellFormed) (sane : s.sane ≠ 0) (wnext : s.wnext = 0)
    (window : Window w off cap h) (addr : s.window = .ref (.blk w) off) (len : s.wsize.toNat = cap)
    (positive : 0 < cap) (limit : cap ≤ 32768)
    (chunk : InputRange w off cap h z.next_in (if z.next_in != .null then z.avail_in else 0)) :
    let run := (inflateBack_c (some r) input i output o).run cs h
    run = .error .outOfFuel ∨ ∃ rc after H, run = .ok ((rc,after.release ⟨cs.nextId⟩),H) ∧ BackStatus rc ∧ A after H := by
  let cell : BPtrCell := ⟨cs.nextId⟩
  let opened : PointerLocals := ⟨cs.nextId+1,(cell,z.next_in)::cs.live⟩
  let z' := {z with msg := .null}
  let t := {s with mode := TYPE,last := 0,whave := 0}
  let H := setI (r.put h z') owner t
  let n := if z.next_in != .null then z.avail_in else 0
  let init := {IL.init with next := z.next_in,have_ := n,put := s.window,left := s.wsize}
  let regs := {init with pointerLocals := opened}
  have ok : A opened H := frame.edit _ _ _ (frame.publishStream opened h z z.next_in z.avail_in z.next_out z.avail_out .null live allowed)
  have buf : Buffers cell w off cap t regs H := by
    refine ⟨?_,⟨?_,?_⟩,addr,len,positive,Nat.le_of_eq len,?_,?_⟩
    · simp [regs,opened]
    · simpa only [H,setI,ZStreamRef.put_bytes] using window.storage
    · simpa only [H,setI,ZStreamRef.put_ro] using window.writable
    · change s.window = .ref (.blk w) (off + (cap - s.wsize.toNat))
      simp [len,addr]
    · simpa only [InputRange,H,setI,ZStreamRef.put_bytes] using chunk
  have start : AtSwitch owner w off cap cell r A regs H := by
    refine ⟨t,upd_same ..,Or.inr ⟨buf,ok,by change (0 < 8 ∧ 0 < 2 ^ (0 : Nat)); decide,wf,⟨sane,wnext,Nat.zero_le _⟩,Or.inl rfl,?_⟩⟩
    intro impossible
    exact absurd impossible (by decide : TYPE ≠ LEN)
  have result := modes_finish (init := init) frame start limit
  unfold inflateBack_c
  rw [valid_entry live index st,scope_run _ _ cs _ fresh]
  rcases result with fuel | ⟨rc,after,G,call,status,kept⟩
  · exact Or.inl (by erw [fuel]; rfl)
  · exact Or.inr ⟨rc,after,G,by erw [call]; rfl,status,kept⟩

#print axioms addressed_call
#print axioms modes_finish
end Zlib.Infback.AddressedTable
