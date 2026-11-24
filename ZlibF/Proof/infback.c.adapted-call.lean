import ZlibF.Proof.«infback.c.addressed-call»
import ZlibF.Proof.«infback.c.callback-modes»
import ZlibF.Proof.«public-back-safety»

/-! Transfer the original finite-input return guarantee through the value callback adapters. -/
namespace Zlib.Infback.CallbackSimulation
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.AddressedTable
open ZlibF.Spec.Public
set_option autoImplicit false

private def valueFinish (c : BCtx) (l : IL) : M Int32 := do
  let s ← ldInflateState c.st
  let mut ret := l.ret
  if l.left < s.wsize then
    if (← c.outCb c.outDesc s.window (s.wsize - l.left)) != 0 && ret == Z_STREAM_END then ret := Z_BUF_ERROR
  wrZ c.strm fun z => {z with next_in := l.next,avail_in := l.have_}
  return ret

private theorem finish (c : BCtx) (cell : BPtrCell) {outer cs : PointerLocals} {l : IL} {h H : Heap} {rc : Int32}
    (ok : CursorOk cell outer cs) (run : valueFinish c l h = .ok (rc,H)) :
    ∃ after, CursorOk cell outer after ∧
      (finishBack c.strm c.st cell (adaptOutput c.outCb) c.outDesc {l with pointerLocals := cs}).run cs h =
        .ok ((rc,after),H) := by
  unfold valueFinish at run
  unfold finishBack
  rw [bind_app] at run
  rw [localBind,localLift]
  cases rd : ldInflateState c.st h with
  | error e => rw [rd] at run; cases run
  | ok pair =>
    obtain ⟨s,G⟩ := pair
    rw [rd] at run
    dsimp only at run ⊢
    by_cases part : l.left < s.wsize
    · let next := cs.assign cell l.next
      have published := lookup_assigned cs cell l.next ok.1
      cases output : c.outCb c.outDesc s.window (s.wsize - l.left) G with
      | error e => simp only [part,↓reduceIte,bind_app,output] at run; cases run
      | ok p =>
        obtain ⟨v,B⟩ := p
        have adaptedOut : (adaptOutput c.outCb c.outDesc s.window (s.wsize-l.left)).run next G = .ok ((v,next),B) := by
          change (liftM _ : PointerLocalM Int32).run next G = _
          rw [localLift,output]
        refine ⟨next,ok.assign l.next,?_⟩
        simp only [part,↓reduceIte,bind_app,output] at run
        simp only [part,↓reduceIte,localBind,callWithNext_run _ _ _ _ _ ok.1]
        erw [adaptedOut]
        dsimp only
        change next.live.lookup cell = some l.next at published
        rw [published]
        dsimp only
        split at run <;> rename_i branch <;>
          simp only [branch,Bool.false_eq_true,↓reduceIte,localBind,localLift,localPure] <;>
          cases write : wrZ c.strm (fun z => {z with next_in := l.next,avail_in := l.have_}) B with
          | error e => simp only [bind_app,write] at run; cases run
          | ok p => obtain ⟨_,T⟩ := p; simp only [bind_app,write,pure_app] at run; cases run; rfl
    · refine ⟨cs,ok,?_⟩
      simp only [part,↓reduceIte,bind_app] at run
      simp only [part,↓reduceIte,localBind,localLift,localPure]
      cases write : wrZ c.strm (fun z => {z with next_in := l.next,avail_in := l.have_}) G with
      | error e => rw [write] at run; cases run
      | ok p => obtain ⟨_,T⟩ := p; rw [write] at run; cases run; rfl

private theorem scope_releases {cs : PointerLocals} (next : BPtr) (fresh : cs.live.lookup ⟨cs.nextId⟩ = none) :
    (PointerLocals.mk (cs.nextId+1) ((⟨cs.nextId⟩,next)::cs.live)).release ⟨cs.nextId⟩ =
      {cs with nextId := cs.nextId+1} := by
  unfold PointerLocals.release
  congr 1
  simp only [List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply List.filter_eq_self.mpr
  intro e mem
  exact bne_iff_ne.mpr (Ne.symm (bne_iff_ne.mp (List.lookup_eq_none_iff.mp fresh e mem)))

private theorem body (c : BCtx) (init : IL) {cs : PointerLocals} {h H : Heap} {rc : Int32}
    (fresh : cs.live.lookup ⟨cs.nextId⟩ = none)
    (run : (do let (_,l) ← runX (xwhile (pure true) (back_dispatch c)) init; valueFinish c l) h = .ok (rc,H)) :
    (withBPtrCell init.next fun cell => do
      let regs ← runBackModesFrom init (back_dispatch (adapted cell c))
      finishBack c.strm c.st cell (adaptOutput c.outCb) c.outDesc regs).run cs h =
      .ok ((rc,{cs with nextId := cs.nextId+1}),H) := by
  let cell : BPtrCell := ⟨cs.nextId⟩
  let opened : PointerLocals := ⟨cs.nextId+1,(cell,init.next)::cs.live⟩
  let outer := {cs with nextId := cs.nextId+1}
  have live : CursorOk cell outer opened :=
    ⟨by simp [opened], scope_releases init.next fresh⟩
  rw [bind_app] at run
  cases value : runX (xwhile (pure true) (back_dispatch c)) init h with
  | error e => rw [value] at run; cases run
  | ok p =>
    obtain ⟨⟨status,l⟩,G⟩ := p
    rw [value] at run
    obtain ⟨middle,inScope,loop⟩ := simWhile (simPure _ true) (dispatch cell outer c) _ _ _ _ _ _ live value
    obtain ⟨after,final,exited⟩ := finish c cell inScope run
    rw [scope_run _ _ cs h fresh,localBind,modes_run]
    erw [loop]
    dsimp only
    rw [exited]
    exact congrArg (fun finalState => Except.ok ((rc,finalState),H)) final.2

private theorem valueEntry {r : ZStreamRef} {owner : Nat} {s : InflateState} {z : ZStream} {h : Heap}
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (st : h.istates owner = some s)
    (k : InflateStatePtr → BPtr → UInt32 → BPtr → UInt32 → M Int32) :
    (withBackStream (some r) Z_STREAM_ERROR k) h =
      (k (some (.tab owner)) z.next_in (if z.next_in != .null then z.avail_in else 0) s.window s.wsize)
        (setI (r.put h {z with msg := .null}) owner {s with mode := TYPE,last := 0,whave := 0}) := by
  let z' := {z with msg := .null}
  let s' := {s with mode := TYPE,last := 0,whave := 0}
  let h₁ := r.put h z'
  let entered := setI h₁ owner s'
  have atS : h₁.istates owner = some s := by simpa only [h₁,ZStreamRef.put_istates] using st
  have atZ : r.get entered = some z' := by rw [Zlib.Infback.Safety.rget_setI]; exact Zlib.Inflate.Proofs.ZStreamRef.get_put_same live _
  have clearMsg : wrZ (some r) (fun t => {t with msg := .null}) h = .ok ((),h₁) := by rw [wrZ_eq,live]
  have clearState : wrS (some (.tab owner)) (fun t => {t with mode := TYPE,last := 0,whave := 0}) h₁ = .ok ((),entered) :=
    wrS_tab atS _
  have sameLift {α : Type} (m : M α) : (liftM m : M α) = m := rfl
  conv => lhs; simp only [withBackStream,sameLift,reduceCtorEq,beq_iff_eq,↓reduceIte,bind_app,ldZ_eq,live,index,
    castInflateState_ok,clearMsg,clearState,atZ,ldInflateState_tab (show entered.istates owner = some s' from upd_same ..)]

/-- On every returning call on a live decoder, the ABI call with adapted
value callbacks gives the same status and heap. It preserves all outer cursor cells. -/
theorem adapted_of_ok {r : ZStreamRef} {owner : Nat} {z : ZStream} {s : InflateState} {h H : Heap} {rc : Int32}
    (live : r.get h = some z) (index : z.state = some (.inflate owner)) (st : h.istates owner = some s)
    (input : InCb) (i : BPtr) (output : OutCb) (o : BPtr) (cs : PointerLocals) (fresh : cs.live.lookup ⟨cs.nextId⟩ = none)
    (run : inflateBack (some r) input i output o h = .ok (rc,H)) :
    (inflateBack_c (some r) (adaptInput input) i (adaptOutput output) o).run cs h =
      .ok ((rc,{cs with nextId := cs.nextId+1}),H) := by
  unfold inflateBack at run
  rw [valueEntry live index st] at run
  unfold inflateBack_c
  rw [valid_entry live index st]
  let c : BCtx := ⟨some r,some (.tab owner),input,i,output,o⟩
  let n : UInt32 := if z.next_in != Ptr.null then z.avail_in else 0
  let init := {IL.init with next := z.next_in, have_ := n,put := s.window,left := s.wsize}
  exact body c init fresh run

/-- Every accepted call covered by the existing public callback protocol returns
through the address-taking ABI with all of that protocol's original guarantees. -/
theorem bounded_returns {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {z : ZStream} {s : InflateState} {input : InCb} {inDesc : BPtr} {output : OutCb} {outDesc : BPtr}
    (protocol : CallbackProtocol r i window n input inDesc output outDesc) (first : List UInt8)
    (history : BackSafeReachable h r i window n) (valid : BackValid h r i z s)
    (bytes : if z.next_in = .null then first = [] else Bytes h z.next_in z.avail_in.toNat first)
    (apart : Separate z.next_in first.length window n)
    (initial : protocol.invariant h {supplied := first,chunks := [],active := z.next_in,held := first})
    (bound : protocol.inputBound < 2 ^ 48) (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (platform : BackPlatform protocol) (chunk : BackFirstChunk z first)
    (cs : PointerLocals) (fresh : cs.live.lookup ⟨cs.nextId⟩ = none) :
    ∃ rc H z' s' log,
      (inflateBack_c (some r) (adaptInput input) inDesc (adaptOutput output) outDesc).run cs h =
        .ok ((rc,{cs with nextId := cs.nextId+1}),H) ∧
      BackValid H r i z' s' ∧ s'.window = window ∧ s'.wsize = s.wsize ∧ protocol.invariant H log ∧
      (rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR) ∧ CallbackFrame protocol.own h H r i window n ∧
      (∀ b, ¬ protocol.own b → (H.live b ↔ h.live b)) := by
  obtain ⟨rc,H,z',s',log,run,post⟩ := BackSafetyProof.inflateBack_safety.2.2 h r i window n z s input inDesc output outDesc
    protocol first history valid bytes apart initial bound fit platform chunk
  exact ⟨rc,H,z',s',log,adapted_of_ok valid.1 valid.2.2.1 valid.2.1 input inDesc output outDesc cs fresh run,post⟩

#print axioms bounded_returns
#print axioms adapted_of_ok
end Zlib.Infback.CallbackSimulation
