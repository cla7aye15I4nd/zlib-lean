import ZlibF.Proof.«infback.c.addressed-final-stored»

/-! The actual switch loop, including consecutive stored, fixed and dynamic blocks. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored Zlib.Infback.AddressedType ZlibF.Spec.Public
set_option autoImplicit false

/-- Premises needed again after returning to the top of the switch. -/
structure SwitchReady (owner w off cap : Nat) (cell : BPtrCell) (A : PointerLocals → Heap → Prop)
    (s : InflateState) (l : IL) (h : Heap) : Prop where
  buffer : Buffers cell w off cap s l h
  caller : A l.pointerLocals h
  bits : ReadyBits l
  wf : s.WellFormed
  state : StOk s
  mode : ModeOk owner s

/-- DONE and BAD no longer read the window or lookup tables. -/
def AtSwitch (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef) (A : PointerLocals → Heap → Prop)
    (l : IL) (h : Heap) : Prop := ∃ s, h.istates owner = some s ∧
  (((s.mode = DONE ∨ s.mode = BAD) ∧ AtExit owner w off cap cell r A s l h) ∨ SwitchReady owner w off cap cell A s l h)

def SwitchCode (l : IL) : Prop := l.ret = Z_BUF_ERROR ∨ l.ret = Z_DATA_ERROR ∨ l.ret = Z_STREAM_END

def ExitPost (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef) (A : PointerLocals → Heap → Prop)
    (regs : IL) (h : Heap) : Prop := SwitchCode regs ∧ ∃ t, AtExit owner w off cap cell r A t regs h

private def Step (inv post : IL → Heap → Prop) (run : Except Fault ((Except Ex Unit × IL) × Heap)) : Prop :=
  (∃ l h, run = .ok ((.error Ex.leave,l),h) ∧ post l h) ∨
  (∃ l h, run = .ok ((.ok (),l),h) ∧ inv l h)

private theorem run_loop (action : X Unit) (inv post : IL → Heap → Prop)
    (step : ∀ l h, inv l h →
      (∃ reg H, runX action l h = .ok ((.error Ex.leave,reg),H) ∧ post reg H) ∨
      (∃ reg H, runX action l h = .ok ((.ok (),reg),H) ∧ inv reg H))
    {l : IL} {h : Heap} (initial : inv l h) :
    runX (xwhile (pure true) action) l h = .error .outOfFuel ∨
      ∃ reg H, runX (xwhile (pure true) action) l h = .ok ((.error Ex.leave,reg),H) ∧ post reg H := by
  let cond : IL × Stop → M (Bool × (IL × Stop)) := fun (reg,s) =>
    match s with
    | .go => do
      let (status,r) ← runX (pure true : X Bool) reg
      pure (match status with
        | .ok b => (b,(r,Stop.go))
        | .error e => (false,(r,Stop.ex e)))
    | other => pure (false,(reg,other))
  let tick : IL × Stop → M (IL × Stop) := fun (reg,_) => do
    let (status,r) ← runX (do action; pure false : X Bool) reg
    pure (match status with
      | .ok b => (r, if b then Stop.brk else Stop.go)
      | .error e => (r,Stop.ex e))
  have advance (n reg H r G s) (body : tick (reg,.go) H = .ok ((r,s),G)) :
      cwhile.go cond tick (n+1) (reg,.go) H = cwhile.go cond tick n (r,s) G := by
    change (tick (reg,.go) >>= cwhile.go cond tick n) H = _
    exact bind_ok body
  have key : ∀ n reg H, inv reg H →
      cwhile.go cond tick n (reg,.go) H = .error .outOfFuel ∨
      ∃ reg' H', cwhile.go cond tick n (reg,.go) H = .ok ((reg',.ex Ex.leave),H') ∧ post reg' H' := by
    intro n
    induction n with
    | zero => exact fun _ _ _ => Or.inl rfl
    | succ n ih =>
      intro reg H admitted
      rcases step reg H admitted with ⟨r,G,run,done_⟩ | ⟨r,G,run,next⟩
      · have body : tick (reg,.go) H = .ok ((r,.ex Ex.leave),G) := by
          simp only [tick,bind_app,runX_bind,run]; rfl
        rw [advance n reg H r G (.ex Ex.leave) body]
        cases n with
        | zero => exact Or.inl rfl
        | succ m => exact Or.inr ⟨r,G,rfl,done_⟩
      · have body : tick (reg,.go) H = .ok ((r,.go),G) := by
          simp only [tick,bind_app,runX_bind,run,runX_pure]; rfl
        rw [advance n reg H r G .go body]
        exact ih r G next
  have expand : runX (xwhile (pure true) action) l h =
      match cwhile.go cond tick fuel (l,.go) h with
      | .error e => .error e
      | .ok ((reg,s),H) => .ok ((Stop.toE s,reg),H) := by
    unfold xwhile xwhileBrk runX
    simp only [ExceptT.run,StateT.run,ExceptT.mk,cwhile,bind_app]
    cases e : cwhile.go cond tick fuel (l,.go) h with
    | error fault => erw [e]
    | ok p => obtain ⟨⟨reg,s⟩,H⟩ := p; erw [e]; cases s <;> rfl
  rw [expand]
  rcases key fuel l h initial with empty | ⟨reg,H,run,done_⟩
  · exact Or.inl (by rw [empty])
  · exact Or.inr ⟨reg,H,by rw [run]; rfl,done_⟩

section
variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
  {output : COutCb} {o : VoidPtr} {A : PointerLocals → Heap → Prop} {r : ZStreamRef}
  (cb : Callbacks owner w off cap cell input i output o A)
  (edit : ∀ cs H t, A cs H → A cs (setI H owner t))
  (stream : ∀ cs H, A cs H → ∃ z, r.get H = some z ∧ z.state = some (.inflate owner))
  (publish : ∀ cs H z next haveIn put left msg, r.get H = some z → A cs H →
    A cs (r.put H {z with next_in := next, avail_in := haveIn, next_out := put, avail_out := left, msg}))
  (globals : ∀ cs H, A cs H → LibraryGlobals H)
  (fit : ∀ cs H, A cs H → ZlibF.PlatformMemory.ByteObjectsFit H)
  (size : cap ≤ 32768)
include cb edit stream publish globals fit size

private theorem stepLen {s : InflateState} {l : IL} {h : Heap} (st : h.istates owner = some s)
    (ready : SwitchReady owner w off cap cell A s l h) (mode : s.mode = LEN) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    Step (AtSwitch owner w off cap cell r A) (ExitPost owner w off cap cell r A) (runX (back_LEN c) l h) := by
  have live cs H (ok : A cs H) : ∃ z, r.get H = some z := by
    obtain ⟨z,rd,_⟩ := stream cs H ok
    exact ⟨z,rd⟩
  obtain ⟨z,rd,index⟩ := stream _ _ ready.caller
  have tabs := ready.mode.2 mode
  obtain ⟨v,regs,H,t,run,record,buffer,allowed,keep,out⟩ := len_round cb edit live publish globals rd index st
    ready.buffer ready.caller mode tabs (fit _ _ ready.caller) ready.state (ready.buffer.size ▸ size)
    ready.bits.1 ready.bits.2
  have kept := allowed (fun _ _ z msg adm atZ => publish _ _ _ z.next_in z.avail_in z.next_out z.avail_out msg atZ adm)
  cases v with
  | error e =>
    obtain ⟨rfl,ret⟩ := out
    exact Or.inl ⟨regs,H,run,Or.inl ret,t,record,buffer,.caller kept⟩
  | ok u =>
    cases u
    have mode' : ModeOk owner t := ⟨by
      rcases out.2 with m | m | m <;> simp [m], fun _ => keep.2.2.2 tabs⟩
    exact Or.inr ⟨regs,H,run,t,record,Or.inr ⟨buffer,kept,
      out.1,keep.2.2.1 ready.wf,keep.1 ready.state,mode'⟩⟩

private theorem switch_step {l : IL} {h : Heap} (inv : AtSwitch owner w off cap cell r A l h) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    Step (AtSwitch owner w off cap cell r A) (ExitPost owner w off cap cell r A) (runX (back_dispatch c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  obtain ⟨s,st,active⟩ := inv
  have fetch : rdS c.st (·.mode) h = .ok (s.mode,h) := by
    change rdS (some (.tab owner)) _ h = _
    simp only [rdI_eq,st]
  have exit (terminal : s.mode = DONE ∨ s.mode = BAD) (a : AtExit owner w off cap cell r A s l h) :
      Step (AtSwitch owner w off cap cell r A) (ExitPost owner w off cap cell r A) (runX (back_dispatch c) l h) := by
    rcases terminal with m | m <;> rw [m] at fetch
    · exact Or.inl ⟨_,_,back_dispatch_exit c l h DONE fetch (by decide) (by decide) (by decide) (by decide),
        Or.inr (Or.inr rfl),s,st,{a.buffers with},a.frame⟩
    · exact Or.inl ⟨_,_,back_dispatch_exit c l h BAD fetch (by decide) (by decide) (by decide) (by decide),
        Or.inr (Or.inl rfl),s,st,{a.buffers with},a.frame⟩
  rcases active with terminal | ready
  · exact exit terminal.1 terminal.2
  have live cs H (ok : A cs H) : ∃ z, r.get H = some z := by
    obtain ⟨z,rd,_⟩ := stream cs H ok
    exact ⟨z,rd⟩
  have msg cs H z msg (ok : A cs H) (atZ : r.get H = some z) : A cs (r.put H {z with msg}) :=
    publish _ _ _ z.next_in z.avail_in z.next_out z.avail_out msg atZ ok
  change Step _ _ (runX (back_dispatch c) l h)
  rcases ready.mode.1 with m | m | m | m | m | m
  · rw [back_dispatch,runX_bind,runX_lift_ok fetch,m]
    change Step _ _ (runX (back_TYPE c) l h)
    have ty := type_safe cb live st ready.buffer ready.caller
    split at ty
    · exact Or.inr ⟨_,_,ty,_,upd_same ..,Or.inl ⟨Or.inl rfl,upd_same ..,
        {ready.buffer with window := ⟨ready.buffer.window.storage,ready.buffer.window.writable⟩},.state (.caller ready.caller) _⟩⟩
    · rcases ty with ⟨regs,H,ret,run,access⟩ | ⟨regs,H,_,buffer,ok,_,bits,choice⟩
      · exact Or.inl ⟨_,_,run,Or.inl ret,s,access⟩
      let marked := {s with last := u2i (bitsV regs 1)}
      let kind := bitsV (dropR regs 1) 2
      let post := dropR (dropR regs 1) 2
      have bound : kind.toNat < 4 := bitsV_lt _ (by decide : (2 : UInt32).toNat < 32)
      have kinds : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by
        have : kind.toNat = 0 ∨ kind.toNat = 1 ∨ kind.toNat = 2 ∨ kind.toNat = 3 := by omega
        rcases this with k | k | k | k
        · exact Or.inl (UInt32.toNat_inj.mp k)
        · exact Or.inr (Or.inl (UInt32.toNat_inj.mp k))
        · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp k)))
        · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp k)))
      change if kind < 3 then runX (back_TYPE c) l h = .ok ((.ok (), post),setI H owner (selectMode marked kind)) else _ at choice
      have good (k : UInt32) (same : kind = k) (lt : k < 3)
          (window : (selectMode marked k).window = s.window) (len : (selectMode marked k).wsize = s.wsize)
          (wf : (selectMode marked k).WellFormed) (health : StOk (selectMode marked k))
          (mode : ModeOk owner (selectMode marked k)) : Step (AtSwitch owner w off cap cell r A) (ExitPost owner w off cap cell r A) (runX (back_TYPE c) l h) := by
        rw [same,ite_eq_left lt] at choice
        exact Or.inr ⟨_,_,choice,_,upd_same ..,Or.inr ⟨{buffer with
            window := ⟨buffer.window.storage,buffer.window.writable⟩
            address := window.trans buffer.address
            size := (congrArg UInt32.toNat len).trans buffer.size},
          edit _ _ _ ok,bits ready.bits.1 ready.bits.2,wf,health,mode⟩⟩
      rcases kinds with k | k | k | k
      · exact good 0 k (by decide) rfl rfl ready.wf ready.state (modeOk_of (Or.inl rfl))
      · exact good 1 k (by decide) rfl rfl ready.wf ready.state (modeOk_fixed owner marked)
      · exact good 2 k (by decide) rfl rfl ready.wf ready.state (modeOk_of (Or.inr (Or.inl rfl)))
      · rw [k,ite_eq_right (by decide : ¬(3 : UInt32) < 3)] at choice
        obtain ⟨z,key,alive,_,run⟩ := choice
        let msgPtr := Ptr.ref (BRef.str key) 0
        have pre : Buffers cell w off cap marked post (setI H owner marked) :=
          {buffer with window := ⟨buffer.window.storage,buffer.window.writable⟩}
        have wb := pre.putStream r {z with msg := msgPtr}
        change runX (back_TYPE c) l h = .ok ((.ok (),post),
          setI (r.put (setI H owner marked) {z with msg := msgPtr}) owner (selectMode marked kind)) at run
        rw [k] at run
        exact Or.inr ⟨_,_,run,_,upd_same ..,Or.inl ⟨Or.inr rfl,upd_same ..,
          {wb with window := ⟨wb.window.storage,wb.window.writable⟩},
          .state (.message (.state (.caller ok) marked) (by simpa using alive) _) _⟩⟩
  · rw [back_dispatch,runX_bind,runX_lift_ok fetch,m]
    change Step _ _ (runX (back_STORED c) l h)
    obtain ⟨v,regs,H,t,run,present,buffer,out,fail,shape,count,reset,frame⟩ := stored_safe cb live st ready.buffer ready.caller
    cases v with
    | error e =>
      obtain ⟨rfl,ret⟩ := fail e rfl
      exact Or.inl ⟨_,_,run,Or.inl ret,t,present,buffer,.caller (frame edit msg)⟩
    | ok u =>
      cases u
      refine Or.inr ⟨_,_,run,t,present,?_⟩
      rcases out rfl with bad | ⟨type,_⟩
      · exact Or.inl ⟨Or.inr bad,present,buffer,.caller (frame edit msg)⟩
      obtain ⟨bits,hold⟩ := reset rfl type
      refine Or.inr ⟨buffer,frame edit msg,by unfold ReadyBits; rw [bits,hold]; decide,?_,?_,?_⟩
      · rw [shape]; exact ready.wf
      · rw [shape]
        exact ⟨ready.state.1,ready.state.2.1,by
          rcases count with eq | eq
          · rw [eq]; exact ready.state.2.2
          · rw [eq]; exact Nat.le_refl _⟩
      · exact ⟨Or.inl type,fun eq => absurd (type.symm.trans eq) (by decide)⟩
  · rw [back_dispatch,runX_bind,runX_lift_ok fetch,m]
    change Step _ _ (runX (back_TABLE c) l h)
    rcases dynamic_safe cb (DynamicFrame.of_private live edit) st ready.buffer ready.caller m ready.wf with empty | bad | built
    · obtain ⟨regs,H,ret,run,t,access⟩ := empty
      exact Or.inl ⟨_,_,run,Or.inl ret,t,access⟩
    · obtain ⟨regs,H,t,record,target,run,access⟩ := bad
      exact Or.inr ⟨_,_,run,t,record,Or.inl ⟨Or.inr target,access⟩⟩
    · obtain ⟨regs,H,t,record,len,wf,tabs,buffer,ok,bits,⟨_,health⟩,cut⟩ := built
      rw [cut]
      exact stepLen cb edit stream publish globals fit size record
        ⟨buffer,ok,bits ready.bits,wf,health ready.state,
          ⟨Or.inr (Or.inr (Or.inr (Or.inl len))),fun _ => tabs⟩⟩ len
  · rw [back_dispatch,runX_bind,runX_lift_ok fetch,m]
    exact stepLen cb edit stream publish globals fit size st ready m
  · exact exit (Or.inl m) ⟨st,ready.buffer,.caller ready.caller⟩
  · exact exit (Or.inr m) ⟨st,ready.buffer,.caller ready.caller⟩

/-- Regardless of the number and kinds of blocks, the switch loop either
leaves with a documented status or exhausts the model's iteration budget. -/
theorem dispatch_loop {l : IL} {h : Heap} (initial : AtSwitch owner w off cap cell r A l h) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    let run := runX (xwhile (pure true) (back_dispatch c)) l h
    run = .error .outOfFuel ∨ ∃ regs H, run = .ok ((.error Ex.leave,regs),H) ∧ ExitPost owner w off cap cell r A regs H :=
  run_loop _ _ _
    (fun _ _ ready => switch_step cb edit stream publish globals fit size ready) initial
end
#print axioms dispatch_loop
end Zlib.Infback.AddressedTable
