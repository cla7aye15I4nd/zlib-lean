import ZlibF.Proof.«infback.c.callback-simulation»

/-! The adapted callbacks can write this activation's cursor without changing
an outer pointer variable or the ordinary callback's heap effects. -/
namespace Zlib.Infback.CallbackSimulation
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback.Proofs
set_option autoImplicit false

def CursorOk (cell : BPtrCell) (outer cs : PointerLocals) : Prop :=
  (cs.live.lookup cell).isSome = true ∧ cs.release cell = outer

theorem CursorOk.assign {cell : BPtrCell} {outer cs : PointerLocals} (ok : CursorOk cell outer cs) (p : BPtr) :
    CursorOk cell outer (cs.assign cell p) :=
  ⟨by rw [lookup_assigned _ _ _ ok.1]; rfl, (release_assigned ..).trans ok.2⟩

abbrev adapted (cell : BPtrCell) (c : BCtx) : DecoderCtx :=
  addressedCtx c.strm c.st cell (adaptInput c.inCb) c.inDesc (adaptOutput c.outCb) c.outDesc

private theorem lift_local {α : Type} (m : M α) (cs : PointerLocals) (h : Heap) :
    (monadLift m : PointerLocalM α) cs h = match m h with
      | .ok (a,H) => .ok ((a,cs),H)
      | .error e => .error e := rfl

theorem inputCall (cell : BPtrCell) (outer : PointerLocals) (c : BCtx) (next : BPtr) :
    Sim (CursorOk cell outer) ((adapted cell c).input next) ((c : DecoderCtx).input next) := by
  intro l cs h res regs H ok run
  change runX (liftM (c.inCb c.inDesc next)) l h = _ at run
  rw [runX_lift] at run
  cases call : c.inCb c.inDesc next h with
  | error e => rw [call] at run; cases run
  | ok pair =>
    obtain ⟨⟨n,p⟩,G⟩ := pair
    rw [call] at run; cases run
    let saved := cs.assign cell next
    let after := saved.assign cell p
    have published := lookup_assigned cs cell next ok.1
    have valid := ok.assign next
    have updated := lookup_assigned saved cell p valid.1
    have cb : (adaptInput c.inCb c.inDesc cell).run saved h = .ok ((n,after),H) := by
      simp [adaptInput,BPtrCell.read,BPtrCell.write,StateT.run,bind,StateT.bind,liftM,lift_local,
        pure,StateT.pure,saved,published,call,after]
    refine ⟨after,valid.assign p,?_⟩
    change runX (inDecoder _) _ _ = _
    rw [runX_inDecoder,callWithNext_run cell next _ cs h ok.1,cb]
    dsimp only
    change after.live.lookup cell = some p at updated
    rw [updated]

theorem outputCall (cell : BPtrCell) (outer : PointerLocals) (c : BCtx) (buf : BPtr) (n : UInt32) :
    Sim (CursorOk cell outer) ((adapted cell c).output buf n) ((c : DecoderCtx).output buf n) := by
  intro l cs h res regs H ok run
  change runX (liftM (c.outCb c.outDesc buf n)) l h = _ at run
  rw [runX_lift] at run
  cases call : c.outCb c.outDesc buf n h with
  | error e => rw [call] at run; cases run
  | ok pair =>
    obtain ⟨rc,G⟩ := pair
    rw [call] at run; cases run
    let after := cs.assign cell l.next
    have published := lookup_assigned cs cell l.next ok.1
    have cb : (adaptOutput c.outCb c.outDesc buf n).run after h = .ok ((rc,after),H) := by
      simp [adaptOutput,liftM,StateT.run,lift_local,call]
    refine ⟨after,ok.assign l.next,?_⟩
    rw [addressedOutput_run _ _ _ _ _ _ _ _ _ _ _ ok.1,cb]
    dsimp only
    change after.live.lookup cell = some l.next at published
    rw [published]

end Zlib.Infback.CallbackSimulation
