import ZlibF.Proof.«infback.c.callback-adapters»

/-! All modes of the ABI decoder simulate value callbacks through their adapters. -/
namespace Zlib.Infback.CallbackSimulation
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback.Proofs
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem adaptedSt (cell : BPtrCell) (c : BCtx) : (adapted cell c).st = c.st := rfl
private theorem adaptedStream (cell : BPtrCell) (c : BCtx) : (adapted cell c).strm = c.strm := rfl

macro "callback_sim_with " known:tactic : tactic =>
  `(tactic| repeat' first
    | ($known:tactic)
    | with_reducible assumption
    | rw [adaptedSt]
    | rw [adaptedStream]
    | with_reducible exact inputCall _ _ _ _
    | with_reducible exact outputCall _ _ _ _ _
    | with_reducible exact simPure _ _
    | with_reducible exact simLift _ _
    | with_reducible exact simThrow _ _
    | with_reducible exact simSet _ _ rfl (by assumption)
    | with_reducible refine simModify _ _ (fun _ _ _ => rfl)
    | with_reducible refine simGetBind (fun _ _ _ => ?_)
    | with_reducible apply simDoWhile
    | with_reducible apply simWhile
    | with_reducible apply simLoopBrk
    | with_reducible apply simWhileBrk
    | with_reducible apply simIf
    | with_reducible refine simBind ?_ (fun _ => ?_)
    | rfl
    | split)

macro "callback_sim" : tactic => `(tactic| callback_sim_with fail)

private theorem bits (P : PointerLocals → Prop) (n : UInt32) : Sim P (BITS n) (BITS n) := by
  unfold BITS
  callback_sim

private theorem drop (P : PointerLocals → Prop) (n : UInt32) : Sim P (DROPBITS n) (DROPBITS n) := by
  unfold DROPBITS
  callback_sim

private theorem byte (P : PointerLocals → Prop) : Sim P BYTEBITS BYTEBITS := by
  unfold BYTEBITS
  callback_sim

private theorem restore (P : PointerLocals → Prop) (strm : ZStreamPtr) (st : InflateStatePtr) :
    Sim P (RESTORE strm st) (RESTORE strm st) := by
  unfold RESTORE
  callback_sim

private theorem load (P : PointerLocals → Prop) (strm : ZStreamPtr) (st : InflateStatePtr) :
    Sim P (LOAD strm st) (LOAD strm st) := by
  unfold LOAD
  callback_sim

private theorem ordered {P : PointerLocals → Prop} (st : InflateStatePtr) {a b : X UInt16} (value : Sim P a b) :
    Sim P (Zlib.Inflate.storeOrderedLength st a) (Zlib.Inflate.storeOrderedLength st b) := by
  unfold Zlib.Inflate.storeOrderedLength Zlib.Inflate.withLengthOrder
  callback_sim

section
variable (cell : BPtrCell) (outer : PointerLocals) (c : BCtx)
local notation "a" => adapted cell c
local notation "v" => (c : DecoderCtx)
local notation "P" => CursorOk cell outer

private theorem pull : Sim P (Zlib.Infback.PULL a) (Zlib.Infback.PULL v) := by
  unfold Zlib.Infback.PULL
  callback_sim

private theorem room : Sim P (Zlib.Infback.ROOM a) (Zlib.Infback.ROOM v) := by
  unfold Zlib.Infback.ROOM
  callback_sim

private theorem pullByte : Sim P (Zlib.Infback.PULLBYTE a) (Zlib.Infback.PULLBYTE v) := by
  unfold Zlib.Infback.PULLBYTE
  refine simBind (pull cell outer c) (fun _ => ?_)
  unfold absorbInputByte
  callback_sim

private theorem need (n : UInt32) : Sim P (Zlib.Infback.NEEDBITS a n) (Zlib.Infback.NEEDBITS v n) := by
  unfold Zlib.Infback.NEEDBITS
  refine simWhile ?_ (pullByte cell outer c)
  callback_sim

private theorem needField : Sim P (needExtra a) (needExtra v) := by
  unfold needExtra
  refine simWhile ?_ (pullByte cell outer c)
  callback_sim

private theorem root (dist : Bool) : Sim P (Zlib.Infback.lookup1 a dist) (Zlib.Infback.lookup1 v dist) := by
  have refill := pullByte cell outer c
  unfold Zlib.Infback.lookup1 lookupRoot
  callback_sim
  all_goals exact bits P _

private theorem link (dist : Bool) : Sim P (Zlib.Infback.lookup2 a dist) (Zlib.Infback.lookup2 v dist) := by
  have refill := pullByte cell outer c
  unfold Zlib.Infback.lookup2 lookupLink
  callback_sim
  all_goals exact bits P _

private theorem extra (dist : Bool) : Sim P (extendExtra a dist) (extendExtra v dist) := by
  have field := needField cell outer c
  unfold extendExtra
  callback_sim
  all_goals first | exact bits P _ | exact drop P _

private theorem copyMatch : Sim P (backMatch a) (backMatch v) := by
  have flush := room cell outer c
  unfold backMatch copyMatchBytes
  callback_sim

private theorem literal (st : InflateStatePtr) : Sim P (emitLiteral st) (emitLiteral st) := by
  unfold emitLiteral
  callback_sim

private theorem bad (msg : String) : Sim P (liftM (Zlib.Infback.badMode a msg)) (liftM (Zlib.Infback.badMode v msg)) :=
  simLift _ _

macro "mode_sim" : tactic =>
  `(tactic| callback_sim_with
    (first
    | with_reducible exact bad _ _ _ _
    | with_reducible exact bits _ _
    | with_reducible exact drop _ _
    | with_reducible exact byte _
    | with_reducible exact restore _ _ _
    | with_reducible exact load _ _ _
    | with_reducible exact pull _ _ _
    | with_reducible exact room _ _ _
    | with_reducible exact need _ _ _ _
    | with_reducible exact root _ _ _ _
    | with_reducible exact link _ _ _ _
    | with_reducible exact extra _ _ _ _
    | with_reducible exact copyMatch _ _ _
    | with_reducible exact literal _ _ _
    | with_reducible apply ordered))

private theorem lengthMode : Sim P (back_LEN a) (back_LEN v) := by
  unfold back_LEN
  mode_sim

private theorem storedMode : Sim P (back_STORED a) (back_STORED v) := by
  unfold back_STORED INITBITS copyStoredInput
  mode_sim

private theorem typeMode : Sim P (back_TYPE a) (back_TYPE v) := by
  unfold back_TYPE
  mode_sim

private theorem lengthSymbols (st : InflateStatePtr) (reject : M Unit) :
    Sim P (readCodeLengths st (Zlib.Infback.lookup1 a false) (Zlib.Infback.NEEDBITS a) reject)
      (readCodeLengths st (Zlib.Infback.lookup1 v false) (Zlib.Infback.NEEDBITS v) reject) := by
  unfold readCodeLengths Zlib.Inflate.appendCurrentCode Zlib.Inflate.setPreviousLength Zlib.Inflate.setRepeatCount repeatCodeLength
  mode_sim

private theorem tableMode : Sim P (back_TABLE a) (back_TABLE v) := by
  unfold back_TABLE sharedCase
  have runLen := lengthMode cell outer c
  have lengths := lengthSymbols cell outer c c.st (Zlib.Infback.badMode v "invalid bit length repeat")
  mode_sim

theorem dispatch : Sim P (back_dispatch a) (back_dispatch v) := by
  have ty := typeMode cell outer c
  have stored := storedMode cell outer c
  have table := tableMode cell outer c
  have len := lengthMode cell outer c
  unfold back_dispatch sharedCase
  mode_sim

end
end Zlib.Infback.CallbackSimulation
