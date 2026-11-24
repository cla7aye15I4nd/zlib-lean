import ZlibF.Proof.«infback.c.addressed-match»

/-! Every branch of one slow LEN dispatch in the address-retaining callback decoder. -/
namespace Zlib.Infback.AddressedTable
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback.Proofs Zlib.Infback.Safety
open Zlib.Infback.AddressedStored Zlib.Inffast.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A LEN round either exits on a callback refusal or returns control to
the dispatcher in a literal/length, new block, or error mode. -/
def LenResult (owner : Nat) (run : Except Fault ((Except Ex Unit × IL) × Heap)) : Prop :=
  (∃ regs H, run = .ok ((.error Ex.leave, regs), H) ∧ regs.ret = Z_BUF_ERROR) ∨
    ∃ regs H t, run = .ok ((.ok (), regs), H) ∧ H.istates owner = some t ∧
      (t.mode = LEN ∨ t.mode = TYPE ∨ t.mode = BAD)

/-- The decoder fields used on entry to the next switch. -/
def LenState (owner : Nat) (before after : InflateState) : Prop :=
  (StOk before → StOk after) ∧ after.last = before.last ∧ (before.WellFormed → after.WellFormed) ∧
    (TablesOk owner before → TablesOk owner after)

theorem LenState.same (owner : Nat) (s : InflateState) : LenState owner s s := ⟨id, rfl, id, id⟩

def LenRound (owner w off cap : Nat) (cell : BPtrCell) (r : ZStreamRef)
    (A : PointerLocals → Heap → Prop) (s : InflateState) (run : Except Fault ((Except Ex Unit × IL) × Heap)) : Prop :=
  ∃ status regs H t, run = .ok ((status, regs), H) ∧ H.istates owner = some t ∧ Buffers cell w off cap t regs H ∧
    ((∀ cs G z msg, A cs G → r.get G = some z → A cs (r.put G {z with msg := msg})) → A regs.pointerLocals H) ∧
    LenState owner s t ∧ match status with
    | .error e => e = Ex.leave ∧ regs.ret = Z_BUF_ERROR
    | .ok _ => ReadyBits regs ∧ (t.mode = LEN ∨ t.mode = TYPE ∨ t.mode = BAD)

theorem LenRound.result {owner w off cap cell r A s run} (round : LenRound owner w off cap cell r A s run) :
    LenResult owner run := by
  obtain ⟨v, regs, H, t, call, st, _, _, _, out⟩ := round
  cases v with
  | error e => obtain ⟨rfl, ret⟩ := out; exact Or.inl ⟨regs, H, call, ret⟩
  | ok u => cases u; exact Or.inr ⟨regs,H,t,call,st,out.2⟩

private theorem LenRound.eof {owner w off cap cell r A s run} {regs : IL} {H : Heap}
    (call : run = .ok ((.error Ex.leave, regs), H)) (ret : regs.ret = Z_BUF_ERROR)
    (st : H.istates owner = some s) (buf : Buffers cell w off cap s regs H) (ok : A regs.pointerLocals H) :
    LenRound owner w off cap cell r A s run :=
  ⟨_,regs,H,s,call,st,buf,fun _ => ok,.same owner s,rfl,ret⟩

private theorem leafBits {l : IL} {code : Code} (width : code.bits.toNat ≤ 15)
    (fit : code.bits.toNat ≤ l.bits.toNat) (near : l.bits.toNat - code.bits.toNat < 8)
    (held : l.hold.toNat < 2 ^ l.bits.toNat) : ReadyBits (dropR l code.bits.toUInt32) := by
  have bound : code.bits.toUInt32.toNat ≤ l.bits.toNat := by simpa using fit
  exact ⟨by rw [dropR_bits bound, UInt8.toNat_toUInt32]; exact near,
    dropR_clean (by rw [UInt8.toNat_toUInt32]; omega) bound held⟩

section
variable {owner w off cap : Nat} {cell : BPtrCell} {input : CInCb} {i : VoidPtr}
  {output : COutCb} {o : VoidPtr} {admitted : PointerLocals → Heap → Prop} {r : ZStreamRef}
  (cb : Callbacks owner w off cap cell input i output o admitted)
  (edit : ∀ cs H t, admitted cs H → admitted cs (setI H owner t))
  (stream : ∀ cs H, admitted cs H → ∃ z, r.get H = some z)
  (globals : ∀ cs H, admitted cs H → LibraryGlobals H)
include cb edit stream globals

private theorem distance_step {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (mode : s.mode = LEN) (tabs : TablesOk owner s) (length : 0 < s.length.toNat)
    (buf : Buffers cell w off cap s l h) (ok : admitted l.pointerLocals h)
    (short : l.bits.toNat < 8) (clean : l.hold.toNat < 2 ^ l.bits.toNat) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenRound owner w off cap cell r admitted s (runX (lenDist c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  change LenRound owner w off cap cell r admitted s (runX (lenDist c) l h)
  rcases distance_read (strm := some r) cb state tabs buf ok globals clean short with empty | next
  · obtain ⟨regs, H, run, ret, buffer, allowed, st⟩ := empty; exact .eof run ret st buffer allowed
  obtain ⟨regs, H, d, read, valid, allowed, present, leaf, _, fit, small, held⟩ := next
  change runX (lenDist c) l h = runX (distSym c) regs H at read
  rw [read]
  have narrow : regs.here.bits.toNat ≤ 15 := by have := leaf.1; omega
  by_cases bad : regs.here.op &&& 64 = 0
  · rcases match_base_read (strm := some r) cb true edit present valid allowed narrow fit small held bad (by simp) with eof | decoded
    · obtain ⟨v,G,run,ret,buffer,ok',st⟩ := eof
      exact ⟨_,v,G,_,run,st,buffer,fun _ => ok', LenState.same owner s,rfl,ret⟩
    obtain ⟨b, loc, G, _, record, buffer, ok', low, clean', cut⟩ := decoded
    let t := addExtra true (matchBase true s regs.here) b
    change runX (distSym c) regs H = runX (lenCopy c) loc G at cut
    rw [cut]
    obtain ⟨z, live⟩ := stream _ _ ok'
    have copy := match_copy cb live record buffer ok' (show 0 < t.length.toNat from length)
    change (if t.offset > t.wsize - (if t.whave < t.wsize then loc.left else 0) then _ else _) at copy
    by_cases far : t.offset > t.wsize - (if t.whave < t.wsize then loc.left else 0)
    · rw [ite_eq_left far] at copy
      obtain ⟨j, _, run⟩ := copy
      let z' := {z with msg := Ptr.ref (.str j) 0}
      have b' := buffer.putStream r z'
      exact ⟨_,loc,_,_,run,upd_same ..,{b' with window := ⟨b'.window.storage,b'.window.writable⟩},
        fun msg => edit _ _ _ (msg _ _ _ _ ok' live), LenState.same owner s, ⟨low,clean'⟩, Or.inr (Or.inr rfl)⟩
    · rw [ite_eq_right far] at copy
      obtain ⟨v, reg, A, u, run, st, valid', admitted', shape, eqBits, eqHold, _, _, failure⟩ := copy
      refine ⟨v,reg,A,u,run,st,valid',fun _ => admitted',?_,?_⟩
      · rw [show u = _ from shape.1]
        exact ⟨fun old => ⟨old.1, old.2.1, by
          change u.whave.toNat ≤ s.wsize.toNat
          rcases shape.2 with eq | eq
          · rw [eq]; exact old.2.2
          · rw [eq]; exact Nat.le_refl _⟩, rfl, id, id⟩
      · cases v with
        | error e => exact failure e rfl
        | ok unit_ =>
          have same := congrArg InflateState.mode shape.1
          exact ⟨by unfold ReadyBits; rw [eqBits, eqHold]; exact ⟨low, clean'⟩, Or.inl (same.trans mode)⟩
  · obtain ⟨z, live⟩ := stream _ _ allowed
    obtain ⟨j, _, badRun⟩ := dist_invalid c rfl rfl live present narrow bad
    have b' := valid.putStream r {z with msg := .ref (.str j) 0}
    exact ⟨_,_,_,_,badRun,upd_same ..,{b' with window := ⟨b'.window.storage,b'.window.writable⟩},
      fun msg => edit _ _ _ (msg _ _ _ _ allowed live), LenState.same owner s,
      leafBits narrow fit small held, Or.inr (Or.inr rfl)⟩

/-- The actual slow LEN case executes both root and subtable lookups.
Input or output callbacks can redirect the cursor on every invocation. -/
theorem slow_round {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (mode : s.mode = LEN) (tabs : TablesOk owner s) (buf : Buffers cell w off cap s l h)
    (ok : admitted l.pointerLocals h) (short : l.bits.toNat < 8) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    (slow : (l.have_ >= 6 && l.left >= 258) = false) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenRound owner w off cap cell r admitted s (runX (back_LEN c) l h) := by
  let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
  change LenRound owner w off cap cell r admitted s (runX (back_LEN c) l h)
  rcases slow_len_read (strm := some r) cb state tabs buf ok globals clean short slow with empty | next
  · obtain ⟨regs, H, run, ret, buffer, allowed, st⟩ := empty; exact .eof run ret st buffer allowed
  obtain ⟨regs, H, d, read, valid, allowed, present, leaf, _, fit, small, held⟩ := next
  change runX (back_LEN c) l h = runX (lenSym c) regs H at read
  rw [read]
  have narrow : regs.here.bits.toNat ≤ 15 := by have := leaf.1; omega
  by_cases lit : regs.here.op = 0
  · obtain ⟨v, reg, A, t, run, buffer, admit, st, bit, hold, _, fields, failure, success⟩ :=
      literal_output (strm := some r) cb edit present valid allowed lit narrow
    refine ⟨v,reg,A,t,run,st,buffer,fun _ => admit,?_,?_⟩
    · rw [show t = _ from fields.1]
      exact ⟨fun old => ⟨old.1, old.2.1, by
        change t.whave.toNat ≤ s.wsize.toNat
        rcases fields.2 with eq | eq
        · rw [eq]; exact old.2.2
        · rw [eq]; exact Nat.le_refl _⟩, rfl, id, id⟩
    · cases v with
      | error e => exact failure e rfl
      | ok u =>
        cases u
        exact ⟨by unfold ReadyBits; rw [bit, hold]; exact leafBits narrow fit small held, Or.inl (success rfl).1⟩
  · by_cases terminal : regs.here.op &&& 32 ≠ 0 ∨ regs.here.op &&& 64 ≠ 0
    · obtain ⟨z, live⟩ := stream _ _ allowed
      have term := len_terminal c rfl rfl live present narrow lit terminal
      dsimp only at term
      split at term
      · exact ⟨_,_,_,_,term,upd_same ..,{valid with window := ⟨valid.window.storage,valid.window.writable⟩},
          fun _ => edit _ _ _ allowed, LenState.same owner s, leafBits narrow fit small held, Or.inr (Or.inl rfl)⟩
      · obtain ⟨j, _, run⟩ := term
        let marked := {s with length := regs.here.val.toUInt32}
        have pre : Buffers cell w off cap marked regs (setI H owner marked) :=
          {valid with window := ⟨valid.window.storage,valid.window.writable⟩}
        have b' := pre.putStream r {z with msg := .ref (.str j) 0}
        exact ⟨_,_,_,_,run,upd_same ..,{b' with window := ⟨b'.window.storage,b'.window.writable⟩},
          fun msg => edit _ _ _ (msg _ _ _ _ (edit _ _ marked allowed) (by simpa using live)), LenState.same owner s,
          leafBits narrow fit small held, Or.inr (Or.inr rfl)⟩
    · have zero32 : regs.here.op &&& 32 = 0 := Classical.byContradiction fun n => terminal (Or.inl n)
      have zero64 : regs.here.op &&& 64 = 0 := Classical.byContradiction fun n => terminal (Or.inr n)
      rcases match_base_read (strm := some r) cb false edit present valid allowed narrow fit small held zero64
        (fun _ => ⟨lit, zero32⟩) with eof | decoded
      · obtain ⟨v,G,run,ret,buffer,ok',st⟩ := eof
        exact ⟨_,v,G,_,run,st,buffer,fun _ => ok', LenState.same owner s,rfl,ret⟩
      obtain ⟨b, loc, G, extra, st, buffer, ok', near, clean', cut⟩ := decoded
      change runX (lenSym c) regs H = runX (lenDist c) loc G at cut
      rw [cut]
      obtain ⟨_, _, base, limit⟩ := (leaf.2.resolve_left lit).resolve_right (fun x => x.2 zero64)
      change b.toNat < 2 ^ (regs.here.op.toUInt32 &&& 15).toNat at extra
      rw [Zlib.Inffast.Proofs.mask15] at extra
      have positive : 0 < (regs.here.val.toUInt32 + b).toNat := by
        rw [UInt32.toNat_add, UInt16.toNat_toUInt32, Nat.mod_eq_of_lt (by omega : regs.here.val.toNat + b.toNat < 2^32)]
        omega
      exact distance_step (s := addExtra false (matchBase false s regs.here) b) cb edit stream globals
        st mode tabs positive buffer ok' near clean'

/-- The actual slow LEN case executes both root and subtable lookups.
Input or output callbacks can redirect the cursor on every invocation. -/
theorem slow_case {s : InflateState} {l : IL} {h : Heap} (state : h.istates owner = some s)
    (mode : s.mode = LEN) (tabs : TablesOk owner s) (buf : Buffers cell w off cap s l h)
    (ok : admitted l.pointerLocals h) (short : l.bits.toNat < 8) (clean : l.hold.toNat < 2 ^ l.bits.toNat)
    (slow : (l.have_ >= 6 && l.left >= 258) = false) :
    let c := addressedCtx (some r) (some (.tab owner)) cell input i output o
    LenResult owner (runX (back_LEN c) l h) :=
  (slow_round cb edit stream globals state mode tabs buf ok short clean slow).result

end
#print axioms slow_round
#print axioms slow_case
end Zlib.Infback.AddressedTable
