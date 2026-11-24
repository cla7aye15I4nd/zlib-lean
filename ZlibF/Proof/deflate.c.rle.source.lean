import ZlibF.Proof.«deflate.c.strategy-loop»
import ZlibF.Proof.«deflate.c.engine.lminner»

namespace Zlib.Deflate.RleProofs
open C StrategyLoop Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

private theorem scan_eight (prev : UInt32) (strend : BPtr) :
    rleMatchBytes prev strend 8 = fun (start : BPtr) => do
      let mut scan := start
      for _ in [0:8] do
        scan ← padd scan 1
        if prev != (← load8 scan).toUInt32 then return (false, scan)
      return (← Ptr.lt scan strend, scan) := by
  funext scan
  simp [List.range', rleMatchBytes, Engine.Proofs.M_bind_assoc,
    Engine.Proofs.M_pure_bind, Engine.Proofs.M_ite_bind]

private theorem clamp_eq (s : DeflateStatePtr) :
    clampRunLength s = wr s (fun d => {d with match_length :=
      if d.match_length > d.lookahead then d.lookahead else d.match_length}) := by
  funext h
  cases s with
  | none => rfl
  | some r =>
    cases r with
    | tab i =>
      cases e : h.dstates i with
      | none => simp [clampRunLength, wr, ldDeflateState, bind_app, DeflateStateRef.get, e]
      | some d =>
        have put (v : DeflateState) : stDeflateState (some (.tab i)) v h = .ok ((), setD h i v) :=
          stDeflateState_tab e
        by_cases c : d.match_length > d.lookahead <;>
          simp [clampRunLength, wr, bind_app, ldDeflateState_tab e, put, c, pure_app, setD_self e]

private theorem wr_match (s : DeflateStatePtr) {α : Type} (k : Unit → M α) :
    (wr s (fun d => {d with lookahead := d.lookahead - d.match_length}) >>= fun _ =>
      wr s (fun d => {d with strstart := d.strstart + d.match_length}) >>= fun _ =>
      wr s (fun d => {d with match_length := 0}) >>= k) =
    wr s (fun d => {d with
      lookahead := d.lookahead - d.match_length
      strstart := d.strstart + d.match_length
      match_length := 0}) >>= k := by
  rw [← assocM, wr_then_wr, ← assocM, wr_then_wr]

private theorem read_again {α : Type} (s : DeflateStatePtr) (test : DeflateState → Prop)
    [DecidablePred test] (yes no : DeflateState → M α) :
    (ldDeflateState s >>= fun d => if test d then yes d else ldDeflateState s >>= no) =
    (ldDeflateState s >>= fun d => if test d then yes d else no d) := by
  funext h
  cases s with
  | none => rfl
  | some r =>
    cases r with
    | tab i =>
      cases e : h.dstates i with
      | none => simp [ldDeflateState, bind_app, DeflateStateRef.get, e]
      | some d =>
        by_cases c : test d <;> simp [bind_app, ldDeflateState_tab e, c]

private theorem sim_ite {α β : Type} {R : α → β → Prop} {a₁ a₂ : M α} {b₁ b₂ : M β}
    {c : Prop} [Decidable c] (left : Sim R a₁ b₁) (right : Sim R a₂ b₂) :
    Sim R (if c then a₁ else a₂) (if c then b₁ else b₂) := by
  split <;> assumption

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
private theorem step_sim (s : DeflateStatePtr) (flush : Int32) (flag : Bool) :
    Sim Corresponds (deflate_rle_step s flush flag) (deflate_rle_body s flush (pack flag)) := by
  unfold deflate_rle_step deflate_rle_body
  simp only [rd, assocM, pure_bindM, wr_cursor, wr_match, scan_eight, clamp_eq, read_again]
  repeat' first
    | apply Sim.bind; intro x
    | apply sim_ite
    | split
    | exact Sim.pure rfl
    | exact Sim.pure ⟨rfl,rfl⟩

abbrev legacy (n : Nat) (s : DeflateStatePtr) (flush : Int32) : M block_state :=
  StrategyLoop.legacy s flush (deflate_rle_body s flush) n

theorem legacy_fuel (s : DeflateStatePtr) (flush : Int32) : legacy fuel s flush = (do
    let st ← cwhile forever (deflate_rle_body s flush) {}
    if let some r := st.ret then return r
    wr s (fun d => {d with insert := 0})
    finish_tail s flush) := rfl

theorem legacy_unfold (n : Nat) (s : DeflateStatePtr) (flush : Int32) : legacy n s flush = (do
    let st ← cwhile.go forever (deflate_rle_body s flush) n {}
    if let some r := st.ret then return r
    wr s (fun d => {d with insert := 0})
    finish_tail s flush) := rfl

theorem eq_of_not_outOfFuel (s : DeflateStatePtr) (flush : Int32) (h : Heap)
    (defined : legacy fuel s flush h ≠ .error .outOfFuel) :
    deflate_rle s flush h = legacy fuel s flush h :=
  StrategyLoop.eq_of_not_outOfFuel s flush _ _ (step_sim s flush) h defined

theorem of_legacy_ok {s : DeflateStatePtr} {flush : Int32} {h after : Heap} {result : block_state}
    (run : legacy fuel s flush h = .ok (result,after)) :
    deflate_rle s flush h = .ok (result,after) := by
  rw [eq_of_not_outOfFuel s flush h (by simp [run]),run]

theorem to_legacy_ok {s : DeflateStatePtr} {flush : Int32} {h after : Heap} {result : block_state}
    (run : deflate_rle s flush h = .ok (result,after)) :
    legacy (fuel+1) s flush h = .ok (result,after) :=
  StrategyLoop.to_legacy_ok s flush _ _ (step_sim s flush) run

end Zlib.Deflate.RleProofs
