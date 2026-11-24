import ZlibF.Proof.«deflate.c.strategy-loop»

namespace Zlib.Deflate.HuffProofs
open C StrategyLoop
set_option autoImplicit false

private theorem step_sim (s : DeflateStatePtr) (flush : Int32) (flag : Bool) :
    Sim Corresponds (deflate_huff_step s flush flag) (deflate_huff_body s flush (pack flag)) := by
  unfold deflate_huff_step deflate_huff_body
  simp only [rd, assocM, pure_bindM, wr_cursor]
  repeat' first
    | apply Sim.bind; intro x
    | split
    | exact Sim.pure rfl
    | exact Sim.pure ⟨rfl,rfl⟩

abbrev legacy (n : Nat) (s : DeflateStatePtr) (flush : Int32) : M block_state :=
  StrategyLoop.legacy s flush (deflate_huff_body s flush) n

theorem legacy_fuel (s : DeflateStatePtr) (flush : Int32) : legacy fuel s flush = (do
    let st ← cwhile forever (deflate_huff_body s flush) {}
    if let some r := st.ret then return r
    wr s (fun d => {d with insert := 0})
    finish_tail s flush) := rfl

theorem legacy_unfold (n : Nat) (s : DeflateStatePtr) (flush : Int32) : legacy n s flush = (do
    let st ← cwhile.go forever (deflate_huff_body s flush) n {}
    if let some r := st.ret then return r
    wr s (fun d => {d with insert := 0})
    finish_tail s flush) := rfl

theorem eq_of_not_outOfFuel (s : DeflateStatePtr) (flush : Int32) (h : Heap)
    (defined : legacy fuel s flush h ≠ .error .outOfFuel) :
    deflate_huff s flush h = legacy fuel s flush h :=
  StrategyLoop.eq_of_not_outOfFuel s flush _ _ (step_sim s flush) h defined

theorem of_legacy_ok {s : DeflateStatePtr} {flush : Int32} {h after : Heap} {result : block_state}
    (run : legacy fuel s flush h = .ok (result,after)) :
    deflate_huff s flush h = .ok (result,after) := by
  rw [eq_of_not_outOfFuel s flush h (by simp [run]),run]

theorem to_legacy_ok {s : DeflateStatePtr} {flush : Int32} {h after : Heap} {result : block_state}
    (run : deflate_huff s flush h = .ok (result,after)) :
    legacy (fuel+1) s flush h = .ok (result,after) :=
  StrategyLoop.to_legacy_ok s flush _ _ (step_sim s flush) run

end Zlib.Deflate.HuffProofs
