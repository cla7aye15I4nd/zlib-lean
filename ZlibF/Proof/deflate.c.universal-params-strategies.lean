import ZlibF.Proof.«deflate.c.engine.lminner»
import ZlibF.Proof.«deflate.c.huff.source»
import ZlibF.Proof.«deflate.c.rle.source»
import ZlibF.Proof.«deflate.c.universal-params-publish»
import ZlibF.Proof.«deflate.c.engine.slow-source»

/-!
# deflate.c: the parameter frame for the matcher and the compression strategies

`longest_match`, `deflate_stored`,
`deflate_fast`, `deflate_slow`, `deflate_rle` and `deflate_huff` keep every parameter of every
record (`ExactM`).
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem exact_forever (st : LoopS) : ExactM (forever st) := ExactM.pure _

theorem exact_tally_dist (s : DeflateStatePtr) (distance length : UInt32) :
    ExactM (tally_dist s distance length) := by
  cases s with
  | none =>
    unfold tally_dist
    repeat' first
      | exact exact_put_symbol_byte _ _
      | x_step
  | some ref =>
    cases ref
    unfold tally_dist
    repeat' first
      | exact exact_put_symbol_byte _ _
      | exact exact_freq_inc _ _
      | exact exact_d_code _
      | x_step

theorem exact_lm_cond (limit scan match_ : BPtr) : ExactM (lm_cond limit scan match_) := by
  unfold lm_cond
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply ExactM.bind
  · apply ExactM.list_forIn
    intro value member current
    x_steps
  · rintro ⟨result, scan, match_⟩
    cases result <;> dsimp only
    all_goals x_steps

private theorem exact_lm_body_with (getEnd : DeflateState → M BPtr) (safe : ∀ d, ExactM (getEnd d)) (s : DeflateStatePtr) (st : LMState) : ExactM (lm_body_with getEnd lm_cond s st) := by
  unfold lm_body_with
  repeat' first
    | with_reducible exact safe _
    | with_reducible exact exact_lm_cond _ _ _
    | x_step

theorem exact_lm_body (s : DeflateStatePtr) (st : LMState) : ExactM (lm_body s st) := by
  apply exact_lm_body_with
  intro d
  repeat' first
    | x_step

theorem exact_longest_match (s : DeflateStatePtr) (cur : UInt32) : ExactM (longest_match s cur) := by
  unfold longest_match searchMatches
  simp only [Zlib.Deflate.Engine.Proofs.compare_eight_eq]
  repeat' first
    | with_reducible exact exact_lm_body_with _ (fun _ => ExactM.pure _) _ _
    | x_step

theorem ExactM.list_forIn_plain {α β : Type} (values : List α) (body : α → β → M (ForInStep β))
    (exact : ∀ value state, ExactM (body value state)) (initial : β) :
    ExactM (forIn values initial body) := by
  induction values generalizing initial with
  | nil => simp only [List.forIn_nil]; exact ExactM.pure _
  | cons head tail ih =>
    simp only [List.forIn_cons]
    apply ExactM.bind (exact head initial)
    intro decision
    cases decision with
    | done value => exact ExactM.pure _
    | yield next => exact ih next

/-- The strategies' callees as steps. -/
macro "strategy_step" : tactic => `(tactic|
  first
    | exact_join
    | with_reducible exact exact_tally_lit _ _
    | with_reducible exact exact_tally_dist _ _ _
    | with_reducible exact exact_updateHashAt _ _ _
    | with_reducible exact exact_insertStringAt _ _
    | with_reducible exact exact_INSERT_STRING _ _
    | with_reducible exact exact_UPDATE_HASH _ _
    | with_reducible exact exact_longest_match _ _
    | with_reducible exact exact_FLUSH_BLOCK _ _
    | with_reducible exact exact_FLUSH_BLOCK_ONLY _ _
    | with_reducible exact exact_finish_tail _ _
    | with_reducible exact exact_fill_window _
    | with_reducible exact exact_read_buf _ _ _
    | with_reducible exact exact_flush_pending _
    | with_reducible exact exact_put_byte _ _
    | with_reducible exact exact_store_at _ _ _
    | with_reducible exact Zlib.Trees.ParamsProofs.exact__tr_stored_block _ _ _ _
    | with_reducible exact exact_slide_hash _
    | with_reducible exact exact_CLEAR_HASH _
    | with_reducible apply ExactM.list_forIn
    | with_reducible apply ExactM.list_forIn_plain
    | with_reducible exact exact_forever _
    | x_step)

private theorem exact_storedAdvance (s : DeflateStatePtr) (n : UInt32) : ExactM (storedAdvance s n) := by
  unfold storedAdvance
  repeat' strategy_step

private theorem exact_storedSlideCount (s : DeflateStatePtr) : ExactM (storedSlideCount s) := by
  unfold storedSlideCount
  repeat' strategy_step

private theorem exact_storedClampInsert (s : DeflateStatePtr) : ExactM (storedClampInsert s) := by
  unfold storedClampInsert
  repeat' strategy_step

private theorem exact_storedHighWater (s : DeflateStatePtr) : ExactM (storedHighWater s) := by
  unfold storedHighWater
  repeat' strategy_step

private theorem exact_storedAddInsert (s : DeflateStatePtr) (n : UInt32) : ExactM (storedAddInsert s n) := by
  unfold storedAddInsert
  dsimp only [cdecl]
  repeat' strategy_step

set_option maxRecDepth 200000 in
theorem exact_deflate_stored (s : DeflateStatePtr) (flush : Int32) : ExactM (deflate_stored s flush) := by
  unfold deflate_stored
  have localValue {α : Type} (v : α) : ExactM (cdecl v) := ExactM.pure _
  repeat' first
    | with_reducible exact localValue _
    | with_reducible exact exact_storedAdvance _ _
    | with_reducible exact exact_storedSlideCount _
    | with_reducible exact exact_storedClampInsert _
    | with_reducible exact exact_storedHighWater _
    | with_reducible exact exact_storedAddInsert _ _
    | strategy_step

set_option maxRecDepth 200000 in
theorem exact_deflate_fast_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    ExactM (deflate_fast_body s flush st) := by
  unfold deflate_fast_body
  repeat' first
    | with_reducible exact exact_tally_lit _ _
    | with_reducible exact exact_tally_dist _ _ _
    | with_reducible exact exact_updateHashAt _ _ _
    | with_reducible exact exact_insertStringAt _ _
    | with_reducible exact exact_INSERT_STRING _ _
    | with_reducible exact exact_UPDATE_HASH _ _
    | with_reducible exact exact_longest_match _ _
    | with_reducible exact exact_FLUSH_BLOCK _ _
    | with_reducible exact exact_fill_window _
    | with_reducible exact exact_forever _
    | x_step

theorem exact_deflate_fast (s : DeflateStatePtr) (flush : Int32) : ExactM (deflate_fast s flush) := by
  unfold deflate_fast deflate_fast_step finishHashBlock
  repeat' strategy_step

/-- The callees of the lazy strategy as steps. -/
macro "slow_step" : tactic => `(tactic|
  first
    | with_reducible exact exact_tally_lit _ _
    | with_reducible exact exact_tally_dist _ _ _
    | with_reducible exact exact_updateHashAt _ _ _
    | with_reducible exact exact_insertStringAt _ _
    | with_reducible exact exact_INSERT_STRING _ _
    | with_reducible exact exact_longest_match _ _
    | with_reducible exact exact_FLUSH_BLOCK _ _
    | with_reducible exact exact_FLUSH_BLOCK_ONLY _ _
    | with_reducible exact exact_fill_window _
    | x_step)

open Zlib.Deflate.Engine.Proofs in
theorem exact_slowFind (s : DeflateStatePtr) (head : UInt32) : ExactM (slowFind s head) := by
  unfold slowFind; repeat' slow_step

open Zlib.Deflate.Engine.Proofs in
theorem exact_slowSearch (s : DeflateStatePtr) : ExactM (slowSearch s) := by
  unfold slowSearch
  repeat' first | with_reducible exact exact_slowFind _ _ | slow_step

open Zlib.Deflate.Engine.Proofs in
theorem exact_slowMatchBody (s : DeflateStatePtr) (max_insert head : UInt32) :
    ExactM (slowMatchBody s max_insert head) := by
  unfold slowMatchBody; repeat' slow_step

open Zlib.Deflate.Engine.Proofs in
theorem exact_slowMatchCond (s : DeflateStatePtr) (head : UInt32) : ExactM (slowMatchCond s head) := by
  unfold slowMatchCond; repeat' slow_step

open Zlib.Deflate.Engine.Proofs in
theorem exact_slowMatchAdvance (s : DeflateStatePtr) (max_insert head : UInt32) :
    ExactM (slowMatchAdvance s max_insert head) := by
  unfold slowMatchAdvance
  repeat' first
    | with_reducible exact exact_slowMatchBody _ _ _
    | with_reducible exact exact_slowMatchCond _ _
    | slow_step

open Zlib.Deflate.Engine.Proofs in
theorem exact_slowDecision (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (head : UInt32) :
    ExactM (slowDecision s flush st head) := by
  unfold slowDecision
  repeat' first
    | with_reducible exact exact_slowMatchAdvance _ _ _
    | slow_step

theorem exact_deflate_slow_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    ExactM (deflate_slow_body s flush st) := by
  rw [Zlib.Deflate.Engine.Proofs.slow_body_source]
  repeat' first
    | with_reducible exact exact_slowSearch _
    | with_reducible exact exact_slowDecision _ _ _ _
    | slow_step

theorem exact_deflate_slow (s : DeflateStatePtr) (flush : Int32) : ExactM (deflate_slow s flush) := by
  unfold deflate_slow deflate_slow_step slowFinish finishHashBlock
  repeat' strategy_step

theorem exact_deflate_rle_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    ExactM (deflate_rle_body s flush st) := by
  unfold deflate_rle_body
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' strategy_step

theorem exact_deflate_rle (s : DeflateStatePtr) (flush : Int32) : ExactM (deflate_rle s flush) := by
  have frame : ExactM (RleProofs.legacy (fuel+1) s flush) := by
    rw [RleProofs.legacy_unfold]
    repeat' first
      | with_reducible exact ExactM.cwhile_go forever _ exact_forever (exact_deflate_rle_body s flush) _ _
      | strategy_step
  exact fun _ _ _ run => frame _ _ _ (RleProofs.to_legacy_ok run)

theorem exact_deflate_huff_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    ExactM (deflate_huff_body s flush st) := by
  unfold deflate_huff_body
  repeat' strategy_step

theorem exact_deflate_huff (s : DeflateStatePtr) (flush : Int32) : ExactM (deflate_huff s flush) := by
  have frame : ExactM (HuffProofs.legacy (fuel+1) s flush) := by
    rw [HuffProofs.legacy_unfold]
    repeat' first
      | with_reducible exact ExactM.cwhile_go forever _ exact_forever (exact_deflate_huff_body s flush) _ _
      | strategy_step
  exact fun _ _ _ run => frame _ _ _ (HuffProofs.to_legacy_ok run)

end Zlib.Deflate.Universal.Params
