import ZlibF.Proof.«deflate.c.engine.lminner»
import ZlibF.Proof.«deflate.c.huff.source»
import ZlibF.Proof.«deflate.c.rle.source»
import ZlibF.Proof.«deflate.c.universal-call-keep-publish»
import ZlibF.Proof.«deflate.c.engine.slow-source»

/-!
# deflate.c: `KeepRel` for the matcher and the compression strategies

Port of `deflate.c.universal-params-strategies`: `longest_match`, `deflate_stored`,
`deflate_fast`, `deflate_slow`, `deflate_rle` and `deflate_huff` are in `KeepM`.
-/

namespace Zlib.Deflate.Universal.Keep
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem keep_forever (st : LoopS) : KeepM (forever st) := KeepM.pure _

theorem keep_tally_dist (s : DeflateStatePtr) (distance length : UInt32) :
    KeepM (tally_dist s distance length) := by
  cases s with
  | none =>
    unfold tally_dist
    repeat' first
      | exact keep_put_symbol_byte _ _
      | k_step
  | some ref =>
    cases ref
    unfold tally_dist
    repeat' first
      | exact keep_put_symbol_byte _ _
      | exact keep_freq_inc _ _
      | exact keep_d_code _
      | k_step

theorem keep_lm_cond (limit scan match_ : BPtr) : KeepM (lm_cond limit scan match_) := by
  unfold lm_cond
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply KeepM.bind
  · apply KeepM.list_forIn
    intro value member current
    k_steps
  · rintro ⟨result, scan, match_⟩
    cases result <;> dsimp only
    all_goals k_steps

private theorem keep_lm_body_with (getEnd : DeflateState → M BPtr) (safe : ∀ d, KeepM (getEnd d)) (s : DeflateStatePtr) (st : LMState) : KeepM (lm_body_with getEnd lm_cond s st) := by
  unfold lm_body_with
  repeat' first
    | with_reducible exact safe _
    | with_reducible exact keep_lm_cond _ _ _
    | k_step

theorem keep_lm_body (s : DeflateStatePtr) (st : LMState) : KeepM (lm_body s st) := by
  apply keep_lm_body_with
  intro d
  repeat' first
    | k_step

theorem keep_longest_match (s : DeflateStatePtr) (cur : UInt32) : KeepM (longest_match s cur) := by
  unfold longest_match searchMatches
  simp only [Zlib.Deflate.Engine.Proofs.compare_eight_eq]
  repeat' first
    | with_reducible exact keep_lm_body_with _ (fun _ => KeepM.pure _) _ _
    | k_step

theorem KeepM.list_forIn_plain {α β : Type} (values : List α) (body : α → β → M (ForInStep β))
    (exact : ∀ value state, KeepM (body value state)) (initial : β) :
    KeepM (forIn values initial body) := by
  induction values generalizing initial with
  | nil => simp only [List.forIn_nil]; exact KeepM.pure _
  | cons head tail ih =>
    simp only [List.forIn_cons]
    apply KeepM.bind (exact head initial)
    intro decision
    cases decision with
    | done value => exact KeepM.pure _
    | yield next => exact ih next

/-- The strategies' callees as steps. -/
macro "k_strategy_step" : tactic => `(tactic|
  first
    | keep_join
    | with_reducible exact keep_tally_lit _ _
    | with_reducible exact keep_tally_dist _ _ _
    | with_reducible exact keep_updateHashAt _ _ _
    | with_reducible exact keep_insertStringAt _ _
    | with_reducible exact keep_INSERT_STRING _ _
    | with_reducible exact keep_UPDATE_HASH _ _
    | with_reducible exact keep_longest_match _ _
    | with_reducible exact keep_FLUSH_BLOCK _ _
    | with_reducible exact keep_FLUSH_BLOCK_ONLY _ _
    | with_reducible exact keep_finish_tail _ _
    | with_reducible exact keep_fill_window _
    | with_reducible exact keep_read_buf _ _ _
    | with_reducible exact keep_flush_pending _
    | with_reducible exact keep_put_byte _ _
    | with_reducible exact keep_store_at _ _ _
    | with_reducible exact Zlib.Trees.KeepProofs.keep__tr_stored_block _ _ _ _
    | with_reducible exact keep_slide_hash _
    | with_reducible exact keep_CLEAR_HASH _
    | with_reducible apply KeepM.list_forIn
    | with_reducible apply KeepM.list_forIn_plain
    | with_reducible exact keep_forever _
    | k_step)

private theorem keep_storedAdvance (s : DeflateStatePtr) (n : UInt32) : KeepM (storedAdvance s n) := by
  unfold storedAdvance
  repeat' k_strategy_step

private theorem keep_storedSlideCount (s : DeflateStatePtr) : KeepM (storedSlideCount s) := by
  unfold storedSlideCount
  repeat' k_strategy_step

private theorem keep_storedClampInsert (s : DeflateStatePtr) : KeepM (storedClampInsert s) := by
  unfold storedClampInsert
  repeat' k_strategy_step

private theorem keep_storedHighWater (s : DeflateStatePtr) : KeepM (storedHighWater s) := by
  unfold storedHighWater
  repeat' k_strategy_step

private theorem keep_storedAddInsert (s : DeflateStatePtr) (n : UInt32) : KeepM (storedAddInsert s n) := by
  unfold storedAddInsert
  dsimp only [cdecl]
  repeat' k_strategy_step

set_option maxRecDepth 200000 in
theorem keep_deflate_stored (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_stored s flush) := by
  unfold deflate_stored
  have localValue {α : Type} (v : α) : KeepM (cdecl v) := KeepM.pure _
  repeat' first
    | with_reducible exact localValue _
    | with_reducible exact keep_storedAdvance _ _
    | with_reducible exact keep_storedSlideCount _
    | with_reducible exact keep_storedClampInsert _
    | with_reducible exact keep_storedHighWater _
    | with_reducible exact keep_storedAddInsert _ _
    | k_strategy_step

set_option maxRecDepth 200000 in
theorem keep_deflate_fast_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_fast_body s flush st) := by
  unfold deflate_fast_body
  repeat' first
    | with_reducible exact keep_tally_lit _ _
    | with_reducible exact keep_tally_dist _ _ _
    | with_reducible exact keep_updateHashAt _ _ _
    | with_reducible exact keep_insertStringAt _ _
    | with_reducible exact keep_INSERT_STRING _ _
    | with_reducible exact keep_UPDATE_HASH _ _
    | with_reducible exact keep_longest_match _ _
    | with_reducible exact keep_FLUSH_BLOCK _ _
    | with_reducible exact keep_fill_window _
    | with_reducible exact keep_forever _
    | k_step

theorem keep_deflate_fast (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_fast s flush) := by
  unfold deflate_fast deflate_fast_step finishHashBlock
  repeat' k_strategy_step

/-- The callees of the lazy strategy as steps. -/
macro "k_slow_step" : tactic => `(tactic|
  first
    | with_reducible exact keep_tally_lit _ _
    | with_reducible exact keep_tally_dist _ _ _
    | with_reducible exact keep_updateHashAt _ _ _
    | with_reducible exact keep_insertStringAt _ _
    | with_reducible exact keep_INSERT_STRING _ _
    | with_reducible exact keep_longest_match _ _
    | with_reducible exact keep_FLUSH_BLOCK _ _
    | with_reducible exact keep_FLUSH_BLOCK_ONLY _ _
    | with_reducible exact keep_fill_window _
    | k_step)

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowFind (s : DeflateStatePtr) (head : UInt32) : KeepM (slowFind s head) := by
  unfold slowFind; repeat' k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowSearch (s : DeflateStatePtr) : KeepM (slowSearch s) := by
  unfold slowSearch
  repeat' first | with_reducible exact keep_slowFind _ _ | k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowMatchBody (s : DeflateStatePtr) (max_insert head : UInt32) :
    KeepM (slowMatchBody s max_insert head) := by
  unfold slowMatchBody; repeat' k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowMatchCond (s : DeflateStatePtr) (head : UInt32) : KeepM (slowMatchCond s head) := by
  unfold slowMatchCond; repeat' k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowMatchAdvance (s : DeflateStatePtr) (max_insert head : UInt32) :
    KeepM (slowMatchAdvance s max_insert head) := by
  unfold slowMatchAdvance
  repeat' first
    | with_reducible exact keep_slowMatchBody _ _ _
    | with_reducible exact keep_slowMatchCond _ _
    | k_slow_step

open Zlib.Deflate.Engine.Proofs in
theorem keep_slowDecision (s : DeflateStatePtr) (flush : Int32) (st : LoopS) (head : UInt32) :
    KeepM (slowDecision s flush st head) := by
  unfold slowDecision
  repeat' first
    | with_reducible exact keep_slowMatchAdvance _ _ _
    | k_slow_step

theorem keep_deflate_slow_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_slow_body s flush st) := by
  rw [Zlib.Deflate.Engine.Proofs.slow_body_source]
  repeat' first
    | with_reducible exact keep_slowSearch _
    | with_reducible exact keep_slowDecision _ _ _ _
    | k_slow_step

theorem keep_deflate_slow (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_slow s flush) := by
  unfold deflate_slow deflate_slow_step slowFinish finishHashBlock
  repeat' k_strategy_step

theorem keep_deflate_rle_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_rle_body s flush st) := by
  unfold deflate_rle_body
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' k_strategy_step

theorem keep_deflate_rle (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_rle s flush) := by
  have frame : KeepM (RleProofs.legacy (fuel+1) s flush) := by
    rw [RleProofs.legacy_unfold]
    repeat' first
      | with_reducible exact KeepM.cwhile_go forever _ keep_forever (keep_deflate_rle_body s flush) _ _
      | k_strategy_step
  exact fun _ _ _ run => frame _ _ _ (RleProofs.to_legacy_ok run)

theorem keep_deflate_huff_body (s : DeflateStatePtr) (flush : Int32) (st : LoopS) :
    KeepM (deflate_huff_body s flush st) := by
  unfold deflate_huff_body
  repeat' k_strategy_step

theorem keep_deflate_huff (s : DeflateStatePtr) (flush : Int32) : KeepM (deflate_huff s flush) := by
  have frame : KeepM (HuffProofs.legacy (fuel+1) s flush) := by
    rw [HuffProofs.legacy_unfold]
    repeat' first
      | with_reducible exact KeepM.cwhile_go forever _ keep_forever (keep_deflate_huff_body s flush) _ _
      | k_strategy_step
  exact fun _ _ _ run => frame _ _ _ (HuffProofs.to_legacy_ok run)

end Zlib.Deflate.Universal.Keep
