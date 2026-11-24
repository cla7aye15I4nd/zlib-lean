import ZlibF.Proof.«deflate.c.hash-order»
import ZlibF.Proof.«deflate.c.universal-params-steps»
import ZlibF.Proof.«trees.c.monad»

/-!
# deflate.c: the parameter frame for the helpers of `deflate_base.c`

The macros and helpers of
`deflate_base.c.lean` keep every parameter of every record (`ExactM`).
-/

namespace Zlib.Deflate.Universal.Params
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

theorem exact_chk32 (v : Int) : ExactM (chk32 v) := by
  unfold chk32; exact ExactM.ite _ (ExactM.pure _) (ExactM.ub _)
theorem exact_chk64 (v : Int) : ExactM (chk64 v) := by
  unfold chk64; exact ExactM.ite _ (ExactM.pure _) (ExactM.ub _)
theorem exact_iadd (a b : Int32) : ExactM (iadd a b) := exact_chk32 _
theorem exact_isub (a b : Int32) : ExactM (isub a b) := exact_chk32 _
theorem exact_ineg (a : Int32) : ExactM (ineg a) := exact_chk32 _
theorem exact_ladd (a b : Int64) : ExactM (ladd a b) := exact_chk64 _
theorem exact_lsub (a b : Int64) : ExactM (lsub a b) := exact_chk64 _
theorem exact_ishl (a : Int32) (n : Int) : ExactM (ishl a n) := by
  unfold ishl; exact ExactM.ite _ (exact_chk32 _) (ExactM.ub _)
theorem exact_ushl (a n : UInt32) : ExactM (ushl a n) := by
  unfold ushl; exact ExactM.ite _ (ExactM.pure _) (ExactM.ub _)
theorem exact_config_at (level : Int32) : ExactM (config_at level) := by
  unfold config_at; exact ExactM.ite _ (ExactM.pure _) (ExactM.ub _)
theorem exact_padd {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : ExactM (padd p n) :=
  exact_ptr_add _ _
theorem exact_psub {R T : Type} [Space Heap R T] (p : Ptr R) (n : Nat) : ExactM (psub p n) :=
  exact_ptr_add _ _
theorem exact_rd {α : Type} (p : DeflateStatePtr) (f : DeflateState → α) : ExactM (rd p f) :=
  ExactM.bind (exact_ldDeflateState p) (fun _ => ExactM.pure _)
theorem exact_zrd {α : Type} (p : ZStreamPtr) (f : ZStream → α) : ExactM (zrd p f) :=
  ExactM.bind (exact_ldZStream p) (fun _ => ExactM.pure _)

/-- The helpers above as steps. -/
macro "x_leaf" : tactic => `(tactic|
  first
    | with_reducible exact exact_chk32 _
    | with_reducible exact exact_chk64 _
    | with_reducible exact exact_iadd _ _
    | with_reducible exact exact_isub _ _
    | with_reducible exact exact_ineg _
    | with_reducible exact exact_ladd _ _
    | with_reducible exact exact_lsub _ _
    | with_reducible exact exact_ishl _ _
    | with_reducible exact exact_ushl _ _
    | with_reducible exact exact_config_at _
    | with_reducible exact exact_padd _ _
    | with_reducible exact exact_psub _ _
    | with_reducible exact exact_rd _ _
    | with_reducible exact exact_zrd _ _
    | exact_leaf)

/-- One step: a helper, a primitive or a composition rule. -/
macro "x_step" : tactic => `(tactic|
  first
    | x_leaf
    | exact_step
    | split)

macro "x_steps" : tactic => `(tactic| repeat' x_step)

/-- A load, steps that keep every parameter, and a store of a record with the loaded parameters. -/
theorem exact_ld_st0 {β : Type} (p : DeflateStatePtr) (q : DeflateState → M β)
    (g : DeflateState → β → DeflateState) (hq : ∀ d, ExactM (q d)) (hg : ∀ d x, Pars (g d x) = Pars d) :
    ExactM (do
      let d ← ldDeflateState p
      let x ← q d
      stDeflateState p (g d x)) := by
  have whole := exact_ld_st p q g (fun _ _ => (Pure.pure () : M Unit)) hq hg (fun _ _ => ExactM.pure _)
  have tail : ∀ (d : DeflateState) (x : β),
      (stDeflateState p (g d x) >>= fun _ => (Pure.pure () : M Unit)) = stDeflateState p (g d x) := by
    intro d x
    funext h
    simp only [bind_app, pure_app]
    cases stDeflateState p (g d x) h <;> rfl
  simpa only [tail] using whole

theorem exact_store_at (p : BPtr) (i : Nat) (v : UInt8) : ExactM (store_at p i v) := by
  unfold store_at; x_steps

theorem exact_put_byte (s : DeflateStatePtr) (c : UInt8) : ExactM (put_byte s c) := by
  unfold put_byte Zlib.Trees.put_byte
  simp only [cdecl_eq, M_pure_bind]
  exact ExactM.bind (exact_ldDeflateState s) (fun _ =>
    ExactM.bind (exact_ptr_add _ _) (fun _ =>
      ExactM.bind (exact_wr _ _ (fun _ => rfl)) (fun _ => exact_store8 _ _)))

theorem exact_putShortMSB (s : DeflateStatePtr) (b : UInt32) : ExactM (putShortMSB s b) := by
  unfold putShortMSB
  exact ExactM.bind (exact_put_byte _ _) (fun _ => exact_put_byte _ _)

theorem exact_UPDATE_HASH (s : DeflateStatePtr) (c : UInt8) : ExactM (UPDATE_HASH s c) := by
  unfold UPDATE_HASH
  exact exact_ld_st0 s (fun d => ushl d.ins_h d.hash_shift)
    (fun d sh => { d with ins_h := (sh ^^^ c.toUInt32) &&& d.hash_mask }) (fun _ => exact_ushl _ _)
    (fun _ _ => rfl)

theorem exact_INSERT_STRING (s : DeflateStatePtr) (str : UInt32) : ExactM (INSERT_STRING s str) := by
  unfold INSERT_STRING
  repeat' first | exact exact_UPDATE_HASH _ _ | x_step

theorem exact_updateHashAt (s : DeflateStatePtr) (window : BPtr) (i : UInt32) :
    ExactM (updateHashAt s window i) := by
  intro h u after run
  have old := (Zlib.Deflate.Proofs.HashOrder.updateHashAt_ok_iff s window i h after u).mp run
  exact ExactM.bind (exact_index8 _ _) (fun byte => exact_UPDATE_HASH s byte) h u after old

theorem exact_insertStringAt (s : DeflateStatePtr) (str : UInt32) : ExactM (insertStringAt s str) := by
  intro h v after run
  exact exact_INSERT_STRING s str h v after
    ((Zlib.Deflate.Proofs.HashOrder.insertStringAt_ok_iff s str h after v).mp run)

theorem exact_CLEAR_HASH (s : DeflateStatePtr) : ExactM (CLEAR_HASH s) := by
  unfold CLEAR_HASH; x_steps

theorem exact_d_code (dist : UInt16) : ExactM (d_code dist) := by
  unfold d_code; x_steps

theorem exact_freq_inc (r : CtDataRef) (i : Nat) : ExactM (freq_inc r i) := by
  unfold freq_inc; x_steps

theorem exact_put_symbol_byte (p : DeflateStatePtr) (v : UInt8) :
    ExactM (Zlib.Trees.put_symbol_byte p v) := by
  unfold Zlib.Trees.put_symbol_byte
  exact ExactM.bind (exact_ldDeflateState p) (fun _ =>
    ExactM.bind (exact_ptr_add _ _) (fun _ =>
      ExactM.bind (exact_wr _ _ (fun _ => rfl)) (fun _ => exact_store8 _ _)))

theorem exact_tally_lit (s : DeflateStatePtr) (c : UInt8) : ExactM (tally_lit s c) := by
  cases s with
  | none =>
    unfold tally_lit
    repeat' first
      | exact exact_put_symbol_byte _ _
      | x_step
  | some ref =>
    cases ref
    unfold tally_lit
    repeat' first
      | exact exact_put_symbol_byte _ _
      | exact exact_freq_inc _ _
      | x_step

theorem exact_slide_hash (s : DeflateStatePtr) : ExactM (slide_hash s) := by
  unfold slide_hash; x_steps

theorem exact_read_buf (p : ZStreamPtr) (buf : BPtr) (n : UInt32) : ExactM (read_buf p buf n) := by
  unfold read_buf; x_steps

theorem exact_fill_window (s : DeflateStatePtr) : ExactM (fill_window s) := by
  unfold fill_window fillWindowBody slideWindowForFill fillFromStream primeWindowHash fillWindowInsert
    fillWindowCondition clearWindowTail
  repeat' first
    | with_reducible exact exact_updateHashAt _ _ _
    | with_reducible exact exact_slide_hash _
    | with_reducible exact exact_read_buf _ _ _
    | with_reducible exact exact_UPDATE_HASH _ _
    | x_step

end Zlib.Deflate.Universal.Params
