import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.«inflate.c.memory-meta-frame-run»

/-!
# inflate.c: a block-body or trailer trip keeps `in` and the configuration

One trip of the mode loop (`inflate_dispatch`) that starts in a block-body mode (`TYPE` .. `LIT`) or a
trailer mode (`CHECK`, `LENGTH`) never writes the register `in` and never changes the fields `wrap`,
`reqwrap`, `head`, `reqbits` and `wbits` of any decoder record.

The proof is a frame relation composed through the translated source, in the style of the
memory-meta frame. `BodyCfgX k x` says: every successful run of `x` from registers with `in = k`
ends with `in = k`, and the configuration fields of every decoder record are unchanged (a record
neither appears nor disappears). The relation holds for every outcome, including `goto inf_leave`
and `return`. Every callee (`inflate_fast`, `inflate_table`, `inflate_fixed`, the checksums) is
covered by a frame proof about its translated body, not by an assumed contract.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-! ## The relation -/

/-- The configuration fields of a decoder: `wrap`, `reqwrap`, `head`, `reqbits`, `wbits`. -/
def bodyCfgOf (s : InflateState) : Int32 × Int32 × Option GzHeaderRef × UInt32 × UInt32 :=
  (s.wrap, s.reqwrap, s.head, s.reqbits, s.wbits)

/-- The configuration fields of every decoder record, including absent records. -/
def bodyCfgObs (h : Heap) : Nat → Option (Int32 × Int32 × Option GzHeaderRef × UInt32 × UInt32) :=
  fun b => (h.istates b).map bodyCfgOf

/-- A successful run returns a value satisfying `Q` and keeps every configuration field. -/
def BodyCfgH {τ : Type} (Q : τ → Prop) (m : M τ) : Prop :=
  ∀ h v after, m h = .ok (v, after) → Q v ∧ bodyCfgObs after = bodyCfgObs h

/-- A successful run keeps every configuration field. -/
def BodyCfgM {τ : Type} (m : M τ) : Prop :=
  ∀ h v after, m h = .ok (v, after) → bodyCfgObs after = bodyCfgObs h

/-- From registers with `in = k`, every successful run of a mode program, whatever its outcome,
ends with `in = k` and keeps every configuration field. -/
def BodyCfgX {α : Type} (k : UInt32) (x : X α) : Prop :=
  ∀ l, l.in_ = k → BodyCfgH (fun p : Except Ex α × IL => p.2.in_ = k) (runX x l)

/-! ## Composition in `M` -/

theorem bodyCfgH_pure {τ : Type} {Q : τ → Prop} {v : τ} (hv : Q v) : BodyCfgH Q (pure v) := by
  intro h w after run
  cases run
  exact ⟨hv, rfl⟩

theorem bodyCfgH_bind {α β : Type} {Q1 : α → Prop} {Q2 : β → Prop} {m : M α} {f : α → M β}
    (hm : BodyCfgH Q1 m) (hf : ∀ v, Q1 v → BodyCfgH Q2 (f v)) : BodyCfgH Q2 (m >>= f) := by
  intro h w after run
  rw [bind_app] at run
  cases e : m h with
  | error fault => rw [e] at run; cases run
  | ok pair =>
    obtain ⟨v, mid⟩ := pair
    rw [e] at run
    obtain ⟨q1, f1⟩ := hm h v mid e
    obtain ⟨q2, f2⟩ := hf v q1 mid w after run
    exact ⟨q2, f2.trans f1⟩

theorem bodyCfgH_of_M {τ : Type} {m : M τ} (frame : BodyCfgM m) : BodyCfgH (fun _ => True) m :=
  fun h v after run => ⟨trivial, frame h v after run⟩

theorem bodyCfgM_of_H {τ : Type} {Q : τ → Prop} {m : M τ} (frame : BodyCfgH Q m) : BodyCfgM m :=
  fun h v after run => (frame h v after run).2

theorem bodyCfgM_pure {τ : Type} (v : τ) : BodyCfgM (pure v) := by
  intro h w after run
  cases run
  rfl

theorem bodyCfgM_bind {α β : Type} {m : M α} {f : α → M β}
    (hm : BodyCfgM m) (hf : ∀ v, BodyCfgM (f v)) : BodyCfgM (m >>= f) :=
  bodyCfgM_of_H (bodyCfgH_bind (bodyCfgH_of_M hm) (fun v _ => bodyCfgH_of_M (hf v)))

theorem bodyCfgM_ub {α : Type} (message : String) : BodyCfgM (ub message : M α) := by
  intro h v after run
  cases run

theorem bodyCfgM_ite {α : Type} {test : Prop} [Decidable test] {yes no : M α}
    (hy : BodyCfgM yes) (hn : BodyCfgM no) : BodyCfgM (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

/-- A terminating C loop keeps an invariant of its carried locals and the configuration. -/
theorem bodyCfgH_cwhile {σ : Type} (P : σ → Prop) {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ s, P s → BodyCfgH (fun p : Bool × σ => P p.2) (cond s)) (hb : ∀ s, P s → BodyCfgH P (body s))
    (s : σ) (hs : P s) : BodyCfgH P (cwhile cond body s) := by
  have key : ∀ n s, P s → BodyCfgH P (cwhile.go cond body n s) := by
    intro n
    induction n with
    | zero =>
      intro s _ h v after run
      simp only [cwhile.go] at run
      cases run
    | succ n ih =>
      intro s hs h v after run
      simp only [cwhile.go, bind_app] at run
      cases condition : cond s h with
      | error fault => rw [condition] at run; cases run
      | ok pair =>
        obtain ⟨⟨test, middle⟩, heap1⟩ := pair
        rw [condition] at run
        obtain ⟨p1, f1⟩ := hc s hs h (test, middle) heap1 condition
        cases test with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
          cases run
          exact ⟨p1, f1⟩
        | true =>
          simp only [ite_true, bind_app] at run
          cases executed : body middle heap1 with
          | error fault => rw [executed] at run; cases run
          | ok pair =>
            obtain ⟨next, heap2⟩ := pair
            rw [executed] at run
            obtain ⟨p2, f2⟩ := hb middle p1 heap1 next heap2 executed
            obtain ⟨p3, f3⟩ := ih next p2 heap2 v after run
            exact ⟨p3, f3.trans (f2.trans f1)⟩
  exact key fuel s hs

theorem bodyCfgM_cwhile {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (hc : ∀ s, BodyCfgM (cond s)) (hb : ∀ s, BodyCfgM (body s)) (s : σ) :
    BodyCfgM (cwhile cond body s) :=
  bodyCfgM_of_H (bodyCfgH_cwhile (fun _ => True) (fun s _ => bodyCfgH_of_M (hc s))
    (fun s _ => bodyCfgH_of_M (hb s)) s trivial)

theorem bodyCfgM_cdoWhile {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (hb : ∀ s, BodyCfgM (body s)) (hc : ∀ s, BodyCfgM (cond s)) (s : σ) :
    BodyCfgM (cdoWhile body cond s) := by
  have key : ∀ n s, BodyCfgM (cdoWhile.go body cond n s) := by
    intro n
    induction n with
    | zero =>
      intro s h v after run
      simp only [cdoWhile.go] at run
      cases run
    | succ n ih =>
      intro s h v after run
      simp only [cdoWhile.go, bind_app] at run
      cases executed : body s h with
      | error fault => rw [executed] at run; cases run
      | ok pair =>
        obtain ⟨middle, heap1⟩ := pair
        rw [executed] at run
        have first := hb s h middle heap1 executed
        simp only [] at run
        cases condition : cond middle heap1 with
        | error fault => rw [condition] at run; cases run
        | ok pair =>
          obtain ⟨⟨test, next⟩, heap2⟩ := pair
          rw [condition] at run
          have second := hc middle heap1 (test, next) heap2 condition
          cases test with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, pure_app] at run
            cases run
            exact second.trans first
          | true =>
            simp only [ite_true] at run
            exact (ih next heap2 v after run).trans (second.trans first)
  exact key fuel s

theorem bodyCfgM_list_forIn {α β : Type} (values : List α)
    (body : (value : α) → value ∈ values → β → M (ForInStep β))
    (frames : ∀ value membership state, BodyCfgM (body value membership state))
    (initial : β) : BodyCfgM (List.forIn' values initial body) := by
  induction values generalizing initial with
  | nil =>
    simp only [List.forIn'_eq_forIn', List.forIn'_nil]
    exact bodyCfgM_pure _
  | cons head tail ih =>
    simp only [List.forIn'_eq_forIn', List.forIn'_cons]
    refine bodyCfgM_bind (frames head (by simp) initial) (fun decision => ?_)
    cases decision with
    | done result => exact bodyCfgM_pure _
    | yield next =>
      exact ih (fun value membership state => body value (by simp [membership]) state)
        (fun value membership state => frames value (by simp [membership]) state) next

/-! ## Heap writes -/

/-- Replacing one decoder record by one with the same configuration keeps the observation. -/
theorem bodyCfgObs_set {h : Heap} {id : Nat} {old new : InflateState} (get : h.istates id = some old)
    (same : bodyCfgOf new = bodyCfgOf old) :
    bodyCfgObs { h with istates := upd h.istates id (some new) } = bodyCfgObs h := by
  funext b
  show Option.map bodyCfgOf (upd h.istates id (some new) b) = Option.map bodyCfgOf (h.istates b)
  rw [upd_apply]
  split
  · rename_i e
    subst e
    rw [get]
    show some (bodyCfgOf new) = some (bodyCfgOf old)
    rw [same]
  · rfl

theorem bodyCfg_byte_put (h : Heap) (ref : BRef) (array : Array UInt8) :
    bodyCfgObs (Space.put h ref array) = bodyCfgObs h := by
  cases ref <;> simp only [Space.put]
  all_goals first | rfl | (split <;> rfl)

theorem bodyCfg_word_put (h : Heap) (ref : WRef) (array : Array UInt16) :
    bodyCfgObs (Space.put h ref array) = bodyCfgObs h := by
  cases ref with
  | blk b => rfl
  | dstate_bl_count id =>
    simp only [Space.put]
    split <;> rfl
  | istate_lens id =>
    cases get : h.istates id with
    | none => simp only [Space.put, get]
    | some s =>
      simp only [Space.put, get]
      exact bodyCfgObs_set get rfl
  | istate_work id =>
    cases get : h.istates id with
    | none => simp only [Space.put, get]
    | some s =>
      simp only [Space.put, get]
      exact bodyCfgObs_set get rfl

theorem bodyCfg_code_put (h : Heap) (ref : CodeRef) (array : Array Code) :
    bodyCfgObs (Space.put h ref array) = bodyCfgObs h := by
  cases ref with
  | istate_codes id =>
    cases get : h.istates id with
    | none => simp only [Space.put, get]
    | some s =>
      simp only [Space.put, get]
      exact bodyCfgObs_set get rfl
  | st_lenfix => rfl
  | st_distfix => rfl

theorem bodyCfg_stream_put (h : Heap) (r : ZStreamRef) (v : ZStream) :
    bodyCfgObs (r.put h v) = bodyCfgObs h := by
  cases r with
  | tab i =>
    simp only [ZStreamRef.put]
    split <;> rfl
  | in_gzstate_strm i =>
    simp only [ZStreamRef.put]
    split <;> rfl

/-! ## Primitives -/

section pointers
variable {R T : Type} [Space Heap R T]

theorem bodyCfgM_ptr_add (p : Ptr R) (offset : Int) : BodyCfgM (p.add offset) := by
  intro h value after run
  unfold Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

theorem bodyCfgM_ptr_load (p : Ptr R) : BodyCfgM (Ptr.load p : M T) := by
  intro h value after run
  unfold Ptr.load at run
  repeat' first | split at run | (cases run <;> rfl)

theorem bodyCfgM_ptr_index (p : Ptr R) (index : Int) : BodyCfgM (Ptr.index p index : M T) :=
  bodyCfgM_bind (bodyCfgM_ptr_add p index) (fun next => bodyCfgM_ptr_load next)

theorem bodyCfgM_ptr_diff [DecidableEq R] (p q : Ptr R) : BodyCfgM (p.diff q) := by
  intro h value after run
  unfold Ptr.diff at run
  repeat' first | split at run | (cases run <;> rfl)

theorem bodyCfgM_ptr_lt [DecidableEq R] (p q : Ptr R) : BodyCfgM (p.lt q) := by
  intro h value after run
  unfold Ptr.lt at run
  repeat' first | split at run | (cases run <;> rfl)

/-- A typed store keeps the configuration whenever writes to that array space do. -/
theorem bodyCfgM_ptr_store (p : Ptr R) (value : T)
    (writes : ∀ (h : Heap) (ref : R) (array : Array T), bodyCfgObs (Space.put h ref array : Heap) = bodyCfgObs h) :
    BodyCfgM (p.store value) := by
  intro h result after run
  cases p with
  | null => cases run
  | ref ref off =>
    cases get : Space.get h ref with
    | none => simp only [Ptr.store, get] at run; cases run
    | some array =>
      simp only [Ptr.store, get] at run
      split at run
      · cases run
      · split at run
        · rw [Space.modify_eq h ref array _ get] at run
          cases run
          exact writes _ _ _
        · cases run
end pointers

theorem bodyCfgM_store8 (p : BPtr) (value : UInt8) : BodyCfgM (store8 p value) :=
  bodyCfgM_ptr_store p value bodyCfg_byte_put

theorem bodyCfgM_store16 (p : WPtr) (value : UInt16) : BodyCfgM (p.store value) :=
  bodyCfgM_ptr_store p value bodyCfg_word_put

theorem bodyCfgM_storeCode (p : CodePtr) (value : Code) : BodyCfgM (p.store value) :=
  bodyCfgM_ptr_store p value bodyCfg_code_put

theorem bodyCfgM_memcpyB (destination source : BPtr) (count : Nat) :
    BodyCfgM (memcpyB destination source count) := by
  intro h value after run
  cases destination with
  | null => cases run
  | ref dest off =>
    cases source with
    | null => cases run
    | ref src srcOff =>
      cases destGet : (Space.get h dest : Option (Array UInt8)) <;>
        cases srcGet : (Space.get h src : Option (Array UInt8))
      all_goals simp only [memcpyB, Ptr.memcpy, destGet, srcGet] at run
      all_goals first
        | cases run
        | skip
      rename_i array sourceArray
      rw [Space.modify_eq h dest array _ destGet] at run
      repeat' first
        | split at run
        | (cases run <;> exact bodyCfg_byte_put _ _ _)

theorem bodyCfgM_ldS (pointer : InflateStatePtr) : BodyCfgM (ldInflateState pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab zs =>
      rw [ldI_eq] at run
      split at run <;> cases run
      rfl

theorem bodyCfgM_ldZ (pointer : ZStreamPtr) : BodyCfgM (ldZStream pointer) := by
  intro h value after run
  cases pointer with
  | none => cases run
  | some pointer =>
    rw [ldZ_eq] at run
    split at run <;> cases run
    rfl

theorem bodyCfgM_rdS {α : Type} (pointer : InflateStatePtr) (field : InflateState → α) :
    BodyCfgM (rdS pointer field) :=
  bodyCfgM_bind (bodyCfgM_ldS pointer) (fun _ => bodyCfgM_pure _)

theorem bodyCfgM_rdZ {α : Type} (pointer : ZStreamPtr) (field : ZStream → α) :
    BodyCfgM (rdZ pointer field) :=
  bodyCfgM_bind (bodyCfgM_ldZ pointer) (fun _ => bodyCfgM_pure _)

theorem bodyCfgM_stZ (pointer : ZStreamPtr) (v : ZStream) : BodyCfgM (stZStream pointer v) := by
  intro h w after run
  cases pointer with
  | none => cases run
  | some r =>
    rw [stZ_eq] at run
    cases get : r.get h with
    | none => rw [get] at run; cases run
    | some old =>
      rw [get] at run
      cases run
      exact bodyCfg_stream_put h r v

theorem bodyCfgM_wrZ (pointer : ZStreamPtr) (update : ZStream → ZStream) : BodyCfgM (wrZ pointer update) := by
  unfold wrZ
  exact bodyCfgM_bind (bodyCfgM_ldZ pointer) (fun z => bodyCfgM_stZ pointer (update z))

/-- A decoder update that keeps the configuration fields keeps the observation. -/
theorem bodyCfgM_wrS (pointer : InflateStatePtr) (update : InflateState → InflateState)
    (same : ∀ s, bodyCfgOf (update s) = bodyCfgOf s) : BodyCfgM (wrS pointer update) := by
  intro h v after run
  cases pointer with
  | none => cases run
  | some pointer =>
    cases pointer with
    | tab i =>
      rw [wrI_eq] at run
      cases get : h.istates i with
      | none => rw [get] at run; cases run
      | some old =>
        rw [get] at run
        cases run
        exact bodyCfgObs_set get (same old)

/-- The literal load/store pair of the callees (`s = *state; *state = { s with ... }`). -/
theorem bodyCfgM_ld_st (pointer : InflateStatePtr) (update : InflateState → InflateState)
    (same : ∀ s, bodyCfgOf (update s) = bodyCfgOf s) :
    BodyCfgM (ldInflateState pointer >>= fun s => stInflateState pointer (update s)) :=
  bodyCfgM_wrS pointer update same

theorem bodyCfgM_ld_st_bind {β : Type} (pointer : InflateStatePtr) (update : InflateState → InflateState)
    (next : Unit → M β) (same : ∀ s, bodyCfgOf (update s) = bodyCfgOf s) (frame : ∀ u, BodyCfgM (next u)) :
    BodyCfgM (ldInflateState pointer >>= fun s => stInflateState pointer (update s) >>= next) := by
  rw [← memory_meta_frame_bind_assoc]
  exact bodyCfgM_bind (bodyCfgM_ld_st pointer update same) frame

theorem bodyCfgM_setMode (pointer : InflateStatePtr) (mode : UInt32) : BodyCfgM (setMode pointer mode) :=
  bodyCfgM_wrS pointer _ (fun _ => rfl)

theorem bodyCfgM_castI (state : Option StateRef) : BodyCfgM (castInflateState state) := by
  intro h value after run
  unfold castInflateState at run
  repeat' first | split at run | (cases run <;> rfl)

theorem bodyCfgM_strLit (message : String) : BodyCfgM (Zlib.Zutil.strLit message) := by
  intro h value after run
  unfold Zlib.Zutil.strLit strLitRef at run
  repeat' first | split at run | (cases run <;> rfl)

theorem bodyCfgM_setMsg (pointer : ZStreamPtr) (message : String) : BodyCfgM (setMsg pointer message) := by
  unfold setMsg
  exact bodyCfgM_bind (bodyCfgM_strLit _) (fun _ => bodyCfgM_bind (bodyCfgM_ldZ _) (fun _ => bodyCfgM_stZ _ _))

theorem bodyCfgM_badMode (context : Ctx) (message : String) : BodyCfgM (badMode context message) := by
  unfold badMode
  exact bodyCfgM_bind (bodyCfgM_setMsg _ _) (fun _ => bodyCfgM_setMode _ _)

theorem bodyCfgM_hcrcOn (pointer : InflateStatePtr) : BodyCfgM (hcrcOn pointer) :=
  bodyCfgM_bind (bodyCfgM_ldS pointer) (fun _ => bodyCfgM_pure _)

theorem bodyCfgM_orderAt (index : UInt32) : BodyCfgM (orderAt index) := by
  unfold orderAt
  split
  · exact bodyCfgM_pure _
  · exact bodyCfgM_ub _

theorem bodyCfgM_shl32 (value shift : UInt32) : BodyCfgM (shl32 value shift) := by
  unfold shl32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_shr32 (value shift : UInt32) : BodyCfgM (shr32 value shift) := by
  unfold shr32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_shl64 (value : UInt64) (shift : UInt32) : BodyCfgM (shl64 value shift) := by
  unfold shl64
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_shr64 (value : UInt64) (shift : UInt32) : BodyCfgM (shr64 value shift) := by
  unfold shr64
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_chkI32 (value : Int) : BodyCfgM (chkI32 value) := by
  unfold chkI32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_chkI64 (value : Int) : BodyCfgM (chkI64 value) := by
  unfold chkI64
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

/-! ## Checksums -/

set_option hygiene false in
/-- Decomposition of read-only callee code in `M`. Names resolve where it is used. -/
macro "body_cfg_m" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact bodyCfgM_adler_do1 _ _
    | with_reducible exact bodyCfgM_adler_do16 _
    | with_reducible exact bodyCfgM_adler_step _
    | with_reducible exact bodyCfgM_crc_shr64 _ _
    | with_reducible exact bodyCfgM_crc_table _
    | with_reducible exact bodyCfgM_crc_idx1 _ _
    | with_reducible exact bodyCfgM_crc_idx2 _ _ _
    | with_reducible exact bodyCfgM_crc_address _
    | with_reducible exact bodyCfgM_crc_loadWord _
    | with_reducible exact bodyCfgM_crc_word _
    | with_reducible exact bodyCfgM_crc_word_big _
    | with_reducible exact bodyCfgM_crc_wordAt _ _
    | with_reducible exact bodyCfgM_crc_braid _ _
    | with_reducible exact bodyCfgM_crc_braid_big _ _
    | with_reducible exact bodyCfgM_crc_block_little _
    | with_reducible exact bodyCfgM_crc_block_big _
    | with_reducible exact bodyCfgM_crc_byte _ _
    | with_reducible exact bodyCfgM_table_chk32 _
    | with_reducible exact bodyCfgM_table_shl32 _ _
    | with_reducible exact bodyCfgM_table_shr32 _ _
    | with_reducible exact bodyCfgM_table_shl1i32 _
    | with_reducible exact bodyCfgM_table_geta _ _
    | with_reducible exact bodyCfgM_table_seta _ _ _
    | with_reducible exact bodyCfgM_table_storeCode _ _ _
    | with_reducible exact bodyCfgM_table_buildStep _ _
    | with_reducible exact bodyCfgM_fast_shl32 _ _
    | with_reducible exact bodyCfgM_fast_shl64 _ _
    | with_reducible exact bodyCfgM_fast_shr64 _ _
    | with_reducible exact bodyCfgM_fast_chk64 _
    | with_reducible exact bodyCfgM_fast_subn _ _
    | with_reducible exact bodyCfgM_fast_pull _
    | with_reducible exact bodyCfgM_fast_copy1 _
    | with_reducible exact bodyCfgM_fast_copyOp _
    | with_reducible exact bodyCfgM_fast_badData _ _
    | with_reducible exact bodyCfgM_fast_copyMatch _ _
    | with_reducible exact bodyCfgM_fast_dodist _ _
    | with_reducible exact bodyCfgM_fast_dolen _ _
    | with_reducible exact bodyCfgM_fast_body _ _
    | with_reducible exact bodyCfgM_store8 _ _
    | with_reducible exact bodyCfgM_store16 _ _
    | with_reducible exact bodyCfgM_storeCode _ _
    | with_reducible exact bodyCfgM_ldS _
    | with_reducible exact bodyCfgM_ldZ _
    | with_reducible exact bodyCfgM_stZ _ _
    | with_reducible exact bodyCfgM_castI _
    | with_reducible exact bodyCfgM_strLit _
    | with_reducible exact bodyCfgM_ptr_load _
    | with_reducible exact bodyCfgM_ptr_index _ _
    | with_reducible exact bodyCfgM_ptr_add _ _
    | with_reducible exact bodyCfgM_ptr_diff _ _
    | with_reducible exact bodyCfgM_ptr_lt _ _
    | with_reducible exact bodyCfgM_pure _
    | with_reducible exact bodyCfgM_ub _
    | with_reducible (refine bodyCfgM_ld_st_bind _ _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine bodyCfgM_ld_st _ _ (fun _ => ?_))
    | with_reducible (refine bodyCfgM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine bodyCfgM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply bodyCfgM_ite
    | with_reducible (refine bodyCfgM_bind ?_ (fun _ => ?_))
    | rfl)

theorem bodyCfgM_adler_do1 (state : Zlib.Adler32.Locals) (index : Int) :
    BodyCfgM (Zlib.Adler32.do1 state index) := by
  unfold Zlib.Adler32.do1
  exact bodyCfgM_bind (bodyCfgM_ptr_index _ _) (fun _ => bodyCfgM_pure _)

theorem bodyCfgM_adler_do16 (state : Zlib.Adler32.Locals) : BodyCfgM (Zlib.Adler32.do16 state) := by
  unfold Zlib.Adler32.do16
  body_cfg_m

theorem bodyCfgM_adler_step (state : Zlib.Adler32.Locals) : BodyCfgM (Zlib.Adler32.stepByte state) := by
  unfold Zlib.Adler32.stepByte
  exact bodyCfgM_bind (bodyCfgM_ptr_load _) (fun _ =>
    bodyCfgM_bind (bodyCfgM_ptr_add _ _) (fun _ => bodyCfgM_pure _))

theorem bodyCfgM_adler32_z (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    BodyCfgM (Zlib.Adler32.adler32_z seed buffer length) := by
  unfold Zlib.Adler32.adler32_z Zlib.Adler32.lenPostDec
  body_cfg_m

theorem bodyCfgM_adler32 (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    BodyCfgM (Zlib.Adler32.adler32 seed buffer length) := bodyCfgM_adler32_z seed buffer length.toUInt64

theorem bodyCfgM_crc_whole (seed : UInt64) (buffer : BPtr) (length : UInt64) :
    BodyCfgM (Zlib.Crc32.crc32_z seed buffer length) := by
  intro h result after run
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged seed buffer length h result after run
  rfl

theorem bodyCfgM_crc32 (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    BodyCfgM (Zlib.Crc32.crc32 seed buffer length) := bodyCfgM_crc_whole seed buffer length.toUInt64

theorem bodyCfgM_UPDATE_CHECK (pointer : InflateStatePtr) (seed : UInt64) (buffer : BPtr) (length : UInt32) :
    BodyCfgM (UPDATE_CHECK pointer seed buffer length) := by
  unfold UPDATE_CHECK
  refine bodyCfgM_bind (bodyCfgM_rdS _ _) (fun flags => ?_)
  exact bodyCfgM_ite (bodyCfgM_crc32 _ _ _) (bodyCfgM_adler32 _ _ _)

/-! ## Table construction -/

theorem bodyCfgM_table_chk32 (value : Int) : BodyCfgM (Zlib.Inftrees.chk32 value) := by
  unfold Zlib.Inftrees.chk32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_table_shl32 (value shift : UInt32) : BodyCfgM (Zlib.Inftrees.shl32 value shift) := by
  unfold Zlib.Inftrees.shl32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_table_shr32 (value shift : UInt32) : BodyCfgM (Zlib.Inftrees.shr32 value shift) := by
  unfold Zlib.Inftrees.shr32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_table_shl1i32 (shift : UInt32) : BodyCfgM (Zlib.Inftrees.shl1i32 shift) := by
  unfold Zlib.Inftrees.shl1i32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_table_geta (array : Array UInt16) (index : Nat) : BodyCfgM (Zlib.Inftrees.geta array index) := by
  unfold Zlib.Inftrees.geta
  split
  · exact bodyCfgM_pure _
  · exact bodyCfgM_ub _

theorem bodyCfgM_table_seta (array : Array UInt16) (index : Nat) (value : UInt16) :
    BodyCfgM (Zlib.Inftrees.seta array index value) := by
  unfold Zlib.Inftrees.seta
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_table_storeCode (pointer : CodePtr) (index : Nat) (value : Code) :
    BodyCfgM (Zlib.Inftrees.storeCode pointer index value) :=
  bodyCfgM_bind (bodyCfgM_ptr_add _ _) (fun next => bodyCfgM_storeCode next value)

/-- Fixed-table installation writes only the table pointers and widths. -/
theorem bodyCfgM_inflate_fixed (pointer : InflateStatePtr) : BodyCfgM (Zlib.Inftrees.inflate_fixed pointer) := by
  unfold Zlib.Inftrees.inflate_fixed
  body_cfg_m

theorem bodyCfgM_table_buildStep (context : Zlib.Inftrees.Ctx) (state : Zlib.Inftrees.TS) :
    BodyCfgM (Zlib.Inftrees.buildStep context state) := by
  unfold Zlib.Inftrees.buildStep
  body_cfg_m

/-- The whole dynamic-table constructor writes only word and code arrays. -/
theorem bodyCfgM_inflate_table (kind : UInt32) (lens : WPtr) (count : UInt32)
    (table : CodePtr) (bits : UInt32) (work : WPtr) :
    BodyCfgM (Zlib.Inftrees.inflate_table kind lens count table bits work) := by
  unfold Zlib.Inftrees.inflate_table
  body_cfg_m

/-! ## The fast decoder -/

theorem bodyCfgM_fast_shl32 (value shift : UInt32) : BodyCfgM (Zlib.Inffast.shl32 value shift) := by
  unfold Zlib.Inffast.shl32
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_fast_shl64 (value shift : UInt64) : BodyCfgM (Zlib.Inffast.shl64 value shift) := by
  unfold Zlib.Inffast.shl64
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_fast_shr64 (value shift : UInt64) : BodyCfgM (Zlib.Inffast.shr64 value shift) := by
  unfold Zlib.Inffast.shr64
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_fast_chk64 (value : Int) : BodyCfgM (Zlib.Inffast.chk64 value) := by
  unfold Zlib.Inffast.chk64
  exact bodyCfgM_ite (bodyCfgM_pure _) (bodyCfgM_ub _)

theorem bodyCfgM_fast_subn (pointer : BPtr) (count : UInt32) : BodyCfgM (Zlib.Inffast.subn pointer count) :=
  bodyCfgM_ptr_add _ _

theorem bodyCfgM_fast_pull (state : Zlib.Inffast.L) : BodyCfgM (Zlib.Inffast.pull state) := by
  unfold Zlib.Inffast.pull
  exact bodyCfgM_bind (bodyCfgM_ptr_load _) (fun _ =>
    bodyCfgM_bind (bodyCfgM_ptr_add _ _) (fun _ =>
      bodyCfgM_bind (bodyCfgM_fast_shl64 _ _) (fun _ => bodyCfgM_pure _)))

theorem bodyCfgM_fast_copy1 (state : Zlib.Inffast.L) : BodyCfgM (Zlib.Inffast.copy1 state) := by
  unfold Zlib.Inffast.copy1
  exact bodyCfgM_bind (bodyCfgM_ptr_load _) (fun _ =>
    bodyCfgM_bind (bodyCfgM_ptr_add _ _) (fun _ =>
      bodyCfgM_bind (bodyCfgM_store8 _ _) (fun _ =>
        bodyCfgM_bind (bodyCfgM_ptr_add _ _) (fun _ => bodyCfgM_pure _))))

theorem bodyCfgM_fast_copyOp (state : Zlib.Inffast.L) : BodyCfgM (Zlib.Inffast.copyOp state) :=
  bodyCfgM_cdoWhile bodyCfgM_fast_copy1 (fun _ => bodyCfgM_pure _) state

theorem bodyCfgM_fast_badData (context : Zlib.Inffast.Ctx) (message : String) :
    BodyCfgM (Zlib.Inffast.badData context message) := by
  unfold Zlib.Inffast.badData
  body_cfg_m

theorem bodyCfgM_fast_copyMatch (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.copyMatch context state) := by
  unfold Zlib.Inffast.copyMatch
  body_cfg_m

theorem bodyCfgM_fast_dodist (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.dodist context state) := by
  unfold Zlib.Inffast.dodist
  body_cfg_m

theorem bodyCfgM_fast_dolen (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.dolen context state) := by
  unfold Zlib.Inffast.dolen
  body_cfg_m

theorem bodyCfgM_fast_body (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.inflate_fast_body context state) := by
  unfold Zlib.Inffast.inflate_fast_body
  body_cfg_m

theorem bodyCfgM_ptr_le {R T : Type} [Space Heap R T] [DecidableEq R] (p q : Ptr R) :
    BodyCfgM (p.le q) :=
  bodyCfgM_bind (bodyCfgM_ptr_lt q p) (fun b => bodyCfgM_pure (!b))

theorem bodyCfgM_fast_load64 (p : BPtr) : BodyCfgM (Zlib.Inffast.load64 p) := by
  unfold Zlib.Inffast.load64
  body_cfg_m

theorem bodyCfgM_fast_store64 (out : BPtr) (v : UInt64) : BodyCfgM (Zlib.Inffast.store64 out v) := by
  unfold Zlib.Inffast.store64
  body_cfg_m

set_option hygiene false in
local macro "body_cfg_m_fast_step" : tactic =>
  `(tactic| first
    | with_reducible assumption
    | with_reducible exact bodyCfgM_fast_shl32 _ _
    | with_reducible exact bodyCfgM_fast_shl64 _ _
    | with_reducible exact bodyCfgM_fast_shr64 _ _
    | with_reducible exact bodyCfgM_fast_chk64 _
    | with_reducible exact bodyCfgM_fast_subn _ _
    | with_reducible exact bodyCfgM_memcpyB _ _ _
    | with_reducible exact bodyCfgM_store8 _ _
    | with_reducible exact bodyCfgM_store16 _ _
    | with_reducible exact bodyCfgM_ldS _
    | with_reducible exact bodyCfgM_ldZ _
    | with_reducible exact bodyCfgM_stZ _ _
    | with_reducible exact bodyCfgM_castI _
    | with_reducible exact bodyCfgM_strLit _
    | with_reducible exact bodyCfgM_ptr_load _
    | with_reducible exact bodyCfgM_ptr_index _ _
    | with_reducible exact bodyCfgM_ptr_add _ _
    | with_reducible exact bodyCfgM_ptr_diff _ _
    | with_reducible exact bodyCfgM_ptr_lt _ _
    | with_reducible exact bodyCfgM_pure _
    | with_reducible exact bodyCfgM_ub _
    | with_reducible (refine bodyCfgM_ld_st_bind _ _ _ (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine bodyCfgM_ld_st _ _ (fun _ => ?_))
    | with_reducible (refine bodyCfgM_cwhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible (refine bodyCfgM_cdoWhile (fun _ => ?_) (fun _ => ?_) _)
    | with_reducible apply bodyCfgM_ite
    | with_reducible (refine bodyCfgM_bind ?_ (fun _ => ?_))
    | rfl)

theorem bodyCfgM_fast_copy_back (out : BPtr) (dist len : UInt32) :
    BodyCfgM (Zlib.Inffast.copy_back out dist len) := by
  unfold Zlib.Inffast.copy_back
  repeat' first
    | with_reducible exact bodyCfgM_fast_subn _ _
    | with_reducible exact bodyCfgM_fast_load64 _
    | with_reducible exact bodyCfgM_fast_store64 _ _
    | with_reducible (rintro ⟨_, _⟩; dsimp only)
    | body_cfg_m_fast_step

theorem bodyCfgM_fast_refill64 (l : Zlib.Inffast.L) : BodyCfgM (Zlib.Inffast.refill64 l) := by
  unfold Zlib.Inffast.refill64
  repeat' first
    | with_reducible exact bodyCfgM_fast_load64 _
    | with_reducible exact bodyCfgM_fast_shl64 _ _
    | body_cfg_m_fast_step

theorem bodyCfgM_fast_copyMatch8 (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.copyMatch8 context state) := by
  unfold Zlib.Inffast.copyMatch8
  repeat' first
    | with_reducible exact bodyCfgM_fast_badData _ _
    | with_reducible exact bodyCfgM_fast_copy_back _ _ _
    | with_reducible exact bodyCfgM_fast_subn _ _
    | body_cfg_m_fast_step

theorem bodyCfgM_fast_dodist8 (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.dodist8 context state) := by
  unfold Zlib.Inffast.dodist8
  repeat' first
    | with_reducible exact bodyCfgM_fast_copyMatch8 _ _
    | with_reducible exact bodyCfgM_fast_badData _ _
    | with_reducible exact bodyCfgM_fast_refill64 _
    | body_cfg_m_fast_step

theorem bodyCfgM_fast_dolen8 (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.dolen8 context state) := by
  unfold Zlib.Inffast.dolen8
  repeat' first
    | with_reducible exact bodyCfgM_fast_dodist8 _ _
    | with_reducible exact bodyCfgM_fast_badData _ _
    | with_reducible exact bodyCfgM_fast_refill64 _
    | body_cfg_m_fast_step

theorem bodyCfgM_fast_body8 (context : Zlib.Inffast.Ctx) (state : Zlib.Inffast.L) :
    BodyCfgM (Zlib.Inffast.inflate_fast_body8 context state) := by
  unfold Zlib.Inffast.inflate_fast_body8
  repeat' first
    | with_reducible exact bodyCfgM_fast_dolen8 _ _
    | with_reducible exact bodyCfgM_fast_refill64 _
    | body_cfg_m_fast_step

/-- The whole fast decoder writes the stream, output bytes and `mode`, `hold`, `bits` only. -/
theorem bodyCfgM_inflate_fast (strm : ZStreamPtr) (start : UInt32) :
    BodyCfgM (Zlib.Inffast.inflate_fast strm start) := by
  unfold Zlib.Inffast.inflate_fast
  repeat' first
    | with_reducible exact bodyCfgM_fast_body _ _
    | with_reducible exact bodyCfgM_fast_body8 _ _
    | with_reducible exact bodyCfgM_ptr_le _ _
    | body_cfg_m_fast_step

/-! ## Composition in `X` -/

theorem bodyCfgX_pure {α : Type} (k : UInt32) (v : α) : BodyCfgX k (pure v) := by
  intro l hl h w after run
  cases run
  exact ⟨hl, rfl⟩

theorem bodyCfgX_bind {α β : Type} {k : UInt32} {x : X α} {f : α → X β}
    (hx : BodyCfgX k x) (hf : ∀ v, BodyCfgX k (f v)) : BodyCfgX k (x >>= f) := by
  intro l hl h w after run
  rw [runX_bind] at run
  cases e : runX x l h with
  | error fault => rw [e] at run; cases run
  | ok pair =>
    obtain ⟨⟨d, l1⟩, h1⟩ := pair
    rw [e] at run
    obtain ⟨q1, f1⟩ := hx l hl h (d, l1) h1 e
    cases d with
    | error exit =>
      cases run
      exact ⟨q1, f1⟩
    | ok v =>
      obtain ⟨q2, f2⟩ := hf v l1 q1 h1 w after run
      exact ⟨q2, f2.trans f1⟩

/-- Reading the registers: the continuation may use that the value read has `in = k`. -/
theorem bodyCfgX_get_bind {β : Type} {k : UInt32} {f : IL → X β}
    (hf : ∀ l, l.in_ = k → BodyCfgX k (f l)) : BodyCfgX k ((get : X IL) >>= f) := by
  intro l hl h w after run
  rw [runX_bind, runX_get] at run
  exact hf l hl l hl h w after run

theorem bodyCfgX_get (k : UInt32) : BodyCfgX k (get : X IL) := by
  intro l hl h w after run
  cases run
  exact ⟨hl, rfl⟩

theorem bodyCfgX_set {k : UInt32} (v : IL) (hv : v.in_ = k) : BodyCfgX k (set v : X PUnit) := by
  intro l _ h w after run
  cases run
  exact ⟨hv, rfl⟩

theorem bodyCfgX_modify {k : UInt32} (f : IL → IL) (hf : ∀ l, (f l).in_ = l.in_) :
    BodyCfgX k (modify f : X PUnit) := by
  intro l hl h w after run
  cases run
  exact ⟨(hf l).trans hl, rfl⟩

theorem bodyCfgX_throw {α : Type} (k : UInt32) (exit : Ex) : BodyCfgX k (throw exit : X α) := by
  intro l hl h w after run
  cases run
  exact ⟨hl, rfl⟩

theorem bodyCfgX_lift {α : Type} {k : UInt32} {m : M α} (frame : BodyCfgM m) :
    BodyCfgX k (monadLift m : X α) := by
  intro l hl h w after run
  rw [runX_lift] at run
  cases source : m h with
  | error fault =>
    simp only [source] at run
    cases run
  | ok pair =>
    obtain ⟨v, mid⟩ := pair
    simp only [source] at run
    cases run
    exact ⟨hl, frame _ _ _ source⟩

theorem bodyCfgX_ite {α : Type} {k : UInt32} {test : Prop} [Decidable test] {yes no : X α}
    (hy : BodyCfgX k yes) (hn : BodyCfgX k no) : BodyCfgX k (if test then yes else no) := by
  by_cases selected : test
  · simpa only [selected, ↓reduceIte] using hy
  · simpa only [selected, ↓reduceIte] using hn

/-- The actual X loop wrapper keeps `in` and the configuration, including direct returns and
leave exceptions. -/
theorem bodyCfgX_xwhileBrk {k : UInt32} {cond body : X Bool}
    (hc : BodyCfgX k cond) (hb : BodyCfgX k body) : BodyCfgX k (xwhileBrk cond body) := by
  intro l hl h outcome after run
  let loopCond := fun (current : IL × Stop) => match current.2 with
    | .go => do
      let (result, next) ← runX cond current.1
      pure (match result with
        | .ok value => (value, (next, Stop.go))
        | .error exit => (false, (next, Stop.ex exit)))
    | stop => pure (false, (current.1, stop))
  let loopBody := fun (current : IL × Stop) => do
    let (result, next) ← runX body current.1
    pure (match result with
      | .ok value => (next, if value then Stop.brk else Stop.go)
      | .error exit => (next, Stop.ex exit))
  have condFrame : ∀ current : IL × Stop, current.1.in_ = k →
      BodyCfgH (fun p : Bool × (IL × Stop) => p.2.1.in_ = k) (loopCond current) := by
    intro ⟨current, stop⟩ hk
    cases stop with
    | go =>
      exact bodyCfgH_bind (hc current hk) (fun ⟨r, n⟩ hp => by cases r <;> exact bodyCfgH_pure hp)
    | brk => exact bodyCfgH_pure hk
    | ex exit => exact bodyCfgH_pure hk
  have bodyFrame : ∀ current : IL × Stop, current.1.in_ = k →
      BodyCfgH (fun p : IL × Stop => p.1.in_ = k) (loopBody current) := by
    intro ⟨current, stop⟩ hk
    exact bodyCfgH_bind (hb current hk) (fun ⟨r, n⟩ hp => by cases r <;> exact bodyCfgH_pure hp)
  have loop := bodyCfgH_cwhile (fun s : IL × Stop => s.1.in_ = k) condFrame bodyFrame (l, Stop.go) hl
  let program : M (Except Ex Unit × IL) := do
    let (next, stop) ← cwhile loopCond loopBody (l, Stop.go)
    pure (match stop with
      | .ex exit => (Except.error exit, next)
      | _ => (Except.ok (), next))
  have complete : BodyCfgH (fun p : Except Ex Unit × IL => p.2.in_ = k) program :=
    bodyCfgH_bind loop (fun ⟨n, stop⟩ hp => by cases stop <;> exact bodyCfgH_pure hp)
  have source : runX (xwhileBrk cond body) l = program := rfl
  rw [source] at run
  exact complete h outcome after run

theorem bodyCfgX_xwhile {k : UInt32} {cond : X Bool} {body : X Unit}
    (hc : BodyCfgX k cond) (hb : BodyCfgX k body) : BodyCfgX k (xwhile cond body) :=
  bodyCfgX_xwhileBrk hc (bodyCfgX_bind hb (fun _ => bodyCfgX_pure k false))

theorem bodyCfgX_xdoWhile {k : UInt32} {body : X Unit} {cond : X Bool}
    (hb : BodyCfgX k body) (hc : BodyCfgX k cond) : BodyCfgX k (xdoWhile body cond) :=
  bodyCfgX_bind hb (fun _ => bodyCfgX_xwhile hc hb)

theorem bodyCfgX_xloopBrk {k : UInt32} {body : X Bool} (frame : BodyCfgX k body) :
    BodyCfgX k (xloopBrk body) := bodyCfgX_xwhileBrk (bodyCfgX_pure k true) frame

/-! ## Macros and modes -/

set_option hygiene false in
/-- Decomposition of mode code in `X`. A register write must keep `in`; a decoder write must
keep the configuration fields; both side goals are closed by `rfl` or by the hypothesis that the
registers read have `in = k`. Names resolve where it is used. -/
macro "body_cfg_x" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact bodyCfgX_LOAD _ _ _
    | with_reducible exact bodyCfgX_RESTORE _ _ _
    | with_reducible exact bodyCfgX_INITBITS _
    | with_reducible exact bodyCfgX_PULLBYTE _
    | with_reducible exact bodyCfgX_NEEDBITS _ _
    | with_reducible exact bodyCfgX_BITS _ _
    | with_reducible exact bodyCfgX_DROPBITS _ _
    | with_reducible exact bodyCfgX_BYTEBITS _
    | with_reducible exact bodyCfgX_lookup1 _ _ _
    | with_reducible exact bodyCfgX_lookup2 _ _ _
    | with_reducible exact bodyCfgX_pure _ _
    | with_reducible (refine bodyCfgX_get_bind (fun _ _ => ?_))
    | with_reducible exact bodyCfgX_get _
    | with_reducible (refine bodyCfgX_set _ ?_)
    | with_reducible (refine bodyCfgX_modify _ (fun _ => ?_))
    | with_reducible exact bodyCfgX_throw _ _
    | with_reducible apply bodyCfgX_lift
    | with_reducible exact bodyCfgM_inflate_table _ _ _ _ _ _
    | with_reducible exact bodyCfgM_inflate_fixed _
    | with_reducible exact bodyCfgM_inflate_fast _ _
    | with_reducible exact bodyCfgM_UPDATE_CHECK _ _ _ _
    | with_reducible exact bodyCfgM_crc32 _ _ _
    | with_reducible exact bodyCfgM_adler32 _ _ _
    | with_reducible exact bodyCfgM_ldS _
    | with_reducible exact bodyCfgM_ldZ _
    | with_reducible exact bodyCfgM_rdS _ _
    | with_reducible exact bodyCfgM_rdZ _ _
    | with_reducible exact bodyCfgM_setMode _ _
    | with_reducible exact bodyCfgM_setMsg _ _
    | with_reducible exact bodyCfgM_badMode _ _
    | with_reducible exact bodyCfgM_hcrcOn _
    | with_reducible exact bodyCfgM_orderAt _
    | with_reducible exact bodyCfgM_store8 _ _
    | with_reducible exact bodyCfgM_store16 _ _
    | with_reducible exact bodyCfgM_storeCode _ _
    | with_reducible exact bodyCfgM_memcpyB _ _ _
    | with_reducible exact bodyCfgM_ptr_load _
    | with_reducible exact bodyCfgM_ptr_index _ _
    | with_reducible exact bodyCfgM_ptr_add _ _
    | with_reducible exact bodyCfgM_ptr_diff _ _
    | with_reducible exact bodyCfgM_shl32 _ _
    | with_reducible exact bodyCfgM_shr32 _ _
    | with_reducible exact bodyCfgM_shl64 _ _
    | with_reducible exact bodyCfgM_shr64 _ _
    | with_reducible exact bodyCfgM_chkI32 _
    | with_reducible exact bodyCfgM_chkI64 _
    | with_reducible exact bodyCfgM_wrZ _ _
    | with_reducible exact bodyCfgM_stZ _ _
    | with_reducible exact bodyCfgM_pure _
    | with_reducible (refine bodyCfgM_wrS _ _ (fun _ => ?_))
    | with_reducible (refine bodyCfgM_bind ?_ (fun _ => ?_))
    | with_reducible apply bodyCfgX_xdoWhile
    | with_reducible apply bodyCfgX_xwhile
    | with_reducible apply bodyCfgX_xloopBrk
    | with_reducible apply bodyCfgX_xwhileBrk
    | with_reducible apply bodyCfgX_ite
    | with_reducible (refine bodyCfgX_bind ?_ (fun _ => ?_))
    | rfl
    | assumption
    | split)

theorem bodyCfgX_LOAD (k : UInt32) (strm : ZStreamPtr) (state : InflateStatePtr) : BodyCfgX k (LOAD strm state) := by
  unfold LOAD
  body_cfg_x

theorem bodyCfgX_RESTORE (k : UInt32) (strm : ZStreamPtr) (state : InflateStatePtr) :
    BodyCfgX k (RESTORE strm state) := by
  unfold RESTORE
  body_cfg_x

theorem bodyCfgX_INITBITS (k : UInt32) : BodyCfgX k INITBITS := by
  unfold INITBITS
  body_cfg_x

theorem bodyCfgX_PULLBYTE (k : UInt32) : BodyCfgX k PULLBYTE := by
  unfold PULLBYTE
  body_cfg_x

theorem bodyCfgX_NEEDBITS (k : UInt32) (count : UInt32) : BodyCfgX k (NEEDBITS count) := by
  unfold NEEDBITS
  body_cfg_x

theorem bodyCfgX_BITS (k : UInt32) (count : UInt32) : BodyCfgX k (BITS count) := by
  unfold BITS
  body_cfg_x

theorem bodyCfgX_DROPBITS (k : UInt32) (count : UInt32) : BodyCfgX k (DROPBITS count) := by
  unfold DROPBITS
  body_cfg_x

theorem bodyCfgX_BYTEBITS (k : UInt32) : BodyCfgX k BYTEBITS := by
  unfold BYTEBITS
  body_cfg_x

theorem bodyCfgX_lookup1 (k : UInt32) (context : Ctx) (distance : Bool) : BodyCfgX k (lookup1 context distance) := by
  unfold lookup1
  body_cfg_x

theorem bodyCfgX_lookup2 (k : UInt32) (context : Ctx) (distance : Bool) : BodyCfgX k (lookup2 context distance) := by
  unfold lookup2
  body_cfg_x

theorem bodyCfgX_inflate_DONE (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_DONE context) := by
  unfold inflate_DONE
  body_cfg_x

theorem bodyCfgX_inflate_LENGTH (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_LENGTH context) := by
  unfold inflate_LENGTH
  have continuation0 := bodyCfgX_inflate_DONE context k
  body_cfg_x

theorem bodyCfgX_inflate_CHECK (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_CHECK context) := by
  unfold inflate_CHECK
  have continuation0 := bodyCfgX_inflate_LENGTH context k
  body_cfg_x

theorem bodyCfgX_inflate_LIT (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_LIT context) := by
  unfold inflate_LIT
  body_cfg_x

theorem bodyCfgX_inflate_MATCH (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_MATCH context) := by
  unfold inflate_MATCH
  body_cfg_x

theorem bodyCfgX_inflate_DISTEXT (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_DISTEXT context) := by
  unfold inflate_DISTEXT
  have continuation0 := bodyCfgX_inflate_MATCH context k
  body_cfg_x

theorem bodyCfgX_inflate_DIST (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_DIST context) := by
  unfold inflate_DIST
  have continuation0 := bodyCfgX_inflate_DISTEXT context k
  body_cfg_x

theorem bodyCfgX_inflate_LENEXT (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_LENEXT context) := by
  unfold inflate_LENEXT
  have continuation0 := bodyCfgX_inflate_DIST context k
  body_cfg_x

theorem bodyCfgX_inflate_LEN (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_LEN context) := by
  unfold inflate_LEN
  have continuation0 := bodyCfgX_inflate_LENEXT context k
  body_cfg_x

theorem bodyCfgX_inflate_LEN_ (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_LEN_ context) := by
  unfold inflate_LEN_
  have continuation0 := bodyCfgX_inflate_LEN context k
  body_cfg_x

theorem bodyCfgX_inflate_CODELENS (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_CODELENS context) := by
  unfold inflate_CODELENS
  have continuation0 := bodyCfgX_inflate_LEN_ context k
  body_cfg_x

theorem bodyCfgX_inflate_LENLENS (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_LENLENS context) := by
  unfold inflate_LENLENS
  have continuation0 := bodyCfgX_inflate_CODELENS context k
  body_cfg_x

theorem bodyCfgX_inflate_TABLE (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_TABLE context) := by
  unfold inflate_TABLE
  have continuation0 := bodyCfgX_inflate_LENLENS context k
  body_cfg_x

theorem bodyCfgX_inflate_COPY (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_COPY context) := by
  unfold inflate_COPY
  body_cfg_x

theorem bodyCfgX_inflate_COPY_ (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_COPY_ context) := by
  unfold inflate_COPY_
  have continuation0 := bodyCfgX_inflate_COPY context k
  body_cfg_x

theorem bodyCfgX_inflate_STORED (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_STORED context) := by
  unfold inflate_STORED
  have continuation0 := bodyCfgX_inflate_COPY_ context k
  body_cfg_x

theorem bodyCfgX_inflate_TYPEDO (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_TYPEDO context) := by
  unfold inflate_TYPEDO
  body_cfg_x

theorem bodyCfgX_inflate_TYPE (context : Ctx) (k : UInt32) : BodyCfgX k (inflate_TYPE context) := by
  unfold inflate_TYPE
  have continuation0 := bodyCfgX_inflate_TYPEDO context k
  body_cfg_x

/-! ## The dispatch -/

set_option linter.unusedSimpArgs false in
/-- One trip of the mode loop that starts in a block-body mode (`TYPE` .. `LIT`) or a trailer mode
(`CHECK`, `LENGTH`) and ends normally leaves the register `in` and the configuration fields `wrap`,
`reqwrap`, `head`, `reqbits`, `wbits` of the decoder record unchanged. -/
theorem body_dispatch_frame {c : Ctx} {l l' : IL} {h h' : Heap} {zs : Nat} {s : InflateState}
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (body : TYPE ≤ s.mode ∧ s.mode ≤ LIT ∨ s.mode = CHECK ∨ s.mode = LENGTH)
    (run : runX (inflate_dispatch c) l h = .ok ((.ok (), l'), h')) :
    l'.in_ = l.in_ ∧ ∃ s', h'.istates zs = some s' ∧ s'.wrap = s.wrap ∧ s'.reqwrap = s.reqwrap ∧
      s'.head = s.head ∧ s'.reqbits = s.reqbits ∧ s'.wbits = s.wbits := by
  have read : runX (monadLift (rdS c.st (fun x : InflateState => x.mode)) : X UInt32) l h =
      .ok ((.ok s.mode, l), h) := by
    apply runX_lift_ok
    rw [st, rdI_eq, hs]
  have modes : s.mode = TYPE ∨ s.mode = TYPEDO ∨ s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY ∨
      s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS ∨ s.mode = LEN_ ∨ s.mode = LEN ∨
      s.mode = LENEXT ∨ s.mode = DIST ∨ s.mode = DISTEXT ∨ s.mode = MATCH ∨ s.mode = LIT ∨
      s.mode = CHECK ∨ s.mode = LENGTH := by
    have range := body
    simp only [← UInt32.toNat_inj] at range ⊢
    simp [TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
      DISTEXT, MATCH, LIT, CHECK, LENGTH, UInt32.le_iff_toNat_le] at range ⊢
    omega
  have frame : l'.in_ = l.in_ ∧ bodyCfgObs h' = bodyCfgObs h := by
    unfold inflate_dispatch at run
    rw [runX_bind, read] at run
    rcases modes with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e | e
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_TYPE c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_TYPEDO c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_STORED c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_COPY_ c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_COPY c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_TABLE c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_LENLENS c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_CODELENS c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_LEN_ c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_LEN c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_LENEXT c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_DIST c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_DISTEXT c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_MATCH c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_LIT c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_CHECK c l.in_ l rfl h _ h' run
    · with_reducible simp [e, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
        TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST,
        DISTEXT, MATCH, LIT, CHECK, LENGTH] at run
      exact bodyCfgX_inflate_LENGTH c l.in_ l rfl h _ h' run
  obtain ⟨regs, observed⟩ := frame
  refine ⟨regs, ?_⟩
  have atZs : Option.map bodyCfgOf (h'.istates zs) = Option.map bodyCfgOf (h.istates zs) :=
    congrFun observed zs
  rw [hs] at atZs
  cases get : h'.istates zs with
  | none =>
    rw [get] at atZs
    cases atZs
  | some s' =>
    rw [get] at atZs
    have fields : bodyCfgOf s' = bodyCfgOf s := Option.some.inj atZs
    exact ⟨s', rfl, congrArg (·.1) fields, congrArg (·.2.1) fields, congrArg (·.2.2.1) fields,
      congrArg (·.2.2.2.1) fields, congrArg (·.2.2.2.2) fields⟩

#print axioms body_dispatch_frame

end Zlib.Inflate.Proofs
