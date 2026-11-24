import Lean2C.OriginalUncompressRefill

/-! Output-address independence of the dynamic Huffman table builder. -/
namespace Lean2C.OriginalUncompress.Refill
open C Zlib.Inftrees
set_option autoImplicit false

/-- Rebinding the automatic stream's output field leaves this operation's
value or fault unchanged, and changes only that field in its result heap. -/
def Memory {α : Type} (k : Nat) (p : BPtr) (m : M α) : Prop :=
  ∀ h, m (heap k p h) = mapped id (heap k p) (m h)

namespace Tables

private theorem loop {α : Type} {k : Nat} {p : BPtr} {cond : α → M (Bool × α)} {body : α → M α}
    (test : ∀ v, Memory k p (cond v)) (step : ∀ v, Memory k p (body v)) (v : α) :
    Memory k p (cwhile cond body v) := by
  intro h
  exact while_map id (heap k p) cond body test step v h

private theorem doLoop {α : Type} {k : Nat} {p : BPtr} {cond : α → M (Bool × α)} {body : α → M α}
    (step : ∀ v, Memory k p (body v)) (test : ∀ v, Memory k p (cond v)) (v : α) :
    Memory k p (cdoWhile body cond v) := by
  unfold cdoWhile
  induction fuel generalizing v with
  | zero => intro; rfl
  | succ n ih =>
    rw [cdoWhile.go]
    apply memBind (step v)
    intro a
    apply memBind (test a)
    rintro ⟨selected, b⟩
    cases selected with
    | false => intro; rfl
    | true => exact ih b

private theorem seq {α β : Type} {k : Nat} {p : BPtr} {a : M α} {f : α → M β}
    (first : Memory k p a) (next : ∀ v, Memory k p (f v)) : Memory k p (a >>= f) := memBind first next

private theorem pureM {α : Type} (k : Nat) (p : BPtr) (v : α) : Memory k p (pure v) := fun _ => rfl
private theorem ubM {α : Type} (k : Nat) (p : BPtr) (why : String) : Memory k p (ub why : M α) := fun _ => rfl

private theorem choice {α : Type} {k : Nat} {p : BPtr} {test : Prop} [Decidable test] {a b : M α}
    (left : Memory k p a) (right : Memory k p b) : Memory k p (if test then a else b) := by
  split <;> assumption

/-- The two element types manipulated by inflate_table live in arrays
disjoint from the stream record table, including the decoder's own arrays. -/
private class ArrayFields (R : Type) (T : outParam Type) [Space Heap R T] : Prop where
  get : ∀ k p h (r : R), (Space.get (heap k p h) r : Option (Array T)) = Space.get h r
  ro : ∀ k p h (r : R), Space.ro (heap k p h) r = Space.ro h r
  modify : ∀ k p h (r : R) (f : Array T → Array T),
    Space.modify (heap k p h) r f = heap k p (Space.modify h r f)

private instance : ArrayFields WRef UInt16 where
  get _ _ _ r := by cases r <;> rfl
  ro _ _ _ r := by cases r <;> rfl
  modify _ _ _ r _ := by cases r <;> rfl

private instance : ArrayFields CodeRef Code where
  get _ _ _ r := by cases r <;> rfl
  ro _ _ _ r := by cases r <;> rfl
  modify _ _ _ r _ := by cases r <;> rfl

section pointers
variable {R T : Type} [Space Heap R T] [ArrayFields R T]

private theorem add (k : Nat) (p : BPtr) (q : Ptr R) (i : Int) : Memory k p (q.add i) := by
  intro h
  by_cases zero : i = 0
  · simp only [Ptr.add, zero, ↓reduceIte]; rfl
  cases q with
  | null => simp only [Ptr.add, zero, ↓reduceIte]; rfl
  | ref r n =>
    simp only [Ptr.add, zero, ↓reduceIte, ArrayFields.get]
    cases Space.get h r with
    | none => rfl
    | some a => dsimp only; split <;> rfl

private theorem loadP (k : Nat) (p : BPtr) (q : Ptr R) : Memory k p q.load := by
  intro h
  cases q with
  | null => rfl
  | ref r n =>
    simp only [Ptr.load, ArrayFields.get]
    cases Space.get h r with
    | none => rfl
    | some a => dsimp only; split <;> rfl

private theorem index (k : Nat) (p : BPtr) (q : Ptr R) (i : Int) : Memory k p (q.index i) :=
  seq (add k p q i) (loadP k p)

private theorem store (k : Nat) (p : BPtr) (q : Ptr R) (v : T) : Memory k p (q.store v) := by
  intro h
  cases q with
  | null => rfl
  | ref r n =>
    simp only [Ptr.store, ArrayFields.get, ArrayFields.ro, ArrayFields.modify]
    cases Space.get h r with
    | none => rfl
    | some a => dsimp only; repeat' first | split | rfl

private theorem diff [DecidableEq R] (k : Nat) (p : BPtr) (a b : Ptr R) : Memory k p (a.diff b) := by
  intro h
  cases a <;> cases b <;> try rfl
  rename_i r i s j
  simp only [Ptr.diff, ArrayFields.get]
  by_cases same : r = s
  · simp only [same, ↓reduceIte]
    cases Space.get h s with
    | none => rfl
    | some arr => dsimp only; repeat' first | split | rfl
  · simp only [same, ↓reduceIte]; rfl

end pointers

theorem word_add (k : Nat) (p : BPtr) (q : WPtr) (i : Int) : Memory k p (q.add i) := add k p q i
theorem word_index (k : Nat) (p : BPtr) (q : WPtr) (i : Int) : Memory k p (q.index i) := index k p q i
theorem word_store (k : Nat) (p : BPtr) (q : WPtr) (v : UInt16) : Memory k p (q.store v) := store k p q v

private theorem storeCodeM (k : Nat) (p : BPtr) (q : CodePtr) (i : Nat) (v : Code) : Memory k p (storeCode q i v) :=
  seq (add k p _ _) (fun _ => store k p _ _)

private theorem getA (k : Nat) (p : BPtr) (a : Array UInt16) (i : Nat) : Memory k p (geta a i) := by
  intro h; unfold geta; cases a[i]? <;> rfl
private theorem setA (k : Nat) (p : BPtr) (a : Array UInt16) (i : Nat) (v : UInt16) : Memory k p (seta a i v) := by
  intro h; unfold seta; split <;> rfl
private theorem signed (k : Nat) (p : BPtr) (i : Int) : Memory k p (chk32 i) := by
  intro h; unfold chk32; split <;> rfl
private theorem left (k : Nat) (p : BPtr) (v n : UInt32) : Memory k p (shl32 v n) := by
  intro h; unfold shl32; split <;> rfl
private theorem right (k : Nat) (p : BPtr) (v n : UInt32) : Memory k p (shr32 v n) := by
  intro h; unfold shr32; split <;> rfl
private theorem signedLeft (k : Nat) (p : BPtr) (n : UInt32) : Memory k p (shl1i32 n) := by
  intro h; unfold shl1i32; split <;> rfl

local macro "table_steps" : tactic =>
  `(tactic| repeat' first
    | with_reducible exact signed _ _ _
    | with_reducible exact left _ _ _ _
    | with_reducible exact right _ _ _ _
    | with_reducible exact signedLeft _ _ _
    | with_reducible exact getA _ _ _ _
    | with_reducible exact setA _ _ _ _ _
    | with_reducible exact storeCodeM _ _ _ _ _
    | with_reducible exact store _ _ _ _
    | with_reducible exact loadP _ _ _
    | with_reducible exact index _ _ _ _
    | with_reducible exact add _ _ _ _
    | with_reducible exact diff _ _ _ _
    | with_reducible exact pureM _ _ _
    | with_reducible exact ubM _ _ _
    | with_reducible refine loop (fun _ => ?_) (fun _ => ?_) _
    | with_reducible refine doLoop (fun _ => ?_) (fun _ => ?_) _
    | with_reducible apply choice
    | with_reducible refine seq ?_ (fun _ => ?_))

private theorem step (k : Nat) (p : BPtr) (c : Zlib.Inftrees.Ctx) (s : TS) : Memory k p (buildStep c s) := by
  unfold buildStep
  table_steps

/-- Every histogram, symbol-sort and table emission step is insensitive to
the output cursor, including each partial write before a returning error. -/
theorem build (k : Nat) (p : BPtr) (kind : UInt32) (lens : WPtr) (count : UInt32)
    (tab : CodePtr) (width : UInt32) (work : WPtr) : Memory k p (inflate_table kind lens count tab width work) := by
  unfold inflate_table
  table_steps <;> exact step k p _ _

#print axioms build
end Tables
end Lean2C.OriginalUncompress.Refill
