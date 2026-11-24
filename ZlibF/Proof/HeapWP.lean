import Std.WP
import ZlibF.Runtime.Ptr

/-! Weakest preconditions for the modeled C monad and frames for read-only calls. -/

namespace C
open Std.WP Lean.Order

namespace HeapWP

/-- The runtime has the same state and fault behavior as this transformer stack. -/
scoped instance : WPMonad M (Heap → Prop) (Fault → Prop) :=
  inferInstanceAs (WPMonad (StateT Heap (Except Fault)) (Heap → Prop) (Fault → Prop))

end HeapWP
open scoped HeapWP

/-- A fault carries its own postcondition and discards the heap. -/
theorem wp_run (m : M α) (Q : α → Heap → Prop) (E : Fault → Prop) (h : Heap) :
    wp m Q E h = match m h with | .ok (x, s) => Q x s | .error e => E e := by
  change pushExcept (fun (x, s) => Q x s) E (m h) = _
  cases m h <;> rfl

/-- An exact read-only result at one heap. The default error postcondition rejects every fault. -/
theorem okOn_iff_triple {m : M α} {h : Heap} {x : α} :
    OkOn h m x ↔ ⦃ fun s => s = h ⦄ m ⦃ fun y s => y = x ∧ s = h ⦄ := by
  constructor
  · intro ok
    exact ⟨fun s hs => by subst s; simp [wp_run, show m h = _ from ok]⟩
  · intro spec
    have post := spec.le_wp h rfl
    cases e : m h with
    | error => simp [wp_run, e] at post
    | ok => simpa [OkOn, wp_run, e, Prod.ext_iff] using post

/-- A successful read leaves every predicate on the input heap available to its caller. -/
theorem OkOn.frame {m : M α} {P : Heap → Prop} {value : Heap → α}
    (ok : ∀ h, P h → OkOn h m (value h)) (F : Heap → Prop) :
    ⦃ fun h => P h ∧ F h ⦄ m ⦃ fun y h => y = value h ∧ F h ⦄ := by
  refine ⟨fun h ⟨hp, hf⟩ => ?_⟩
  rw [wp_run, show m h = _ from ok h hp]
  exact ⟨rfl, hf⟩

/-- A returning indexed read leaves every heap component unchanged. -/
theorem Ptr.index_heap {R T : Type} [Space Heap R T] [Inhabited T]
    {p : Ptr R} {i : Int} {h after : Heap} {v : T}
    (run : Ptr.index p i h = .ok (v, after)) : after = h := by
  unfold Ptr.index at run
  rw [bind_app] at run
  cases added : Ptr.add p i h with
  | error fault => rw [added] at run; cases run
  | ok pair =>
    obtain ⟨q, mid⟩ := pair
    rw [added] at run
    have same : mid = h := by
      unfold Ptr.add at added
      repeat' first | split at added | (cases added <;> rfl)
    subst mid
    change Ptr.load q h = _ at run
    unfold Ptr.load at run
    repeat' first | split at run | (cases run <;> rfl)

/-- Read a live in-bounds element while carrying the caller's heap predicate. -/
theorem Ptr.index_spec {R T : Type} [Space Heap R T] [Inhabited T]
    (ref : R) (off i : Nat) (bs : Array T) (F : Heap → Prop) :
    ⦃ fun s => (Space.get s ref = some bs ∧ off + i < bs.size) ∧ F s ⦄ Ptr.index (.ref ref off) i
    ⦃ fun b s => b = bs[off + i]! ∧ F s ⦄ := by
  apply OkOn.frame
  intro h ⟨hb, hi⟩
  simpa [hi] using Ptr.index_ok hb hi

end C
