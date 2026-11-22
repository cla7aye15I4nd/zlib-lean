import ZlibF.Proof.«gzlib.c.simple»
import ZlibF.Proof.«gzfs.oracle»

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- The result and the world of `lseek(fd, off, whence)` (it does not look at the heap). -/
def lseekRes (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) : Int64 × Fs :=
  match fsLseek fd off wh w Heap.empty with
  | .ok (r, _) => r
  | .error _ => (-1, w)

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

theorem fsLseek_pure (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) :
    ∃ x, fsLseek fd off wh w = (pure x : M (Int64 × Fs)) :=
  Zlib.GzFs.Proofs.fsLseek_pure fd off wh w

theorem fsLseek_eq (fd : Int32) (off : Int64) (wh : Int32) (w : Fs) (h : Heap) :
    fsLseek fd off wh w h = .ok (lseekRes fd off wh w, h) := by
  obtain ⟨x, hx⟩ := fsLseek_pure fd off wh w
  unfold lseekRes
  rw [hx]
  rfl

theorem G_bind_app {α β : Type} (m : G α) (f : α → G β) (fs : Fs) (h : Heap) :
    (m >>= f) fs h = match m fs h with | .ok ((a, fs1), h1) => f a fs1 h1 | .error e => .error e := by
  simp only [bind, StateT.bind]
  cases hm : m fs h with
  | error e => rfl
  | ok v => obtain ⟨⟨a, fs1⟩, h1⟩ := v; rfl

theorem G_pure_app {α : Type} (a : α) (fs : Fs) (h : Heap) : (pure a : G α) fs h = .ok ((a, fs), h) := rfl

theorem G_lift_app {α : Type} (m : M α) (fs : Fs) (h : Heap) :
    (StateT.lift m : G α) fs h = match m h with | .ok (a, h1) => .ok ((a, fs), h1) | .error e => .error e := rfl

/-- Evaluate a straight-line `G` computation on a `gz_state` record: the lifts, the binds, the field accesses and the
file calls. -/
macro "ggsimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, G_bind_app, G_pure_app, G_lift_app,
    bind_app, pure_app, ldS_eq, updS_eq, updX_eq, ldZ_eq, updZ_eq, castState_hnd, fsLseek_eq, $ts,*])

/-- `gzrewind` on a handle that satisfies the invariant. -/
theorem gzrewind_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (fs : Fs) :
    gzrewind (hnd gs) fs h =
      if s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR) then .ok ((-1, fs), h)
      else if (lseekRes s.fd s.start SEEK_SET fs).1 = -1 then .ok ((-1, (lseekRes s.fd s.start SEEK_SET fs).2), h)
      else .ok ((0, (lseekRes s.fd s.start SEEK_SET fs).2), setS (freeStr h s.msg) gs (resetRec s)) := by
  have hs := hG.hs
  unfold gzrewind
  by_cases hc : s.mode ≠ GZ_READ ∨ (s.err ≠ Z_OK ∧ s.err ≠ Z_BUF_ERROR)
  · ggsimp [hs, hc]
  · by_cases hl : (lseekRes s.fd s.start SEEK_SET fs).1 = -1
    · ggsimp [hs, hc, hl]
    · ggsimp [hs, hc, hl, gz_reset_run hG]




/-- `gzrewind(NULL)` returns -1; the world and the heap are unchanged. No precondition. -/
theorem gzrewind_null (fs : Fs) (h : Heap) : gzrewind none fs h = .ok ((-1, fs), h) := rfl

/-! ## gzoffset64, gzoffset -/

/-- `gzoffset64(NULL)` returns -1; the world and the heap are unchanged. No precondition. -/
theorem gzoffset64_null (fs : Fs) (h : Heap) : gzoffset64 none fs h = .ok ((-1, fs), h) := rfl

/-- `gzoffset` is `gzoffset64` (`z_off_t` is `long`, so the range check `ret == (z_off_t)ret` always holds). -/
theorem gzoffset_eq (file : GzFilePtr) (fs : Fs) (h : Heap) : gzoffset file fs h = gzoffset64 file fs h := by
  unfold gzoffset
  simp only [G_bind_app]
  cases hh : gzoffset64 file fs h with
  | error e => rfl
  | ok v => obtain ⟨⟨a, fs1⟩, h1⟩ := v; simp [G_pure_app]

end Zlib.Gzlib.Proofs
