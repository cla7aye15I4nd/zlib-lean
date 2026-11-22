import ZlibF.Proof.«inflate.c.window-state-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual source continuation when inf_leave requests a window update. -/
def leaveWithWindow (c : Ctx) (l : IL) (z : ZStream) : M Int32 := do
  if (← updatewindow c.strm z.next_out (l.out_ - z.avail_out)) != 0 then
    setMode c.st MEM
    return Z_MEM_ERROR
  else
    leaveFinalize c l z

/-- Expose the actual callee and both its return branches. -/
theorem leaveAfterRestore_window {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (update : (s.wsize != 0 || (l.out_ != z.avail_out && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true) :
    leaveAfterRestore c l h = leaveWithWindow c l z h := by
  unfold leaveAfterRestore leaveWithWindow leaveFinalize
  rw [E.strm, E.st]
  simp only [bind_app, ldZ_eq, E.hz, ldI_eq, E.hs, update, ↓reduceIte]

/-- The window-state frame also retains the guarded table clause when its
actual table contents have been retained on the returned heap. -/
theorem WindowStateFrame.tables {h after : Heap} {s state : InflateState}
    (frame : WindowStateFrame s state)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (tables : DataTableInvariant h s) : DataTableInvariant after state := by
  intro active
  have oldActive : DataTableMode s.mode := by rw [frame] at active; exact active
  have safe := tables oldActive
  constructor
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.lengthTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · obtain ⟨ref, off, array, ptr, get, safe⟩ := safe.distanceTable
    exact ⟨ref, off, array, by rw [frame]; exact ptr, by rw [views]; exact get,
      by rw [frame]; exact safe⟩
  · exact safe.lengthLeaves_frame (by rw [frame]) (by rw [frame]) (fun ref _ _ => views ref)

end Zlib.Inflate.Proofs
