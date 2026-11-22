import ZlibF.Proof.«inflate.c.buffer-frame-compose»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Replacing a writable byte view by an equally sized array changes no
object outside that entire view. This is a coarse frame used before the
source proof narrows writes to the caller's output interval. -/
theorem byte_view_full_buffer_frame
    {h : Heap} {dest : BRef} {old array : Array UInt8}
    (get : Space.get h dest = some old)
    (write : Space.ro h dest = false)
    (size : array.size = old.size) :
    BufferFrame h (Space.put h dest array) (fun _ => False)
      [⟨.ref dest 0, old.size⟩] := by
  have restored : restoreRegions h (Space.put h dest array)
      [⟨.ref dest 0, old.size⟩] = h := by
    simp only [restoreRegions, List.foldl_cons, List.foldl_nil,
      get, byte_view_put_put get write array old,
      byte_view_put_self get write]
  refine ⟨?_, ?_⟩
  · rw [restored]
    simp only [Frame, Nat.le_refl, true_and]
    intro b live unchanged
    repeat' constructor <;> rfl
  · intro region member ref off beforeArray pointer getRef
    simp only [List.mem_singleton] at member
    subst region
    cases pointer
    have beforeEq : beforeArray = old := by
      rw [get] at getRef
      cases getRef
      rfl
    subst beforeArray
    refine ⟨array, byte_view_get_put get write array, size, ?_⟩
    intro j within outside
    exfalso
    apply outside
    exact ⟨⟨.ref dest 0, old.size⟩, by simp,
      0, rfl, Nat.zero_le _, by simpa using within⟩

#print axioms byte_view_full_buffer_frame

end Zlib.Inflate.Proofs
