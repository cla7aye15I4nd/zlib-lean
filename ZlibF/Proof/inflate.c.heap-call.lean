import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem heapCall_of_actual_run {α : Type} {program : M α} {h after : Heap} {value : α}
    (run : C.run program h = .ok (value, after)) (fs : Zlib.GzFs.Fs) :
    heapCall program fs h = .ok ((value, fs), after) := by
  change program h = .ok (value, after) at run
  simp only [heapCall, run]

end Zlib.Inflate.Proofs
