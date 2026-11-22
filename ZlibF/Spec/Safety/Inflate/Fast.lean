import ZlibF.Spec.Common.Inflate.InflateFast

/-!
# Goals of the fast decoder

Safety of one actual fast-decoder iteration and of the whole fast call, stated over
`ZlibF/Spec/Common/Inflate/InflateFast.lean`.
-/

namespace Zlib.Inffast.Spec
open C Zlib.Inffast

/-- Safety and progress of the actual fast body on every concrete permitted state. -/
def Goal.step_safe : Prop :=
  ∀ (e : Proofs.Env) (c : Ctx) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
      (l : L) (i o : Nat),
    StepPre e c A l i o →
    ∃ l' h', C.run (inflate_fast_body c l) (e.heap A msg mode) = .ok (l', h') ∧
      StepPost e A msg mode i o l' h'

/-- Safety, termination, frame and exact register writeback of the actual whole fast decoder.
No body/callee contract is a hypothesis. The complete format-refinement goal is separate. -/
def Goal.fast_safe : Prop :=
  ∀ e : Proofs.Env, ∃ after,
    C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧ FastPost e after

end Zlib.Inffast.Spec
