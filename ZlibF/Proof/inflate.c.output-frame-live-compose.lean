import ZlibF.Proof.«inflate.c.default-dispatch-output-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Whole-object frames compose when actual execution retains every
previously live object. No per-table shape conclusion is inferred. -/
theorem frame_trans_live
    {first second third : Heap} {changed : Nat → Prop}
    (left : Frame first second changed) (right : Frame second third changed)
    (liveNext : ∀ b, first.live b → second.live b) : Frame first third changed := by
  obtain ⟨staticL, allocL, garbageL, nextL, countL, slotsL⟩ := left
  obtain ⟨staticR, allocR, garbageR, nextR, countR, slotsR⟩ := right
  refine ⟨staticL.trans staticR, allocL.trans allocR, garbageL.trans garbageR,
    Nat.le_trans nextL nextR, Nat.le_trans countL countR, ?_⟩
  intro b live outside
  obtain ⟨bL, wL, sL, hL, dL, iL, gL, rL⟩ := slotsL b live outside
  obtain ⟨bR, wR, sR, hR, dR, iR, gR, rR⟩ :=
    slotsR b (liveNext b live) outside
  exact ⟨bR.trans bL, wR.trans wL, sR.trans sL, hR.trans hL,
    dR.trans dL, iR.trans iL, gR.trans gL, rR.trans rL⟩

end Zlib.Inflate.Proofs
