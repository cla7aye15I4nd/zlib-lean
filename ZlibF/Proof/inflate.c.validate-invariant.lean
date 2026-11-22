import ZlibF.Proof.«inflate.c.header-default»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Toggling validation retains every actual code-array view. -/
theorem validate_code_views {h : Heap} {zs : Nat} {s : InflateState}
    (get : h.istates zs = some s) (check : Int32) (ref : CodeRef) :
    (Space.get (setI h zs (validateState check s)) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp only [Space.get, setI_istates_same, get, Option.map_some]
      rfl
    · simp [Space.get, setI, upd_ne _ _ _ _ same]
  | st_lenfix => rfl
  | st_distfix => rfl

end Zlib.Inflate.Proofs
