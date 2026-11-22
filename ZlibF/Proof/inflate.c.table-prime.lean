import ZlibF.Proof.«inflate.c.codelens-invariant»
import ZlibF.Proof.«inflate.c.misc2»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Updating the private bit buffer retains every actual code-array view. -/
theorem code_views_set_bits {h : Heap} {zs : Nat} {s : InflateState}
    (state : h.istates zs = some s) (hold : UInt64) (bits : UInt32) (ref : CodeRef) :
    (Space.get (setI h zs { s with hold, bits }) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp [Space.get, state]
    · simp [Space.get, setI, upd_ne _ _ _ _ same]
  | st_lenfix => rfl
  | st_distfix => rfl

/-- Both guarded table clauses survive an actual private bit-buffer update.
No table contract is assumed for a callee. -/
theorem table_clauses_set_bits {h : Heap} {zs : Nat} {s : InflateState}
    (state : h.istates zs = some s) (hold : UInt64) (bits : UInt32)
    (data : DataTableInvariant h s) (codes : CodeLengthInvariant zs s) :
    DataTableInvariant (setI h zs { s with hold, bits }) { s with hold, bits } ∧
      CodeLengthInvariant zs { s with hold, bits } := by
  refine ⟨?_, codes⟩
  intro active
  have tables := data active
  constructor
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := tables.lengthTable
    exact ⟨ref, offset, array, pointer, by rw [code_views_set_bits state]; exact get, safe⟩
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := tables.distanceTable
    exact ⟨ref, offset, array, pointer, by rw [code_views_set_bits state]; exact get, safe⟩
  · exact tables.lengthLeaves_frame rfl rfl (fun ref _ _ => code_views_set_bits state _ _ ref)

end Zlib.Inflate.Proofs
