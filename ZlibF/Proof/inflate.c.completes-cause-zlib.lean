import ZlibF.Proof.«inflate.c.completes-cause-header»
import ZlibF.Proof.«inflate.c.completes-cause-dynamic»

/-! # inflate.c: the cause rows of a zlib call, all proved -/

namespace Zlib.Inflate.Proofs
set_option autoImplicit false

theorem zlib_cause_rows : ZlibCauseRows :=
  ⟨cause_head_zlib, fun c f r _ => cause_dictid c f r, fun c f r _ => cause_dict c f r,
    fun c f r _ => cause_type_final c f r, cause_dynamic, cause_length_zlib⟩

end Zlib.Inflate.Proofs
