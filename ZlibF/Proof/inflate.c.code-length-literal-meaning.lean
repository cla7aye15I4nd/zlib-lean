import ZlibF.Proof.«inflate.c.codelens-step»
import ZlibF.Proof.«inflate.c.lookup-codes»
import ZlibF.Proof.«inftrees.c.code-length-contents»
import ZlibF.Proof.«inffast.c.sig»
import ZlibF.Spec.Functional.Inflate.InflateDecodeTableShort

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inftrees.Proofs (lensOf)
set_option autoImplicit false

/-- A literal store appends exactly its decoded length to the initialized
length prefix. The old header alphabet is not read from the overwritten lens. -/
theorem clWrite_lens_prefix {s : InflateState} {value : UInt16}
    (bound : s.«have».toNat < 320) (inside : s.«have».toNat < s.lens.size) :
    lensOf (fun k => ((clWrite s value).lens.getD k 0).toNat) (clWrite s value).«have».toNat =
      lensOf (fun k => (s.lens.getD k 0).toNat) s.«have».toNat ++ [value.toNat] := by
  have count : (clWrite s value).«have».toNat = s.«have».toNat + 1 := by
    change (s.«have» + 1).toNat = _
    rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
  rw [count, lensOf, List.range_succ, List.map_append, List.map_singleton]
  have stored : ((clWrite s value).lens.getD s.«have».toNat 0).toNat = value.toNat := by
    simp [clWrite, inside]
  rw [stored]
  congr 1
  apply List.map_congr_left
  intro k member
  have smaller : k < s.«have».toNat := List.mem_range.mp member
  change ((s.lens.set! s.«have».toNat value).getD k 0).toNat = (s.lens.getD k 0).toNat
  rw [Zlib.Inftrees.Proofs.getD_set!, ite_eq_right (by omega)]

#print axioms clWrite_lens_prefix
end Zlib.Inflate.Proofs
