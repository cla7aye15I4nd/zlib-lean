import ZlibF.Proof.«crc32.c»
import ZlibF.Proof.LibcBorrowLoops
import Init.Data.Range.Lemmas
import ZlibF.Zlib.«adler32.c»
import ZlibF.Zlib.«crc32.c»

/-! Borrow metadata preservation by the actual checksum read loops. -/
set_option maxRecDepth 10000
namespace C.LibcBorrow

/-- Array indexing is a read, including every supported static reference. -/
theorem stable_ptr_index {R T : Type} [Space Heap R T] (p : Ptr R) (k : Int) :
    StableM (Ptr.index p k : M T) := by
  unfold Ptr.index
  exact StableM.bind (stable_ptr_add _ _) (fun _ => stable_ptr_load _)

macro "borrow_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact StableM.pure _
    | exact StableM.ub _
    | with_reducible exact stable_load8 _
    | with_reducible exact stable_index8 _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible exact stable_ptr_index _ _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.cdoWhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | intro x
    | dsimp only)

open Zlib.Adler32 in
theorem stable_adler_do1 (s : Locals) (i : Int) : StableM (do1 s i) := by
  unfold do1
  borrow_steps

open Zlib.Adler32 in
theorem stable_adler_do16 (s : Locals) : StableM (do16 s) := by
  unfold do16
  repeat' first | with_reducible exact stable_adler_do1 _ _ | with_reducible apply StableM.bind | intro x

open Zlib.Adler32 in
theorem stable_adler_stepByte (s : Locals) : StableM (stepByte s) := by
  unfold stepByte
  borrow_steps

open Zlib.Adler32 in
theorem stable_adler32_z (v : UInt64) (p : BPtr) (n : UInt64) : StableM (adler32_z v p n) := by
  unfold adler32_z
  repeat' first
    | with_reducible exact stable_adler_do16 _
    | with_reducible exact stable_adler_stepByte _
    | (unfold lenPostDec; exact StableM.pure _)
    | with_reducible exact StableM.pure _
    | with_reducible exact stable_index8 _ _
    | with_reducible exact stable_ptr_add _ _
    | with_reducible apply StableM.cwhile
    | with_reducible apply StableM.cdoWhile
    | with_reducible apply StableM.ite
    | with_reducible apply StableM.bind
    | intro x
    | dsimp only

open Zlib.Adler32 in
theorem stable_adler32 (v : UInt64) (p : BPtr) (n : UInt32) : StableM (adler32 v p n) :=
  stable_adler32_z _ _ _

open Zlib.Crc32 in
theorem stable_crc32_z (v : UInt64) (p : BPtr) (n : UInt64) : StableM (crc32_z v p n) := by
  intro h val after hr
  cases Zlib.Crc32.Proofs.crc32_z_heap_unchanged v p n h val after hr
  rfl

open Zlib.Crc32 in
theorem stable_crc32 (v : UInt64) (p : BPtr) (n : UInt32) : StableM (crc32 v p n) :=
  stable_crc32_z _ _ _

#print axioms stable_adler32
#print axioms stable_crc32
end C.LibcBorrow
