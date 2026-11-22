import ZlibF.Proof.«gzlib.c.error-inv-premises»
import ZlibF.Proof.«gzwrite.c.init»
import ZlibF.Proof.«gzwrite.c.comp»
import ZlibF.Proof.«gzwrite.c.zero»
import ZlibF.Proof.«gzwrite.c.write»
import ZlibF.Proof.«gzwrite.c.write-calls»
import ZlibF.Proof.«gzwrite.c.flush-params»
import ZlibF.Proof.«gzwrite.c.close»
import ZlibF.Proof.«gzwrite.c.printf»
import ZlibF.Spec.Safety.GzSafety

/-!
# gz write side: the write lemmas without the `gz_error` premises

The write-side theorems of `gzwrite.c.*` take the premises `GzErrorSpec` and `GzErrorOwn`, the facts of
`gz_error`. Both are proved (`gzwrite_gzErrorSpec_holds`, `gzwrite_gzErrorOwn_holds` in `gzlib.c.error-inv-premises`,
from `GzInv.gz_error`). This file applies them, and states each write lemma with no premise on `gz_error`, over the definitions of
`gz.inv-model`.

`gzclose_w_step` is stated with `GzCloseSafe` (`ZlibF/Spec/Safety/GzSafety.lean`); `gzclose_w_step_of` is its
written-out form, with `GzRead.Close.Released`, which is `GzReleased` by definition (`gzReleased_eq_close_released`).
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
set_option autoImplicit false

/-- **`gz_init`** (`gz_init_safe`): allocates `in`, `out` and the deflate state, or frees what it
allocated and records `Z_MEM_ERROR`. -/
theorem gz_init_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size = 0) :
    RunSafe (Zlib.Gzwrite.gz_init (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  Zlib.Gzwrite.SafeInit.gz_init_safe_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i h fs s inv hfs hm hsz

/-- **`gz_comp`** (`gz_comp_safe`), for `0 ≤ flush ≤ 5`. -/
theorem gz_comp_safe (i : Nat) (flush : Int32) (src : Region) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInvUpToInput h i s src) (hfs : FileSystem fs) (hsz : s.size ≠ 0)
    (hflush : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5) :
    RunSafe (Zlib.Gzwrite.gz_comp (gzSt i) flush) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧
      GzPost h i s [] fs' after (fun h' i' s' =>
        if r = 0 then GzInvUpToInput h' i' s' src else GzInvUpToInputWeak h' i' s' src) :=
  gz_comp_safe_of' gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i flush src h fs s inv hfs hsz hflush

/-- **`gz_zero`** (`gz_zero_safe`). -/
theorem gz_zero_safe (i : Nat) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE) (hsz : s.size ≠ 0) :
    RunSafe (Zlib.Gzwrite.gz_zero (gzSt i)) fs h True fun r fs' after =>
      (r = 0 ∨ r = -1) ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  gz_zero_safe_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i h fs s inv hfs hm hsz

/-- **`gz_write`** (`gz_write_safe`). Relies on patch 0004 (gzwrite position overflow). -/
theorem gz_write_safe (i : Nat) (buf : BPtr) (len : UInt64) (h : Heap) (fs : Fs) (s : GzState)
    (inv : GzInv h i s) (hfs : FileSystem fs) (hm : s.mode = GZ_WRITE)
    (hbuf : len = 0 ∨ GzRange h i s buf len.toNat false) :
    RunSafe (Zlib.Gzwrite.gz_write (gzSt i) buf len) fs h True fun r fs' after =>
      r.toNat ≤ len.toNat ∧ FdsKept fs fs' ∧ GzPost h i s [] fs' after GzInv :=
  gz_write_safe_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i buf len h fs s inv hfs hm hbuf

/-- **`gzwrite`** (`gzwrite_step`). Relies on patch 0004 (gzwrite position overflow). -/
theorem gzwrite_step (i : Nat) (buf : BPtr) (len : UInt32) :
    GzCallSafe i (.gzwrite (some (.in_gzstate_x i)) buf len) :=
  gzwrite_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i buf len

/-- **`gzfwrite`** (`gzfwrite_step`). Relies on patch 0004 (gzwrite position overflow). -/
theorem gzfwrite_step (i : Nat) (buf : BPtr) (size nitems : UInt64) :
    GzCallSafe i (.gzfwrite buf size nitems (some (.in_gzstate_x i))) :=
  gzfwrite_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i buf size nitems

/-- **`gzputc`** (`gzputc_step`). Relies on patch 0004 (gzwrite position overflow). -/
theorem gzputc_step (i : Nat) (c : Int32) : GzCallSafe i (.gzputc (some (.in_gzstate_x i)) c) :=
  gzputc_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i c

/-- **`gzputs`** (`gzputs_step`). Relies on patch 0004 (gzwrite position overflow). -/
theorem gzputs_step (i : Nat) (str : BPtr) : GzCallSafe i (.gzputs (some (.in_gzstate_x i)) str) :=
  gzputs_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i str

/-- **`gzvprintf`** (`gzvprintf_step`). Relies on patch 0004 (gzwrite position overflow). -/
theorem gzvprintf_step (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzvprintf (some (.in_gzstate_x i)) format va) :=
  gzvprintf_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i format va

/-- **`gzprintf`** (`gzprintf_step`): `gzprintf` is `gzvprintf`. -/
theorem gzprintf_step (i : Nat) (format : BPtr) (va : List VaArg) :
    GzCallSafe i (.gzprintf (some (.in_gzstate_x i)) format va) :=
  gzprintf_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i format va

/-- **`gzflush`** (`gzflush_step`). -/
theorem gzflush_step (i : Nat) (flush : Int32) : GzCallSafe i (.gzflush (some (.in_gzstate_x i)) flush) :=
  gzflush_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i flush

/-- **`gzsetparams`** (`gzsetparams_step`). -/
theorem gzsetparams_step (i : Nat) (level strategy : Int32) :
    GzCallSafe i (.gzsetparams (some (.in_gzstate_x i)) level strategy) :=
  gzsetparams_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i level strategy

/-- `GzRead.Close.Released`, the copy of `GzReleased` in `gz.read-close`, is `GzReleased`. -/
theorem gzReleased_eq_close_released : GzReleased = GzRead.Close.Released := rfl

/-- **`gzclose_w`** (`gzclose_w_step`): on any handle in `GzInv`, for every OS world, the call
returns, and either refuses a reader with no effect, or releases the writer. -/
theorem gzclose_w_step (i : Nat) : GzCloseSafe i (.gzclose_w (some (.in_gzstate_x i))) :=
  gzclose_w_step_of gzwrite_gzErrorSpec_holds gzwrite_gzErrorOwn_holds i

end ZlibF.Spec.Public.GzSkeleton
