import ZlibF.Runtime.Schema
import ZlibF.Zlib.«inffixed.h»
import ZlibF.Spec.Common.Inflate.FastTable

/-!
# inffast.c: the shape of the decoding tables (`TableOK` for `inflate_fast`)

`inflate_fast` reads the literal/length table `lencode` and the distance table `distcode` without checking them. What
it needs is the shape that `inflate_table` gives (`proof/inftrees.md`, theorem T2) and that the static tables `lenfix`
and `distfix` have. `LenTableSafe` and `DistTableSafe` state it for a table `ca[o ..]` with root width `R`:

* the root has `2^R` entries inside the array and `R ≤ 15`;
* a root entry is a leaf (literal, base value, end of block, invalid code) or a link to a second level that lies inside
  the array, with `1 ≤ op ≤ 15` bits, and whose entries are leaves;
* the bits of a root entry plus those of the second-level entry reached from it are at most 15;
* a length base has at most 5 extra bits and a base value of at least 3 whose largest value, with the extra bits, is
  258; a distance base has at most 13 extra bits and a base value of at least 1.

`inflate_table` must establish `LenTableSafe` for the table it builds for `LENS` and `DistTableSafe` for `DISTS`
(the table pointer and `*bits` it returns being `o` and `R`). The static tables are proved below.
-/

namespace Zlib.Inffast.Proofs
open C Zlib.Inffast.Spec

set_option maxRecDepth 100000 in
/-- The static literal/length table `lenfix` (inffixed.h), root width 9, has the shape `LenTableSafe` (kernel
evaluation of all 512 entries). -/
theorem lenfix_tableSafe : LenTableSafe Zlib.InffixedH.lenfix 0 9 := by
  unfold LenTableSafe TableSafe
  refine ⟨by decide, by decide +kernel, ?_⟩
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every leaf of the static literal/length table `lenfix` reads at least one bit (kernel evaluation of all 512
entries). -/
theorem lenfix_leavesPositive : LenLeavesPositive Zlib.InffixedH.lenfix 0 9 := by
  unfold LenLeavesPositive
  decide +kernel

set_option maxRecDepth 100000 in
/-- The static distance table `distfix`, root width 5, has the shape `DistTableSafe`. -/
theorem distfix_tableSafe : DistTableSafe Zlib.InffixedH.distfix 0 5 := by
  unfold DistTableSafe TableSafe
  refine ⟨by decide, by decide +kernel, ?_⟩
  decide +kernel

end Zlib.Inffast.Proofs
