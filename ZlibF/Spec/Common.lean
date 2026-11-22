import ZlibF.Spec.Common.Back
import ZlibF.Spec.Common.Bits
import ZlibF.Spec.Common.ByteAddress
import ZlibF.Spec.Common.Calls
import ZlibF.Spec.Common.Checksums
import ZlibF.Spec.Common.Copy
import ZlibF.Spec.Common.Crc32Statics
import ZlibF.Spec.Common.DeflateGood
import ZlibF.Spec.Common.Domains
import ZlibF.Spec.Common.GzInv
import ZlibF.Spec.Common.GzState
import ZlibF.Spec.Common.HeapUniq
import ZlibF.Spec.Common.History
import ZlibF.Spec.Common.Inflate.FastEnv
import ZlibF.Spec.Common.Inflate.FastTable
import ZlibF.Spec.Common.Inflate.InflateCodeLengthInvariant
import ZlibF.Spec.Common.Inflate.InflateFast
import ZlibF.Spec.Common.Inflate.InflateFastCallOrigin
import ZlibF.Spec.Common.Inflate.InflateFastOrigin
import ZlibF.Spec.Common.Inflate.InflateFastPlatform
import ZlibF.Spec.Common.Inflate.InflateOutputInvariant
import ZlibF.Spec.Common.Inflate.InflatePendingInvariant
import ZlibF.Spec.Common.Inflate.InflateRootTable
import ZlibF.Spec.Common.Inflate.InflateSubtable
import ZlibF.Spec.Common.Inflate.InflateTableContent
import ZlibF.Spec.Common.Inflate.InflateTableExtent
import ZlibF.Spec.Common.Inflate.InflateTableInvariant
import ZlibF.Spec.Common.Inflate.InflateTableSafety
import ZlibF.Spec.Common.Inflate.TableBuild
import ZlibF.Spec.Common.Inflate.TableCanon
import ZlibF.Spec.Common.Inflate.WindowCopy
import ZlibF.Spec.Common.InflateGood
import ZlibF.Spec.Common.Initialisation
import ZlibF.Spec.Common.Lifecycle
import ZlibF.Spec.Common.Memory
import ZlibF.Spec.Common.Parameters
import ZlibF.Spec.Common.PlatformMemory
import ZlibF.Spec.Common.Queries
import ZlibF.Spec.Common.Sequences
import ZlibF.Spec.Common.StreamQueries
import ZlibF.Spec.Common.Streams
import ZlibF.Spec.Common.TreesInv
import ZlibF.Spec.Common.Utilities

/-!
# The common specification

The definitions that both the safety goals (`ZlibF/Spec/Safety/`) and the functional goals
(`ZlibF/Spec/Functional/`) use: the heap and stream invariants, the call catalogue, the argument
domains and the histories. A common module imports no safety and no functional module, and no
proof module (`scripts/check-spec-layers.py`).

These modules use the Lean namespace `ZlibF.Spec.Public`: the folder name `Common` is not part of
any goal or theorem name.
-/
