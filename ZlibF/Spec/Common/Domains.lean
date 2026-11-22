import ZlibF.Spec.Common.Back

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-- Caller storage before init. No library invariant or callee contract is supplied. -/
def InitDomain (h : Heap) (r : ZStreamRef) (version : BPtr) : Prop :=
  Fresh h ∧ Zlib.Inflate.Spec.Uniq h ∧ LibraryGlobals h ∧
  VersionValue h version (some 49) ∧
  ∃ z, r.get h = some z ∧ DefaultOrNull z ∧ z.state = none

/-- Fixed caller storage for top-level non-emptiness obligations. The window remains caller-owned. -/
def witnessHeap : Heap :=
  { Heap.empty with
    streams := upd Heap.empty.streams 0 (some default)
    bytes := upd (upd Heap.empty.bytes 1 (some #[49, 0])) 2
      (some (Array.replicate 32768 0))
    nextBlk := 3
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

end ZlibF.Spec.Public
