import ZlibF.Runtime.Schema

/-!
# Heap uniqueness: a block number holds an object of at most one table

`cnt` and `Uniq` of the namespaces of the inflate, deflate and gz handle invariants
(`Zlib.Inflate.Spec`, `Zlib.Deflate.Spec`, `Zlib.Gzlib.Spec`). The three definitions are the same text. They
are part of what the safety goals mean, so they are here, under `ZlibF/Spec/`, and not in the proof modules
`inflate.c.base`, `deflate.c.base` and `gzlib.c.base`, which keep their lemmas.
-/

namespace Zlib.Inflate.Spec
open C

/-- 1 if the table entry holds an object, else 0. -/
def cnt {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

/-- A block number holds an object of at most one table. -/
def Uniq (h : Heap) : Prop := ∀ b,
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) +
  cnt (h.gzstates b) ≤ 1

end Zlib.Inflate.Spec

namespace Zlib.Deflate.Spec
open C

/-- 1 if the table entry holds an object, else 0. -/
def cnt {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

/-- A block number holds an object of at most one table. -/
def Uniq (h : Heap) : Prop := ∀ b,
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) +
  cnt (h.gzstates b) ≤ 1

end Zlib.Deflate.Spec

namespace Zlib.Gzlib.Spec
open C

/-- 1 if the table entry holds an object, else 0. -/
def cnt {α : Type} (o : Option α) : Nat := if o.isSome then 1 else 0

/-- A block number holds an object of at most one table. -/
def Uniq (h : Heap) : Prop := ∀ b,
  cnt (h.bytes b) + cnt (h.words b) + cnt (h.streams b) + cnt (h.gzheaders b) + cnt (h.dstates b) + cnt (h.istates b) +
  cnt (h.gzstates b) ≤ 1

end Zlib.Gzlib.Spec
