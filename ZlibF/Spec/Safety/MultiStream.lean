import ZlibF.Spec.Common.Sequences

/-!
# Multi-stream compositionality and non-interference safety goals

Contracts proving that multiple distinct `z_stream` objects (`inflate` and/or `deflate`)
with disjoint owned heap blocks can be initialized, interleaved in arbitrary sequential order,
and destroyed without violating each other's reachability, invariants, or owned allocations.
-/

namespace ZlibF.Spec.Public
open C ZlibF.Spec
set_option autoImplicit false

/-- Two streams are distinct and own pairwise disjoint sets of internal heap blocks. -/
def StreamDisjoint (h : Heap) (r₁ r₂ : ZStreamRef) : Prop :=
  r₁ ≠ r₂ ∧ ∀ b, StreamOwned h r₁ b → ¬ StreamOwned h r₂ b

/-- Every caller memory region written by `call` on `r₁` avoids blocks owned by `r₂`. -/
def ExternalWriteSafe (h : Heap) (r₁ r₂ : ZStreamRef) (call : Call) : Prop :=
  ∀ reg ∈ StreamWriteRegions h r₁ call, ∀ b, ByteRoot reg.pointer b → ¬ StreamOwned h r₂ b

/-- **Multi-stream disjoint initialization**: initializing a second stream `r₂` on a heap
containing a reachable stream `r₁` (`r₁ ≠ r₂`) preserves `r₁`'s reachability and owned blocks
while producing a disjoint second stream `r₂`. -/
def Goal.multi_stream_init_disjoint : Prop :=
  (∀ h after r₁ r₂ z₂ kind₁ version wb,
    StreamReachable kind₁ h r₁ → LibraryGlobals h →
    r₁ ≠ r₂ → r₂.get h = some z₂ → DefaultOrNull z₂ → VersionValue h version (some 49) →
    C.run (Zlib.Inflate.inflateInit2_ (some r₂) wb version 112) h = .ok (Z_OK, after) →
    (kind₁ = .inflate → ZlibF.PlatformMemory.ByteObjectsFit after) →
    StreamReachable kind₁ after r₁ ∧ StreamReachable .inflate after r₂ ∧
      StreamDisjoint after r₁ r₂ ∧ (∀ b, StreamOwned after r₁ b ↔ StreamOwned h r₁ b)) ∧
  (∀ h after r₁ r₂ z₂ kind₁ version level method wb mem strategy,
    StreamReachable kind₁ h r₁ → LibraryGlobals h →
    r₁ ≠ r₂ → r₂.get h = some z₂ → DefaultOrNull z₂ → VersionValue h version (some 49) →
    C.run (Zlib.Deflate.deflateInit2_ (some r₂) level method wb mem strategy version 112) h =
      .ok (Z_OK, after) →
    (kind₁ = .inflate → ZlibF.PlatformMemory.ByteObjectsFit after) →
    StreamReachable kind₁ after r₁ ∧ StreamReachable .deflate after r₂ ∧
      StreamDisjoint after r₁ r₂ ∧ (∀ b, StreamOwned after r₁ b ↔ StreamOwned h r₁ b))

/-- **Multi-stream interleaved step safety**: any permitted operation on stream `r₁` whose
declared caller write regions do not overlap `r₂`'s owned blocks terminates cleanly without fault,
preserves `r₁`'s and `r₂`'s stream invariants, acts as a valid `Rebuffer` on `r₂`, preserves
`r₂`'s record and owned blocks, and keeps both streams disjoint. -/
def Goal.multi_stream_step_safety : Prop :=
  ∀ h r₁ r₂ kind₁ kind₂ call,
    StreamReachable kind₁ h r₁ → StreamReachable kind₂ h r₂ → LibraryGlobals h →
    StreamDisjoint h r₁ r₂ → ZlibF.PlatformMemory.ByteObjectsFit h →
    StreamOperation kind₁ r₁ call → StreamArguments h r₁ call →
    ExternalWriteSafe h r₁ r₂ call →
    ∃ value after,
      call.execute default h = .ok ((value, default), after) ∧
      StreamInvariant kind₁ after r₁ ∧ StreamInvariant kind₂ after r₂ ∧
      StreamReachable kind₁ after r₁ ∧
      ((kind₂ = .inflate → ZlibF.PlatformMemory.ByteObjectsFit after) →
        StreamReachable kind₂ after r₂) ∧
      Rebuffer h after r₂ ∧ r₂.get after = r₂.get h ∧
      (∀ b, StreamOwned after r₂ b ↔ StreamOwned h r₂ b) ∧
      StreamDisjoint after r₁ r₂

/-- **Multi-stream teardown safety**: ending stream `r₁` frees every block owned by `r₁` while
leaving a disjoint stream `r₂` reachable, intact, and invariant-preserving. -/
def Goal.multi_stream_end_safety : Prop :=
  ∀ h r₁ r₂ kind₁ kind₂,
    StreamReachable kind₁ h r₁ → StreamReachable kind₂ h r₂ → LibraryGlobals h →
    StreamDisjoint h r₁ r₂ →
    ∃ rc after z₁',
      C.run ((match kind₁ with
        | .inflate => Zlib.Inflate.inflateEnd
        | .deflate => Zlib.Deflate.deflateEnd) (some r₁)) h = .ok (rc, after) ∧
      (rc = Z_OK ∨ kind₁ = .deflate ∧ rc = Z_DATA_ERROR) ∧
      r₁.get after = some z₁' ∧ z₁'.state = none ∧
      Frame h after (fun b => StreamRoot r₁ b ∨ StreamOwned h r₁ b) ∧
      LiveChange h after (fun _ => False) (StreamOwned h r₁) ∧
      Rebuffer h after r₂ ∧ r₂.get after = r₂.get h ∧
      (∀ b, StreamOwned after r₂ b ↔ StreamOwned h r₂ b) ∧
      StreamInvariant kind₂ after r₂ ∧
      ((kind₂ = .inflate → ZlibF.PlatformMemory.ByteObjectsFit after) →
        StreamReachable kind₂ after r₂)

/-- **Multi-stream non-vacuity**: there exists a concrete heap hosting both a reachable
`deflate` stream and a reachable `inflate` stream with disjoint owned storage, and stepping
the `deflate` stream preserves both streams' reachability and disjointness. -/
def Goal.multi_stream_nonvacuity : Prop :=
  ∃ h₀ h₁ h₂ r_def r_inf,
    StreamReachable .deflate h₀ r_def ∧
    StreamReachable .deflate h₁ r_def ∧
    StreamReachable .inflate h₁ r_inf ∧
    StreamDisjoint h₁ r_def r_inf ∧
    LibraryGlobals h₁ ∧
    ZlibF.PlatformMemory.ByteObjectsFit h₁ ∧
    C.run (Zlib.Deflate.deflateReset (some r_def)) h₁ = .ok (Z_OK, h₂) ∧
    StreamReachable .deflate h₂ r_def ∧
    StreamReachable .inflate h₂ r_inf ∧
    StreamDisjoint h₂ r_def r_inf

end ZlibF.Spec.Public