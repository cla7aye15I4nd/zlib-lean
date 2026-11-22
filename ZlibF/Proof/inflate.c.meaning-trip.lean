import ZlibF.Proof.«inflate.c.meaning-side»

/-!
# inflate.c: one trip of the mode loop keeps the format meaning (`TripMeaning`, by mode)

The structure of `TripMeaning c f (CallSide c r)`, the premise of `loop_meaning`. A trip from
`LoopMatches` dispatches on the decoder mode. The modes a `LoopMatches` state can be in
(`loop_mode_cases`) are grouped into rows; each row is one `TripAt` statement, universal in the
configuration unless the row names a wrapper. The rows are proved from the per-mode steps of
`inflate.c.meaning-*` through the dispatch equations and small adapters (the body steps end in
`LoopMatches`, `LeaveShort` or `BAD` with `LoopRefuted`, not in `TripOutcome`), or are new mode
steps.

Each row is a named proposition. The assemblies take the rows as hypotheses; a row is proved by a theorem of exactly its type
in its own file.

* `trip_meaning_zlib`: the zlib wrapper, from `ZlibTripRows`. It needs no gzip header row and no
  raw `CHECK` row, since a zlib configuration never reaches the gzip header modes
  (`GzipFieldsAbsent`).
* `trip_meaning`: every configuration, from `TripRows`.

The trip from the raw `CHECK` state (`RawCheck`, the end of raw data inside a call) is the row
`TripRawCheck`, the second premise of the loop rule; for zlib it is vacuous
(`raw_check_trip_zlib`).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningDictid (NeedDictExit)
set_option autoImplicit false

/-- One trip of the loop of the call `c`, from `LoopMatches` and `CallSide`, when the decoder state
satisfies `P`: the dispatch runs without a fault and ends in a `TripOutcome`, at the dictionary
request, or (raw data after the final block) in the raw `CHECK` state `RawCheck`. -/
def TripAt (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (P : InflateState → Prop) : Prop :=
  ∀ h l, CallSide c r l h → LoopMatches c f h l →
    (∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → P s) →
    ∃ result l' h', runX (inflate_dispatch c) l h = .ok ((result, l'), h') ∧
      (TripOutcome c f result h' l' ∨ NeedDictExit c f result h' l' ∨
        (result = .ok () ∧ RawCheck c f h' l'))

/-- A fact of the one decoder state of the call holds of every state the context names. -/
theorem at_state {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState} {P : InflateState → Prop}
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s) (p : P s) :
    ∀ zs' s', c.st = some (.tab zs') → h.istates zs' = some s' → P s' := by
  intro zs' s' st' hs'
  rw [st] at st'
  cases st'
  rw [hs] at hs'
  cases hs'
  exact p

/-! ## Rows -/

/-- The modes of a `LoopMatches` state, grouped as the rows below. From `LoopStageMatches`: a
header stage is in `HEAD`..`DICTID`, a dictionary request in `DICT`, a body stage in
`TYPE`..`LIT` (`body_mode_range`), a trailer in `CHECK` or `LENGTH`, the end in `DONE`. -/
def LoopModeCases : Prop :=
  ∀ (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL), LoopMatches c f h l →
    ∃ zs s, c.st = some (.tab zs) ∧ h.istates zs = some s ∧
      (s.mode = HEAD ∨ (FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) ∨ s.mode = DICTID ∨ s.mode = DICT ∨
       ((s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) ∨
       ((s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0) ∨
       (s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) ∨
       (s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) ∨
       (LEN_ ≤ s.mode ∧ s.mode ≤ LIT) ∨ s.mode = CHECK ∨ s.mode = LENGTH ∨ s.mode = DONE)

/-- A zlib or raw configuration never reaches the gzip header modes: `ConfigMatches` fixes the
wrapper code (5 or 0), and the safety invariant puts `FLAGS`..`HCRC` only under a gzip wrapper
code (`GzipHeaderMode`). -/
def GzipFieldsAbsent : Prop :=
  ∀ (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (h : Heap) (l : IL), CallSide c r l h →
    LoopMatches c f h l → (f.wrap = .zlib ∨ f.wrap = .raw) →
    ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → ¬ (FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)

/-- `HEAD`, raw: from `head_raw_step`; the raw width is 8..15 by `Api.inflWbits`. -/
def TripHeadRaw : Prop :=
  ∀ c f r, f.wrap = .raw → TripAt c f r (fun s => s.mode = HEAD)

/-- `HEAD`, zlib wrapper, every configured window (0 and 8..15): header checks, the `FDICT` branch
to `DICTID`, the window check, the short-input leave, each rejection as `LoopBad`. New step. -/
def TripHeadZlib : Prop :=
  ∀ c f r, f.wrap = .zlib → TripAt c f r (fun s => s.mode = HEAD)

/-- `HEAD`, gzip and automatic detection: the gzip magic, and for `.auto` the zlib branch. New step;
not needed by the zlib round trip. -/
def TripHeadGzip : Prop :=
  ∀ c f r, (f.wrap = .gzip ∨ f.wrap = .auto) → TripAt c f r (fun s => s.mode = HEAD)

/-- The gzip header field modes `FLAGS`..`HCRC`. New steps; not needed by the zlib round trip. -/
def TripGzipFields : Prop :=
  ∀ c f r, TripAt c f r (fun s => FLAGS ≤ s.mode ∧ s.mode ≤ HCRC)

/-- `DICTID`: from `dictid_step`. -/
def TripDictid : Prop := ∀ c f r, TripAt c f r (fun s => s.mode = DICTID)

/-- `DICT`: with no dictionary, `RESTORE()` and `Z_NEED_DICT` (`NeedDictExit`); with one, on to
`TYPE`. New step. -/
def TripDict : Prop := ∀ c f r, TripAt c f r (fun s => s.mode = DICT)

/-- `TYPE`/`TYPEDO` before the last block: from `type_step` and `typedo_step`, with the adapter
from their ends to `TripOutcome`. -/
def TripTypeOpen : Prop :=
  ∀ c f r, TripAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0)

/-- `TYPE`/`TYPEDO` after the last block, with a wrapper: `BYTEBITS()` and on to `CHECK` (the
stage moves from the body to the trailer). New step. -/
def TripTypeFinal : Prop :=
  ∀ c f r, f.wrap ≠ .raw → TripAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0)

/-- `TYPE`/`TYPEDO` after the last block of raw data: `TYPE` with `Z_BLOCK` or `Z_TREES` leaves;
otherwise `BYTEBITS()` and on to `CHECK`, which ends the trip in `RawCheck` (no `LoopMatches`
state is a raw `CHECK`: the trailer stage needs a wrapper). Not needed by the zlib round trip. -/
def TripTypeFinalRaw : Prop :=
  ∀ c f r, f.wrap = .raw → TripAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0)

/-- Stored blocks: from `stored_step`, `copy_start_step` and `copy_step`. -/
def TripStored : Prop :=
  ∀ c f r, TripAt c f r (fun s => s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)

/-- The dynamic header: from `table_step`, `lenlens_step` and `codelens_step`, which fall through
into the next mode. `WellFormed` and `CodeLengthInvariant` come from `CallSide`; the code-length
contents need `DynamicMatches` to carry `CodeLengthContents`. -/
def TripDynamic : Prop :=
  ∀ c f r, TripAt c f r (fun s => s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS)

/-- Codes: `LEN_`, `LEN` (fast path `fast_call_meaning` and slow path), `LENEXT`, `DIST`,
`DISTEXT`, `MATCH`, `LIT`; all premises from `CallSide`. -/
def TripCodes : Prop := ∀ c f r, TripAt c f r (fun s => LEN_ ≤ s.mode ∧ s.mode ≤ LIT)

/-- `CHECK` with a wrapper: from `check_step`. -/
def TripCheckWrapped : Prop :=
  ∀ c f r, f.wrap ≠ .raw → TripAt c f r (fun s => s.mode = CHECK)

/-- `CHECK` for raw data, from `LoopMatches`: vacuous, since no `LoopMatches` state is a raw
`CHECK`; the raw `CHECK` state is `RawCheck`, row `TripRawCheck`. Not needed by the zlib round
trip. -/
def TripCheckRaw : Prop :=
  ∀ c f r, f.wrap = .raw → TripAt c f r (fun s => s.mode = CHECK)

/-- `LENGTH` and `DONE`: from `length_step` and `done_step`. -/
def TripTrailer : Prop := ∀ c f r, TripAt c f r (fun s => s.mode = LENGTH ∨ s.mode = DONE)

/-- The raw `CHECK` state (`RawCheck`): `CHECK`, `LENGTH` and `DONE` run in one trip with nothing
to read, and the call leaves with `Z_STREAM_END` in `DONE`. Not needed by the zlib round trip. -/
def TripRawCheck : Prop := ∀ c f r, RawCheckTrip c f (CallSide c r)

/-- The rows the zlib wrapper needs. -/
structure ZlibTripRows : Prop where
  modes : LoopModeCases
  absent : GzipFieldsAbsent
  headZlib : TripHeadZlib
  dictid : TripDictid
  dict : TripDict
  typeOpen : TripTypeOpen
  typeFinal : TripTypeFinal
  stored : TripStored
  dynamic : TripDynamic
  codes : TripCodes
  checkWrapped : TripCheckWrapped
  trailer : TripTrailer

/-- The rows of every configuration. -/
structure TripRows : Prop extends ZlibTripRows where
  headRaw : TripHeadRaw
  typeFinalRaw : TripTypeFinalRaw
  headGzip : TripHeadGzip
  gzipFields : TripGzipFields
  checkRaw : TripCheckRaw
  rawCheck : TripRawCheck

/-! ## Assembly -/

/-- The gzip field modes in a zlib or raw configuration: vacuous by `GzipFieldsAbsent`. -/
theorem trip_gzip_fields_plain (modes : LoopModeCases) (absent : GzipFieldsAbsent)
    (c : Ctx) (f : LoopFrame) (r : ZStreamRef) (plain : f.wrap = .zlib ∨ f.wrap = .raw) :
    TripAt c f r (fun s => FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) := by
  intro h l side loop range
  obtain ⟨zs, s, st, hs, _⟩ := modes c f h l loop
  exact absurd (range zs s st hs) (absent c f r h l side loop plain zs s st hs)

/-- `TripMeaning` from a row for each mode group. -/
theorem trip_of_rows {c : Ctx} {f : LoopFrame} {r : ZStreamRef} (rows : ZlibTripRows)
    (head : TripAt c f r (fun s => s.mode = HEAD))
    (fields : TripAt c f r (fun s => FLAGS ≤ s.mode ∧ s.mode ≤ HCRC))
    (check : TripAt c f r (fun s => s.mode = CHECK))
    (final : TripAt c f r (fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0)) :
    TripMeaning c f (CallSide c r) := by
  intro h l side loop
  obtain ⟨zs, s, st, hs, mode⟩ := rows.modes c f h l loop
  rcases mode with m | m | m | m | m | m | m | m | m | m | m | m
  · exact head h l side loop (at_state (P := fun s => s.mode = HEAD) st hs m)
  · exact fields h l side loop (at_state (P := fun s => FLAGS ≤ s.mode ∧ s.mode ≤ HCRC) st hs m)
  · exact rows.dictid c f r h l side loop (at_state (P := fun s => s.mode = DICTID) st hs m)
  · exact rows.dict c f r h l side loop (at_state (P := fun s => s.mode = DICT) st hs m)
  · exact rows.typeOpen c f r h l side loop
      (at_state (P := fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last = 0) st hs m)
  · exact final h l side loop
      (at_state (P := fun s => (s.mode = TYPE ∨ s.mode = TYPEDO) ∧ s.last ≠ 0) st hs m)
  · exact rows.stored c f r h l side loop
      (at_state (P := fun s => s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY) st hs m)
  · exact rows.dynamic c f r h l side loop
      (at_state (P := fun s => s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) st hs m)
  · exact rows.codes c f r h l side loop
      (at_state (P := fun s => LEN_ ≤ s.mode ∧ s.mode ≤ LIT) st hs m)
  · exact check h l side loop (at_state (P := fun s => s.mode = CHECK) st hs m)
  · exact rows.trailer c f r h l side loop
      (at_state (P := fun s => s.mode = LENGTH ∨ s.mode = DONE) st hs (Or.inl m))
  · exact rows.trailer c f r h l side loop
      (at_state (P := fun s => s.mode = LENGTH ∨ s.mode = DONE) st hs (Or.inr m))

/-- `TripMeaning` in every configuration. -/
theorem trip_meaning (rows : TripRows) (c : Ctx) (f : LoopFrame) (r : ZStreamRef) :
    TripMeaning c f (CallSide c r) := by
  have z := rows.toZlibTripRows
  cases hw : f.wrap with
  | raw =>
    exact trip_of_rows z (rows.headRaw c f r hw) (rows.gzipFields c f r) (rows.checkRaw c f r hw)
      (rows.typeFinalRaw c f r hw)
  | zlib =>
    exact trip_of_rows z (rows.headZlib c f r hw) (rows.gzipFields c f r)
      (rows.checkWrapped c f r (by rw [hw]; decide)) (rows.typeFinal c f r (by rw [hw]; decide))
  | gzip =>
    exact trip_of_rows z (rows.headGzip c f r (Or.inl hw)) (rows.gzipFields c f r)
      (rows.checkWrapped c f r (by rw [hw]; decide)) (rows.typeFinal c f r (by rw [hw]; decide))
  | auto =>
    exact trip_of_rows z (rows.headGzip c f r (Or.inr hw)) (rows.gzipFields c f r)
      (rows.checkWrapped c f r (by rw [hw]; decide)) (rows.typeFinal c f r (by rw [hw]; decide))

/-- No zlib state is the raw `CHECK` state, so the raw `CHECK` trip is vacuous for zlib. -/
theorem raw_check_trip_zlib {c : Ctx} {f : LoopFrame} {Side : IL → Heap → Prop}
    (zlib : f.wrap = .zlib) : RawCheckTrip c f Side := by
  intro h l _ raw
  rw [raw.1] at zlib
  cases zlib

/-- `TripMeaning` for the zlib wrapper, without the gzip header rows and the raw `CHECK` row. -/
theorem trip_meaning_zlib (rows : ZlibTripRows) (c : Ctx) (f : LoopFrame) (r : ZStreamRef)
    (zlib : f.wrap = .zlib) : TripMeaning c f (CallSide c r) :=
  trip_of_rows rows (rows.headZlib c f r zlib)
    (trip_gzip_fields_plain rows.modes rows.absent c f r (Or.inl zlib))
    (rows.checkWrapped c f r (by rw [zlib]; decide)) (rows.typeFinal c f r (by rw [zlib]; decide))

end Zlib.Inflate.Proofs
