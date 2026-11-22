import ZlibF.Proof.«inflate.c.meaning-trip»
import ZlibF.Proof.«inflate.c.meaning-check»
import ZlibF.Proof.«inflate.c.meaning-trailer»
import ZlibF.Proof.«inflate.c.check-dispatch»

/-!
# inflate.c: the trip rows `DICTID`, `CHECK` with a wrapper, `LENGTH` and `DONE`

Each row of `inflate.c.meaning-trip` here is the per-mode step of `inflate.c.meaning-*` behind the
dispatch equation of its mode. The steps already end in `TripOutcome` or `NeedDictExit`.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The side facts give the environment of the decoder state of the call. -/
theorem CallSide.env {c : Ctx} {r : ZStreamRef} {l : IL} {h : Heap} (side : CallSide c r l h) :
    ∃ zs z s, Env c h r zs z s ∧ DefaultStateJ h r zs z s :=
  let ⟨zs, z, s, strm, st, j, _⟩ := side
  ⟨zs, z, s, ⟨strm, st, j.good.live.hz, j.good.live.hs⟩, j⟩

/-- The real switch selects the DONE branch. -/
theorem inflate_dispatch_DONE {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL) (mode : s.mode = DONE) :
    runX (inflate_dispatch c) l h = runX (inflate_DONE c) l h := by
  unfold inflate_dispatch
  rw [runX_bind, runX_rdS E]
  with_reducible simp [mode, HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    DICTID, DICT, TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
    LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE]

/-- `DICTID`: `dictid_step`. -/
theorem trip_dictid : TripDictid := by
  intro c f r h l side loop mode
  obtain ⟨zs, z, s, E, _⟩ := side.env
  obtain ⟨result, l', h', run, out⟩ := MeaningDictid.dictid_step loop E.strm E.hz mode
  exact ⟨result, l', h', (inflate_dispatch_DICTID E l (mode zs s E.st E.hs)).trans run,
    out.elim Or.inl (fun need => Or.inr (Or.inl need))⟩

/-- `CHECK` with a wrapper: `check_step`; the CRC tables are library globals. -/
theorem trip_check_wrapped : TripCheckWrapped := by
  intro c f r wrapped h l side loop mode
  obtain ⟨zs, z, s, E, j⟩ := side.env
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    have globals := j.globals
    unfold LibraryGlobals at globals
    rw [Zlib.Crc32.Proofs.StaticsOK, globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨result, l', h', run, out⟩ :=
    MeaningCheck.check_step loop E.strm E.hz statics mode wrapped
  exact ⟨result, l', h', (inflate_dispatch_CHECK E l (mode zs s E.st E.hs)).trans run, Or.inl out⟩

/-- `LENGTH` and `DONE`: `length_step` and `done_step`. -/
theorem trip_trailer : TripTrailer := by
  intro c f r h l side loop mode
  obtain ⟨zs, z, s, E, _⟩ := side.env
  rcases mode zs s E.st E.hs with length | done
  · obtain ⟨result, l', h', run, out⟩ :=
      MeaningTrailer.length_step loop E.strm E.hz (at_state (P := fun s => s.mode = LENGTH) E.st E.hs length)
    exact ⟨result, l', h', (inflate_dispatch_LENGTH E l length).trans run, Or.inl out⟩
  · obtain ⟨run, kept⟩ := MeaningTrailer.done_step loop
    exact ⟨_, _, _, (inflate_dispatch_DONE E l done).trans run,
      Or.inl (Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, kept⟩)⟩)⟩

#print axioms trip_dictid
#print axioms trip_check_wrapped
#print axioms trip_trailer

end Zlib.Inflate.Proofs
