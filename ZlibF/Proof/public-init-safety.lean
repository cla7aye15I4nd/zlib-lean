import ZlibF.Proof.«public-inflate-init2»
import ZlibF.Proof.«public-deflate-init2»
import ZlibF.Spec.Safety.Initialisation

/-!
# Safety of the inflate and deflate init functions

Each goal of `ZlibF/Spec/Safety/Initialisation.lean` follows from the full contract of the same
function (`Goal.inflateInit2_`, `Goal.deflateInit2_`). A wrong version or `stream_size` is the
contract's version refusal, and a `NULL` stream with the right ones is its stream refusal; both
leave the heap unchanged. A stream record with the right version and size is the contract's main
clause, which has no premise on the record's `state` field. The failure
branches of the contracts give `SameObjects` (or `SameObjectsUpToTableShape`) with the heap whose
stream record was rewritten; `frame_of_same` turns that into the frame of the record and an
unchanged set of live blocks. `inflateInit_` and `deflateInit_` are `inflateInit2_` and
`deflateInit2_` with fixed arguments in the translation.
-/

namespace ZlibF.Spec.Public.InitSafetyProof
open C ZlibF.Spec ZlibF.Spec.Public

theorem upToShape_of_same {e a : Heap} (s : SameObjects e a) : SameObjectsUpToTableShape e a := by
  obtain ⟨hb, hw, hro, hs, hg, hd, hi, hgz, hst, hal, hga, hn, hna⟩ := s
  exact ⟨fun b => by rw [hb], fun b => by rw [hw], hro, fun b => by rw [hs], fun b => by rw [hg],
    fun b => by rw [hd], fun b => by rw [hi], fun b => by rw [hgz], hst, hal, hga, hn, hna⟩

/-- Rewriting a live stream record changes nothing but that record, and keeps every block live. -/
theorem frame_of_same {h after : Heap} {r : ZStreamRef} {z v : ZStream} (hz : r.get h = some z)
    (s : SameObjectsUpToTableShape (r.put h v) after) :
    Frame h after (StreamRoot r) ∧ LiveChange h after (fun _ => False) (fun _ => False) := by
  obtain ⟨hb, hw, hro, hs, hg, hd, hi, hgz, hst, hal, hga, hn, hna⟩ := s
  cases r with
  | tab i =>
    have hzi : h.streams i = some z := hz
    have hput : ZStreamRef.put h (.tab i) v = { h with streams := upd h.streams i (some v) } := by
      simp [ZStreamRef.put, hzi]
    rw [hput] at hb hw hro hs hg hd hi hgz hst hal hga hn hna
    have hlive : ∀ b, after.live b ↔ h.live b := by
      intro b
      by_cases hbi : b = i
      · subst hbi
        simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_same, hzi]
        simp
      · simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_ne _ _ _ _ hbi]
    refine ⟨⟨hst.symm, hal.symm, hga.symm, hn, hna, ?_⟩, fun b => by simp [hlive b]⟩
    intro b hl hnot
    have hbi : b ≠ i := hnot
    refine ⟨hb b, hw b, ?_, hg b, hd b, hi b, hgz b, ?_⟩
    · rw [hs b]; exact upd_ne _ _ _ _ hbi
    · exact hro b (by simpa [Heap.live, upd_ne _ _ _ _ hbi] using hl)
  | in_gzstate_strm i =>
    obtain ⟨g, hgi, -⟩ : ∃ g, h.gzstates i = some g ∧ g.strm = z := by
      simp only [ZStreamRef.get, Option.map_eq_some_iff] at hz; exact hz
    have hput : ZStreamRef.put h (.in_gzstate_strm i) v =
        { h with gzstates := upd h.gzstates i (some { g with strm := v }) } := by
      simp [ZStreamRef.put, hgi]
    rw [hput] at hb hw hro hs hg hd hi hgz hst hal hga hn hna
    have hlive : ∀ b, after.live b ↔ h.live b := by
      intro b
      by_cases hbi : b = i
      · subst hbi
        simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_same, hgi]
        simp
      · simp only [Heap.live, hb, hw, hs, hg, hd, hi, hgz, upd_ne _ _ _ _ hbi]
    refine ⟨⟨hst.symm, hal.symm, hga.symm, hn, hna, ?_⟩, fun b => by simp [hlive b]⟩
    intro b hl hnot
    have hbi : b ≠ i := hnot
    refine ⟨hb b, hw b, hs b, hg b, hd b, hi b, ?_, ?_⟩
    · rw [hgz b]; exact upd_ne _ _ _ _ hbi
    · exact hro b (by simpa [Heap.live, upd_ne _ _ _ _ hbi] using hl)

/-- The record case of `inflateInit2_` with the right version and size, from its contract. -/
theorem inflateInit2_record {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr} (wb : Int32)
    (hf : Fresh h) (hu : Zlib.Inflate.Spec.Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (hd : DefaultOrNull z) (hv : VersionValue h version (some 49)) :
    ∃ rc after, C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (rc, after) ∧
      InitCallSafe .inflate h after r rc := by
  obtain ⟨rc, after, hrun, -, hbr⟩ :=
    (ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public wb).2.2 h r z version hf hu hg hz hd hv
  refine ⟨rc, after, hrun, ?_⟩
  by_cases ha : h.allocOk h.nalloc = false
  · rw [ite_eq_left ha] at hbr
    obtain ⟨hrc, hsame⟩ := hbr
    obtain ⟨hfr, hl⟩ := frame_of_same hz (upToShape_of_same hsame)
    exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
  · rw [ite_eq_right ha] at hbr
    cases hw : Api.inflWbits wb.toInt with
    | none =>
      rw [hw] at hbr
      obtain ⟨hrc, hsame⟩ := hbr
      obtain ⟨hfr, hl⟩ := frame_of_same hz hsame
      exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
    | some p =>
      obtain ⟨wrap, bits⟩ := p
      rw [hw] at hbr
      obtain ⟨hrc, z', s', hgood, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr, hl⟩ := hbr
      subst hrc
      refine ⟨hfr, Or.inl ⟨rfl, StreamReachable.inflateInit hf hu hg hz hd hv hrun,
        fun b => b = h.nextBlk, ?_, hl⟩⟩
      intro b hb
      subst hb
      exact ⟨z', hgood.live.hz, Or.inl ⟨h.nextBlk, s', hgood.live.zst, hgood.live.hs, Or.inl rfl⟩⟩

/-- An unchanged heap is a safe outcome of a refused init call on a stream record. -/
theorem same_heap_safe (kind : StreamKind) (h : Heap) (r : ZStreamRef) {rc : Int32}
    (hrc : rc ≠ Z_OK) : InitCallSafe kind h h r rc :=
  ⟨⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ =>
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
    Or.inr ⟨hrc, fun _ => by simp⟩⟩

/-- `Goal.inflateInit2__safety`: `inflateInit2_` is safe on every call `zlib.h` allows: a `NULL` stream, a wrong version or a wrong `stream_size` is refused with the heap unchanged; on a stream record, on `Z_OK` the stream is reachable and owns every new block, on any other code no live block changes; from its functional init theorem. -/
theorem inflateInit2__safety : Goal.inflateInit2__safety := by
  intro h strm version size wb ⟨hf, hu, hg, ⟨head, hv⟩, hs⟩
  have hc := ZlibF.Spec.Public.Proofs.InflateInit.inflate_init2_public wb
  by_cases hok : head = some 49 ∧ size = 112
  · obtain ⟨rfl, rfl⟩ := hok
    cases strm with
    | none => exact ⟨_, _, hc.2.1 h version hv, Or.inr rfl, rfl⟩
    | some r =>
      obtain ⟨z, hz, hd⟩ := hs r rfl
      exact inflateInit2_record wb hf hu hg hz hd hv
  · have hne : head ≠ some 49 ∨ size ≠ 112 := by
      by_cases h1 : head = some 49
      · exact Or.inr fun h2 => hok ⟨h1, h2⟩
      · exact Or.inl h1
    refine ⟨_, _, hc.1 h strm version head size hv hne, ?_⟩
    cases strm with
    | none => exact ⟨Or.inl rfl, rfl⟩
    | some r => exact same_heap_safe .inflate h r (by decide)

/-- `Goal.inflateInit__safety`: `inflateInit_` is safe on every call `zlib.h` allows, as `inflateInit2_` at window bits 15; from its functional init theorem. -/
theorem inflateInit__safety : Goal.inflateInit__safety :=
  fun h strm version size d => inflateInit2__safety h strm version size DEF_WBITS d

/-- The record case of `deflateInit2_` with the right version and size, from its contract. -/
theorem deflateInit2_record {h : Heap} {r : ZStreamRef} {z : ZStream} {version : BPtr}
    (level method wb mem strategy : Int32)
    (hf : Fresh h) (hu : Zlib.Inflate.Spec.Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (hd : DefaultOrNull z) (hv : VersionValue h version (some 49)) :
    ∃ rc after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (rc, after) ∧ InitCallSafe .deflate h after r rc := by
  obtain ⟨rc, after, hrun, hbr⟩ :=
    (ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof level method wb mem strategy).2.2
      h r z version hf hu hg hz hd hv
  refine ⟨rc, after, hrun, ?_⟩
  cases hp : Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
  | none =>
    rw [hp] at hbr
    obtain ⟨hrc, hsame, -⟩ := hbr
    obtain ⟨hfr, hl⟩ := frame_of_same hz (upToShape_of_same hsame)
    exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
  | some p =>
    rw [hp] at hbr
    dsimp only at hbr
    by_cases ha : h.allocOk h.nalloc = false
    · rw [ite_eq_left ha] at hbr
      obtain ⟨hrc, -, hsame⟩ := hbr
      obtain ⟨hfr, hl⟩ := frame_of_same hz (upToShape_of_same hsame)
      exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩
    · rw [ite_eq_right ha] at hbr
      obtain ⟨-, hbr⟩ := hbr
      by_cases hall : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
      · rw [ite_eq_left hall] at hbr
        obtain ⟨hrc, z', s', hgood, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfr, hl, -⟩ := hbr
        subst hrc
        refine ⟨hfr, Or.inl ⟨rfl, StreamReachable.deflateInit hf hu hg hz hd hv hrun,
          DeflateOwned h.nextBlk s', ?_, hl⟩⟩
        intro b hb
        exact ⟨z', hgood.live.hz, Or.inr ⟨h.nextBlk, s', hgood.live.zst, hgood.live.hs, hb⟩⟩
      · rw [ite_eq_right hall] at hbr
        obtain ⟨hrc, -, hl, hfr⟩ := hbr
        exact ⟨hfr, Or.inr ⟨by rw [hrc]; decide, hl⟩⟩

/-- `Goal.deflateInit2__safety`: `deflateInit2_` is safe on every call `zlib.h` allows: a `NULL` stream, a wrong version or a wrong `stream_size` is refused with the heap unchanged; on a stream record, on `Z_OK` the stream is reachable and owns every new block, on any other code no live block changes; from its functional init theorem. -/
theorem deflateInit2__safety : Goal.deflateInit2__safety := by
  intro h strm version size level method wb mem strategy ⟨hf, hu, hg, ⟨head, hv⟩, hs⟩
  have hc := ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof level method wb mem strategy
  by_cases hok : head = some 49 ∧ size = 112
  · obtain ⟨rfl, rfl⟩ := hok
    cases strm with
    | none => exact ⟨_, _, hc.2.1 h version hv, Or.inr rfl, rfl⟩
    | some r =>
      obtain ⟨z, hz, hd⟩ := hs r rfl
      exact deflateInit2_record level method wb mem strategy hf hu hg hz hd hv
  · have hne : head ≠ some 49 ∨ size ≠ 112 := by
      by_cases h1 : head = some 49
      · exact Or.inr fun h2 => hok ⟨h1, h2⟩
      · exact Or.inl h1
    refine ⟨_, _, hc.1 h strm version head size hv hne, ?_⟩
    cases strm with
    | none => exact ⟨Or.inl rfl, rfl⟩
    | some r => exact same_heap_safe .deflate h r (by decide)

/-- `Goal.deflateInit__safety`: `deflateInit_` is safe on every call `zlib.h` allows, as `deflateInit2_` with the default method, window, memory level and strategy; from its functional init theorem. -/
theorem deflateInit__safety : Goal.deflateInit__safety :=
  fun h strm version size level d =>
    deflateInit2__safety h strm version size level Z_DEFLATED MAX_WBITS
      DEF_MEM_LEVEL Z_DEFAULT_STRATEGY d

end ZlibF.Spec.Public.InitSafetyProof
