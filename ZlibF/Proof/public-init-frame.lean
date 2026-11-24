import ZlibF.Spec.Common.Initialisation
import ZlibF.Spec.Common.Memory

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

end ZlibF.Spec.Public.InitSafetyProof
