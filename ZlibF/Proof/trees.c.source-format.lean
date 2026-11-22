import ZlibF.Proof.«trees.c.header-decode»

/-! # trees.c: source-alphabet format facts from actual construction -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- Data facts for the constructed literal/length and distance alphabets. -/
structure SourceFormatData (d : DeflateState) : Prop where
  lit : ZlibF.Spec.Acceptable .litLen
    (lens (sendLengths d .lit) (d.l_desc.max_code.toInt.toNat + 1))
  dist : ZlibF.Spec.Acceptable .dist
    (lens (sendLengths d .dist) (d.d_desc.max_code.toInt.toNat + 1))
  eob : ZlibF.Spec.HasEndOfBlock
    (lens (sendLengths d .lit) (d.l_desc.max_code.toInt.toNat + 1))

/-- Actual literal and distance construction establish the independent
source-alphabet acceptance rules and retain the used END_BLOCK symbol. -/
theorem bl_prepare_source_format {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hEOB : d.dyn_ltree[256]!.fc ≠ 0) :
    ∃ e : DeflateState, blPrepare (Sp id) h = .ok ((), setD h id e) ∧ SourceFormatData e := by
  obtain ⟨aL, lit, hrL, hframeL, ML, hML, hmaxL, haccL, hdecodeL⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
    (ws_build_tree_decodable_initialized (h0 := h) .lit hI.base.wf hI.base.static hI.run.to0)
  have haL : aL = () := Subsingleton.elim _ _
  subst aL
  rw [setD_self hI.base.dstate] at hrL
  have hIL := hframeL.treesInvAt hI
  obtain ⟨aD, dist, hrD, hframeD, MD, hMD, hmaxD, haccD, hdecodeD⟩ := merge_ws_and
    (ws_build_tree_frame_initialized (h0 := h) .dist hIL.base.wf hIL.base.static hIL.run.to0)
    (ws_build_tree_decodable_initialized (h0 := h) .dist hIL.base.wf hIL.base.static hIL.run.to0)
  have haD : aD = () := Subsingleton.elim _ _
  subst aD
  have hlDesc := hframeD.other_desc .lit (by decide +kernel)
  have hlTree := hframeD.other_tree .lit (by decide +kernel)
  simp only [TK.getDesc, TK.arr] at hlDesc hlTree hmaxL hmaxD
  have hLN : dist.l_desc.max_code.toInt.toNat = ML := by rw [hlDesc, hmaxL]; omega
  have hDN : dist.d_desc.max_code.toInt.toNat = MD := by rw [hmaxD]; omega
  have hLit : lens (sendLengths dist .lit) (dist.l_desc.max_code.toInt.toNat + 1) =
      Zlib.Inftrees.Proofs.lensOf (fun n => lit.dyn_ltree[n]!.dl.toNat) (ML + 1) := by
    rw [hLN]
    unfold lens Zlib.Inftrees.Proofs.lensOf sendLengths
    simp only [TK.arr, hlTree]
  have hDist : lens (sendLengths dist .dist) (dist.d_desc.max_code.toInt.toNat + 1) =
      Zlib.Inftrees.Proofs.lensOf (fun n => dist.dyn_dtree[n]!.dl.toNat) (MD + 1) := by
    rw [hDN]
    rfl
  obtain ⟨used, hused, hpositive, hbound⟩ := bl_prepare_used hI 256 (by decide +kernel) hEOB
  simp only [TK.descRef] at hrL hrD
  have hrun : blPrepare (Sp id) h = .ok ((), setD h id dist) := by
    have hpL : pLdesc (Sp id) h = .ok (some (.in_dstate_l_desc id), h) := by
      unfold pLdesc
      rw [bind_app, sid_run hI.base.dstate]
      rfl
    have hpD : pDdesc (Sp id) (setD h id lit) = .ok (some (.in_dstate_d_desc id), setD h id lit) := by
      unfold pDdesc
      rw [bind_app, sid_run (setD_dstates_same h id lit)]
      rfl
    unfold blPrepare
    rw [bind_app, hpL]
    simp only []
    rw [bind_app, hrL]
    simp only []
    rw [bind_app, hpD]
    exact hrD
  have he : used = dist := same_record_of_runs hused hrun
  subst used
  refine ⟨dist, hrun, ?_, ?_, ?_⟩
  · rw [hLit]
    exact haccL .litLen
  · rw [hDist]
    exact haccD .dist
  · change (lens (sendLengths dist .lit) (dist.l_desc.max_code.toInt.toNat + 1)).getD 256 0 ≠ 0
    have hi : 256 < dist.l_desc.max_code.toInt.toNat + 1 := by omega
    rw [lens, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    change dist.dyn_ltree[256]!.dl.toNat ≠ 0
    omega

/-- Actual BL construction preserves both independent source-alphabet
acceptance rules and END_BLOCK, including the scan sentinel writes. -/
theorem build_bl_preserves_source_format {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hin : BLInput d) (hf : SourceFormatData d) :
    ∃ (mb : Int32) (e : DeflateState), build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧ SourceFormatData e := by
  obtain ⟨mb, e, hr, hLD, hDD, hLT, hDT, hIe, hout⟩ := build_bl_preserves_source_codes hI hin
  have hL : lens (sendLengths e .lit) (e.l_desc.max_code.toInt.toNat + 1) =
      lens (sendLengths d .lit) (d.l_desc.max_code.toInt.toNat + 1) := by
    rw [hLD]
    apply lens_congr
    intro i hi
    change e.dyn_ltree[i]!.dl.toNat = d.dyn_ltree[i]!.dl.toNat
    rw [hLT i (by omega)]
  have hD : lens (sendLengths e .dist) (e.d_desc.max_code.toInt.toNat + 1) =
      lens (sendLengths d .dist) (d.d_desc.max_code.toInt.toNat + 1) := by
    rw [hDD]
    apply lens_congr
    intro i hi
    change e.dyn_dtree[i]!.dl.toNat = d.dyn_dtree[i]!.dl.toNat
    rw [hDT i (by omega)]
  exact ⟨mb, e, hr, ⟨hL.symm ▸ hf.lit, hD.symm ▸ hf.dist, hL.symm ▸ hf.eob⟩⟩

end Zlib.Trees.Proofs
