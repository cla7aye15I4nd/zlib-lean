import ZlibF.Proof.«trees.c.all-trees»
import ZlibF.Math.DeflateHeaderDecode
import ZlibF.Math.HuffmanZeroPadding

/-! # trees.c: independently decoding the emitted tree descriptions -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- Both terminal guards are facts about stored data, not callee contracts. -/
def SourceGuards (d : DeflateState) : Prop :=
  ∀ tk : TK, tk ≠ .bl →
    15 < sendLengths d tk ((tk.getDesc d).max_code.toInt.toNat + 1)

/-- The actual BL constructor retains the guards written by its two scans. -/
theorem build_bl_tree_source_guards {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (mb : Int32) (e : DeflateState),
      build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧ SourceGuards e := by
  obtain ⟨mb, scanned, built, e, B, hr, hs, hfreq, hframe, he, hmb, hlo, hhi, htail, hIe, hout, hcodes⟩ :=
    build_bl_tree_checked hI hin
  refine ⟨mb, e, hr, ?_⟩
  intro tk hne
  have hT := hframe.other_tree tk hne
  have hD := hframe.other_desc tk hne
  have hLs := hI.base.wf.1
  have hDs := hI.base.wf.2.1
  have hlm := hin.l286
  have hdm := hin.d30
  cases tk
  · change 15 < e.dyn_ltree[e.l_desc.max_code.toInt.toNat + 1]!.dl.toNat
    rw [he]
    change 15 < built.dyn_ltree[built.l_desc.max_code.toInt.toNat + 1]!.dl.toNat
    change built.dyn_ltree = scanned.dyn_ltree at hT
    change built.l_desc = scanned.l_desc at hD
    rw [hT, hD, hs]
    change 15 < (scGuard d.dyn_ltree d.l_desc.max_code.toInt.toNat)[d.l_desc.max_code.toInt.toNat + 1]!.dl.toNat
    rw [scGuard_lengths _ _ (by omega), guarded, ite_eq_left rfl]
    decide +kernel
  · change 15 < e.dyn_dtree[e.d_desc.max_code.toInt.toNat + 1]!.dl.toNat
    rw [he]
    change 15 < built.dyn_dtree[built.d_desc.max_code.toInt.toNat + 1]!.dl.toNat
    change built.dyn_dtree = scanned.dyn_dtree at hT
    change built.d_desc = scanned.d_desc at hD
    rw [hT, hD, hs]
    change 15 < (scGuard d.dyn_dtree d.d_desc.max_code.toInt.toNat)[d.d_desc.max_code.toInt.toNat + 1]!.dl.toNat
    rw [scGuard_lengths _ _ (by omega), guarded, ite_eq_left rfl]
    decide +kernel
  · exact False.elim (hne rfl)

/-- Stored data derived from actual construction make the two emitted
source-tree descriptions satisfy the independent code-length grammar. -/
theorem allTreeData_codeLens {d : DeflateState} {L D B : Nat}
    (hd : AllTreeData d L D B) (hg : SourceGuards d) (suffix : List Bool) :
    ZlibF.Spec.CodeLens
      (Zlib.Inftrees.Proofs.lensOf (fun n => d.bl_tree[n]!.dl.toNat) (d.bl_desc.max_code.toInt.toNat + 1))
      (L + D) []
      (sendTreeBits (blWords d) (sendLengths d .lit) (L - 1) ++
        sendTreeBits (blWords d) (sendLengths d .dist) (D - 1) ++ suffix)
      suffix (lens (sendLengths d .lit) L ++ lens (sendLengths d .dist) D) := by
  have hLC := hd.lit_count
  have hDC := hd.dist_count
  have hL0 := hd.lit_data.nonneg
  have hD0 := hd.dist_data.nonneg
  change 0 ≤ d.l_desc.max_code.toInt at hL0
  change 0 ≤ d.d_desc.max_code.toInt at hD0
  have hLN : d.l_desc.max_code.toInt.toNat + 1 = L := by omega
  have hDN : d.d_desc.max_code.toInt.toNat + 1 = D := by omega
  apply twoTrees_codeLens L D suffix (by have := hd.lit_min; omega) (by have := hd.dist_min; omega)
  · intro i hi
    apply hd.lit_data.lengths
    change i ≤ d.l_desc.max_code.toInt.toNat
    omega
  · intro i hi
    apply hd.dist_data.lengths
    change i ≤ d.d_desc.max_code.toInt.toNat
    omega
  · simpa only [TK.getDesc, hLN] using hg .lit (by decide +kernel)
  · simpa only [TK.getDesc, hDN] using hg .dist (by decide +kernel)
  · intro k r hk hp
    by_cases hleft : 0 < scanFreqUpTo (sendLengths d .lit) L k
    · exact (hd.lit_data.codes k hk (by simpa only [TK.getDesc, hLN] using hleft)).2 r
    · have hright : 0 < scanFreqUpTo (sendLengths d .dist) D k := by omega
      exact (hd.dist_data.codes k hk (by simpa only [TK.getDesc, hDN] using hright)).2 r

/-- Actual table data needed by the independent dynamic-header reader. -/
structure HeaderTableData (d : DeflateState) (B : Nat) : Prop where
  max_lt : d.bl_desc.max_code.toInt.toNat < 19
  upper_zero : ∀ v < 19, d.bl_desc.max_code.toInt.toNat < v → d.bl_tree[v]!.dl.toNat = 0
  omitted_zero : ∀ rank, B ≤ rank → rank < 19 → d.bl_tree[bl_order[rank]!.toNat]!.dl.toNat = 0
  acceptable : ZlibF.Spec.Acceptable .codeLength (lens (fun n => d.bl_tree[n]!.dl.toNat) 19)

/-- The actual constructor proves table acceptance, trailing-zero storage
and the omitted-rank condition on the same returned record. -/
theorem build_bl_tree_header_tables {h : Heap} {id b : Nat} {d : DeflateState} {buf : Array UInt8}
    (hI : TreesInvAt h id d b buf) (hin : BLInput d) :
    ∃ (mb : Int32) (e : DeflateState), build_bl_tree (Sp id) h = .ok (mb, setD h id e) ∧
      HeaderTableData e (mb.toInt.toNat + 1) := by
  obtain ⟨mb, scanned, built, e, B, hr, hs, hfreq, hframe, he, hmb, hlo, hhi, htail, hIe, hout, hcodes⟩ :=
    build_bl_tree_checked hI hin
  obtain ⟨mb2, e2, hr2, hlen, hupper, hIe2, hout2⟩ := build_bl_tree_all_lengths hI hin
  have heq : e2 = e := same_record_of_runs hr2 hr
  subst e2
  obtain ⟨M, hM, hdesc, hacc, hwords⟩ := hcodes
  have hmax : e.bl_desc.max_code.toInt.toNat = M := by rw [hdesc]; omega
  have hu : ∀ v < 19, e.bl_desc.max_code.toInt.toNat < v → e.bl_tree[v]!.dl.toNat = 0 := by
    intro v hv hm
    rw [hupper v hv hm]
    rfl
  refine ⟨mb, e, hr, ⟨by omega, hu, ?_, ?_⟩⟩
  · intro rank hrank hr19
    have ht := htail rank (by omega) (by omega)
    have hz : e.bl_tree[bl_order[rank]!.toNat]!.dl = 0 := by
      simpa only [blUsed, bne_eq_false_iff_eq] using ht
    rw [hz]
    rfl
  · have hpad := ZlibF.Spec.Proofs.acceptable_zeroPadding (19 - (M + 1)) hacc
    have hlens := lens_trailing_zeros (fun n => e.bl_tree[n]!.dl.toNat) (M + 1) 19
      (by omega) (fun i hi hi19 => hu i hi19 (by omega))
    change ZlibF.Spec.Acceptable .codeLength
      (lens (fun n => e.bl_tree[n]!.dl.toNat) (M + 1) ++ List.replicate (19 - (M + 1)) 0) at hpad
    rw [← hlens] at hpad
    exact hpad

/-- A padded nineteen-symbol BL table decodes the exact same emitted
source-tree bits as the constructor's trimmed table. -/
theorem allTreeData_codeLens_full {d : DeflateState} {L D B : Nat}
    (hd : AllTreeData d L D B) (hg : SourceGuards d) (ht : HeaderTableData d B) (suffix : List Bool) :
    ZlibF.Spec.CodeLens (lens (fun n => d.bl_tree[n]!.dl.toNat) 19) (L + D) []
      (sendTreeBits (blWords d) (sendLengths d .lit) (L - 1) ++
        sendTreeBits (blWords d) (sendLengths d .dist) (D - 1) ++ suffix)
      suffix (lens (sendLengths d .lit) L ++ lens (sendLengths d .dist) D) := by
  have hpad := ZlibF.Spec.Proofs.codeLens_zeroPadding
    (19 - (d.bl_desc.max_code.toInt.toNat + 1)) (allTreeData_codeLens hd hg suffix)
  have hlens := lens_trailing_zeros (fun n => d.bl_tree[n]!.dl.toNat)
    (d.bl_desc.max_code.toInt.toNat + 1) 19 (by have := ht.max_lt; omega)
    (fun i hi hi19 => ht.upper_zero i hi19 (by omega))
  rw [hlens]
  exact hpad

/-- The complete header model recovers its three actual count fields and
the complete acceptable BL table through the independent format readers. -/
theorem allTreeData_header_fields {d : DeflateState} {L D B : Nat}
    (hd : AllTreeData d L D B) (ht : HeaderTableData d B) (suffix : List Bool) :
    (do
      let (hlit, r1) ← ZlibF.Spec.readBits 5
        (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B ++ suffix)
      let (hdist, r2) ← ZlibF.Spec.readBits 5 r1
      let (hclen, r3) ← ZlibF.Spec.readBits 4 r2
      let (cl, r4) ← ZlibF.Spec.readCodeLenLens (hclen + 4) r3
      pure (hlit, hdist, hclen, cl, r4)) =
      some (L - 257, D - 1, B - 4, lens (fun i => d.bl_tree[i]!.dl.toNat) 19,
        sendTreeBits (blWords d) (sendLengths d .lit) (L - 1) ++
          sendTreeBits (blWords d) (sendLengths d .dist) (D - 1) ++ suffix) ∧
    ZlibF.Spec.DynamicCountsOK (L - 257) (D - 1) ∧
    ZlibF.Spec.Acceptable .codeLength (lens (fun i => d.bl_tree[i]!.dl.toNat) 19) := by
  refine ⟨?_, ⟨?_, ?_⟩, ht.acceptable⟩
  · exact allTreesBits_read_fields (blWords d) _ _ L D B suffix hd.lit_min hd.lit_max
      hd.dist_min hd.dist_max hd.bl_min hd.bl_max hd.bl_lengths ht.omitted_zero
  · have := hd.lit_min; have := hd.lit_max; omega
  · have := hd.dist_min; have := hd.dist_max; omega

/-- The header precedes any independently valid payload for its exact
two source alphabets. This is a header-composition lemma, not a proof that
the actual compressor produces the assumed payload symbols. -/
theorem allTreeData_dynamic_body {d : DeflateState} {L D B : Nat}
    (hd : AllTreeData d L D B) (hg : SourceGuards d) (ht : HeaderTableData d B)
    (heob : ZlibF.Spec.HasEndOfBlock (lens (sendLengths d .lit) L))
    (hL : ZlibF.Spec.Acceptable .litLen (lens (sendLengths d .lit) L))
    (hD : ZlibF.Spec.Acceptable .dist (lens (sendLengths d .dist) D))
    (dict history out : List UInt8) (payload rest : List Bool)
    (hp : ZlibF.Spec.Symbols (lens (sendLengths d .lit) L) (lens (sendLengths d .dist) D)
      dict history payload rest out) :
    ZlibF.Spec.Body dict 2 history
      (allTreesBits (blWords d) (sendLengths d .lit) (sendLengths d .dist) L D B ++ payload) rest out := by
  have hl : L - 257 + 257 = L := by have := hd.lit_min; omega
  have hd1 : D - 1 + 1 = D := by have := hd.dist_min; omega
  have hb : B - 4 + 4 = B := by have := hd.bl_min; omega
  have htL : (lens (sendLengths d .lit) L ++ lens (sendLengths d .dist) D).take L =
      lens (sendLengths d .lit) L := List.take_left' (lens_length _ _)
  have htD : (lens (sendLengths d .lit) L ++ lens (sendLengths d .dist) D).drop L =
      lens (sendLengths d .dist) D := List.drop_left' (lens_length _ _)
  simp only [allTreesBits, List.append_assoc]
  refine ZlibF.Spec.Body.dynamic (hlit := L - 257) (hdist := D - 1) (hclen := B - 4)
    (cl := lens (fun n => d.bl_tree[n]!.dl.toNat) 19)
    (r4 := sendTreeBits (blWords d) (sendLengths d .lit) (L - 1) ++
      (sendTreeBits (blWords d) (sendLengths d .dist) (D - 1) ++ payload)) (r5 := payload)
    (lens := lens (sendLengths d .lit) L ++ lens (sendLengths d .dist) D)
    (readBits_natBits 5 _ _ (by have := hd.lit_min; have := hd.lit_max; omega))
    (readBits_natBits 5 _ _ (by have := hd.dist_min; have := hd.dist_max; omega))
    (readBits_natBits 4 _ _ (by have := hd.bl_min; have := hd.bl_max; omega))
    (allTreeData_header_fields hd ht payload).2.1 ?_ ht.acceptable ?_ ?_ ?_ ?_ ?_
  · rw [hb]
    exact readCodeLenLens_blLensBits (blWords d) B _ hd.bl_max hd.bl_lengths ht.omitted_zero
  · rw [hl, hd1]
    simpa only [List.append_assoc] using allTreeData_codeLens_full hd hg ht payload
  · simpa only [hl, htL] using heob
  · simpa only [hl, htL] using hL
  · simpa only [hl, htD] using hD
  · simpa only [hl, htL, htD] using hp

end Zlib.Trees.Proofs
