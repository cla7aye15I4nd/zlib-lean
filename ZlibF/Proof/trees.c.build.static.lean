import ZlibF.Proof.«trees.c.build.complete»
import ZlibF.Proof.«trees.c.inv»

/-! # trees.c: the three installed static tree descriptors -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees

/-- The actual installed descriptor selected by a dynamic tree. -/
def TK.buildDesc : TK → StaticTreeDesc
  | .lit => (trees_statics default).static_l_desc
  | .dist => (trees_statics default).static_d_desc
  | .bl => (trees_statics default).static_bl_desc

def TK.buildStaticRef : TK → StaticTreeDescRef
  | .lit => .st_static_l_desc
  | .dist => .st_static_d_desc
  | .bl => .st_static_bl_desc

/-- Extra-bit counts of the actual installed tables, including the literal
prefix with no extra bits. -/
def TK.buildExtra : TK → Nat → Nat
  | .lit, n => if n < 257 then 0 else extra_lbits_tab[n - 257]!.toInt.toNat
  | .dist, n => extra_dbits_tab[n]!.toInt.toNat
  | .bl, n => extra_blbits_tab[n]!.toInt.toNat

def TK.buildStaticLen : TK → Option (Nat → Nat)
  | .lit => some (fun n => static_ltree_tab[n]!.dl.toNat)
  | .dist => some (fun n => static_dtree_tab[n]!.dl.toNat)
  | .bl => none

/-- Installed descriptors are exactly the ones read by build_tree. -/
theorem trees_build_desc_get {h : Heap} (hs : Out.TreesStatic h.static) (tk : TK) :
    StaticTreeDescRef.get h tk.buildStaticRef = some tk.buildDesc := by
  cases tk
  · have he := congrArg Statics.static_l_desc hs
    change some h.static.static_l_desc = _
    rw [← he]
    rfl
  · have he := congrArg Statics.static_d_desc hs
    change some h.static.static_d_desc = _
    rw [← he]
    rfl
  · have he := congrArg Statics.static_bl_desc hs
    change some h.static.static_bl_desc = _
    rw [← he]
    rfl

set_option maxRecDepth 4096 in
/-- Every static-data premise of the construction theorem holds for the
actual installed tables. The finite value bounds are checked by the kernel. -/
theorem trees_build_static {h0 : Heap} {id : Nat} (hs : Out.TreesStatic h0.static) (tk : TK) :
    BTBuildStatic h0 id tk.buildDesc tk.buildExtra tk.buildStaticLen := by
  have hL : ∀ i : Fin 29, 0 ≤ extra_lbits_tab[i.val]!.toInt ∧ extra_lbits_tab[i.val]!.toInt ≤ 1000 := by decide +kernel
  have hD : ∀ i : Fin 30, 0 ≤ extra_dbits_tab[i.val]!.toInt ∧ extra_dbits_tab[i.val]!.toInt ≤ 1000 := by decide +kernel
  have hB : ∀ i : Fin 19, 0 ≤ extra_blbits_tab[i.val]!.toInt ∧ extra_blbits_tab[i.val]!.toInt ≤ 1000 := by decide +kernel
  have hSL : ∀ i : Fin 288, static_ltree_tab[i.val]!.dl.toNat ≤ 15 := by decide +kernel
  have hSD : ∀ i : Fin 30, static_dtree_tab[i.val]!.dl.toNat ≤ 15 := by decide +kernel
  cases tk
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
    · intro n hn
      change n < 286 at hn
      constructor
      · intro hbase
        change 257 ≤ n at hbase
        refine ⟨.st_extra_lbits, extra_lbits_tab, rfl, ?_, by change n - 257 < 29; omega, ?_, ?_, ?_⟩
        · intro e
          simp [Space.get, setD, hs.extra_lbits]
        · exact (hL ⟨n - 257, by omega⟩).1
        · exact (hL ⟨n - 257, by omega⟩).2
        · simp only [TK.buildExtra, ite_eq_right (show ¬ n < 257 by omega)]
          rfl
      · intro hbase
        change n < 257 at hbase
        simp only [TK.buildExtra, hbase, ite_true]
    · refine Or.inr ⟨.st_static_ltree, static_ltree_tab, (fun n => static_ltree_tab[n]!.dl.toNat), rfl, rfl, ?_, ?_⟩
      · intro e
        simp [Space.get, setD, hs.static_ltree]
      · intro n hn
        change n < 286 at hn
        exact ⟨by change n < 288; omega, hSL ⟨n, by omega⟩, rfl⟩
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
    · intro n hn
      change n < 30 at hn
      constructor
      · intro hbase
        refine ⟨.st_extra_dbits, extra_dbits_tab, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · intro e
          simp [Space.get, setD, hs.extra_dbits]
        · change n - 0 < 30; omega
        · exact (hD ⟨n, hn⟩).1
        · exact (hD ⟨n, hn⟩).2
        · rfl
      · intro hbase
        change n < 0 at hbase
        omega
    · refine Or.inr ⟨.st_static_dtree, static_dtree_tab, (fun n => static_dtree_tab[n]!.dl.toNat), rfl, rfl, ?_, ?_⟩
      · intro e
        simp [Space.get, setD, hs.static_dtree]
      · intro n hn
        change n < 30 at hn
        exact ⟨by change n < 30; exact hn, hSD ⟨n, hn⟩, rfl⟩
  · refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, Or.inl ⟨rfl, rfl⟩⟩
    intro n hn
    change n < 19 at hn
    constructor
    · intro hbase
      refine ⟨.st_extra_blbits, extra_blbits_tab, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro e
        simp [Space.get, setD, hs.extra_blbits]
      · change n - 0 < 19; omega
      · exact (hB ⟨n, hn⟩).1
      · exact (hB ⟨n, hn⟩).2
      · rfl
    · intro hbase
      change n < 0 at hbase
      omega


end Zlib.Trees.Proofs
