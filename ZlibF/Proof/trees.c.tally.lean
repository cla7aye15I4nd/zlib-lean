import ZlibF.Proof.«trees.c.align»

/-!
# trees.c: `_tr_tally`
-/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees

theorem length_code_le (i : Nat) (hi : i < 256) : (length_code_tab[i]'(by rw [length_code_tab_size]; exact hi)).toNat ≤ 28 := by
  have : ∀ j : Fin 256, (length_code_tab[j.val]'(by rw [length_code_tab_size]; exact j.isLt)).toNat ≤ 28 := by
    decide +kernel
  exact this ⟨i, hi⟩

theorem dist_code_le (i : Nat) (hi : i < 512) : (dist_code_tab[i]'(by rw [dist_code_tab_size]; exact hi)).toNat ≤ 29 := by
  have : ∀ j : Fin 512, (dist_code_tab[j.val]'(by rw [dist_code_tab_size]; exact j.isLt)).toNat ≤ 29 := by
    decide +kernel
  exact this ⟨i, hi⟩

theorem arr_get_bang (a : Array UInt8) (i : Nat) (hi : i < a.size) : a[i]! = a[i] := getElem!_pos a i hi

/-- `d_code(dist)` as a number (`dist` here is `dist - 1` of the symbol). -/
def dcodeN (d : Nat) : Nat := if d < 256 then (dist_code_tab[d]!).toNat else (dist_code_tab[256 + d / 128]!).toNat

/-- `d_code` reads `_dist_code` inside its bounds for `dist < 32768`; the code is at most 29. -/
theorem d_code_run {h : Heap} (hs : TreesStatic h.static) (dist : UInt32) (hd : dist.toNat < 32768) :
    ∃ c : UInt8, d_code dist h = .ok (c, h) ∧ c.toNat = dcodeN dist.toNat ∧ c.toNat ≤ 29 := by
  have hg : Space.get h BRef.st_dist_code = some dist_code_tab := by simp [Space.get, hs.dist_code]
  unfold d_code
  by_cases h1 : dist < 256
  · have h2 : dist.toNat < 256 := by simpa [UInt32.lt_iff_toNat_lt] using h1
    have hi : dist.toNat < dist_code_tab.size := by rw [dist_code_tab_size]; omega
    have e := Ptr.index_ok (off := 0) (i := dist.toNat) hg (by omega)
    unfold OkOn at e
    simp only [h1, ite_true]
    refine ⟨_, e, ?_, ?_⟩
    · have := arr_get_bang dist_code_tab dist.toNat hi
      simp only [dcodeN, h2, ite_true, Nat.zero_add]
      exact congrArg UInt8.toNat this.symm
    · exact dist_code_le _ (by omega)
  · have h2 : ¬ dist.toNat < 256 := by simpa [UInt32.lt_iff_toNat_lt] using h1
    have hsh : (dist >>> 7).toNat = dist.toNat / 128 := by
      rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
    have hidx : ((256 : UInt32) + (dist >>> 7)).toNat = 256 + dist.toNat / 128 := by
      rw [UInt32.toNat_add, hsh]; simp; omega
    have hi : 256 + dist.toNat / 128 < dist_code_tab.size := by rw [dist_code_tab_size]; omega
    have e := Ptr.index_ok (off := 0) (i := 256 + dist.toNat / 128) hg (by omega)
    unfold OkOn at e
    simp only [h1, ite_false]
    refine ⟨_, by rw [hidx, e], ?_, ?_⟩
    · have := arr_get_bang dist_code_tab (256 + dist.toNat / 128) hi
      simp only [dcodeN, h2, ite_false, Nat.zero_add]
      exact congrArg UInt8.toNat this.symm
    · exact dist_code_le _ (by omega)


theorem toNat_add_one_u32 {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]; have : (1 : UInt32).toNat = 1 := by decide
  rw [this]; omega

/-- The array with `Freq` of entry `i` incremented (`tree[i].Freq++`, modulo 2^16). -/
def bumpFc (a : Array CtData) (i : Nat) : Array CtData := a.set! i { (a[i]!) with fc := (a[i]!).fc + 1 }

theorem u8i_toInt (x : UInt8) : (u8i x).toInt = x.toNat := by
  unfold u8i
  have := x.toNat_lt
  exact i32_ofInt_toInt (by omega) (by omega)

/-- The record after the counting part of a match symbol. -/
def tallyMatchRec (D : DeflateState) (dist lc : UInt32) : DeflateState :=
  { D with «matches» := D.«matches» + 1, dyn_ltree := bumpFc D.dyn_ltree ((length_code_tab[lc.toNat]!).toNat + 257), dyn_dtree := bumpFc D.dyn_dtree (dcodeN (dist.toNat - 1)) }

@[simp] theorem bumpFc_size (a : Array CtData) (i : Nat) : (bumpFc a i).size = a.size := by
  simp [bumpFc]

/-- The record after `_tr_tally`. -/
def tallyRec (d : DeflateState) (dist lc : UInt32) : DeflateState :=
  if dist = 0 then { d with sym_next := d.sym_next + 1 + 1 + 1, dyn_ltree := bumpFc d.dyn_ltree lc.toNat }
  else tallyMatchRec { d with sym_next := d.sym_next + 1 + 1 + 1 } dist lc

theorem tallyRec_wf {d : DeflateState} (hw : d.WellFormed) (dist lc : UInt32) : (tallyRec d dist lc).WellFormed := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
  unfold tallyRec tallyMatchRec
  split <;> exact ⟨by simpa using w1, by simpa using w2, w3, w4, w5, w6⟩

theorem tallyRec_run {id : Nat} {d : DeflateState} (hr : TreesRun id d) (hroom : d.sym_next.toNat + 3 ≤ d.sym_end.toNat)
    (hm : d.sym_next.toNat % 3 = 0) (hsn : d.sym_next.toNat + 3 < 2 ^ 32) (dist lc : UInt32) :
    TreesRun id (tallyRec d dist lc) := by
  have e : (d.sym_next + 1 + 1 + 1).toNat = d.sym_next.toNat + 3 := by
    have e1 : (d.sym_next + 1).toNat = d.sym_next.toNat + 1 := toNat_add_one_u32 (by omega)
    have e2 : (d.sym_next + 1 + 1).toNat = d.sym_next.toNat + 2 := by
      rw [toNat_add_one_u32 (by rw [e1]; omega), e1]
    rw [toNat_add_one_u32 (by rw [e2]; omega), e2]
  unfold tallyRec tallyMatchRec
  split
  · exact ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf,
      by show (d.sym_next + 1 + 1 + 1).toNat ≤ d.sym_end.toNat; omega,
      by show (d.sym_next + 1 + 1 + 1).toNat % 3 = 0; omega⟩
  · exact ⟨hr.ldyn, hr.lstat, hr.ddyn, hr.dstat, hr.bldyn, hr.blstat, hr.bi_lo, hr.bi_hi, hr.bi_buf,
      by show (d.sym_next + 1 + 1 + 1).toNat ≤ d.sym_end.toNat; omega,
      by show (d.sym_next + 1 + 1 + 1).toNat % 3 = 0; omega⟩


end Zlib.Trees.Proofs.Out
