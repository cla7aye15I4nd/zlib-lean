import ZlibF.Proof.«deflate.c.life.bound»
import ZlibF.Proof.«deflate.c.engine.encoded-state»
import ZlibF.Spec.Functional.Api.Compress

/-! # `deflateBound` of a default stream before its first output

At the default parameters (zlib wrapper, window and hash bits 15, default strategy) and before
any byte is consumed (`strstart = 0`), `deflateBound(strm, n)` is `compressBound(n)`.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The default branch of the bound is `compressBound`, saturation included. -/
theorem default_bound_tail_value (level : Int32) (fx st n : UInt64) :
    (boundTailP 15 15 level 0 6 fx st n).toNat = ZlibF.Spec.Api.compressBound n.toNat := by
  have guard : ((15 : UInt32) != 15 || (15 : UInt32) != 15 || (0 : Int32) == Z_FIXED) = false := by decide
  unfold boundTailP
  rw [ite_eq_right (by simp only [guard]; decide)]
  simp only []
  have s12 : (n >>> 12).toNat = n.toNat / 4096 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have s14 : (n >>> 14).toNat = n.toNat / 16384 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have s25 : (n >>> 25).toNat = n.toNat / 33554432 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have range := UInt64.toNat_lt n
  have sumNat : (n + (n >>> 12) + (n >>> 14) + (n >>> 25) + 13 - 6 + 6).toNat =
      (n.toNat + n.toNat / 4096 + n.toNat / 16384 + n.toNat / 33554432 + 13) % 18446744073709551616 := by
    simp only [UInt64.toNat_add, UInt64.toNat_sub, s12, s14, s25, UInt64.reduceToNat]
    omega
  have compare : (n + (n >>> 12) + (n >>> 14) + (n >>> 25) + 13 - 6 + 6 < n) ↔
      (n + (n >>> 12) + (n >>> 14) + (n >>> 25) + 13 - 6 + 6).toNat < n.toNat := UInt64.lt_iff_toNat_lt
  have unfolded : ZlibF.Spec.Api.compressBound n.toNat =
      if n.toNat + n.toNat / 4096 + n.toNat / 16384 + n.toNat / 33554432 + 13 ≥ 18446744073709551616
      then 18446744073709551615
      else n.toNat + n.toNat / 4096 + n.toNat / 16384 + n.toNat / 33554432 + 13 := by
    unfold ZlibF.Spec.Api.compressBound
    rfl
  rw [unfolded]
  have small : n.toNat / 4096 + n.toNat / 16384 + n.toNat / 33554432 + 13 < 18446744073709551616 := by
    omega
  generalize hX : n.toNat + n.toNat / 4096 + n.toNat / 16384 + n.toNat / 33554432 + 13 = X at sumNat ⊢
  generalize hB : (n + (n >>> 12) + (n >>> 14) + (n >>> 25) + 13 - 6 + 6) = B at sumNat compare ⊢
  by_cases big : X ≥ 18446744073709551616
  · have reduce : X % 18446744073709551616 = X - 18446744073709551616 := by
      rw [Nat.mod_eq_sub_mod big, Nat.mod_eq_of_lt (by omega)]
    have lt : B.toNat < n.toNat := by rw [sumNat, reduce]; omega
    rw [ite_eq_left big, ite_eq_left (compare.mpr lt)]
    rfl
  · have reduce : X % 18446744073709551616 = X := Nat.mod_eq_of_lt (by omega)
    have notLt : ¬ B < n := fun lt => by have := compare.mp lt; rw [sumNat, reduce] at this; omega
    rw [ite_eq_right big, ite_eq_right notLt, sumNat, reduce]

/-- **`deflateBound` before the first output**: on a default stream still in `INIT_STATE`, the
bound is `compressBound`. -/
theorem default_initial_bound_value {h after : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {n b : UInt64} (start : EngineStart h r ds z d)
    (run : C.run (deflateBound (some r) n) h = .ok (b, after)) :
    b.toNat = ZlibF.Spec.Api.compressBound n.toNat := by
  have body := boundBody_zlib start.good.live (Or.inl start.wrap) (fixedLen n) (storeLen n) n
  have wl : (6 + (if d.strstart != 0 then 4 else 0) : UInt64) = 6 := by rw [start.start]; rfl
  rw [wl, start.windowBits, start.hashBits, start.strategy] at body
  have computed : C.run (deflateBound (some r) n) h =
      .ok (boundTailP 15 15 d.level 0 6 (fixedLen n) (storeLen n) n, h) := by
    unfold deflateBound
    simp only [C.run, deflateBound_z_eq, body]
  obtain ⟨values, _⟩ := Prod.mk.inj (Except.ok.inj (computed.symm.trans run))
  rw [← values]
  exact default_bound_tail_value d.level (fixedLen n) (storeLen n) n

end Zlib.Deflate.Engine.Proofs
