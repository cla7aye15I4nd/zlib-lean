import ZlibF.Math.DeflateHuffmanChain

/-!
Pure depth/height mathematics adapted from the pinned zlib-formal reference
`0f1428677ebf5b1614ff77f4702bbb382b2bf3c6`.
Imports and namespace use this project's tree shape and clamped levels.
The modular recurrence is retained until the level bound rules out wrap.
-/

namespace Zlib.Trees.Proofs.GB

section height
variable {H : Nat → Nat} {hm J elems maxc : Nat} {dl : Nat → Nat}

theorem dl_child (S : PShape H hm J elems maxc) (C : Clamped H hm J elems 1000 dl) {q i : Nat}
    (a : hm ≤ q) (b : q < 573) (e : H q = elems + i) {c : Nat} (hc : c = 572 - 2 * i ∨ c = 571 - 2 * i)
    (hcq : q < c) (hc2 : c < 573) : dl (H c) = dl (H q) + 1 := by
  have := S.hm_eq
  rw [dl_step S C (by omega) hc2]
  have hd : dadP elems c = H q := by unfold dadP; rw [e]; omega
  rw [hd]
  have := dl_le S C q a b
  omega

end height

end Zlib.Trees.Proofs.GB
