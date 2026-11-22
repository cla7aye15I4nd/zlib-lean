import ZlibF.Proof.«trees.c.compress-source»

/-! # trees.c: complete fixed-code literal payload execution

This file covers every permitted symbol-buffer size, including the
default memLevel 8. The symbol buffer contains literals only. The entry
pending count is zero and at most ten bits are buffered, allowing the usual
seven entry bits plus a fixed-block header. No output-room or callee
contract is assumed. Initialization and block selection are outside its scope.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

/-- Words from the actual installed fixed literal/length table. -/
def fixedLiteralWords (k : Nat) : UInt16 × UInt16 :=
  (static_ltree_tab[k]!.fc, static_ltree_tab[k]!.dl)

set_option maxHeartbeats 1000000 in
/-- The finite table check includes every literal and its stored code word. -/
theorem fixed_literal_fits (k : Nat) (hk : k < 256) :
    CodeFits fixedLiteralWords k ∧ (fixedLiteralWords k).2.toNat ≤ 9 := by
  have checked : ∀ i : Fin 256,
      CodeFits fixedLiteralWords i.val ∧ (fixedLiteralWords i.val).2.toNat ≤ 9 := by
    unfold CodeFits
    decide +kernel
  exact checked ⟨k, hk⟩

/-- The actual fixed END_BLOCK entry is a seven-bit zero word. -/
theorem fixed_literal_end : fixedLiteralWords 256 = (0, 7) := by decide +kernel

/-- Fixed code bits for the first n original three-byte literal symbols. -/
def fixedLiteralPrefix (buf : Array UInt8) (offset n : Nat) : List Bool :=
  (List.range n).flatMap (fun i => codeBits fixedLiteralWords buf[offset + 3 * i + 2]!.toNat)

theorem fixedLiteralPrefix_succ (buf : Array UInt8) (offset n : Nat) :
    fixedLiteralPrefix buf offset (n + 1) = fixedLiteralPrefix buf offset n ++
      codeBits fixedLiteralWords buf[offset + 3 * n + 2]!.toNat := by
  simp [fixedLiteralPrefix, List.range_succ, List.flatMap_append]

theorem fixedLiteralPrefix_length (buf : Array UInt8) (offset n : Nat) :
    (fixedLiteralPrefix buf offset n).length ≤ 9 * n := by
  induction n with
  | zero => simp [fixedLiteralPrefix]
  | succ n ih =>
    rw [fixedLiteralPrefix_succ, List.length_append]
    have cost := (fixed_literal_fits buf[offset + 3 * n + 2]!.toNat
      (UInt8.toNat_lt _)).2
    simp only [codeBits, natBits_length]
    omega

/-- One actual loop body reads its original three bytes before writing.
The unread-byte and nine-bit emission bounds are derived from the entry
state and the completed prefix, rather than assumed as room contracts. -/
theorem cbFixedLiteralBody_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState}
    {buf0 buf : Array UInt8} {n i : Nat} (sx : UInt32)
    (ht : EmitState id b h0 d0 buf0 (fixedLiteralPrefix buf0 d0.lit_bufsize.toNat i) h d buf)
    (hp : d0.pending = 0) (hv : d0.bi_valid.toInt ≤ 10)
    (hcapacity : n + 1 ≤ d0.lit_bufsize.toNat) (hi : i < n) (hsx : sx.toNat = 3 * i)
    (hzero : buf0[d0.lit_bufsize.toNat + 3 * i]! = 0 ∧
      buf0[d0.lit_bufsize.toNat + 3 * i + 1]! = 0) :
    EWP (cbReadBody (Sp id) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) sx) h
      (fun next H => next.toNat = 3 * (i + 1) ∧ ∃ D B,
        EmitState id b h0 d0 buf0 (fixedLiteralPrefix buf0 d0.lit_bufsize.toNat (i + 1)) H D B) := by
  have hsize : buf0.size = 4 * d0.lit_bufsize.toNat := by
    rw [← ht.size, ht.inv.base.size, ht.payload_fields.2.2]
  have hlo : 128 ≤ d0.lit_bufsize.toNat := by
    rw [← ht.payload_fields.2.2]
    exact ht.inv.base.lit_lo
  have hhi : d0.lit_bufsize.toNat ≤ 32768 := by
    rw [← ht.payload_fields.2.2]
    exact ht.inv.base.lit_hi
  have hlen := fixedLiteralPrefix_length buf0 d0.lit_bufsize.toNat i
  have hread := cbReadSymbol_run ht sx (3 * i) d0.lit_bufsize.toNat hsx
    (by omega) rfl (by omega) (by simp only [hp, UInt64.toNat_zero]; omega)
  rw [hzero.1, hzero.2] at hread
  simp only [UInt8.toNat_zero, Nat.mul_zero, Nat.zero_add,
    show UInt32.ofNat 0 = 0 from rfl] at hread
  unfold cbReadBody
  refine EWP.read hread ?_
  simp only []
  unfold cbSymbol
  simp only [show ((0 : UInt32) == 0) = true from rfl, ite_true]
  have hbyte := UInt8.toNat_lt buf0[d0.lit_bufsize.toNat + 3 * i + 2]!
  have hfit := fixed_literal_fits _ hbyte
  have hroom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
      (fixedLiteralWords buf0[d0.lit_bufsize.toNat + 3 * i + 2]!.toNat).2.toNat ≤ 8 * buf.size := by
    apply ht.room _ (9 * i + 9)
    · omega
    · simp only [hp, UInt64.toNat_zero]
      omega
  have he := ht.payload_code .fixedLit buf0[d0.lit_bufsize.toNat + 3 * i + 2]!.toNat
    (by change _ < static_ltree_tab.size; rw [static_ltree_tab_size]; omega) hfit.1 hroom
  rw [← u8i_toInt buf0[d0.lit_bufsize.toNat + 3 * i + 2]!] at he
  refine EWP.bind he ?_
  rintro _ H ⟨D, B, htrace⟩
  refine EWP.pure ⟨?_, D, B, ?_⟩
  · rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [fixedLiteralPrefix_succ]
    exact htrace

end Zlib.Trees.Proofs
