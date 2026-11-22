import ZlibF.Proof.«public-roundtrip-uncompress»

/-! # Non-vacuity of `uncompress(compress(x)) = x`

`Goal.compress_uncompress_roundtrip_witness`: a caller heap with the one-byte source `"a"` and a
14-byte destination (`compressBound(1) = 14`) satisfies every premise of the `compress` half; and
for every output that `compress` can produce there, a second heap that holds it as the source, a
one-byte destination and a length cell satisfies every premise of the `uncompress` half.
-/

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The caller heap of `compress`: the source at block 0, the destination at block 1. -/
def wcHeap : Heap :=
  { Heap.empty with
    bytes := upd (upd Heap.empty.bytes 0 (some #[0x61])) 1 (some (Array.replicate 14 0))
    nextBlk := 2
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

/-- The caller heap of `uncompress`: the stream at block 0, the destination at block 1 and the
length cell at block 2. -/
def wuHeap (out : List UInt8) : Heap :=
  { Heap.empty with
    bytes := upd (upd (upd Heap.empty.bytes 0 (some out.toArray)) 1 (some #[0])) 2
      (some (lengthBytes 1).toArray)
    nextBlk := 3
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

theorem wc_fresh : Fresh wcHeap := by
  intro b hb hl
  have h0 : b ≠ 0 := by change 2 ≤ b at hb; omega
  have h1 : b ≠ 1 := by change 2 ≤ b at hb; omega
  simp [Heap.live, wcHeap, Heap.empty, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1] at hl

theorem wu_fresh (out : List UInt8) : Fresh (wuHeap out) := by
  intro b hb hl
  have h0 : b ≠ 0 := by change 3 ≤ b at hb; omega
  have h1 : b ≠ 1 := by change 3 ≤ b at hb; omega
  have h2 : b ≠ 2 := by change 3 ≤ b at hb; omega
  simp [Heap.live, wuHeap, Heap.empty, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2] at hl

theorem wc_uniq : Zlib.Deflate.Spec.Uniq wcHeap := by
  intro b
  by_cases h0 : b = 0
  · subst b; simp [wcHeap, Heap.empty, Zlib.Deflate.Spec.cnt]
  by_cases h1 : b = 1
  · subst b; simp [wcHeap, Heap.empty, Zlib.Deflate.Spec.cnt]
  simp [wcHeap, Heap.empty, Zlib.Deflate.Spec.cnt, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1]

theorem wu_uniq (out : List UInt8) : Zlib.Inflate.Spec.Uniq (wuHeap out) := by
  intro b
  by_cases h0 : b = 0
  · subst b; simp [wuHeap, Heap.empty, Zlib.Inflate.Spec.cnt]
  by_cases h1 : b = 1
  · subst b; simp [wuHeap, Heap.empty, Zlib.Inflate.Spec.cnt]
  by_cases h2 : b = 2
  · subst b; simp [wuHeap, Heap.empty, Zlib.Inflate.Spec.cnt]
  simp [wuHeap, Heap.empty, Zlib.Inflate.Spec.cnt, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1, upd_ne _ _ _ _ h2]

/-- The static strings fit. -/
theorem static_strings_fit (h : Heap) (i : Nat) (a : Array UInt8) (get : Space.get h (BRef.str i) = some a)
    (borrow : h.libcErrorBorrow = none) : a.size < ZlibF.PlatformMemory.byteObjectLimit := by
  have bounds : ∀ j : Fin strTable.size,
      (strBytes strTable[j]).size < ZlibF.PlatformMemory.byteObjectLimit := by
    decide +kernel
  by_cases inside : i < strTable.size
  · rw [C.LibcBorrow.source_view h i inside, Array.getElem?_eq_getElem inside] at get
    cases get
    exact bounds ⟨i, inside⟩
  · simp [BRef.get_str, staticStringBytes, inside, borrow] at get

set_option maxRecDepth 8192 in
theorem wc_fit : ZlibF.PlatformMemory.ByteObjectsFit wcHeap := by
  intro ref a get
  cases ref with
  | blk b =>
    by_cases zero : b = 0
    · subst b
      simp [BRef.get_blk, wcHeap, upd_ne] at get
      cases get
      decide
    · by_cases one : b = 1
      · subst b
        simp [BRef.get_blk, wcHeap] at get
        cases get
        decide
      · simp [Space.get, wcHeap, Heap.empty, upd_ne, zero, one] at get
  | str i => exact static_strings_fit wcHeap i a get rfl
  | dstate_depth i => simp [Space.get, wcHeap, Heap.empty] at get
  | st_dist_code =>
    cases get
    decide
  | st_length_code =>
    cases get
    decide

set_option maxRecDepth 8192 in
theorem wu_fit (out : List UInt8) (small : out.length ≤ 14) : ZlibF.PlatformMemory.ByteObjectsFit (wuHeap out) := by
  intro ref a get
  cases ref with
  | blk b =>
    by_cases zero : b = 0
    · subst b
      simp [BRef.get_blk, wuHeap, upd_ne] at get
      cases get
      simp only [List.size_toArray, ZlibF.PlatformMemory.byteObjectLimit]
      omega
    · by_cases one : b = 1
      · subst b
        simp [BRef.get_blk, wuHeap, upd_ne] at get
        cases get
        decide
      · by_cases two : b = 2
        · subst b
          simp [BRef.get_blk, wuHeap] at get
          cases get
          decide
        · simp [Space.get, wuHeap, Heap.empty, upd_ne, zero, one, two] at get
  | str i => exact static_strings_fit (wuHeap out) i a get rfl
  | dstate_depth i => simp [Space.get, wuHeap, Heap.empty] at get
  | st_dist_code =>
    cases get
    show wcHeap.static.dist_code.size < _
    decide
  | st_length_code =>
    cases get
    show wcHeap.static.length_code.size < _
    decide

/-- **`Goal.compress_uncompress_roundtrip_witness`.** -/
theorem compress_uncompress_roundtrip_witness : Goal.compress_uncompress_roundtrip_witness := by
  refine ⟨wcHeap, .ref (.blk 1) 0, 14, .ref (.blk 0) 0, 1, [0x61], wc_fresh, wc_uniq, rfl, wc_fit,
    fun _ => rfl, by simp, ?_, ?_, ?_, ?_, by decide, ?_⟩
  · exact Or.inr ⟨.blk 0, 0, #[0x61], rfl, by simp [Space.get, wcHeap, upd_ne], by decide, rfl⟩
  · exact Or.inr ⟨.blk 1, 0, Array.replicate 14 0, rfl, by simp [Space.get, wcHeap],
      rfl, by simp⟩
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · simp [compressRejected]
  · intro stored out bound len
    have bound14 : stored.toNat ≤ 14 := by
      have : Api.compressBound (1 : UInt64).toNat = 14 := by decide
      omega
    refine ⟨wuHeap out, .ref (.blk 1) 0, .ref (.blk 2) 0, .ref (.blk 0) 0, 1, wu_fresh out, wu_uniq out, rfl,
      wu_fit out (by omega), fun _ => rfl, ?_, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, by decide⟩
    · refine ⟨Or.inr ⟨.blk 2, 0, (lengthBytes 1).toArray, rfl, by simp [Space.get, wuHeap], by decide, ?_⟩,
        Or.inr ⟨.blk 2, 0, (lengthBytes 1).toArray, rfl, by simp [Space.get, wuHeap],
          rfl, by decide⟩⟩
      decide
    · refine Or.inr ⟨.blk 0, 0, out.toArray, rfl, by simp [Space.get, wuHeap, upd_ne], by simp; omega, ?_⟩
      simp [← len]
    · exact Or.inr ⟨.blk 1, 0, #[0], rfl, by simp [Space.get, wuHeap, upd_ne],
        rfl, by decide⟩
    · exact Or.inr (Or.inr (Or.inl (by decide)))
    · exact Or.inr (Or.inr (Or.inl (by decide)))
    · exact Or.inr (Or.inr (Or.inl (by decide)))

end ZlibF.Spec.Public.Proofs.RoundTrip

#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.compress_uncompress_roundtrip_witness
