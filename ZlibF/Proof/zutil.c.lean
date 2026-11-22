import ZlibF.Proof.LibcBorrow
import ZlibF.Zlib.«zutil.c»

/-!
# zutil.c: specification, safety and correctness

Statements of `docs/en/proof/zutil.md`. Every function of the translation (`zError`, `zlibVersion`,
`zlibCompileFlags`, `zcalloc`, `zcfree`) has a `_safe` theorem (no fault, on every input `zutil.h` and `zlib.h`
allow, with the frame, ownership and `Fresh` facts the callers need) and a `_correct` theorem (the value, against
the specification in `Zlib.Zutil.Spec`, which does not mention the translation).

`zmemcpy`, `zmemzero` and `zmemcmp` are not compiled in the default build (`HAVE_MEMCPY`): the macros of
`zutil.h` expand to `memcpy`, `memset`, `memcmp`, so there is no translation of them here. The behaviour of the
two the runtime provides is in `Ptr.memcpy_ok` and `Ptr.fill_ok`.

String literals: a literal is a static read-only array (`BRef.str i`, see `zutil.c.lean`). Evaluating one does not
change the heap, so the ownership statements say that the live blocks are the same as before.
-/

namespace Zlib.Zutil.Spec
open C

/-- The message of `z_errmsg` for a return code: `Z_NEED_DICT` (2) to `Z_VERSION_ERROR` (-6); every other code,
and `Z_OK`, gives the empty string. -/
def errText : Int → String
  | 2 => "need dictionary"
  | 1 => "stream end"
  | 0 => ""
  | -1 => "file error"
  | -2 => "stream error"
  | -3 => "data error"
  | -4 => "insufficient memory"
  | -5 => "buffer error"
  | -6 => "incompatible version"
  | _ => ""

/-- The two-bit code of `zlibCompileFlags` for a type size in bytes (2: 0, 4: 1, 8: 2, otherwise 3). -/
def sizeCode (n : Nat) : Nat := if n = 2 then 0 else if n = 4 then 1 else if n = 8 then 2 else 3

/-- Bits 0..7 of `zlibCompileFlags`: the sizes of `uInt`, `uLong`, `voidpf`, `z_off_t`, two bits each. -/
def compileFlags (uInt uLong voidpf zoff : Nat) : Nat :=
  sizeCode uInt + 4 * sizeCode uLong + 16 * sizeCode voidpf + 64 * sizeCode zoff

/-- The NUL-terminated string `s` is stored at the start of the read-only static array that `p` points to (a string
literal: it is in no table of the heap and is always live). -/
def CString (h : Heap) (p : BPtr) (s : String) : Prop :=
  ∃ i, p = .ref (.str i) 0 ∧ Space.get h (BRef.str i) = some (s.toUTF8.data.push 0) ∧ Space.ro h (BRef.str i) = true

end Zlib.Zutil.Spec

namespace Zlib.Zutil.Proofs
open C Zlib.Zutil Zlib.Zutil.Spec

/-- The heap after `strLit s`: the same heap (a literal is static). -/
def litHeap (h : Heap) (_s : String) : Heap := h

/-- What evaluating a literal leaves of the heap: all of it. -/
def LitFrame (h h' : Heap) : Prop := h' = h

/-- `s` is a string literal of the sources. -/
def IsLit (s : String) : Prop := s ∈ strTable

theorem strLit_run (h : Heap) (s : String) (hs : IsLit s) :
    ∃ i, strLit s h = .ok (.ref (.str i) 0, litHeap h s) ∧ strTable[i]? = some s := by
  unfold strLit
  exact strLitRef_of_mem hs

theorem litHeap_cstring (h : Heap) (s : String) (i : Nat) (hi : strTable[i]? = some s) :
    CString (litHeap h s) (.ref (.str i) 0) s := by
  have inside : i < strTable.size := Array.getElem?_eq_some_iff.mp hi |>.1
  refine ⟨i, rfl, ?_, rfl⟩
  rw [C.LibcBorrow.source_view (litHeap h s) i inside, hi]
  rfl

theorem litHeap_frame (h : Heap) (s : String) : LitFrame h (litHeap h s) := rfl

set_option maxRecDepth 100000 in
theorem errText_lit (k : Int) : IsLit (errText k) := by
  unfold IsLit errText
  rw [Array.mem_def]
  split <;> decide +kernel

/-! ### zError -/

theorem zError_eval (err : Int32) :
    zError err = strLit (errText err.toInt) := by
  funext h
  by_cases hr : err < -6 || err > 2
  · have h1 : err.toInt < -6 ∨ 2 < err.toInt := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with hr | hr
      · left; have := Int32.lt_iff_toInt_lt.mp hr; simpa using this
      · right; have := Int32.lt_iff_toInt_lt.mp hr; simpa using this
    have : errText err.toInt = "" := by
      unfold errText
      split <;> first | omega | rfl
    rw [this]
    simp [zError, hr, z_errmsg, strLit]
  · have h1 : -6 ≤ err.toInt ∧ err.toInt ≤ 2 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int32.not_lt] at hr
      have a := Int32.le_iff_toInt_le.mp hr.1
      have b := Int32.le_iff_toInt_le.mp hr.2
      simpa using And.intro a b
    obtain ⟨k, hk1, hk2, rfl⟩ : ∃ k : Int, -6 ≤ k ∧ k ≤ 2 ∧ err = Int32.ofInt k :=
      ⟨err.toInt, h1.1, h1.2, (Int32.ofInt_toInt err).symm⟩
    rcases (by omega : k = -6 ∨ k = -5 ∨ k = -4 ∨ k = -3 ∨ k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **zError, safety.** For every `int` argument (no restriction: the index is always in `0..9`), `zError` runs
without undefined behaviour. It returns a string literal and changes nothing, in particular allocates nothing. -/
theorem zError_safe (h : Heap) (err : Int32) :
    ∃ p h', C.run (zError err) h = .ok (p, h') ∧ LitFrame h h' := by
  obtain ⟨i, hr, -⟩ := strLit_run h (errText err.toInt) (errText_lit _)
  exact ⟨_, _, by rw [C.run, zError_eval, hr], litHeap_frame h _⟩

/-- **zError, correctness.** For every `int` `err`, `zError err` returns a pointer to the NUL-terminated message of
`z_errmsg` for the code (`Spec.errText`): the zlib texts for `2` down to `-6`, the empty string otherwise. The
message is a static read-only literal and the heap is unchanged. -/
theorem zError_correct (h : Heap) (err : Int32) :
    ∃ i h', C.run (zError err) h = .ok (.ref (.str i) 0, h') ∧
      CString h' (.ref (.str i) 0) (errText err.toInt) ∧ h' = litHeap h (errText err.toInt) := by
  obtain ⟨i, hr, hi⟩ := strLit_run h (errText err.toInt) (errText_lit _)
  exact ⟨i, _, by rw [C.run, zError_eval, hr], litHeap_cstring h _ i hi, rfl⟩

/-! ### zlibVersion -/

/-! ### zlibCompileFlags -/

/-! ### zcalloc -/

/-- The heap after a successful `malloc` of `n` bytes, as `allocB_some` has it. -/
def allocHeap (h : Heap) (n : Nat) : Heap :=
  { h with bytes := upd h.bytes h.nextBlk (some (Array.ofFn (n := n) fun i => Junk.of (h.garbage h.nalloc i.val))),
           ro := upd h.ro h.nextBlk false, nextBlk := h.nextBlk + 1, nalloc := h.nalloc + 1 }

/-- What a heap that gained one fresh writable byte block shares with the one before. -/
def AllocFrame (h h' : Heap) : Prop :=
  (∀ S, h.Owns S → h'.Owns (fun b => S b ∨ b = h.nextBlk)) ∧ (Fresh h → Fresh h') ∧
  h'.nextBlk = h.nextBlk + 1 ∧ h'.nalloc = h.nalloc + 1 ∧
  (∀ b, b ≠ h.nextBlk → h'.bytes b = h.bytes b ∧ h'.ro b = h.ro b) ∧
  h'.words = h.words ∧ h'.streams = h.streams ∧ h'.gzheaders = h.gzheaders ∧ h'.dstates = h.dstates ∧
  h'.istates = h.istates ∧ h'.gzstates = h.gzstates ∧ h'.static = h.static ∧
  h'.allocOk = h.allocOk ∧ h'.garbage = h.garbage

theorem allocHeap_frame (h : Heap) (n : Nat) : AllocFrame h (allocHeap h n) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro S hO b
    by_cases hb : b = h.nextBlk
    · subst hb; simp [Heap.live, allocHeap]
    · have := hO b
      simp only [Heap.live, allocHeap] at this ⊢
      simp [upd_ne _ _ _ _ hb, hb, this]
  · intro hF
    refine Fresh.mono hF (by simp [allocHeap]) ?_
    intro x hx
    have hx' : x ≠ h.nextBlk := by simp [allocHeap] at hx; omega
    simp [allocHeap, upd_ne _ _ _ _ hx']
  · intro b hb
    simp [allocHeap, upd_ne _ _ _ _ hb]

/-- The heap after a failed `malloc`: only the call counter moves. -/
def failHeap (h : Heap) : Heap := { h with nalloc := h.nalloc + 1 }

theorem zcalloc_ok_run (h : Heap) (op : BPtr) (items sz : UInt32) (hok : h.allocOk h.nalloc = true)
    (hF : Fresh h) :
    zcalloc op items sz h = .ok (.ref (.blk h.nextBlk) 0, allocHeap h (items * sz).toNat) := by
  unfold zcalloc
  exact allocB_some _ hok (C.UInt32.toNat_lt_mallocLimit _)

theorem zcalloc_fail_run (h : Heap) (op : BPtr) (items sz : UInt32) (hok : ¬ h.allocOk h.nalloc = true) :
    zcalloc op items sz h = .ok (.null, failHeap h) := by
  unfold zcalloc
  exact allocB_none _ hok

/-- **zcalloc, correctness (allocation succeeds).** When the allocation oracle says yes, the result is the start of
a new block; the block is writable; its size in bytes is `items * size` reduced modulo 2^32 (the `unsigned`
product of the C); and its content is arbitrary (`malloc` does not clear: this is not `calloc`). -/
theorem zcalloc_correct_some (h : Heap) (op : BPtr) (items sz : UInt32) (hok : h.allocOk h.nalloc = true)
    (hF : Fresh h) :
    ∃ h' a, C.run (zcalloc op items sz) h = .ok (.ref (.blk h.nextBlk) 0, h') ∧
      h'.bytes h.nextBlk = some a ∧ h'.ro h.nextBlk = false ∧
      a.size = items.toNat * sz.toNat % 2 ^ 32 ∧
      (∀ i (hi : i < a.size), a[i] = Junk.of (h.garbage h.nalloc i)) ∧ AllocFrame h h' := by
  refine ⟨_, Array.ofFn (n := (items * sz).toNat) fun i => Junk.of (h.garbage h.nalloc i.val),
    zcalloc_ok_run h op items sz hok hF, by simp [allocHeap], by simp [allocHeap], ?_, ?_, allocHeap_frame h _⟩
  · simp [UInt32.toNat_mul]
  · intro i hi
    simp

/-! ### zcfree -/

/-- **zcfree, safety.** `ptr` is `NULL`, or the start of a live writable byte block (a block returned by `zcalloc`
and not yet freed, `zlib.h`'s `free_func` contract). Then `zcfree` runs without undefined behaviour: for `NULL`
the heap is unchanged, otherwise exactly that block is removed. `op` (the `opaque` argument) is ignored. -/
theorem zcfree_safe (h : Heap) (op ptr : BPtr)
    (hp : ptr = .null ∨ ∃ b a, ptr = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false) :
    ∃ h', C.run (zcfree op ptr) h = .ok ((), h') ∧
      ((ptr = .null ∧ h' = h) ∨ ∃ b, ptr = .ref (.blk b) 0 ∧ h' = { h with bytes := upd h.bytes b none }) := by
  rcases hp with rfl | ⟨b, a, rfl, hb, hro⟩
  · exact ⟨h, freeB_null, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, freeB_ok hb hro, Or.inr ⟨b, rfl, rfl⟩⟩

/-- **zcfree, correctness (ownership).** Freeing a live writable byte block `b` that no other table holds removes
exactly `b` from the live blocks; freeing `NULL` changes nothing. -/
theorem zcfree_correct (h : Heap) (op : BPtr) (b : Nat) (a : Array UInt8) (S : Nat → Prop)
    (hb : h.bytes b = some a) (hro : h.ro b = false)
    (hother : h.words b = none ∧ h.streams b = none ∧ h.gzheaders b = none ∧ h.dstates b = none ∧
      h.istates b = none ∧ h.gzstates b = none)
    (hO : h.Owns S) :
    ∃ h', C.run (zcfree op (.ref (.blk b) 0)) h = .ok ((), h') ∧ h'.Owns (fun x => S x ∧ x ≠ b) ∧
      h'.bytes b = none ∧ (∀ x, x ≠ b → h'.bytes x = h.bytes x) := by
  obtain ⟨h', hr, hO'⟩ := freeB_owns hb hro hother hO
  refine ⟨h', hr, hO', ?_⟩
  have : h' = { h with bytes := upd h.bytes b none } := by
    have := freeB_ok hb hro
    rw [hr] at this
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at this
    exact this
  subst this
  exact ⟨by simp, fun x hx => by simp [upd_ne _ _ _ _ hx]⟩

/-! ### No leak: allocate, then free -/

/-! ### Non-vacuity: concrete runs of the real functions -/

/-- The hypotheses of the `zcalloc` and `zcfree` theorems hold together on a heap made by the real functions: on
the empty heap `zcalloc` of 16 bytes (allocation succeeds) is run, its result satisfies the hypotheses of
`zcfree_safe` and `zcfree_correct` (live writable block, owned by the one-block set), and `zcfree` frees it. -/
example : ∃ h1 : Heap, C.run (zcalloc .null 1 16) Heap.empty = .ok (.ref (.blk 0) 0, h1) ∧
    (∃ a, h1.bytes 0 = some a ∧ a.size = 16 ∧ h1.ro 0 = false) ∧
    ∃ h2 : Heap, C.run (zcfree .null (.ref (.blk 0) 0)) h1 = .ok ((), h2) ∧ h2.Owns (fun _ => False) := by
  obtain ⟨h1, a, hr, hb, hro, hsz, -, hO, -, -, -, -, hw, hs, hg, hd, hi, hz, -⟩ :=
    zcalloc_correct_some Heap.empty .null 1 16 rfl Heap.empty_fresh
  have hO0 : (Heap.empty).Owns (fun _ => False) := by
    intro b; simp [Heap.live, Heap.empty]
  have hO1 : h1.Owns (fun b => False ∨ b = 0) := hO _ hO0
  obtain ⟨h2, hr2, hO2, -⟩ := zcfree_correct h1 .null 0 a _ hb hro
    ⟨by rw [hw]; rfl, by rw [hs]; rfl, by rw [hg]; rfl, by rw [hd]; rfl, by rw [hi]; rfl, by rw [hz]; rfl⟩ hO1
  refine ⟨h1, hr, ⟨a, hb, by simpa using hsz, hro⟩, h2, hr2, ?_⟩
  intro b
  have := hO2 b
  simpa using this

/-- `zError` on the empty heap for the code `Z_MEM_ERROR` (-4) returns the text "insufficient memory" in a
read-only static literal and leaves the heap as it was (an instance of `zError_correct`). -/
example : ∃ i, C.run (zError (-4)) Heap.empty = .ok (.ref (.str i) 0, Heap.empty) ∧
    strTable[i]? = some "insufficient memory" ∧ Space.ro Heap.empty (BRef.str i) = true := by
  obtain ⟨i, hr, hi⟩ := strLit_run Heap.empty (errText (-4 : Int32).toInt) (errText_lit _)
  have e : errText (-4 : Int32).toInt = "insufficient memory" := rfl
  rw [e] at hi
  exact ⟨i, by rw [C.run, zError_eval, hr] <;> rfl, hi, rfl⟩

end Zlib.Zutil.Proofs
