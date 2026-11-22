import ZlibF.Proof.«infback.c.back»
import ZlibF.Proof.«inflate.c.main.macros»

/-!
# infback.c: the input macros with the call-back `in`

`PULL`, `PULLBYTE` and `NEEDBITS` of `inflateBack()`. The bit algebra (`BitInv`, `PULLBYTE_succ`, `BITS_run`, `DROPBITS_run`,
`BYTEBITS_run`) is the one of `inflate()` (module `inflate.c.main.macros`): `PULLBYTE` of `infback.c` differs only in that
`PULL` may call `in` when no input is left.

The registers describe the rest `bs` of the chunk that `in` returned last (`BIn`); the chunk is in a block of `in` (`ownI`),
so `out`, the writes into the window and the record tables cannot change it.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- The registers describe the bytes `bs` left of the current chunk (`BitInv`), and a non-empty chunk is in an `ownI` block. -/
structure BIn (ownI : Nat → Prop) (h : Heap) (l : IL) (bs : List UInt8) : Prop where
  bit : BitInv h l bs
  own : bs = [] ∨ ∃ b off, l.next = .ref (.blk b) off ∧ ownI b

/-- The input is finite: a measure `μ` of what `in` can still deliver (it depends only on the blocks of `in`), and a call that
returns `n` bytes lowers it by at least `n`. Without it `inflateBack` may run for ever: zlib.h does not promise that `in`
eventually reports the end of input, and the model then runs out of fuel. -/
structure InFinite (c : BCtx) (ownI : Nat → Prop) (R : Heap → Prop) (μ : Heap → Nat) : Prop where
  step : ∀ h nx n nx' h', R h → c.inCb c.inDesc nx h = .ok ((n, nx'), h') → μ h' + n.toNat ≤ μ h
  local_ : ∀ h h', (∀ b, ownI b → h'.bytes b = h.bytes b) → μ h' = μ h

/-- The input still to be read: the bits held, the bytes of the chunk, and what `in` can still deliver (in bits). -/
def phi (μ : Heap → Nat) (h : Heap) (l : IL) : Nat := l.bits.toNat + 8 * l.have_.toNat + 8 * μ h

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem BIn.congr {ownI : Nat → Prop} {h h' : Heap} {l : IL} {bs : List UInt8}
    (hS : ∀ b, ownI b → h'.bytes b = h.bytes b) (B : BIn ownI h l bs) : BIn ownI h' l bs := by
  obtain ⟨⟨he, hn, hl⟩, ho⟩ := B
  refine ⟨⟨he, ?_, hl⟩, ho⟩
  rcases hn with e | ⟨r, a, off, hnx, hg, hsz, hbs⟩
  · exact Or.inl e
  · rcases ho with e | ⟨b, off', hb, hown⟩
    · exact Or.inl e
    · rw [hb] at hnx
      obtain ⟨h1, h2⟩ := Ptr.ref.inj hnx
      subst h1
      have hg' : h.bytes b = some a := hg
      refine Or.inr ⟨_, a, off, by rw [hb, h2], ?_, hsz, hbs⟩
      show h'.bytes b = some a
      rw [hS b hown, hg']

/-- `PULL()` when input is left: nothing happens. -/
theorem PULL_have {c : BCtx} {l : IL} {h : Heap} (hne : l.have_ ≠ 0) :
    runX (PULL c) l h = .ok ((.ok (), l), h) := by
  have hb : (l.have_ == 0) = false := by simpa using hne
  unfold PULL
  simp [runX_bind, runX_get, hne, runX_pure]

/-- `PULL()` with no input left and `in` returning a chunk of `n ≠ 0` bytes at `nx`. -/
theorem PULL_chunk {c : BCtx} {l : IL} {h h' : Heap} {n : UInt32} {nx : BPtr} (h0 : l.have_ = 0) (hn : n ≠ 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((n, nx), h')) :
    runX (PULL c) l h = .ok ((.ok (), { l with have_ := n, next := nx }), h') := by
  have hb : (n == 0) = false := by simpa using hn
  unfold PULL
  simp [runX_bind, runX_get, h0, hin, hn, runX_set, runX_pure, runX_lift]

theorem PULL_noinput {c : BCtx} {l : IL} {h h' : Heap} {nx : BPtr} (h0 : l.have_ = 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h')) :
    runX (PULL c) l h = .ok ((.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h') :=
  PULL_eof h0 hin

theorem PULLBYTE_c_eq (c : BCtx) {l : IL} {h : Heap} (hne : l.have_ ≠ 0) :
    runX (Zlib.Infback.PULLBYTE c) l h = runX Zlib.Inflate.PULLBYTE l h := by
  have hb : (l.have_ == 0) = false := by simpa using hne
  unfold Zlib.Infback.PULLBYTE Zlib.Inflate.PULLBYTE
  simp only [runX_bind, PULL_have hne, runX_get, hb, Bool.false_eq_true, ↓reduceIte, runX_set, runX_lift]
  generalize load8 l.next h = r1
  rcases r1 with e | ⟨a1, h1⟩
  · rfl
  simp only []
  generalize Ptr.add l.next 1 h1 = r2
  rcases r2 with e | ⟨a2, h2⟩
  · rfl
  simp only []
  generalize shl64 a1.toUInt64 l.bits h2 = r3
  rcases r3 with e | ⟨a3, h3⟩ <;> rfl

/-- `PULLBYTE` of `inflate()` with its pointer made explicit. -/
theorem PULLBYTE_nx {h : Heap} {l : IL} {b : UInt8} {r : BRef} {off : Nat} {a : Array UInt8} (hne : l.have_ ≠ 0)
    (hnext : l.next = .ref r off) (hg : (Space.get h r : Option (Array UInt8)) = some a) (hlt : off < a.size)
    (hb : a[off] = b) (hbits : l.bits.toNat < 64) :
    runX Zlib.Inflate.PULLBYTE l h = .ok ((.ok (), pulled l b (.ref r (off + 1))), h) := by
  have hne' : (l.have_ == 0) = false := by simpa using hne
  have hadd : OkOn h (l.next.add 1) (.ref r (off + 1)) := by
    rw [hnext]; exact Ptr.add_nat_ok (n := 1) hg (by omega)
  have hld : OkOn h (load8 l.next) b := by
    rw [hnext]
    have := Ptr.load_ok (h := h) (r := r) (off := off) hg hlt
    rw [hb] at this; exact this
  have hshl : shl64 b.toUInt64 l.bits h = .ok (b.toUInt64 <<< l.bits.toUInt64, h) := by
    rw [shl64_run _ _ hbits]; rfl
  unfold Zlib.Inflate.PULLBYTE
  rw [runX_bind, runX_get]
  simp only [hne', Bool.false_eq_true, ↓reduceIte]
  simp only [runX_bind, runX_set, runX_lift_ok hld, runX_lift_ok hadd, runX_lift_ok hshl]
  rfl

/-- The registers after a successful `PULLBYTE`/`NEEDBITS`: only `next`, `have`, `hold`, `bits` differ. -/
def InShape (l l' : IL) : Prop := l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits }

theorem InShape.refl (l : IL) : InShape l l := by cases l; rfl

theorem InShape.trans {l l1 l2 : IL} (a : InShape l l1) (b : InShape l1 l2) : InShape l l2 := by
  cases l; cases l1; cases l2; simp_all [InShape]

end Zlib.Infback.Proofs
