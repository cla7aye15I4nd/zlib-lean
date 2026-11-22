import ZlibF.Proof.«inflate.c.entry-header»
import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.window-physical-history»
import ZlibF.Proof.«inflate.c.need-dict-sourcecut»
import ZlibF.Proof.«inflate.c.wrapper-output-credit»
import ZlibF.Spec.Common.Sequences
import ZlibF.Spec.Functional.Api.Goals
import ZlibF.Spec.Functional.Api.InflateAccepted

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem bytes_unique {h : Heap} {p : BPtr} {n : Nat} {xs ys : List UInt8}
    (one : Bytes h p n xs) (two : Bytes h p n ys) : xs = ys := by
  rcases one with ⟨null, _zero, empty⟩ | ⟨ref, off, array, pointer, get, _bound, values⟩
  · rcases two with ⟨_null, _zero, empty2⟩ | ⟨_ref, _off, _array, pointer, _⟩
    · exact empty.trans empty2.symm
    · rw [null] at pointer
      cases pointer
  · cases pointer
    rcases two with ⟨null, _⟩ | ⟨ref2, off2, array2, pointer, get2, _bound2, values2⟩
    · cases null
    · cases pointer
      have same : array = array2 := Option.some.inj (get.symm.trans get2)
      subst array2
      exact values.trans values2.symm

theorem inputAdvance_injective {p q : BPtr} {count : Nat}
    (equal : inputAdvance p count = inputAdvance q count) : p = q := by
  cases p with
  | null => cases q with
    | null => rfl
    | ref ref off => cases equal
  | ref ref off => cases q with
    | null => cases equal
    | ref ref2 off2 =>
      obtain ⟨sameRef, sameOff⟩ := Ptr.ref.inj equal
      have same : off = off2 := Nat.add_right_cancel sameOff
      cases sameRef
      cases same
      rfl

theorem dictionary_syncAlloc
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (invariant : DefaultStateJ h r zs z s)
    (stored : InflateDictionary h s history) : InflateDictionary (syncAlloc h) s history := by
  rcases invariant.good.inv.win.block with null | ⟨w, a, window, get, _readonly, size⟩
  · rcases stored with empty | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · have current := default_state_syncAlloc invariant
    have nextGet := (byte_view_syncAlloc (ref := .blk w) invariant.good.fresh get).1
    exact (dictionary_eq_saved current.good window nextGet size).mpr
      ((dictionary_eq_saved invariant.good window get size).mp stored)

theorem dictionary_free_local
    {h : Heap} {r : ZStreamRef} {zs block : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} {array : Array UInt8} (invariant : DefaultStateJ h r zs z s)
    (localGet : h.bytes block = some array) (localSize : array.size = 4)
    (stored : InflateDictionary h s history) :
    InflateDictionary (freeWin h (.ref (.blk block) 0)) s history := by
  rcases invariant.good.inv.win.block with null | ⟨w, a, window, get, _readonly, size⟩
  · rcases stored with empty | ⟨ref, off, bytes, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · have other : block ≠ w := by
      intro equal
      subst w
      rcases invariant.local_width with bits | none
      · exact default_local_not_window invariant.good localGet localSize bits window
      · rw [none] at window
        cases window
    have kept := freeWin_bytes_ne h (.ref (.blk block) 0) (b := w)
      (by intro w2 pointer; cases pointer; exact other)
    have current := invariant.free_local localGet localSize
    exact (dictionary_eq_saved current.good window (kept.1.trans get) size).mpr
      ((dictionary_eq_saved invariant.good window get size).mp stored)

theorem leave_active_origin
    {c : Ctx} {l : IL} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after))
    (get : after.istates zs = some state) (active : state.mode < CHECK) (lowOut : s.mode ≤ DICT → l.out_ = l.left) : s.mode < CHECK := by
  obtain ⟨otherRc, otherHeap, stream, current, source, final, _alloc, _next, _have, _put, _left, outcome⟩ :=
    inflate_leave_default_public_accounting E invariant allocator buffers bits lowOut
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have stateEq : current = state := Option.some.inj (final.good.live.hs.symm.trans get)
  subst current
  rcases outcome with ⟨_code, _fields, mode⟩ | ⟨_code, mem, _fields⟩
  · simpa only [mode] using active
  · rw [mem] at active
    exact False.elim ((by decide : ¬ MEM < CHECK) active)

#print axioms bytes_unique
#print axioms inputAdvance_injective
#print axioms dictionary_syncAlloc
#print axioms dictionary_free_local
#print axioms leave_active_origin

theorem bytes_zero {h : Heap} {p : BPtr} {values : List UInt8}
    (observed : Bytes h p 0 values) : values = [] := by
  rcases observed with ⟨_, _, empty⟩ | ⟨_, _, _, _, _, _, values⟩
  · exact empty
  · simpa only [List.take_zero] using values

#print axioms bytes_zero
theorem old_byte_view_free_new {initial bodyHeap : Heap} {ref : BRef} {array : Array UInt8}
    (fresh : Fresh initial) (get : Space.get initial ref = some array) :
    (Space.get (freeWin bodyHeap (syncBuf initial)) ref : Option (Array UInt8)) =
      Space.get bodyHeap ref := by
  cases ref with
  | blk block =>
    have other : block ≠ initial.nextBlk := by
      intro equal
      subst block
      have absent := (fresh_dead fresh (Nat.le_refl initial.nextBlk)).1
      change initial.bytes initial.nextBlk = some array at get
      rw [get] at absent
      cases absent
    exact (freeWin_bytes_ne bodyHeap (syncBuf initial)
      (by intro w pointer; cases pointer; exact Ne.symm other)).1
  | dstate_depth block => rfl
  | str value => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

theorem bytes_free_new_back
    {initial bodyHeap : Heap} {p : BPtr} {capacity count : Nat} {output : List UInt8}
    (fresh : Fresh initial) (writable : Writable initial p capacity)
    (observed : Bytes (freeWin bodyHeap (syncBuf initial)) p count output) :
    Bytes bodyHeap p count output := by
  rcases writable with ⟨null, _zero⟩ | ⟨ref, off, array, pointer, get, _readonly, _room⟩
  · rcases observed with empty | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl empty
    · rw [null] at pointer
      cases pointer
  · cases pointer
    rcases observed with ⟨null, _⟩ | ⟨ref2, off2, array2, pointer, get2, room, values⟩
    · cases null
    · cases pointer
      exact Or.inr ⟨ref, off, array2, rfl,
        by rw [old_byte_view_free_new fresh get] at get2; exact get2, room, values⟩

#print axioms old_byte_view_free_new
#print axioms bytes_free_new_back
end Zlib.Inflate.Proofs.WindowHistory
