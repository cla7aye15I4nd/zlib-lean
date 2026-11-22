import ZlibF.Proof.«inflate.c.window-pointer-run»
import ZlibF.Proof.«inflate.c.default-local-output-frame»
import ZlibF.Proof.«inflate.c.window-public-ring»
import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.window-state-frame»
import ZlibF.Spec.Functional.Inflate.InflateFastMatchHistory
import ZlibF.Proof.«inflate.c.leave-default-public-accounting»
import ZlibF.Proof.«inflate.c.leave-output-footprint»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»
import ZlibF.Proof.«inflate.c.default-state»

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The fast copier and public dictionary use the same chronological ring. -/
theorem saved_zero_eq_ring (a : Array UInt8) (ws wn wh : Nat) :
    Zlib.Inffast.Spec.MatchHistory.saved a ws wn wh 0 = ringList a ws wn wh := by
  simp only [Zlib.Inffast.Spec.MatchHistory.saved, ringList, Nat.zero_add,
    Array.getElem!_eq_getD]
  rfl

/-- The public predicate exposes exactly the saved bytes used by fast matches. -/
theorem dictionary_eq_saved {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {w : Nat} {a : Array UInt8} {history : List UInt8}
    (good : Good h r zs z s) (window : s.window = .ref (.blk w) 0)
    (get : h.bytes w = some a) (size : a.size = 2 ^ s.wbits.toNat) :
    InflateDictionary h s history ↔
      history = Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0 := by
  rw [saved_zero_eq_ring]
  exact inflateDictionary_eq_ring good window get size

#print axioms saved_zero_eq_ring
#print axioms dictionary_eq_saved
/-- A chronological dictionary has the exact fast-match saved view whenever
the real window exists. The lazy unallocated alternative represents only
an empty dictionary and has whave zero. -/
theorem dictionary_saved_or_lazy
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {history : List UInt8} (good : Good h r zs z s)
    (stored : InflateDictionary h s history) :
    (s.window = .null ∧ s.whave = 0 ∧ history = []) ∨
    ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧
      a.size = 2 ^ s.wbits.toNat ∧
      Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0 = history := by
  rcases good.inv.win.block with null | ⟨w, a, window, get, readonly, size⟩
  · rcases stored with ⟨zero, empty⟩ | ⟨ref, off, array, pointer, _⟩
    · exact Or.inl ⟨null, zero, empty⟩
    · rw [null] at pointer
      cases pointer
  · exact Or.inr ⟨w, a, window, get, readonly, size,
      ((dictionary_eq_saved good window get size).mp stored).symm⟩

#print axioms dictionary_saved_or_lazy
end Zlib.Inflate.Proofs.WindowHistory
