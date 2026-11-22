import ZlibF.Proof.«inflate.c.match-step»
import ZlibF.Spec.Common.History
import ZlibF.Spec.Functional.Api.Basic

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The existing public caller-range premise excludes the stream's actual
owned window, for every supported caller byte view. -/
theorem callerRange_private_window {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) {pointer : BPtr} {size : Nat} {writing : Bool}
    (range : CallerRange h r pointer size writing) {dest : BRef} {offset : Nat}
    (ptr : pointer = .ref dest offset) :
    ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w := by
  rcases range with null | ⟨_, _, unowned⟩
  · rw [ptr] at null
    cases null
  · intro w window same
    have root : ByteRoot pointer w := by rw [ptr, same]; exact rfl
    apply unowned w root
    exact ⟨z, good.live.hz, Or.inl ⟨zs, s, good.live.zst, good.live.hs, Or.inr window⟩⟩

/-- Extract the slow decoder's output view and private-window separation
from the public range. Cursor accounting remains an internal loop fact. -/
theorem callerRange_slow_output {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (good : Good h r zs z s) (l : IL) (range : CallerRange h r l.put l.left.toNat true)
    (nonnull : l.put ≠ .null) (count : l.left.toNat ≤ l.out_.toNat)
    (produced : ∀ dest offset, l.put = .ref dest offset → l.out_.toNat - l.left.toNat ≤ offset) :
    ∃ (dest : BRef) (array : Array UInt8) (outOffset : Nat),
      l.put = .ref dest outOffset ∧ Space.get h dest = some array ∧ Space.ro h dest = false ∧
      outOffset + l.left.toNat ≤ array.size ∧ l.left.toNat ≤ l.out_.toNat ∧
      l.out_.toNat - l.left.toNat ≤ outOffset ∧
      (∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w) := by
  have writable : Writable h l.put l.left.toNat := by
    rcases range with null | ⟨_, write, _⟩
    · exact False.elim (nonnull null)
    · exact write rfl
  rcases writable with ⟨null, _⟩ | ⟨dest, outOffset, array, ptr, get, write, room⟩
  · exact False.elim (nonnull null)
  · exact ⟨dest, array, outOffset, ptr, get, write, room, count, produced dest outOffset ptr,
      callerRange_private_window good range ptr⟩

end Zlib.Inflate.Proofs
