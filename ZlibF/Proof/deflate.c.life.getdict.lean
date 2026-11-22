import ZlibF.Proof.«deflate.c.base»
import ZlibF.Proof.«deflate.c.engine.macros»

/-!
# deflate.c: `deflateGetDictionary`

`deflateGetDictionary` copies the last `len = min(strstart + lookahead, w_size)` bytes of the history that the window
holds into the caller's buffer, and reports `len`. It never changes the stream or the state. The stream check refuses a
stream that is not initialised with `Z_STREAM_ERROR`.
-/

namespace Zlib.Deflate.Spec
open C

/-- The number of bytes `deflateGetDictionary` returns: the history in the window, `strstart + lookahead`, at most
`w_size` (the sum is in `unsigned`; for a state with `strstart + lookahead <= window_size <= 2^16` it does not wrap). -/
def dictLen (d : DeflateState) : UInt32 :=
  if d.strstart + d.lookahead > d.w_size then d.w_size else d.strstart + d.lookahead

/-- The caller's buffer can take the `n` bytes: it is a writable byte block with room for them at its offset, and the
range does not overlap the source range `[src, src + n)` of the window (the two may share a block only if the ranges are
disjoint, as `memcpy` requires). -/
def DictDest (h : Heap) (d : DeflateState) (src n : Nat) (dictionary : BPtr) : Prop :=
  ∃ x off da, dictionary = .ref (.blk x) off ∧ h.bytes x = some da ∧ h.ro x = false ∧ off + n ≤ da.size ∧
    ∀ w, d.window = .ref (.blk w) 0 → (x ≠ w ∨ off + n ≤ src ∨ src + n ≤ off)

end Zlib.Deflate.Spec

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs

theorem dictLen_toNat {d : DeflateState} (hw : d.window_size.toNat = 2 * d.w_size.toNat)
    (hws : d.w_size.toNat ≤ 32768) (hfill : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    (dictLen d).toNat = min (d.strstart.toNat + d.lookahead.toNat) d.w_size.toNat := by
  have hs : (d.strstart + d.lookahead).toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  unfold dictLen
  by_cases hc : d.strstart + d.lookahead > d.w_size
  · simp only [hc, ite_true]
    have := UInt32.lt_iff_toNat_lt.mp hc
    omega
  · simp only [hc, ite_false]
    have : ¬ d.w_size.toNat < (d.strstart + d.lookahead).toNat := fun e => hc (UInt32.lt_iff_toNat_lt.mpr e)
    omega

theorem getdict_unfold {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (dictionary : BPtr) (hasDictLength : Bool) :
    deflateGetDictionary (some r) dictionary hasDictLength h =
      ((if dictionary != .null && dictLen d != 0 then
          (do let from_ ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
              memcpyB dictionary (← psub from_ (dictLen d).toNat) (dictLen d).toNat
              pure (Z_OK, if hasDictLength then some (dictLen d) else none) : M (Int32 × Option UInt32))
        else pure (Z_OK, if hasDictLength then some (dictLen d) else none)) h) := by
  unfold deflateGetDictionary
  dsimp' [stateCheck_live hL, hL.zst, hL.hz, hL.hs, dictLen]
  split <;> split <;> simp_all

/-- No copy: the buffer is `NULL`, or the history is empty. -/
theorem deflateGetDictionary_run_nocopy {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hL : DLive h r ds z d) (dictionary : BPtr) (hasDictLength : Bool)
    (hn : dictionary = .null ∨ dictLen d = 0) :
    deflateGetDictionary (some r) dictionary hasDictLength h =
      .ok ((Z_OK, if hasDictLength then some (dictLen d) else none), h) := by
  rw [getdict_unfold hL]
  have : ¬ (dictionary != .null && dictLen d != 0) = true := by
    rcases hn with e | e <;> simp [e]
  simp only [this]
  rfl

/-- **deflateGetDictionary, refusal.** On a stream the check refuses (including `NULL`): `Z_STREAM_ERROR`, no length
stored, nothing changes. -/
theorem deflateGetDictionary_reject {h : Heap} {strm : ZStreamPtr} (hD : StreamDom h strm) (hN : ¬ DInitialised h strm)
    (dictionary : BPtr) (hasDictLength : Bool) :
    C.run (deflateGetDictionary strm dictionary hasDictLength) h = .ok ((Z_STREAM_ERROR, none), h) := by
  unfold deflateGetDictionary
  exact check_refuse hD hN _ _

end Zlib.Deflate.Proofs
