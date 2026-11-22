import ZlibF.Proof.«inflate.c.sync2»

/-!
# inflate.c: `inflateSync`, the whole call

The call makes the local array `buf[4]`, runs the search and frees `buf` before returning.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate _root_.Zlib.Inflate.Spec

theorem freeWin_bytes_ne (H : Heap) (p : BPtr) {b : Nat} (hp : ∀ w, p = .ref (.blk w) 0 → w ≠ b) :
    (freeWin H p).bytes b = H.bytes b ∧ (freeWin H p).ro b = H.ro b := by
  cases p with
  | null => exact ⟨rfl, rfl⟩
  | ref x o =>
    cases x with
    | blk w =>
      cases o with
      | zero => have := hp w rfl; simp [freeWin, upd_ne _ _ _ _ (Ne.symm this)]
      | succ o => exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩

theorem win_ne_buf {h : Heap} {st : InflateState} (hF : Fresh h) (hW : WinInv h st) :
    ∀ w, st.window = .ref (.blk w) 0 → w ≠ h.nextBlk := by
  intro w hw e
  subst e
  rcases hW.block with hn | ⟨w', a, hw', ha, -⟩
  · rw [hn] at hw; cases hw
  · rw [hw] at hw'
    have := (BRef.blk.inj (Ptr.ref.inj hw').1)
    subst this
    obtain ⟨e0, -⟩ := fresh_dead hF (Nat.le_refl _)
    rw [ha] at e0; cases e0

theorem good_freeBuf {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {nb : Nat}
    (hG : Good H r zs z st) (hn : ∀ w, st.window = .ref (.blk w) 0 → w ≠ nb) :
    Good (freeWin H (.ref (.blk nb) 0)) r zs z st := by
  obtain ⟨⟨hz, hs, zst, back, hm, za, zf⟩, ⟨wf, win, rq, bits, ptr⟩, hU, hF⟩ := hG
  refine ⟨⟨by simpa using hz, by simpa using hs, zst, back, hm, za, zf⟩, ⟨wf, ?_, rq, bits, ptr⟩,
    uniq_freeWin hU _, fresh_freeWin hF _⟩
  refine ⟨win.wbits, ?_, win.nullws, win.ws, win.hv, win.wn, win.eq⟩
  rcases win.block with h0 | ⟨w, a, hw, ha, hro, hsz⟩
  · exact Or.inl h0
  · have hne := hn w hw
    have := freeWin_bytes_ne H (.ref (.blk nb) 0) (b := w) (by intro w' e; have := BRef.blk.inj (Ptr.ref.inj e).1; subst this; exact Ne.symm hne)
    exact Or.inr ⟨w, a, hw, by rw [this.1]; exact ha, by rw [this.2]; exact hro, hsz⟩

end Zlib.Inflate.Proofs
