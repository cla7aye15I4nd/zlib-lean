import ZlibF.Spec.Common.StreamQueries
import ZlibF.Proof.«inflate.c.misc»
import ZlibF.Spec.Functional.StreamQueries
import ZlibF.Spec.Functional.Format.Checksum

/-! Fixed C array layout for the public decode-table query. The counterexample to the
condition without that layout is an impossible C object shape, not a reachable library bug. -/
namespace ZlibF.Spec.Public.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

private theorem refused_dom {h : Heap} {p : ZStreamPtr} (hr : RefusedInflate h p) : StreamDom h p := by
  rcases hr with hnull | ⟨r,z,rfl,hz,hbad⟩
  · exact Or.inl hnull
  · refine Or.inr ⟨r,z,rfl,hz,?_⟩
    rcases hbad with hza | hzf | hs | ⟨i,s,hstate,hsi,_⟩
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzf)
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr ⟨i,s,hstate,hsi⟩))

private theorem refused_not_initialised {h : Heap} {p : ZStreamPtr} (hr : RefusedInflate h p) : ¬ Initialised h p := by
  intro ⟨r',i',z',s',hp,hL⟩
  rcases hr with hn | ⟨r,z,hp',hz,hbad⟩
  · rw [hn] at hp; cases hp
  · rw [hp'] at hp
    cases hp
    have heq : z = z' := Option.some.inj (hz.symm.trans hL.hz)
    subst z'
    rcases hbad with ha | hf | hstate | ⟨i,s,hi,hs,hfail⟩
    · exact hL.zalloc ha
    · exact hL.zfree hf
    · have hh := hL.zst
      rw [hstate] at hh; cases hh
    · have hieq : i = i' := by
        have hh := hL.zst
        rw [hi] at hh
        cases hh
        rfl
      subst i'
      have hseq : s = s' := Option.some.inj (hs.symm.trans hL.hs)
      subst s'
      rcases hfail with hback | hlo | hhi
      · exact hback hL.back
      · exact (UInt32.not_lt.mpr hL.mode.1) hlo
      · exact (UInt32.not_lt.mpr hL.mode.2) hhi

private theorem refused_state_check {h : Heap} {p : ZStreamPtr} (hr : RefusedInflate h p) :
    inflateStateCheck p h = .ok (1, h) := by
  obtain ⟨v, hv, hclass⟩ := inflateStateCheck_total (refused_dom hr)
  rcases hclass with ⟨_, hi⟩ | ⟨rfl, _⟩
  · exact (refused_not_initialised hr hi).elim
  · exact hv

/-- The fixed C array bounds make pointer subtraction representable. No callee contract is assumed. -/
theorem codes_used_record {h : Heap} {r : ZStreamRef} {i : Nat}
    {z : ZStream} {s : InflateState} {n : Nat}
    (hv : InflateView h r i z s) (hsize : s.codes.size = 1732)
    (hnext : s.next = .ref (.istate_codes i) n) (hn : n ≤ s.codes.size) :
    C.run (inflateCodesUsed (some r)) h = .ok (UInt64.ofNat n, h) := by
  rcases hv with ⟨hz,hstate,hi,hback,ha,hf,hlo,hhi⟩
  have hl : Live h r i z s := ⟨hz,hi,hstate,hback,⟨hlo,hhi⟩,ha,hf⟩
  have hc : Space.get h (CodeRef.istate_codes i) = some s.codes := by simp [Space.get, hl.hs]
  have hd := Ptr.diff_ok hc (show n ≤ s.codes.size from hn)
    (show 0 ≤ s.codes.size by omega)
    (show -(2 ^ 63 : Int) ≤ (n : Int) - (0 : Nat) ∧ (n : Int) - (0 : Nat) < 2 ^ 63 by omega)
  have hd' : Ptr.diff (Ptr.ref (CodeRef.istate_codes i) n) (Ptr.ref (CodeRef.istate_codes i) 0) h =
      .ok (Int64.ofInt ((n : Int) - (0 : Nat)), h) := hd
  unfold C.run inflateCodesUsed
  isimp [stateCheck_live hl, hl.zst, hl.hz, hl.hs, hnext, codesP, hd']
  simp [ofInt_toUInt64]

/-- `unsigned long inflateCodesUsed(z_streamp strm)` includes clean refusal and the source's fixed array layout. -/
theorem inflate_codes_used : Goal.inflateCodesUsed := by
  constructor
  · intro h p hr
    unfold C.run inflateCodesUsed
    isimp [refused_state_check hr]
  · intro h r i z s n hv hsize hnext hn
    exact codes_used_record hv hsize hnext hn

end ZlibF.Spec.Public.Proofs
