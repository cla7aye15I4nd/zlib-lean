import ZlibF.Proof.«infback.c.safety-reach»
import ZlibF.Proof.«public-infback-init»
import ZlibF.Proof.PlatformMemory
import ZlibF.Proof.«inflate.c.default-entry»
import ZlibF.Spec.Safety.Domains

/-!
# Callback decoder: the call clause is not vacuous

`Goal.inflateBack_call_domain`: a concrete history, a concrete pair of callbacks and a concrete
`CallbackProtocol` satisfy every premise of the call clause of `Goal.inflateBack_safety`.

The history is `inflateBackInit_` on `witnessHeap` with a 32768-byte window (block 2), then a
caller's edit that points `next_in` at the two bytes of block 1. The input callback reports the
end of the input; the output callback accepts every chunk. The protocol owns block 1, and its
invariant says that block 1 still holds the two bytes, that they are the input supplied so far, and
that the chunk in use is empty or is those two bytes.
-/

namespace ZlibF.Spec.Public.BackCallDomainProof
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec
  Zlib.Infback.Proofs Zlib.Infback.Safety ZlibF.Spec.Public.InflateBackInitProof
set_option autoImplicit false

/-- The input callback of the witness: no more input. -/
def noInput : InCb := fun _ _ h => .ok ((0, .null), h)

/-- The output callback of the witness: every chunk is accepted. -/
def takeOutput : OutCb := fun _ _ _ h => .ok (0, h)

/-- The window of the witness. -/
abbrev win : BPtr := .ref (.blk 2) 0

/-- The first chunk of the witness: the two bytes of block 1. -/
abbrev chunk : BPtr := .ref (.blk 1) 0

/-- The invariant of the witness protocol. -/
def witnessInvariant (h : Heap) (log : BackLog) : Prop :=
  h.bytes 1 = some #[49, 0] ∧ log.supplied = [49, 0] ∧
    (log.held = [] ∨ (log.held = [49, 0] ∧ log.active = chunk))

theorem frame_refl (own : Nat → Prop) (h : Heap) : Frame h h own :=
  ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem external_refl (own : Nat → Prop) {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (entry : CallbackEntry h r i window n) :
    ExternalFrame own h h ∧ SameBytePrefix h h window window n := by
  obtain ⟨z, s, valid, w, size⟩ := entry
  obtain ⟨-, -, -, -, -, -, -, -, -, -, wr, fresh, uniq, -⟩ := valid
  rw [w, size] at wr
  obtain ⟨xs, bytes⟩ := bytes_of_writable wr
  exact ⟨⟨frame_refl own h, fresh, uniq, fun _ dead live => absurd live dead, fun _ _ _ => rfl⟩, xs, bytes, bytes⟩

theorem chunk_bytes {h : Heap} (e : h.bytes 1 = some #[49, 0]) : Bytes h chunk 2 [49, 0] :=
  Or.inr ⟨.blk 1, 0, #[49, 0], rfl, e, by decide, rfl⟩

/-- The bytes of block 1 are not touched when the window slice of block 2 is restored. -/
theorem restore_bytes_one (h after : Heap) (n : Nat) :
    (restoreWindow h after win n).bytes 1 = after.bytes 1 := by
  unfold restoreWindow
  simp only [Space.get, Space.put]
  split
  · exact upd_ne _ _ _ _ (by decide)
  · rfl

/-- The protocol of the witness, for the stream record in block 0 and a state in block `i`. -/
def witnessProtocol (i n : Nat) (hi : i ≠ 1) :
    CallbackProtocol (.tab 0) i win n noInput .null takeOutput .null where
  own := fun b => b = 1
  invariant := witnessInvariant
  inputBound := 2
  disjoint := ⟨hi, fun b root => by
    have e : b = 0 := root
    omega⟩
  local_ := by
    intro h after log agree
    have e : h.bytes 1 = after.bytes 1 := by
      rw [← restore_bytes_one h after n]
      exact (agree.2.2.2.2.2 1 rfl).1
    unfold witnessInvariant
    rw [e]
  bounded := by
    intro h log inv
    rw [inv.2.1]
    exact Nat.le_refl _
  liveInput := by
    intro h log inv held
    rcases inv.2.2 with empty | ⟨full, active⟩
    · exact absurd empty held
    · rw [full, active]
      exact chunk_bytes inv.1
  inStep := by
    intro h log next entry inv
    obtain ⟨ext, same⟩ := external_refl (fun b => b = 1) entry
    refine ⟨0, .null, h, [], rfl, rfl, ext, same, fun ne => absurd rfl ne, ?_⟩
    exact ⟨inv.1, by simpa using inv.2.1, Or.inl rfl⟩
  outStep := by
    intro h log pointer n bytes entry inv _ _
    obtain ⟨ext, same⟩ := external_refl (fun b => b = 1) entry
    refine ⟨0, h, rfl, ext, same, ?_, inv.1, inv.2.1, inv.2.2⟩
    intro held
    rcases inv.2.2 with empty | ⟨full, active⟩
    · exact absurd empty held
    · rw [full, active]
      exact chunk_bytes inv.1

theorem witness_platform (i n : Nat) (hi : i ≠ 1) : BackPlatform (witnessProtocol i n hi) := by
  refine ⟨?_, ?_⟩
  · intro h log next count pointer after _ fit run
    have e : (Except.ok (((0 : UInt32), (Ptr.null : BPtr)), h) : Except Fault ((UInt32 × BPtr) × Heap)) =
        .ok ((count, pointer), after) := run
    injection e with e
    injection e with e1 e2
    injection e1 with e3 e4
    subst e2 e3
    exact ⟨fit, fun ne => absurd rfl ne⟩
  · intro h log pointer count rc after _ fit run
    have e : (Except.ok ((0 : Int32), h) : Except Fault (Int32 × Heap)) = .ok (rc, after) := run
    injection e with e
    injection e with e1 e2
    subst e2
    exact fit

theorem put_bytes (h : Heap) (v : ZStream) : (ZStreamRef.put h (.tab 0) v).bytes = h.bytes := by
  simp only [ZStreamRef.put]; split <;> rfl

theorem put_fields (h : Heap) (v : ZStream) :
    (ZStreamRef.put h (.tab 0) v).static = h.static ∧ (ZStreamRef.put h (.tab 0) v).allocOk = h.allocOk ∧
    (ZStreamRef.put h (.tab 0) v).garbage = h.garbage ∧ (ZStreamRef.put h (.tab 0) v).nextBlk = h.nextBlk ∧
    (ZStreamRef.put h (.tab 0) v).nalloc = h.nalloc ∧ (ZStreamRef.put h (.tab 0) v).ro = h.ro ∧
    (ZStreamRef.put h (.tab 0) v).words = h.words ∧ (ZStreamRef.put h (.tab 0) v).gzheaders = h.gzheaders ∧
    (ZStreamRef.put h (.tab 0) v).dstates = h.dstates ∧ (ZStreamRef.put h (.tab 0) v).istates = h.istates ∧
    (ZStreamRef.put h (.tab 0) v).gzstates = h.gzstates ∧
    ∀ b, b ≠ 0 → (ZStreamRef.put h (.tab 0) v).streams b = h.streams b := by
  simp only [ZStreamRef.put]
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun b ne => upd_ne _ _ _ _ ne⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- `int inflateBack(z_streamp strm, in_func in, void FAR *in_desc, out_func out, void FAR *out_desc)`.
The premises of the call clause of `Goal.inflateBack_safety` hold together: after
`inflateBackInit_` on `witnessHeap` and a caller's edit of `next_in` and `avail_in`, with the
callbacks `noInput` and `takeOutput`, the protocol `witnessProtocol` and the first chunk
`[49, 0]`. -/
theorem inflateBack_call_domain : Goal.inflateBack_call_domain := by
  obtain ⟨hf, hu, hg, hv, z0, hz0, hdz, -⟩ := public_witness_domain
  obtain ⟨hvn, hv0⟩ := version_value_read hv
  have wr : Writable witnessHeap win (2 ^ (15 : Int32).toInt.toNat) := public_witness_window (wb := 15) (by decide)
  have run1 : C.run (inflateBackInit_ (some (.tab 0)) 15 win (.ref (.blk 1) 0) 112) witnessHeap =
      .ok (Z_OK, backOkHeap witnessHeap (.tab 0) z0 win 15) :=
    inflateBackInit__success hz0 hf rfl hdz.1 hdz.2 hvn hv0 (by simp) (by decide) (by decide)
  have hd : BackInitArguments witnessHeap (.tab 0) (.ref (.blk 1) 0) := ⟨hf, hu, hg, hv, z0, hz0, hdz⟩
  have reach1 := BackSafeReachable.init hd (by decide) (by decide) wr (by simp) ⟨2, 0, rfl⟩ run1
  obtain ⟨z, s, valid, w, size, -⟩ := reach_init hd (by decide) (by decide) wr (by simp) run1
  generalize hh1 : backOkHeap witnessHeap (.tab 0) z0 win 15 = h1 at reach1 valid
  generalize hn : 2 ^ (15 : Int32).toInt.toNat = n at reach1 size
  have hi : witnessHeap.nextBlk ≠ 1 := by simp [witnessHeap]
  generalize witnessHeap.nextBlk = i at reach1 valid hi
  have hz1 : ZStreamRef.get h1 (.tab 0) = some z := valid.1
  let z' : ZStream := { z with next_in := chunk, avail_in := 2 }
  obtain ⟨est, eok, egar, enb, ena, ero, ewords, egzh, eds, eis, egs, estreams⟩ := put_fields h1 z'
  have rebuf : Rebuffer h1 (ZStreamRef.put h1 (.tab 0) z') (.tab 0) := by
    have shape := Zlib.Inflate.Proofs.shape_put hz1 z'
    refine ⟨Shape.fresh shape enb valid.2.2.2.2.2.2.2.2.2.2.2.1, Shape.uniq shape valid.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_,
      ⟨est.symm, eok.symm, egar.symm, Nat.le_of_eq enb.symm, Nat.le_of_eq ena.symm, ?_⟩,
      z, z', hz1, Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz1 z', rfl⟩
    · unfold LibraryGlobals
      rw [est]
      exact valid.2.2.2.2.2.2.2.2.2.2.2.2.2
    · intro b _ owned
      have ne : b ≠ 0 := by
        intro e
        subst e
        apply owned
        rintro ⟨z2, hz2, ⟨i2, s2, st2, hs2, own2⟩ | ⟨i2, s2, st2, -, -⟩⟩
        · have ez : z2 = z := Option.some.inj (hz2.symm.trans hz1)
          subst ez
          have ei : i2 = i := by
            have := st2.symm.trans valid.2.2.1
            injection this with this
            injection this
          subst ei
          have es : s2 = s := Option.some.inj (hs2.symm.trans valid.2.1)
          subst es
          rcases own2 with e | e
          · have hs0 : h1.istates 0 = some s2 := by rw [e]; exact hs2
            have hu1 := valid.2.2.2.2.2.2.2.2.2.2.2.2.1 0
            have hz0' : h1.streams 0 = some z2 := hz1
            rw [hs0, hz0'] at hu1
            simp [cnt] at hu1
            omega
          · rw [w] at e
            cases e
        · have ez : z2 = z := Option.some.inj (hz2.symm.trans hz1)
          subst ez
          have := st2.symm.trans valid.2.2.1
          injection this with this
          cases this
      rw [put_bytes, ewords, egzh, eds, eis, egs, ero]
      exact ⟨rfl, rfl, estreams b ne, rfl, rfl, rfl, rfl, rfl⟩
  have wr1 : Writable h1 win n := by
    have x := valid.2.2.2.2.2.2.2.2.2.2.1
    rw [w, size] at x
    exact x
  have same : SameBytePrefix h1 (ZStreamRef.put h1 (.tab 0) z') win win n := by
    obtain ⟨xs, bytes⟩ := bytes_of_writable wr1
    refine ⟨xs, bytes, ?_⟩
    rcases bytes with null | ⟨ref, off, a, ptr, get, room, eq⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, a, ptr, by rw [get_put]; exact get, room, eq⟩
  have ro : ∀ b, h1.live b → (ZStreamRef.put h1 (.tab 0) z').live b →
      (ZStreamRef.put h1 (.tab 0) z').ro b = h1.ro b := fun b _ _ => by rw [ero]
  have reach := BackSafeReachable.caller reach1 rebuf same ro
  obtain ⟨z'', valid'⟩ := reach_caller valid w size rebuf same ro
  have ez : z'' = z' :=
    Option.some.inj (valid'.1.symm.trans (Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz1 z'))
  subst ez
  have fit1 : ZlibF.PlatformMemory.ByteObjectsFit h1 := by
    rw [← hh1]
    unfold backOkHeap
    exact ZlibF.PlatformMemory.ByteObjectsFit.put_stream
      (ZlibF.PlatformMemory.ByteObjectsFit.of_storage_eq (after := allocIstHeap _ _)
        (ZlibF.PlatformMemory.ByteObjectsFit.put_stream inflate_default_witness_platform _ _) rfl rfl rfl) _ _
  have bytes1 : (ZStreamRef.put h1 (.tab 0) z').bytes 1 = some #[49, 0] := by
    rw [put_bytes, ← hh1]
    simp only [backOkHeap, allocIstHeap, put_bytes]
    simp [witnessHeap, upd_ne _ _ _ _ (show (1 : Nat) ≠ 2 by decide)]
  refine ⟨ZStreamRef.put h1 (.tab 0) z', .tab 0, i, win, n, z', s, noInput, .null, takeOutput, .null,
    witnessProtocol i n hi, [49, 0], by simp, ?_, reach, valid', chunk_bytes bytes1, ?_,
    ⟨bytes1, rfl, Or.inr ⟨rfl, rfl⟩⟩, ?_, ZlibF.PlatformMemory.ByteObjectsFit.put_stream fit1 _ _,
    witness_platform i n hi, fun _ => ⟨1, 0, rfl⟩⟩
  · intro e
    cases e
  · simp [Separate, z']
  · show (2 : Nat) < 2 ^ 48
    decide

#print axioms inflateBack_call_domain

end ZlibF.Spec.Public.BackCallDomainProof
