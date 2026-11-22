import ZlibF.Proof.«gzwrite.c.flush-params»

/-!
# gzwrite.c: the runs inside `gzvprintf`

The pieces of `gzvprintf` that are not calls of a proved callee:

1. `gz_vacate_inv_run`: the first `gz_vacate` of `gzvprintf`, on a record in `GzInv`, returns 0 and changes nothing
   (W4 puts the pending input in the first half of `in`). The proof is that of `gz_vacate_safe_of`.
2. `PrintfArgs.at`: the format reads the same and the pointer arguments stay live on every later heap of the call.
   The argument domain (`GzArguments`) puts the format and every pointer argument apart from the blocks the handle
   owns, so a step that changes only owned blocks and keeps the `strerror` borrow keeps them (`bytes_of_post`,
   `get_of_frame`).
3. `vsnprintf_in`: `vsnprintf` into the `in` buffer at `in + o`, with room `size` (`o + size ≤ 2·size`, W3). For
   every result of its contract: on success the first `min(r, size - 1)` bytes and a NUL; on failure at most `size`
   bytes. Both write only the `in` buffer, which is a data buffer of the handle: `GzInv` holds after.
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs Zlib.Gzguts ZlibF.Spec.Public
open Zlib.Gzwrite.SafeInit (GzErrorSpec GzErrorOwn)
set_option autoImplicit false

section printfRun
variable {i : Nat}

/-! ## The first `gz_vacate` -/

/-- **`gz_vacate` on a record in `GzInv`** returns 0 and changes nothing. -/
theorem gz_vacate_inv_run {h : Heap} {s : GzState} {fs : Fs} (inv : GzInv h i s) (hm : s.mode = GZ_WRITE)
    (hsz : s.size ≠ 0) : Zlib.Gzwrite.gz_vacate (gzSt i) fs h = .ok ((0, fs), h) := by
  have hs := inv.common.record
  have w := inv.writer hm
  have hZ : ldZ (strmOf (gzSt i)) h = .ok (s.strm, h) := Zlib.Gzlib.Proofs.ldZ_run hs
  have hS : ldS (gzSt i) h = .ok (s, h) := Zlib.Gzlib.Proofs.ldS_run hs
  unfold Zlib.Gzwrite.gz_vacate
  rcases w.input with ⟨hn, -⟩ | ⟨-, a, ha, hle⟩
  · have hnull : (s.strm.next_in == .null) = true := by rw [hn]; rfl
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, ↓reduceIte]
  · obtain ⟨B, arr, hin, hB, -, hasz⟩ := (w.bufs hsz).1
    have hni : s.strm.next_in = .ref (.blk B) a := by rw [ha, hin]; simp [padv]
    have hnull : (Ptr.ref (BRef.blk B) a == (.null : BPtr)) = false := rfl
    have hg : Space.get h (BRef.blk B) = some arr := hB
    have h1 : Ptr.add (Ptr.ref (BRef.blk B) a) (s.strm.avail_in.toNat : Int) h =
        .ok (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat), h) :=
      Ptr.add_nat_ok (R := BRef) hg (by omega)
    have h2 : Ptr.add s.«in» (s.size.toNat : Int) h = .ok (Ptr.ref (BRef.blk B) s.size.toNat, h) := by
      rw [hin]
      have := Ptr.add_nat_ok (R := BRef) (h := h) (off := 0) (n := s.size.toNat) hg (by omega)
      rw [Nat.zero_add] at this
      exact this
    have h3 : Ptr.le (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) (Ptr.ref (BRef.blk B) s.size.toNat) h =
        .ok (true, h) := by
      have hlt : ¬ s.size.toNat < a + s.strm.avail_in.toNat := by omega
      have c1 : s.size.toNat ≤ arr.size ∧ a + s.strm.avail_in.toNat ≤ arr.size := ⟨by omega, by omega⟩
      have hlt' : Ptr.lt (Ptr.ref (BRef.blk B) s.size.toNat) (Ptr.ref (BRef.blk B) (a + s.strm.avail_in.toNat)) h =
          .ok (false, h) := by
        simp [Ptr.lt, hg, c1, hlt]
      simp only [Ptr.le, bind_app, hlt']
      rfl
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hZ,
      hnull, Bool.false_eq_true, ↓reduceIte, hS, hni, h1, h2, h3]

/-! ## The arguments of the call on later heaps -/

/-- The format and the pointer arguments of a `gzprintf` call past the mode test, on the heap `h0` of the call: the
argument domain (`GzArguments`) and the fit of the byte objects. -/
def PrintfArgs (h0 : Heap) (i : Nat) (s0 : GzState) (format : BPtr) (va : List VaArg) : Prop :=
  ZlibF.PlatformMemory.ByteObjectsFit h0 ∧
    ((∃ fmt, CString h0 format fmt) ∧ ∀ q, VaArg.str q ∈ va → ∀ b o, q = .ref (.blk b) o → ∃ a, h0.bytes b = some a) ∧
    (∀ b, ByteRoot format b → ¬ GzOwned h0 i s0 b) ∧
    ∀ q, VaArg.str q ∈ va → ∀ b, ByteRoot q b → ¬ GzOwned h0 i s0 b

/-- **The format reads the same, and the pointer arguments stay live, on a later heap** of the call that keeps the
`strerror` borrow. -/
theorem PrintfArgs.at {h0 H : Heap} {s0 : GzState} {fs : Fs} {P : Heap → Nat → GzState → Prop} {format : BPtr}
    {va : List VaArg} (A : PrintfArgs h0 i s0 format va) (post : GzPost h0 i s0 [] fs H P)
    (hbor : H.libcErrorBorrow = h0.libcErrorBorrow) :
    (∃ fmt, CString H format fmt) ∧ ∀ q, VaArg.str q ∈ va → ∀ b o, q = .ref (.blk b) o → ∃ a, H.bytes b = some a := by
  obtain ⟨-, ⟨⟨fmt, hc⟩, live⟩, nof, noa⟩ := A
  refine ⟨⟨fmt, bytes_of_post hc.1 nof post hbor, hc.2⟩, fun q hq b o hqb => ?_⟩
  obtain ⟨a, ha⟩ := live q hq b o hqb
  obtain ⟨-, s', -, -, -, ⟨fr, -⟩, -, -⟩ := post
  have fr' : Frame h0 H (GzOwned h0 i s0) := fr
  have hget := get_of_frame fr' hbor (BRef.blk b) o (fun x hx => by
    subst hqb
    have hxb : x = b := hx
    subst hxb
    exact ⟨Or.inl (by rw [ha]; simp), noa _ hq x rfl⟩)
  exact ⟨a, by rw [show H.bytes b = Space.get H (BRef.blk b) from rfl, hget]; exact ha⟩

/-! ## `vsnprintf` into the `in` buffer -/

/-- **`storeBytes` into the `in` buffer** keeps `GzInv` and writes only that buffer. -/
theorem in_storeBytes {H : Heap} {v : GzState} {fs : Fs} (inv : GzInv H i v) (hsz : v.size ≠ 0) {B : Nat}
    {arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr) (hro : H.ro B = false)
    {o : Nat} (bs : Array UInt8) (hfit : o + bs.size ≤ arr.size) (hfs : FileSystem fs) :
    ∃ H2 arr2, storeBytes (.ref (.blk B) o) bs H = .ok ((), H2) ∧ H2.bytes B = some arr2 ∧ arr2.size = arr.size ∧
      H2.ro B = false ∧ GzInv H2 i v ∧ GzPost H i v [] fs H2 GzInv := by
  by_cases hne : bs.isEmpty = true
  · refine ⟨H, arr, by unfold storeBytes; simp [hne], hB, rfl, hro, inv, (GetcUngetc.Eff.refl inv hfs).2⟩
  have hne' : bs.isEmpty = false := by simpa using hne
  obtain ⟨H2, run, st⟩ := GzRead.storeBytes_view H (BRef.blk B) o arr bs hB hro hfit
    (Fresh.slotUsed_next inv.common.fresh) hne'
  have hdB : GzRead.DataBuf v B := ⟨hsz, Or.inl hin⟩
  have hx : (copyRange arr bs o 0 bs.size).size = arr.size := size_copyRange _ _ _ _ _
  obtain ⟨inv2, hl2, ho2⟩ := GzRead.GzInv.stored inv st hB hx (Or.inl ⟨B, rfl, hdB⟩)
  have Bl : H.live B := inv.common.live B hdB.owned
  have hBn : B ≠ H.nextBlk := fun e => inv.common.fresh B (by omega) Bl
  have fr : Frame H H2 (GzOwned H i v) := by
    refine ⟨st.static.symm, st.allocOk.symm, st.garbage.symm, by rw [st.nextBlk]; omega,
      by rw [st.nalloc]; exact Nat.le_refl _, fun b hl hn => ?_⟩
    have hbB : b ≠ B := fun e => hn (e ▸ hdB.owned)
    have hbn : b ≠ H.nextBlk := fun e => inv.common.fresh b (by omega) hl
    exact ⟨st.bytes b (fun e => hbB (BRef.blk.inj e).symm), by rw [st.words], by rw [st.streams],
      by rw [st.gzheaders], st.dstates b (fun e => by cases e), by rw [st.istates], by rw [st.gzstates], st.ro b hbn⟩
  exact ⟨H2, _, run, st.view, hx, by rw [st.ro B hBn]; exact hro, inv2,
    post_frame inv.common.live hfs fr hl2 ho2 rfl rfl inv2⟩

/-- **A NUL into the `in` buffer** keeps `GzInv`. -/
theorem in_store0 {H : Heap} {v : GzState} {fs : Fs} (inv : GzInv H i v) (hw : v.mode = GZ_WRITE)
    (hsz : v.size ≠ 0) {B : Nat} {arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr)
    (hro : H.ro B = false) {n : Nat} (hn : n < arr.size) (hfs : FileSystem fs) :
    store8 (.ref (.blk B) n) 0 H = .ok ((), Space.put H (BRef.blk B) (arr.set! n 0)) ∧
      GzInv (Space.put H (BRef.blk B) (arr.set! n 0)) i v ∧
      GzPost H i v [] fs (Space.put H (BRef.blk B) (arr.set! n 0)) GzInv ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).bytes B = some (arr.set! n 0) ∧ (arr.set! n 0).size = arr.size ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).ro B = false ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).libcErrorBorrow = H.libcErrorBorrow ∧
      (Space.put H (BRef.blk B) (arr.set! n 0)).gzstates = H.gzstates := by
  have hg : Space.get H (BRef.blk B) = some arr := hB
  have hro' : Space.ro H (BRef.blk B) = false := hro
  obtain ⟨inv', ho, fr, hl⟩ := inv_in_put inv hw hsz hin hB hro (arr := arr.set! n 0) (by simp)
  refine ⟨Ptr.store_ok hg hro' hn, inv', post_frame inv.common.live hfs fr hl ho rfl rfl inv', ?_, by simp,
    hro, rfl, rfl⟩
  show upd H.bytes B (some (arr.set! n 0)) B = some (arr.set! n 0)
  exact upd_same _ _ _

/-- `vsnprintf` after its oracle call count. -/
theorem vsnprintf_app (dst : BPtr) (size : UInt64) (fmt : BPtr) (args : List VaArg) (fs : Fs) (h : Heap) :
    vsnprintf dst size fmt args fs h = (do
      let _ ← cstring fmt
      argsLive args
      let r := fs.printfRet fs.nprintf
      if 0 ≤ r then
        if size != 0 then
          let k := min r.toInt.toNat (size.toNat - 1)
          storeBytes dst ((fs.printfOut fs.nprintf ++ Array.replicate k 0).extract 0 k)
          let q ← dst.add k
          store8 q 0
        return r
      else
        let e := fs.printfErrno fs.nprintf
        setErrno (if e == 0 then EOVERFLOW else e)
        storeBytes dst ((fs.printfOut fs.nprintf).extract 0 size.toNat)
        return r : G Int32) { fs with nprintf := fs.nprintf + 1 } h := rfl

/-- **The pointer arguments are live**: `argsLive` returns and changes nothing. -/
theorem argsLive_ok {H : Heap} {va : List VaArg}
    (live : ∀ q, VaArg.str q ∈ va → ∀ b o, q = .ref (.blk b) o → ∃ a, H.bytes b = some a) :
    argsLive va H = .ok ((), H) := by
  have hall : va.any (argDangling H) = false := by
    rw [List.any_eq_false]
    intro x hx
    cases x with
    | str q =>
      cases q with
      | null => simp [argDangling]
      | ref r o =>
        cases r with
        | blk b =>
          obtain ⟨a, ha⟩ := live _ hx b o rfl
          simp [argDangling, ha]
        | _ => simp [argDangling]
    | _ => simp [argDangling]
  simp [argsLive, hall]

/-- **`vsnprintf` into the `in` buffer**, at `in + o` with room `size` (`o + size ≤ 2·size`), with a format that is
a string and live pointer arguments: it returns, keeps `GzInv` and the size of `in`, and changes only `in`. -/
theorem vsnprintf_in {h0 : Heap} {s0 : GzState} {fs0 fs : Fs} {H : Heap} {v : GzState}
    (E : GetcUngetc.Eff i h0 s0 fs0 fs H) (inv : GzInv H i v) (hw : v.mode = GZ_WRITE) (hsz : v.size ≠ 0)
    {B : Nat} {arr : Array UInt8} (hin : v.«in» = .ref (.blk B) 0) (hB : H.bytes B = some arr)
    (hasz : arr.size = 2 * v.size.toNat) {o : Nat} (ho : o ≤ v.size.toNat)
    {format : BPtr} {va : List VaArg} {fmt : List UInt8} (hc : CString H format fmt)
    (live : ∀ q, VaArg.str q ∈ va → ∀ b o, q = .ref (.blk b) o → ∃ a, H.bytes b = some a) :
    ∃ len fs' H', vsnprintf (.ref (.blk B) o) v.size.toUInt64 format va fs H = .ok ((len, fs'), H') ∧
      GetcUngetc.Eff i h0 s0 fs0 fs' H' ∧ GzInv H' i v ∧ ∃ arr', H'.bytes B = some arr' ∧ arr'.size = arr.size := by
  have hfs : FileSystem fs := E.2.1
  have hro : H.ro B = false := by
    obtain ⟨B', a', hin', hB', hro', -⟩ := ((inv.writer hw).bufs hsz).1
    rw [hin] at hin'
    cases hin'
    exact hro'
  have hf : cstring format H = .ok (fmt.toArray, H) := Zlib.GzFs.Proofs.cstring_of_CString hc
  have hl : argsLive va H = .ok ((), H) := argsLive_ok live
  have hS32 := v.size.toNat_lt
  have hsn64 : v.size.toUInt64.toNat = v.size.toNat := UInt32.toNat_toUInt64 _
  have hpos : 0 < v.size.toNat := by
    rcases Nat.eq_zero_or_pos v.size.toNat with e | e
    · exact absurd (UInt32.toNat_inj.mp (by rw [e]; rfl)) hsz
    · exact e
  have hsn : (v.size.toUInt64 != 0) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro e
    have := congrArg UInt64.toNat e
    rw [hsn64] at this
    simp at this
    omega
  rw [vsnprintf_app]
  by_cases hok : 0 ≤ fs.printfRet fs.nprintf
  · -- success: `min(r, size - 1)` oracle bytes and a NUL
    obtain ⟨k, hk⟩ : ∃ k, k = min (fs.printfRet fs.nprintf).toInt.toNat (v.size.toUInt64.toNat - 1) := ⟨_, rfl⟩
    have hkle : k ≤ v.size.toNat - 1 := by rw [hk, hsn64]; exact Nat.min_le_right _ _
    obtain ⟨out, hout⟩ : ∃ out, out = (fs.printfOut fs.nprintf ++ Array.replicate k 0).extract 0 k := ⟨_, rfl⟩
    have hks : out.size = k := by
      rw [hout, Array.size_extract, Array.size_append, Array.size_replicate]; omega
    obtain ⟨H2, arr2, run2, hB2, hsz2, hro2, inv2, P2⟩ :=
      in_storeBytes (fs := { fs with nprintf := fs.nprintf + 1 }) inv hsz hin hB hro (o := o) out
        (by rw [hks]; omega) hfs
    have hadd : Ptr.add (Ptr.ref (BRef.blk B) o) (k : Int) H2 = .ok (.ref (.blk B) (o + k), H2) :=
      Ptr.add_nat_ok (R := BRef) (show Space.get H2 (BRef.blk B) = some arr2 from hB2) (by omega)
    obtain ⟨run3, inv3, P3, hB3, hsz3, -⟩ := in_store0 (fs := { fs with nprintf := fs.nprintf + 1 }) inv2 hw hsz hin
      hB2 hro2 (n := o + k) (by omega) hfs
    refine ⟨fs.printfRet fs.nprintf, { fs with nprintf := fs.nprintf + 1 },
      Space.put H2 (BRef.blk B) (arr2.set! (o + k) 0), ?_,
      GetcUngetc.Eff.trans (GetcUngetc.Eff.trans E inv P2 (fun _ => Iff.rfl)) inv2 P3 (fun _ => Iff.rfl), inv3, _,
      hB3, by rw [hsz3, hsz2]⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hf,
      hl, hok, ↓reduceIte, hsn, ← hk, ← hout, run2, hadd, run3]
  · -- failure: `errno` and at most `size` oracle bytes, no NUL
    obtain ⟨junk, hj⟩ : ∃ junk, junk = (fs.printfOut fs.nprintf).extract 0 v.size.toUInt64.toNat := ⟨_, rfl⟩
    have hjs : junk.size ≤ v.size.toNat := by
      rw [hj, Array.size_extract, hsn64]; omega
    obtain ⟨e, he⟩ : ∃ e : Int32, e = (if fs.printfErrno fs.nprintf == 0 then EOVERFLOW
        else fs.printfErrno fs.nprintf) := ⟨_, rfl⟩
    obtain ⟨fs2, hfs2⟩ : ∃ fs2 : Fs, fs2 = { { fs with nprintf := fs.nprintf + 1 } with errno := e } := ⟨_, rfl⟩
    have hfsok : FileSystem fs2 := by rw [hfs2]; exact hfs
    obtain ⟨H2, arr2, run2, hB2, hsz2, hro2, inv2, P2⟩ :=
      in_storeBytes (fs := fs2) inv hsz hin hB hro (o := o) junk (by omega) hfsok
    have hset : setErrno e { fs with nprintf := fs.nprintf + 1 } H = .ok (((), fs2), H) := by rw [hfs2]; rfl
    refine ⟨fs.printfRet fs.nprintf, fs2, H2, ?_,
      GetcUngetc.Eff.trans E inv P2 (by rw [hfs2]; exact fun _ => Iff.rfl), inv2, _, hB2, hsz2⟩
    simp only [liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift, cbind_app, clift_app, cpure_app, hf,
      hl, hok, ↓reduceIte, ← he, ← hj, hset, run2]

end printfRun

end ZlibF.Spec.Public.GzSkeleton
