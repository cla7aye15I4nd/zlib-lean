import ZlibF.Proof.«public-compress-safe»
import ZlibF.Proof.«public-compress-safe-mid»
import ZlibF.Proof.«public-uncompress-wrappers»

/-!
# compress.c: safety of the C-ABI wrappers `compress2_z_c`, `compress2_c`, `compress_z_c`, `compress_c`

Proves `CompressorCSafety` (pointer-cell `destLen : PtrU64` contract) for the C-ABI companion
definitions exported by `Lean2C.Simple`, reusing `compressReach_mid`, `goalDeflate_mid`,
`loopFacts_mid`, `init_cases`, `loop_result`, `epilogue`, `deflate_end_public`, and the 8-byte
scalar cell infrastructure (`public-uncompress-memory`, `public-uncompress-cells`).
-/

namespace ZlibF.Spec.Public.Proofs.Compress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Compress Zlib.Deflate Zlib.Gzguts
open ZlibF.Spec.Public.Proofs.Uncompress hiding measure
open Zlib.Deflate.Spec (DGood DLive DStInv DBlocks)
open Zlib.Trees.Proofs.Out (TreesInv TreesInvAt TreesBase TreesRun)
open Zlib.Inflate.Proofs (byte_view_get_put)
open ZlibF.Spec.Public.DeflateEndProof (deflate_end_public)
variable {R : Heap → ZStreamRef → Prop}
set_option autoImplicit false

/-- **Safety of a pointer-cell compressor entry**: runs without undefined behavior (`C.run … = .ok`),
returns `Z_STREAM_ERROR` without mutating objects on rejected arguments, writes at most `capacity`
bytes at `dest` and the resulting length to `destLen`, releases all temporary allocations, and
blames `Z_MEM_ERROR` only on an allocator failure. -/
def CompressorCSafety
    (program : BPtr → BPtr → BPtr → UInt64 → M Int32)
    (nullableLength : Bool) : Prop :=
  ∀ h dest destLen source capacity n xs,
    Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (nullableLength = false → destLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat xs) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    Separate source n.toNat dest capacity.toNat →
    Separate destLen 8 dest capacity.toNat →
    Separate destLen 8 source n.toNat →
    ∃ rc after,
      C.run (program dest destLen source n) h = .ok (rc, after) ∧
      (compressRejected dest (if destLen = .null then none else some capacity) source n →
        rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape h after) ∧
      (destLen ≠ .null → (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out got h₁ expected,
          Store h dest out h₁ ∧
          Store h₁ destLen (lengthBytes got) expected ∧
          SameObjectsUpToTableShape expected after ∧
          out.length ≤ capacity.toNat ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

private theorem version_gz_run (h : Heap) :
    Zlib.GzFs.strLit ZLIB_VERSION h = .ok (.ref (.str 57) 0, h) := by
  simpa [Zlib.GzFs.strLit, Zlib.Zutil.zlibVersion, Zlib.Zutil.strLit] using version_run h

private theorem allocLocalZ_run {h : Heap} (fresh : Fresh h) :
    allocLocalZ h = .ok (some (.tab h.nextBlk),
      { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1 }) := by
  have slot : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false := fresh.slotUsed_next
  simp [allocLocalZ, allocZStream, slot]

private theorem freeZStream_local_zero {h : Heap} :
    freeZStream (some (.tab h.nextBlk))
      { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1 } =
      .ok ((), { h with streams := upd (upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc)))) h.nextBlk none,
                         nextBlk := h.nextBlk + 1 }) := by
  simp [freeZStream]

private theorem same_freeZStream_local {h : Heap} (fresh : Fresh h) :
    SameObjectsUpToTableShape h
      { h with streams := upd (upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc)))) h.nextBlk none,
               nextBlk := h.nextBlk + 1 } := by
  have nl := fresh h.nextBlk (Nat.le_refl _)
  simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at nl
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun b => ?_, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, Nat.le_succ _, Nat.le_refl _⟩
  by_cases eb : b = h.nextBlk
  · subst eb; simp [nl.2.2.1]
  · simp [upd_ne _ _ _ _ eb]

private theorem writeOut_fresh {h : Heap} {q : BPtr} {xs : List UInt8} (f : Fresh h) :
    Fresh (writeOut h q xs) := by
  intro b hb live
  have nb : (writeOut h q xs).nextBlk = h.nextBlk := (writeOut_globals h q xs).2.2.2.1
  rw [nb] at hb
  exact f b hb ((writeOut_live b).1 live)

private theorem writeOut_uniq {h : Heap} {q : BPtr} {xs : List UInt8} (u : Zlib.Deflate.Spec.Uniq h) :
    Zlib.Deflate.Spec.Uniq (writeOut h q xs) := by
  by_cases ex : xs = []
  · subst ex; rw [writeOut_nil]; exact u
  cases q with
  | null => exact u
  | ref r i =>
    cases g : Space.get h r with
    | none => rw [writeOut_none g]; exact u
    | some a =>
      rw [writeOut_some g ex]
      cases r with
      | blk c =>
        intro b
        have ub := u b
        simp only [Space.get] at g
        simp only [Space.put, upd_apply, Zlib.Deflate.Spec.cnt] at ub ⊢
        split
        · subst b; simp [g] at ub ⊢; exact ub
        · exact ub
      | dstate_depth c =>
        intro b
        have ub := u b
        simp only [Space.get] at g
        cases ds : h.dstates c with
        | none => rw [ds] at g; cases g
        | some st =>
          simp only [Space.put, ds, upd_apply, Zlib.Deflate.Spec.cnt] at ub ⊢
          by_cases hbc : b = c
          · subst hbc; simp [ds] at ub ⊢; exact ub
          · simp [hbc] at ub ⊢; exact ub
      | str _ => exact u
      | st_dist_code => exact u
      | st_length_code => exact u

private theorem writeOut_globals_eq {h : Heap} {q : BPtr} {xs : List UInt8} (g : LibraryGlobals h) :
    LibraryGlobals (writeOut h q xs) := by
  unfold LibraryGlobals
  rw [(writeOut_globals h q xs).1]
  exact g

private theorem writeOut_fit {h : Heap} {q : BPtr} {xs : List UInt8}
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h) (w : Writable h q xs.length) :
    ZlibF.PlatformMemory.ByteObjectsFit (writeOut h q xs) := by
  by_cases ne : xs = []
  · subst ne; rw [writeOut_nil]; exact fit
  rcases w with ⟨-, h0⟩ | ⟨rr, iw, aw, rfl, gw, row, fitw⟩
  · exact absurd (List.eq_nil_of_length_eq_zero h0) ne
  intro r a gr
  by_cases same : r = rr
  · subst same
    rcases writeOut_same gw row (xs := xs) with e | ⟨hnil, _⟩
    · rw [e] at gr
      cases gr
      rw [written_size aw iw xs fitw]
      exact fit r aw gw
    · exact absurd hnil ne
  · rw [writeOut_other (fun j e => same (by cases e; rfl))] at gr
    exact fit r a gr

private theorem separate_symm' {p q : BPtr} {n m : Nat} (s : Separate p n q m) : Separate q m p n := by
  rcases s with rfl | rfl | s
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · right; right
    cases p with
    | null => cases q <;> exact trivial
    | ref r i =>
      cases q with
      | null => exact trivial
      | ref s j =>
        rcases s with ne | h1 | h2
        · exact Or.inl ne.symm
        · exact Or.inr (Or.inr h1)
        · exact Or.inr (Or.inl h2)

private theorem same_trans {X Y Z : Heap}
    (h1 : SameObjectsUpToTableShape X Y) (h2 : SameObjectsUpToTableShape Y Z) :
    SameObjectsUpToTableShape X Z := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := h2
  refine ⟨fun b => (b1 b).trans (a1 b), fun b => (b2 b).trans (a2 b), fun b lb => ?_,
    fun b => (b4 b).trans (a4 b), fun b => (b5 b).trans (a5 b), fun b => (b6 b).trans (a6 b),
    fun b => (b7 b).trans (a7 b), fun b => (b8 b).trans (a8 b), b9.trans a9, b10.trans a10,
    b11.trans a11, Nat.le_trans a12 b12, Nat.le_trans a13 b13⟩
  have lY : Y.live b := by
    simp only [Heap.live] at lb ⊢
    rw [a1 b, a2 b, a4 b, a5 b, a6 b, a7 b, a8 b]; exact lb
  exact (b3 b lY).trans (a3 b lb)

private theorem put_unchanged (Z : Heap) (t : BRef) (v : Array UInt8) :
    (Space.put Z t v).ro = Z.ro ∧ (Space.put Z t v).words = Z.words ∧
    (Space.put Z t v).streams = Z.streams ∧ (Space.put Z t v).gzheaders = Z.gzheaders ∧
    (Space.put Z t v).istates = Z.istates ∧ (Space.put Z t v).gzstates = Z.gzstates ∧
    (Space.put Z t v).static = Z.static ∧ (Space.put Z t v).allocOk = Z.allocOk ∧
    (Space.put Z t v).garbage = Z.garbage ∧ (Space.put Z t v).nextBlk = Z.nextBlk ∧
    (Space.put Z t v).nalloc = Z.nalloc := by
  cases t with
  | dstate_depth id => cases hs : Z.dstates id <;> simp [Space.put, hs]
  | _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem put_blk_eq (Z : Heap) (t : BRef) (v : Array UInt8) (x : Nat) :
    (Space.put Z t v).bytes x = if t = .blk x then some v else Z.bytes x := by
  cases t with
  | blk b =>
    by_cases hbx : b = x
    · subst hbx; simp [Space.put]
    · simp [Space.put, upd_ne _ _ _ _ (fun e => hbx e.symm), hbx]
  | dstate_depth id => cases hs : Z.dstates id <;> simp [Space.put, hs]
  | _ => simp [Space.put]

private theorem put_dstates_eq (Z : Heap) (t : BRef) (v : Array UInt8) (x : Nat) :
    (Space.put Z t v).dstates x =
      if t = .dstate_depth x then (Z.dstates x).map (fun s => { s with depth := v }) else Z.dstates x := by
  cases t with
  | dstate_depth id =>
    by_cases hix : id = x
    · subst hix
      cases hs : Z.dstates id with
      | none => simp [Space.put, hs]
      | some s => simp [Space.put, hs]
    · cases hs : Z.dstates id with
      | none => simp [Space.put, hs, hix]
      | some s => simp [Space.put, hs, hix, upd_ne _ _ _ _ (fun e => hix e.symm)]
  | _ => simp [Space.put]

private theorem put_put_comm_same {X : Heap} {r s : BRef} {a b : Array UInt8} (hne : r ≠ s) :
    SameObjectsUpToTableShape (Space.put (Space.put X r a) s b) (Space.put (Space.put X s b) r a) := by
  have u1 := put_unchanged X r a
  have u2 := put_unchanged (Space.put X r a) s b
  have u3 := put_unchanged X s b
  have u4 := put_unchanged (Space.put X s b) r a
  refine ⟨fun x => ?_, fun x => ?_, fun x _ => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [put_blk_eq, put_blk_eq, put_blk_eq, put_blk_eq]
    by_cases hr : r = .blk x <;> by_cases hs : s = .blk x
    · exact absurd (hr.trans hs.symm) hne
    · simp [hr, hs]
    · simp [hr, hs]
    · simp [hr, hs]
  · simp [u1.2.1, u2.2.1, u3.2.1, u4.2.1]
  · simp [u1.1, u2.1, u3.1, u4.1]
  · simp [u1.2.2.1, u2.2.2.1, u3.2.2.1, u4.2.2.1]
  · simp [u1.2.2.2.1, u2.2.2.2.1, u3.2.2.2.1, u4.2.2.2.1]
  · rw [put_dstates_eq, put_dstates_eq, put_dstates_eq, put_dstates_eq]
    by_cases hr : r = .dstate_depth x <;> by_cases hs : s = .dstate_depth x
    · exact absurd (hr.trans hs.symm) hne
    · simp [hr, hs]
    · simp [hr, hs]
    · simp [hr, hs]
  · simp [u1.2.2.2.2.1, u2.2.2.2.2.1, u3.2.2.2.2.1, u4.2.2.2.2.1]
  · simp [u1.2.2.2.2.2.1, u2.2.2.2.2.2.1, u3.2.2.2.2.2.1, u4.2.2.2.2.2.1]
  · simp [u1.2.2.2.2.2.2.1, u2.2.2.2.2.2.2.1, u3.2.2.2.2.2.2.1, u4.2.2.2.2.2.2.1]
  · simp [u1.2.2.2.2.2.2.2.1, u2.2.2.2.2.2.2.2.1, u3.2.2.2.2.2.2.2.1, u4.2.2.2.2.2.2.2.1]
  · simp [u1.2.2.2.2.2.2.2.2.1, u2.2.2.2.2.2.2.2.2.1, u3.2.2.2.2.2.2.2.2.1, u4.2.2.2.2.2.2.2.2.1]
  · simp only [u1.2.2.2.2.2.2.2.2.2.1, u2.2.2.2.2.2.2.2.2.2.1,
      u3.2.2.2.2.2.2.2.2.2.1, u4.2.2.2.2.2.2.2.2.2.1]; exact Nat.le_refl _
  · simp only [u1.2.2.2.2.2.2.2.2.2.2, u2.2.2.2.2.2.2.2.2.2.2,
      u3.2.2.2.2.2.2.2.2.2.2, u4.2.2.2.2.2.2.2.2.2.2]; exact Nat.le_refl _

private theorem writeOut_destLen_overwrite {h : Heap} {dest destLen : BPtr} {out l0 lv : List UInt8}
    {cap : Nat} (wd : Writable h destLen l0.length) (hl : lv.length = l0.length)
    (wo : Writable h dest cap) (outLe : out.length ≤ cap) :
    SameObjectsUpToTableShape (writeOut (writeOut h dest out) destLen lv)
      (writeOut (writeOut (writeOut h destLen l0) dest out) destLen lv) := by
  by_cases el : lv = []
  · have el0 : l0 = [] := List.eq_nil_of_length_eq_zero (by rw [← hl, el]; rfl)
    subst el el0
    rw [writeOut_nil, writeOut_nil, writeOut_nil]
    exact same_refl _
  rcases wd with ⟨-, h0⟩ | ⟨r, i, a, rfl, gr, ro, fitl⟩
  · exact absurd (List.eq_nil_of_length_eq_zero (by omega)) el
  have el0 : l0 ≠ [] := fun e => el (List.eq_nil_of_length_eq_zero (by rw [hl, e]; rfl))
  by_cases eo : out = []
  · subst eo
    rw [writeOut_nil, writeOut_nil]
    have wL := writeOut_some gr el0 (i := i)
    have gL : Space.get (writeOut h (.ref r i) l0) r =
        some (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size) := by
      rw [wL]; exact byte_view_get_put gr ro _
    have wOuter := writeOut_some gL el (i := i)
    have wR := writeOut_some gr el (i := i)
    rw [wOuter, wL, wR, put_put_any]
    have hArr :
        (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract 0 i ++ lv.toArray ++
          (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract (i + lv.length)
            (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).size =
        a.extract 0 i ++ lv.toArray ++ a.extract (i + lv.length) a.size := by
      apply Array.ext'
      apply List.ext_getElem?
      intro j
      let a1 := a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size
      have sz1 : a1.size = a.size := written_size a i l0 fitl
      have wl1 := written_get? a1 i lv (by rw [sz1, hl]; exact fitl) j
      have wR' := written_get? a i lv (by rw [hl]; exact fitl) j
      have w1 := written_get? a i l0 fitl j
      simp only [Array.getElem?_toList]
      rw [wl1, wR', w1]
      by_cases h1 : j < i
      · simp [h1]
      · by_cases h2 : j < i + lv.length
        · simp [h1, h2]
        · simp [h1, h2, show ¬ j < i + l0.length by omega]
    rw [hArr]
    exact same_refl _
  rcases wo with ⟨-, ho0⟩ | ⟨rd, id, ad, rfl, gd, rod, fitd⟩
  · exact absurd (List.eq_nil_of_length_eq_zero (by omega)) eo
  by_cases same : rd = r
  · subst same
    rw [gr] at gd; cases gd
    have wL := writeOut_some gr el0 (i := i)
    have g1 : Space.get (writeOut h (.ref rd i) l0) rd =
        some (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size) := by
      rw [wL]; exact byte_view_get_put gr ro _
    have ro1 : Space.ro (writeOut h (.ref rd i) l0) rd = false := by rw [writeOut_ro]; exact ro
    have w2 := writeOut_some g1 eo (i := id) (xs := out)
    have g2 : Space.get (writeOut (writeOut h (.ref rd i) l0) (.ref rd id) out) rd =
        some ((a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract 0 id ++ out.toArray ++
         (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract (id + out.length)
           (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).size) := by
      rw [w2]; exact byte_view_get_put g1 ro1 _
    have wR := writeOut_some gr eo (i := id) (xs := out)
    have gR : Space.get (writeOut h (.ref rd id) out) rd =
        some (a.extract 0 id ++ out.toArray ++ a.extract (id + out.length) a.size) := by
      rw [wR]; exact byte_view_get_put gr rod _
    have wO1 := writeOut_some gR el (i := i)
    have wO2 := writeOut_some g2 el (i := i)
    rw [wO1, wR, wO2, w2, wL, put_put_any, put_put_any, put_put_any]
    have hArr :
        (a.extract 0 id ++ out.toArray ++ a.extract (id + out.length) a.size).extract 0 i ++ lv.toArray ++
          (a.extract 0 id ++ out.toArray ++ a.extract (id + out.length) a.size).extract (i + lv.length)
            (a.extract 0 id ++ out.toArray ++ a.extract (id + out.length) a.size).size =
        ((a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract 0 id ++ out.toArray ++
          (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract (id + out.length)
            (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).size).extract 0 i ++ lv.toArray ++
          ((a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract 0 id ++ out.toArray ++
            (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract (id + out.length)
              (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).size).extract (i + lv.length)
            ((a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract 0 id ++ out.toArray ++
              (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract (id + out.length)
                (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).size).size := by
      apply Array.ext'
      apply List.ext_getElem?
      intro j
      let b0 := a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size
      let bR := a.extract 0 id ++ out.toArray ++ a.extract (id + out.length) a.size
      let bL := b0.extract 0 id ++ out.toArray ++ b0.extract (id + out.length) b0.size
      have sz0 : b0.size = a.size := written_size a i l0 fitl
      have sz1 : bL.size = b0.size := written_size b0 id out (by rw [sz0]; omega)
      have szR : bR.size = a.size := written_size a id out (by omega)
      have wgR := written_get? bR i lv (by rw [szR, hl]; exact fitl) j
      have wgL := written_get? bL i lv (by rw [sz1, sz0, hl]; exact fitl) j
      have wa := written_get? b0 id out (by rw [sz0]; omega) j
      have wb := written_get? a i l0 fitl j
      have wc := written_get? a id out (by omega) j
      simp only [Array.getElem?_toList]
      rw [wgR, wgL]
      by_cases hi : j < i
      · simp only [hi, ite_true, show j < i + lv.length by omega]
        rw [wa, wc, wb]; simp [hi]
      · by_cases hi2 : j < i + lv.length
        · simp [hi, hi2]
        · simp only [hi, hi2, ite_false]
          rw [wa, wc, wb]
          have notl0 : ¬ j < i + l0.length := by omega
          by_cases hd : j < id <;> by_cases hd2 : j < id + out.length <;> simp [hi, notl0, hd, hd2]
    rw [hArr]
    exact same_refl _
  · have neRL : ∀ j, Ptr.ref r i ≠ Ptr.ref rd j := fun _ e => same (by cases e; rfl)
    have neLR : ∀ j, Ptr.ref rd id ≠ Ptr.ref r j := fun _ e => same (by cases e; rfl)
    have gD1 : Space.get (writeOut h (.ref r i) l0) rd = some ad := by rw [writeOut_other neRL]; exact gd
    have gR1 : Space.get (writeOut h (.ref rd id) out) r = some a := by rw [writeOut_other neLR]; exact gr
    have ro1 : Space.ro (writeOut h (.ref rd id) out) r = false := by rw [writeOut_ro]; exact ro
    have wL0 := writeOut_some gr el0 (i := i)
    have wD0 := writeOut_some gd eo (i := id) (xs := out)
    have wD1 := writeOut_some gD1 eo (i := id) (xs := out)
    have wL1 := writeOut_some gR1 el0 (i := i)
    have gL2 : Space.get (writeOut (writeOut h (.ref rd id) out) (.ref r i) l0) r =
        some (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size) := by
      rw [wL1]; exact byte_view_get_put gR1 ro1 _
    have scomm : SameObjectsUpToTableShape (writeOut (writeOut h (.ref r i) l0) (.ref rd id) out)
        (writeOut (writeOut h (.ref rd id) out) (.ref r i) l0) := by
      rw [wD1, wL1, wL0, wD0]
      exact put_put_comm_same (fun e => same e.symm)
    have scommD := same_writeOut_both scomm (.ref r i) lv
    have wInner := writeOut_some gR1 el (i := i)
    have wOuter := writeOut_some gL2 el (i := i)
    have hArr :
        (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract 0 i ++ lv.toArray ++
          (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).extract (i + lv.length)
            (a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size).size =
        a.extract 0 i ++ lv.toArray ++ a.extract (i + lv.length) a.size := by
      apply Array.ext'
      apply List.ext_getElem?
      intro j
      let a1 := a.extract 0 i ++ l0.toArray ++ a.extract (i + l0.length) a.size
      have sz1 : a1.size = a.size := written_size a i l0 fitl
      have wl1 := written_get? a1 i lv (by rw [sz1, hl]; exact fitl) j
      have wR' := written_get? a i lv (by rw [hl]; exact fitl) j
      have wb := written_get? a i l0 fitl j
      simp only [Array.getElem?_toList]
      rw [wl1, wR', wb]
      by_cases h1 : j < i
      · simp [h1]
      · by_cases h2 : j < i + lv.length
        · simp [h1, h2]
        · simp [h1, h2, show ¬ j < i + l0.length by omega]
    have hEqR : writeOut (writeOut (writeOut h (.ref rd id) out) (.ref r i) l0) (.ref r i) lv =
        writeOut (writeOut h (.ref rd id) out) (.ref r i) lv := by
      rw [wOuter, wL1, wInner, put_put_any, hArr]
    exact same_trans (by rw [← hEqR]; exact same_refl _) (by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩ := scommD
      exact ⟨fun b => (s1 b).symm, fun b => (s2 b).symm, fun b lb => by
        have lb' : (writeOut (writeOut (writeOut h (.ref r i) l0) (.ref rd id) out) (.ref r i) lv).live b := by
          simp only [Heap.live] at lb ⊢; rw [← s1 b, ← s2 b, ← s4 b, ← s5 b, ← s6 b, ← s7 b, ← s8 b]; exact lb
        exact (s3 b lb').symm,
        fun b => (s4 b).symm, fun b => (s5 b).symm, fun b => (s6 b).symm, fun b => (s7 b).symm, fun b => (s8 b).symm,
        s9.symm, s10.symm, s11.symm,
        by simp only [(writeOut_globals _ _ _).2.2.2.1]; exact Nat.le_refl _,
        by simp only [(writeOut_globals _ _ _).2.2.2.2.1]; exact Nat.le_refl _⟩)

private theorem dgood_writeOut {H : Heap} {k : Nat} {zf : ZStream} {sf : DeflateState}
    (good : DGood H (.tab k) (k + 1) zf sf)
    (owned : ∀ b, DeflateOwned (k + 1) sf b ↔ k + 1 ≤ b ∧ b < k + 6)
    {destLen : BPtr} {xs : List UInt8}
    (blkLt : ∀ r i, destLen = .ref r i → ∀ c, BRef.block r = some c → c < k) :
    DGood (writeOut H destLen xs) (.tab k) (k + 1) zf sf := by
  by_cases ex : xs = []
  · subst ex; rw [writeOut_nil]; exact good
  cases destLen with
  | null => exact good
  | ref r i =>
    cases g : Space.get H r with
    | none => rw [writeOut_none g]; exact good
    | some a =>
      rw [writeOut_some g ex]
      let a' := a.extract 0 i ++ xs.toArray ++ a.extract (i + xs.length) a.size
      have hsame : ∀ b, k ≤ b → SameAt H (Space.put H r a') b := by
        intro b hb
        refine SameAt.put_other H a' (fun hc => ?_)
        exact absurd (blkLt r i rfl b hc) (by omega)
      have sk : H.streams k = some zf := good.live.hz
      have sk' : (Space.put H r a').streams k = some zf := (hsame k (Nat.le_refl k)).2.2.1.trans sk
      have sd' : (Space.put H r a').dstates (k + 1) = some sf :=
        (hsame (k + 1) (by omega)).2.2.2.2.1.trans good.live.hs
      have st' : (Space.put H r a').static = H.static := (put_globals H r a').1
      have ownedBlk : ∀ b, DeflateOwned (k + 1) sf b → k ≤ b := fun b ho => by
        have := (owned b).1 ho; omega
      obtain ⟨w, p, q, b, db⟩ := good.inv.blocks
      have hw : k ≤ w := ownedBlk w (Or.inr (Or.inl db.win))
      have hp : k ≤ p := ownedBlk p (Or.inr (Or.inr (Or.inl db.prev)))
      have hq : k ≤ q := ownedBlk q (Or.inr (Or.inr (Or.inr (Or.inl db.head))))
      have hb : k ≤ b := ownedBlk b (Or.inr (Or.inr (Or.inr (Or.inr db.pbuf))))
      have sw := hsame w hw; have sp := hsame p hp; have sq := hsame q hq; have sb := hsame b hb
      have inv' : DStInv (Space.put H r a') (k + 1) sf :=
        { good.inv with
          blocks := ⟨w, p, q, b,
            { db with
              wa := by obtain ⟨aa, ha, hsz⟩ := db.wa; exact ⟨aa, sw.1.trans ha, hsz⟩
              wro := sw.2.2.2.2.2.2.2.trans db.wro
              pa := by obtain ⟨aa, ha, hsz⟩ := db.pa; exact ⟨aa, sp.2.1.trans ha, hsz⟩
              qa := by obtain ⟨aa, ha, hsz⟩ := db.qa; exact ⟨aa, sq.2.1.trans ha, hsz⟩
              ba := by obtain ⟨aa, ha, hsz⟩ := db.ba; exact ⟨aa, sb.1.trans ha, hsz⟩
              bro := sb.2.2.2.2.2.2.2.trans db.bro }⟩ }
      have tr' : TreesInv (Space.put H r a') (k + 1) := by
        obtain ⟨d₀, b₀, buf₀, tr⟩ := good.trees
        have hsd : H.dstates (k + 1) = some d₀ := tr.base.dstate
        have ed : d₀ = sf := Option.some.inj (hsd.symm.trans good.live.hs)
        subst ed
        have eb : b₀ = b := by
          have := tr.base.pbuf.symm.trans db.pbuf
          simp only [Ptr.ref.injEq, BRef.blk.injEq] at this
          exact this.1
        subst eb
        refine ⟨d₀, b₀, buf₀, ⟨{ tr.base with
          dstate := sd'
          static := by unfold Zlib.Trees.Proofs.Out.TreesStatic; rw [st']; exact tr.base.static
          bytes := sb.1.trans tr.base.bytes
          rw := sb.2.2.2.2.2.2.2.trans tr.base.rw }, tr.run⟩⟩
      have u' : Zlib.Deflate.Spec.Uniq (Space.put H r a') := by
        rw [← writeOut_some g ex]
        exact writeOut_uniq good.uniq
      have f' : Fresh (Space.put H r a') := by
        rw [← writeOut_some g ex]
        exact writeOut_fresh good.fresh
      exact ⟨{ good.live with hz := sk', hs := sd' }, inv', u', f', tr'⟩

private theorem agree_to_same_upto {keep : Nat → Prop} {E H : Heap}
    (ag : Agree keep E H) (_ : ∀ b, keep b → E.live b) :
    ∀ b, keep b → SameAt E H b := ag.blocks

private theorem same_writeOut_comm_cell {h : Heap} {p q : BPtr} {xp xq : List UInt8}
    (wp : Writable h p xp.length) (wq : Writable h q xq.length) (sep : Separate p xp.length q xq.length)
    (hp0 : p ≠ .null) (hq0 : q ≠ .null) (hne : xp ≠ [] ∧ xq ≠ []) :
    SameObjectsUpToTableShape (writeOut (writeOut h p xp) q xq) (writeOut (writeOut h q xq) p xp) := by
  rcases wp with ⟨rfl, -⟩ | ⟨rp, ip, ap, rfl, grp, rop, fitp⟩
  · exact absurd rfl hp0
  rcases wq with ⟨rfl, -⟩ | ⟨rq, iq, aq, rfl, grq, roq, fitq⟩
  · exact absurd rfl hq0
  by_cases same : rp = rq
  · subst same
    rw [grp] at grq; cases grq
    have sep' : ip + xp.length ≤ iq ∨ iq + xq.length ≤ ip := by
      rcases sep with h0 | h0 | s
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hne.1
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hne.2
      · exact s.resolve_left (fun e => e rfl)
    have wp1 := writeOut_some grp hne.1 (i := ip)
    have gp1 : Space.get (writeOut h (.ref rp ip) xp) rp =
        some (ap.extract 0 ip ++ xp.toArray ++ ap.extract (ip + xp.length) ap.size) := by
      rw [wp1]; exact byte_view_get_put grp rop _
    have wq1 := writeOut_some grp hne.2 (i := iq)
    have gq1 : Space.get (writeOut h (.ref rp iq) xq) rp =
        some (ap.extract 0 iq ++ xq.toArray ++ ap.extract (iq + xq.length) ap.size) := by
      rw [wq1]; exact byte_view_get_put grp roq _
    rw [writeOut_some gp1 hne.2, wp1, writeOut_some gq1 hne.1, wq1, put_put_any, put_put_any]
    have hArr :
        (ap.extract 0 ip ++ xp.toArray ++ ap.extract (ip + xp.length) ap.size).extract 0 iq ++ xq.toArray ++
          (ap.extract 0 ip ++ xp.toArray ++ ap.extract (ip + xp.length) ap.size).extract (iq + xq.length)
            (ap.extract 0 ip ++ xp.toArray ++ ap.extract (ip + xp.length) ap.size).size =
        (ap.extract 0 iq ++ xq.toArray ++ ap.extract (iq + xq.length) ap.size).extract 0 ip ++ xp.toArray ++
          (ap.extract 0 iq ++ xq.toArray ++ ap.extract (iq + xq.length) ap.size).extract (ip + xp.length)
            (ap.extract 0 iq ++ xq.toArray ++ ap.extract (iq + xq.length) ap.size).size := by
      apply Array.ext'
      apply List.ext_getElem?
      intro j
      let ap1 := ap.extract 0 ip ++ xp.toArray ++ ap.extract (ip + xp.length) ap.size
      let aq1 := ap.extract 0 iq ++ xq.toArray ++ ap.extract (iq + xq.length) ap.size
      have szp : ap1.size = ap.size := written_size ap ip xp fitp
      have szq : aq1.size = ap.size := written_size ap iq xq fitq
      have w1 := written_get? ap1 iq xq (by rw [szp]; exact fitq) j
      have w2 := written_get? aq1 ip xp (by rw [szq]; exact fitp) j
      have wp' := written_get? ap ip xp fitp j
      have wq' := written_get? ap iq xq fitq j
      simp only [Array.getElem?_toList]
      rw [w1, w2, wp', wq']
      rcases sep' with lt | lt <;>
        by_cases hp1 : j < ip <;> by_cases hp2 : j < ip + xp.length <;>
        by_cases hq1 : j < iq <;> by_cases hq2 : j < iq + xq.length <;>
        simp [hp1, hp2, hq1, hq2] <;> try omega
    rw [hArr]
    exact same_refl _
  · have nePQ : ∀ j, Ptr.ref rp ip ≠ Ptr.ref rq j := fun _ e => same (by cases e; rfl)
    have neQP : ∀ j, Ptr.ref rq iq ≠ Ptr.ref rp j := fun _ e => same (by cases e; rfl)
    have gQ1 : Space.get (writeOut h (.ref rp ip) xp) rq = some aq := by rw [writeOut_other nePQ]; exact grq
    have gP1 : Space.get (writeOut h (.ref rq iq) xq) rp = some ap := by rw [writeOut_other neQP]; exact grp
    rw [writeOut_some gQ1 hne.2, writeOut_some gP1 hne.1,
      writeOut_some grp hne.1, writeOut_some grq hne.2]
    exact put_put_comm_same same

/-- Safety of `compress2_z_c` at every compression level. -/
theorem compress2_z_c_safety_gen (cr : CompressReach R) (call : GoalDeflateFor R)
    (facts : DeflateLoopFactsFor R) (level : Int32) :
    CompressorCSafety (fun d dl s n => compress2_z_c d dl s n level) true := by
  intro h dest destLen source capacity n xs fresh uniq globals fit dcell _ srcB destW sep sepD sepS
  by_cases rej : compressRejected dest (if destLen = .null then none else some capacity) source n
  · have run : C.run (compress2_z_c dest destLen source n level) h =
        .ok (Z_STREAM_ERROR,
          { h with streams := upd (upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc)))) h.nextBlk none,
                   nextBlk := h.nextBlk + 1 }) := by
      have al := allocLocalZ_run fresh
      have fr := freeZStream_local_zero (h := h)
      rcases rej with c0 | ⟨sn, n0⟩ | ⟨c, hc, dn, c0⟩
      · have hdl : destLen = .null := by
          by_cases hne : destLen = .null
          · exact hne
          · simp [hne] at c0
        subst hdl
        unfold compress2_z_c
        by_cases hsn : (decide (n > 0) && source == .null) = true
        · simp only [C.run, bind_app, al, hsn, ite_true, fr, pure_app]
        · have hsn' : (decide (n > 0) && source == .null) = false := Bool.eq_false_iff.mpr hsn
          simp only [C.run, bind_app, al, hsn', Bool.false_eq_true, ite_false, beq_self_eq_true,
            ite_true, fr, pure_app]
      · have npos : decide (n > 0) = true := by
          simp only [decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
          have : n.toNat ≠ 0 := fun e => n0 (UInt64.toNat_inj.mp (by simpa using e))
          omega
        unfold compress2_z_c
        simp only [C.run, bind_app, al, npos, sn, beq_self_eq_true, Bool.and_self, ite_true, fr, pure_app]
      · have hdn : destLen ≠ .null := fun e => by simp [e] at hc
        simp only [hdn, ite_false, Option.some.injEq] at hc
        subst hc
        have cpos : decide (capacity > 0) = true := by
          simp only [decide_eq_true_eq, gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
          have : capacity.toNat ≠ 0 := fun e => c0 (UInt64.toNat_inj.mp (by simpa using e))
          omega
        let hzPre := { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1 }
        have ldCell : LengthCell hzPre destLen capacity := by
          obtain ⟨hb, hw⟩ := dcell hdn
          exact ⟨by rcases hb with ⟨h0, -⟩ | h1; exact absurd h0 hdn; exact Or.inr h1,
                 by rcases hw with ⟨h0, -⟩ | h1; exact absurd h0 hdn; exact Or.inr h1⟩
        dsimp only [hzPre] at ldCell
        have hbn : (destLen == .null) = false := beq_false_of_ne hdn
        by_cases hsn : (decide (n > 0) && source == .null) = true
        · simp [C.run, compress2_z_c, al, fr, hsn]
        · have hsn' : (decide (n > 0) && source == .null) = false := Bool.eq_false_iff.mpr hsn
          unfold compress2_z_c
          simp only [C.run, bind_app, al, hsn', Bool.false_eq_true, ite_false, hbn,
            load64_cell ldCell, cpos, dn, beq_self_eq_true, Bool.and_self, ite_true, fr, pure_app]
    exact ⟨Z_STREAM_ERROR, _, run, fun _ => ⟨rfl, same_freeZStream_local fresh⟩, fun hdl hs hd => by
      exfalso
      rcases rej with c0 | ⟨rfl, hne⟩ | ⟨c, hc, rfl, hne⟩
      · simp [hdl] at c0
      · exact hne (hs rfl)
      · simp only [hdl, ite_false, Option.some.injEq] at hc; subst hc
        exact hne (hd rfl)⟩
  · have hdl : destLen ≠ .null := fun e => by apply rej; left; simp [e]
    have hsN : ¬ (n > 0 ∧ source = .null) := fun x => rej (Or.inr (Or.inl ⟨x.2, by
      intro e; rw [e] at x; exact absurd x.1 (by decide)⟩))
    have hcN : ¬ (capacity > 0 ∧ dest = .null) := fun x => rej (Or.inr (Or.inr ⟨capacity, by simp [hdl], x.2, by
      intro e; rw [e] at x; exact absurd x.1 (by decide)⟩))
    have hsn : (decide (n > 0) && source == .null) = false := by
      cases hb : (decide (n > 0) && source == .null)
      · rfl
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb; exact absurd hb hsN
    have hcn : (decide (capacity > 0) && dest == .null) = false := by
      cases hb : (decide (capacity > 0) && dest == .null)
      · rfl
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb; exact absurd hb hcN
    have wd0 : Writable h destLen (lengthBytes 0).length := by
      rw [lengthBytes_length]; exact (dcell hdl).2
    let h₀ := writeOut h destLen (lengthBytes 0)
    have store0 : Store h destLen (lengthBytes 0) h₀ := store_writeOut wd0
    have fresh₀ : Fresh h₀ := writeOut_fresh fresh
    have uniq₀ : Zlib.Deflate.Spec.Uniq h₀ := writeOut_uniq uniq
    have globals₀ : LibraryGlobals h₀ := writeOut_globals_eq globals
    have fit₀ : ZlibF.PlatformMemory.ByteObjectsFit h₀ := writeOut_fit fit wd0
    have srcB₀ : Bytes h₀ source n.toNat (if source = .null then [] else xs) := by
      by_cases sn : source = .null
      · have n0 : n = 0 := Classical.byContradiction fun hne => hsN ⟨by
          have : n.toNat ≠ 0 := fun e => hne (UInt64.toNat_inj.mp (by simpa using e))
          exact Nat.pos_of_ne_zero this |> fun hpos => by simpa [UInt64.lt_iff_toNat_lt] using hpos, sn⟩
        subst sn n0; simp; exact Or.inl ⟨rfl, rfl, rfl⟩
      · simp only [sn, ite_false]
        exact bytes_writeOut_sep (srcB sn) (separate_symm' sepS) (by simp [lengthBytes_length]) (dcell hdl).2
    have destW₀ : Writable h₀ dest capacity.toNat := by
      by_cases dn : dest = .null
      · have c0 : capacity = 0 := Classical.byContradiction fun hne => hcN ⟨by
          have : capacity.toNat ≠ 0 := fun e => hne (UInt64.toNat_inj.mp (by simpa using e))
          exact Nat.pos_of_ne_zero this |> fun hpos => by simpa [UInt64.lt_iff_toNat_lt] using hpos, dn⟩
        subst dn c0; exact Or.inl ⟨rfl, rfl⟩
      · exact writable_writeOut (destW dn) (by simp [lengthBytes_length]) (dcell hdl).2
    let hzPre := { h with streams := upd h.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))), nextBlk := h.nextBlk + 1 }
    have ldCell : LengthCell hzPre destLen capacity := by
      obtain ⟨hb, hw⟩ := dcell hdl
      exact ⟨by rcases hb with ⟨h0, -⟩ | h1; exact absurd h0 hdl; exact Or.inr h1,
             by rcases hw with ⟨h0, -⟩ | h1; exact absurd h0 hdl; exact Or.inr h1⟩
    dsimp only [hzPre] at ldCell
    obtain ⟨hPreS, storePreS, sfPre⟩ := store64_writable (h := hzPre) 0 ldCell.2
    dsimp only [hzPre] at storePreS
    have eqPre : hPreS = writeOut hzPre destLen (lengthBytes 0) := store_fun sfPre
    have nb0 : h₀.nextBlk = h.nextBlk := (writeOut_globals h destLen (lengthBytes 0)).2.2.2.1
    have na0 : h₀.nalloc = h.nalloc := (writeOut_globals h destLen (lengthBytes 0)).2.2.2.2.1
    have ao0 : h₀.allocOk = h.allocOk := (writeOut_globals h destLen (lengthBytes 0)).2.1
    have ng0 : h₀.garbage h₀.nalloc = h.garbage h.nalloc := by
      rw [na0, (writeOut_globals h destLen (lengthBytes 0)).2.2.1]
    have hcomm : writeOut hzPre destLen (lengthBytes 0) =
        { h₀ with streams := upd h₀.streams h.nextBlk (some (ZStream.garbage (h.garbage h.nalloc))),
                  nextBlk := h.nextBlk + 1 } := by
      rcases wd0 with ⟨h0, -⟩ | ⟨r, i, a, hp, gr, ro, fitr⟩
      · exact absurd h0 hdl
      · have neq : (lengthBytes 0) ≠ [] := by decide
        have grPre : Space.get hzPre r = some a := by cases r <;> exact gr
        dsimp only [h₀]
        rw [hp, writeOut_some grPre neq, writeOut_some gr neq]
        cases r with
        | dstate_depth id => cases hs : h.dstates id <;> simp [hzPre, Space.put, hs]
        | _ => simp [hzPre, Space.put]
    have hzS : hPreS.streams h.nextBlk = some (ZStream.garbage (h.garbage h.nalloc)) := by
      rw [eqPre, hcomm]; simp
    have eqcHeap : stZStream (some (.tab h.nextBlk))
        { zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null,
          next_in := (ZStream.garbage (h.garbage h.nalloc)).next_in,
          avail_in := (ZStream.garbage (h.garbage h.nalloc)).avail_in,
          total_in := (ZStream.garbage (h.garbage h.nalloc)).total_in,
          next_out := (ZStream.garbage (h.garbage h.nalloc)).next_out,
          avail_out := (ZStream.garbage (h.garbage h.nalloc)).avail_out,
          total_out := (ZStream.garbage (h.garbage h.nalloc)).total_out,
          msg := (ZStream.garbage (h.garbage h.nalloc)).msg,
          state := (ZStream.garbage (h.garbage h.nalloc)).state,
          data_type := (ZStream.garbage (h.garbage h.nalloc)).data_type,
          adler := (ZStream.garbage (h.garbage h.nalloc)).adler,
          reserved := (ZStream.garbage (h.garbage h.nalloc)).reserved } hPreS =
        .ok ((), cHeap h₀) := by
      subst eqPre
      rw [hcomm]
      simp [stZStream, ZStreamRef.put, ZStreamRef.get, ZStreamRef.isRo, cHeap, cStream, nb0, ng0, upd_upd]
    obtain ⟨rcI, afterI, initRun, outcome⟩ := init_cases fresh₀ uniq₀ globals₀ level
    have initRun' : deflateInit_ (some (.tab h.nextBlk)) level (.ref (.str 57) 0) 112 (cHeap h₀) =
        .ok (rcI, afterI) := by rw [← nb0]; exact initRun
    rcases outcome with ⟨rcNe, u2, liveA, frameA, ⟨z', hz'⟩, memA⟩ | ⟨rfl, -, p, initial⟩
    · have hz'h : afterI.streams h.nextBlk = some z' := by rw [← nb0]; exact hz'
      have rcNeB : (rcI != Z_OK) = true := bne_iff_ne.mpr rcNe
      have run : C.run (compress2_z_c dest destLen source n level) h =
          .ok (rcI, { afterI with streams := upd afterI.streams h₀.nextBlk none }) := by
        unfold compress2_z_c
        simp only [C.run, bind_app, allocLocalZ_run fresh, hsn, beq_false_of_ne hdl,
          Bool.false_eq_true, ite_false, load64_cell ldCell, hcn, storePreS, zwr, ldZStream, ZStreamRef.get, hzS,
          eqcHeap, version_gz_run, sizeof_z_stream, initRun', rcNeB, ite_true, freeZStream, hz'h, pure_app, nb0]
      refine ⟨rcI, { afterI with streams := upd afterI.streams h₀.nextBlk none }, run, fun r => absurd r rej, ?_⟩
      intro _ _ _
      refine ⟨[], 0, h, h₀, Or.inl ⟨rfl, rfl⟩, store0, init_failure_heap fresh₀ u2 liveA frameA hz', Nat.zero_le _, fun m => ?_⟩
      obtain ⟨j, lo, hi, bad⟩ := memA m
      rw [na0] at lo
      rw [ao0] at bad
      exact ⟨j, lo, hi, bad⟩
    · obtain ⟨z, s, good, -, zfree, -, -, -, -, -, -, -, -, -, gzhead, -, -, -, frameI, liveI, ownedI⟩ := initial
      let e₀ : CEnv := ⟨h₀, dest, source, if source = .null then [] else xs, n.toNat, capacity.toNat⟩
      have ok₀ : COK e₀ := ⟨fresh₀, globals₀, srcB₀, destW₀, sep, bytes_bound srcB₀ fit₀, writable_bound destW₀ fit₀⟩
      have k0 : ¬ h₀.live h₀.nextBlk := fresh₀ _ (Nat.le_refl _)
      have hzA : afterI.streams h₀.nextBlk = some z := good.live.hz
      let z0 : ZStream := { z with next_in := source, avail_in := 0, next_out := dest, avail_out := 0 }
      have globalsA : LibraryGlobals afterI := by
        have := frameI.1
        simp only [LibraryGlobals] at globals₀ ⊢
        rw [← this]; exact globals₀
      have notOwnK : ¬ DeflateOwned (h₀.nextBlk + 1) s h₀.nextBlk := by
        intro o; have := (ownedI h₀.nextBlk).1 o; simp only [cHeap] at this; omega
      have rb := rebuffer_tab (z1 := z0) good globalsA notOwnK (by simp [z0])
      have initRun2 : C.run (deflateInit2_ (some (.tab h₀.nextBlk)) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL
          Z_DEFAULT_STRATEGY (.ref (.str 57) 0) 112) (cHeap h₀) = .ok (Z_OK, afterI) := by
        simpa only [deflateInit_, C.run] using initRun
      have reachI : R afterI (.tab h₀.nextBlk) :=
        cr.init (cHeap_fresh fresh₀) (cHeap_uniq fresh₀ uniq₀) (cHeap_globals globals₀)
          (cHeap_get h₀) (cStream_default h₀) (version_value (cHeap h₀)) initRun2
      obtain ⟨z0', hz0', -, good0⟩ := Zlib.Deflate.Universal.rebuffer_good good rb
      have H0eq : (ZStreamRef.tab h₀.nextBlk).put afterI z0 =
          { afterI with streams := upd afterI.streams h₀.nextBlk (some z0) } := put_tab_eq hzA
      have ez : z0' = z0 := by
        have := Zlib.Deflate.Proofs.ZStreamRef.get_put_same (r := .tab h₀.nextBlk) good.live.hz z0
        exact Option.some.inj (hz0'.symm.trans this)
      subst ez
      have sameA : ∀ b, h₀.live b → SameAt h₀ { afterI with streams := upd afterI.streams h₀.nextBlk (some z0) } b := by
        intro b lb
        have bk : b ≠ h₀.nextBlk := fun x => k0 (x ▸ lb)
        have notOwnB : ¬ DeflateOwned (h₀.nextBlk + 1) s b := by
          intro o; have := (ownedI b).1 o; have := fresh₀.lt lb; simp [cHeap] at *; omega
        obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
          frameI.2.2.2.2.2 b ((cHeap_live h₀ b).2 (Or.inl lb)) (by simp only [StreamRoot]; exact bk)
        simp only [cHeap, upd_ne _ _ _ _ bk] at t1 t2 t3 t4 t5 t6 t7 t8
        exact ⟨t1, t2, by simp [upd_ne _ _ _ _ bk, t3], t4, t5, t6, t7, t8⟩
      have borrowA : afterI.libcErrorBorrow = h₀.libcErrorBorrow := by
        have := Zlib.Deflate.BorrowProofs.stable_deflateInit_ (some (.tab h₀.nextBlk)) level (.ref (.str 57) 0) 112
          (cHeap h₀) Z_OK afterI initRun
        simpa [cHeap] using this
      have cs0 : CState R e₀ (Z_OK, capacity, n) { afterI with streams := upd afterI.streams h₀.nextBlk (some z0) } [] 0 z0 s := by
        refine
          { reach := by rw [← H0eq]; exact cr.rebuffer reachI rb
            good := by rw [← H0eq]; exact good0
            zfree := zfree
            gzhead := gzhead
            owned := fun b => by
              show DeflateOwned (h₀.nextBlk + 1) s b ↔ h₀.nextBlk + 1 ≤ b ∧ b < h₀.nextBlk + 6
              rw [show h₀.nextBlk + 6 = (h₀.nextBlk + 1) + 5 by omega]
              exact ownedI b
            inCount := by show 0 + (0 : UInt32).toNat + n.toNat = n.toNat; simp
            nextIn := by show source = advance source 0; rw [advance_zero]
            outCount := by show ([] : List UInt8).length + (0 : UInt32).toNat + capacity.toNat = capacity.toNat; simp
            nextOut := by show dest = advance dest ([] : List UInt8).length; rw [List.length_nil, advance_zero]
            agree := ?_
            liveOnly := ?_
            nalloc := ?_ }
        · rw [writeOut_nil]
          refine ⟨sameA, ?_, ?_, ?_, ?_⟩
          · have := frameI.1; simp [cHeap] at this; exact this.symm
          · have := frameI.2.1; simp [cHeap] at this; exact this.symm
          · have := frameI.2.2.1; simp [cHeap] at this; exact this.symm
          · exact borrowA
        · intro b lb
          have l1 : afterI.live b := by
            by_cases bk : b = h₀.nextBlk
            · subst bk; simp [Heap.live, hzA]
            · simpa [Heap.live, upd_ne _ _ _ _ bk] using lb
          rcases (liveI b).1 l1 with ⟨lc, -⟩ | o
          · rcases (cHeap_live h₀ b).1 lc with x | x
            · exact Or.inl x
            · exact Or.inr (Or.inl x)
          · right; right
            have := (ownedI b).1 o
            simpa [cHeap, CEnv.k] using this
        · have := frameI.2.2.2.2.1
          simp [cHeap] at this
          exact this
      generalize hres : cdoWhile
        (fun x => do
          let __do_lift ← zrd (some (.tab h₀.nextBlk)) fun x => x.avail_out
          if (__do_lift == 0) = true then do
              zwr (some (.tab h₀.nextBlk)) fun z =>
                  { z with avail_out := if x.2.1 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.1.toUInt32 }
              let __do_lift ← zrd (some (.tab h₀.nextBlk)) fun x => x.avail_in
              if (__do_lift == 0) = true then do
                  zwr (some (.tab h₀.nextBlk)) fun z =>
                      { z with avail_in := if x.2.2 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.2.toUInt32 }
                  let err ← deflate (some (.tab h₀.nextBlk))
                      (if (x.2.2 - (if x.2.2 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.2.toUInt32).toUInt64 != 0) = true
                       then Z_NO_FLUSH else Z_FINISH)
                  pure (err,
                    x.2.1 - (if x.2.1 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.1.toUInt32).toUInt64,
                    x.2.2 - (if x.2.2 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.2.toUInt32).toUInt64)
                else do
                  let err ← deflate (some (.tab h₀.nextBlk))
                      (if (x.2.2 != 0) = true then Z_NO_FLUSH else Z_FINISH)
                  pure (err,
                    x.2.1 - (if x.2.1 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.1.toUInt32).toUInt64,
                    x.2.2)
            else do
              let __do_lift ← zrd (some (.tab h₀.nextBlk)) fun x => x.avail_in
              if (__do_lift == 0) = true then do
                  zwr (some (.tab h₀.nextBlk)) fun z =>
                      { z with avail_in := if x.2.2 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.2.toUInt32 }
                  let err ← deflate (some (.tab h₀.nextBlk))
                      (if (x.2.2 - (if x.2.2 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.2.toUInt32).toUInt64 != 0) = true
                       then Z_NO_FLUSH else Z_FINISH)
                  pure (err, x.2.1,
                    x.2.2 - (if x.2.2 > UInt32.toUInt64 4294967295 then 4294967295 else x.2.2.toUInt32).toUInt64)
                else do
                  let err ← deflate (some (.tab h₀.nextBlk))
                      (if (x.2.2 != 0) = true then Z_NO_FLUSH else Z_FINISH)
                  pure (err, x.2.1, x.2.2))
        (fun st => pure (st.1 == Z_OK, st))
        (Z_OK, capacity, n) { afterI with streams := upd afterI.streams h₀.nextBlk (some z0) } = res
      obtain ⟨st', H', loopEq, code', out, used, zf, sf, csf⟩ :=
        loop_result cr call facts ok₀ cs0 (Or.inl rfl) hres (k := h₀.nextBlk) rfl (by cbody_ok) (fun _ _ => rfl)
      obtain ⟨d, rcE, H2_o, diffRun, -, -, -, -, outLe⟩ := epilogue ok₀ csf
      have hzf : H'.streams h₀.nextBlk = some zf := csf.good.live.hz
      have diffRun' : Ptr.diff zf.next_out dest H' = .ok (d, H') := diffRun
      have wd_out : Writable (writeOut h₀ dest out) destLen 8 :=
        writable_writeOut (writable_writeOut (dcell hdl).2 (by simp [lengthBytes_length]) (dcell hdl).2)
          outLe destW₀
      have dlLive : ∀ r i, destLen = .ref r i → ∀ c, BRef.block r = some c → h₀.live c := by
        intro r i hp c hc
        rcases (dcell hdl).2 with ⟨h0, -⟩ | ⟨r', i', a', hp', g', -, -⟩
        · exact absurd h0 hdl
        · simp only [hp] at hp'; cases hp'
          exact (writeOut_live c).2 (view_block_live g' c hc)
      have blkLt : ∀ r i, destLen = .ref r i → ∀ c, BRef.block r = some c → c < h₀.nextBlk :=
        fun r i hp c hc => fresh₀.lt (dlLive r i hp c hc)
      have wH' : Writable H' destLen 8 := csf.agree.writable wd_out dlLive
      obtain ⟨H's, storeRes, stRes⟩ := store64_writable d.toUInt64 wH'
      have h'sEq : H's = writeOut H' destLen (lengthBytes d.toUInt64) := store_fun stRes
      have goodS : DGood H's (.tab h₀.nextBlk) (h₀.nextBlk + 1) zf sf := by
        rw [h'sEq]
        exact dgood_writeOut csf.good csf.owned blkLt
      obtain ⟨-, -, -, -, -, H2s_safe, run_safe, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, uniq2_safe, -, -⟩ :=
        Zlib.Deflate.Proofs.deflateEnd_safe goodS csf.zfree
      obtain ⟨H2s, endRun, hz2, liveC, fb, -, next2⟩ :=
        ZlibF.Spec.Public.DeflateEndProof.deflate_end_public H's (.tab h₀.nextBlk) (h₀.nextBlk + 1) zf sf goodS csf.zfree
      have uniq2 : Zlib.Deflate.Spec.Uniq H2s := by
        have := Except.ok.inj (run_safe.symm.trans endRun)
        simp only [Prod.mk.injEq] at this
        obtain ⟨-, rfl⟩ := this
        exact uniq2_safe
      have freeRun : freeZStream (some (.tab h₀.nextBlk)) H2s =
          .ok ((), { H2s with streams := upd H2s.streams h₀.nextBlk none }) := by
        simp only [freeZStream]
        rw [show H2s.streams.get h₀.nextBlk = some { zf with state := none } from hz2]
      have run : C.run (compress2_z_c dest destLen source n level) h =
          .ok (if st'.1 = Z_STREAM_END then Z_OK else st'.1,
               { H2s with streams := upd H2s.streams h₀.nextBlk none }) := by
        have hokF : (Z_OK != Z_OK) = false := by decide
        have loopRun := hres.trans loopEq
        have hzwr0 : zwr (some (.tab h.nextBlk))
            (fun z => { z with zalloc := FnPtr.null, zfree := FnPtr.null, «opaque» := .null }) hPreS =
            .ok ((), cHeap h₀) := by
          simp only [zwr, bind_app, ldZStream, ZStreamRef.get, hzS, eqcHeap]
        have hzwr1 : zwr (some (.tab h₀.nextBlk))
            (fun z => { z with next_out := dest, avail_out := 0 }) afterI =
            .ok ((), { afterI with streams := (upd afterI.streams h₀.nextBlk (some { z with next_out := dest, avail_out := 0 })) }) := by
          simp [zwr, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, hzA]
        have hzwr2 : zwr (some (.tab h₀.nextBlk))
            (fun z => { z with next_in := source, avail_in := 0 })
            { afterI with streams := (upd afterI.streams h₀.nextBlk (some { z with next_out := dest, avail_out := 0 })) } =
            .ok ((), { afterI with streams := upd afterI.streams h₀.nextBlk (some z0) }) := by
          simp [zwr, ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, upd_same, upd_upd, z0]
        have hzrdOut : zrd (some (.tab h₀.nextBlk)) (fun x => x.next_out) H' = .ok (zf.next_out, H') := by
          simp [zrd, ldZStream, ZStreamRef.get, hzf]
        unfold compress2_z_c
        simp only [C.run, bind_app, allocLocalZ_run fresh, hsn, beq_false_of_ne hdl,
          Bool.false_eq_true, ite_false, load64_cell ldCell, hcn, storePreS, hzwr0,
          version_gz_run, sizeof_z_stream, initRun', hokF]
        rw [← nb0]
        simp only [hzwr1, hzwr2]
        erw [loopRun]
        have endRun' : deflateEnd (some (.tab h₀.nextBlk)) H's =
            .ok (if sf.status = BUSY_STATE then Z_DATA_ERROR else Z_OK, H2s) := endRun
        simp only [hzrdOut, diffRun', storeRes, endRun', freeRun, pure_app, beq_iff_eq]
      have wd : Writable h dest capacity.toNat := by
        by_cases dn : dest = .null
        · exact Or.inl ⟨dn, Classical.byContradiction fun e => hcN ⟨by simp [UInt64.lt_iff_toNat_lt]; omega, dn⟩⟩
        · exact destW dn
      let expected := writeOut (writeOut h dest out) destLen (lengthBytes d.toUInt64)
      have expSame : SameObjectsUpToTableShape expected (writeOut (writeOut h₀ dest out) destLen (lengthBytes d.toUInt64)) := by
        dsimp [expected, h₀]
        exact writeOut_destLen_overwrite wd0 (by simp [lengthBytes_length]) wd outLe
      have storeDest : Store h dest out (writeOut h dest out) := by
        by_cases eo : out = []
        · subst eo; rw [writeOut_nil]; exact Or.inl ⟨rfl, rfl⟩
        · by_cases dn : dest = .null
          · subst dn
            have c0 : capacity.toNat = 0 := Classical.byContradiction fun hne =>
              hcN ⟨by simp [UInt64.lt_iff_toNat_lt]; omega, rfl⟩
            have h0 : out = [] := List.eq_nil_of_length_eq_zero (by simpa [e₀, c0] using outLe)
            exact absurd h0 eo
          · exact store_writeOut (by
              have := writable_sub (c := 0) (m := out.length) wd (by simpa [e₀] using outLe)
              simpa [advance_zero] using this)
      have w_after_dest : Writable (writeOut h dest out) destLen 8 :=
        writable_writeOut (dcell hdl).2 (by simpa [e₀] using outLe) wd
      have storeCell : Store (writeOut h dest out) destLen (lengthBytes d.toUInt64) expected :=
        store_writeOut (by rw [lengthBytes_length]; exact w_after_dest)
      have sameUpto : SameObjectsUpToTableShape expected { H2s with streams := upd H2s.streams h₀.nextBlk none } := by
        refine same_trans expSame ?_
        let exp₀ := writeOut (writeOut h₀ dest out) destLen (lengthBytes d.toUInt64)
        have hgl_d := writeOut_globals (writeOut h₀ dest out) destLen (lengthBytes d.toUInt64)
        have hgl_o := writeOut_globals h₀ dest out
        have hgl_h := writeOut_globals H' destLen (lengthBytes d.toUInt64)
        have neqD : lengthBytes d.toUInt64 ≠ [] := by
          intro e; have := congrArg List.length e; simp [lengthBytes_length] at this
        have agS : Agree h₀.live exp₀ H's := by
          rw [h'sEq]
          refine ⟨fun b lb => ?_, by rw [hgl_h.1, hgl_d.1, csf.agree.static],
            by rw [hgl_h.2.1, hgl_d.2.1, csf.agree.allocOk],
            by rw [hgl_h.2.2.1, hgl_d.2.2.1, csf.agree.garbage],
            by rw [hgl_h.2.2.2.2.2, hgl_d.2.2.2.2.2, csf.agree.borrow]⟩
          rcases (dcell hdl).2 with ⟨h0, -⟩ | ⟨r, i, _, hp, -, -, -⟩
          · exact absurd h0 hdl
          · dsimp only [exp₀]; rw [hp]
            cases gE : Space.get (writeOut h₀ dest out) r with
            | none =>
              have gH : Space.get H' r = none := by
                rw [(csf.agree.get (fun c hc => dlLive r i hp c hc)).1]; exact gE
              rw [writeOut_none gE, writeOut_none gH]
              exact csf.agree.blocks b lb
            | some aE =>
              have gH : Space.get H' r = some aE := by
                rw [(csf.agree.get (fun c hc => dlLive r i hp c hc)).1]; exact gE
              rw [writeOut_some gE neqD (i := i), writeOut_some gH neqD (i := i)]
              exact SameAt.put _ (csf.agree.blocks b lb) (fun c hc => csf.agree.blocks c (dlLive r i hp c hc))
        have hLive : ∀ b, h₀.live b → H's.live b := fun b hb => by
          obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := agS.blocks b hb
          have lexp : exp₀.live b := (writeOut_live b).2 ((writeOut_live b).2 hb)
          simp only [Heap.live] at lexp ⊢
          rw [s1, s2, s3, s4, s5, s6, s7]; exact lexp
        have notChanged : ∀ b, h₀.live b → ¬ (StreamRoot (.tab h₀.nextBlk) b ∨ DeflateOwned (h₀.nextBlk + 1) sf b) := by
          intro b lb hc
          have lt := fresh₀.lt lb
          rcases hc with sr | own
          · simp only [StreamRoot] at sr; omega
          · have hown := (csf.owned b).1 own
            simp only [CEnv.k, e₀] at hown
            omega
        have eLive : ∀ b, exp₀.live b ↔ h₀.live b := fun b =>
          (writeOut_live b).trans (writeOut_live b)
        obtain ⟨fs, fa, fg, -, hnallocE, frameB⟩ := fb
        have hLiveS : ∀ b, H's.live b → h₀.live b ∨ b = h₀.nextBlk ∨ (h₀.nextBlk + 1 ≤ b ∧ b < h₀.nextBlk + 6) := by
          intro b hb
          rw [h'sEq, writeOut_live b] at hb
          exact csf.liveOnly b hb
        have kLt : h₀.nextBlk < H's.nextBlk := by
          have hzS' : H's.streams h₀.nextBlk = some zf := goodS.live.hz
          have : H's.live h₀.nextBlk := Or.inr (Or.inr (Or.inl (by rw [hzS']; simp)))
          exact goodS.fresh.lt this
        refine upto_of ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro b
          by_cases bk : b = h₀.nextBlk
          · subst bk; exact tables_freed uniq2 hz2 (fun l => k0 ((eLive _).1 l))
          · refine Tables.trans ?_ (freed_tables bk)
            by_cases lb : h₀.live b
            · obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := agS.blocks b lb
              obtain ⟨t1, t2, t3, t4, t5, t6, t7, -⟩ := frameB b (hLive b lb) (notChanged b lb)
              exact ⟨t1.trans s1, t2.trans s2, t3.trans s3, t4.trans s4, t5.trans s5, t6.trans s6, t7.trans s7⟩
            · refine tables_dead (fun l => lb ((eLive b).1 l)) (fun l2 => ?_)
              rcases (liveC b).1 l2 with ⟨l1, notOwned⟩ | f
              · rcases hLiveS b l1 with x | x | x
                · exact lb x
                · exact bk x
                · exact notOwned (by simpa [CEnv.k] using (csf.owned b).2 x)
              · exact f
        · intro b lE
          have lb := (eLive b).1 lE
          have bk : b ≠ h₀.nextBlk := fun x => k0 (x ▸ lb)
          have t := (frameB b (hLive b lb) (notChanged b lb)).2.2.2.2.2.2.2
          have s8 := (agS.blocks b lb).2.2.2.2.2.2.2
          show H2s.ro b = _
          rw [t, s8]
        · show H2s.static = _
          rw [← fs, agS.static]
        · show H2s.allocOk = _
          rw [← fa, agS.allocOk]
        · show H2s.garbage = _
          rw [← fg, agS.garbage]
        · show exp₀.nextBlk ≤ H2s.nextBlk
          rw [hgl_d.2.2.2.1, hgl_o.2.2.2.1, next2]
          exact Nat.le_of_lt kLt
        · show exp₀.nalloc ≤ H2s.nalloc
          rw [hgl_d.2.2.2.2.1, hgl_o.2.2.2.2.1]
          have naH : H's.nalloc = H'.nalloc := by rw [h'sEq]; exact hgl_h.2.2.2.2.1
          have hna : H'.nalloc ≤ H2s.nalloc := by rw [← naH]; exact hnallocE
          exact Nat.le_trans csf.nalloc hna
      refine ⟨if st'.1 = Z_STREAM_END then Z_OK else st'.1,
        { H2s with streams := upd H2s.streams h₀.nextBlk none }, run, fun r => absurd r rej, ?_⟩
      intro _ _ _
      exact ⟨out, d.toUInt64, writeOut h dest out, expected, storeDest, storeCell, sameUpto, outLe, fun m => by
        exfalso
        rcases code' with x | x | x | x <;> rw [x] at m <;> exact absurd m (by decide)⟩

/-- Safety of `compress2_c` at every compression level. -/
theorem compress2_c_safety_gen (cr : CompressReach R) (call : GoalDeflateFor R)
    (facts : DeflateLoopFactsFor R) (level : Int32) :
    CompressorCSafety (fun d dl s n => compress2_c d dl s n level) false := by
  intro h dest destLen source capacity n xs fresh uniq globals fit dcell nn srcB destW sep sepD sepS
  have hdl : destLen ≠ .null := nn rfl
  have kept := cellHeap_kept fresh capacity
  have agree := cellHeap_agree fresh capacity
  have k0 : ¬ h.live h.nextBlk := fresh h.nextBlk (Nat.le_refl _)
  have notK : ∀ (q : BPtr) (m : Nat), (∀ r i, q = .ref r i → ∃ a, Space.get h r = some a) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk := fun _ _ => not_cell_block fresh
  have viaW : ∀ (q : BPtr) (m : Nat), (q ≠ .null → Writable h q m) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk := by
    intro q m w r i hq
    exact not_cell_block fresh (fun r' i' hq' => by
      rcases w (by rw [hq]; simp) with ⟨h0, -⟩ | ⟨r'', i'', a, hq'', g, -, -⟩
      · rw [hq] at h0; cases h0
      · rw [hq'] at hq''; cases hq''; exact ⟨a, g⟩) r i hq
  have viaB : ∀ (q : BPtr) (m : Nat) (ys : List UInt8), (q ≠ .null → Bytes h q m ys) →
      ∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk := by
    intro q m ys b r i hq
    exact not_cell_block fresh (fun r' i' hq' => by
      rcases b (by rw [hq]; simp) with ⟨h0, -, -⟩ | ⟨r'', i'', a, hq'', g, -, -⟩
      · rw [hq] at h0; cases h0
      · rw [hq'] at hq''; cases hq''; exact ⟨a, g⟩) r i hq
  have destK := viaW dest _ destW
  have srcK := viaB source _ _ srcB
  have lenK := viaW destLen 8 (fun dl => (dcell dl).2)
  have sepCell : ∀ (q : BPtr) (m : Nat), (∀ r i, q = .ref r i → ∀ c, BRef.block r = some c → c ≠ h.nextBlk) →
      Separate (cellPtr h) 8 q m :=
    fun _ _ qk => separate_cell (fun i e => qk (.blk h.nextBlk) i e h.nextBlk rfl rfl)
  have rawCell : LengthCell (cellRaw h) destLen capacity := by
    obtain ⟨hb, hw⟩ := dcell hdl
    refine ⟨?_, ?_⟩
    · rcases hb with ⟨h0, -⟩ | ⟨r, i, a, hp, gr, fitr, xr⟩
      · exact absurd h0 hdl
      · have ne : ∀ c, BRef.block r = some c → c ≠ h.nextBlk := lenK r i hp
        have gs : Space.get (cellRaw h) r = some a := by
          cases r with
          | blk c => exact (upd_ne _ _ _ _ (ne c rfl) : _).trans gr
          | _ => exact gr
        exact Or.inr ⟨r, i, a, hp, gs, fitr, xr⟩
    · rcases hw with ⟨h0, -⟩ | ⟨r, i, a, hp, gr, ro, fitr⟩
      · exact absurd h0 hdl
      · have ne : ∀ c, BRef.block r = some c → c ≠ h.nextBlk := lenK r i hp
        have gs : Space.get (cellRaw h) r = some a := by
          cases r with
          | blk c => exact (upd_ne _ _ _ _ (ne c rfl) : _).trans gr
          | _ => exact gr
        have ros : Space.ro (cellRaw h) r = false := by
          cases r with
          | blk c => exact (upd_ne _ _ _ _ (ne c rfl) : _).trans ro
          | _ => exact ro
        exact Or.inr ⟨r, i, a, hp, gs, ros, fitr⟩
  obtain ⟨rc, after', run', rej', ok'⟩ :=
    compress2_z_c_safety_gen cr call facts level (cellHeap h capacity) dest (cellPtr h) source capacity n xs
      (cellHeap_fresh fresh capacity) (cellHeap_uniq fresh uniq capacity) (cellHeap_globals globals capacity)
      (cellHeap_fit fresh fit capacity) (fun _ => cellHeap_cell h capacity) (fun e => by cases e)
      (fun sn => kept.bytes_of (srcB sn)) (fun dn => kept.writable_of (destW dn)) sep
      (sepCell dest _ destK) (sepCell source _ srcK)
  have x'k : (cellHeap h capacity).words h.nextBlk = none ∧ (cellHeap h capacity).streams h.nextBlk = none ∧
      (cellHeap h capacity).gzheaders h.nextBlk = none ∧ (cellHeap h capacity).dstates h.nextBlk = none ∧
      (cellHeap h capacity).istates h.nextBlk = none ∧ (cellHeap h capacity).gzstates h.nextBlk = none := by
    simp only [Heap.live, not_or, ne_eq, Decidable.not_not] at k0
    exact ⟨k0.2.1, k0.2.2.1, k0.2.2.2.1, k0.2.2.2.2.1, k0.2.2.2.2.2.1, k0.2.2.2.2.2.2⟩
  by_cases bad : compressRejected dest (if destLen = .null then none else some capacity) source n
  · have badCell : compressRejected dest (if cellPtr h = .null then none else some capacity) source n := by
      have cne : cellPtr h ≠ .null := by simp [cellPtr]
      simpa [hdl, cne] using bad
    obtain ⟨rfl, sm⟩ := rej' badCell
    have lcGot : LengthCell after' (cellPtr h) capacity := by
      have hc := cellHeap_cell h capacity
      obtain ⟨s1, -, s3, -⟩ := sm
      refine ⟨?_, ?_⟩
      · rcases hc.1 with ⟨h0, -⟩ | ⟨r, i, a, hp, g, f, x⟩
        · cases h0
        · simp only [cellPtr] at hp; cases hp
          refine Or.inr ⟨.blk h.nextBlk, 0, a, rfl, ?_, f, x⟩
          change after'.bytes h.nextBlk = some a
          rw [s1 h.nextBlk]; exact g
      · rcases hc.2 with ⟨h0, -⟩ | ⟨r, i, a, hp, g, ro, f⟩
        · cases h0
        · simp only [cellPtr] at hp; cases hp
          refine Or.inr ⟨.blk h.nextBlk, 0, a, rfl, ?_, ?_, f⟩
          · change after'.bytes h.nextBlk = some a
            rw [s1 h.nextBlk]; exact g
          · change after'.ro h.nextBlk = false
            rw [s3 h.nextBlk (Or.inl (by simp [cellHeap]))]; exact ro
    have wDL : Writable after' destLen 8 := by
      have wd0 := agree.writable (dcell hdl).2 (fun r i hp c hc => lenK r i hp c hc)
      rcases wd0 with ⟨h0, -⟩ | ⟨r, i, a, hp, gr, ro, fitr⟩
      · exact absurd h0 hdl
      · cases r with
        | blk c =>
          refine Or.inr ⟨.blk c, i, a, hp, ?_, ?_, fitr⟩
          · change after'.bytes c = some a; rw [sm.1 c]; exact gr
          · change after'.ro c = false
            rw [sm.2.2.1 c (Or.inl (by simp only [Space.get] at gr; rw [gr]; simp))]; exact ro
        | dstate_depth c =>
          refine Or.inr ⟨.dstate_depth c, i, a, hp, ?_, ro, fitr⟩
          simp only [Space.get] at gr ⊢; rw [sm.2.2.2.2.2.1 c]; exact gr
        | str _ => cases ro
        | st_dist_code => cases ro
        | st_length_code => cases ro
    obtain ⟨wAfter, storeAfter, sfAfter⟩ := store64_writable capacity wDL
    have wEq : wAfter = writeOut after' destLen (lengthBytes capacity) := store_fun sfAfter
    have cellB : wAfter.bytes h.nextBlk = some (lengthBytes capacity).toArray ∧ wAfter.ro h.nextBlk = false := by
      rw [wEq]
      have l0 := writeOut_same_other (H := after') (p := destLen) (xs := lengthBytes capacity) h.nextBlk
        (fun r i hp hb => lenK r i hp _ hb rfl)
      rw [l0.1, l0.2.2.2.2.2.2.2]
      exact ⟨by rw [sm.1 h.nextBlk]; simp [cellHeap],
             by rw [sm.2.2.1 h.nextBlk (Or.inl (by simp [cellHeap]))]; simp [cellHeap]⟩
    have freeR := freeB_blk_run cellB.1 cellB.2
    have run : C.run (compress2_c dest destLen source n level) h =
        .ok (Z_STREAM_ERROR, { wAfter with bytes := upd wAfter.bytes h.nextBlk none }) := by
      have hfr : freeB (cellPtr h) wAfter =
          .ok ((), { wAfter with bytes := upd wAfter.bytes h.nextBlk none }) := by
        simpa [cellPtr] using freeR
      unfold compress2_c
      simp only [C.run, bind_app, alloc_cell_run fresh, load64_cell rawCell, store_cell_run h capacity]
      rw [show compress2_z_c dest (cellPtr h) source n level (cellHeap h capacity) = .ok (Z_STREAM_ERROR, after') from run']
      simp only [load64_cell lcGot, storeAfter, hfr, pure_app]
    refine ⟨Z_STREAM_ERROR, { wAfter with bytes := upd wAfter.bytes h.nextBlk none }, run,
      fun _ => ⟨rfl, ?_⟩, fun _ hs hd => by
        exfalso
        rcases bad with c0 | ⟨rfl, hne⟩ | ⟨c, hc, rfl, hne⟩
        · simp [hdl] at c0
        · exact hne (hs rfl)
        · simp only [hdl, ite_false, Option.some.injEq] at hc; subst hc
          exact hne (hd rfl)⟩
    rw [wEq]
    have selfC : writeOut (cellHeap h capacity) destLen (lengthBytes capacity) = cellHeap h capacity :=
      cell_self_write (kept.cell_of (dcell hdl))
    have smW := selfC ▸ same_writeOut_both sm destLen (lengthBytes capacity)
    exact same_without_cell smW agree k0 x'k (by simp [cellHeap]) (by simp [cellHeap])
  · have hsN : source = .null → n = 0 := fun e => Classical.byContradiction fun ne =>
      bad (Or.inr (Or.inl ⟨e, ne⟩))
    have hcN : dest = .null → capacity = 0 := fun e => Classical.byContradiction fun ne =>
      bad (Or.inr (Or.inr ⟨capacity, by simp [hdl], e, ne⟩))
    have wd : Writable h dest capacity.toNat := by
      by_cases dn : dest = .null
      · exact Or.inl ⟨dn, by rw [hcN dn]; rfl⟩
      · exact destW dn
    have lbne : ∀ v, lengthBytes v ≠ [] := by
      intro v e; have := congrArg List.length e; simp [lengthBytes_length] at this
    obtain ⟨out, got, h₁', exp', S1, S2, sm, outLe, mem'⟩ := ok' (by simp [cellPtr]) hsN hcN
    have e1 := store_fun S1
    have e2 := store_fun S2
    subst e1 e2
    -- Read `got` back from `cellPtr h` in `after'`, write to `destLen`, and free `cellPtr h`
    have cellAfter : after'.bytes h.nextBlk = some (lengthBytes got).toArray ∧ after'.ro h.nextBlk = false := by
      have l0 := writeOut_same_other (H := cellHeap h capacity) (p := dest) (xs := out) h.nextBlk
        (fun r i hp hb => destK r i hp _ hb rfl)
      have g1 : Space.get (writeOut (cellHeap h capacity) dest out) (BRef.blk h.nextBlk) =
          some (lengthBytes capacity).toArray := by
        show (writeOut (cellHeap h capacity) dest out).bytes h.nextBlk = _
        rw [l0.1]; simp [cellHeap]
      have r1 : Space.ro (writeOut (cellHeap h capacity) dest out) (BRef.blk h.nextBlk) = false := by
        show (writeOut (cellHeap h capacity) dest out).ro h.nextBlk = false
        rw [l0.2.2.2.2.2.2.2]; simp [cellHeap]
      have mid := writeOut_some (X := writeOut (cellHeap h capacity) dest out) (i := 0) g1 (lbne got)
      have l1 : (writeOut (writeOut (cellHeap h capacity) dest out) (cellPtr h) (lengthBytes got)).bytes h.nextBlk =
          some (lengthBytes got).toArray := by
        show Space.get (writeOut (writeOut (cellHeap h capacity) dest out) (cellPtr h) (lengthBytes got)) (BRef.blk h.nextBlk) = _
        rw [cellPtr, mid]
        simp [Space.get, Space.put, lengthBytes_length]
      have rr1 : (writeOut (writeOut (cellHeap h capacity) dest out) (cellPtr h) (lengthBytes got)).ro h.nextBlk = false := by
        show Space.ro (writeOut (writeOut (cellHeap h capacity) dest out) (cellPtr h) (lengthBytes got)) (BRef.blk h.nextBlk) = false
        rw [writeOut_ro (r := .blk h.nextBlk)]; exact r1
      exact ⟨by rw [sm.1 h.nextBlk]; exact l1,
             by rw [sm.2.2.1 h.nextBlk (Or.inl (by rw [l1]; simp))]; exact rr1⟩
    have lcGot : LengthCell after' (cellPtr h) got :=
      ⟨Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes got).toArray, rfl, cellAfter.1, by simp [lengthBytes_length],
        by change ((lengthBytes got).drop 0).take 8 = lengthBytes got
           rw [List.drop_zero]
           exact List.take_of_length_le (by rw [lengthBytes_length]; exact Nat.le_refl _)⟩,
       Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes got).toArray, rfl, cellAfter.1, cellAfter.2, by simp [lengthBytes_length]⟩⟩
    have wDL : Writable after' destLen 8 := by
      have w0 := writable_writeOut (agree.writable (dcell hdl).2 (fun r i hp c hc => lenK r i hp c hc))
        outLe (kept.writable_of wd)
      have l0c := writeOut_same_other (H := cellHeap h capacity) (p := dest) (xs := out) h.nextBlk
        (fun r i hp hb => destK r i hp _ hb rfl)
      have wc1 : Writable (writeOut (cellHeap h capacity) dest out) (cellPtr h) 8 :=
        Or.inr ⟨.blk h.nextBlk, 0, (lengthBytes capacity).toArray, by simp [cellPtr],
          by show (writeOut (cellHeap h capacity) dest out).bytes h.nextBlk = _; rw [l0c.1]; simp [cellHeap],
          by show (writeOut (cellHeap h capacity) dest out).ro h.nextBlk = false; rw [l0c.2.2.2.2.2.2.2]; simp [cellHeap],
          by simp [lengthBytes_length]⟩
      have w1 := writable_writeOut (xs := lengthBytes got) w0 (by simp [lengthBytes_length]) wc1
      rcases w1 with ⟨h0, -⟩ | ⟨r, i, a, hp, gr, ro, fitr⟩
      · exact absurd h0 hdl
      · cases r with
        | blk c =>
          refine Or.inr ⟨.blk c, i, a, hp, ?_, ?_, fitr⟩
          · change after'.bytes c = some a; rw [sm.1 c]; exact gr
          · change after'.ro c = false
            rw [sm.2.2.1 c (Or.inl (by simp only [Space.get] at gr; rw [gr]; simp))]; exact ro
        | dstate_depth c =>
          refine Or.inr ⟨.dstate_depth c, i, a, hp, ?_, ro, fitr⟩
          simp only [Space.get] at gr ⊢; rw [sm.2.2.2.2.2.1 c]; exact gr
        | str _ => cases ro
        | st_dist_code => cases ro
        | st_length_code => cases ro
    obtain ⟨wAfter, storeAfter, sfAfter⟩ := store64_writable got wDL
    have wEq : wAfter = writeOut after' destLen (lengthBytes got) := store_fun sfAfter
    have cellB : wAfter.bytes h.nextBlk = some (lengthBytes got).toArray ∧ wAfter.ro h.nextBlk = false := by
      rw [wEq]
      have l0 := writeOut_same_other (H := after') (p := destLen) (xs := lengthBytes got) h.nextBlk
        (fun r i hp hb => lenK r i hp _ hb rfl)
      exact ⟨by rw [l0.1]; exact cellAfter.1, by rw [l0.2.2.2.2.2.2.2]; exact cellAfter.2⟩
    have freeR := freeB_blk_run cellB.1 cellB.2
    have run : C.run (compress2_c dest destLen source n level) h =
        .ok (rc, { wAfter with bytes := upd wAfter.bytes h.nextBlk none }) := by
      have hfr : freeB (cellPtr h) wAfter =
          .ok ((), { wAfter with bytes := upd wAfter.bytes h.nextBlk none }) := by
        simpa [cellPtr] using freeR
      unfold compress2_c
      simp only [C.run, bind_app, alloc_cell_run fresh, load64_cell rawCell, store_cell_run h capacity]
      rw [show compress2_z_c dest (cellPtr h) source n level (cellHeap h capacity) = .ok (rc, after') from run']
      simp only [load64_cell lcGot, storeAfter, hfr, pure_app]
    have a1 := agree.writeOut_both (xs := out) destK
    have a2 := a1.writeOut_both (xs := lengthBytes got) lenK
    have a3 := a2.write_right (xs := lengthBytes got) (p := cellPtr h)
      (fun r i hp => by simp only [cellPtr, Ptr.ref.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl)
    have smW := same_writeOut_both sm destLen (lengthBytes got)
    have smComm : SameObjectsUpToTableShape
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got))
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) (cellPtr h) (lengthBytes got)) destLen (lengthBytes got)) := by
      apply same_writeOut_comm_cell
      · rw [lengthBytes_length]
        exact writable_writeOut (kept.writable_of (dcell hdl).2) outLe (kept.writable_of wd)
      · rw [lengthBytes_length]
        have wc0 := (cellHeap_cell h capacity).2
        exact writable_writeOut wc0 outLe (kept.writable_of wd)
      · rw [lengthBytes_length]
        exact separate_symm' (sepCell destLen 8 lenK)
      · exact hdl
      · simp [cellPtr]
      · exact ⟨lbne got, lbne got⟩
    have smW' := same_trans smComm smW
    have x'k2 : (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).words h.nextBlk = none ∧
        (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).streams h.nextBlk = none ∧
        (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).gzheaders h.nextBlk = none ∧
        (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).dstates h.nextBlk = none ∧
        (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).istates h.nextBlk = none ∧
        (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).gzstates h.nextBlk = none := by
      have o1 := writeOut_same_other (H := cellHeap h capacity) (p := dest) (xs := out) h.nextBlk
        (fun r i hp hb => destK r i hp _ hb rfl)
      have o2 := writeOut_same_other (H := writeOut (cellHeap h capacity) dest out) (p := destLen) (xs := lengthBytes got) h.nextBlk
        (fun r i hp hb => lenK r i hp _ hb rfl)
      rw [o2.2.1, o2.2.2.1, o2.2.2.2.1, o2.2.2.2.2.1, o2.2.2.2.2.2.1, o2.2.2.2.2.2.2.1,
          o1.2.1, o1.2.2.1, o1.2.2.2.1, o1.2.2.2.2.1, o1.2.2.2.2.2.1, o1.2.2.2.2.2.2.1]
      exact x'k
    have x'k3 : (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).words h.nextBlk = none ∧
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).streams h.nextBlk = none ∧
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).gzheaders h.nextBlk = none ∧
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).dstates h.nextBlk = none ∧
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).istates h.nextBlk = none ∧
        (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).gzstates h.nextBlk = none := by
      have gCell : Space.get (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (BRef.blk h.nextBlk) =
          some (lengthBytes capacity).toArray := by
        have o1 := writeOut_same_other (H := cellHeap h capacity) (p := dest) (xs := out) h.nextBlk
          (fun r i hp hb => destK r i hp _ hb rfl)
        have o2 := writeOut_same_other (H := writeOut (cellHeap h capacity) dest out) (p := destLen) (xs := lengthBytes got) h.nextBlk
          (fun r i hp hb => lenK r i hp _ hb rfl)
        show (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)).bytes h.nextBlk =
            some (lengthBytes capacity).toArray
        rw [o2.1, o1.1]; simp [cellHeap]
      rw [cellPtr, writeOut_some gCell (lbne got)]
      exact x'k2
    have storeDest : Store h dest out (writeOut h dest out) := agree.store_left S1 destK
    have storeCell : Store (writeOut h dest out) destLen (lengthBytes got)
        (writeOut (writeOut h dest out) destLen (lengthBytes got)) := by
      apply store_writeOut
      rw [lengthBytes_length]
      exact writable_writeOut (dcell hdl).2 outLe wd
    refine ⟨rc, { wAfter with bytes := upd wAfter.bytes h.nextBlk none }, run,
      fun b => absurd b bad, fun _ _ _ => ?_⟩
    refine ⟨out, got, writeOut h dest out, writeOut (writeOut h dest out) destLen (lengthBytes got),
      storeDest, storeCell, ?_, outLe, fun m => ?_⟩
    · rw [wEq]
      have nbE : (writeOut (writeOut h dest out) destLen (lengthBytes got)).nextBlk ≤
          (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).nextBlk := by
        simp only [(writeOut_globals _ _ _).2.2.2.1, cellHeap]; omega
      have naE : (writeOut (writeOut h dest out) destLen (lengthBytes got)).nalloc ≤
          (writeOut (writeOut (writeOut (cellHeap h capacity) dest out) destLen (lengthBytes got)) (cellPtr h) (lengthBytes got)).nalloc := by
        simp only [(writeOut_globals _ _ _).2.2.2.2.1, cellHeap]; exact Nat.le_refl _
      have kNotLive : ¬ (writeOut (writeOut h dest out) destLen (lengthBytes got)).live h.nextBlk := by
        rw [writeOut_live, writeOut_live]; exact k0
      exact same_without_cell smW' a3 kNotLive x'k3 nbE naE
    · obtain ⟨j, lo, hi, bbad⟩ := mem' m
      have naW : wAfter.nalloc = after'.nalloc := by rw [wEq]; exact (writeOut_globals _ _ _).2.2.2.2.1
      rw [naW]
      exact ⟨j, by simpa [cellHeap] using lo, hi, by simpa [cellHeap] using bbad⟩

/-- Safety of `compress_z_c`: `compress2_z_c` at `Z_DEFAULT_COMPRESSION`. -/
theorem compress_z_c_safety (cr : CompressReach R) (call : GoalDeflateFor R)
    (facts : DeflateLoopFactsFor R) :
    CompressorCSafety compress_z_c true :=
  compress2_z_c_safety_gen cr call facts Z_DEFAULT_COMPRESSION

/-- Safety of `compress_c`: `compress2_c` at `Z_DEFAULT_COMPRESSION`. -/
theorem compress_c_safety (cr : CompressReach R) (call : GoalDeflateFor R)
    (facts : DeflateLoopFactsFor R) :
    CompressorCSafety compress_c false :=
  compress2_c_safety_gen cr call facts Z_DEFAULT_COMPRESSION

/-- Public hypothesis-free safety theorems for all four C-ABI compressor entrypoints. -/
theorem compress2_z_c_safety_pub (level : Int32) :
    CompressorCSafety (fun d dl s n => compress2_z_c d dl s n level) true :=
  compress2_z_c_safety_gen compressReach_mid goalDeflate_mid loopFacts_mid level

theorem compress2_c_safety_pub (level : Int32) :
    CompressorCSafety (fun d dl s n => compress2_c d dl s n level) false :=
  compress2_c_safety_gen compressReach_mid goalDeflate_mid loopFacts_mid level

theorem compress_z_c_safety_pub : CompressorCSafety compress_z_c true :=
  compress2_z_c_safety_pub Z_DEFAULT_COMPRESSION

theorem compress_c_safety_pub : CompressorCSafety compress_c false :=
  compress2_c_safety_pub Z_DEFAULT_COMPRESSION

#print axioms compress2_z_c_safety_pub
#print axioms compress2_c_safety_pub
#print axioms compress_z_c_safety_pub
#print axioms compress_c_safety_pub

end ZlibF.Spec.Public.Proofs.Compress

