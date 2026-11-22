import ZlibF.Proof.«public-uncompress-safe»
import ZlibF.Proof.«public-roundtrip-compress»

/-! # `uncompress` completes on a complete stream

`uncompress` runs `uncompress2_z` inside two length-cell wrappers. Its local stream, from
`inflateInit`, is a default decoder history (`DefaultInflateTrace`): the refills of the loop are
caller edits and every call runs where allocations succeed. On a source that decodes to `D` and
does not ask for a dictionary, with room for `D`, every call either returns `Z_OK` with an output
that is still a prefix of `D`, or returns `Z_STREAM_END` with exactly `D` written
(`Goal.default_inflate_progress`); `Z_NEED_DICT` would need `FDICT`, and `Z_BUF_ERROR` needs
`Z_FINISH`. The loop of the safety proof (`call_phase_safe`) is followed with this history beside
it (`tracked_uloop`).

The run of `uncompress2_z` is the one of its safety proof (`accepted_run_safe`), with the tracked
loop added: both loops are the same actual loop, so they end on the same heap, and two loop ends on
one heap have written the same bytes (`final_output_eq`). No uniqueness of decoding is used. The
two wrappers keep the heap's allocator (`single_of_counted_on`, `counted2_of_z_on`).
-/

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

section Uncompress
open ZlibF.Spec.Public.Proofs.Uncompress
open Zlib.Inflate (inflate)
open Zlib.Uncompr (UncLoop)

/-- A byte range is read the same way twice. -/
theorem bytes_unique {H : Heap} {p : BPtr} {n : Nat} {xs ys : List UInt8} (a : Bytes H p n xs)
    (b : Bytes H p n ys) : xs = ys := by
  rcases a with ⟨p0, -, rfl⟩ | ⟨r, i, arr, rfl, g, -, rfl⟩
  · rcases b with ⟨-, -, rfl⟩ | ⟨r', i', arr', pr, -, -, -⟩
    · rfl
    · rw [p0] at pr
      cases pr
  · rcases b with ⟨p0, -, -⟩ | ⟨r', i', arr', pr, g', -, rfl⟩
    · cases p0
    · cases pr
      rw [g] at g'
      cases g'
      rfl

/-- Two ends of the loop on one heap have written the same bytes. -/
theorem final_output_eq {e : Env} (ok : EnvOK e) {l : UncLoop} {rc1 rc2 : Int32} {Hp1 Hp2 H : Heap}
    {logp1 logp2 : DataLog} {in1 in2 o1 o2 : List UInt8} {u1 u2 i1 i2 : Nat} {zp1 zp2 z1 z2 : ZStream}
    {sp1 sp2 s1 s2 : InflateState}
    (f1 : SafeFinal e l rc1 Hp1 H logp1 in1 o1 u1 i1 zp1 z1 sp1 s1)
    (f2 : SafeFinal e l rc2 Hp2 H logp2 in2 o2 u2 i2 zp2 z2 sp2 s2) :
    logp1.output ++ o1 = logp2.output ++ o2 := by
  have ez : z1 = z2 := Option.some.inj (f1.good.live.hz.symm.trans f2.good.live.hz)
  subst ez
  have c1 := f1.outCount
  have c2 := f2.outCount
  have len : (logp1.output ++ o1).length = (logp2.output ++ o2).length := by omega
  rcases ok.outW with ⟨_, c0⟩ | w
  · have a : logp1.output ++ o1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have b : logp2.output ++ o2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [a, b]
  · have blocks := ZlibF.Spec.Public.Proofs.Compress.caller_view_blocks (Or.inr w)
    have htake : ∀ {xs ys : List UInt8}, (xs ++ ys).take xs.length = xs := by
      intro xs ys; induction xs <;> simp [*]
    have read : ∀ O P : List UInt8, P <+: O → O.length ≤ e.cap →
        Agree e.h₀.live (writeOut e.h₀ e.out0 O) H → Bytes H e.out0 P.length P := by
      intro O P hpref le agree
      have wO : Writable e.h₀ e.out0 O.length := by
        have := writable_sub (c := 0) (m := O.length) w (by omega)
        rwa [advance_zero] at this
      have bFull := agree.bytes (bytes_writeOut_self wO) blocks
      have bSub := bytes_sub bFull (show 0 + P.length ≤ O.length by have := hpref.length_le; omega)
      rw [advance_zero, List.drop_zero] at bSub
      obtain ⟨suf, rfl⟩ := hpref
      simpa only [htake] using bSub
    obtain ⟨w1, p1, l1, a1⟩ := f1.agree
    obtain ⟨w2, p2, l2, a2⟩ := f2.agree
    have b1 := read w1 (logp1.output ++ o1) p1 l1 a1
    have b2 := read w2 (logp2.output ++ o2) p2 l2 a2
    rw [len] at b1
    exact bytes_unique b1 b2

/-- What a run on a complete stream with room for its decoding gives. -/
structure UFacts (e : Env) (D : List UInt8) : Prop where
  ok : EnvOK e
  decodes : Zlib.Decodes [] e.src D
  noDict : ¬ AsksDictionary e.src
  room : D.length ≤ e.cap
  noFail : NoAllocationFailure e.h₀

/-- The loop goes on: the safety state, the decoder history of the stream, and an output that
is a prefix of `D`. -/
def UGoing (e : Env) (D : List UInt8) (l : UncLoop) (H : Heap) : Prop :=
  ∃ log i z s, SafeState e l H log i z s ∧ DefaultInflateTrace e.r H log ∧ log.finished = false ∧
    log.output <+: D

/-- The loop has ended with `Z_STREAM_END` and exactly `D` written. -/
def UDone (e : Env) (D : List UInt8) (l : UncLoop) (H : Heap) : Prop :=
  l.err = Z_STREAM_END ∧ ∃ Hp logp input output u i zp z sp s,
    SafeFinal e l l.err Hp H logp input output u i zp z sp s ∧ logp.output ++ output = D

/-- **One call on a complete stream**, after the refills: it ends with `D` written, or returns
`Z_OK` with an output that is still a prefix of `D`. -/
theorem classify {e : Env} {D : List UInt8} (F : UFacts e D) {l : UncLoop} {H H' : Heap} {log : DataLog}
    {i : Nat} {z : ZStream} {s : InflateState} {rc : Int32} {input out : List UInt8} {u : Nat}
    (st : SafeState e l H log i z s) (trace : DefaultInflateTrace e.r H log)
    (unfinished : log.finished = false) (pre : log.output <+: D)
    (fullIn : z.avail_in = 0 → l.len = 0) (fullOut : z.avail_out = 0 → l.left = 0)
    (obs : DataStep .inflate H H' e.r Z_NO_FLUSH rc input out u)
    (inEq : input = (e.src.drop log.input.length).take z.avail_in.toNat) :
    (rc = Z_STREAM_END ∧ log.output ++ out = D) ∨ (rc = Z_OK ∧ log.output ++ out <+: D) := by
  have original := obs
  obtain ⟨z0, _z1, g0, _g1, buffers, _active, bytesIn, _usedEq, _bytesOut, _run⟩ := original
  have ez : z0 = z := Option.some.inj (g0.symm.trans st.good.live.hz)
  subst ez
  have noFail : NoAllocationFailure H := by
    intro k
    obtain ⟨w, -, -, ag⟩ := st.agree
    rw [ag.allocOk, (writeOut_globals e.h₀ e.out0 w).2.1]
    exact F.noFail k
  have inC := st.inCount
  have outC := st.outCount
  have srcLen := F.ok.srcLen
  have prefixLog : log.input <+: e.src := by
    have tp := List.take_prefix log.input.length e.src
    rw [← st.inTake] at tp
    exact tp
  have prefixIn : log.input ++ input <+: e.src := by
    rw [inEq]
    have tp := List.take_prefix (log.input.length + z0.avail_in.toNat) e.src
    rw [List.take_add, ← st.inTake] at tp
    exact tp
  have nonempty : input ≠ [] ∨ log.input = e.src := by
    by_cases a0 : z0.avail_in = 0
    · right
      have len0 := fullIn a0
      have l0 : l.len.toNat = 0 := by simp [len0]
      have a0n : z0.avail_in.toNat = 0 := by rw [a0]; rfl
      rw [st.inTake]
      exact List.take_of_length_le (by omega)
    · left
      rw [inEq]
      intro nil
      have count := congrArg List.length nil
      rw [List.length_take, List.length_drop, List.length_nil] at count
      have pos : z0.avail_in.toNat ≠ 0 := fun zero => a0 (u32_zero zero)
      omega
  have roomOrDone : z0.avail_out ≠ 0 ∨ log.output = D := by
    by_cases o0 : z0.avail_out = 0
    · right
      have l0 := fullOut o0
      have lN : l.left.toNat = 0 := by simp [l0]
      have oN : z0.avail_out.toNat = 0 := by rw [o0]; rfl
      have le := pre.length_le
      have room := F.room
      exact pre.eq_of_length (by omega)
    · exact Or.inl o0
  have outNN : z0.next_out ≠ .null := by
    rw [st.nextOut]
    exact ZlibF.Spec.Public.Proofs.Uncompress.advance_ne_null _ F.ok.outNotNull
  obtain ⟨rc', _after', out', _u', step', cases⟩ :=
    Zlib.Inflate.Proofs.DefaultCompletes.progress e.r H log e.src D input z0 Z_NO_FLUSH trace unfinished
      F.decodes prefixLog st.fit noFail buffers st.good.live.hz outNN roomOrDone bytesIn prefixIn nonempty
      (Or.inl rfl)
  obtain ⟨_, erc, _, eo⟩ := inflate_step_unique step' obs
  rw [erc, eo] at cases
  rcases cases with ⟨e1, -, e3⟩ | ⟨codes, -, -, p⟩ | ⟨_, asks, _⟩
  · exact Or.inl ⟨e1, e3⟩
  · rcases codes with c | ⟨_, f⟩
    · exact Or.inr ⟨c, p⟩
    · exact absurd f (by decide)
  · exact absurd asks F.noDict

/-- **The tracked loop of `uncompress2_z`** on a complete stream: it ends with `Z_STREAM_END` and
exactly `D` written. -/
theorem tracked_uloop {e : Env} {D : List UInt8} (F : UFacts e D) {body : UncLoop → M UncLoop}
    {cond : UncLoop → M (Bool × UncLoop)} (hB : BodyOK e.r body) (hC : CondOK cond) {l : UncLoop}
    {H : Heap} (going : UGoing e D l H) :
    ∃ l' H', cdoWhile body cond l H = .ok (l', H') ∧ UDone e D l' H' := by
  have start := going
  obtain ⟨_, _, _, _, st0, _⟩ := start
  refine cdoWhile_decreasing (UGoing e D) (UDone e D) (measure e) ?_ going (measure_bound F.ok st0)
  rintro l H ⟨log, i, z, s, st, trace, unfinished, pre⟩
  have hz : e.r.get H = some z := st.good.live.hz
  have st1 := st.refill F.ok
  have rebuf := rebuffer_put st.good st.globals (st.notOwned e.k (Or.inr (Or.inl rfl)))
    (z₁ := refilled z l) (by simp [refilled])
  have trace1 : DefaultInflateTrace e.r (e.r.put H (refilled z l)) log := .caller trace rebuf st1.fit
  have noFail1 : NoAllocationFailure (e.r.put H (refilled z l)) := by
    intro k
    obtain ⟨w, -, -, ag⟩ := st1.agree
    rw [ag.allocOk, (writeOut_globals e.h₀ e.out0 w).2.1]
    exact F.noFail k
  obtain ⟨rc, H', run, more, done⟩ :=
    call_phase_safe Zlib.Inflate.Proofs.inflate_public F.ok st1 (refilled_full_in z l) (refilled_full_out z l)
  have bodyEq : body l H = .ok ({ refilledLoop z l with err := rc }, H') := by
    rw [hB l H z hz]
    simp only [bind_app, pure_app]
    rw [show inflate (some e.r) Z_NO_FLUSH (e.r.put H (refilled z l)) = .ok (rc, H') from run]
  refine ⟨_, H', rc == Z_OK, { refilledLoop z l with err := rc }, H', bodyEq, hC _ _, ?_, ?_⟩
  · intro c
    have rcOk : rc = Z_OK := by simpa using c
    obtain ⟨input, out, u, z', s', obs, inEq, _uLe, st', lt⟩ := more rcOk
    rcases classify F st1 trace1 unfinished pre (refilled_full_in z l) (refilled_full_out z l) obs inEq with
      ⟨endc, _⟩ | ⟨_, pre'⟩
    · rw [rcOk] at endc
      exact absurd endc (by decide)
    · refine ⟨⟨okLog log input out u, i, z', s', st', ?_, ?_, pre'⟩, ?_⟩
      · have t := DefaultInflateTrace.step trace1 st1.fit noFail1 obs
        rw [rcOk] at t
        exact t
      · show (log.finished || (Z_OK == Z_STREAM_END)) = false
        rw [unfinished]
        decide
      · rw [measure_refill st] at lt
        exact lt
  · intro c
    have rcNe : rc ≠ Z_OK := by simpa using c
    obtain ⟨input, output, u, z', s', fin⟩ := done rcNe
    rcases classify F st1 trace1 unfinished pre (refilled_full_in z l) (refilled_full_out z l) fin.step
        fin.input_eq with ⟨endc, written⟩ | ⟨okc, _⟩
    · exact ⟨endc, _, _, input, output, u, i, _, z', _, s', fin, written⟩
    · exact absurd okc rcNe

/-- The tracked loop of the translation, found in a goal by `generalize`. -/
theorem tracked_uresult {e : Env} {D : List UInt8} (F : UFacts e D) {body : UncLoop → M UncLoop}
    {cond : UncLoop → M (Bool × UncLoop)} {l : UncLoop} {H : Heap} (going : UGoing e D l H)
    {res : Except Fault (UncLoop × Heap)} (hres : cdoWhile body cond l H = res) {k : Nat}
    (hk : e.r = .tab k) (hB : BodyOK (.tab k) body) (hC : CondOK cond) :
    ∃ l' H', res = .ok (l', H') ∧ UDone e D l' H' := by
  obtain ⟨l', H', run, done⟩ := tracked_uloop F (hk ▸ hB) hC going
  exact ⟨l', H', hres.symm.trans run, done⟩

set_option maxRecDepth 100000 in
open Zlib.Inflate.Proofs Zlib.Inflate.Spec in
/-- The local stream of `uncompress2_z` after `inflateInit` and the first buffer setting is a
default decoder history. -/
theorem start_trace {e : Env} (ok : EnvOK e) (uniq : Zlib.Inflate.Spec.Uniq e.h₀)
    (globals : LibraryGlobals e.h₀) (fit : ZlibF.PlatformMemory.ByteObjectsFit e.h₀)
    (alloc : e.h₀.allocOk e.h₀.nalloc = true) :
    DefaultInflateTrace e.r (startHeap e.h₀ e.source e.out0) {} := by
  have fresh := ok.fresh
  have kk : e.k = e.h₀.nextBlk := rfl
  have globalsP : LibraryGlobals (preHeap e.h₀ e.source) := by
    simpa [LibraryGlobals, preHeap, localHeap, streamHeap] using globals
  have domain : InitDomain (preHeap e.h₀ e.source) (.tab e.h₀.nextBlk) (.ref (.str 57) 0) :=
    ⟨preHeap_fresh fresh _, preHeap_uniq fresh uniq _, globalsP, version_value _, preStream e.h₀ e.source,
      preHeap_stream e.h₀ e.source, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  have run : C.run (Zlib.Inflate.inflateInit_ (some (.tab e.h₀.nextBlk)) (.ref (.str 57) 0) 112)
      (preHeap e.h₀ e.source) = .ok (Z_OK, initHeap e.h₀ e.source) := init_ok_run fresh e.source alloc
  have initial := ZlibF.Spec.Public.Proofs.InflateInit.init15_initial (preHeap_fresh fresh e.source)
    (preHeap_uniq fresh uniq e.source) (preHeap_stream e.h₀ e.source) alloc (Or.inl rfl) (Or.inl rfl) (by simp)
    (version_byte _)
  obtain ⟨zI, sI, goodI, -, -, -, winI, -, -, -, -, -, -, -, -, -, -, -, -, -, -, frameI, -⟩ := initial
  have toInit : initOkHeap (preHeap e.h₀ e.source) (.tab e.h₀.nextBlk) (preStream e.h₀ e.source) 5 15 =
      initHeap e.h₀ e.source := rfl
  rw [toInit] at goodI frameI
  have nb : (preHeap e.h₀ e.source).nextBlk = e.h₀.nextBlk + 2 := rfl
  rw [nb] at goodI
  have zIeq : zI = initStreamRec e.h₀ e.source :=
    Option.some.inj (goodI.live.hz.symm.trans (initHeap_stream e.h₀ e.source))
  subst zIeq
  have globalsI : LibraryGlobals (initHeap e.h₀ e.source) := by
    have := frameI.1
    simp only [LibraryGlobals] at globalsP ⊢
    rw [← this]; exact globalsP
  have ownI : ∀ b, InflateOwned (e.h₀.nextBlk + 2) sI b ↔ b = e.h₀.nextBlk + 2 := by
    intro b
    simp only [InflateOwned, winI]
    constructor
    · rintro (x | x)
      · exact x
      · cases x
    · exact Or.inl
  have rebuf := rebuffer_put (e := e) goodI globalsI (by rw [ownI, kk]; omega)
    (z₁ := boundStream e.h₀ e.source e.out0) (by simp [boundStream])
  have hzI : (initHeap e.h₀ e.source).streams e.h₀.nextBlk = some (initStreamRec e.h₀ e.source) :=
    initHeap_stream e.h₀ e.source
  have Seq : startHeap e.h₀ e.source e.out0 =
      { initHeap e.h₀ e.source with
        streams := upd (initHeap e.h₀ e.source).streams e.h₀.nextBlk (some (boundStream e.h₀ e.source e.out0)) } :=
    put_tab_eq hzI
  have getS : ∀ rr : BRef, Space.get (startHeap e.h₀ e.source e.out0) rr = Space.get (preHeap e.h₀ e.source) rr := by
    intro rr
    rw [Seq, (put_tab_get (H := initHeap e.h₀ e.source) (k := e.h₀.nextBlk) (boundStream e.h₀ e.source e.out0) rr).1]
    exact (initHeap_get e.h₀ e.source rr).1
  have fitS : ZlibF.PlatformMemory.ByteObjectsFit (startHeap e.h₀ e.source e.out0) := by
    intro rr a g
    rw [getS rr] at g
    exact preHeap_fit fresh fit e.source rr a g
  have rebuf' : Rebuffer (initHeap e.h₀ e.source) (startHeap e.h₀ e.source e.out0) e.r := rebuf
  exact .caller (.init domain run) rebuf' fitS

end Uncompress

end ZlibF.Spec.Public.Proofs.RoundTrip

/-! ## The run of `uncompress2_z` on a complete stream -/

namespace ZlibF.Spec.Public.Proofs.Uncompress
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Gzguts Zlib.Inflate.Proofs Zlib.Inflate.Spec Zlib.Uncompr
open Zlib.Inflate (inflate inflateEnd inflateInit_)
set_option autoImplicit false

/-- The completion relation: the safety relation, and on a complete stream without a dictionary
request with room for its decoding, `Z_OK` and exactly the decoding. -/
def CRel (src : List UInt8) (cap : Nat) (rc : Int32) (out : List UInt8) (used : Nat) : Prop :=
  SafeRel src cap rc out used ∧
    ∀ D, Zlib.Decodes [] src D → ¬ AsksDictionary src → D.length ≤ cap → rc = Z_OK ∧ out = D

/-- The accepted arguments on a heap where every allocation succeeds: the run and cleanup of the
safety proof, and on a complete stream with room for its decoding, `Z_OK` and the decoding. -/
theorem accepted_run_complete {h : Heap} {dest destLen source sourceLen : BPtr}
    {capacity n : UInt64} {src : List UInt8}
    (noFail : NoAllocationFailure h) (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (fit : ZlibF.PlatformMemory.ByteObjectsFit h)
    (dcell : LengthCell h destLen capacity) (scell : LengthCell h sourceLen n)
    (srcB : Bytes h source n.toNat src) (destW : dest ≠ .null → Writable h dest capacity.toNat)
    (sep : UtilitySeparation dest capacity.toNat source n.toNat destLen sourceLen)
    (sl : sourceLen ≠ .null) (dl : destLen ≠ .null) (sN : source = .null → n = 0)
    (dN : dest = .null → capacity = 0) :
    ∃ rc after, C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after) ∧
      ∃ out used got consumed h₁ h₂ expected,
        StorePrefix h dest out capacity.toNat h₁ ∧ Store h₁ sourceLen (lengthBytes consumed) h₂ ∧
        Store h₂ destLen (lengthBytes got) expected ∧ SameObjectsUpToTableShape expected after ∧
        CRel src capacity.toNat rc out used ∧
        ((got.toNat = out.length ∧ consumed.toNat = used) ∨
          (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity ∧ consumed = n)) ∧
        (rc = Z_MEM_ERROR → AllocationFailed h after) := by
  have kept := localHeap_kept fresh
  have ln : load64 sourceLen (localHeap h) = .ok (n, localHeap h) := load64_cell (kept.cell_of scell)
  have ld : load64 destLen (localHeap h) = .ok (capacity, localHeap h) := load64_cell (kept.cell_of dcell)
  have c1 : (decide (n > 0) && source == Ptr.null) = false := by
    cases hb : (decide (n > 0) && source == Ptr.null)
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact absurd (sN hb.2) ((pos_iff n).1 hb.1)
  have c2 : (decide (capacity > 0) && dest == Ptr.null) = false := by
    cases hb : (decide (capacity > 0) && dest == Ptr.null)
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact absurd (dN hb.2) ((pos_iff capacity).1 hb.1)
  unfold uncompress2_z
  simp only [C.run, bind_app, allocLocalZ_run fresh, allocLocal_run fresh,
    show (sourceLen == Ptr.null) = false from beq_false_of_ne sl, Bool.false_eq_true, ite_false, ln, c1,
    show (destLen == Ptr.null) = false from beq_false_of_ne dl, ld, c2, prepare_run, version_run]
  have selfS : Store h sourceLen (lengthBytes n) h := by
    have := store_writeOut (xs := lengthBytes n) (by rw [lengthBytes_length]; exact scell.2)
    rwa [cell_self_write scell] at this
  have selfD : Store h destLen (lengthBytes capacity) h := by
    have := store_writeOut (xs := lengthBytes capacity) (by rw [lengthBytes_length]; exact dcell.2)
    rwa [cell_self_write dcell] at this
  by_cases alloc : h.allocOk h.nalloc = true
  · -- the environment of the run
    let out0 : BPtr :=
      if (capacity == 0 && dest == Ptr.null) = true then Ptr.ref (BRef.blk (h.nextBlk + 1)) 0 else dest
    let e : Env := ⟨h, source, out0, src, n.toNat, capacity.toNat⟩
    have resCase : (capacity == 0 && dest == Ptr.null) = true → capacity = 0 ∧ dest = .null := by
      intro hb; simp only [Bool.and_eq_true, beq_iff_eq] at hb; exact hb
    have ok : EnvOK e := by
      refine ⟨fresh, srcB, bytes_length srcB, ?_, ?_, ?_, bytes_bound srcB fit, ?_⟩
      · by_cases hb : (capacity == 0 && dest == Ptr.null) = true
        · left
          obtain ⟨c0, -⟩ := resCase hb
          refine ⟨by simp only [e, out0, hb, ite_true]; rfl, by simp only [e, c0]; rfl⟩
        · right
          simp only [e, out0, hb, Bool.false_eq_true, ite_false]
          by_cases dn : dest = .null
          · have c0 := dN dn
            exfalso; apply hb; simp [c0, dn]
          · exact destW dn
      · simp only [e, out0]
        split
        · simp
        · intro dn
          rename_i hb
          apply hb; simp [dN dn, dn]
      · simp only [e, out0]
        split
        · rename_i hb
          obtain ⟨c0, -⟩ := resCase hb
          exact Or.inr (Or.inl (by simp [c0]))
        · exact separate_symm sep.1
      · simp only [e]
        by_cases dn : dest = .null
        · rw [dN dn]; decide
        · exact writable_bound (destW dn) fit
    have outSep : ∀ (q : BPtr), Separate q 8 dest capacity.toNat → Separate q 8 e.out0 e.cap := by
      intro q sq
      simp only [e, out0]
      split
      · rename_i hb
        obtain ⟨c0, -⟩ := resCase hb
        exact Or.inr (Or.inl (by simp [c0]))
      · exact sq
    have cells : Cells e sourceLen destLen n capacity :=
      ⟨scell, dcell, rfl, rfl, outSep sourceLen sep.2.2.2.1, outSep destLen sep.2.1, sep.2.2.2.2.2⟩
    -- initialization and the loop
    rw [init_ok_run fresh source alloc]
    have okEq : (Z_OK != Z_OK) = false := by decide
    simp only [okEq, Bool.false_eq_true, ite_false, bind_app, bind_run]
    obtain ⟨s0, st0⟩ := start_state ok uniq globals fit alloc n capacity rfl rfl
    generalize hres : cdoWhile _ _ _ _ = res
    obtain ⟨l', H', loopEq, Hp, logp, input, output, u, zp, z, sp, s, fin⟩ :=
      loop_result_safe inflate_public ok st0.toSafeState hres (k := h.nextBlk) rfl (by body_ok) (fun _ _ => rfl)
    -- on a complete stream the same loop ends with the decoding
    have complete : ∀ D, Zlib.Decodes [] src D → ¬ AsksDictionary src → D.length ≤ capacity.toNat →
        l'.err = Z_STREAM_END ∧ logp.output ++ output = D := by
      intro D decodes noDict room
      have F : ZlibF.Spec.Public.Proofs.RoundTrip.UFacts e D := ⟨ok, decodes, noDict, room, noFail⟩
      have going0 : ZlibF.Spec.Public.Proofs.RoundTrip.UGoing e D { err := Z_OK, len := n, left := capacity }
          (startHeap e.h₀ e.source e.out0) :=
        ⟨{}, _, _, s0, st0.toSafeState, ZlibF.Spec.Public.Proofs.RoundTrip.start_trace ok uniq globals fit alloc,
          rfl, List.nil_prefix⟩
      obtain ⟨l2, H2', loopEq2, endc, Hp2, logp2, in2, out2, u2, i2, zp2, z2, sp2, s2, fin2, written⟩ :=
        ZlibF.Spec.Public.Proofs.RoundTrip.tracked_uresult F going0 hres (k := h.nextBlk) rfl (by body_ok)
          (fun _ _ => rfl)
      obtain ⟨ls, hs⟩ := Prod.mk.inj (Except.ok.inj (loopEq2.symm.trans loopEq))
      subst ls hs
      exact ⟨endc, (ZlibF.Spec.Public.Proofs.RoundTrip.final_output_eq ok fin fin2).trans written⟩
    rw [loopEq]
    simp only []
    have hz : (ZStreamRef.tab h.nextBlk).get H' = some z := fin.good.live.hz
    obtain ⟨written, H1, H2, H3, hpref, outWLe, l1, s1, l2, s2, endRun, res1, res2, ⟨zz, hzz⟩, same, memF⟩ :=
      epilogue ok cells fin
    have endRun' : inflateEnd (some (ZStreamRef.tab h.nextBlk)) H2 = .ok (Z_OK, H3) := endRun
    simp only [ldZ, ldZStream_ok hz, l1, s1, l2, s2, endRun', pure_app]
    rw [freeB_reserved_run (k := h.nextBlk) (H := H3) res1 res2]
    simp only []
    rw [freeZStream_local_run (k := h.nextBlk) (H := reservedFreed H3 h.nextBlk) hzz]
    simp only []
    have eN : e.n = n.toNat := rfl
    have eCap : e.cap = capacity.toNat := rfl
    have eSrc : e.src = src := rfl
    have inC := fin.inCount
    have outC := fin.outCount
    have nB := ok.nBound
    have cB := ok.capBound
    have srcLen := ok.srcLen
    have preIn := fin.pre.inCount
    rw [eN] at inC nB preIn; rw [eCap] at outC cB outWLe; rw [eSrc, eN] at srcLen
    have outLe : (logp.output ++ output).length ≤ capacity.toNat := by omega
    -- the counts as natural numbers
    have zin := z.avail_in.toNat_lt
    have zout := z.avail_out.toNat_lt
    have lenNat : (l'.len + z.avail_in.toUInt64).toNat = l'.len.toNat + z.avail_in.toNat := by
      rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
      omega
    have leftNat : (l'.left + z.avail_out.toUInt64).toNat = l'.left.toNat + z.avail_out.toNat := by
      rw [UInt64.toNat_add, UInt32.toNat_toUInt64]
      omega
    have consumedNat : (n - (l'.len + z.avail_in.toUInt64)).toNat = logp.input.length + u := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, lenNat]; omega), lenNat]
      omega
    have gotNat : (capacity - (l'.left + z.avail_out.toUInt64)).toNat = (logp.output ++ output).length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, leftNat]; omega), leftNat]
      omega
    -- the stores
    have h1W : Writable h dest written.length ∨ written = [] := by
      by_cases ne : written = []
      · exact Or.inr ne
      · left
        have dn : dest ≠ .null := by
          intro dn
          have := dN dn
          rw [this] at outWLe
          exact ne (List.eq_nil_of_length_eq_zero (by simpa using outWLe))
        have := writable_sub (c := 0) (m := written.length) (destW dn) (by omega)
        rwa [advance_zero] at this
    have h1eq : writeOut h dest written = writeOut h out0 written := by
      rcases h1W with w | ne
      · simp only [out0]
        split
        · rename_i hb
          obtain ⟨c0, -⟩ := resCase hb
          rw [c0] at outWLe
          simp at outWLe
          rw [show written = [] from List.eq_nil_of_length_eq_zero (by simpa using outWLe)]
          simp [writeOut_nil]
        · rfl
      · rw [ne, writeOut_nil, writeOut_nil]
    have store1W : Store h dest written (writeOut h out0 written) := by
      rw [← h1eq]
      rcases h1W with w | ne
      · exact store_writeOut w
      · rw [ne, writeOut_nil]; exact Or.inl ⟨rfl, rfl⟩
    have store1 : StorePrefix h dest (logp.output ++ output) capacity.toNat (writeOut h out0 written) :=
      ⟨written, hpref, outWLe, store1W⟩
    have cS := cell_after_output (out := written) ok scell cells.sepS outWLe
    have cD := cell_after_output (out := written) ok dcell cells.sepD outWLe
    have store2 := store_writeOut (h := writeOut h out0 written) (p := sourceLen)
      (xs := lengthBytes (n - (l'.len + z.avail_in.toUInt64))) (by rw [lengthBytes_length]; exact cS.2)
    have cD1 := cell_writeOut_sep (xs := lengthBytes (n - (l'.len + z.avail_in.toUInt64))) cD cells.sepSD
      (by simp [lengthBytes_length]) cS.2
    have store3 := store_writeOut (h := writeOut (writeOut h out0 written) sourceLen
      (lengthBytes (n - (l'.len + z.avail_in.toUInt64)))) (p := destLen)
      (xs := lengthBytes (capacity - (l'.left + z.avail_out.toUInt64))) (by rw [lengthBytes_length]; exact cD1.2)
    -- the bounds and the code
    have unc : CRel src capacity.toNat (finalCode l'.err (l'.len + z.avail_in.toUInt64))
        (logp.output ++ output) (logp.input.length + u) := by
      refine ⟨⟨outLe, by omega, finalCode_codes fin.codes⟩, ?_⟩
      intro D decodes noDict room
      obtain ⟨endc, written⟩ := complete D decodes noDict room
      refine ⟨?_, written⟩
      rw [endc]
      rfl
    refine ⟨finalCode l'.err (l'.len + z.avail_in.toUInt64), freedHeap H3 e.k, rfl,
      logp.output ++ output, logp.input.length + u, capacity - (l'.left + z.avail_out.toUInt64),
      n - (l'.len + z.avail_in.toUInt64), _, _, _, store1, store2, store3, same, unc,
      Or.inl ⟨gotNat, consumedNat⟩, fun hm => memF (finalCode_mem hm)⟩
  · -- initialization fails
    exact absurd (noFail h.nalloc) alloc

/-- `uncompress2_z` with the completion relation, on heaps where every allocation succeeds. -/
theorem uncompress2_z_with_complete : CountedWithOn NoAllocationFailure uncompress2_z true CRel := by
  intro h dest destLen source sourceLen capacity n src noFail fresh uniq globals fit dcell scell _ srcB destW sep
  by_cases bad : sourceLen = .null ∨ destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨
      (dest = .null ∧ capacity ≠ 0)
  · refine ⟨Z_STREAM_ERROR, releasedHeap (localHeap h) h.nextBlk,
      uncompress2_z_refused fresh dcell scell bad, fun _ => ⟨rfl, released_same fresh⟩, ?_⟩
    intro sl dl sN dN
    exfalso
    rcases bad with b | b | b | b
    · exact sl b
    · exact dl b
    · exact b.2 (sN b.1)
    · exact b.2 (dN b.1)
  · have sl : sourceLen ≠ .null := fun e => bad (Or.inl e)
    have dl : destLen ≠ .null := fun e => bad (Or.inr (Or.inl e))
    have sN : source = .null → n = 0 := fun e => Classical.byContradiction fun ne =>
      bad (Or.inr (Or.inr (Or.inl ⟨e, ne⟩)))
    have dN : dest = .null → capacity = 0 := fun e => Classical.byContradiction fun ne =>
      bad (Or.inr (Or.inr (Or.inr ⟨e, ne⟩)))
    have srcB' : Bytes h source n.toNat (if source = .null then [] else src) := by
      by_cases sn : source = .null
      · rw [ite_eq_left sn, sn, sN sn]; exact Or.inl ⟨rfl, rfl, rfl⟩
      · rw [ite_eq_right sn]; exact srcB sn
    obtain ⟨rc, after, run, rest⟩ := accepted_run_complete noFail fresh uniq globals fit (dcell dl) (scell sl) srcB'
      destW sep sl dl sN dN
    exact ⟨rc, after, run, fun b => absurd b bad, fun _ _ _ _ => rest⟩


theorem crel_le (src : List UInt8) (cap : Nat) (rc : Int32) (out : List UInt8) (used : Nat)
    (r : CRel src cap rc out used) : out.length ≤ cap := r.1.1

/-- `uncompress` with the completion relation, on heaps where every allocation succeeds: its two
wrappers allocate no memory and keep the allocator. -/
theorem uncompress_with_complete : SingleWithOn NoAllocationFailure uncompress false CRel := by
  rw [singleWrap_uncompress]
  exact single_of_counted_on (fun _ _ pre => pre)
    (counted2_of_z_on (fun _ _ _ pre => pre) crel_le uncompress2_z_with_complete)

end ZlibF.Spec.Public.Proofs.Uncompress

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.Uncompress
set_option autoImplicit false

/-- **`Goal.uncompress_completes`**: `uncompress` of a complete zlib stream without a dictionary
request, with room for its decoding, on a heap where every allocation succeeds, returns `Z_OK`,
writes the decoding and stores its length. -/
theorem uncompress_completes : Goal.uncompress_completes := by
  intro h dest destLen source capacity n stream xs fresh uniq globals fit noFail cell dl sn dn srcB destW
    sep1 sep2 sep3 decodes noDict room
  obtain ⟨rc, after, run, -, good⟩ :=
    uncompress_with_complete h dest destLen source capacity n stream noFail fresh uniq globals fit
      (fun _ => cell) (fun _ => dl) (fun _ => srcB) (fun _ => destW) sep1 sep2 sep3
  obtain ⟨out, _used, got, h₁, expected, S1, S2, sm, rel, counts, _mem⟩ :=
    good dl (fun e => absurd e sn) (fun e => absurd e dn)
  rw [ite_eq_right sn] at rel
  obtain ⟨rcOk, outEq⟩ := rel.2 xs decodes noDict room
  subst outEq
  have outLe := crel_le _ _ _ _ _ rel
  have gotEq : got.toNat = out.length := by
    rcases counts with c | ⟨m, -, -, -⟩
    · exact c
    · rw [rcOk] at m
      exact absurd m (by decide)
  obtain ⟨written, hpref, wLen, S1'⟩ := S1
  have e1 := store_fun S1'
  have e2 := store_fun S2
  subst e1 e2
  have wWritten : Writable h dest written.length := by
    have := writable_sub (c := 0) (m := written.length) destW (by omega)
    rwa [advance_zero] at this
  have hPrefLen : out.length ≤ written.length := hpref.length_le
  have wOut : Writable h dest out.length := by
    have := writable_sub (c := 0) (m := out.length) destW (by omega)
    rwa [advance_zero] at this
  have wLen1 : Writable (writeOut h dest written) destLen 8 := writable_writeOut cell.2 wLen destW
  have lenBytes : (lengthBytes got).length ≤ 8 := by simp [lengthBytes]
  have sepWritten : Separate dest written.length destLen 8 := by
    have := separate_sub (c := 0) (d := 0) (n' := 8) (m' := written.length) sep2 (by omega) (by omega)
    rw [advance_zero, advance_zero] at this
    exact separate_symm this
  have bytes1 : Bytes (writeOut h dest written) dest written.length written := bytes_writeOut_self wWritten
  have bytes2 := bytes_writeOut_sep (xs := lengthBytes got) bytes1 sepWritten lenBytes wLen1
  have htake : ∀ {xs ys : List UInt8}, (xs ++ ys).take xs.length = xs := by
    intro xs ys; induction xs <;> simp [*]
  have writtenTake : written.take out.length = out := by
    obtain ⟨suf, rfl⟩ := hpref
    exact htake
  have bytes2Out : Bytes (writeOut (writeOut h dest written) destLen (lengthBytes got)) dest out.length out := by
    have bSub := bytes_sub bytes2 (show 0 + out.length ≤ written.length by omega)
    rw [advance_zero, List.drop_zero, writtenTake] at bSub
    exact bSub
  have wDest : Writable (writeOut (writeOut h dest written) destLen (lengthBytes got)) dest out.length :=
    writable_writeOut (writable_writeOut wOut (Nat.le_refl written.length) wWritten) lenBytes wLen1
  refine ⟨after, by rw [← rcOk]; exact run, bytes_of_same sm wDest bytes2Out, ?_⟩
  have gotV : got = UInt64.ofNat out.length := by rw [← gotEq, UInt64.ofNat_toNat]
  rw [← gotV]
  exact same_cell sm (cell_written wLen1 got)

/-- **`Goal.compress_uncompress_roundtrip`: `uncompress(compress(x)) = x`.** -/
theorem compress_uncompress_roundtrip : Goal.compress_uncompress_roundtrip :=
  compress_uncompress_roundtrip_of compress_completes uncompress_completes

end ZlibF.Spec.Public.Proofs.RoundTrip

#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.uncompress_completes
#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.compress_uncompress_roundtrip
