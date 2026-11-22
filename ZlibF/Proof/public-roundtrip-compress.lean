import ZlibF.Proof.«public-compress-safe-mid»
import ZlibF.Proof.«public-roundtrip-inflate»
import ZlibF.Proof.«public-deflate-init-domain»

/-! # `compress` completes with `compressBound` room

`compress_z` runs `deflateInit` at the default level, then the loop of `compress2_z`: refill the
output and input buffers from the remaining lengths (each at most `UINT_MAX`), then one `deflate`
call with `Z_NO_FLUSH` while source remains and `Z_FINISH` after. Its local stream is a clean
default history (`DefaultCleanHistory`) whose accepted input is the source read so far and whose
output is the destination written so far.

Every call returns `Z_OK` or `Z_STREAM_END`: the arguments are never refused, the output room is
never empty (the destination is never full before the end), and once the stream is in
`FINISH_STATE` no input is left (`finish_entry_of_step`: a call enters `FINISH_STATE` only with
`Z_FINISH` and leaves no input). The destination is never full before the end:

* after a `Z_NO_FLUSH` call some source is unread, so the output is below the bound of what was
  read (`output_le_bound`), which is below the bound of the whole source;
* a `Z_FINISH` call that returns `Z_OK` fills its room (`finish_ok_fills`). If that was the last
  room: with a destination of at most `UINT_MAX` bytes the call is the first one, from a stream
  with no output, and it wrote less than the bound (`first_ok_output_lt`); with a larger
  destination the output is above `UINT_MAX`, where the counted ledger is strictly below the
  bound (`counted_blocks_below_default_bound_of_wide`).

The last call returns `Z_STREAM_END` and has accepted all the source (`stream_end_consumes`); the
output decodes to the source (`ended_decodes`) and does not ask for a dictionary
(`default_no_dictionary_request`).
-/

namespace ZlibF.Spec.Public.Proofs.RoundTrip
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public.Proofs.Uncompress (writeOut writeOut_same written_size written_get?)
set_option autoImplicit false

/-! ## Facts about one call of a clean history -/

/-- A call of a clean history that enters `FINISH_STATE` used `Z_FINISH` and left no input. -/
theorem finish_entry_of_step {r : ZStreamRef} {h after : Heap} {log : DataLog} {ds : Nat}
    {z z' : ZStream} {d result : DeflateState} {flush rc : Int32} {input out : List UInt8} {used : Nat}
    (history : DefaultCleanHistory r h log) (clean : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (good : Zlib.Deflate.Spec.DGood h r ds z d) (goodA : Zlib.Deflate.Spec.DGood after r ds z' result)
    (step : DataStep .deflate h after r flush rc input out used)
    (before : d.status ≠ FINISH_STATE) (entered : result.status = FINISH_STATE) :
    flush = Z_FINISH ∧ z'.avail_in = 0 := by
  obtain ⟨ds0, z0, d0, config, state, ledger⟩ := clean_size_ledger history
  obtain ⟨eds, ez, ed⟩ := ZlibF.Spec.Public.Proofs.Compress.dgood_unique state.protocol.good good
  subst eds ez ed
  have original := step
  obtain ⟨_z1, _z2, _get1, _get2, buffers, _rest⟩ := original
  have getA := goodA.live.hz
  have dA := goodA.live.hs
  rcases caller_output_storage_cases state.protocol.good buffers with null | raw | ⟨owner, oo, pointer⟩
  · exact (ledger.step_raw state clean (Or.inl null) step getA dA).2.2 before entered
  · exact (ledger.step_raw state clean (Or.inr raw) step getA dA).2.2 before entered
  · exact (ledger.step_foreign state clean pointer step getA dA).2.2 before entered

/-- The counted ledger of a clean history: at most `n + 11 + 5⌊n/16383⌋` bytes for `n` accepted. -/
theorem output_le_counted {r : ZStreamRef} {h : Heap} {log : DataLog}
    (history : DefaultCleanHistory r h log) :
    log.output.length ≤ log.input.length + 11 + 5 * (log.input.length / 16383) := by
  obtain ⟨_ds, _z, _d, _config, state, ledger⟩ := clean_size_ledger history
  exact ledger.output_le state

theorem unsaturatedBound_strict {a b : Nat} (lt : a < b) : unsaturatedBound a < unsaturatedBound b := by
  unfold unsaturatedBound
  have h1 : a / 4096 ≤ b / 4096 := Nat.div_le_div_right (Nat.le_of_lt lt)
  have h2 : a / 16384 ≤ b / 16384 := Nat.div_le_div_right (Nat.le_of_lt lt)
  have h3 : a / 33554432 ≤ b / 33554432 := Nat.div_le_div_right (Nat.le_of_lt lt)
  omega

/-- Below `2^63` the bound does not saturate. -/
theorem compressBound_of_small {n : Nat} (small : n < 2 ^ 63) :
    Api.compressBound n = unsaturatedBound n := by
  apply compressBound_eq_unsaturated
  unfold unsaturatedBound
  omega

/-! ## Heap facts -/

/-- The bytes written by `writeOut` read back. -/
theorem bytes_writeOut_self {h : Heap} {p : BPtr} {xs : List UInt8} (w : Writable h p xs.length) :
    Bytes (writeOut h p xs) p xs.length xs := by
  rcases w with ⟨p0, n0⟩ | ⟨r, i, a, rfl, g, ro, fit⟩
  · subst p0
    have : xs = [] := List.eq_nil_of_length_eq_zero n0
    subst this
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · right
    rcases writeOut_same (i := i) (xs := xs) g ro with put | ⟨e, get⟩
    · refine ⟨r, i, _, rfl, put, ?_, ?_⟩
      · rw [written_size a i xs fit]; exact fit
      · apply List.ext_getElem?
        intro j
        have key := written_get? a i xs fit (i + j)
        rw [← Array.getElem?_toList] at key
        rw [List.getElem?_take, List.getElem?_drop]
        by_cases jl : j < xs.length
        · rw [ite_eq_left jl, key, ite_eq_right (by omega), ite_eq_left (by omega)]
          simp
        · rw [ite_eq_right jl]
          exact List.getElem?_eq_none (by omega)
    · subst e
      exact ⟨r, i, a, rfl, get, by simpa using fit, by simp⟩

/-- A byte range in a writable view of `E` reads the same in a heap with the same objects. -/
theorem bytes_of_same {E F : Heap} {p : BPtr} {n : Nat} {xs : List UInt8}
    (same : SameObjectsUpToTableShape E F) (w : Writable E p n) (b : Bytes E p n xs) :
    Bytes F p n xs := by
  rcases b with null | ⟨r, i, a, rfl, g, fit, value⟩
  · exact Or.inl null
  · have ro : Space.ro E r = false := by
      rcases w with ⟨p0, _⟩ | ⟨r', i', a', pr, _, ro', _⟩
      · cases p0
      · cases pr; exact ro'
    obtain ⟨sb, -, -, -, -, sd, -, -, ss, -, -, -, -⟩ := same
    have get : Space.get F r = Space.get E r := by
      cases r with
      | blk c => exact sb c
      | str k => simp [Space.ro] at ro
      | dstate_depth c => simp [Space.get, sd c]
      | st_dist_code => simp [Space.get, ss]
      | st_length_code => simp [Space.get, ss]
    exact Or.inr ⟨r, i, a, rfl, get.trans g, fit, value⟩

theorem u32_zero {x : UInt32} (zero : x.toNat = 0) : x = 0 := UInt32.toNat_inj.mp (by rw [zero]; rfl)

theorem u64_zero {x : UInt64} (zero : x.toNat = 0) : x = 0 := UInt64.toNat_inj.mp (by rw [zero]; rfl)

/-- `Ptr.diff` from a pointer into a byte view to the pointer `L` bytes further. -/
theorem ptrDiff_advance {H : Heap} {r : BRef} {i L : Nat} {a : Array UInt8} (g : Space.get H r = some a)
    (fit : i + L ≤ a.size) (small : L < 2 ^ 63) :
    ∃ d, Ptr.diff (advance (.ref r i) L) (.ref r i) H = .ok (d, H) ∧ d.toUInt64.toNat = L := by
  refine ⟨Int64.ofInt (((i + L : Nat) : Int) - ((i : Nat) : Int)), ?_, ?_⟩
  · have b2 : i ≤ a.size := by omega
    simp only [advance, Ptr.diff]
    rw [ite_eq_left trivial]
    simp only [g]
    rw [ite_eq_left ⟨fit, b2⟩, ite_eq_left (by omega)]
  · have value : (((i + L : Nat) : Int) - ((i : Nat) : Int)) = ((L : Nat) : Int) := by omega
    rw [value, Int64.ofInt_eq_ofNat, Int64.toUInt64_ofNat', UInt64.toNat_ofNat']
    omega

/-! ## The loop of `compress2_z` with the history of its stream -/

section Loop
open ZlibF.Spec.Public.Proofs.Compress
open ZlibF.Spec.Public.Proofs.Uncompress (advance_zero refill refill_le refill_toNat)

/-- What the accepted arguments of a run with `compressBound` room give. -/
structure CFacts (e : CEnv) : Prop where
  ok : COK e
  length : e.src.length = e.n
  room : unsaturatedBound e.n ≤ e.cap
  dest : e.dest ≠ .null
  source : e.source = .null → e.n = 0

/-- The loop continues: the state of the run, the clean history of its stream, and what keeps the
next call from failing. -/
def Going (e : CEnv) (st : Loop) (H : Heap) : Prop :=
  ∃ out used z s log, CState DeflateReachMid e st H out used z s ∧
    DefaultCleanHistory e.r H log ∧ log.input = e.src.take used ∧ log.output = out ∧
    log.finished = false ∧ out.length < e.cap ∧
    (s.status = FINISH_STATE → z.avail_in = 0 ∧ st.2.2 = 0) ∧
    (e.cap ≤ 4294967295 → out = [] ∧ used = 0 ∧ z.avail_in = 0 ∧ z.avail_out = 0)

/-- The loop has ended with `Z_STREAM_END` after accepting the whole source. -/
def Ended (e : CEnv) (st : Loop) (H : Heap) : Prop :=
  st.1 = Z_STREAM_END ∧ ∃ out used z s log, CState DeflateReachMid e st H out used z s ∧
    DefaultCleanHistory e.r H log ∧ log.input = e.src.take used ∧ log.output = out ∧
    log.result = Z_STREAM_END ∧ used = e.n

theorem advance_ne_null {p : BPtr} (ne : p ≠ .null) (m : Nat) : advance p m ≠ .null := by
  cases p with
  | null => exact absurd rfl ne
  | ref r i => simp [advance]

theorem refill_zero : refill 0 = 0 := (refill_le 0).2.mpr rfl

/-- **One iteration of the tracked loop.** The call returns `Z_OK` and the loop goes on with a
smaller measure, or it returns `Z_STREAM_END` with the whole source accepted. -/
theorem tracked_step {e : CEnv} (F : CFacts e) {st : Loop} {H : Heap} {out : List UInt8} {used : Nat}
    {z : ZStream} {s : DeflateState} {log : DataLog}
    (cs : CState DeflateReachMid e st H out used z s) (history : DefaultCleanHistory e.r H log)
    (inEq : log.input = e.src.take used) (outEq : log.output = out) (unfinished : log.finished = false)
    (room : out.length < e.cap) (protocol : s.status = FINISH_STATE → z.avail_in = 0 ∧ st.2.2 = 0)
    (small : e.cap ≤ 4294967295 → out = [] ∧ used = 0 ∧ z.avail_in = 0 ∧ z.avail_out = 0) :
    ∃ rc H', (do let x ← Zlib.Deflate.deflate (some e.r) (cflush z st); pure (x, crest z st) : M Loop)
        (e.r.put H (crefilled z st)) = .ok ((rc, crest z st), H') ∧
      (rc = Z_OK → Going e (rc, crest z st) H' ∧ cmeasure e (rc, crest z st) H' < cmeasure e st H) ∧
      (rc ≠ Z_OK → Ended e (rc, crest z st) H') := by
  obtain ⟨rc, H', run, _kept, lt, codes, H1, o, u, z', s', rb, hz1, good1, buffers, active, run', inSnap,
      acc, written, kept⟩ :=
    ZlibF.Spec.Public.Proofs.Compress.step compressReach_mid goalDeflate_mid loopFacts_mid F.ok cs
  have reach1 : DeflateReachMid H1 e.r := .rebuffer cs.reach rb
  obtain ⟨rcC, afterC, _zC, _sC, _uC, _oC, runC, -, -, -, -, -, -, refuseIff, -, endFacts, -, -, bufIff, -,
      -, -, -, -, -, -, -⟩ :=
    goalDeflate_mid H1 e.r (e.k + 1) (crefilled z st) s (cflush z st) reach1 good1 buffers active
  have rcEq : rcC = rc := (Prod.mk.inj (Except.ok.inj (runC.symm.trans run'))).1
  have inC := cs.inCount
  have outC := cs.outCount
  have cin := crest_in z st
  have cout := crest_out z st
  have accIn := acc.2.2.1
  have accOut := acc.2.2.2.1
  have usedLe := acc.1
  have flushCases : (cflush z st = Z_FINISH ∧ (crest z st).2 = 0) ∨
      (cflush z st = Z_NO_FLUSH ∧ (crest z st).2 ≠ 0) := by
    unfold cflush
    by_cases zero : (crest z st).2 = 0
    · exact Or.inl ⟨by rw [ite_eq_left zero], zero⟩
    · exact Or.inr ⟨by rw [ite_eq_right zero], zero⟩
  have clean : cflush z st = Z_NO_FLUSH ∨ cflush z st = Z_FINISH := by
    rcases flushCases with ⟨f, _⟩ | ⟨f, _⟩
    · exact Or.inr f
    · exact Or.inl f
  have finishedEmpty : s.status = FINISH_STATE → (crefilled z st).avail_in = 0 ∧ (crest z st).2 = 0 := by
    intro fin
    obtain ⟨zin, rest⟩ := protocol fin
    have a : (crefilled z st).avail_in = 0 := by simp [crefilled, zin, rest, refill_zero]
    refine ⟨a, u64_zero ?_⟩
    have aN : (crefilled z st).avail_in.toNat = 0 := by rw [a]; rfl
    have zinN : z.avail_in.toNat = 0 := by rw [zin]; rfl
    have restN : st.2.2.toNat = 0 := by rw [rest]; rfl
    omega
  have outPtr : (crefilled z st).next_out ≠ .null := by
    show z.next_out ≠ .null
    rw [cs.nextOut]
    exact advance_ne_null F.dest _
  have inPtr : (crefilled z st).avail_in ≠ 0 → (crefilled z st).next_in ≠ .null := by
    intro nonzero
    show z.next_in ≠ .null
    rw [cs.nextIn]
    by_cases sn : e.source = .null
    · exfalso
      have n0 := F.source sn
      apply nonzero
      have zin : z.avail_in = 0 := u32_zero (by omega)
      have rest : st.2.2 = 0 := u64_zero (by omega)
      simp [crefilled, zin, rest, refill_zero]
    · exact advance_ne_null sn _
  have notRef : ¬ DeflateRefuses (crefilled z st) s (cflush z st) := by
    rintro (bad | bad | bad | ⟨n0, nz⟩ | ⟨fin, notF⟩)
    · rcases clean with f | f <;> rw [f] at bad <;> exact absurd bad (by decide)
    · rcases clean with f | f <;> rw [f] at bad <;> exact absurd bad (by decide)
    · exact outPtr bad
    · exact inPtr nz n0
    · apply notF
      rcases flushCases with ⟨f, _⟩ | ⟨_, nz⟩
      · exact f
      · exact absurd (finishedEmpty fin).2 nz
  have roomOut1 : (crefilled z st).avail_out ≠ 0 := by
    intro zero
    by_cases zo : z.avail_out = 0
    · have refilled : (crefilled z st).avail_out = refill st.2.1 := by simp [crefilled, zo]
      rw [refilled] at zero
      have rest0 : st.2.1 = 0 := (refill_le st.2.1).2.mp zero
      have restN : st.2.1.toNat = 0 := by rw [rest0]; rfl
      have zoN : z.avail_out.toNat = 0 := by rw [zo]; rfl
      omega
    · have same : (crefilled z st).avail_out = z.avail_out := by simp [crefilled, zo]
      exact zo (same ▸ zero)
  have notInFinish : ¬ (s.status = FINISH_STATE ∧ (crefilled z st).avail_in ≠ 0) :=
    fun ⟨fin, nz⟩ => nz (finishedEmpty fin).1
  have notStream : rc ≠ Z_STREAM_ERROR := fun bad => notRef (refuseIff.1 (rcEq.trans bad))
  have notBuf : rc ≠ Z_BUF_ERROR := by
    intro bad
    obtain ⟨zin, _, notF, _⟩ := (bufIff notRef roomOut1 notInFinish).1 (rcEq.trans bad)
    rcases flushCases with ⟨f, _⟩ | ⟨f, _⟩
    · exact notF f
    · exact noflush_input f zin
  have outcome : rc = Z_OK ∨ rc = Z_STREAM_END := by
    rcases codes with c | c | c | c
    · exact Or.inl c
    · exact Or.inr c
    · exact absurd c notStream
    · exact absurd c notBuf
  have observed : DataStep .deflate H1 H' e.r (cflush z st) rc
      ((e.src.drop used).take (crefilled z st).avail_in.toNat) o u := by
    refine ⟨crefilled z st, z', hz1, kept.good.live.hz, buffers, active, inSnap, by omega, ?_, run'⟩
    have diff : (crefilled z st).avail_out.toNat - z'.avail_out.toNat = o.length := by omega
    rw [diff]
    exact written
  have history1 : DefaultCleanHistory e.r H1 log := .caller history rb
  have history' := DefaultCleanHistory.step history1 clean observed
  have taken : ((e.src.drop used).take (crefilled z st).avail_in.toNat).take u = (e.src.drop used).take u := by
    rw [List.take_take, Nat.min_eq_left usedLe]
  have accepted : log.input ++ ((e.src.drop used).take (crefilled z st).avail_in.toNat).take u =
      e.src.take (used + u) := by
    rw [taken, inEq, List.take_add]
  have growIn : used + u ≤ e.n := by omega
  have inputLen : (e.src.take (used + u)).length = used + u := by
    rw [List.length_take, F.length]
    omega
  refine ⟨rc, H', run, ?_, ?_⟩
  · intro okRc
    subst okRc
    have logIn : (deflateLogStep log (cflush z st) Z_OK
        ((e.src.drop used).take (crefilled z st).avail_in.toNat) o u).input = e.src.take (used + u) := accepted
    have logOut : (deflateLogStep log (cflush z st) Z_OK
        ((e.src.drop used).take (crefilled z st).avail_in.toNat) o u).output = out ++ o := by
      show log.output ++ o = out ++ o
      rw [outEq]
    have boundN := F.room
    have finishFill : cflush z st = Z_FINISH → (out ++ o).length + (crest z st).1.toNat = e.cap := by
      intro f
      have okF := observed
      rw [f] at okF
      have fills := finish_ok_fills history1 hz1 okF
      simp only [List.length_append]
      omega
    have notFull : (out ++ o).length < e.cap := by
      rcases flushCases with ⟨f, _⟩ | ⟨f, nz⟩
      · have fill := finishFill f
        by_cases left : (crest z st).1.toNat = 0
        · exfalso
          have full : (out ++ o).length = e.cap := by omega
          have mono := unsaturatedBound_mono growIn
          by_cases capSmall : e.cap ≤ 4294967295
          · obtain ⟨out0, _used0, -, -⟩ := small capSmall
            have empty : log.output = [] := outEq.trans out0
            have okF := observed
            rw [f] at okF
            have strict := first_ok_output_lt history1 empty okF
            have sumLen : log.input.length +
                (((e.src.drop used).take (crefilled z st).avail_in.toNat).take u).length = used + u := by
              rw [← List.length_append, accepted, inputLen]
            rw [sumLen] at strict
            rw [out0] at full
            simp only [List.nil_append] at full
            omega
          · have counted := output_le_counted history'
            rw [logIn, logOut, inputLen] at counted
            have wide := ZlibF.Math.DeflateBound.counted_blocks_below_default_bound_of_wide (used + u) (by omega)
            unfold unsaturatedBound at mono boundN
            omega
        · omega
      · have le := output_le_bound history'
        rw [logIn, logOut, inputLen] at le
        have lt : used + u < e.n := by
          have : (crest z st).2.toNat ≠ 0 := fun zero => nz (u64_zero zero)
          omega
        have strict := unsaturatedBound_strict lt
        omega
    have protocol' : s'.status = FINISH_STATE → z'.avail_in = 0 ∧ (crest z st).2 = 0 := by
      intro fin'
      by_cases fin : s.status = FINISH_STATE
      · obtain ⟨a1, rest⟩ := finishedEmpty fin
        refine ⟨u32_zero ?_, rest⟩
        have aN : (crefilled z st).avail_in.toNat = 0 := by rw [a1]; rfl
        omega
      · obtain ⟨f, drained⟩ := finish_entry_of_step history1 clean good1 kept.good observed fin fin'
        refine ⟨drained, ?_⟩
        rcases flushCases with ⟨_, zero⟩ | ⟨g, _⟩
        · exact zero
        · rw [g] at f
          exact absurd f (by decide)
    have small' : e.cap ≤ 4294967295 →
        out ++ o = [] ∧ used + u = 0 ∧ z'.avail_in = 0 ∧ z'.avail_out = 0 := by
      intro capSmall
      exfalso
      obtain ⟨out0, used0, zin0, zout0⟩ := small capSmall
      have zinN : z.avail_in.toNat = 0 := by rw [zin0]; rfl
      have zoutN : z.avail_out.toNat = 0 := by rw [zout0]; rfl
      have outN : out.length = 0 := by rw [out0]; rfl
      have nLe : e.n ≤ e.cap := by unfold unsaturatedBound at boundN; omega
      have refIn : (refill st.2.2).toNat = min st.2.2.toNat 4294967295 := refill_toNat _
      have refOut : (refill st.2.1).toNat = min st.2.1.toNat 4294967295 := refill_toNat _
      have ai : (crefilled z st).avail_in = refill st.2.2 := by simp [crefilled, zin0]
      have ao : (crefilled z st).avail_out = refill st.2.1 := by simp [crefilled, zout0]
      rw [ai, refIn] at cin
      rw [ao, refOut] at cout
      have restIn : (crest z st).2 = 0 := u64_zero (by omega)
      have restOut : (crest z st).1.toNat = 0 := by omega
      have f : cflush z st = Z_FINISH := by
        rcases flushCases with ⟨f, _⟩ | ⟨_, nz⟩
        · exact f
        · exact absurd restIn nz
      have fill := finishFill f
      omega
    refine ⟨⟨out ++ o, used + u, z', s', deflateLogStep log (cflush z st) Z_OK
      ((e.src.drop used).take (crefilled z st).avail_in.toNat) o u, kept, history', logIn, logOut, ?_,
      notFull, protocol', small'⟩, lt rfl⟩
    show (log.finished || (Z_OK == Z_STREAM_END)) = false
    rw [unfinished]
    decide
  · intro notOk
    have ended : rc = Z_STREAM_END := outcome.resolve_left notOk
    have finishFlag : cflush z st = Z_FINISH := (endFacts (rcEq.trans ended)).1
    have restZero : (crest z st).2 = 0 := by
      rcases flushCases with ⟨_, zero⟩ | ⟨f, _⟩
      · exact zero
      · rw [f] at finishFlag
        exact absurd finishFlag (by decide)
    have consumes : u = ((e.src.drop used).take (crefilled z st).avail_in.toNat).length := by
      have endStep := observed
      rw [ended] at endStep
      exact stream_end_consumes history1 endStep
    have restN : (crest z st).2.toNat = 0 := by rw [restZero]; rfl
    have usedAll : used + u = e.n := by
      rw [consumes, List.length_take, List.length_drop, F.length]
      omega
    refine ⟨ended, out ++ o, used + u, z', s', deflateLogStep log (cflush z st) rc
      ((e.src.drop used).take (crefilled z st).avail_in.toNat) o u, kept, history', accepted, ?_, ended,
      usedAll⟩
    show log.output ++ o = out ++ o
    rw [outEq]

/-- **The tracked loop** ends with `Z_STREAM_END` and the whole source accepted. -/
theorem tracked_loop {e : CEnv} (F : CFacts e) {body : Loop → M Loop} {cond : Loop → M (Bool × Loop)}
    (hB : CBodyOK e.r body) (hC : CCondOK cond) {st : Loop} {H : Heap} (going : Going e st H) :
    ∃ st' H', cdoWhile body cond st H = .ok (st', H') ∧ Ended e st' H' := by
  have start := going
  obtain ⟨_, _, _, _, _, cs0, _⟩ := start
  refine cdoWhile_decreasing (Going e) (Ended e) (cmeasure e) ?_ going (cmeasure_bound F.ok cs0)
  rintro st H ⟨out, used, z, s, log, cs, history, inEq, outEq, unfinished, room, protocol, small⟩
  obtain ⟨rc, H', run, okCase, endCase⟩ :=
    tracked_step F cs history inEq outEq unfinished room protocol small
  have bodyEq : body st H = .ok ((rc, crest z st), H') := by
    rw [hB st H z cs.good.live.hz]
    exact run
  refine ⟨_, H', rc == Z_OK, (rc, crest z st), H', bodyEq, hC _ _, ?_, ?_⟩
  · intro c
    have rcOk : rc = Z_OK := by simpa using c
    exact okCase rcOk
  · intro c
    apply endCase
    intro rcOk
    rw [rcOk] at c
    exact absurd c (by decide)

/-- The tracked loop of the translation, found in a goal by `generalize`. -/
theorem tracked_result {e : CEnv} (F : CFacts e) {body : Loop → M Loop} {cond : Loop → M (Bool × Loop)}
    {st : Loop} {H : Heap} (going : Going e st H) {res : Except Fault (Loop × Heap)}
    (hres : cdoWhile body cond st H = res) {k : Nat} (hk : e.r = .tab k) (hB : CBodyOK (.tab k) body)
    (hC : CCondOK cond) :
    ∃ st' H', res = .ok (st', H') ∧ Ended e st' H' := by
  obtain ⟨st', H', run, done⟩ := tracked_loop F (hk ▸ hB) hC going
  exact ⟨st', H', hres.symm.trans run, done⟩

/-! ## `compress_z` -/

open Zlib.Compress Zlib.Deflate in
open ZlibF.Spec.Public.Proofs.Uncompress hiding measure in
set_option maxRecDepth 10000 in
/-- **`Goal.compress_z_completes`**: `compress_z` with `compressBound` room returns `Z_OK`, stores
the length it wrote, at most the bound, and the bytes decode to the source without asking for a
dictionary. -/
theorem compress_z_completes_core : Goal.compress_z_completes := by
  intro h dest c source n xs fresh uniq globals fit noFail srcB destW sep rej room
  have a1 : ¬ (n > 0 ∧ source = .null) := fun x => rej (Or.inr (Or.inl ⟨x.2, by
    intro e; rw [e] at x; exact absurd x.1 (by decide)⟩))
  have a2 : ¬ (c > 0 ∧ dest = .null) := fun x => rej (Or.inr (Or.inr ⟨c, rfl, x.2, by
    intro e; rw [e] at x; exact absurd x.1 (by decide)⟩))
  have harg : ((decide (n > 0) && source == .null) || (decide (c > 0) && dest == .null)) = false := by
    cases hb : ((decide (n > 0) && source == .null) || (decide (c > 0) && dest == .null))
    · rfl
    · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      rcases hb with x | x
      · exact absurd x a1
      · exact absurd x a2
  have slot : ({ h with allocOk := fun _ => true } : Heap).slotUsed h.nextBlk = false := fresh.slotUsed_next
  unfold Zlib.Compress.compress_z Zlib.Compress.compress2_z
  simp [C.run, harg, allocLocalZ, allocZStream, slot, zwr, zrd, ldZStream,
    stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, ZlibF.Spec.Public.Proofs.Compress.version_run, upd_upd]
  generalize hI : Zlib.Deflate.deflateInit_ _ _ _ _ _ = I
  have hI' : Zlib.Deflate.deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112
      (cHeap h) = I := hI
  obtain ⟨rc, after, initRun, outcome⟩ := init_cases fresh uniq globals Z_DEFAULT_COMPRESSION
  rw [initRun] at hI'
  subst hI'
  have domain : InitDomain (cHeap h) (.tab h.nextBlk) (.ref (.str 57) 0) :=
    ⟨cHeap_fresh fresh, cHeap_uniq fresh uniq, cHeap_globals globals, ZlibF.Spec.Public.Proofs.Compress.version_value (cHeap h), cStream h,
      cHeap_get h, cStream_default h, rfl⟩
  obtain ⟨_after0, okRun, -, -⟩ := ZlibF.Spec.Public.Proofs.DeflateInitDomain.deflate_domain_general (cHeap h)
    (.tab h.nextBlk) (.ref (.str 57) 0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY _
    domain rfl (fun _ _ => noFail _)
  have rcOk : rc = Z_OK := (Prod.mk.inj (Except.ok.inj (initRun.symm.trans okRun))).1
  rcases outcome with ⟨rcNe, -⟩ | ⟨-, -, p, initial⟩
  · exact absurd rcOk rcNe
  subst rcOk
  obtain ⟨z, s, good, -, zfree, -, -, -, -, -, -, -, -, -, gzhead, -, -, -, frameI, liveI, ownedI⟩ := initial
  let e : CEnv := ⟨h, dest, source, xs, n.toNat, c.toNat⟩
  have ok : COK e := ⟨fresh, globals, srcB, destW, sep, bytes_bound srcB fit, writable_bound destW fit⟩
  have roomU : unsaturatedBound n.toNat ≤ c.toNat := by
    rw [← compressBound_of_small ok.nBound]
    exact room
  have atLeast : 13 ≤ unsaturatedBound n.toNat := by unfold unsaturatedBound; omega
  have F : CFacts e := by
    refine ⟨ok, public_bytes_length srcB, roomU, ?_, ?_⟩
    · intro d0
      rcases destW with ⟨_, c0⟩ | ⟨r, i, a, pr, _⟩
      · change c.toNat = 0 at c0
        omega
      · change dest = .null at d0
        rw [pr] at d0
        cases d0
    · intro sn
      by_cases n0 : n = 0
      · show n.toNat = 0
        rw [n0]
        rfl
      · exact absurd (Or.inr (Or.inl ⟨sn, n0⟩)) rej
  have k0 : ¬ h.live h.nextBlk := fresh _ (Nat.le_refl _)
  have hzA : after.streams h.nextBlk = some z := good.live.hz
  let z0 : ZStream := { z with next_in := source, avail_in := 0, next_out := dest, avail_out := 0 }
  have globalsA : LibraryGlobals after := by
    have := frameI.1
    simp only [LibraryGlobals] at globals ⊢
    rw [← this]; exact globals
  have notOwnK : ¬ DeflateOwned (h.nextBlk + 1) s h.nextBlk := by
    intro o; have := (ownedI h.nextBlk).1 o; simp only [cHeap] at this; omega
  have rb := rebuffer_tab (z1 := z0) good globalsA notOwnK (by simp [z0])
  have initRun2 : C.run (Zlib.Deflate.deflateInit2_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION Z_DEFLATED
      MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY (.ref (.str 57) 0) 112) (cHeap h) = .ok (Z_OK, after) := initRun
  have reachI : DeflateReachMid after (.tab h.nextBlk) :=
    compressReach_mid.init (cHeap_fresh fresh) (cHeap_uniq fresh uniq) (cHeap_globals globals)
      (cHeap_get h) (cStream_default h) (ZlibF.Spec.Public.Proofs.Compress.version_value (cHeap h)) initRun2
  obtain ⟨zr, hzr, -, good0⟩ := Zlib.Deflate.Universal.rebuffer_good good rb
  have H0eq : (ZStreamRef.tab h.nextBlk).put after z0 =
      { after with streams := upd after.streams h.nextBlk (some z0) } := put_tab_eq hzA
  have ez : zr = z0 := by
    have := Zlib.Deflate.Proofs.ZStreamRef.get_put_same (r := .tab h.nextBlk) good.live.hz z0
    exact Option.some.inj (hzr.symm.trans this)
  subst ez
  have sameA : ∀ b, h.live b → SameAt h { after with streams := upd after.streams h.nextBlk (some z0) } b := by
    intro b lb
    have bk : b ≠ h.nextBlk := fun x => k0 (x ▸ lb)
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
      frameI.2.2.2.2.2 b ((cHeap_live h b).2 (Or.inl lb)) (by simp only [StreamRoot]; exact bk)
    simp only [cHeap, upd_ne _ _ _ _ bk] at t1 t2 t3 t4 t5 t6 t7 t8
    exact ⟨t1, t2, by simp [upd_ne _ _ _ _ bk, t3], t4, t5, t6, t7, t8⟩
  have borrowA : after.libcErrorBorrow = h.libcErrorBorrow := by
    have := Zlib.Deflate.BorrowProofs.stable_deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION
      (.ref (.str 57) 0) 112 (cHeap h) Z_OK after initRun
    simpa [cHeap] using this
  have cs0 : CState DeflateReachMid e (Z_OK, c, n) { after with streams := upd after.streams h.nextBlk (some z0) }
      [] 0 z0 s := by
    refine
      { reach := by rw [← H0eq]; exact compressReach_mid.rebuffer reachI rb
        good := by rw [← H0eq]; exact good0
        zfree := zfree
        gzhead := gzhead
        owned := fun b => by
          show DeflateOwned (h.nextBlk + 1) s b ↔ h.nextBlk + 1 ≤ b ∧ b < h.nextBlk + 6
          rw [show h.nextBlk + 6 = (h.nextBlk + 1) + 5 by omega]
          exact ownedI b
        inCount := by show 0 + (0 : UInt32).toNat + n.toNat = n.toNat; simp
        nextIn := by show source = advance source 0; rw [ZlibF.Spec.Public.Proofs.Uncompress.advance_zero]
        outCount := by show ([] : List UInt8).length + (0 : UInt32).toNat + c.toNat = c.toNat; simp
        nextOut := by show dest = advance dest ([] : List UInt8).length; rw [List.length_nil, ZlibF.Spec.Public.Proofs.Uncompress.advance_zero]
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
      have l1 : after.live b := by
        by_cases bk : b = h.nextBlk
        · subst bk; simp [Heap.live, hzA]
        · simpa [Heap.live, upd_ne _ _ _ _ bk] using lb
      rcases (liveI b).1 l1 with ⟨lc, -⟩ | o
      · rcases (cHeap_live h b).1 lc with x | x
        · exact Or.inl x
        · exact Or.inr (Or.inl x)
      · right; right
        have := (ownedI b).1 o
        simpa [cHeap, CEnv.k] using this
    · have := frameI.2.2.2.2.1
      simp [cHeap] at this
      exact this
  have initRunC : C.run (Zlib.Deflate.deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0)
      112) (cHeap h) = .ok (Z_OK, after) := initRun
  have history0 : DefaultCleanHistory (.tab h.nextBlk)
      { after with streams := upd after.streams h.nextBlk (some z0) } {} := by
    rw [← H0eq]
    exact .caller (.init domain initRunC) rb
  have going0 : Going e (Z_OK, c, n) { after with streams := upd after.streams h.nextBlk (some z0) } := by
    refine ⟨[], 0, z0, s, {}, cs0, history0, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show 0 < c.toNat
      omega
    · intro fin
      exact absurd fin (no_output_not_finishing history0 rfl cs0.good.live.hz (h.nextBlk + 1) s
        cs0.good.live.zst cs0.good.live.hs)
    · intro _
      exact ⟨rfl, rfl, rfl, rfl⟩
  -- the loop
  simp [ldZStream, stZStream, ZStreamRef.get, ZStreamRef.put, ZStreamRef.isRo, hzA]
  generalize hres : cdoWhile _ _ _ _ = res
  obtain ⟨st', H', loopEq, endCode, out, used, zf, sf, log, csf, historyF, inF, outF, resultF, usedF⟩ :=
    tracked_result F going0 hres (k := h.nextBlk) rfl (by cbody_ok) (fun _ _ => rfl)
  rw [loopEq]
  -- the cleanup
  obtain ⟨d, rcE, H2, diffRun, endRun, freeRun, store, same, outLe⟩ := epilogue ok csf
  have hzf : H'.streams h.nextBlk = some zf := csf.good.live.hz
  have endRun' : Zlib.Deflate.deflateEnd (some (.tab h.nextBlk)) H' = .ok (rcE, H2) := endRun
  have freeRun' : freeZStream (some (.tab h.nextBlk)) H2 =
      .ok ((), { H2 with streams := upd H2.streams h.nextBlk none }) := freeRun
  have diffRun' : Ptr.diff zf.next_out dest H' = .ok (d, H') := diffRun
  have outLe' : out.length ≤ c.toNat := outLe
  have value : d.toUInt64.toNat = out.length := by
    have wH : Writable H' dest c.toNat :=
      csf.agree.writable (writable_writeOut destW outLe destW) (caller_view_blocks (Or.inr destW))
    rcases wH with ⟨d0, _⟩ | ⟨r, i, a, pr, g, _, fitA⟩
    · exact absurd d0 F.dest
    · obtain ⟨d', run2, val⟩ := ptrDiff_advance (i := i) (L := out.length) g (by omega)
        (by have := ok.capBound; change c.toNat < 2 ^ 63 at this; omega)
      have diff2 := diffRun'
      rw [csf.nextOut] at diff2
      change Ptr.diff (advance dest out.length) dest H' = .ok (d, H') at diff2
      rw [pr] at diff2
      have dd := (Prod.mk.inj (Except.ok.inj (diff2.symm.trans run2))).1
      rw [dd]
      exact val
  have wOut : Writable h dest out.length := by
    have := writable_sub (c := 0) (m := out.length) destW (by omega)
    rwa [ZlibF.Spec.Public.Proofs.Uncompress.advance_zero] at this
  have decodes := ended_decodes historyF.toDefault resultF
  rw [outF, inF, usedF] at decodes
  have takeAll : xs.take n.toNat = xs := List.take_of_length_le (by
    have := F.length
    change xs.length = n.toNat at this
    omega)
  have noDict := default_no_dictionary_request historyF.toDefault
  rw [outF] at noDict
  have bound := output_le_bound historyF
  rw [outF, inF, usedF, List.length_take, F.length, Nat.min_self] at bound
  refine ⟨d.toUInt64, { H2 with streams := upd H2.streams h.nextBlk none }, ?_, ?_, out, value.symm, ?_, ?_,
    noDict⟩
  · simp [hzf, diffRun', endRun', freeRun', endCode]
  · rw [value, compressBound_of_small ok.nBound]
    exact bound
  · rw [value]
    exact bytes_of_same same (writable_writeOut wOut (Nat.le_refl _) wOut) (bytes_writeOut_self wOut)
  · rw [takeAll] at decodes
    exact decodes

/-- **`Goal.compress_completes`**: `compress` is `compress2` at the default level, which reads the
length cell and calls `compress2_z`. -/
theorem compress_completes : Goal.compress_completes := by
  intro h dest c source n xs fresh uniq globals fit noFail srcB destW sep rej room
  obtain ⟨stored, after, out, run, rest⟩ :=
    compress_z_completes_core h dest c source n xs fresh uniq globals fit noFail srcB destW sep rej room
  refine ⟨stored, after, out, ?_, rest⟩
  have run' : Zlib.Compress.compress2_z dest (some c) source n Z_DEFAULT_COMPRESSION h =
      .ok ((Z_OK, some stored), after) := run
  simp [C.run, Zlib.Compress.compress, Zlib.Compress.compress2, run']

/-- **`uncompress(compress(x)) = x` from its two halves**: `Goal.compress_completes` and
`Goal.uncompress_completes`. -/
theorem compress_uncompress_roundtrip_of (compressed : Goal.compress_completes)
    (uncompressed : Goal.uncompress_completes) : Goal.compress_uncompress_roundtrip := by
  intro h dest c source n xs fresh uniq globals fit noFail srcB destW sep rej room
  obtain ⟨stored, after, out, run, _le, outLen, bytes, decodes, noDict⟩ :=
    compressed h dest c source n xs fresh uniq globals fit noFail srcB destW sep rej room
  have xsLen : xs.length = n.toNat := public_bytes_length srcB
  have direct : C.run (Zlib.Compress.compress dest (some c) source n) h = .ok ((Z_OK, stored), after) := by
    simp only [C.run] at run ⊢
    rw [bind_app] at run
    cases result : Zlib.Compress.compress dest (some c) source n h with
    | error err =>
      rw [result] at run
      cases run
    | ok pair =>
      obtain ⟨⟨rc, size⟩, final⟩ := pair
      rw [result] at run
      have same : (rc = Z_OK ∧ size = stored) ∧ final = after := by simpa [pure_app] using run
      obtain ⟨⟨rcEq, sizeEq⟩, heapEq⟩ := same
      rw [rcEq, sizeEq, heapEq]
  refine ⟨stored, after, out, direct, outLen, bytes, ?_⟩
  intro h₂ dest₂ destLen₂ source₂ capacity₂ fresh₂ uniq₂ globals₂ fit₂ noFail₂ cell nnLen nnSrc nnDest
    srcB₂ destW₂ sep₂ sepLen₁ sepLen₂ enough
  obtain ⟨after₂, run₂, written, cell₂⟩ :=
    uncompressed h₂ dest₂ destLen₂ source₂ capacity₂ stored out xs fresh₂ uniq₂ globals₂ fit₂ noFail₂ cell
      nnLen nnSrc nnDest srcB₂ destW₂ sep₂ sepLen₁ sepLen₂ decodes noDict (by omega)
  refine ⟨after₂, run₂, ?_, ?_⟩
  · rw [← xsLen]
    exact written
  · rw [xsLen, UInt64.ofNat_toNat] at cell₂
    exact cell₂

end Loop

end ZlibF.Spec.Public.Proofs.RoundTrip

#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.compress_z_completes_core
#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.compress_completes
#print axioms ZlibF.Spec.Public.Proofs.RoundTrip.compress_uncompress_roundtrip_of
