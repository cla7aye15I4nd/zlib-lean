import ZlibF.Proof.«deflate.c.base»

/-! # From the field writes of `deflateInit2_` to the initialization proof

The model implements zlib's default allocator. Its byte and word requests leave the
DeflateState table alone, including on allocation refusal. This is why the safety
proof can remember the four pointers and the size fields between requests.
-/

namespace Zlib.Deflate.Proofs
open C Zlib.Deflate

private theorem bytes_table {strm : ZStreamPtr} {n size : UInt32} {h g : Heap} {p : BPtr}
    (run : ZALLOC_bytes strm n size h = .ok (p,g)) : g.dstates = h.dstates := by
  cases strm with
  | none => simp [ZALLOC_bytes,zalloc_default,bind_app,ldZStream] at run
  | some r =>
    cases hz : r.get h with
    | none => simp [ZALLOC_bytes,zalloc_default,bind_app,ldZ_eq,hz] at run
    | some z =>
      by_cases ha : z.zalloc = .fn "zcalloc"
      · simp [ZALLOC_bytes,zalloc_default,bind_app,ldZ_eq,hz,ha,Zlib.Zutil.zcalloc,allocB] at run
        split at run <;> (try split at run) <;> simp_all <;> rw [← run.2]
      · simp [ZALLOC_bytes,zalloc_default,bind_app,ldZ_eq,hz,ha,ub] at run

private theorem words_table {strm : ZStreamPtr} {n : UInt32} {h g : Heap} {p : WPtr}
    (run : ZALLOC_words strm n h = .ok (p,g)) : g.dstates = h.dstates := by
  cases strm with
  | none => simp [ZALLOC_words,zalloc_default,bind_app,ldZStream] at run
  | some r =>
    cases hz : r.get h with
    | none => simp [ZALLOC_words,zalloc_default,bind_app,ldZ_eq,hz] at run
    | some z =>
      by_cases ha : z.zalloc = .fn "zcalloc"
      · simp [ZALLOC_words,zalloc_default,bind_app,ldZ_eq,hz,ha,allocW] at run
        split at run <;> (try split at run) <;> simp_all <;> rw [← run.2]
      · simp [ZALLOC_words,zalloc_default,bind_app,ldZ_eq,hz,ha,ub] at run

private def ScalarResult (m : M Int32) : Prop := (∃ e, m = ub e) ∨ (∃ x, m = pure x)
private theorem chk_scalar (a : Int) : ScalarResult (chk32 a) := by
  unfold chk32
  split <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩
private theorem shift_scalar (n : Int) : ScalarResult (ishl 1 n) := by
  unfold ishl
  split
  · exact chk_scalar _
  · exact Or.inl ⟨_, rfl⟩

private theorem padd_heap {h g : Heap} {p v : BPtr} {n : Nat}
    (run : padd p n h = .ok (v, g)) : g = h := by
  unfold padd Ptr.add at run
  repeat' first | split at run | (cases run <;> rfl)

/-- Snapshot form used by the existing initialization proofs. -/
def initSaved (strm : ZStreamPtr) (s : DeflateStatePtr) (level method windowBits memLevel strategy wrap : Int32) : M Int32 := do
  stDeflateState s DeflateState.zeroed
  zwr strm (fun z => { z with state := StateRef.ofDeflateState s })
  let w_bits : UInt32 := windowBits.toUInt32
  let w_size : UInt32 := (← ishl 1 w_bits.toNat).toUInt32
  let hash_bits : UInt32 := memLevel.toUInt32 + 7
  let hash_size : UInt32 := (← ishl 1 hash_bits.toNat).toUInt32
  wr s (fun d => { d with strm := strm, status := INIT_STATE, wrap := wrap, w_bits := w_bits, w_size := w_size,
                          w_mask := w_size - 1, hash_bits := hash_bits, hash_size := hash_size,
                          hash_mask := hash_size - 1,
                          hash_shift := (hash_bits + (MIN_MATCH_u - 1)) / MIN_MATCH_u })
  let window ← ZALLOC_bytes strm w_size 2
  wr s (fun d => { d with window })
  let prev ← ZALLOC_words strm w_size
  wr s (fun d => { d with prev })
  let head ← ZALLOC_words strm hash_size
  wr s (fun d => { d with head })
  let lit_bufsize : UInt32 := (← ishl 1 (← iadd memLevel 6).toInt.toNat).toUInt32
  wr s (fun d => { d with high_water := 0, lit_bufsize })
  let pending_buf ← ZALLOC_bytes strm lit_bufsize 4
  wr s (fun d => { d with pending_buf, pending_buf_size := lit_bufsize.toUInt64 * 4 })
  if window == .null || prev == .null || head == .null || pending_buf == .null then
    wr s (fun d => { d with status := FINISH_STATE })
    let m ← ERR_MSG Z_MEM_ERROR
    zwr strm (fun z => { z with msg := m })
    let _ ← deflateEnd strm
    return Z_MEM_ERROR
  let sym_buf ← padd pending_buf lit_bufsize.toNat
  wr s (fun d => { d with sym_buf, sym_end := (lit_bufsize - 1) * 3 })
  wr s (fun d => { d with level, strategy, «method» := method.toUInt32.toUInt8 })
  deflateReset strm

/-- Both forms give the same result and heap, including allocation refusals and modeled faults. -/
theorem initAllocated_eq_saved (strm : ZStreamPtr) (s : DeflateStatePtr)
    (level method wb mem strategy wrap : Int32) :
    initAllocated strm s level method wb mem strategy wrap =
      initSaved strm s level method wb mem strategy wrap := by
  funext h
  cases s with
  | none => rfl
  | some s =>
    rcases s with ⟨i⟩
    cases strm with
    | none =>
      unfold initAllocated initSaved
      simp only [bind_app, stD_eq]
      cases h.dstates i <;> rfl
    | some r =>
      unfold initAllocated initSaved
      simp only [cinline_eq, bind_app, stD_eq]
      cases hd : h.dstates i with
      | none => rfl
      | some d =>
        simp only [zwr_eq, ZStreamRef.get_setD]
        cases hz : r.get h with
        | none => rfl
        | some z =>
          simp only [wrD_eq, rdD_eq, ZStreamRef.put_dstates, setD_dstates_same]
          rcases shift_scalar (wb.toUInt32.toNat : Int) with ⟨e, hw⟩ | ⟨w, hw⟩
          · erw [hw]
            rfl
          erw [hw]
          simp only [pure_app, setD_dstates_same, setD_setD]
          rcases shift_scalar ((mem.toUInt32 + 7).toNat : Int) with ⟨e, hh⟩ | ⟨hs, hh⟩
          · erw [hh]
            rfl
          erw [hh]
          simp only [pure_app, setD_dstates_same, setD_setD, ZStreamRef.put_dstates]

          -- The allocator leaves the state record live with the sizes and pointers written so far.
          generalize ha : ZALLOC_bytes (some r) w.toUInt32 2 _ = ar
          rcases ar with e | ⟨window, h1⟩
          · rfl
          simp only [bytes_table ha, setD_dstates_same]
          generalize hb : ZALLOC_words (some r) w.toUInt32 _ = br
          rcases br with e | ⟨prev, h2⟩
          · rfl
          simp only [words_table hb, setD_dstates_same]
          generalize hc : ZALLOC_words (some r) hs.toUInt32 _ = cr
          rcases cr with e | ⟨head, h3⟩
          · rfl
          simp only [words_table hc, setD_dstates_same, setD_setD]

          have add : ScalarResult (iadd mem 6) := chk_scalar _
          rcases add with ⟨e, hk⟩ | ⟨k, hk⟩
          · erw [hk]
            rfl
          erw [hk]
          simp only [pure_app]
          rcases shift_scalar (k.toInt.toNat : Int) with ⟨e, hl⟩ | ⟨lit, hl⟩
          · erw [hl]
            rfl
          erw [hl]
          simp only [pure_app, setD_dstates_same, setD_setD]
          generalize hp : ZALLOC_bytes (some r) lit.toUInt32 4 _ = pr
          rcases pr with e | ⟨pending, h4⟩
          · rfl
          simp only [ldD_eq, bytes_table hp, setD_dstates_same, setD_setD]

          -- Both forms clean up the same allocations on refusal and reset the same record on success.
          split
          · rfl
          · simp only [bind_app, wrD_eq]
            generalize hs : padd pending lit.toUInt32.toNat _ = sr
            rcases sr with e | ⟨sym, after⟩
            · rfl
            have he := padd_heap hs
            subst after
            simp only [setD_dstates_same, setD_setD]

end Zlib.Deflate.Proofs
