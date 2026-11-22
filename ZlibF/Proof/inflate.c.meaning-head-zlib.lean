import ZlibF.Proof.«inflate.c.meaning-trip»
import ZlibF.Proof.«inflate.c.meaning-dictid»
import ZlibF.Proof.«inflate.c.meaning-fields»
import ZlibF.Proof.«inflate.c.head-default-state»
import ZlibF.Math.«inflate-meaning-wrap»

/-!
# inflate.c: `HEAD` with the zlib wrapper keeps the format meaning (`TripHeadZlib`)

`case HEAD:` with `wrap = 5` (zlib, check bit set) and no header record:

* `NEEDBITS(16)` leaves for more input: the parse stays at the empty header with fewer than 16
  held bits (`LoopMatches`).
* With 16 bits held the two header bytes `CMF`, `FLG` are known. The literal checks of the C pass
  exactly when `Zlib.HeaderOK cmf flg ∧ Api.ZlibFits configured [cmf, flg]`:
  * accepted without `FDICT`: the body starts at its first block boundary, with an empty window,
    `check = adler32 [] = 1`, `flags = 0` and the width `HeaderWidth` asks for;
  * accepted with `FDICT`: the header stage `[cmf, flg]` in `DICTID`;
  * rejected: `BAD`, and no stream of the configuration starts with these two bytes
    (`LoopDoomed`), since every such stream starts with a header that passes the checks
    (`layerDecodes_head`).

The width is general: every configured window, 0 and 8 to 15. With 0 the decoder takes the
header's width; otherwise the configured width bounds the header's.
-/

namespace Zlib.Inflate.Proofs.MeaningHeadZlib
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## The header word -/

/-- The exact unsigned checks on a two-byte zlib header imply the RFC header predicate. -/
theorem zlib_head_format {s : InflateState} {l : IL} {cmf flg : UInt8}
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat)
    (header : headHeaderRejected s l = false)
    (method : headMethodRejected l = false)
    (window : (headWindowRegs l).len.toNat ≤ 15) :
    ZlibF.Spec.Zlib.HeaderOK cmf flg := by
  have mask8 : ((1 : UInt32) <<< 8 - 1) = 255 := by decide +kernel
  have mask4 : ((1 : UInt32) <<< 4 - 1) = 15 := by decide +kernel
  have cmfBound : cmf.toNat < 256 := cmf.toNat_lt
  have flgBound : flg.toNat < 256 := flg.toNat_lt
  have low8 : (l.hold.toUInt32 &&& 255).toNat = cmf.toNat := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32]
    change (l.hold.toNat % 4294967296) &&& (2 ^ 8 - 1) = cmf.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have low4 : (l.hold.toUInt32 &&& 15).toNat = cmf.toNat % 16 := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32]
    change (l.hold.toNat % 4294967296) &&& (2 ^ 4 - 1) = cmf.toNat % 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have high8 : (l.hold >>> 8).toNat = flg.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change l.hold.toNat / 256 = flg.toNat
    omega
  have info : ((l.hold >>> (4 : UInt32).toUInt64).toUInt32 &&& 15).toNat =
      cmf.toNat / 16 := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow]
    change (l.hold.toNat / 16 % 4294967296) &&& (2 ^ 4 - 1) = cmf.toNat / 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have shifted : ((l.hold.toUInt32 &&& 255) <<< 8).toUInt64.toNat = cmf.toNat * 256 := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_shiftLeft, low8, Nat.shiftLeft_eq]
    change cmf.toNat * 256 % 4294967296 = cmf.toNat * 256
    omega
  have check :
      (((l.hold.toUInt32 &&& 255) <<< 8).toUInt64 + (l.hold >>> 8)) % 31 = 0 := by
    simp only [headHeaderRejected, mask8, Bool.or_eq_false_iff] at header
    simpa using header.2
  have checkNat := congrArg UInt64.toNat check
  rw [UInt64.toNat_mod, UInt64.toNat_add, shifted, high8] at checkNat
  have m : (l.hold.toUInt32 &&& 15) = i2u Z_DEFLATED := by
    simp only [headMethodRejected, mask4] at method
    simpa using method
  have mNat := congrArg UInt32.toNat m
  rw [low4] at mNat
  have width : (headWindowRegs l).len.toNat =
      (cmf.toNat / 16 + 8) % 4294967296 := by
    simp only [headWindowRegs, mask4, UInt32.toNat_add, info]
    rfl
  rw [width] at window
  refine ⟨?_, ?_, ?_⟩
  · change cmf.toNat % 16 = 8 at mNat
    exact mNat
  · omega
  · change (cmf.toNat * 256 + flg.toNat) % 31 = 0
    change ((cmf.toNat * 256 + flg.toNat) % 18446744073709551616) % 31 = 0 at checkNat
    have bound : cmf.toNat * 256 + flg.toNat < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt bound] at checkNat
    exact checkNat

/-- The header width field is the `CINFO` nibble plus eight. -/
theorem zlib_head_window_length {l : IL} {cmf flg : UInt8}
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat) :
    (headWindowRegs l).len.toNat = cmf.toNat / 16 + 8 := by
  have cmfBound : cmf.toNat < 256 := cmf.toNat_lt
  have flgBound : flg.toNat < 256 := flg.toNat_lt
  have mask4 : ((1 : UInt32) <<< 4 - 1) = 15 := by decide +kernel
  have info : ((l.hold >>> (4 : UInt32).toUInt64).toUInt32 &&& 15).toNat =
      cmf.toNat / 16 := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow]
    change (l.hold.toNat / 16 % 4294967296) &&& (2 ^ 4 - 1) = cmf.toNat / 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [headWindowRegs, mask4, UInt32.toNat_add, info]
  change (cmf.toNat / 16 + 8) % 4294967296 = cmf.toNat / 16 + 8
  omega

/-- A header that satisfies the RFC predicate passes the first two literal checks of the C and
announces a width of at most 15. -/
theorem zlib_head_checks_pass {s : InflateState} {l : IL} {cmf flg : UInt8}
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat) (wrap : s.wrap = 5)
    (ok : ZlibF.Spec.Zlib.HeaderOK cmf flg) :
    headHeaderRejected s l = false ∧ headMethodRejected l = false ∧
      (headWindowRegs l).len.toNat ≤ 15 := by
  have mask8 : ((1 : UInt32) <<< 8 - 1) = 255 := by decide +kernel
  have mask4 : ((1 : UInt32) <<< 4 - 1) = 15 := by decide +kernel
  have cmfBound : cmf.toNat < 256 := cmf.toNat_lt
  have flgBound : flg.toNat < 256 := flg.toNat_lt
  have low8 : (l.hold.toUInt32 &&& 255).toNat = cmf.toNat := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32]
    change (l.hold.toNat % 4294967296) &&& (2 ^ 8 - 1) = cmf.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have low4 : (l.hold.toUInt32 &&& 15).toNat = cmf.toNat % 16 := by
    rw [UInt32.toNat_and, UInt64.toNat_toUInt32]
    change (l.hold.toNat % 4294967296) &&& (2 ^ 4 - 1) = cmf.toNat % 16
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have high8 : (l.hold >>> 8).toNat = flg.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change l.hold.toNat / 256 = flg.toNat
    omega
  have shifted : ((l.hold.toUInt32 &&& 255) <<< 8).toUInt64.toNat = cmf.toNat * 256 := by
    rw [UInt32.toNat_toUInt64, UInt32.toNat_shiftLeft, low8, Nat.shiftLeft_eq]
    change cmf.toNat * 256 % 4294967296 = cmf.toNat * 256
    omega
  have word : (((l.hold.toUInt32 &&& 255) <<< 8).toUInt64 + (l.hold >>> 8)).toNat =
      cmf.toNat * 256 + flg.toNat := by
    rw [UInt64.toNat_add, shifted, high8]
    change (cmf.toNat * 256 + flg.toNat) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have modZero : (((l.hold.toUInt32 &&& 255) <<< 8).toUInt64 + (l.hold >>> 8)) % 31 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, word]
    change (cmf.toNat * 256 + flg.toNat) % 31 = 0
    exact ok.2.2
  have method : (l.hold.toUInt32 &&& 15) = i2u Z_DEFLATED := by
    apply UInt32.toNat_inj.mp
    rw [low4]
    change cmf.toNat % 16 = 8
    exact ok.1
  refine ⟨?_, ?_, ?_⟩
  · unfold headHeaderRejected
    rw [mask8, modZero, wrap] <;> decide
  · unfold headMethodRejected
    rw [mask4, method] <;> simp
  · rw [zlib_head_window_length wire]
    have := ok.2.1
    omega

theorem zlib_head_mask512 (n : Nat) :
    n &&& 512 = 0 ↔ n / 512 % 2 = 0 := by
  have bit : n &&& 512 = 0 ↔ n.testBit 9 = false := by
    constructor
    · intro zero
      have eq := congrArg (fun x : Nat => x.testBit 9) zero
      simp only [Nat.testBit_and, show (512 : Nat) = 2 ^ 9 from rfl,
        Nat.testBit_two_pow, decide_true, Bool.and_true] at eq
      exact eq
    · intro zero
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, show (512 : Nat) = 2 ^ 9 from rfl, Nat.testBit_two_pow]
      by_cases index : i = 9
      · subst i
        simp [zero]
      · simp [Ne.symm index]
  rw [bit, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]
  omega

/-- `DROPBITS(4)` and the test `hold & 0x200` select the `FDICT` bit of `FLG`. -/
theorem zlib_head_mode {l : IL} {cmf flg : UInt8}
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat) :
    headDefaultMode l = if flg.toNat / 32 % 2 = 0 then TYPE else DICTID := by
  have cmfBound : cmf.toNat < 256 := cmf.toNat_lt
  have zero : ((headWindowRegs l).hold &&& 512) = 0 ↔ flg.toNat / 32 % 2 = 0 := by
    rw [← UInt64.toNat_inj]
    simp only [headWindowRegs, UInt64.toNat_and]
    change (l.hold >>> (4 : UInt32).toUInt64).toNat &&& 512 = 0 ↔ _
    rw [zlib_head_mask512, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    change l.hold.toNat / 16 / 512 % 2 = 0 ↔ _
    have quotient : l.hold.toNat / 16 / 512 = flg.toNat / 32 := by omega
    rw [quotient]
  by_cases flag : flg.toNat / 32 % 2 = 0
  · simp [headDefaultMode, zero.mpr flag, flag]
  · have nonzero : ((headWindowRegs l).hold &&& 512) ≠ 0 := fun h => flag (zero.mp h)
    simp [headDefaultMode, nonzero, flag]

/-- A zlib header is not the gzip magic. -/
theorem zlib_head_not_gzip {cmf flg : UInt8} (ok : ZlibF.Spec.Zlib.HeaderOK cmf flg) :
    ¬ IsGzipHeader [cmf, flg] := by
  intro magic
  have first : cmf = 31 := by
    have projected := congrArg (fun bytes : List UInt8 => bytes.headD 0) magic
    simpa using projected
  have method := ok.1
  rw [first] at method
  exact (by decide : ¬ ((31 : UInt8).toNat % 16 = 8)) method

/-- A configured nonzero width bounds the header's width. -/
theorem zlib_fits_le {configured : Nat} {cmf flg : UInt8}
    (fits : ZlibF.Spec.Api.ZlibFits configured [cmf, flg]) (nonzero : configured ≠ 0) :
    cmf.toNat / 16 + 8 ≤ configured := by
  rcases fits with zero | ⟨c', head, le⟩
  · exact absurd zero nonzero
  · simp only [List.head?_cons, Option.some.injEq] at head
    subst head
    exact le

/-! ## The accepted state -/

/-- The width after an accepted header, for every configured width. -/
theorem zlib_head_width {s : InflateState} {l : IL} {configured : Nat} {cmf flg : UInt8}
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat) (ok : ZlibF.Spec.Zlib.HeaderOK cmf flg)
    (window : HeadWindow s) (width0 : configured = 0 → s.wbits = 0) :
    HeaderWidth (headDefaultState s l) configured [cmf, flg] := by
  have lenEq := zlib_head_window_length (l := l) wire
  have cinfo := ok.2.1
  by_cases z0 : s.wbits = 0
  · have w : (headDefaultState s l).wbits = (headWindowRegs l).len := by
      show headWidth s l = _
      unfold headWidth
      rw [ite_eq_left z0]
    refine ⟨by rw [w]; omega, by rw [w]; omega,
      fun _ => ⟨fun g => absurd g (zlib_head_not_gzip ok), fun _ => ?_⟩⟩
    show 2 ^ (headDefaultState s l).wbits.toNat = 2 ^ (cmf.toNat / 16 + 8)
    rw [w, lenEq]
  · have w : (headDefaultState s l).wbits = s.wbits := by
      show headWidth s l = _
      unfold headWidth
      rw [ite_eq_right z0]
    have range := window.resolve_right (fun e => z0 e.1)
    exact ⟨by rw [w]; exact range.1, by rw [w]; exact range.2, fun cz => absurd (width0 cz) z0⟩

/-- An accepted header keeps the configuration of the trace. -/
theorem zlib_head_config {s : InflateState} {l l2 : IL} {wrap : Api.Wrap} {configured : Nat}
    (config : ConfigMatches (loopState s l) wrap configured) :
    ConfigMatches (loopState (headDefaultState s l) l2) wrap configured := by
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  refine ⟨c1, c2, c3, c4, fun nz => ?_, ?_⟩
  · have w : s.wbits.toNat = configured := c5 nz
    have sNZ : s.wbits ≠ 0 := by
      intro e
      rw [e] at w
      exact nz (w.symm.trans rfl)
    show (headWidth s l).toNat = configured
    unfold headWidth
    rw [ite_eq_right sNZ]
    exact w
  · show headDefaultMode l ≠ SYNC
    unfold headDefaultMode
    split <;> decide

/-! ## The loop facts at `HEAD` -/

/-- In `HEAD` the loop holds whole bytes, at most two, and no output. -/
theorem zlib_head_loop_entry {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    (loop : LoopMatches c f h l)
    (head : ∀ zs state, c.st = some (.tab zs) → h.istates zs = some state → state.mode = HEAD) :
    l.bits.toNat % 8 = 0 ∧ l.bits.toNat ≤ 16 ∧ f.logOut = [] ∧ loopPending l = 0 ∧
      l.put = f.start := by
  obtain ⟨zs, state, callOut, consumed, held, stage, tag, get, _ret, _config,
    _have, _inputLength, _buffer, _left, pending, cursor, _bytes, _writable,
    _sepInput, _sepWindow, _sepOutput, inputBits, heldBits, parsed,
    stageMatch, wrapper, outputEq⟩ := loop
  have mode : state.mode = HEAD := head zs state tag get
  have high : (loopState state l).mode ≤ DICTID := by
    change state.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨header, stageEq⟩ := MeaningDictid.stage_of_header stageMatch high
  subst stage
  have headerFacts := wrapper.1.2.1 mode
  have emptyHeader : header = [] := headerFacts.1
  subst header
  have consumedEmpty : consumed = [] := by simpa [ZlibF.Spec.bytesToBits] using parsed.1
  have lengths := congrArg List.length inputBits
  rw [consumedEmpty] at lengths
  simp only [List.nil_append, bytesToBits_length'] at lengths
  have heldLength : held.length = l.bits.toNat := heldBits.1
  have aligned : l.bits.toNat % 8 = 0 := by omega
  have bound : l.bits.toNat ≤ 16 := headerFacts.2.1
  have emptyOutput : f.logOut ++ callOut = [] := outputEq.symm
  obtain ⟨logEmpty, callEmpty⟩ := List.append_eq_nil_iff.mp emptyOutput
  have pendingBound := pending.1
  have pendingEmpty : loopPending l = 0 := by rw [callEmpty] at pendingBound; simpa using pendingBound
  have sameCursor : l.put = f.start := by
    rw [callEmpty, List.length_nil, inputAdvance_zero] at cursor
    exact cursor
  exact ⟨aligned, bound, logEmpty, pendingEmpty, sameCursor⟩

/-- The configuration facts `HEAD` reads: the zlib wrapper code, no header record, and the
width (0 when the header chooses it, else the configured one). -/
theorem zlib_head_entry {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat}
    {s : InflateState} (loop : LoopMatches c f h l) (st : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (mode : s.mode = HEAD) (zlib : f.wrap = .zlib) :
    s.wrap = 5 ∧ s.head = none ∧ (f.configured = 0 → s.wbits = 0) ∧
      (f.configured ≠ 0 → s.wbits.toNat = f.configured) := by
  obtain ⟨zs1, s1, _, _, _, stage, st1, hs1, _, config, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    stageM, wrapM, _⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have high : (loopState s l).mode ≤ DICTID := by
    show s.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM high
  have width0 := (wrapM.1.2.1 mode).2.2
  have wrapEq : s.wrap = wrapCode f.wrap := config.1
  rw [zlib] at wrapEq
  exact ⟨wrapEq, config.2.2.1, width0, config.2.2.2.2.1⟩

/-- The two bytes of a complete header pull are the input read so far, and `hold` holds them. -/
theorem zlib_head_word {s : InflateState} {l : IL} {source : List UInt8} {held : List Bool}
    (sourceBits : ZlibF.Spec.bytesToBits source = held)
    (buffer : HeldBits (loopState s l) held)
    (full : 16 ≤ l.bits.toNat) (bound : l.bits.toNat ≤ 23) :
    ∃ cmf flg, source = [cmf, flg] ∧ l.bits.toNat = 16 ∧
      l.hold.toNat = cmf.toNat + 256 * flg.toNat := by
  have sourceLength := congrArg List.length sourceBits
  rw [bytesToBits_length'] at sourceLength
  have heldLength : held.length = l.bits.toNat := buffer.1
  have two : source.length = 2 := by omega
  have sixteen : l.bits.toNat = 16 := by omega
  obtain ⟨cmf, flg, sourceEq⟩ : ∃ cmf flg, source = [cmf, flg] := by
    cases source with
    | nil => simp at two
    | cons cmf tail =>
      cases tail with
      | nil => simp at two
      | cons flg rest =>
        have empty : rest = [] := by simpa using two
        subst rest
        exact ⟨cmf, flg, rfl⟩
  refine ⟨cmf, flg, sourceEq, sixteen, ?_⟩
  have value : l.hold.toNat = MeaningBits.heldValue held := buffer.2
  rw [← sourceBits, MeaningFields.heldValue_bytesToBits, sourceEq] at value
  simpa [MeaningFields.leValue] using value

/-- At 16 held bits in `HEAD` the input read so far is the two header bytes. -/
theorem zlib_head_observation {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL}
    (loop : LoopMatches c f h l)
    (head : ∀ zs state, c.st = some (.tab zs) → h.istates zs = some state → state.mode = HEAD)
    (full : 16 ≤ l.bits.toNat) :
    ∃ cmf flg, f.logIn ++ f.inp.take (loopRead l) = [cmf, flg] ∧
      l.hold.toNat = cmf.toNat + 256 * flg.toNat ∧ l.bits.toNat = 16 ∧ f.logOut = [] := by
  have entry := zlib_head_loop_entry loop head
  obtain ⟨zs, state, _callOut, consumed, held, stage, tag, get, _ret, _config,
    _have, _inputLength, _buffer, _left, _pending, _cursor, _bytes, _writable,
    _sepInput, _sepWindow, _sepOutput, inputBits, heldBits, parsed,
    stageMatch, wrapper, _outputEq⟩ := loop
  have mode : state.mode = HEAD := head zs state tag get
  have high : (loopState state l).mode ≤ DICTID := by
    change state.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨header, stageEq⟩ := MeaningDictid.stage_of_header stageMatch high
  subst stage
  have empty : header = [] := (wrapper.1.2.1 mode).1
  subst header
  have consumedEmpty : consumed = [] := by simpa [ZlibF.Spec.bytesToBits] using parsed.1
  rw [consumedEmpty, List.nil_append] at inputBits
  have bound : l.bits.toNat ≤ 23 := by have := entry.2.1; omega
  obtain ⟨cmf, flg, sourceEq, bits, value⟩ := zlib_head_word inputBits heldBits full bound
  exact ⟨cmf, flg, sourceEq, value, bits, entry.2.2.1⟩

/-- A wrapped `HEAD` stage holds any bit buffer of at most 16 bits. -/
theorem zlib_head_bits {h : Heap} {s : InflateState} {f : LoopFrame} {checked bytes : List UInt8}
    (stage : LoopStageMatches h s f checked (.header bytes))
    (wrapper : WrapMatches h s f.wrap f.configured f.dict (.header bytes))
    (mode : s.mode = HEAD) (wrapped : f.wrap ≠ .raw)
    (hold : UInt64) (bits : UInt32) (small : bits.toNat ≤ 16) :
    LoopStageMatches h { s with hold := hold, bits := bits } f checked (.header bytes) ∧
    WrapMatches h { s with hold := hold, bits := bits } f.wrap f.configured f.dict (.header bytes) := by
  obtain ⟨⟨rawHead, header, _dictid, _flags, _gzip, wrappedC, last0, total0, _rawBits⟩,
    window, used⟩ := wrapper
  obtain ⟨empty, _oldBound, width⟩ := header mode
  refine ⟨stage, ⟨rawHead, fun _ => ⟨empty, small, width⟩,
    fun m => absurd (mode.symm.trans m) (by decide),
    fun m => absurd (mode.symm.trans m) (by decide),
    fun low _high => ?_, wrappedC, last0, total0,
    fun raw => False.elim (wrapped raw)⟩, window, used⟩
  have low' : TIME ≤ s.mode := low
  rw [mode] at low'
  exact absurd low' (by decide)

/-! ## The run of `case HEAD:` -/

/-- With the zlib wrapper and 16 bits pulled, `case HEAD:` is the literal header check. -/
theorem zlib_head_run_ok {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l l' : IL} (E : Env c h r zs z s) (wrap : s.wrap = 5)
    (head : s.head = none) (needRun : runX (NEEDBITS 16) l h = .ok ((.ok (), l'), h)) :
    runX (inflate_HEAD c) l h = runX (headDefaultCheck c s l') l' h := by
  have nowrap : (s.wrap == 0) = false := by rw [wrap] <;> rfl
  have nogzip : ((s.wrap &&& 2) != 0) = false := by rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, needRun]
  simp only []
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_ldS E]
  simp only [nogzip, bne_self_eq_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, head]
  unfold headDefaultCheck
  simp only

/-- With the zlib wrapper, `case HEAD:` leaves when `NEEDBITS(16)` runs out of input. -/
theorem zlib_head_run_leave {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {l l' : IL} (E : Env c h r zs z s) (wrap : s.wrap = 5)
    (needRun : runX (NEEDBITS 16) l h = .ok ((.error Ex.leave, l'), h)) :
    runX (inflate_HEAD c) l h = .ok ((.error Ex.leave, l'), h) := by
  have nowrap : (s.wrap == 0) = false := by rw [wrap] <;> rfl
  unfold inflate_HEAD
  rw [runX_bind, runX_rdS E]
  simp only [nowrap, Bool.false_eq_true, ↓reduceIte]
  rw [runX_bind, needRun]

/-! ## The three ends -/

/-- Two header bytes that fail the RFC predicate or the configured width start no stream of the
configuration. -/
theorem zlib_head_doomed {f : LoopFrame} {l : IL} {cmf flg : UInt8} (zlib : f.wrap = .zlib)
    (input : f.logIn ++ f.inp.take (loopRead l) = [cmf, flg])
    (invalid : ¬ (ZlibF.Spec.Zlib.HeaderOK cmf flg ∧ ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg])) :
    LoopDoomed f l := by
  intro source decoded valid _ pre
  rw [input] at pre
  rcases layerDecodes_head valid pre (by rw [zlib]; decide) with ⟨gzipLike, _⟩ | ⟨_, okFits⟩
  · rw [zlib] at gzipLike
    rcases gzipLike with g | g <;> cases g
  · exact invalid okFits

/-- A rejected header: `BAD`, with the configuration kept and the input read so far doomed. -/
theorem zlib_head_bad {c : Ctx} {f : LoopFrame} {h : Heap} {l regs : IL} {r : ZStreamRef}
    {z : ZStream} {zs : Nat} {s : InflateState} {i : Nat} {cmf flg : UInt8}
    (loop : LoopMatches c f h l) (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (zlib : f.wrap = .zlib) (input : f.logIn ++ f.inp.take (loopRead l) = [cmf, flg])
    (invalid : ¬ (ZlibF.Spec.Zlib.HeaderOK cmf flg ∧ ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg]))
    (regsEq : regs = l ∨ regs = headWindowRegs l) :
    LoopBad c f (badHeap h r zs z s i) regs := by
  obtain ⟨zs1, s1, _, _, _, _, st1, hs1, _, config, haveLe, inLen, _⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have doomed : LoopDoomed f l := zlib_head_doomed zlib input invalid
  have get : (badHeap h r zs z s i).istates zs = some { s with mode := BAD } := by
    simp only [badHeap, setI_istates_same]
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := config
  rcases regsEq with rfl | rfl
  · exact ⟨zs, { s with mode := BAD }, st, get, rfl,
      ⟨c1, c2, c3, c4, c5, show BAD ≠ SYNC by decide⟩, haveLe, inLen, doomed⟩
  · exact ⟨zs, { s with mode := BAD }, st, get, rfl,
      ⟨c1, c2, c3, c4, c5, show BAD ≠ SYNC by decide⟩, haveLe, inLen, doomed⟩

/-- An accepted header: the body at its first block boundary, or the header stage in `DICTID`
when `FDICT` is set. -/
theorem zlib_head_accepted {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef}
    {z : ZStream} {zs : Nat} {s : InflateState} {cmf flg : UInt8}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (mode : s.mode = HEAD)
    (zlib : f.wrap = .zlib) (window : HeadWindow s)
    (wire : l.hold.toNat = cmf.toNat + 256 * flg.toNat)
    (input : f.logIn ++ f.inp.take (loopRead l) = [cmf, flg])
    (ok : ZlibF.Spec.Zlib.HeaderOK cmf flg) (fits : ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg]) :
    LoopMatches c f (setI (r.put h { z with adler := 1 }) zs (headDefaultState s l))
      { headWindowRegs l with hold := 0, bits := 0 } := by
  obtain ⟨zs1, s1, callOut, consumed, held, stage, st1, hs1, retOk, config, haveLe, inLen, binv,
    leftLe, pend, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  have same : zs = zs1 ∧ s = s1 := by
    have st := E.st
    rw [st] at st1
    cases st1
    exact ⟨rfl, Option.some.inj (E.hs.symm.trans hs1)⟩
  obtain ⟨rfl, rfl⟩ := same
  have high : (loopState s l).mode ≤ DICTID := by
    show s.mode ≤ DICTID
    rw [mode]
    decide
  obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM high
  obtain ⟨⟨_, headC, _, _, _, wrappedC, last0, total0, _⟩, _, dictC⟩ := wrapM
  obtain ⟨bytesNil, _, width0⟩ := headC mode
  subst bytesNil
  have wrapped : f.wrap ≠ .raw := by rw [zlib]; decide
  obtain ⟨havedict0, wsize0, whave0⟩ := wrappedC wrapped
  have dictNil : f.dict = [] := dictC.resolve_right wrapped
  have outNil : f.logOut ++ callOut = [] := outputEq.symm
  obtain ⟨logNil, callNil⟩ := List.append_eq_nil_iff.mp outNil
  subst callNil
  have pend0 : loopPending l = 0 := by
    have := pend.1
    simp only [List.length_nil] at this
    omega
  have notGzip := zlib_head_not_gzip ok
  have width := zlib_head_width (l := l) wire ok window width0
  have views := MeaningDictid.sameViews_put h r { z with adler := 1 } zs (headDefaultState s l)
  have binv2 := binv.byte_views (fun ref => (views ref).1)
  have bitsNew : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = bytesToBits [cmf, flg] ++ [] := by
    rw [List.append_nil, input]
  have modeEq := zlib_head_mode (l := l) wire
  by_cases plain : flg.toNat / 32 % 2 = 0
  · have modeT : headDefaultMode l = TYPE := by rw [modeEq, ite_eq_left plain]
    refine ⟨zs, headDefaultState s l, [], bytesToBits [cmf, flg], [],
      .body [cmf, flg] ⟨[], false, .boundary⟩, E.st, setI_istates_same _ _ _, retOk,
      zlib_head_config config, haveLe, inLen, ⟨binv2.have_eq, binv2.next, by simp⟩, leftLe,
      ⟨Nat.le_of_eq pend0, fun _ _ _ => pend0⟩, putEq, views.bytes outBytes,
      views.writable writable, sepIn, sepWin, sepOutIn, bitsNew, ⟨rfl, rfl⟩,
      wrapParsed_zlib_body (Or.inl zlib) ok fits plain,
      ⟨⟨Or.inl modeT, rfl, last0, by show (0 : UInt32).toNat < 8; decide⟩,
        Or.inr ⟨wsize0, whave0, by rw [dictNil, logNil] <;> rfl⟩, ?_⟩,
      ⟨?_, width, Or.inl dictNil⟩, by rw [logNil] <;> rfl⟩
    · refine ⟨?_, fun _ => ?_⟩
      · rw [logNil]
        simp only [List.append_nil, List.take_nil, List.length_nil]
        exact total0
      · show (1 : UInt64) = _
        rw [logNil, zlib]
        split
        · rename_i gz
          simp at gz
        · simp only [List.append_nil, List.take_nil] <;> decide
    · show FlagsMatch _ f.wrap _
      rw [zlib]
      unfold FlagsMatch
      rw [ite_eq_right (show ¬ (Api.Wrap.zlib = Api.Wrap.raw) by decide), ite_eq_right notGzip] <;> rfl
  · have fdict : flg.toNat / 32 % 2 = 1 := by omega
    have modeD : headDefaultMode l = DICTID := by rw [modeEq, ite_eq_right plain]
    refine ⟨zs, headDefaultState s l, [], bytesToBits [cmf, flg], [], .header [cmf, flg], E.st,
      setI_istates_same _ _ _, retOk, zlib_head_config config, haveLe, inLen,
      ⟨binv2.have_eq, binv2.next, by simp⟩, leftLe,
      ⟨Nat.le_of_eq pend0, fun _ _ e => by cases e⟩, putEq, views.bytes outBytes,
      views.writable writable, sepIn, sepWin, sepOutIn, bitsNew, ⟨rfl, rfl⟩,
      wrapParsed_zlib_fdict (Or.inl zlib) ok fits fdict, ?_,
      ⟨?_, Or.inr ⟨wsize0, whave0, by rw [dictNil] <;> rfl⟩, Or.inl dictNil⟩, by rw [logNil] <;> rfl⟩
    · show HEAD ≤ headDefaultMode l ∧ headDefaultMode l ≤ DICTID
      rw [modeD]
      decide
    · refine ⟨fun raw => absurd raw wrapped, fun m => ?_,
        fun _ => ⟨rfl, notGzip, rfl, by show (0 : UInt32).toNat ≤ 32; decide, width, fdict⟩,
        fun m => ?_, fun _ hi => ?_, fun _ => ⟨havedict0, wsize0, whave0⟩, last0, total0,
        fun raw => absurd raw wrapped⟩
      · have m' : headDefaultMode l = HEAD := m
        rw [modeD] at m'
        exact absurd m' (by decide)
      · have m' : headDefaultMode l = FLAGS := m
        rw [modeD] at m'
        exact absurd m' (by decide)
      · have hi' : headDefaultMode l ≤ HCRC := hi
        rw [modeD] at hi'
        exact absurd hi' (by decide)

end Zlib.Inflate.Proofs.MeaningHeadZlib

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningHeadZlib
set_option autoImplicit false

/-- `HEAD` with the zlib wrapper, every configured window (0 and 8 to 15): the short-input leave,
the accepted header (the body, or `DICTID` with `FDICT`), and each rejection as `LoopBad`. -/
theorem trip_head_zlib : TripHeadZlib := by
  intro c f r zlib h l side loop head
  obtain ⟨zs, z, s, strm, st, inv, _, _, _⟩ := side
  have E : Env c h r zs z s := ⟨strm, st, inv.good.live.hz, inv.good.live.hs⟩
  have mode : s.mode = HEAD := head zs s st E.hs
  have window : HeadWindow s := inv.toDefaultDecodeJ.headWindow
  obtain ⟨wrap5, headNone, width0, widthCfg⟩ := zlib_head_entry loop st E.hs mode zlib
  obtain ⟨aligned, small, _, _, _⟩ := zlib_head_loop_entry loop head
  have wrapped : f.wrap ≠ .raw := by rw [zlib]; decide
  obtain ⟨result, l', j, needRun, _, _, bitsCount, enough, leaveFacts, kinds, bitsMax, loopAt⟩ :=
    MeaningBits.LoopMatches.needbits_at loop (ok := fun n => n ≤ 16)
      (fun zs' s' _ _ st' hs' stageM' wrapM' hold bits okb => by
        have mode' : s'.mode = HEAD := head zs' s' st' hs'
        have high : (loopState s' l).mode ≤ DICTID := by
          show s'.mode ≤ DICTID
          rw [mode']
          decide
        obtain ⟨bytes, rfl⟩ := MeaningDictid.stage_of_header stageM' high
        exact zlib_head_bits stageM' wrapM' mode' wrapped hold bits okb) 16 (by decide)
  have n16 : (16 : UInt32).toNat = 16 := rfl
  have dispatch := inflate_dispatch_HEAD E l mode
  rcases kinds with rfl | rfl
  · have atLeast := enough rfl
    rw [n16] at atLeast bitsMax
    have bits16 : l'.bits.toNat = 16 := by omega
    have loop' := loopAt (show l'.bits.toNat ≤ 16 by omega)
    obtain ⟨cmf, flg, input, wire, _, _⟩ := zlib_head_observation loop' head (by omega)
    have dispatchRun := dispatch.trans (zlib_head_run_ok E wrap5 headNone needRun)
    have lenEq := zlib_head_window_length (l := l') wire
    by_cases valid : ZlibF.Spec.Zlib.HeaderOK cmf flg ∧ ZlibF.Spec.Api.ZlibFits f.configured [cmf, flg]
    · obtain ⟨hdr, meth, len15⟩ := zlib_head_checks_pass (s := s) wire wrap5 valid.1
      have accRun : runX (headDefaultCheck c s l') l' h =
          .ok ((.ok (), { headWindowRegs l' with hold := 0, bits := 0 }),
            setI (r.put h { z with adler := 1 }) zs (headDefaultState s l')) := by
        by_cases z0 : s.wbits = 0
        · exact headDefaultCheck_accept_zero E l' hdr meth z0 len15
        · have range := window.resolve_right (fun e => z0 e.1)
          have cfgNZ : f.configured ≠ 0 := fun e => z0 (width0 e)
          have w := widthCfg cfgNZ
          have fitsLe := zlib_fits_le valid.2 cfgNZ
          exact headDefaultCheck_accept E l' hdr meth (by omega) range
      exact ⟨_, _, _, dispatchRun.trans accRun, Or.inl (Or.inl ⟨rfl, Or.inl
        (zlib_head_accepted loop' E mode zlib window wire input valid.1 valid.2)⟩)⟩
    · obtain ⟨regs, i, badRun, regsEq⟩ : ∃ (regs : IL) (i : Nat),
          runX (headDefaultCheck c s l') l' h = .ok ((.ok (), regs), badHeap h r zs z s i) ∧
            (regs = l' ∨ regs = headWindowRegs l') := by
        by_cases hdr : headHeaderRejected s l' = true
        · obtain ⟨i, run⟩ := headDefaultCheck_bad_header E l' hdr
          exact ⟨_, i, run, Or.inl rfl⟩
        have hdrF : headHeaderRejected s l' = false := by simpa using hdr
        by_cases meth : headMethodRejected l' = true
        · obtain ⟨i, run⟩ := headDefaultCheck_bad_method E l' hdrF meth
          exact ⟨_, i, run, Or.inl rfl⟩
        have methF : headMethodRejected l' = false := by simpa using meth
        by_cases z0 : s.wbits = 0
        · by_cases big : 15 < (headWindowRegs l').len.toNat
          · obtain ⟨i, run⟩ := headDefaultCheck_bad_window_zero E l' hdrF methF big
            exact ⟨_, i, run, Or.inr rfl⟩
          · exfalso
            apply valid
            refine ⟨zlib_head_format wire hdrF methF (by omega), ?_⟩
            by_cases cz : f.configured = 0
            · exact Or.inl cz
            · have w := widthCfg cz
              have zz : (0 : UInt32).toNat = 0 := rfl
              rw [z0, zz] at w
              exact absurd w.symm cz
        · by_cases wide : s.wbits.toNat < (headWindowRegs l').len.toNat
          · obtain ⟨i, run⟩ := headDefaultCheck_bad_window E l' hdrF methF z0 wide
            exact ⟨_, i, run, Or.inr rfl⟩
          · exfalso
            apply valid
            have range := window.resolve_right (fun e => z0 e.1)
            have cfgNZ : f.configured ≠ 0 := fun e => z0 (width0 e)
            have w := widthCfg cfgNZ
            refine ⟨zlib_head_format wire hdrF methF (by omega), Or.inr ⟨cmf, rfl, by omega⟩⟩
      exact ⟨_, _, _, dispatchRun.trans badRun, Or.inl (Or.inl ⟨rfl, Or.inr
        (zlib_head_bad loop' st E.hs zlib input valid regsEq)⟩)⟩
  · have below := (leaveFacts rfl).2
    rw [n16] at below
    exact ⟨_, _, _, dispatch.trans (zlib_head_run_leave E wrap5 needRun),
      Or.inl (Or.inr ⟨rfl, Or.inl (loopAt (show l'.bits.toNat ≤ 16 by omega))⟩)⟩

#print axioms trip_head_zlib

end Zlib.Inflate.Proofs
