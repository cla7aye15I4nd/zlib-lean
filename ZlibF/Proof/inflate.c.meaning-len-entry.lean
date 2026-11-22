import ZlibF.Proof.«inflate.c.meaning-fast»
import ZlibF.Proof.«inflate.c.fast-view-caller-start-step»
import ZlibF.Proof.«inflate.c.meaning-trip-body»

/-!
# inflate.c: `case LEN_` entered by a fall-through keeps the format meaning

`CODELENS` falls through into `LEN_` (`state->mode = LEN_; if (flush == Z_TREES) goto inf_leave;`),
so a dynamic-header trip can end inside `LEN_`/`LEN`. `len_entry_step` runs `case LEN_` from
`LoopMatches` and the safety invariant of the decoder state (`DefaultStateJ`, `DispatchBuffers`),
stated with explicit facts rather than `CallSide`, since the fall-through point is not the start of a
dispatch. It ends as the body steps do: a leave with `LoopMatches`, or `.ok` with `LoopMatches` or
with `BAD` and the input read so far refuted.

The slow path is `len__step`. The fast path (`inflate_fast`) is `fast_call_meaning`, which takes
input and output in any byte view the dispatch packet admits. `len_entry_step` takes the fast step
either for separate heap byte blocks (`RawFastIO`) or as the proposition `FastLenMeaning`, which is
`fast_call_meaning` stated without the pointer premises and is proved as `fast_len_meaning`
(`inflate.c.meaning-trip-codes`).
-/

namespace Zlib.Inflate.Proofs.MeaningLenEntry
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningMatch
open Zlib.Inflate.Proofs.MeaningDistance Zlib.Inflate.Proofs.MeaningLength
open ZlibF.Spec.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- `fast_call_meaning` for any caller byte views of input and output, stated without the pointer
premises. Proved as `fast_len_meaning` (`inflate.c.meaning-trip-codes`). -/
def FastLenMeaning : Prop :=
  ∀ (c : Ctx) (f : LoopFrame) (h : Heap) (l : IL) (r : ZStreamRef) (z : ZStream),
    LoopMatches c f h l → c.strm = some r → r.get h = some z →
    (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true →
    (∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.mode = LEN ∧ Good h r zs z s ∧ DataTablesSafe h s ∧ DataPendingInvariant s) →
    ZlibF.PlatformMemory.ByteObjectsFit h →
    DispatchBuffers h r l (f.inp.drop (loopRead l)) →
    (f.wrap = .raw → f.configured ≠ 0) →
    ∃ l' h', runX (inflate_LEN c) l h = .ok ((.ok (), l'), h') ∧ loopRead l ≤ loopRead l' ∧
      (LoopMatches c f h' l' ∨
        ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
          LoopRefuted f l'))

/-- The ends of a body step. -/
def BodyEnds (c : Ctx) (f : LoopFrame) (result : Except Ex Unit) (h : Heap) (l : IL) : Prop :=
  (result = .error Ex.leave ∧ LoopMatches c f h l) ∨
    (result = .ok () ∧ (LoopMatches c f h l ∨
      ((∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = BAD) ∧ LoopRefuted f l)))

set_option maxHeartbeats 4000000 in
/-- `case LEN_` from `LoopMatches` and the safety invariant of the state record. The fast path needs
input and output in heap byte blocks, or `FastLenMeaning`. -/
theorem len_entry_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (loop : LoopMatches c f h l) (E : Env c h r zs z s) (j : DefaultStateJ h r zs z s)
    (buf : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (fastCase : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true → RawFastIO l ∨ FastLenMeaning) :
    ∃ result l' h', runX (inflate_LEN_ c) l h = .ok ((result, l'), h') ∧
      BodyEnds c f result h' l' := by
  have loop0 := loop
  obtain ⟨zs0, s0, callOut, consumed, held, stage, st0, hs0, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have e0 : zs0 = zs := by
    rw [E.st] at st0
    cases st0
    rfl
  subst e0
  have e1 : s0 = s := Option.some.inj (hs0.symm.trans E.hs)
  subst e1
  have st := E.st
  have hs := E.hs
  -- the configuration
  have rawWidth : f.wrap = .raw → f.configured ≠ 0 := by
    intro raw zero
    obtain ⟨c1, c2, _, c4, _⟩ := config
    have w : s0.wrap = 0 := by
      have b : s0.wrap = wrapCode f.wrap := c1
      rw [b, raw]
      rfl
    have rw0 : s0.reqwrap = 0 := by
      have a : s0.reqwrap = s0.wrap := c2
      rw [a, w]
    have rb : s0.reqbits.toNat = 0 := by
      have d : s0.reqbits.toNat = f.configured := c4
      rw [d, zero]
    exact j.requestedBits.2 rw0 (UInt32.toNat_inj.mp (by rw [rb]; rfl))
  have buffers : DispatchBuffers h r l (f.inp.drop (loopRead l)) :=
    ⟨buf.input, buf.output, buf.separate, binv⟩
  have oldMode : DataTableMode s0.mode := by rw [mode]; unfold DataTableMode; decide
  have tables0 : DataTablesSafe h s0 := j.tables oldMode
  by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · -- `inflate_fast`
    let current := { s0 with mode := LEN }
    let heap := setI h zs0 current
    have frame : DecodeStateFrame s0 current := rfl
    have good := j.good.decode_update frame (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
    have tables := tables0.decode_update j.good.live.hs frame
    have pending : DataPendingInvariant current := by
      apply dataPendingInvariant_idle (s := current) j.pending.sane
      change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
      decide
    have decoded := j.toDefaultDecodeJ.decode_update good (fun _ => tables) pending frame
      (by change DataExitMode LEN; exact Or.inl (by unfold DataTableMode; decide))
      (byte_view_sizes_setI h zs0 current) rfl
    have packet : DispatchBuffers heap r l (f.inp.drop (loopRead l)) :=
      buffers.byte_views j.good good rfl (byte_view_get_setI h zs0 current) (byte_view_ro_setI h zs0 current)
    -- `LoopMatches` after `state->mode = LEN`
    obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len stageM (Or.inr mode)
    have pendBase := pendLe.2 _ _ rfl
    obtain ⟨⟨last, lenTable, distTable, _, p7⟩, window, check⟩ := stageM
    obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
    have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
    subst heldEq
    have loop1 := loop_move (s' := current) (l' := l) (j := 0)
      (pos := ⟨out, final, .codes L D .none⟩) st retOk
      ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LEN ≠ SYNC by decide⟩
      haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
      ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) (inputAdvance_zero l.next).symm binv bitsEq
      (HeldBits.of_natBits (s := loopState current l) binv.hold_lt) wrapHeader consumedEq
      deflate
      ⟨last, table_setI (s' := current) hs rfl lenTable,
        table_setI (s' := current) hs rfl distTable, Or.inr rfl, p7⟩
      (window_transfer (s := loopState s0 l) (s' := loopState current l) rfl rfl rfl rfl
        (fun q => byte_view_get_setI h zs0 _ q) window) check wrapM outputEq
    have stateFacts : ∀ zs' s', c.st = some (.tab zs') → heap.istates zs' = some s' →
        s'.mode = LEN ∧ Good heap r zs' z s' ∧ DataTablesSafe heap s' ∧ DataPendingInvariant s' := by
      intro zs' s' st' hs'
      rw [st] at st'
      cases st'
      have get : heap.istates zs0 = some current := setI_istates_same h zs0 current
      rw [get] at hs'
      cases hs'
      exact ⟨rfl, good, tables, pending⟩
    have hzHeap : r.get heap = some z := by
      show r.get (setI h zs0 current) = some z
      rw [ZStreamRef.get_setI]
      exact E.hz
    have run0 : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := len__run E l
    have ends : ∃ l' h', runX (inflate_LEN c) l heap = .ok ((.ok (), l'), h') ∧ loopRead l ≤ loopRead l' ∧
        (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopRefuted f l')) := by
      rcases fastCase fast with raw | general
      · obtain ⟨ib, io, ob, oo, input, output, _⟩ := raw
        exact MeaningFast.fast_call_meaning loop1 E.strm hzHeap fast stateFacts decoded.platform packet
          input output rawWidth
      · exact general c f heap l r z loop1 E.strm hzHeap fast stateFacts decoded.platform packet rawWidth
    obtain ⟨l', h', run, _, rest⟩ := ends
    exact ⟨.ok (), l', h', run0.trans run, Or.inr ⟨rfl, rest⟩⟩
  · -- the slow path
    have lenMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LEN_ :=
      at_state (P := fun s => s.mode = LEN_) st hs mode
    have win := j.good.inv.win
    have bounds := at_state (P := fun s => s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) st hs
      (window_bounds win)
    have sane := at_state (P := fun s => s.sane ≠ 0) st hs (by rw [j.pending.sane]; decide)
    have wsizeBits := at_state (P := fun s => s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat) st hs
      (by
        intro nz
        rcases win.ws with zero | pow
        · exact absurd (UInt32.toNat_inj.mp (by rw [zero]; rfl)) nz
        · exact pow)
    have ring := at_state (P := fun s => s.whave < s.wsize → s.wnext = s.whave) st hs
      (by
        intro lt
        exact UInt32.toNat_inj.mp (win.eq (UInt32.lt_iff_toNat_lt.mp lt)))
    have privateWindow := at_state
      (P := fun s => ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d) st hs
      (by
        intro w o d i window put same
        rcases win.block with null | ⟨wb, a, wref, _⟩
        · rw [null] at window
          cases window
        · rw [wref] at window
          cases window
          exact callerRange_private_window j.good buf.output.range put wb wref same.symm)
    have tables := at_state (P := fun s => DataTablesSafe h s) st hs tables0
    obtain ⟨result, l', h', run, ends⟩ := len__step loop0 E.strm E.hz fast lenMode tables bounds sane
      wsizeBits ring privateWindow rawWidth
    refine ⟨result, l', h', run, ?_⟩
    rcases ends with ⟨e, _, m⟩ | ⟨e, _, rest⟩
    · exact Or.inl ⟨e, m⟩
    · exact Or.inr ⟨e, rest⟩

#print axioms len_entry_step

end Zlib.Inflate.Proofs.MeaningLenEntry
