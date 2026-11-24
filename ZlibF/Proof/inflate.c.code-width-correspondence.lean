import ZlibF.Proof.«infback.c.repeat-fields»

/-! The shared bit-consumption helper keeps the current Huffman code while
updating the signed back count. The slow paths agree on faults as well as
successful executions. The fast path reads the same output count across RESTORE. -/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Infback.Equality
open Zlib.Inffast (inflate_fast)

private def dropAndAccount (st : InflateStatePtr) (bits : UInt8) : X Unit := do
  DROPBITS bits.toUInt32
  let s ← ldInflateState st
  let back ← chkI32 (s.back.toInt + bits.toNat)
  wrS st fun s => { s with back }

private theorem dropKeepsCode (st : InflateStatePtr) (bits : UInt8) (code : Code) :
    Zlib.Infback.CodeFrame.KeepsCode code (dropAndAccount st bits) := by
  unfold dropAndAccount
  apply registerFrame_bind (Zlib.Infback.CodeFrame.drop code _)
  intro _
  register_frame_source

private theorem consumeHere (st : InflateStatePtr) (k : Code → X α) :
    (do consumeCodeWidth st false
        k (← get).here) = (do
      let here := (← get).here
      DROPBITS here.bits.toUInt32
      let s ← ldInflateState st
      let back ← chkI32 (s.back.toInt + here.bits.toNat)
      wrS st fun s => { s with back }
      k here) := by
  funext l h
  change runX _ l h = runX _ l h
  have after := codeAfter (dropAndAccount st l.here.bits) (dropKeepsCode st l.here.bits)
    (fun here _ => k here) l h
  simpa only [dropAndAccount, consumeCodeWidth, x_bind_assoc, runX_bind, runX_get, Bool.false_eq_true, ite_false] using after

private def distPrefix (c : Ctx) (tail : X Unit) : X Unit := do
  lookup1 c true
  let here := (← get).here
  -- if ((here.op & 0xf0) == 0) {
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    consumeCodeWidth c.st true
  -- DROPBITS(here.bits); state->back += here.bits;
  tail

private def distSuffix (c : Ctx) (here : Code) : X Unit := do
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15; state->mode = DISTEXT;
  wrS c.st fun s => { s with offset := here.val.toUInt32 }
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15 }
  setMode c.st DISTEXT
  inflate_DISTEXT c

theorem DIST_previous (c : Ctx) : inflate_DIST c = (do
  lookup1 c true
  let here := (← get).here
  -- if ((here.op & 0xf0) == 0) {
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }
  -- DROPBITS(here.bits); state->back += here.bits;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk }
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15; state->mode = DISTEXT;
  wrS c.st fun s => { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }
  setMode c.st DISTEXT
  inflate_DISTEXT c) := by
  change distPrefix c (do consumeCodeWidth c.st false; distSuffix c (← get).here) = _
  rw [consumeHere c.st (distSuffix c)]
  unfold distPrefix distSuffix consumeCodeWidth
  simp only [↓reduceIte, setMode, x_bind_assoc, two_state_writes]
  first | rfl | done

private def lenPrefix (c : Ctx) (tail : X Unit) : X Unit := do
  let l ← get
  -- if (have >= 6 && left >= 258 && bits < 8) { RESTORE(); inflate_fast(strm, out); LOAD(); ...; break; }
  if l.have_ >= 6 && l.left >= 258 && l.bits < 8 then
    RESTORE c.strm c.st
    inflate_fast c.strm (← get).out_
    LOAD c.strm c.st
    -- if (state->mode == TYPE) state->back = -1;
    if (← rdS c.st (·.mode)) == TYPE then wrS c.st fun s => { s with back := -1 }
    return
  -- state->back = 0;
  wrS c.st fun s => { s with back := 0 }
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    consumeCodeWidth c.st true
  -- DROPBITS(here.bits); state->back += here.bits; state->length = (unsigned)here.val;
  tail

private def lenSuffix (c : Ctx) (here : Code) : X Unit := do
  wrS c.st fun s => { s with length := here.val.toUInt32 }
  -- if ((int)(here.op) == 0) { state->mode = LIT; break; }
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  -- if (here.op & 32) { state->back = -1; state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1 }
    setMode c.st TYPE
    return
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; state->mode = LENEXT; /* fallthrough */
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15 }
  setMode c.st LENEXT
  inflate_LENEXT c

theorem LEN_previous (c : Ctx) : inflate_LEN c = (do
  let l ← get
  -- if (have >= 6 && left >= 258 && bits < 8) { RESTORE(); inflate_fast(strm, out); LOAD(); ...; break; }
  if l.have_ >= 6 && l.left >= 258 && l.bits < 8 then
    RESTORE c.strm c.st
    inflate_fast c.strm l.out_
    LOAD c.strm c.st
    -- if (state->mode == TYPE) state->back = -1;
    if (← rdS c.st (·.mode)) == TYPE then wrS c.st fun s => { s with back := -1 }
    return
  -- state->back = 0;
  wrS c.st fun s => { s with back := 0 }
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }
  -- DROPBITS(here.bits); state->back += here.bits; state->length = (unsigned)here.val;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk, length := here.val.toUInt32 }
  -- if ((int)(here.op) == 0) { state->mode = LIT; break; }
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  -- if (here.op & 32) { state->back = -1; state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1, mode := TYPE }
    return
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; state->mode = LENEXT; /* fallthrough */
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }
  inflate_LENEXT c) := by
  change lenPrefix c (do consumeCodeWidth c.st false; lenSuffix c (← get).here) = _
  rw [consumeHere c.st (lenSuffix c)]
  unfold lenPrefix lenSuffix consumeCodeWidth
  simp only [↓reduceIte, setMode, x_bind_assoc, two_state_writes]
  funext l h
  change runX _ l h = runX _ l h
  simp only [runX_bind, runX_get]
  split
  · simp only [runX_bind, runX_get, RESTORE_stores, runX_lift]
    cases got : restoreStores c.strm c.st l h with
    | error e => rfl
    | ok pair => obtain ⟨u, after⟩ := pair; rfl
  · rfl

end Zlib.Inflate.Proofs
