import ZlibF.Proof.«infback.c.repeat-fields»

/-! Equality of complete decoder computations before and after C emission was aligned with
the patched Linux source. Each right-hand side retains the earlier mode body and its
continuation. Equality includes the local registers, returned heap, and both fault paths. -/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
open Zlib.Adler32 Zlib.Crc32
open Zlib.Inftrees (inflate_fixed inflate_table)
theorem liftHeapBind {α β : Type} (m : M α) (k : α → M β) :
    (monadLift (m >>= k) : X β) = ((monadLift m : X α) >>= fun a => monadLift (k a)) := by
  funext l h
  change runX _ l h = runX _ l h
  simp only [runX_lift, runX_bind, bind_app]
  cases hv : m h with
  | error e => rfl
  | ok pair => obtain ⟨a, after⟩ := pair; rfl

private theorem liftPureOrd {α : Type} (a : α) : (monadLift (pure a : M α) : X α) = pure a := rfl

private theorem bindIteOrd (p : Prop) [Decidable p] (yes no : X α) (k : α → X β) :
    ((if p then yes else no) >>= k) = (if p then yes >>= k else no >>= k) := by
  by_cases h : p <;> simp only [h, ↓reduceIte]

theorem lookup1_previous (c : Ctx) (dist : Bool) : lookup1 c dist = (xloopBrk (do
    let s ← ldInflateState c.st
    let tab := if dist then s.distcode else s.lencode
    let nb := if dist then s.distbits else s.lenbits
    let b ← BITS nb
    let here ← Ptr.index tab (b.toNat : Int)
    modify fun l => { l with here := here }
    if here.bits.toUInt32 <= (← get).bits then return true
    PULLBYTE
    return false)) := rfl

theorem lookup2_previous (c : Ctx) (dist : Bool) : lookup2 c dist = (xloopBrk (do
    let s ← ldInflateState c.st
    let tab := if dist then s.distcode else s.lencode
    let last := (← get).last
    let b ← BITS (last.bits.toUInt32 + last.op.toUInt32)
    let sh ← shr32 b last.bits.toUInt32
    let here ← Ptr.index tab ((last.val.toUInt32 + sh).toNat : Int)
    modify fun l => { l with here := here }
    if (last.bits.toUInt32 + here.bits.toUInt32) <= (← get).bits then return true
    PULLBYTE
    return false)) := rfl

theorem inflate_CHECK_previous (c : Ctx) : inflate_CHECK c = (do
  let s ← ldInflateState c.st
  -- if (state->wrap) {
  if s.wrap != 0 then
    NEEDBITS 32
    -- out -= left;
    modify fun l => { l with out_ := l.out_ - l.left }
    let l ← get
    -- strm->total_out += out; state->total += out;
    wrZ c.strm fun z => { z with total_out := z.total_out + l.out_.toUInt64 }
    wrS c.st fun s => { s with total := s.total + l.out_.toUInt64 }
    -- if ((state->wrap & 4) && out) strm->adler = state->check = UPDATE_CHECK(state->check, put - out, out);
    let s ← ldInflateState c.st
    if (s.wrap &&& 4) != 0 && l.out_ != 0 then
      let p ← l.put.add (-(l.out_.toNat : Int))
      let v ← UPDATE_CHECK c.st s.check p l.out_
      wrS c.st fun s => { s with check := v }
      wrZ c.strm fun z => { z with adler := v }
    -- out = left;
    modify fun l => { l with out_ := l.left }
    -- if ((state->wrap & 4) && ((state->flags ? hold : ZSWAP32(hold)) != state->check)) { ...BAD; break; }
    let s ← ldInflateState c.st
    let l ← get
    if (s.wrap &&& 4) != 0 && (if s.flags != 0 then l.hold else ZSWAP32 l.hold) != s.check then
      badMode c "incorrect data check"
      return
    INITBITS
  -- state->mode = LENGTH; /* fallthrough */
  setMode c.st LENGTH
  inflate_LENGTH c) := by
  unfold inflate_CHECK accountCheckedOutput
  simp only [x_bind_assoc, bindIteOrd]

theorem inflate_TYPEDO_previous (c : Ctx) : inflate_TYPEDO c = (do
  -- if (state->last) { BYTEBITS(); state->mode = CHECK; break; }
  if (← rdS c.st (·.last)) != 0 then
    BYTEBITS
    setMode c.st CHECK
    return
  NEEDBITS 3
  -- state->last = BITS(1); DROPBITS(1);
  let b ← BITS 1
  wrS c.st fun s => { s with last := u2i b }
  DROPBITS 1
  -- switch (BITS(2)) {
  match (← BITS 2) with
  | 0 => setMode c.st STORED
  | 1 =>
    inflate_fixed c.st
    setMode c.st LEN_
    -- if (flush == Z_TREES) { DROPBITS(2); goto inf_leave; }
    if c.flush == Z_TREES then
      DROPBITS 2
      throw Ex.leave
  | 2 => setMode c.st TABLE
  | _ => badMode c "invalid block type"
  -- DROPBITS(2); break;
  DROPBITS 2) := by
  unfold inflate_TYPEDO rdS
  simp only [liftHeapBind, x_bind_assoc, x_pure_bind, liftPureOrd]
  rfl

/-- The complete ordinary literal emission step equals the previous computation. -/
theorem LIT_preserved (c : Ctx) : inflate_LIT c = (do
  let l ← get
  -- if (left == 0) goto inf_leave;
  if l.left == 0 then throw Ex.leave
  -- *put++ = (unsigned char)(state->length);
  let s ← ldInflateState c.st
  store8 l.put s.length.toUInt8
  let p ← l.put.add 1
  -- left--; state->mode = LEN;
  set { l with put := p, left := l.left - 1 }
  setMode c.st LEN) := by
  funext l h
  change runX _ l h = runX _ l h
  simp only [runX_bind, runX_get]
  by_cases empty : (l.left == 0) = true
  · simp only [empty, ↓reduceIte, runX_bind, runX_throw]
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, emitLiteral, x_bind_assoc, runX_bind, runX_get]

/-- The complete distance extra bits step equals the previous computation. -/
theorem DISTEXT_preserved (c : Ctx) : inflate_DISTEXT c = (do
  let s ← ldInflateState c.st
  -- if (state->extra) {
  if s.extra != 0 then
    NEEDBITS s.extra
    -- state->offset += BITS(state->extra);
    let b ← BITS s.extra
    wrS c.st fun s => { s with offset := s.offset + b }
    -- DROPBITS(state->extra);
    DROPBITS s.extra
    -- state->back += state->extra;   (`int += unsigned`: computed in unsigned, converted back)
    wrS c.st fun s => { s with back := u2i (i2u s.back + s.extra) }
  -- state->mode = MATCH; /* fallthrough */
  setMode c.st MATCH
  inflate_MATCH c) := by
  unfold inflate_DISTEXT addExtra
  simp only [↓reduceIte, x_bind_assoc, x_pure_bind, bindIteOrd]

/-- The complete length extra bits and consecutive state writes step equals the previous computation. -/
theorem LENEXT_preserved (c : Ctx) : inflate_LENEXT c = (do
  let s ← ldInflateState c.st
  if s.extra != 0 then
    NEEDBITS s.extra
    -- state->length += BITS(state->extra);
    let b ← BITS s.extra
    wrS c.st fun s => { s with length := s.length + b }
    DROPBITS s.extra
    wrS c.st fun s => { s with back := u2i (i2u s.back + s.extra) }
  -- state->was = state->length; state->mode = DIST; /* fallthrough */
  wrS c.st fun s => { s with was := s.length, mode := DIST }
  inflate_DIST c) := by
  unfold inflate_LENEXT addExtra setMode
  simp only [↓reduceIte, Bool.false_eq_true, x_bind_assoc, x_pure_bind, bindIteOrd]
  simp only [Zlib.Infback.Equality.two_state_writes]
  first | rfl | done

theorem TIME_previous (c : Ctx) : inflate_TIME c = (do
  NEEDBITS 32
  let l ← get
  let s ← ldInflateState c.st
  -- if (state->head != Z_NULL) state->head->time = hold;
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with time := l.hold }
  -- if ((state->flags & 0x0200) && (state->wrap & 4)) CRC4(state->check, hold);
  if ← hcrcOn c.st then CRC4 c
  INITBITS
  setMode c.st OS
  inflate_OS c) := by
  unfold inflate_TIME storeHeaderWord
  simp only [↓reduceIte, x_bind_assoc, x_pure_bind, bindIteOrd, Bool.false_eq_true]
theorem OS_previous (c : Ctx) : inflate_OS c = (do
  NEEDBITS 16
  let l ← get
  let s ← ldInflateState c.st
  -- if (state->head != Z_NULL) { state->head->xflags = (int)(hold & 0xff); state->head->os = (int)(hold >> 8); }
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with xflags := (l.hold &&& 0xff).toUInt32.toInt32, os := (l.hold >>> 8).toUInt32.toInt32 }
  if ← hcrcOn c.st then CRC2 c
  INITBITS
  setMode c.st EXLEN
  inflate_EXLEN c) := by
  unfold inflate_OS storeHeaderWord
  simp only [↓reduceIte, x_bind_assoc, x_pure_bind, bindIteOrd]

theorem LENLENS_previous (c : Ctx) : inflate_LENLENS c = (do
  -- while (state->have < state->ncode) { NEEDBITS(3); state->lens[order[state->have++]] = (unsigned short)BITS(3); DROPBITS(3); }
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < s.ncode)
    (do
      NEEDBITS 3
      withLengthOrder c.st fun o => do
        let b ← BITS 3
        Ptr.store (← (lensP c.st).add (o.toNat : Int)) b.toUInt16
        DROPBITS 3)
  -- while (state->have < 19) state->lens[order[state->have++]] = 0;
  xwhile
    (do let s ← ldInflateState c.st; return s.«have» < 19)
    (do
      withLengthOrder c.st fun o => do
        Ptr.store (← (lensP c.st).add (o.toNat : Int)) (0 : UInt16))
  -- state->next = state->codes; state->lencode = state->distcode = (const code FAR *)(state->next); state->lenbits = 7;
  wrS c.st fun s =>
    let s := { s with next := codesP c.st }
    let s := { s with distcode := s.next }
    let s := { s with lencode := s.next }
    { s with lenbits := 7 }
  -- ret = inflate_table(CODES, state->lens, 19, &(state->next), &(state->lenbits), state->work);
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  -- if (ret) { "invalid code lengths set"; BAD; break; }
  if r != 0 then
    badMode c "invalid code lengths set"
    return
  -- state->have = 0; state->mode = CODELENS; /* fallthrough */
  wrS c.st fun s => { s with «have» := 0, mode := CODELENS }
  inflate_CODELENS c) := by
  unfold inflate_LENLENS storeOrderedLength withLengthOrder startLengthTable setMode
  simp only [liftHeapBind, x_bind_assoc, x_pure_bind, Zlib.Infback.Equality.two_state_writes]
  first | rfl | done

theorem TABLE_previous (c : Ctx) : inflate_TABLE c = (do
  NEEDBITS 14
  -- state->nlen = BITS(5) + 257; DROPBITS(5);
  let b ← BITS 5
  wrS c.st fun s => { s with nlen := b + 257 }
  DROPBITS 5
  -- state->ndist = BITS(5) + 1; DROPBITS(5);
  let b ← BITS 5
  wrS c.st fun s => { s with ndist := b + 1 }
  DROPBITS 5
  -- state->ncode = BITS(4) + 4; DROPBITS(4);
  let b ← BITS 4
  wrS c.st fun s => { s with ncode := b + 4 }
  DROPBITS 4
  -- if (state->nlen > 286 || state->ndist > 30) { "too many length or distance symbols"; BAD; break; }
  let s ← ldInflateState c.st
  if s.nlen > 286 || s.ndist > 30 then
    badMode c "too many length or distance symbols"
    return
  -- state->have = 0; state->mode = LENLENS; /* fallthrough */
  wrS c.st fun s => { s with «have» := 0, mode := LENLENS }
  inflate_LENLENS c) := by
  unfold inflate_TABLE
  simp only [setMode, Zlib.Infback.Equality.two_state_writes]

set_option maxRecDepth 3000 in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
theorem COPY_previous (c : Ctx) : inflate_COPY c = (do
  -- copy = state->length;
  let s ← ldInflateState c.st
  let mut copy := s.length
  -- if (copy) {
  if copy != 0 then
    let l ← get
    if copy > l.have_ then copy := l.have_
    if copy > l.left then copy := l.left
    -- if (copy == 0) goto inf_leave;
    if copy == 0 then
      set { l with copy := copy }
      throw Ex.leave
    -- zmemcpy(put, next, copy);
    memcpyB l.put l.next copy.toNat
    -- have -= copy; next += copy; left -= copy; put += copy; state->length -= copy;
    let nx ← l.next.add (copy.toNat : Int)
    let pt ← l.put.add (copy.toNat : Int)
    set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
    wrS c.st fun s => { s with length := s.length - copy }
    return
  modify fun l => { l with copy := copy }
  -- state->mode = TYPE; break;
  setMode c.st TYPE) := by
  funext l h
  change runX _ l h = runX _ l h
  simp only [runX_bind, runX_lift]
  cases hs : ldInflateState c.st h with
  | error fault => rfl
  | ok result =>
    obtain ⟨state, after⟩ := result
    simp only [runX_modify, runX_get]
    by_cases nonempty : (state.length != 0) = true
    · simp only [nonempty, ↓reduceIte, copyStoredInput, runX_bind, runX_get]
      by_cases up : state.length > l.have_ <;>
        by_cases room : l.have_ > l.left <;>
        by_cases width : state.length > l.left <;>
        simp only [up, room, width, ↓reduceIte]
      all_goals
        (first | by_cases zero : (l.left == 0) = true | skip)
        <;> (first | by_cases hzero : (l.have_ == 0) = true | skip)
        <;> simp_all [runX_bind, runX_set, runX_throw, runX_lift]
      all_goals
        rcases m : memcpyB _ _ _ _ with fault | ⟨u, h1⟩ <;> simp only [m, runX_pure] <;> try rfl
      all_goals
        rcases a : Ptr.add l.next _ h1 with fault | ⟨v, h2⟩ <;> simp only [a] <;> try rfl
      all_goals
        rcases b : Ptr.add l.put _ h2 with fault | ⟨t, h3⟩ <;> simp only [b] <;> try rfl
      all_goals
        rcases e : wrS c.st _ h3 with fault | ⟨u, h4⟩ <;> simp only [e, runX_pure] <;> rfl
    · simp [nonempty, runX_bind, runX_modify, runX_lift]

theorem DICT_previous (c : Ctx) : inflate_DICT c = (do
  -- if (state->havedict == 0) { RESTORE(); strm->total_in += in - strm->avail_in; return Z_NEED_DICT; }
  if (← rdS c.st (·.havedict)) == 0 then
    RESTORE c.strm c.st
    let l ← get
    wrZ c.strm fun z => { z with total_in := z.total_in + (l.in_ - z.avail_in).toUInt64 }
    throw (Ex.ret Z_NEED_DICT)
  -- strm->adler = state->check = adler32(0L, Z_NULL, 0);
  let v ← adler32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  -- state->mode = TYPE; /* fallthrough */
  setMode c.st TYPE
  inflate_TYPE c) := by
  unfold inflate_DICT startDataCheck storeChecksum
  simp only [↓reduceIte, liftHeapBind, x_bind_assoc, Bool.false_eq_true]

theorem DICTID_previous (c : Ctx) : inflate_DICTID c = (do
  NEEDBITS 32
  -- strm->adler = state->check = ZSWAP32(hold);
  let v := ZSWAP32 (← get).hold
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  INITBITS
  setMode c.st DICT
  inflate_DICT c) := by
  unfold inflate_DICTID storeDictId storeChecksum
  simp only [liftHeapBind, x_bind_assoc]

private theorem ignoreGet (k : X α) : (get >>= fun (_ : IL) => k) = k := rfl

theorem HCRC_previous (c : Ctx) : inflate_HCRC c = (do
  -- if (state->flags & 0x0200) {
  if ((← rdS c.st (·.flags)) &&& 0x0200) != 0 then
    NEEDBITS 16
    let s ← ldInflateState c.st
    -- if ((state->wrap & 4) && hold != (state->check & 0xffff)) { "header crc mismatch"; BAD; break; }
    if (s.wrap &&& 4) != 0 && (← get).hold != (s.check &&& 0xffff) then
      badMode c "header crc mismatch"
      return
    INITBITS
  -- if (state->head != Z_NULL) { state->head->hcrc = (int)((state->flags >> 9) & 1); state->head->done = 1; }
  let s ← ldInflateState c.st
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with hcrc := (s.flags >>> 9) &&& 1, done := 1 }
  -- strm->adler = state->check = crc32(0L, Z_NULL, 0);
  let v ← crc32 0 .null 0
  wrS c.st fun s => { s with check := v }
  wrZ c.strm fun z => { z with adler := v }
  -- state->mode = TYPE; break;
  setMode c.st TYPE) := by
  unfold inflate_HCRC startDataCheck storeChecksum updateHeader rdS
  simp only [↓reduceIte, liftHeapBind, x_bind_assoc, ignoreGet, liftPureOrd, x_pure_bind, bindIteOrd]

theorem COMMENT_previous (c : Ctx) : inflate_COMMENT c = (do
  if ((← rdS c.st (·.flags)) &&& 0x1000) != 0 then
    if (← get).have_ == 0 then throw Ex.leave
    modify fun l => { l with copy := 0 }
    xdoWhile
      (do
        let l ← get
        let b ← index8 l.next l.copy.toNat
        set { l with len := b.toUInt32, copy := l.copy + 1 }
        let s ← ldInflateState c.st
        if s.head != none then
          let g ← ldGzHeader s.head
          if g.comment != .null && s.length < g.comm_max then
            store8 (← g.comment.add (s.length.toNat : Int)) b
            wrS c.st fun s => { s with length := s.length + 1 })
      (do let l ← get; return l.len != 0 && l.copy < l.have_)
    if ← hcrcOn c.st then
      let l ← get
      let v ← crc32 (← rdS c.st (·.check)) l.next l.copy
      wrS c.st fun s => { s with check := v }
    let l ← get
    let nx ← l.next.add (l.copy.toNat : Int)
    set { l with have_ := l.have_ - l.copy, next := nx }
    if l.len != 0 then throw Ex.leave
  else
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with comment := .null }
  setMode c.st HCRC
  inflate_HCRC c) := by
  unfold inflate_COMMENT readHeaderString updateHeader rdS
  simp only [↓reduceIte, Bool.false_eq_true, liftHeapBind, x_bind_assoc, x_pure_bind, liftPureOrd, ignoreGet, bindIteOrd]
  first | rfl | done

theorem NAME_previous (c : Ctx) : inflate_NAME c = (do
  if ((← rdS c.st (·.flags)) &&& 0x0800) != 0 then
    if (← get).have_ == 0 then throw Ex.leave
    modify fun l => { l with copy := 0 }
    xdoWhile
      (do
        let l ← get
        let b ← index8 l.next l.copy.toNat
        set { l with len := b.toUInt32, copy := l.copy + 1 }
        let s ← ldInflateState c.st
        if s.head != none then
          let g ← ldGzHeader s.head
          if g.name != .null && s.length < g.name_max then
            store8 (← g.name.add (s.length.toNat : Int)) b
            wrS c.st fun s => { s with length := s.length + 1 })
      (do let l ← get; return l.len != 0 && l.copy < l.have_)
    if ← hcrcOn c.st then
      let l ← get
      let v ← crc32 (← rdS c.st (·.check)) l.next l.copy
      wrS c.st fun s => { s with check := v }
    let l ← get
    let nx ← l.next.add (l.copy.toNat : Int)
    set { l with have_ := l.have_ - l.copy, next := nx }
    if l.len != 0 then throw Ex.leave
  else
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with name := .null }
  wrS c.st fun s => { s with length := 0, mode := COMMENT }
  inflate_COMMENT c) := by
  unfold inflate_NAME readHeaderString updateHeader rdS setMode
  simp only [↓reduceIte, liftHeapBind, x_bind_assoc, x_pure_bind, liftPureOrd, ignoreGet, bindIteOrd, Zlib.Infback.Equality.two_state_writes]
  first | rfl | done

theorem EXTRA_previous (c : Ctx) : inflate_EXTRA c = (do
  if ((← rdS c.st (·.flags)) &&& 0x0400) != 0 then
    let s ← ldInflateState c.st
    let l ← get
    let copy := if s.length > l.have_ then l.have_ else s.length
    set { l with copy := copy }
    if copy != 0 then
      if s.head != none then
        let g ← ldGzHeader s.head
        if g.extra != .null then
          let len := g.extra_len - s.length
          modify fun l => { l with len := len }
          if len < g.extra_max then
            let n := if len + copy > g.extra_max then g.extra_max - len else copy
            memcpyB (← g.extra.add (len.toNat : Int)) (← get).next n.toNat
      if ← hcrcOn c.st then
        let v ← crc32 (← rdS c.st (·.check)) (← get).next copy
        wrS c.st fun s => { s with check := v }
      let l ← get
      let nx ← l.next.add (copy.toNat : Int)
      set { l with have_ := l.have_ - copy, next := nx }
      wrS c.st fun s => { s with length := s.length - copy }
    if (← rdS c.st (·.length)) != 0 then throw Ex.leave
  wrS c.st fun s => { s with length := 0, mode := NAME }
  inflate_NAME c) := by
  unfold inflate_EXTRA copyHeaderExtra rdS setMode
  simp only [liftHeapBind, x_bind_assoc, x_pure_bind, liftPureOrd, bindIteOrd, Zlib.Infback.Equality.two_state_writes]
  first | rfl | done

private theorem registers_after_write {α : Type} (write : IL → M Unit) (cont : IL → X α) :
    (do let before ← get; write before; let after ← get; cont after : X α) =
    (do let before ← get; write before; cont before) := by
  funext l h
  change runX _ l h = runX _ l h
  simp only [runX_bind, runX_get, runX_lift]
  cases e : write l h with
  | error fault => rfl
  | ok p => cases p; rfl

private theorem reload_state_else {α : Type} (st : InflateStatePtr) (p : InflateState → Bool)
    (yes no : InflateState → X α) :
    (do let s ← ldInflateState st; if p s then yes s else let t ← ldInflateState st; no t : X α) =
    (do let s ← ldInflateState st; if p s then yes s else no s) := by
  funext l h
  change runX _ l h = runX _ l h
  cases st with
  | none => simp [runX_bind, runX_lift, ldInflateState]
  | some r =>
    cases r with
    | tab i =>
      cases e : h.istates i with
      | none => simp [runX_bind, runX_lift, ldInflateState, InflateStateRef.get, e]
      | some s =>
        simp only [runX_bind, runX_lift_ok (ldInflateState_tab e)]
        cases test : p s <;> simp only [Bool.false_eq_true, ↓reduceIte, runX_bind, runX_lift_ok (ldInflateState_tab e)]

theorem EXLEN_previous (c : Ctx) : inflate_EXLEN c = (do
  let s ← ldInflateState c.st
  if (s.flags &&& 0x0400) != 0 then
    NEEDBITS 16
    let l ← get
    wrS c.st fun s => { s with length := l.hold.toUInt32 }
    let s ← ldInflateState c.st
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with extra_len := l.hold.toUInt32 }
    if ← hcrcOn c.st then CRC2 c
    INITBITS
  else
    if s.head != none then
      let g ← ldGzHeader s.head
      stGzHeader s.head { g with extra := .null }
  setMode c.st EXTRA
  inflate_EXTRA c) := by
  unfold inflate_EXLEN updateHeader
  simp only [x_bind_assoc, bindIteOrd, x_pure_bind, ignoreGet, registers_after_write, reload_state_else]

theorem FLAGS_previous (c : Ctx) : inflate_FLAGS c = (do
  NEEDBITS 16
  let l ← get
  wrS c.st fun s => { s with flags := l.hold.toUInt32.toInt32 }
  let s ← ldInflateState c.st
  if (s.flags &&& 0xff) != Z_DEFLATED then
    badMode c "unknown compression method"
    return
  if (s.flags &&& 0xe000) != 0 then
    badMode c "unknown header flags set"
    return
  if s.head != none then
    let g ← ldGzHeader s.head
    stGzHeader s.head { g with text := ((l.hold >>> 8) &&& 1).toUInt32.toInt32 }
  if ← hcrcOn c.st then CRC2 c
  INITBITS
  setMode c.st TIME
  inflate_TIME c) := by
  unfold inflate_FLAGS
  simp only [x_bind_assoc, bindIteOrd, x_pure_bind]
  apply congrArg (Bind.bind (NEEDBITS 16))
  funext _ l h
  change runX _ l h = runX _ l h
  cases st : c.st with
  | none => simp [runX_bind, runX_get, runX_lift, wrS, ldInflateState]
  | some r =>
    cases r with
    | tab i =>
      cases e : h.istates i with
      | none => simp [runX_bind, runX_get, runX_lift, wrI_eq, e]
      | some state =>
        simp only [runX_bind, runX_get, runX_lift, wrI_eq, e, ldInflateState_tab (setI_istates_same ..)]
        by_cases method : ((l.hold.toUInt32.toInt32 &&& 0xff) != Z_DEFLATED) = true
        · simp only [method, ↓reduceIte]
        · by_cases flags : ((l.hold.toUInt32.toInt32 &&& 0xe000) != 0) = true
          · simp only [method, flags, Bool.false_eq_true, ↓reduceIte]
          · simp only [method, flags, Bool.false_eq_true, ↓reduceIte, runX_bind,
              runX_get, runX_lift, ldInflateState_tab (setI_istates_same ..)]
            all_goals by_cases hd : (state.head != none) = true <;> simp only [hd, Bool.false_eq_true, ↓reduceIte, runX_pure, runX_bind]

end Zlib.Inflate.Proofs

namespace Zlib.Infback.Equality
open C Zlib.Inflate Zlib.Infback
theorem lookup1_previous (c : DecoderCtx) (dist : Bool) : Zlib.Infback.lookup1 c dist = (xloopBrk (do
    let s ← ldInflateState c.st
    let tab : ConstCodePtr := if dist then s.distcode else s.lencode
    let nb := if dist then s.distbits else s.lenbits
    let b ← BITS nb
    let here ← Ptr.index tab (b.toNat : Int)
    modify fun l => { l with here := here }
    if here.bits.toUInt32 <= (← get).bits then return true
    Zlib.Infback.PULLBYTE c
    return false)) := rfl

theorem lookup2_previous (c : DecoderCtx) (dist : Bool) : Zlib.Infback.lookup2 c dist = (xloopBrk (do
    let s ← ldInflateState c.st
    let tab : ConstCodePtr := if dist then s.distcode else s.lencode
    let last := (← get).last
    let b ← BITS (last.bits.toUInt32 + last.op.toUInt32)
    let sh ← shr32 b last.bits.toUInt32
    let here ← Ptr.index tab ((last.val.toUInt32 + sh).toNat : Int)
    modify fun l => { l with here := here }
    if (last.bits.toUInt32 + here.bits.toUInt32) <= (← get).bits then return true
    Zlib.Infback.PULLBYTE c
    return false)) := rfl

end Zlib.Infback.Equality
