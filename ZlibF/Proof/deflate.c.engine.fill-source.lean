import ZlibF.Proof.«deflate.c.engine.initial»

/-! # Source fragments of fill_window

All statements and their order are retained. The complete equality is
checked against the translated function before execution lemmas use them.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem fill_ite_bind {α β : Type} (c : Prop) [Decidable c] (a b : M α) (f : α → M β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

def fillPrime (s : DeflateStatePtr) : M Unit := do
  -- if (s->lookahead + s->insert >= MIN_MATCH) { ... }
  let d ← ldDeflateState s
  if d.lookahead + d.insert ≥ MIN_MATCH_u then
    let str : UInt32 := d.strstart - d.insert                    -- uInt str = s->strstart - s->insert;
    -- s->ins_h = s->window[str];
    let c0 ← index8 d.window str.toNat
    wr s (fun d => { d with ins_h := c0.toUInt32 })
    -- UPDATE_HASH(s, s->ins_h, s->window[str + 1]);
    UPDATE_HASH s (← index8 d.window (str + 1).toNat)
    -- while (s->insert) { ... }
    let (_, _) ← cwhile
      (fun (str, brk) => do
        let ins ← rd s (·.insert)
        pure (ins != 0 && !brk, (str, brk)))
      (fun (str, _brk) => do
        let d ← ldDeflateState s
        -- UPDATE_HASH(s, s->ins_h, s->window[str + MIN_MATCH-1]);
        UPDATE_HASH s (← index8 d.window (str + (MIN_MATCH_u - 1)).toNat)
        let d ← ldDeflateState s
        -- s->prev[str & s->w_mask] = s->head[s->ins_h];
        let v ← Ptr.index d.head d.ins_h.toNat
        Ptr.store (← padd d.prev (str &&& d.w_mask).toNat) v
        -- s->head[s->ins_h] = (Pos)str;
        Ptr.store (← padd d.head d.ins_h.toNat) str.toUInt16
        -- str++; s->insert--;
        let str := str + 1
        wr s (fun d => { d with insert := d.insert - 1 })
        -- if (s->lookahead + s->insert < MIN_MATCH) break;
        let d ← ldDeflateState s
        pure (str, d.lookahead + d.insert < MIN_MATCH_u))
      (str, false)

def fillBody (s : DeflateStatePtr) (wsize : UInt32) : Bool → M Bool := fun (_ : Bool) => do
      let d ← ldDeflateState s
      -- more = (unsigned)(s->window_size -(ulg)s->lookahead -(ulg)s->strstart);
      let mut more : UInt32 := (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toUInt32
      -- if (s->strstart >= wsize + MAX_DIST(s)) { ... }   (MAX_DIST(s) = w_size - MIN_LOOKAHEAD)
      if d.strstart ≥ wsize + (d.w_size - MIN_LOOKAHEAD_u) then
        -- zmemcpy(s->window, s->window + wsize, (unsigned)wsize - more);
        memcpyB d.window (← padd d.window wsize.toNat) (wsize - more).toNat
        wr s (fun d => { d with match_start := d.match_start - wsize }) -- s->match_start -= wsize;
        wr s (fun d => { d with strstart := d.strstart - wsize })       -- s->strstart -= wsize;
        let block_start ← lsub (← rd s (·.block_start)) wsize.toUInt64.toInt64
        wr s (fun d => { d with block_start })                         -- s->block_start -= (long) wsize;
        -- if (s->insert > s->strstart) s->insert = s->strstart;
        wr s (fun d => { d with insert := if d.insert > d.strstart then d.strstart else d.insert })
        slide_hash s
        more := more + wsize                                             -- more += wsize;
      -- if (s->strm->avail_in == 0) break;
      let strm ← rd s (·.strm)
      if (← zrd strm (·.avail_in)) == 0 then return true
      -- n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more);
      let d ← ldDeflateState s
      let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
      let n ← read_buf strm dst more
      wr s (fun d => { d with lookahead := d.lookahead + n })            -- s->lookahead += n;
      fillPrime s
      pure false

def fillCond (s : DeflateStatePtr) : Bool → M (Bool × Bool) := fun brk => do
      if brk then return (false, brk)
      -- while (s->lookahead < MIN_LOOKAHEAD && s->strm->avail_in != 0)
      let d ← ldDeflateState s
      if d.lookahead < MIN_LOOKAHEAD_u then
        return ((← zrd d.strm (·.avail_in)) != 0, brk)
      return (false, brk)

def fillHighWater (s : DeflateStatePtr) : M Unit := do
  -- if (s->high_water < s->window_size) { ... }
  let d ← ldDeflateState s
  if d.high_water < d.window_size then
    let curr : UInt64 := d.strstart.toUInt64 + d.lookahead.toUInt64   -- ulg curr = s->strstart + (ulg)(s->lookahead);
    if d.high_water < curr then
      -- init = s->window_size - curr; if (init > WIN_INIT) init = WIN_INIT;
      let mut init : UInt64 := d.window_size - curr
      if init > WIN_INIT_u then init := WIN_INIT_u
      -- zmemzero(s->window + curr, (unsigned)init);
      memsetB (← padd d.window curr.toNat) 0 init.toUInt32.toNat
      wr s (fun d => { d with high_water := curr + init })              -- s->high_water = curr + init;
    else if d.high_water < curr + WIN_INIT_u then
      -- init = (ulg)curr + WIN_INIT - s->high_water;
      let mut init : UInt64 := curr + WIN_INIT_u - d.high_water
      -- if (init > s->window_size - s->high_water) init = s->window_size - s->high_water;
      if init > d.window_size - d.high_water then init := d.window_size - d.high_water
      -- zmemzero(s->window + s->high_water, (unsigned)init);
      memsetB (← padd d.window d.high_water.toNat) 0 init.toUInt32.toNat
      wr s (fun d => { d with high_water := d.high_water + init })      -- s->high_water += init;

/-- `local void fill_window(deflate_state *s)`.
The complete source decomposition preserves every branch and loop. -/
theorem fill_window_source (s : DeflateStatePtr) : fill_window s = (do
    let wsize ← rd s (·.w_size)
    let _ ← cdoWhileBrk (fillWindowBody s wsize) (fillWindowCondition s) ()
    fillHighWater s) := rfl

/-- Without a slide or input, the C loop exits immediately. The entire remaining action is
    the original high-water padding, including its failure behavior. -/
theorem fill_window_no_input {h : Heap} {s : DeflateStatePtr} {d : DeflateState} {z : ZStream}
    (state : ldDeflateState s h = .ok (d, h)) (stream : ldZStream d.strm h = .ok (z, h))
    (noSlide : ¬d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (empty : z.avail_in = 0) :
    fill_window s h = fillHighWater s h := by
  have body : fillWindowBody s d.w_size () h = .ok (.brk (), h) := by
    simp [fillWindowBody, fillFromStream, bind_app, state, noSlide, rd, zrd, pure_app, stream, empty]
  have loop : cdoWhileBrk (fillWindowBody s d.w_size) (fillWindowCondition s) () h =
      .ok ((), h) := by
    unfold cdoWhileBrk cdoWhileCtrl
    rw [show fuel = (2^64-1)+1 by decide, cdoWhileCtrl.go]
    simp [bind_app, body, pure_app]
  rw [fill_window_source]
  simp only [rd, bind_app, state, pure_app, loop]

/-- Testing before the assignment and writing the clamped value agree on every heap. -/
theorem clampInsert_eq (s : DeflateStatePtr) :
    (do let d ← ldDeflateState s
        if d.insert > d.strstart then wr s (fun d => { d with insert := d.strstart })) =
      wr s (fun d => { d with insert := if d.insert > d.strstart then d.strstart else d.insert }) := by
  funext h
  cases s with
  | none => rfl
  | some r =>
    cases r with
    | tab i =>
      cases live : h.dstates i with
      | none => simp [wr, bind_app, ldDeflateState, DeflateStateRef.get, live]
      | some d =>
        by_cases need : d.insert > d.strstart
        · simp [wr, bind_app, ldDeflateState_tab live, need]
        · simp [wr, bind_app, ldDeflateState_tab live, need, stDeflateState_tab live, upd_self _ _ _ live]

/-- With no slide and no input, the previous flag-based loop and emitted loop have the same
    complete execution, including faults in the high-water padding. -/
theorem fill_empty_eq_legacy {h : Heap} {s : DeflateStatePtr} {d : DeflateState} {z : ZStream}
    (state : ldDeflateState s h = .ok (d, h)) (stream : ldZStream d.strm h = .ok (z, h))
    (noSlide : ¬d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (empty : z.avail_in = 0) :
    fill_window s h = (do
      let n ← rd s (·.w_size)
      let _ ← cdoWhile (fillBody s n) (fillCond s) false
      fillHighWater s) h := by
  rw [fill_window_no_input state stream noSlide empty]
  have body : fillBody s d.w_size false h = .ok (true, h) := by
    simp [fillBody, bind_app, state, noSlide, rd, zrd, pure_app, stream, empty]
  have loop : cdoWhile (fillBody s d.w_size) (fillCond s) false h = .ok (true, h) := by
    unfold cdoWhile
    rw [show fuel = (2^64-1)+1 by decide, cdoWhile.go]
    simp [bind_app, body, fillCond, pure_app]
  simp only [rd, bind_app, state, pure_app, loop]

end Zlib.Deflate.Engine.Proofs
