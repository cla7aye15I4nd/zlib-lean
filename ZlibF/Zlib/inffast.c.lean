import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Tables
import ZlibF.Zlib.«zutil.c»

/-!
# inffast.c — faithful translation

Source: `inffast.c`, default LP64 little-endian build (`Z_INFLATE_FETCH == 64` via `Z_UNALIGNED_FAST` and `Z_REG64`;
`ASMINF`, `INFLATE_STRICT`, `INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR`, and `Z_INFLATE_BYTES` are undefined, so the
64-bit fast loop, `load64`, `copy_back`, and fallback 8-bit loop are live, the `dmax` test and `ARRR` block are dead
and omitted). `Tracevv` and `TRACE_LITERAL` expand to nothing.

Mapping of the control flow (decision, per `docs/en/design/translation.md`):

* `do { ... } while (in <= last8 && out <= end8);` and `do { ... } while (in < last && out < end);` are `cdoWhile`;
  every `break` of the C leaves its loop *without* evaluating the condition, so the locals carry a flag `broke` and the
  condition is `false` when it is set.
* The labels `dolen8` / `dodist8` and `dolen` / `dodist` are the entry points of blocks; `goto` re-enters the same block
  via a `cdoWhile` whose flag (`againL`, `againD`) is cleared first.
* All loop-carried locals live in one record `L` (`hold` holds `hold8` during the 64-bit loop, and is masked back to
  `unsigned long` when leaving the 64-bit loop).

Decisions on the model: `unsigned long` and `unsigned` shifts fault for a count at or above the width; `load64` and
`zmemcpy(..., 8)` on LP64 little-endian read/store the eight little-endian bytes (`index8`/`store8`), and `zmemcpy`
between buffers is `memcpyB`; `in`, `out`, `from`, `last`, `end`, `beg`, `last8`, `end8` are `BPtr`s checked by the
runtime; the error strings are literals made by `Zlib.Zutil.strLit`; `strm->state` is cast to an inflate state.
-/

namespace Zlib.Inffast
open C

/-! ### Small checked operations -/

/-- `x << n` for `unsigned`: undefined if `n >= 32`. -/
def shl32 (x n : UInt32) : M UInt32 :=
  if n < 32 then pure (x <<< n) else ub "shift count out of range"

/-- `x << n` for `unsigned long`: undefined if `n >= 64`. -/
def shl64 (x n : UInt64) : M UInt64 :=
  if n < 64 then pure (x <<< n) else ub "shift count out of range"

/-- `x >> n` for `unsigned long`: undefined if `n >= 64`. -/
def shr64 (x n : UInt64) : M UInt64 :=
  if n < 64 then pure (x >>> n) else ub "shift count out of range"

/-- A `long` result: a fault if it does not fit. -/
def chk64 (v : Int) : M Int64 :=
  if -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807 then pure (Int64.ofInt v) else ub "signed integer overflow"

/-- `p - n` for a pointer and an `unsigned` count. -/
def subn (p : BPtr) (n : UInt32) : M BPtr := p.add (-(n.toNat : Int))

/-! ### The locals -/

/-- The local variables of `inflate_fast` that change during the loop. -/
structure L where
  in_ : BPtr
  out : BPtr
  hold : UInt64
  bits : UInt32
  here : CodePtr
  op : UInt32
  len : UInt32
  dist : UInt32
  from_ : BPtr
  broke : Bool
  againL : Bool
  againD : Bool

/-- What `inflate_fast` reads once and does not change. -/
structure Ctx where
  strm : ZStreamPtr
  state : InflateStatePtr
  last : BPtr
  beg : BPtr
  end_ : BPtr
  wsize : UInt32
  whave : UInt32
  wnext : UInt32
  window : BPtr
  lcode : CodePtr
  dcode : CodePtr
  lmask : UInt32
  dmask : UInt32

/-- `hold += (unsigned long)(*in++) << bits; bits += 8;` -/
def pull (l : L) : M L := do
  let b ← load8 l.in_
  let in_ ← l.in_.add 1
  let sh ← shl64 b.toUInt64 l.bits.toUInt64
  pure { l with in_, hold := l.hold + sh, bits := l.bits + 8 }

/-- `*out++ = *from++;` -/
def copy1 (l : L) : M L := do
  let b ← load8 l.from_
  let from_ ← l.from_.add 1
  store8 l.out b
  let out ← l.out.add 1
  pure { l with from_, out }

/-- `do { *out++ = *from++; } while (--op);` -/
def copyOp (l : L) : M L :=
  cdoWhile copy1 (fun l => let op := l.op - 1; pure (op != 0, { l with op })) l

/-- `strm->msg = (z_const char *)"..."; state->mode = BAD;` -/
def badData (c : Ctx) (msg : String) : M Unit := do
  let p ← Zlib.Zutil.strLit msg
  let st ← ldZStream c.strm
  stZStream c.strm { st with msg := p }
  let s ← ldInflateState c.state
  stInflateState c.state { s with mode := BAD }

/-- `load64(p)` on LP64 little-endian: reads eight bytes starting at `p` as a `UInt64`. -/
def load64 (p : BPtr) : M UInt64 := do
  let b0 ← index8 p 0
  let b1 ← index8 p 1
  let b2 ← index8 p 2
  let b3 ← index8 p 3
  let b4 ← index8 p 4
  let b5 ← index8 p 5
  let b6 ← index8 p 6
  let b7 ← index8 p 7
  pure (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
    (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))

/-- `zmemcpy(out, &v, 8)` on LP64 little-endian: stores eight bytes of `v` starting at `out`. -/
def store64 (out : BPtr) (v : UInt64) : M Unit := do
  store8 out (v &&& 0xff).toUInt8
  store8 (← out.add 1) ((v >>> 8) &&& 0xff).toUInt8
  store8 (← out.add 2) ((v >>> 16) &&& 0xff).toUInt8
  store8 (← out.add 3) ((v >>> 24) &&& 0xff).toUInt8
  store8 (← out.add 4) ((v >>> 32) &&& 0xff).toUInt8
  store8 (← out.add 5) ((v >>> 40) &&& 0xff).toUInt8
  store8 (← out.add 6) ((v >>> 48) &&& 0xff).toUInt8
  store8 (← out.add 7) ((v >>> 56) &&& 0xff).toUInt8

/-- `local unsigned char FAR *copy_back(unsigned char FAR *out, unsigned dist, unsigned len)`
(`Z_U8` defined, LP64 little-endian). -/
def copy_back (out : BPtr) (dist len : UInt32) : M BPtr := do
  -- unsigned char FAR *from = out - dist;
  let from_ ← subn out dist
  -- unsigned char FAR *stop = out + len;
  let stop ← out.add (len.toNat : Int)
  -- if (dist >= 16) { do { zmemcpy(out, from, 16); out += 16; from += 16; } while (out < stop); return stop; }
  if dist >= 16 then
    let _ ← cdoWhile
      (fun (out, from_) => do
        memcpyB out from_ 16
        let out ← out.add 16
        let from_ ← from_.add 16
        pure (out, from_))
      (fun (out, from_) => do pure (← Ptr.lt out stop, (out, from_)))
      (out, from_)
    return stop
  -- if (dist >= 8) { do { zmemcpy(out, from, 8); out += 8; from += 8; } while (out < stop); return stop; }
  if dist >= 8 then
    let _ ← cdoWhile
      (fun (out, from_) => do
        memcpyB out from_ 8
        let out ← out.add 8
        let from_ ← from_.add 8
        pure (out, from_))
      (fun (out, from_) => do pure (← Ptr.lt out stop, (out, from_)))
      (out, from_)
    return stop
  -- if (dist == 1) { Z_U8 run = *from; run |= run << 8; ... do { zmemcpy(out, &run, 8); out += 8; } while (out < stop); return stop; }
  if dist == 1 then
    let b ← load8 from_
    let mut run : UInt64 := b.toUInt64
    run := run ||| (run <<< 8)
    run := run ||| (run <<< 16)
    run := run ||| (run <<< 32)
    let _ ← cdoWhile
      (fun out => do
        store64 out run
        out.add 8)
      (fun out => do pure (← Ptr.lt out stop, out))
      out
    return stop
  -- do { Z_U8 v; zmemcpy(&v, from, 8); zmemcpy(out, &v, 8); out += dist; from += dist; } while (out < stop); return stop;
  let _ ← cdoWhile
    (fun (out, from_) => do
      let v ← load64 from_
      store64 out v
      let out ← out.add (dist.toNat : Int)
      let from_ ← from_.add (dist.toNat : Int)
      pure (out, from_))
    (fun (out, from_) => do pure (← Ptr.lt out stop, (out, from_)))
    (out, from_)
  return stop

/-- Refill in the 64-bit loop: `hold8 |= load64(in) << bits; in += (63 - bits) >> 3; bits |= 56;`. -/
def refill64 (l : L) : M L := do
  let w ← load64 l.in_
  let sh ← shl64 w l.bits.toUInt64
  let in_ ← l.in_.add (((63 - l.bits) >>> 3).toNat : Int)
  pure { l with in_, hold := l.hold ||| sh, bits := l.bits ||| 56 }

/-- The tail of the distance block in the 64-bit loop, from `if (dist > op)`: copies the match via `zmemcpy`
from the window and `copy_back`. `dist` and `len` are set; `op = out - beg`. -/
def copyMatch8 (c : Ctx) (l : L) : M L := do
  let mut l := l
  -- if (dist > op) {                /* see if copy from window */
  if l.dist > l.op then
    -- op = dist - op;             /* distance back in window */
    l := { l with op := l.dist - l.op }
    -- if (op > whave) {
    if l.op > c.whave then
      -- if (state->sane) { strm->msg = "invalid distance too far back"; state->mode = BAD; break; }
      let s ← ldInflateState c.state
      if s.sane != 0 then
        badData c "invalid distance too far back"
        return { l with broke := true }
      -- (INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR is not defined)
    -- from = window;
    l := { l with from_ := c.window }
    -- if (wnext == 0)             /* very common case */
    if c.wnext == 0 then
      -- from += wsize - op;
      l := { l with from_ := ← l.from_.add (c.wsize - l.op).toNat }
    -- else if (wnext < op) {      /* wrap around window */
    else if c.wnext < l.op then
      -- from += wsize + wnext - op;
      l := { l with from_ := ← l.from_.add (c.wsize + c.wnext - l.op).toNat }
      -- op -= wnext;
      l := { l with op := l.op - c.wnext }
      -- if (op < len) {         /* some end of window, then start */
      if l.op < l.len then
        -- zmemcpy(out, from, op); out += op; len -= op; from = window; op = wnext;
        memcpyB l.out l.from_ l.op.toNat
        l := { l with out := ← l.out.add l.op.toNat, len := l.len - l.op, from_ := c.window, op := c.wnext }
    -- else                        /* contiguous in window */
    else
      -- from += wnext - op;
      l := { l with from_ := ← l.from_.add (c.wnext - l.op).toNat }
    -- if (op > len) op = len;
    if l.op > l.len then
      l := { l with op := l.len }
    -- zmemcpy(out, from, op);     /* from the window */
    memcpyB l.out l.from_ l.op.toNat
    -- out += op; len -= op;
    l := { l with out := ← l.out.add l.op.toNat, len := l.len - l.op }
    -- if (len) out = copy_back(out, dist, len);
    if l.len != 0 then
      l := { l with out := ← copy_back l.out l.dist l.len }
  else
    -- out = copy_back(out, dist, len);
    l := { l with out := ← copy_back l.out l.dist l.len }
  pure l

/-- The block starting at `dodist8:` in the 64-bit loop. Sets `againD` for `goto dodist8`, `broke` for `break`. -/
def dodist8 (c : Ctx) (l : L) : M L := do
  let mut l := { l with againD := false }
  -- op = (unsigned)(here->bits);
  let e ← l.here.load
  l := { l with op := e.bits.toUInt32 }
  -- hold8 >>= op; bits -= op;
  l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
  l := { l with bits := l.bits - l.op }
  -- op = (unsigned)(here->op);
  let e ← l.here.load
  l := { l with op := e.op.toUInt32 }
  -- if (op & 16) {                  /* distance base */
  if l.op &&& 16 != 0 then
    -- dist = (unsigned)(here->val);
    let e ← l.here.load
    l := { l with dist := e.val.toUInt32 }
    -- op &= 15;                   /* number of extra bits */
    l := { l with op := l.op &&& 15 }
    -- dist += (unsigned)hold8 & ((1U << op) - 1);
    let m ← shl32 1 l.op
    l := { l with dist := l.dist + (l.hold.toUInt32 &&& (m - 1)) }
    -- (INFLATE_STRICT is not defined)
    -- hold8 >>= op; bits -= op;
    l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
    l := { l with bits := l.bits - l.op }
    -- op = (unsigned)(out - beg); /* max distance in output */
    let d ← l.out.diff c.beg
    l := { l with op := d.toUInt64.toUInt32 }
    copyMatch8 c l
  -- else if ((op & 64) == 0) {      /* 2nd level distance code */
  else if l.op &&& 64 == 0 then
    -- here = dcode + here->val + (hold8 & ((1U << op) - 1));
    let e ← l.here.load
    let h1 ← c.dcode.add e.val.toNat
    let m ← shl32 1 l.op
    let here ← h1.add (l.hold &&& (m - 1).toUInt64).toNat
    -- goto dodist8;
    pure { l with here, againD := true }
  else
    -- strm->msg = "invalid distance code"; state->mode = BAD; break;
    badData c "invalid distance code"
    pure { l with broke := true }

/-- The block starting at `dolen8:` in the 64-bit loop. Sets `againL` for `goto dolen8`, `broke` for `break`. -/
def dolen8 (c : Ctx) (l : L) : M L := do
  let mut l := { l with againL := false }
  -- op = (unsigned)(here->bits);
  let e ← l.here.load
  l := { l with op := e.bits.toUInt32 }
  -- hold8 >>= op; bits -= op;
  l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
  l := { l with bits := l.bits - l.op }
  -- op = (unsigned)(here->op);
  let e ← l.here.load
  l := { l with op := e.op.toUInt32 }
  -- if (op == 0) {                      /* literal */
  if l.op == 0 then
    -- *out++ = (unsigned char)(here->val);
    let e ← l.here.load
    store8 l.out e.val.toUInt8
    pure { l with out := ← l.out.add 1 }
  -- else if (op & 16) {                 /* length base */
  else if l.op &&& 16 != 0 then
    -- len = (unsigned)(here->val);
    let e ← l.here.load
    l := { l with len := e.val.toUInt32 }
    -- op &= 15;                       /* number of extra bits */
    l := { l with op := l.op &&& 15 }
    -- len += (unsigned)hold8 & ((1U << op) - 1);
    let m ← shl32 1 l.op
    l := { l with len := l.len + (l.hold.toUInt32 &&& (m - 1)) }
    -- hold8 >>= op; bits -= op;
    l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
    l := { l with bits := l.bits - l.op }
    -- here = dcode + (hold8 & dmask);
    l := { l with here := ← c.dcode.add (l.hold &&& c.dmask.toUInt64).toNat }
    -- dodist8: ...
    cdoWhile (dodist8 c) (fun l => pure (l.againD, l)) l
  -- else if ((op & 64) == 0) {          /* 2nd level length code */
  else if l.op &&& 64 == 0 then
    -- here = lcode + here->val + (hold8 & ((1U << op) - 1));
    let e ← l.here.load
    let h1 ← c.lcode.add e.val.toNat
    let m ← shl32 1 l.op
    let here ← h1.add (l.hold &&& (m - 1).toUInt64).toNat
    -- goto dolen8;
    pure { l with here, againL := true }
  -- else if (op & 32) {                 /* end-of-block */
  else if l.op &&& 32 != 0 then
    -- state->mode = TYPE; break;
    let s ← ldInflateState c.state
    stInflateState c.state { s with mode := TYPE }
    pure { l with broke := true }
  else
    -- strm->msg = "invalid literal/length code"; state->mode = BAD; break;
    badData c "invalid literal/length code"
    pure { l with broke := true }

/-- One pass of the body of the 64-bit `do ... while (in <= last8 && out <= end8)` loop (`Z_INFLATE_FETCH == 64`). -/
def inflate_fast_body8 (c : Ctx) (l : L) : M L := do
  -- hold8 |= load64(in) << bits; in += (63 - bits) >> 3; bits |= 56;
  let l ← refill64 l
  -- here = lcode + (hold8 & lmask);
  let here ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat
  let mut l := { l with here }
  -- if (here->op == 0) {        /* up to three literals a refill */
  let e ← l.here.load
  if e.op == 0 then
    -- hold8 >>= here->bits; bits -= here->bits; *out++ = (unsigned char)(here->val);
    let hold ← shr64 l.hold e.bits.toUInt64
    let bits := l.bits - e.bits.toUInt32
    store8 l.out e.val.toUInt8
    let out ← l.out.add 1
    -- here = lcode + (hold8 & lmask);
    let here ← c.lcode.add (hold &&& c.lmask.toUInt64).toNat
    l := { l with hold, bits, out, here }
    -- if (here->op == 0) {
    let e ← l.here.load
    if e.op == 0 then
      -- hold8 >>= here->bits; bits -= here->bits; *out++ = (unsigned char)(here->val);
      let hold ← shr64 l.hold e.bits.toUInt64
      let bits := l.bits - e.bits.toUInt32
      store8 l.out e.val.toUInt8
      let out ← l.out.add 1
      -- here = lcode + (hold8 & lmask);
      let here ← c.lcode.add (hold &&& c.lmask.toUInt64).toNat
      l := { l with hold, bits, out, here }
      -- if (here->op == 0) {
      let e ← l.here.load
      if e.op == 0 then
        -- hold8 >>= here->bits; bits -= here->bits; *out++ = (unsigned char)(here->val); continue;
        let hold ← shr64 l.hold e.bits.toUInt64
        let bits := l.bits - e.bits.toUInt32
        store8 l.out e.val.toUInt8
        let out ← l.out.add 1
        return { l with hold, bits, out }
    -- hold8 |= load64(in) << bits; in += (63 - bits) >> 3; bits |= 56;
    l ← refill64 l
  -- dolen8: ...
  cdoWhile (dolen8 c) (fun l => pure (l.againL, l)) l

/-- The tail of the distance block, from the test `if (dist > op)`: copy the match. `dist` and `len` are set;
`op = out - beg`. -/
def copyMatch (c : Ctx) (l : L) : M L := do
  let mut l := l
  -- if (dist > op) {                /* see if copy from window */
  if l.dist > l.op then
    -- op = dist - op;             /* distance back in window */
    l := { l with op := l.dist - l.op }
    -- if (op > whave) {
    if l.op > c.whave then
      -- if (state->sane) { strm->msg = "invalid distance too far back"; state->mode = BAD; break; }
      let s ← ldInflateState c.state
      if s.sane != 0 then
        badData c "invalid distance too far back"
        return { l with broke := true }
      -- (INFLATE_ALLOW_INVALID_DISTANCE_TOOFAR_ARRR is not defined)
    -- from = window;
    l := { l with from_ := c.window }
    -- if (wnext == 0) {           /* very common case */
    if c.wnext == 0 then
      -- from += wsize - op;
      l := { l with from_ := ← l.from_.add (c.wsize - l.op).toNat }
      -- if (op < len) {         /* some from window */
      if l.op < l.len then
        -- len -= op; do { *out++ = *from++; } while (--op); from = out - dist;
        l := { l with len := l.len - l.op }
        l ← copyOp l
        l := { l with from_ := ← subn l.out l.dist }
    -- else if (wnext < op) {      /* wrap around window */
    else if c.wnext < l.op then
      -- from += wsize + wnext - op;
      l := { l with from_ := ← l.from_.add (c.wsize + c.wnext - l.op).toNat }
      -- op -= wnext;
      l := { l with op := l.op - c.wnext }
      -- if (op < len) {         /* some from end of window */
      if l.op < l.len then
        -- len -= op; do { *out++ = *from++; } while (--op); from = window;
        l := { l with len := l.len - l.op }
        l ← copyOp l
        l := { l with from_ := c.window }
        -- if (wnext < len) {  /* some from start of window */
        if c.wnext < l.len then
          -- op = wnext; len -= op; do { *out++ = *from++; } while (--op); from = out - dist;
          l := { l with op := c.wnext }
          l := { l with len := l.len - l.op }
          l ← copyOp l
          l := { l with from_ := ← subn l.out l.dist }
    -- else {                      /* contiguous in window */
    else
      -- from += wnext - op;
      l := { l with from_ := ← l.from_.add (c.wnext - l.op).toNat }
      -- if (op < len) {         /* some from window */
      if l.op < l.len then
        -- len -= op; do { *out++ = *from++; } while (--op); from = out - dist;
        l := { l with len := l.len - l.op }
        l ← copyOp l
        l := { l with from_ := ← subn l.out l.dist }
    -- while (len > 2) { *out++ = *from++; *out++ = *from++; *out++ = *from++; len -= 3; }
    l ← cwhile (fun l => pure (l.len > 2, l))
      (fun l => do
        let l ← copy1 l
        let l ← copy1 l
        let l ← copy1 l
        pure { l with len := l.len - 3 }) l
    -- if (len) { *out++ = *from++; if (len > 1) *out++ = *from++; }
    if l.len != 0 then
      l ← copy1 l
      if l.len > 1 then l ← copy1 l
  -- else {
  else
    -- from = out - dist;          /* copy direct from output */
    l := { l with from_ := ← subn l.out l.dist }
    -- do { *out++ = *from++; *out++ = *from++; *out++ = *from++; len -= 3; } while (len > 2);
    l ← cdoWhile
      (fun l => do
        let l ← copy1 l
        let l ← copy1 l
        let l ← copy1 l
        pure { l with len := l.len - 3 })
      (fun l => pure (l.len > 2, l)) l
    -- if (len) { *out++ = *from++; if (len > 1) *out++ = *from++; }
    if l.len != 0 then
      l ← copy1 l
      if l.len > 1 then l ← copy1 l
  pure l

/-- The block that starts at the label `dodist:`. Sets `againD` for `goto dodist`, `broke` for `break`. -/
def dodist (c : Ctx) (l : L) : M L := do
  let mut l := { l with againD := false }
  -- op = (unsigned)(here->bits);
  let e ← l.here.load
  l := { l with op := e.bits.toUInt32 }
  -- hold >>= op; bits -= op;
  l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
  l := { l with bits := l.bits - l.op }
  -- op = (unsigned)(here->op);
  let e ← l.here.load
  l := { l with op := e.op.toUInt32 }
  -- if (op & 16) {                      /* distance base */
  if l.op &&& 16 != 0 then
    -- dist = (unsigned)(here->val);
    let e ← l.here.load
    l := { l with dist := e.val.toUInt32 }
    -- op &= 15;                       /* number of extra bits */
    l := { l with op := l.op &&& 15 }
    -- if (bits < op) { hold += ... ; bits += 8; if (bits < op) { hold += ...; bits += 8; } }
    if l.bits < l.op then
      l ← pull l
      if l.bits < l.op then
        l ← pull l
    -- dist += (unsigned)hold & ((1U << op) - 1);
    let m ← shl32 1 l.op
    l := { l with dist := l.dist + (l.hold.toUInt32 &&& (m - 1)) }
    -- (INFLATE_STRICT is not defined)
    -- hold >>= op; bits -= op;
    l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
    l := { l with bits := l.bits - l.op }
    -- op = (unsigned)(out - beg);     /* max distance in output */
    let d ← l.out.diff c.beg
    l := { l with op := d.toUInt64.toUInt32 }
    copyMatch c l
  -- else if ((op & 64) == 0) {          /* 2nd level distance code */
  else if l.op &&& 64 == 0 then
    -- here = dcode + here->val + (hold & ((1U << op) - 1));
    let e ← l.here.load
    let h1 ← c.dcode.add e.val.toNat
    let m ← shl32 1 l.op
    let here ← h1.add (l.hold &&& (m - 1).toUInt64).toNat
    -- goto dodist;
    pure { l with here, againD := true }
  else
    -- strm->msg = "invalid distance code"; state->mode = BAD; break;
    badData c "invalid distance code"
    pure { l with broke := true }

/-- The block that starts at the label `dolen:`. Sets `againL` for `goto dolen`, `broke` for `break`. -/
def dolen (c : Ctx) (l : L) : M L := do
  let mut l := { l with againL := false }
  -- op = (unsigned)(here->bits);
  let e ← l.here.load
  l := { l with op := e.bits.toUInt32 }
  -- hold >>= op; bits -= op;
  l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
  l := { l with bits := l.bits - l.op }
  -- op = (unsigned)(here->op);
  let e ← l.here.load
  l := { l with op := e.op.toUInt32 }
  -- if (op == 0) {                          /* literal */
  if l.op == 0 then
    -- *out++ = (unsigned char)(here->val);
    let e ← l.here.load
    store8 l.out e.val.toUInt8
    pure { l with out := ← l.out.add 1 }
  -- else if (op & 16) {                     /* length base */
  else if l.op &&& 16 != 0 then
    -- len = (unsigned)(here->val);
    let e ← l.here.load
    l := { l with len := e.val.toUInt32 }
    -- op &= 15;                           /* number of extra bits */
    l := { l with op := l.op &&& 15 }
    -- if (op) {
    if l.op != 0 then
      -- if (bits < op) { hold += (unsigned long)(*in++) << bits; bits += 8; }
      if l.bits < l.op then l ← pull l
      -- len += (unsigned)hold & ((1U << op) - 1);
      let m ← shl32 1 l.op
      l := { l with len := l.len + (l.hold.toUInt32 &&& (m - 1)) }
      -- hold >>= op; bits -= op;
      l := { l with hold := ← shr64 l.hold l.op.toUInt64 }
      l := { l with bits := l.bits - l.op }
    -- if (bits < 15) { two pulls }
    if l.bits < 15 then
      l ← pull l
      l ← pull l
    -- here = dcode + (hold & dmask);
    l := { l with here := ← c.dcode.add (l.hold &&& c.dmask.toUInt64).toNat }
    -- dodist: ...
    cdoWhile (dodist c) (fun l => pure (l.againD, l)) l
  -- else if ((op & 64) == 0) {              /* 2nd level length code */
  else if l.op &&& 64 == 0 then
    -- here = lcode + here->val + (hold & ((1U << op) - 1));
    let e ← l.here.load
    let h1 ← c.lcode.add e.val.toNat
    let m ← shl32 1 l.op
    let here ← h1.add (l.hold &&& (m - 1).toUInt64).toNat
    -- goto dolen;
    pure { l with here, againL := true }
  -- else if (op & 32) {                     /* end-of-block */
  else if l.op &&& 32 != 0 then
    -- state->mode = TYPE; break;
    let s ← ldInflateState c.state
    stInflateState c.state { s with mode := TYPE }
    pure { l with broke := true }
  else
    -- strm->msg = "invalid literal/length code"; state->mode = BAD; break;
    badData c "invalid literal/length code"
    pure { l with broke := true }

/-- One pass of the body of the `do ... while` loop of `inflate_fast`. -/
def inflate_fast_body (c : Ctx) (l : L) : M L := do
  let mut l := l
  -- if (bits < 15) { hold += (unsigned long)(*in++) << bits; bits += 8; (twice) }
  if l.bits < 15 then
    l ← pull l
    l ← pull l
  -- here = lcode + (hold & lmask);
  l := { l with here := ← c.lcode.add (l.hold &&& c.lmask.toUInt64).toNat }
  -- dolen: ...
  cdoWhile (dolen c) (fun l => pure (l.againL, l)) l

/-- `void ZLIB_INTERNAL inflate_fast(z_streamp strm, unsigned start)` -/
def inflate_fast (strm : ZStreamPtr) (start : UInt32) : M (CHidden Unit) := do
  -- state = (struct inflate_state FAR *)strm->state;
  let sm ← ldZStream strm
  let state ← castInflateState sm.state
  -- in = strm->next_in;
  let in_ := sm.next_in
  -- last = in + (strm->avail_in - 5);
  let last ← in_.add (sm.avail_in - 5).toNat
  -- out = strm->next_out;
  let out := sm.next_out
  -- beg = out - (start - strm->avail_out);
  let beg ← subn out (start - sm.avail_out)
  -- end = out + (strm->avail_out - 257);
  let end_ ← out.add (sm.avail_out - 257).toNat
  -- wsize = state->wsize; whave = state->whave; wnext = state->wnext; window = state->window;
  -- hold = state->hold; bits = state->bits; lcode = state->lencode; dcode = state->distcode;
  let s ← ldInflateState state
  -- back = window != Z_NULL && out + strm->avail_out == window + wsize;
  let back : Bool ←
    if s.window != .null then do
      let outEnd ← out.add (sm.avail_out.toNat : Int)
      let winEnd ← s.window.add (s.wsize.toNat : Int)
      pure (outEnd == winEnd)
    else pure false
  -- lmask = (1U << state->lenbits) - 1;
  let lmask := (← shl32 1 s.lenbits) - 1
  -- dmask = (1U << state->distbits) - 1;
  let dmask := (← shl32 1 s.distbits) - 1
  let c : Ctx := { strm, state, last, beg, end_, wsize := s.wsize, whave := s.whave, wnext := s.wnext,
                   window := s.window, lcode := s.lencode, dcode := s.distcode, lmask, dmask }
  let l : L := { in_, out, hold := s.hold, bits := s.bits, here := default, op := 0, len := 0, dist := 0,
                 from_ := default, broke := false, againL := false, againD := false }
  -- if (!back && strm->avail_in >= 16 && strm->avail_out >= 2 + 258 + 15) { ... }
  let (l, skip8) ←
    if !back && sm.avail_in >= 16 && sm.avail_out >= 2 + 258 + 15 then
      let last8 ← in_.add (sm.avail_in - 16).toNat
      let end8 ← out.add (sm.avail_out - (2 + 258 + 15)).toNat
      let l ← cdoWhile (inflate_fast_body8 c)
        (fun l => do
          if l.broke then pure (false, l)
          else if ← Ptr.le l.in_ last8 then pure (← Ptr.le l.out end8, l)
          else pure (false, l)) l
      let len := l.bits >>> 3
      let in_ ← subn l.in_ len
      let bits := l.bits - (len <<< 3)
      let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
      let l := { l with in_, bits, hold, len }
      let st ← ldInflateState state
      let skip8 ←
        if st.mode != LEN then pure true
        else pure !(← Ptr.lt l.out end_)
      pure (l, skip8)
    else
      pure (l, false)
  -- do { ... } while (in < last && out < end);
  let l ←
    if skip8 then pure l
    else
      cdoWhile (inflate_fast_body c)
        (fun l => do
          -- a `break` leaves the loop without evaluating the condition
          if l.broke then pure (false, l)
          else if ← Ptr.lt l.in_ c.last then pure (← Ptr.lt l.out c.end_, l)
          else pure (false, l)) l
  -- leave:
  -- len = bits >> 3;
  let len := l.bits >>> 3
  -- in -= len;
  let in_ ← subn l.in_ len
  -- bits -= len << 3;
  let bits := l.bits - (len <<< 3)
  -- hold &= (1U << bits) - 1;
  let hold := l.hold &&& ((← shl32 1 bits) - 1).toUInt64
  -- strm->next_in = in; strm->next_out = out;
  -- strm->avail_in = (unsigned)(in < last ? 5 + (last - in) : 5 - (in - last));
  let ai : Int64 ←
    if ← Ptr.lt in_ last then do let d ← last.diff in_; chk64 (5 + d.toInt)
    else do let d ← in_.diff last; chk64 (5 - d.toInt)
  -- strm->avail_out = (unsigned)(out < end ? 257 + (end - out) : 257 - (out - end));
  let ao : Int64 ←
    if ← Ptr.lt l.out end_ then do let d ← end_.diff l.out; chk64 (257 + d.toInt)
    else do let d ← l.out.diff end_; chk64 (257 - d.toInt)
  let sm ← ldZStream strm
  stZStream strm { sm with next_in := in_, next_out := l.out, avail_in := ai.toUInt64.toUInt32,
                           avail_out := ao.toUInt64.toUInt32 }
  -- state->hold = hold; state->bits = bits;
  let s ← ldInflateState state
  stInflateState state { s with hold, bits }

/-! ### Exact-shape C-ABI companions (`load64_c`, `copy_back_c`, `inflate_fast_c`) -/

/-- Exact C-shaped `load64`: `unsigned long v; memcpy(&v, p, 8); return v;`. -/
def load64_c (p : ConstBPtr) : M (COrder 1 (CStaticAs "load64" UInt64)) := do
  let v ← memcpyLoad64 p
  return v

/-- Locals of `copy_back` in exact upstream C declaration order (`out` reuses the parameter). -/
structure CopyBackLocals where
  from_ : BPtr
  stop : BPtr
  out : BPtr

/-- Exact C-shaped `copy_back`: uses `memcpy` (`align 1`), preserving branch and loop order. -/
def copy_back_c (out : BPtr) (dist len : UInt32) : M (COrder 2 (CStaticAs "copy_back" BPtr)) := do
  let from0 ← cinline (subn out dist)
  let stop0 ← cinline (out.add (len.toNat : Int))
  let l ← cdecl ({ from_ := from0, stop := stop0, out } : CopyBackLocals)
  if dist >= 16 then
    let _ ← cdoWhile
      (fun (l : CopyBackLocals) => do
        memcpyB l.out l.from_ 16
        let out1 ← cinline (l.out.add 16)
        let from1 ← cinline (l.from_.add 16)
        let l := { l with out := out1 }
        pure { l with from_ := from1 })
      (fun (l : CopyBackLocals) => do pure (← Ptr.lt l.out l.stop, l))
      l
    return l.stop
  if dist >= 8 then
    let _ ← cdoWhile
      (fun (l : CopyBackLocals) => do
        memcpyB l.out l.from_ 8
        let out1 ← cinline (l.out.add 8)
        let from1 ← cinline (l.from_.add 8)
        let l := { l with out := out1 }
        pure { l with from_ := from1 })
      (fun (l : CopyBackLocals) => do pure (← Ptr.lt l.out l.stop, l))
      l
    return l.stop
  if dist == 1 then
    let b ← cinline (load8 l.from_)
    let mut run : UInt64 := b.toUInt64
    run := run ||| (run <<< 8)
    run := run ||| (run <<< 16)
    run := run ||| (run <<< 32)
    let _ ← cdoWhile
      (fun (l : CopyBackLocals) => do
        memcpyStore64 l.out run
        let out1 ← cinline (l.out.add 8)
        pure { l with out := out1 })
      (fun (l : CopyBackLocals) => do pure (← Ptr.lt l.out l.stop, l))
      l
    return l.stop
  let _ ← cdoWhile
    (fun (l : CopyBackLocals) => do
      let v ← memcpyLoad64 l.from_
      memcpyStore64 l.out v
      let out1 ← cinline (l.out.add (dist.toNat : Int))
      let from1 ← cinline (l.from_.add (dist.toNat : Int))
      let l := { l with out := out1 }
      pure { l with from_ := from1 })
    (fun (l : CopyBackLocals) => do pure (← Ptr.lt l.out l.stop, l))
    l
  return l.stop

/-- Locals of `inflate_fast` in exact upstream C declaration order. -/
structure InflateFastLocals where
  state : InflateStatePtr
  in_ : ConstBPtr
  last : ConstBPtr
  out : BPtr
  beg : BPtr
  end_ : BPtr
  wsize : UInt32
  whave : UInt32
  wnext : UInt32
  window : BPtr
  back : Bool
  hold : UInt64
  bits : UInt32
  lcode : ConstCodePtr
  dcode : ConstCodePtr
  lmask : UInt32
  dmask : UInt32
  here : ConstCodePtr
  op : UInt32
  len : UInt32
  dist : UInt32
  from_ : BPtr
  hold8 : UInt64
  last8 : ConstBPtr
  end8 : BPtr

/-- Helper: `strm->msg = ...; state->mode = BAD;` for C-shaped `inflate_fast_c`. -/
def badDataC (strm : ZStreamPtr) (state : InflateStatePtr) (msg : String) : M Unit := do
  let p ← Zlib.Zutil.strLit msg
  let st ← ldZStream strm
  stZStream strm { st with msg := p }
  let s ← ldInflateState state
  stInflateState state { s with mode := BAD }

/-- Match copy tail inside the 64-bit loop (`dolen8` / `dodist8`), calling `copy_back`. -/
def copyMatch8C (strm : ZStreamPtr) (l : InflateFastLocals) :
    M (LoopStep InflateFastLocals Empty) := do
  let mut l := l
  if l.dist > l.op then
    l := { l with op := l.dist - l.op }
    if l.op > l.whave then
      let s ← ldInflateState l.state
      if s.sane != 0 then
        badDataC strm l.state "invalid distance too far back"
        return .brk l
    l := { l with from_ := l.window }
    if l.wnext == 0 then
      let f1 ← cinline (l.from_.add (l.wsize - l.op).toNat)
      l := { l with from_ := f1 }
    else if l.wnext < l.op then
      let f1 ← cinline (l.from_.add (l.wsize + l.wnext - l.op).toNat)
      l := { l with from_ := f1 }
      l := { l with op := l.op - l.wnext }
      if l.op < l.len then
        memcpyB l.out l.from_ l.op.toNat
        let o1 ← cinline (l.out.add l.op.toNat)
        l := { l with out := o1, len := l.len - l.op, from_ := l.window }
        l := { l with op := l.wnext }
    else
      let f1 ← cinline (l.from_.add (l.wnext - l.op).toNat)
      l := { l with from_ := f1 }
    if l.op > l.len then
      l := { l with op := l.len }
    memcpyB l.out l.from_ l.op.toNat
    let o1 ← cinline (l.out.add l.op.toNat)
    l := { l with out := o1, len := l.len - l.op }
    if l.len != 0 then
      let o2 ← cinline (copy_back_c l.out l.dist l.len)
      l := { l with out := o2 }
  else
    let o2 ← cinline (copy_back_c l.out l.dist l.len)
    l := { l with out := o2 }
  return .next l

/-- `dodist8:` label block inside the 64-bit fast loop. -/
def dodist8BodyC (strm : ZStreamPtr) (l : InflateFastLocals) :
    M (GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty)) := do
  let mut l := l
  let e ← cinline l.here.load
  l := { l with op := e.bits.toUInt32 }
  let h1 ← cinline (shr64 l.hold8 l.op.toUInt64)
  l := { l with hold8 := h1 }
  l := { l with bits := l.bits - l.op }
  let e ← cinline l.here.load
  l := { l with op := e.op.toUInt32 }
  if l.op &&& 16 != 0 then
    let e ← cinline l.here.load
    l := { l with dist := e.val.toUInt32 }
    l := { l with op := l.op &&& 15 }
    let m ← cinline (shl32 1 l.op)
    l := { l with dist := l.dist + (l.hold8.toUInt32 &&& (m - 1)) }
    let h2 ← cinline (shr64 l.hold8 l.op.toUInt64)
    l := { l with hold8 := h2 }
    l := { l with bits := l.bits - l.op }
    let d ← cinline (l.out.diff l.beg)
    l := { l with op := d.toUInt64.toUInt32 }
    let step ← copyMatch8C strm l
    return .done step
  else if l.op &&& 64 == 0 then
    let e ← cinline l.here.load
    let m ← cinline (shl32 1 l.op)
    let here1 ← cinline (do
      let h1 ← l.dcode.add e.val.toNat
      h1.add (l.hold8 &&& (m - 1).toUInt64).toNat)
    return .goto { l with here := here1 }
  else
    badDataC strm l.state "invalid distance code"
    return .done (.brk l)

/-- `dolen8:` label block inside the 64-bit fast loop. -/
def dolen8BodyC (strm : ZStreamPtr) (l : InflateFastLocals) :
    M (GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty)) := do
  let mut l := l
  let e ← cinline l.here.load
  l := { l with op := e.bits.toUInt32 }
  let h1 ← cinline (shr64 l.hold8 l.op.toUInt64)
  l := { l with hold8 := h1 }
  l := { l with bits := l.bits - l.op }
  let e ← cinline l.here.load
  l := { l with op := e.op.toUInt32 }
  if l.op == 0 then
    let e ← cinline l.here.load
    store8 l.out e.val.toUInt8
    let out1 ← cinline (l.out.add 1)
    return .done (.next { l with out := out1 })
  else if l.op &&& 16 != 0 then
    let e ← cinline l.here.load
    l := { l with len := e.val.toUInt32 }
    l := { l with op := l.op &&& 15 }
    let m ← cinline (shl32 1 l.op)
    l := { l with len := l.len + (l.hold8.toUInt32 &&& (m - 1)) }
    let h2 ← cinline (shr64 l.hold8 l.op.toUInt64)
    l := { l with hold8 := h2 }
    l := { l with bits := l.bits - l.op }
    let here1 ← cinline (l.dcode.add (l.hold8 &&& l.dmask.toUInt64).toNat)
    l := { l with here := here1 }
    let step ← clabel "dodist8" (dodist8BodyC strm) l
    return .done step
  else if l.op &&& 64 == 0 then
    let e ← cinline l.here.load
    let m ← cinline (shl32 1 l.op)
    let here1 ← cinline (do
      let h1 ← l.lcode.add e.val.toNat
      h1.add (l.hold8 &&& (m - 1).toUInt64).toNat)
    return .goto { l with here := here1 }
  else if l.op &&& 32 != 0 then
    let s ← ldInflateState l.state
    stInflateState l.state { s with mode := TYPE }
    return .done (.brk l)
  else
    badDataC strm l.state "invalid literal/length code"
    return .done (.brk l)

/-- Byte copy loop `do { *out++ = *from++; } while (--op);` over `InflateFastLocals`. -/
def copyOpC (l : InflateFastLocals) : M InflateFastLocals :=
  cdoWhile
    (fun (l : InflateFastLocals) => do
      let (out1, from1) ← copyBytePostInc l.out l.from_
      pure { l with out := out1, from_ := from1 })
    (fun (l : InflateFastLocals) => let op := l.op - 1; pure (op != 0, { l with op }))
    l

/-- Match copy tail inside the 8-bit fallback loop (`dolen` / `dodist`). -/
def copyMatchC (strm : ZStreamPtr) (l : InflateFastLocals) :
    M (LoopStep InflateFastLocals Empty) := do
  let mut l := l
  if l.dist > l.op then
    l := { l with op := l.dist - l.op }
    if l.op > l.whave then
      let s ← ldInflateState l.state
      if s.sane != 0 then
        badDataC strm l.state "invalid distance too far back"
        return .brk l
    l := { l with from_ := l.window }
    if l.wnext == 0 then
      let f1 ← cinline (l.from_.add (l.wsize - l.op).toNat)
      l := { l with from_ := f1 }
      if l.op < l.len then
        l := { l with len := l.len - l.op }
        l ← copyOpC l
        let f2 ← cinline (subn l.out l.dist)
        l := { l with from_ := f2 }
    else if l.wnext < l.op then
      let f1 ← cinline (l.from_.add (l.wsize + l.wnext - l.op).toNat)
      l := { l with from_ := f1 }
      l := { l with op := l.op - l.wnext }
      if l.op < l.len then
        l := { l with len := l.len - l.op }
        l ← copyOpC l
        l := { l with from_ := l.window }
        if l.wnext < l.len then
          l := { l with op := l.wnext, len := l.len - l.wnext }
          l ← copyOpC l
          let f2 ← cinline (subn l.out l.dist)
          l := { l with from_ := f2 }
    else
      let f1 ← cinline (l.from_.add (l.wnext - l.op).toNat)
      l := { l with from_ := f1 }
      if l.op < l.len then
        l := { l with len := l.len - l.op }
        l ← copyOpC l
        let f2 ← cinline (subn l.out l.dist)
        l := { l with from_ := f2 }
    l ← cwhile
      (fun (l : InflateFastLocals) => pure (l.len > 2, l))
      (fun (l : InflateFastLocals) => do
        let (out1, from1) ← copyBytePostInc l.out l.from_
        let (out2, from2) ← copyBytePostInc out1 from1
        let (out3, from3) ← copyBytePostInc out2 from2
        let l := { l with out := out3, from_ := from3 }
        pure { l with len := l.len - 3 })
      l
    if l.len != 0 then
      let (out1, from1) ← copyBytePostInc l.out l.from_
      l := { l with out := out1, from_ := from1 }
      if l.len > 1 then
        let (out2, from2) ← copyBytePostInc l.out l.from_
        l := { l with out := out2, from_ := from2 }
  else
    let f1 ← cinline (subn l.out l.dist)
    l := { l with from_ := f1 }
    l ← cdoWhile
      (fun (l : InflateFastLocals) => do
        let (out1, from1) ← copyBytePostInc l.out l.from_
        let (out2, from2) ← copyBytePostInc out1 from1
        let (out3, from3) ← copyBytePostInc out2 from2
        let l := { l with out := out3, from_ := from3 }
        pure { l with len := l.len - 3 })
      (fun (l : InflateFastLocals) => pure (l.len > 2, l))
      l
    if l.len != 0 then
      let (out1, from1) ← copyBytePostInc l.out l.from_
      l := { l with out := out1, from_ := from1 }
      if l.len > 1 then
        let (out2, from2) ← copyBytePostInc l.out l.from_
        l := { l with out := out2, from_ := from2 }
  return .next l

/-- `dodist:` label block inside the 8-bit fallback loop. -/
def dodistBodyC (strm : ZStreamPtr) (l : InflateFastLocals) :
    M (GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty)) := do
  let mut l := l
  let e ← cinline l.here.load
  l := { l with op := e.bits.toUInt32 }
  let h1 ← cinline (shr64 l.hold l.op.toUInt64)
  l := { l with hold := h1, bits := l.bits - l.op }
  let e ← cinline l.here.load
  l := { l with op := e.op.toUInt32 }
  if l.op &&& 16 != 0 then
    let e ← cinline l.here.load
    l := { l with dist := e.val.toUInt32 }
    l := { l with op := l.op &&& 15 }
    if l.bits < l.op then
      let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
      l := { l with in_ := in1, hold := hold1, bits := bits1 }
      if l.bits < l.op then
        let (in2, hold2, bits2) ← pullByte64 l.in_ l.hold l.bits
        l := { l with in_ := in2, hold := hold2, bits := bits2 }
    let m ← cinline (shl32 1 l.op)
    l := { l with dist := l.dist + (l.hold.toUInt32 &&& (m - 1)) }
    let h2 ← cinline (shr64 l.hold l.op.toUInt64)
    l := { l with hold := h2, bits := l.bits - l.op }
    let d ← cinline (l.out.diff l.beg)
    l := { l with op := d.toUInt64.toUInt32 }
    let step ← copyMatchC strm l
    return .done step
  else if l.op &&& 64 == 0 then
    let e ← cinline l.here.load
    let m ← cinline (shl32 1 l.op)
    let here1 ← cinline (do
      let h1 ← l.dcode.add e.val.toNat
      h1.add (l.hold &&& (m - 1).toUInt64).toNat)
    return .goto { l with here := here1 }
  else
    badDataC strm l.state "invalid distance code"
    return .done (.brk l)

/-- `dolen:` label block inside the 8-bit fallback loop. -/
def dolenBodyC (strm : ZStreamPtr) (l : InflateFastLocals) :
    M (GotoStep InflateFastLocals (LoopStep InflateFastLocals Empty)) := do
  let mut l := l
  let e ← cinline l.here.load
  l := { l with op := e.bits.toUInt32 }
  let h1 ← cinline (shr64 l.hold l.op.toUInt64)
  l := { l with hold := h1, bits := l.bits - l.op }
  let e ← cinline l.here.load
  l := { l with op := e.op.toUInt32 }
  if l.op == 0 then
    let e ← cinline l.here.load
    store8 l.out e.val.toUInt8
    let out1 ← cinline (l.out.add 1)
    return .done (.next { l with out := out1 })
  else if l.op &&& 16 != 0 then
    let e ← cinline l.here.load
    l := { l with len := e.val.toUInt32 }
    l := { l with op := l.op &&& 15 }
    if l.op != 0 then
      if l.bits < l.op then
        let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
        l := { l with in_ := in1, hold := hold1, bits := bits1 }
      let m ← cinline (shl32 1 l.op)
      l := { l with len := l.len + (l.hold.toUInt32 &&& (m - 1)) }
      let h2 ← cinline (shr64 l.hold l.op.toUInt64)
      l := { l with hold := h2, bits := l.bits - l.op }
    if l.bits < 15 then
      let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
      let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
      l := { l with in_ := in2, hold := hold2, bits := bits2 }
    let here1 ← cinline (l.dcode.add (l.hold &&& l.dmask.toUInt64).toNat)
    l := { l with here := here1 }
    let step ← clabel "dodist" (dodistBodyC strm) l
    return .done step
  else if l.op &&& 64 == 0 then
    let e ← cinline l.here.load
    let m ← cinline (shl32 1 l.op)
    let here1 ← cinline (do
      let h1 ← l.lcode.add e.val.toNat
      h1.add (l.hold &&& (m - 1).toUInt64).toNat)
    return .goto { l with here := here1 }
  else if l.op &&& 32 != 0 then
    let s ← ldInflateState l.state
    stInflateState l.state { s with mode := TYPE }
    return .done (.brk l)
  else
    badDataC strm l.state "invalid literal/length code"
    return .done (.brk l)

/-- Exact C-shaped `inflate_fast`: uses `cdecl`, `cforwardLabel "leave"`, `cdoWhileBrk`,
`clabel "dolen8"` / `"dodist8"` / `"dolen"` / `"dodist"`, `pullByte64`, and `copyBytePostInc`. -/
def inflate_fast_c (strm : ZStreamPtr) (start : UInt32) : M (COrder 3 (CHiddenAs "inflate_fast" Unit)) := do
  let mut l ← cdecl ({
    state := default, in_ := default, last := default, out := default,
    beg := default, end_ := default, wsize := default, whave := default,
    wnext := default, window := default, back := default, hold := default,
    bits := default, lcode := default, dcode := default, lmask := default,
    dmask := default, here := default, op := default, len := default,
    dist := default, from_ := default, hold8 := default, last8 := default,
    end8 := default
  } : InflateFastLocals)
  let sm ← ldZStream strm
  let st0 ← cinline (castInflateState sm.state)
  l := { l with state := st0 }
  l := { l with in_ := sm.next_in }
  let last0 ← cinline (l.in_.add (sm.avail_in - 5).toNat)
  l := { l with last := last0 }
  l := { l with out := sm.next_out }
  let beg0 ← cinline (subn l.out (start - sm.avail_out))
  l := { l with beg := beg0 }
  let end0 ← cinline (l.out.add (sm.avail_out - 257).toNat)
  l := { l with end_ := end0 }
  let s ← ldInflateState l.state
  l := { l with wsize := s.wsize }
  l := { l with whave := s.whave }
  l := { l with wnext := s.wnext }
  l := { l with window := s.window }
  let back0 ← cinline (do
    if l.window != .null then do
      let outEnd ← l.out.add (sm.avail_out.toNat : Int)
      let winEnd ← l.window.add (l.wsize.toNat : Int)
      pure (outEnd == winEnd)
    else pure false)
  l := { l with back := back0 }
  l := { l with hold := s.hold }
  l := { l with bits := s.bits }
  l := { l with lcode := s.lencode }
  l := { l with dcode := s.distcode }
  let lmask0 ← cinline (do pure ((← shl32 1 s.lenbits) - 1))
  l := { l with lmask := lmask0 }
  let dmask0 ← cinline (do pure ((← shl32 1 s.distbits) - 1))
  l := { l with dmask := dmask0 }
  cforwardLabel "leave"
    (do
      let mut l := l
      if !l.back && sm.avail_in >= 16 && sm.avail_out >= 2 + 258 + 15 then
        let last80 ← cinline (l.in_.add (sm.avail_in - 16).toNat)
        l := { l with last8 := last80 }
        let end80 ← cinline (l.out.add (sm.avail_out - (2 + 258 + 15)).toNat)
        l := { l with end8 := end80 }
        l := { l with hold8 := l.hold }
        l ← cdoWhileBrk
          (fun (l : InflateFastLocals) => do
            let mut l := l
            let w0 ← cinline (load64_c l.in_)
            let sh0 ← cinline (shl64 w0 l.bits.toUInt64)
            let in0 ← cinline (l.in_.add (((63 - l.bits) >>> 3).toNat : Int))
            l := { l with hold8 := l.hold8 ||| sh0 }
            l := { l with in_ := in0, bits := l.bits ||| 56 }
            let h0 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
            l := { l with here := h0 }
            let e0 ← cinline l.here.load
            if e0.op == 0 then
              let sh1 ← cinline (shr64 l.hold8 e0.bits.toUInt64)
              l := { l with hold8 := sh1 }
              l := { l with bits := l.bits - e0.bits.toUInt32 }
              store8 l.out e0.val.toUInt8
              let out1 ← cinline (l.out.add 1)
              l := { l with out := out1 }
              let h1 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
              l := { l with here := h1 }
              let e1 ← cinline l.here.load
              if e1.op == 0 then
                let sh2 ← cinline (shr64 l.hold8 e1.bits.toUInt64)
                l := { l with hold8 := sh2 }
                l := { l with bits := l.bits - e1.bits.toUInt32 }
                store8 l.out e1.val.toUInt8
                let out2 ← cinline (l.out.add 1)
                l := { l with out := out2 }
                let h2 ← cinline (l.lcode.add (l.hold8 &&& l.lmask.toUInt64).toNat)
                l := { l with here := h2 }
                let e2 ← cinline l.here.load
                if e2.op == 0 then
                  let sh3 ← cinline (shr64 l.hold8 e2.bits.toUInt64)
                  l := { l with hold8 := sh3 }
                  l := { l with bits := l.bits - e2.bits.toUInt32 }
                  store8 l.out e2.val.toUInt8
                  let out3 ← cinline (l.out.add 1)
                  return .cont { l with out := out3 }
              let w1 ← cinline (load64_c l.in_)
              let sh4 ← cinline (shl64 w1 l.bits.toUInt64)
              let in1 ← cinline (l.in_.add (((63 - l.bits) >>> 3).toNat : Int))
              l := { l with hold8 := l.hold8 ||| sh4 }
              l := { l with in_ := in1, bits := l.bits ||| 56 }
            clabel "dolen8" (dolen8BodyC strm) l)
          (fun (l : InflateFastLocals) => do
            if ← Ptr.le l.in_ l.last8 then pure (← Ptr.le l.out l.end8, l)
            else pure (false, l))
          l
        l := { l with len := l.bits >>> 3 }
        let in2 ← cinline (subn l.in_ l.len)
        l := { l with in_ := in2, bits := l.bits - (l.len <<< 3) }
        let msk ← cinline (shl32 1 l.bits)
        l := { l with hold := l.hold8 &&& (msk - 1).toUInt64 }
        let st1 ← ldInflateState l.state
        if st1.mode != LEN then return .goto l
        if !(← cinline (Ptr.lt l.out l.end_)) then return .goto l
        return .fall l
      else
        return .fall l)
    (fun (l : InflateFastLocals) => do
      cdoWhileBrk
        (fun (l : InflateFastLocals) => do
          let mut l := l
          if l.bits < 15 then
            let (in1, hold1, bits1) ← pullByte64 l.in_ l.hold l.bits
            let (in2, hold2, bits2) ← pullByte64 in1 hold1 bits1
            l := { l with in_ := in2, hold := hold2, bits := bits2 }
          let h0 ← cinline (l.lcode.add (l.hold &&& l.lmask.toUInt64).toNat)
          l := { l with here := h0 }
          clabel "dolen" (dolenBodyC strm) l)
        (fun (l : InflateFastLocals) => do
          if ← Ptr.lt l.in_ l.last then pure (← Ptr.lt l.out l.end_, l)
          else pure (false, l))
        l)
    (fun (l : InflateFastLocals) => do
      let mut l := l
      l := { l with len := l.bits >>> 3 }
      let in1 ← cinline (subn l.in_ l.len)
      l := { l with in_ := in1, bits := l.bits - (l.len <<< 3) }
      let msk ← cinline (shl32 1 l.bits)
      l := { l with hold := l.hold &&& (msk - 1).toUInt64 }
      let sm2 ← ldZStream strm
      stZStream strm { sm2 with next_in := l.in_, next_out := l.out }
      let ai ← cinline (do
        if ← Ptr.lt l.in_ l.last then do let d ← l.last.diff l.in_; chk64 (5 + d.toInt)
        else do let d ← l.in_.diff l.last; chk64 (5 - d.toInt))
      let sm3 ← ldZStream strm
      stZStream strm { sm3 with avail_in := ai.toUInt64.toUInt32 }
      let ao ← cinline (do
        if ← Ptr.lt l.out l.end_ then do let d ← l.end_.diff l.out; chk64 (257 + d.toInt)
        else do let d ← l.out.diff l.end_; chk64 (257 - d.toInt))
      let sm4 ← ldZStream strm
      stZStream strm { sm4 with avail_out := ao.toUInt64.toUInt32 }
      let s2 ← ldInflateState l.state
      stInflateState l.state { s2 with hold := l.hold, bits := l.bits })

end Zlib.Inffast
