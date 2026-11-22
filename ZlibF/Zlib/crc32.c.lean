import ZlibF.Runtime.Alloc
import ZlibF.Runtime.Address
import ZlibF.Zlib.«crc32.h»

/-!
# crc32.c — faithful translation

Source: `crc32.c` and `crc32.h`, default x86_64 Linux build (`Z_REG64` defined in `zutil.h`, `Z_U4` defined in
`zconf.h`). Preprocessor decisions: `DYNAMIC_CRC_TABLE`, `MAKECRCH`, `Z_TESTN`, `Z_TESTW`, `Z_TESTCUT`, `Z_TESTNLOW`,
`Z_REG32`, `ARMCRC32` (`__aarch64__` only) and `HAVE_S390X_VX` are undefined, so the static tables of `crc32.h` are
used and `make_crc_table`, `braid`, `write_table*` and `z_once` are dead. `DEF_W = 4`, `DEF_N = 5`, `DEF_CUT = 320`,
`DEF_NLOW = 2`, so `N = 5`, `W = 4`, `BRAID_CUT = 320`, `NLOW = 2`, `NMIN = 2`, `z_word_t` is `unsigned` (`UInt32`),
and `z_crc_t` is `unsigned` (`UInt32`). The `#if N > 5` and `#if NLOW > 2` parts are dead.

Decisions on the model:

* **Tables.** `crc_table` and `x2n_table` are the `Statics` fields of the same name (read through `UPtr`;
  `initStatics` sets them from `crc32.h.lean`). `crc_big_table`, `crc_braid2_table`, `crc_braid2_big_table`,
  `crc_braid5_table`, `crc_braid5_big_table` are only indexed, so they are Lean constants, indexed with a bounds check.
* **Alignment.** `((z_size_t)buf & (W - 1))` observes the low two address bits. Raw byte blocks retain the
  aligned-origin convention, so their offsets supply these bits. Static and embedded byte arrays use arbitrary
  stable origin residues from the heap. Proofs must hold for every residue, including nonzero field alignment.
  This abstraction is only for the low-bit test; it does not supply a general ABI address or aliasing model.
* **Words.** `words[i]` reads the byte buffer as `unsigned` (`z_word_t`); the translation reads the 4 bytes in order
  and assembles them little endian (`loadWord`). The formal strict-aliasing issue of this cast is not modelled; it is
  inside the object either way.
* **Endianness.** `*(unsigned char *)&endian` with `endian = 1` is the low byte of `endian` on the little-endian
  target, so the big-endian branch is dead at run time; it is translated for completeness and is not reached
  (the differential test cannot cover it).
* `multmodp` loops forever when `a` has no bit set among bits 0..31 (`a != 0` is not enough); the C then never
  ends, and here the loop runs out of fuel. `crc32_combine_op(crc1, crc2, op)` reaches it for `op` with zero low
  32 bits.
-/

namespace Zlib.Crc32
open C

/-- `Z_BATCH` etc. are `ARMCRC32` only. `N`, `W`, `BRAID_CUT`, `NLOW`, `NMIN`: -/
def N : Int32 := 5
def W : Int32 := 4
def BRAID_CUT : Int32 := 320
def NLOW : Int32 := 2
def NMIN : Int32 := 2

/-- `#define POLY 0xedb88320` (an `unsigned int` constant). -/
def POLY : UInt64 := 0xedb88320

/-- The `Statics` with the contents that `crc32.c` fixes: `crc_table` and `x2n_table` (from `crc32.h`). -/
def initStatics (s : Statics) : Statics :=
  { s with crc_table := Zlib.Crc32H.crc_table, x2n_table := Zlib.Crc32H.x2n_table }

/-- `x >> n` for `unsigned long`: undefined if `n >= 64`. -/
def shr64 (x n : UInt64) : M UInt64 :=
  if n < 64 then pure (x >>> n) else ub "shift count out of range"

/-- `crc_table[i]` -/
def crcTab (i : UInt64) : M UInt32 := Ptr.index (Ptr.ref URef.st_crc_table 0) i.toNat

/-- `x2n_table[i]` -/
def x2nTab (i : UInt32) : M UInt32 := Ptr.index (Ptr.ref URef.st_x2n_table 0) i.toNat

/-- `t[k][i]` for a constant two-dimensional table. -/
def idx2 {α : Type} (t : Array (Array α)) (k i : Nat) : M α :=
  match t[k]? with
  | some r => match r[i]? with
    | some v => pure v
    | none => ub "table index outside its array"
  | none => ub "table index outside its array"

/-- `t[i]` for a constant table. -/
def idx1 {α : Type} (t : Array α) (i : Nat) : M α :=
  match t[i]? with
  | some v => pure v
  | none => ub "table index outside its array"

/-- `(z_size_t)buf`, represented up to the low bits observed by the CRC alignment test. -/
def addrOf (p : BPtr) : M UInt64 :=
  C.ByteAddress.address p

/-- `words[i]` for `z_word_t const *words` (`W == 4`, `z_word_t` = `unsigned`) over the byte buffer at `p`
(little-endian target). -/
def loadWord (p : BPtr) : M UInt32 := do
  let mut w : UInt32 := 0
  for i in [0:4] do
    let b ← index8 p i
    w := w ||| (b.toUInt32 <<< (8 * i).toUInt32)
  pure w

/-! ### Byte swaps and the word CRCs -/

/-- `local z_word_t byte_swap(z_word_t word)` (`W == 4`) -/
def byte_swap (word : UInt32) : UInt32 :=
  ((word &&& 0xff000000) >>> 24) |||
  ((word &&& 0xff0000) >>> 8) |||
  ((word &&& 0xff00) <<< 8) |||
  ((word &&& 0xff) <<< 24)

/-- `local z_crc_t crc_word(z_word_t data)` (`W == 4`) -/
def crc_word (data : UInt32) : M UInt32 := do
  -- for (k = 0; k < W; k++) data = (data >> 8) ^ crc_table[data & 0xff];
  let (data, _) ← cwhile (fun (data, k) => pure (k < W, (data, k)))
    (fun (data, k) => do
      let t ← crcTab (data &&& 0xff).toUInt64
      pure ((data >>> 8) ^^^ t, k + 1)) (data, (0 : Int32))
  -- return (z_crc_t)data;
  pure data

/-- `local z_word_t crc_word_big(z_word_t data)` (`W == 4`) -/
def crc_word_big (data : UInt32) : M UInt32 := do
  -- for (k = 0; k < W; k++) data = (data << 8) ^ crc_big_table[(data >> ((W - 1) << 3)) & 0xff];
  let (data, _) ← cwhile (fun (data, k) => pure (k < W, (data, k)))
    (fun (data, k) => do
      let t ← idx1 Zlib.Crc32H.crc_big_table (((data >>> 24) &&& 0xff).toNat)
      pure ((data <<< 8) ^^^ t, k + 1)) (data, (0 : Int32))
  pure data

/-! ### Polynomial arithmetic -/

/-- `local uLong multmodp(uLong a, uLong b)` -/
def multmodp (a b : UInt64) : M UInt64 := do
  -- m = (uLong)1 << 31; p = 0;
  -- for (;;) { if (a & m) { p ^= b; if ((a & (m - 1)) == 0) break; }
  --            m >>= 1; b = b & 1 ? (b >> 1) ^ POLY : b >> 1; }
  let (_, p, _, _) ← cwhile (fun (m, p, b, brk) => pure (!brk, (m, p, b, brk)))
    (fun (m, p, b, brk) => do
      let mut p := p
      if a &&& m != 0 then
        p := p ^^^ b
        if a &&& (m - 1) == 0 then return (m, p, b, true)
      let m := m >>> 1
      let b := if b &&& 1 != 0 then (b >>> 1) ^^^ POLY else b >>> 1
      pure (m, p, b, brk)) (((1 : UInt64) <<< 31, (0 : UInt64), b, false) : UInt64 × UInt64 × UInt64 × Bool)
  pure p

/-- `local uLong x2nmodp(z_off64_t n, unsigned k)` -/
def x2nmodp (n : Int64) (k : UInt32) : M UInt64 := do
  -- p = (uLong)1 << 31;             /* x^0 == 1 */
  -- while (n) { if (n & 1) p = multmodp(x2n_table[k & 31], p); n >>= 1; k++; }
  let (p, _, _) ← cwhile (fun (p, n, k) => pure (n != 0, (p, n, k)))
    (fun (p, n, k) => do
      let mut p := p
      if n &&& 1 != 0 then
        let t ← x2nTab (k &&& 31)
        p ← multmodp t.toUInt64 p
      pure (p, n >>> 1, k + 1)) (((1 : UInt64) <<< 31, n, k) : UInt64 × Int64 × UInt32)
  pure p

/-- `const z_crc_t FAR * ZEXPORT get_crc_table(void)` -/
def get_crc_table : M UPtr :=
  -- return (const z_crc_t FAR *)crc_table;
  pure (Ptr.ref URef.st_crc_table 0)

/-! ### `crc32_braid` and `crc32_z` -/

/-- `CRCWORD(t, w)` for `W == 4`: `((CRCB(t, w, 0) ^ CRCB(t, w, 1)) ^ (CRCB(t, w, 2) ^ CRCB(t, w, 3)))`. -/
def crcWord (t : Array (Array UInt32)) (w : UInt32) : M UInt32 := do
  let b0 ← idx2 t 0 (w &&& 0xff).toNat
  let b1 ← idx2 t 1 ((w >>> 8) &&& 0xff).toNat
  let b2 ← idx2 t 2 ((w >>> 16) &&& 0xff).toNat
  let b3 ← idx2 t 3 ((w >>> 24) &&& 0xff).toNat
  pure ((b0 ^^^ b1) ^^^ (b2 ^^^ b3))

/-- The little-endian braids for `NLOW = 2`: `crc0`, `crc1` (`z_crc_t`), `words`, `blks`. -/
structure BL2 where
  crc0 : UInt32
  crc1 : UInt32
  words : BPtr
  blks : UInt64

/-- The big-endian braids for `NLOW = 2`: `crc0`, `crc1` (`z_word_t`), `words`, `blks`. -/
structure BB2 where
  crc0 : UInt32
  crc1 : UInt32
  words : BPtr
  blks : UInt64

/-- The little-endian braids for `N = 5`: `crc0 .. crc4` (`z_crc_t`), `words`, `blks`. -/
structure BL where
  crc0 : UInt32
  crc1 : UInt32
  crc2 : UInt32
  crc3 : UInt32
  crc4 : UInt32
  words : BPtr
  blks : UInt64

/-- The big-endian braids for `N = 5`: `crc0 .. crc4` (`z_word_t`), `words`, `blks`. -/
structure BB where
  crc0 : UInt32
  crc1 : UInt32
  crc2 : UInt32
  crc3 : UInt32
  crc4 : UInt32
  words : BPtr
  blks : UInt64

/-- `words[i]` for `W == 4` (`z_word_t` is 4 bytes). -/
def wordAt (words : BPtr) (i : Nat) : M UInt32 := do
  loadWord (← words.add (4 * i))

/-- The body of `while (--blks)` in `crc32_braid` (little-endian branch, `NLOW = 2`). -/
def blockLittle2 (s : BL2) : M BL2 := do
  -- word0 = crc0 ^ words[0]; word1 = crc1 ^ words[1];
  let word0 := s.crc0 ^^^ (← wordAt s.words 0)
  let word1 := s.crc1 ^^^ (← wordAt s.words 1)
  -- words += NLOW;
  let words ← s.words.add 8
  -- crc0 = CRCWORD(crc_braid2_table, word0); crc1 = CRCWORD(crc_braid2_table, word1);
  let crc0 ← crcWord Zlib.Crc32H.crc_braid2_table word0
  let crc1 ← crcWord Zlib.Crc32H.crc_braid2_table word1
  pure { s with crc0, crc1, words }

/-- The body of `while (--blks)` in `crc32_braid` (big-endian branch, `NLOW = 2`). -/
def blockBig2 (s : BB2) : M BB2 := do
  let word0 := s.crc0 ^^^ (← wordAt s.words 0)
  let word1 := s.crc1 ^^^ (← wordAt s.words 1)
  let words ← s.words.add 8
  let crc0 ← crcWord Zlib.Crc32H.crc_braid2_big_table word0
  let crc1 ← crcWord Zlib.Crc32H.crc_braid2_big_table word1
  pure { s with crc0, crc1, words }

/-- The body of `while (--blks)` in `crc32_z` (little-endian branch, `N = 5`). -/
def blockLittle (s : BL) : M BL := do
  -- word0 = crc0 ^ words[0]; ... word4 = crc4 ^ words[4];
  let word0 := s.crc0 ^^^ (← wordAt s.words 0)
  let word1 := s.crc1 ^^^ (← wordAt s.words 1)
  let word2 := s.crc2 ^^^ (← wordAt s.words 2)
  let word3 := s.crc3 ^^^ (← wordAt s.words 3)
  let word4 := s.crc4 ^^^ (← wordAt s.words 4)
  -- words += N;
  let words ← s.words.add 20
  -- crc0 = CRCWORD(crc_braid5_table, word0); ... crc4 = CRCWORD(crc_braid5_table, word4);
  let crc0 ← crcWord Zlib.Crc32H.crc_braid5_table word0
  let crc1 ← crcWord Zlib.Crc32H.crc_braid5_table word1
  let crc2 ← crcWord Zlib.Crc32H.crc_braid5_table word2
  let crc3 ← crcWord Zlib.Crc32H.crc_braid5_table word3
  let crc4 ← crcWord Zlib.Crc32H.crc_braid5_table word4
  pure { s with crc0, crc1, crc2, crc3, crc4, words }

/-- The body of `while (--blks)` in `crc32_z` (big-endian branch, `N = 5`). -/
def blockBig (s : BB) : M BB := do
  let word0 := s.crc0 ^^^ (← wordAt s.words 0)
  let word1 := s.crc1 ^^^ (← wordAt s.words 1)
  let word2 := s.crc2 ^^^ (← wordAt s.words 2)
  let word3 := s.crc3 ^^^ (← wordAt s.words 3)
  let word4 := s.crc4 ^^^ (← wordAt s.words 4)
  let words ← s.words.add 20
  let crc0 ← crcWord Zlib.Crc32H.crc_braid5_big_table word0
  let crc1 ← crcWord Zlib.Crc32H.crc_braid5_big_table word1
  let crc2 ← crcWord Zlib.Crc32H.crc_braid5_big_table word2
  let crc3 ← crcWord Zlib.Crc32H.crc_braid5_big_table word3
  let crc4 ← crcWord Zlib.Crc32H.crc_braid5_big_table word4
  pure { s with crc0, crc1, crc2, crc3, crc4, words }

/-- `crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];` -/
def crcByte (crc : UInt64) (buf : BPtr) : M (UInt64 × BPtr) := do
  let b ← load8 buf
  let buf ← buf.add 1
  let t ← crcTab ((crc ^^^ b.toUInt64) &&& 0xff)
  pure ((crc >>> 8) ^^^ t.toUInt64, buf)

/-- `local uLong crc32_braid(uLong crc, const unsigned char FAR *buf, z_size_t len)` -/
def crc32_braid (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  let mut crc := crc
  let mut buf := buf
  let mut len := len
  -- if (len >= NLOW * W + W - 1) {
  if len ≥ (NLOW * W + W - 1).toInt.toNat.toUInt64 then
    -- while (len && ((z_size_t)buf & (W - 1)) != 0) { len--; crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }
    let (c, b, l) ← cwhile
      (fun (c, b, l) => do
        if l == 0 then pure (false, (c, b, l))
        else pure ((← addrOf b) &&& (W - 1).toInt.toNat.toUInt64 != 0, (c, b, l)))
      (fun (c, b, l) => do
        let l := l - 1
        let (c, b) ← crcByte c b
        pure (c, b, l)) (crc, buf, len)
    crc := c; buf := b; len := l
    -- blks = len / (NLOW * W); len -= blks * NLOW * W; words = (z_word_t const *)buf;
    let nw : UInt64 := (NLOW * W).toInt.toNat.toUInt64
    let blks := len / nw
    len := len - blks * nw
    let words := buf
    -- endian = 1;
    let endian : UInt32 := 1
    -- if (*(unsigned char *)&endian) {   /* Little endian. */
    if endian.toUInt8 != 0 then
      -- crc0 = (z_crc_t)crc; crc1 = 0;
      let s : BL2 := { crc0 := crc.toUInt32, crc1 := 0, words, blks }
      -- while (--blks) { ... }
      let s ← cwhile (fun s => let blks := s.blks - 1; pure (blks != 0, { s with blks })) blockLittle2 s
      -- crc = crc_word(crc0 ^ words[0]);
      crc := (← crc_word (s.crc0 ^^^ (← wordAt s.words 0))).toUInt64
      -- crc = crc_word(crc1 ^ words[1] ^ crc);
      crc := (← crc_word ((s.crc1 ^^^ (← wordAt s.words 1)).toUInt64 ^^^ crc).toUInt32).toUInt64
      -- words += NLOW;
      buf := ← s.words.add 8
    else
      -- /* Big endian. */ crc0 = byte_swap(crc); crc1 = 0;
      let s : BB2 := { crc0 := byte_swap crc.toUInt32, crc1 := 0, words, blks }
      let s ← cwhile (fun s => let blks := s.blks - 1; pure (blks != 0, { s with blks })) blockBig2 s
      -- comb = crc_word_big(crc0 ^ words[0]); comb = crc_word_big(crc1 ^ words[1] ^ comb);
      let comb ← crc_word_big (s.crc0 ^^^ (← wordAt s.words 0))
      let comb ← crc_word_big (s.crc1 ^^^ (← wordAt s.words 1) ^^^ comb)
      -- words += NLOW; crc = byte_swap(comb);
      let words ← s.words.add 8
      crc := (byte_swap comb).toUInt64
      -- buf = (unsigned char const *)words;
      buf := words
  -- while (len >= 8) { len -= 8; eight times: crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }
  let (c, b, l) ← cwhile (fun (c, b, l) => pure (l ≥ 8, (c, b, l)))
    (fun (c, b, l) => do
      let l := l - 8
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      pure (c, b, l)) (crc, buf, len)
  crc := c; buf := b; len := l
  -- while (len) { len--; crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }
  let (c, _, _) ← cwhile (fun (c, b, l) => pure (l != 0, (c, b, l)))
    (fun (c, b, l) => do
      let l := l - 1
      let (c, b) ← crcByte c b
      pure (c, b, l)) (crc, buf, len)
  -- return crc;
  pure c

/-- `uLong ZEXPORT crc32_z(uLong crc, const unsigned char FAR *buf, z_size_t len)` -/
def crc32_z (crc : UInt64) (buf : BPtr) (len : UInt64) : M UInt64 := do
  -- if (buf == Z_NULL) return 0;
  if buf == .null then return 0
  -- crc = (~crc) & 0xffffffff;
  let mut crc := (~~~crc) &&& 0xffffffff
  let mut buf := buf
  let mut len := len
  -- if (len >= NMIN * W + W - 1) {
  if len ≥ (NMIN * W + W - 1).toInt.toNat.toUInt64 then
    -- if (len < BRAID_CUT || len < N * W + W - 1) return crc32_braid(crc, buf, len) ^ 0xffffffff;
    if len < BRAID_CUT.toInt.toNat.toUInt64 || len < (N * W + W - 1).toInt.toNat.toUInt64 then
      return (← crc32_braid crc buf len) ^^^ 0xffffffff
    -- while (len && ((z_size_t)buf & (W - 1)) != 0) { len--; crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }
    let (c, b, l) ← cwhile
      (fun (c, b, l) => do
        if l == 0 then pure (false, (c, b, l))
        else pure ((← addrOf b) &&& (W - 1).toInt.toNat.toUInt64 != 0, (c, b, l)))
      (fun (c, b, l) => do
        let l := l - 1
        let (c, b) ← crcByte c b
        pure (c, b, l)) (crc, buf, len)
    crc := c; buf := b; len := l
    -- blks = len / (N * W); len -= blks * N * W; words = (z_word_t const *)buf;
    let nw : UInt64 := (N * W).toInt.toNat.toUInt64
    let blks := len / nw
    len := len - blks * nw
    let words := buf
    -- endian = 1;
    let endian : UInt32 := 1
    -- if (*(unsigned char *)&endian) {   /* Little endian. */
    if endian.toUInt8 != 0 then
      -- crc0 = (z_crc_t)crc; crc1 = 0; ... crc4 = 0;
      let s : BL := { crc0 := crc.toUInt32, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words, blks }
      -- while (--blks) { ... }
      let s ← cwhile (fun s => let blks := s.blks - 1; pure (blks != 0, { s with blks })) blockLittle s
      -- crc = crc_word(crc0 ^ words[0]);
      crc := (← crc_word (s.crc0 ^^^ (← wordAt s.words 0))).toUInt64
      -- crc = crc_word(crc1 ^ words[1] ^ crc); ... crc4
      crc := (← crc_word ((s.crc1 ^^^ (← wordAt s.words 1)).toUInt64 ^^^ crc).toUInt32).toUInt64
      crc := (← crc_word ((s.crc2 ^^^ (← wordAt s.words 2)).toUInt64 ^^^ crc).toUInt32).toUInt64
      crc := (← crc_word ((s.crc3 ^^^ (← wordAt s.words 3)).toUInt64 ^^^ crc).toUInt32).toUInt64
      crc := (← crc_word ((s.crc4 ^^^ (← wordAt s.words 4)).toUInt64 ^^^ crc).toUInt32).toUInt64
      -- words += N;
      buf := ← s.words.add 20
    else
      -- /* Big endian. */ crc0 = byte_swap(crc); crc1 = 0; ... crc4 = 0;
      let s : BB := { crc0 := byte_swap crc.toUInt32, crc1 := 0, crc2 := 0, crc3 := 0, crc4 := 0, words, blks }
      let s ← cwhile (fun s => let blks := s.blks - 1; pure (blks != 0, { s with blks })) blockBig s
      -- comb = crc_word_big(crc0 ^ words[0]); comb = crc_word_big(crc1 ^ words[1] ^ comb); ...
      let comb ← crc_word_big (s.crc0 ^^^ (← wordAt s.words 0))
      let comb ← crc_word_big (s.crc1 ^^^ (← wordAt s.words 1) ^^^ comb)
      let comb ← crc_word_big (s.crc2 ^^^ (← wordAt s.words 2) ^^^ comb)
      let comb ← crc_word_big (s.crc3 ^^^ (← wordAt s.words 3) ^^^ comb)
      let comb ← crc_word_big (s.crc4 ^^^ (← wordAt s.words 4) ^^^ comb)
      -- words += N; crc = byte_swap(comb);
      let words ← s.words.add 20
      crc := (byte_swap comb).toUInt64
      -- buf = (unsigned char const *)words;
      buf := words
    -- (little endian: buf = (unsigned char const *)words;  done above)
  -- while (len >= 8) { len -= 8; eight times: crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }
  let (c, b, l) ← cwhile (fun (c, b, l) => pure (l ≥ 8, (c, b, l)))
    (fun (c, b, l) => do
      let l := l - 8
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      let (c, b) ← crcByte c b
      pure (c, b, l)) (crc, buf, len)
  crc := c; buf := b; len := l
  -- while (len) { len--; crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]; }
  let (c, _, _) ← cwhile (fun (c, b, l) => pure (l != 0, (c, b, l)))
    (fun (c, b, l) => do
      let l := l - 1
      let (c, b) ← crcByte c b
      pure (c, b, l)) (crc, buf, len)
  -- return crc ^ 0xffffffff;
  pure (c ^^^ 0xffffffff)

/-- `uLong ZEXPORT crc32(uLong crc, const unsigned char FAR *buf, uInt len)` -/
def crc32 (crc : UInt64) (buf : BPtr) (len : UInt32) : M UInt64 :=
  -- return crc32_z(crc, buf, len);
  crc32_z crc buf len.toUInt64

/-- `uLong ZEXPORT crc32_combine_gen64(z_off64_t len2)` -/
def crc32_combine_gen64 (len2 : Int64) : M UInt64 := do
  -- if (len2 < 0) return 0;
  if len2 < 0 then return 0
  -- return x2nmodp(len2, 3);
  x2nmodp len2 3

/-- `uLong ZEXPORT crc32_combine_gen(z_off_t len2)` -/
def crc32_combine_gen (len2 : Int64) : M UInt64 :=
  -- return crc32_combine_gen64((z_off64_t)len2);
  crc32_combine_gen64 len2

/-- `uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op)` -/
def crc32_combine_op (crc1 crc2 op : UInt64) : M UInt64 := do
  -- if (op == 0) return 0;
  if op == 0 then return 0
  -- return multmodp(op, crc1 & 0xffffffff) ^ (crc2 & 0xffffffff);
  let m ← multmodp op (crc1 &&& 0xffffffff)
  pure (m ^^^ (crc2 &&& 0xffffffff))

/-- `uLong ZEXPORT crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)` -/
def crc32_combine64 (crc1 crc2 : UInt64) (len2 : Int64) : M UInt64 := do
  -- return crc32_combine_op(crc1, crc2, crc32_combine_gen64(len2));
  crc32_combine_op crc1 crc2 (← crc32_combine_gen64 len2)

/-- `uLong ZEXPORT crc32_combine(uLong crc1, uLong crc2, z_off_t len2)` -/
def crc32_combine (crc1 crc2 : UInt64) (len2 : Int64) : M UInt64 :=
  -- return crc32_combine64(crc1, crc2, (z_off64_t)len2);
  crc32_combine64 crc1 crc2 len2

end Zlib.Crc32
