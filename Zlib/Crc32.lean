import C99.DSL
import Zlib.Headers.Common
import Zlib.Tables.Crc32H

/-!
# `crc32.c` — Braided CRC-32 Checksum and Combine Operations (`W=4, N=5, NLOW=2`)
-/

namespace Zlib.Crc32

open C99 Zlib.Spec

c_tu_begin crc32TU "crc32.c"

c_include_local "abi_common.h"

c_define N := 5
c_define BRAID_CUT := 320
c_define NLOW := 2
c_define NMIN := NLOW
c_define W := 4
c_typedef Z_U4 z_word_t;

c_fn local z_word_t byte_swap(z_word_t word) {
  return
    (word & 0xff000000) >> 24 |
    (word & 0xff0000) >> 8 |
    (word & 0xff00) << 8 |
    (word & 0xff) << 24;
}

c_include_tu Zlib.Tables.crc32H

c_define POLY := 0xedb88320

c_fn local uLong multmodp(uLong a, uLong b) {
  uLong m, p;

  m = (uLong)1 << 31;
  p = 0;
  for (;;) {
    if (a & m) {
      p ^= b;
      if ((a & (m - 1)) == 0)
        break;
    }
    m >>= 1;
    b = b & 1 ? (b >> 1) ^ POLY : b >> 1;
  }
  return p;
}

c_fn local uLong x2nmodp(z_off64_t n, unsigned k) {
  uLong p;

  p = (uLong)1 << 31;
  while (n) {
    if (n & 1)
      p = multmodp(x2n_table[k & 31], p);
    n >>= 1;
    k++;
  }
  return p;
}

c_fn const z_crc_t FAR * ZEXPORT get_crc_table(void) {
  return (const z_crc_t FAR *)crc_table;
}

c_fn local z_crc_t crc_word(z_word_t data) {
  int k;
  for (k = 0; k < W; k++)
    data = (data >> 8) ^ crc_table[data & 0xff];
  return (z_crc_t)data;
}

c_fn local z_word_t crc_word_big(z_word_t data) {
  int k;
  for (k = 0; k < W; k++)
    data = (data << 8) ^ crc_big_table[(data >> ((W - 1) << 3)) & 0xff];
  return data;
}

c_macro CRCB(t, w, k) := t[k][((w) >> ((k) << 3)) & 0xff]
c_macro CRCWORD(t, w) := ((CRCB(t, w, 0) ^ CRCB(t, w, 1)) ^ (CRCB(t, w, 2) ^ CRCB(t, w, 3)))

c_fn local uLong crc32_braid(uLong crc, const unsigned char FAR *buf, z_size_t len) {
  if (len >= NLOW * W + W - 1) {
    z_size_t blks;
    z_word_t const *words;
    unsigned endian;

    while (len && ((z_size_t)buf & (W - 1)) != 0) {
      len.-;
      crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    }

    blks = len / (NLOW * W);
    len -= blks * NLOW * W;
    words = (z_word_t const *)buf;

    endian = 1;
    if (*(unsigned char *)&endian) {
      z_crc_t crc0;
      z_word_t word0;
      z_crc_t crc1;
      z_word_t word1;

      crc0 = (z_crc_t)crc;
      crc1 = 0;

      while (.-blks) {
        word0 = crc0 ^ words[0];
        word1 = crc1 ^ words[1];
        words += NLOW;

        crc0 = CRCWORD(crc_braid2_table, word0);
        crc1 = CRCWORD(crc_braid2_table, word1);
      }

      crc = crc_word(crc0 ^ words[0]);
      crc = crc_word(crc1 ^ words[1] ^ crc);
      words += NLOW;
    }
    else {
      z_word_t crc0, word0, comb;
      z_word_t crc1, word1;

      crc0 = byte_swap(crc);
      crc1 = 0;

      while (.-blks) {
        word0 = crc0 ^ words[0];
        word1 = crc1 ^ words[1];
        words += NLOW;

        crc0 = CRCWORD(crc_braid2_big_table, word0);
        crc1 = CRCWORD(crc_braid2_big_table, word1);
      }

      comb = crc_word_big(crc0 ^ words[0]);
      comb = crc_word_big(crc1 ^ words[1] ^ comb);
      words += NLOW;
      crc = byte_swap(comb);
    }

    buf = (unsigned char const *)words;
  }

  while (len >= 8) {
    len -= 8;
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
  }
  while (len) {
    len.-;
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
  }

  return crc;
}

c_fn uLong ZEXPORT crc32_z(uLong crc, const unsigned char FAR *buf, z_size_t len)
  requires buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat;
  ensures  view' = view;
{
  if (buf == Z_NULL) return 0;

  crc = (~crc) & 0xffffffff;

  if (len >= NMIN * W + W - 1) {
    z_size_t blks;
    z_word_t const *words;
    unsigned endian;

    if (len < BRAID_CUT || len < N * W + W - 1)
      return crc32_braid(crc, buf, len) ^ 0xffffffff;

    while (len && ((z_size_t)buf & (W - 1)) != 0) {
      len.-;
      crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    }

    blks = len / (N * W);
    len -= blks * N * W;
    words = (z_word_t const *)buf;

    endian = 1;
    if (*(unsigned char *)&endian) {
      z_crc_t crc0;
      z_word_t word0;
      z_crc_t crc1;
      z_word_t word1;
      z_crc_t crc2;
      z_word_t word2;
      z_crc_t crc3;
      z_word_t word3;
      z_crc_t crc4;
      z_word_t word4;

      crc0 = (z_crc_t)crc;
      crc1 = 0;
      crc2 = 0;
      crc3 = 0;
      crc4 = 0;

      while (.-blks) {
        word0 = crc0 ^ words[0];
        word1 = crc1 ^ words[1];
        word2 = crc2 ^ words[2];
        word3 = crc3 ^ words[3];
        word4 = crc4 ^ words[4];
        words += N;

        crc0 = CRCWORD(crc_braid5_table, word0);
        crc1 = CRCWORD(crc_braid5_table, word1);
        crc2 = CRCWORD(crc_braid5_table, word2);
        crc3 = CRCWORD(crc_braid5_table, word3);
        crc4 = CRCWORD(crc_braid5_table, word4);
      }

      crc = crc_word(crc0 ^ words[0]);
      crc = crc_word(crc1 ^ words[1] ^ crc);
      crc = crc_word(crc2 ^ words[2] ^ crc);
      crc = crc_word(crc3 ^ words[3] ^ crc);
      crc = crc_word(crc4 ^ words[4] ^ crc);
      words += N;
    }
    else {
      z_word_t crc0, word0, comb;
      z_word_t crc1, word1;
      z_word_t crc2, word2;
      z_word_t crc3, word3;
      z_word_t crc4, word4;

      crc0 = byte_swap(crc);
      crc1 = 0;
      crc2 = 0;
      crc3 = 0;
      crc4 = 0;

      while (.-blks) {
        word0 = crc0 ^ words[0];
        word1 = crc1 ^ words[1];
        word2 = crc2 ^ words[2];
        word3 = crc3 ^ words[3];
        word4 = crc4 ^ words[4];
        words += N;

        crc0 = CRCWORD(crc_braid5_big_table, word0);
        crc1 = CRCWORD(crc_braid5_big_table, word1);
        crc2 = CRCWORD(crc_braid5_big_table, word2);
        crc3 = CRCWORD(crc_braid5_big_table, word3);
        crc4 = CRCWORD(crc_braid5_big_table, word4);
      }

      comb = crc_word_big(crc0 ^ words[0]);
      comb = crc_word_big(crc1 ^ words[1] ^ comb);
      comb = crc_word_big(crc2 ^ words[2] ^ comb);
      comb = crc_word_big(crc3 ^ words[3] ^ comb);
      comb = crc_word_big(crc4 ^ words[4] ^ comb);
      words += N;
      crc = byte_swap(comb);
    }

    buf = (unsigned char const *)words;
  }

  while (len >= 8) {
    len -= 8;
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
  }
  while (len) {
    len.-;
    crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff];
  }

  return crc ^ 0xffffffff;
}

c_fn uLong ZEXPORT crc32(uLong crc, const unsigned char FAR *buf, uInt len)
  requires buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat;
  ensures  view' = view;
{
  return crc32_z(crc, buf, len);
}

c_fn uLong ZEXPORT crc32_combine_gen64(z_off64_t len2)
  requires True;
  ensures  view' = view;
{
  if (len2 < 0)
    return 0;
  return x2nmodp(len2, 3);
}

c_fn uLong ZEXPORT crc32_combine_gen(z_off_t len2)
  requires True;
  ensures  view' = view;
{
  return crc32_combine_gen64((z_off64_t)len2);
}

c_fn uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op)
  requires op = 0 ∨ (op &&& 0xffffffff) ≠ 0;
  ensures  view' = view;
{
  if (op == 0)
    return 0;
  return multmodp(op, crc1 & 0xffffffff) ^ (crc2 & 0xffffffff);
}

c_fn uLong ZEXPORT crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)
  requires True;
  ensures  view' = view;
{
  return crc32_combine_op(crc1, crc2, crc32_combine_gen64(len2));
}

c_fn uLong ZEXPORT crc32_combine(uLong crc1, uLong crc2, z_off_t len2)
  requires True;
  ensures  view' = view;
{
  return crc32_combine64(crc1, crc2, (z_off64_t)len2);
}

c_tu_end crc32TU

end Zlib.Crc32
