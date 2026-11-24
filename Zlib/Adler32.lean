import C99.DSL
import Zlib.Headers.Common

/-!
# `adler32.c` — Adler-32 Checksum Computation
-/

namespace Zlib.Adler32

open C99 Zlib.Spec

c_tu_begin adler32TU "adler32.c"

c_include_local "abi_common.h"

c_define BASE := 65521U
c_define NMAX := 5552

c_stmt_macro DO1(buf, i) := { adler += (buf)[i]; sum2 += adler; }
c_stmt_macro DO2(buf, i) := { DO1(buf, i); DO1(buf, i + 1); }
c_stmt_macro DO4(buf, i) := { DO2(buf, i); DO2(buf, i + 2); }
c_stmt_macro DO8(buf, i) := { DO4(buf, i); DO4(buf, i + 4); }
c_stmt_macro DO16(buf) := { DO8(buf, 0); DO8(buf, 8); }

c_stmt_macro MOD(a) := a %= BASE;
c_stmt_macro MOD28(a) := a %= BASE;
c_stmt_macro MOD63(a) := a %= BASE;

c_fn uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len)
  requires (len.toNat = 1 → Readable m buf 1) ∧ (len.toNat ≠ 1 → buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat);
  ensures  view' = view;
{
  unsigned long sum2;
  unsigned n;

  sum2 = (adler >> 16) & 0xffff;
  adler &= 0xffff;

  if (len == 1) {
    adler += buf[0];
    if (adler >= BASE)
      adler -= BASE;
    sum2 += adler;
    if (sum2 >= BASE)
      sum2 -= BASE;
    return adler | (sum2 << 16);
  }

  if (buf == Z_NULL)
    return 1L;

  if (len < 16) {
    while (len.-) {
      adler += *buf++;
      sum2 += adler;
    }
    if (adler >= BASE)
      adler -= BASE;
    MOD28(sum2);
    return adler | (sum2 << 16);
  }

  while (len >= NMAX) {
    len -= NMAX;
    n = NMAX / 16;
    do {
      DO16(buf);
      buf += 16;
    } while (.-n);
    MOD(adler);
    MOD(sum2);
  }

  if (len) {
    while (len >= 16) {
      len -= 16;
      DO16(buf);
      buf += 16;
    }
    while (len.-) {
      adler += *buf++;
      sum2 += adler;
    }
    MOD(adler);
    MOD(sum2);
  }

  return adler | (sum2 << 16);
}

c_fn uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len)
  requires (len.toNat = 1 → Readable m buf 1) ∧ (len.toNat ≠ 1 → buf = .null ∨ len.toNat = 0 ∨ Readable m buf len.toNat);
  ensures  view' = view;
{
  return adler32_z(adler, buf, len);
}

c_fn local uLong adler32_combine_(uLong adler1, uLong adler2, z_off64_t len2) {
  unsigned long sum1;
  unsigned long sum2;
  unsigned rem;

  if (len2 < 0)
    return 0xffffffffUL;

  MOD63(len2);
  rem = (unsigned)len2;
  sum1 = adler1 & 0xffff;
  sum2 = rem * sum1;
  MOD(sum2);
  sum1 += (adler2 & 0xffff) + BASE - 1;
  sum2 += ((adler1 >> 16) & 0xffff) + ((adler2 >> 16) & 0xffff) + BASE - rem;
  if (sum1 >= BASE) sum1 -= BASE;
  if (sum1 >= BASE) sum1 -= BASE;
  if (sum2 >= ((unsigned long)BASE << 1)) sum2 -= ((unsigned long)BASE << 1);
  if (sum2 >= BASE) sum2 -= BASE;
  return sum1 | (sum2 << 16);
}

c_fn uLong ZEXPORT adler32_combine(uLong adler1, uLong adler2, z_off_t len2)
  requires True;
  ensures  view' = view;
{
  return adler32_combine_(adler1, adler2, len2);
}

c_fn uLong ZEXPORT adler32_combine64(uLong adler1, uLong adler2, z_off64_t len2)
  requires True;
  ensures  view' = view;
{
  return adler32_combine_(adler1, adler2, len2);
}

c_tu_end adler32TU

end Zlib.Adler32
