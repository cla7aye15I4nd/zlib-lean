import C99.DSL
import Zlib.Headers.Common

/-!
# `compress.c` — One-Shot Memory Buffer Compression
-/

namespace Zlib.Compress

open C99 Zlib.Spec

c_tu_begin compressTU "compress.c"

c_include_local "abi_common.h"

c_fn int ZEXPORT compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen, int level)
  requires OptTypedCell tags m destLen (.int .u64) ∧ DisjointFrom destLen owned;
  requires sourceLen.toNat = 0 ∨ source = .null ∨ Readable m source sourceLen.toNat;
  requires destLen = .null ∨ ∃ cap, readU64? m destLen = some cap ∧
    (cap = 0 ∨ dest = .null ∨ (Writable m dest cap ∧ DisjointFrom dest owned));
  modifies writes [dest, destLen];
  ensures  view' = view;
{
  z_stream stream;
  int err;
  const uInt max = (uInt)-1;
  z_size_t left;

  if ((sourceLen > 0 && source == Z_NULL) ||
      destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL))
    return Z_STREAM_ERROR;

  left = *destLen;
  *destLen = 0;

  stream.zalloc = (alloc_func)0;
  stream.zfree = (free_func)0;
  stream.opaque = (voidpf)0;

  err = deflateInit(&stream, level);
  if (err != Z_OK) return err;

  stream.next_out = dest;
  stream.avail_out = 0;
  stream.next_in = (z_const Bytef *)source;
  stream.avail_in = 0;

  do {
    if (stream.avail_out == 0) {
      stream.avail_out = left > (z_size_t)max ? max : (uInt)left;
      left -= stream.avail_out;
    }
    if (stream.avail_in == 0) {
      stream.avail_in = sourceLen > (z_size_t)max ? max : (uInt)sourceLen;
      sourceLen -= stream.avail_in;
    }
    err = deflate(&stream, sourceLen ? Z_NO_FLUSH : Z_FINISH);
  } while (err == Z_OK);

  *destLen = (z_size_t)(stream.next_out - dest);
  deflateEnd(&stream);
  return err == Z_STREAM_END ? Z_OK : err;
}

c_fn int ZEXPORT compress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen, int level)
  requires TypedCell tags m destLen (.int .u64) ∧ DisjointFrom destLen owned;
  requires sourceLen.toNat = 0 ∨ source = .null ∨ Readable m source sourceLen.toNat;
  requires ∃ cap, readU64? m destLen = some cap ∧
    (cap = 0 ∨ dest = .null ∨ (Writable m dest cap ∧ DisjointFrom dest owned));
  modifies writes [dest, destLen];
  ensures  view' = view;
{
  int ret;
  z_size_t got = *destLen;
  ret = compress2_z(dest, &got, source, sourceLen, level);
  *destLen = (uLong)got;
  return ret;
}

c_fn int ZEXPORT compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)
  requires OptTypedCell tags m destLen (.int .u64) ∧ DisjointFrom destLen owned;
  requires sourceLen.toNat = 0 ∨ source = .null ∨ Readable m source sourceLen.toNat;
  requires destLen = .null ∨ ∃ cap, readU64? m destLen = some cap ∧
    (cap = 0 ∨ dest = .null ∨ (Writable m dest cap ∧ DisjointFrom dest owned));
  modifies writes [dest, destLen];
  ensures  view' = view;
{
  return compress2_z(dest, destLen, source, sourceLen, Z_DEFAULT_COMPRESSION);
}

c_fn int ZEXPORT compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)
  requires TypedCell tags m destLen (.int .u64) ∧ DisjointFrom destLen owned;
  requires sourceLen.toNat = 0 ∨ source = .null ∨ Readable m source sourceLen.toNat;
  requires ∃ cap, readU64? m destLen = some cap ∧
    (cap = 0 ∨ dest = .null ∨ (Writable m dest cap ∧ DisjointFrom dest owned));
  modifies writes [dest, destLen];
  ensures  view' = view;
{
  return compress2(dest, destLen, source, sourceLen, Z_DEFAULT_COMPRESSION);
}

c_fn z_size_t ZEXPORT compressBound_z(z_size_t sourceLen)
  requires True;
  ensures  view' = view;
{
  z_size_t bound = sourceLen + (sourceLen >> 12) + (sourceLen >> 14) +
                   (sourceLen >> 25) + 13;
  return bound < sourceLen ? (z_size_t)-1 : bound;
}

c_fn uLong ZEXPORT compressBound(uLong sourceLen)
  requires True;
  ensures  view' = view;
{
  z_size_t bound = compressBound_z(sourceLen);
  return (uLong)bound != bound ? (uLong)-1 : (uLong)bound;
}

c_tu_end compressTU

end Zlib.Compress
