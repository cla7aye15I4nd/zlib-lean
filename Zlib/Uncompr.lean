import C99.DSL
import Zlib.Headers.Common

/-!
# `uncompr.c` — One-Shot Memory Buffer Decompression
-/

namespace Zlib.Uncompr

open C99 Zlib.Spec

c_tu_begin uncomprTU "uncompr.c"

c_include_local "abi_common.h"

c_fn int ZEXPORT uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen)
  requires valid_or_null(sourceLen) && valid_or_null(destLen);
  requires disjoint_owned(sourceLen, destLen);
  requires separated(dest, destLen, source, sourceLen);
  requires sourceLen == NULL || *sourceLen == 0 || source == NULL ||
    (readable(source, *sourceLen) && disjoint_owned(source));
  requires destLen == NULL || *destLen == 0 || dest == NULL ||
    (writable(dest, *destLen) && disjoint_owned(dest));
  modifies dest, destLen, sourceLen;
  ensures  view' == view;
{
  z_stream stream;
  int err;
  const uInt max = (uInt)-1;
  z_size_t len, left;

  if (sourceLen == Z_NULL || (*sourceLen > 0 && source == Z_NULL) ||
      destLen == Z_NULL || (*destLen > 0 && dest == Z_NULL))
    return Z_STREAM_ERROR;

  len = *sourceLen;
  left = *destLen;
  if (left == 0 && dest == Z_NULL)
    dest = (Bytef *)&stream.reserved;

  stream.next_in = (z_const Bytef *)source;
  stream.avail_in = 0;
  stream.zalloc = (alloc_func)0;
  stream.zfree = (free_func)0;
  stream.opaque = (voidpf)0;

  err = inflateInit(&stream);
  if (err != Z_OK) return err;

  stream.next_out = dest;
  stream.avail_out = 0;

  do {
    if (stream.avail_out == 0) {
      stream.avail_out = left > (z_size_t)max ? max : (uInt)left;
      left -= stream.avail_out;
    }
    if (stream.avail_in == 0) {
      stream.avail_in = len > (z_size_t)max ? max : (uInt)len;
      len -= stream.avail_in;
    }
    err = inflate(&stream, Z_NO_FLUSH);
  } while (err == Z_OK);

  len += stream.avail_in;
  left += stream.avail_out;
  *sourceLen -= len;
  *destLen -= left;

  inflateEnd(&stream);
  return err == Z_STREAM_END ? Z_OK :
         err == Z_NEED_DICT ? Z_DATA_ERROR :
         err == Z_BUF_ERROR && len == 0 ? Z_DATA_ERROR :
         err;
}

c_fn int ZEXPORT uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen)
  requires valid(sourceLen) && valid(destLen);
  requires disjoint_owned(sourceLen, destLen);
  requires separated(dest, destLen, source, sourceLen);
  requires *sourceLen == 0 || source == NULL || (readable(source, *sourceLen) && disjoint_owned(source));
  requires *destLen == 0 || dest == NULL || (writable(dest, *destLen) && disjoint_owned(dest));
  modifies dest, destLen, sourceLen;
  ensures  view' == view;
{
  int ret;
  z_size_t got = *destLen, used = *sourceLen;
  ret = uncompress2_z(dest, &got, source, &used);
  *sourceLen = (uLong)used;
  *destLen = (uLong)got;
  return ret;
}

c_fn int ZEXPORT uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)
  requires valid_or_null(destLen) && disjoint_owned(destLen);
  requires separated(dest, destLen, source);
  requires sourceLen == 0 || source == NULL || (readable(source, sourceLen) && disjoint_owned(source));
  requires destLen == NULL || *destLen == 0 || dest == NULL ||
    (writable(dest, *destLen) && disjoint_owned(dest));
  modifies dest, destLen;
  ensures  view' == view;
{
  z_size_t used = sourceLen;
  return uncompress2_z(dest, destLen, source, &used);
}

c_fn int ZEXPORT uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)
  requires valid(destLen) && disjoint_owned(destLen);
  requires separated(dest, destLen, source);
  requires sourceLen == 0 || source == NULL || (readable(source, sourceLen) && disjoint_owned(source));
  requires *destLen == 0 || dest == NULL || (writable(dest, *destLen) && disjoint_owned(dest));
  modifies dest, destLen;
  ensures  view' == view;
{
  uLong used = sourceLen;
  return uncompress2(dest, destLen, source, &used);
}

c_tu_end uncomprTU

end Zlib.Uncompr
