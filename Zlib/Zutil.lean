import C99.DSL
import Zlib.Headers.Common

/-!
# `zutil.c` — Target-Dependent Utility Functions
-/

namespace Zlib.Zutil

open C99 Zlib.Spec

c_tu_begin zutilTU "zutil.c"

c_include_local "abi_common.h"
c_include_local "abi_gz.h"

c_var z_const char * const z_errmsg[10] = {
  (z_const char *)"need dictionary",
  (z_const char *)"stream end",
  (z_const char *)"",
  (z_const char *)"file error",
  (z_const char *)"stream error",
  (z_const char *)"data error",
  (z_const char *)"insufficient memory",
  (z_const char *)"buffer error",
  (z_const char *)"incompatible version",
  (z_const char *)""
};

c_fn const char * ZEXPORT zlibVersion(void)
  requires True;
  ensures  CString m' ret ∧ view' = view;
{
  return ZLIB_VERSION;
}

c_fn uLong ZEXPORT zlibCompileFlags(void)
  requires True;
  ensures  view' = view;
{
  uLong flags;

  flags = 0;
  switch ((int)(sizeof(uInt))) {
  case 2:   break;
  case 4:   flags += 1;     break;
  case 8:   flags += 2;     break;
  default:  flags += 3;
  }
  switch ((int)(sizeof(uLong))) {
  case 2:   break;
  case 4:   flags += 1 << 2;    break;
  case 8:   flags += 2 << 2;    break;
  default:  flags += 3 << 2;
  }
  switch ((int)(sizeof(voidpf))) {
  case 2:   break;
  case 4:   flags += 1 << 4;    break;
  case 8:   flags += 2 << 4;    break;
  default:  flags += 3 << 4;
  }
  switch ((int)(sizeof(z_off_t))) {
  case 2:   break;
  case 4:   flags += 1 << 6;    break;
  case 8:   flags += 2 << 6;    break;
  default:  flags += 3 << 6;
  }
  return flags;
}

c_fn const char * ZEXPORT zError(int err) {
  return ERR_MSG(err);
}

c_fn voidpf ZLIB_INTERNAL zcalloc(voidpf opaque, unsigned items, unsigned size) {
  (void)opaque;
  return sizeof(uInt) > 2 ? (voidpf)malloc(items * size) :
                            (voidpf)calloc(items, size);
}

c_fn void ZLIB_INTERNAL zcfree(voidpf opaque, voidpf ptr) {
  (void)opaque;
  free(ptr);
}

c_tu_end zutilTU

end Zlib.Zutil
