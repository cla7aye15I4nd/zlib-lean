import C99.DSL
import Zlib.Headers.Common

/-!
# `gzclose.c` — Close a Gzip File Stream
-/

namespace Zlib.Gzclose

open C99 Zlib.Spec

c_tu_begin gzcloseTU "gzclose.c"

c_include_local "abi_gz.h"

c_fn int ZEXPORT gzclose(gzFile file)
  requires gz_ready(file);
  modifies file;
  ensures  view' == view.closeGz(file, m');
{
  gz_statep state;

  if (file == NULL)
    return Z_STREAM_ERROR;
  state = (gz_statep)file;

  return state->mode == GZ_READ ? gzclose_r(file) : gzclose_w(file);
}

c_tu_end gzcloseTU

end Zlib.Gzclose
