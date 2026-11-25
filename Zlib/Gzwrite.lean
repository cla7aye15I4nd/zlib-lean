import C99.DSL
import Zlib.Headers.Common

/-!
# `gzwrite.c` — Gzip File Writing and Compression
-/

namespace Zlib.Gzwrite

open C99 Zlib.Spec

c_tu_begin gzwriteTU "gzwrite.c"

c_include_local "abi_gz.h"

c_fn local int gz_init(gz_statep state) {
  int ret;
  z_streamp strm = &(state->strm);

  state->in = (unsigned char *)malloc(state->want << 1);
  if (state->in == NULL) {
    gz_error(state, Z_MEM_ERROR, "out of memory");
    return -1;
  }

  if (!state->direct) {
    state->out = (unsigned char *)malloc(state->want);
    if (state->out == NULL) {
      free(state->in);
      gz_error(state, Z_MEM_ERROR, "out of memory");
      return -1;
    }

    strm->zalloc = Z_NULL;
    strm->zfree = Z_NULL;
    strm->opaque = Z_NULL;
    ret = deflateInit2(strm, state->level, Z_DEFLATED,
                       MAX_WBITS + 16, DEF_MEM_LEVEL, state->strategy);
    if (ret != Z_OK) {
      free(state->out);
      free(state->in);
      gz_error(state, Z_MEM_ERROR, "out of memory");
      return -1;
    }
  }
  strm->next_in = NULL;

  state->size = state->want;

  if (!state->direct) {
    strm->avail_out = state->size;
    strm->next_out = state->out;
    state->x.next = strm->next_out;
  }
  return 0;
}

c_fn local int gz_comp(gz_statep state, int flush) {
  int ret, writ;
  unsigned have, put, max = ((unsigned)-1 >> 2) + 1;
  z_streamp strm = &(state->strm);

  if (state->size == 0 && gz_init(state) == -1)
    return -1;

  if (state->direct) {
    while (strm->avail_in) {
      errno = 0;
      state->again = 0;
      put = strm->avail_in > max ? max : strm->avail_in;
      writ = (int)write(state->fd, strm->next_in, put);
      if (writ < 0) {
        if (BLOCKED(errno))
          state->again = 1;
        gz_error(state, Z_ERRNO, zstrerror());
        return -1;
      }
      strm->avail_in -= (unsigned)writ;
      strm->next_in += writ;
    }
    return 0;
  }

  if (state->reset) {
    if (strm->avail_in == 0 && flush == Z_NO_FLUSH)
      return 0;
    deflateReset(strm);
    state->reset = 0;
  }

  ret = Z_OK;
  do {
    if (strm->avail_out == 0 || (flush != Z_NO_FLUSH &&
        (flush != Z_FINISH || ret == Z_STREAM_END))) {
      while (strm->next_out > state->x.next) {
        errno = 0;
        state->again = 0;
        put = strm->next_out - state->x.next > (int)max ? max :
              (unsigned)(strm->next_out - state->x.next);
        writ = (int)write(state->fd, state->x.next, put);
        if (writ < 0) {
          if (BLOCKED(errno))
            state->again = 1;
          gz_error(state, Z_ERRNO, zstrerror());
          return -1;
        }
        state->x.next += writ;
      }
      if (strm->avail_out == 0) {
        strm->avail_out = state->size;
        strm->next_out = state->out;
        state->x.next = state->out;
      }
    }

    have = strm->avail_out;
    ret = deflate(strm, flush);
    if (ret == Z_STREAM_ERROR) {
      gz_error(state, Z_STREAM_ERROR, "internal error: deflate stream corrupt");
      return -1;
    }
    have -= strm->avail_out;
  } while (have);

  if (flush == Z_FINISH)
    state->reset = 1;

  return 0;
}

c_fn local int gz_zero(gz_statep state) {
  int first, ret;
  unsigned n;
  z_streamp strm = &(state->strm);

  if (state->size == 0 && gz_init(state) == -1)
    return -1;

  if (strm->avail_in && gz_comp(state, Z_NO_FLUSH) == -1)
    return -1;

  first = 1;
  do {
    n = GT_OFF(state->size) || (z_off64_t)state->size > state->skip ?
        (unsigned)state->skip : state->size;
    if (first) {
      memset(state->in, 0, n);
      first = 0;
    }
    strm->avail_in = n;
    strm->next_in = state->in;
    ret = gz_comp(state, Z_NO_FLUSH);
    n -= strm->avail_in;
    state->x.pos += n;
    state->skip -= n;
    if (ret == -1) {
      strm->avail_in = 0;
      strm->next_in = state->in;
      return -1;
    }
  } while (state->skip);
  return 0;
}

c_fn local z_size_t gz_write(gz_statep state, voidpc buf, z_size_t len) {
  z_size_t put = len;
  z_off64_t room;
  int ret;

  if (len == 0)
    return 0;

  if (state->size == 0 && gz_init(state) == -1)
    return 0;

  if (state->skip && gz_zero(state) == -1)
    return 0;

  room = GZ_OFF_MAX - state->x.pos;
  if ((z_off64_t)(z_size_t)room == room && (z_size_t)room < len) {
    gz_error(state, Z_DATA_ERROR, "position overflow");
    return 0;
  }

  if (len < state->size) {
    for (;;) {
      unsigned have, copy;

      if (state->strm.avail_in == 0)
        state->strm.next_in = state->in;
      have = (unsigned)((state->strm.next_in + state->strm.avail_in) - state->in);
      copy = state->size - have;
      if (copy > len)
        copy = (unsigned)len;
      memcpy(state->in + have, buf, copy);
      state->strm.avail_in += copy;
      state->x.pos += copy;
      buf = (const char *)buf + copy;
      len -= copy;
      if (len == 0)
        break;
      if (gz_comp(state, Z_NO_FLUSH) == -1)
        return state->again ? put - len : 0;
    }
  }
  else {
    if (state->strm.avail_in && gz_comp(state, Z_NO_FLUSH) == -1)
      return 0;

    state->strm.next_in = (z_const Bytef *)buf;
    do {
      unsigned n = (unsigned)-1;

      if (n > len)
        n = (unsigned)len;
      state->strm.avail_in = n;
      ret = gz_comp(state, Z_NO_FLUSH);
      n -= state->strm.avail_in;
      state->x.pos += n;
      len -= n;
      if (ret == -1) {
        state->strm.avail_in = 0;
        state->strm.next_in = state->in;
        return state->again ? put - len : 0;
      }
    } while (len);
    state->strm.next_in = state->in;
  }

  return put;
}

c_fn int ZEXPORT gzwrite(gzFile file, voidpc buf, unsigned len)
  requires gz_ready(file) && disjoint_owned(buf);
  requires file == NULL || len == 0 || len >= (1 << 31) || readable(buf, len);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return 0;
  state = (gz_statep)file;

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again))
    return 0;
  gz_error(state, Z_OK, NULL);

  if ((int)len < 0) {
    gz_error(state, Z_DATA_ERROR, "requested length does not fit in int");
    return 0;
  }

  return (int)gz_write(state, buf, len);
}

c_fn z_size_t ZEXPORT gzfwrite(voidpc buf, z_size_t size, z_size_t nitems, gzFile file)
  requires gz_ready(file) && disjoint_owned(buf);
  requires file == NULL || size * nitems == 0 || size * nitems >= (1 << 64) || readable(buf, size * nitems);
  ensures  view' == view;
{
  z_size_t len;
  gz_statep state;

  if (file == NULL)
    return 0;
  state = (gz_statep)file;

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again))
    return 0;
  gz_error(state, Z_OK, NULL);

  len = nitems * size;
  if (size && len / size != nitems) {
    gz_error(state, Z_STREAM_ERROR, "request does not fit in a size_t");
    return 0;
  }

  return len ? gz_write(state, buf, len) / size : 0;
}

c_fn int ZEXPORT gzputc(gzFile file, int c)
  requires gz_ready(file);
  ensures  view' == view;
{
  unsigned have;
  unsigned char buf[1];
  gz_statep state;
  z_streamp strm;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  strm = &(state->strm);

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again))
    return -1;
  gz_error(state, Z_OK, NULL);

  if (state->skip && gz_zero(state) == -1)
    return -1;

  if (state->size) {
    if (strm->avail_in == 0)
      strm->next_in = state->in;
    have = (unsigned)((strm->next_in + strm->avail_in) - state->in);
    if (have < state->size && state->x.pos < GZ_OFF_MAX) {
      state->in[have] = (unsigned char)c;
      strm->avail_in++;
      state->x.pos++;
      return c & 0xff;
    }
  }

  buf[0] = (unsigned char)c;
  if (gz_write(state, buf, 1) != 1)
    return -1;
  return c & 0xff;
}

c_fn int ZEXPORT gzputs(gzFile file, const char *s)
  requires gz_ready(file) && disjoint_owned(s) && (file == NULL || cstring(s));
  ensures  view' == view;
{
  z_size_t len, put;
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again))
    return -1;
  gz_error(state, Z_OK, NULL);

  len = strlen(s);
  if ((int)len < 0 || (unsigned)len != len) {
    gz_error(state, Z_STREAM_ERROR, "string length does not fit in int");
    return -1;
  }
  put = gz_write(state, s, len);
  return len && put == 0 ? -1 : (int)put;
}

c_fn local int gz_vacate(gz_statep state) {
  z_streamp strm;

  strm = &(state->strm);
  if (strm->next_in == NULL ||
      strm->next_in + strm->avail_in <= state->in + state->size)
    return 0;
  (void)gz_comp(state, Z_NO_FLUSH);
  if (strm->avail_in == 0) {
    strm->next_in = state->in;
    return 0;
  }
  memmove(state->in, strm->next_in, strm->avail_in);
  strm->next_in = state->in;
  return strm->avail_in > state->size;
}

c_fn int ZEXPORTVA gzvprintf(gzFile file, const char *format, va_list va) {
  int len, ret;
  char *next;
  gz_statep state;
  z_streamp strm;

  if (file == NULL)
    return Z_STREAM_ERROR;
  state = (gz_statep)file;
  strm = &(state->strm);

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again))
    return Z_STREAM_ERROR;
  gz_error(state, Z_OK, NULL);

  if (state->size == 0 && gz_init(state) == -1)
    return state->err;

  if (state->skip && gz_zero(state) == -1)
    return state->err;

  ret = gz_vacate(state);
  if (state->err) {
    if (ret && state->again) {
      gz_error(state, Z_BUF_ERROR, "stalled write on gzprintf");
      return state->err;
    }
    if (!state->again)
      return state->err;
  }
  if (strm->avail_in == 0)
    strm->next_in = state->in;
  next = (char *)(state->in + (strm->next_in - state->in) + strm->avail_in);
  next[state->size - 1] = 0;
  len = vsnprintf(next, state->size, format, va);

  if (len == 0 || (unsigned)len >= state->size || next[state->size - 1] != 0)
    return 0;

  if (GZ_OFF_MAX - state->x.pos < len) {
    gz_error(state, Z_DATA_ERROR, "position overflow");
    return state->err;
  }

  strm->avail_in += (unsigned)len;
  state->x.pos += len;

  ret = gz_vacate(state);
  if (ret) {
    strm->avail_in -= (unsigned)len;
    state->x.pos -= len;
    if (state->again)
      gz_error(state, Z_BUF_ERROR, "stalled write on gzprintf");
    return state->err;
  }
  if (state->err && !state->again)
    return state->err;
  return len;
}

c_fn int ZEXPORTVA gzprintf(gzFile file, const char *format, ...)
  requires gz_ready(file) && disjoint_owned(format) && (file == NULL || safe_fmt(format));
  requires forall(a in vaArgs, disjoint_owned(a));
  ensures  view' == view;
{
  va_list va;
  int ret;

  va_start(va, format);
  ret = gzvprintf(file, format, va);
  va_end(va);
  return ret;
}

c_fn int ZEXPORT gzflush(gzFile file, int flush)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return Z_STREAM_ERROR;
  state = (gz_statep)file;

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again))
    return Z_STREAM_ERROR;
  gz_error(state, Z_OK, NULL);

  if (flush < 0 || flush > Z_FINISH)
    return Z_STREAM_ERROR;

  if (state->skip && gz_zero(state) == -1)
    return state->err;

  (void)gz_comp(state, flush);
  return state->err;
}

c_fn int ZEXPORT gzsetparams(gzFile file, int level, int strategy)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;
  z_streamp strm;

  if (file == NULL)
    return Z_STREAM_ERROR;
  state = (gz_statep)file;
  strm = &(state->strm);

  if (state->mode != GZ_WRITE || (state->err != Z_OK && !state->again) ||
      state->direct)
    return Z_STREAM_ERROR;
  gz_error(state, Z_OK, NULL);

  if (level == state->level && strategy == state->strategy)
    return Z_OK;

  if (state->skip && gz_zero(state) == -1)
    return state->err;

  if (state->size) {
    if (strm->avail_in && gz_comp(state, Z_BLOCK) == -1)
      return state->err;
    deflateParams(strm, level, strategy);
  }
  state->level = level;
  state->strategy = strategy;
  return Z_OK;
}

c_fn int ZEXPORT gzclose_w(gzFile file)
  requires gz_ready(file);
  ensures  view' == view.closeGz(file, m');
{
  int ret = Z_OK;
  gz_statep state;

  if (file == NULL)
    return Z_STREAM_ERROR;
  state = (gz_statep)file;

  if (state->mode != GZ_WRITE)
    return Z_STREAM_ERROR;

  if (state->skip && gz_zero(state) == -1)
    ret = state->err;

  if (gz_comp(state, Z_FINISH) == -1)
    ret = state->err;
  if (state->size) {
    if (!state->direct) {
      (void)deflateEnd(&(state->strm));
      free(state->out);
    }
    free(state->in);
  }
  gz_error(state, Z_OK, NULL);
  free(state->path);
  if (close(state->fd) == -1)
    ret = Z_ERRNO;
  free(state);
  return ret;
}

c_tu_end gzwriteTU

end Zlib.Gzwrite
