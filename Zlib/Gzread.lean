import C99.DSL
import Zlib.Headers.Common

/-!
# `gzread.c` — Gzip File Reading and Decompression
-/

namespace Zlib.Gzread

open C99 Zlib.Spec

c_tu_begin gzreadTU "gzread.c"

c_include_local "abi_gz.h"

c_define_const LOOK := 0
c_define_const COPY := 1
c_define_const GZIP := 2

c_fn local int gz_load(gz_statep state, unsigned char *buf, unsigned len, unsigned *have) {
  int ret;
  unsigned get, max = ((unsigned)-1 >> 2) + 1;

  state->again = 0;
  errno = 0;
  *have = 0;
  do {
    get = len - *have;
    if (get > max)
      get = max;
    ret = (int)read(state->fd, buf + *have, get);
    if (ret <= 0)
      break;
    *have += (unsigned)ret;
  } while (*have < len);
  if (ret < 0) {
    if (BLOCKED(errno)) {
      state->again = 1;
      if (*have != 0)
        return 0;
    }
    gz_error(state, Z_ERRNO, zstrerror());
    return -1;
  }
  if (ret == 0)
    state->eof = 1;
  return 0;
}

c_fn local int gz_avail(gz_statep state) {
  unsigned got;
  z_streamp strm = &(state->strm);

  if (state->err != Z_OK && state->err != Z_BUF_ERROR)
    return -1;
  if (state->eof == 0) {
    if (strm->avail_in) {
      unsigned char *p = state->in;
      const unsigned char *q = strm->next_in;

      if (q != p) {
        unsigned n = strm->avail_in;

        do {
          *p++ = *q++;
        } while (.-n);
      }
    }
    if (gz_load(state, state->in + strm->avail_in,
                state->size - strm->avail_in, &got) == -1)
      return -1;
    strm->avail_in += got;
    strm->next_in = state->in;
  }
  return 0;
}

c_fn local unsigned gz_room(gz_statep state, unsigned max) {
  if (state->x.pos > 0 && GZ_OFF_MAX - state->x.pos < max)
    return (unsigned)(GZ_OFF_MAX - state->x.pos);
  return max;
}

c_fn local int gz_look(gz_statep state) {
  z_streamp strm = &(state->strm);

  if (state->size == 0) {
    state->in = (unsigned char *)malloc(state->want);
    state->out = (unsigned char *)malloc(state->want << 1);
    if (state->in == NULL || state->out == NULL) {
      free(state->out);
      free(state->in);
      gz_error(state, Z_MEM_ERROR, "out of memory");
      return -1;
    }
    state->size = state->want;

    state->strm.zalloc = Z_NULL;
    state->strm.zfree = Z_NULL;
    state->strm.opaque = Z_NULL;
    state->strm.avail_in = 0;
    state->strm.next_in = Z_NULL;
    if (inflateInit2(&(state->strm), 15 + 16) != Z_OK) {
      free(state->out);
      free(state->in);
      state->size = 0;
      gz_error(state, Z_MEM_ERROR, "out of memory");
      return -1;
    }
  }

  if (state->direct == -1 || state->junk == 0) {
    if (state->junk == 0 && strm->avail_in == 0) {
      if (gz_avail(state) == -1)
        return -1;
      if (strm->avail_in == 0)
        return 0;
    }
    inflateReset(strm);
    state->how = GZIP;
    state->junk = state->junk != -1;
    state->direct = 0;
    return 0;
  }

  if (gz_avail(state) == -1)
    return -1;
  if (strm->avail_in == 0 || (state->again && strm->avail_in < 4))
    return 0;

  if (strm->avail_in > 3 &&
      strm->next_in[0] == 31 && strm->next_in[1] == 139 &&
      strm->next_in[2] == 8 && strm->next_in[3] < 32) {
    inflateReset(strm);
    state->how = GZIP;
    state->junk = 0;
    state->direct = 0;
    return 0;
  }

  state->x.next = state->out;
  memcpy(state->x.next, strm->next_in, strm->avail_in);
  state->x.have = gz_room(state, strm->avail_in);
  if (state->x.have < strm->avail_in)
    gz_error(state, Z_DATA_ERROR, "position overflow");
  strm->avail_in = 0;
  state->how = COPY;
  return 0;
}

c_fn local int gz_decomp(gz_statep state) {
  int ret = Z_OK;
  unsigned had;
  z_streamp strm = &(state->strm);

  had = strm->avail_out;
  do {
    if (strm->avail_in == 0 && gz_avail(state) == -1) {
      ret = state->err;
      break;
    }
    if (strm->avail_in == 0) {
      if (!state->again)
        gz_error(state, Z_BUF_ERROR, "unexpected end of file");
      break;
    }

    ret = inflate(strm, Z_NO_FLUSH);
    if (strm->avail_out < had)
      state->junk = 0;
    if (ret == Z_STREAM_ERROR || ret == Z_NEED_DICT) {
      gz_error(state, Z_STREAM_ERROR, "internal error: inflate stream corrupt");
      break;
    }
    if (ret == Z_MEM_ERROR) {
      gz_error(state, Z_MEM_ERROR, "out of memory");
      break;
    }
    if (ret == Z_DATA_ERROR) {
      if (state->junk == 1) {
        strm->avail_in = 0;
        state->eof = 1;
        state->how = LOOK;
        ret = Z_OK;
        break;
      }
      gz_error(state, Z_DATA_ERROR,
               strm->msg == NULL ? "compressed data error" : strm->msg);
      break;
    }
  } while (strm->avail_out && ret != Z_STREAM_END);

  state->x.have = had - strm->avail_out;
  state->x.next = strm->next_out - state->x.have;

  if (ret == Z_STREAM_END) {
    state->junk = 0;
    state->how = LOOK;
    return 0;
  }

  return ret != Z_OK ? -1 : 0;
}

c_fn local int gz_fetch(gz_statep state) {
  unsigned room;
  z_streamp strm = &(state->strm);

  if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again)
    return -1;

  do {
    switch (state->how) {
    case LOOK:
      if (gz_look(state) == -1)
        return -1;
      if (state->how == LOOK)
        return 0;
      break;
    case COPY:
      room = gz_room(state, state->size << 1);
      state->x.next = state->out;
      if (gz_load(state, state->out, room ? room : 1, &(state->x.have)) == -1)
        return -1;
      return 0;
    case GZIP:
      room = gz_room(state, state->size << 1);
      strm->avail_out = room ? room : 1;
      strm->next_out = state->out;
      if (gz_decomp(state) == -1)
        return -1;
      break;
    default:
      gz_error(state, Z_STREAM_ERROR, "state corrupt");
      return -1;
    }
  } while (state->x.have == 0 && (!state->eof || strm->avail_in));
  return 0;
}

c_fn local void gz_skip_have(gz_statep state) {
  unsigned n;

  n = GT_OFF(state->x.have) ||
      (z_off64_t)state->x.have > state->skip ?
      (unsigned)state->skip : state->x.have;
  state->x.have -= n;
  state->x.next += n;
  state->x.pos += n;
  state->skip -= n;
}

c_fn local int gz_skip(gz_statep state) {
  do {
    if (state->x.have)
      gz_skip_have(state);
    else if (state->eof && state->strm.avail_in == 0) {
      if (state->how == GZIP && state->err == Z_OK)
        gz_error(state, Z_BUF_ERROR, "unexpected end of file");
      state->skip = 0;
      state->past = 1;
      break;
    }
    else {
      if (gz_fetch(state) == -1 && state->x.have == 0)
        return -1;
    }
  } while (state->skip);
  return 0;
}

c_fn local z_size_t gz_read(gz_statep state, voidp buf, z_size_t len) {
  z_size_t got;
  unsigned n;
  int err;

  if (len == 0)
    return 0;

  if (state->skip && gz_skip(state) == -1)
    return 0;

  got = 0;
  err = 0;
  do {
    n = (unsigned)-1;
    if (n > len)
      n = (unsigned)len;

    n = gz_room(state, n);
    if (n == 0 && state->x.have) {
      state->x.have = 0;
      gz_error(state, Z_DATA_ERROR, "position overflow");
      break;
    }

    if (state->x.have) {
      if (state->x.have < n)
        n = state->x.have;
      memcpy(buf, state->x.next, n);
      state->x.next += n;
      state->x.have -= n;
      if (state->err != Z_OK)
        err = -1;
    }
    else if (state->eof && state->strm.avail_in == 0) {
      if (state->how == GZIP && state->err == Z_OK)
        gz_error(state, Z_BUF_ERROR, "unexpected end of file");
      break;
    }
    else if (state->how == LOOK || n < (state->size << 1)) {
      if (gz_fetch(state) == -1 && state->x.have == 0)
        err = -1;
      continue;
    }
    else if (state->how == COPY)
      err = gz_load(state, (unsigned char *)buf, n, &n);
    else {
      state->strm.avail_out = n;
      state->strm.next_out = (unsigned char *)buf;
      err = gz_decomp(state);
      n = state->x.have;
      state->x.have = 0;
    }

    len -= n;
    buf = (char *)buf + n;
    got += n;
    state->x.pos += n;
  } while (len && !err);

  if (len && state->eof)
    state->past = 1;

  return got;
}

c_fn int ZEXPORT gzread(gzFile file, voidp buf, unsigned len)
  requires gz_ready(file) && disjoint_owned(buf);
  requires file == NULL || len == 0 || len >= (1 << 31) || writable(buf, len);
  modifies buf;
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ)
    return -1;

  if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again &&
      state->x.have == 0)
    return -1;
  if (state->again)
    gz_error(state, Z_OK, NULL);

  if ((int)len < 0) {
    if (state->err == Z_OK || state->err == Z_BUF_ERROR)
      gz_error(state, Z_STREAM_ERROR, "request does not fit in an int");
    return -1;
  }

  len = (unsigned)gz_read(state, buf, len);

  if (len == 0) {
    if (state->err != Z_OK && state->err != Z_BUF_ERROR)
      return -1;
    if (state->again) {
      gz_error(state, Z_ERRNO, zstrerror());
      return -1;
    }
  }

  return (int)len;
}

c_fn z_size_t ZEXPORT gzfread(voidp buf, z_size_t size, z_size_t nitems, gzFile file)
  requires gz_ready(file) && disjoint_owned(buf);
  requires file == NULL || size * nitems == 0 || size * nitems >= (1 << 64) || writable(buf, size * nitems);
  modifies buf;
  ensures  view' == view;
{
  z_size_t len;
  gz_statep state;

  if (file == NULL)
    return 0;
  state = (gz_statep)file;
  if (state->mode != GZ_READ)
    return 0;

  if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again &&
      state->x.have == 0)
    return 0;
  if (state->again)
    gz_error(state, Z_OK, NULL);

  len = nitems * size;
  if (size && len / size != nitems) {
    if (state->err == Z_OK || state->err == Z_BUF_ERROR)
      gz_error(state, Z_STREAM_ERROR, "request does not fit in a size_t");
    return 0;
  }

  return len ? gz_read(state, buf, len) / size : 0;
}

c_fn int ZEXPORT gzgetc(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  unsigned char buf[1];
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ)
    return -1;

  if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again &&
      state->x.have == 0)
    return -1;
  if (state->again)
    gz_error(state, Z_OK, NULL);

  if (state->x.have) {
    state->x.have.-;
    state->x.pos++;
    return *(state->x.next)++;
  }

  return gz_read(state, buf, 1) < 1 ? -1 : buf[0];
}

c_fn int ZEXPORT gzgetc_(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  return gzgetc(file);
}

c_fn int ZEXPORT gzungetc(int c, gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ)
    return -1;

  if (state->how == LOOK && state->x.have == 0)
    (void)gz_look(state);

  if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again &&
      state->size == 0)
    return -1;
  if (state->again)
    gz_error(state, Z_OK, NULL);

  if (state->skip && gz_skip(state) == -1)
    return -1;

  if (c < 0)
    return -1;

  if (state->x.have == 0) {
    state->x.have = 1;
    state->x.next = state->out + (state->size << 1) - 1;
    state->x.next[0] = (unsigned char)c;
    state->x.pos.-;
    state->past = 0;
    return c;
  }

  if (state->x.have == (state->size << 1)) {
    if (state->err == Z_OK || state->err == Z_BUF_ERROR)
      gz_error(state, Z_DATA_ERROR, "out of room to push characters");
    return -1;
  }

  if (state->x.next == state->out) {
    unsigned char *src = state->out + state->x.have;
    unsigned char *dest = state->out + (state->size << 1);

    while (src > state->out)
      *.-dest = *.-src;
    state->x.next = dest;
  }
  state->x.have++;
  state->x.next.-;
  state->x.next[0] = (unsigned char)c;
  state->x.pos.-;
  state->past = 0;
  return c;
}

c_fn char * ZEXPORT gzgets(gzFile file, char *buf, int len)
  requires gz_ready(file) && disjoint_owned(buf);
  requires file == NULL || buf == NULL || len < 1 || writable(buf, len);
  modifies buf;
  ensures  view' == view;
{
  unsigned left, n;
  char *str;
  unsigned char *eol;
  gz_statep state;

  if (file == NULL || buf == NULL || len < 1)
    return NULL;
  state = (gz_statep)file;
  if (state->mode != GZ_READ)
    return NULL;

  if (state->err != Z_OK && state->err != Z_BUF_ERROR && !state->again &&
      state->x.have == 0)
    return NULL;
  if (state->again)
    gz_error(state, Z_OK, NULL);

  if (state->skip && gz_skip(state) == -1)
    return NULL;

  str = buf;
  left = (unsigned)len - 1;
  if (left) do {
    if (state->x.have == 0 && gz_fetch(state) == -1 &&
        state->x.have == 0)
      break;
    if (state->x.have == 0) {
      state->past = 1;
      break;
    }

    n = state->x.have > left ? left : state->x.have;
    n = gz_room(state, n);
    if (n == 0) {
      state->x.have = 0;
      gz_error(state, Z_DATA_ERROR, "position overflow");
      break;
    }
    eol = (unsigned char *)memchr(state->x.next, '\n', n);
    if (eol != NULL)
      n = (unsigned)(eol - state->x.next) + 1;

    memcpy(buf, state->x.next, n);
    state->x.have -= n;
    state->x.next += n;
    state->x.pos += n;
    left -= n;
    buf += n;
  } while (left && eol == NULL);

  if (buf == str && len > 1)
    return NULL;
  buf[0] = 0;
  return str;
}

c_fn int ZEXPORT gzdirect(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return 0;
  state = (gz_statep)file;

  if (state->mode == GZ_READ && state->how == LOOK && state->x.have == 0) {
    (void)gz_look(state);
    gz_skip_have(state);
  }

  return state->direct == 1;
}

c_fn int ZEXPORT gzclose_r(gzFile file)
  requires gz_ready(file);
  ensures  view' == view.closeGz(file, m');
{
  int ret, err;
  gz_statep state;

  if (file == NULL)
    return Z_STREAM_ERROR;
  state = (gz_statep)file;
  if (state->mode != GZ_READ)
    return Z_STREAM_ERROR;

  if (state->size) {
    inflateEnd(&(state->strm));
    free(state->out);
    free(state->in);
  }
  err = state->err == Z_BUF_ERROR ? Z_BUF_ERROR : Z_OK;
  gz_error(state, Z_OK, NULL);
  free(state->path);
  ret = close(state->fd);
  free(state);
  return ret ? Z_ERRNO : err;
}

c_tu_end gzreadTU

end Zlib.Gzread
