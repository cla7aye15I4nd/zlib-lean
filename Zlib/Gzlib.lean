import C99.DSL
import Zlib.Headers.Common

/-!
# `gzlib.c` — Gzip File Handling, Opening, Seeking, and Errors
-/

namespace Zlib.Gzlib

open C99 Zlib.Spec

c_tu_begin gzlibTU "gzlib.c"

c_include_local "abi_gz.h"

c_define_const LOOK := 0
c_define_const COPY := 1
c_define_const GZIP := 2

c_fn local void gz_reset(gz_statep state) {
  state->x.have = 0;
  state->past = 0;
  if (state->mode == GZ_READ) {
    state->eof = 0;
    state->how = LOOK;
    state->junk = -1;
  }
  else
    state->reset = 0;
  state->again = 0;
  state->skip = 0;
  gz_error(state, Z_OK, NULL);
  state->x.pos = 0;
  state->strm.avail_in = 0;
}

c_fn local gzFile gz_open(const void *path, int fd, const char *mode) {
  gz_statep state;
  z_size_t len;
  int oflag = 0;
  int exclusive = 0;

  if (path == NULL || mode == NULL)
    return NULL;

  state = (gz_statep)malloc(sizeof(gz_state));
  if (state == NULL)
    return NULL;
  state->size = 0;
  state->want = GZBUFSIZE;
  state->err = Z_OK;
  state->msg = NULL;

  state->mode = GZ_NONE;
  state->level = Z_DEFAULT_COMPRESSION;
  state->strategy = Z_DEFAULT_STRATEGY;
  state->direct = 0;
  while (*mode) {
    if (*mode >= '0' && *mode <= '9')
      state->level = *mode - '0';
    else
      switch (*mode) {
      case 'r':
        state->mode = GZ_READ;
        break;
      case 'w':
        state->mode = GZ_WRITE;
        break;
      case 'a':
        state->mode = GZ_APPEND;
        break;
      case '+':
        free(state);
        return NULL;
      case 'b':
        break;
      case 'e':
        oflag |= O_CLOEXEC;
        break;
      case 'x':
        exclusive = 1;
        break;
      case 'f':
        state->strategy = Z_FILTERED;
        break;
      case 'h':
        state->strategy = Z_HUFFMAN_ONLY;
        break;
      case 'R':
        state->strategy = Z_RLE;
        break;
      case 'F':
        state->strategy = Z_FIXED;
        break;
      case 'G':
        state->direct = -1;
        break;
      case 'N':
        oflag |= O_NONBLOCK;
        break;
      case 'T':
        state->direct = 1;
        break;
      default:
        ;
      }
    mode++;
  }

  if (state->mode == GZ_NONE) {
    free(state);
    return NULL;
  }

  if (state->mode == GZ_READ) {
    if (state->direct == 1) {
      free(state);
      return NULL;
    }
    if (state->direct == 0)
      state->direct = 1;
  }
  else if (state->direct == -1) {
    free(state);
    return NULL;
  }

  len = strlen((const char *)path);
  state->path = (char *)malloc(len + 1);
  if (state->path == NULL) {
    free(state);
    return NULL;
  }
  {
    (void)snprintf(state->path, len + 1, "%s", (const char *)path);
  }

  oflag |= O_LARGEFILE |
      (state->mode == GZ_READ ?
       O_RDONLY :
       (O_WRONLY | O_CREAT |
        (exclusive ? O_EXCL : 0) |
        (state->mode == GZ_WRITE ? O_TRUNC : O_APPEND)));

  if (fd == -1)
    state->fd = open((const char *)path, oflag, 0666);
  else {
    if (oflag & O_NONBLOCK)
      fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
    if (oflag & O_CLOEXEC)
      fcntl(fd, F_SETFD, fcntl(fd, F_GETFD) | FD_CLOEXEC);
    state->fd = fd;
  }
  if (state->fd == -1) {
    free(state->path);
    free(state);
    return NULL;
  }
  if (state->mode == GZ_APPEND) {
    LSEEK(state->fd, 0, SEEK_END);
    state->mode = GZ_WRITE;
  }

  if (state->mode == GZ_READ) {
    state->start = LSEEK(state->fd, 0, SEEK_CUR);
    if (state->start == -1) state->start = 0;
  }

  gz_reset(state);

  return (gzFile)state;
}

c_fn gzFile ZEXPORT gzopen(const char *path, const char *mode)
  requires opt_cstring(path) && opt_cstring(mode);
  ensures  view' == (ret == NULL ? view : view.addGz(ret));
{
  return gz_open(path, -1, mode);
}

c_fn gzFile ZEXPORT gzopen64(const char *path, const char *mode)
  requires opt_cstring(path) && opt_cstring(mode);
  ensures  view' == (ret == NULL ? view : view.addGz(ret));
{
  return gz_open(path, -1, mode);
}

c_fn gzFile ZEXPORT gzdopen(int fd, const char *mode)
  requires opt_cstring(mode);
  ensures  view' == (ret == NULL ? view : view.addGz(ret));
{
  char *path;
  gzFile gz;

  if (fd < 0 || (path = (char *)malloc(7 + 3 * sizeof(int))) == NULL)
    return NULL;
  (void)snprintf(path, 7 + 3 * sizeof(int), "<fd:%d>", fd);
  gz = gz_open(path, fd, mode);
  free(path);
  return gz;
}

c_fn int ZEXPORT gzbuffer(gzFile file, unsigned size)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return -1;

  if (state->size != 0)
    return -1;

  if ((size << 1) < size)
    return -1;
  if (size < 8)
    size = 8;
  state->want = size;
  return 0;
}

c_fn int ZEXPORT gzrewind(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;

  if (state->mode != GZ_READ ||
      (state->err != Z_OK && state->err != Z_BUF_ERROR))
    return -1;

  if (LSEEK(state->fd, state->start, SEEK_SET) == -1)
    return -1;
  gz_reset(state);
  return 0;
}

c_fn z_off64_t ZEXPORT gzseek64(gzFile file, z_off64_t offset, int whence)
  requires gz_ready(file);
  ensures  view' == view;
{
  unsigned n;
  z_off64_t ret, pos;
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return -1;

  if (state->err != Z_OK && state->err != Z_BUF_ERROR)
    return -1;

  if (whence != SEEK_SET && whence != SEEK_CUR)
    return -1;

  pos = whence == SEEK_SET ? 0 :
        state->x.pos + (state->past ? 0 : state->skip);
  if (pos > 0 && offset > GZ_OFF_MAX - pos)
    return -1;
  if (offset < -pos)
    return -1;
  pos += offset;

  if (state->x.pos < 0 && pos > GZ_OFF_MAX + state->x.pos)
    return -1;

  if (state->mode == GZ_READ && state->how == COPY) {
    ret = LSEEK(state->fd, pos - state->x.pos - (z_off64_t)state->x.have,
                SEEK_CUR);
    if (ret == -1)
      return -1;
    state->x.have = 0;
    state->eof = 0;
    state->past = 0;
    state->skip = 0;
    gz_error(state, Z_OK, NULL);
    state->strm.avail_in = 0;
    state->x.pos = pos;
    return pos;
  }

  if (pos < state->x.pos) {
    if (state->mode != GZ_READ)
      return -1;
    if (gzrewind(file) == -1)
      return -1;
  }
  offset = pos - state->x.pos;

  if (state->mode == GZ_READ) {
    n = GT_OFF(state->x.have) || (z_off64_t)state->x.have > offset ?
        (unsigned)offset : state->x.have;
    state->x.have -= n;
    state->x.next += n;
    state->x.pos += n;
    offset -= n;
  }

  state->skip = offset;
  return pos;
}

c_fn z_off_t ZEXPORT gzseek(gzFile file, z_off_t offset, int whence)
  requires gz_ready(file);
  ensures  view' == view;
{
  z_off64_t ret;

  ret = gzseek64(file, (z_off64_t)offset, whence);
  return ret == (z_off_t)ret ? (z_off_t)ret : -1;
}

c_fn z_off64_t ZEXPORT gztell64(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return -1;

  return state->x.pos + (state->past ? 0 : state->skip);
}

c_fn z_off_t ZEXPORT gztell(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  z_off64_t ret;

  ret = gztell64(file);
  return ret == (z_off_t)ret ? (z_off_t)ret : -1;
}

c_fn z_off64_t ZEXPORT gzoffset64(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  z_off64_t offset;
  gz_statep state;

  if (file == NULL)
    return -1;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return -1;

  offset = LSEEK(state->fd, 0, SEEK_CUR);
  if (offset < 0)
    return -1;
  if (state->mode == GZ_READ)
    offset -= state->strm.avail_in;
  return offset;
}

c_fn z_off_t ZEXPORT gzoffset(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  z_off64_t ret;

  ret = gzoffset64(file);
  return ret == (z_off_t)ret ? (z_off_t)ret : -1;
}

c_fn int ZEXPORT gzeof(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return 0;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return 0;

  return state->mode == GZ_READ ? state->past : 0;
}

c_fn const char * ZEXPORT gzerror(gzFile file, int *errnum)
  requires gz_ready(file) && valid_or_null(errnum) && disjoint_owned(errnum);
  modifies errnum;
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return NULL;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return NULL;

  if (errnum != NULL)
    *errnum = state->err;
  return state->err == Z_MEM_ERROR ? "out of memory" :
                                     (state->msg == NULL ? "" : state->msg);
}

c_fn void ZEXPORT gzclearerr(gzFile file)
  requires gz_ready(file);
  ensures  view' == view;
{
  gz_statep state;

  if (file == NULL)
    return;
  state = (gz_statep)file;
  if (state->mode != GZ_READ && state->mode != GZ_WRITE)
    return;

  if (state->mode == GZ_READ) {
    state->eof = 0;
    state->past = 0;
  }
  gz_error(state, Z_OK, NULL);
}

c_fn void ZLIB_INTERNAL gz_error(gz_statep state, int err, const char *msg) {
  if (state->msg != NULL) {
    if (state->err != Z_MEM_ERROR)
      free(state->msg);
    state->msg = NULL;
  }

  state->err = err;
  if (msg == NULL)
    return;

  if (err == Z_MEM_ERROR)
    return;

  if ((state->msg = (char *)malloc(strlen(state->path) + strlen(msg) + 3)) == NULL) {
    state->err = Z_MEM_ERROR;
    return;
  }
  (void)snprintf(state->msg, strlen(state->path) + strlen(msg) + 3,
                 "%s%s%s", state->path, ": ", msg);
}

c_fn unsigned ZLIB_INTERNAL gz_intmax(void) {
  return INT_MAX;
}

c_tu_end gzlibTU

end Zlib.Gzlib
