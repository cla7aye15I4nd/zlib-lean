import C99.DSL
import Zlib.Spec.Memory

/-!
# Shared Zlib Types, ABI Headers, Constants, and Macros (`Zlib.Headers.Common`)

Emits self-contained ABI headers (`abi_common.h`, `abi_deflate.h`, `abi_inflate.h`,
`abi_gz.h`) matching upstream LP64 typedefs, all 10 ABI structs (163 fields), enums,
constants, and shared preprocessor macros.
-/

namespace Zlib.Headers

open C99

c_spec_view Zlib.Spec.ClientView
c_spec_lib Zlib.Spec
c_spec_const STREAM_DEFLATE      := Zlib.Spec.StreamKind.deflate
c_spec_const STREAM_INFLATE      := Zlib.Spec.StreamKind.inflate
c_spec_const STREAM_INFLATE_BACK := Zlib.Spec.StreamKind.inflateBack
c_spec_pred init_stream_ready    [tags, owned, view, m] := Zlib.Spec.InitStreamReady
c_spec_pred stream_alive         [tags, owned, view, m] := Zlib.Spec.StreamAlive
c_spec_pred stream_ready         [tags, owned, view, m] := Zlib.Spec.StreamReady
c_spec_pred gz_ready             [view]                 := Zlib.Spec.GzReady
c_spec_pred deflate_header_ready [tags, owned, m]       := Zlib.Spec.DeflateHeaderReady
c_spec_pred inflate_header_ready [tags, owned, m]       := Zlib.Spec.InflateHeaderReady
c_spec_pred header_disjoint      [tags, m]              := Zlib.Spec.HeaderDisjoint
c_spec_pred dict_writable        [tags, owned, m]       := Zlib.Spec.DictWritable
c_spec_pred writes_stream        [tags, m]              := Zlib.Spec.writesStream

-- Register POSIX off_t aliases in persisted Lean DSL scope without duplicate C typedefs
c_typedef long z_off_t;
c_typedef long z_off64_t;
c_typedef unsigned long size_t;

-- Register zlib C qualifier and linkage macro aliases in persisted DSL scope
c_qual_alias z_const := const
c_qual_alias TCONST := const
c_qual_alias FAR := none
c_link_alias local := static
c_link_alias ZEXPORT := export
c_link_alias ZEXPORTVA := export
c_link_alias ZLIB_INTERNAL := hidden

/-! ## 1. `abi_common.h` -/

c_header_begin abiCommonH "abi_common.h"

c_pp "#ifndef ABI_COMMON_H"
c_pp "#define ABI_COMMON_H"
c_pp "#ifdef _LARGEFILE64_SOURCE"
c_pp "#  ifndef _LARGEFILE_SOURCE"
c_pp "#    define _LARGEFILE_SOURCE 1"
c_pp "#  endif"
c_pp "#  undef _FILE_OFFSET_BITS"
c_pp "#  undef _TIME_BITS"
c_pp "#endif"
c_pp "#ifdef __APPLE__"
c_pp "#  define OS_CODE 19"
c_pp "#else"
c_pp "#  define OS_CODE 3"
c_pp "#endif"

c_include "stddef.h"
c_include "sys/types.h"
c_include "unistd.h"
c_include "stdarg.h"
c_include "limits.h"
c_include "stdlib.h"
c_include "string.h"

c_pp "#if defined(_LARGEFILE64_SOURCE) && _LFS64_LARGEFILE-0"
c_pp "typedef off64_t z_off64_t;"
c_pp "#else"
c_pp "typedef off_t z_off64_t;"
c_pp "#endif"
c_pp "typedef off_t z_off_t;"

c_typedef unsigned char Byte;
c_typedef unsigned int uInt;
c_typedef unsigned long uLong;
c_typedef Byte Bytef;
c_typedef char charf;
c_typedef int intf;
c_typedef uInt uIntf;
c_typedef uLong uLongf;
c_typedef const void *voidpc;
c_typedef void *voidpf;
c_typedef void *voidp;
c_typedef unsigned long z_size_t;
c_typedef unsigned Z_U4;
c_typedef Z_U4 z_crc_t;
c_typedef unsigned long Z_U8;

c_typedef unsigned char uch;
c_typedef uch uchf;
c_typedef unsigned short ush;
c_typedef ush ushf;
c_typedef unsigned long ulg;

c_typedef voidpf (*alloc_func)(voidpf opaque, uInt items, uInt size);
c_typedef void (*free_func)(voidpf opaque, voidpf address);
c_typedef unsigned (*in_func)(void *, z_const unsigned char **);
c_typedef int (*out_func)(void *, unsigned char *, unsigned);

c_fwd struct internal_state;

c_typedef struct z_stream_s {
  z_const Bytef *next_in;
  uInt avail_in;
  uLong total_in;
  Bytef *next_out;
  uInt avail_out;
  uLong total_out;
  z_const char *msg;
  struct internal_state *state;
  alloc_func zalloc;
  free_func zfree;
  voidpf opaque;
  int data_type;
  uLong adler;
  uLong reserved;
} z_stream;
c_typedef z_stream *z_streamp;

c_typedef struct gz_header_s {
  int text;
  uLong time;
  int xflags;
  int os;
  Bytef *extra;
  uInt extra_len;
  uInt extra_max;
  Bytef *name;
  uInt name_max;
  Bytef *comment;
  uInt comm_max;
  int hcrc;
  int done;
} gz_header;
c_typedef gz_header *gz_headerp;

-- Public constants & error codes
c_define ZLIB_VERSION := "1.4.0.1-motley"
c_define ZLIB_VERNUM := 0x1401
c_define ZLIB_VER_MAJOR := 1
c_define ZLIB_VER_MINOR := 4
c_define ZLIB_VER_REVISION := 0
c_define ZLIB_VER_SUBREVISION := 1

c_define Z_NO_FLUSH := 0
c_define Z_PARTIAL_FLUSH := 1
c_define Z_SYNC_FLUSH := 2
c_define Z_FULL_FLUSH := 3
c_define Z_FINISH := 4
c_define Z_BLOCK := 5
c_define Z_TREES := 6

c_define Z_OK := 0
c_define Z_STREAM_END := 1
c_define Z_NEED_DICT := 2
c_define Z_ERRNO := (-1)
c_define Z_STREAM_ERROR := (-2)
c_define Z_DATA_ERROR := (-3)
c_define Z_MEM_ERROR := (-4)
c_define Z_BUF_ERROR := (-5)
c_define Z_VERSION_ERROR := (-6)

c_define Z_NO_COMPRESSION := 0
c_define Z_BEST_SPEED := 1
c_define Z_BEST_COMPRESSION := 9
c_define Z_DEFAULT_COMPRESSION := (-1)

c_define Z_FILTERED := 1
c_define Z_HUFFMAN_ONLY := 2
c_define Z_RLE := 3
c_define Z_FIXED := 4
c_define Z_DEFAULT_STRATEGY := 0

c_define Z_BINARY := 0
c_define Z_TEXT := 1
c_define Z_ASCII := 1
c_define Z_UNKNOWN := 2

c_define Z_DEFLATED := 8
c_define Z_NULL := 0
c_define NULL := 0

c_define MAX_MEM_LEVEL := 9
c_define MAX_WBITS := 15
c_define DEF_WBITS := 15
c_define DEF_MEM_LEVEL := 8

c_define STORED_BLOCK := 0
c_define STATIC_TREES := 1
c_define DYN_TREES := 2
c_define MIN_MATCH := 3
c_define MAX_MATCH := 258
c_define PRESET_DICT := 0x20

c_define_const OS_CODE := 19

-- Utility globals, prototypes, and macros
c_global extern z_const char * const z_errmsg[10];
c_macro ERR_MSG(err) := z_errmsg[(err) < -6 || (err) > 2 ? 9 : 2 - (err)]
c_stmt_macro ERR_RETURN(strm, err) := return ((strm)->msg = ERR_MSG(err), (err));

c_define zmemcpy := memcpy
c_define zmemcmp := memcmp
c_macro zmemzero(dest, len) := memset((dest), 0, (len))

c_stmt_macro Assert(cond, msg) := ;
c_stmt_macro Trace(x) := ;
c_stmt_macro Tracev(x) := ;
c_stmt_macro Tracevv(x) := ;
c_stmt_macro Tracec(c, x) := ;
c_stmt_macro Tracecv(c, x) := ;

c_proto voidpf ZLIB_INTERNAL zcalloc(voidpf opaque, unsigned items, unsigned size);
c_proto void ZLIB_INTERNAL zcfree(voidpf opaque, voidpf ptr);
c_macro ZALLOC(strm, items, size) := (*((strm)->zalloc))((strm)->opaque, (items), (size))
c_macro ZFREE(strm, addr) := (*((strm)->zfree))((strm)->opaque, (voidpf)(addr))
c_stmt_macro TRY_FREE(s, p) := { if (p) ZFREE(s, p); }

c_macro ZSWAP32(q) := ((((q) >> 24) & 0xff) + (((q) >> 8) & 0xff00) + (((q) & 0xff00) << 8) + (((q) & 0xff) << 24))

-- Public zlib prototypes needed across units
c_proto const char * ZEXPORT zlibVersion(void);
c_proto uLong ZEXPORT adler32(uLong adler, const Bytef *buf, uInt len);
c_proto uLong ZEXPORT adler32_z(uLong adler, const Bytef *buf, z_size_t len);
c_proto uLong ZEXPORT crc32(uLong crc, const Bytef *buf, uInt len);
c_proto uLong ZEXPORT crc32_z(uLong crc, const Bytef *buf, z_size_t len);
c_proto int ZEXPORT deflateInit_(z_streamp strm, int level, const char *version, int stream_size);
c_proto int ZEXPORT deflateInit2_(z_streamp strm, int level, int method, int windowBits, int memLevel, int strategy, const char *version, int stream_size);
c_proto int ZEXPORT deflate(z_streamp strm, int flush);
c_proto int ZEXPORT deflateEnd(z_streamp strm);
c_proto int ZEXPORT deflateReset(z_streamp strm);
c_proto int ZEXPORT deflateResetKeep(z_streamp strm);
c_proto int ZEXPORT deflateParams(z_streamp strm, int level, int strategy);
c_proto z_size_t ZEXPORT deflateBound_z(z_streamp strm, z_size_t sourceLen);
c_proto uLong ZEXPORT deflateBound(z_streamp strm, uLong sourceLen);
c_proto int ZEXPORT inflateInit_(z_streamp strm, const char *version, int stream_size);
c_proto int ZEXPORT inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size);
c_proto int ZEXPORT inflate(z_streamp strm, int flush);
c_proto int ZEXPORT inflateEnd(z_streamp strm);
c_proto int ZEXPORT inflateReset(z_streamp strm);
c_proto int ZEXPORT inflateResetKeep(z_streamp strm);
c_proto int ZEXPORT inflateReset2(z_streamp strm, int windowBits);
c_proto uLong ZEXPORT adler32_combine64(uLong, uLong, z_off64_t);
c_proto uLong ZEXPORT crc32_combine64(uLong, uLong, z_off64_t);
c_proto uLong ZEXPORT crc32_combine_gen64(z_off64_t);
c_proto uLong ZEXPORT crc32_combine_op(uLong crc1, uLong crc2, uLong op);
c_proto z_size_t ZEXPORT compressBound_z(z_size_t sourceLen);
c_proto uLong ZEXPORT compressBound(uLong sourceLen);
c_proto int ZEXPORT deflateCopy(z_streamp dest, z_streamp source);
c_proto int ZEXPORT inflateCopy(z_streamp dest, z_streamp source);

c_macro deflateInit(strm, level) := deflateInit_((strm), (level), ZLIB_VERSION, (int)sizeof(z_stream))
c_macro inflateInit(strm) := inflateInit_((strm), ZLIB_VERSION, (int)sizeof(z_stream))
c_macro deflateInit2(strm, level, method, windowBits, memLevel, strategy) := deflateInit2_((strm), (level), (method), (windowBits), (memLevel), (strategy), ZLIB_VERSION, (int)sizeof(z_stream))
c_macro inflateInit2(strm, windowBits) := inflateInit2_((strm), (windowBits), ZLIB_VERSION, (int)sizeof(z_stream))
c_proto int ZEXPORT inflateBackInit_(z_streamp strm, int windowBits, unsigned char FAR *window, const char *version, int stream_size);
c_macro inflateBackInit(strm, windowBits, window) := inflateBackInit_((strm), (windowBits), (window), ZLIB_VERSION, (int)sizeof(z_stream))

c_pp "#endif"
c_header_end abiCommonH

/-! ## 2. `abi_deflate.h` — Deflate State & Huffman Tree ABI -/

c_header_begin abiDeflateH "abi_deflate.h"

c_pp "#ifndef ABI_DEFLATE_H"
c_pp "#define ABI_DEFLATE_H"
c_include_local "abi_common.h"

c_define LENGTH_CODES := 29
c_define LITERALS := 256
c_define L_CODES := (LITERALS + 1 + LENGTH_CODES)
c_define D_CODES := 30
c_define BL_CODES := 19
c_define HEAP_SIZE := (2 * L_CODES + 1)
c_define MAX_BITS := 15
c_define Buf_size := 16

c_define INIT_STATE := 42
c_define GZIP_STATE := 57
c_define EXTRA_STATE := 69
c_define NAME_STATE := 73
c_define COMMENT_STATE := 91
c_define HCRC_STATE := 103
c_define BUSY_STATE := 113
c_define FINISH_STATE := 666

c_typedef struct ct_data_s {
  union {
    ush freq;
    ush code;
  } fc;
  union {
    ush dad;
    ush len;
  } dl;
} ct_data;

c_define_field Freq := fc, freq
c_define_field Code := fc, code
c_define_field Dad := dl, dad
c_define_field Len := dl, len
c_define_field max_insert_length := max_lazy_match

c_typedef struct static_tree_desc_s static_tree_desc;

c_struct static_tree_desc_s {
  const ct_data *static_tree;
  const intf *extra_bits;
  int extra_base;
  int elems;
  int max_length;
};

c_typedef struct tree_desc_s {
  ct_data *dyn_tree;
  int max_code;
  const static_tree_desc *stat_desc;
} tree_desc;

c_typedef ush Pos;
c_typedef Pos Posf;
c_typedef unsigned IPos;

c_struct internal_state {
  z_streamp strm;
  int status;
  Bytef *pending_buf;
  ulg pending_buf_size;
  Bytef *pending_out;
  ulg pending;
  int wrap;
  gz_headerp gzhead;
  ulg gzindex;
  Byte method;
  int last_flush;
  uInt w_size;
  uInt w_bits;
  uInt w_mask;
  Bytef *window;
  ulg window_size;
  Posf *prev;
  Posf *head;
  uInt ins_h;
  uInt hash_size;
  uInt hash_bits;
  uInt hash_mask;
  uInt hash_shift;
  long block_start;
  uInt match_length;
  IPos prev_match;
  int match_available;
  uInt strstart;
  uInt match_start;
  uInt lookahead;
  uInt prev_length;
  uInt max_chain_length;
  uInt max_lazy_match;
  int level;
  int strategy;
  uInt good_match;
  int nice_match;
  struct ct_data_s dyn_ltree[HEAP_SIZE];
  struct ct_data_s dyn_dtree[2 * D_CODES + 1];
  struct ct_data_s bl_tree[2 * BL_CODES + 1];
  struct tree_desc_s l_desc;
  struct tree_desc_s d_desc;
  struct tree_desc_s bl_desc;
  ush bl_count[MAX_BITS + 1];
  int heap[2 * L_CODES + 1];
  int heap_len;
  int heap_max;
  uch depth[2 * L_CODES + 1];
  uchf *sym_buf;
  uInt lit_bufsize;
  uInt sym_next;
  uInt sym_end;
  ulg opt_len;
  ulg static_len;
  uInt matches;
  uInt insert;
  ush bi_buf;
  int bi_valid;
  int bi_used;
  ulg high_water;
  int slid;
};

c_typedef struct internal_state deflate_state;

c_define MIN_LOOKAHEAD := (MAX_MATCH + MIN_MATCH + 1)
c_macro MAX_DIST(s) := ((s)->w_size - MIN_LOOKAHEAD)
c_define WIN_INIT := MAX_MATCH
c_define LIT_BUFS := 4

c_stmt_macro put_byte(s, c) := { s->pending_buf[s->pending++] = (Bytef)(c); }

c_proto void ZLIB_INTERNAL _tr_init(deflate_state *s);
c_proto int ZLIB_INTERNAL _tr_tally(deflate_state *s, unsigned dist, unsigned lc);
c_proto void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last);
c_proto void ZLIB_INTERNAL _tr_flush_bits(deflate_state *s);
c_proto void ZLIB_INTERNAL _tr_align(deflate_state *s);
c_proto void ZLIB_INTERNAL _tr_stored_block(deflate_state *s, charf *buf, ulg stored_len, int last);

c_pp "extern const uch C99_HIDDEN _length_code[];"
c_pp "extern const uch C99_HIDDEN _dist_code[];"

c_macro d_code(dist) := ((dist) < 256 ? _dist_code[dist] : _dist_code[256 + ((dist) >> 7)])
c_stmt_macro _tr_tally_lit(s, c, flush) := {
  uch cc = (c);
  s->sym_buf[s->sym_next++] = 0;
  s->sym_buf[s->sym_next++] = 0;
  s->sym_buf[s->sym_next++] = cc;
  s->dyn_ltree[cc].Freq++;
  flush = (s->sym_next == s->sym_end);
}
c_stmt_macro _tr_tally_dist(s, distance, length, flush) := {
  uch len = (uch)(length);
  ush dist = (ush)(distance);
  s->sym_buf[s->sym_next++] = (uch)dist;
  s->sym_buf[s->sym_next++] = (uch)(dist >> 8);
  s->sym_buf[s->sym_next++] = len;
  dist.-;
  s->dyn_ltree[_length_code[len] + LITERALS + 1].Freq++;
  s->dyn_dtree[d_code(dist)].Freq++;
  flush = (s->sym_next == s->sym_end);
}

c_pp "#endif"
c_header_end abiDeflateH

/-! ## 3. `abi_inflate.h` — Inflate State, Huffman Code, and Enums -/

c_header_begin abiInflateH "abi_inflate.h"

c_pp "#ifndef ABI_INFLATE_H"
c_pp "#define ABI_INFLATE_H"
c_include_local "abi_common.h"

c_typedef struct {
  unsigned char op;
  unsigned char bits;
  unsigned short val;
} code;

c_define LENBITS := 10
c_define DISTBITS := 8
c_define ENOUGH_LENS := 1332
c_define ENOUGH_DISTS := 400
c_define ENOUGH := (ENOUGH_LENS + ENOUGH_DISTS)

c_typedef enum {
  CODES,
  LENS,
  DISTS
} codetype;

c_typedef enum {
  HEAD = 16180,
  FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
  DICTID, DICT,
  TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
  LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT,
  CHECK, LENGTH, DONE, BAD, MEM, SYNC
} inflate_mode;

c_struct inflate_state {
  z_streamp strm;
  inflate_mode mode;
  int last;
  int wrap;
  int reqwrap;
  int havedict;
  int flags;
  unsigned dmax;
  unsigned long check;
  unsigned long total;
  gz_headerp head;
  unsigned reqbits;
  unsigned wbits;
  unsigned wsize;
  unsigned whave;
  unsigned wnext;
  unsigned char *window;
  unsigned long hold;
  unsigned bits;
  unsigned length;
  unsigned offset;
  unsigned extra;
  code const *lencode;
  code const *distcode;
  unsigned lenbits;
  unsigned distbits;
  unsigned ncode;
  unsigned nlen;
  unsigned ndist;
  unsigned have;
  code *next;
  unsigned short lens[320];
  unsigned short work[288];
  code codes[ENOUGH];
  int sane;
  int back;
  unsigned was;
};

c_proto int ZLIB_INTERNAL inflate_table(codetype type, unsigned short *lens, unsigned codes, code **table, unsigned *bits, unsigned short *work);
c_proto void ZLIB_INTERNAL inflate_fixed(struct inflate_state *state);
c_proto void ZLIB_INTERNAL inflate_fast(z_streamp strm, unsigned start);

c_pp "#endif"
c_header_end abiInflateH

/-! ## 4. `abi_gz.h` — Gzip File State & POSIX I/O Macros -/

c_header_begin abiGzH "abi_gz.h"

c_pp "#ifndef ABI_GZ_H"
c_pp "#define ABI_GZ_H"
c_include_local "abi_common.h"
c_include "stdio.h"
c_pp "#ifndef _POSIX_C_SOURCE"
c_pp "#  define _POSIX_C_SOURCE 200112L"
c_pp "#endif"
c_include "fcntl.h"
c_include "errno.h"
c_pp "#ifndef O_LARGEFILE"
c_pp "#  define O_LARGEFILE 0"
c_pp "#endif"
c_pp "#if defined(_LARGEFILE64_SOURCE) && _LFS64_LARGEFILE-0"
c_pp "#  define LSEEK lseek64"
c_pp "#else"
c_pp "#  define LSEEK lseek"
c_pp "#endif"

-- Portable POSIX constants with LP64/macOS fallback values for Lean Semantics
c_define_const O_RDONLY := 0
c_define_const O_WRONLY := 1
c_define_const O_CREAT := 0x0200
c_define_const O_TRUNC := 0x0400
c_define_const O_APPEND := 0x0008
c_define_const O_EXCL := 0x0800
c_define_const O_NONBLOCK := 0x0004
c_define_const O_CLOEXEC := 0x1000000
c_define_const O_LARGEFILE := 0
c_define_const F_GETFD := 1
c_define_const F_SETFD := 2
c_define_const F_GETFL := 3
c_define_const F_SETFL := 4
c_define_const FD_CLOEXEC := 1
c_define_const SEEK_SET := 0
c_define_const SEEK_CUR := 1
c_define_const SEEK_END := 2
c_define_const EAGAIN := 35
c_define_const EWOULDBLOCK := 35
c_define_const CHAR_BIT := 8
c_define_const INT_MAX := 2147483647

c_macro BLOCKED(e) := ((e) == EAGAIN || (e) == EWOULDBLOCK)

c_define GZBUFSIZE := 8192
c_define GZ_NONE := 0
c_define GZ_READ := 7247
c_define GZ_WRITE := 31153
c_define GZ_APPEND := 1
c_pp "#define LOOK 0"
c_pp "#define COPY 1"
c_pp "#define GZIP 2"

c_struct gzFile_s {
  unsigned have;
  unsigned char *next;
  z_off64_t pos;
};
c_typedef struct gzFile_s *gzFile;

c_typedef struct {
  struct gzFile_s x;
  int mode;
  int fd;
  char *path;
  unsigned size;
  unsigned want;
  unsigned char *in;
  unsigned char *out;
  int direct;
  int junk;
  int how;
  int again;
  z_off64_t start;
  int eof;
  int past;
  int level;
  int strategy;
  int reset;
  z_off64_t skip;
  int err;
  char *msg;
  z_stream strm;
} gz_state;
c_typedef gz_state *gz_statep;

c_proto void ZLIB_INTERNAL gz_error(gz_statep, int, const char *);
c_proto unsigned ZLIB_INTERNAL gz_intmax(void);
c_proto gzFile ZEXPORT gzopen64(const char *, const char *);
c_proto z_off64_t ZEXPORT gzseek64(gzFile, z_off64_t, int);
c_proto z_off64_t ZEXPORT gztell64(gzFile);
c_proto z_off64_t ZEXPORT gzoffset64(gzFile);
c_proto int ZEXPORT gzclose_r(gzFile file);
c_proto int ZEXPORT gzclose_w(gzFile file);
c_proto int ZEXPORT gzread(gzFile file, voidp buf, unsigned len);
c_proto int ZEXPORT gzwrite(gzFile file, voidpc buf, unsigned len);
c_proto void ZEXPORT gzclearerr(gzFile file);
c_proto int ZEXPORTVA gzvprintf(gzFile file, const char *format, va_list va);
c_macro zstrerror() := strerror(errno)
c_macro GT_OFF(x) := (sizeof(int) == sizeof(z_off64_t) && (x) > gz_intmax())
c_define GZ_OFF_MAX := ((((z_off64_t)1 << ((sizeof(z_off64_t)) * CHAR_BIT - 2)) - 1) * 2 + 1)

c_pp "#endif"
c_header_end abiGzH

def allABIHeaders : List TU := [abiCommonH, abiDeflateH, abiInflateH, abiGzH]

end Zlib.Headers
