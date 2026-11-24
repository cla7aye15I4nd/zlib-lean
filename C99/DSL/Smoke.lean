import C99.DSL.Elab

namespace C99.DSL.Smoke

c_header_begin smokeHdr "smoke.h"

c_include "stdarg.h"

c_typedef unsigned int u32_t;
c_typedef unsigned short u16_t;
c_typedef unsigned char byte_t;

c_typedef struct smoke_node_s {
  union {
    u16_t freq;
    u16_t code;
  } fc;
  union {
    u16_t dad;
    u16_t len;
  } dl;
} smoke_node;

c_typedef struct {
  u16_t code;
} code;

c_define_field Freq := fc, freq
c_define_field Code := fc, code
c_define_field Len := dl, len

c_pp "#define SMOKE_FLAG 0x10"
c_define_const SMOKE_FLAG := 0x10
c_macro SMOKE_DOUBLE(x) := ((x) + (x))

c_enum smoke_mode {
  MODE_INIT = 0,
  MODE_COPY,
  MODE_DONE = SMOKE_FLAG + 1
};

c_macro DOUBLE_SUM(a, b) := ((a) + (b))

c_header_end smokeHdr

c_tu_begin smokeTU "smoke.c"

c_typedef u32_t (*pair_fn)(u32_t, u32_t);

c_define STEP_MAX := 8
c_stmt_macro ACC_ONE(p, i) := { total += (p)[i]; step++; }
c_stmt_macro ACC_TWO(p, i) := { ACC_ONE(p, i); ACC_ONE(p, i + 1); }

c_var static const u16_t kTable[2][3] = { {1, 2, 3}, {4, 5, 6} };

c_fn static u32_t helper_add(u32_t a, u32_t b) {
  return a + b;
}

c_fn static unsigned rev_bits(unsigned code, int len) {
  unsigned res = 0;
  do {
    res |= code & 1;
    code >>= 1;
    res <<= 1;
  } while (.-len > 0);
  return res >> 1;
}

c_fn int smoke_entry(const byte_t *in, unsigned c_arg, enum smoke_mode mode, const char *fmt, ...)
  requires («in» = C99.Val.null ∨ ∃ b off, «in» = C99.Val.ptr b off) ∧ fmt = fmt ∧ vaArgs = vaArgs;
  requires c_arg ≥ 0 ∧ mode ≥ 0;
  modifies fun _ => False;
  ensures  ret = ret ∧ view' = view;
{
  const byte_t *from = in;
  const byte_t *end = in + 4;
  unsigned char const *words = (unsigned char const *)from;
  u32_t total = 0;
  int step = 0;
  int have = 3;
  int n = 2;
  int ret = 0;
  smoke_node node;
  va_list ap;
  pair_fn fn = helper_add;

  node.Freq = (u16_t)((c_arg) + 1);
  node.Len = (u16_t)kTable[1][2] + (u16_t)rev_bits(c_arg, 4);
  total = DOUBLE_SUM(node.Freq, fn(1U, (u32_t)SMOKE_FLAG));
  total += (u32_t)sizeof(*from) + (u32_t)sizeof(smoke_node);

  while (have.-) {
    if (words < end) {
      ACC_TWO(words, 0);
      total = (c_arg) - 1;
    }
  }

  do {
    .-n;
    if (n == 1) goto back_step;
    break;
  back_step:
    total++;
  } while (n > 0);

  switch (mode) {
    case MODE_INIT:
    case MODE_COPY:
      ret = (int)total;
      break;
    case MODE_DONE:
      ret = 1;
      goto leave;
    default:
      ret = -1;
      break;
  }

  va_start(ap, fmt);
  va_end(ap);

leave:
  return ret + (int)step;
}

c_tu_end smokeTU

example : List (C99.FnContract Unit) := smokeTUContracts

end C99.DSL.Smoke
