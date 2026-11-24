import C99.DSL
import Zlib.Headers.Common

/-!
# `inffast.c` — Fast Inflate Decoding Loop (`Z_INFLATE_FETCH = 64`)
-/

namespace Zlib.Inffast

open C99

c_tu_begin inffastTU "inffast.c"

c_include_local "abi_inflate.h"

c_stmt_macro TRACE_LITERAL(here) := ;

c_fn local Z_U8 load64(z_const unsigned char FAR *p) {
  Z_U8 v = 1;
  if (*(unsigned char *)&v) {
    zmemcpy(&v, p, 8);
    return v;
  }
  return (Z_U8)p[0] | ((Z_U8)p[1] << 8) | ((Z_U8)p[2] << 16) |
         ((Z_U8)p[3] << 24) | ((Z_U8)p[4] << 32) | ((Z_U8)p[5] << 40) |
         ((Z_U8)p[6] << 48) | ((Z_U8)p[7] << 56);
}

c_fn local unsigned char FAR *copy_back(unsigned char FAR *out, unsigned dist, unsigned len) {
  unsigned char FAR *from = out - dist;
  unsigned char FAR *stop = out + len;

  if (dist >= 16) {
    do {
      zmemcpy(out, from, 16);
      out += 16;
      from += 16;
    } while (out < stop);
    return stop;
  }
  if (dist >= 8) {
    do {
      zmemcpy(out, from, 8);
      out += 8;
      from += 8;
    } while (out < stop);
    return stop;
  }
  if (dist == 1) {
    Z_U8 run = *from;
    run |= run << 8;
    run |= run << 16;
    run |= run << 32;
    do {
      zmemcpy(out, &run, 8);
      out += 8;
    } while (out < stop);
    return stop;
  }
  do {
    Z_U8 v;
    zmemcpy(&v, from, 8);
    zmemcpy(out, &v, 8);
    out += dist;
    from += dist;
  } while (out < stop);
  return stop;
}

c_fn void ZLIB_INTERNAL inflate_fast(z_streamp strm, unsigned start) {
  struct inflate_state FAR *state;
  z_const unsigned char FAR *in;
  z_const unsigned char FAR *last;
  unsigned char FAR *out;
  unsigned char FAR *beg;
  unsigned char FAR *end;
  unsigned wsize;
  unsigned whave;
  unsigned wnext;
  unsigned char FAR *window;
  int back;
  unsigned long hold;
  unsigned bits;
  code const FAR *lcode;
  code const FAR *dcode;
  unsigned lmask;
  unsigned dmask;
  code const *here;
  unsigned op;
  unsigned len;
  unsigned dist;
  unsigned char FAR *from;
  Z_U8 hold8;
  z_const unsigned char FAR *last8;
  unsigned char FAR *end8;

  state = (struct inflate_state FAR *)strm->state;
  in = strm->next_in;
  last = in + (strm->avail_in - 5);
  out = strm->next_out;
  beg = out - (start - strm->avail_out);
  end = out + (strm->avail_out - 257);
  wsize = state->wsize;
  whave = state->whave;
  wnext = state->wnext;
  window = state->window;
  back = window != Z_NULL && out + strm->avail_out == window + wsize;
  hold = state->hold;
  bits = state->bits;
  lcode = state->lencode;
  dcode = state->distcode;
  lmask = (1U << state->lenbits) - 1;
  dmask = (1U << state->distbits) - 1;

  if (!back && strm->avail_in >= 16 && strm->avail_out >= 2 + 258 + 15) {
    last8 = in + (strm->avail_in - 16);
    end8 = out + (strm->avail_out - (2 + 258 + 15));
    hold8 = hold;
    do {
      hold8 |= load64(in) << bits;
      in += (63 - bits) >> 3;
      bits |= 56;
      here = lcode + (hold8 & lmask);
      if (here->op == 0) {
        hold8 >>= here->bits;
        bits -= here->bits;
        TRACE_LITERAL(here);
        *out++ = (unsigned char)(here->val);
        here = lcode + (hold8 & lmask);
        if (here->op == 0) {
          hold8 >>= here->bits;
          bits -= here->bits;
          TRACE_LITERAL(here);
          *out++ = (unsigned char)(here->val);
          here = lcode + (hold8 & lmask);
          if (here->op == 0) {
            hold8 >>= here->bits;
            bits -= here->bits;
            TRACE_LITERAL(here);
            *out++ = (unsigned char)(here->val);
            continue;
          }
        }
        hold8 |= load64(in) << bits;
        in += (63 - bits) >> 3;
        bits |= 56;
      }
    dolen8:
      op = (unsigned)(here->bits);
      hold8 >>= op;
      bits -= op;
      op = (unsigned)(here->op);
      if (op == 0) {
        TRACE_LITERAL(here);
        *out++ = (unsigned char)(here->val);
      }
      else if (op & 16) {
        len = (unsigned)(here->val);
        op &= 15;
        len += (unsigned)hold8 & ((1U << op) - 1);
        hold8 >>= op;
        bits -= op;
        here = dcode + (hold8 & dmask);
      dodist8:
        op = (unsigned)(here->bits);
        hold8 >>= op;
        bits -= op;
        op = (unsigned)(here->op);
        if (op & 16) {
          dist = (unsigned)(here->val);
          op &= 15;
          dist += (unsigned)hold8 & ((1U << op) - 1);
          hold8 >>= op;
          bits -= op;
          op = (unsigned)(out - beg);
          if (dist > op) {
            op = dist - op;
            if (op > whave) {
              if (state->sane) {
                strm->msg = (z_const char *)"invalid distance too far back";
                state->mode = BAD;
                break;
              }
            }
            from = window;
            if (wnext == 0)
              from += wsize - op;
            else if (wnext < op) {
              from += wsize + wnext - op;
              op -= wnext;
              if (op < len) {
                zmemcpy(out, from, op);
                out += op;
                len -= op;
                from = window;
                op = wnext;
              }
            }
            else
              from += wnext - op;
            if (op > len)
              op = len;
            zmemcpy(out, from, op);
            out += op;
            len -= op;
            if (len)
              out = copy_back(out, dist, len);
          }
          else
            out = copy_back(out, dist, len);
        }
        else if ((op & 64) == 0) {
          here = dcode + here->val + (hold8 & ((1U << op) - 1));
          goto dodist8;
        }
        else {
          strm->msg = (z_const char *)"invalid distance code";
          state->mode = BAD;
          break;
        }
      }
      else if ((op & 64) == 0) {
        here = lcode + here->val + (hold8 & ((1U << op) - 1));
        goto dolen8;
      }
      else if (op & 32) {
        state->mode = TYPE;
        break;
      }
      else {
        strm->msg = (z_const char *)"invalid literal/length code";
        state->mode = BAD;
        break;
      }
    } while (in <= last8 && out <= end8);

    len = bits >> 3;
    in -= len;
    bits -= len << 3;
    hold = (unsigned long)(hold8 & ((1U << bits) - 1));
    if (state->mode != LEN || out >= end)
      goto leave;
  }

  do {
    if (bits < 15) {
      hold += (unsigned long)(*in++) << bits;
      bits += 8;
      hold += (unsigned long)(*in++) << bits;
      bits += 8;
    }
    here = lcode + (hold & lmask);
  dolen:
    op = (unsigned)(here->bits);
    hold >>= op;
    bits -= op;
    op = (unsigned)(here->op);
    if (op == 0) {
      *out++ = (unsigned char)(here->val);
    }
    else if (op & 16) {
      len = (unsigned)(here->val);
      op &= 15;
      if (op) {
        if (bits < op) {
          hold += (unsigned long)(*in++) << bits;
          bits += 8;
        }
        len += (unsigned)hold & ((1U << op) - 1);
        hold >>= op;
        bits -= op;
      }
      if (bits < 15) {
        hold += (unsigned long)(*in++) << bits;
        bits += 8;
        hold += (unsigned long)(*in++) << bits;
        bits += 8;
      }
      here = dcode + (hold & dmask);
    dodist:
      op = (unsigned)(here->bits);
      hold >>= op;
      bits -= op;
      op = (unsigned)(here->op);
      if (op & 16) {
        dist = (unsigned)(here->val);
        op &= 15;
        if (bits < op) {
          hold += (unsigned long)(*in++) << bits;
          bits += 8;
          if (bits < op) {
            hold += (unsigned long)(*in++) << bits;
            bits += 8;
          }
        }
        dist += (unsigned)hold & ((1U << op) - 1);
        hold >>= op;
        bits -= op;
        op = (unsigned)(out - beg);
        if (dist > op) {
          op = dist - op;
          if (op > whave) {
            if (state->sane) {
              strm->msg = (z_const char *)"invalid distance too far back";
              state->mode = BAD;
              break;
            }
          }
          from = window;
          if (wnext == 0) {
            from += wsize - op;
            if (op < len) {
              len -= op;
              do {
                *out++ = *from++;
              } while (.-op);
              from = out - dist;
            }
          }
          else if (wnext < op) {
            from += wsize + wnext - op;
            op -= wnext;
            if (op < len) {
              len -= op;
              do {
                *out++ = *from++;
              } while (.-op);
              from = window;
              if (wnext < len) {
                op = wnext;
                len -= op;
                do {
                  *out++ = *from++;
                } while (.-op);
                from = out - dist;
              }
            }
          }
          else {
            from += wnext - op;
            if (op < len) {
              len -= op;
              do {
                *out++ = *from++;
              } while (.-op);
              from = out - dist;
            }
          }
          while (len > 2) {
            *out++ = *from++;
            *out++ = *from++;
            *out++ = *from++;
            len -= 3;
          }
          if (len) {
            *out++ = *from++;
            if (len > 1)
              *out++ = *from++;
          }
        }
        else {
          from = out - dist;
          do {
            *out++ = *from++;
            *out++ = *from++;
            *out++ = *from++;
            len -= 3;
          } while (len > 2);
          if (len) {
            *out++ = *from++;
            if (len > 1)
              *out++ = *from++;
          }
        }
      }
      else if ((op & 64) == 0) {
        here = dcode + here->val + (hold & ((1U << op) - 1));
        goto dodist;
      }
      else {
        strm->msg = (z_const char *)"invalid distance code";
        state->mode = BAD;
        break;
      }
    }
    else if ((op & 64) == 0) {
      here = lcode + here->val + (hold & ((1U << op) - 1));
      goto dolen;
    }
    else if (op & 32) {
      state->mode = TYPE;
      break;
    }
    else {
      strm->msg = (z_const char *)"invalid literal/length code";
      state->mode = BAD;
      break;
    }
  } while (in < last && out < end);

leave:
  len = bits >> 3;
  in -= len;
  bits -= len << 3;
  hold &= (1U << bits) - 1;

  strm->next_in = in;
  strm->next_out = out;
  strm->avail_in = (unsigned)(in < last ? 5 + (last - in) : 5 - (in - last));
  strm->avail_out = (unsigned)(out < end ? 257 + (end - out) : 257 - (out - end));
  state->hold = hold;
  state->bits = bits;
  return;
}

c_tu_end inffastTU

end Zlib.Inffast
