/* C side of the differential test for infback.c (inflateBackInit_, inflateBack, inflateBackEnd): links the REAL zlib
 * (patched copy). One case per line:
 *   infback WB INCH OPTS hex:INPUT
 * WB    windowBits for inflateBackInit (the window is a malloc'ed buffer of 2^WB bytes)
 * INCH  size of the pieces the `in` call-back hands out (it returns pieces of the input, then 0)
 * OPTS  bit 1: the `out` call-back fails (returns 1) on its second call
 *       bit 2: the `out` call-back fails on its first call
 *       bit 4: strm.next_in / avail_in are preset with the first 5 bytes of the input
 *       bit 8: retain &next and redirect it from an output callback into a second input buffer
 *       bit 16 (with bit 8): redirect the outer cursor from a nested decoder's output callback
 * The output line holds the result, the unused input, the call-back counters, the lengths of the first 16 `out` calls,
 * the message and everything `out` received. */
#define _LARGEFILE64_SOURCE 1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "zlib.h"

static long long parse_i(const char *s) {
    char *e; errno = 0;
    long long v = strtoll(s, &e, 10);
    if (*s == '\0' || *e != '\0' || errno) { fprintf(stderr, "bad number %s\n", s); exit(2); }
    return v;
}
static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}
static unsigned char *parse_hex(const char *s, size_t *len) {
    if (strncmp(s, "hex:", 4) != 0) { fprintf(stderr, "bad buffer\n"); exit(2); }
    s += 4;
    size_t n = strlen(s);
    if (n % 2) { fprintf(stderr, "odd hex\n"); exit(2); }
    *len = n / 2;
    unsigned char *b = malloc(*len + 1);
    for (size_t i = 0; i < *len; i++) {
        int h = hexval(s[2 * i]), l = hexval(s[2 * i + 1]);
        if (h < 0 || l < 0) { fprintf(stderr, "bad hex digit\n"); exit(2); }
        b[i] = (unsigned char)(h * 16 + l);
    }
    return b;
}

typedef struct {
    unsigned char *input; size_t len, pos, inch;
    unsigned nin, nout, opts;
    unsigned char *obuf; size_t olen;
    unsigned olens[16];
    z_const unsigned char **slot;
    unsigned char *alternate;
} ctl_t;

typedef struct {
    z_const unsigned char **outer, **inner;
    unsigned char *input, *replacement;
} nested_t;

static unsigned nested_in(void *desc, z_const unsigned char **slot) {
    nested_t *c = desc;
    if (c->inner || slot == c->outer) abort();
    c->inner = slot;
    *slot = c->input;
    return 8;
}

static int nested_out(void *desc, unsigned char *buf, unsigned len) {
    nested_t *c = desc;
    if (len != 1 || buf[0] != 'N' || *c->inner != c->input + 6) abort();
    *c->outer = c->replacement;
    *c->inner = c->input + 1;
    return 0;
}

static void nested_redirect(z_const unsigned char **outer, unsigned char *replacement) {
    unsigned char data[] = {1, 1, 0, 254, 255, 'N', 19, 47};
    unsigned char window[256];
    nested_t c = {outer, NULL, data, replacement};
    z_stream z = {0};
    if (inflateBackInit(&z, 8, window) != Z_OK ||
        inflateBack(&z, nested_in, &c, nested_out, &c) != Z_STREAM_END ||
        z.next_in != data + 1 || z.avail_in != 2 || *outer != replacement ||
        inflateBackEnd(&z) != Z_OK) abort();
}

/* Equality is defined even when the cursor points into the other input object. */
static size_t input_offset(ctl_t *c, z_const unsigned char *p) {
    for (size_t i = 0; i <= c->len; i++)
        if (p == c->input + i || p == c->alternate + i) return i;
    abort();
}

static unsigned in_cb(void *d, z_const unsigned char **buf) {
    ctl_t *c = d;
    if (c->opts & 8) {
        if (c->nin && c->slot != buf) abort();
        c->slot = buf;
    }
    c->nin++;
    size_t n = c->len - c->pos < c->inch ? c->len - c->pos : c->inch;
    *buf = c->input + c->pos;
    c->pos += n;
    return (unsigned)n;
}
static int out_cb(void *d, unsigned char *buf, unsigned len) {
    ctl_t *c = d;
    if (c->nout < 16) c->olens[c->nout] = len;
    c->nout++;
    memcpy(c->obuf + c->olen, buf, len);
    c->olen += len;
    if ((c->opts & 8) && c->slot && *c->slot) {
        unsigned char *replacement = c->alternate + input_offset(c, *c->slot);
        if (c->opts & 16) nested_redirect(c->slot, replacement);
        else *c->slot = replacement;
    }
    if ((c->opts & 2) && c->nout == 1) return 1;
    if ((c->opts & 1) && c->nout == 2) return 1;
    return 0;
}

static void hexout(const unsigned char *b, size_t n) {
    for (size_t i = 0; i < n; i++) printf("%02x", b[i]);
}

static void run_case(char **tok) {
    int wb = (int)parse_i(tok[1]);
    size_t inch = (size_t)parse_i(tok[2]);
    unsigned opts = (unsigned)parse_i(tok[3]);
    size_t len;
    unsigned char *input = parse_hex(tok[4], &len);
    ctl_t c; memset(&c, 0, sizeof c);
    c.input = input; c.len = len; c.inch = inch ? inch : 1; c.opts = opts;
    if (opts & 8) {
        c.alternate = malloc(len + 1);
        if (c.alternate == NULL) abort();
        memcpy(c.alternate, input, len);
        /* First payload byte after a full 256-byte window in a stored block. */
        if (len > 261) c.alternate[261] ^= 64;
    }
    c.obuf = malloc(1 << 20);
    z_stream strm; memset(&strm, 0, sizeof strm);
    unsigned char *window = malloc(wb >= 0 && wb < 16 ? (size_t)1 << wb : 1);
    int init = inflateBackInit(&strm, wb, window);
    printf("init=%d", init);
    if (init == Z_OK) {
        if (opts & 4) {
            size_t k = len < 5 ? len : 5;
            strm.next_in = input; strm.avail_in = (uInt)k; c.pos = k;
        }
        int ret = inflateBack(&strm, in_cb, &c, out_cb, &c);
        c.slot = NULL;
        printf(" rc=%d ain=%u nin=", ret, strm.avail_in);
        if (strm.next_in == NULL) printf("null");
        else if (opts & 8) {
            size_t off = input_offset(&c, strm.next_in);
            printf("%s%zu", strm.next_in == c.alternate + off ? "alternate+" : "input+", off);
        } else printf("%ld", (long)(strm.next_in - input));
        printf(" calls=%u,%u olens=", c.nin, c.nout);
        for (unsigned i = 0; i < 16 && i < c.nout; i++) printf("%s%u", i ? "," : "", c.olens[i]);
        printf(" msg=");
        if (strm.msg == NULL) printf("-"); else for (const char *p = strm.msg; *p; p++) printf("%02x", (unsigned char)*p);
        printf(" end=%d", inflateBackEnd(&strm));
        printf(" out="); hexout(c.obuf, c.olen);
    }
    printf("\n");
    free(window); free(c.obuf); free(c.alternate); free(input);
}

int main(void) {
    char *line = NULL; size_t cap = 0; ssize_t got;
    int bad = 0;
    while ((got = getline(&line, &cap, stdin)) >= 0) {
        char *save, *tok[16]; int nt = 0;
        for (char *t = strtok_r(line, " \t\r\n", &save); t && nt < 16; t = strtok_r(NULL, " \t\r\n", &save))
            tok[nt++] = t;
        if (nt == 0) continue;
        if (strcmp(tok[0], "infback") == 0 && nt == 5) {
            run_case(tok);
        } else {
            fprintf(stderr, "unknown function or wrong arity: %s\n", tok[0]);
            printf("BADINPUT\n");
            bad = 1;
        }
    }
    free(line);
    return bad;
}
