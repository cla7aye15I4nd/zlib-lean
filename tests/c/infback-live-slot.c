#include <stdio.h>
#include "zlib.h"

/* One final stored block containing 'A', followed by two unused input bytes. */
static unsigned char input_bytes[] = {1, 1, 0, 254, 255, 'A', 19, 47};
static unsigned char other_suffix[] = {19, 47};

struct callbacks {
    z_const unsigned char **slot;
    unsigned calls_in, calls_out;
    int redirect, observed_suffix, correct_output;
};

static unsigned provide(void *opaque, z_const unsigned char **slot) {
    struct callbacks *c = opaque;
    c->slot = slot;
    if (c->calls_in++ != 0)
        return 0;
    *slot = input_bytes;
    return sizeof(input_bytes);
}

static int collect(void *opaque, unsigned char *bytes, unsigned len) {
    struct callbacks *c = opaque;
    c->calls_out++;
    c->correct_output = len == 1 && bytes[0] == 'A';
    if (c->slot != NULL) {
        c->observed_suffix = *c->slot == input_bytes + 6;
        if (c->redirect)
            *c->slot = other_suffix;
    }
    return 0;
}

static int trial(int redirect) {
    z_stream stream = {0};
    struct callbacks c = {0};
    unsigned char window[32768];
    c.redirect = redirect;
    if (inflateBackInit(&stream, 15, window) != Z_OK) return 1;
    int rc = inflateBack(&stream, provide, &c, collect, &c);
    /* The local slot has ended its lifetime. Inspect only public return fields. */
    c.slot = NULL;
    int returned_suffix = stream.next_in == (redirect ? other_suffix : input_bytes + 6);
    unsigned unused = stream.avail_in;
    int end = inflateBackEnd(&stream);
    printf("redirect=%d in=%u out=%u observed=%d output=%d returned=%d unused=%u rc=%d end=%d\n",
           redirect, c.calls_in, c.calls_out, c.observed_suffix, c.correct_output,
           returned_suffix, unused, rc, end);
    return !(c.calls_in == 1 && c.calls_out == 1 && c.observed_suffix && c.correct_output &&
             returned_suffix && unused == 2 && rc == Z_STREAM_END && end == Z_OK);
}

int main(void) {
    int original = trial(0);
    int redirected = trial(1);
    return original || redirected;
}
