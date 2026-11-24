#include "table-fields-generated.c"
#include <assert.h>

static struct inflate_state origin;
static code table[4];
static unsigned expected_bits;
static int expect_fields;
static int calls;

int inflate_table(codetype type, unsigned short *lens, unsigned codes,
                  code **next, unsigned *bits, unsigned short *work) {
    assert(type == CODES && codes == 19);
    assert(lens == origin.lens && work == origin.work);
    assert((next == &origin.next) == expect_fields);
    assert((bits == &origin.lenbits) == expect_fields);
    assert(*next == table && *bits == expected_bits);
    *next = table + 1;
    *bits = 11;
    calls++;
    return 42;
}

static void reset(int direct, unsigned width) {
    origin = (struct inflate_state){.next = table, .lenbits = 7, .distbits = 5};
    expect_fields = direct;
    expected_bits = width;
}

int main(void) {
    struct inflate_state other = {0};
    unsigned char byte = 2;
    assert(helper_locals(&byte, 43) == 46);
    reset(1, 7);
    assert(forward(&origin) == 42 && origin.next == table + 1 && origin.lenbits == 11 && origin.distbits == 5);
    reset(0, 7);
    assert(other_state(&origin, &other) == 42 && other.next == table + 1 && other.lenbits == 11);
    assert(origin.next == table && origin.lenbits == 7);
    reset(0, 7);
    assert(other_bits(&origin) == 42 && origin.lenbits == 7 && origin.distbits == 11);
    reset(0, 8);
    assert(changed_bits(&origin) == 42 && origin.next == table + 1 && origin.lenbits == 11);
    reset(0, 7);
    assert(discard(&origin) == 42 && origin.next == table && origin.lenbits == 7);
    reset(0, 7);
    assert(intervening_write(&origin) == 42 && origin.next == table + 1 && origin.lenbits == 11);
    reset(1, 7);
    assert(delayed_result(&origin) == 11 && origin.lenbits == 23);
    reset(0, 7);
    assert(delayed_commit(&origin) == 42 && origin.lenbits == 11 && origin.distbits == 23);
    reset(0, 7);
    assert(extra_update(&origin) == 42 && origin.lenbits == 11 && origin.distbits == 23);
    reset(0, 7);
    assert(aliased_update(&origin, &origin) == 7 && origin.lenbits == 23);
    reset(0, 7);
    assert(aliased_update(&origin, &other) == 7 && origin.lenbits == 7 && other.lenbits == 23);
    reset(0, 7);
    swap_widths(&origin);
    assert(origin.lenbits == 5 && origin.distbits == 7);
    reset(0, 7);
    chained_widths(&origin);
    assert(origin.lenbits == 10 && origin.distbits == 15);
    assert(optional_count(0) == 77 && optional_count(1) == 0 && optional_count(3) == 2);
    assert(nested_range(0) == 0 && nested_range(2) == 6 && nested_range(5) == 15);
    assert(calls == 9);
    return 0;
}
