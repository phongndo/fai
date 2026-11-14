/* C23's <stdbit.h>: bit counts and powers of two, type-generic and per type. */
#include "fai_test.h"
#include <stdbit.h>

static unsigned vals[] = {0u, 1u, 2u, 3u, 0x80000000u, 0xFFFFFFFFu, 0x00F0u, 1000u};

int main(void) {
  for (unsigned i = 0; i < sizeof vals / sizeof vals[0]; i++) {
    unsigned v = vals[i];
    print_str("v ");
    print_long(v);
    show(" leading_zeros", stdc_leading_zeros(v));
    show(" leading_ones", stdc_leading_ones(v));
    show(" trailing_zeros", stdc_trailing_zeros(v));
    show(" trailing_ones", stdc_trailing_ones(v));
    show(" first_one", stdc_first_leading_one(v));
    show(" first_trailing_one", stdc_first_trailing_one(v));
    show(" count_ones", stdc_count_ones(v));
    show(" count_zeros", stdc_count_zeros(v));
    show(" single bit", stdc_has_single_bit(v));
    show(" bit width", stdc_bit_width(v));
    show(" bit floor", stdc_bit_floor(v));
    if (v <= 0x80000000u) show(" bit ceil", stdc_bit_ceil(v));
  }
  unsigned char c = 0x10;
  show("uc lz", stdc_leading_zeros_uc(c));
  unsigned long long ull = 1ull << 50;
  show("ull tz", stdc_trailing_zeros_ull(ull));
  show("ull width", stdc_bit_width(ull));
  unsigned short us = 0x00FF;
  show("us ones", stdc_count_ones_us(us));
  show("endian", __STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__);
  return 0;
}
