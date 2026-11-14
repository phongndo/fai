/* C23's _BitInt(N) with the builtins that depend on N, not on the storage: checked arithmetic
 * into a _BitInt, the bit counts, and values whose bits above N were changed through a char
 * pointer (a _BitInt's value is its low N bits). */
#include "fai_test.h"

int main(void) {
  unsigned _BitInt(9) a = 511, r;
  show("u9 add over", __builtin_add_overflow(a, 1, &r));
  show("u9 add val", r);
  _BitInt(9) s = 255, t;
  show("s9 add over", __builtin_add_overflow(s, 1, &t));
  show("s9 add val", t);
  show("s9 mul over", __builtin_mul_overflow((_BitInt(9))-16, 16, &t));
  show("s9 mul val", t);
  show("s9 sub over", __builtin_sub_overflow(-200, 100, &t));
  show("s9 sub val", t);
  unsigned _BitInt(9) x = 1, y = 511, z = 0x100;
  show("clzg", __builtin_clzg(x));
  show("ctzg", __builtin_ctzg(z));
  show("popcountg", __builtin_popcountg(y));
  show("leading ones", __builtin_stdc_leading_ones(y));
  show("count zeros", __builtin_stdc_count_zeros(z));
  show("first leading one", __builtin_stdc_first_leading_one(z));
  show("bit width", __builtin_stdc_bit_width(z));
  show("bit ceil", (long)__builtin_stdc_bit_ceil((unsigned _BitInt(9))200));
  _BitInt(9) p = -2;
  ((unsigned char *)&p)[1] &= 1; /* the padding bits change; the value stays -2 */
  p /= 2;
  show("padding div", p);
  _BitInt(9) q = -2;
  ((unsigned char *)&q)[1] &= 1;
  q >>= 1;
  show("padding shift", q);
  return 0;
}
