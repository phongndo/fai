/* C23: _BitInt wider than 64 bits (to BITINT_MAXWIDTH), here 128 and 100 bits. */
#include "fai_test.h"

int main(void) {
  unsigned _BitInt(128) x = 1;
  x <<= 100;
  x += 12345;
  show("hi", (long)(x >> 96));
  show("lo", (long)(x & 0xFFFFFFFF));
  _BitInt(100) y = -1;
  y *= 1000000007wb;
  show("y", (long)y);
  unsigned _BitInt(128) f = 1;
  for (int i = 1; i <= 30; i++) f *= i;
  show("30! >> 64", (long)(f >> 64));
  show("30! low", (long)(f & 0xFFFFFFFFFFFFull));
  return 0;
}
