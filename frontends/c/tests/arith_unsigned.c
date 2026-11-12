/* Unsigned arithmetic wraps; unsigned division, remainder, and shifts; signed/unsigned mixing
 * as C converts it. */
#include "fai_test.h"

int main(void) {
  unsigned a = 4000000000u;
  unsigned b = a + a; /* wraps */
  show("wrap add", b);
  show("wrap sub", 3u - 5u);
  show("wrap mul", 65537u * 65537u);
  unsigned long big = 18446744073709551615ul;
  show("ulong max + 1", (long)(big + 1));
  show("ulong / 10 % 1000", (long)(big / 10 % 1000));
  show("udiv", 4000000000u / 7u);
  show("urem", 4000000000u % 7u);
  show("ushr", 0x80000000u >> 31);
  show("ushl", 0xffffffffu << 4);
  show("compare -1 < 1u", -1 < 1u);
  show("compare -1L < 1u", -1L < 1u);
  unsigned char c = 250;
  c += 10;
  show("uchar wrap", c);
  unsigned short h = 65535;
  h++;
  show("ushort wrap", h);
  unsigned x = 0x12345678;
  unsigned rot = (x << 8) | (x >> 24);
  show("rotate", rot);
  unsigned long long h64 = 1469598103934665603ull;
  for (int i = 0; i < 10; i++) {
    h64 ^= (unsigned long long)i;
    h64 *= 1099511628211ull;
  }
  show("fnv low", (long)(h64 & 0xffffffff));
  show("fnv high", (long)(h64 >> 32));
  unsigned n = 0;
  n--;
  show("unsigned -1", n);
  show("negate unsigned", -(unsigned)5);
  return 0;
}
