/* Signed integer arithmetic: + - * / % (C's truncating division), shifts, and the usual
 * arithmetic conversions on int, long, and long long. */
#include "fai_test.h"

static int add(int a, int b) { return a + b; }
static long mul(long a, long b) { return a * b; }

int main(void) {
  int xs[] = {0, 1, -1, 7, -7, 13, -13, 1000003, -1000003, 2147483647, -2147483647 - 1};
  int ds[] = {1, -1, 2, -2, 3, -3, 7, -7, 1000};
  long acc = 0;
  for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
    for (unsigned j = 0; j < sizeof ds / sizeof ds[0]; j++) {
      int x = xs[i], d = ds[j];
      if (x == -2147483647 - 1 && d == -1) continue; /* overflows: UB */
      int q = x / d, r = x % d;
      if (q * d + r != x) show("bad division", x);
      acc = acc * 31 + q + 3 * r;
      acc %= 1000000007;
    }
  }
  show("div/rem checksum", acc);
  show("-7 / 2", -7 / 2);
  show("-7 % 2", -7 % 2);
  show("7 / -2", 7 / -2);
  show("7 % -2", 7 % -2);
  show("add", add(-40, 2));
  show("mul", mul(-123456789L, 1000L));
  show("shl", 1 << 30);
  show("shl long", 1L << 62);
  show("shr negative", -256 >> 4);
  show("shr", 1000 >> 3);
  show("neg", -(-5));
  show("not", ~0);
  show("and", 0x5a5a & 0x0ff0);
  show("or", 0x5000 | 0x00a5);
  show("xor", 0xffff ^ 0x0f0f);
  long long big = 9000000000000000000LL;
  show("big / 3", (long)(big / 3));
  show("big % 1000", (long)(big % 1000));
  int m = -17;
  show("mixed", m * 3L + 2);
  short s = -300;
  show("short promoted", s * s);
  return 0;
}
