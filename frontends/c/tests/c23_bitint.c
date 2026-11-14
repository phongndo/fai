/* C23: bit-precise integers, _BitInt(N), up to 64 bits, and the wb and uwb suffixes. */
#include "fai_test.h"

static unsigned _BitInt(7) add7(unsigned _BitInt(7) a, unsigned _BitInt(7) b) { return a + b; }

int main(void) {
  unsigned _BitInt(3) u3 = 7;
  u3 = u3 + 1; /* wraps at 3 bits */
  show("u3 wrap", u3);
  _BitInt(12) s12 = -2000;
  show("s12", s12);
  show("s12 / 3", s12 / 3);
  unsigned _BitInt(7) a = 100uwb, b = 50uwb;
  show("add7", add7(a, b));
  show("sizeof 7", sizeof(unsigned _BitInt(7)));
  show("sizeof 33", sizeof(_BitInt(33)));
  _BitInt(33) big = (_BitInt(33))1 << 32;
  show("big", big);
  unsigned _BitInt(64) all = -1;
  show("all>>60", (long)(all >> 60));
  show("generic", _Generic(3wb, _BitInt(3): 1, int: 2, default: 3));
  _BitInt(20) arr[4] = {1, -1, 300000, -300000};
  long s = 0;
  for (int i = 0; i < 4; i++) s += arr[i] * (i + 1);
  show("arr", s);
  unsigned _BitInt(9) m = 511;
  m *= 3;
  show("mul wrap", m);
  return 0;
}
