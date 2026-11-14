/* C23: auto deduces an object's type from its initializer. */
#include "fai_test.h"

struct point {
  int x, y;
};

static long big(void) { return 1L << 35; }

int main(void) {
  auto i = 42;
  auto l = big();
  auto c = 'a';
  auto u = 3000000000u;
  auto p = &i;
  auto s = (struct point){3, 4};
  show("i", i);
  show("sizeof i", sizeof i);
  show("l>>32", l >> 32);
  show("sizeof l", sizeof l);
  show("c", c);
  show("generic u", _Generic(u, unsigned: 1, default: 0));
  show("u", u);
  *p += 1;
  show("via p", i);
  show("s", s.x * 10 + s.y);
  auto sum = 0;
  for (auto k = 0; k < 10; k++) sum += k;
  show("sum", sum);
  return 0;
}
