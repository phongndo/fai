/* _Bool, the logical operators, and comparisons as values. */
#include "fai_test.h"
#include <stdbool.h>

static bool is_even(int x) { return x % 2 == 0; }

int main(void) {
  bool t = true, f = false;
  show("true", t);
  show("false", f);
  show("not", !t);
  show("and", t && f);
  show("or", t || f);
  bool b = 42;
  show("42 as bool", b);
  b = b + 1;
  show("bool + 1", b);
  int evens = 0;
  for (int i = 0; i < 17; i++) evens += is_even(i);
  show("evens", evens);
  show("cmp sum", (3 < 4) + (4 < 3) + (5 == 5) + (5 != 5) + (2 <= 2) + (3 >= 4));
  bool flags[4] = {1, 0, 1, 1};
  int mask = 0;
  for (int i = 0; i < 4; i++) mask |= flags[i] << i;
  show("mask", mask);
  struct { bool on; int v; } s = {1, 7};
  show("struct bool", s.on && s.v);
  return 0;
}
