/* C23: static_assert is a keyword, and its message is optional, at file, block, and member
 * scope. */
#include "fai_test.h"

static_assert(sizeof(int) == 4);
static_assert(sizeof(long) == 8, "LP64");

struct s {
  int a;
  static_assert(sizeof(int) >= 2);
  int b;
};

int main(void) {
  static_assert(1 + 1 == 2);
  for (int i = 0; i < 2; i++) {
    static_assert(sizeof(struct s) == 8);
    show("i", i);
  }
  struct s v = {1, 2};
  show("sum", v.a + v.b);
  return 0;
}
