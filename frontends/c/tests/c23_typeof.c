/* C23: typeof and typeof_unqual, on expressions and on type names. */
#include "fai_test.h"

#define SWAP(a, b)                                                                                 \
  do {                                                                                             \
    typeof(a) tmp_ = (a);                                                                          \
    (a) = (b);                                                                                     \
    (b) = tmp_;                                                                                    \
  } while (0)

static int twice(int x) { return 2 * x; }

int main(void) {
  int a = 3, b = 9;
  SWAP(a, b);
  show("a", a);
  show("b", b);
  long l = 1L << 40;
  typeof(l) m = l + 1;
  show("sizeof m", sizeof m);
  show("m>>40", m >> 40);
  typeof(int[4]) arr = {1, 2, 3, 4};
  show("sizeof arr", sizeof arr);
  show("arr[3]", arr[3]);
  const int ci = 7;
  typeof_unqual(ci) mut = ci;
  mut += 1;
  show("unqual", mut);
  show("generic const", _Generic(typeof_unqual(ci) *, int *: 1, const int *: 2, default: 3));
  typeof(twice) *fp = twice;
  show("fp", fp(21));
  typeof(typeof(char) *) pc = "xyz";
  show("pc", pc[1]);
  unsigned short us = 65535;
  typeof(us + 0) promoted = us + 1;
  show("promoted", promoted);
  return 0;
}
