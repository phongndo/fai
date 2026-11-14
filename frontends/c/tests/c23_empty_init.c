/* C23: the empty initializer {} for scalars, arrays, structs, and unions. */
#include "fai_test.h"

struct s {
  int a;
  long b;
  char c[5];
  struct {
    short x, y;
  } inner;
};

union u {
  long l;
  int i;
};

static int sum_bytes(const void *p, unsigned long n) {
  const unsigned char *b = p;
  int s = 0;
  for (unsigned long i = 0; i < n; i++) s += b[i];
  return s;
}

int main(void) {
  int i = {};
  show("int", i);
  long arr[6] = {};
  show("arr", sum_bytes(arr, sizeof arr));
  struct s v = {};
  show("struct", v.a + v.b + v.c[4] + v.inner.y);
  union u w = {};
  show("union", w.l);
  int *p = {};
  show("ptr null", p == 0);
  double d = {};
  show("double zero", d == 0.0);
  for (int k = 0; k < 3; k++) {
    int fresh[4] = {};
    fresh[k] = k + 1;
    show("fresh", fresh[0] + fresh[1] * 10 + fresh[2] * 100 + fresh[3] * 1000);
  }
  struct s lit = (struct s){};
  show("compound", lit.inner.x);
  return 0;
}
