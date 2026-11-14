/* C23: labels before declarations and at the end of compound statements. */
#include "fai_test.h"

static int g(int n) {
  int r = 0;
  for (int i = 0; i < n; i++) {
    if (i == 3) goto next;
    r += i;
  next:
  }
  return r;
}

static int h(int v) {
  switch (v) {
  case 1:
    int x = 10;
    return x;
  default:
  }
  return -1;
}

static int total;

static int f2(int n) {
  total = 0;
  if (n < 0) goto out;
again:
  int k = n * 2;
  total += k;
  n--;
  if (n > 0) goto again;
out:
  return total;
}

int main(void) {
  show("f2 4", f2(4));
  show("f2 -1", f2(-1));
  show("g 6", g(6));
  show("h 1", h(1));
  show("h 2", h(2));
  return 0;
}
