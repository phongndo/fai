/* C23: unreachable() from <stddef.h>. */
#include "fai_test.h"
#include <stddef.h>

static int pick(int k) {
  switch (k & 3) {
  case 0:
    return 10;
  case 1:
    return 20;
  case 2:
    return 30;
  case 3:
    return 40;
  }
  unreachable();
}

static int checked(int v) {
  if (v < 0) unreachable();
  return v * 2;
}

int main(void) {
  int s = 0;
  for (int i = 0; i < 9; i++) s += pick(i);
  show("pick sum", s);
  show("checked", checked(21));
  return 0;
}
