/* C23: a variadic function needs no named parameter, and va_start takes only the list. */
#include "fai_test.h"
#include <stdarg.h>

static long sum_until_zero(...) {
  va_list ap;
  va_start(ap);
  long s = 0;
  for (;;) {
    int v = va_arg(ap, int);
    if (v == 0) break;
    s += v;
  }
  va_end(ap);
  return s;
}

static long weighted(int n, ...) {
  va_list ap;
  va_start(ap);
  long s = 0;
  for (int i = 1; i <= n; i++) s += i * va_arg(ap, long);
  va_end(ap);
  return s;
}

int main(void) {
  show("sum", sum_until_zero(1, 2, 3, 4, 0));
  show("empty", sum_until_zero(0));
  show("many", sum_until_zero(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0));
  show("weighted", weighted(3, 10L, 20L, 30L));
  long (*fp)(...) = sum_until_zero;
  show("via ptr", fp(5, 5, 0));
  return 0;
}
