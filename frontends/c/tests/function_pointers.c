/* Function pointers: tables, callbacks, pointers as parameters and results, comparisons, and
 * calls written with and without `*`. */
#include "fai_test.h"

typedef long (*op)(long, long);

static long add(long a, long b) { return a + b; }
static long sub(long a, long b) { return a - b; }
static long mul(long a, long b) { return a * b; }
static long fold(const long *xs, int n, long init, op f) {
  for (int i = 0; i < n; i++) init = f(init, xs[i]);
  return init;
}
static op pick(char c) {
  switch (c) {
  case '+': return add;
  case '-': return &sub;
  default: return mul;
  }
}
static void each(int n, void (*visit)(int)) {
  for (int i = 0; i < n; i++) (*visit)(i);
}
static long total;
static void accumulate(int i) { total += i * i; }

struct handler { const char *name; long (*fn)(long, long); };
static const struct handler handlers[] = {{"add", add}, {"sub", sub}, {"mul", mul}};

int main(void) {
  long xs[] = {3, 1, 4, 1, 5};
  show("sum", fold(xs, 5, 0, add));
  show("product", fold(xs, 5, 1, pick('*')));
  show("difference", fold(xs, 5, 100, pick('-')));
  each(5, accumulate);
  show("callbacks", total);
  for (int i = 0; i < 3; i++) {
    print_str(handlers[i].name);
    fai_put_char(' ');
    print_long(handlers[i].fn(7, 3));
  }
  op f = add;
  show("same function", f == add);
  show("different function", f == sub);
  show("explicit deref", (*f)(20, 22));
  long (*arr[2])(long, long) = {mul, add};
  show("array of pointers", arr[0](6, 7) + arr[1](1, 1));
  return 0;
}
