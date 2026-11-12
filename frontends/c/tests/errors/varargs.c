/* What fai-cc's varargs don't cover yet: structs and unions as variadic arguments and read by
 * va_arg (track A), and long double (binary128) arguments. */
#include <stdarg.h>

struct pair {
  int a, b;
};

void sink(int n, ...);

void pass_struct(struct pair *p) { sink(1, *p); }

void pass_long_double(long double *x) { sink(1, *x); }

int read_struct(int n, ...) {
  va_list ap;
  va_start(ap, n);
  struct pair p = va_arg(ap, struct pair);
  va_end(ap);
  return p.a;
}

int main(void) { return 0; }

// expect: 11:44: structs and unions as variadic arguments (track A)
// expect: 13:49: 'long double' (binary128 on AArch64)
// expect: 18:19: 'va_arg' of structs and unions (track A)
