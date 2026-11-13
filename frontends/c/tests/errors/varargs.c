/* What fcc's varargs don't cover yet: long double (binary128) arguments, and returning a
 * va_list. */
#include <stdarg.h>

void sink(int n, ...);

void pass_long_double(long double *x) { sink(1, *x); }

va_list give(va_list ap) { return ap; }

int main(void) { return 0; }

// expect: 7:49: 'long double' (binary128 on AArch64)
// expect: 9:9: returning a 'va_list'
