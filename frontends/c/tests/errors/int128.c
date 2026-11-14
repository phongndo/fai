/* 128-bit integers are pairs of 64-bit halves in fcc, and a switch takes one FIR integer. */
int main(void) {
  __int128 big = 1;
  switch (big) {
  case 1:
    return 0;
  }
  return 1;
}

#include <stdarg.h>
__int128 first(int n, ...) {
  va_list ap;
  va_start(ap, n);
  __int128 x = va_arg(ap, __int128);
  va_end(ap);
  return x;
}
int use(void) { return (int)first(1, (__int128)2); }

// expect: 4:3: a 'switch' on a 128-bit integer
// expect: 15:16: 'va_arg' of a 128-bit integer
// expect: 19:38: 128-bit integers as variadic arguments
