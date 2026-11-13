/* Calls with more arguments than registers, of mixed widths and signedness: between functions
 * defined here (direct, recursive, and through pointers), into C functions compiled by the
 * reference compiler (tests/extern/many_args.c), and back from them into functions here, which
 * also return narrow integers to C. On x86-64 the seventh argument and later go on the stack; on
 * AArch64 the ninth. Every argument to a C function is at least an `int` (fcc can't pass
 * `char` or `short` to C on x86-64 yet: C expects its caller to extend them). */
#include "fai_test.h"

/* Defined in tests/extern/many_args.c. */
long ext_sum10(int a, long b, unsigned c, long d, int e, long f, int g, long h, unsigned i,
               long j);
long ext_mix(const char *s, int a, long b, int c, long d, int e, long f, const long *p, int g);
long ext_calls_back(long (*f)(signed char, short, int, long, unsigned char, unsigned short,
                              unsigned, unsigned long, signed char, long));
long ext_narrow_results(void);

/* Ten arguments of every width, weighted so that a swap shows. */
long weigh(signed char a, short b, int c, long d, unsigned char e, unsigned short f, unsigned g,
           unsigned long h, signed char i, long j) {
  return a + 3 * b + 5L * c + 7 * d + 11 * e + 13 * f + 17L * g + 19 * (long)h + 23 * i +
         29 * j;
}

/* Recursion with stack arguments that change on every call. */
static long spin(long n, long a, long b, long c, long d, long e, long f, long g, long h) {
  if (n == 0) return a - b + c - d + e - f + g - h;
  return spin(n - 1, h, a + 1, b, c * 2 % 1000, d, e + n, f, g - 1);
}

/* Narrow results, for C to extend. */
signed char sc(int x) { return (signed char)x; }
unsigned char uc(int x) { return (unsigned char)x; }
short ss(int x) { return (short)x; }
unsigned short us(int x) { return (unsigned short)x; }
_Bool truth(long x) { return x != 0; }

static long apply(long (*fn)(long, long, long, long, long, long, long, long), long k) {
  return fn(k, k + 1, k + 2, k + 3, k + 4, k + 5, k + 6, k + 7);
}
static long poly8(long a, long b, long c, long d, long e, long f, long g, long h) {
  return ((((((a * 2 + b) * 2 + c) * 2 + d) * 2 + e) * 2 + f) * 2 + g) * 2 + h;
}
static long alt8(long a, long b, long c, long d, long e, long f, long g, long h) {
  return a - b + c - d + e - f + g - h;
}

int main(void) {
  show("weigh", weigh(-1, -300, 70000, -5000000000L, 200, 60000, 4000000000u, 123456789012UL,
                      -128, 77));
  show("weigh2", weigh(127, 32767, -1, 1, 255, 65535, 0, 0, 1, -1));
  show("spin", spin(25, 1, 2, 3, 4, 5, 6, 7, 8));
  show("sum10", ext_sum10(-1, 2, 3000000000u, -4, 5, -6, 7, -8, 9, -10));
  long arr[3] = {100, 200, 300};
  show("mix", ext_mix("abc", 1, 2, 3, 4, 5, 6, arr, 7));
  show("back", ext_calls_back(weigh));
  show("narrow", ext_narrow_results());
  long (*fns[2])(long, long, long, long, long, long, long, long) = {poly8, alt8};
  for (int i = 0; i < 2; i++) show("apply", apply(fns[i], 3 * i - 2));
  show("sc", sc(200));
  show("uc", uc(-56));
  show("ss", ss(40000));
  show("us", us(-1));
  show("truth", truth(-5) + truth(0));
  return 0;
}
