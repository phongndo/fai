/* The C functions many_args.c calls, compiled by the reference compiler: they take more
 * arguments than registers, and call back into many_args.c with narrow ones (which C extends) and
 * use its narrow results. */
#include "fai_test.h"

long ext_sum10(int a, long b, unsigned c, long d, int e, long f, int g, long h, unsigned i,
               long j) {
  show("ext a", a);
  show("ext j", j);
  return a + 2 * b + 3L * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9L * i + 10 * j;
}

long ext_mix(const char *s, int a, long b, int c, long d, int e, long f, const long *p, int g) {
  print_str(s);
  fai_put_char('\n');
  return a + b + c + d + e + f + p[0] + p[2] + g;
}

long ext_calls_back(long (*f)(signed char, short, int, long, unsigned char, unsigned short,
                              unsigned, unsigned long, signed char, long)) {
  return f(-2, 1000, -3, 4, 250, 65000, 7, 8, -9, 10) +
         f(5, -6, 7, -8, 9, 10, 4294967295u, 12, 13, -14);
}

signed char sc(int x);
unsigned char uc(int x);
short ss(int x);
unsigned short us(int x);
_Bool truth(long x);

long ext_narrow_results(void) {
  long r = 0;
  for (int k = -300; k <= 300; k += 37)
    r = r * 3 + sc(k) + 2 * uc(k) + 5 * ss(k * 997) + 7 * us(k * 991) + truth(k);
  return r;
}
