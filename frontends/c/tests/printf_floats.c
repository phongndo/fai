/* printf with doubles and floats (promoted to double): %f %e %g %a and their upper-case forms,
 * widths, precisions (also through *), flags, rounding at the last digit, signed zeros,
 * infinities, NaNs, subnormals, and the limits; a float computed in the program and printed
 * both ways. */
#include <float.h>
#include <math.h>
#include <stdio.h>

/* Inputs in non-constant globals, so the reference compiler can't fold the calls. */
double d[] = {0.0, -0.0, 1.0, -2.5, 0.1, 1.0 / 3, 123456.789, 1e-5, 6.02214076e23, 2.5e-300,
              DBL_MIN, DBL_MAX, 4.9e-324, 0.5, 1.5, 2.5, 1e15, 1e16, 9.999999e-5};
float f[] = {0.1f, -3.75f, 16777217.0f, FLT_MIN, FLT_MAX, 1e-45f};
double three = 3.0;

int main(void) {
  for (unsigned i = 0; i < sizeof d / sizeof d[0]; i++) {
    double x = d[i];
    printf("%2u f %f | %.2f | %.0f | %12.4f | %-12.1f| %+f\n", i, x, x, x, x, x, x);
    printf("   e %e | %.3E | %.0e | %+.10e\n", x, x, x, x);
    printf("   g %g | %G | %.3g | %#g | %.17g | %#.0g\n", x, x, x, x, x, x);
    printf("   a %a | %A | %.3a | %.0a\n", x, x, x, x);
  }
  for (unsigned i = 0; i < sizeof f / sizeof f[0]; i++)
    printf("float %f %e %g %a %.9g\n", f[i], f[i], f[i], f[i], f[i]);
  /* Infinities and NaNs. */
  double inf = d[11] * 10, nan = inf - inf;
  printf("[%f] [%F] [%e] [%G] [%a] [%5f] [%-6e]\n", inf, -inf, inf, -inf, inf, inf, -inf);
  printf("[%f] [%E] [%g] [%A] [%+f] [% f]\n", nan, nan, nan, nan, fabs(nan), fabs(nan));
  /* Ties: printf rounds the exact binary value, to even on an exact tie. */
  printf("ties %.0f %.0f %.0f %.0f %.1f %.1f %.2f\n", d[13], d[14], d[15], -d[13], 0.25, 0.35,
         1.005);
  /* Width and precision through *. */
  for (int p = 0; p <= 12; p += 3) printf("[%*.*f] [%.*e] [%.*g]\n", p + 8, p, d[5], p, d[5], p, d[5]);
  /* Zero padding and the alternative forms. */
  printf("[%010.3f] [%-10.3f] [%+010.2e] [%#.0f] [%#.0e] [%#x]\n", -d[3], d[3], d[4], three,
         three, 0);
  /* A computation's result, through its bits and its value. */
  float acc = 0;
  for (int i = 1; i <= 10; i++) acc += f[0] * i;
  union {
    float f;
    unsigned u;
  } bits = {acc};
  printf("sum 0x%08x %.9g %a\n", bits.u, acc, acc);
  double harmonic = 0;
  for (int i = 1; i <= 1000; i++) harmonic += 1.0 / i;
  printf("harmonic %.17g %a %e\n", harmonic, harmonic, harmonic);
  printf("sqrt2 %.20f\n", sqrt(2.0));
  return 0;
}
