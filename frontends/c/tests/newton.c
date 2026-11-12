/* Newton's method: square and cube roots, a polynomial's roots, and bisection on the same
 * polynomial; float and double, with iteration counts. */
#include "fai_test.h"

double inputs[] = {2.0, 10.0, 0.5, 1e-6, 12345.678, 1e300, 3.0};

double newton_sqrt(double a, int *iters) {
  double x = a > 1 ? a : 1.0;
  *iters = 0;
  for (;;) {
    double next = 0.5 * (x + a / x);
    ++*iters;
    if (next >= x) return x;
    x = next;
  }
}

float newton_cbrt(float a) {
  float x = a;
  for (int i = 0; i < 60; i++) x = x - (x * x * x - a) / (3 * x * x);
  return x;
}

/* p(x) = x^3 - 2x - 5 (Wallis's example) and its derivative. */
double p(double x) { return (x * x - 2) * x - 5; }
double dp(double x) { return 3 * x * x - 2; }

double bisect(double lo, double hi, int steps) {
  while (steps-- > 0) {
    double mid = lo + (hi - lo) / 2;
    if ((p(mid) < 0) == (p(lo) < 0))
      lo = mid;
    else
      hi = mid;
  }
  return lo;
}

int main(void) {
  for (unsigned i = 0; i < sizeof inputs / sizeof inputs[0]; i++) {
    int n;
    double r = newton_sqrt(inputs[i], &n);
    show_d("sqrt", r);
    show("iterations", n);
    show_d("error", r * r - inputs[i]);
    show_d("vs builtin", r - __builtin_sqrt(inputs[i]));
    if (inputs[i] < 1e30f) show_f("cbrt", newton_cbrt((float)inputs[i]));
  }
  double x = 2.0;
  int k = 0;
  do {
    double step = p(x) / dp(x);
    x -= step;
    k++;
    if (step < 0 ? -step < 1e-15 : step < 1e-15) break;
  } while (k < 50);
  show_d("root", x);
  show("steps", k);
  show_d("p(root)", p(x));
  show_d("bisect", bisect(2.0, 3.0, 60));
  show_d("bisect - newton", bisect(2.0, 3.0, 60) - x);
  return 0;
}
