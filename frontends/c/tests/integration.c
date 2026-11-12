/* Numerical integration: the trapezoid rule, Simpson's rule, and a midpoint sum, of
 * polynomials and of 4 / (1 + x^2) (pi), in double and float; Kahan summation against naive. */
#include "fai_test.h"

typedef double (*fn)(double);

double cube(double x) { return x * x * x; }
double pi_density(double x) { return 4.0 / (1.0 + x * x); }
double bump(double x) { return x * (1 - x) * (x - 0.5) * (x - 0.5); }

double trapezoid(fn f, double a, double b, int n) {
  double h = (b - a) / n, s = (f(a) + f(b)) / 2;
  for (int i = 1; i < n; i++) s += f(a + i * h);
  return s * h;
}

double simpson(fn f, double a, double b, int n) {
  double h = (b - a) / n, s = f(a) + f(b);
  for (int i = 1; i < n; i++) s += (i % 2 ? 4 : 2) * f(a + i * h);
  return s * h / 3;
}

float midpoint_f(float a, float b, int n) {
  float h = (b - a) / n, s = 0;
  for (int i = 0; i < n; i++) {
    float x = a + (i + 0.5f) * h;
    s += 4.0f / (1.0f + x * x);
  }
  return s * h;
}

int main(void) {
  fn fs[] = {cube, pi_density, bump};
  const char *names[] = {"cube", "pi", "bump"};
  for (int k = 0; k < 3; k++) {
    for (int n = 2; n <= 2048; n *= 8) {
      print_str(names[k]);
      fai_put_char(' ');
      fai_put_long(n);
      fai_put_char('\n');
      show_d("trapezoid", trapezoid(fs[k], 0, 1, n));
      show_d("simpson", simpson(fs[k], 0, 1, n));
    }
  }
  show_f("midpoint float", midpoint_f(0, 1, 1000));
  /* Summing 0.1 a million times. */
  double naive = 0, sum = 0, comp = 0;
  float fsum = 0;
  for (int i = 0; i < 1000000; i++) {
    naive += 0.1;
    fsum += 0.1f;
    double y = 0.1 - comp;
    double t = sum + y;
    comp = (t - sum) - y;
    sum = t;
  }
  show_d("naive", naive);
  show_d("kahan", sum);
  show_f("float", fsum);
  return 0;
}
