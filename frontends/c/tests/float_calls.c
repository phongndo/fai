/* Floats through calls: float and double parameters and results, more than eight float
 * arguments (the rest on the stack), floats interleaved with integers, recursion, and calls
 * through function pointers (in arrays, in structs, returned by functions, as callbacks). */
#include "fai_test.h"

typedef double (*unary)(double);
typedef float (*fbinary)(float, float);

double half(double x) { return x / 2; }
double square(double x) { return x * x; }
double negate(double x) { return -x; }
float fadd(float a, float b) { return a + b; }
float fmul(float a, float b) { return a * b; }
float fsub(float a, float b) { return a - b; }

/* Ten doubles and ten floats: d0-d7 then the stack. */
double sum10(double a, double b, double c, double d, double e, double f, double g, double h,
             double i, double j) {
  return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j;
}
float fsum10(float a, float b, float c, float d, float e, float f, float g, float h, float i,
             float j) {
  return a - b + c - d + e - f + g - h + i * 100 - j * 1000;
}

/* Integers and floats interleaved, each class past its eight registers. */
double mixed(int i0, double d0, long i1, float f1, int i2, double d2, char c3, float f3,
             int i4, double d4, int i5, double d5, int i6, double d6, int i7, double d7,
             int i8, float f8, long i9, double d9) {
  return i0 + d0 * 2 + i1 * 3 + f1 * 4 + i2 * 5 + d2 * 6 + c3 * 7 + f3 * 8 + i4 * 9 + d4 * 10 +
         i5 * 11 + d5 * 12 + i6 * 13 + d6 * 14 + i7 * 15 + d7 * 16 + i8 * 17 + f8 * 18 +
         i9 * 19 + d9 * 20;
}

double power(double x, int n) {
  if (n == 0) return 1;
  if (n < 0) return 1 / power(x, -n);
  double h = power(x, n / 2);
  return n % 2 ? h * h * x : h * h;
}

double apply(unary f, double x, int times) {
  while (times-- > 0) x = f(x);
  return x;
}

struct ops {
  const char *name;
  fbinary op;
  float unit;
};

fbinary pick(int k) { return k == 0 ? fadd : k == 1 ? fmul : fsub; }

float fold(fbinary op, float init, const float *xs, int n) {
  for (int i = 0; i < n; i++) init = op(init, xs[i]);
  return init;
}

/* A float result that is also a float argument of the next call. */
float chain(float x) { return fmul(fadd(x, 1.5f), fsub(x, 0.25f)); }

void sort(double *xs, int n, int (*less)(double, double)) {
  for (int i = 1; i < n; i++) {
    double v = xs[i];
    int j = i;
    while (j > 0 && less(v, xs[j - 1])) {
      xs[j] = xs[j - 1];
      j--;
    }
    xs[j] = v;
  }
}
int ascending(double a, double b) { return a < b; }
int by_magnitude(double a, double b) { return (a < 0 ? -a : a) > (b < 0 ? -b : b); }

double values[] = {3.5, -7.25, 0.0, 1e10, -1e-10, 42.0, -0.0, 2.5};

int main(void) {
  unary table[] = {half, square, negate};
  for (int i = 0; i < 3; i++) show_d("apply", apply(table[i], 3.0, 3));
  show_d("sum10", sum10(1, 2, 3, 4, 5, 6, 7, 8, 9.5, 10.25));
  show_f("fsum10", fsum10(1, 2, 3, 4, 5, 6, 7, 8, 0.5f, 0.125f));
  double (*s10)(double, double, double, double, double, double, double, double, double,
                double) = sum10;
  show_d("sum10 indirect", s10(0.5, 1, 1.5, 2, 2.5, 3, 3.5, 4, 4.5, 5));
  show_d("mixed", mixed(1, 0.5, 2, 0.25f, 3, 1.5, 'a', -0.75f, 4, 2.5, 5, 3.5, 6, 4.5, 7, 5.5,
                        8, 0.125f, 9, 6.5));
  show_d("power", power(1.0001, 10000));
  show_d("power neg", power(2, -10));
  float xs[] = {1.5f, 2.0f, -0.5f, 4.0f};
  struct ops ops[] = {{"sum", fadd, 0.0f}, {"product", fmul, 1.0f}, {"difference", fsub, 0.0f}};
  for (int i = 0; i < 3; i++) {
    print_str(ops[i].name);
    fai_put_char(' ');
    show_f("fold", fold(ops[i].op, ops[i].unit, xs, 4));
    show_f("pick", pick(i)(3.0f, 0.5f));
  }
  show_f("chain", chain(chain(2.0f)));
  double v[8];
  for (int i = 0; i < 8; i++) v[i] = values[i];
  sort(v, 8, ascending);
  for (int i = 0; i < 8; i++) show_d("ascending", v[i]);
  sort(v, 8, by_magnitude);
  for (int i = 0; i < 8; i++) show_d("by magnitude", v[i]);
  return (int)apply(half, 64.0, 3);
}
