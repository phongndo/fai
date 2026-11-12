/* A rational-number library on a struct of two longs (16 bytes: x0 and x1 each way), always in
 * lowest terms with a positive denominator: sums of harmonic and alternating series, continued
 * fractions of sqrt(2) and e, Egyptian fractions, Gaussian elimination over the rationals, and
 * a table of mixed results returned through a struct of a rational and a flag. */
#include "fai_test.h"

typedef struct { long num, den; } rat;
typedef struct { rat value; int exact; } result; /* 24 bytes: returned through x8 */

static long gcd(long a, long b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  while (b) {
    long t = a % b;
    a = b;
    b = t;
  }
  return a;
}
static rat mk(long n, long d) {
  if (d < 0) {
    n = -n;
    d = -d;
  }
  long g = gcd(n, d);
  if (g > 1) {
    n /= g;
    d /= g;
  }
  return (rat){n, d};
}
static rat radd(rat a, rat b) {
  long g = gcd(a.den, b.den);
  return mk(a.num * (b.den / g) + b.num * (a.den / g), a.den / g * b.den);
}
static rat rneg(rat a) { return (rat){-a.num, a.den}; }
static rat rsub(rat a, rat b) { return radd(a, rneg(b)); }
static rat rmul(rat a, rat b) {
  long g1 = gcd(a.num, b.den), g2 = gcd(b.num, a.den);
  if (g1 == 0) g1 = 1;
  if (g2 == 0) g2 = 1;
  return mk((a.num / g1) * (b.num / g2), (a.den / g2) * (b.den / g1));
}
static rat rinv(rat a) { return mk(a.den, a.num); }
static rat rdiv(rat a, rat b) { return rmul(a, rinv(b)); }
static int rcmp(rat a, rat b) {
  long l = a.num * b.den, r = b.num * a.den;
  return (l > r) - (l < r);
}
static rat from_long(long n) { return (rat){n, 1}; }

static void show_r(const char *label, rat r) {
  print_str(label);
  fai_put_char(' ');
  fai_put_long(r.num);
  fai_put_char('/');
  fai_put_long(r.den);
  fai_put_char('\n');
}

/* Evaluate the continued fraction [a0; a1, ..., a_{n-1}]. */
static rat cfrac(const long *a, int n) {
  rat r = from_long(a[n - 1]);
  for (int i = n - 2; i >= 0; i--) r = radd(from_long(a[i]), rinv(r));
  return r;
}

/* A division that reports a zero divisor instead of dividing. */
static result safe_div(rat a, rat b) {
  if (b.num == 0) return (result){{0, 1}, 0};
  return (result){rdiv(a, b), 1};
}

int main(void) {
  rat h = from_long(0);
  for (int i = 1; i <= 20; i++) h = radd(h, mk(1, i));
  show_r("H20", h);
  rat alt = from_long(0);
  for (int i = 1; i <= 15; i++) alt = radd(alt, mk(i % 2 ? 1 : -1, i));
  show_r("alternating 15", alt);
  show_r("product", rmul(mk(-21, 8), mk(4, -35)));
  show_r("quotient", rdiv(mk(3, 7), mk(9, 14)));
  show("compare", rcmp(mk(355, 113), mk(22, 7)) * 10 + rcmp(mk(1, 3), mk(2, 6)));

  long sqrt2[12], e[12];
  for (int i = 0; i < 12; i++) {
    sqrt2[i] = i == 0 ? 1 : 2;
    e[i] = i == 0 ? 2 : (i % 3 == 2 ? 2 * (i / 3 + 1) : 1);
  }
  for (int n = 2; n <= 12; n += 5) {
    show_r("sqrt2", cfrac(sqrt2, n));
    show_r("e", cfrac(e, n));
  }

  /* Egyptian fractions of 4/13 by the greedy algorithm. */
  rat r = mk(4, 13);
  print_str("egyptian 4/13 =");
  while (r.num != 0) {
    long d = (r.den + r.num - 1) / r.num;
    fai_put_char(' ');
    fai_put_long(d);
    r = rsub(r, mk(1, d));
  }
  fai_put_char('\n');

  /* Solve a 3x3 system exactly: the Hilbert matrix times x = (1, 1, 1). */
  rat m[3][4];
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++) m[i][j] = mk(1, i + j + 1);
    m[i][3] = from_long(1);
  }
  for (int col = 0; col < 3; col++) {
    for (int row = col + 1; row < 3; row++) {
      rat f = rdiv(m[row][col], m[col][col]);
      for (int k = col; k < 4; k++) m[row][k] = rsub(m[row][k], rmul(f, m[col][k]));
    }
  }
  rat x[3];
  for (int i = 2; i >= 0; i--) {
    rat s = m[i][3];
    for (int k = i + 1; k < 3; k++) s = rsub(s, rmul(m[i][k], x[k]));
    x[i] = rdiv(s, m[i][i]);
  }
  show_r("x0", x[0]);
  show_r("x1", x[1]);
  show_r("x2", x[2]);

  rat ds[4] = {{1, 2}, {0, 1}, {-3, 4}, {5, 1}};
  for (int i = 0; i < 4; i++) {
    result q = safe_div(mk(7, 3), ds[i]);
    show("exact", q.exact);
    show_r("value", q.value);
  }
  show("safe_div().value.den", safe_div(mk(1, 6), mk(1, 4)).value.den);
  return 0;
}
