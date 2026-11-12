/* float and double arithmetic at the edges: NaNs (quiet, signaling, with payloads), infinities,
 * signed zeros, subnormals, overflow and underflow, ties to even; unary minus, every comparison
 * on NaN, `!x` and conditions on floats, compound assignment, and ++/-- on floats. The inputs
 * are non-constant globals, so the reference compiler can't fold them. */
#include "fai_test.h"

double dv[] = {0.0,     -0.0,     1.0,      -1.5,     0.1,       3.0,
               1e308,   -1e308,   4.9e-324, -4.9e-324, 2.2250738585072014e-308,
               1.0 / 0.0, -1.0 / 0.0};
float fv[] = {0.0f, -0.0f, 1.0f, -1.5f, 0.1f, 3.0f, 3e38f, -3e38f, 1.4e-45f, 1.17549435e-38f};
/* NaNs by their bits: the canonical one, a negative one with a payload, a signaling one. */
unsigned long nan_bits[] = {0x7ff8000000000000UL, 0xfff8000000000123UL, 0x7ff0000000000456UL};
unsigned fnan_bits[] = {0x7fc00000u, 0xffc00123u, 0x7f800456u};

double from_bits(unsigned long u) {
  union {
    unsigned long u;
    double d;
  } x;
  x.u = u;
  return x.d;
}
float from_fbits(unsigned u) {
  union {
    unsigned u;
    float f;
  } x;
  x.u = u;
  return x.f;
}

void compare(double a, double b) {
  fai_put_long(a < b);
  fai_put_long(a <= b);
  fai_put_long(a > b);
  fai_put_long(a >= b);
  fai_put_long(a == b);
  fai_put_long(a != b);
  fai_put_long(!a);
  fai_put_long(a ? 1 : 0);
  _Bool t = a;
  fai_put_long(t);
  if (a && b) fai_put_char('&');
  if (a || b) fai_put_char('|');
  fai_put_char('\n');
}

void fcompare(float a, float b) {
  fai_put_long(a < b);
  fai_put_long(a <= b);
  fai_put_long(a > b);
  fai_put_long(a >= b);
  fai_put_long(a == b);
  fai_put_long(a != b);
  fai_put_long(!a);
  while (a) {
    fai_put_char('w');
    break;
  }
  fai_put_char('\n');
}

double inf_d = 1.0 / 0.0;

int main(void) {
  int nd = sizeof dv / sizeof dv[0], nf = sizeof fv / sizeof fv[0];
  /* Every pair of doubles through + - * /. */
  for (int i = 0; i < nd; i++) {
    for (int j = 0; j < nd; j++) {
      double a = dv[i], b = dv[j];
      show_d("+", a + b);
      show_d("-", a - b);
      show_d("*", a * b);
      show_d("/", a / b);
      compare(a, b);
    }
    show_d("neg", -dv[i]);
  }
  for (int i = 0; i < nf; i++) {
    for (int j = 0; j < nf; j++) {
      float a = fv[i], b = fv[j];
      show_f("f+", a + b);
      show_f("f-", a - b);
      show_f("f*", a * b);
      show_f("f/", a / b);
      fcompare(a, b);
    }
    show_f("fneg", -fv[i]);
  }
  /* NaNs: payloads propagate (quieted), comparisons are unordered. */
  for (int i = 0; i < 3; i++) {
    double n = from_bits(nan_bits[i]);
    float fn = from_fbits(fnan_bits[i]);
    show_d("nan+1", n + 1.0);
    show_d("1*nan", 1.5 * n);
    show_d("neg nan", -n);
    show_f("fnan+1", fn + 1.0f);
    show_f("fneg nan", -fn);
    /* With two different NaNs C doesn't say whose payload wins (the reference compiler
     * commutes `+` and `*`), so both operands are the same NaN. */
    show_d("nan+nan", n + n);
    show_f("fnan*fnan", fn * fn);
    show_d("nan-inf", n - inf_d);
    compare(n, 1.0);
    compare(n, n);
    fcompare(fn, fn);
  }
  /* Invalid operations make the default NaN. */
  double inf = dv[11], zero = dv[0];
  show_d("inf-inf", inf - inf);
  show_d("0/0", zero / zero);
  show_d("0*inf", zero * inf);
  show_d("1/-0", 1.0 / dv[1]);

  /* Ties to even, at both precisions. */
  double one = dv[2];
  show_d("1+2^-53", one + 0x1p-53);
  show_d("1+3*2^-53", one + 0x3p-53);
  float fone = fv[2];
  show_f("f1+2^-24", fone + 0x1p-24f);
  show_f("f1+3*2^-24", fone + 0x3p-24f);
  show_d("0.1+0.2", dv[4] + 0.2);
  show_f("f0.1+0.2", fv[4] + 0.2f);
  /* Subnormals: the smallest halves to zero (a tie, even); the largest subnormal plus the
   * smallest is the smallest normal. */
  show_d("min/2", dv[8] / 2);
  show_d("min*1.5", dv[8] * 1.5);
  show_d("minnormal-min", dv[10] - dv[8]);
  show_f("fmin/2", fv[8] / 2);
  show_f("fmin*3/2", fv[8] * 3 / 2);
  show_f("fminnormal-min", fv[9] - fv[8]);

  /* Compound assignment and increments. */
  double x = dv[4];
  x += 1;
  x *= 3;
  x -= 0.25f;
  x /= 7;
  show_d("x", x);
  float f = fv[4];
  f += x;
  f *= 2;
  show_f("f", f);
  int k = 7;
  k *= 1.5;
  show("k", k);
  k += 0.75;
  show("k", k);
  k /= 0.5;
  show("k", k);
  long acc = 3;
  acc -= dv[3];
  show("acc", acc);
  double y = 0.5;
  show_d("y++", y++);
  show_d("++y", ++y);
  show_d("y--", y--);
  show_d("--y", --y);
  float g = 16777216.0f;
  g++;
  show_f("2^24+1", g);
  g--;
  --g;
  show_f("2^24-2", g);
  /* Accumulating 0.1 ten times isn't 1. */
  double s = 0;
  for (int i = 0; i < 10; i++) s += dv[4];
  show_d("sum", s);
  show("sum==1", s == 1.0);
  /* No contraction: `a * b + c` rounds twice (a fused 0.1 * 10 - 1 is 2^-54). */
  show_d("0.1*10-1", dv[4] * 10 - dv[2]);
  show_f("f0.1*10-1", fv[4] * 10 - fv[2]);
  /* Mixed float and double: the float converts. */
  show_d("mixed", fv[4] * dv[4]);
  show_d("cond", dv[2] > fv[3] ? dv[4] : fv[4]);
  return 0;
}
