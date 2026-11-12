/* Complex arithmetic on a struct of two doubles (an HFA: d0 and d1 each way) and of two floats:
 * products, quotients, integer powers by squaring, a Julia set drawn as ASCII, the roots of
 * unity, a radix-2 FFT and its inverse on 16 points, and Newton's method on z^3 - 1. */
#include "fai_test.h"

typedef struct { double re, im; } cplx;
typedef struct { float re, im; } cplxf;

static cplx c(double re, double im) { return (cplx){re, im}; }
static cplx cadd(cplx a, cplx b) { return c(a.re + b.re, a.im + b.im); }
static cplx csub(cplx a, cplx b) { return c(a.re - b.re, a.im - b.im); }
static cplx cmul(cplx a, cplx b) { return c(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re); }
static cplx cscale(cplx a, double k) { return c(a.re * k, a.im * k); }
static cplx cconj(cplx a) { return c(a.re, -a.im); }
static double cnorm2(cplx a) { return a.re * a.re + a.im * a.im; }
static cplx cdiv(cplx a, cplx b) { return cscale(cmul(a, cconj(b)), 1.0 / cnorm2(b)); }
static cplx cpow(cplx z, unsigned n) {
  cplx r = c(1, 0);
  while (n) {
    if (n & 1) r = cmul(r, z);
    z = cmul(z, z);
    n >>= 1;
  }
  return r;
}
static cplxf cmulf(cplxf a, cplxf b) {
  return (cplxf){a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re};
}

static void show_c(const char *label, cplx z) {
  print_str(label);
  fai_put_char('\n');
  show_d("  re", z.re);
  show_d("  im", z.im);
}

/* In-place radix-2 FFT of n points (n a power of two); `w` holds the n/2 twiddles. */
static void fft(cplx *x, int n, const cplx *w, int inverse) {
  for (int i = 1, j = 0; i < n; i++) {
    int bit = n >> 1;
    for (; j & bit; bit >>= 1) j ^= bit;
    j ^= bit;
    if (i < j) {
      cplx t = x[i];
      x[i] = x[j];
      x[j] = t;
    }
  }
  for (int len = 2; len <= n; len <<= 1) {
    for (int i = 0; i < n; i += len) {
      for (int k = 0; k < len / 2; k++) {
        cplx tw = w[k * (n / len)];
        if (inverse) tw = cconj(tw);
        cplx u = x[i + k], v = cmul(x[i + k + len / 2], tw);
        x[i + k] = cadd(u, v);
        x[i + k + len / 2] = csub(u, v);
      }
    }
  }
}

int main(void) {
  cplx a = c(3, 4), b = c(1, -2);
  show_c("a*b", cmul(a, b));
  show_c("a/b", cdiv(a, b));
  show_c("(a/b)*b", cmul(cdiv(a, b), b));
  show_c("a^10", cpow(a, 10));
  show_c("i^4", cpow(c(0, 1), 4));
  cplxf f = cmulf((cplxf){1.5f, -0.5f}, (cplxf){0.25f, 2.0f});
  show_f("float re", f.re);
  show_f("float im", f.im);

  /* A Julia set for c = -0.8 + 0.156i. */
  cplx k = c(-0.8, 0.156);
  long inside = 0;
  for (int row = 0; row < 16; row++) {
    for (int col = 0; col < 48; col++) {
      cplx z = c(-1.6 + col * (3.2 / 48), -1.0 + row * (2.0 / 16));
      int it = 0;
      while (it < 60 && cnorm2(z) <= 4.0) {
        z = cadd(cmul(z, z), k);
        it++;
      }
      inside += it == 60;
      fai_put_char(" .:-=+*#%@"[it * 9 / 60]);
    }
    fai_put_char('\n');
  }
  show("inside", inside);

  /* Twiddles by repeated multiplication from w = e^{-2 pi i / 16}, with the exact cos and sin of
   * pi/8 as constants. */
  enum { N = 16 };
  cplx w[N / 2];
  cplx step = c(0.92387953251128674, -0.38268343236508978);
  w[0] = c(1, 0);
  for (int i = 1; i < N / 2; i++) w[i] = cmul(w[i - 1], step);
  show_c("w^8", cmul(w[7], step));
  cplx x[N];
  for (int i = 0; i < N; i++) x[i] = c(i % 4 == 0 ? 1.0 : 0.0, (i * 7 % 5) * 0.25);
  cplx orig[N];
  for (int i = 0; i < N; i++) orig[i] = x[i];
  fft(x, N, w, 0);
  for (int i = 0; i < N; i += 3) {
    show("bin", i);
    show_c("X", x[i]);
  }
  fft(x, N, w, 1);
  double err = 0;
  for (int i = 0; i < N; i++) {
    cplx d = csub(cscale(x[i], 1.0 / N), orig[i]);
    err += cnorm2(d);
  }
  show("round trip small", err < 1e-20);

  /* Newton on z^3 = 1 from points around the circle: which root each finds. */
  for (int i = 0; i < 12; i++) {
    cplx z = cpow(c(0.92387953251128674, 0.38268343236508978), (unsigned)i);
    z = cscale(z, 1.5);
    for (int it = 0; it < 30; it++) {
      cplx z2 = cmul(z, z);
      z = csub(z, cdiv(csub(cmul(z2, z), c(1, 0)), cscale(z2, 3)));
    }
    int root = z.re > 0 ? 0 : z.im > 0 ? 1 : 2;
    show("root", root);
  }
  return 0;
}
