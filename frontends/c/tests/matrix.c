/* Integer matrices: multiplication, transpose, powers (Fibonacci by matrix power, modular),
 * and a determinant by fraction-free elimination. */
#include "fai_test.h"

#define M 4
typedef long mat[M][M];

static void mul(mat r, mat a, mat b) {
  mat t;
  for (int i = 0; i < M; i++)
    for (int j = 0; j < M; j++) {
      long s = 0;
      for (int k = 0; k < M; k++) s += a[i][k] * b[k][j];
      t[i][j] = s;
    }
  for (int i = 0; i < M; i++)
    for (int j = 0; j < M; j++) r[i][j] = t[i][j];
}

static void fib_matrix(unsigned long n, unsigned long mod, unsigned long out[2][2]) {
  unsigned long r[2][2] = {{1, 0}, {0, 1}}, b[2][2] = {{1, 1}, {1, 0}};
  while (n) {
    unsigned long t[2][2];
    if (n & 1) {
      for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) t[i][j] = (r[i][0] * b[0][j] + r[i][1] * b[1][j]) % mod;
      for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) r[i][j] = t[i][j];
    }
    for (int i = 0; i < 2; i++)
      for (int j = 0; j < 2; j++) t[i][j] = (b[i][0] * b[0][j] + b[i][1] * b[1][j]) % mod;
    for (int i = 0; i < 2; i++)
      for (int j = 0; j < 2; j++) b[i][j] = t[i][j];
    n >>= 1;
  }
  for (int i = 0; i < 2; i++)
    for (int j = 0; j < 2; j++) out[i][j] = r[i][j];
}

static long det(mat a) {
  mat m;
  for (int i = 0; i < M; i++)
    for (int j = 0; j < M; j++) m[i][j] = a[i][j];
  long prev = 1, sign = 1;
  for (int k = 0; k < M - 1; k++) {
    if (m[k][k] == 0) {
      int r = k + 1;
      while (r < M && m[r][k] == 0) r++;
      if (r == M) return 0;
      for (int j = 0; j < M; j++) { long t = m[k][j]; m[k][j] = m[r][j]; m[r][j] = t; }
      sign = -sign;
    }
    for (int i = k + 1; i < M; i++)
      for (int j = k + 1; j < M; j++) m[i][j] = (m[i][j] * m[k][k] - m[i][k] * m[k][j]) / prev;
    prev = m[k][k];
  }
  return sign * m[M - 1][M - 1];
}

int main(void) {
  mat a = {{2, 0, 1, 3}, {1, 1, 0, 2}, {0, 3, 1, 1}, {4, 1, 2, 0}};
  mat id = {{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}};
  mat p;
  mul(p, a, id);
  mul(p, p, a);
  mul(p, p, a);
  long trace = 0;
  for (int i = 0; i < M; i++) trace += p[i][i];
  show("trace a^3", trace);
  show("a^3[3][0]", p[3][0]);
  show("det a", det(a));
  show("det a^3", det(p));
  unsigned long f[2][2];
  fib_matrix(90, 1000000007ul, f);
  show("fib(90) mod p", (long)f[0][1]);
  fib_matrix(1000000, 1000000007ul, f);
  show("fib(10^6) mod p", (long)f[0][1]);
  return 0;
}
