/* Linear algebra on doubles and floats: matrix products, Gaussian elimination with partial
 * pivoting (a determinant and a solve), and a power iteration for the largest eigenvalue. */
#include "fai_test.h"

#define N 4

double A[N][N] = {{4, -2, 1, 0.5}, {3, 6, -4, 2}, {2, 1, 8, -1}, {0.25, -3, 1, 5}};
double rhs[N] = {1, 2, 3, 4};
float F[3][3] = {{0.1f, 0.2f, 0.3f}, {0.4f, 0.5f, 0.6f}, {0.7f, 0.8f, 0.9f}};

void matmul(int n, double a[][N], double b[][N], double c[][N]) {
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      double s = 0;
      for (int k = 0; k < n; k++) s += a[i][k] * b[k][j];
      c[i][j] = s;
    }
}

double fabs_(double x) { return x < 0 ? -x : x; }

/* Solves a x = b in place (a and b are destroyed); returns the determinant. */
double gauss(double a[][N], double b[], double x[]) {
  double det = 1;
  for (int c = 0; c < N; c++) {
    int piv = c;
    for (int r = c + 1; r < N; r++)
      if (fabs_(a[r][c]) > fabs_(a[piv][c])) piv = r;
    if (piv != c) {
      for (int k = 0; k < N; k++) {
        double t = a[c][k];
        a[c][k] = a[piv][k];
        a[piv][k] = t;
      }
      double t = b[c];
      b[c] = b[piv];
      b[piv] = t;
      det = -det;
    }
    det *= a[c][c];
    for (int r = c + 1; r < N; r++) {
      double f = a[r][c] / a[c][c];
      for (int k = c; k < N; k++) a[r][k] -= f * a[c][k];
      b[r] -= f * b[c];
    }
  }
  for (int r = N - 1; r >= 0; r--) {
    double s = b[r];
    for (int k = r + 1; k < N; k++) s -= a[r][k] * x[k];
    x[r] = s / a[r][r];
  }
  return det;
}

int main(void) {
  double C[N][N], D[N][N];
  matmul(N, A, A, C);
  matmul(N, C, A, D);
  for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++) show_d("A^3", D[i][j]);

  double M[N][N], b[N], x[N];
  for (int i = 0; i < N; i++) {
    b[i] = rhs[i];
    for (int j = 0; j < N; j++) M[i][j] = A[i][j];
  }
  show_d("det", gauss(M, b, x));
  for (int i = 0; i < N; i++) show_d("x", x[i]);
  for (int i = 0; i < N; i++) {
    double r = -rhs[i];
    for (int j = 0; j < N; j++) r += A[i][j] * x[j];
    show_d("residual", r);
  }

  /* Power iteration. */
  double v[N] = {1, 1, 1, 1}, lambda = 0;
  for (int it = 0; it < 100; it++) {
    double w[N], norm = 0;
    for (int i = 0; i < N; i++) {
      w[i] = 0;
      for (int j = 0; j < N; j++) w[i] += A[i][j] * v[j];
      if (fabs_(w[i]) > norm) norm = fabs_(w[i]);
    }
    for (int i = 0; i < N; i++) v[i] = w[i] / norm;
    lambda = norm;
  }
  show_d("lambda", lambda);

  float G[3][3];
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++) {
      float s = 0;
      for (int k = 0; k < 3; k++) s += F[i][k] * F[k][j];
      G[i][j] = s;
    }
  for (int i = 0; i < 3; i++) show_f("F^2 diag", G[i][i]);
  float trace = 0;
  for (int i = 0; i < 3; i++) trace += G[i][i];
  show_f("trace", trace);
  return 0;
}
