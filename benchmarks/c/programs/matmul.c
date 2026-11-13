// Dense double matrix multiply (i-k-j order) on the heap, repeated: 2D indexing, FP multiply-add
// (not contracted: every compiler is run with -ffp-contract=off).
#include <stdio.h>
#include <stdlib.h>

static void init(double *m, int n, unsigned seed) {
  for (int i = 0; i < n * n; i++) {
    seed = seed * 1103515245u + 12345u;
    m[i] = (double)(seed >> 16 & 1023) / 512.0 - 1.0;
  }
}

static void matmul(const double *a, const double *b, double *c, int n) {
  for (int i = 0; i < n * n; i++)
    c[i] = 0.0;
  for (int i = 0; i < n; i++)
    for (int k = 0; k < n; k++) {
      double aik = a[i * n + k];
      for (int j = 0; j < n; j++)
        c[i * n + j] += aik * b[k * n + j];
    }
}

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  int n = 160;
  double *a = malloc(sizeof(double) * n * n);
  double *b = malloc(sizeof(double) * n * n);
  double *c = malloc(sizeof(double) * n * n);
  init(a, n, 1);
  init(b, n, 2);
  double sum = 0.0;
  for (int r = 0; r < reps; r++) {
    matmul(a, b, c, n);
    for (int i = 0; i < n * n; i += 7)
      sum += c[i];
    a[r % (n * n)] += 0.5;
  }
  printf("matmul %.9e\n", sum);
  free(a);
  free(b);
  free(c);
  return 0;
}
