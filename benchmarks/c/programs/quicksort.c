// Recursive quicksort (median of three, insertion sort below 16) of pseudo-random ints, repeated:
// calls, recursion, swaps through pointers.
#include <stdio.h>
#include <stdlib.h>

static void insertion(int *a, int lo, int hi) {
  for (int i = lo + 1; i <= hi; i++) {
    int v = a[i], j = i - 1;
    while (j >= lo && a[j] > v) {
      a[j + 1] = a[j];
      j--;
    }
    a[j + 1] = v;
  }
}

static void swap(int *a, int i, int j) {
  int t = a[i];
  a[i] = a[j];
  a[j] = t;
}

static void quicksort(int *a, int lo, int hi) {
  while (hi - lo >= 16) {
    int mid = lo + (hi - lo) / 2;
    if (a[mid] < a[lo]) swap(a, mid, lo);
    if (a[hi] < a[lo]) swap(a, hi, lo);
    if (a[hi] < a[mid]) swap(a, hi, mid);
    int pivot = a[mid];
    int i = lo, j = hi;
    while (i <= j) {
      while (a[i] < pivot) i++;
      while (a[j] > pivot) j--;
      if (i <= j) swap(a, i++, j--);
    }
    if (j - lo < hi - i) {
      quicksort(a, lo, j);
      lo = i;
    } else {
      quicksort(a, i, hi);
      hi = j;
    }
  }
  insertion(a, lo, hi);
}

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  int n = 100000;
  int *a = malloc(sizeof(int) * n);
  unsigned s = 7;
  long check = 0;
  for (int r = 0; r < reps; r++) {
    for (int i = 0; i < n; i++) {
      s = s * 1103515245u + 12345u;
      a[i] = (int)(s >> 1) % 1000000;
    }
    quicksort(a, 0, n - 1);
    for (int i = 1; i < n; i++)
      if (a[i - 1] > a[i]) {
        printf("quicksort unsorted at %d\n", i);
        return 1;
      }
    check += a[n / 2] + a[n / 3];
  }
  printf("quicksort %ld\n", check);
  free(a);
  return 0;
}
