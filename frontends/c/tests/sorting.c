/* Sorting: insertion sort, quicksort, merge sort with a buffer, heap sort, and a generic sort
 * through a comparison function pointer over structs. */
#include "fai_test.h"

static unsigned long seed = 12345;
static int rnd(void) {
  seed = seed * 6364136223846793005ul + 1442695040888963407ul;
  return (int)(seed >> 33) % 1000;
}

static void insertion(int *a, int n) {
  for (int i = 1; i < n; i++) {
    int v = a[i], j = i - 1;
    while (j >= 0 && a[j] > v) { a[j + 1] = a[j]; j--; }
    a[j + 1] = v;
  }
}

static void quick(int *a, int lo, int hi) {
  if (lo >= hi) return;
  int p = a[(lo + hi) / 2], i = lo, j = hi;
  while (i <= j) {
    while (a[i] < p) i++;
    while (a[j] > p) j--;
    if (i <= j) { int t = a[i]; a[i] = a[j]; a[j] = t; i++; j--; }
  }
  quick(a, lo, j);
  quick(a, i, hi);
}

static int buffer[256];
static void merge_sort(int *a, int n) {
  if (n < 2) return;
  int m = n / 2;
  merge_sort(a, m);
  merge_sort(a + m, n - m);
  int i = 0, j = m, k = 0;
  while (i < m && j < n) buffer[k++] = a[i] <= a[j] ? a[i++] : a[j++];
  while (i < m) buffer[k++] = a[i++];
  while (j < n) buffer[k++] = a[j++];
  for (k = 0; k < n; k++) a[k] = buffer[k];
}

static void sift(int *a, int i, int n) {
  for (;;) {
    int l = 2 * i + 1, r = l + 1, m = i;
    if (l < n && a[l] > a[m]) m = l;
    if (r < n && a[r] > a[m]) m = r;
    if (m == i) return;
    int t = a[i]; a[i] = a[m]; a[m] = t;
    i = m;
  }
}
static void heap(int *a, int n) {
  for (int i = n / 2 - 1; i >= 0; i--) sift(a, i, n);
  for (int e = n - 1; e > 0; e--) {
    int t = a[0]; a[0] = a[e]; a[e] = t;
    sift(a, 0, e);
  }
}

struct person { const char *name; int age; };
static int by_age(const void *a, const void *b) {
  const struct person *x = a, *y = b;
  return x->age - y->age;
}
static void generic_sort(void *base, int n, int size, int (*cmp)(const void *, const void *)) {
  char *b = base;
  for (int i = 1; i < n; i++)
    for (int j = i; j > 0 && cmp(b + (j - 1) * size, b + j * size) > 0; j--)
      for (int k = 0; k < size; k++) {
        char t = b[(j - 1) * size + k];
        b[(j - 1) * size + k] = b[j * size + k];
        b[j * size + k] = t;
      }
}

static long digest(const int *a, int n) {
  long h = 0;
  for (int i = 0; i < n; i++) {
    if (i && a[i - 1] > a[i]) return -1;
    h = (h * 131 + a[i]) % 1000000007;
  }
  return h;
}

int main(void) {
  int a[200], b[200], c[200], d[200];
  for (int i = 0; i < 200; i++) a[i] = b[i] = c[i] = d[i] = rnd();
  insertion(a, 200);
  quick(b, 0, 199);
  merge_sort(c, 200);
  heap(d, 200);
  show("insertion", digest(a, 200));
  show("quick", digest(b, 200));
  show("merge", digest(c, 200));
  show("heap", digest(d, 200));
  struct person people[] = {{"ann", 31}, {"bob", 25}, {"cyd", 47}, {"dee", 19}, {"eve", 25}};
  generic_sort(people, 5, sizeof people[0], by_age);
  for (int i = 0; i < 5; i++) {
    print_str(people[i].name);
    fai_put_char(' ');
    print_long(people[i].age);
  }
  return 0;
}
