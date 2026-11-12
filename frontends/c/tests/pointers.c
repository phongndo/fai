/* Pointers: address-of, dereference, arithmetic, differences, comparisons, pointers to
 * pointers, and void pointers converted back. */
#include "fai_test.h"
#include <stddef.h>

static void swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}

static int sum(const int *begin, const int *end) {
  int s = 0;
  while (begin < end) s += *begin++;
  return s;
}

int main(void) {
  int a = 1, b = 2;
  swap(&a, &b);
  show("swapped a", a);
  show("swapped b", b);
  int arr[8];
  for (int i = 0; i < 8; i++) arr[i] = i * i;
  show("sum", sum(arr, arr + 8));
  show("sum tail", sum(&arr[5], &arr[8]));
  int *p = arr + 6;
  show("p[-2]", p[-2]);
  show("2[arr]", 2 [arr]);
  ptrdiff_t d = p - arr;
  show("p - arr", d);
  show("arr < p", arr < p);
  show("p >= arr + 6", p >= arr + 6);
  show("p == &arr[6]", p == &arr[6]);
  int *np = NULL;
  show("null is false", !np);
  int **pp = &p;
  **pp = 99;
  show("arr[6]", arr[6]);
  *pp = &a;
  show("*p", *p);
  void *v = arr;
  int *back = v;
  show("back[3]", back[3]);
  char *bytes = (char *)&arr[1];
  show("first byte of arr[1]", bytes[0]);
  long *lp = (long *)0;
  show("null long ptr", lp == 0);
  const int *cp = arr;
  cp += 3;
  show("*cp", *cp);
  cp -= 2;
  show("*cp", *cp);
  return 0;
}
