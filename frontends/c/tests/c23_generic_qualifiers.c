/* C23: arrays of qualified elements are qualified array types, so a pointer to an array of int
 * converts to a pointer to an array of const int; and _Generic's controlling operand
 * undergoes lvalue conversion. */
#include "fai_test.h"

static int total(const int (*rows)[3], int n) {
  int s = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < 3; j++) s += rows[i][j];
  return s;
}

static void zero(void *p, unsigned long n) {
  unsigned char *b = p;
  while (n--) *b++ = 0;
}

int main(void) {
  int m[2][3] = {{1, 2, 3}, {4, 5, 6}};
  show("total", total(m, 2));
  const int c = 3;
  show("generic const", _Generic(c, int: 1, const int: 2, default: 3));
  const int arr[2] = {7, 8};
  show("generic arr", _Generic(arr, const int *: 1, int *: 2, default: 3));
  int buf[4] = {1, 2, 3, 4};
  zero(buf, sizeof buf);
  show("zeroed", buf[0] + buf[3]);
  return 0;
}
