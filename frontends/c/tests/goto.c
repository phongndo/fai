/* goto: forward and backward jumps, cleanup chains, loops written with labels, jumps out of
 * nested loops, and a jump into the middle of a loop body. */
#include "fai_test.h"

static int find(int grid[4][4], int want, int *row, int *col) {
  for (int i = 0; i < 4; i++)
    for (int j = 0; j < 4; j++)
      if (grid[i][j] == want) {
        *row = i;
        *col = j;
        goto found;
      }
  return 0;
found:
  return 1;
}

static int steps(int stage) {
  int log = 0;
  if (stage < 1) goto fail0;
  log = log * 10 + 1;
  if (stage < 2) goto fail1;
  log = log * 10 + 2;
  if (stage < 3) goto fail2;
  log = log * 10 + 3;
  return log;
fail2:
  log = log * 10 + 7;
fail1:
  log = log * 10 + 8;
fail0:
  log = log * 10 + 9;
  return -log;
}

static long collatz(long n) {
  long count = 0;
top:
  if (n == 1) goto done;
  count++;
  if (n % 2) goto odd;
  n /= 2;
  goto top;
odd:
  n = 3 * n + 1;
  goto top;
done:
  return count;
}

static int into_loop(int n) {
  int s = 0, i = 0;
  goto middle;
  for (; i < n; i++) {
    s += 100;
  middle:
    s += i;
  }
  return s;
}

int main(void) {
  int grid[4][4];
  for (int i = 0; i < 16; i++) grid[i / 4][i % 4] = i * 3;
  int r = -1, c = -1;
  show("found", find(grid, 27, &r, &c));
  show("row", r);
  show("col", c);
  show("not found", find(grid, 28, &r, &c));
  for (int s = 0; s <= 3; s++) show("steps", steps(s));
  show("collatz 27", collatz(27));
  show("into loop", into_loop(4));
  int k = 0;
again:
  k++;
  if (k < 10) goto again;
  show("k", k);
  return 0;
}
