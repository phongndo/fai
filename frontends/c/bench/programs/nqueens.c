// N-queens solutions by recursive backtracking over bitmasks: recursion, bit operations.
#include <stdio.h>
#include <stdlib.h>

static long solve(unsigned cols, unsigned diag1, unsigned diag2, unsigned all) {
  if (cols == all)
    return 1;
  long count = 0;
  unsigned avail = all & ~(cols | diag1 | diag2);
  while (avail) {
    unsigned bit = avail & -avail;
    avail ^= bit;
    count += solve(cols | bit, (diag1 | bit) << 1 & all, (diag2 | bit) >> 1, all);
  }
  return count;
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 8;
  printf("nqueens %d %ld\n", n, solve(0, 0, 0, (1u << n) - 1));
  return 0;
}
