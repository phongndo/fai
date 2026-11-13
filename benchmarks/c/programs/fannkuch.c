// Pancake flips over every permutation of n elements (generated in place, Heap-style counters):
// small int arrays, data-dependent loops and branches.
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 8;
  int perm[16], work[16], count[16];
  for (int i = 0; i < n; i++)
    perm[i] = i;
  long checksum = 0;
  int maxflips = 0, sign = 1;
  for (int i = 0; i < n; i++)
    count[i] = i;
  for (;;) {
    for (int i = 0; i < n; i++)
      work[i] = perm[i];
    int flips = 0;
    for (int k = work[0]; k != 0; k = work[0]) {
      for (int lo = 0, hi = k; lo < hi; lo++, hi--) {
        int t = work[lo];
        work[lo] = work[hi];
        work[hi] = t;
      }
      flips++;
    }
    if (flips > maxflips)
      maxflips = flips;
    checksum += sign * flips;
    sign = -sign;
    // Next permutation: rotate the first i+1 elements while counters wrap.
    int i = 1;
    for (; i < n; i++) {
      int first = perm[0];
      for (int j = 0; j < i; j++)
        perm[j] = perm[j + 1];
      perm[i] = first;
      if (--count[i] >= 0)
        break;
      count[i] = i;
    }
    if (i >= n)
      break;
  }
  printf("fannkuch %ld %d\n", checksum, maxflips);
  return 0;
}
