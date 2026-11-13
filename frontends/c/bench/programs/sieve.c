// Sieve of Eratosthenes over 2^20 bytes, repeated: byte stores, nested loops, an array scan.
#include <stdio.h>
#include <stdlib.h>

#define N (1 << 20)
static unsigned char flags[N];

static int sieve(void) {
  for (int i = 0; i < N; i++)
    flags[i] = 1;
  flags[0] = flags[1] = 0;
  for (int i = 2; (long)i * i < N; i++)
    if (flags[i])
      for (int j = i * i; j < N; j += i)
        flags[j] = 0;
  int count = 0;
  for (int i = 0; i < N; i++)
    count += flags[i];
  return count;
}

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  long total = 0;
  for (int r = 0; r < reps; r++)
    total += sieve();
  printf("sieve %ld\n", total);
  return 0;
}
