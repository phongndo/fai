/* The sieve of Eratosthenes over a global byte array, prime counting, and twin primes. */
#include "fai_test.h"

#define N 20000
static unsigned char composite[N + 1];

int main(void) {
  for (int i = 2; (long)i * i <= N; i++)
    if (!composite[i])
      for (int j = i * i; j <= N; j += i) composite[j] = 1;
  int count = 0, twins = 0, last = 0;
  long sum = 0;
  for (int i = 2; i <= N; i++) {
    if (composite[i]) continue;
    count++;
    sum += i;
    if (last && i - last == 2) twins++;
    last = i;
  }
  show("primes", count);
  show("sum", sum);
  show("twins", twins);
  show("largest", last);
  return 0;
}
