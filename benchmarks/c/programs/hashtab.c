// Open-addressing hash table of 64-bit keys (linear probing): multiply-shift hashing, unsigned
// arithmetic, struct arrays, unpredictable branches.
#include <stdio.h>
#include <stdlib.h>

struct slot {
  unsigned long key;
  long value;
};

#define BITS 17
#define CAP (1ul << BITS)

static unsigned long hash(unsigned long k) {
  return (k * 0x9E3779B97F4A7C15ul) >> (64 - BITS);
}

static void put(struct slot *t, unsigned long key, long value) {
  unsigned long i = hash(key);
  while (t[i].key != 0 && t[i].key != key)
    i = (i + 1) & (CAP - 1);
  t[i].key = key;
  t[i].value += value;
}

static long get(const struct slot *t, unsigned long key) {
  unsigned long i = hash(key);
  while (t[i].key != 0) {
    if (t[i].key == key)
      return t[i].value;
    i = (i + 1) & (CAP - 1);
  }
  return -1;
}

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  struct slot *t = malloc(sizeof(struct slot) * CAP);
  long total = 0;
  for (int r = 0; r < reps; r++) {
    for (unsigned long i = 0; i < CAP; i++) {
      t[i].key = 0;
      t[i].value = 0;
    }
    unsigned long s = 88172645463325252ul + (unsigned long)r;
    for (int i = 0; i < 80000; i++) {
      s ^= s << 13;
      s ^= s >> 7;
      s ^= s << 17;
      put(t, (s & 0xFFFFF) + 1, i);
    }
    for (unsigned long k = 1; k <= 200000; k++)
      total += get(t, k);
  }
  printf("hashtab %ld\n", total);
  free(t);
  return 0;
}
