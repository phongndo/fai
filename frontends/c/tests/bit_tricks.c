/* Bit manipulation: population count, leading and trailing zeros by loops, reversal, rotates,
 * parity, power-of-two tests, and sign extension of bit slices by shifts. */
#include "fai_test.h"
#include <stdint.h>

static int popcount(uint64_t x) {
  x = x - ((x >> 1) & 0x5555555555555555ull);
  x = (x & 0x3333333333333333ull) + ((x >> 2) & 0x3333333333333333ull);
  x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0full;
  return (int)((x * 0x0101010101010101ull) >> 56);
}
static int clz(uint32_t x) {
  if (!x) return 32;
  int n = 0;
  while (!(x & 0x80000000u)) { x <<= 1; n++; }
  return n;
}
static int ctz(uint64_t x) {
  if (!x) return 64;
  int n = 0;
  while (!(x & 1)) { x >>= 1; n++; }
  return n;
}
static uint32_t reverse(uint32_t x) {
  x = ((x >> 1) & 0x55555555u) | ((x & 0x55555555u) << 1);
  x = ((x >> 2) & 0x33333333u) | ((x & 0x33333333u) << 2);
  x = ((x >> 4) & 0x0f0f0f0fu) | ((x & 0x0f0f0f0fu) << 4);
  x = ((x >> 8) & 0x00ff00ffu) | ((x & 0x00ff00ffu) << 8);
  return (x >> 16) | (x << 16);
}
static uint32_t rotl(uint32_t x, unsigned r) { return (x << (r & 31)) | (x >> ((32 - r) & 31)); }
static int32_t sext(uint32_t x, int bits) {
  int shift = 32 - bits;
  return (int32_t)(x << shift) >> shift;
}

int main(void) {
  show("popcount", popcount(0xdeadbeefcafebabeull));
  show("clz", clz(0x00012345));
  show("ctz", ctz(0x1000000000ull));
  show("reverse", reverse(0x12345678u));
  show("rotl", rotl(0x80000001u, 4));
  show("rotl 0", rotl(0xabcdef01u, 0));
  show("parity", popcount(0x7) & 1);
  int pow2 = 0;
  for (unsigned v = 1; v < 5000; v++) pow2 += (v & (v - 1)) == 0;
  show("powers of two", pow2);
  show("sext 5 bits", sext(0x1d, 5));
  show("sext 12 bits", sext(0x7ff, 12));
  uint16_t h = 0xabcd;
  show("swap bytes", (uint16_t)(h << 8 | h >> 8));
  int64_t neg = -1;
  show("arithmetic shift", neg >> 63);
  show("logical shift", (long)((uint64_t)neg >> 60));
  show("mask low", (long)(0xffffffffffffffffull >> (64 - 12)));
  return 0;
}
