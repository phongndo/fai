/* More values live at once than there are registers, across calls and loops: the register
 * allocator spills, and keeps values in callee-saved registers across calls. */
#include "fai_test.h"

static long noise(long x) { return (x * 2654435761L) % 1000003; }

/* Sixteen accumulators updated together in a loop with a call in it (unsigned, so that their
 * overflow wraps). */
static unsigned long accumulate(int n) {
  unsigned long a = 1, b = 2, c = 3, d = 4, e = 5, f = 6, g = 7, h = 8;
  unsigned long i = 9, j = 10, k = 11, l = 12, m = 13, o = 14, p = 15, q = 16;
  for (int t = 0; t < n; t++) {
    unsigned long z = (unsigned long)noise(t);
    a += z ^ b;
    b += a >> 3;
    c ^= b + z;
    d -= c * 3;
    e += d & 0xffff;
    f |= e >> 7;
    g += f % 97;
    h ^= g << 2;
    i += h / 7;
    j -= i ^ 5;
    k += j * j % 1009;
    l ^= k;
    m += l >> 1;
    o -= m & 255;
    p += o ^ a;
    q ^= p + t;
  }
  return a + b + c + d + e + f + g + h + i + j + k + l + m + o + p + q;
}

/* Calls in the arguments of calls, with values live across all of them. */
static long f3(long x, long y, long z) { return x * 100 + y * 10 + z; }
static long nested(long a, long b) {
  long c = a * b, d = a - b, e = a + b;
  long r = f3(f3(a, noise(b), c), f3(d, e, noise(a)), f3(noise(c), noise(d), noise(e)));
  return r + a + b + c + d + e;
}

/* A deep expression of unsigned and signed values. */
static unsigned long mash(unsigned long x, long y) {
  return ((x * 31 + (unsigned long)y) ^ (x >> 7)) + ((x << 3) | (unsigned long)(y >> 2)) -
         (x % 1000) * ((unsigned long)y % 77 + 1) + (unsigned long)(y / 3) +
         ((x ^ (unsigned long)y) & 0xfff0) + (unsigned long)(y < 0) + (x > 1000 ? x / 1000 : x);
}

int main(void) {
  show("accumulate", (long)(accumulate(1000) % 1000000007));
  for (long a = -3; a <= 3; a += 2) show("nested", nested(a, 7 - a));
  unsigned long acc = 0;
  for (long y = -500; y <= 500; y += 125) acc = acc * 7 + mash(acc + 12345, y);
  show("mash", (long)(acc % 1000000007));
  return 0;
}
