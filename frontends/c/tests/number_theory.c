/* 64-bit number theory: gcd and lcm, modular exponentiation and inverses, Miller-Rabin with
 * fixed bases (products kept below 2^64), and Euler's totient. */
#include "fai_test.h"

typedef unsigned long long u64;

static u64 gcd(u64 a, u64 b) {
  while (b) {
    u64 t = a % b;
    a = b;
    b = t;
  }
  return a;
}

static u64 mulmod(u64 a, u64 b, u64 m) {
  u64 r = 0;
  a %= m;
  while (b) {
    if (b & 1) r = (r + a) % m;
    a = (a << 1) % m;
    b >>= 1;
  }
  return r;
}

static u64 powmod(u64 b, u64 e, u64 m) {
  u64 r = 1 % m;
  b %= m;
  for (; e; e >>= 1) {
    if (e & 1) r = mulmod(r, b, m);
    b = mulmod(b, b, m);
  }
  return r;
}

static int is_prime(u64 n) {
  if (n < 2) return 0;
  u64 small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
  for (int i = 0; i < 12; i++)
    if (n % small[i] == 0) return n == small[i];
  u64 d = n - 1;
  int s = 0;
  while (!(d & 1)) { d >>= 1; s++; }
  for (int i = 0; i < 12; i++) {
    u64 x = powmod(small[i], d, n);
    if (x == 1 || x == n - 1) continue;
    int composite = 1;
    for (int r = 1; r < s; r++) {
      x = mulmod(x, x, n);
      if (x == n - 1) { composite = 0; break; }
    }
    if (composite) return 0;
  }
  return 1;
}

static long long inverse(long long a, long long m) {
  long long g = m, x = 0, x1 = 1, a1 = a;
  while (a1) {
    long long q = g / a1, t = g - q * a1;
    g = a1;
    a1 = t;
    t = x - q * x1;
    x = x1;
    x1 = t;
  }
  return g == 1 ? (x % m + m) % m : -1;
}

static u64 totient(u64 n) {
  u64 r = n;
  for (u64 p = 2; p * p <= n; p++)
    if (n % p == 0) {
      while (n % p == 0) n /= p;
      r -= r / p;
    }
  if (n > 1) r -= r / n;
  return r;
}

int main(void) {
  show("gcd", (long)gcd(1071, 462));
  show("lcm", (long)(12 / gcd(12, 18) * 18));
  show("2^64-1 mod 97", (long)(~0ull % 97));
  show("powmod", (long)powmod(3, 1000000, 1000000007));
  show("big powmod", (long)powmod(123456789, 987654321, 18446744073709551557ull));
  u64 tests[] = {1, 2, 97, 561, 7919, 1000000007, 4294967291ull, 4294967297ull,
                 18446744073709551557ull};
  for (int i = 0; i < 9; i++) show("prime", is_prime(tests[i]));
  show("inverse", inverse(17, 3120));
  show("no inverse", inverse(6, 9));
  show("totient", (long)totient(1000000));
  return 0;
}
