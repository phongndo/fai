/* Arbitrary-precision unsigned arithmetic in base 10^9 over arrays of unsigned ints: 50!,
 * 2^200, and a Fibonacci number, printed digit group by digit group. */
#include "fai_test.h"

#define LIMBS 40
#define BASE 1000000000u

typedef struct { unsigned limb[LIMBS]; int n; } big;

static void set(big *a, unsigned v) {
  a->n = 1;
  a->limb[0] = v;
}

static void mul_small(big *a, unsigned m) {
  unsigned long carry = 0;
  for (int i = 0; i < a->n; i++) {
    unsigned long cur = (unsigned long)a->limb[i] * m + carry;
    a->limb[i] = (unsigned)(cur % BASE);
    carry = cur / BASE;
  }
  while (carry) {
    a->limb[a->n++] = (unsigned)(carry % BASE);
    carry /= BASE;
  }
}

static void add(big *r, const big *a, const big *b) {
  unsigned carry = 0;
  int n = a->n > b->n ? a->n : b->n;
  for (int i = 0; i < n; i++) {
    unsigned x = i < a->n ? a->limb[i] : 0, y = i < b->n ? b->limb[i] : 0;
    unsigned s = x + y + carry;
    carry = s >= BASE;
    r->limb[i] = carry ? s - BASE : s;
  }
  r->n = n;
  if (carry) r->limb[r->n++] = 1;
}

static void print_big(const char *label, const big *a) {
  print_str(label);
  fai_put_char(' ');
  fai_put_long(a->limb[a->n - 1]);
  for (int i = a->n - 2; i >= 0; i--) {
    unsigned v = a->limb[i];
    char digits[9];
    for (int k = 8; k >= 0; k--) {
      digits[k] = (char)('0' + v % 10);
      v /= 10;
    }
    for (int k = 0; k < 9; k++) fai_put_char(digits[k]);
  }
  fai_put_char('\n');
}

int main(void) {
  big f;
  set(&f, 1);
  for (unsigned i = 2; i <= 50; i++) mul_small(&f, i);
  print_big("50!", &f);
  big p;
  set(&p, 1);
  for (int i = 0; i < 200; i++) mul_small(&p, 2);
  print_big("2^200", &p);
  big a, b, c;
  set(&a, 0);
  set(&b, 1);
  for (int i = 0; i < 300; i++) {
    add(&c, &a, &b);
    a = b;
    b = c;
  }
  print_big("fib(300)", &a);
  return 0;
}
