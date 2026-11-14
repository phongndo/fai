/* C23: constexpr arrays, structs, and unions, read at run time and in constant expressions. */
#include "fai_test.h"

struct rgb {
  unsigned char r, g, b;
};

constexpr struct rgb palette[3] = {{255, 0, 0}, {0, 255, 0}, {10, 20, 30}};
constexpr int primes[] = {2, 3, 5, 7, 11, 13};
constexpr unsigned NPRIMES = sizeof primes / sizeof primes[0];
constexpr char greeting[] = "hello";

static int lookup(unsigned i) { return primes[i % NPRIMES]; }

int main(void) {
  static_assert(NPRIMES == 6);
  long s = 0;
  for (unsigned i = 0; i < 3; i++) s += palette[i].r + palette[i].g * 2 + palette[i].b * 3;
  show("palette", s);
  show("lookup 8", lookup(8));
  show("greeting", greeting[1]);
  print_str(greeting);
  fai_put_char('\n');
  constexpr struct rgb local = {1, 2, 3};
  show("local", local.r + local.g + local.b);
  constexpr double scale[] = {0.5, 0.25};
  show("scale", (long)(scale[0] * 8 + scale[1] * 8));
  return 0;
}
