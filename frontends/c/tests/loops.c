/* while, do-while, and for loops with break and continue, nested, with empty parts, and with
 * declarations in their headers. */
#include "fai_test.h"

int main(void) {
  int i = 0, s = 0;
  while (i < 10) {
    i++;
    if (i % 3 == 0) continue;
    if (i == 8) break;
    s += i;
  }
  show("while", s);
  s = 0;
  i = 0;
  do {
    s += i;
    if (i == 2) { i += 2; continue; }
    i++;
  } while (i < 7);
  show("do-while", s);
  i = 100;
  do i--; while (0);
  show("do once", i);
  long prod = 1;
  for (int k = 1; k <= 10; k++) {
    if (k % 2) continue;
    prod *= k;
  }
  show("for even product", prod);
  int found = -1;
  for (int a = 1; a < 20 && found < 0; a++)
    for (int b = a; b < 20; b++) {
      if (b > 15) break;
      if (a * a + b * b == 13 * 13) { found = a * 100 + b; break; }
    }
  show("pythagorean", found);
  int n = 0;
  for (;;) {
    if (++n >= 5) break;
  }
  show("forever", n);
  int count = 0;
  for (int x = 0, y = 10; x < y; x++, y--) count++;
  show("two variables", count);
  int bits = 0;
  for (unsigned v = 0xf0f0; v; v &= v - 1) bits++;
  show("popcount", bits);
  int nested = 0;
  for (int a = 0; a < 4; a++) {
    int b = 0;
    while (1) {
      if (b > a) break;
      do {
        nested++;
        if (nested % 5 == 0) break;
      } while (0);
      b++;
      continue;
    }
  }
  show("nested", nested);
  return 0;
}
