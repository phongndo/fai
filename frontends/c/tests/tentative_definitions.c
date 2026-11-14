/* Variables declared `extern` (as a header declares them) and then defined in this file by
 * tentative definitions (`int x;`), possibly more than once, used before and after: each is this
 * file's global, not another file's. */
#include "fai_test.h"

extern int counter;
extern struct pair {
  int a, b;
} pair;
extern long table[];

static int bump(void) { return ++counter; }

int counter;
int *pc = &counter;
struct pair pair;
int counter;
long table[3];

int main(void) {
  bump();
  *pc += 4;
  pair.b = counter * 2;
  table[2] = pair.b + 1;
  show("counter", counter);
  show("pair", pair.a + pair.b);
  show("table", table[0] + table[2]);
  return 0;
}
