/* C23: parameters may be unnamed in a function definition; and () declares no parameters,
 * as (void) does. */
#include "fai_test.h"

static int second(int, int b) { return b; }
static int ignore_all(int, long, char *) { return 7; }
static int no_params() { return 11; }

typedef int (*binop)(int, int);

int main(void) {
  show("second", second(1, 2));
  show("ignore", ignore_all(1, 2, "x"));
  show("no params", no_params());
  binop f = second;
  show("via ptr", f(5, 6));
  int (*g)() = no_params;
  show("g", g());
  return 0;
}
