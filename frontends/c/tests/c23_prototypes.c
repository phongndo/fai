/* C23: an empty parameter list means no parameters, so () declarations are prototypes, and
 * calls through them are checked and work as with (void). */
#include "fai_test.h"

int counter();
static int value();

int counter() {
  static int n;
  return ++n;
}

static int value() { return 42; }

struct ops {
  int (*get)();
};

int main(void) {
  counter();
  show("counter", counter());
  show("value", value());
  struct ops o = {value};
  show("ops", o.get());
  int (*fns[2])() = {counter, value};
  show("fns", fns[0]() + fns[1]());
  return 0;
}
