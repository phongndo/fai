/* C23: bool, true, and false are keywords (no <stdbool.h>), true and false have type bool,
 * and they work in the preprocessor. */
#include "fai_test.h"

static bool flip(bool b) { return !b; }

#if true
#define PP_TRUE 1
#else
#define PP_TRUE 0
#endif

int main(void) {
  bool t = true, f = false;
  show("true", t);
  show("false", f);
  show("flip", flip(f));
  show("sizeof true", sizeof true);
  show("generic", _Generic(true, bool: 1, int: 2, default: 3));
  show("pp true", PP_TRUE);
  bool b = 7;
  show("7 as bool", b);
  bool arr[3] = {true, false, 5};
  int n = 0;
  for (int i = 0; i < 3; i++) n += arr[i];
  show("count", n);
  show("true + true", true + true);
  return 0;
}
