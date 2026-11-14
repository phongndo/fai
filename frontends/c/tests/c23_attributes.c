/* C23: standard attributes, [[...]], and __has_c_attribute. */
#include "fai_test.h"

[[nodiscard]] static int compute(int x) { return x * 3; }
[[deprecated("use compute")]] static int old_compute(int x) { return x * 2; }
[[maybe_unused]] static int unused_helper(void) { return 0; }
[[unsequenced]] static int square(int x) { return x * x; }
[[reproducible]] static int cube(int x) { return x * x * x; }

[[noreturn]] static void spin(void) {
  for (;;) {
  }
}

struct [[maybe_unused]] tagged {
  [[maybe_unused]] int field;
};

static int fall(int v) {
  int r = 0;
  switch (v) {
  case 0:
    r += 1;
    [[fallthrough]];
  case 1:
    r += 10;
    [[fallthrough]];
  case 2:
    r += 100;
    break;
  default:
    r = -1;
  }
  return r;
}

int main(void) {
  [[maybe_unused]] int x = 5;
  show("compute", compute(4));
  show("old", old_compute(4));
  show("square", square(7));
  show("cube", cube(3));
  show("fall 0", fall(0));
  show("fall 1", fall(1));
  show("fall 2", fall(2));
  show("fall 3", fall(3));
  show("has nodiscard", __has_c_attribute(nodiscard) > 0);
  show("has fallthrough", __has_c_attribute(fallthrough) > 0);
  show("has nonsense", __has_c_attribute(nonsense));
  struct tagged t = {9};
  show("field", t.field);
  (void)spin;
  return 0;
}
