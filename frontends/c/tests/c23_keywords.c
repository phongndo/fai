/* C23's new keyword spellings: alignas, alignof, and the width macros in <limits.h> and
 * <stdint.h>. */
#include "fai_test.h"
#include <limits.h>
#include <stdint.h>

struct aligned {
  char c;
  alignas(16) int i;
};

static alignas(8) char buf[3];

int main(void) {
  show("alignof long", alignof(long));
  show("alignof aligned", alignof(struct aligned));
  show("sizeof aligned", sizeof(struct aligned));
  show("buf aligned", ((unsigned long)(void *)buf & 7) == 0);
  show("bool width", BOOL_WIDTH);
  show("char width", CHAR_WIDTH);
  show("int width", INT_WIDTH);
  show("long width", LONG_WIDTH);
  show("ullong width", ULLONG_WIDTH);
  show("int32 width", INT32_WIDTH);
  show("uintptr width", UINTPTR_WIDTH);
  show("bitint maxwidth", BITINT_MAXWIDTH >= 64);
  return 0;
}
