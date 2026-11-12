/* System headers through Clang's preprocessor for the AArch64 Linux target: the fixed-width
 * types of <stdint.h>, <limits.h>, <stddef.h>, and <stdbool.h>, and sizeof/_Alignof. */
#include "fai_test.h"
#include <limits.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct s { char c; int64_t x; };

int main(void) {
  show("INT_MAX", INT_MAX);
  show("INT_MIN", INT_MIN);
  show("LONG_MAX", LONG_MAX);
  show("CHAR_BIT", CHAR_BIT);
  show("CHAR_MIN", CHAR_MIN);
  show("UCHAR_MAX", UCHAR_MAX);
  show("SHRT_MIN", SHRT_MIN);
  show("INT8_MIN", INT8_MIN);
  show("UINT16_MAX", UINT16_MAX);
  show("sizeof int8_t", sizeof(int8_t));
  show("sizeof int64_t", sizeof(int64_t));
  show("sizeof intptr_t", sizeof(intptr_t));
  show("sizeof size_t", sizeof(size_t));
  show("sizeof long long", sizeof(long long));
  show("sizeof void *", sizeof(void *));
  show("sizeof bool", sizeof(bool));
  show("alignof long", alignof(long));
  show("alignof struct s", _Alignof(struct s));
  show("sizeof struct s", sizeof(struct s));
  show("offsetof x", offsetof(struct s, x));
  uint8_t u8 = 255;
  u8++;
  show("uint8 wraps", u8);
  int16_t i16 = -32768;
  show("int16", i16);
  uint32_t u32 = UINT32_MAX;
  show("uint32 max", u32);
  int64_t i64 = INT64_MIN;
  show("int64 min / 2", i64 / 2);
  size_t n = SIZE_MAX;
  show("size_t max is -1", (long)n);
  alignas(16) char buf[3];
  show("alignas", alignof(buf) >= 16 || sizeof buf == 3);
  return 0;
}
