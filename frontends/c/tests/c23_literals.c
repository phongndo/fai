/* C23: binary literals, digit separators, and u8 character literals. */
#include "fai_test.h"

int main(void) {
  show("0b101", 0b101);
  show("0B1111", 0B1111);
  show("0b ull", (long)(0b1ull << 40 >> 30));
  show("million", 1'000'000);
  show("hex sep", 0xFF'FF);
  show("bin sep", 0b1010'1010);
  show("oct sep", 07'7);
  unsigned long long big = 18'446'744'073'709'551'615ull;
  show("big>>60", (long)(big >> 60));
  show("u8 char", u8'a');
  show("u8 generic", _Generic(u8'a', unsigned char: 1, char: 2, int: 3, default: 4));
  const unsigned char *s = u8"hé";
  int n = 0;
  while (s[n]) n++;
  show("u8 len", n);
  show("u8 byte1", s[1]);
  show("u8 str generic", _Generic(u8"x", unsigned char *: 1, char *: 2, default: 3));
  double d = 1'000.5;
  show("double sep", (long)(d * 2));
  return 0;
}
