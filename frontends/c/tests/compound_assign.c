/* Compound assignment on every operator and on narrow types, where the computation is done in
 * the promoted type and the result converted back. */
#include "fai_test.h"

int main(void) {
  int x = 100;
  x += 5;
  x -= 3;
  x *= 7;
  x /= 3;
  x %= 50;
  x <<= 4;
  x >>= 2;
  x &= 0x3f;
  x |= 0x100;
  x ^= 0x55;
  show("int", x);
  unsigned char c = 200;
  c += 100; /* 300 wraps to 44 */
  show("uchar +=", c);
  c *= 3;
  show("uchar *=", c);
  c <<= 3;
  show("uchar <<=", c);
  signed char s = 100;
  s -= 300;
  show("schar -=", s);
  short h = 1000;
  h *= 100;
  show("short *=", h);
  unsigned u = 10;
  u -= 20;
  show("unsigned -=", (long)u);
  long l = 1;
  l <<= 40;
  show("long <<=", l);
  int arr[4] = {1, 2, 3, 4};
  int i = 0;
  arr[i++] += 10;
  arr[i++] *= 10;
  show("arr0", arr[0]);
  show("arr1", arr[1]);
  show("i", i);
  _Bool b = 0;
  b += 2;
  show("bool +=", b);
  int sh = 3;
  long w = 5;
  w <<= sh;
  show("long <<= int", w);
  return 0;
}
