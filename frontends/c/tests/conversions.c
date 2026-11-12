/* Integer conversions: truncation, sign and zero extension, plain char (unsigned on AArch64
 * Linux), and explicit casts between every width. */
#include "fai_test.h"

int main(void) {
  long l = 0x123456789abcdefL;
  show("to int", (int)l);
  show("to short", (short)l);
  show("to signed char", (signed char)l);
  show("to unsigned char", (unsigned char)l);
  show("to unsigned short", (unsigned short)l);
  signed char sc = -5;
  unsigned char uc = 251;
  char c = (char)200;
  show("sc to long", sc);
  show("uc to long", uc);
  show("plain char 200", c);
  show("plain char is unsigned", (char)-1 > 0);
  show("sc to unsigned", (long)(unsigned)sc);
  show("short -1 to unsigned short to int", (int)(unsigned short)(short)-1);
  int i = -1;
  unsigned long ul = i;
  show("int -1 to unsigned long, low", (long)(ul & 0xffff));
  show("int -1 to unsigned long == max", ul == 18446744073709551615ul);
  long back = (int)4294967295u;
  show("unsigned max to int", back);
  long long ll = -1;
  show("long long to unsigned int", (unsigned)ll);
  _Bool bs[] = {0, 1, 2, -1, 256};
  long sum = 0;
  for (int k = 0; k < 5; k++) sum = sum * 10 + bs[k];
  show("bool conversions", sum);
  show("bool of null", (_Bool)(char *)0);
  int arr[3];
  show("bool of pointer", (_Bool)arr);
  return 0;
}
