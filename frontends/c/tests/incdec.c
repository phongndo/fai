/* Pre and post increment and decrement on integers, narrow integers, and pointers. */
#include "fai_test.h"

int main(void) {
  int i = 5;
  show("i++", i++);
  show("i", i);
  show("++i", ++i);
  show("i--", i--);
  show("--i", --i);
  unsigned char c = 255;
  c++;
  show("uchar 255++", c);
  c--;
  show("uchar 0--", c);
  signed char s = 127;
  s++; /* converted back: wraps */
  show("schar 127++", s);
  int arr[5] = {10, 20, 30, 40, 50};
  int *p = arr;
  show("*p++", *p++);
  show("*p", *p);
  show("*++p", *++p);
  show("(*p)++", (*p)++);
  show("arr[2]", arr[2]);
  p--;
  show("*p after p--", *p);
  int *q = &arr[4];
  show("q - p", q - p);
  long n = 0;
  for (int k = 0; k < 10; k++) n += k++;
  show("loop k++", n);
  return 0;
}
