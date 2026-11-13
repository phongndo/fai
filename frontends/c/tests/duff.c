/* Duff's device: case labels inside a do-while, so the switch jumps into the loop. fcc
 * lowers such a function to basic blocks. */
#include "fai_test.h"

static void copy(int *to, const int *from, int count) {
  int n = (count + 7) / 8;
  switch (count % 8) {
  case 0: do { *to++ = *from++;
  case 7:      *to++ = *from++;
  case 6:      *to++ = *from++;
  case 5:      *to++ = *from++;
  case 4:      *to++ = *from++;
  case 3:      *to++ = *from++;
  case 2:      *to++ = *from++;
  case 1:      *to++ = *from++;
          } while (--n > 0);
  }
}

static int weird(int x) {
  int r = 0;
  switch (x) {
    if (0) {
    case 1:
      r = 10;
    } else {
    case 2:
      r += 20;
    }
    break;
  case 3:
    for (r = 0; r < 3; r++) {
    case 4:
      r += 100;
    }
  }
  return r;
}

int main(void) {
  int src[23], dst[23];
  for (int i = 0; i < 23; i++) { src[i] = i * 7; dst[i] = -1; }
  for (int n = 1; n <= 23; n += 5) {
    copy(dst, src, n);
    long s = 0;
    for (int i = 0; i < 23; i++) s += dst[i];
    show("copied", s);
  }
  for (int x = 0; x <= 4; x++) show("weird", weird(x));
  return 0;
}
