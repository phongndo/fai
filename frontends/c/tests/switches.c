/* switch: fall-through, default first or in the middle or absent, nested switches, break and
 * continue inside loops, GNU case ranges, and returns from cases. */
#include "fai_test.h"

static int classify(char c) {
  switch (c) {
  case 'a': case 'e': case 'i': case 'o': case 'u':
    return 1;
  case ' ':
  case '\n':
    return 2;
  default:
    if (c >= '0' && c <= '9') return 3;
    return 0;
  }
}

static int fall(int x) {
  int r = 0;
  switch (x) {
  default:
    r += 1000;
  case 1:
    r += 1;
  case 2:
    r += 2;
    break;
  case 3:
    r += 3;
  case 4: {
    int t = r * 2;
    r = t + 4;
  }
  }
  return r;
}

static long nested(int a, int b) {
  switch (a) {
  case 0:
    switch (b) {
    case 0: return 0;
    case 1: break;
    default: return -1;
    }
    return 1;
  case 1:
    return 10 + b;
  }
  return 99;
}

int main(void) {
  const char *text = "hi you 42\n";
  long counts = 0;
  for (const char *p = text; *p; p++) counts = counts * 4 + classify(*p);
  show("classify", counts);
  for (int x = 0; x <= 5; x++) show("fall", fall(x));
  show("nested 0 0", nested(0, 0));
  show("nested 0 1", nested(0, 1));
  show("nested 0 2", nested(0, 2));
  show("nested 1 5", nested(1, 5));
  show("nested 2 0", nested(2, 0));
  int odd = 0, even = 0, skipped = 0;
  for (int i = 0; i < 20; i++) {
    switch (i % 4) {
    case 0:
      even++;
      continue;
    case 1:
    case 3:
      odd++;
      break;
    case 2:
      if (i > 10) { skipped++; continue; }
      even++;
    }
    if (i == 17) break;
  }
  show("odd", odd);
  show("even", even);
  show("skipped", skipped);
  long big = 0;
  for (long v = -3; v < 6; v++) {
    switch (v) {
    case -3: big += 1; break;
    case 5000000000L: big += 1000; break;
    case 2: big += 10;
    }
  }
  show("long switch", big);
  unsigned char u = 200;
  switch (u) {
  case 200: show("uchar 200", 1); break;
  default: show("uchar default", 1);
  }
  int ranges = 0;
  for (int i = 0; i < 30; i++) {
    switch (i) {
    case 1 ... 5: ranges += 1; break;
    case 10 ... 12: ranges += 100; break;
    }
  }
  show("case ranges", ranges);
  switch (3) { }
  switch (u) default: show("only default", u);
  return 0;
}
