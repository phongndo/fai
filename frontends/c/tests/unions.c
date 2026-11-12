/* Unions as memory: members share storage, so writing one and reading another reinterprets
 * the bytes (little-endian); the union is as large and aligned as its largest member. */
#include "fai_test.h"

union word {
  unsigned int u;
  unsigned char bytes[4];
  unsigned short halves[2];
};

union value {
  long l;
  struct { int lo, hi; } parts;
  char c;
};

struct tagged {
  int kind;
  union { long i; const char *s; struct { short a, b; } pair; } as;
};

static long describe(const struct tagged *t) {
  switch (t->kind) {
  case 0: return t->as.i;
  case 1: return t->as.s[0];
  default: return t->as.pair.a * 100 + t->as.pair.b;
  }
}

int main(void) {
  union word w;
  w.u = 0x11223344;
  show("byte 0", w.bytes[0]);
  show("byte 3", w.bytes[3]);
  show("half 1", w.halves[1]);
  w.bytes[1] = 0xff;
  show("u", (long)w.u);
  union value v;
  v.l = -2;
  show("lo", v.parts.lo);
  show("hi", v.parts.hi);
  show("sizeof value", sizeof(union value));
  show("sizeof word", sizeof(union word));
  struct tagged ts[3] = {{0, {.i = 42}}, {1, {.s = "zebra"}}, {2, {.pair = {7, 9}}}};
  for (int i = 0; i < 3; i++) show("describe", describe(&ts[i]));
  union value copy = v;
  show("copy hi", copy.parts.hi);
  return 0;
}
