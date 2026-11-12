/* Enums (constants, explicit values, as switch cases and array indices) and typedefs of
 * scalars, pointers, arrays, structs, and function types. */
#include "fai_test.h"

enum color { RED, GREEN = 5, BLUE, ALPHA = -1 };
typedef enum { NORTH, EAST, SOUTH, WEST } dir;
typedef unsigned long u64;
typedef int vec3[3];
typedef struct pair { int a, b; } pair;
typedef int binop(int, int);
typedef binop *binop_ptr;

static int plus(int a, int b) { return a + b; }

static const char *name(enum color c) {
  switch (c) {
  case RED: return "red";
  case GREEN: return "green";
  case BLUE: return "blue";
  default: return "other";
  }
}

static dir turn(dir d) { return (dir)((d + 1) % 4); }

int main(void) {
  show("RED", RED);
  show("GREEN", GREEN);
  show("BLUE", BLUE);
  show("ALPHA", ALPHA);
  enum color cs[] = {BLUE, RED, ALPHA, GREEN};
  for (int i = 0; i < 4; i++) {
    print_str(name(cs[i]));
    fai_put_char('\n');
  }
  dir d = WEST;
  d = turn(d);
  show("turned", d);
  u64 big = (u64)1 << 63;
  show("u64 top bit set", big != 0);
  vec3 v = {1, 2, 3};
  show("vec3 sum", v[0] + v[1] + v[2]);
  pair p = {3, 4};
  binop_ptr f = plus;
  show("binop", f(p.a, p.b));
  int counts[WEST + 1] = {0};
  counts[SOUTH] = 7;
  show("counts[SOUTH]", counts[2]);
  show("sizeof enum", sizeof(enum color));
  return 0;
}
