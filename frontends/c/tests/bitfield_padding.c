/* Bitfields whose bytes FIR's layout would leave as implicit padding (the struct's tail, or the
 * gap before an aligned member), in global, static, local, and nested initializers; and a
 * compound literal that is a function's first stack slot (FIR id 0). */
#include "fai_test.h"

struct tail_u {
  int x;
  char y;
  unsigned z : 1;
};

struct tail_s {
  int x;
  char y;
  signed z : 3;
};

struct middle {
  char a;
  unsigned b : 4;
  short c;
};

struct wide_tail {
  long x;
  char y;
  unsigned z : 12;
  unsigned w : 7;
};

struct outer {
  struct tail_u in;
  struct middle mid[2];
  int after;
};

struct tail_u gu = {1, 2, 1};
struct tail_s gs = {3, 4, -3};
struct middle gm = {5, 9, 300};
struct wide_tail gw = {6, 7, 0xabc, 0x55};
struct outer go = {{8, 9, 1}, {{10, 11, 12}, {13, 14, 15}}, 16};
union with_tail {
  struct tail_s s;
  long l;
};
union with_tail gun = {.s = {17, 18, 3}};

static int first_slot(int *p) {
  return *p;
}

static int literal_first(void) {
  return first_slot((int[1]){7});
}

static int struct_literal_first(void) {
  return ((struct tail_s){19, 20, -1}).z;
}

static int static_local(void) {
  static struct tail_u s = {21, 22, 1};
  int r = s.z;
  s.z = 0;
  return r;
}

int main(void) {
  show("gu.z", gu.z);
  show("gs.z", gs.z);
  show("gm.b", gm.b);
  show("gm.c", gm.c);
  show("gw.z", gw.z);
  show("gw.w", gw.w);
  show("go.in.z", go.in.z);
  show("go.mid[0].b", go.mid[0].b);
  show("go.mid[1].b", go.mid[1].b);
  show("go.after", go.after);
  show("gun.s.z", gun.s.z);
  show("literal", literal_first());
  show("struct literal", struct_literal_first());
  show("static local", static_local());
  show("static local again", static_local());

  struct tail_u lu = {23, 24, 1};
  struct tail_s ls = {25, 26, -4};
  struct wide_tail lw = {27, 28, 0xfff, 0x7f};
  show("lu.z", lu.z);
  show("ls.z", ls.z);
  show("lw.z", lw.z);
  show("lw.w", lw.w);
  struct tail_u copy = gu;
  copy.y = 99;
  show("copy.z", copy.z);
  gu = lu;
  gu.z ^= 1;
  show("gu.z flipped", gu.z);
  show("lu.z kept", lu.z);
  ls.z += 1;
  show("ls.z incremented", ls.z);
  struct outer lo = go;
  lo.mid[1].b = 3;
  show("lo.in.z", lo.in.z);
  show("lo.mid[1].b", lo.mid[1].b);
  show("lo.mid[1].c", lo.mid[1].c);
  return gu.z + (gs.z != -3) + (int)sizeof(struct tail_u) - 8;
}
