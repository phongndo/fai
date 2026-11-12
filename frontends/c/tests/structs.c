/* Structs: layout (padding, nesting, arrays of structs), member access through values and
 * pointers, assignment as a copy, and offsetof. */
#include "fai_test.h"
#include <stddef.h>

struct point { int x, y; };
struct rect { struct point min, max; char tag; };
struct mixed { char c; long l; short s; char d; int i; };
typedef struct { struct point pts[3]; int n; } poly;

static int area(const struct rect *r) {
  return (r->max.x - r->min.x) * (r->max.y - r->min.y);
}

static void translate(struct rect *r, int dx, int dy) {
  r->min.x += dx;
  r->max.x += dx;
  r->min.y += dy;
  r->max.y += dy;
}

int main(void) {
  struct rect r = {{1, 2}, {11, 7}, 'r'};
  show("area", area(&r));
  translate(&r, 5, -2);
  show("min.x", r.min.x);
  show("max.y", r.max.y);
  struct rect copy = r;
  copy.min.x = 0;
  show("copy area", area(&copy));
  show("original area", area(&r));
  show("sizeof mixed", sizeof(struct mixed));
  show("offset l", offsetof(struct mixed, l));
  show("offset s", offsetof(struct mixed, s));
  show("offset d", offsetof(struct mixed, d));
  show("offset i", offsetof(struct mixed, i));
  show("sizeof rect", sizeof(struct rect));
  poly p = {{{0, 0}, {4, 0}, {0, 3}}, 3};
  long twice = 0;
  for (int i = 0; i < p.n; i++) {
    struct point a = p.pts[i], b = p.pts[(i + 1) % p.n];
    twice += (long)a.x * b.y - (long)b.x * a.y;
  }
  show("twice area", twice);
  struct mixed m;
  m.c = 'a';
  m.l = -1;
  m.s = 300;
  m.d = 'z';
  m.i = 123456;
  struct mixed m2;
  m2 = m;
  show("m2.l", m2.l);
  show("m2.s", m2.s);
  show("m2.i", m2.i);
  struct point *pp = &p.pts[1];
  pp->y = 9;
  show("through pointer", p.pts[1].y);
  struct point pts[4];
  for (int i = 0; i < 4; i++) pts[i] = (struct point){i, i * i};
  show("pts[3].y", pts[3].y);
  return 0;
}
