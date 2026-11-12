/* Aggregate expressions: struct-valued ?: and comma, chained struct assignment, assignment
 * through pointers into arrays of structs, pointers to arrays, large zeroed locals, and
 * sizeof of expressions that aren't evaluated. */
#include "fai_test.h"

struct v3 { long x, y, z; };
struct box { struct v3 lo, hi; char name[8]; };

static long dot(const struct v3 *a, const struct v3 *b) {
  return a->x * b->x + a->y * b->y + a->z * b->z;
}

static struct box boxes[3] = {{{0, 0, 0}, {1, 1, 1}, "unit"}, {{-1, -2, -3}, {4, 5, 6}, "big"}};

int main(void) {
  struct v3 a = {1, 2, 3}, b = {4, 5, 6}, c;
  c = (dot(&a, &b) > 10 ? a : b);
  show("ternary struct", c.x);
  c = (a.x++, b);
  show("comma struct", c.z);
  struct v3 d, e;
  d = e = a;
  show("chained", d.x + e.y);
  boxes[2] = boxes[1];
  boxes[2].name[0] = 'B';
  print_str(boxes[2].name);
  fai_put_char(' ');
  print_str(boxes[1].name);
  fai_put_char('\n');
  struct box *bp = &boxes[0];
  bp[1].hi = bp[0].hi;
  show("assigned member", boxes[1].hi.z);
  int arr[3][4];
  int (*row)[4] = arr;
  for (int i = 0; i < 12; i++) arr[i / 4][i % 4] = i;
  row++;
  show("pointer to array", (*row)[2]);
  show("row stride", (char *)(row + 1) - (char *)row);
  int (*whole)[3][4] = &arr;
  show("whole", (*whole)[2][3]);
  long big[512] = {[511] = 9};
  long s = 0;
  for (int i = 0; i < 512; i++) s += big[i];
  show("big zeroed", s);
  int n = 5;
  show("sizeof unevaluated", sizeof(n++));
  show("n", n);
  struct v3 zero = {0};
  show("zero", zero.x + zero.y + zero.z);
  const struct v3 *pick = n > 3 ? &a : &b;
  show("pick", pick->x);
  struct box local = boxes[1];
  local.lo.y += 10;
  show("local copy", local.lo.y);
  show("global unchanged", boxes[1].lo.y);
  return 0;
}
