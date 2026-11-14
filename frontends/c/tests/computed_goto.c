/* GNU C's labels as values: a bytecode interpreter dispatching through a static const table of
 * label addresses (as Lua's and CPython's do), label addresses in variables, compared, and a
 * computed goto in a loop; a writable static table, one object across calls; and a table whose
 * declaration a jump skips. */
#include "fai_test.h"

enum { INC, DBL, NEG, JNZ, END };

static long run(const unsigned char *code, long acc) {
  static const void *const ops[] = {&&op_inc, &&op_dbl, &&op_neg, &&op_jnz, &&op_end};
  long count = 3;
  const unsigned char *pc = code;
#define NEXT goto *ops[*pc++]
  NEXT;
op_inc:
  acc++;
  NEXT;
op_dbl:
  acc *= 2;
  NEXT;
op_neg:
  acc = -acc;
  NEXT;
op_jnz:
  if (--count > 0) {
    pc = code;
    NEXT;
  }
  NEXT;
op_end:
  return acc;
#undef NEXT
}

static int pick(int k) {
  void *where = k ? &&yes : &&no;
  int same = where == &&yes;
  goto *where;
yes:
  return 10 + same;
no:
  return 20 + same;
}

static int swap(int k) {
  static void *t[] = {&&a, &&b};
  if (k == 2) {
    void *x = t[0];
    t[0] = t[1];
    t[1] = x;
    return 0;
  }
  goto *t[k];
a:
  return 10;
b:
  return 20;
}

static const void *const *saved;
static int same(int n) {
  static const void *const t[] = {&&out};
  if (!n) {
    saved = t;
    return same(1);
  }
  return saved == t;
out:
  return 0;
}

static int skipped(void) {
  goto start;
  static void *const t[] = {&&bad, &&ok};
start:
  goto *t[1];
bad:
  return 99;
ok:
  return 7;
}

int main(void) {
  unsigned char prog[] = {INC, DBL, INC, NEG, JNZ, END};
  show("run", run(prog, 1));
  show("pick 1", pick(1));
  show("pick 0", pick(0));
  long s = 0;
  for (int i = 0; i < 5; i++) s = s * 3 + run(prog + (i % 3), i);
  show("loop", s);
  int before = swap(0);
  swap(2);
  show("swap", before * 100 + swap(0));
  show("same", same(0));
  show("skipped", skipped());
  return 0;
}
