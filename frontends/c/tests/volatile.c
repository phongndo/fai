/* volatile objects: locals, globals, struct members, pointers to volatile, and volatile
 * pointers, read and written by assignment, compound assignment, and ++/--. Each access is a
 * call of one of fcc's access functions, so it happens, once, where the program says. */
#include "fai_test.h"

struct regs {
  volatile unsigned char ctrl;
  volatile short status;
  volatile int count;
  volatile long total;
  int plain;
};

static volatile int ticks;
static int *volatile cursor;

static void bump(volatile int *p, int n) {
  for (int i = 0; i < n; i++) (*p)++;
}

int main(void) {
  volatile int flag = 1;
  flag += 2;
  flag++;
  show("flag", flag);
  bump(&ticks, 5);
  ticks *= 3;
  show("ticks", ticks);
  struct regs r = {0};
  r.ctrl = 0x1ff; /* converted to unsigned char */
  r.status = -2;
  r.count = r.ctrl + r.status;
  r.total = (long)r.count << 33;
  r.plain = 4;
  show("ctrl", r.ctrl);
  show("status", r.status);
  show("count", r.count);
  show("total>>32", r.total >> 32);
  volatile struct regs *vr = &r;
  vr->plain += 1;
  show("plain", r.plain);
  int arr[3] = {10, 20, 30};
  cursor = arr;
  cursor++;
  show("cursor", *cursor);
  /* An initializer and a checked result are volatile writes too. */
  volatile int init = 7;
  show("init", init);
  volatile long checked;
  show("checked over", __builtin_mul_overflow(1L << 40, 1L << 30, &checked));
  show("checked", checked == 0);
  /* Stores that look dead still happen; the last one is what is read. */
  volatile int sink = 0;
  for (int i = 0; i < 10; i++) sink = i;
  show("sink", sink);
#ifndef FAI_TEST_INTEGERS_ONLY
  volatile double d = 1.5;
  d *= 2;
  volatile float f = 0.25f;
  f += 1;
  show_d("d", d);
  show_f("f", f);
#endif
  return flag;
}
