/* GNU C's atomic builtins (__atomic_*) and fences, on 8- to 64-bit integers and pointers: loads,
 * stores, exchanges, compare-exchanges that succeed and fail, fetch-op and op-fetch forms, and the
 * generic forms that take values through pointers. Each is a call of one of fcc's atomic
 * functions. */
#include "fai_test.h"

static unsigned char c8 = 250;
static short s16 = -5;
static int i32 = 7;
static long i64 = 1L << 40;
static int *ptr;

int main(void) {
  show("load8", __atomic_load_n(&c8, __ATOMIC_RELAXED));
  show("fetch_add8", __atomic_fetch_add(&c8, 10, __ATOMIC_SEQ_CST));
  show("c8", c8);
  show("add_fetch16", __atomic_add_fetch(&s16, -10, __ATOMIC_SEQ_CST));
  show("fetch_sub16", __atomic_fetch_sub(&s16, 100, __ATOMIC_ACQ_REL));
  show("s16", s16);
  show("xchg32", __atomic_exchange_n(&i32, 42, __ATOMIC_SEQ_CST));
  show("fetch_and32", __atomic_fetch_and(&i32, 0x22, __ATOMIC_RELAXED));
  show("or_fetch32", __atomic_or_fetch(&i32, 0x100, __ATOMIC_RELAXED));
  show("fetch_xor32", __atomic_fetch_xor(&i32, -1, __ATOMIC_RELAXED));
  show("nand_fetch32", __atomic_nand_fetch(&i32, 0xff, __ATOMIC_RELAXED));
  show("i32", i32);
  long e = 5;
  show("cas fail", __atomic_compare_exchange_n(&i64, &e, 9, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST));
  show("expected now", e >> 32);
  show("cas ok", __atomic_compare_exchange_n(&i64, &e, -9, 1, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED));
  show("i64", i64);
  unsigned char ec = 1;
  show("cas8 fail", __atomic_compare_exchange_n(&c8, &ec, 2, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST));
  show("ec", ec);
  int x = 3;
  __atomic_store_n(&ptr, &x, __ATOMIC_RELEASE);
  show("via ptr", *__atomic_load_n(&ptr, __ATOMIC_ACQUIRE));
  int *old = __atomic_exchange_n(&ptr, (int *)0, __ATOMIC_SEQ_CST);
  show("old ptr", old == &x);
  show("ptr null", ptr == 0);
  long v = 77, got;
  __atomic_store(&i64, &v, __ATOMIC_SEQ_CST);
  __atomic_load(&i64, &got, __ATOMIC_SEQ_CST);
  show("generic", got);
  long nv = 88, ov;
  __atomic_exchange(&i64, &nv, &ov, __ATOMIC_SEQ_CST);
  show("generic xchg", ov * 100 + i64);
  /* The operands, side effects included, come before the operation. */
  int y = 0;
  __atomic_store_n(&y, 1, (y = 2, __ATOMIC_SEQ_CST));
  show("order operand first", y);
  __atomic_thread_fence(__ATOMIC_SEQ_CST);
  __sync_synchronize();
  return 0;
}
