/* Variadic functions defined in C, printed through the helpers (so the interpreter's run is
 * compared too): va_arg of int, unsigned, long, pointers, and double, arguments C promotes
 * (char, short, float, _Bool, enums), more than eight of each class (the rest on the stack),
 * va_copy, a va_list passed to another function (by value: a struct on AArch64) and by
 * pointer, kept in a struct, restarted, and calls through pointers to variadic functions. */
#include "fai_test.h"
#include <stdarg.h>

/* The sum of n ints. */
static int sum_ints(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int s = 0;
  for (int i = 0; i < n; i++) s += va_arg(ap, int);
  va_end(ap);
  return s;
}

/* Arguments described by a string: i int, u unsigned, l long, p pointer to long, d double. */
static double mixed(const char *kinds, ...) {
  va_list ap;
  va_start(ap, kinds);
  double total = 0;
  for (const char *k = kinds; *k; k++) {
    switch (*k) {
    case 'i': total += va_arg(ap, int); break;
    case 'u': total += va_arg(ap, unsigned); break;
    case 'l': total += (double)va_arg(ap, long); break;
    case 'p': total += (double)*va_arg(ap, long *); break;
    case 'd': total += va_arg(ap, double); break;
    }
  }
  va_end(ap);
  return total;
}

/* Promoted arguments, read as the promoted types; the result's bits show each was read whole. */
enum color { RED = 3, GREEN = 5 };
static long promoted(int n, ...) {
  va_list ap;
  va_start(ap, n);
  int c = va_arg(ap, int);       /* char */
  int sc = va_arg(ap, int);      /* signed char */
  int s = va_arg(ap, int);       /* short */
  int us = va_arg(ap, int);      /* unsigned short */
  double f = va_arg(ap, double); /* float */
  int b = va_arg(ap, int);       /* _Bool */
  int e = va_arg(ap, int);       /* enum */
  va_end(ap);
  show("char", c);
  show("signed char", sc);
  show("short", s);
  show("unsigned short", us);
  show_d("float", f);
  show("bool", b);
  show("enum", e);
  return n + c + sc + s + us + b + e;
}

/* Twelve longs and twelve doubles, interleaved: four of each go on the stack. */
static double many(int n, ...) {
  va_list ap;
  va_start(ap, n);
  long li = 0;
  double d = 0;
  for (int i = 0; i < n; i++) {
    li = li * 3 + va_arg(ap, long);
    d = d * 0.5 + va_arg(ap, double);
  }
  va_end(ap);
  show("many longs", li);
  return d;
}

/* A va_list passed by value: the callee reads its own copy. */
static long vsum_longs(int n, va_list ap) {
  long s = 0;
  for (int i = 0; i < n; i++) s += va_arg(ap, long);
  return s;
}

/* Through a pointer: the callee moves the caller's cursor. */
static long next_long(va_list *ap) { return va_arg(*ap, long); }

/* va_copy: count up to the zero, then go back over the arguments to sum them. */
static long count_then_sum(long first, ...) {
  va_list ap, again;
  va_start(ap, first);
  va_copy(again, ap);
  int n = first != 0;
  if (first != 0)
    while (va_arg(ap, long) != 0) n++;
  va_end(ap);
  long s = first + (n > 1 ? vsum_longs(n - 1, again) : 0);
  /* vsum_longs read its own copy: `again` still starts at the second argument. */
  long second = n > 1 ? next_long(&again) : 0;
  long third = n > 2 ? next_long(&again) : 0;
  va_end(again);
  show("count", n);
  show("second", second);
  show("third", third);
  return s;
}

/* A cursor kept in a struct, read by another function. */
struct reader {
  int left;
  va_list ap;
};
static int take(struct reader *r) {
  if (r->left == 0) return -1;
  r->left--;
  return va_arg(r->ap, int);
}
static int max_of(int n, ...) {
  struct reader r;
  r.left = n;
  va_start(r.ap, n);
  int best = take(&r);
  for (int v; (v = take(&r)) != -1;)
    if (v > best) best = v;
  va_end(r.ap);
  return best;
}

/* Reading the arguments twice by starting again. */
static long twice(int n, ...) {
  va_list ap;
  long s = 0;
  for (int round = 1; round <= 2; round++) {
    va_start(ap, n);
    for (int i = 0; i < n; i++) s += round * va_arg(ap, int);
    va_end(ap);
  }
  return s;
}

/* Pointers through the arguments keep pointing at their objects; strings too. */
static void fill(int n, ...) {
  va_list ap;
  va_start(ap, n);
  for (int i = 0; i < n; i++) {
    int *p = va_arg(ap, int *);
    *p = (i + 1) * 100;
  }
  const char *s = va_arg(ap, const char *);
  print_str(s);
  fai_put_char('\n');
  va_end(ap);
}

/* No fixed argument read: only the format's count. A variadic function returning double. */
static double average(int n, ...) {
  va_list ap;
  va_start(ap, n);
  double s = 0;
  for (int i = 0; i < n; i++) s += va_arg(ap, double);
  va_end(ap);
  return n ? s / n : 0;
}

/* Unsigned and signed limits round-trip. */
static void limits(int n, ...) {
  va_list ap;
  va_start(ap, n);
  show("int min", va_arg(ap, int));
  show("unsigned max", va_arg(ap, unsigned));
  show("long min", va_arg(ap, long));
  unsigned long u = va_arg(ap, unsigned long);
  show("ulong max high", (long)(u >> 32));
  show("long long", va_arg(ap, long long));
  show("null", va_arg(ap, void *) == 0);
  va_end(ap);
  (void)n;
}

/* Nested variadic calls in arguments. */
static int add3(int a, ...) {
  va_list ap;
  va_start(ap, a);
  int b = va_arg(ap, int), c = va_arg(ap, int);
  va_end(ap);
  return a + b + c;
}

int main(void) {
  show("sum none", sum_ints(0));
  show("sum 5", sum_ints(5, 1, 2, 3, 4, 5));
  show("sum negative", sum_ints(3, -10, 20, -30));
  long big = 1L << 40;
  show_d("mixed", mixed("iuldpd", -7, 4000000000u, 1L << 50, 0.25, &big, -1.5));
  char c = 'A';
  signed char sc = -5;
  short s = -1234;
  unsigned short us = 65000;
  float f = 0.1f;
  _Bool b = 1;
  enum color e = GREEN;
  show("promoted", promoted(1, c, sc, s, us, f, b, e));
  show_d("many", many(12, 1L, 1.0, 2L, 2.0, 3L, 3.0, 4L, 4.0, 5L, 5.0, 6L, 6.0, 7L, 7.0, 8L, 8.0,
                      9L, 9.0, 10L, 10.0, 11L, 11.0, -12L, 12.0));
  show("count_then_sum", count_then_sum(10L, 20L, 30L, 40L, 0L));
  show("count_then_sum one", count_then_sum(0L));
  show("max_of", max_of(6, 3, 17, -4, 99, 12, 98));
  show("twice", twice(3, 1, 2, 3));
  int x = 0, y = 0, z = 0;
  fill(3, &x, &y, &z, "filled");
  show("x y z", x * 10000 + y + z);
  show_d("average", average(4, 1.5, 2.5, 3.25, -1.0));
  show_d("average none", average(0));
  limits(0, -2147483647 - 1, 4294967295u, -9223372036854775807L - 1, 18446744073709551615UL,
         123456789012345LL, (void *)0);
  show("nested", add3(add3(1, 2, 3), add3(4, 5, 6), sum_ints(2, 7, 8)));
  /* Through pointers to variadic functions. */
  int (*fp)(int, ...) = sum_ints;
  show("through pointer", fp(4, 10, 20, 30, 40));
  double (*fps[])(int, ...) = {many, average};
  show_d("pointer table", fps[1](2, 3.0, 4.0));
  int (*pick)(int, ...) = x > 0 ? max_of : add3;
  show("picked", pick(3, 5, 9, 2));
  return 0;
}
