/* Structs and unions by value across separately compiled code: calls to C functions the
 * reference compiler compiled (extern/struct_extern.c) with one of each AAPCS64 class, directly,
 * through pointers, through `...`, and with enough arguments to reach the stack; functions here
 * that code calls back (directly and through pointers, and a variadic one); and libc's `div`,
 * `ldiv`, and `lldiv`, which return `div_t` (x0) and `ldiv_t`/`lldiv_t` (x0, x1). */
#include "extern/struct_extern.h"
#include "fai_test.h"
#include <stdarg.h>
#include <stdlib.h>

struct pair fai_pair(struct pair x) {
  show("fai pair.a", x.a);
  print_str(x.s);
  fai_put_char('\n');
  return (struct pair){x.a * 3, x.s + 2};
}

struct big fai_big(struct big x) {
  show_d("fai big.d", x.d);
  x.v[6] += 100; /* this copy only */
  x.d *= 8;
  return x;
}

struct hfa4d fai_hfa4d(struct hfa4d x, struct small s) {
  show_d("fai hfa4d.b", x.b);
  show("fai small", s.c + s.s + s.i);
  return (struct hfa4d){{x.c, x.b}, x.a[1], x.a[0] + s.s};
}

long fai_va(const char *tags, ...) {
  va_list ap;
  va_start(ap, tags);
  unsigned long acc = 0; /* wraps: no overflow */
  for (const char *t = tags; *t; t++) {
    acc *= 3;
    switch (*t) {
    case 'h': {
      struct hfa3 h = va_arg(ap, struct hfa3);
      acc += (long)(h.a * 2 + h.b + h.c);
      break;
    }
    case 's': {
      struct small s = va_arg(ap, struct small);
      acc += s.c * 2 + s.s + s.i;
      break;
    }
    case 'p': {
      struct pair p = va_arg(ap, struct pair);
      acc += p.a * 2 + p.s[0];
      break;
    }
    case 'b': {
      struct big b = va_arg(ap, struct big);
      acc += b.v[0] * 2 + b.v[6] + (long)b.d;
      break;
    }
    case 'f': {
      struct flags f = va_arg(ap, struct flags);
      acc += f.on * 2 + f.mode + f.lvl + f.id;
      break;
    }
    case 'n':
      acc += va_arg(ap, union num).l * 2;
      break;
    case 'i':
      acc += va_arg(ap, int) * 2;
      break;
    case 'e':
      va_arg(ap, struct empty);
      break;
    }
  }
  va_end(ap);
  show("fai va", (long)acc);
  return (long)acc;
}

int main(void) {
  struct hfa3 h = ext_hfa3((struct hfa3){1.5f, 2.5f, -3.5f}, 2.0f);
  show_f("hfa3", h.a + h.b * 10 + h.c * 100);
  struct hfa4d d = ext_hfa4d((struct hfa4d){{0.5, 1.5}, 2.5, 3.5});
  show_d("hfa4d.b", d.b);
  struct small s = ext_small(7, (struct small){'a', -300, 70000});
  show("small", s.c * 1000000L + s.s * 1000L + s.i);
  struct pair p = ext_pair((struct pair){6, "left "}, (struct pair){7, "right"});
  show("pair.a", p.a);
  print_str(p.s);
  fai_put_char('\n');
  struct al16 a = ext_al16(1, (struct al16){12, 34});
  show("al16", a.a * 100 + a.b);
  struct big b = {{1, -2, 3, -4, 5, -6, 7}, 1.25};
  struct big b2 = ext_big(b, 3);
  show("big kept", b.v[6]);
  show("big ret", b2.v[6]);
  show_d("big ret d", b2.d);
  struct flags f = ext_flags((struct flags){1, 6, -5, 4321});
  show("flags", f.on * 1000 + f.mode * 100 + f.lvl * 10);
  show("flags.id", f.id);
  union num n;
  n.l = 0x1122334455667788;
  n = ext_num(n, 0);
  show("num", n.l);
  n.d = 2.75;
  n = ext_num(n, 1);
  show_d("num.d", n.d);

  struct hfa3 hs[4] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}, {10, 11, 12}};
  struct pair ps[4] = {{1, "a"}, {2, "b"}, {3, "c"}, {4, "d"}};
  struct small ss[3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
  show_d("many", ext_many(hs[0], hs[1], hs[2], ss[0], ps[0], ps[1], ps[2], ss[1], b, hs[3],
                          ss[2], ps[3]));
  double (*mp)(struct hfa3, struct hfa3, struct hfa3, struct small, struct pair, struct pair,
               struct pair, struct small, struct big, struct hfa3, struct small, struct pair) =
      ext_many;
  show_d("many pointer", mp(hs[3], hs[2], hs[1], ss[2], ps[3], ps[2], ps[1], ss[0], b2, hs[0],
                            ss[1], ps[0]));
  /* Through `...`: past the eight x and v registers onto the stack too. */
  struct empty none = ext_empty(4, (struct empty){}, 2);
  show("va", ext_va("hdspbfnihhhhheppppp", hs[0], d, s, p, b, f, n, 5, hs[1], hs[2], hs[3], hs[0],
                    hs[1], none, ps[0], ps[1], ps[2], ps[3], ps[0]));
  struct hfa3 (*hp)(struct hfa3, float) = ext_hfa3;
  show_f("pointer hfa3", hp(hs[1], 0.5f).c);
  show("callbacks", ext_callbacks(fai_pair, fai_big));
  show("fai_va here", fai_va("pi", ps[3], 21));

  div_t q = div(-17, 5);
  show("div quot", q.quot);
  show("div rem", q.rem);
  ldiv_t lq = ldiv(1234567890123L, -1000L);
  show("ldiv quot", lq.quot);
  show("ldiv rem", lq.rem);
  show("lldiv rem", lldiv(-99LL, 7LL).rem);
  show("div().quot", div(100, 7).quot + ldiv(9, 2).rem);
  return 0;
}
