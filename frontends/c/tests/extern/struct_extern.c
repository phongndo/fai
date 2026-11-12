/* The C functions struct_extern.c calls and that call it, compiled by the reference compiler:
 * each prints what it received and returns a struct built from it. */
#include "struct_extern.h"
#include "fai_test.h"
#include <stdarg.h>

struct hfa3 ext_hfa3(struct hfa3 x, float k) {
  show_f("ext hfa3.a", x.a);
  show_f("ext hfa3.c", x.c);
  return (struct hfa3){x.c * k, x.b * k, x.a * k};
}

struct hfa4d ext_hfa4d(struct hfa4d x) {
  show_d("ext hfa4d.a1", x.a[1]);
  show_d("ext hfa4d.c", x.c);
  x.b += x.a[0];
  return x;
}

struct small ext_small(int pad, struct small x) {
  show("ext small pad", pad);
  show("ext small", x.c * 1000000L + x.s * 1000L + x.i);
  return (struct small){(char)(x.c + 1), (short)(x.s * 2), x.i - 1};
}

struct pair ext_pair(struct pair x, struct pair y) {
  show("ext pair.a", x.a + y.a);
  print_str(x.s);
  print_str(y.s);
  fai_put_char('\n');
  return (struct pair){x.a * y.a, y.s + 1};
}

struct al16 ext_al16(int pad, struct al16 x) {
  show("ext al16 pad", pad);
  show("ext al16", x.a * 10 + x.b);
  return (struct al16){x.b, (int)x.a};
}

struct big ext_big(struct big x, long k) {
  long s = 0;
  for (int i = 0; i < 7; i++) s += x.v[i];
  show("ext big sum", s);
  show_d("ext big.d", x.d);
  for (int i = 0; i < 7; i++) x.v[i] *= (int)k; /* this copy only */
  x.d = -x.d;
  return x;
}

struct flags ext_flags(struct flags x) {
  show("ext flags", x.on * 1000 + x.mode * 100 + x.lvl * 10);
  show("ext flags.id", x.id);
  x.on ^= 1;
  x.mode = (x.mode + 3) & 7;
  x.lvl = (signed char)-x.lvl;
  return x;
}

union num ext_num(union num x, int which) {
  if (which == 0) show("ext num.l", x.l);
  else show_d("ext num.d", x.d);
  x.c[7] ^= 0x40;
  return x;
}

struct empty ext_empty(int a, struct empty e, int b) {
  show("ext empty", a * 10 + b);
  return e;
}

double ext_many(struct hfa3 a, struct hfa3 b, struct hfa3 c, struct small d, struct pair e,
                struct pair f, struct pair g, struct small h, struct big i, struct hfa3 j,
                struct small k, struct pair l) {
  return a.a + b.b * 2 + c.c * 3 + d.i * 4 + e.a * 5 + f.a * 6 + g.a * 7 + h.s * 8 + i.d * 9 +
         j.c * 10 + k.c * 11 + l.a * 12;
}

static long va_body(const char *tags, va_list ap) {
  unsigned long acc = 0; /* wraps: no overflow */
  for (const char *t = tags; *t; t++) {
    acc *= 3;
    switch (*t) {
    case 'h': {
      struct hfa3 h = va_arg(ap, struct hfa3);
      acc += (long)(h.a + h.b + h.c);
      break;
    }
    case 'd': {
      struct hfa4d d = va_arg(ap, struct hfa4d);
      acc += (long)(d.a[0] + d.a[1] + d.b + d.c);
      break;
    }
    case 's': {
      struct small s = va_arg(ap, struct small);
      acc += s.c + s.s + s.i;
      break;
    }
    case 'p': {
      struct pair p = va_arg(ap, struct pair);
      acc += p.a + p.s[0];
      break;
    }
    case 'b': {
      struct big b = va_arg(ap, struct big);
      acc += b.v[0] + b.v[6] + (long)b.d;
      break;
    }
    case 'f': {
      struct flags f = va_arg(ap, struct flags);
      acc += f.on + f.mode + f.lvl + f.id;
      break;
    }
    case 'n':
      acc += va_arg(ap, union num).l;
      break;
    case 'i':
      acc += va_arg(ap, int);
      break;
    case 'e':
      va_arg(ap, struct empty);
      break;
    }
  }
  return (long)acc;
}

long ext_va(const char *tags, ...) {
  va_list ap;
  va_start(ap, tags);
  long r = va_body(tags, ap);
  va_end(ap);
  return r;
}

long ext_callbacks(struct pair (*f)(struct pair), struct big (*g)(struct big)) {
  struct pair p = fai_pair((struct pair){5, "direct"});
  struct pair q = f((struct pair){6, "pointer"});
  struct big b = {{1, 2, 3, 4, 5, 6, 7}, 0.5};
  struct big r = fai_big(b), s = g(b);
  struct hfa4d h = fai_hfa4d((struct hfa4d){{1, 2}, 3, 4}, (struct small){'x', 9, -9});
  long v = fai_va("hspbfneei", (struct hfa3){1, 2, 3}, (struct small){1, 2, 3},
                  (struct pair){4, "A"}, b, (struct flags){1, 5, -3, 77}, (union num){.l = -5}, (struct empty){},
                  (struct empty){}, 8);
  show("ext saw p", p.a);
  print_str(p.s);
  fai_put_char('\n');
  show("ext saw q", q.a);
  show("ext saw r", r.v[6] + b.v[6]);
  show_d("ext saw s.d", s.d);
  show_d("ext saw h.c", h.c);
  return p.a + q.a + r.v[0] + s.v[1] + v;
}
