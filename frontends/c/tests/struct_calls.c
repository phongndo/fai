/* Struct values in expressions and calls: results used as `f().x` and `f().a[i]`, passed on as
 * `g(f())`, chained, assigned, chosen by `?:` and `,`, returned from recursion and loops, through
 * function pointers (in arrays and structs), as variadic arguments of every class (enough to
 * reach the stack), and read back by `va_arg`, also after `va_copy` and in a callee taking a
 * `va_list`; empty structs through `...` are nothing. Struct returns from functions with `goto`
 * and `switch` too. */
#include "fai_test.h"
#include <stdarg.h>

struct pt { int x, y; };
struct seg { struct pt a, b; };
struct box { long v[4]; };
struct hf { float a, b, c; };
struct hd { double a, b; };
struct sm { char tag; short n; };
struct bits { unsigned lo : 4, hi : 4; signed char s : 6; };
union nu { long l; double d; };
struct none {};

static struct pt pt(int x, int y) {
  struct pt p = {x, y};
  return p;
}
static struct pt add(struct pt a, struct pt b) { return pt(a.x + b.x, a.y + b.y); }
static struct pt neg(struct pt a) { return pt(-a.x, -a.y); }
static struct seg seg(struct pt a, struct pt b) { return (struct seg){a, b}; }
static struct box box(long k) {
  struct box b;
  for (int i = 0; i < 4; i++) b.v[i] = k * (i + 1);
  return b;
}
static long box_sum(struct box b) { return b.v[0] + b.v[1] + b.v[2] + b.v[3]; }
static struct box box_rev(struct box b) {
  struct box r;
  for (int i = 0; i < 4; i++) r.v[i] = b.v[3 - i];
  return r;
}

/* Recursion: the nth Fibonacci pair (F(n), F(n+1)) as a struct. */
static struct pt fib(int n) {
  if (n == 0) return pt(0, 1);
  struct pt p = fib(n - 1);
  return pt(p.y, p.x + p.y);
}

/* A function that falls off its end on one path (whose value is never used). */
static struct pt maybe(int ok) {
  if (ok) return pt(1, 2);
}

/* Basic blocks: a function with `goto` returns structs from its blocks, and falls off its end. */
static struct pt walk(int n, int stop) {
  struct pt p = {0, 0};
  int i = 0;
again:
  if (i == stop) return p;
  p = add(p, pt(i, 1));
  if (++i < n) goto again;
  if (n < 0) goto done;
  return neg(p);
done:;
}
static struct seg pick(int k, const struct seg *segs) {
  switch (k) {
  case 0: return segs[0];
  case 1:
  case 2: return *segs;
  default: return seg(pt(k, k), segs[1].b);
  }
}
static long total(const struct box b) { return b.v[0] - b.v[3]; }

typedef struct pt (*binop)(struct pt, struct pt);
static struct pt sub(struct pt a, struct pt b) { return add(a, neg(b)); }
static struct pt mul(struct pt a, struct pt b) { return pt(a.x * b.x, a.y * b.y); }
struct ops { binop f[3]; const char *names; };

static struct hd apply_hd(struct hd (*f)(struct hd), struct hd x) { return f(f(x)); }
static struct hd swap_hd(struct hd x) { return (struct hd){x.b * 2, x.a}; }

/* Variadic: the count, then structs of the kinds the tags say. */
static void show_args(const char *tags, ...) {
  va_list ap;
  va_start(ap, tags);
  for (const char *t = tags; *t; t++) {
    switch (*t) {
    case 'p': {
      struct pt p = va_arg(ap, struct pt);
      show("pt", p.x * 1000 + p.y);
      break;
    }
    case 'b':
      show("box", box_sum(va_arg(ap, struct box)));
      break;
    case 'f': {
      struct hf h = va_arg(ap, struct hf);
      show_f("hf", h.a + h.b * 10 + h.c * 100);
      break;
    }
    case 'd':
      show_d("hd", va_arg(ap, struct hd).b);
      break;
    case 's': {
      struct sm s = va_arg(ap, struct sm);
      show("sm", s.tag * 1000 + s.n);
      break;
    }
    case 'u':
      show("nu", va_arg(ap, union nu).l);
      break;
    case 'i':
      show("int", va_arg(ap, int));
      break;
    case 'g':
      show_d("double", va_arg(ap, double));
      break;
    case 'n':
      va_arg(ap, struct none);
      print_str("none\n");
      break;
    }
  }
  va_end(ap);
}

/* A va_list carried to another function, and copied: the copy reads the same structs again. */
static long sum_pts_v(int n, va_list ap) {
  long s = 0;
  for (int i = 0; i < n; i++) {
    struct pt p = va_arg(ap, struct pt);
    s += p.x * 10 + p.y;
  }
  return s;
}
static long sum_pts_twice(int n, ...) {
  va_list ap, again;
  va_start(ap, n);
  va_copy(again, ap);
  long s = sum_pts_v(n, ap);
  s += sum_pts_v(n, again) * 1000;
  va_end(again);
  va_end(ap);
  return s;
}

static struct bits bits(unsigned lo, unsigned hi, int s) {
  struct bits b = {lo, hi, s};
  return b;
}

int main(void) {
  show("f().x", pt(3, 4).x);
  show("f().y", add(pt(1, 2), pt(10, 20)).y);
  show("chain", add(add(pt(1, 1), pt(2, 2)), neg(add(pt(5, 0), pt(0, 7)))).x);
  show("nested", seg(pt(1, 2), add(pt(3, 4), pt(5, 6))).b.y);
  show("box[2]", box(7).v[2]);
  show("g(f())", box_sum(box_rev(box(3))));
  struct pt p = pt(0, 0);
  for (int i = 0; i < 5; i++) p = add(p, pt(i, i * i)); /* the temporary each iteration */
  show("loop x", p.x);
  show("loop y", p.y);
  struct pt q = p.x > 5 ? pt(1, 1) : neg(p);
  show("?: a", q.x);
  q = p.x < 5 ? pt(1, 1) : neg(p);
  show("?: b", q.y);
  show("?: member", (p.y > 0 ? fib(10) : fib(11)).x);
  q = (p = pt(9, 8), neg(p));
  show("comma", q.x * 100 + q.y);
  struct pt r, s;
  r = s = fib(20);
  show("fib 20", r.x);
  show("fib 21", s.y);
  show("maybe", maybe(1).y);
  maybe(0);
  struct ops o = {{add, sub, mul}, "+-*"};
  for (int i = 0; i < 3; i++) {
    struct pt v = o.f[i](pt(6, 7), pt(2, 3));
    fai_put_char(o.names[i]);
    fai_put_char(' ');
    print_long(v.x * 100 + v.y);
  }
  binop f = sub;
  show("pointer", f(f(pt(10, 10), pt(1, 2)), pt(1, 1)).y);
  struct hd h = apply_hd(swap_hd, (struct hd){1.5, 2.5});
  show_d("apply a", h.a);
  show_d("apply b", h.b);
  struct bits bt = bits(9, 6, -20);
  show("bits", bt.lo * 100 + bt.hi * 10);
  show("bits s", bits(1, 2, -31).s);

  union nu u;
  u.l = -123456789;
  show_args("pbfdsu", pt(1, 2), box(1), (struct hf){1, 2, 3}, (struct hd){0, 0.125},
            (struct sm){'a', 7}, u);
  /* Eight 8-byte structs fill x1-x7 and then the stack; HFAs fill v0-v7 and then the stack. */
  show_args("ppppppppppiibd", pt(1, 1), pt(2, 2), pt(3, 3), pt(4, 4), pt(5, 5), pt(6, 6),
            pt(7, 7), pt(8, 8), pt(9, 9), pt(10, 10), 11, 12, box(2), (struct hd){1, 2});
  show_args("ffgffdgd", (struct hf){1, 1, 1}, (struct hf){2, 2, 2}, 0.5, (struct hf){3, 3, 3},
            (struct hf){4, 4, 4}, (struct hd){5, 5}, 6.0, (struct hd){7, 7});
  show("va_copy", sum_pts_twice(3, pt(1, 2), pt(3, 4), pt(5, 6)));
  struct none z;
  show_args("ninp", z, 5, (struct none){}, pt(6, 7));
  show("walk", walk(5, 9).x);
  show("walk stop", walk(5, 2).y);
  struct seg segs[2] = {seg(pt(1, 2), pt(3, 4)), seg(pt(5, 6), pt(7, 8))};
  for (int k = 0; k < 4; k++) show("pick", pick(k, segs).a.x * 10 + pick(k, segs).b.y);
  show("const param", total(box(5)));
  return 0;
}
