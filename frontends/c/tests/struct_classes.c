/* Structs and unions passed and returned by value, one of each AAPCS64 class: HFAs of one to four
 * floats and doubles (through members, arrays, nested structs, and unions), small composites of
 * up to 8 and 16 bytes with padding, 16-byte aligned ones (an even register pair), composites
 * over 16 bytes (by reference, the callee's copy its own), pointers, bitfields, unions, empty
 * structs (a GNU extension: no bytes, and no argument), and enough arguments that each class
 * spills to the stack. Every field is printed where it
 * arrives, and each function returns a struct built from its arguments. */
#include "fai_test.h"

struct f1 { float a; };
struct f2 { float a, b; };
struct f3 { float a[3]; };
struct f4 { float a; struct { float b, c; } in; float d; };
struct d1 { double a; };
struct d2 { double a; double b; };
struct d3 { double a; double b[2]; };
struct d4 { struct d2 lo, hi; };
/* An HFA through a union, and despite an `aligned` attribute on the struct (GCC's argument
 * alignment is its fields'), and despite a zero-width bitfield. */
union uf3 { float x; float v[3]; };
struct __attribute__((aligned(8))) f2a { float a, b; };
struct fz { float a; int : 0; float b; };

struct c1 { char c; };
struct c3 { char a, b, c; };
struct i8b { int a; short s; char c; };      /* 8 bytes, one byte of padding */
struct pad12 { char c; int i; short s; };    /* 12 bytes, padding inside and at the end */
struct mix16 { char c; double d; };          /* 16 bytes: not an HFA */
struct fi { float f; int i; };               /* floats and integers: x registers */
struct al16 { _Alignas(16) long a; };        /* 16-byte aligned: an even register pair */
struct __attribute__((aligned(16))) sal { long a; }; /* 16-byte aligned in memory only */
struct ptrs { const char *s; long *p; };
struct arr { short v[5]; };
struct bits { unsigned a : 3; int b : 9; unsigned c : 20; char d; };
struct big { long a, b, c; };                /* 24 bytes: by reference */
struct huge { int v[20]; struct d2 tail; };
union ui { int i; float f; char c[6]; };
struct empty {};
struct eh { struct empty e; float a, b; }; /* still an HFA */
struct fam { int n; short tail[]; };      /* passed without its flexible member */
struct z0 { float a, b; float none[0]; };  /* not an HFA (GCC's rule): x0 */
union uh { long l[3]; double d; };

static void pf(const char *l, float x) { show_f(l, x); }
static void pd(const char *l, double x) { show_d(l, x); }

static struct f1 g_f1(struct f1 x) { pf("f1.a", x.a); x.a *= 2; return x; }
static struct f2 g_f2(struct f2 x) { pf("f2.a", x.a); pf("f2.b", x.b); return (struct f2){x.b, x.a}; }
static struct f3 g_f3(struct f3 x) {
  for (int i = 0; i < 3; i++) pf("f3", x.a[i]);
  x.a[0] += x.a[2];
  return x;
}
static struct f4 g_f4(struct f4 x) {
  pf("f4.a", x.a);
  pf("f4.b", x.in.b);
  pf("f4.c", x.in.c);
  pf("f4.d", x.d);
  struct f4 r = {x.d, {x.in.c, x.in.b}, x.a};
  return r;
}
static struct d1 g_d1(struct d1 x) { pd("d1.a", x.a); x.a = -x.a; return x; }
static struct d2 g_d2(struct d2 x) { pd("d2.a", x.a); pd("d2.b", x.b); x.b /= 3; return x; }
static struct d3 g_d3(struct d3 x) {
  pd("d3.a", x.a);
  pd("d3.b0", x.b[0]);
  pd("d3.b1", x.b[1]);
  x.b[1] = x.a + x.b[0];
  return x;
}
static struct d4 g_d4(struct d4 x) {
  pd("d4.lo.a", x.lo.a);
  pd("d4.hi.b", x.hi.b);
  struct d4 r = {x.hi, x.lo};
  return r;
}
static union uf3 g_uf3(union uf3 x) { pf("uf3.v2", x.v[2]); x.v[1] = 0.25f; return x; }
static struct f2a g_f2a(struct f2a x) { pf("f2a.b", x.b); x.a = 1.5f; return x; }
static struct fz g_fz(struct fz x) { pf("fz.a", x.a); pf("fz.b", x.b); return x; }

static struct c1 g_c1(struct c1 x) { show("c1", x.c); x.c++; return x; }
static struct c3 g_c3(struct c3 x) {
  show("c3", x.a * 10000 + x.b * 100 + x.c);
  return (struct c3){x.c, x.b, x.a};
}
static struct i8b g_i8b(struct i8b x) {
  show("i8b.a", x.a);
  show("i8b.s", x.s);
  show("i8b.c", x.c);
  x.a = -x.a;
  return x;
}
static struct pad12 g_pad12(struct pad12 x) {
  show("pad12.c", x.c);
  show("pad12.i", x.i);
  show("pad12.s", x.s);
  x.s = (short)(x.s + x.i);
  return x;
}
static struct mix16 g_mix16(struct mix16 x) {
  show("mix16.c", x.c);
  pd("mix16.d", x.d);
  x.d *= 4;
  return x;
}
static struct fi g_fi(struct fi x) { pf("fi.f", x.f); show("fi.i", x.i); x.i += 1; return x; }
static struct al16 g_al16(int pad, struct al16 x, int after) {
  show("al16 pad", pad);
  show("al16.a", x.a);
  show("al16 after", after);
  x.a += after;
  return x;
}
static struct sal g_sal(int pad, struct sal x, int after) {
  show("sal pad", pad);
  show("sal.a", x.a);
  show("sal after", after);
  x.a -= after;
  return x;
}
static struct ptrs g_ptrs(struct ptrs x) {
  print_str(x.s);
  fai_put_char('\n');
  show("*p", *x.p);
  *x.p += 1;
  x.s++;
  return x;
}
static struct arr g_arr(struct arr x) {
  long s = 0;
  for (int i = 0; i < 5; i++) s = s * 10 + x.v[i];
  show("arr", s);
  x.v[4] = -1;
  return x;
}
static struct bits g_bits(struct bits x) {
  show("bits.a", x.a);
  show("bits.b", x.b);
  show("bits.c", x.c);
  show("bits.d", x.d);
  x.b = -x.b;
  x.c ^= 0xfffff;
  return x;
}
static struct big g_big(struct big x) {
  show("big.a", x.a);
  show("big.c", x.c);
  x.b = x.a + x.c; /* the callee's copy */
  return x;
}
static struct huge g_huge(struct huge x) {
  long s = 0;
  for (int i = 0; i < 20; i++) s += x.v[i] * (i + 1);
  show("huge sum", s);
  pd("huge.tail.b", x.tail.b);
  for (int i = 0; i < 20; i++) x.v[i] = -x.v[i];
  return x;
}
static union ui g_ui(union ui x) { show("ui.i", x.i); x.c[5] = 'z'; return x; }
static union uh g_uh(union uh x) { show("uh.l2", x.l[2]); x.l[0] = 77; return x; }
static struct empty g_empty(int a, struct empty e, int b) {
  show("empty a", a);
  show("empty b", b);
  return e;
}
static struct eh g_eh(struct eh x) { pf("eh.b", x.b); x.a += x.b; return x; }
static struct fam g_fam(struct fam x) { show("fam.n", x.n); x.n *= 3; return x; }
static struct z0 g_z0(double pad, struct z0 x) {
  show_d("z0 pad", pad);
  pf("z0.b", x.b);
  return (struct z0){x.b, x.a};
}

/* More arguments than registers: nine HFAs of two doubles (only four fit d0-d7), nine 16-byte
 * structs (four fit x0-x7), interleaved with scalars that then go to the stack too. */
static double many_d2(struct d2 a, struct d2 b, struct d2 c, struct d2 d, double e, struct d2 f,
                      struct d2 g, struct d2 h, struct d2 i, struct d2 j) {
  return a.a + b.b * 2 + c.a * 3 + d.b * 4 + e * 5 + f.a * 6 + g.b * 7 + h.a * 8 + i.b * 9 +
         j.a * 10;
}
static long many_mix(struct mix16 a, int b, struct mix16 c, struct al16 d, struct mix16 e, int f,
                     struct big g, struct mix16 h, struct al16 i, struct pad12 j, struct c3 k,
                     long l) {
  return a.c + b * 2 + c.c * 3 + d.a * 4 + e.c * 5 + f * 6 + g.c * 7 + h.c * 8 + i.a * 9 +
         j.i * 10 + k.b * 11 + l * 12 + (long)(a.d + c.d + e.d + h.d);
}
static float many_f(struct f3 a, struct f3 b, struct f4 c, struct f1 d, float e, struct f2 f,
                    struct f1 g) {
  return a.a[0] + b.a[1] * 2 + c.d * 3 + d.a * 4 + e * 5 + f.b * 6 + g.a * 7;
}

int main(void) {
  struct f1 f1 = g_f1((struct f1){1.25f});
  pf("ret f1", f1.a);
  struct f2 f2 = g_f2((struct f2){-2.0f, 3.5f});
  pf("ret f2", f2.a - f2.b);
  struct f3 f3 = g_f3((struct f3){{1, 2, 3}});
  pf("ret f3", f3.a[0]);
  struct f4 f4 = g_f4((struct f4){1, {2, 3}, 4});
  pf("ret f4", f4.a * 1000 + f4.in.b * 100 + f4.in.c * 10 + f4.d);
  pf("ret d1", g_d1((struct d1){0.1}).a);
  struct d2 d2 = g_d2((struct d2){1e300, 1.0});
  pd("ret d2", d2.b);
  struct d3 d3 = g_d3((struct d3){1.5, {2.25, 0}});
  pd("ret d3", d3.b[1]);
  struct d4 d4 = g_d4((struct d4){{1, 2}, {3, 4}});
  pd("ret d4", d4.lo.a * 1000 + d4.lo.b * 100 + d4.hi.a * 10 + d4.hi.b);
  union uf3 u3;
  u3.v[0] = 1;
  u3.v[1] = 2;
  u3.v[2] = 3;
  u3 = g_uf3(u3);
  pf("ret uf3", u3.v[0] + u3.v[1]);
  struct f2a fa = g_f2a((struct f2a){7, 8});
  pf("ret f2a", fa.a + fa.b);
  struct fz z = g_fz((struct fz){9, 10});
  pf("ret fz", z.b);

  show("ret c1", g_c1((struct c1){'A'}).c);
  struct c3 c3 = g_c3((struct c3){1, 2, 3});
  show("ret c3", c3.a * 100 + c3.c);
  struct i8b i8 = g_i8b((struct i8b){-5, 300, 'q'});
  show("ret i8b", i8.a + i8.s + i8.c);
  struct pad12 p12 = g_pad12((struct pad12){'p', 100000, -7});
  show("ret pad12", p12.s);
  struct mix16 m16 = g_mix16((struct mix16){'m', 2.5});
  pd("ret mix16", m16.d);
  struct fi fi = g_fi((struct fi){0.5f, 41});
  show("ret fi", fi.i);
  struct al16 a16 = g_al16(1, (struct al16){1L << 40}, 3);
  show("ret al16", a16.a);
  struct sal s16 = g_sal(4, (struct sal){-9}, 5);
  show("ret sal", s16.a);
  long n = 41;
  struct ptrs ps = g_ptrs((struct ptrs){"pointers", &n});
  print_str(ps.s);
  fai_put_char('\n');
  show("n", n);
  struct arr ar = g_arr((struct arr){{1, 2, 3, 4, 5}});
  show("ret arr", ar.v[0] + ar.v[4]);
  struct bits bt = g_bits((struct bits){5, -100, 0x12345, 'd'});
  show("ret bits.b", bt.b);
  show("ret bits.c", bt.c);
  show("ret bits.a", bt.a);
  struct big bg = {1, 2, 3};
  struct big bg2 = g_big(bg);
  show("big.b kept", bg.b);
  show("ret big.b", bg2.b);
  struct huge h;
  for (int i = 0; i < 20; i++) h.v[i] = i * i - 50;
  h.tail = (struct d2){0.5, -0.75};
  struct huge h2 = g_huge(h);
  show("huge kept", h.v[3]);
  show("ret huge", h2.v[3]);
  union ui ui;
  ui.i = 0x41424344;
  ui.c[4] = 'E';
  ui.c[5] = 'F';
  ui = g_ui(ui);
  show("ret ui", ui.c[0] + ui.c[4] + ui.c[5]);
  union uh uh;
  uh.l[0] = 1;
  uh.l[1] = 2;
  uh.l[2] = 3;
  uh = g_uh(uh);
  show("ret uh", uh.l[0] + uh.l[2]);
  struct empty e = g_empty(1, (struct empty){}, 2);
  e = g_empty(3, e, 4);
  show("sizeof empty", sizeof e);
  pf("ret eh", g_eh((struct eh){{}, 0.5f, 0.25f}).a);
  show("ret fam", g_fam((struct fam){14}).n);
  pf("ret z0", g_z0(0.5, (struct z0){1, 2}).a);

  struct d2 d[10];
  for (int i = 0; i < 10; i++) d[i] = (struct d2){i + 0.5, -i - 0.25};
  pd("many_d2", many_d2(d[0], d[1], d[2], d[3], 100.0, d[5], d[6], d[7], d[8], d[9]));
  struct mix16 mx[4] = {{1, 0.5}, {2, 1.5}, {3, 2.5}, {4, 3.5}};
  show("many_mix", many_mix(mx[0], 2, mx[1], (struct al16){3}, mx[2], 5, (struct big){6, 7, 8},
                            mx[3], (struct al16){9}, (struct pad12){1, 10, 2},
                            (struct c3){3, 11, 4}, 12));
  pf("many_f", many_f((struct f3){{1, 2, 3}}, (struct f3){{4, 5, 6}}, (struct f4){7, {8, 9}, 10},
                      (struct f1){11}, 12, (struct f2){13, 14}, (struct f1){15}));
  return 0;
}
