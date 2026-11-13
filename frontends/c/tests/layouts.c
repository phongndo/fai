/* Struct and union layouts that need care: _Alignas members, flexible array members, bitfields
 * at odd offsets and next to other members, anonymous struct and union members, and nested
 * unions; fcc checks FIR's layout of each against Clang's. */
#include "fai_test.h"
#include <stddef.h>
#include <stdlib.h>

struct aligned { char c; _Alignas(16) int x; char d; };
struct flex { int n; long items[]; };
struct odd_bits { char a; unsigned b : 3; unsigned c : 7; short s; unsigned long d : 33; char e; };
struct anon {
  int kind;
  union { long l; struct { short lo, hi; }; };
  struct { char tag; char name[3]; };
};
union nested { struct { char a, b; } pair; int whole; struct odd_bits bits; };
struct one_bit { _Bool flag : 1; };
struct gap { char c; int : 0; char d; };

static struct anon global_anon = {.kind = 3, .hi = -2, .tag = 't', .name = "ab"};
static union nested global_union = {.pair = {1, 2}};
static struct odd_bits global_bits = {'q', 5, 100, -9, 0x1ffffffffUL, 'z'};

int main(void) {
  show("sizeof aligned", sizeof(struct aligned));
  show("offsetof x", offsetof(struct aligned, x));
  show("offsetof d", offsetof(struct aligned, d));
  show("alignof aligned", _Alignof(struct aligned));
  struct aligned al = {'a', 42, 'z'};
  struct aligned al2 = al;
  show("aligned copy", al2.x + al2.d);
  show("sizeof flex", sizeof(struct flex));
  struct flex *f = malloc(sizeof(struct flex) + 4 * sizeof(long));
  f->n = 4;
  for (int i = 0; i < f->n; i++) f->items[i] = i * 100;
  show("flex", f->items[3] + f->n);
  free(f);
  show("sizeof odd_bits", sizeof(struct odd_bits));
  show("offsetof s", offsetof(struct odd_bits, s));
  show("offsetof e", offsetof(struct odd_bits, e));
  struct odd_bits ob = {0};
  ob.a = 'x';
  ob.b = 7;
  ob.c = 99;
  ob.s = -1234;
  ob.d = 0x123456789UL;
  ob.e = 'y';
  show("odd a", ob.a);
  show("odd b", ob.b);
  show("odd c", ob.c);
  show("odd s", ob.s);
  show("odd d", (long)ob.d);
  show("odd e", ob.e);
  show("global odd b", global_bits.b);
  show("global odd c", global_bits.c);
  show("global odd s", global_bits.s);
  show("global odd d", (long)global_bits.d);
  show("global odd e", global_bits.e);
  show("sizeof anon", sizeof(struct anon));
  struct anon an = {.kind = 1, .l = 0x0003000400050006L, .tag = 'k'};
  show("anon lo", an.lo);
  show("anon hi", an.hi);
  show("anon tag", an.tag);
  show("global anon hi", global_anon.hi);
  show("global anon name", global_anon.name[1]);
  show("global anon l", global_anon.l);
  show("sizeof nested", sizeof(union nested));
  show("global union whole", global_union.whole);
  union nested un;
  un.whole = 0;
  un.bits.b = 5;
  show("union bits", un.bits.b);
  struct one_bit ob1 = {1};
  show("one bit", ob1.flag);
  ob1.flag = 0;
  show("one bit cleared", ob1.flag);
  show("sizeof gap", sizeof(struct gap));
  show("offsetof gap d", offsetof(struct gap, d));
  return 0;
}
