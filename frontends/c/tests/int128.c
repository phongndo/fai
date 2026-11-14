/* 128-bit integers (`__int128`, `unsigned __int128`): constants, + - * / % (division calls
 * libgcc's __divti3 and friends), bitwise operators, shifts across the halves, comparisons,
 * conversions to and from narrower integers and doubles, parameters, results, globals, and
 * arrays. fcc keeps one as its two 64-bit halves. */
#include "fai_test.h"

typedef unsigned __int128 u128;
typedef __int128 s128;

static u128 g = ((u128)0x0123456789abcdefull << 64) | 0xfedcba9876543210ull;
static s128 table[3] = {-1, (s128)1 << 100, 42};

static void show128(const char *label, u128 v) {
  print_str(label);
  fai_put_char(' ');
  print_hex((unsigned long)(v >> 64), 16);
  print_hex((unsigned long)v, 16);
  fai_put_char('\n');
}

static u128 mul64(unsigned long a, unsigned long b) { return (u128)a * b; }
static s128 negate(s128 x) { return -x; }
static unsigned shift_narrow(unsigned x, s128 n) { return x << n; }
enum big : unsigned __int128 { SMALL = 1, HUGE = (unsigned __int128)1 << 100 };
static u128 from_enum(enum big e) { return e; }

int main(void) {
  u128 a = g, b = mul64(0xffffffffffffffffull, 0xfffffffffffffffeull);
  show128("g", a);
  show128("mul64", b);
  show128("add", a + b);
  show128("sub", a - b);
  show128("mul", a * b);
  show128("div", a / 1000000007);
  show128("rem", a % 1000000007);
  show128("and", a & b);
  show128("xor", a ^ ~b);
  show128("shl 3", a << 3);
  show128("shl 64", a << 64);
  show128("shl 100", a << 100);
  show128("shr 70", a >> 70);
  s128 n = negate((s128)a);
  show128("neg", (u128)n);
  show128("sar 4", (u128)(n >> 4));
  show128("sar 120", (u128)(n >> 120));
  show128("sdiv", (u128)(n / -12345));
  show128("srem", (u128)(n % -12345));
  show("lt", a < b);
  show("slt", n < (s128)b);
  show("eq", a == g);
  show("to long", (long)(n >> 64));
  show("to int", (int)a);
  show128("from long", (u128)(s128)-5L);
  show128("from unsigned", (u128)4000000000u);
  show("to double", (long)((double)(a >> 70) / 1024));
  show128("from double", (u128)(s128)-1e30);
  s128 sum = 0;
  for (int i = 0; i < 3; i++) sum += table[i];
  show128("table", (u128)sum);
  u128 c = 1;
  for (int i = 1; i <= 30; i++) c *= i;
  show128("30!", c);
  show("truth", !c + !!c);
  show("narrow << wide", shift_narrow(1, 5));
  enum big e = HUGE;
  show128("enum", from_enum(e) + SMALL);
  show("enum cmp", e > SMALL);
  return 0;
}
