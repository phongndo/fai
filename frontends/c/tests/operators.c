/* Short-circuit evaluation (side effects happen only when evaluated), the conditional operator
 * (nested, with side effects, of pointer and void type), and the comma operator. */
#include "fai_test.h"

static int calls;
static int note(int v) { calls = calls * 10 + v; return v; }
static void say(const char *s) { print_str(s); fai_put_char('\n'); }

int main(void) {
  calls = 0;
  int r = note(0) && note(1);
  show("and short", r);
  show("calls", calls);
  calls = 0;
  r = note(1) || note(2);
  show("or short", r);
  show("calls", calls);
  calls = 0;
  r = (note(1) && note(2)) || note(3);
  show("mixed", r);
  show("calls", calls);
  calls = 0;
  r = note(0) || (note(4) && note(0)) || note(5);
  show("chain", r);
  show("calls", calls);
  int x = 7;
  const char *size = x < 5 ? "small" : x < 10 ? "medium" : "large";
  say(size);
  calls = 0;
  int y = x > 3 ? note(8) : note(9);
  show("ternary", y);
  show("calls", calls);
  x > 3 ? say("void then") : say("void else");
  int a = 1, b = 2;
  int *p = x ? &a : &b;
  *p = 50;
  show("a", a);
  int c = (a++, b++, a + b);
  show("comma", c);
  for (int i = 0, j = 10; i < j; i += 3, j -= 3) show("pair", i * 100 + j);
  int z = 0;
  z = z ? z : 17;
  show("elvis-like", z);
  long m = (x & 1) ? (long)x << 40 : -1;
  show("wide ternary", m);
  show("logical values", (5 && 3) + (0 || -1) + !!42);
  return 0;
}
