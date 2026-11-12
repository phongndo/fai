/* Block scopes and shadowing, static locals (one object across calls, per function), and
 * locals in loops getting their initializers every iteration. */
#include "fai_test.h"

static int next_id(void) {
  static int id = 100;
  return id++;
}

static int other(void) {
  static int id;
  return ++id;
}

static const char *cycle(void) {
  static const char *names[] = {"red", "green", "blue"};
  static int i;
  return names[i++ % 3];
}

int x = 1;

int main(void) {
  show("next_id", next_id());
  show("next_id", next_id());
  show("other", other());
  show("other", other());
  show("next_id", next_id());
  for (int i = 0; i < 4; i++) {
    print_str(cycle());
    fai_put_char(' ');
  }
  fai_put_char('\n');
  show("global x", x);
  int x = 2;
  show("local x", x);
  {
    int x = 3;
    show("inner x", x);
    {
      extern int x;
      show("extern x", x);
    }
  }
  show("local x again", x);
  long sum = 0;
  for (int i = 0; i < 3; i++) {
    int fresh = 10;
    fresh += i;
    sum += fresh;
  }
  show("fresh", sum);
  return 0;
}
