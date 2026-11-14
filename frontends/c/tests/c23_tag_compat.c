/* C23: a struct, union, or enum may be redeclared with the same content, in the same scope,
 * and such types with the same tag and content are compatible. */
#include "fai_test.h"

struct point {
  int x, y;
};
struct point {
  int x, y;
};

#define PAIR(T)                                                                                    \
  struct pair_##T {                                                                                \
    T first, second;                                                                               \
  }

static PAIR(int) make(int a, int b) { return (PAIR(int)){a, b}; }

static int sum(PAIR(int) p) { return p.first + p.second; }

enum color { RED, GREEN };
enum color { RED, GREEN };

int main(void) {
  struct point p = {3, 4};
  show("point", p.x * p.y);
  show("pair", sum(make(20, 22)));
  PAIR(int) q = make(1, 2);
  show("q", q.second);
  show("green", GREEN);
  return 0;
}
