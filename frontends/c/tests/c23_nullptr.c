/* C23: nullptr and nullptr_t. */
#include "fai_test.h"
#include <stddef.h>

static int deref_or(const int *p, int dflt) { return p ? *p : dflt; }
static int is_null(void *p) { return p == nullptr; }

int main(void) {
  int x = 41;
  int *p = nullptr;
  show("null", deref_or(p, -1));
  p = &x;
  show("nonnull", deref_or(p, -1));
  show("is_null nullptr", is_null(nullptr));
  show("is_null &x", is_null(&x));
  nullptr_t n = nullptr;
  char *c = n;
  show("char null", c == nullptr);
  show("sizeof nullptr_t", sizeof(nullptr_t));
  show("generic", _Generic(nullptr, nullptr_t: 1, void *: 2, default: 3));
  bool b = nullptr;
  show("as bool", b);
  show("not", !nullptr);
  int *q = 0 ? &x : nullptr;
  show("cond", q == nullptr);
  void (*fp)(void) = nullptr;
  show("fn ptr", fp == nullptr);
  return 0;
}
