/* C23's preprocessor: #elifdef, #elifndef, __VA_OPT__, __has_include, #warning, and
 * __STDC_VERSION__. */
#include "fai_test.h"

#if __has_include(<stddef.h>)
#define HAVE_STDDEF 1
#else
#define HAVE_STDDEF 0
#endif

#if __has_include("no_such_header_here.h")
#define HAVE_NONE 1
#else
#define HAVE_NONE 0
#endif

#define ALPHA
#ifdef NOT_DEFINED
#define WHICH 1
#elifdef ALPHA
#define WHICH 2
#else
#define WHICH 3
#endif

#ifdef NOT_DEFINED
#define WHICH2 1
#elifndef ALSO_NOT_DEFINED
#define WHICH2 2
#endif

#define NONEMPTY(...) (0 __VA_OPT__(+1))

#define SUM(first, ...) (first __VA_OPT__(+ sum_rest(__VA_ARGS__)))
static int sum_rest(int a, int b) { return a + b; }

#warning "this warning is expected"

int main(void) {
  show("stdc version", __STDC_VERSION__ >= 202311L);
  show("has stddef", HAVE_STDDEF);
  show("has none", HAVE_NONE);
  show("elifdef", WHICH);
  show("elifndef", WHICH2);
  show("sum 1", SUM(5));
  show("sum 3", SUM(5, 6, 7));
  show("nonempty 0", NONEMPTY());
  show("nonempty 1", NONEMPTY(x));
  return 0;
}
