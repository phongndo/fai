/* C23's <stdckdint.h>: checked integer arithmetic. */
#include "fai_test.h"
#include <limits.h>
#include <stdckdint.h>

static int vals[] = {0, 1, -1, 1000, INT_MAX, INT_MIN, 46341, -46341};

int main(void) {
  for (unsigned i = 0; i < sizeof vals / sizeof vals[0]; i++) {
    for (unsigned j = 0; j < sizeof vals / sizeof vals[0]; j++) {
      int a = vals[i], b = vals[j], r;
      bool o1 = ckd_add(&r, a, b);
      fai_put_long(o1);
      fai_put_char(' ');
      fai_put_long(r);
      bool o2 = ckd_sub(&r, a, b);
      fai_put_char(' ');
      fai_put_long(o2);
      fai_put_char(' ');
      fai_put_long(r);
      bool o3 = ckd_mul(&r, a, b);
      fai_put_char(' ');
      fai_put_long(o3);
      fai_put_char(' ');
      fai_put_long(r);
      fai_put_char('\n');
    }
  }
  unsigned u;
  show("u sub over", ckd_sub(&u, 1u, 2u));
  show("u sub val", u);
  long l;
  show("mixed", ckd_add(&l, INT_MAX, 1u));
  show("mixed val", l);
  unsigned char uc;
  show("narrow", ckd_add(&uc, 200, 100));
  show("narrow val", uc);
  short sh;
  show("neg to short", ckd_mul(&sh, -300, 200));
  show("short val", sh);
  unsigned long ul;
  show("neg to unsigned", ckd_add(&ul, -5, 3));
  show("ul low", (long)(ul & 0xffff));
  return 0;
}
