/* Calls to C library functions that fai-cc doesn't define: external functions with
 * conservative effects (strlen, memcpy, memset, memcmp, abs, putchar). The program's
 * interpreter run can't be compared (the interpreter's world answers external calls with
 * zeros), only its native runs. */
#include "fai_test.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
  const char *s = "external";
  show("strlen", (long)strlen(s));
  char buf[32];
  memset(buf, 'x', sizeof buf);
  memcpy(buf, s, strlen(s) + 1);
  print_str(buf);
  fai_put_char('\n');
  show("tail kept", buf[20]);
  show("memcmp", memcmp("abc", "abd", 3) < 0);
  show("abs", abs(-17));
  show("labs", labs(-123456789012L));
  putchar('o');
  putchar('k');
  putchar('\n');
  return 0;
}
