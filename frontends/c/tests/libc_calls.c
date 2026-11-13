/* Calls to C library functions that fcc doesn't define: external functions with
 * conservative effects (strlen, memcpy, memset, memcmp, abs, putchar, printf). The program's
 * interpreter run can't be compared (the interpreter's world answers external calls with
 * zeros), only its native runs. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
  const char *s = "external";
  printf("strlen %zu\n", strlen(s));
  char buf[32];
  memset(buf, 'x', sizeof buf);
  memcpy(buf, s, strlen(s) + 1);
  puts(buf);
  printf("tail kept %c\n", buf[20]);
  printf("memcmp %d\n", memcmp("abc", "abd", 3) < 0);
  printf("abs %d labs %ld\n", abs(-17), labs(-123456789012L));
  putchar('o');
  putchar('k');
  putchar('\n');
  return 0;
}
