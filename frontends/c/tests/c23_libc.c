/* C23's library additions in <string.h>: strdup, strndup, memccpy, memset_explicit. */
#include "fai_test.h"
#include <stdlib.h>
#include <string.h>

int main(void) {
  char *d = strdup("copy me");
  print_str(d);
  fai_put_char('\n');
  char *n = strndup("truncate", 5);
  print_str(n);
  fai_put_char('\n');
  char dst[16] = {0};
  char *end = memccpy(dst, "abc,def", ',', sizeof dst);
  print_str(dst);
  fai_put_char('\n');
  show("memccpy end", end - dst);
  char secret[8] = "secret!";
  memset_explicit(secret, 0, sizeof secret);
  int nz = 0;
  for (int i = 0; i < 8; i++) nz += secret[i] != 0;
  show("nonzero", nz);
  free(d);
  free(n);
  return 0;
}
