/* Variables defined in another file: this program's (extern/extern_variables.c, compiled by
 * the reference compiler) and libc's (stdout). Each is reached through its address, read
 * from the GOT; initializers holding their addresses are filled before main. */
#include "fai_test.h"
#include <stdio.h>

extern long ext_counter;
extern int ext_table[4];
extern const char ext_name[];
extern struct ext_pair {
  int a;
  long b;
} ext_pair;
extern int *ext_ptr;

static long *counter_addr(void) { return &ext_counter; }

struct entry {
  const char *name;
  void *data;
};
static struct entry entries[] = {{"counter", &ext_counter}, {"none", 0}, {"third", &ext_table[2]}};
static void *const pair_addr = &ext_pair;
long *counter_ptr = &ext_counter;
extern int ext_seen_early;
static int **lit_ptr = (int *[]){&ext_table[3], 0};

int main(void) {
  ext_counter += 2;
  (*counter_addr())++;
  show("counter", ext_counter);
  int s = 0;
  for (int i = 0; i < 4; i++) s += ext_table[i] * (i + 1);
  show("table", s);
  ext_table[0] = 100;
  show("via ptr", *ext_ptr + ext_table[0]);
  print_str(ext_name);
  fai_put_char('\n');
  ext_pair.b *= 7;
  show("pair", ext_pair.a + ext_pair.b);
  show("entry counter", *(long *)entries[0].data);
  show("entry none", entries[1].data == 0);
  show("entry third", *(int *)entries[2].data);
  show("pair addr", pair_addr == &ext_pair);
  show("seen early", ext_seen_early);
  show("literal", *lit_ptr[0] + (lit_ptr[1] == 0));
  fputs("through stdout\n", stdout);
  fflush(stdout);
  return 0;
}
