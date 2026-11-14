/* Global initializers that point inside another object (`&table[2]`, `"abcdef" + 3`, a struct
 * member, one past the end), and integers converted to pointers: `offset(@g, N)` and an
 * integer initializing a `ptr`. */
#include "fai_test.h"

int table[4] = {1, 2, 3, 4};
int *third = &table[2];
int *end = &table[4];
const char *tail = "abcdef" + 3;
struct pair {
  long a;
  int b[3];
} pr = {7, {8, 9, 10}};
int *pb = &pr.b[1];
static void *tags[] = {(void *)0, (void *)1, (void *)-1, (void *)4096};
static const int *rows[] = {&table[0], &table[1], &table[3]};

int main(void) {
  show("third", *third);
  show("end - third", end - third);
  show("tail", *tail);
  show("pb", *pb + pb[1]);
  show("tags", (long)tags[1] + (long)tags[2] + (long)tags[3]);
  show("null tag", tags[0] == 0);
  show("rows", *rows[0] * 100 + *rows[1] * 10 + *rows[2]);
  return 0;
}
