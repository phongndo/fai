/* Pointers converted to integers and back (ptr.expose and ptr.from_exposed): the round trip
 * gives a usable pointer, and alignment is visible in the address. The output doesn't depend on
 * the addresses themselves. */
#include "fai_test.h"
#include <stdint.h>

struct node { long key; struct node *next; };

int main(void) {
  long xs[4] = {10, 20, 30, 40};
  uintptr_t addr = (uintptr_t)&xs[1];
  long *p = (long *)addr;
  show("round trip", *p);
  show("aligned to 8", (addr & 7) == 0);
  uintptr_t next = addr + sizeof(long);
  show("next element", *(long *)next);
  intptr_t diff = (intptr_t)&xs[3] - (intptr_t)&xs[0];
  show("byte distance", diff);
  /* XOR-linked: store a pointer as an integer and recover it. */
  struct node n2 = {2, 0}, n1 = {1, 0};
  uintptr_t hidden = (uintptr_t)&n2 ^ 0x5a5a;
  n1.next = (struct node *)(hidden ^ 0x5a5a);
  show("hidden next key", n1.next->key);
  show("null as integer", (long)(uintptr_t)(void *)0);
  return 0;
}
