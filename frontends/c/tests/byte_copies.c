/* Objects copied byte by byte through char pointers (a hand-written memcpy and memmove),
 * including structs that hold pointers: the copies must still work as the originals. */
#include "fai_test.h"
#include <stddef.h>

static void *copy(void *dst, const void *src, size_t n) {
  unsigned char *d = dst;
  const unsigned char *s = src;
  while (n--) *d++ = *s++;
  return dst;
}

static void *move(void *dst, const void *src, size_t n) {
  unsigned char *d = dst;
  const unsigned char *s = src;
  if (d < s) {
    while (n--) *d++ = *s++;
  } else {
    d += n;
    s += n;
    while (n--) *--d = *--s;
  }
  return dst;
}

struct rec { const char *name; long id; struct rec *self; int scores[3]; };

int main(void) {
  struct rec a = {"original", 7, 0, {1, 2, 3}};
  a.self = &a;
  struct rec b;
  copy(&b, &a, sizeof a);
  print_str(b.name);
  fai_put_char('\n');
  show("id", b.id);
  show("self points at a", b.self == &a);
  show("through copied pointer", b.self->scores[2]);
  int arr[10];
  for (int i = 0; i < 10; i++) arr[i] = i;
  move(arr + 2, arr, 5 * sizeof(int));
  long s = 0;
  for (int i = 0; i < 10; i++) s = s * 10 + arr[i];
  show("move right", s);
  move(arr, arr + 3, 6 * sizeof(int));
  s = 0;
  for (int i = 0; i < 10; i++) s = s * 10 + arr[i];
  show("move left", s);
  long x = 0x0102030405060708;
  unsigned char raw[8];
  copy(raw, &x, 8);
  show("lowest byte first", raw[0]);
  int *ptrs[2] = {&arr[1], &arr[9]};
  int *back[2];
  copy(back, ptrs, sizeof ptrs);
  show("copied pointers", *back[0] + *back[1]);
  return 0;
}
