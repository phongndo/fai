/* Globals with initializers: integers, arrays, structs, strings, pointers to other globals
 * and to functions (declared before or after), tentative definitions, and const data. */
#include "fai_test.h"

int counter;
int counter;
long seeded = -42;
const int primes[] = {2, 3, 5, 7, 11, 13};
static char message[] = "global";
const char *motto = "keep it simple";
const char *words[] = {"alpha", "beta", "gamma", 0};
int *first_prime_ptr = (int *)primes;
struct entry { const char *key; int (*fn)(int); struct entry *next; };
static int dbl(int x) { return 2 * x; }
static int sq(int x);
struct entry e2;
struct entry e1 = {"double", dbl, &e2};
struct entry e2 = {"square", sq, &e1};
static int sq(int x) { return x * x; }
long matrix[2][3] = {{1, 2, 3}, {4, 5, 6}};
struct { int a; char b[4]; long c; } nested = {7, "xyz", 99};
unsigned char bytes[5] = {255, 128, 0, 1};

static void bump(void) { counter++; }

int main(void) {
  bump();
  bump();
  show("counter", counter);
  show("seeded", seeded);
  int s = 0;
  for (unsigned i = 0; i < sizeof primes / sizeof primes[0]; i++) s += primes[i];
  show("primes", s);
  message[0] = 'G';
  print_str(message);
  fai_put_char('\n');
  print_str(motto);
  fai_put_char('\n');
  for (const char **w = words; *w; w++) {
    print_str(*w);
    fai_put_char(' ');
  }
  fai_put_char('\n');
  show("first prime", *first_prime_ptr);
  struct entry *e = &e1;
  for (int i = 0; i < 4; i++) {
    print_str(e->key);
    fai_put_char(' ');
    print_long(e->fn(i + 3));
    e = e->next;
  }
  show("matrix[1][2]", matrix[1][2]);
  show("nested.b[1]", nested.b[1]);
  show("nested.c", nested.c);
  show("bytes", bytes[0] + bytes[1] + bytes[2] + bytes[3] + bytes[4]);
  return 0;
}
