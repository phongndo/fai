/* Recursion: factorial, Fibonacci, Ackermann, mutual recursion through prototypes, and the
 * Tower of Hanoi. */
#include "fai_test.h"

static long fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
static int fib(int n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
static int ack(int m, int n) {
  if (m == 0) return n + 1;
  if (n == 0) return ack(m - 1, 1);
  return ack(m - 1, ack(m, n - 1));
}
static int is_odd(unsigned n);
static int is_even(unsigned n) { return n == 0 ? 1 : is_odd(n - 1); }
static int is_odd(unsigned n) { return n == 0 ? 0 : is_even(n - 1); }
static int moves;
static void hanoi(int n, int from, int to, int via) {
  if (n == 0) return;
  hanoi(n - 1, from, via, to);
  moves++;
  hanoi(n - 1, via, to, from);
}
static int depth(int n, int *max) {
  int local[4] = {n, n, n, n};
  if (n > *max) *max = n;
  if (n < 50) depth(n + 1, max);
  return local[0] + local[3];
}

int main(void) {
  show("fact 20", fact(20));
  show("fib 20", fib(20));
  show("ack 2 3", ack(2, 3));
  show("even 101", is_even(101));
  show("odd 101", is_odd(101));
  hanoi(10, 1, 3, 2);
  show("hanoi moves", moves);
  int max = 0;
  show("depth", depth(0, &max));
  show("max", max);
  return 0;
}
