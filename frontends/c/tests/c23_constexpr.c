/* C23: constexpr objects, in constant expressions (array sizes, case labels, static
 * initializers, static_assert). */
#include "fai_test.h"

constexpr int N = 5;
constexpr long BIG = 1L << 40;
constexpr unsigned char MASK = 0xF0;
constexpr double HALF = 0.5;

struct pair {
  int a, b;
};
constexpr struct pair P = {3, 4};

static int table[N] = {1, 2, 3, 4, 5};
static int doubled = N * 2;

static int classify(int v) {
  switch (v) {
  case N:
    return 100;
  case N + 1:
    return 101;
  case P.a:
    return 3;
  default:
    return -1;
  }
}

int main(void) {
  static_assert(N == 5);
  static_assert(P.b == 4);
  int sum = 0;
  for (int i = 0; i < N; i++) sum += table[i];
  show("sum", sum);
  show("doubled", doubled);
  show("big", BIG >> 32);
  show("mask", MASK);
  show("half*10", (long)(HALF * 10));
  show("classify 5", classify(5));
  show("classify 6", classify(6));
  show("classify 3", classify(3));
  show("classify 9", classify(9));
  constexpr int local = N * N;
  int arr[local];
  for (int i = 0; i < local; i++) arr[i] = i;
  show("arr last", arr[local - 1]);
  show("pair", P.a * 10 + P.b);
  return 0;
}
