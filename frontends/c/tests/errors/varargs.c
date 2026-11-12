/* Variadic functions come with track V: defining one and calling one (printf). */
#include <stdio.h>

int sum(int n, ...) { return n; }

int main(void) {
  printf("%d\n", 1);
  return 0;
}

// expect: 4:5: variadic functions (track V)
// expect: 7:3: calls to variadic functions (track V)
