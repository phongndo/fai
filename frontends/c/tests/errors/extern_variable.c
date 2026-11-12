/* A variable defined in another file (here libc's stdout): FIR has no external globals. */
#include <stdio.h>

int main(void) {
  fputs("hi", stdout);
  return 0;
}

// expect: 5:15: external variables ('stdout' is defined in another file
