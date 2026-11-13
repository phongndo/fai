/* The output helpers of fai_test.h, for the corpus's native runs (compiled by the reference C
 * compiler and linked into both its binary and fcc's). */
#include <stdio.h>

void fai_put_long(long v) { printf("%ld", v); }

void fai_put_char(int c) { putchar((unsigned char)c); }
