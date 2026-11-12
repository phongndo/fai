/* `long double` (AAPCS64's is IEEE binary128, which FIR doesn't have) and `_Complex` are
 * diagnosed where they are used; `float` and `double` are fine around them. */
long double scale = 2.5L;
double _Complex z;

long double third(long double x) { return x / 3; }

int literal(double d) { return (int)(d + 1.0L); }

int local(void) {
  long double x = 0;
  return 0;
}

double fine(float f) { return f * 2.0; }

int main(void) { return (int)fine(1.5f); }

// expect: 3:13: 'long double' (binary128 on AArch64)
// expect: 4:17: '_Complex'
// expect: 6:13: 'long double' (binary128 on AArch64)
// expect: 8:38: 'long double' (binary128 on AArch64)
// expect: 11:15: 'long double' (binary128 on AArch64)
