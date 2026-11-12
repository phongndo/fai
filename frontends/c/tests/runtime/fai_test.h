/* The corpus's output helpers. Until fai-cc has varargs (track V) there is no printf, so the
 * programs print through two external functions, defined in fai_runtime.c for native runs; in
 * `fir run` each call is an event (`@fai_put_long(i64 42) -> ();`), which the test harness turns
 * back into the same text. Floats print as their exact bits in hexadecimal and a rounded
 * decimal, both computed in C on top of the two. */
#ifndef FAI_TEST_H
#define FAI_TEST_H

/* Print a signed number in decimal, without a newline. */
void fai_put_long(long v);
/* Print one character (its low 8 bits). */
void fai_put_char(int c);

static inline void print_str(const char *s) {
  while (*s) fai_put_char(*s++);
}

static inline void print_long(long v) {
  fai_put_long(v);
  fai_put_char('\n');
}

/* "label value\n" */
static inline void show(const char *label, long v) {
  print_str(label);
  fai_put_char(' ');
  print_long(v);
}

/* The bits of a double or a float. */
static inline unsigned long double_bits(double d) {
  union {
    double d;
    unsigned long u;
  } x;
  x.d = d;
  return x.u;
}
static inline unsigned float_bits(float f) {
  union {
    float f;
    unsigned u;
  } x;
  x.f = f;
  return x.u;
}

/* `v` in hexadecimal, `digits` digits, after "0x". */
static inline void print_hex(unsigned long v, int digits) {
  fai_put_char('0');
  fai_put_char('x');
  for (int i = digits - 1; i >= 0; i--) fai_put_char("0123456789abcdef"[(v >> (4 * i)) & 15]);
}

/* A double in decimal with six digits after the point (rounded half up from the exact
 * remainder), "inf", "nan", or "big" beyond 1e15; a negative sign for negative zero too. */
static inline void print_fixed(double x) {
  if (x != x) {
    print_str("nan");
    return;
  }
  if (double_bits(x) >> 63) {
    fai_put_char('-');
    x = -x;
  }
  if (x > 1e15) {
    print_str(x - x == 0 ? "big" : "inf");
    return;
  }
  long ip = (long)x;
  long frac = (long)((x - ip) * 1e6 + 0.5);
  if (frac >= 1000000) {
    ip++;
    frac -= 1000000;
  }
  fai_put_long(ip);
  fai_put_char('.');
  for (long d = 100000; d > 0; d /= 10) fai_put_char('0' + (int)(frac / d % 10));
}

/* "label 0x<bits> <decimal>\n": the exact bits, then a readable value. */
static inline void show_d(const char *label, double x) {
  print_str(label);
  fai_put_char(' ');
  print_hex(double_bits(x), 16);
  fai_put_char(' ');
  print_fixed(x);
  fai_put_char('\n');
}
static inline void show_f(const char *label, float x) {
  print_str(label);
  fai_put_char(' ');
  print_hex(float_bits(x), 8);
  fai_put_char(' ');
  print_fixed(x);
  fai_put_char('\n');
}

#endif
