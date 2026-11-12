/* The corpus's output helpers. Until fai-cc has varargs (track V) there is no printf, so the
 * programs print through two external functions, defined in fai_runtime.c for native runs; in
 * `fir run` each call is an event (`@fai_put_long(i64 42) -> ();`), which the test harness turns
 * back into the same text. */
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

#endif
