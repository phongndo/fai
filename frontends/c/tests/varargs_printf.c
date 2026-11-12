/* A small printf written in C over va_arg (%d %i %u %x %c %s %f %ld %lu %lx %%, the flags - 0 +,
 * widths, and precisions for strings and doubles), checked against the C library's
 * vsnprintf on the same arguments through va_copy, and forwarding of a va_list between
 * functions that take ... and those that take a va_list. */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

struct out {
  char *buf;
  int len, cap;
};

static void put(struct out *o, char c) {
  if (o->len + 1 < o->cap) o->buf[o->len] = c;
  o->len++;
}

static void pad(struct out *o, int n, char c) {
  while (n-- > 0) put(o, c);
}

/* An unsigned number's digits in `base`, at the end of `tmp`; their count. */
static int digits(char *tmp, unsigned long v, unsigned base) {
  int n = 0;
  do {
    tmp[31 - n++] = "0123456789abcdef"[v % base];
    v /= base;
  } while (v);
  return n;
}

static void field(struct out *o, const char *s, int n, int width, int left, char fill) {
  if (!left) pad(o, width - n, fill);
  for (int i = 0; i < n; i++) put(o, s[i]);
  if (left) pad(o, width - n, ' ');
}

/* A double with `prec` digits after the point, rounded half away from zero on the scaled
 * value (the test's values are exact in binary there, so it agrees with printf). */
static int fixed(char *tmp, double x, int prec) {
  char *p = tmp;
  if (x < 0) {
    *p++ = '-';
    x = -x;
  }
  double scale = 1;
  for (int i = 0; i < prec; i++) scale *= 10;
  unsigned long v = (unsigned long)(x * scale + 0.5);
  char d[32];
  int n = digits(d, v, 10);
  while (n <= prec) d[31 - n++] = '0';
  for (int i = n - 1; i >= 0; i--) {
    if (i == prec - 1) *p++ = '.';
    *p++ = d[31 - i];
  }
  return (int)(p - tmp);
}

static int my_vsnprintf(char *buf, int cap, const char *fmt, va_list ap) {
  struct out o = {buf, 0, cap};
  for (const char *f = fmt; *f; f++) {
    if (*f != '%') {
      put(&o, *f);
      continue;
    }
    f++;
    int left = 0, plus = 0;
    char fill = ' ';
    for (;; f++) {
      if (*f == '-') left = 1;
      else if (*f == '0') fill = '0';
      else if (*f == '+') plus = 1;
      else break;
    }
    int width = 0, prec = -1;
    if (*f == '*') {
      width = va_arg(ap, int);
      f++;
    }
    while (*f >= '0' && *f <= '9') width = width * 10 + (*f++ - '0');
    if (*f == '.') {
      f++;
      prec = 0;
      if (*f == '*') {
        prec = va_arg(ap, int);
        f++;
      }
      while (*f >= '0' && *f <= '9') prec = prec * 10 + (*f++ - '0');
    }
    int lng = 0;
    if (*f == 'l') {
      lng = 1;
      f++;
    }
    char tmp[48];
    char d[32];
    switch (*f) {
    case 'd':
    case 'i': {
      long v = lng ? va_arg(ap, long) : va_arg(ap, int);
      unsigned long mag = v < 0 ? 0 - (unsigned long)v : (unsigned long)v;
      int n = digits(d, mag, 10), k = 0;
      if (v < 0) tmp[k++] = '-';
      else if (plus) tmp[k++] = '+';
      if (fill == '0' && !left && k) {
        put(&o, tmp[0]);
        width--;
        k = 0;
      }
      memcpy(tmp + k, d + 32 - n, n);
      field(&o, tmp, k + n, width, left, left ? ' ' : fill);
      break;
    }
    case 'u':
    case 'x': {
      unsigned long v = lng ? va_arg(ap, unsigned long) : va_arg(ap, unsigned);
      int n = digits(d, v, *f == 'x' ? 16 : 10);
      field(&o, d + 32 - n, n, width, left, left ? ' ' : fill);
      break;
    }
    case 'c':
      tmp[0] = (char)va_arg(ap, int);
      field(&o, tmp, 1, width, left, ' ');
      break;
    case 's': {
      const char *s = va_arg(ap, const char *);
      int n = (int)strlen(s);
      if (prec >= 0 && prec < n) n = prec;
      field(&o, s, n, width, left, ' ');
      break;
    }
    case 'f': {
      int n = fixed(tmp, va_arg(ap, double), prec < 0 ? 6 : prec);
      field(&o, tmp, n, width, left, ' ');
      break;
    }
    case '%':
      put(&o, '%');
      break;
    default:
      put(&o, '?');
      break;
    }
  }
  if (cap > 0) o.buf[o.len < cap ? o.len : cap - 1] = 0;
  return o.len;
}

static int my_snprintf(char *buf, int cap, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = my_vsnprintf(buf, cap, fmt, ap);
  va_end(ap);
  return r;
}

/* Format with both, print both, and say whether they agree. */
static int checks, agreed;
static void check(const char *fmt, ...) {
  va_list ap, ref;
  va_start(ap, fmt);
  va_copy(ref, ap);
  char mine[96], theirs[96];
  int a = my_vsnprintf(mine, sizeof mine, fmt, ap);
  int b = vsnprintf(theirs, sizeof theirs, fmt, ref);
  va_end(ref);
  va_end(ap);
  checks++;
  agreed += a == b && strcmp(mine, theirs) == 0;
  printf("%-26s -> %2d \"%s\" %s\n", fmt, a, mine, a == b && !strcmp(mine, theirs) ? "ok" : theirs);
}

/* Forwarding: ... to va_list to va_list. */
static int inner(char *buf, int cap, const char *fmt, va_list ap) {
  return my_vsnprintf(buf, cap, fmt, ap);
}
static int middle(char *buf, int cap, const char *fmt, va_list ap) {
  va_list copy;
  va_copy(copy, ap);
  int r = inner(buf, cap, fmt, copy);
  va_end(copy);
  return r;
}
static int outer(char *buf, int cap, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = middle(buf, cap, fmt, ap);
  /* `middle` worked on copies, so ap still starts at the first argument. */
  int first = va_arg(ap, int);
  va_end(ap);
  return r * 1000 + first;
}

int main(void) {
  check("plain text");
  check("%d %i %d", 0, -12345, 2147483647);
  check("[%5d] [%-5d] [%05d] [%+d]", 42, 42, -42, 7);
  check("%ld %lu %lx", -9000000000L, 18000000000000000000UL, 0xdeadbeefcafeUL);
  check("%u %x %08x", 4294967295u, 48879u, 255u);
  check("%c%c%c [%3c]", 'a', 'b', 'c', 'd');
  check("[%s] [%8s] [%-8s] [%.2s]", "str", "right", "left", "precision");
  check("[%*d] [%-*d] [%.*s]", 6, 1, 6, 2, 3, "abcdef");
  check("%f %.2f %.0f %8.3f", 1.5, -2.25, 3.0, 0.125);
  check("%f", 1048576.0625);
  check("100%% %s", "done");
  char tiny[6];
  int r = my_snprintf(tiny, sizeof tiny, "%s", "truncate me");
  printf("tiny %d \"%s\"\n", r, tiny);
  char buf[64];
  r = outer(buf, sizeof buf, "%d+%d=%s", 20, 22, "42");
  printf("outer %d \"%s\"\n", r, buf);
  printf("%d of %d agree\n", agreed, checks);
  return agreed == checks ? 0 : 1;
}
