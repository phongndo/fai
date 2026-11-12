/* String routines written in C: length, copy, concatenate, compare, search, reverse, number
 * formatting and parsing, and a tokenizer. */
#include "fai_test.h"
#include <stddef.h>

static size_t my_strlen(const char *s) {
  const char *p = s;
  while (*p) p++;
  return (size_t)(p - s);
}
static char *my_strcpy(char *d, const char *s) {
  char *r = d;
  while ((*d++ = *s++)) {}
  return r;
}
static char *my_strcat(char *d, const char *s) {
  my_strcpy(d + my_strlen(d), s);
  return d;
}
static int my_strcmp(const char *a, const char *b) {
  while (*a && *a == *b) a++, b++;
  return (unsigned char)*a - (unsigned char)*b;
}
static const char *my_strstr(const char *h, const char *n) {
  for (; *h; h++) {
    const char *a = h, *b = n;
    while (*a && *b && *a == *b) a++, b++;
    if (!*b) return h;
  }
  return 0;
}
static void reverse(char *s) {
  for (char *e = s + my_strlen(s) - 1; s < e; s++, e--) {
    char t = *s;
    *s = *e;
    *e = t;
  }
}
static char *itoa(long v, char *buf, int base) {
  const char *digits = "0123456789abcdef";
  unsigned long u = v < 0 ? -(unsigned long)v : (unsigned long)v;
  char *p = buf;
  do {
    *p++ = digits[u % base];
    u /= base;
  } while (u);
  if (v < 0) *p++ = '-';
  *p = 0;
  reverse(buf);
  return buf;
}
static long atol_(const char *s) {
  long sign = 1, v = 0;
  while (*s == ' ') s++;
  if (*s == '-' || *s == '+') sign = *s++ == '-' ? -1 : 1;
  while (*s >= '0' && *s <= '9') v = v * 10 + (*s++ - '0');
  return sign * v;
}
static int split(char *s, char sep, char **out, int max) {
  int n = 0;
  while (*s && n < max) {
    out[n++] = s;
    while (*s && *s != sep) s++;
    if (*s) *s++ = 0;
  }
  return n;
}

int main(void) {
  char buf[64];
  my_strcpy(buf, "Hello");
  my_strcat(buf, ", ");
  my_strcat(buf, "FIR!");
  print_str(buf);
  fai_put_char('\n');
  show("length", my_strlen(buf));
  show("cmp equal", my_strcmp("abc", "abc"));
  show("cmp less", my_strcmp("abc", "abd") < 0);
  show("cmp prefix", my_strcmp("ab", "abc") < 0);
  show("cmp high byte", my_strcmp("\xff", "a") > 0);
  const char *found = my_strstr(buf, "FIR");
  show("strstr offset", found ? found - buf : -1);
  show("strstr missing", my_strstr(buf, "xyz") == 0);
  char num[32];
  print_str(itoa(-9876543210L, num, 10));
  fai_put_char('\n');
  print_str(itoa(255, num, 16));
  fai_put_char('\n');
  print_str(itoa(5, num, 2));
  fai_put_char('\n');
  show("atol", atol_("  -12345xyz"));
  char csv[] = "red,green,,blue";
  char *fields[8];
  int n = split(csv, ',', fields, 8);
  show("fields", n);
  for (int i = 0; i < n; i++) {
    fai_put_char('[');
    print_str(fields[i]);
    fai_put_char(']');
  }
  fai_put_char('\n');
  return 0;
}
