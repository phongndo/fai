/* printf's strings and characters (%s with widths and precisions, %c, %%), puts, and the
 * buffer functions: sprintf and snprintf (truncation, the would-be length, a null buffer of
 * size 0), vsnprintf and vprintf through wrappers that take ..., and fprintf and vfprintf into
 * a memory stream (fmemopen: FIR has no external globals for stdout yet). */
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

/* snprintf through a va_list: the formatted length, even when it didn't fit. */
static int format(char *buf, size_t n, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = vsnprintf(buf, n, fmt, ap);
  va_end(ap);
  return r;
}

/* A logger: a prefix, then the caller's format, through vprintf. */
static int counter;
static void logf_(const char *level, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  printf("[%s #%d] ", level, ++counter);
  vprintf(fmt, ap);
  va_end(ap);
  putchar('\n');
}

/* vfprintf into a stream, twice from a copy of the same arguments. */
static void twice_to(FILE *f, const char *fmt, ...) {
  va_list ap, again;
  va_start(ap, fmt);
  va_copy(again, ap);
  vfprintf(f, fmt, ap);
  fputs(" / ", f);
  vfprintf(f, fmt, again);
  va_end(again);
  va_end(ap);
}

const char *words[] = {"", "a", "fai", "compiler", "a longer string of words"};
size_t one = 1; /* not a constant, so compilers don't warn about the truncation */

int main(void) {
  for (int i = 0; i < 5; i++) {
    const char *w = words[i];
    printf("[%s] [%10s] [%-10s] [%.3s] [%10.2s] [%-*s] [%.*s]\n", w, w, w, w, w, 6, w, i, w);
  }
  printf("chars [%c] [%5c] [%-5c] [%c%c%c]\n", 'x', 'y', 'z', 'f', 'a', 'i');
  printf("percent %% [%5s%%]\n", "50");
  puts("puts adds a newline");
  puts("");

  char buf[32];
  int n = sprintf(buf, "%s=%d;%c", "key", -42, '!');
  printf("sprintf %d \"%s\"\n", n, buf);
  n = snprintf(buf, 8, "%s", "truncated string");
  printf("snprintf %d \"%s\" %zu\n", n, buf, strlen(buf));
  n = snprintf(0, 0, "%d %s %f", 123456, "abc", 1.5);
  printf("snprintf size only %d\n", n);
  n = snprintf(buf, one, "%d", 99);
  printf("snprintf size 1 %d \"%s\"\n", n, buf);
  /* Building a string piece by piece at an offset. */
  int len = 0;
  for (int i = 0; i < 5; i++) len += snprintf(buf + len, sizeof buf - len, "%d,", i * i);
  printf("pieces %d %s\n", len, buf);

  n = format(buf, sizeof buf, "%s|%5.1f|%x|%c", "vsn", 2.25, 48879u, 'Q');
  printf("format %d \"%s\"\n", n, buf);
  n = format(buf, 6, "%d", 1234567890);
  printf("format truncated %d \"%s\"\n", n, buf);

  logf_("info", "%d files, %s", 3, "done");
  logf_("warn", "ratio %.3f exceeds %e", 0.6667, 1e-3);
  logf_("none", "plain");

  char mem[128];
  memset(mem, 0, sizeof mem);
  FILE *f = fmemopen(mem, sizeof mem, "w");
  if (!f) return 1;
  fprintf(f, "fprintf %d %s %.2f;", 7, "into", 0.125);
  twice_to(f, "<%ld %g>", 1L << 33, -0.5);
  fclose(f);
  printf("stream \"%s\"\n", mem);
  return 0;
}
