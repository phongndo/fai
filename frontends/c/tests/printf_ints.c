/* printf with integers of every width and signedness: the length modifiers (hh, h, l, ll, j, z,
 * t), conversions d i u o x X c, flags (- + space # 0), widths and precisions (also through *),
 * the limits of each type, and printf's return value. Pointers print through %p into a buffer
 * that is checked, not printed (addresses differ between builds). */
#include <inttypes.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Values in non-constant globals, so the reference compiler can't fold the calls. */
signed char sc[] = {SCHAR_MIN, -1, 0, 1, SCHAR_MAX};
unsigned char uc[] = {0, 1, 127, 128, UCHAR_MAX};
short ss[] = {SHRT_MIN, -300, 0, 300, SHRT_MAX};
unsigned short us[] = {0, 1, 32768, 40000, USHRT_MAX};
int si[] = {INT_MIN, -123456, 0, 7, INT_MAX};
unsigned ui[] = {0, 1, 2147483648u, 3000000000u, UINT_MAX};
long sl[] = {LONG_MIN, -9876543210L, 0, 42, LONG_MAX};
unsigned long ul[] = {0, 1, 1UL << 63, 12345678901234567890UL, ULONG_MAX};
long long sll[] = {LLONG_MIN, -1, 0, 1, LLONG_MAX};

int main(void) {
  for (int i = 0; i < 5; i++) {
    printf("hhd %hhd %hhi | hhu %hhu %hhx %hho\n", sc[i], sc[i], uc[i], uc[i], uc[i]);
    printf("hd %hd %6hd %-6hd| hu %hu %#hx %#ho\n", ss[i], ss[i], ss[i], us[i], us[i], us[i]);
    printf("d %d %i %+d % d %011d %-11d| u %u %x %X %#x %#o %o\n", si[i], si[i], si[i], si[i],
           si[i], si[i], ui[i], ui[i], ui[i], ui[i], ui[i], ui[i]);
    printf("ld %ld %+21ld| lu %lu %lx %#lX %lo\n", sl[i], sl[i], ul[i], ul[i], ul[i], ul[i]);
    printf("lld %lld %llu %llx\n", sll[i], (unsigned long long)sll[i], (unsigned long long)sll[i]);
  }
  /* Narrower types passed as int: a char promoted, and printed back narrowed. */
  char c = 'q';
  short negative = -2;
  printf("c %c%c%c|%3c|%-3c|\n", c, 'r' + 1, 65, c, c);
  printf("hhd of 300 %hhd, hd of 70000 %hd, hhu of -1 %hhu\n", 300, 70000, -1);
  printf("short %d unsigned short %u\n", negative, (unsigned short)negative);
  /* Precision on integers: a minimum digit count; zero with precision 0 prints nothing. */
  printf("[%.5d] [%.0d] [%8.3d] [%-8.3x] [%#.0o] [%+.3d]\n", 42, 0, -7, 255u, 0u, 5);
  /* Width and precision through *, negative width meaning left-aligned. */
  for (int w = -6; w <= 6; w += 4) printf("[%*d] [%.*d] [%*.*x]\n", w, 99, w, 99, w, 3, 0xabcu);
  /* The fixed-width types and their macros. */
  int8_t i8 = -128;
  uint16_t u16 = 65535;
  int32_t i32 = -2147483647 - 1;
  uint64_t u64 = UINT64_MAX;
  int64_t i64 = INT64_MIN;
  printf("%" PRId8 " %" PRIu16 " %" PRId32 " %" PRIu64 " %" PRId64 " %" PRIx64 "\n", i8, u16, i32,
         u64, i64, u64);
  intmax_t im = INTMAX_MIN;
  uintmax_t um = UINTMAX_MAX;
  size_t sz = sizeof(long double);
  ptrdiff_t pd = &si[4] - &si[1];
  printf("j %jd %ju z %zu %zx t %td\n", im, um, sz, sz, pd);
  /* printf's result: the number of characters written. */
  int n = printf("%d-%s-%c\n", 12345, "ab", 'z');
  int m = printf("%s", "");
  printf("returned %d %d\n", n, m);
  /* %% and adjacent conversions. */
  printf("100%% %d%%%d %5s%%\n", 1, 2, "x");
  /* Pointers: %p of null is "(nil)"; others start with 0x and read back. */
  char buf[64];
  snprintf(buf, sizeof buf, "%p", (void *)0);
  printf("null %s\n", buf);
  int target = 5;
  snprintf(buf, sizeof buf, "%p", (void *)&target);
  void *back = 0;
  int got = sscanf(buf, "%p", &back);
  printf("pointer 0x prefix %d, scanned %d, same %d\n", strncmp(buf, "0x", 2) == 0, got,
         back == (void *)&target);
  uintptr_t addr = (uintptr_t)&target;
  snprintf(buf, sizeof buf, "%" PRIxPTR, addr);
  printf("as hex digits %d\n", (int)strlen(buf) > 0 && strtoul(buf, 0, 16) == addr);
  return 0;
}
