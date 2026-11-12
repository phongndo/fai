/* CRC-32 (IEEE) with a table built at run time, and Adler-32, over strings and a generated
 * buffer: unsigned 32-bit arithmetic, shifts, and table lookups. */
#include "fai_test.h"
#include <stdint.h>

static uint32_t table[256];

static void build(void) {
  for (uint32_t i = 0; i < 256; i++) {
    uint32_t c = i;
    for (int k = 0; k < 8; k++) c = c & 1 ? 0xedb88320u ^ (c >> 1) : c >> 1;
    table[i] = c;
  }
}

static uint32_t crc32(const unsigned char *p, unsigned long n) {
  uint32_t c = 0xffffffffu;
  while (n--) c = table[(c ^ *p++) & 0xff] ^ (c >> 8);
  return c ^ 0xffffffffu;
}

static uint32_t adler32(const unsigned char *p, unsigned long n) {
  uint32_t a = 1, b = 0;
  for (unsigned long i = 0; i < n; i++) {
    a = (a + p[i]) % 65521;
    b = (b + a) % 65521;
  }
  return b << 16 | a;
}

static unsigned long len(const char *s) {
  unsigned long n = 0;
  while (s[n]) n++;
  return n;
}

int main(void) {
  build();
  const char *s = "The quick brown fox jumps over the lazy dog";
  show("crc32", crc32((const unsigned char *)s, len(s)));
  show("crc32 empty", crc32((const unsigned char *)"", 0));
  show("crc32 123456789", crc32((const unsigned char *)"123456789", 9));
  show("adler32", adler32((const unsigned char *)s, len(s)));
  unsigned char buf[1000];
  for (int i = 0; i < 1000; i++) buf[i] = (unsigned char)(i * 31 + (i >> 3));
  show("crc32 buffer", crc32(buf, sizeof buf));
  show("adler32 buffer", adler32(buf, sizeof buf));
  return 0;
}
