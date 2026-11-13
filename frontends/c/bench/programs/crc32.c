// Table-driven CRC-32 over a pseudo-random buffer, repeated: byte loads, table lookups, shifts.
#include <stdio.h>
#include <stdlib.h>

static unsigned table[256];
static unsigned char buf[1 << 16];

static void make_table(void) {
  for (unsigned i = 0; i < 256; i++) {
    unsigned c = i;
    for (int k = 0; k < 8; k++)
      c = c & 1 ? 0xEDB88320u ^ (c >> 1) : c >> 1;
    table[i] = c;
  }
}

static unsigned crc32(const unsigned char *p, long n, unsigned crc) {
  crc = ~crc;
  for (long i = 0; i < n; i++)
    crc = table[(crc ^ p[i]) & 0xFF] ^ (crc >> 8);
  return ~crc;
}

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  make_table();
  unsigned s = 12345;
  for (int i = 0; i < (int)sizeof buf; i++) {
    s = s * 1664525u + 1013904223u;
    buf[i] = (unsigned char)(s >> 24);
  }
  unsigned crc = 0;
  for (int r = 0; r < reps; r++)
    crc = crc32(buf, sizeof buf, crc);
  printf("crc32 %08x\n", crc);
  return 0;
}
