/* Conversions between integers and floats at the edges of their ranges (but inside them: C's
 * out-of-range float-to-integer conversion is UB), rounding of integers to floats (ties to
 * even), double to float (rounding, overflow to infinity, underflow to subnormals and zero),
 * float to double (exact, NaNs quieted), and _Bool from floats. */
#include "fai_test.h"

double dv[] = {2147483647.0, -2147483648.0, 2147483647.9, -2147483648.9, 4294967295.5,
               9223372036854774784.0, -9223372036854775808.0, 18446744073709549568.0,
               -0.99, 0.99, -0.0, 127.9, -128.9, 255.5, 32767.5, -32768.5, 65535.25, 1e-300};
float fv[] = {2147483520.0f, -2147483648.0f, 4294967040.0f, 9223371487098961920.0f,
              -9223372036854775808.0f, 18446742974197923840.0f, -0.5f, 255.9f};
long lv[] = {0, 1, -1, 16777217, -16777217, 16777219, 9007199254740993L, -9007199254740993L,
             9223372036854775807L, -9223372036854775807L - 1, 0x7ffffe0000000000L, 123456789};
unsigned long uv[] = {0, 16777217, 0xffffffffffffffffUL, 0x8000000000000001UL,
                      0xfffffff7ffffffffUL, 9007199254740993UL};
double narrow[] = {3.4028234663852886e38, 3.4028235677973366e38, 3.4028235677973362e38, 1e39,
                   -1e39, 1.401298464324817e-45, 7.006492321624085e-46, 7.006492321624087e-46,
                   1e-46, -1e-46, 1.1754942807573643e-38, 0.1, 16777217.0, 1.0 / 3};
unsigned long nan_bits[] = {0x7ff8000000000000UL, 0xfff4000012345678UL, 0x7ff0000000000001UL};
unsigned fnan_bits[] = {0x7fc00000u, 0xff812345u, 0x7f800001u};

int main(void) {
  /* double to every integer type, in range. */
  show("int max", (int)dv[0]);
  show("int min", (int)dv[1]);
  show("int max.9", (int)dv[2]);
  show("int min.9", (int)dv[3]);
  show("unsigned max.5", (unsigned)dv[4]);
  show("long near max", (long)dv[5]);
  show("long min", (long)dv[6]);
  show("unsigned long near max", (long)((unsigned long)dv[7] >> 1));
  show("unsigned long near max low", (long)((unsigned long)dv[7] & 0xffff));
  show("-0.99 to int", (int)dv[8]);
  show("-0.99 to unsigned", (unsigned)dv[8]);
  show("0.99 to unsigned char", (unsigned char)dv[9]);
  show("-0 to long", (long)dv[10]);
  show("signed char 127.9", (signed char)dv[11]);
  show("signed char -128.9", (signed char)dv[12]);
  show("unsigned char 255.5", (unsigned char)dv[13]);
  show("short 32767.5", (short)dv[14]);
  show("short -32768.5", (short)dv[15]);
  show("unsigned short 65535.25", (unsigned short)dv[16]);
  show("char 1e-300", (char)dv[17]);
  /* float to integers. */
  show("f int", (int)fv[0]);
  show("f int min", (int)fv[1]);
  show("f unsigned", (unsigned)fv[2]);
  show("f long", (long)fv[3]);
  show("f long min", (long)fv[4]);
  show("f unsigned long", (long)((unsigned long)fv[5] >> 8));
  show("f -0.5 unsigned", (unsigned)fv[6]);
  show("f unsigned char", (unsigned char)fv[7]);
  /* Integers to floats: rounded to nearest, ties to even. */
  for (unsigned i = 0; i < sizeof lv / sizeof lv[0]; i++) {
    show_d("long to double", (double)lv[i]);
    show_f("long to float", (float)lv[i]);
    show_d("int to double", (double)(int)lv[i]);
    show_f("int to float", (float)(int)lv[i]);
    show_f("short to float", (short)lv[i]);
    show_d("unsigned to double", (unsigned)lv[i]);
    show_f("unsigned char to float", (unsigned char)lv[i]);
    show_f("signed char to float", (signed char)lv[i]);
  }
  for (unsigned i = 0; i < sizeof uv / sizeof uv[0]; i++) {
    show_d("unsigned long to double", uv[i]);
    show_f("unsigned long to float", uv[i]);
    show_f("unsigned to float", (unsigned)uv[i]);
  }
  /* double to float and back. */
  for (unsigned i = 0; i < sizeof narrow / sizeof narrow[0]; i++) {
    float f = narrow[i];
    show_f("narrowed", f);
    show_d("widened", f);
    show_f("negated", -narrow[i]);
  }
  for (int i = 0; i < 3; i++) {
    union {
      unsigned long u;
      double d;
    } n = {nan_bits[i]};
    union {
      unsigned u;
      float f;
    } fn = {fnan_bits[i]};
    show_f("nan narrowed", (float)n.d);
    show_d("nan widened", fn.f);
    show("nan to bool", (_Bool)n.d);
    show("float nan to bool", (_Bool)fn.f);
  }
  /* _Bool from floats: nonzero (NaN included) is 1; both zeros are 0. */
  show("bool 0.5", (_Bool)dv[9]);
  show("bool -0", (_Bool)dv[10]);
  show("bool 1e-300", (_Bool)dv[17]);
  show("bool tiny float", (_Bool)(float)narrow[6]);
  _Bool b = fv[6];
  show("bool -0.5f", b);
  /* Constants convert exactly as at run time. */
  show_f("16777217 const", (float)16777217);
  show_d("2^63+1 const", (double)9223372036854775809UL);
  show_f("bool const", (_Bool)1);
  return 0;
}
