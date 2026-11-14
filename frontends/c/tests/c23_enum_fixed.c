/* C23: enumerations with a fixed underlying type, and enumeration constants beyond int. */
#include "fai_test.h"

enum small : unsigned char { S_A = 1, S_B = 200, S_C = 255 };
enum wide : long long { W_A = -1, W_B = 1LL << 40 };
enum : short { ANON = -3 };
enum big { BIG_A = 0x100000000LL, BIG_B };

struct packed_fields {
  enum small s;
  enum small t;
};

int main(void) {
  show("sizeof small", sizeof(enum small));
  show("sizeof wide", sizeof(enum wide));
  enum small s = S_B;
  s = s + 100; /* converted to unsigned char */
  show("small wrap", s);
  show("S_C", S_C);
  show("generic", _Generic(S_A, enum small: 1, int: 2, default: 3));
  show("W_B>>32", W_B >> 32);
  show("W_A", W_A);
  show("anon", ANON);
  show("sizeof ANON", sizeof ANON);
  show("BIG_B>>32", BIG_B >> 32);
  show("BIG_B low", BIG_B & 0xff);
  show("sizeof struct", sizeof(struct packed_fields));
  enum wide w = W_B;
  w += 5;
  show("wide add", w & 0xffff);
  return 0;
}
