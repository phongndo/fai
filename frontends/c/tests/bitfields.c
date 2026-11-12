/* Bitfields: signed and unsigned, packed into shared storage units as Clang lays them out,
 * read and written alone and with neighbors, in locals and globals. */
#include "fai_test.h"

struct flags {
  unsigned ready : 1;
  unsigned mode : 3;
  signed delta : 5;
  unsigned char tag;
  unsigned long wide : 40;
  int tail : 12;
};

struct packet {
  unsigned version : 4, ihl : 4;
  unsigned char tos;
  unsigned short length;
};

struct flags global_flags = {1, 5, -7, 'g', 0x123456789ul, -100};

int main(void) {
  struct flags f = {0};
  f.ready = 1;
  f.mode = 6;
  f.delta = -3;
  f.tag = 'x';
  f.wide = 0xfffffffffful;
  f.tail = 2047;
  show("ready", f.ready);
  show("mode", f.mode);
  show("delta", f.delta);
  show("tag", f.tag);
  show("wide", (long)f.wide);
  show("tail", f.tail);
  f.mode = 9; /* truncated to 3 bits */
  show("mode truncated", f.mode);
  f.delta += 20; /* 17 in 5 signed bits: -15 */
  show("delta wrapped", f.delta);
  show("assignment value", f.mode = 13);
  f.tail++;
  show("tail++", f.tail);
  show("global ready", global_flags.ready);
  show("global mode", global_flags.mode);
  show("global delta", global_flags.delta);
  show("global tag", global_flags.tag);
  show("global wide", (long)global_flags.wide);
  show("global tail", global_flags.tail);
  show("sizeof flags", sizeof(struct flags));
  struct packet p = {4, 5, 0, 1500};
  unsigned char *raw = (unsigned char *)&p;
  show("raw byte 0", raw[0]);
  show("length", p.length);
  p.ihl = 15;
  show("raw byte 0 after", raw[0]);
  show("sizeof packet", sizeof p);
  return 0;
}
