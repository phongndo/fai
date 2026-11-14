/* C23: #embed a file's bytes into an initializer, with limit, prefix, suffix, if_empty, and
 * __has_embed. */
#include "fai_test.h"

static const unsigned char head[] = {
#embed "c23_embed.c" limit(16)
};

static const unsigned char framed[] = {
#embed "c23_embed.c" limit(4) prefix(0xAA, ) suffix(, 0xBB)
};

static const int empty_or[] = {
#embed "c23_embed.c" limit(0) if_empty(42)
};

#if __has_embed("c23_embed.c")
#define HAS_EMBED 1
#else
#define HAS_EMBED 0
#endif

int main(void) {
  show("sizeof head", sizeof head);
  long sum = 0;
  for (unsigned i = 0; i < sizeof head; i++) sum += head[i];
  show("sum", sum);
  print_str("text ");
  for (unsigned i = 0; i < sizeof head; i++) fai_put_char(head[i]);
  fai_put_char('\n');
  show("framed size", sizeof framed);
  show("framed first", framed[0]);
  show("framed last", framed[sizeof framed - 1]);
  show("empty or", empty_or[0]);
  show("has embed", HAS_EMBED);
  return 0;
}
