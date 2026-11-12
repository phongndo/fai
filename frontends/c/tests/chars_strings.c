/* Characters and string literals: escapes, comparisons, and strings as const arrays. */
#include "fai_test.h"

static int count(const char *s, char c) {
  int n = 0;
  for (; *s; s++)
    if (*s == c) n++;
  return n;
}

int main(void) {
  const char *greeting = "hello, world";
  print_str(greeting);
  fai_put_char('\n');
  show("count l", count(greeting, 'l'));
  show("escapes", '\n' + '\t' + '\\' + '\'' + '\x41' + '\101' + '\0');
  char word[] = "abcdef";
  show("sizeof word", sizeof word);
  word[0] = 'A';
  word[5] = 'F';
  print_str(word);
  fai_put_char('\n');
  const char *same = "hello, world";
  show("literal chars equal", same[4] == greeting[4]);
  show("string index", "xyz"[1]);
  char high = '\xe9';
  show("high char", high);
  show("upper", 'a' - 32);
  char buf[16];
  int n = 0;
  for (char ch = 'a'; ch <= 'z'; ch += 5) buf[n++] = ch;
  buf[n] = 0;
  print_str(buf);
  fai_put_char('\n');
  return 0;
}
