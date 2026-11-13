// Text processing: generate words, split them, hash them, and compare them with hand-written
// string routines: byte loops, char classification, calls.
#include <stdio.h>
#include <stdlib.h>

static long my_strlen(const char *s) {
  long n = 0;
  while (s[n])
    n++;
  return n;
}

static int my_strcmp(const char *a, const char *b) {
  while (*a && *a == *b) {
    a++;
    b++;
  }
  return (int)*a - (int)*b;
}

static unsigned fnv(const char *s, long n) {
  unsigned h = 2166136261u;
  for (long i = 0; i < n; i++)
    h = (h ^ (unsigned char)s[i]) * 16777619u;
  return h;
}

static int is_alpha(char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); }

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  int len = 1 << 16;
  char *text = malloc(len + 1);
  char word[64], prev[64];
  unsigned s = 99;
  for (int i = 0; i < len; i++) {
    s = s * 1103515245u + 12345u;
    unsigned r = (s >> 16) % 32;
    text[i] = r < 5 ? ' ' : r < 6 ? ',' : (char)('a' + r % 26);
  }
  text[len] = 0;
  unsigned long acc = 0;
  long words = 0, same = 0;
  for (int r = 0; r < reps; r++) {
    prev[0] = 0;
    long i = 0, n = my_strlen(text);
    while (i < n) {
      while (i < n && !is_alpha(text[i]))
        i++;
      int w = 0;
      while (i < n && is_alpha(text[i]) && w < 63)
        word[w++] = text[i++];
      word[w] = 0;
      if (w == 0)
        continue;
      words++;
      acc += fnv(word, my_strlen(word));
      if (my_strcmp(word, prev) < 0)
        same++;
      for (int k = 0; k <= w; k++)
        prev[k] = word[k];
    }
  }
  printf("strings %ld %ld %lu\n", words, same, acc);
  free(text);
  return 0;
}
