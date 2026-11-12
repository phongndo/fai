/* A string-keyed hash table with chaining over a fixed pool of entries (no heap): insert,
 * update, lookup, delete, and a word count over a text. */
#include "fai_test.h"

#define BUCKETS 31
#define POOL 128

struct entry {
  char key[16];
  long value;
  struct entry *next;
};

struct table {
  struct entry *buckets[BUCKETS];
  struct entry pool[POOL];
  struct entry *free_list;
  int used, size;
};

static unsigned long hash(const char *s) {
  unsigned long h = 5381;
  while (*s) h = h * 33 + (unsigned char)*s++;
  return h;
}

static int streq(const char *a, const char *b) {
  while (*a && *a == *b) a++, b++;
  return *a == *b;
}

static void init(struct table *t) {
  for (int i = 0; i < BUCKETS; i++) t->buckets[i] = 0;
  t->free_list = 0;
  t->used = t->size = 0;
}

static struct entry *alloc_entry(struct table *t) {
  if (t->free_list) {
    struct entry *e = t->free_list;
    t->free_list = e->next;
    return e;
  }
  return t->used < POOL ? &t->pool[t->used++] : 0;
}

static struct entry **slot(struct table *t, const char *key) {
  struct entry **p = &t->buckets[hash(key) % BUCKETS];
  while (*p && !streq((*p)->key, key)) p = &(*p)->next;
  return p;
}

static long *put(struct table *t, const char *key) {
  struct entry **p = slot(t, key);
  if (!*p) {
    struct entry *e = alloc_entry(t);
    if (!e) return 0;
    int i = 0;
    for (; key[i] && i < 15; i++) e->key[i] = key[i];
    e->key[i] = 0;
    e->value = 0;
    e->next = 0;
    *p = e;
    t->size++;
  }
  return &(*p)->value;
}

static int del(struct table *t, const char *key) {
  struct entry **p = slot(t, key);
  if (!*p) return 0;
  struct entry *e = *p;
  *p = e->next;
  e->next = t->free_list;
  t->free_list = e;
  t->size--;
  return 1;
}

static struct table table;

int main(void) {
  init(&table);
  const char *text = "the quick brown fox jumps over the lazy dog the fox is quick and the dog is lazy";
  char word[16];
  int n = 0;
  for (const char *p = text;; p++) {
    if (*p == ' ' || *p == 0) {
      if (n) {
        word[n] = 0;
        (*put(&table, word))++;
        n = 0;
      }
      if (!*p) break;
    } else if (n < 15) {
      word[n++] = *p;
    }
  }
  show("distinct", table.size);
  const char *probe[] = {"the", "fox", "lazy", "cat", "quick"};
  for (int i = 0; i < 5; i++) {
    struct entry *e = *slot(&table, probe[i]);
    print_str(probe[i]);
    fai_put_char(' ');
    print_long(e ? e->value : -1);
  }
  show("delete the", del(&table, "the"));
  show("delete the again", del(&table, "the"));
  show("size", table.size);
  *put(&table, "new") = 77;
  show("reused slot", (*slot(&table, "new"))->value);
  long checksum = 0;
  for (int b = 0; b < BUCKETS; b++)
    for (struct entry *e = table.buckets[b]; e; e = e->next) checksum += e->value * (b + 1);
  show("checksum", checksum);
  return 0;
}
