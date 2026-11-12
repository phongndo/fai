/* A binary search tree on the heap: insertion, lookup, in-order traversal through a callback,
 * height, deletion with the successor, and freeing the tree. */
#include "fai_test.h"
#include <stdlib.h>

struct tree {
  long key;
  struct tree *left, *right;
};

static struct tree *insert(struct tree *t, long key) {
  if (!t) {
    t = malloc(sizeof(struct tree));
    t->key = key;
    t->left = t->right = 0;
  } else if (key < t->key) {
    t->left = insert(t->left, key);
  } else if (key > t->key) {
    t->right = insert(t->right, key);
  }
  return t;
}

static int contains(const struct tree *t, long key) {
  while (t && t->key != key) t = key < t->key ? t->left : t->right;
  return t != 0;
}

static int height(const struct tree *t) {
  if (!t) return 0;
  int l = height(t->left), r = height(t->right);
  return 1 + (l > r ? l : r);
}

static void walk(const struct tree *t, void (*f)(long)) {
  if (!t) return;
  walk(t->left, f);
  f(t->key);
  walk(t->right, f);
}

static struct tree *erase(struct tree *t, long key) {
  if (!t) return 0;
  if (key < t->key) {
    t->left = erase(t->left, key);
  } else if (key > t->key) {
    t->right = erase(t->right, key);
  } else if (t->left && t->right) {
    struct tree *s = t->right;
    while (s->left) s = s->left;
    t->key = s->key;
    t->right = erase(t->right, s->key);
  } else {
    struct tree *child = t->left ? t->left : t->right;
    free(t);
    return child;
  }
  return t;
}

static void destroy(struct tree *t) {
  if (!t) return;
  destroy(t->left);
  destroy(t->right);
  free(t);
}

static void print_key(long k) {
  fai_put_long(k);
  fai_put_char(' ');
}

int main(void) {
  struct tree *t = 0;
  long keys[] = {50, 30, 70, 20, 40, 60, 80, 35, 45, 65, 30, 50};
  for (unsigned i = 0; i < sizeof keys / sizeof keys[0]; i++) t = insert(t, keys[i]);
  walk(t, print_key);
  fai_put_char('\n');
  show("height", height(t));
  show("contains 45", contains(t, 45));
  show("contains 46", contains(t, 46));
  t = erase(t, 30);
  t = erase(t, 50);
  t = erase(t, 99);
  walk(t, print_key);
  fai_put_char('\n');
  show("root", t->key);
  destroy(t);
  return 0;
}
