// Binary trees allocated with malloc and freed, depth-first: calls, recursion, pointer chasing,
// the allocator.
#include <stdio.h>
#include <stdlib.h>

struct node {
  struct node *left, *right;
  int value;
};

static struct node *build(int depth, int value) {
  struct node *n = malloc(sizeof *n);
  n->value = value;
  if (depth > 0) {
    n->left = build(depth - 1, 2 * value);
    n->right = build(depth - 1, 2 * value + 1);
  } else {
    n->left = n->right = 0;
  }
  return n;
}

static long check(const struct node *n) {
  if (!n->left)
    return n->value & 1023;
  return (n->value & 1023) + check(n->left) + check(n->right);
}

static void destroy(struct node *n) {
  if (n->left) {
    destroy(n->left);
    destroy(n->right);
  }
  free(n);
}

int main(int argc, char **argv) {
  int reps = argc > 1 ? atoi(argv[1]) : 1;
  long total = 0;
  for (int r = 0; r < reps; r++) {
    struct node *t = build(16, r + 1);
    total += check(t);
    destroy(t);
  }
  printf("bintree %ld\n", total);
  return 0;
}
