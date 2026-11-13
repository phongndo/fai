/* Linked lists on the heap (malloc and free, which fcc lowers to FIR's c.malloc
 * allocations): push, append, reverse, merge sort, removal, and freeing everything. */
#include "fai_test.h"
#include <stdlib.h>

struct node {
  int value;
  struct node *next;
};

static struct node *cons(int v, struct node *next) {
  struct node *n = malloc(sizeof *n);
  n->value = v;
  n->next = next;
  return n;
}

static struct node *reverse(struct node *l) {
  struct node *r = 0;
  while (l) {
    struct node *next = l->next;
    l->next = r;
    r = l;
    l = next;
  }
  return r;
}

static struct node *merge(struct node *a, struct node *b) {
  struct node head, *t = &head;
  while (a && b) {
    if (a->value <= b->value) { t->next = a; a = a->next; }
    else { t->next = b; b = b->next; }
    t = t->next;
  }
  t->next = a ? a : b;
  return head.next;
}

static struct node *sort(struct node *l) {
  if (!l || !l->next) return l;
  struct node *slow = l, *fast = l->next;
  while (fast && fast->next) { slow = slow->next; fast = fast->next->next; }
  struct node *right = slow->next;
  slow->next = 0;
  return merge(sort(l), sort(right));
}

static struct node *remove_if(struct node *l, int (*pred)(int)) {
  struct node **p = &l;
  while (*p) {
    if (pred((*p)->value)) {
      struct node *dead = *p;
      *p = dead->next;
      free(dead);
    } else {
      p = &(*p)->next;
    }
  }
  return l;
}

static int is_multiple_of_3(int v) { return v % 3 == 0; }

static void print_list(struct node *l) {
  for (; l; l = l->next) {
    fai_put_long(l->value);
    fai_put_char(l->next ? ' ' : '\n');
  }
}

int main(void) {
  struct node *l = 0;
  for (int i = 0; i < 12; i++) l = cons((i * 7 + 3) % 17, l);
  print_list(l);
  l = reverse(l);
  print_list(l);
  l = sort(l);
  print_list(l);
  l = remove_if(l, is_multiple_of_3);
  print_list(l);
  int n = 0;
  long sum = 0;
  while (l) {
    struct node *next = l->next;
    n++;
    sum += l->value;
    free(l);
    l = next;
  }
  show("freed", n);
  show("sum", sum);
  free(0);
  return 0;
}
