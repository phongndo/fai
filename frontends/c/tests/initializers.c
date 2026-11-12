/* Brace and designated initializers, local and global, with the members not named zeroed;
 * compound literals at block and file scope. */
#include "fai_test.h"

struct cfg { int width, height; const char *title; int flags[4]; struct { char on; long v; } opt; };

static struct cfg defaults = {.title = "untitled", .width = 80, .flags[2] = 5, .opt.v = 3};
static int sparse[10] = {[1] = 1, [4] = 4, [8] = 8, 9};
int *file_scope_literal = (int[]){7, 8, 9};
static struct cfg *ptr_to_literal = &(struct cfg){.height = 24};

static long sum_cfg(const struct cfg *c) {
  long s = c->width + c->height + c->opt.on + c->opt.v;
  for (int i = 0; i < 4; i++) s += c->flags[i] * (i + 1);
  return s;
}

int main(void) {
  show("defaults", sum_cfg(&defaults));
  print_str(defaults.title);
  fai_put_char('\n');
  long s = 0;
  for (int i = 0; i < 10; i++) s = s * 10 + sparse[i];
  show("sparse", s);
  show("file scope literal", file_scope_literal[2]);
  show("pointer to literal", ptr_to_literal->height);
  struct cfg local = {.height = 50, .flags = {1, 2}, .opt = {1, 2}};
  show("local", sum_cfg(&local));
  struct cfg positional = {1, 2, "p", {3, 4, 5, 6}, {7, 8}};
  show("positional", sum_cfg(&positional));
  int grid[3][3] = {[0][0] = 1, [1] = {2, 3}, [2][2] = 4};
  long g = 0;
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++) g = g * 10 + grid[i][j];
  show("grid", g);
  long total = 0;
  for (int i = 0; i < 3; i++) {
    int *lit = (int[]){i, i * 2, i * 3};
    total += lit[0] + lit[1] + lit[2];
  }
  show("literal in loop", total);
  struct cfg *heapless = &(struct cfg){.width = 5};
  heapless->width += 1;
  show("literal lvalue", heapless->width);
  char text[8] = "hi";
  show("text tail zero", text[2] + text[7]);
  int x = 4, y = 9;
  int computed[] = {x * y, x + y, [5] = x - y};
  show("computed", computed[0] + computed[1] + computed[2] + computed[5]);
  show("computed length", sizeof computed / sizeof computed[0]);
  return 0;
}
