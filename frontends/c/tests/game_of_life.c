/* Conway's Game of Life on a torus: a glider and a blinker on two-dimensional char grids,
 * with the grid copied as a struct each generation; printed with printf and putchar. */
#include <stdio.h>

#define W 12
#define H 10
struct grid { char cells[H][W]; };

static int neighbors(const struct grid *g, int r, int c) {
  int n = 0;
  for (int dr = -1; dr <= 1; dr++)
    for (int dc = -1; dc <= 1; dc++)
      if (dr || dc) n += g->cells[(r + dr + H) % H][(c + dc + W) % W];
  return n;
}


static void print_grid(const struct grid *g) {
  for (int r = 0; r < H; r++) {
    char row[W + 1];
    for (int c = 0; c < W; c++) row[c] = g->cells[r][c] ? '#' : '.';
    row[W] = 0;
    printf("%2d %s\n", r, row);
  }
}

int main(void) {
  static struct grid g, tmp;
  g.cells[0][1] = g.cells[1][2] = g.cells[2][0] = g.cells[2][1] = g.cells[2][2] = 1;
  g.cells[6][8] = g.cells[6][9] = g.cells[6][10] = 1;
  for (int gen = 0; gen < 9; gen++) {
    /* step() returns the grid by value through a pointer-free copy */
    struct grid *src = gen % 2 ? &tmp : &g, *dst = gen % 2 ? &g : &tmp;
    for (int r = 0; r < H; r++)
      for (int c = 0; c < W; c++) {
        int n = neighbors(src, r, c);
        dst->cells[r][c] = n == 3 || (n == 2 && src->cells[r][c]);
      }
  }
  print_grid(&tmp);
  int alive = 0;
  for (int r = 0; r < H; r++)
    for (int c = 0; c < W; c++) alive += tmp.cells[r][c];
  printf("alive %d of %d\n", alive, W * H);
  return 0;
}
