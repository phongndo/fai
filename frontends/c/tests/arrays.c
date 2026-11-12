/* Arrays: local and global, initialized partly and fully, multidimensional, as parameters,
 * and sizeof of each. */
#include "fai_test.h"

int global_table[10] = {1, 1, 2, 3, 5, 8};
static long grid[3][4];

static long trace(long m[][4], int n) {
  long t = 0;
  for (int i = 0; i < n; i++) t += m[i][i];
  return t;
}

static int total(int n, int *xs) {
  int s = 0;
  for (int i = 0; i < n; i++) s += xs[i];
  return s;
}

int main(void) {
  int local[5] = {3, 1, 4};
  show("local total", total(5, local));
  show("global total", total(10, global_table));
  show("sizeof local", sizeof local);
  show("sizeof grid", sizeof grid);
  show("sizeof grid[0]", sizeof grid[0]);
  for (int i = 0; i < 3; i++)
    for (int j = 0; j < 4; j++) grid[i][j] = i * 10 + j;
  show("trace", trace(grid, 3));
  show("grid[2][3]", grid[2][3]);
  int cube[2][3][4];
  int n = 0;
  for (int i = 0; i < 2; i++)
    for (int j = 0; j < 3; j++)
      for (int k = 0; k < 4; k++) cube[i][j][k] = n++;
  show("cube[1][2][3]", cube[1][2][3]);
  int (*row)[4] = cube[1];
  show("row[1][1]", row[1][1]);
  int *flat = &cube[0][0][0];
  show("flat[17]", flat[17]);
  char names[3][6] = {"one", "two", "three"};
  print_str(names[2]);
  fai_put_char('\n');
  int zeros[100] = {0};
  int nz = 0;
  for (int i = 0; i < 100; i++) nz += zeros[i] != 0;
  show("nonzero", nz);
  int sized[] = {1, 2, 3, 4, 5, 6, 7};
  show("inferred length", sizeof sized / sizeof *sized);
  return 0;
}
