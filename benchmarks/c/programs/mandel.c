// Mandelbrot escape counts over a grid of doubles: a tight FP loop with a data-dependent exit.
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  int size = argc > 1 ? atoi(argv[1]) : 200;
  long total = 0;
  for (int py = 0; py < size; py++) {
    double ci = 2.0 * py / size - 1.0;
    for (int px = 0; px < size; px++) {
      double cr = 2.5 * px / size - 2.0;
      double zr = 0.0, zi = 0.0;
      int it = 0;
      while (it < 100 && zr * zr + zi * zi <= 4.0) {
        double t = zr * zr - zi * zi + cr;
        zi = 2.0 * zr * zi + ci;
        zr = t;
        it++;
      }
      total += it;
    }
  }
  printf("mandel %ld\n", total);
  return 0;
}
