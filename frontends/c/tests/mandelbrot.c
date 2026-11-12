/* The Mandelbrot set as ASCII art, in double, and a coarser float rendering; then the
 * escape-time histogram. */
#include "fai_test.h"

static int escape(double cr, double ci, int limit) {
  double zr = 0, zi = 0;
  int n = 0;
  while (n < limit && zr * zr + zi * zi <= 4.0) {
    double t = zr * zr - zi * zi + cr;
    zi = 2 * zr * zi + ci;
    zr = t;
    n++;
  }
  return n;
}

static int escapef(float cr, float ci, int limit) {
  float zr = 0, zi = 0;
  int n;
  for (n = 0; n < limit; n++) {
    float zr2 = zr * zr, zi2 = zi * zi;
    if (zr2 + zi2 > 4.0f) break;
    zi = 2 * zr * zi + ci;
    zr = zr2 - zi2 + cr;
  }
  return n;
}

int main(void) {
  const char *shades = " .:-=+*#%@";
  int hist[11] = {0};
  for (int y = 0; y < 24; y++) {
    for (int x = 0; x < 72; x++) {
      double cr = -2.2 + x * (3.2 / 72), ci = -1.2 + y * (2.4 / 24);
      int n = escape(cr, ci, 200);
      hist[n == 200 ? 10 : n / 20]++;
      fai_put_char(n == 200 ? '@' : shades[n % 9]);
    }
    fai_put_char('\n');
  }
  for (int i = 0; i < 11; i++) show("bucket", hist[i]);
  for (float ci = -1.0f; ci <= 1.0f; ci += 0.25f) {
    for (float cr = -2.0f; cr <= 0.5f; cr += 0.125f) fai_put_char(escapef(cr, ci, 50) == 50 ? '#' : '.');
    fai_put_char('\n');
  }
  return 0;
}
