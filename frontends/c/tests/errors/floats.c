/* Floating point comes with track F2: every use is diagnosed where it is. */
double scale = 2.5;

int half(int x) {
  float f = x;
  return (int)(f / 2);
}

int main(void) { return half(4); }

// expect: 2:8: floating-point types ('double', track F2)
// expect: 5:9: floating-point types ('float', track F2)
