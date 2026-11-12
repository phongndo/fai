/* Variable-length arrays aren't supported. */
int sum(int n) {
  int xs[n];
  int s = 0;
  for (int i = 0; i < n; i++) xs[i] = i, s += xs[i];
  return s;
}

int main(void) { return sum(3); }

// expect: 3:7: variable-length arrays
