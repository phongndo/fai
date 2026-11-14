/* Assigning a struct with volatile members: one mem.copy would make their accesses ordinary
 * ones. */
struct regs {
  volatile int status;
  int data;
};

int main(void) {
  struct regs a = {1, 2}, b;
  b = a;
  return b.data;
}

// expect: 10:5: assigning a struct or union with 'volatile' members
