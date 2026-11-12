/* Inline assembly. */
int main(void) {
  __asm__("nop");
  return 0;
}

// expect: 3:3: inline assembly
