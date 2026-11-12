/* 128-bit integers: FIR has them, the AArch64 backend doesn't yet. */
int main(void) {
  __int128 big = 1;
  return (int)big;
}

// expect: 3:12: 128-bit integers ('__int128')
